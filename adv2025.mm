$[ set.mm $]

$( ADVENT OF METAMATH 2025!

   The task is to prove a variety of results about the provability logic GL (and a few results about a weaker logic K4).
   The results about GL can be interpreted in terms of provability in Peano arithmetic, in particular some famous statements
   about provability (like Godel's second theorem) can be expressed (and proved) in this logic.

   The proofs don't require anything besides theorems of propositional logic and the definitions and axioms from this file,
   so one can load set.mm only up to theorem ~ wex , and it should be sufficient for the proofs.
   No knowledge of Godel's theorems of proof theory are required, but theorem comments try to provide some context anyway.

   The proofs are usually fairly short (and sometimes trivial), so some statements are grouped into one day (for example, Day 1a and Day 1b).
   If you get stuck on some problem, one can usually find the solution in the book Boolos "The logic of provability", chapters 1 and 3.

   Have fun!
$)

$c []. $.

$( If ` ph ` is a wff, then ` []. ph ` is a wff.  The box symbol ` []. ` can
   be read as "necessarily", or "provable" in the case of the provability logic. $)
cbox $a wff []. ph $.

${
  ax-necess.1 $e |- ph $.
  $( The necessitation rule: if something is true, it is necessary true. $)
  ax-necess $a |- []. ph $.
$}

$( The distribution axiom.  This axiom together with ~ ax-necess defines the weakest normal modal logic K. $)
ax-distrb $a |- ( []. ( ph -> ps ) -> ( []. ph -> []. ps ) ) $.

${
  monrule.1 $e |- ( ph -> ps ) $.
  $( Day 1a.  The monotony rule. $)
  monrule $p |- ( []. ph -> []. ps ) $=
    ( wi cbox ax-necess ax-distrb ax-mp ) ABDZEAEBEDICFABGH $.
$}

${
  monbirule.1 $e |- ( ph <-> ps ) $.
  $( Day 1b.  The monotony rule for biimplications. $)
  monbirule $p |- ( []. ph <-> []. ps ) $=
    ( cbox biimpi monrule biimpri impbii ) ADBDABABCEFBAABCGFH $.
$}

$( Day 2.  Box can be distributed through conjunction. $)
distrconj $p |- ( []. ( ph /\ ps ) <-> ( []. ph /\ []. ps ) ) $=
  ( wa cbox simpl monrule simpr jca wi pm3.2 ax-distrb syl imp impbii ) ABCZDZA
  DZBDZCPQROAABEFOBABGFHQRPQBOIZDRPIASABJFBOKLMN $.

${
  monimpconj.1 $e |- ( ( ph /\ ps ) -> ch ) $.
  $( Day 3a.  Monotony for an implication with a conjunction inside. $)
  monimpconj $p |- ( ( []. ph /\ []. ps ) -> []. ch ) $=
    ( cbox wa distrconj monrule sylbir ) AEBEFABFZECEABGJCDHI $.
$}

$( Day 3b.  Box can be "factored out" of a disjunction in one direction. $)
distrdisj $p |- ( ( []. ph \/ []. ps ) -> []. ( ph \/ ps ) ) $=
  ( cbox wo orc monrule olc jaoi ) ACABDZCBCAIABEFBIBAGFH $.

$c <>. $.

$( If ` ph ` is a wff, then ` <>. ph ` is a wff.  The diamond symbol ` <>. `
   can be read as "possibly" and it is defined in terms of ` []. ` .  In the
   case of provability logic, ` <>. ph ` can be interpreted as " ` ph ` is
   consistent with Peano arithmetic". $)
cdiam $a wff <>. ph $.

$( The definition of ` <>. ` in terms of ` []. ` .
   I.e. ` ph ` is consisent with Peano arithmetic if and only if
   it is not provable that ` ph ` is false. $)
df-diam $a |- ( <>. ph <-> -. []. -. ph ) $.

${
  monruled.1 $e |- ( ph -> ps ) $.
  $( Day 4a.  The monotony rule (for diamond). $)
  monruled $p |- ( <>. ph -> <>. ps ) $=
    ( wn cbox cdiam con3i monrule df-diam 3imtr4i ) ADZEZDBDZEZDAFBFNLMKABCGHGA
    IBIJ $.
$}

${
  monbiruled.1 $e |- ( ph <-> ps ) $.
  $( Day 4b.  The monotony rule for biimplications (for diamond). $)
  monbiruled $p |- ( <>. ph <-> <>. ps ) $=
    ( cdiam biimpi monruled biimpri impbii ) ADBDABABCEFBAABCGFH $.
$}

$( Day 5.  Diamond can be distributed through conjunction in one
   direction. $)
distrconjd $p |- ( <>. ( ph /\ ps ) -> ( <>. ph /\ <>. ps ) ) $=
  ( wa cdiam simpl monruled simpr jca ) ABCZDADBDIAABEFIBABGFH $.

$( Day 6.  Diamond can be distributed through disjunction. $)
distrdisjd $p |- ( <>. ( ph \/ ps ) <-> ( <>. ph \/ <>. ps ) ) $=
  ( wo wn cbox cdiam wa ianor ioran monbirule distrconj df-diam orbi12i 3bitr4i
  bitri xchnxbir ) ABCZDZEZDADZEZDZBDZEZDZCZQFAFZBFZCUAUDGZUFSUAUDHSTUCGZEUIRUJ
  ABIJTUCKOPQLUGUBUHUEALBLMN $.

$( Day 7.  If we have a conjunction of a diamond and a box, we can "factor" the diamond out. $)
dandb $p |- ( ( <>. ph /\ []. ps ) -> <>. ( ph /\ ps ) ) $=
  ( cdiam cbox wa wi wn con3 monimpconj ex con3d df-diam 3imtr4g pm3.21 monrule
  imp syl11 ) ACZBDZABEZCZATFZDZRUASUCAGZDZGTGZDZGRUAUCUGUEUCUGUEUBUFUDUBUFUDAT
  HPIJKALTLMBUBBANOQP $.


$( The Godel-Lob axiom, which defines the logic GL. In this logic ` []. ` is
   interpreted as "provable in Peano arithmetic (PA)".  In particular, this
   axiom corresponds to Lob's theorem, which shows that if the statement
   ` []. ph -> ph ` is provable in PA, then ` ph ` is provable in PA. Since
   we are studying an abstract modal logic, we do not need to worry about PA,
   but of course all the results we'll obtain will have consequences for
   provability in PA. $)
ax-gl $a |- ( []. ( []. ph -> ph ) -> []. ph ) $.

$( Day 8a.  Modal logic K4 extends K with an axiom ` [] ph -> []. []. ph ` .
   Turns out this axiom is true in GL, hence GL extends K4.  One can
   interpret this result as: if something is provable, then it's provable
   that it's provable. $)
axk4 $p |- ( []. ph -> []. []. ph ) $=
  ( cbox wa wi pm3.2 simpr monrule syl11 ax-gl syl distrconj sylib simpld ) ABZ
  NBZNNNACZBZONCNQPDZBQARNAPQNAEPANAFGHGPIJNAKLM $.

$( Day 8b.  Another form of ~ axk4 . $)
axk4d $p |- ( <>. <>. ph -> <>. ph ) $=
  ( cdiam wn cbox df-diam notbii biid con1bii bitri axk4 monbirule 3bitrri 3syl
  biimpi con4i ) ABZPBZPCZACZDZTDZQCZRTRTCZCZTPUCAEFZTUCUCGHZINSJUAUBUBUDDZCZCU
  GUAQUHQRDZCUHPEUIUGRUDUEKFIFUGUHUHGHUDTUFKLNMO $.

${
  sdsdeqsdlem.1 $e |- []. ( ( ph /\ ps ) -> th ) $.
  $( Day 9a.  Two simple lemmata for ~ sdsdeqsd .  The proofs should reply
     on ~ axk4 and its corollaries, not on ~ ax-gl . $)
  sdsdeqsd1lem1 $p |- []. ( ( <>. ph /\ []. ps ) -> <>. th ) $=
    ( wa wi cbox cdiam axk4 dandb wn con3 monimpconj con3d df-diam 3imtr4g syl5
    imp ex monrule mp2b ) ABEZCFZGZUDGAHBGEZCHZFZGDUCIUDUGUEUBHZUDUFABJUDUBKZGZ
    KCKZGZKUHUFUDULUJUDULUJUCUKUIUCUKUIUBCLRMSNUBOCOPQTUA $.

  $( Day 9b. $)
  sdsdeqsd1lem2 $p |- []. ( ( []. ph /\ <>. ps ) -> <>. th ) $=
    ( cdiam cbox wa wi pm3.22 imim1i monrule ax-mp sdsdeqsd1lem1 ) BEZAFZGZCEZH
    ZFONGZQHZFBACABGZCHZFBAGZCHZFDUBUDUCUACBAIJKLMRTSPQONIJKL $.
$}

$( Day 10.  Operator ` []. <>. ` applied twice equals itself in logic K4.
   This proof again shouldn't rely on ~ ax-gl directly. $)
sdsdeqsd $p |- ( []. <>. []. <>. ph <-> []. <>. ph ) $=
  ( cdiam cbox axk4 wa distrconj wi simpl ax-necess sdsdeqsd1lem2 sdsdeqsd1lem1
  axk4d syl imim2i monrule ax-mp ax-distrb sylbir mpdan simpr impbii ) ABZCZBZC
  ZUCUEUECZUCUDDUEUFEUDUEEZCZUCUDUEFUGUBGZCZUHUCGUGUBBZBZGZCUJUCUDUKUBUCUBUBUCE
  UBGUBUCHIJKUMUIULUBUGULUKUBUBLALMNOPUGUBQPRSUCUCCZCZUEUCUNUOUBDUCDMUCUOEUBUNE
  ZCZUEUBUNFUPUDGCUQUEGAUCUCAUCEUCGAUCTIKUPUDQPRSUA $.

$( Day 11.  A certain argument in the proof of Lob's theorem.  Again, don't
   rely on ~ ax-gl directly. $)
lobstep $p |- ( []. ( ps <-> ( []. ps -> ph ) ) -> ( []. ( []. ph -> ph ) -> []. ph ) ) $=
  ( cbox wi wb wa dfbi2 monbirule distrconj sylbb axk4 ax-distrb imim2i monrule
  mpdi syl ax-1 monimpconj ex mpd syl5 sylbbr imbi1 biimpa pm3.35 pm2.27 sylbir
  adantll mpdan syl6com 3syl com3l a1dd sylc com24 com3r com13 imp ) BBCZADZEZC
  ZBUTDZCZUTBDZCZFZACZADZCZVHDZVBVCVEFZCVGVAVLBUTGHVCVEIJVDVFVKVDUSVHDZCZVFVKDV
  DVDCVNVCKVDVMVDUSUTCZDZVMBUTLVPUSUSCZVHBKVOVQVHDUSUSALMOPNPVFVNVDVKVFVHUSDZCZ
  VNVDVKDZDVFVFCZVSVEKZVFVRVHVOVFUSAUTAUSQNUTBLZUANPVSVNVFVTVSVNVFVTDZVSVNFZVHU
  SEZCZWDWGVRVMFZCWEWFWHVHUSGHVRVMIUBWGVJVDVFVHWGVJVDVFVHDZDZWGVJFVOVOWJWFVIUTW
  FVIUTVHUSAUCUDRZWKVOVOWIVDVFVOVOVHVFWAVOUSDZCZVOVOVHDZDWBVFWLWCNVOWMUTADZCZWN
  VOVOCZWMWPDZUTKVOWQFUTVOFZCZWRUTVOIWTWMWPWSWLWOVOWLWOUTVOWLFUSWOVOUSUEUSAUFPU
  HRSUGUIUTALUJUKULUMUNSUOPSUPTUQTURP $.

$( Day 12a.  An unusual consequence of ~ ax-gl which works for any formulae
   ` ph ` and ` ps ` .  This could be interpreted as "if we can prove that
   ` ph ` is consistent with PA, then we can prove anything". From now on
   we can use ~ ax-gl in proofs again. $)
kurbis $p |- ( []. <>. ph -> []. ps ) $=
  ( cdiam cbox wn df-diam biimpi monrule wi pm2.21 ax-gl syl axk4 monimpconj ex
  imp syl56 mpd orc orcanai syl2imc ) ACZDAEZDZEZDZBDZUBUEUBUEAFGHUFADZEZDZUGUF
  UDUJUFUDUCIZDUDUEUKUDUCJHUCKLZUDUDDZUFUJUIIZDZUJUCMUFUMUOUEUDUNUEUDUNUDUNJPNO
  UIKQRUJUHUFUDUGUJUHAIZDUHUIUPUHAJHAKLULUHUDUGAUCBAABABSTNOUARL $.

$( Day 12b.  We can prove False (i.e.  PA is inconsistent) if and only if we
   can prove consistency for any sentence ` ph ` . $)
bfbdp $p |- ( []. F. <-> []. <>. ph ) $=
  ( wfal cbox cdiam falim monrule kurbis impbii ) BCADZCBIIEFABGH $.

$( Day 13.  Godel's second theorem can be proved in PA. Namely, if PA is
   consistent ( ` -. []. F. ` ), then we can't prove in PA that it's
   consistent. $)
godel2 $p |- ( -. []. F. -> -. []. -. []. F. ) $=
  ( wfal cbox wn wtru df-fal monbirule notbii df-diam sylbb2 monrule kurbis syl
  cdiam con3i ) ABZCZBZOQDMZBOPRPDCZBZCROTASEFGDHIJDAKLN $.

$( Day 14.  Note that ` []. ph \/ []. -. ph ` can be interpreted as " ` ph `
   is decidable".  Hence the following means that if inconsistency of PA is
   not provable, then the consistency of PA is undecidable. $)
incundec $p |- ( -. []. []. F. -> -. ( []. -. []. F. \/ []. -. -. []. F. ) ) $=
  ( wfal cbox wn wo godel2 con4i axk4 syl notnotr monrule jaoi con3i ) ABZCZBZN
  CZBZDMBZORQOMRMOEFAGHPMMIJKL $.

$( Day 15.  Lemma for ~ equiva . $)
equivalem $p |- ( []. ( ph <-> -. []. ph ) -> []. ( ph <-> -. []. F. ) ) $=
  ( cbox wn wb wi wa wfal dfbi2 monbirule distrconj axk4 monrule ax-distrb syl5
  con3 impcom monimpconj ex 3syl imp sylbb falim imim1 syl cdiam notnotr kurbis
  con3i df-diam biimpri imim2i imim1d jca sylbbr ) AABZCZDZBZAUPEZBZUPAEZBZFZAG
  BZCZEZBZVEAEZBZFZAVEDZBZURUSVAFZBVCUQVMAUPHIUSVAJUAVCVGVIVBUTVGVBVBBVDUOEZBZU
  TVGEVAKVBVNVDUPBZVBUOGUPUPUBLUPAMNLVOUTVGVNUSVFUSVNVFVNUPVEEUSVFVDUOOAUPVEUCN
  PQRSPUTVBVIUTUOVPEZBZUOVDEZBZVBVIEUTUTBVRUSKUTVQAUPMLUDVQVSVPVDUOVPACZCZBZCZB
  WAUEZBVDUPWDWCUOWBAAUFLUHLWDWEWEWDWAUIUJLWAGUGSUKLVTVBVIVSVAVHVSVAVHVSVEUPAUO
  VDOULTQRSTUMVLVFVHFZBVJVKWFAVEHIVFVHJUNS $.

$( Day 16.  It is provable that a statement ` ph ` is equivalent to the
   assertion that ` ph ` is unprovable if and only if it is provable that
   ` ph ` is equivalent to PA being consistent. $)
equiva $p |- ( []. ( ph <-> -. []. ph ) <-> []. ( ph <-> -. []. F. ) ) $=
  ( cbox wn wb wfal equivalem wi dfbi2 monbirule distrconj sylbb axk4 ax-distrb
  wa monrule syl 2a1 pm2.21 pm2.24d ja a1i godel2 con4i impcom monimpconj mpdan
  jad notnotr falim ax-1 anim12i bicomi sylbb1 impbii ) AABZCZDZBZAEBZCZDZBZAFV
  BAUPGZBZUPAGZBZNZURVBAUTGZBZUTAGZBZNZVGVBVHVJNZBVLVAVMAUTHIVHVJJKVIVDVKVFVIUO
  UTBZGZBZVDVIVIBVPVHLVIVOAUTMOPVHVOVCVOVHVCUOVNVHVCGUPVHAQVNAUTVCACVCGVNAUPRUA
  VNUSVCUSVNUBUCSUGTUDUEUFVJVEUTAVEUTCUSVEUSUHUSUOAEAAUIOSPAUPUJTOUKPVCVENZBVGU
  RVCVEJVQUQUQVQAUPHULIUMPUN $.

$( Day 17.  A corollary from ~ equiva .  It is provable that ` ph ` is
   equivalent to the assertion that ` ph ` is disprovable if and only if it
   is provable that ` ph ` is equivalent to PA being inconsistent. $)
equivacor $p |- ( []. ( ph <-> []. -. ph ) <-> []. ( ph <-> []. F. ) ) $=
  ( wn cbox wb wfal notbi monbirule equiva bicomi 3bitri ) AABZCZDZCKLBDZCKECZB
  DZCAODZCMNALFGKHPQQPAOFIGJ $.

$( Day 18.  It is probable that ` ph ` is equivalent to the assertion that
   ` ph ` is provable if and only if it is provable that ` ph ` is equivalent
   to anything that is provable. $)
equivb $p |- ( []. ( ph <-> []. ph ) <-> []. ( ph <-> T. ) ) $=
  ( cbox wb wi dfbi2 monbirule distrconj bitri ax-gl simplbiim pm5.1 monimpconj
  wtru wa axk4 mpdan impbii tbtru ) AABZCZBZSAMCZBUASUAASDZBZSADZBZSUAUCUENZBUD
  UFNTUGASEFUCUEGHAIJSSBUAAOASTASKLPQAUBARFH $.

$( Day 19. It is provable that ` ph ` is equivalent to the assertion that
   ` ph ` is consistent with PA if and only if it is provable that ` ph ` is
   equivalent to anything that is disprovable. $)
equivbcor $p |- ( []. ( ph <-> <>. ph ) <-> []. ( ph <-> F. ) ) $=
  ( cdiam wb cbox wn wtru wfal notbi biid con1bii df-diam xchnxbir bibi2i bitri
  monbirule equivb df-fal con2bii bitr4i ) AABZCZDZAEZFCZDZAGCZDUBUCUCDZCZDUEUA
  UHUAUCTEZCUHATHUIUGUCUGEZUGTUGUJUJIJAKLMNOUCPNUDUFUDUCGEZCUFFUKUCGFQRMAGHSON
  $.

$( Day 20.  Formula ` []. ph -> ph ` is called the reflection principle for
   ` ph ` , in particular, ~ ax-gl means that ` ph ` is provable if the
   reflection principle for ` ph ` is provable.  The following result means
   that there's no single reflection principle which implies
   ` -. []. []. F. ` .  See Boolos p. 63 for more context. $)
norefl $p |- ( []. ( ( []. ph -> ph ) -> -. []. []. F. ) -> []. []. F. ) $=
  ( cbox wi wfal jarl jarr jca monrule distrconj axk4 ax-distrb syl con4 pm3.34
  wn wa cdiam notnotr con3i 3syl df-diam biimpri kurbis syl6 monimpconj syl2anr
  sylbi ax-gl ) ABZACDBZBZOZCZBUIOULCZAULCZPZBZUKUJCZBZUKUMUPUMUNUOUIAULEUIAULF
  GHUQUNBZUOBZPUSUNUOIVAUIULBZCZBZUKUICZBUSUTVAVABVDUOJVAVCAULKHLUNVEUIUKMHVCVE
  URVCVEPUKVBUJUKUIVBNVBUJOZOZBZOZBVFQZBUJULVIVHUKVGUJUJRHSHVIVJVJVIVFUAUBHVFDU
  CTUDUEUFUGUJUHT $.

$c [.] $.

$( If ` ph ` is a wff, then ` [.] ph ` is a wff. $)
cdbox $a wff [.] ph $.

$( The definition of the "dotted box" ` [.] ` in terms of ` []. ` .  This
   definition makes sense, since ` []. ph -> ph ` is not, in general, a
   theorem of GL. $)
df-dbox $a |- ( [.] ph <-> ( []. ph /\ ph ) ) $.

$( The following five results prove some properties of the dotted box. One can use ~ axk4 but not ~ ax-gl in the proofs. $)

$( Day 21. $)
dbbeqb $p |- ( [.] []. ph <-> []. ph ) $=
  ( cbox cdbox df-dbox simprbi axk4 id sylanbrc impbii ) ABZCZJKJBZJJDZEJLJKAFJ
  GMHI $.

$( Day 22. $)
dbbeqbdb $p |- ( [.] []. ph <-> []. [.] ph ) $=
  ( cbox wa cdbox distrconj df-dbox monbirule 3bitr4ri ) ABZACZBIBICADZBIDIAEKJ
  AFGIFH $.

$( Day 23. $)
dbeqdbdb $p |- ( [.] ph <-> [.] [.] ph ) $=
  ( cdbox cbox wa df-dbox dbbeqbdb dbbeqb bitr3i anbi12i sylbbr anabss5 simprbi
  sylbi impbii ) ABZOBZOACZADZPAEZQAPPOCZODQRDOEZTQORTQBQAFAGHSIJKMPTOUALN $.

${
  dbimp.1 $e |- ( [.] ph -> ps ) $.
  $( Day 24a. $)
  dbimp1 $p |- ( []. ph -> []. ps ) $=
    ( cdbox wi cbox ax-necess ax-distrb wa df-dbox biimpri monrule distrconj wn
    imnan axk4 pm2.21 nsyl5 ja sylbir sylnbi ax-1 mp2b ) ADZBEZFUDFZBFZEAFZUGEZ
    UECGUDBHUFUGUIUHAIZFZUFUIUJUDUDUJAJKLUKUHFZUHIZUIUHAMUMNULUHNZEUIULUHOULUNU
    IUHULUIAPUHUGQZRUOSTUARUGUHUBSUC $.

  $( Day 24b. $)
  dbimp2 $p |- ( [.] ph -> [.] ps ) $=
    ( cbox wa cdbox dbimp1 adantr df-dbox sylbir jca 3imtr4i ) ADZAEZBDZBEAFZBF
    NOBMOAABCGHNPBAIZCJKQBIL $.
$}

$( Day 25a.  Lemma for ~ puzzle . $)
puzzlelem $p |- ( [.] ( [.] ( ph -> [.] ph ) -> ph ) -> []. ( ph -> [.] ph ) ) $=
  ( cdbox wi cbox wa df-dbox biimpi axk4 dbimp1 ax-distrb syl5 monrule simplbi2
  id imim2i 3syl adantr ax-gl ) AABZCZBZACZBZUBDZUBEZTDZTCZDZUFUCUEUBFGUDUHUBUD
  UDDUFADZCZDUHUBHUDUJUFUADUDUITUAUANIUAAJKLUJUGUITUFSUIAAFMOLPQTRP $.

$( Day 25b.  A puzzle from Boolos' book, see p. 164 for a solution. $)
puzzle $p |- ( [.] ( [.] ( ph -> [.] ph ) -> ph ) -> ph ) $=
  ( cdbox wi cbox puzzlelem df-dbox wa biimtrrid expd peirce syl6 simplbiim mpd
  id ) AABZCZBZACZBZPDZAAESRDRTACRFRTPACARTPATPGQRAPFRNHIAOJKLM $.
