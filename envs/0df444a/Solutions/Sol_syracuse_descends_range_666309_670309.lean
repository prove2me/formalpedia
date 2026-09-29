-- Prove2me | solution 1 for syracuse_descends_range_666309_670309
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:04:51.438447+00:00
-- url     : https://prove2.me/submissions/c34a5d49-ce0f-48a8-ac1f-472c8af4ca51

import Mathlib
import Definitions.Def_syracuseStep

set_option maxHeartbeats 1000000

open Nat

/-- Half of all odd numbers descend in a single Syracuse step, uniformly. -/
theorem step_lt_of_one_mod_four (m : ℕ) (h1 : 1 < m) (h4 : m % 4 = 1) : syracuseStep m < m := by
  have hne : 3 * m + 1 ≠ 0 := by omega
  have hdvd : (2:ℕ) ^ 2 ∣ 3 * m + 1 := by
    have : (4:ℕ) ∣ 3 * m + 1 := by omega
    simpa using this
  have hle : 2 ≤ (3 * m + 1).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).mp hdvd
  have hpow : (2:ℕ) ^ 2 ≤ 2 ^ ((3 * m + 1).factorization 2) :=
    Nat.pow_le_pow_right (by norm_num) hle
  have h1' : syracuseStep m ≤ (3 * m + 1) / 2 ^ 2 := by
    show ordCompl[2] (3 * m + 1) ≤ _
    exact Nat.div_le_div_left hpow (by positivity)
  have h2' : (3 * m + 1) / 2 ^ 2 < m := by
    apply Nat.div_lt_of_lt_mul
    omega
  omega

/-- `Blo L x` : some Syracuse iterate of `x` drops below `L`. -/
abbrev Blo (L x : ℕ) : Prop := ∃ t : ℕ, syracuseStep^[t] x < L

theorem bbase {L x y : ℕ} (h : syracuseStep x = y) (hy : y < L) : Blo L x :=
  ⟨1, by rw [Function.iterate_one, h]; exact hy⟩

theorem bstep {L x y : ℕ} (h : syracuseStep x = y) (hy : Blo L y) : Blo L x := by
  obtain ⟨t, ht⟩ := hy
  exact ⟨t + 1, by rw [Function.iterate_add_apply, Function.iterate_one, h]; exact ht⟩

theorem se (a : ℕ) {y z : ℕ} (h : 3 * y + 1 = 2 ^ a * z) (hz : Odd z) :
    syracuseStep y = z := by
  have hz0 : z ≠ 0 := by rintro rfl; simp [Nat.odd_iff] at hz
  have hfac : (3 * y + 1).factorization 2 = a := by
    rw [h, Nat.factorization_mul (by positivity) hz0]
    simp [Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by rwa [Nat.two_dvd_ne_zero, ← Nat.odd_iff])]
  show ordCompl[2] (3 * y + 1) = z
  rw [hfac, h, Nat.mul_div_cancel_left _ (by positivity)]


theorem B753673 : Blo 666309 753673 := bbase (se 2 (by rfl) ⟨282627, by rfl⟩ : syracuseStep 753673 = 565255) (by norm_num)
theorem B1507373 : Blo 666309 1507373 := bbase (se 3 (by rfl) ⟨282632, by rfl⟩ : syracuseStep 1507373 = 565265) (by norm_num)
theorem B753709 : Blo 666309 753709 := bbase (se 3 (by rfl) ⟨141320, by rfl⟩ : syracuseStep 753709 = 282641) (by norm_num)
theorem B753745 : Blo 666309 753745 := bbase (se 2 (by rfl) ⟨282654, by rfl⟩ : syracuseStep 753745 = 565309) (by norm_num)
theorem B1802341 : Blo 666309 1802341 := bbase (se 4 (by rfl) ⟨168969, by rfl⟩ : syracuseStep 1802341 = 337939) (by norm_num)
theorem B1507445 : Blo 666309 1507445 := bbase (se 5 (by rfl) ⟨70661, by rfl⟩ : syracuseStep 1507445 = 141323) (by norm_num)
theorem B753781 : Blo 666309 753781 := bbase (se 5 (by rfl) ⟨35333, by rfl⟩ : syracuseStep 753781 = 70667) (by norm_num)
theorem B2261141 : Blo 666309 2261141 := bbase (se 6 (by rfl) ⟨52995, by rfl⟩ : syracuseStep 2261141 = 105991) (by norm_num)
theorem B753817 : Blo 666309 753817 := bbase (se 2 (by rfl) ⟨282681, by rfl⟩ : syracuseStep 753817 = 565363) (by norm_num)
theorem B3375269 : Blo 666309 3375269 := bbase (se 4 (by rfl) ⟨316431, by rfl⟩ : syracuseStep 3375269 = 632863) (by norm_num)
theorem B1900709 : Blo 666309 1900709 := bbase (se 4 (by rfl) ⟨178191, by rfl⟩ : syracuseStep 1900709 = 356383) (by norm_num)
theorem B1507517 : Blo 666309 1507517 := bbase (se 3 (by rfl) ⟨282659, by rfl⟩ : syracuseStep 1507517 = 565319) (by norm_num)
theorem B753853 : Blo 666309 753853 := bbase (se 3 (by rfl) ⟨141347, by rfl⟩ : syracuseStep 753853 = 282695) (by norm_num)
theorem B753889 : Blo 666309 753889 := bbase (se 2 (by rfl) ⟨282708, by rfl⟩ : syracuseStep 753889 = 565417) (by norm_num)
theorem B1507589 : Blo 666309 1507589 := bbase (se 4 (by rfl) ⟨141336, by rfl⟩ : syracuseStep 1507589 = 282673) (by norm_num)
theorem B753925 : Blo 666309 753925 := bbase (se 4 (by rfl) ⟨70680, by rfl⟩ : syracuseStep 753925 = 141361) (by norm_num)
theorem B753961 : Blo 666309 753961 := bbase (se 2 (by rfl) ⟨282735, by rfl⟩ : syracuseStep 753961 = 565471) (by norm_num)
theorem B1507661 : Blo 666309 1507661 := bbase (se 3 (by rfl) ⟨282686, by rfl⟩ : syracuseStep 1507661 = 565373) (by norm_num)
theorem B753997 : Blo 666309 753997 := bbase (se 3 (by rfl) ⟨141374, by rfl⟩ : syracuseStep 753997 = 282749) (by norm_num)
theorem B754033 : Blo 666309 754033 := bbase (se 2 (by rfl) ⟨282762, by rfl⟩ : syracuseStep 754033 = 565525) (by norm_num)
theorem B1507733 : Blo 666309 1507733 := bbase (se 6 (by rfl) ⟨35337, by rfl⟩ : syracuseStep 1507733 = 70675) (by norm_num)
theorem B754069 : Blo 666309 754069 := bbase (se 6 (by rfl) ⟨17673, by rfl⟩ : syracuseStep 754069 = 35347) (by norm_num)
theorem B1507805 : Blo 666309 1507805 := bbase (se 3 (by rfl) ⟨282713, by rfl⟩ : syracuseStep 1507805 = 565427) (by norm_num)
theorem B2851301 : Blo 666309 2851301 := bbase (se 4 (by rfl) ⟨267309, by rfl⟩ : syracuseStep 2851301 = 534619) (by norm_num)
theorem B1507877 : Blo 666309 1507877 := bbase (se 4 (by rfl) ⟨141363, by rfl⟩ : syracuseStep 1507877 = 282727) (by norm_num)
theorem B2261573 : Blo 666309 2261573 := bbase (se 4 (by rfl) ⟨212022, by rfl⟩ : syracuseStep 2261573 = 424045) (by norm_num)
theorem B1901141 : Blo 666309 1901141 := bbase (se 8 (by rfl) ⟨11139, by rfl⟩ : syracuseStep 1901141 = 22279) (by norm_num)
theorem B1507949 : Blo 666309 1507949 := bbase (se 3 (by rfl) ⟨282740, by rfl⟩ : syracuseStep 1507949 = 565481) (by norm_num)
theorem B1508021 : Blo 666309 1508021 := bbase (se 5 (by rfl) ⟨70688, by rfl⟩ : syracuseStep 1508021 = 141377) (by norm_num)
theorem B1508093 : Blo 666309 1508093 := bbase (se 3 (by rfl) ⟨282767, by rfl⟩ : syracuseStep 1508093 = 565535) (by norm_num)
theorem B1508165 : Blo 666309 1508165 := bbase (se 4 (by rfl) ⟨141390, by rfl⟩ : syracuseStep 1508165 = 282781) (by norm_num)
theorem B1016693 : Blo 666309 1016693 := bbase (se 5 (by rfl) ⟨47657, by rfl⟩ : syracuseStep 1016693 = 95315) (by norm_num)
theorem B1835909 : Blo 666309 1835909 := bbase (se 4 (by rfl) ⟨172116, by rfl⟩ : syracuseStep 1835909 = 344233) (by norm_num)
theorem B1606549 : Blo 666309 1606549 := bbase (se 6 (by rfl) ⟨37653, by rfl⟩ : syracuseStep 1606549 = 75307) (by norm_num)
theorem B721841 : Blo 666309 721841 := bbase (se 2 (by rfl) ⟨270690, by rfl⟩ : syracuseStep 721841 = 541381) (by norm_num)
theorem B951277 : Blo 666309 951277 := bbase (se 3 (by rfl) ⟨178364, by rfl⟩ : syracuseStep 951277 = 356729) (by norm_num)
theorem B2262005 : Blo 666309 2262005 := bbase (se 5 (by rfl) ⟨106031, by rfl⟩ : syracuseStep 2262005 = 212063) (by norm_num)
theorem B5407829 : Blo 666309 5407829 := bbase (se 8 (by rfl) ⟨31686, by rfl⟩ : syracuseStep 5407829 = 63373) (by norm_num)
theorem B1901893 : Blo 666309 1901893 := bbase (se 4 (by rfl) ⟨178302, by rfl⟩ : syracuseStep 1901893 = 356605) (by norm_num)
theorem B3376565 : Blo 666309 3376565 := bbase (se 5 (by rfl) ⟨158276, by rfl⟩ : syracuseStep 3376565 = 316553) (by norm_num)
theorem B2852293 : Blo 666309 2852293 := bbase (se 4 (by rfl) ⟨267402, by rfl⟩ : syracuseStep 2852293 = 534805) (by norm_num)
theorem B1607165 : Blo 666309 1607165 := bbase (se 3 (by rfl) ⟨301343, by rfl⟩ : syracuseStep 1607165 = 602687) (by norm_num)
theorem B951869 : Blo 666309 951869 := bbase (se 3 (by rfl) ⟨178475, by rfl⟩ : syracuseStep 951869 = 356951) (by norm_num)
theorem B722525 : Blo 666309 722525 := bbase (se 3 (by rfl) ⟨135473, by rfl⟩ : syracuseStep 722525 = 270947) (by norm_num)
theorem B951949 : Blo 666309 951949 := bbase (se 3 (by rfl) ⟨178490, by rfl⟩ : syracuseStep 951949 = 356981) (by norm_num)
theorem B1607357 : Blo 666309 1607357 := bbase (se 3 (by rfl) ⟨301379, by rfl⟩ : syracuseStep 1607357 = 602759) (by norm_num)
theorem B952069 : Blo 666309 952069 := bbase (se 4 (by rfl) ⟨89256, by rfl⟩ : syracuseStep 952069 = 178513) (by norm_num)
theorem B952165 : Blo 666309 952165 := bbase (se 4 (by rfl) ⟨89265, by rfl⟩ : syracuseStep 952165 = 178531) (by norm_num)
theorem B5146517 : Blo 666309 5146517 := bbase (se 6 (by rfl) ⟨120621, by rfl⟩ : syracuseStep 5146517 = 241243) (by norm_num)
theorem B2754485 : Blo 666309 2754485 := bbase (se 5 (by rfl) ⟨129116, by rfl⟩ : syracuseStep 2754485 = 258233) (by norm_num)
theorem B1607933 : Blo 666309 1607933 := bbase (se 3 (by rfl) ⟨301487, by rfl⟩ : syracuseStep 1607933 = 602975) (by norm_num)
theorem B1018117 : Blo 666309 1018117 := bbase (se 4 (by rfl) ⟨95448, by rfl⟩ : syracuseStep 1018117 = 190897) (by norm_num)
theorem B952661 : Blo 666309 952661 := bbase (se 10 (by rfl) ⟨1395, by rfl⟩ : syracuseStep 952661 = 2791) (by norm_num)
theorem B1018421 : Blo 666309 1018421 := bbase (se 5 (by rfl) ⟨47738, by rfl⟩ : syracuseStep 1018421 = 95477) (by norm_num)
theorem B1608317 : Blo 666309 1608317 := bbase (se 3 (by rfl) ⟨301559, by rfl⟩ : syracuseStep 1608317 = 603119) (by norm_num)
theorem B723601 : Blo 666309 723601 := bbase (se 2 (by rfl) ⟨271350, by rfl⟩ : syracuseStep 723601 = 542701) (by norm_num)
theorem B7244437 : Blo 666309 7244437 := bbase (se 6 (by rfl) ⟨169791, by rfl⟩ : syracuseStep 7244437 = 339583) (by norm_num)
theorem B3377861 : Blo 666309 3377861 := bbase (se 4 (by rfl) ⟨316674, by rfl⟩ : syracuseStep 3377861 = 633349) (by norm_num)
theorem B1805141 : Blo 666309 1805141 := bbase (se 9 (by rfl) ⟨5288, by rfl⟩ : syracuseStep 1805141 = 10577) (by norm_num)
theorem B953213 : Blo 666309 953213 := bbase (se 3 (by rfl) ⟨178727, by rfl⟩ : syracuseStep 953213 = 357455) (by norm_num)
theorem B854921 : Blo 666309 854921 := bbase (se 2 (by rfl) ⟨320595, by rfl⟩ : syracuseStep 854921 = 641191) (by norm_num)
theorem B5082101 : Blo 666309 5082101 := bbase (se 5 (by rfl) ⟨238223, by rfl⟩ : syracuseStep 5082101 = 476447) (by norm_num)
theorem B5704789 : Blo 666309 5704789 := bbase (se 8 (by rfl) ⟨33426, by rfl⟩ : syracuseStep 5704789 = 66853) (by norm_num)
theorem B953965 : Blo 666309 953965 := bbase (se 3 (by rfl) ⟨178868, by rfl⟩ : syracuseStep 953965 = 357737) (by norm_num)
theorem B3214981 : Blo 666309 3214981 := bbase (se 4 (by rfl) ⟨301404, by rfl⟩ : syracuseStep 3214981 = 602809) (by norm_num)
theorem B3051173 : Blo 666309 3051173 := bbase (se 4 (by rfl) ⟨286047, by rfl⟩ : syracuseStep 3051173 = 572095) (by norm_num)
theorem B3379157 : Blo 666309 3379157 := bbase (se 7 (by rfl) ⟨39599, by rfl⟩ : syracuseStep 3379157 = 79199) (by norm_num)
theorem B1904741 : Blo 666309 1904741 := bbase (se 4 (by rfl) ⟨178569, by rfl⟩ : syracuseStep 1904741 = 357139) (by norm_num)
theorem B7213205 : Blo 666309 7213205 := bbase (se 6 (by rfl) ⟨169059, by rfl⟩ : syracuseStep 7213205 = 338119) (by norm_num)
theorem B6426773 : Blo 666309 6426773 := bbase (se 6 (by rfl) ⟨150627, by rfl⟩ : syracuseStep 6426773 = 301255) (by norm_num)
theorem B1610077 : Blo 666309 1610077 := bbase (se 3 (by rfl) ⟨301889, by rfl⟩ : syracuseStep 1610077 = 603779) (by norm_num)
theorem B1282565 : Blo 666309 1282565 := bbase (se 4 (by rfl) ⟨120240, by rfl⟩ : syracuseStep 1282565 = 240481) (by norm_num)
theorem B1282645 : Blo 666309 1282645 := bbase (se 8 (by rfl) ⟨7515, by rfl⟩ : syracuseStep 1282645 = 15031) (by norm_num)
theorem B1217173 : Blo 666309 1217173 := bbase (se 6 (by rfl) ⟨28527, by rfl⟩ : syracuseStep 1217173 = 57055) (by norm_num)
theorem B3805973 : Blo 666309 3805973 := bbase (se 6 (by rfl) ⟨89202, by rfl⟩ : syracuseStep 3805973 = 178405) (by norm_num)
theorem B5706773 : Blo 666309 5706773 := bbase (se 6 (by rfl) ⟨133752, by rfl⟩ : syracuseStep 5706773 = 267505) (by norm_num)
theorem B3380453 : Blo 666309 3380453 := bbase (se 4 (by rfl) ⟨316917, by rfl⟩ : syracuseStep 3380453 = 633835) (by norm_num)
theorem B1905925 : Blo 666309 1905925 := bbase (se 4 (by rfl) ⟨178680, by rfl⟩ : syracuseStep 1905925 = 357361) (by norm_num)
theorem B1906085 : Blo 666309 1906085 := bbase (se 4 (by rfl) ⟨178695, by rfl⟩ : syracuseStep 1906085 = 357391) (by norm_num)
theorem B1218053 : Blo 666309 1218053 := bbase (se 4 (by rfl) ⟨114192, by rfl⟩ : syracuseStep 1218053 = 228385) (by norm_num)
theorem B1906325 : Blo 666309 1906325 := bbase (se 6 (by rfl) ⟨44679, by rfl⟩ : syracuseStep 1906325 = 89359) (by norm_num)
theorem B1906517 : Blo 666309 1906517 := bbase (se 9 (by rfl) ⟨5585, by rfl⟩ : syracuseStep 1906517 = 11171) (by norm_num)
theorem B759889 : Blo 666309 759889 := bbase (se 2 (by rfl) ⟨284958, by rfl⟩ : syracuseStep 759889 = 569917) (by norm_num)
theorem B792749 : Blo 666309 792749 := bbase (se 3 (by rfl) ⟨148640, by rfl⟩ : syracuseStep 792749 = 297281) (by norm_num)
theorem B2857301 : Blo 666309 2857301 := bbase (se 10 (by rfl) ⟨4185, by rfl⟩ : syracuseStep 2857301 = 8371) (by norm_num)
theorem B3381749 : Blo 666309 3381749 := bbase (se 5 (by rfl) ⟨158519, by rfl⟩ : syracuseStep 3381749 = 317039) (by norm_num)
theorem B760313 : Blo 666309 760313 := bbase (se 2 (by rfl) ⟨285117, by rfl⟩ : syracuseStep 760313 = 570235) (by norm_num)
theorem B2136581 : Blo 666309 2136581 := bbase (se 4 (by rfl) ⟨200304, by rfl⟩ : syracuseStep 2136581 = 400609) (by norm_num)
theorem B2857589 : Blo 666309 2857589 := bbase (se 5 (by rfl) ⟨133949, by rfl⟩ : syracuseStep 2857589 = 267899) (by norm_num)
theorem B1907509 : Blo 666309 1907509 := bbase (se 5 (by rfl) ⟨89414, by rfl⟩ : syracuseStep 1907509 = 178829) (by norm_num)
theorem B7609301 : Blo 666309 7609301 := bbase (se 7 (by rfl) ⟨89171, by rfl⟩ : syracuseStep 7609301 = 178343) (by norm_num)
theorem B760801 : Blo 666309 760801 := bbase (se 2 (by rfl) ⟨285300, by rfl⟩ : syracuseStep 760801 = 570601) (by norm_num)
theorem B2137349 : Blo 666309 2137349 := bbase (se 4 (by rfl) ⟨200376, by rfl⟩ : syracuseStep 2137349 = 400753) (by norm_num)
theorem B2858341 : Blo 666309 2858341 := bbase (se 4 (by rfl) ⟨267969, by rfl⟩ : syracuseStep 2858341 = 535939) (by norm_num)
theorem B2530709 : Blo 666309 2530709 := bbase (se 6 (by rfl) ⟨59313, by rfl⟩ : syracuseStep 2530709 = 118627) (by norm_num)
theorem B3612053 : Blo 666309 3612053 := bbase (se 6 (by rfl) ⟨84657, by rfl⟩ : syracuseStep 3612053 = 169315) (by norm_num)
theorem B1285645 : Blo 666309 1285645 := bbase (se 3 (by rfl) ⟨241058, by rfl⟩ : syracuseStep 1285645 = 482117) (by norm_num)
theorem B1351309 : Blo 666309 1351309 := bbase (se 3 (by rfl) ⟨253370, by rfl⟩ : syracuseStep 1351309 = 506741) (by norm_num)
theorem B2530997 : Blo 666309 2530997 := bbase (se 5 (by rfl) ⟨118640, by rfl⟩ : syracuseStep 2530997 = 237281) (by norm_num)
theorem B3219173 : Blo 666309 3219173 := bbase (se 4 (by rfl) ⟨301797, by rfl⟩ : syracuseStep 3219173 = 603595) (by norm_num)
theorem B2137861 : Blo 666309 2137861 := bbase (se 4 (by rfl) ⟨200424, by rfl⟩ : syracuseStep 2137861 = 400849) (by norm_num)
theorem B3383045 : Blo 666309 3383045 := bbase (se 4 (by rfl) ⟨317160, by rfl⟩ : syracuseStep 3383045 = 634321) (by norm_num)
theorem B761717 : Blo 666309 761717 := bbase (se 5 (by rfl) ⟨35705, by rfl⟩ : syracuseStep 761717 = 71411) (by norm_num)
theorem B1810309 : Blo 666309 1810309 := bbase (se 4 (by rfl) ⟨169716, by rfl⟩ : syracuseStep 1810309 = 339433) (by norm_num)
theorem B1908613 : Blo 666309 1908613 := bbase (se 4 (by rfl) ⟨178932, by rfl⟩ : syracuseStep 1908613 = 357865) (by norm_num)
theorem B1712141 : Blo 666309 1712141 := bbase (se 3 (by rfl) ⟨321026, by rfl⟩ : syracuseStep 1712141 = 642053) (by norm_num)
theorem B2859077 : Blo 666309 2859077 := bbase (se 4 (by rfl) ⟨268038, by rfl⟩ : syracuseStep 2859077 = 536077) (by norm_num)
theorem B1351829 : Blo 666309 1351829 := bbase (se 6 (by rfl) ⟨31683, by rfl⟩ : syracuseStep 1351829 = 63367) (by norm_num)
theorem B2564885 : Blo 666309 2564885 := bbase (se 6 (by rfl) ⟨60114, by rfl⟩ : syracuseStep 2564885 = 120229) (by norm_num)
theorem B2532181 : Blo 666309 2532181 := bbase (se 9 (by rfl) ⟨7418, by rfl⟩ : syracuseStep 2532181 = 14837) (by norm_num)
theorem B6595445 : Blo 666309 6595445 := bbase (se 5 (by rfl) ⟨309161, by rfl⟩ : syracuseStep 6595445 = 618323) (by norm_num)
theorem B3384341 : Blo 666309 3384341 := bbase (se 6 (by rfl) ⟨79320, by rfl⟩ : syracuseStep 3384341 = 158641) (by norm_num)
theorem B2532485 : Blo 666309 2532485 := bbase (se 4 (by rfl) ⟨237420, by rfl⟩ : syracuseStep 2532485 = 474841) (by norm_num)
theorem B2172149 : Blo 666309 2172149 := bbase (se 5 (by rfl) ⟨101819, by rfl⟩ : syracuseStep 2172149 = 203639) (by norm_num)
theorem B1353053 : Blo 666309 1353053 := bbase (se 3 (by rfl) ⟨253697, by rfl⟩ : syracuseStep 1353053 = 507395) (by norm_num)
theorem B2139605 : Blo 666309 2139605 := bbase (se 7 (by rfl) ⟨25073, by rfl⟩ : syracuseStep 2139605 = 50147) (by norm_num)
theorem B2139797 : Blo 666309 2139797 := bbase (se 6 (by rfl) ⟨50151, by rfl⟩ : syracuseStep 2139797 = 100303) (by norm_num)
theorem B1288045 : Blo 666309 1288045 := bbase (se 3 (by rfl) ⟨241508, by rfl⟩ : syracuseStep 1288045 = 483017) (by norm_num)
theorem B1353613 : Blo 666309 1353613 := bbase (se 3 (by rfl) ⟨253802, by rfl⟩ : syracuseStep 1353613 = 507605) (by norm_num)
theorem B763961 : Blo 666309 763961 := bbase (se 2 (by rfl) ⟨286485, by rfl⟩ : syracuseStep 763961 = 572971) (by norm_num)
theorem B1124509 : Blo 666309 1124509 := bbase (se 3 (by rfl) ⟨210845, by rfl⟩ : syracuseStep 1124509 = 421691) (by norm_num)
theorem B1124597 : Blo 666309 1124597 := bbase (se 5 (by rfl) ⟨52715, by rfl⟩ : syracuseStep 1124597 = 105431) (by norm_num)
theorem B3385637 : Blo 666309 3385637 := bbase (se 4 (by rfl) ⟨317403, by rfl⟩ : syracuseStep 3385637 = 634807) (by norm_num)
theorem B1124725 : Blo 666309 1124725 := bbase (se 5 (by rfl) ⟨52721, by rfl⟩ : syracuseStep 1124725 = 105443) (by norm_num)
theorem B1354133 : Blo 666309 1354133 := bbase (se 6 (by rfl) ⟨31737, by rfl⟩ : syracuseStep 1354133 = 63475) (by norm_num)
theorem B1124813 : Blo 666309 1124813 := bbase (se 3 (by rfl) ⟨210902, by rfl⟩ : syracuseStep 1124813 = 421805) (by norm_num)
theorem B2599445 : Blo 666309 2599445 := bbase (se 6 (by rfl) ⟨60924, by rfl⟩ : syracuseStep 2599445 = 121849) (by norm_num)
theorem B1124941 : Blo 666309 1124941 := bbase (se 3 (by rfl) ⟨210926, by rfl⟩ : syracuseStep 1124941 = 421853) (by norm_num)
theorem B5089877 : Blo 666309 5089877 := bbase (se 8 (by rfl) ⟨29823, by rfl⟩ : syracuseStep 5089877 = 59647) (by norm_num)
theorem B1125029 : Blo 666309 1125029 := bbase (se 4 (by rfl) ⟨105471, by rfl⟩ : syracuseStep 1125029 = 210943) (by norm_num)
theorem B1288901 : Blo 666309 1288901 := bbase (se 4 (by rfl) ⟨120834, by rfl⟩ : syracuseStep 1288901 = 241669) (by norm_num)
theorem B1125157 : Blo 666309 1125157 := bbase (se 4 (by rfl) ⟨105483, by rfl⟩ : syracuseStep 1125157 = 210967) (by norm_num)
theorem B1125245 : Blo 666309 1125245 := bbase (se 3 (by rfl) ⟨210983, by rfl⟩ : syracuseStep 1125245 = 421967) (by norm_num)
theorem B1125373 : Blo 666309 1125373 := bbase (se 3 (by rfl) ⟨211007, by rfl⟩ : syracuseStep 1125373 = 422015) (by norm_num)
theorem B1354781 : Blo 666309 1354781 := bbase (se 3 (by rfl) ⟨254021, by rfl⟩ : syracuseStep 1354781 = 508043) (by norm_num)
theorem B1125461 : Blo 666309 1125461 := bbase (se 8 (by rfl) ⟨6594, by rfl⟩ : syracuseStep 1125461 = 13189) (by norm_num)
theorem B1715341 : Blo 666309 1715341 := bbase (se 3 (by rfl) ⟨321626, by rfl⟩ : syracuseStep 1715341 = 643253) (by norm_num)
theorem B2534597 : Blo 666309 2534597 := bbase (se 4 (by rfl) ⟨237618, by rfl⟩ : syracuseStep 2534597 = 475237) (by norm_num)
theorem B1125589 : Blo 666309 1125589 := bbase (se 7 (by rfl) ⟨13190, by rfl⟩ : syracuseStep 1125589 = 26381) (by norm_num)
theorem B2862373 : Blo 666309 2862373 := bbase (se 4 (by rfl) ⟨268347, by rfl⟩ : syracuseStep 2862373 = 536695) (by norm_num)
theorem B1125677 : Blo 666309 1125677 := bbase (se 3 (by rfl) ⟨211064, by rfl⟩ : syracuseStep 1125677 = 422129) (by norm_num)
theorem B1125805 : Blo 666309 1125805 := bbase (se 3 (by rfl) ⟨211088, by rfl⟩ : syracuseStep 1125805 = 422177) (by norm_num)
theorem B1224157 : Blo 666309 1224157 := bbase (se 3 (by rfl) ⟨229529, by rfl⟩ : syracuseStep 1224157 = 459059) (by norm_num)
theorem B2534885 : Blo 666309 2534885 := bbase (se 4 (by rfl) ⟨237645, by rfl⟩ : syracuseStep 2534885 = 475291) (by norm_num)
theorem B1125893 : Blo 666309 1125893 := bbase (se 4 (by rfl) ⟨105552, by rfl⟩ : syracuseStep 1125893 = 211105) (by norm_num)
theorem B3386933 : Blo 666309 3386933 := bbase (se 5 (by rfl) ⟨158762, by rfl⟩ : syracuseStep 3386933 = 317525) (by norm_num)
theorem B1126021 : Blo 666309 1126021 := bbase (se 4 (by rfl) ⟨105564, by rfl⟩ : syracuseStep 1126021 = 211129) (by norm_num)
theorem B1126109 : Blo 666309 1126109 := bbase (se 3 (by rfl) ⟨211145, by rfl⟩ : syracuseStep 1126109 = 422291) (by norm_num)
theorem B3092213 : Blo 666309 3092213 := bbase (se 5 (by rfl) ⟨144947, by rfl⟩ : syracuseStep 3092213 = 289895) (by norm_num)
theorem B1126237 : Blo 666309 1126237 := bbase (se 3 (by rfl) ⟨211169, by rfl⟩ : syracuseStep 1126237 = 422339) (by norm_num)
theorem B1126325 : Blo 666309 1126325 := bbase (se 5 (by rfl) ⟨52796, by rfl⟩ : syracuseStep 1126325 = 105593) (by norm_num)
theorem B1126453 : Blo 666309 1126453 := bbase (se 5 (by rfl) ⟨52802, by rfl⟩ : syracuseStep 1126453 = 105605) (by norm_num)
theorem B1126541 : Blo 666309 1126541 := bbase (se 3 (by rfl) ⟨211226, by rfl⟩ : syracuseStep 1126541 = 422453) (by norm_num)
theorem B1355933 : Blo 666309 1355933 := bbase (se 3 (by rfl) ⟨254237, by rfl⟩ : syracuseStep 1355933 = 508475) (by norm_num)
theorem B1126669 : Blo 666309 1126669 := bbase (se 3 (by rfl) ⟨211250, by rfl⟩ : syracuseStep 1126669 = 422501) (by norm_num)
theorem B1126757 : Blo 666309 1126757 := bbase (se 4 (by rfl) ⟨105633, by rfl⟩ : syracuseStep 1126757 = 211267) (by norm_num)
theorem B5419477 : Blo 666309 5419477 := bbase (se 7 (by rfl) ⟨63509, by rfl⟩ : syracuseStep 5419477 = 127019) (by norm_num)
theorem B1126885 : Blo 666309 1126885 := bbase (se 4 (by rfl) ⟨105645, by rfl⟩ : syracuseStep 1126885 = 211291) (by norm_num)
theorem B1126973 : Blo 666309 1126973 := bbase (se 3 (by rfl) ⟨211307, by rfl⟩ : syracuseStep 1126973 = 422615) (by norm_num)
theorem B2536069 : Blo 666309 2536069 := bbase (se 4 (by rfl) ⟨237756, by rfl⟩ : syracuseStep 2536069 = 475513) (by norm_num)
theorem B3814037 : Blo 666309 3814037 := bbase (se 6 (by rfl) ⟨89391, by rfl⟩ : syracuseStep 3814037 = 178783) (by norm_num)
theorem B1127101 : Blo 666309 1127101 := bbase (se 3 (by rfl) ⟨211331, by rfl⟩ : syracuseStep 1127101 = 422663) (by norm_num)
theorem B1127189 : Blo 666309 1127189 := bbase (se 6 (by rfl) ⟨26418, by rfl⟩ : syracuseStep 1127189 = 52837) (by norm_num)
theorem B3388229 : Blo 666309 3388229 := bbase (se 4 (by rfl) ⟨317646, by rfl⟩ : syracuseStep 3388229 = 635293) (by norm_num)
theorem B1127317 : Blo 666309 1127317 := bbase (se 6 (by rfl) ⟨26421, by rfl⟩ : syracuseStep 1127317 = 52843) (by norm_num)
theorem B2536373 : Blo 666309 2536373 := bbase (se 5 (by rfl) ⟨118892, by rfl⟩ : syracuseStep 2536373 = 237785) (by norm_num)
theorem B1127405 : Blo 666309 1127405 := bbase (se 3 (by rfl) ⟨211388, by rfl⟩ : syracuseStep 1127405 = 422777) (by norm_num)
theorem B1127533 : Blo 666309 1127533 := bbase (se 3 (by rfl) ⟨211412, by rfl⟩ : syracuseStep 1127533 = 422825) (by norm_num)
theorem B2143397 : Blo 666309 2143397 := bbase (se 4 (by rfl) ⟨200943, by rfl⟩ : syracuseStep 2143397 = 401887) (by norm_num)
theorem B1127621 : Blo 666309 1127621 := bbase (se 4 (by rfl) ⟨105714, by rfl⟩ : syracuseStep 1127621 = 211429) (by norm_num)
theorem B4568309 : Blo 666309 4568309 := bbase (se 5 (by rfl) ⟨214139, by rfl⟩ : syracuseStep 4568309 = 428279) (by norm_num)
theorem B1127749 : Blo 666309 1127749 := bbase (se 4 (by rfl) ⟨105726, by rfl⟩ : syracuseStep 1127749 = 211453) (by norm_num)
theorem B1127837 : Blo 666309 1127837 := bbase (se 3 (by rfl) ⟨211469, by rfl⟩ : syracuseStep 1127837 = 422939) (by norm_num)
theorem B1127965 : Blo 666309 1127965 := bbase (se 3 (by rfl) ⟨211493, by rfl⟩ : syracuseStep 1127965 = 422987) (by norm_num)
theorem B1128053 : Blo 666309 1128053 := bbase (se 5 (by rfl) ⟨52877, by rfl⟩ : syracuseStep 1128053 = 105755) (by norm_num)
theorem B4273877 : Blo 666309 4273877 := bbase (se 7 (by rfl) ⟨50084, by rfl⟩ : syracuseStep 4273877 = 100169) (by norm_num)
theorem B1128181 : Blo 666309 1128181 := bbase (se 5 (by rfl) ⟨52883, by rfl⟩ : syracuseStep 1128181 = 105767) (by norm_num)
theorem B3815221 : Blo 666309 3815221 := bbase (se 5 (by rfl) ⟨178838, by rfl⟩ : syracuseStep 3815221 = 357677) (by norm_num)
theorem B1128269 : Blo 666309 1128269 := bbase (se 3 (by rfl) ⟨211550, by rfl⟩ : syracuseStep 1128269 = 423101) (by norm_num)
theorem B1357661 : Blo 666309 1357661 := bbase (se 3 (by rfl) ⟨254561, by rfl⟩ : syracuseStep 1357661 = 509123) (by norm_num)
theorem B1128397 : Blo 666309 1128397 := bbase (se 3 (by rfl) ⟨211574, by rfl⟩ : syracuseStep 1128397 = 423149) (by norm_num)
theorem B1128485 : Blo 666309 1128485 := bbase (se 4 (by rfl) ⟨105795, by rfl⟩ : syracuseStep 1128485 = 211591) (by norm_num)
theorem B4110421 : Blo 666309 4110421 := bbase (se 8 (by rfl) ⟨24084, by rfl⟩ : syracuseStep 4110421 = 48169) (by norm_num)
theorem B3389525 : Blo 666309 3389525 := bbase (se 8 (by rfl) ⟨19860, by rfl⟩ : syracuseStep 3389525 = 39721) (by norm_num)
theorem B1128613 : Blo 666309 1128613 := bbase (se 4 (by rfl) ⟨105807, by rfl⟩ : syracuseStep 1128613 = 211615) (by norm_num)
theorem B2406581 : Blo 666309 2406581 := bbase (se 5 (by rfl) ⟨112808, by rfl⟩ : syracuseStep 2406581 = 225617) (by norm_num)
theorem B1128701 : Blo 666309 1128701 := bbase (se 3 (by rfl) ⟨211631, by rfl⟩ : syracuseStep 1128701 = 423263) (by norm_num)
theorem B1423669 : Blo 666309 1423669 := bbase (se 5 (by rfl) ⟨66734, by rfl⟩ : syracuseStep 1423669 = 133469) (by norm_num)
theorem B1128829 : Blo 666309 1128829 := bbase (se 3 (by rfl) ⟨211655, by rfl⟩ : syracuseStep 1128829 = 423311) (by norm_num)
theorem B3422677 : Blo 666309 3422677 := bbase (se 7 (by rfl) ⟨40109, by rfl⟩ : syracuseStep 3422677 = 80219) (by norm_num)
theorem B1128917 : Blo 666309 1128917 := bbase (se 7 (by rfl) ⟨13229, by rfl⟩ : syracuseStep 1128917 = 26459) (by norm_num)
theorem B6404629 : Blo 666309 6404629 := bbase (se 6 (by rfl) ⟨150108, by rfl⟩ : syracuseStep 6404629 = 300217) (by norm_num)
theorem B1129045 : Blo 666309 1129045 := bbase (se 8 (by rfl) ⟨6615, by rfl⟩ : syracuseStep 1129045 = 13231) (by norm_num)
theorem B1129133 : Blo 666309 1129133 := bbase (se 3 (by rfl) ⟨211712, by rfl⟩ : syracuseStep 1129133 = 423425) (by norm_num)
theorem B1129261 : Blo 666309 1129261 := bbase (se 3 (by rfl) ⟨211736, by rfl⟩ : syracuseStep 1129261 = 423473) (by norm_num)
theorem B1129349 : Blo 666309 1129349 := bbase (se 4 (by rfl) ⟨105876, by rfl⟩ : syracuseStep 1129349 = 211753) (by norm_num)
theorem B2702261 : Blo 666309 2702261 := bbase (se 5 (by rfl) ⟨126668, by rfl⟩ : syracuseStep 2702261 = 253337) (by norm_num)
theorem B2538485 : Blo 666309 2538485 := bbase (se 5 (by rfl) ⟨118991, by rfl⟩ : syracuseStep 2538485 = 237983) (by norm_num)
theorem B1129477 : Blo 666309 1129477 := bbase (se 4 (by rfl) ⟨105888, by rfl⟩ : syracuseStep 1129477 = 211777) (by norm_num)
theorem B1129565 : Blo 666309 1129565 := bbase (se 3 (by rfl) ⟨211793, by rfl⟩ : syracuseStep 1129565 = 423587) (by norm_num)
theorem B1686653 : Blo 666309 1686653 := bbase (se 3 (by rfl) ⟨316247, by rfl⟩ : syracuseStep 1686653 = 632495) (by norm_num)
theorem B1424557 : Blo 666309 1424557 := bbase (se 3 (by rfl) ⟨267104, by rfl⟩ : syracuseStep 1424557 = 534209) (by norm_num)
theorem B1129693 : Blo 666309 1129693 := bbase (se 3 (by rfl) ⟨211817, by rfl⟩ : syracuseStep 1129693 = 423635) (by norm_num)
theorem B2538773 : Blo 666309 2538773 := bbase (se 6 (by rfl) ⟨59502, by rfl⟩ : syracuseStep 2538773 = 119005) (by norm_num)
theorem B1129781 : Blo 666309 1129781 := bbase (se 5 (by rfl) ⟨52958, by rfl⟩ : syracuseStep 1129781 = 105917) (by norm_num)
theorem B1686845 : Blo 666309 1686845 := bbase (se 3 (by rfl) ⟨316283, by rfl⟩ : syracuseStep 1686845 = 632567) (by norm_num)
theorem B802121 : Blo 666309 802121 := bbase (se 2 (by rfl) ⟨300795, by rfl⟩ : syracuseStep 802121 = 601591) (by norm_num)
theorem B11124053 : Blo 666309 11124053 := bbase (se 11 (by rfl) ⟨8147, by rfl⟩ : syracuseStep 11124053 = 16295) (by norm_num)
theorem B3390821 : Blo 666309 3390821 := bbase (se 4 (by rfl) ⟨317889, by rfl⟩ : syracuseStep 3390821 = 635779) (by norm_num)
theorem B2145653 : Blo 666309 2145653 := bbase (se 5 (by rfl) ⟨100577, by rfl⟩ : syracuseStep 2145653 = 201155) (by norm_num)
theorem B1129909 : Blo 666309 1129909 := bbase (se 5 (by rfl) ⟨52964, by rfl⟩ : syracuseStep 1129909 = 105929) (by norm_num)
theorem B2145781 : Blo 666309 2145781 := bbase (se 5 (by rfl) ⟨100583, by rfl⟩ : syracuseStep 2145781 = 201167) (by norm_num)
theorem B900613 : Blo 666309 900613 := bbase (se 4 (by rfl) ⟨84432, by rfl⟩ : syracuseStep 900613 = 168865) (by norm_num)
theorem B1129997 : Blo 666309 1129997 := bbase (se 3 (by rfl) ⟨211874, by rfl⟩ : syracuseStep 1129997 = 423749) (by norm_num)
theorem B802333 : Blo 666309 802333 := bbase (se 3 (by rfl) ⟨150437, by rfl⟩ : syracuseStep 802333 = 300875) (by norm_num)
theorem B966173 : Blo 666309 966173 := bbase (se 3 (by rfl) ⟨181157, by rfl⟩ : syracuseStep 966173 = 362315) (by norm_num)
theorem B2637413 : Blo 666309 2637413 := bbase (se 4 (by rfl) ⟨247257, by rfl⟩ : syracuseStep 2637413 = 494515) (by norm_num)
theorem B1130125 : Blo 666309 1130125 := bbase (se 3 (by rfl) ⟨211898, by rfl⟩ : syracuseStep 1130125 = 423797) (by norm_num)
theorem B1687189 : Blo 666309 1687189 := bbase (se 6 (by rfl) ⟨39543, by rfl⟩ : syracuseStep 1687189 = 79087) (by norm_num)
theorem B1425053 : Blo 666309 1425053 := bbase (se 3 (by rfl) ⟨267197, by rfl⟩ : syracuseStep 1425053 = 534395) (by norm_num)
theorem B802477 : Blo 666309 802477 := bbase (se 3 (by rfl) ⟨150464, by rfl⟩ : syracuseStep 802477 = 300929) (by norm_num)
theorem B1130213 : Blo 666309 1130213 := bbase (se 4 (by rfl) ⟨105957, by rfl⟩ : syracuseStep 1130213 = 211915) (by norm_num)
theorem B3817205 : Blo 666309 3817205 := bbase (se 5 (by rfl) ⟨178931, by rfl⟩ : syracuseStep 3817205 = 357863) (by norm_num)
theorem B1687301 : Blo 666309 1687301 := bbase (se 4 (by rfl) ⟨158184, by rfl⟩ : syracuseStep 1687301 = 316369) (by norm_num)
theorem B1130341 : Blo 666309 1130341 := bbase (se 4 (by rfl) ⟨105969, by rfl⟩ : syracuseStep 1130341 = 211939) (by norm_num)
theorem B2703253 : Blo 666309 2703253 := bbase (se 6 (by rfl) ⟨63357, by rfl⟩ : syracuseStep 2703253 = 126715) (by norm_num)
theorem B1130429 : Blo 666309 1130429 := bbase (se 3 (by rfl) ⟨211955, by rfl⟩ : syracuseStep 1130429 = 423911) (by norm_num)
theorem B1687493 : Blo 666309 1687493 := bbase (se 4 (by rfl) ⟨158202, by rfl⟩ : syracuseStep 1687493 = 316405) (by norm_num)
theorem B999485 : Blo 666309 999485 := bbase (se 3 (by rfl) ⟨187403, by rfl⟩ : syracuseStep 999485 = 374807) (by norm_num)
theorem B1130557 : Blo 666309 1130557 := bbase (se 3 (by rfl) ⟨211979, by rfl⟩ : syracuseStep 1130557 = 423959) (by norm_num)
theorem B999509 : Blo 666309 999509 := bbase (se 8 (by rfl) ⟨5856, by rfl⟩ : syracuseStep 999509 = 11713) (by norm_num)
theorem B999533 : Blo 666309 999533 := bbase (se 3 (by rfl) ⟨187412, by rfl⟩ : syracuseStep 999533 = 374825) (by norm_num)
theorem B999557 : Blo 666309 999557 := bbase (se 4 (by rfl) ⟨93708, by rfl⟩ : syracuseStep 999557 = 187417) (by norm_num)
theorem B1130645 : Blo 666309 1130645 := bbase (se 6 (by rfl) ⟨26499, by rfl⟩ : syracuseStep 1130645 = 52999) (by norm_num)
theorem B999581 : Blo 666309 999581 := bbase (se 3 (by rfl) ⟨187421, by rfl⟩ : syracuseStep 999581 = 374843) (by norm_num)
theorem B999605 : Blo 666309 999605 := bbase (se 5 (by rfl) ⟨46856, by rfl⟩ : syracuseStep 999605 = 93713) (by norm_num)
theorem B999629 : Blo 666309 999629 := bbase (se 3 (by rfl) ⟨187430, by rfl⟩ : syracuseStep 999629 = 374861) (by norm_num)
theorem B9126101 : Blo 666309 9126101 := bbase (se 7 (by rfl) ⟨106946, by rfl⟩ : syracuseStep 9126101 = 213893) (by norm_num)
theorem B999653 : Blo 666309 999653 := bbase (se 4 (by rfl) ⟨93717, by rfl⟩ : syracuseStep 999653 = 187435) (by norm_num)
theorem B999677 : Blo 666309 999677 := bbase (se 3 (by rfl) ⟨187439, by rfl⟩ : syracuseStep 999677 = 374879) (by norm_num)
theorem B999701 : Blo 666309 999701 := bbase (se 6 (by rfl) ⟨23430, by rfl⟩ : syracuseStep 999701 = 46861) (by norm_num)
theorem B1130773 : Blo 666309 1130773 := bbase (se 6 (by rfl) ⟨26502, by rfl⟩ : syracuseStep 1130773 = 53005) (by norm_num)
theorem B1687837 : Blo 666309 1687837 := bbase (se 3 (by rfl) ⟨316469, by rfl⟩ : syracuseStep 1687837 = 632939) (by norm_num)
theorem B999725 : Blo 666309 999725 := bbase (se 3 (by rfl) ⟨187448, by rfl⟩ : syracuseStep 999725 = 374897) (by norm_num)
theorem B999749 : Blo 666309 999749 := bbase (se 4 (by rfl) ⟨93726, by rfl⟩ : syracuseStep 999749 = 187453) (by norm_num)
theorem B999773 : Blo 666309 999773 := bbase (se 3 (by rfl) ⟨187457, by rfl⟩ : syracuseStep 999773 = 374915) (by norm_num)
theorem B1130861 : Blo 666309 1130861 := bbase (se 3 (by rfl) ⟨212036, by rfl⟩ : syracuseStep 1130861 = 424073) (by norm_num)
theorem B999797 : Blo 666309 999797 := bbase (se 5 (by rfl) ⟨46865, by rfl⟩ : syracuseStep 999797 = 93731) (by norm_num)
theorem B999821 : Blo 666309 999821 := bbase (se 3 (by rfl) ⟨187466, by rfl⟩ : syracuseStep 999821 = 374933) (by norm_num)
theorem B1687949 : Blo 666309 1687949 := bbase (se 3 (by rfl) ⟨316490, by rfl⟩ : syracuseStep 1687949 = 632981) (by norm_num)
theorem B999845 : Blo 666309 999845 := bbase (se 4 (by rfl) ⟨93735, by rfl⟩ : syracuseStep 999845 = 187471) (by norm_num)
theorem B1130917 : Blo 666309 1130917 := bbase (se 4 (by rfl) ⟨106023, by rfl⟩ : syracuseStep 1130917 = 212047) (by norm_num)
theorem B2539957 : Blo 666309 2539957 := bbase (se 5 (by rfl) ⟨119060, by rfl⟩ : syracuseStep 2539957 = 238121) (by norm_num)
theorem B999869 : Blo 666309 999869 := bbase (se 3 (by rfl) ⟨187475, by rfl⟩ : syracuseStep 999869 = 374951) (by norm_num)
theorem B999893 : Blo 666309 999893 := bbase (se 7 (by rfl) ⟨11717, by rfl⟩ : syracuseStep 999893 = 23435) (by norm_num)
theorem B999917 : Blo 666309 999917 := bbase (se 3 (by rfl) ⟨187484, by rfl⟩ : syracuseStep 999917 = 374969) (by norm_num)
theorem B1130989 : Blo 666309 1130989 := bbase (se 3 (by rfl) ⟨212060, by rfl⟩ : syracuseStep 1130989 = 424121) (by norm_num)
theorem B1425917 : Blo 666309 1425917 := bbase (se 3 (by rfl) ⟨267359, by rfl⟩ : syracuseStep 1425917 = 534719) (by norm_num)
theorem B999941 : Blo 666309 999941 := bbase (se 4 (by rfl) ⟨93744, by rfl⟩ : syracuseStep 999941 = 187489) (by norm_num)
theorem B999965 : Blo 666309 999965 := bbase (se 3 (by rfl) ⟨187493, by rfl⟩ : syracuseStep 999965 = 374987) (by norm_num)
theorem B999989 : Blo 666309 999989 := bbase (se 5 (by rfl) ⟨46874, by rfl⟩ : syracuseStep 999989 = 93749) (by norm_num)
theorem B1131077 : Blo 666309 1131077 := bbase (se 4 (by rfl) ⟨106038, by rfl⟩ : syracuseStep 1131077 = 212077) (by norm_num)
theorem B1000013 : Blo 666309 1000013 := bbase (se 3 (by rfl) ⟨187502, by rfl⟩ : syracuseStep 1000013 = 375005) (by norm_num)
theorem B1688141 : Blo 666309 1688141 := bbase (se 3 (by rfl) ⟨316526, by rfl⟩ : syracuseStep 1688141 = 633053) (by norm_num)
theorem B1000037 : Blo 666309 1000037 := bbase (se 4 (by rfl) ⟨93753, by rfl⟩ : syracuseStep 1000037 = 187507) (by norm_num)
theorem B3392117 : Blo 666309 3392117 := bbase (se 5 (by rfl) ⟨159005, by rfl⟩ : syracuseStep 3392117 = 318011) (by norm_num)
theorem B1000061 : Blo 666309 1000061 := bbase (se 3 (by rfl) ⟨187511, by rfl⟩ : syracuseStep 1000061 = 375023) (by norm_num)
theorem B1426061 : Blo 666309 1426061 := bbase (se 3 (by rfl) ⟨267386, by rfl⟩ : syracuseStep 1426061 = 534773) (by norm_num)
theorem B1000085 : Blo 666309 1000085 := bbase (se 6 (by rfl) ⟨23439, by rfl⟩ : syracuseStep 1000085 = 46879) (by norm_num)
theorem B1000109 : Blo 666309 1000109 := bbase (se 3 (by rfl) ⟨187520, by rfl⟩ : syracuseStep 1000109 = 375041) (by norm_num)
theorem B1000133 : Blo 666309 1000133 := bbase (se 4 (by rfl) ⟨93762, by rfl⟩ : syracuseStep 1000133 = 187525) (by norm_num)
theorem B1000157 : Blo 666309 1000157 := bbase (se 3 (by rfl) ⟨187529, by rfl⟩ : syracuseStep 1000157 = 375059) (by norm_num)
theorem B2540261 : Blo 666309 2540261 := bbase (se 4 (by rfl) ⟨238149, by rfl⟩ : syracuseStep 2540261 = 476299) (by norm_num)
theorem B1000181 : Blo 666309 1000181 := bbase (se 5 (by rfl) ⟨46883, by rfl⟩ : syracuseStep 1000181 = 93767) (by norm_num)
theorem B1000205 : Blo 666309 1000205 := bbase (se 3 (by rfl) ⟨187538, by rfl⟩ : syracuseStep 1000205 = 375077) (by norm_num)
theorem B1000229 : Blo 666309 1000229 := bbase (se 4 (by rfl) ⟨93771, by rfl⟩ : syracuseStep 1000229 = 187543) (by norm_num)
theorem B1000253 : Blo 666309 1000253 := bbase (se 3 (by rfl) ⟨187547, by rfl⟩ : syracuseStep 1000253 = 375095) (by norm_num)
theorem B1000277 : Blo 666309 1000277 := bbase (se 9 (by rfl) ⟨2930, by rfl⟩ : syracuseStep 1000277 = 5861) (by norm_num)
theorem B5718869 : Blo 666309 5718869 := bbase (se 9 (by rfl) ⟨16754, by rfl⟩ : syracuseStep 5718869 = 33509) (by norm_num)
theorem B1000301 : Blo 666309 1000301 := bbase (se 3 (by rfl) ⟨187556, by rfl⟩ : syracuseStep 1000301 = 375113) (by norm_num)
theorem B1000325 : Blo 666309 1000325 := bbase (se 4 (by rfl) ⟨93780, by rfl⟩ : syracuseStep 1000325 = 187561) (by norm_num)
theorem B1000349 : Blo 666309 1000349 := bbase (se 3 (by rfl) ⟨187565, by rfl⟩ : syracuseStep 1000349 = 375131) (by norm_num)
theorem B1688485 : Blo 666309 1688485 := bbase (se 4 (by rfl) ⟨158295, by rfl⟩ : syracuseStep 1688485 = 316591) (by norm_num)
theorem B1000373 : Blo 666309 1000373 := bbase (se 5 (by rfl) ⟨46892, by rfl⟩ : syracuseStep 1000373 = 93785) (by norm_num)
theorem B1000397 : Blo 666309 1000397 := bbase (se 3 (by rfl) ⟨187574, by rfl⟩ : syracuseStep 1000397 = 375149) (by norm_num)
theorem B1000421 : Blo 666309 1000421 := bbase (se 4 (by rfl) ⟨93789, by rfl⟩ : syracuseStep 1000421 = 187579) (by norm_num)
theorem B1000445 : Blo 666309 1000445 := bbase (se 3 (by rfl) ⟨187583, by rfl⟩ : syracuseStep 1000445 = 375167) (by norm_num)
theorem B1000469 : Blo 666309 1000469 := bbase (se 6 (by rfl) ⟨23448, by rfl⟩ : syracuseStep 1000469 = 46897) (by norm_num)
theorem B1688597 : Blo 666309 1688597 := bbase (se 6 (by rfl) ⟨39576, by rfl⟩ : syracuseStep 1688597 = 79153) (by norm_num)
theorem B1000493 : Blo 666309 1000493 := bbase (se 3 (by rfl) ⟨187592, by rfl⟩ : syracuseStep 1000493 = 375185) (by norm_num)
theorem B1000517 : Blo 666309 1000517 := bbase (se 4 (by rfl) ⟨93798, by rfl⟩ : syracuseStep 1000517 = 187597) (by norm_num)
theorem B1000541 : Blo 666309 1000541 := bbase (se 3 (by rfl) ⟨187601, by rfl⟩ : syracuseStep 1000541 = 375203) (by norm_num)
theorem B1000565 : Blo 666309 1000565 := bbase (se 5 (by rfl) ⟨46901, by rfl⟩ : syracuseStep 1000565 = 93803) (by norm_num)
theorem B1000589 : Blo 666309 1000589 := bbase (se 3 (by rfl) ⟨187610, by rfl⟩ : syracuseStep 1000589 = 375221) (by norm_num)
theorem B1000613 : Blo 666309 1000613 := bbase (se 4 (by rfl) ⟨93807, by rfl⟩ : syracuseStep 1000613 = 187615) (by norm_num)
theorem B1000637 : Blo 666309 1000637 := bbase (se 3 (by rfl) ⟨187619, by rfl⟩ : syracuseStep 1000637 = 375239) (by norm_num)
theorem B1000661 : Blo 666309 1000661 := bbase (se 7 (by rfl) ⟨11726, by rfl⟩ : syracuseStep 1000661 = 23453) (by norm_num)
theorem B1688789 : Blo 666309 1688789 := bbase (se 7 (by rfl) ⟨19790, by rfl⟩ : syracuseStep 1688789 = 39581) (by norm_num)
theorem B804053 : Blo 666309 804053 := bbase (se 7 (by rfl) ⟨9422, by rfl⟩ : syracuseStep 804053 = 18845) (by norm_num)
theorem B1000685 : Blo 666309 1000685 := bbase (se 3 (by rfl) ⟨187628, by rfl⟩ : syracuseStep 1000685 = 375257) (by norm_num)
theorem B1000709 : Blo 666309 1000709 := bbase (se 4 (by rfl) ⟨93816, by rfl⟩ : syracuseStep 1000709 = 187633) (by norm_num)
theorem B1000733 : Blo 666309 1000733 := bbase (se 3 (by rfl) ⟨187637, by rfl⟩ : syracuseStep 1000733 = 375275) (by norm_num)
theorem B2704693 : Blo 666309 2704693 := bbase (se 5 (by rfl) ⟨126782, by rfl⟩ : syracuseStep 2704693 = 253565) (by norm_num)
theorem B1000757 : Blo 666309 1000757 := bbase (se 5 (by rfl) ⟨46910, by rfl⟩ : syracuseStep 1000757 = 93821) (by norm_num)
theorem B1000781 : Blo 666309 1000781 := bbase (se 3 (by rfl) ⟨187646, by rfl⟩ : syracuseStep 1000781 = 375293) (by norm_num)
theorem B1000805 : Blo 666309 1000805 := bbase (se 4 (by rfl) ⟨93825, by rfl⟩ : syracuseStep 1000805 = 187651) (by norm_num)
theorem B1426805 : Blo 666309 1426805 := bbase (se 5 (by rfl) ⟨66881, by rfl⟩ : syracuseStep 1426805 = 133763) (by norm_num)
theorem B1000829 : Blo 666309 1000829 := bbase (se 3 (by rfl) ⟨187655, by rfl⟩ : syracuseStep 1000829 = 375311) (by norm_num)
theorem B1000853 : Blo 666309 1000853 := bbase (se 6 (by rfl) ⟨23457, by rfl⟩ : syracuseStep 1000853 = 46915) (by norm_num)
theorem B1000877 : Blo 666309 1000877 := bbase (se 3 (by rfl) ⟨187664, by rfl⟩ : syracuseStep 1000877 = 375329) (by norm_num)
theorem B1000901 : Blo 666309 1000901 := bbase (se 4 (by rfl) ⟨93834, by rfl⟩ : syracuseStep 1000901 = 187669) (by norm_num)
theorem B1000925 : Blo 666309 1000925 := bbase (se 3 (by rfl) ⟨187673, by rfl⟩ : syracuseStep 1000925 = 375347) (by norm_num)
theorem B1590749 : Blo 666309 1590749 := bbase (se 3 (by rfl) ⟨298265, by rfl⟩ : syracuseStep 1590749 = 596531) (by norm_num)
theorem B1000949 : Blo 666309 1000949 := bbase (se 5 (by rfl) ⟨46919, by rfl⟩ : syracuseStep 1000949 = 93839) (by norm_num)
theorem B1000973 : Blo 666309 1000973 := bbase (se 3 (by rfl) ⟨187682, by rfl⟩ : syracuseStep 1000973 = 375365) (by norm_num)
theorem B1525277 : Blo 666309 1525277 := bbase (se 3 (by rfl) ⟨285989, by rfl⟩ : syracuseStep 1525277 = 571979) (by norm_num)
theorem B1000997 : Blo 666309 1000997 := bbase (se 4 (by rfl) ⟨93843, by rfl⟩ : syracuseStep 1000997 = 187687) (by norm_num)
theorem B804389 : Blo 666309 804389 := bbase (se 4 (by rfl) ⟨75411, by rfl⟩ : syracuseStep 804389 = 150823) (by norm_num)
theorem B1689133 : Blo 666309 1689133 := bbase (se 3 (by rfl) ⟨316712, by rfl⟩ : syracuseStep 1689133 = 633425) (by norm_num)
theorem B1001021 : Blo 666309 1001021 := bbase (se 3 (by rfl) ⟨187691, by rfl⟩ : syracuseStep 1001021 = 375383) (by norm_num)
theorem B1001045 : Blo 666309 1001045 := bbase (se 8 (by rfl) ⟨5865, by rfl⟩ : syracuseStep 1001045 = 11731) (by norm_num)
theorem B1001069 : Blo 666309 1001069 := bbase (se 3 (by rfl) ⟨187700, by rfl⟩ : syracuseStep 1001069 = 375401) (by norm_num)
theorem B1001093 : Blo 666309 1001093 := bbase (se 4 (by rfl) ⟨93852, by rfl⟩ : syracuseStep 1001093 = 187705) (by norm_num)
theorem B804505 : Blo 666309 804505 := bbase (se 2 (by rfl) ⟨301689, by rfl⟩ : syracuseStep 804505 = 603379) (by norm_num)
theorem B1689245 : Blo 666309 1689245 := bbase (se 3 (by rfl) ⟨316733, by rfl⟩ : syracuseStep 1689245 = 633467) (by norm_num)
theorem B1001117 : Blo 666309 1001117 := bbase (se 3 (by rfl) ⟨187709, by rfl⟩ : syracuseStep 1001117 = 375419) (by norm_num)
theorem B1525405 : Blo 666309 1525405 := bbase (se 3 (by rfl) ⟨286013, by rfl⟩ : syracuseStep 1525405 = 572027) (by norm_num)
theorem B1001141 : Blo 666309 1001141 := bbase (se 5 (by rfl) ⟨46928, by rfl⟩ : syracuseStep 1001141 = 93857) (by norm_num)
theorem B1001165 : Blo 666309 1001165 := bbase (se 3 (by rfl) ⟨187718, by rfl⟩ : syracuseStep 1001165 = 375437) (by norm_num)
theorem B804577 : Blo 666309 804577 := bbase (se 2 (by rfl) ⟨301716, by rfl⟩ : syracuseStep 804577 = 603433) (by norm_num)
theorem B1001189 : Blo 666309 1001189 := bbase (se 4 (by rfl) ⟨93861, by rfl⟩ : syracuseStep 1001189 = 187723) (by norm_num)
theorem B804601 : Blo 666309 804601 := bbase (se 2 (by rfl) ⟨301725, by rfl⟩ : syracuseStep 804601 = 603451) (by norm_num)
theorem B1001213 : Blo 666309 1001213 := bbase (se 3 (by rfl) ⟨187727, by rfl⟩ : syracuseStep 1001213 = 375455) (by norm_num)
theorem B1001237 : Blo 666309 1001237 := bbase (se 6 (by rfl) ⟨23466, by rfl⟩ : syracuseStep 1001237 = 46933) (by norm_num)
theorem B1001261 : Blo 666309 1001261 := bbase (se 3 (by rfl) ⟨187736, by rfl⟩ : syracuseStep 1001261 = 375473) (by norm_num)
theorem B1001285 : Blo 666309 1001285 := bbase (se 4 (by rfl) ⟨93870, by rfl⟩ : syracuseStep 1001285 = 187741) (by norm_num)
theorem B771925 : Blo 666309 771925 := bbase (se 9 (by rfl) ⟨2261, by rfl⟩ : syracuseStep 771925 = 4523) (by norm_num)
theorem B1689437 : Blo 666309 1689437 := bbase (se 3 (by rfl) ⟨316769, by rfl⟩ : syracuseStep 1689437 = 633539) (by norm_num)
theorem B1001309 : Blo 666309 1001309 := bbase (se 3 (by rfl) ⟨187745, by rfl⟩ : syracuseStep 1001309 = 375491) (by norm_num)
theorem B1001333 : Blo 666309 1001333 := bbase (se 5 (by rfl) ⟨46937, by rfl⟩ : syracuseStep 1001333 = 93875) (by norm_num)
theorem B3393413 : Blo 666309 3393413 := bbase (se 4 (by rfl) ⟨318132, by rfl⟩ : syracuseStep 3393413 = 636265) (by norm_num)
theorem B804745 : Blo 666309 804745 := bbase (se 2 (by rfl) ⟨301779, by rfl⟩ : syracuseStep 804745 = 603559) (by norm_num)
theorem B1001357 : Blo 666309 1001357 := bbase (se 3 (by rfl) ⟨187754, by rfl⟩ : syracuseStep 1001357 = 375509) (by norm_num)
theorem B1001381 : Blo 666309 1001381 := bbase (se 4 (by rfl) ⟨93879, by rfl⟩ : syracuseStep 1001381 = 187759) (by norm_num)
theorem B1001405 : Blo 666309 1001405 := bbase (se 3 (by rfl) ⟨187763, by rfl⟩ : syracuseStep 1001405 = 375527) (by norm_num)
theorem B1001429 : Blo 666309 1001429 := bbase (se 7 (by rfl) ⟨11735, by rfl⟩ : syracuseStep 1001429 = 23471) (by norm_num)
theorem B1001453 : Blo 666309 1001453 := bbase (se 3 (by rfl) ⟨187772, by rfl⟩ : syracuseStep 1001453 = 375545) (by norm_num)
theorem B1001477 : Blo 666309 1001477 := bbase (se 4 (by rfl) ⟨93888, by rfl⟩ : syracuseStep 1001477 = 187777) (by norm_num)
theorem B1001501 : Blo 666309 1001501 := bbase (se 3 (by rfl) ⟨187781, by rfl⟩ : syracuseStep 1001501 = 375563) (by norm_num)
theorem B1001525 : Blo 666309 1001525 := bbase (se 5 (by rfl) ⟨46946, by rfl⟩ : syracuseStep 1001525 = 93893) (by norm_num)
theorem B1001549 : Blo 666309 1001549 := bbase (se 3 (by rfl) ⟨187790, by rfl⟩ : syracuseStep 1001549 = 375581) (by norm_num)
theorem B1001573 : Blo 666309 1001573 := bbase (se 4 (by rfl) ⟨93897, by rfl⟩ : syracuseStep 1001573 = 187795) (by norm_num)
theorem B1427557 : Blo 666309 1427557 := bbase (se 4 (by rfl) ⟨133833, by rfl⟩ : syracuseStep 1427557 = 267667) (by norm_num)
theorem B1001597 : Blo 666309 1001597 := bbase (se 3 (by rfl) ⟨187799, by rfl⟩ : syracuseStep 1001597 = 375599) (by norm_num)
theorem B1001621 : Blo 666309 1001621 := bbase (se 6 (by rfl) ⟨23475, by rfl⟩ : syracuseStep 1001621 = 46951) (by norm_num)
theorem B1001645 : Blo 666309 1001645 := bbase (se 3 (by rfl) ⟨187808, by rfl⟩ : syracuseStep 1001645 = 375617) (by norm_num)
theorem B1689781 : Blo 666309 1689781 := bbase (se 5 (by rfl) ⟨79208, by rfl⟩ : syracuseStep 1689781 = 158417) (by norm_num)
theorem B903349 : Blo 666309 903349 := bbase (se 5 (by rfl) ⟨42344, by rfl⟩ : syracuseStep 903349 = 84689) (by norm_num)
theorem B1001669 : Blo 666309 1001669 := bbase (se 4 (by rfl) ⟨93906, by rfl⟩ : syracuseStep 1001669 = 187813) (by norm_num)
theorem B3623125 : Blo 666309 3623125 := bbase (se 7 (by rfl) ⟨42458, by rfl⟩ : syracuseStep 3623125 = 84917) (by norm_num)
theorem B1001693 : Blo 666309 1001693 := bbase (se 3 (by rfl) ⟨187817, by rfl⟩ : syracuseStep 1001693 = 375635) (by norm_num)
theorem B1001717 : Blo 666309 1001717 := bbase (se 5 (by rfl) ⟨46955, by rfl⟩ : syracuseStep 1001717 = 93911) (by norm_num)
theorem B1427701 : Blo 666309 1427701 := bbase (se 5 (by rfl) ⟨66923, by rfl⟩ : syracuseStep 1427701 = 133847) (by norm_num)
theorem B1001741 : Blo 666309 1001741 := bbase (se 3 (by rfl) ⟨187826, by rfl⟩ : syracuseStep 1001741 = 375653) (by norm_num)
theorem B1689893 : Blo 666309 1689893 := bbase (se 4 (by rfl) ⟨158427, by rfl⟩ : syracuseStep 1689893 = 316855) (by norm_num)
theorem B1001765 : Blo 666309 1001765 := bbase (se 4 (by rfl) ⟨93915, by rfl⟩ : syracuseStep 1001765 = 187831) (by norm_num)
theorem B1001789 : Blo 666309 1001789 := bbase (se 3 (by rfl) ⟨187835, by rfl⟩ : syracuseStep 1001789 = 375671) (by norm_num)
theorem B1001813 : Blo 666309 1001813 := bbase (se 10 (by rfl) ⟨1467, by rfl⟩ : syracuseStep 1001813 = 2935) (by norm_num)
theorem B1001837 : Blo 666309 1001837 := bbase (se 3 (by rfl) ⟨187844, by rfl⟩ : syracuseStep 1001837 = 375689) (by norm_num)
theorem B1001861 : Blo 666309 1001861 := bbase (se 4 (by rfl) ⟨93924, by rfl⟩ : syracuseStep 1001861 = 187849) (by norm_num)
theorem B1001885 : Blo 666309 1001885 := bbase (se 3 (by rfl) ⟨187853, by rfl⟩ : syracuseStep 1001885 = 375707) (by norm_num)
theorem B1001909 : Blo 666309 1001909 := bbase (se 5 (by rfl) ⟨46964, by rfl⟩ : syracuseStep 1001909 = 93929) (by norm_num)
theorem B2574773 : Blo 666309 2574773 := bbase (se 5 (by rfl) ⟨120692, by rfl⟩ : syracuseStep 2574773 = 241385) (by norm_num)
theorem B1001933 : Blo 666309 1001933 := bbase (se 3 (by rfl) ⟨187862, by rfl⟩ : syracuseStep 1001933 = 375725) (by norm_num)
theorem B1690085 : Blo 666309 1690085 := bbase (se 4 (by rfl) ⟨158445, by rfl⟩ : syracuseStep 1690085 = 316891) (by norm_num)
theorem B1001957 : Blo 666309 1001957 := bbase (se 4 (by rfl) ⟨93933, by rfl⟩ : syracuseStep 1001957 = 187867) (by norm_num)
theorem B1067509 : Blo 666309 1067509 := bbase (se 5 (by rfl) ⟨50039, by rfl⟩ : syracuseStep 1067509 = 100079) (by norm_num)
theorem B1001981 : Blo 666309 1001981 := bbase (se 3 (by rfl) ⟨187871, by rfl⟩ : syracuseStep 1001981 = 375743) (by norm_num)
theorem B772609 : Blo 666309 772609 := bbase (se 2 (by rfl) ⟨289728, by rfl⟩ : syracuseStep 772609 = 579457) (by norm_num)
theorem B1002005 : Blo 666309 1002005 := bbase (se 6 (by rfl) ⟨23484, by rfl⟩ : syracuseStep 1002005 = 46969) (by norm_num)
theorem B1002029 : Blo 666309 1002029 := bbase (se 3 (by rfl) ⟨187880, by rfl⟩ : syracuseStep 1002029 = 375761) (by norm_num)
theorem B1067573 : Blo 666309 1067573 := bbase (se 5 (by rfl) ⟨50042, by rfl⟩ : syracuseStep 1067573 = 100085) (by norm_num)
theorem B1002053 : Blo 666309 1002053 := bbase (se 4 (by rfl) ⟨93942, by rfl⟩ : syracuseStep 1002053 = 187885) (by norm_num)
theorem B1002077 : Blo 666309 1002077 := bbase (se 3 (by rfl) ⟨187889, by rfl⟩ : syracuseStep 1002077 = 375779) (by norm_num)
theorem B1428077 : Blo 666309 1428077 := bbase (se 3 (by rfl) ⟨267764, by rfl⟩ : syracuseStep 1428077 = 535529) (by norm_num)
theorem B1002101 : Blo 666309 1002101 := bbase (se 5 (by rfl) ⟨46973, by rfl⟩ : syracuseStep 1002101 = 93947) (by norm_num)
theorem B1002125 : Blo 666309 1002125 := bbase (se 3 (by rfl) ⟨187898, by rfl⟩ : syracuseStep 1002125 = 375797) (by norm_num)
theorem B1002149 : Blo 666309 1002149 := bbase (se 4 (by rfl) ⟨93951, by rfl⟩ : syracuseStep 1002149 = 187903) (by norm_num)
theorem B1002173 : Blo 666309 1002173 := bbase (se 3 (by rfl) ⟨187907, by rfl⟩ : syracuseStep 1002173 = 375815) (by norm_num)
theorem B1002197 : Blo 666309 1002197 := bbase (se 7 (by rfl) ⟨11744, by rfl⟩ : syracuseStep 1002197 = 23489) (by norm_num)
theorem B1002221 : Blo 666309 1002221 := bbase (se 3 (by rfl) ⟨187916, by rfl⟩ : syracuseStep 1002221 = 375833) (by norm_num)
theorem B1002245 : Blo 666309 1002245 := bbase (se 4 (by rfl) ⟨93960, by rfl⟩ : syracuseStep 1002245 = 187921) (by norm_num)
theorem B1002269 : Blo 666309 1002269 := bbase (se 3 (by rfl) ⟨187925, by rfl⟩ : syracuseStep 1002269 = 375851) (by norm_num)
theorem B2542373 : Blo 666309 2542373 := bbase (se 4 (by rfl) ⟨238347, by rfl⟩ : syracuseStep 2542373 = 476695) (by norm_num)
theorem B1002293 : Blo 666309 1002293 := bbase (se 5 (by rfl) ⟨46982, by rfl⟩ : syracuseStep 1002293 = 93965) (by norm_num)
theorem B1690429 : Blo 666309 1690429 := bbase (se 3 (by rfl) ⟨316955, by rfl⟩ : syracuseStep 1690429 = 633911) (by norm_num)
theorem B871241 : Blo 666309 871241 := bbase (se 2 (by rfl) ⟨326715, by rfl⟩ : syracuseStep 871241 = 653431) (by norm_num)
theorem B1002317 : Blo 666309 1002317 := bbase (se 3 (by rfl) ⟨187934, by rfl⟩ : syracuseStep 1002317 = 375869) (by norm_num)
theorem B1002341 : Blo 666309 1002341 := bbase (se 4 (by rfl) ⟨93969, by rfl⟩ : syracuseStep 1002341 = 187939) (by norm_num)
theorem B1002365 : Blo 666309 1002365 := bbase (se 3 (by rfl) ⟨187943, by rfl⟩ : syracuseStep 1002365 = 375887) (by norm_num)
theorem B1002389 : Blo 666309 1002389 := bbase (se 6 (by rfl) ⟨23493, by rfl⟩ : syracuseStep 1002389 = 46987) (by norm_num)
theorem B1690541 : Blo 666309 1690541 := bbase (se 3 (by rfl) ⟨316976, by rfl⟩ : syracuseStep 1690541 = 633953) (by norm_num)
theorem B1002413 : Blo 666309 1002413 := bbase (se 3 (by rfl) ⟨187952, by rfl⟩ : syracuseStep 1002413 = 375905) (by norm_num)
theorem B1002437 : Blo 666309 1002437 := bbase (se 4 (by rfl) ⟨93978, by rfl⟩ : syracuseStep 1002437 = 187957) (by norm_num)
theorem B1002461 : Blo 666309 1002461 := bbase (se 3 (by rfl) ⟨187961, by rfl⟩ : syracuseStep 1002461 = 375923) (by norm_num)
theorem B1428445 : Blo 666309 1428445 := bbase (se 3 (by rfl) ⟨267833, by rfl⟩ : syracuseStep 1428445 = 535667) (by norm_num)
theorem B1002485 : Blo 666309 1002485 := bbase (se 5 (by rfl) ⟨46991, by rfl⟩ : syracuseStep 1002485 = 93983) (by norm_num)
theorem B1002509 : Blo 666309 1002509 := bbase (se 3 (by rfl) ⟨187970, by rfl⟩ : syracuseStep 1002509 = 375941) (by norm_num)
theorem B1002533 : Blo 666309 1002533 := bbase (se 4 (by rfl) ⟨93987, by rfl⟩ : syracuseStep 1002533 = 187975) (by norm_num)
theorem B1002557 : Blo 666309 1002557 := bbase (se 3 (by rfl) ⟨187979, by rfl⟩ : syracuseStep 1002557 = 375959) (by norm_num)
theorem B2542661 : Blo 666309 2542661 := bbase (se 4 (by rfl) ⟨238374, by rfl⟩ : syracuseStep 2542661 = 476749) (by norm_num)
theorem B1002581 : Blo 666309 1002581 := bbase (se 8 (by rfl) ⟨5874, by rfl⟩ : syracuseStep 1002581 = 11749) (by norm_num)
theorem B1690733 : Blo 666309 1690733 := bbase (se 3 (by rfl) ⟨317012, by rfl⟩ : syracuseStep 1690733 = 634025) (by norm_num)
theorem B1002605 : Blo 666309 1002605 := bbase (se 3 (by rfl) ⟨187988, by rfl⟩ : syracuseStep 1002605 = 375977) (by norm_num)
theorem B1002629 : Blo 666309 1002629 := bbase (se 4 (by rfl) ⟨93996, by rfl⟩ : syracuseStep 1002629 = 187993) (by norm_num)
theorem B2411669 : Blo 666309 2411669 := bbase (se 6 (by rfl) ⟨56523, by rfl⟩ : syracuseStep 2411669 = 113047) (by norm_num)
theorem B1002653 : Blo 666309 1002653 := bbase (se 3 (by rfl) ⟨187997, by rfl⟩ : syracuseStep 1002653 = 375995) (by norm_num)
theorem B1002677 : Blo 666309 1002677 := bbase (se 5 (by rfl) ⟨47000, by rfl⟩ : syracuseStep 1002677 = 94001) (by norm_num)
theorem B1002701 : Blo 666309 1002701 := bbase (se 3 (by rfl) ⟨188006, by rfl⟩ : syracuseStep 1002701 = 376013) (by norm_num)
theorem B1002725 : Blo 666309 1002725 := bbase (se 4 (by rfl) ⟨94005, by rfl⟩ : syracuseStep 1002725 = 188011) (by norm_num)
theorem B1527029 : Blo 666309 1527029 := bbase (se 5 (by rfl) ⟨71579, by rfl⟩ : syracuseStep 1527029 = 143159) (by norm_num)
theorem B1002749 : Blo 666309 1002749 := bbase (se 3 (by rfl) ⟨188015, by rfl⟩ : syracuseStep 1002749 = 376031) (by norm_num)
theorem B1002773 : Blo 666309 1002773 := bbase (se 6 (by rfl) ⟨23502, by rfl⟩ : syracuseStep 1002773 = 47005) (by norm_num)
theorem B1002797 : Blo 666309 1002797 := bbase (se 3 (by rfl) ⟨188024, by rfl⟩ : syracuseStep 1002797 = 376049) (by norm_num)
theorem B1002821 : Blo 666309 1002821 := bbase (se 4 (by rfl) ⟨94014, by rfl⟩ : syracuseStep 1002821 = 188029) (by norm_num)
theorem B1625429 : Blo 666309 1625429 := bbase (se 11 (by rfl) ⟨1190, by rfl⟩ : syracuseStep 1625429 = 2381) (by norm_num)
theorem B1002845 : Blo 666309 1002845 := bbase (se 3 (by rfl) ⟨188033, by rfl⟩ : syracuseStep 1002845 = 376067) (by norm_num)
theorem B1264997 : Blo 666309 1264997 := bbase (se 4 (by rfl) ⟨118593, by rfl⟩ : syracuseStep 1264997 = 237187) (by norm_num)
theorem B1002869 : Blo 666309 1002869 := bbase (se 5 (by rfl) ⟨47009, by rfl⟩ : syracuseStep 1002869 = 94019) (by norm_num)
theorem B1002893 : Blo 666309 1002893 := bbase (se 3 (by rfl) ⟨188042, by rfl⟩ : syracuseStep 1002893 = 376085) (by norm_num)
theorem B1002917 : Blo 666309 1002917 := bbase (se 4 (by rfl) ⟨94023, by rfl⟩ : syracuseStep 1002917 = 188047) (by norm_num)
theorem B2411957 : Blo 666309 2411957 := bbase (se 5 (by rfl) ⟨113060, by rfl⟩ : syracuseStep 2411957 = 226121) (by norm_num)
theorem B1002941 : Blo 666309 1002941 := bbase (se 3 (by rfl) ⟨188051, by rfl⟩ : syracuseStep 1002941 = 376103) (by norm_num)
theorem B1691077 : Blo 666309 1691077 := bbase (se 4 (by rfl) ⟨158538, by rfl⟩ : syracuseStep 1691077 = 317077) (by norm_num)
theorem B1002965 : Blo 666309 1002965 := bbase (se 7 (by rfl) ⟨11753, by rfl⟩ : syracuseStep 1002965 = 23507) (by norm_num)
theorem B1002989 : Blo 666309 1002989 := bbase (se 3 (by rfl) ⟨188060, by rfl⟩ : syracuseStep 1002989 = 376121) (by norm_num)
theorem B1265149 : Blo 666309 1265149 := bbase (se 3 (by rfl) ⟨237215, by rfl⟩ : syracuseStep 1265149 = 474431) (by norm_num)
theorem B1003013 : Blo 666309 1003013 := bbase (se 4 (by rfl) ⟨94032, by rfl⟩ : syracuseStep 1003013 = 188065) (by norm_num)
theorem B1003037 : Blo 666309 1003037 := bbase (se 3 (by rfl) ⟨188069, by rfl⟩ : syracuseStep 1003037 = 376139) (by norm_num)
theorem B1691189 : Blo 666309 1691189 := bbase (se 5 (by rfl) ⟨79274, by rfl⟩ : syracuseStep 1691189 = 158549) (by norm_num)
theorem B1003061 : Blo 666309 1003061 := bbase (se 5 (by rfl) ⟨47018, by rfl⟩ : syracuseStep 1003061 = 94037) (by norm_num)
theorem B1003085 : Blo 666309 1003085 := bbase (se 3 (by rfl) ⟨188078, by rfl⟩ : syracuseStep 1003085 = 376157) (by norm_num)
theorem B1003109 : Blo 666309 1003109 := bbase (se 4 (by rfl) ⟨94041, by rfl⟩ : syracuseStep 1003109 = 188083) (by norm_num)
theorem B1003133 : Blo 666309 1003133 := bbase (se 3 (by rfl) ⟨188087, by rfl⟩ : syracuseStep 1003133 = 376175) (by norm_num)
theorem B1003157 : Blo 666309 1003157 := bbase (se 6 (by rfl) ⟨23511, by rfl⟩ : syracuseStep 1003157 = 47023) (by norm_num)
theorem B1003181 : Blo 666309 1003181 := bbase (se 3 (by rfl) ⟨188096, by rfl⟩ : syracuseStep 1003181 = 376193) (by norm_num)
theorem B1003205 : Blo 666309 1003205 := bbase (se 4 (by rfl) ⟨94050, by rfl⟩ : syracuseStep 1003205 = 188101) (by norm_num)
theorem B1003229 : Blo 666309 1003229 := bbase (se 3 (by rfl) ⟨188105, by rfl⟩ : syracuseStep 1003229 = 376211) (by norm_num)
theorem B1691381 : Blo 666309 1691381 := bbase (se 5 (by rfl) ⟨79283, by rfl⟩ : syracuseStep 1691381 = 158567) (by norm_num)
theorem B1003253 : Blo 666309 1003253 := bbase (se 5 (by rfl) ⟨47027, by rfl⟩ : syracuseStep 1003253 = 94055) (by norm_num)
theorem B1003277 : Blo 666309 1003277 := bbase (se 3 (by rfl) ⟨188114, by rfl⟩ : syracuseStep 1003277 = 376229) (by norm_num)
theorem B12865301 : Blo 666309 12865301 := bbase (se 6 (by rfl) ⟨301530, by rfl⟩ : syracuseStep 12865301 = 603061) (by norm_num)
theorem B1003301 : Blo 666309 1003301 := bbase (se 4 (by rfl) ⟨94059, by rfl⟩ : syracuseStep 1003301 = 188119) (by norm_num)
theorem B1265453 : Blo 666309 1265453 := bbase (se 3 (by rfl) ⟨237272, by rfl⟩ : syracuseStep 1265453 = 474545) (by norm_num)
theorem B5066549 : Blo 666309 5066549 := bbase (se 5 (by rfl) ⟨237494, by rfl⟩ : syracuseStep 5066549 = 474989) (by norm_num)
theorem B1003325 : Blo 666309 1003325 := bbase (se 3 (by rfl) ⟨188123, by rfl⟩ : syracuseStep 1003325 = 376247) (by norm_num)
theorem B1003349 : Blo 666309 1003349 := bbase (se 9 (by rfl) ⟨2939, by rfl⟩ : syracuseStep 1003349 = 5879) (by norm_num)
theorem B1068893 : Blo 666309 1068893 := bbase (se 3 (by rfl) ⟨200417, by rfl⟩ : syracuseStep 1068893 = 400835) (by norm_num)
theorem B1003373 : Blo 666309 1003373 := bbase (se 3 (by rfl) ⟨188132, by rfl⟩ : syracuseStep 1003373 = 376265) (by norm_num)
theorem B1003397 : Blo 666309 1003397 := bbase (se 4 (by rfl) ⟨94068, by rfl⟩ : syracuseStep 1003397 = 188137) (by norm_num)
theorem B1003421 : Blo 666309 1003421 := bbase (se 3 (by rfl) ⟨188141, by rfl⟩ : syracuseStep 1003421 = 376283) (by norm_num)
theorem B1003445 : Blo 666309 1003445 := bbase (se 5 (by rfl) ⟨47036, by rfl⟩ : syracuseStep 1003445 = 94073) (by norm_num)
theorem B1003469 : Blo 666309 1003469 := bbase (se 3 (by rfl) ⟨188150, by rfl⟩ : syracuseStep 1003469 = 376301) (by norm_num)
theorem B1003493 : Blo 666309 1003493 := bbase (se 4 (by rfl) ⟨94077, by rfl⟩ : syracuseStep 1003493 = 188155) (by norm_num)
theorem B1003517 : Blo 666309 1003517 := bbase (se 3 (by rfl) ⟨188159, by rfl⟩ : syracuseStep 1003517 = 376319) (by norm_num)
theorem B1003541 : Blo 666309 1003541 := bbase (se 6 (by rfl) ⟨23520, by rfl⟩ : syracuseStep 1003541 = 47041) (by norm_num)
theorem B1069085 : Blo 666309 1069085 := bbase (se 3 (by rfl) ⟨200453, by rfl⟩ : syracuseStep 1069085 = 400907) (by norm_num)
theorem B1003565 : Blo 666309 1003565 := bbase (se 3 (by rfl) ⟨188168, by rfl⟩ : syracuseStep 1003565 = 376337) (by norm_num)
theorem B1003589 : Blo 666309 1003589 := bbase (se 4 (by rfl) ⟨94086, by rfl⟩ : syracuseStep 1003589 = 188173) (by norm_num)
theorem B1691725 : Blo 666309 1691725 := bbase (se 3 (by rfl) ⟨317198, by rfl⟩ : syracuseStep 1691725 = 634397) (by norm_num)
theorem B1003613 : Blo 666309 1003613 := bbase (se 3 (by rfl) ⟨188177, by rfl⟩ : syracuseStep 1003613 = 376355) (by norm_num)
theorem B1003637 : Blo 666309 1003637 := bbase (se 5 (by rfl) ⟨47045, by rfl⟩ : syracuseStep 1003637 = 94091) (by norm_num)
theorem B1003661 : Blo 666309 1003661 := bbase (se 3 (by rfl) ⟨188186, by rfl⟩ : syracuseStep 1003661 = 376373) (by norm_num)
theorem B1069213 : Blo 666309 1069213 := bbase (se 3 (by rfl) ⟨200477, by rfl⟩ : syracuseStep 1069213 = 400955) (by norm_num)
theorem B1003685 : Blo 666309 1003685 := bbase (se 4 (by rfl) ⟨94095, by rfl⟩ : syracuseStep 1003685 = 188191) (by norm_num)
theorem B1691837 : Blo 666309 1691837 := bbase (se 3 (by rfl) ⟨317219, by rfl⟩ : syracuseStep 1691837 = 634439) (by norm_num)
theorem B1003709 : Blo 666309 1003709 := bbase (se 3 (by rfl) ⟨188195, by rfl⟩ : syracuseStep 1003709 = 376391) (by norm_num)
theorem B1626325 : Blo 666309 1626325 := bbase (se 7 (by rfl) ⟨19058, by rfl⟩ : syracuseStep 1626325 = 38117) (by norm_num)
theorem B1003733 : Blo 666309 1003733 := bbase (se 7 (by rfl) ⟨11762, by rfl⟩ : syracuseStep 1003733 = 23525) (by norm_num)
theorem B2543845 : Blo 666309 2543845 := bbase (se 4 (by rfl) ⟨238485, by rfl⟩ : syracuseStep 2543845 = 476971) (by norm_num)
theorem B1003757 : Blo 666309 1003757 := bbase (se 3 (by rfl) ⟨188204, by rfl⟩ : syracuseStep 1003757 = 376409) (by norm_num)
theorem B1003781 : Blo 666309 1003781 := bbase (se 4 (by rfl) ⟨94104, by rfl⟩ : syracuseStep 1003781 = 188209) (by norm_num)
theorem B1003805 : Blo 666309 1003805 := bbase (se 3 (by rfl) ⟨188213, by rfl⟩ : syracuseStep 1003805 = 376427) (by norm_num)
theorem B1003829 : Blo 666309 1003829 := bbase (se 5 (by rfl) ⟨47054, by rfl⟩ : syracuseStep 1003829 = 94109) (by norm_num)
theorem B1003853 : Blo 666309 1003853 := bbase (se 3 (by rfl) ⟨188222, by rfl⟩ : syracuseStep 1003853 = 376445) (by norm_num)
theorem B2249045 : Blo 666309 2249045 := bbase (se 10 (by rfl) ⟨3294, by rfl⟩ : syracuseStep 2249045 = 6589) (by norm_num)
theorem B1003877 : Blo 666309 1003877 := bbase (se 4 (by rfl) ⟨94113, by rfl⟩ : syracuseStep 1003877 = 188227) (by norm_num)
theorem B1692029 : Blo 666309 1692029 := bbase (se 3 (by rfl) ⟨317255, by rfl⟩ : syracuseStep 1692029 = 634511) (by norm_num)
theorem B1003901 : Blo 666309 1003901 := bbase (se 3 (by rfl) ⟨188231, by rfl⟩ : syracuseStep 1003901 = 376463) (by norm_num)
theorem B1003925 : Blo 666309 1003925 := bbase (se 6 (by rfl) ⟨23529, by rfl⟩ : syracuseStep 1003925 = 47059) (by norm_num)
theorem B1003949 : Blo 666309 1003949 := bbase (se 3 (by rfl) ⟨188240, by rfl⟩ : syracuseStep 1003949 = 376481) (by norm_num)
theorem B1429949 : Blo 666309 1429949 := bbase (se 3 (by rfl) ⟨268115, by rfl⟩ : syracuseStep 1429949 = 536231) (by norm_num)
theorem B1528253 : Blo 666309 1528253 := bbase (se 3 (by rfl) ⟨286547, by rfl⟩ : syracuseStep 1528253 = 573095) (by norm_num)
theorem B1003973 : Blo 666309 1003973 := bbase (se 4 (by rfl) ⟨94122, by rfl⟩ : syracuseStep 1003973 = 188245) (by norm_num)
theorem B1003997 : Blo 666309 1003997 := bbase (se 3 (by rfl) ⟨188249, by rfl⟩ : syracuseStep 1003997 = 376499) (by norm_num)
theorem B1004021 : Blo 666309 1004021 := bbase (se 5 (by rfl) ⟨47063, by rfl⟩ : syracuseStep 1004021 = 94127) (by norm_num)
theorem B1004045 : Blo 666309 1004045 := bbase (se 3 (by rfl) ⟨188258, by rfl⟩ : syracuseStep 1004045 = 376517) (by norm_num)
theorem B2544149 : Blo 666309 2544149 := bbase (se 6 (by rfl) ⟨59628, by rfl⟩ : syracuseStep 2544149 = 119257) (by norm_num)
theorem B1266205 : Blo 666309 1266205 := bbase (se 3 (by rfl) ⟨237413, by rfl⟩ : syracuseStep 1266205 = 474827) (by norm_num)
theorem B1004069 : Blo 666309 1004069 := bbase (se 4 (by rfl) ⟨94131, by rfl⟩ : syracuseStep 1004069 = 188263) (by norm_num)
theorem B676397 : Blo 666309 676397 := bbase (se 3 (by rfl) ⟨126824, by rfl⟩ : syracuseStep 676397 = 253649) (by norm_num)
theorem B1004093 : Blo 666309 1004093 := bbase (se 3 (by rfl) ⟨188267, by rfl⟩ : syracuseStep 1004093 = 376535) (by norm_num)
theorem B1462853 : Blo 666309 1462853 := bbase (se 4 (by rfl) ⟨137142, by rfl⟩ : syracuseStep 1462853 = 274285) (by norm_num)
theorem B1430093 : Blo 666309 1430093 := bbase (se 3 (by rfl) ⟨268142, by rfl⟩ : syracuseStep 1430093 = 536285) (by norm_num)
theorem B1004117 : Blo 666309 1004117 := bbase (se 8 (by rfl) ⟨5883, by rfl⟩ : syracuseStep 1004117 = 11767) (by norm_num)
theorem B1004141 : Blo 666309 1004141 := bbase (se 3 (by rfl) ⟨188276, by rfl⟩ : syracuseStep 1004141 = 376553) (by norm_num)
theorem B1004165 : Blo 666309 1004165 := bbase (se 4 (by rfl) ⟨94140, by rfl⟩ : syracuseStep 1004165 = 188281) (by norm_num)
theorem B1004189 : Blo 666309 1004189 := bbase (se 3 (by rfl) ⟨188285, by rfl⟩ : syracuseStep 1004189 = 376571) (by norm_num)
theorem B1266349 : Blo 666309 1266349 := bbase (se 3 (by rfl) ⟨237440, by rfl⟩ : syracuseStep 1266349 = 474881) (by norm_num)
theorem B1004213 : Blo 666309 1004213 := bbase (se 5 (by rfl) ⟨47072, by rfl⟩ : syracuseStep 1004213 = 94145) (by norm_num)
theorem B1004237 : Blo 666309 1004237 := bbase (se 3 (by rfl) ⟨188294, by rfl⟩ : syracuseStep 1004237 = 376589) (by norm_num)
theorem B1692373 : Blo 666309 1692373 := bbase (se 7 (by rfl) ⟨19832, by rfl⟩ : syracuseStep 1692373 = 39665) (by norm_num)
theorem B1004261 : Blo 666309 1004261 := bbase (se 4 (by rfl) ⟨94149, by rfl⟩ : syracuseStep 1004261 = 188299) (by norm_num)
theorem B1004285 : Blo 666309 1004285 := bbase (se 3 (by rfl) ⟨188303, by rfl⟩ : syracuseStep 1004285 = 376607) (by norm_num)
theorem B2249477 : Blo 666309 2249477 := bbase (se 4 (by rfl) ⟨210888, by rfl⟩ : syracuseStep 2249477 = 421777) (by norm_num)
theorem B1004309 : Blo 666309 1004309 := bbase (se 6 (by rfl) ⟨23538, by rfl⟩ : syracuseStep 1004309 = 47077) (by norm_num)
theorem B1069853 : Blo 666309 1069853 := bbase (se 3 (by rfl) ⟨200597, by rfl⟩ : syracuseStep 1069853 = 401195) (by norm_num)
theorem B1004333 : Blo 666309 1004333 := bbase (se 3 (by rfl) ⟨188312, by rfl⟩ : syracuseStep 1004333 = 376625) (by norm_num)
theorem B676669 : Blo 666309 676669 := bbase (se 3 (by rfl) ⟨126875, by rfl⟩ : syracuseStep 676669 = 253751) (by norm_num)
theorem B1692485 : Blo 666309 1692485 := bbase (se 4 (by rfl) ⟨158670, by rfl⟩ : syracuseStep 1692485 = 317341) (by norm_num)
theorem B1004357 : Blo 666309 1004357 := bbase (se 4 (by rfl) ⟨94158, by rfl⟩ : syracuseStep 1004357 = 188317) (by norm_num)
theorem B1266509 : Blo 666309 1266509 := bbase (se 3 (by rfl) ⟨237470, by rfl⟩ : syracuseStep 1266509 = 474941) (by norm_num)
theorem B1004381 : Blo 666309 1004381 := bbase (se 3 (by rfl) ⟨188321, by rfl⟩ : syracuseStep 1004381 = 376643) (by norm_num)
theorem B1004405 : Blo 666309 1004405 := bbase (se 5 (by rfl) ⟨47081, by rfl⟩ : syracuseStep 1004405 = 94163) (by norm_num)
theorem B1004429 : Blo 666309 1004429 := bbase (se 3 (by rfl) ⟨188330, by rfl⟩ : syracuseStep 1004429 = 376661) (by norm_num)
theorem B1004453 : Blo 666309 1004453 := bbase (se 4 (by rfl) ⟨94167, by rfl⟩ : syracuseStep 1004453 = 188335) (by norm_num)
theorem B1430453 : Blo 666309 1430453 := bbase (se 5 (by rfl) ⟨67052, by rfl⟩ : syracuseStep 1430453 = 134105) (by norm_num)
theorem B1004477 : Blo 666309 1004477 := bbase (se 3 (by rfl) ⟨188339, by rfl⟩ : syracuseStep 1004477 = 376679) (by norm_num)
theorem B1004501 : Blo 666309 1004501 := bbase (se 7 (by rfl) ⟨11771, by rfl⟩ : syracuseStep 1004501 = 23543) (by norm_num)
theorem B1266653 : Blo 666309 1266653 := bbase (se 3 (by rfl) ⟨237497, by rfl⟩ : syracuseStep 1266653 = 474995) (by norm_num)
theorem B1004525 : Blo 666309 1004525 := bbase (se 3 (by rfl) ⟨188348, by rfl⟩ : syracuseStep 1004525 = 376697) (by norm_num)
theorem B1692677 : Blo 666309 1692677 := bbase (se 4 (by rfl) ⟨158688, by rfl⟩ : syracuseStep 1692677 = 317377) (by norm_num)
theorem B1004549 : Blo 666309 1004549 := bbase (se 4 (by rfl) ⟨94176, by rfl⟩ : syracuseStep 1004549 = 188353) (by norm_num)
theorem B1004573 : Blo 666309 1004573 := bbase (se 3 (by rfl) ⟨188357, by rfl⟩ : syracuseStep 1004573 = 376715) (by norm_num)
theorem B1004597 : Blo 666309 1004597 := bbase (se 5 (by rfl) ⟨47090, by rfl⟩ : syracuseStep 1004597 = 94181) (by norm_num)
theorem B1004621 : Blo 666309 1004621 := bbase (se 3 (by rfl) ⟨188366, by rfl⟩ : syracuseStep 1004621 = 376733) (by norm_num)
theorem B1004645 : Blo 666309 1004645 := bbase (se 4 (by rfl) ⟨94185, by rfl⟩ : syracuseStep 1004645 = 188371) (by norm_num)
theorem B1004669 : Blo 666309 1004669 := bbase (se 3 (by rfl) ⟨188375, by rfl⟩ : syracuseStep 1004669 = 376751) (by norm_num)
theorem B1004693 : Blo 666309 1004693 := bbase (se 6 (by rfl) ⟨23547, by rfl⟩ : syracuseStep 1004693 = 47095) (by norm_num)
theorem B1004717 : Blo 666309 1004717 := bbase (se 3 (by rfl) ⟨188384, by rfl⟩ : syracuseStep 1004717 = 376769) (by norm_num)
theorem B2249909 : Blo 666309 2249909 := bbase (se 5 (by rfl) ⟨105464, by rfl⟩ : syracuseStep 2249909 = 210929) (by norm_num)
theorem B1004741 : Blo 666309 1004741 := bbase (se 4 (by rfl) ⟨94194, by rfl⟩ : syracuseStep 1004741 = 188389) (by norm_num)
theorem B1004765 : Blo 666309 1004765 := bbase (se 3 (by rfl) ⟨188393, by rfl⟩ : syracuseStep 1004765 = 376787) (by norm_num)
theorem B1070309 : Blo 666309 1070309 := bbase (se 4 (by rfl) ⟨100341, by rfl⟩ : syracuseStep 1070309 = 200683) (by norm_num)
theorem B1627381 : Blo 666309 1627381 := bbase (se 5 (by rfl) ⟨76283, by rfl⟩ : syracuseStep 1627381 = 152567) (by norm_num)
theorem B1004789 : Blo 666309 1004789 := bbase (se 5 (by rfl) ⟨47099, by rfl⟩ : syracuseStep 1004789 = 94199) (by norm_num)
theorem B1266941 : Blo 666309 1266941 := bbase (se 3 (by rfl) ⟨237551, by rfl⟩ : syracuseStep 1266941 = 475103) (by norm_num)
theorem B1004813 : Blo 666309 1004813 := bbase (se 3 (by rfl) ⟨188402, by rfl⟩ : syracuseStep 1004813 = 376805) (by norm_num)
theorem B1004837 : Blo 666309 1004837 := bbase (se 4 (by rfl) ⟨94203, by rfl⟩ : syracuseStep 1004837 = 188407) (by norm_num)
theorem B1004861 : Blo 666309 1004861 := bbase (se 3 (by rfl) ⟨188411, by rfl⟩ : syracuseStep 1004861 = 376823) (by norm_num)
theorem B1004885 : Blo 666309 1004885 := bbase (se 17 (by rfl) ⟨11, by rfl⟩ : syracuseStep 1004885 = 23) (by norm_num)
theorem B1693021 : Blo 666309 1693021 := bbase (se 3 (by rfl) ⟨317441, by rfl⟩ : syracuseStep 1693021 = 634883) (by norm_num)
theorem B1004909 : Blo 666309 1004909 := bbase (se 3 (by rfl) ⟨188420, by rfl⟩ : syracuseStep 1004909 = 376841) (by norm_num)
theorem B1004933 : Blo 666309 1004933 := bbase (se 4 (by rfl) ⟨94212, by rfl⟩ : syracuseStep 1004933 = 188425) (by norm_num)
theorem B1267093 : Blo 666309 1267093 := bbase (se 6 (by rfl) ⟨29697, by rfl⟩ : syracuseStep 1267093 = 59395) (by norm_num)
theorem B1004957 : Blo 666309 1004957 := bbase (se 3 (by rfl) ⟨188429, by rfl⟩ : syracuseStep 1004957 = 376859) (by norm_num)
theorem B1004981 : Blo 666309 1004981 := bbase (se 5 (by rfl) ⟨47108, by rfl⟩ : syracuseStep 1004981 = 94217) (by norm_num)
theorem B1070533 : Blo 666309 1070533 := bbase (se 4 (by rfl) ⟨100362, by rfl⟩ : syracuseStep 1070533 = 200725) (by norm_num)
theorem B1693133 : Blo 666309 1693133 := bbase (se 3 (by rfl) ⟨317462, by rfl⟩ : syracuseStep 1693133 = 634925) (by norm_num)
theorem B1005005 : Blo 666309 1005005 := bbase (se 3 (by rfl) ⟨188438, by rfl⟩ : syracuseStep 1005005 = 376877) (by norm_num)
theorem B1005029 : Blo 666309 1005029 := bbase (se 4 (by rfl) ⟨94221, by rfl⟩ : syracuseStep 1005029 = 188443) (by norm_num)
theorem B1005053 : Blo 666309 1005053 := bbase (se 3 (by rfl) ⟨188447, by rfl⟩ : syracuseStep 1005053 = 376895) (by norm_num)
theorem B1070597 : Blo 666309 1070597 := bbase (se 4 (by rfl) ⟨100368, by rfl⟩ : syracuseStep 1070597 = 200737) (by norm_num)
theorem B1005077 : Blo 666309 1005077 := bbase (se 6 (by rfl) ⟨23556, by rfl⟩ : syracuseStep 1005077 = 47113) (by norm_num)
theorem B1005101 : Blo 666309 1005101 := bbase (se 3 (by rfl) ⟨188456, by rfl⟩ : syracuseStep 1005101 = 376913) (by norm_num)
theorem B1005125 : Blo 666309 1005125 := bbase (se 4 (by rfl) ⟨94230, by rfl⟩ : syracuseStep 1005125 = 188461) (by norm_num)
theorem B1005149 : Blo 666309 1005149 := bbase (se 3 (by rfl) ⟨188465, by rfl⟩ : syracuseStep 1005149 = 376931) (by norm_num)
theorem B2250341 : Blo 666309 2250341 := bbase (se 4 (by rfl) ⟨210969, by rfl⟩ : syracuseStep 2250341 = 421939) (by norm_num)
theorem B1005173 : Blo 666309 1005173 := bbase (se 5 (by rfl) ⟨47117, by rfl⟩ : syracuseStep 1005173 = 94235) (by norm_num)
theorem B1070725 : Blo 666309 1070725 := bbase (se 4 (by rfl) ⟨100380, by rfl⟩ : syracuseStep 1070725 = 200761) (by norm_num)
theorem B1693325 : Blo 666309 1693325 := bbase (se 3 (by rfl) ⟨317498, by rfl⟩ : syracuseStep 1693325 = 634997) (by norm_num)
theorem B1005197 : Blo 666309 1005197 := bbase (se 3 (by rfl) ⟨188474, by rfl⟩ : syracuseStep 1005197 = 376949) (by norm_num)
theorem B1005221 : Blo 666309 1005221 := bbase (se 4 (by rfl) ⟨94239, by rfl⟩ : syracuseStep 1005221 = 188479) (by norm_num)
theorem B1005245 : Blo 666309 1005245 := bbase (se 3 (by rfl) ⟨188483, by rfl⟩ : syracuseStep 1005245 = 376967) (by norm_num)
theorem B1267397 : Blo 666309 1267397 := bbase (se 4 (by rfl) ⟨118818, by rfl⟩ : syracuseStep 1267397 = 237637) (by norm_num)
theorem B1005269 : Blo 666309 1005269 := bbase (se 7 (by rfl) ⟨11780, by rfl⟩ : syracuseStep 1005269 = 23561) (by norm_num)
theorem B1005293 : Blo 666309 1005293 := bbase (se 3 (by rfl) ⟨188492, by rfl⟩ : syracuseStep 1005293 = 376985) (by norm_num)
theorem B1005317 : Blo 666309 1005317 := bbase (se 4 (by rfl) ⟨94248, by rfl⟩ : syracuseStep 1005317 = 188497) (by norm_num)
theorem B1005341 : Blo 666309 1005341 := bbase (se 3 (by rfl) ⟨188501, by rfl⟩ : syracuseStep 1005341 = 377003) (by norm_num)
theorem B1431341 : Blo 666309 1431341 := bbase (se 3 (by rfl) ⟨268376, by rfl⟩ : syracuseStep 1431341 = 536753) (by norm_num)
theorem B2709301 : Blo 666309 2709301 := bbase (se 5 (by rfl) ⟨126998, by rfl⟩ : syracuseStep 2709301 = 253997) (by norm_num)
theorem B1005365 : Blo 666309 1005365 := bbase (se 5 (by rfl) ⟨47126, by rfl⟩ : syracuseStep 1005365 = 94253) (by norm_num)
theorem B1005389 : Blo 666309 1005389 := bbase (se 3 (by rfl) ⟨188510, by rfl⟩ : syracuseStep 1005389 = 377021) (by norm_num)
theorem B1005413 : Blo 666309 1005413 := bbase (se 4 (by rfl) ⟨94257, by rfl⟩ : syracuseStep 1005413 = 188515) (by norm_num)
theorem B1005437 : Blo 666309 1005437 := bbase (se 3 (by rfl) ⟨188519, by rfl⟩ : syracuseStep 1005437 = 377039) (by norm_num)
theorem B1005461 : Blo 666309 1005461 := bbase (se 6 (by rfl) ⟨23565, by rfl⟩ : syracuseStep 1005461 = 47131) (by norm_num)
theorem B677845 : Blo 666309 677845 := bbase (se 7 (by rfl) ⟨7943, by rfl⟩ : syracuseStep 677845 = 15887) (by norm_num)
theorem B1693669 : Blo 666309 1693669 := bbase (se 4 (by rfl) ⟨158781, by rfl⟩ : syracuseStep 1693669 = 317563) (by norm_num)
theorem B2250773 : Blo 666309 2250773 := bbase (se 6 (by rfl) ⟨52752, by rfl⟩ : syracuseStep 2250773 = 105505) (by norm_num)
theorem B1431589 : Blo 666309 1431589 := bbase (se 4 (by rfl) ⟨134211, by rfl⟩ : syracuseStep 1431589 = 268423) (by norm_num)
theorem B1693781 : Blo 666309 1693781 := bbase (se 8 (by rfl) ⟨9924, by rfl⟩ : syracuseStep 1693781 = 19849) (by norm_num)
theorem B1693973 : Blo 666309 1693973 := bbase (se 6 (by rfl) ⟨39702, by rfl⟩ : syracuseStep 1693973 = 79405) (by norm_num)
theorem B678217 : Blo 666309 678217 := bbase (se 2 (by rfl) ⟨254331, by rfl⟩ : syracuseStep 678217 = 508663) (by norm_num)
theorem B1268149 : Blo 666309 1268149 := bbase (se 5 (by rfl) ⟨59444, by rfl⟩ : syracuseStep 1268149 = 118889) (by norm_num)
theorem B2251205 : Blo 666309 2251205 := bbase (se 4 (by rfl) ⟨211050, by rfl⟩ : syracuseStep 2251205 = 422101) (by norm_num)
theorem B1268293 : Blo 666309 1268293 := bbase (se 4 (by rfl) ⟨118902, by rfl⟩ : syracuseStep 1268293 = 237805) (by norm_num)
theorem B1694317 : Blo 666309 1694317 := bbase (se 3 (by rfl) ⟨317684, by rfl⟩ : syracuseStep 1694317 = 635369) (by norm_num)
theorem B1694429 : Blo 666309 1694429 := bbase (se 3 (by rfl) ⟨317705, by rfl⟩ : syracuseStep 1694429 = 635411) (by norm_num)
theorem B1268453 : Blo 666309 1268453 := bbase (se 4 (by rfl) ⟨118917, by rfl⟩ : syracuseStep 1268453 = 237835) (by norm_num)
theorem B1071949 : Blo 666309 1071949 := bbase (se 3 (by rfl) ⟨200990, by rfl⟩ : syracuseStep 1071949 = 401981) (by norm_num)
theorem B1858405 : Blo 666309 1858405 := bbase (se 4 (by rfl) ⟨174225, by rfl⟩ : syracuseStep 1858405 = 348451) (by norm_num)
theorem B2251637 : Blo 666309 2251637 := bbase (se 5 (by rfl) ⟨105545, by rfl⟩ : syracuseStep 2251637 = 211091) (by norm_num)
theorem B1268597 : Blo 666309 1268597 := bbase (se 5 (by rfl) ⟨59465, by rfl⟩ : syracuseStep 1268597 = 118931) (by norm_num)
theorem B1694621 : Blo 666309 1694621 := bbase (se 3 (by rfl) ⟨317741, by rfl⟩ : syracuseStep 1694621 = 635483) (by norm_num)
theorem B2710565 : Blo 666309 2710565 := bbase (se 4 (by rfl) ⟨254115, by rfl⟩ : syracuseStep 2710565 = 508231) (by norm_num)
theorem B1236061 : Blo 666309 1236061 := bbase (se 3 (by rfl) ⟨231761, by rfl⟩ : syracuseStep 1236061 = 463523) (by norm_num)
theorem B1268885 : Blo 666309 1268885 := bbase (se 6 (by rfl) ⟨29739, by rfl⟩ : syracuseStep 1268885 = 59479) (by norm_num)
theorem B679061 : Blo 666309 679061 := bbase (se 6 (by rfl) ⟨15915, by rfl⟩ : syracuseStep 679061 = 31831) (by norm_num)
theorem B711865 : Blo 666309 711865 := bbase (se 2 (by rfl) ⟨266949, by rfl⟩ : syracuseStep 711865 = 533899) (by norm_num)
theorem B744665 : Blo 666309 744665 := bbase (se 2 (by rfl) ⟨279249, by rfl⟩ : syracuseStep 744665 = 558499) (by norm_num)
theorem B1694965 : Blo 666309 1694965 := bbase (se 5 (by rfl) ⟨79451, by rfl⟩ : syracuseStep 1694965 = 158903) (by norm_num)
theorem B711937 : Blo 666309 711937 := bbase (se 2 (by rfl) ⟨266976, by rfl⟩ : syracuseStep 711937 = 533953) (by norm_num)
theorem B2252069 : Blo 666309 2252069 := bbase (se 4 (by rfl) ⟨211131, by rfl⟩ : syracuseStep 2252069 = 422263) (by norm_num)
theorem B1269037 : Blo 666309 1269037 := bbase (se 3 (by rfl) ⟨237944, by rfl⟩ : syracuseStep 1269037 = 475889) (by norm_num)
theorem B1695077 : Blo 666309 1695077 := bbase (se 4 (by rfl) ⟨158913, by rfl⟩ : syracuseStep 1695077 = 317827) (by norm_num)
theorem B3431813 : Blo 666309 3431813 := bbase (se 4 (by rfl) ⟨321732, by rfl⟩ : syracuseStep 3431813 = 643465) (by norm_num)
theorem B1072621 : Blo 666309 1072621 := bbase (se 3 (by rfl) ⟨201116, by rfl⟩ : syracuseStep 1072621 = 402233) (by norm_num)
theorem B843301 : Blo 666309 843301 := bbase (se 4 (by rfl) ⟨79059, by rfl⟩ : syracuseStep 843301 = 158119) (by norm_num)
theorem B1695269 : Blo 666309 1695269 := bbase (se 4 (by rfl) ⟨158931, by rfl⟩ : syracuseStep 1695269 = 317863) (by norm_num)
theorem B1269341 : Blo 666309 1269341 := bbase (se 3 (by rfl) ⟨238001, by rfl⟩ : syracuseStep 1269341 = 476003) (by norm_num)
theorem B712309 : Blo 666309 712309 := bbase (se 5 (by rfl) ⟨33389, by rfl⟩ : syracuseStep 712309 = 66779) (by norm_num)
theorem B843473 : Blo 666309 843473 := bbase (se 2 (by rfl) ⟨316302, by rfl⟩ : syracuseStep 843473 = 632605) (by norm_num)
theorem B2252501 : Blo 666309 2252501 := bbase (se 7 (by rfl) ⟨26396, by rfl⟩ : syracuseStep 2252501 = 52793) (by norm_num)
theorem B843529 : Blo 666309 843529 := bbase (se 2 (by rfl) ⟨316323, by rfl⟩ : syracuseStep 843529 = 632647) (by norm_num)
theorem B1203989 : Blo 666309 1203989 := bbase (se 6 (by rfl) ⟨28218, by rfl⟩ : syracuseStep 1203989 = 56437) (by norm_num)
theorem B843625 : Blo 666309 843625 := bbase (se 2 (by rfl) ⟨316359, by rfl⟩ : syracuseStep 843625 = 632719) (by norm_num)
theorem B1564541 : Blo 666309 1564541 := bbase (se 3 (by rfl) ⟨293351, by rfl⟩ : syracuseStep 1564541 = 586703) (by norm_num)
theorem B1695613 : Blo 666309 1695613 := bbase (se 3 (by rfl) ⟨317927, by rfl⟩ : syracuseStep 1695613 = 635855) (by norm_num)
theorem B712685 : Blo 666309 712685 := bbase (se 3 (by rfl) ⟨133628, by rfl⟩ : syracuseStep 712685 = 267257) (by norm_num)
theorem B1695725 : Blo 666309 1695725 := bbase (se 3 (by rfl) ⟨317948, by rfl⟩ : syracuseStep 1695725 = 635897) (by norm_num)
theorem B843797 : Blo 666309 843797 := bbase (se 6 (by rfl) ⟨19776, by rfl⟩ : syracuseStep 843797 = 39553) (by norm_num)
theorem B1925141 : Blo 666309 1925141 := bbase (se 6 (by rfl) ⟨45120, by rfl⟩ : syracuseStep 1925141 = 90241) (by norm_num)
theorem B712757 : Blo 666309 712757 := bbase (se 5 (by rfl) ⟨33410, by rfl⟩ : syracuseStep 712757 = 66821) (by norm_num)
theorem B843853 : Blo 666309 843853 := bbase (se 3 (by rfl) ⟨158222, by rfl⟩ : syracuseStep 843853 = 316445) (by norm_num)
theorem B1499237 : Blo 666309 1499237 := bbase (se 4 (by rfl) ⟨140553, by rfl⟩ : syracuseStep 1499237 = 281107) (by norm_num)
theorem B2252933 : Blo 666309 2252933 := bbase (se 4 (by rfl) ⟨211212, by rfl⟩ : syracuseStep 2252933 = 422425) (by norm_num)
theorem B1499309 : Blo 666309 1499309 := bbase (se 3 (by rfl) ⟨281120, by rfl⟩ : syracuseStep 1499309 = 562241) (by norm_num)
theorem B843949 : Blo 666309 843949 := bbase (se 3 (by rfl) ⟨158240, by rfl⟩ : syracuseStep 843949 = 316481) (by norm_num)
theorem B1695917 : Blo 666309 1695917 := bbase (se 3 (by rfl) ⟨317984, by rfl⟩ : syracuseStep 1695917 = 635969) (by norm_num)
theorem B3039461 : Blo 666309 3039461 := bbase (se 4 (by rfl) ⟨284949, by rfl⟩ : syracuseStep 3039461 = 569899) (by norm_num)
theorem B712945 : Blo 666309 712945 := bbase (se 2 (by rfl) ⟨267354, by rfl⟩ : syracuseStep 712945 = 534709) (by norm_num)
theorem B1499381 : Blo 666309 1499381 := bbase (se 5 (by rfl) ⟨70283, by rfl⟩ : syracuseStep 1499381 = 140567) (by norm_num)
theorem B3203333 : Blo 666309 3203333 := bbase (se 4 (by rfl) ⟨300312, by rfl⟩ : syracuseStep 3203333 = 600625) (by norm_num)
theorem B1499453 : Blo 666309 1499453 := bbase (se 3 (by rfl) ⟨281147, by rfl⟩ : syracuseStep 1499453 = 562295) (by norm_num)
theorem B1270093 : Blo 666309 1270093 := bbase (se 3 (by rfl) ⟨238142, by rfl⟩ : syracuseStep 1270093 = 476285) (by norm_num)
theorem B844121 : Blo 666309 844121 := bbase (se 2 (by rfl) ⟨316545, by rfl⟩ : syracuseStep 844121 = 633091) (by norm_num)
theorem B1499525 : Blo 666309 1499525 := bbase (se 4 (by rfl) ⟨140580, by rfl⟩ : syracuseStep 1499525 = 281161) (by norm_num)
theorem B844177 : Blo 666309 844177 := bbase (se 2 (by rfl) ⟨316566, by rfl⟩ : syracuseStep 844177 = 633133) (by norm_num)
theorem B8151445 : Blo 666309 8151445 := bbase (se 6 (by rfl) ⟨191049, by rfl⟩ : syracuseStep 8151445 = 382099) (by norm_num)
theorem B713129 : Blo 666309 713129 := bbase (se 2 (by rfl) ⟨267423, by rfl⟩ : syracuseStep 713129 = 534847) (by norm_num)
theorem B1499597 : Blo 666309 1499597 := bbase (se 3 (by rfl) ⟨281174, by rfl⟩ : syracuseStep 1499597 = 562349) (by norm_num)
theorem B1073621 : Blo 666309 1073621 := bbase (se 7 (by rfl) ⟨12581, by rfl⟩ : syracuseStep 1073621 = 25163) (by norm_num)
theorem B1270237 : Blo 666309 1270237 := bbase (se 3 (by rfl) ⟨238169, by rfl⟩ : syracuseStep 1270237 = 476339) (by norm_num)
theorem B844273 : Blo 666309 844273 := bbase (se 2 (by rfl) ⟨316602, by rfl⟩ : syracuseStep 844273 = 633205) (by norm_num)
theorem B1696261 : Blo 666309 1696261 := bbase (se 4 (by rfl) ⟨159024, by rfl⟩ : syracuseStep 1696261 = 318049) (by norm_num)
theorem B1499669 : Blo 666309 1499669 := bbase (se 6 (by rfl) ⟨35148, by rfl⟩ : syracuseStep 1499669 = 70297) (by norm_num)
theorem B2253365 : Blo 666309 2253365 := bbase (se 5 (by rfl) ⟨105626, by rfl⟩ : syracuseStep 2253365 = 211253) (by norm_num)
theorem B1499741 : Blo 666309 1499741 := bbase (se 3 (by rfl) ⟨281201, by rfl⟩ : syracuseStep 1499741 = 562403) (by norm_num)
theorem B1696373 : Blo 666309 1696373 := bbase (se 5 (by rfl) ⟨79517, by rfl⟩ : syracuseStep 1696373 = 159035) (by norm_num)
theorem B1270397 : Blo 666309 1270397 := bbase (se 3 (by rfl) ⟨238199, by rfl⟩ : syracuseStep 1270397 = 476399) (by norm_num)
theorem B844445 : Blo 666309 844445 := bbase (se 3 (by rfl) ⟨158333, by rfl⟩ : syracuseStep 844445 = 316667) (by norm_num)
theorem B1499813 : Blo 666309 1499813 := bbase (se 4 (by rfl) ⟨140607, by rfl⟩ : syracuseStep 1499813 = 281215) (by norm_num)
theorem B2286245 : Blo 666309 2286245 := bbase (se 4 (by rfl) ⟨214335, by rfl⟩ : syracuseStep 2286245 = 428671) (by norm_num)
theorem B844501 : Blo 666309 844501 := bbase (se 7 (by rfl) ⟨9896, by rfl⟩ : syracuseStep 844501 = 19793) (by norm_num)
theorem B1204949 : Blo 666309 1204949 := bbase (se 7 (by rfl) ⟨14120, by rfl⟩ : syracuseStep 1204949 = 28241) (by norm_num)
theorem B1499885 : Blo 666309 1499885 := bbase (se 3 (by rfl) ⟨281228, by rfl⟩ : syracuseStep 1499885 = 562457) (by norm_num)
theorem B1270541 : Blo 666309 1270541 := bbase (se 3 (by rfl) ⟨238226, by rfl⟩ : syracuseStep 1270541 = 476453) (by norm_num)
theorem B1499957 : Blo 666309 1499957 := bbase (se 5 (by rfl) ⟨70310, by rfl⟩ : syracuseStep 1499957 = 140621) (by norm_num)
theorem B844597 : Blo 666309 844597 := bbase (se 5 (by rfl) ⟨39590, by rfl⟩ : syracuseStep 844597 = 79181) (by norm_num)
theorem B1696565 : Blo 666309 1696565 := bbase (se 5 (by rfl) ⟨79526, by rfl⟩ : syracuseStep 1696565 = 159053) (by norm_num)
theorem B1500029 : Blo 666309 1500029 := bbase (se 3 (by rfl) ⟨281255, by rfl⟩ : syracuseStep 1500029 = 562511) (by norm_num)
theorem B1500101 : Blo 666309 1500101 := bbase (se 4 (by rfl) ⟨140634, by rfl⟩ : syracuseStep 1500101 = 281269) (by norm_num)
theorem B844769 : Blo 666309 844769 := bbase (se 2 (by rfl) ⟨316788, by rfl⟩ : syracuseStep 844769 = 633577) (by norm_num)
theorem B2253797 : Blo 666309 2253797 := bbase (se 4 (by rfl) ⟨211293, by rfl⟩ : syracuseStep 2253797 = 422587) (by norm_num)
theorem B1500173 : Blo 666309 1500173 := bbase (se 3 (by rfl) ⟨281282, by rfl⟩ : syracuseStep 1500173 = 562565) (by norm_num)
theorem B844825 : Blo 666309 844825 := bbase (se 2 (by rfl) ⟨316809, by rfl⟩ : syracuseStep 844825 = 633619) (by norm_num)
theorem B1270829 : Blo 666309 1270829 := bbase (se 3 (by rfl) ⟨238280, by rfl⟩ : syracuseStep 1270829 = 476561) (by norm_num)
theorem B1500245 : Blo 666309 1500245 := bbase (se 8 (by rfl) ⟨8790, by rfl⟩ : syracuseStep 1500245 = 17581) (by norm_num)
theorem B844921 : Blo 666309 844921 := bbase (se 2 (by rfl) ⟨316845, by rfl⟩ : syracuseStep 844921 = 633691) (by norm_num)
theorem B713881 : Blo 666309 713881 := bbase (se 2 (by rfl) ⟨267705, by rfl⟩ : syracuseStep 713881 = 535411) (by norm_num)
theorem B1500317 : Blo 666309 1500317 := bbase (se 3 (by rfl) ⟨281309, by rfl⟩ : syracuseStep 1500317 = 562619) (by norm_num)
theorem B3433637 : Blo 666309 3433637 := bbase (se 4 (by rfl) ⟨321903, by rfl⟩ : syracuseStep 3433637 = 643807) (by norm_num)
theorem B1270981 : Blo 666309 1270981 := bbase (se 4 (by rfl) ⟨119154, by rfl⟩ : syracuseStep 1270981 = 238309) (by norm_num)
theorem B713953 : Blo 666309 713953 := bbase (se 2 (by rfl) ⟨267732, by rfl⟩ : syracuseStep 713953 = 535465) (by norm_num)
theorem B1500389 : Blo 666309 1500389 := bbase (se 4 (by rfl) ⟨140661, by rfl⟩ : syracuseStep 1500389 = 281323) (by norm_num)
theorem B845093 : Blo 666309 845093 := bbase (se 4 (by rfl) ⟨79227, by rfl⟩ : syracuseStep 845093 = 158455) (by norm_num)
theorem B1500461 : Blo 666309 1500461 := bbase (se 3 (by rfl) ⟨281336, by rfl⟩ : syracuseStep 1500461 = 562673) (by norm_num)
theorem B845149 : Blo 666309 845149 := bbase (se 3 (by rfl) ⟨158465, by rfl⟩ : syracuseStep 845149 = 316931) (by norm_num)
theorem B1500533 : Blo 666309 1500533 := bbase (se 5 (by rfl) ⟨70337, by rfl⟩ : syracuseStep 1500533 = 140675) (by norm_num)
theorem B2254229 : Blo 666309 2254229 := bbase (se 6 (by rfl) ⟨52833, by rfl⟩ : syracuseStep 2254229 = 105667) (by norm_num)
theorem B714133 : Blo 666309 714133 := bbase (se 6 (by rfl) ⟨16737, by rfl⟩ : syracuseStep 714133 = 33475) (by norm_num)
theorem B1500605 : Blo 666309 1500605 := bbase (se 3 (by rfl) ⟨281363, by rfl⟩ : syracuseStep 1500605 = 562727) (by norm_num)
theorem B845245 : Blo 666309 845245 := bbase (se 3 (by rfl) ⟨158483, by rfl⟩ : syracuseStep 845245 = 316967) (by norm_num)
theorem B1271285 : Blo 666309 1271285 := bbase (se 5 (by rfl) ⟨59591, by rfl⟩ : syracuseStep 1271285 = 119183) (by norm_num)
theorem B1500677 : Blo 666309 1500677 := bbase (se 4 (by rfl) ⟨140688, by rfl⟩ : syracuseStep 1500677 = 281377) (by norm_num)
theorem B4285973 : Blo 666309 4285973 := bbase (se 6 (by rfl) ⟨100452, by rfl⟩ : syracuseStep 4285973 = 200905) (by norm_num)
theorem B1500749 : Blo 666309 1500749 := bbase (se 3 (by rfl) ⟨281390, by rfl⟩ : syracuseStep 1500749 = 562781) (by norm_num)
theorem B1631821 : Blo 666309 1631821 := bbase (se 3 (by rfl) ⟨305966, by rfl⟩ : syracuseStep 1631821 = 611933) (by norm_num)
theorem B845417 : Blo 666309 845417 := bbase (se 2 (by rfl) ⟨317031, by rfl⟩ : syracuseStep 845417 = 634063) (by norm_num)
theorem B1500821 : Blo 666309 1500821 := bbase (se 6 (by rfl) ⟨35175, by rfl⟩ : syracuseStep 1500821 = 70351) (by norm_num)
theorem B845473 : Blo 666309 845473 := bbase (se 2 (by rfl) ⟨317052, by rfl⟩ : syracuseStep 845473 = 634105) (by norm_num)
theorem B1500893 : Blo 666309 1500893 := bbase (se 3 (by rfl) ⟨281417, by rfl⟩ : syracuseStep 1500893 = 562835) (by norm_num)
theorem B845569 : Blo 666309 845569 := bbase (se 2 (by rfl) ⟨317088, by rfl⟩ : syracuseStep 845569 = 634177) (by norm_num)
theorem B1500965 : Blo 666309 1500965 := bbase (se 4 (by rfl) ⟨140715, by rfl⟩ : syracuseStep 1500965 = 281431) (by norm_num)
theorem B2254661 : Blo 666309 2254661 := bbase (se 4 (by rfl) ⟨211374, by rfl⟩ : syracuseStep 2254661 = 422749) (by norm_num)
theorem B714577 : Blo 666309 714577 := bbase (se 2 (by rfl) ⟨267966, by rfl⟩ : syracuseStep 714577 = 535933) (by norm_num)
theorem B1501037 : Blo 666309 1501037 := bbase (se 3 (by rfl) ⟨281444, by rfl⟩ : syracuseStep 1501037 = 562889) (by norm_num)
theorem B845741 : Blo 666309 845741 := bbase (se 3 (by rfl) ⟨158576, by rfl⟩ : syracuseStep 845741 = 317153) (by norm_num)
theorem B1501109 : Blo 666309 1501109 := bbase (se 5 (by rfl) ⟨70364, by rfl⟩ : syracuseStep 1501109 = 140729) (by norm_num)
theorem B714701 : Blo 666309 714701 := bbase (se 3 (by rfl) ⟨134006, by rfl⟩ : syracuseStep 714701 = 268013) (by norm_num)
theorem B1140709 : Blo 666309 1140709 := bbase (se 4 (by rfl) ⟨106941, by rfl⟩ : syracuseStep 1140709 = 213883) (by norm_num)
theorem B845797 : Blo 666309 845797 := bbase (se 4 (by rfl) ⟨79293, by rfl⟩ : syracuseStep 845797 = 158587) (by norm_num)
theorem B1370093 : Blo 666309 1370093 := bbase (se 3 (by rfl) ⟨256892, by rfl⟩ : syracuseStep 1370093 = 513785) (by norm_num)
theorem B1501181 : Blo 666309 1501181 := bbase (se 3 (by rfl) ⟨281471, by rfl⟩ : syracuseStep 1501181 = 562943) (by norm_num)
theorem B2287669 : Blo 666309 2287669 := bbase (se 5 (by rfl) ⟨107234, by rfl⟩ : syracuseStep 2287669 = 214469) (by norm_num)
theorem B1501253 : Blo 666309 1501253 := bbase (se 4 (by rfl) ⟨140742, by rfl⟩ : syracuseStep 1501253 = 281485) (by norm_num)
theorem B845893 : Blo 666309 845893 := bbase (se 4 (by rfl) ⟨79302, by rfl⟩ : syracuseStep 845893 = 158605) (by norm_num)
theorem B1501325 : Blo 666309 1501325 := bbase (se 3 (by rfl) ⟨281498, by rfl⟩ : syracuseStep 1501325 = 562997) (by norm_num)
theorem B714953 : Blo 666309 714953 := bbase (se 2 (by rfl) ⟨268107, by rfl⟩ : syracuseStep 714953 = 536215) (by norm_num)
theorem B1501397 : Blo 666309 1501397 := bbase (se 7 (by rfl) ⟨17594, by rfl⟩ : syracuseStep 1501397 = 35189) (by norm_num)
theorem B1272037 : Blo 666309 1272037 := bbase (se 4 (by rfl) ⟨119253, by rfl⟩ : syracuseStep 1272037 = 238507) (by norm_num)
theorem B846065 : Blo 666309 846065 := bbase (se 2 (by rfl) ⟨317274, by rfl⟩ : syracuseStep 846065 = 634549) (by norm_num)
theorem B2255093 : Blo 666309 2255093 := bbase (se 5 (by rfl) ⟨105707, by rfl⟩ : syracuseStep 2255093 = 211415) (by norm_num)
theorem B1501469 : Blo 666309 1501469 := bbase (se 3 (by rfl) ⟨281525, by rfl⟩ : syracuseStep 1501469 = 563051) (by norm_num)
theorem B846121 : Blo 666309 846121 := bbase (se 2 (by rfl) ⟨317295, by rfl⟩ : syracuseStep 846121 = 634591) (by norm_num)
theorem B1501541 : Blo 666309 1501541 := bbase (se 4 (by rfl) ⟨140769, by rfl⟩ : syracuseStep 1501541 = 281539) (by norm_num)
theorem B1272181 : Blo 666309 1272181 := bbase (se 5 (by rfl) ⟨59633, by rfl⟩ : syracuseStep 1272181 = 119267) (by norm_num)
theorem B846217 : Blo 666309 846217 := bbase (se 2 (by rfl) ⟨317331, by rfl⟩ : syracuseStep 846217 = 634663) (by norm_num)
theorem B3467669 : Blo 666309 3467669 := bbase (se 6 (by rfl) ⟨81273, by rfl⟩ : syracuseStep 3467669 = 162547) (by norm_num)
theorem B1501613 : Blo 666309 1501613 := bbase (se 3 (by rfl) ⟨281552, by rfl⟩ : syracuseStep 1501613 = 563105) (by norm_num)
theorem B1501685 : Blo 666309 1501685 := bbase (se 5 (by rfl) ⟨70391, by rfl⟩ : syracuseStep 1501685 = 140783) (by norm_num)
theorem B1272341 : Blo 666309 1272341 := bbase (se 6 (by rfl) ⟨29820, by rfl⟩ : syracuseStep 1272341 = 59641) (by norm_num)
theorem B846389 : Blo 666309 846389 := bbase (se 5 (by rfl) ⟨39674, by rfl⟩ : syracuseStep 846389 = 79349) (by norm_num)
theorem B1501757 : Blo 666309 1501757 := bbase (se 3 (by rfl) ⟨281579, by rfl⟩ : syracuseStep 1501757 = 563159) (by norm_num)
theorem B846445 : Blo 666309 846445 := bbase (se 3 (by rfl) ⟨158708, by rfl⟩ : syracuseStep 846445 = 317417) (by norm_num)
theorem B1501829 : Blo 666309 1501829 := bbase (se 4 (by rfl) ⟨140796, by rfl⟩ : syracuseStep 1501829 = 281593) (by norm_num)
theorem B715397 : Blo 666309 715397 := bbase (se 4 (by rfl) ⟨67068, by rfl⟩ : syracuseStep 715397 = 134137) (by norm_num)
theorem B2255525 : Blo 666309 2255525 := bbase (se 4 (by rfl) ⟨211455, by rfl⟩ : syracuseStep 2255525 = 422911) (by norm_num)
theorem B1272485 : Blo 666309 1272485 := bbase (se 4 (by rfl) ⟨119295, by rfl⟩ : syracuseStep 1272485 = 238591) (by norm_num)
theorem B1501901 : Blo 666309 1501901 := bbase (se 3 (by rfl) ⟨281606, by rfl⟩ : syracuseStep 1501901 = 563213) (by norm_num)
theorem B846541 : Blo 666309 846541 := bbase (se 3 (by rfl) ⟨158726, by rfl⟩ : syracuseStep 846541 = 317453) (by norm_num)
theorem B1207045 : Blo 666309 1207045 := bbase (se 4 (by rfl) ⟨113160, by rfl⟩ : syracuseStep 1207045 = 226321) (by norm_num)
theorem B1501973 : Blo 666309 1501973 := bbase (se 6 (by rfl) ⟨35202, by rfl⟩ : syracuseStep 1501973 = 70405) (by norm_num)
theorem B813845 : Blo 666309 813845 := bbase (se 6 (by rfl) ⟨19074, by rfl⟩ : syracuseStep 813845 = 38149) (by norm_num)
theorem B1502045 : Blo 666309 1502045 := bbase (se 3 (by rfl) ⟨281633, by rfl⟩ : syracuseStep 1502045 = 563267) (by norm_num)
theorem B846713 : Blo 666309 846713 := bbase (se 2 (by rfl) ⟨317517, by rfl⟩ : syracuseStep 846713 = 635035) (by norm_num)
theorem B715645 : Blo 666309 715645 := bbase (se 3 (by rfl) ⟨134183, by rfl⟩ : syracuseStep 715645 = 268367) (by norm_num)
theorem B813961 : Blo 666309 813961 := bbase (se 2 (by rfl) ⟨305235, by rfl⟩ : syracuseStep 813961 = 610471) (by norm_num)
theorem B2288533 : Blo 666309 2288533 := bbase (se 6 (by rfl) ⟨53637, by rfl⟩ : syracuseStep 2288533 = 107275) (by norm_num)
theorem B1502117 : Blo 666309 1502117 := bbase (se 4 (by rfl) ⟨140823, by rfl⟩ : syracuseStep 1502117 = 281647) (by norm_num)
theorem B813997 : Blo 666309 813997 := bbase (se 3 (by rfl) ⟨152624, by rfl⟩ : syracuseStep 813997 = 305249) (by norm_num)
theorem B846769 : Blo 666309 846769 := bbase (se 2 (by rfl) ⟨317538, by rfl⟩ : syracuseStep 846769 = 635077) (by norm_num)
theorem B3206101 : Blo 666309 3206101 := bbase (se 7 (by rfl) ⟨37571, by rfl⟩ : syracuseStep 3206101 = 75143) (by norm_num)
theorem B1502189 : Blo 666309 1502189 := bbase (se 3 (by rfl) ⟨281660, by rfl⟩ : syracuseStep 1502189 = 563321) (by norm_num)
theorem B846865 : Blo 666309 846865 := bbase (se 2 (by rfl) ⟨317574, by rfl⟩ : syracuseStep 846865 = 635149) (by norm_num)
theorem B1502261 : Blo 666309 1502261 := bbase (se 5 (by rfl) ⟨70418, by rfl⟩ : syracuseStep 1502261 = 140837) (by norm_num)
theorem B2255957 : Blo 666309 2255957 := bbase (se 8 (by rfl) ⟨13218, by rfl⟩ : syracuseStep 2255957 = 26437) (by norm_num)
theorem B3796085 : Blo 666309 3796085 := bbase (se 5 (by rfl) ⟨177941, by rfl⟩ : syracuseStep 3796085 = 355883) (by norm_num)
theorem B1502333 : Blo 666309 1502333 := bbase (se 3 (by rfl) ⟨281687, by rfl⟩ : syracuseStep 1502333 = 563375) (by norm_num)
theorem B847037 : Blo 666309 847037 := bbase (se 3 (by rfl) ⟨158819, by rfl⟩ : syracuseStep 847037 = 317639) (by norm_num)
theorem B1502405 : Blo 666309 1502405 := bbase (se 4 (by rfl) ⟨140850, by rfl⟩ : syracuseStep 1502405 = 281701) (by norm_num)
theorem B847093 : Blo 666309 847093 := bbase (se 5 (by rfl) ⟨39707, by rfl⟩ : syracuseStep 847093 = 79415) (by norm_num)
theorem B1502477 : Blo 666309 1502477 := bbase (se 3 (by rfl) ⟨281714, by rfl⟩ : syracuseStep 1502477 = 563429) (by norm_num)
theorem B1502549 : Blo 666309 1502549 := bbase (se 11 (by rfl) ⟨1100, by rfl⟩ : syracuseStep 1502549 = 2201) (by norm_num)
theorem B847189 : Blo 666309 847189 := bbase (se 11 (by rfl) ⟨620, by rfl⟩ : syracuseStep 847189 = 1241) (by norm_num)
theorem B814429 : Blo 666309 814429 := bbase (se 3 (by rfl) ⟨152705, by rfl⟩ : syracuseStep 814429 = 305411) (by norm_num)
theorem B5074325 : Blo 666309 5074325 := bbase (se 6 (by rfl) ⟨118929, by rfl⟩ : syracuseStep 5074325 = 237859) (by norm_num)
theorem B1502621 : Blo 666309 1502621 := bbase (se 3 (by rfl) ⟨281741, by rfl⟩ : syracuseStep 1502621 = 563483) (by norm_num)
theorem B1502693 : Blo 666309 1502693 := bbase (se 4 (by rfl) ⟨140877, by rfl⟩ : syracuseStep 1502693 = 281755) (by norm_num)
theorem B847361 : Blo 666309 847361 := bbase (se 2 (by rfl) ⟨317760, by rfl⟩ : syracuseStep 847361 = 635521) (by norm_num)
theorem B2256389 : Blo 666309 2256389 := bbase (se 4 (by rfl) ⟨211536, by rfl⟩ : syracuseStep 2256389 = 423073) (by norm_num)
theorem B1502765 : Blo 666309 1502765 := bbase (se 3 (by rfl) ⟨281768, by rfl⟩ : syracuseStep 1502765 = 563537) (by norm_num)
theorem B847417 : Blo 666309 847417 := bbase (se 2 (by rfl) ⟨317781, by rfl⟩ : syracuseStep 847417 = 635563) (by norm_num)
theorem B1502837 : Blo 666309 1502837 := bbase (se 5 (by rfl) ⟨70445, by rfl⟩ : syracuseStep 1502837 = 140891) (by norm_num)
theorem B847513 : Blo 666309 847513 := bbase (se 2 (by rfl) ⟨317817, by rfl⟩ : syracuseStep 847513 = 635635) (by norm_num)
theorem B1502909 : Blo 666309 1502909 := bbase (se 3 (by rfl) ⟨281795, by rfl⟩ : syracuseStep 1502909 = 563591) (by norm_num)
theorem B1502981 : Blo 666309 1502981 := bbase (se 4 (by rfl) ⟨140904, by rfl⟩ : syracuseStep 1502981 = 281809) (by norm_num)
theorem B847685 : Blo 666309 847685 := bbase (se 4 (by rfl) ⟨79470, by rfl⟩ : syracuseStep 847685 = 158941) (by norm_num)
theorem B1503053 : Blo 666309 1503053 := bbase (se 3 (by rfl) ⟨281822, by rfl⟩ : syracuseStep 1503053 = 563645) (by norm_num)
theorem B847741 : Blo 666309 847741 := bbase (se 3 (by rfl) ⟨158951, by rfl⟩ : syracuseStep 847741 = 317903) (by norm_num)
theorem B1503125 : Blo 666309 1503125 := bbase (se 6 (by rfl) ⟨35229, by rfl⟩ : syracuseStep 1503125 = 70459) (by norm_num)
theorem B2256821 : Blo 666309 2256821 := bbase (se 5 (by rfl) ⟨105788, by rfl⟩ : syracuseStep 2256821 = 211577) (by norm_num)
theorem B1142741 : Blo 666309 1142741 := bbase (se 7 (by rfl) ⟨13391, by rfl⟩ : syracuseStep 1142741 = 26783) (by norm_num)
theorem B1503197 : Blo 666309 1503197 := bbase (se 3 (by rfl) ⟨281849, by rfl⟩ : syracuseStep 1503197 = 563699) (by norm_num)
theorem B847837 : Blo 666309 847837 := bbase (se 3 (by rfl) ⟨158969, by rfl⟩ : syracuseStep 847837 = 317939) (by norm_num)
theorem B1372133 : Blo 666309 1372133 := bbase (se 4 (by rfl) ⟨128637, by rfl⟩ : syracuseStep 1372133 = 257275) (by norm_num)
theorem B1929205 : Blo 666309 1929205 := bbase (se 5 (by rfl) ⟨90431, by rfl⟩ : syracuseStep 1929205 = 180863) (by norm_num)
theorem B749605 : Blo 666309 749605 := bbase (se 4 (by rfl) ⟨70275, by rfl⟩ : syracuseStep 749605 = 140551) (by norm_num)
theorem B1503269 : Blo 666309 1503269 := bbase (se 4 (by rfl) ⟨140931, by rfl⟩ : syracuseStep 1503269 = 281863) (by norm_num)
theorem B749641 : Blo 666309 749641 := bbase (se 2 (by rfl) ⟨281115, by rfl⟩ : syracuseStep 749641 = 562231) (by norm_num)
theorem B749677 : Blo 666309 749677 := bbase (se 3 (by rfl) ⟨140564, by rfl⟩ : syracuseStep 749677 = 281129) (by norm_num)
theorem B1503341 : Blo 666309 1503341 := bbase (se 3 (by rfl) ⟨281876, by rfl⟩ : syracuseStep 1503341 = 563753) (by norm_num)
theorem B848009 : Blo 666309 848009 := bbase (se 2 (by rfl) ⟨318003, by rfl⟩ : syracuseStep 848009 = 636007) (by norm_num)
theorem B749713 : Blo 666309 749713 := bbase (se 2 (by rfl) ⟨281142, by rfl⟩ : syracuseStep 749713 = 562285) (by norm_num)
theorem B749749 : Blo 666309 749749 := bbase (se 5 (by rfl) ⟨35144, by rfl⟩ : syracuseStep 749749 = 70289) (by norm_num)
theorem B1503413 : Blo 666309 1503413 := bbase (se 5 (by rfl) ⟨70472, by rfl⟩ : syracuseStep 1503413 = 140945) (by norm_num)
theorem B848065 : Blo 666309 848065 := bbase (se 2 (by rfl) ⟨318024, by rfl⟩ : syracuseStep 848065 = 636049) (by norm_num)
theorem B749785 : Blo 666309 749785 := bbase (se 2 (by rfl) ⟨281169, by rfl⟩ : syracuseStep 749785 = 562339) (by norm_num)
theorem B749821 : Blo 666309 749821 := bbase (se 3 (by rfl) ⟨140591, by rfl⟩ : syracuseStep 749821 = 281183) (by norm_num)
theorem B1503485 : Blo 666309 1503485 := bbase (se 3 (by rfl) ⟨281903, by rfl⟩ : syracuseStep 1503485 = 563807) (by norm_num)
theorem B749857 : Blo 666309 749857 := bbase (se 2 (by rfl) ⟨281196, by rfl⟩ : syracuseStep 749857 = 562393) (by norm_num)
theorem B848161 : Blo 666309 848161 := bbase (se 2 (by rfl) ⟨318060, by rfl⟩ : syracuseStep 848161 = 636121) (by norm_num)
theorem B749893 : Blo 666309 749893 := bbase (se 4 (by rfl) ⟨70302, by rfl⟩ : syracuseStep 749893 = 140605) (by norm_num)
theorem B1503557 : Blo 666309 1503557 := bbase (se 4 (by rfl) ⟨140958, by rfl⟩ : syracuseStep 1503557 = 281917) (by norm_num)
theorem B2257253 : Blo 666309 2257253 := bbase (se 4 (by rfl) ⟨211617, by rfl⟩ : syracuseStep 2257253 = 423235) (by norm_num)
theorem B749929 : Blo 666309 749929 := bbase (se 2 (by rfl) ⟨281223, by rfl⟩ : syracuseStep 749929 = 562447) (by norm_num)
theorem B749965 : Blo 666309 749965 := bbase (se 3 (by rfl) ⟨140618, by rfl⟩ : syracuseStep 749965 = 281237) (by norm_num)
theorem B1503629 : Blo 666309 1503629 := bbase (se 3 (by rfl) ⟨281930, by rfl⟩ : syracuseStep 1503629 = 563861) (by norm_num)
theorem B750001 : Blo 666309 750001 := bbase (se 2 (by rfl) ⟨281250, by rfl⟩ : syracuseStep 750001 = 562501) (by norm_num)
theorem B4288949 : Blo 666309 4288949 := bbase (se 5 (by rfl) ⟨201044, by rfl⟩ : syracuseStep 4288949 = 402089) (by norm_num)
theorem B848333 : Blo 666309 848333 := bbase (se 3 (by rfl) ⟨159062, by rfl⟩ : syracuseStep 848333 = 318125) (by norm_num)
theorem B750037 : Blo 666309 750037 := bbase (se 7 (by rfl) ⟨8789, by rfl⟩ : syracuseStep 750037 = 17579) (by norm_num)
theorem B1503701 : Blo 666309 1503701 := bbase (se 7 (by rfl) ⟨17621, by rfl⟩ : syracuseStep 1503701 = 35243) (by norm_num)
theorem B750073 : Blo 666309 750073 := bbase (se 2 (by rfl) ⟨281277, by rfl⟩ : syracuseStep 750073 = 562555) (by norm_num)
theorem B913933 : Blo 666309 913933 := bbase (se 3 (by rfl) ⟨171362, by rfl⟩ : syracuseStep 913933 = 342725) (by norm_num)
theorem B750109 : Blo 666309 750109 := bbase (se 3 (by rfl) ⟨140645, by rfl⟩ : syracuseStep 750109 = 281291) (by norm_num)
theorem B1503773 : Blo 666309 1503773 := bbase (se 3 (by rfl) ⟨281957, by rfl⟩ : syracuseStep 1503773 = 563915) (by norm_num)
theorem B1602109 : Blo 666309 1602109 := bbase (se 3 (by rfl) ⟨300395, by rfl⟩ : syracuseStep 1602109 = 600791) (by norm_num)
theorem B750145 : Blo 666309 750145 := bbase (se 2 (by rfl) ⟨281304, by rfl⟩ : syracuseStep 750145 = 562609) (by norm_num)
theorem B750181 : Blo 666309 750181 := bbase (se 4 (by rfl) ⟨70329, by rfl⟩ : syracuseStep 750181 = 140659) (by norm_num)
theorem B1503845 : Blo 666309 1503845 := bbase (se 4 (by rfl) ⟨140985, by rfl⟩ : syracuseStep 1503845 = 281971) (by norm_num)
theorem B750217 : Blo 666309 750217 := bbase (se 2 (by rfl) ⟨281331, by rfl⟩ : syracuseStep 750217 = 562663) (by norm_num)
theorem B750253 : Blo 666309 750253 := bbase (se 3 (by rfl) ⟨140672, by rfl⟩ : syracuseStep 750253 = 281345) (by norm_num)
theorem B1503917 : Blo 666309 1503917 := bbase (se 3 (by rfl) ⟨281984, by rfl⟩ : syracuseStep 1503917 = 563969) (by norm_num)
theorem B2716357 : Blo 666309 2716357 := bbase (se 4 (by rfl) ⟨254658, by rfl⟩ : syracuseStep 2716357 = 509317) (by norm_num)
theorem B750289 : Blo 666309 750289 := bbase (se 2 (by rfl) ⟨281358, by rfl⟩ : syracuseStep 750289 = 562717) (by norm_num)
theorem B750325 : Blo 666309 750325 := bbase (se 5 (by rfl) ⟨35171, by rfl⟩ : syracuseStep 750325 = 70343) (by norm_num)
theorem B1503989 : Blo 666309 1503989 := bbase (se 5 (by rfl) ⟨70499, by rfl⟩ : syracuseStep 1503989 = 140999) (by norm_num)
theorem B2257685 : Blo 666309 2257685 := bbase (se 6 (by rfl) ⟨52914, by rfl⟩ : syracuseStep 2257685 = 105829) (by norm_num)
theorem B750361 : Blo 666309 750361 := bbase (se 2 (by rfl) ⟨281385, by rfl⟩ : syracuseStep 750361 = 562771) (by norm_num)
theorem B750397 : Blo 666309 750397 := bbase (se 3 (by rfl) ⟨140699, by rfl⟩ : syracuseStep 750397 = 281399) (by norm_num)
theorem B1504061 : Blo 666309 1504061 := bbase (se 3 (by rfl) ⟨282011, by rfl⟩ : syracuseStep 1504061 = 564023) (by norm_num)
theorem B750433 : Blo 666309 750433 := bbase (se 2 (by rfl) ⟨281412, by rfl⟩ : syracuseStep 750433 = 562825) (by norm_num)
theorem B3437413 : Blo 666309 3437413 := bbase (se 4 (by rfl) ⟨322257, by rfl⟩ : syracuseStep 3437413 = 644515) (by norm_num)
theorem B750469 : Blo 666309 750469 := bbase (se 4 (by rfl) ⟨70356, by rfl⟩ : syracuseStep 750469 = 140713) (by norm_num)
theorem B1504133 : Blo 666309 1504133 := bbase (se 4 (by rfl) ⟨141012, by rfl⟩ : syracuseStep 1504133 = 282025) (by norm_num)
theorem B750505 : Blo 666309 750505 := bbase (se 2 (by rfl) ⟨281439, by rfl⟩ : syracuseStep 750505 = 562879) (by norm_num)
theorem B750541 : Blo 666309 750541 := bbase (se 3 (by rfl) ⟨140726, by rfl⟩ : syracuseStep 750541 = 281453) (by norm_num)
theorem B1504205 : Blo 666309 1504205 := bbase (se 3 (by rfl) ⟨282038, by rfl⟩ : syracuseStep 1504205 = 564077) (by norm_num)
theorem B750577 : Blo 666309 750577 := bbase (se 2 (by rfl) ⟨281466, by rfl⟩ : syracuseStep 750577 = 562933) (by norm_num)
theorem B750613 : Blo 666309 750613 := bbase (se 6 (by rfl) ⟨17592, by rfl⟩ : syracuseStep 750613 = 35185) (by norm_num)
theorem B1504277 : Blo 666309 1504277 := bbase (se 6 (by rfl) ⟨35256, by rfl⟩ : syracuseStep 1504277 = 70513) (by norm_num)
theorem B750649 : Blo 666309 750649 := bbase (se 2 (by rfl) ⟨281493, by rfl⟩ : syracuseStep 750649 = 562987) (by norm_num)
theorem B750685 : Blo 666309 750685 := bbase (se 3 (by rfl) ⟨140753, by rfl⟩ : syracuseStep 750685 = 281507) (by norm_num)
theorem B1504349 : Blo 666309 1504349 := bbase (se 3 (by rfl) ⟨282065, by rfl⟩ : syracuseStep 1504349 = 564131) (by norm_num)
theorem B750721 : Blo 666309 750721 := bbase (se 2 (by rfl) ⟨281520, by rfl⟩ : syracuseStep 750721 = 563041) (by norm_num)
theorem B750757 : Blo 666309 750757 := bbase (se 4 (by rfl) ⟨70383, by rfl⟩ : syracuseStep 750757 = 140767) (by norm_num)
theorem B1504421 : Blo 666309 1504421 := bbase (se 4 (by rfl) ⟨141039, by rfl⟩ : syracuseStep 1504421 = 282079) (by norm_num)
theorem B2258117 : Blo 666309 2258117 := bbase (se 4 (by rfl) ⟨211698, by rfl⟩ : syracuseStep 2258117 = 423397) (by norm_num)
theorem B750793 : Blo 666309 750793 := bbase (se 2 (by rfl) ⟨281547, by rfl⟩ : syracuseStep 750793 = 563095) (by norm_num)
theorem B750829 : Blo 666309 750829 := bbase (se 3 (by rfl) ⟨140780, by rfl⟩ : syracuseStep 750829 = 281561) (by norm_num)
theorem B1504493 : Blo 666309 1504493 := bbase (se 3 (by rfl) ⟨282092, by rfl⟩ : syracuseStep 1504493 = 564185) (by norm_num)
theorem B1602821 : Blo 666309 1602821 := bbase (se 4 (by rfl) ⟨150264, by rfl⟩ : syracuseStep 1602821 = 300529) (by norm_num)
theorem B750865 : Blo 666309 750865 := bbase (se 2 (by rfl) ⟨281574, by rfl⟩ : syracuseStep 750865 = 563149) (by norm_num)
theorem B1144109 : Blo 666309 1144109 := bbase (se 3 (by rfl) ⟨214520, by rfl⟩ : syracuseStep 1144109 = 429041) (by norm_num)
theorem B750901 : Blo 666309 750901 := bbase (se 5 (by rfl) ⟨35198, by rfl⟩ : syracuseStep 750901 = 70397) (by norm_num)
theorem B1504565 : Blo 666309 1504565 := bbase (se 5 (by rfl) ⟨70526, by rfl⟩ : syracuseStep 1504565 = 141053) (by norm_num)
theorem B3437909 : Blo 666309 3437909 := bbase (se 13 (by rfl) ⟨629, by rfl⟩ : syracuseStep 3437909 = 1259) (by norm_num)
theorem B750937 : Blo 666309 750937 := bbase (se 2 (by rfl) ⟨281601, by rfl⟩ : syracuseStep 750937 = 563203) (by norm_num)
theorem B750973 : Blo 666309 750973 := bbase (se 3 (by rfl) ⟨140807, by rfl⟩ : syracuseStep 750973 = 281615) (by norm_num)
theorem B1504637 : Blo 666309 1504637 := bbase (se 3 (by rfl) ⟨282119, by rfl⟩ : syracuseStep 1504637 = 564239) (by norm_num)
theorem B751009 : Blo 666309 751009 := bbase (se 2 (by rfl) ⟨281628, by rfl⟩ : syracuseStep 751009 = 563257) (by norm_num)
theorem B751045 : Blo 666309 751045 := bbase (se 4 (by rfl) ⟨70410, by rfl⟩ : syracuseStep 751045 = 140821) (by norm_num)
theorem B1504709 : Blo 666309 1504709 := bbase (se 4 (by rfl) ⟨141066, by rfl⟩ : syracuseStep 1504709 = 282133) (by norm_num)
theorem B751081 : Blo 666309 751081 := bbase (se 2 (by rfl) ⟨281655, by rfl⟩ : syracuseStep 751081 = 563311) (by norm_num)
theorem B751117 : Blo 666309 751117 := bbase (se 3 (by rfl) ⟨140834, by rfl⟩ : syracuseStep 751117 = 281669) (by norm_num)
theorem B1504781 : Blo 666309 1504781 := bbase (se 3 (by rfl) ⟨282146, by rfl⟩ : syracuseStep 1504781 = 564293) (by norm_num)
theorem B1734173 : Blo 666309 1734173 := bbase (se 3 (by rfl) ⟨325157, by rfl⟩ : syracuseStep 1734173 = 650315) (by norm_num)
theorem B751153 : Blo 666309 751153 := bbase (se 2 (by rfl) ⟨281682, by rfl⟩ : syracuseStep 751153 = 563365) (by norm_num)
theorem B751189 : Blo 666309 751189 := bbase (se 8 (by rfl) ⟨4401, by rfl⟩ : syracuseStep 751189 = 8803) (by norm_num)
theorem B1504853 : Blo 666309 1504853 := bbase (se 8 (by rfl) ⟨8817, by rfl⟩ : syracuseStep 1504853 = 17635) (by norm_num)
theorem B2258549 : Blo 666309 2258549 := bbase (se 5 (by rfl) ⟨105869, by rfl⟩ : syracuseStep 2258549 = 211739) (by norm_num)
theorem B751225 : Blo 666309 751225 := bbase (se 2 (by rfl) ⟨281709, by rfl⟩ : syracuseStep 751225 = 563419) (by norm_num)
theorem B1603205 : Blo 666309 1603205 := bbase (se 4 (by rfl) ⟨150300, by rfl⟩ : syracuseStep 1603205 = 300601) (by norm_num)
theorem B751261 : Blo 666309 751261 := bbase (se 3 (by rfl) ⟨140861, by rfl⟩ : syracuseStep 751261 = 281723) (by norm_num)
theorem B1504925 : Blo 666309 1504925 := bbase (se 3 (by rfl) ⟨282173, by rfl⟩ : syracuseStep 1504925 = 564347) (by norm_num)
theorem B751297 : Blo 666309 751297 := bbase (se 2 (by rfl) ⟨281736, by rfl⟩ : syracuseStep 751297 = 563473) (by norm_num)
theorem B784069 : Blo 666309 784069 := bbase (se 4 (by rfl) ⟨73506, by rfl⟩ : syracuseStep 784069 = 147013) (by norm_num)
theorem B751333 : Blo 666309 751333 := bbase (se 4 (by rfl) ⟨70437, by rfl⟩ : syracuseStep 751333 = 140875) (by norm_num)
theorem B1504997 : Blo 666309 1504997 := bbase (se 4 (by rfl) ⟨141093, by rfl⟩ : syracuseStep 1504997 = 282187) (by norm_num)
theorem B751369 : Blo 666309 751369 := bbase (se 2 (by rfl) ⟨281763, by rfl⟩ : syracuseStep 751369 = 563527) (by norm_num)
theorem B2029349 : Blo 666309 2029349 := bbase (se 4 (by rfl) ⟨190251, by rfl⟩ : syracuseStep 2029349 = 380503) (by norm_num)
theorem B751405 : Blo 666309 751405 := bbase (se 3 (by rfl) ⟨140888, by rfl⟩ : syracuseStep 751405 = 281777) (by norm_num)
theorem B1505069 : Blo 666309 1505069 := bbase (se 3 (by rfl) ⟨282200, by rfl⟩ : syracuseStep 1505069 = 564401) (by norm_num)
theorem B751441 : Blo 666309 751441 := bbase (se 2 (by rfl) ⟨281790, by rfl⟩ : syracuseStep 751441 = 563581) (by norm_num)
theorem B751477 : Blo 666309 751477 := bbase (se 5 (by rfl) ⟨35225, by rfl⟩ : syracuseStep 751477 = 70451) (by norm_num)
theorem B1505141 : Blo 666309 1505141 := bbase (se 5 (by rfl) ⟨70553, by rfl⟩ : syracuseStep 1505141 = 141107) (by norm_num)
theorem B751513 : Blo 666309 751513 := bbase (se 2 (by rfl) ⟨281817, by rfl⟩ : syracuseStep 751513 = 563635) (by norm_num)
theorem B1603493 : Blo 666309 1603493 := bbase (se 4 (by rfl) ⟨150327, by rfl⟩ : syracuseStep 1603493 = 300655) (by norm_num)
theorem B751549 : Blo 666309 751549 := bbase (se 3 (by rfl) ⟨140915, by rfl⟩ : syracuseStep 751549 = 281831) (by norm_num)
theorem B1505213 : Blo 666309 1505213 := bbase (se 3 (by rfl) ⟨282227, by rfl⟩ : syracuseStep 1505213 = 564455) (by norm_num)
theorem B1898453 : Blo 666309 1898453 := bbase (se 7 (by rfl) ⟨22247, by rfl⟩ : syracuseStep 1898453 = 44495) (by norm_num)
theorem B751585 : Blo 666309 751585 := bbase (se 2 (by rfl) ⟨281844, by rfl⟩ : syracuseStep 751585 = 563689) (by norm_num)
theorem B751621 : Blo 666309 751621 := bbase (se 4 (by rfl) ⟨70464, by rfl⟩ : syracuseStep 751621 = 140929) (by norm_num)
theorem B1505285 : Blo 666309 1505285 := bbase (se 4 (by rfl) ⟨141120, by rfl⟩ : syracuseStep 1505285 = 282241) (by norm_num)
theorem B2258981 : Blo 666309 2258981 := bbase (se 4 (by rfl) ⟨211779, by rfl⟩ : syracuseStep 2258981 = 423559) (by norm_num)
theorem B751657 : Blo 666309 751657 := bbase (se 2 (by rfl) ⟨281871, by rfl⟩ : syracuseStep 751657 = 563743) (by norm_num)
theorem B751693 : Blo 666309 751693 := bbase (se 3 (by rfl) ⟨140942, by rfl⟩ : syracuseStep 751693 = 281885) (by norm_num)
theorem B1505357 : Blo 666309 1505357 := bbase (se 3 (by rfl) ⟨282254, by rfl⟩ : syracuseStep 1505357 = 564509) (by norm_num)
theorem B751729 : Blo 666309 751729 := bbase (se 2 (by rfl) ⟨281898, by rfl⟩ : syracuseStep 751729 = 563797) (by norm_num)
theorem B12843157 : Blo 666309 12843157 := bbase (se 6 (by rfl) ⟨301011, by rfl⟩ : syracuseStep 12843157 = 602023) (by norm_num)
theorem B751765 : Blo 666309 751765 := bbase (se 6 (by rfl) ⟨17619, by rfl⟩ : syracuseStep 751765 = 35239) (by norm_num)
theorem B1505429 : Blo 666309 1505429 := bbase (se 6 (by rfl) ⟨35283, by rfl⟩ : syracuseStep 1505429 = 70567) (by norm_num)
theorem B1013933 : Blo 666309 1013933 := bbase (se 3 (by rfl) ⟨190112, by rfl⟩ : syracuseStep 1013933 = 380225) (by norm_num)
theorem B751801 : Blo 666309 751801 := bbase (se 2 (by rfl) ⟨281925, by rfl⟩ : syracuseStep 751801 = 563851) (by norm_num)
theorem B751837 : Blo 666309 751837 := bbase (se 3 (by rfl) ⟨140969, by rfl⟩ : syracuseStep 751837 = 281939) (by norm_num)
theorem B1505501 : Blo 666309 1505501 := bbase (se 3 (by rfl) ⟨282281, by rfl⟩ : syracuseStep 1505501 = 564563) (by norm_num)
theorem B1145053 : Blo 666309 1145053 := bbase (se 3 (by rfl) ⟨214697, by rfl⟩ : syracuseStep 1145053 = 429395) (by norm_num)
theorem B751873 : Blo 666309 751873 := bbase (se 2 (by rfl) ⟨281952, by rfl⟩ : syracuseStep 751873 = 563905) (by norm_num)
theorem B751909 : Blo 666309 751909 := bbase (se 4 (by rfl) ⟨70491, by rfl⟩ : syracuseStep 751909 = 140983) (by norm_num)
theorem B1505573 : Blo 666309 1505573 := bbase (se 4 (by rfl) ⟨141147, by rfl⟩ : syracuseStep 1505573 = 282295) (by norm_num)
theorem B751945 : Blo 666309 751945 := bbase (se 2 (by rfl) ⟨281979, by rfl⟩ : syracuseStep 751945 = 563959) (by norm_num)
theorem B751981 : Blo 666309 751981 := bbase (se 3 (by rfl) ⟨140996, by rfl⟩ : syracuseStep 751981 = 281993) (by norm_num)
theorem B1505645 : Blo 666309 1505645 := bbase (se 3 (by rfl) ⟨282308, by rfl⟩ : syracuseStep 1505645 = 564617) (by norm_num)
theorem B752017 : Blo 666309 752017 := bbase (se 2 (by rfl) ⟨282006, by rfl⟩ : syracuseStep 752017 = 564013) (by norm_num)
theorem B752053 : Blo 666309 752053 := bbase (se 5 (by rfl) ⟨35252, by rfl⟩ : syracuseStep 752053 = 70505) (by norm_num)
theorem B1505717 : Blo 666309 1505717 := bbase (se 5 (by rfl) ⟨70580, by rfl⟩ : syracuseStep 1505717 = 141161) (by norm_num)
theorem B2259413 : Blo 666309 2259413 := bbase (se 7 (by rfl) ⟨26477, by rfl⟩ : syracuseStep 2259413 = 52955) (by norm_num)
theorem B752089 : Blo 666309 752089 := bbase (se 2 (by rfl) ⟨282033, by rfl⟩ : syracuseStep 752089 = 564067) (by norm_num)
theorem B752125 : Blo 666309 752125 := bbase (se 3 (by rfl) ⟨141023, by rfl⟩ : syracuseStep 752125 = 282047) (by norm_num)
theorem B1505789 : Blo 666309 1505789 := bbase (se 3 (by rfl) ⟨282335, by rfl⟩ : syracuseStep 1505789 = 564671) (by norm_num)
theorem B752161 : Blo 666309 752161 := bbase (se 2 (by rfl) ⟨282060, by rfl⟩ : syracuseStep 752161 = 564121) (by norm_num)
theorem B752197 : Blo 666309 752197 := bbase (se 4 (by rfl) ⟨70518, by rfl⟩ : syracuseStep 752197 = 141037) (by norm_num)
theorem B1505861 : Blo 666309 1505861 := bbase (se 4 (by rfl) ⟨141174, by rfl⟩ : syracuseStep 1505861 = 282349) (by norm_num)
theorem B752233 : Blo 666309 752233 := bbase (se 2 (by rfl) ⟨282087, by rfl⟩ : syracuseStep 752233 = 564175) (by norm_num)
theorem B752269 : Blo 666309 752269 := bbase (se 3 (by rfl) ⟨141050, by rfl⟩ : syracuseStep 752269 = 282101) (by norm_num)
theorem B1505933 : Blo 666309 1505933 := bbase (se 3 (by rfl) ⟨282362, by rfl⟩ : syracuseStep 1505933 = 564725) (by norm_num)
theorem B752305 : Blo 666309 752305 := bbase (se 2 (by rfl) ⟨282114, by rfl⟩ : syracuseStep 752305 = 564229) (by norm_num)
theorem B948925 : Blo 666309 948925 := bbase (se 3 (by rfl) ⟨177923, by rfl⟩ : syracuseStep 948925 = 355847) (by norm_num)
theorem B752341 : Blo 666309 752341 := bbase (se 7 (by rfl) ⟨8816, by rfl⟩ : syracuseStep 752341 = 17633) (by norm_num)
theorem B1506005 : Blo 666309 1506005 := bbase (se 7 (by rfl) ⟨17648, by rfl⟩ : syracuseStep 1506005 = 35297) (by norm_num)
theorem B2849525 : Blo 666309 2849525 := bbase (se 5 (by rfl) ⟨133571, by rfl⟩ : syracuseStep 2849525 = 267143) (by norm_num)
theorem B752377 : Blo 666309 752377 := bbase (se 2 (by rfl) ⟨282141, by rfl⟩ : syracuseStep 752377 = 564283) (by norm_num)
theorem B752413 : Blo 666309 752413 := bbase (se 3 (by rfl) ⟨141077, by rfl⟩ : syracuseStep 752413 = 282155) (by norm_num)
theorem B1506077 : Blo 666309 1506077 := bbase (se 3 (by rfl) ⟨282389, by rfl⟩ : syracuseStep 1506077 = 564779) (by norm_num)
theorem B752449 : Blo 666309 752449 := bbase (se 2 (by rfl) ⟨282168, by rfl⟩ : syracuseStep 752449 = 564337) (by norm_num)
theorem B752485 : Blo 666309 752485 := bbase (se 4 (by rfl) ⟨70545, by rfl⟩ : syracuseStep 752485 = 141091) (by norm_num)
theorem B1506149 : Blo 666309 1506149 := bbase (se 4 (by rfl) ⟨141201, by rfl⟩ : syracuseStep 1506149 = 282403) (by norm_num)
theorem B2259845 : Blo 666309 2259845 := bbase (se 4 (by rfl) ⟨211860, by rfl⟩ : syracuseStep 2259845 = 423721) (by norm_num)
theorem B752521 : Blo 666309 752521 := bbase (se 2 (by rfl) ⟨282195, by rfl⟩ : syracuseStep 752521 = 564391) (by norm_num)
theorem B3373973 : Blo 666309 3373973 := bbase (se 6 (by rfl) ⟨79077, by rfl⟩ : syracuseStep 3373973 = 158155) (by norm_num)
theorem B752557 : Blo 666309 752557 := bbase (se 3 (by rfl) ⟨141104, by rfl⟩ : syracuseStep 752557 = 282209) (by norm_num)
theorem B1506221 : Blo 666309 1506221 := bbase (se 3 (by rfl) ⟨282416, by rfl⟩ : syracuseStep 1506221 = 564833) (by norm_num)
theorem B752593 : Blo 666309 752593 := bbase (se 2 (by rfl) ⟨282222, by rfl⟩ : syracuseStep 752593 = 564445) (by norm_num)
theorem B752629 : Blo 666309 752629 := bbase (se 5 (by rfl) ⟨35279, by rfl⟩ : syracuseStep 752629 = 70559) (by norm_num)
theorem B1506293 : Blo 666309 1506293 := bbase (se 5 (by rfl) ⟨70607, by rfl⟩ : syracuseStep 1506293 = 141215) (by norm_num)
theorem B949261 : Blo 666309 949261 := bbase (se 3 (by rfl) ⟨177986, by rfl⟩ : syracuseStep 949261 = 355973) (by norm_num)
theorem B752665 : Blo 666309 752665 := bbase (se 2 (by rfl) ⟨282249, by rfl⟩ : syracuseStep 752665 = 564499) (by norm_num)
theorem B752701 : Blo 666309 752701 := bbase (se 3 (by rfl) ⟨141131, by rfl⟩ : syracuseStep 752701 = 282263) (by norm_num)
theorem B1506365 : Blo 666309 1506365 := bbase (se 3 (by rfl) ⟨282443, by rfl⟩ : syracuseStep 1506365 = 564887) (by norm_num)
theorem B752737 : Blo 666309 752737 := bbase (se 2 (by rfl) ⟨282276, by rfl⟩ : syracuseStep 752737 = 564553) (by norm_num)
theorem B752773 : Blo 666309 752773 := bbase (se 4 (by rfl) ⟨70572, by rfl⟩ : syracuseStep 752773 = 141145) (by norm_num)
theorem B1506437 : Blo 666309 1506437 := bbase (se 4 (by rfl) ⟨141228, by rfl⟩ : syracuseStep 1506437 = 282457) (by norm_num)
theorem B752809 : Blo 666309 752809 := bbase (se 2 (by rfl) ⟨282303, by rfl⟩ : syracuseStep 752809 = 564607) (by norm_num)
theorem B752845 : Blo 666309 752845 := bbase (se 3 (by rfl) ⟨141158, by rfl⟩ : syracuseStep 752845 = 282317) (by norm_num)
theorem B1506509 : Blo 666309 1506509 := bbase (se 3 (by rfl) ⟨282470, by rfl⟩ : syracuseStep 1506509 = 564941) (by norm_num)
theorem B949477 : Blo 666309 949477 := bbase (se 4 (by rfl) ⟨89013, by rfl⟩ : syracuseStep 949477 = 178027) (by norm_num)
theorem B752881 : Blo 666309 752881 := bbase (se 2 (by rfl) ⟨282330, by rfl⟩ : syracuseStep 752881 = 564661) (by norm_num)
theorem B752917 : Blo 666309 752917 := bbase (se 6 (by rfl) ⟨17646, by rfl⟩ : syracuseStep 752917 = 35293) (by norm_num)
theorem B1506581 : Blo 666309 1506581 := bbase (se 6 (by rfl) ⟨35310, by rfl⟩ : syracuseStep 1506581 = 70621) (by norm_num)
theorem B2260277 : Blo 666309 2260277 := bbase (se 5 (by rfl) ⟨105950, by rfl⟩ : syracuseStep 2260277 = 211901) (by norm_num)
theorem B752953 : Blo 666309 752953 := bbase (se 2 (by rfl) ⟨282357, by rfl⟩ : syracuseStep 752953 = 564715) (by norm_num)
theorem B752989 : Blo 666309 752989 := bbase (se 3 (by rfl) ⟨141185, by rfl⟩ : syracuseStep 752989 = 282371) (by norm_num)
theorem B1506653 : Blo 666309 1506653 := bbase (se 3 (by rfl) ⟨282497, by rfl⟩ : syracuseStep 1506653 = 564995) (by norm_num)
theorem B753025 : Blo 666309 753025 := bbase (se 2 (by rfl) ⟨282384, by rfl⟩ : syracuseStep 753025 = 564769) (by norm_num)
theorem B753061 : Blo 666309 753061 := bbase (se 4 (by rfl) ⟨70599, by rfl⟩ : syracuseStep 753061 = 141199) (by norm_num)
theorem B1506725 : Blo 666309 1506725 := bbase (se 4 (by rfl) ⟨141255, by rfl⟩ : syracuseStep 1506725 = 282511) (by norm_num)
theorem B3210677 : Blo 666309 3210677 := bbase (se 5 (by rfl) ⟨150500, by rfl⟩ : syracuseStep 3210677 = 301001) (by norm_num)
theorem B753097 : Blo 666309 753097 := bbase (se 2 (by rfl) ⟨282411, by rfl⟩ : syracuseStep 753097 = 564823) (by norm_num)
theorem B753133 : Blo 666309 753133 := bbase (se 3 (by rfl) ⟨141212, by rfl⟩ : syracuseStep 753133 = 282425) (by norm_num)
theorem B1506797 : Blo 666309 1506797 := bbase (se 3 (by rfl) ⟨282524, by rfl⟩ : syracuseStep 1506797 = 565049) (by norm_num)
theorem B1900037 : Blo 666309 1900037 := bbase (se 4 (by rfl) ⟨178128, by rfl⟩ : syracuseStep 1900037 = 356257) (by norm_num)
theorem B753169 : Blo 666309 753169 := bbase (se 2 (by rfl) ⟨282438, by rfl⟩ : syracuseStep 753169 = 564877) (by norm_num)
theorem B3603989 : Blo 666309 3603989 := bbase (se 6 (by rfl) ⟨84468, by rfl⟩ : syracuseStep 3603989 = 168937) (by norm_num)
theorem B753205 : Blo 666309 753205 := bbase (se 5 (by rfl) ⟨35306, by rfl⟩ : syracuseStep 753205 = 70613) (by norm_num)
theorem B1506869 : Blo 666309 1506869 := bbase (se 5 (by rfl) ⟨70634, by rfl⟩ : syracuseStep 1506869 = 141269) (by norm_num)
theorem B753241 : Blo 666309 753241 := bbase (se 2 (by rfl) ⟨282465, by rfl⟩ : syracuseStep 753241 = 564931) (by norm_num)
theorem B949853 : Blo 666309 949853 := bbase (se 3 (by rfl) ⟨178097, by rfl⟩ : syracuseStep 949853 = 356195) (by norm_num)
theorem B753277 : Blo 666309 753277 := bbase (se 3 (by rfl) ⟨141239, by rfl⟩ : syracuseStep 753277 = 282479) (by norm_num)
theorem B1506941 : Blo 666309 1506941 := bbase (se 3 (by rfl) ⟨282551, by rfl⟩ : syracuseStep 1506941 = 565103) (by norm_num)
theorem B1015429 : Blo 666309 1015429 := bbase (se 4 (by rfl) ⟨95196, by rfl⟩ : syracuseStep 1015429 = 190393) (by norm_num)
theorem B917149 : Blo 666309 917149 := bbase (se 3 (by rfl) ⟨171965, by rfl⟩ : syracuseStep 917149 = 343931) (by norm_num)
theorem B753313 : Blo 666309 753313 := bbase (se 2 (by rfl) ⟨282492, by rfl⟩ : syracuseStep 753313 = 564985) (by norm_num)
theorem B753349 : Blo 666309 753349 := bbase (se 4 (by rfl) ⟨70626, by rfl⟩ : syracuseStep 753349 = 141253) (by norm_num)
theorem B1507013 : Blo 666309 1507013 := bbase (se 4 (by rfl) ⟨141282, by rfl⟩ : syracuseStep 1507013 = 282565) (by norm_num)
theorem B1015501 : Blo 666309 1015501 := bbase (se 3 (by rfl) ⟨190406, by rfl⟩ : syracuseStep 1015501 = 380813) (by norm_num)
theorem B2260709 : Blo 666309 2260709 := bbase (se 4 (by rfl) ⟨211941, by rfl⟩ : syracuseStep 2260709 = 423883) (by norm_num)
theorem B753385 : Blo 666309 753385 := bbase (se 2 (by rfl) ⟨282519, by rfl⟩ : syracuseStep 753385 = 565039) (by norm_num)
theorem B753421 : Blo 666309 753421 := bbase (se 3 (by rfl) ⟨141266, by rfl⟩ : syracuseStep 753421 = 282533) (by norm_num)
theorem B1507085 : Blo 666309 1507085 := bbase (se 3 (by rfl) ⟨282578, by rfl⟩ : syracuseStep 1507085 = 565157) (by norm_num)
theorem B753457 : Blo 666309 753457 := bbase (se 2 (by rfl) ⟨282546, by rfl⟩ : syracuseStep 753457 = 565093) (by norm_num)
theorem B753493 : Blo 666309 753493 := bbase (se 9 (by rfl) ⟨2207, by rfl⟩ : syracuseStep 753493 = 4415) (by norm_num)
theorem B1507157 : Blo 666309 1507157 := bbase (se 9 (by rfl) ⟨4415, by rfl⟩ : syracuseStep 1507157 = 8831) (by norm_num)
theorem B753529 : Blo 666309 753529 := bbase (se 2 (by rfl) ⟨282573, by rfl⟩ : syracuseStep 753529 = 565147) (by norm_num)
theorem B753565 : Blo 666309 753565 := bbase (se 3 (by rfl) ⟨141293, by rfl⟩ : syracuseStep 753565 = 282587) (by norm_num)
theorem B1507229 : Blo 666309 1507229 := bbase (se 3 (by rfl) ⟨282605, by rfl⟩ : syracuseStep 1507229 = 565211) (by norm_num)
theorem B753601 : Blo 666309 753601 := bbase (se 2 (by rfl) ⟨282600, by rfl⟩ : syracuseStep 753601 = 565201) (by norm_num)
theorem B4816853 : Blo 666309 4816853 := bbase (se 7 (by rfl) ⟨56447, by rfl⟩ : syracuseStep 4816853 = 112895) (by norm_num)
theorem B753637 : Blo 666309 753637 := bbase (se 4 (by rfl) ⟨70653, by rfl⟩ : syracuseStep 753637 = 141307) (by norm_num)
theorem B1507301 : Blo 666309 1507301 := bbase (se 4 (by rfl) ⟨141309, by rfl⟩ : syracuseStep 1507301 = 282619) (by norm_num)
theorem B16482325 : Blo 666309 16482325 := bstep (se 6 (by rfl) ⟨386304, by rfl⟩ : syracuseStep 16482325 = 772609) B772609
theorem B1507409 : Blo 666309 1507409 := bstep (se 2 (by rfl) ⟨565278, by rfl⟩ : syracuseStep 1507409 = 1130557) B1130557
theorem B1507427 : Blo 666309 1507427 := bstep (se 1 (by rfl) ⟨1130570, by rfl⟩ : syracuseStep 1507427 = 2261141) B2261141
theorem B753763 : Blo 666309 753763 := bstep (se 1 (by rfl) ⟨565322, by rfl⟩ : syracuseStep 753763 = 1130645) B1130645
theorem B1900685 : Blo 666309 1900685 := bstep (se 3 (by rfl) ⟨356378, by rfl⟩ : syracuseStep 1900685 = 712757) B712757
theorem B753907 : Blo 666309 753907 := bstep (se 1 (by rfl) ⟨565430, by rfl⟩ : syracuseStep 753907 = 1130861) B1130861
theorem B950611 : Blo 666309 950611 := bstep (se 1 (by rfl) ⟨712958, by rfl⟩ : syracuseStep 950611 = 1425917) B1425917
theorem B2261357 : Blo 666309 2261357 := bstep (se 3 (by rfl) ⟨424004, by rfl⟩ : syracuseStep 2261357 = 848009) B848009
theorem B1507697 : Blo 666309 1507697 := bstep (se 2 (by rfl) ⟨565386, by rfl⟩ : syracuseStep 1507697 = 1130773) B1130773
theorem B1507715 : Blo 666309 1507715 := bstep (se 1 (by rfl) ⟨1130786, by rfl⟩ : syracuseStep 1507715 = 2261573) B2261573
theorem B754051 : Blo 666309 754051 := bstep (se 1 (by rfl) ⟨565538, by rfl⟩ : syracuseStep 754051 = 1131077) B1131077
theorem B2261411 : Blo 666309 2261411 := bstep (se 1 (by rfl) ⟨1696058, by rfl⟩ : syracuseStep 2261411 = 3392117) B3392117
theorem B950707 : Blo 666309 950707 := bstep (se 1 (by rfl) ⟨713030, by rfl⟩ : syracuseStep 950707 = 1426061) B1426061
theorem B1507889 : Blo 666309 1507889 := bstep (se 2 (by rfl) ⟨565458, by rfl⟩ : syracuseStep 1507889 = 1130917) B1130917
theorem B1507985 : Blo 666309 1507985 := bstep (se 2 (by rfl) ⟨565494, by rfl⟩ : syracuseStep 1507985 = 1130989) B1130989
theorem B1508003 : Blo 666309 1508003 := bstep (se 1 (by rfl) ⟨1131002, by rfl⟩ : syracuseStep 1508003 = 2262005) B2262005
theorem B2261681 : Blo 666309 2261681 := bstep (se 2 (by rfl) ⟨848130, by rfl⟩ : syracuseStep 2261681 = 1696261) B1696261
theorem B3605219 : Blo 666309 3605219 := bstep (se 1 (by rfl) ⟨2703914, by rfl⟩ : syracuseStep 3605219 = 5407829) B5407829
theorem B951203 : Blo 666309 951203 := bstep (se 1 (by rfl) ⟨713402, by rfl⟩ : syracuseStep 951203 = 1426805) B1426805
theorem B1901677 : Blo 666309 1901677 := bstep (se 3 (by rfl) ⟨356564, by rfl⟩ : syracuseStep 1901677 = 713129) B713129
theorem B3376241 : Blo 666309 3376241 := bstep (se 2 (by rfl) ⟨1266090, by rfl⟩ : syracuseStep 3376241 = 2532181) B2532181
theorem B2262221 : Blo 666309 2262221 := bstep (se 3 (by rfl) ⟨424166, by rfl⟩ : syracuseStep 2262221 = 848333) B848333
theorem B2262275 : Blo 666309 2262275 := bstep (se 1 (by rfl) ⟨1696706, by rfl⟩ : syracuseStep 2262275 = 3393413) B3393413
theorem B3802373 : Blo 666309 3802373 := bstep (se 4 (by rfl) ⟨356472, by rfl⟩ : syracuseStep 3802373 = 712945) B712945
theorem B7603469 : Blo 666309 7603469 := bstep (se 3 (by rfl) ⟨1425650, by rfl⟩ : syracuseStep 7603469 = 2851301) B2851301
theorem B1836323 : Blo 666309 1836323 := bstep (se 1 (by rfl) ⟨1377242, by rfl⟩ : syracuseStep 1836323 = 2754485) B2754485
theorem B1803725 : Blo 666309 1803725 := bstep (se 3 (by rfl) ⟨338198, by rfl⟩ : syracuseStep 1803725 = 676397) B676397
theorem B951841 : Blo 666309 951841 := bstep (se 2 (by rfl) ⟨356940, by rfl⟩ : syracuseStep 951841 = 713881) B713881
theorem B3606257 : Blo 666309 3606257 := bstep (se 2 (by rfl) ⟨1352346, by rfl⟩ : syracuseStep 3606257 = 2704693) B2704693
theorem B6096653 : Blo 666309 6096653 := bstep (se 3 (by rfl) ⟨1143122, by rfl⟩ : syracuseStep 6096653 = 2286245) B2286245
theorem B952177 : Blo 666309 952177 := bstep (se 2 (by rfl) ⟨357066, by rfl⟩ : syracuseStep 952177 = 714133) B714133
theorem B3803057 : Blo 666309 3803057 := bstep (se 2 (by rfl) ⟨1426146, by rfl⟩ : syracuseStep 3803057 = 2852293) B2852293
theorem B1607779 : Blo 666309 1607779 := bstep (se 1 (by rfl) ⟨1205834, by rfl⟩ : syracuseStep 1607779 = 2411669) B2411669
theorem B1018019 : Blo 666309 1018019 := bstep (se 1 (by rfl) ⟨763514, by rfl⟩ : syracuseStep 1018019 = 1527029) B1527029
theorem B2033873 : Blo 666309 2033873 := bstep (se 2 (by rfl) ⟨762702, by rfl⟩ : syracuseStep 2033873 = 1525405) B1525405
theorem B1083619 : Blo 666309 1083619 := bstep (se 1 (by rfl) ⟨812714, by rfl⟩ : syracuseStep 1083619 = 1625429) B1625429
theorem B952769 : Blo 666309 952769 := bstep (se 2 (by rfl) ⟨357288, by rfl⟩ : syracuseStep 952769 = 714577) B714577
theorem B2034115 : Blo 666309 2034115 := bstep (se 1 (by rfl) ⟨1525586, by rfl⟩ : syracuseStep 2034115 = 3051173) B3051173
theorem B1804817 : Blo 666309 1804817 := bstep (se 2 (by rfl) ⟨676806, by rfl⟩ : syracuseStep 1804817 = 1353613) B1353613
theorem B3377699 : Blo 666309 3377699 := bstep (se 1 (by rfl) ⟨2533274, by rfl⟩ : syracuseStep 3377699 = 5066549) B5066549
theorem B3050225 : Blo 666309 3050225 := bstep (se 2 (by rfl) ⟨1143834, by rfl⟩ : syracuseStep 3050225 = 2287669) B2287669
theorem B1903409 : Blo 666309 1903409 := bstep (se 2 (by rfl) ⟨713778, by rfl⟩ : syracuseStep 1903409 = 1427557) B1427557
theorem B953299 : Blo 666309 953299 := bstep (se 1 (by rfl) ⟨714974, by rfl⟩ : syracuseStep 953299 = 1429949) B1429949
theorem B1018835 : Blo 666309 1018835 := bstep (se 1 (by rfl) ⟨764126, by rfl⟩ : syracuseStep 1018835 = 1528253) B1528253
theorem B1903601 : Blo 666309 1903601 := bstep (se 2 (by rfl) ⟨713850, by rfl⟩ : syracuseStep 1903601 = 1427701) B1427701
theorem B855043 : Blo 666309 855043 := bstep (se 1 (by rfl) ⟨641282, by rfl⟩ : syracuseStep 855043 = 1282565) B1282565
theorem B953635 : Blo 666309 953635 := bstep (se 1 (by rfl) ⟨715226, by rfl⟩ : syracuseStep 953635 = 1430453) B1430453
theorem B3378509 : Blo 666309 3378509 := bstep (se 3 (by rfl) ⟨633470, by rfl⟩ : syracuseStep 3378509 = 1266941) B1266941
theorem B3804515 : Blo 666309 3804515 := bstep (se 1 (by rfl) ⟨2853386, by rfl⟩ : syracuseStep 3804515 = 5706773) B5706773
theorem B1609393 : Blo 666309 1609393 := bstep (se 2 (by rfl) ⟨603522, by rfl⟩ : syracuseStep 1609393 = 1207045) B1207045
theorem B954193 : Blo 666309 954193 := bstep (se 2 (by rfl) ⟨357822, by rfl⟩ : syracuseStep 954193 = 715645) B715645
theorem B1085281 : Blo 666309 1085281 := bstep (se 2 (by rfl) ⟨406980, by rfl⟩ : syracuseStep 1085281 = 813961) B813961
theorem B3051377 : Blo 666309 3051377 := bstep (se 2 (by rfl) ⟨1144266, by rfl⟩ : syracuseStep 3051377 = 2288533) B2288533
theorem B954227 : Blo 666309 954227 := bstep (se 1 (by rfl) ⟨715670, by rfl⟩ : syracuseStep 954227 = 1431341) B1431341
theorem B1085329 : Blo 666309 1085329 := bstep (se 2 (by rfl) ⟨406998, by rfl⟩ : syracuseStep 1085329 = 813997) B813997
theorem B1904593 : Blo 666309 1904593 := bstep (se 2 (by rfl) ⟨714222, by rfl⟩ : syracuseStep 1904593 = 1428445) B1428445
theorem B2854925 : Blo 666309 2854925 := bstep (se 3 (by rfl) ⟨535298, by rfl⟩ : syracuseStep 2854925 = 1070597) B1070597
theorem B36606005 : Blo 666309 36606005 := bstep (se 5 (by rfl) ⟨1715906, by rfl⟩ : syracuseStep 36606005 = 3431813) B3431813
theorem B4067405 : Blo 666309 4067405 := bstep (se 3 (by rfl) ⟨762638, by rfl⟩ : syracuseStep 4067405 = 1525277) B1525277
theorem B7606385 : Blo 666309 7606385 := bstep (se 2 (by rfl) ⟨2852394, by rfl⟩ : syracuseStep 7606385 = 5704789) B5704789
theorem B1904867 : Blo 666309 1904867 := bstep (se 1 (by rfl) ⟨1428650, by rfl⟩ : syracuseStep 1904867 = 2857301) B2857301
theorem B5706125 : Blo 666309 5706125 := bstep (se 3 (by rfl) ⟨1069898, by rfl⟩ : syracuseStep 5706125 = 2139797) B2139797
theorem B1905059 : Blo 666309 1905059 := bstep (se 1 (by rfl) ⟨1428794, by rfl⟩ : syracuseStep 1905059 = 2857589) B2857589
theorem B1085905 : Blo 666309 1085905 := bstep (se 2 (by rfl) ⟨407214, by rfl⟩ : syracuseStep 1085905 = 814429) B814429
theorem B1807043 : Blo 666309 1807043 := bstep (se 1 (by rfl) ⟨1355282, by rfl⟩ : syracuseStep 1807043 = 2710565) B2710565
theorem B5084045 : Blo 666309 5084045 := bstep (se 3 (by rfl) ⟨953258, by rfl⟩ : syracuseStep 5084045 = 1906517) B1906517
theorem B1905869 : Blo 666309 1905869 := bstep (se 3 (by rfl) ⟨357350, by rfl⟩ : syracuseStep 1905869 = 714701) B714701
theorem B1906051 : Blo 666309 1906051 := bstep (se 1 (by rfl) ⟨1429538, by rfl⟩ : syracuseStep 1906051 = 2859077) B2859077
theorem B2135555 : Blo 666309 2135555 := bstep (se 1 (by rfl) ⟨1601666, by rfl⟩ : syracuseStep 2135555 = 3203333) B3203333
theorem B1709923 : Blo 666309 1709923 := bstep (se 1 (by rfl) ⟨1282442, by rfl⟩ : syracuseStep 1709923 = 2564885) B2564885
theorem B1906541 : Blo 666309 1906541 := bstep (se 3 (by rfl) ⟨357476, by rfl⟩ : syracuseStep 1906541 = 714953) B714953
theorem B4396963 : Blo 666309 4396963 := bstep (se 1 (by rfl) ⟨3297722, by rfl⟩ : syracuseStep 4396963 = 6595445) B6595445
theorem B1218577 : Blo 666309 1218577 := bstep (se 2 (by rfl) ⟨456966, by rfl⟩ : syracuseStep 1218577 = 913933) B913933
theorem B2136145 : Blo 666309 2136145 := bstep (se 2 (by rfl) ⟨801054, by rfl⟩ : syracuseStep 2136145 = 1602109) B1602109
theorem B1710193 : Blo 666309 1710193 := bstep (se 2 (by rfl) ⟨641322, by rfl⟩ : syracuseStep 1710193 = 1282645) B1282645
theorem B1448099 : Blo 666309 1448099 := bstep (se 1 (by rfl) ⟨1086074, by rfl⟩ : syracuseStep 1448099 = 2172149) B2172149
theorem B3381425 : Blo 666309 3381425 := bstep (se 2 (by rfl) ⟨1268034, by rfl⟩ : syracuseStep 3381425 = 2536069) B2536069
theorem B7706933 : Blo 666309 7706933 := bstep (se 5 (by rfl) ⟨361262, by rfl⟩ : syracuseStep 7706933 = 722525) B722525
theorem B9247117 : Blo 666309 9247117 := bstep (se 3 (by rfl) ⟨1733834, by rfl⟩ : syracuseStep 9247117 = 3467669) B3467669
theorem B3807749 : Blo 666309 3807749 := bstep (se 4 (by rfl) ⟨356976, by rfl⟩ : syracuseStep 3807749 = 713953) B713953
theorem B3808205 : Blo 666309 3808205 := bstep (se 3 (by rfl) ⟨714038, by rfl⟩ : syracuseStep 3808205 = 1428077) B1428077
theorem B2169841 : Blo 666309 2169841 := bstep (se 2 (by rfl) ⟨813690, by rfl⟩ : syracuseStep 2169841 = 1627381) B1627381
theorem B1907725 : Blo 666309 1907725 := bstep (se 3 (by rfl) ⟨357698, by rfl⟩ : syracuseStep 1907725 = 715397) B715397
theorem B859267 : Blo 666309 859267 := bstep (se 1 (by rfl) ⟨644450, by rfl⟩ : syracuseStep 859267 = 1288901) B1288901
theorem B2170253 : Blo 666309 2170253 := bstep (se 3 (by rfl) ⟨406922, by rfl⟩ : syracuseStep 2170253 = 813845) B813845
theorem B2530723 : Blo 666309 2530723 := bstep (se 1 (by rfl) ⟨1898042, by rfl⟩ : syracuseStep 2530723 = 3796085) B3796085
theorem B3382883 : Blo 666309 3382883 := bstep (se 1 (by rfl) ⟨2537162, by rfl⟩ : syracuseStep 3382883 = 5074325) B5074325
theorem B3612401 : Blo 666309 3612401 := bstep (se 2 (by rfl) ⟨1354650, by rfl⟩ : syracuseStep 3612401 = 2709301) B2709301
theorem B5086961 : Blo 666309 5086961 := bstep (se 2 (by rfl) ⟨1907610, by rfl⟩ : syracuseStep 5086961 = 3815221) B3815221
theorem B761827 : Blo 666309 761827 := bstep (se 1 (by rfl) ⟨571370, by rfl⟩ : syracuseStep 761827 = 1142741) B1142741
theorem B1908785 : Blo 666309 1908785 := bstep (se 2 (by rfl) ⟨715794, by rfl⟩ : syracuseStep 1908785 = 1431589) B1431589
theorem B5480561 : Blo 666309 5480561 := bstep (se 2 (by rfl) ⟨2055210, by rfl⟩ : syracuseStep 5480561 = 4110421) B4110421
theorem B2859299 : Blo 666309 2859299 := bstep (se 1 (by rfl) ⟨2144474, by rfl⟩ : syracuseStep 2859299 = 4288949) B4288949
theorem B11411765 : Blo 666309 11411765 := bstep (se 5 (by rfl) ⟨534926, by rfl⟩ : syracuseStep 11411765 = 1069853) B1069853
theorem B3383693 : Blo 666309 3383693 := bstep (se 3 (by rfl) ⟨634442, by rfl⟩ : syracuseStep 3383693 = 1268885) B1268885
theorem B1810829 : Blo 666309 1810829 := bstep (se 3 (by rfl) ⟨339530, by rfl⟩ : syracuseStep 1810829 = 679061) B679061
theorem B4563569 : Blo 666309 4563569 := bstep (se 2 (by rfl) ⟨1711338, by rfl⟩ : syracuseStep 4563569 = 3422677) B3422677
theorem B2138989 : Blo 666309 2138989 := bstep (se 3 (by rfl) ⟨401060, by rfl⟩ : syracuseStep 2138989 = 802121) B802121
theorem B762739 : Blo 666309 762739 := bstep (se 1 (by rfl) ⟨572054, by rfl⟩ : syracuseStep 762739 = 1144109) B1144109
theorem B1156115 : Blo 666309 1156115 := bstep (se 1 (by rfl) ⟨867086, by rfl⟩ : syracuseStep 1156115 = 1734173) B1734173
theorem B6431885 : Blo 666309 6431885 := bstep (se 3 (by rfl) ⟨1205978, by rfl⟩ : syracuseStep 6431885 = 2411957) B2411957
theorem B1352899 : Blo 666309 1352899 := bstep (se 1 (by rfl) ⟨1014674, by rfl⟩ : syracuseStep 1352899 = 2029349) B2029349
theorem B1648081 : Blo 666309 1648081 := bstep (se 2 (by rfl) ⟨618030, by rfl⟩ : syracuseStep 1648081 = 1236061) B1236061
theorem B2532941 : Blo 666309 2532941 := bstep (se 3 (by rfl) ⟨474926, by rfl⟩ : syracuseStep 2532941 = 949853) B949853
theorem B3811121 : Blo 666309 3811121 := bstep (se 2 (by rfl) ⟨1429170, by rfl⟩ : syracuseStep 3811121 = 2858341) B2858341
theorem B2861041 : Blo 666309 2861041 := bstep (se 2 (by rfl) ⟨1072890, by rfl⟩ : syracuseStep 2861041 = 2145781) B2145781
theorem B1714193 : Blo 666309 1714193 := bstep (se 2 (by rfl) ⟨642822, by rfl⟩ : syracuseStep 1714193 = 1285645) B1285645
theorem B1124401 : Blo 666309 1124401 := bstep (se 2 (by rfl) ⟨421650, by rfl⟩ : syracuseStep 1124401 = 843301) B843301
theorem B1124435 : Blo 666309 1124435 := bstep (se 1 (by rfl) ⟨843326, by rfl⟩ : syracuseStep 1124435 = 1686653) B1686653
theorem B1353905 : Blo 666309 1353905 := bstep (se 2 (by rfl) ⟨507714, by rfl⟩ : syracuseStep 1353905 = 1015429) B1015429
theorem B1222865 : Blo 666309 1222865 := bstep (se 2 (by rfl) ⟨458574, by rfl⟩ : syracuseStep 1222865 = 917149) B917149
theorem B1124563 : Blo 666309 1124563 := bstep (se 1 (by rfl) ⟨843422, by rfl⟩ : syracuseStep 1124563 = 1686845) B1686845
theorem B7416035 : Blo 666309 7416035 := bstep (se 1 (by rfl) ⟨5562026, by rfl⟩ : syracuseStep 7416035 = 11124053) B11124053
theorem B1354001 : Blo 666309 1354001 := bstep (se 2 (by rfl) ⟨507750, by rfl⟩ : syracuseStep 1354001 = 1015501) B1015501
theorem B2140451 : Blo 666309 2140451 := bstep (se 1 (by rfl) ⟨1605338, by rfl⟩ : syracuseStep 2140451 = 3210677) B3210677
theorem B1124705 : Blo 666309 1124705 := bstep (se 2 (by rfl) ⟨421764, by rfl⟩ : syracuseStep 1124705 = 843529) B843529
theorem B2402659 : Blo 666309 2402659 := bstep (se 1 (by rfl) ⟨1801994, by rfl⟩ : syracuseStep 2402659 = 3603989) B3603989
theorem B1124833 : Blo 666309 1124833 := bstep (se 2 (by rfl) ⟨421812, by rfl⟩ : syracuseStep 1124833 = 843625) B843625
theorem B1124867 : Blo 666309 1124867 := bstep (se 1 (by rfl) ⟨843650, by rfl⟩ : syracuseStep 1124867 = 1687301) B1687301
theorem B1124995 : Blo 666309 1124995 := bstep (se 1 (by rfl) ⟨843746, by rfl⟩ : syracuseStep 1124995 = 1687493) B1687493
theorem B666323 : Blo 666309 666323 := bstep (se 1 (by rfl) ⟨499742, by rfl⟩ : syracuseStep 666323 = 999485) B999485
theorem B666339 : Blo 666309 666339 := bstep (se 1 (by rfl) ⟨499754, by rfl⟩ : syracuseStep 666339 = 999509) B999509
theorem B666355 : Blo 666309 666355 := bstep (se 1 (by rfl) ⟨499766, by rfl⟩ : syracuseStep 666355 = 999533) B999533
theorem B666371 : Blo 666309 666371 := bstep (se 1 (by rfl) ⟨499778, by rfl⟩ : syracuseStep 666371 = 999557) B999557
theorem B1125137 : Blo 666309 1125137 := bstep (se 2 (by rfl) ⟨421926, by rfl⟩ : syracuseStep 1125137 = 843853) B843853
theorem B666387 : Blo 666309 666387 := bstep (se 1 (by rfl) ⟨499790, by rfl⟩ : syracuseStep 666387 = 999581) B999581
theorem B666403 : Blo 666309 666403 := bstep (se 1 (by rfl) ⟨499802, by rfl⟩ : syracuseStep 666403 = 999605) B999605
theorem B2403121 : Blo 666309 2403121 := bstep (se 2 (by rfl) ⟨901170, by rfl⟩ : syracuseStep 2403121 = 1802341) B1802341
theorem B666419 : Blo 666309 666419 := bstep (se 1 (by rfl) ⟨499814, by rfl⟩ : syracuseStep 666419 = 999629) B999629
theorem B666435 : Blo 666309 666435 := bstep (se 1 (by rfl) ⟨499826, by rfl⟩ : syracuseStep 666435 = 999653) B999653
theorem B666451 : Blo 666309 666451 := bstep (se 1 (by rfl) ⟨499838, by rfl⟩ : syracuseStep 666451 = 999677) B999677
theorem B666467 : Blo 666309 666467 := bstep (se 1 (by rfl) ⟨499850, by rfl⟩ : syracuseStep 666467 = 999701) B999701
theorem B666483 : Blo 666309 666483 := bstep (se 1 (by rfl) ⟨499862, by rfl⟩ : syracuseStep 666483 = 999725) B999725
theorem B666499 : Blo 666309 666499 := bstep (se 1 (by rfl) ⟨499874, by rfl⟩ : syracuseStep 666499 = 999749) B999749
theorem B1125265 : Blo 666309 1125265 := bstep (se 2 (by rfl) ⟨421974, by rfl⟩ : syracuseStep 1125265 = 843949) B843949
theorem B666515 : Blo 666309 666515 := bstep (se 1 (by rfl) ⟨499886, by rfl⟩ : syracuseStep 666515 = 999773) B999773
theorem B666531 : Blo 666309 666531 := bstep (se 1 (by rfl) ⟨499898, by rfl⟩ : syracuseStep 666531 = 999797) B999797
theorem B666547 : Blo 666309 666547 := bstep (se 1 (by rfl) ⟨499910, by rfl⟩ : syracuseStep 666547 = 999821) B999821
theorem B1125299 : Blo 666309 1125299 := bstep (se 1 (by rfl) ⟨843974, by rfl⟩ : syracuseStep 1125299 = 1687949) B1687949
theorem B666563 : Blo 666309 666563 := bstep (se 1 (by rfl) ⟨499922, by rfl⟩ : syracuseStep 666563 = 999845) B999845
theorem B666579 : Blo 666309 666579 := bstep (se 1 (by rfl) ⟨499934, by rfl⟩ : syracuseStep 666579 = 999869) B999869
theorem B666595 : Blo 666309 666595 := bstep (se 1 (by rfl) ⟨499946, by rfl⟩ : syracuseStep 666595 = 999893) B999893
theorem B666611 : Blo 666309 666611 := bstep (se 1 (by rfl) ⟨499958, by rfl⟩ : syracuseStep 666611 = 999917) B999917
theorem B666627 : Blo 666309 666627 := bstep (se 1 (by rfl) ⟨499970, by rfl⟩ : syracuseStep 666627 = 999941) B999941
theorem B666643 : Blo 666309 666643 := bstep (se 1 (by rfl) ⟨499982, by rfl⟩ : syracuseStep 666643 = 999965) B999965
theorem B666659 : Blo 666309 666659 := bstep (se 1 (by rfl) ⟨499994, by rfl⟩ : syracuseStep 666659 = 999989) B999989
theorem B666675 : Blo 666309 666675 := bstep (se 1 (by rfl) ⟨500006, by rfl⟩ : syracuseStep 666675 = 1000013) B1000013
theorem B1125427 : Blo 666309 1125427 := bstep (se 1 (by rfl) ⟨844070, by rfl⟩ : syracuseStep 1125427 = 1688141) B1688141
theorem B666691 : Blo 666309 666691 := bstep (se 1 (by rfl) ⟨500018, by rfl⟩ : syracuseStep 666691 = 1000037) B1000037
theorem B666707 : Blo 666309 666707 := bstep (se 1 (by rfl) ⟨500030, by rfl⟩ : syracuseStep 666707 = 1000061) B1000061
theorem B666723 : Blo 666309 666723 := bstep (se 1 (by rfl) ⟨500042, by rfl⟩ : syracuseStep 666723 = 1000085) B1000085
theorem B666739 : Blo 666309 666739 := bstep (se 1 (by rfl) ⟨500054, by rfl⟩ : syracuseStep 666739 = 1000109) B1000109
theorem B666755 : Blo 666309 666755 := bstep (se 1 (by rfl) ⟨500066, by rfl⟩ : syracuseStep 666755 = 1000133) B1000133
theorem B666771 : Blo 666309 666771 := bstep (se 1 (by rfl) ⟨500078, by rfl⟩ : syracuseStep 666771 = 1000157) B1000157
theorem B666787 : Blo 666309 666787 := bstep (se 1 (by rfl) ⟨500090, by rfl⟩ : syracuseStep 666787 = 1000181) B1000181
theorem B666803 : Blo 666309 666803 := bstep (se 1 (by rfl) ⟨500102, by rfl⟩ : syracuseStep 666803 = 1000205) B1000205
theorem B1125569 : Blo 666309 1125569 := bstep (se 2 (by rfl) ⟨422088, by rfl⟩ : syracuseStep 1125569 = 844177) B844177
theorem B666819 : Blo 666309 666819 := bstep (se 1 (by rfl) ⟨500114, by rfl⟩ : syracuseStep 666819 = 1000229) B1000229
theorem B666835 : Blo 666309 666835 := bstep (se 1 (by rfl) ⟨500126, by rfl⟩ : syracuseStep 666835 = 1000253) B1000253
theorem B666851 : Blo 666309 666851 := bstep (se 1 (by rfl) ⟨500138, by rfl⟩ : syracuseStep 666851 = 1000277) B1000277
theorem B3812579 : Blo 666309 3812579 := bstep (se 1 (by rfl) ⟨2859434, by rfl⟩ : syracuseStep 3812579 = 5718869) B5718869
theorem B3386609 : Blo 666309 3386609 := bstep (se 2 (by rfl) ⟨1269978, by rfl⟩ : syracuseStep 3386609 = 2539957) B2539957
theorem B666867 : Blo 666309 666867 := bstep (se 1 (by rfl) ⟨500150, by rfl⟩ : syracuseStep 666867 = 1000301) B1000301
theorem B666883 : Blo 666309 666883 := bstep (se 1 (by rfl) ⟨500162, by rfl⟩ : syracuseStep 666883 = 1000325) B1000325
theorem B1223939 : Blo 666309 1223939 := bstep (se 1 (by rfl) ⟨917954, by rfl⟩ : syracuseStep 1223939 = 1835909) B1835909
theorem B666899 : Blo 666309 666899 := bstep (se 1 (by rfl) ⟨500174, by rfl⟩ : syracuseStep 666899 = 1000349) B1000349
theorem B666915 : Blo 666309 666915 := bstep (se 1 (by rfl) ⟨500186, by rfl⟩ : syracuseStep 666915 = 1000373) B1000373
theorem B666931 : Blo 666309 666931 := bstep (se 1 (by rfl) ⟨500198, by rfl⟩ : syracuseStep 666931 = 1000397) B1000397
theorem B1125697 : Blo 666309 1125697 := bstep (se 2 (by rfl) ⟨422136, by rfl⟩ : syracuseStep 1125697 = 844273) B844273
theorem B666947 : Blo 666309 666947 := bstep (se 1 (by rfl) ⟨500210, by rfl⟩ : syracuseStep 666947 = 1000421) B1000421
theorem B666963 : Blo 666309 666963 := bstep (se 1 (by rfl) ⟨500222, by rfl⟩ : syracuseStep 666963 = 1000445) B1000445
theorem B666979 : Blo 666309 666979 := bstep (se 1 (by rfl) ⟨500234, by rfl⟩ : syracuseStep 666979 = 1000469) B1000469
theorem B1125731 : Blo 666309 1125731 := bstep (se 1 (by rfl) ⟨844298, by rfl⟩ : syracuseStep 1125731 = 1688597) B1688597
theorem B666995 : Blo 666309 666995 := bstep (se 1 (by rfl) ⟨500246, by rfl⟩ : syracuseStep 666995 = 1000493) B1000493
theorem B667011 : Blo 666309 667011 := bstep (se 1 (by rfl) ⟨500258, by rfl⟩ : syracuseStep 667011 = 1000517) B1000517
theorem B667027 : Blo 666309 667027 := bstep (se 1 (by rfl) ⟨500270, by rfl⟩ : syracuseStep 667027 = 1000541) B1000541
theorem B667043 : Blo 666309 667043 := bstep (se 1 (by rfl) ⟨500282, by rfl⟩ : syracuseStep 667043 = 1000565) B1000565
theorem B667059 : Blo 666309 667059 := bstep (se 1 (by rfl) ⟨500294, by rfl⟩ : syracuseStep 667059 = 1000589) B1000589
theorem B667075 : Blo 666309 667075 := bstep (se 1 (by rfl) ⟨500306, by rfl⟩ : syracuseStep 667075 = 1000613) B1000613
theorem B667091 : Blo 666309 667091 := bstep (se 1 (by rfl) ⟨500318, by rfl⟩ : syracuseStep 667091 = 1000637) B1000637
theorem B667107 : Blo 666309 667107 := bstep (se 1 (by rfl) ⟨500330, by rfl⟩ : syracuseStep 667107 = 1000661) B1000661
theorem B1125859 : Blo 666309 1125859 := bstep (se 1 (by rfl) ⟨844394, by rfl⟩ : syracuseStep 1125859 = 1688789) B1688789
theorem B667123 : Blo 666309 667123 := bstep (se 1 (by rfl) ⟨500342, by rfl⟩ : syracuseStep 667123 = 1000685) B1000685
theorem B667139 : Blo 666309 667139 := bstep (se 1 (by rfl) ⟨500354, by rfl⟩ : syracuseStep 667139 = 1000709) B1000709
theorem B667155 : Blo 666309 667155 := bstep (se 1 (by rfl) ⟨500366, by rfl⟩ : syracuseStep 667155 = 1000733) B1000733
theorem B667171 : Blo 666309 667171 := bstep (se 1 (by rfl) ⟨500378, by rfl⟩ : syracuseStep 667171 = 1000757) B1000757
theorem B667187 : Blo 666309 667187 := bstep (se 1 (by rfl) ⟨500390, by rfl⟩ : syracuseStep 667187 = 1000781) B1000781
theorem B667203 : Blo 666309 667203 := bstep (se 1 (by rfl) ⟨500402, by rfl⟩ : syracuseStep 667203 = 1000805) B1000805
theorem B667219 : Blo 666309 667219 := bstep (se 1 (by rfl) ⟨500414, by rfl⟩ : syracuseStep 667219 = 1000829) B1000829
theorem B667235 : Blo 666309 667235 := bstep (se 1 (by rfl) ⟨500426, by rfl⟩ : syracuseStep 667235 = 1000853) B1000853
theorem B1126001 : Blo 666309 1126001 := bstep (se 2 (by rfl) ⟨422250, by rfl⟩ : syracuseStep 1126001 = 844501) B844501
theorem B667251 : Blo 666309 667251 := bstep (se 1 (by rfl) ⟨500438, by rfl⟩ : syracuseStep 667251 = 1000877) B1000877
theorem B667267 : Blo 666309 667267 := bstep (se 1 (by rfl) ⟨500450, by rfl⟩ : syracuseStep 667267 = 1000901) B1000901
theorem B667283 : Blo 666309 667283 := bstep (se 1 (by rfl) ⟨500462, by rfl⟩ : syracuseStep 667283 = 1000925) B1000925
theorem B1060499 : Blo 666309 1060499 := bstep (se 1 (by rfl) ⟨795374, by rfl⟩ : syracuseStep 1060499 = 1590749) B1590749
theorem B667299 : Blo 666309 667299 := bstep (se 1 (by rfl) ⟨500474, by rfl⟩ : syracuseStep 667299 = 1000949) B1000949
theorem B667315 : Blo 666309 667315 := bstep (se 1 (by rfl) ⟨500486, by rfl⟩ : syracuseStep 667315 = 1000973) B1000973
theorem B667331 : Blo 666309 667331 := bstep (se 1 (by rfl) ⟨500498, by rfl⟩ : syracuseStep 667331 = 1000997) B1000997
theorem B667347 : Blo 666309 667347 := bstep (se 1 (by rfl) ⟨500510, by rfl⟩ : syracuseStep 667347 = 1001021) B1001021
theorem B667363 : Blo 666309 667363 := bstep (se 1 (by rfl) ⟨500522, by rfl⟩ : syracuseStep 667363 = 1001045) B1001045
theorem B1126129 : Blo 666309 1126129 := bstep (se 2 (by rfl) ⟨422298, by rfl⟩ : syracuseStep 1126129 = 844597) B844597
theorem B667379 : Blo 666309 667379 := bstep (se 1 (by rfl) ⟨500534, by rfl⟩ : syracuseStep 667379 = 1001069) B1001069
theorem B667395 : Blo 666309 667395 := bstep (se 1 (by rfl) ⟨500546, by rfl⟩ : syracuseStep 667395 = 1001093) B1001093
theorem B1126163 : Blo 666309 1126163 := bstep (se 1 (by rfl) ⟨844622, by rfl⟩ : syracuseStep 1126163 = 1689245) B1689245
theorem B667411 : Blo 666309 667411 := bstep (se 1 (by rfl) ⟨500558, by rfl⟩ : syracuseStep 667411 = 1001117) B1001117
theorem B667427 : Blo 666309 667427 := bstep (se 1 (by rfl) ⟨500570, by rfl⟩ : syracuseStep 667427 = 1001141) B1001141
theorem B667443 : Blo 666309 667443 := bstep (se 1 (by rfl) ⟨500582, by rfl⟩ : syracuseStep 667443 = 1001165) B1001165
theorem B667459 : Blo 666309 667459 := bstep (se 1 (by rfl) ⟨500594, by rfl⟩ : syracuseStep 667459 = 1001189) B1001189
theorem B667475 : Blo 666309 667475 := bstep (se 1 (by rfl) ⟨500606, by rfl⟩ : syracuseStep 667475 = 1001213) B1001213
theorem B667491 : Blo 666309 667491 := bstep (se 1 (by rfl) ⟨500618, by rfl⟩ : syracuseStep 667491 = 1001237) B1001237
theorem B2142065 : Blo 666309 2142065 := bstep (se 2 (by rfl) ⟨803274, by rfl⟩ : syracuseStep 2142065 = 1606549) B1606549
theorem B667507 : Blo 666309 667507 := bstep (se 1 (by rfl) ⟨500630, by rfl⟩ : syracuseStep 667507 = 1001261) B1001261
theorem B667523 : Blo 666309 667523 := bstep (se 1 (by rfl) ⟨500642, by rfl⟩ : syracuseStep 667523 = 1001285) B1001285
theorem B2862989 : Blo 666309 2862989 := bstep (se 3 (by rfl) ⟨536810, by rfl⟩ : syracuseStep 2862989 = 1073621) B1073621
theorem B1126291 : Blo 666309 1126291 := bstep (se 1 (by rfl) ⟨844718, by rfl⟩ : syracuseStep 1126291 = 1689437) B1689437
theorem B667539 : Blo 666309 667539 := bstep (se 1 (by rfl) ⟨500654, by rfl⟩ : syracuseStep 667539 = 1001309) B1001309
theorem B667555 : Blo 666309 667555 := bstep (se 1 (by rfl) ⟨500666, by rfl⟩ : syracuseStep 667555 = 1001333) B1001333
theorem B667571 : Blo 666309 667571 := bstep (se 1 (by rfl) ⟨500678, by rfl⟩ : syracuseStep 667571 = 1001357) B1001357
theorem B667587 : Blo 666309 667587 := bstep (se 1 (by rfl) ⟨500690, by rfl⟩ : syracuseStep 667587 = 1001381) B1001381
theorem B667603 : Blo 666309 667603 := bstep (se 1 (by rfl) ⟨500702, by rfl⟩ : syracuseStep 667603 = 1001405) B1001405
theorem B667619 : Blo 666309 667619 := bstep (se 1 (by rfl) ⟨500714, by rfl⟩ : syracuseStep 667619 = 1001429) B1001429
theorem B667635 : Blo 666309 667635 := bstep (se 1 (by rfl) ⟨500726, by rfl⟩ : syracuseStep 667635 = 1001453) B1001453
theorem B667651 : Blo 666309 667651 := bstep (se 1 (by rfl) ⟨500738, by rfl⟩ : syracuseStep 667651 = 1001477) B1001477
theorem B667667 : Blo 666309 667667 := bstep (se 1 (by rfl) ⟨500750, by rfl⟩ : syracuseStep 667667 = 1001501) B1001501
theorem B1126433 : Blo 666309 1126433 := bstep (se 2 (by rfl) ⟨422412, by rfl⟩ : syracuseStep 1126433 = 844825) B844825
theorem B667683 : Blo 666309 667683 := bstep (se 1 (by rfl) ⟨500762, by rfl⟩ : syracuseStep 667683 = 1001525) B1001525
theorem B667699 : Blo 666309 667699 := bstep (se 1 (by rfl) ⟨500774, by rfl⟩ : syracuseStep 667699 = 1001549) B1001549
theorem B667715 : Blo 666309 667715 := bstep (se 1 (by rfl) ⟨500786, by rfl⟩ : syracuseStep 667715 = 1001573) B1001573
theorem B667731 : Blo 666309 667731 := bstep (se 1 (by rfl) ⟨500798, by rfl⟩ : syracuseStep 667731 = 1001597) B1001597
theorem B667747 : Blo 666309 667747 := bstep (se 1 (by rfl) ⟨500810, by rfl⟩ : syracuseStep 667747 = 1001621) B1001621
theorem B667763 : Blo 666309 667763 := bstep (se 1 (by rfl) ⟨500822, by rfl⟩ : syracuseStep 667763 = 1001645) B1001645
theorem B667779 : Blo 666309 667779 := bstep (se 1 (by rfl) ⟨500834, by rfl⟩ : syracuseStep 667779 = 1001669) B1001669
theorem B667795 : Blo 666309 667795 := bstep (se 1 (by rfl) ⟨500846, by rfl⟩ : syracuseStep 667795 = 1001693) B1001693
theorem B1126561 : Blo 666309 1126561 := bstep (se 2 (by rfl) ⟨422460, by rfl⟩ : syracuseStep 1126561 = 844921) B844921
theorem B667811 : Blo 666309 667811 := bstep (se 1 (by rfl) ⟨500858, by rfl⟩ : syracuseStep 667811 = 1001717) B1001717
theorem B667827 : Blo 666309 667827 := bstep (se 1 (by rfl) ⟨500870, by rfl⟩ : syracuseStep 667827 = 1001741) B1001741
theorem B1126595 : Blo 666309 1126595 := bstep (se 1 (by rfl) ⟨844946, by rfl⟩ : syracuseStep 1126595 = 1689893) B1689893
theorem B667843 : Blo 666309 667843 := bstep (se 1 (by rfl) ⟨500882, by rfl⟩ : syracuseStep 667843 = 1001765) B1001765
theorem B3813581 : Blo 666309 3813581 := bstep (se 3 (by rfl) ⟨715046, by rfl⟩ : syracuseStep 3813581 = 1430093) B1430093
theorem B667859 : Blo 666309 667859 := bstep (se 1 (by rfl) ⟨500894, by rfl⟩ : syracuseStep 667859 = 1001789) B1001789
theorem B667875 : Blo 666309 667875 := bstep (se 1 (by rfl) ⟨500906, by rfl⟩ : syracuseStep 667875 = 1001813) B1001813
theorem B667891 : Blo 666309 667891 := bstep (se 1 (by rfl) ⟨500918, by rfl⟩ : syracuseStep 667891 = 1001837) B1001837
theorem B667907 : Blo 666309 667907 := bstep (se 1 (by rfl) ⟨500930, by rfl⟩ : syracuseStep 667907 = 1001861) B1001861
theorem B667923 : Blo 666309 667923 := bstep (se 1 (by rfl) ⟨500942, by rfl⟩ : syracuseStep 667923 = 1001885) B1001885
theorem B667939 : Blo 666309 667939 := bstep (se 1 (by rfl) ⟨500954, by rfl⟩ : syracuseStep 667939 = 1001909) B1001909
theorem B1716515 : Blo 666309 1716515 := bstep (se 1 (by rfl) ⟨1287386, by rfl⟩ : syracuseStep 1716515 = 2574773) B2574773
theorem B667955 : Blo 666309 667955 := bstep (se 1 (by rfl) ⟨500966, by rfl⟩ : syracuseStep 667955 = 1001933) B1001933
theorem B1126723 : Blo 666309 1126723 := bstep (se 1 (by rfl) ⟨845042, by rfl⟩ : syracuseStep 1126723 = 1690085) B1690085
theorem B667971 : Blo 666309 667971 := bstep (se 1 (by rfl) ⟨500978, by rfl⟩ : syracuseStep 667971 = 1001957) B1001957
theorem B667987 : Blo 666309 667987 := bstep (se 1 (by rfl) ⟨500990, by rfl⟩ : syracuseStep 667987 = 1001981) B1001981
theorem B668003 : Blo 666309 668003 := bstep (se 1 (by rfl) ⟨501002, by rfl⟩ : syracuseStep 668003 = 1002005) B1002005
theorem B668019 : Blo 666309 668019 := bstep (se 1 (by rfl) ⟨501014, by rfl⟩ : syracuseStep 668019 = 1002029) B1002029
theorem B668035 : Blo 666309 668035 := bstep (se 1 (by rfl) ⟨501026, by rfl⟩ : syracuseStep 668035 = 1002053) B1002053
theorem B668051 : Blo 666309 668051 := bstep (se 1 (by rfl) ⟨501038, by rfl⟩ : syracuseStep 668051 = 1002077) B1002077
theorem B668067 : Blo 666309 668067 := bstep (se 1 (by rfl) ⟨501050, by rfl⟩ : syracuseStep 668067 = 1002101) B1002101
theorem B2535857 : Blo 666309 2535857 := bstep (se 2 (by rfl) ⟨950946, by rfl⟩ : syracuseStep 2535857 = 1901893) B1901893
theorem B668083 : Blo 666309 668083 := bstep (se 1 (by rfl) ⟨501062, by rfl⟩ : syracuseStep 668083 = 1002125) B1002125
theorem B668099 : Blo 666309 668099 := bstep (se 1 (by rfl) ⟨501074, by rfl⟩ : syracuseStep 668099 = 1002149) B1002149
theorem B1126865 : Blo 666309 1126865 := bstep (se 2 (by rfl) ⟨422574, by rfl⟩ : syracuseStep 1126865 = 845149) B845149
theorem B668115 : Blo 666309 668115 := bstep (se 1 (by rfl) ⟨501086, by rfl⟩ : syracuseStep 668115 = 1002173) B1002173
theorem B668131 : Blo 666309 668131 := bstep (se 1 (by rfl) ⟨501098, by rfl⟩ : syracuseStep 668131 = 1002197) B1002197
theorem B668147 : Blo 666309 668147 := bstep (se 1 (by rfl) ⟨501110, by rfl⟩ : syracuseStep 668147 = 1002221) B1002221
theorem B668163 : Blo 666309 668163 := bstep (se 1 (by rfl) ⟨501122, by rfl⟩ : syracuseStep 668163 = 1002245) B1002245
theorem B668179 : Blo 666309 668179 := bstep (se 1 (by rfl) ⟨501134, by rfl⟩ : syracuseStep 668179 = 1002269) B1002269
theorem B668195 : Blo 666309 668195 := bstep (se 1 (by rfl) ⟨501146, by rfl⟩ : syracuseStep 668195 = 1002293) B1002293
theorem B668211 : Blo 666309 668211 := bstep (se 1 (by rfl) ⟨501158, by rfl⟩ : syracuseStep 668211 = 1002317) B1002317
theorem B668227 : Blo 666309 668227 := bstep (se 1 (by rfl) ⟨501170, by rfl⟩ : syracuseStep 668227 = 1002341) B1002341
theorem B1126993 : Blo 666309 1126993 := bstep (se 2 (by rfl) ⟨422622, by rfl⟩ : syracuseStep 1126993 = 845245) B845245
theorem B668243 : Blo 666309 668243 := bstep (se 1 (by rfl) ⟨501182, by rfl⟩ : syracuseStep 668243 = 1002365) B1002365
theorem B668259 : Blo 666309 668259 := bstep (se 1 (by rfl) ⟨501194, by rfl⟩ : syracuseStep 668259 = 1002389) B1002389
theorem B1127027 : Blo 666309 1127027 := bstep (se 1 (by rfl) ⟨845270, by rfl⟩ : syracuseStep 1127027 = 1690541) B1690541
theorem B668275 : Blo 666309 668275 := bstep (se 1 (by rfl) ⟨501206, by rfl⟩ : syracuseStep 668275 = 1002413) B1002413
theorem B668291 : Blo 666309 668291 := bstep (se 1 (by rfl) ⟨501218, by rfl⟩ : syracuseStep 668291 = 1002437) B1002437
theorem B668307 : Blo 666309 668307 := bstep (se 1 (by rfl) ⟨501230, by rfl⟩ : syracuseStep 668307 = 1002461) B1002461
theorem B668323 : Blo 666309 668323 := bstep (se 1 (by rfl) ⟨501242, by rfl⟩ : syracuseStep 668323 = 1002485) B1002485
theorem B3388067 : Blo 666309 3388067 := bstep (se 1 (by rfl) ⟨2541050, by rfl⟩ : syracuseStep 3388067 = 5082101) B5082101
theorem B668339 : Blo 666309 668339 := bstep (se 1 (by rfl) ⟨501254, by rfl⟩ : syracuseStep 668339 = 1002509) B1002509
theorem B668355 : Blo 666309 668355 := bstep (se 1 (by rfl) ⟨501266, by rfl⟩ : syracuseStep 668355 = 1002533) B1002533
theorem B668371 : Blo 666309 668371 := bstep (se 1 (by rfl) ⟨501278, by rfl⟩ : syracuseStep 668371 = 1002557) B1002557
theorem B668387 : Blo 666309 668387 := bstep (se 1 (by rfl) ⟨501290, by rfl⟩ : syracuseStep 668387 = 1002581) B1002581
theorem B1127155 : Blo 666309 1127155 := bstep (se 1 (by rfl) ⟨845366, by rfl⟩ : syracuseStep 1127155 = 1690733) B1690733
theorem B668403 : Blo 666309 668403 := bstep (se 1 (by rfl) ⟨501302, by rfl⟩ : syracuseStep 668403 = 1002605) B1002605
theorem B668419 : Blo 666309 668419 := bstep (se 1 (by rfl) ⟨501314, by rfl⟩ : syracuseStep 668419 = 1002629) B1002629
theorem B2175761 : Blo 666309 2175761 := bstep (se 2 (by rfl) ⟨815910, by rfl⟩ : syracuseStep 2175761 = 1631821) B1631821
theorem B668435 : Blo 666309 668435 := bstep (se 1 (by rfl) ⟨501326, by rfl⟩ : syracuseStep 668435 = 1002653) B1002653
theorem B668451 : Blo 666309 668451 := bstep (se 1 (by rfl) ⟨501338, by rfl⟩ : syracuseStep 668451 = 1002677) B1002677
theorem B668467 : Blo 666309 668467 := bstep (se 1 (by rfl) ⟨501350, by rfl⟩ : syracuseStep 668467 = 1002701) B1002701
theorem B668483 : Blo 666309 668483 := bstep (se 1 (by rfl) ⟨501362, by rfl⟩ : syracuseStep 668483 = 1002725) B1002725
theorem B668499 : Blo 666309 668499 := bstep (se 1 (by rfl) ⟨501374, by rfl⟩ : syracuseStep 668499 = 1002749) B1002749
theorem B668515 : Blo 666309 668515 := bstep (se 1 (by rfl) ⟨501386, by rfl⟩ : syracuseStep 668515 = 1002773) B1002773
theorem B668531 : Blo 666309 668531 := bstep (se 1 (by rfl) ⟨501398, by rfl⟩ : syracuseStep 668531 = 1002797) B1002797
theorem B1127297 : Blo 666309 1127297 := bstep (se 2 (by rfl) ⟨422736, by rfl⟩ : syracuseStep 1127297 = 845473) B845473
theorem B668547 : Blo 666309 668547 := bstep (se 1 (by rfl) ⟨501410, by rfl⟩ : syracuseStep 668547 = 1002821) B1002821
theorem B668563 : Blo 666309 668563 := bstep (se 1 (by rfl) ⟨501422, by rfl⟩ : syracuseStep 668563 = 1002845) B1002845
theorem B668579 : Blo 666309 668579 := bstep (se 1 (by rfl) ⟨501434, by rfl⟩ : syracuseStep 668579 = 1002869) B1002869
theorem B668595 : Blo 666309 668595 := bstep (se 1 (by rfl) ⟨501446, by rfl⟩ : syracuseStep 668595 = 1002893) B1002893
theorem B7943093 : Blo 666309 7943093 := bstep (se 5 (by rfl) ⟨372332, by rfl⟩ : syracuseStep 7943093 = 744665) B744665
theorem B668611 : Blo 666309 668611 := bstep (se 1 (by rfl) ⟨501458, by rfl⟩ : syracuseStep 668611 = 1002917) B1002917
theorem B668627 : Blo 666309 668627 := bstep (se 1 (by rfl) ⟨501470, by rfl⟩ : syracuseStep 668627 = 1002941) B1002941
theorem B668643 : Blo 666309 668643 := bstep (se 1 (by rfl) ⟨501482, by rfl⟩ : syracuseStep 668643 = 1002965) B1002965
theorem B668659 : Blo 666309 668659 := bstep (se 1 (by rfl) ⟨501494, by rfl⟩ : syracuseStep 668659 = 1002989) B1002989
theorem B1127425 : Blo 666309 1127425 := bstep (se 2 (by rfl) ⟨422784, by rfl⟩ : syracuseStep 1127425 = 845569) B845569
theorem B668675 : Blo 666309 668675 := bstep (se 1 (by rfl) ⟨501506, by rfl⟩ : syracuseStep 668675 = 1003013) B1003013
theorem B668691 : Blo 666309 668691 := bstep (se 1 (by rfl) ⟨501518, by rfl⟩ : syracuseStep 668691 = 1003037) B1003037
theorem B1127459 : Blo 666309 1127459 := bstep (se 1 (by rfl) ⟨845594, by rfl⟩ : syracuseStep 1127459 = 1691189) B1691189
theorem B668707 : Blo 666309 668707 := bstep (se 1 (by rfl) ⟨501530, by rfl⟩ : syracuseStep 668707 = 1003061) B1003061
theorem B668723 : Blo 666309 668723 := bstep (se 1 (by rfl) ⟨501542, by rfl⟩ : syracuseStep 668723 = 1003085) B1003085
theorem B668739 : Blo 666309 668739 := bstep (se 1 (by rfl) ⟨501554, by rfl⟩ : syracuseStep 668739 = 1003109) B1003109
theorem B668755 : Blo 666309 668755 := bstep (se 1 (by rfl) ⟨501566, by rfl⟩ : syracuseStep 668755 = 1003133) B1003133
theorem B668771 : Blo 666309 668771 := bstep (se 1 (by rfl) ⟨501578, by rfl⟩ : syracuseStep 668771 = 1003157) B1003157
theorem B1029233 : Blo 666309 1029233 := bstep (se 2 (by rfl) ⟨385962, by rfl⟩ : syracuseStep 1029233 = 771925) B771925
theorem B668787 : Blo 666309 668787 := bstep (se 1 (by rfl) ⟨501590, by rfl⟩ : syracuseStep 668787 = 1003181) B1003181
theorem B668803 : Blo 666309 668803 := bstep (se 1 (by rfl) ⟨501602, by rfl⟩ : syracuseStep 668803 = 1003205) B1003205
theorem B1717393 : Blo 666309 1717393 := bstep (se 2 (by rfl) ⟨644022, by rfl⟩ : syracuseStep 1717393 = 1288045) B1288045
theorem B668819 : Blo 666309 668819 := bstep (se 1 (by rfl) ⟨501614, by rfl⟩ : syracuseStep 668819 = 1003229) B1003229
theorem B1127587 : Blo 666309 1127587 := bstep (se 1 (by rfl) ⟨845690, by rfl⟩ : syracuseStep 1127587 = 1691381) B1691381
theorem B668835 : Blo 666309 668835 := bstep (se 1 (by rfl) ⟨501626, by rfl⟩ : syracuseStep 668835 = 1003253) B1003253
theorem B668851 : Blo 666309 668851 := bstep (se 1 (by rfl) ⟨501638, by rfl⟩ : syracuseStep 668851 = 1003277) B1003277
theorem B668867 : Blo 666309 668867 := bstep (se 1 (by rfl) ⟨501650, by rfl⟩ : syracuseStep 668867 = 1003301) B1003301
theorem B668883 : Blo 666309 668883 := bstep (se 1 (by rfl) ⟨501662, by rfl⟩ : syracuseStep 668883 = 1003325) B1003325
theorem B668899 : Blo 666309 668899 := bstep (se 1 (by rfl) ⟨501674, by rfl⟩ : syracuseStep 668899 = 1003349) B1003349
theorem B668915 : Blo 666309 668915 := bstep (se 1 (by rfl) ⟨501686, by rfl⟩ : syracuseStep 668915 = 1003373) B1003373
theorem B668931 : Blo 666309 668931 := bstep (se 1 (by rfl) ⟨501698, by rfl⟩ : syracuseStep 668931 = 1003397) B1003397
theorem B668947 : Blo 666309 668947 := bstep (se 1 (by rfl) ⟨501710, by rfl⟩ : syracuseStep 668947 = 1003421) B1003421
theorem B668963 : Blo 666309 668963 := bstep (se 1 (by rfl) ⟨501722, by rfl⟩ : syracuseStep 668963 = 1003445) B1003445
theorem B1520945 : Blo 666309 1520945 := bstep (se 2 (by rfl) ⟨570354, by rfl⟩ : syracuseStep 1520945 = 1140709) B1140709
theorem B1127729 : Blo 666309 1127729 := bstep (se 2 (by rfl) ⟨422898, by rfl⟩ : syracuseStep 1127729 = 845797) B845797
theorem B668979 : Blo 666309 668979 := bstep (se 1 (by rfl) ⟨501734, by rfl⟩ : syracuseStep 668979 = 1003469) B1003469
theorem B668995 : Blo 666309 668995 := bstep (se 1 (by rfl) ⟨501746, by rfl⟩ : syracuseStep 668995 = 1003493) B1003493
theorem B669011 : Blo 666309 669011 := bstep (se 1 (by rfl) ⟨501758, by rfl⟩ : syracuseStep 669011 = 1003517) B1003517
theorem B669027 : Blo 666309 669027 := bstep (se 1 (by rfl) ⟨501770, by rfl⟩ : syracuseStep 669027 = 1003541) B1003541
theorem B669043 : Blo 666309 669043 := bstep (se 1 (by rfl) ⟨501782, by rfl⟩ : syracuseStep 669043 = 1003565) B1003565
theorem B669059 : Blo 666309 669059 := bstep (se 1 (by rfl) ⟨501794, by rfl⟩ : syracuseStep 669059 = 1003589) B1003589
theorem B669075 : Blo 666309 669075 := bstep (se 1 (by rfl) ⟨501806, by rfl⟩ : syracuseStep 669075 = 1003613) B1003613
theorem B669091 : Blo 666309 669091 := bstep (se 1 (by rfl) ⟨501818, by rfl⟩ : syracuseStep 669091 = 1003637) B1003637
theorem B1127857 : Blo 666309 1127857 := bstep (se 2 (by rfl) ⟨422946, by rfl⟩ : syracuseStep 1127857 = 845893) B845893
theorem B669107 : Blo 666309 669107 := bstep (se 1 (by rfl) ⟨501830, by rfl⟩ : syracuseStep 669107 = 1003661) B1003661
theorem B669123 : Blo 666309 669123 := bstep (se 1 (by rfl) ⟨501842, by rfl⟩ : syracuseStep 669123 = 1003685) B1003685
theorem B3388877 : Blo 666309 3388877 := bstep (se 3 (by rfl) ⟨635414, by rfl⟩ : syracuseStep 3388877 = 1270829) B1270829
theorem B1127891 : Blo 666309 1127891 := bstep (se 1 (by rfl) ⟨845918, by rfl⟩ : syracuseStep 1127891 = 1691837) B1691837
theorem B669139 : Blo 666309 669139 := bstep (se 1 (by rfl) ⟨501854, by rfl⟩ : syracuseStep 669139 = 1003709) B1003709
theorem B669155 : Blo 666309 669155 := bstep (se 1 (by rfl) ⟨501866, by rfl⟩ : syracuseStep 669155 = 1003733) B1003733
theorem B669171 : Blo 666309 669171 := bstep (se 1 (by rfl) ⟨501878, by rfl⟩ : syracuseStep 669171 = 1003757) B1003757
theorem B669187 : Blo 666309 669187 := bstep (se 1 (by rfl) ⟨501890, by rfl⟩ : syracuseStep 669187 = 1003781) B1003781
theorem B669203 : Blo 666309 669203 := bstep (se 1 (by rfl) ⟨501902, by rfl⟩ : syracuseStep 669203 = 1003805) B1003805
theorem B669219 : Blo 666309 669219 := bstep (se 1 (by rfl) ⟨501914, by rfl⟩ : syracuseStep 669219 = 1003829) B1003829
theorem B669235 : Blo 666309 669235 := bstep (se 1 (by rfl) ⟨501926, by rfl⟩ : syracuseStep 669235 = 1003853) B1003853
theorem B669251 : Blo 666309 669251 := bstep (se 1 (by rfl) ⟨501938, by rfl⟩ : syracuseStep 669251 = 1003877) B1003877
theorem B1128019 : Blo 666309 1128019 := bstep (se 1 (by rfl) ⟨846014, by rfl⟩ : syracuseStep 1128019 = 1692029) B1692029
theorem B669267 : Blo 666309 669267 := bstep (se 1 (by rfl) ⟨501950, by rfl⟩ : syracuseStep 669267 = 1003901) B1003901
theorem B669283 : Blo 666309 669283 := bstep (se 1 (by rfl) ⟨501962, by rfl⟩ : syracuseStep 669283 = 1003925) B1003925
theorem B4830833 : Blo 666309 4830833 := bstep (se 2 (by rfl) ⟨1811562, by rfl⟩ : syracuseStep 4830833 = 3623125) B3623125
theorem B669299 : Blo 666309 669299 := bstep (se 1 (by rfl) ⟨501974, by rfl⟩ : syracuseStep 669299 = 1003949) B1003949
theorem B669315 : Blo 666309 669315 := bstep (se 1 (by rfl) ⟨501986, by rfl⟩ : syracuseStep 669315 = 1003973) B1003973
theorem B669331 : Blo 666309 669331 := bstep (se 1 (by rfl) ⟨501998, by rfl⟩ : syracuseStep 669331 = 1003997) B1003997
theorem B669347 : Blo 666309 669347 := bstep (se 1 (by rfl) ⟨502010, by rfl⟩ : syracuseStep 669347 = 1004021) B1004021
theorem B1357489 : Blo 666309 1357489 := bstep (se 2 (by rfl) ⟨509058, by rfl⟩ : syracuseStep 1357489 = 1018117) B1018117
theorem B669363 : Blo 666309 669363 := bstep (se 1 (by rfl) ⟨502022, by rfl⟩ : syracuseStep 669363 = 1004045) B1004045
theorem B669379 : Blo 666309 669379 := bstep (se 1 (by rfl) ⟨502034, by rfl⟩ : syracuseStep 669379 = 1004069) B1004069
theorem B669395 : Blo 666309 669395 := bstep (se 1 (by rfl) ⟨502046, by rfl⟩ : syracuseStep 669395 = 1004093) B1004093
theorem B1128161 : Blo 666309 1128161 := bstep (se 2 (by rfl) ⟨423060, by rfl⟩ : syracuseStep 1128161 = 846121) B846121
theorem B669411 : Blo 666309 669411 := bstep (se 1 (by rfl) ⟨502058, by rfl⟩ : syracuseStep 669411 = 1004117) B1004117
theorem B669427 : Blo 666309 669427 := bstep (se 1 (by rfl) ⟨502070, by rfl⟩ : syracuseStep 669427 = 1004141) B1004141
theorem B669443 : Blo 666309 669443 := bstep (se 1 (by rfl) ⟨502082, by rfl⟩ : syracuseStep 669443 = 1004165) B1004165
theorem B669459 : Blo 666309 669459 := bstep (se 1 (by rfl) ⟨502094, by rfl⟩ : syracuseStep 669459 = 1004189) B1004189
theorem B669475 : Blo 666309 669475 := bstep (se 1 (by rfl) ⟨502106, by rfl⟩ : syracuseStep 669475 = 1004213) B1004213
theorem B669491 : Blo 666309 669491 := bstep (se 1 (by rfl) ⟨502118, by rfl⟩ : syracuseStep 669491 = 1004237) B1004237
theorem B669507 : Blo 666309 669507 := bstep (se 1 (by rfl) ⟨502130, by rfl⟩ : syracuseStep 669507 = 1004261) B1004261
theorem B669523 : Blo 666309 669523 := bstep (se 1 (by rfl) ⟨502142, by rfl⟩ : syracuseStep 669523 = 1004285) B1004285
theorem B1128289 : Blo 666309 1128289 := bstep (se 2 (by rfl) ⟨423108, by rfl⟩ : syracuseStep 1128289 = 846217) B846217
theorem B2537315 : Blo 666309 2537315 := bstep (se 1 (by rfl) ⟨1902986, by rfl⟩ : syracuseStep 2537315 = 3805973) B3805973
theorem B669539 : Blo 666309 669539 := bstep (se 1 (by rfl) ⟨502154, by rfl⟩ : syracuseStep 669539 = 1004309) B1004309
theorem B669555 : Blo 666309 669555 := bstep (se 1 (by rfl) ⟨502166, by rfl⟩ : syracuseStep 669555 = 1004333) B1004333
theorem B1128323 : Blo 666309 1128323 := bstep (se 1 (by rfl) ⟨846242, by rfl⟩ : syracuseStep 1128323 = 1692485) B1692485
theorem B669571 : Blo 666309 669571 := bstep (se 1 (by rfl) ⟨502178, by rfl⟩ : syracuseStep 669571 = 1004357) B1004357
theorem B2144141 : Blo 666309 2144141 := bstep (se 3 (by rfl) ⟨402026, by rfl⟩ : syracuseStep 2144141 = 804053) B804053
theorem B669587 : Blo 666309 669587 := bstep (se 1 (by rfl) ⟨502190, by rfl⟩ : syracuseStep 669587 = 1004381) B1004381
theorem B669603 : Blo 666309 669603 := bstep (se 1 (by rfl) ⟨502202, by rfl⟩ : syracuseStep 669603 = 1004405) B1004405
theorem B669619 : Blo 666309 669619 := bstep (se 1 (by rfl) ⟨502214, by rfl⟩ : syracuseStep 669619 = 1004429) B1004429
theorem B669635 : Blo 666309 669635 := bstep (se 1 (by rfl) ⟨502226, by rfl⟩ : syracuseStep 669635 = 1004453) B1004453
theorem B669651 : Blo 666309 669651 := bstep (se 1 (by rfl) ⟨502238, by rfl⟩ : syracuseStep 669651 = 1004477) B1004477
theorem B669667 : Blo 666309 669667 := bstep (se 1 (by rfl) ⟨502250, by rfl⟩ : syracuseStep 669667 = 1004501) B1004501
theorem B1423345 : Blo 666309 1423345 := bstep (se 2 (by rfl) ⟨533754, by rfl⟩ : syracuseStep 1423345 = 1067509) B1067509
theorem B669683 : Blo 666309 669683 := bstep (se 1 (by rfl) ⟨502262, by rfl⟩ : syracuseStep 669683 = 1004525) B1004525
theorem B1128451 : Blo 666309 1128451 := bstep (se 1 (by rfl) ⟨846338, by rfl⟩ : syracuseStep 1128451 = 1692677) B1692677
theorem B669699 : Blo 666309 669699 := bstep (se 1 (by rfl) ⟨502274, by rfl⟩ : syracuseStep 669699 = 1004549) B1004549
theorem B669715 : Blo 666309 669715 := bstep (se 1 (by rfl) ⟨502286, by rfl⟩ : syracuseStep 669715 = 1004573) B1004573
theorem B669731 : Blo 666309 669731 := bstep (se 1 (by rfl) ⟨502298, by rfl⟩ : syracuseStep 669731 = 1004597) B1004597
theorem B669747 : Blo 666309 669747 := bstep (se 1 (by rfl) ⟨502310, by rfl⟩ : syracuseStep 669747 = 1004621) B1004621
theorem B669763 : Blo 666309 669763 := bstep (se 1 (by rfl) ⟨502322, by rfl⟩ : syracuseStep 669763 = 1004645) B1004645
theorem B669779 : Blo 666309 669779 := bstep (se 1 (by rfl) ⟨502334, by rfl⟩ : syracuseStep 669779 = 1004669) B1004669
theorem B669795 : Blo 666309 669795 := bstep (se 1 (by rfl) ⟨502346, by rfl⟩ : syracuseStep 669795 = 1004693) B1004693
theorem B669811 : Blo 666309 669811 := bstep (se 1 (by rfl) ⟨502358, by rfl⟩ : syracuseStep 669811 = 1004717) B1004717
theorem B669827 : Blo 666309 669827 := bstep (se 1 (by rfl) ⟨502370, by rfl⟩ : syracuseStep 669827 = 1004741) B1004741
theorem B1128593 : Blo 666309 1128593 := bstep (se 2 (by rfl) ⟨423222, by rfl⟩ : syracuseStep 1128593 = 846445) B846445
theorem B669843 : Blo 666309 669843 := bstep (se 1 (by rfl) ⟨502382, by rfl⟩ : syracuseStep 669843 = 1004765) B1004765
theorem B669859 : Blo 666309 669859 := bstep (se 1 (by rfl) ⟨502394, by rfl⟩ : syracuseStep 669859 = 1004789) B1004789
theorem B669875 : Blo 666309 669875 := bstep (se 1 (by rfl) ⟨502406, by rfl⟩ : syracuseStep 669875 = 1004813) B1004813
theorem B964801 : Blo 666309 964801 := bstep (se 2 (by rfl) ⟨361800, by rfl⟩ : syracuseStep 964801 = 723601) B723601
theorem B669891 : Blo 666309 669891 := bstep (se 1 (by rfl) ⟨502418, by rfl⟩ : syracuseStep 669891 = 1004837) B1004837
theorem B669907 : Blo 666309 669907 := bstep (se 1 (by rfl) ⟨502430, by rfl⟩ : syracuseStep 669907 = 1004861) B1004861
theorem B669923 : Blo 666309 669923 := bstep (se 1 (by rfl) ⟨502442, by rfl⟩ : syracuseStep 669923 = 1004885) B1004885
theorem B669939 : Blo 666309 669939 := bstep (se 1 (by rfl) ⟨502454, by rfl⟩ : syracuseStep 669939 = 1004909) B1004909
theorem B669955 : Blo 666309 669955 := bstep (se 1 (by rfl) ⟨502466, by rfl⟩ : syracuseStep 669955 = 1004933) B1004933
theorem B1128721 : Blo 666309 1128721 := bstep (se 2 (by rfl) ⟨423270, by rfl⟩ : syracuseStep 1128721 = 846541) B846541
theorem B669971 : Blo 666309 669971 := bstep (se 1 (by rfl) ⟨502478, by rfl⟩ : syracuseStep 669971 = 1004957) B1004957
theorem B669987 : Blo 666309 669987 := bstep (se 1 (by rfl) ⟨502490, by rfl⟩ : syracuseStep 669987 = 1004981) B1004981
theorem B1128755 : Blo 666309 1128755 := bstep (se 1 (by rfl) ⟨846566, by rfl⟩ : syracuseStep 1128755 = 1693133) B1693133
theorem B670003 : Blo 666309 670003 := bstep (se 1 (by rfl) ⟨502502, by rfl⟩ : syracuseStep 670003 = 1005005) B1005005
theorem B670019 : Blo 666309 670019 := bstep (se 1 (by rfl) ⟨502514, by rfl⟩ : syracuseStep 670019 = 1005029) B1005029
theorem B670035 : Blo 666309 670035 := bstep (se 1 (by rfl) ⟨502526, by rfl⟩ : syracuseStep 670035 = 1005053) B1005053
theorem B670051 : Blo 666309 670051 := bstep (se 1 (by rfl) ⟨502538, by rfl⟩ : syracuseStep 670051 = 1005077) B1005077
theorem B670067 : Blo 666309 670067 := bstep (se 1 (by rfl) ⟨502550, by rfl⟩ : syracuseStep 670067 = 1005101) B1005101
theorem B670083 : Blo 666309 670083 := bstep (se 1 (by rfl) ⟨502562, by rfl⟩ : syracuseStep 670083 = 1005125) B1005125
theorem B670099 : Blo 666309 670099 := bstep (se 1 (by rfl) ⟨502574, by rfl⟩ : syracuseStep 670099 = 1005149) B1005149
theorem B670115 : Blo 666309 670115 := bstep (se 1 (by rfl) ⟨502586, by rfl⟩ : syracuseStep 670115 = 1005173) B1005173
theorem B1128883 : Blo 666309 1128883 := bstep (se 1 (by rfl) ⟨846662, by rfl⟩ : syracuseStep 1128883 = 1693325) B1693325
theorem B670131 : Blo 666309 670131 := bstep (se 1 (by rfl) ⟨502598, by rfl⟩ : syracuseStep 670131 = 1005197) B1005197
theorem B670147 : Blo 666309 670147 := bstep (se 1 (by rfl) ⟨502610, by rfl⟩ : syracuseStep 670147 = 1005221) B1005221
theorem B670163 : Blo 666309 670163 := bstep (se 1 (by rfl) ⟨502622, by rfl⟩ : syracuseStep 670163 = 1005245) B1005245
theorem B670179 : Blo 666309 670179 := bstep (se 1 (by rfl) ⟨502634, by rfl⟩ : syracuseStep 670179 = 1005269) B1005269
theorem B670195 : Blo 666309 670195 := bstep (se 1 (by rfl) ⟨502646, by rfl⟩ : syracuseStep 670195 = 1005293) B1005293
theorem B670211 : Blo 666309 670211 := bstep (se 1 (by rfl) ⟨502658, by rfl⟩ : syracuseStep 670211 = 1005317) B1005317
theorem B670227 : Blo 666309 670227 := bstep (se 1 (by rfl) ⟨502670, by rfl⟩ : syracuseStep 670227 = 1005341) B1005341
theorem B670243 : Blo 666309 670243 := bstep (se 1 (by rfl) ⟨502682, by rfl⟩ : syracuseStep 670243 = 1005365) B1005365
theorem B670259 : Blo 666309 670259 := bstep (se 1 (by rfl) ⟨502694, by rfl⟩ : syracuseStep 670259 = 1005389) B1005389
theorem B1129025 : Blo 666309 1129025 := bstep (se 2 (by rfl) ⟨423384, by rfl⟩ : syracuseStep 1129025 = 846769) B846769
theorem B670275 : Blo 666309 670275 := bstep (se 1 (by rfl) ⟨502706, by rfl⟩ : syracuseStep 670275 = 1005413) B1005413
theorem B670291 : Blo 666309 670291 := bstep (se 1 (by rfl) ⟨502718, by rfl⟩ : syracuseStep 670291 = 1005437) B1005437
theorem B670307 : Blo 666309 670307 := bstep (se 1 (by rfl) ⟨502730, by rfl⟩ : syracuseStep 670307 = 1005461) B1005461
theorem B4274801 : Blo 666309 4274801 := bstep (se 2 (by rfl) ⟨1603050, by rfl⟩ : syracuseStep 4274801 = 3206101) B3206101
theorem B1129153 : Blo 666309 1129153 := bstep (se 2 (by rfl) ⟨423432, by rfl⟩ : syracuseStep 1129153 = 846865) B846865
theorem B1129187 : Blo 666309 1129187 := bstep (se 1 (by rfl) ⟨846890, by rfl⟩ : syracuseStep 1129187 = 1693781) B1693781
theorem B2145037 : Blo 666309 2145037 := bstep (se 3 (by rfl) ⟨402194, by rfl⟩ : syracuseStep 2145037 = 804389) B804389
theorem B2538317 : Blo 666309 2538317 := bstep (se 3 (by rfl) ⟨475934, by rfl⟩ : syracuseStep 2538317 = 951869) B951869
theorem B1129315 : Blo 666309 1129315 := bstep (se 1 (by rfl) ⟨846986, by rfl⟩ : syracuseStep 1129315 = 1693973) B1693973
theorem B1129457 : Blo 666309 1129457 := bstep (se 2 (by rfl) ⟨423546, by rfl⟩ : syracuseStep 1129457 = 847093) B847093
theorem B1424387 : Blo 666309 1424387 := bstep (se 1 (by rfl) ⟨1068290, by rfl⟩ : syracuseStep 1424387 = 2136581) B2136581
theorem B3816497 : Blo 666309 3816497 := bstep (se 2 (by rfl) ⟨1431186, by rfl⟩ : syracuseStep 3816497 = 2862373) B2862373
theorem B1129585 : Blo 666309 1129585 := bstep (se 2 (by rfl) ⟨423594, by rfl⟩ : syracuseStep 1129585 = 847189) B847189
theorem B1129619 : Blo 666309 1129619 := bstep (se 1 (by rfl) ⟨847214, by rfl⟩ : syracuseStep 1129619 = 1694429) B1694429
theorem B1129747 : Blo 666309 1129747 := bstep (se 1 (by rfl) ⟨847310, by rfl⟩ : syracuseStep 1129747 = 1694621) B1694621
theorem B1686865 : Blo 666309 1686865 := bstep (se 2 (by rfl) ⟨632574, by rfl⟩ : syracuseStep 1686865 = 1265149) B1265149
theorem B1129889 : Blo 666309 1129889 := bstep (se 2 (by rfl) ⟨423708, by rfl⟩ : syracuseStep 1129889 = 847417) B847417
theorem B1424899 : Blo 666309 1424899 := bstep (se 1 (by rfl) ⟨1068674, by rfl⟩ : syracuseStep 1424899 = 2137349) B2137349
theorem B1130017 : Blo 666309 1130017 := bstep (se 2 (by rfl) ⟨423756, by rfl⟩ : syracuseStep 1130017 = 847513) B847513
theorem B1130051 : Blo 666309 1130051 := bstep (se 1 (by rfl) ⟨847538, by rfl⟩ : syracuseStep 1130051 = 1695077) B1695077
theorem B1687139 : Blo 666309 1687139 := bstep (se 1 (by rfl) ⟨1265354, by rfl⟩ : syracuseStep 1687139 = 2530709) B2530709
theorem B1130179 : Blo 666309 1130179 := bstep (se 1 (by rfl) ⟨847634, by rfl⟩ : syracuseStep 1130179 = 1695269) B1695269
theorem B1687331 : Blo 666309 1687331 := bstep (se 1 (by rfl) ⟨1265498, by rfl⟩ : syracuseStep 1687331 = 2530997) B2530997
theorem B2146115 : Blo 666309 2146115 := bstep (se 1 (by rfl) ⟨1609586, by rfl⟩ : syracuseStep 2146115 = 3219173) B3219173
theorem B1130321 : Blo 666309 1130321 := bstep (se 2 (by rfl) ⟨423870, by rfl⟩ : syracuseStep 1130321 = 847741) B847741
theorem B3653581 : Blo 666309 3653581 := bstep (se 3 (by rfl) ⟨685046, by rfl⟩ : syracuseStep 3653581 = 1370093) B1370093
theorem B1130449 : Blo 666309 1130449 := bstep (se 2 (by rfl) ⟨423918, by rfl⟩ : syracuseStep 1130449 = 847837) B847837
theorem B2572273 : Blo 666309 2572273 := bstep (se 2 (by rfl) ⟨964602, by rfl⟩ : syracuseStep 2572273 = 1929205) B1929205
theorem B1130483 : Blo 666309 1130483 := bstep (se 1 (by rfl) ⟨847862, by rfl⟩ : syracuseStep 1130483 = 1695725) B1695725
theorem B999473 : Blo 666309 999473 := bstep (se 2 (by rfl) ⟨374802, by rfl⟩ : syracuseStep 999473 = 749605) B749605
theorem B999491 : Blo 666309 999491 := bstep (se 1 (by rfl) ⟨749618, by rfl⟩ : syracuseStep 999491 = 1499237) B1499237
theorem B999521 : Blo 666309 999521 := bstep (se 2 (by rfl) ⟨374820, by rfl⟩ : syracuseStep 999521 = 749641) B749641
theorem B901219 : Blo 666309 901219 := bstep (se 1 (by rfl) ⟨675914, by rfl⟩ : syracuseStep 901219 = 1351829) B1351829
theorem B999539 : Blo 666309 999539 := bstep (se 1 (by rfl) ⟨749654, by rfl⟩ : syracuseStep 999539 = 1499309) B1499309
theorem B1130611 : Blo 666309 1130611 := bstep (se 1 (by rfl) ⟨847958, by rfl⟩ : syracuseStep 1130611 = 1695917) B1695917
theorem B999569 : Blo 666309 999569 := bstep (se 2 (by rfl) ⟨374838, by rfl⟩ : syracuseStep 999569 = 749677) B749677
theorem B999587 : Blo 666309 999587 := bstep (se 1 (by rfl) ⟨749690, by rfl⟩ : syracuseStep 999587 = 1499381) B1499381
theorem B999617 : Blo 666309 999617 := bstep (se 2 (by rfl) ⟨374856, by rfl⟩ : syracuseStep 999617 = 749713) B749713
theorem B1425617 : Blo 666309 1425617 := bstep (se 2 (by rfl) ⟨534606, by rfl⟩ : syracuseStep 1425617 = 1069213) B1069213
theorem B999635 : Blo 666309 999635 := bstep (se 1 (by rfl) ⟨749726, by rfl⟩ : syracuseStep 999635 = 1499453) B1499453
theorem B999665 : Blo 666309 999665 := bstep (se 2 (by rfl) ⟨374874, by rfl⟩ : syracuseStep 999665 = 749749) B749749
theorem B1130753 : Blo 666309 1130753 := bstep (se 2 (by rfl) ⟨424032, by rfl⟩ : syracuseStep 1130753 = 848065) B848065
theorem B999683 : Blo 666309 999683 := bstep (se 1 (by rfl) ⟨749762, by rfl⟩ : syracuseStep 999683 = 1499525) B1499525
theorem B999713 : Blo 666309 999713 := bstep (se 2 (by rfl) ⟨374892, by rfl⟩ : syracuseStep 999713 = 749785) B749785
theorem B3391793 : Blo 666309 3391793 := bstep (se 2 (by rfl) ⟨1271922, by rfl⟩ : syracuseStep 3391793 = 2543845) B2543845
theorem B999731 : Blo 666309 999731 := bstep (se 1 (by rfl) ⟨749798, by rfl⟩ : syracuseStep 999731 = 1499597) B1499597
theorem B999761 : Blo 666309 999761 := bstep (se 2 (by rfl) ⟨374910, by rfl⟩ : syracuseStep 999761 = 749821) B749821
theorem B999779 : Blo 666309 999779 := bstep (se 1 (by rfl) ⟨749834, by rfl⟩ : syracuseStep 999779 = 1499669) B1499669
theorem B999809 : Blo 666309 999809 := bstep (se 2 (by rfl) ⟨374928, by rfl⟩ : syracuseStep 999809 = 749857) B749857
theorem B1130881 : Blo 666309 1130881 := bstep (se 2 (by rfl) ⟨424080, by rfl⟩ : syracuseStep 1130881 = 848161) B848161
theorem B999827 : Blo 666309 999827 := bstep (se 1 (by rfl) ⟨749870, by rfl⟩ : syracuseStep 999827 = 1499741) B1499741
theorem B1130915 : Blo 666309 1130915 := bstep (se 1 (by rfl) ⟨848186, by rfl⟩ : syracuseStep 1130915 = 1696373) B1696373
theorem B999857 : Blo 666309 999857 := bstep (se 2 (by rfl) ⟨374946, by rfl⟩ : syracuseStep 999857 = 749893) B749893
theorem B999875 : Blo 666309 999875 := bstep (se 1 (by rfl) ⟨749906, by rfl⟩ : syracuseStep 999875 = 1499813) B1499813
theorem B2113997 : Blo 666309 2113997 := bstep (se 3 (by rfl) ⟨396374, by rfl⟩ : syracuseStep 2113997 = 792749) B792749
theorem B2146769 : Blo 666309 2146769 := bstep (se 2 (by rfl) ⟨805038, by rfl⟩ : syracuseStep 2146769 = 1610077) B1610077
theorem B999905 : Blo 666309 999905 := bstep (se 2 (by rfl) ⟨374964, by rfl⟩ : syracuseStep 999905 = 749929) B749929
theorem B803299 : Blo 666309 803299 := bstep (se 1 (by rfl) ⟨602474, by rfl⟩ : syracuseStep 803299 = 1204949) B1204949
theorem B999923 : Blo 666309 999923 := bstep (se 1 (by rfl) ⟨749942, by rfl⟩ : syracuseStep 999923 = 1499885) B1499885
theorem B999953 : Blo 666309 999953 := bstep (se 2 (by rfl) ⟨374982, by rfl⟩ : syracuseStep 999953 = 749965) B749965
theorem B999971 : Blo 666309 999971 := bstep (se 1 (by rfl) ⟨749978, by rfl⟩ : syracuseStep 999971 = 1499957) B1499957
theorem B1131043 : Blo 666309 1131043 := bstep (se 1 (by rfl) ⟨848282, by rfl⟩ : syracuseStep 1131043 = 1696565) B1696565
theorem B1000001 : Blo 666309 1000001 := bstep (se 2 (by rfl) ⟨375000, by rfl⟩ : syracuseStep 1000001 = 750001) B750001
theorem B1000019 : Blo 666309 1000019 := bstep (se 1 (by rfl) ⟨750014, by rfl⟩ : syracuseStep 1000019 = 1500029) B1500029
theorem B1000049 : Blo 666309 1000049 := bstep (se 2 (by rfl) ⟨375018, by rfl⟩ : syracuseStep 1000049 = 750037) B750037
theorem B7225969 : Blo 666309 7225969 := bstep (se 2 (by rfl) ⟨2709738, by rfl⟩ : syracuseStep 7225969 = 5419477) B5419477
theorem B1000067 : Blo 666309 1000067 := bstep (se 1 (by rfl) ⟨750050, by rfl⟩ : syracuseStep 1000067 = 1500101) B1500101
theorem B1000097 : Blo 666309 1000097 := bstep (se 2 (by rfl) ⟨375036, by rfl⟩ : syracuseStep 1000097 = 750073) B750073
theorem B1000115 : Blo 666309 1000115 := bstep (se 1 (by rfl) ⟨750086, by rfl⟩ : syracuseStep 1000115 = 1500173) B1500173
theorem B1000145 : Blo 666309 1000145 := bstep (se 2 (by rfl) ⟨375054, by rfl⟩ : syracuseStep 1000145 = 750109) B750109
theorem B1688273 : Blo 666309 1688273 := bstep (se 2 (by rfl) ⟨633102, by rfl⟩ : syracuseStep 1688273 = 1266205) B1266205
theorem B1000163 : Blo 666309 1000163 := bstep (se 1 (by rfl) ⟨750122, by rfl⟩ : syracuseStep 1000163 = 1500245) B1500245
theorem B1000193 : Blo 666309 1000193 := bstep (se 2 (by rfl) ⟨375072, by rfl⟩ : syracuseStep 1000193 = 750145) B750145
theorem B1688323 : Blo 666309 1688323 := bstep (se 1 (by rfl) ⟨1266242, by rfl⟩ : syracuseStep 1688323 = 2532485) B2532485
theorem B1000211 : Blo 666309 1000211 := bstep (se 1 (by rfl) ⟨750158, by rfl⟩ : syracuseStep 1000211 = 1500317) B1500317
theorem B1000241 : Blo 666309 1000241 := bstep (se 2 (by rfl) ⟨375090, by rfl⟩ : syracuseStep 1000241 = 750181) B750181
theorem B1000259 : Blo 666309 1000259 := bstep (se 1 (by rfl) ⟨750194, by rfl⟩ : syracuseStep 1000259 = 1500389) B1500389
theorem B1000289 : Blo 666309 1000289 := bstep (se 2 (by rfl) ⟨375108, by rfl⟩ : syracuseStep 1000289 = 750217) B750217
theorem B1622897 : Blo 666309 1622897 := bstep (se 2 (by rfl) ⟨608586, by rfl⟩ : syracuseStep 1622897 = 1217173) B1217173
theorem B1000307 : Blo 666309 1000307 := bstep (se 1 (by rfl) ⟨750230, by rfl⟩ : syracuseStep 1000307 = 1500461) B1500461
theorem B2540429 : Blo 666309 2540429 := bstep (se 3 (by rfl) ⟨476330, by rfl⟩ : syracuseStep 2540429 = 952661) B952661
theorem B1000337 : Blo 666309 1000337 := bstep (se 2 (by rfl) ⟨375126, by rfl⟩ : syracuseStep 1000337 = 750253) B750253
theorem B1688465 : Blo 666309 1688465 := bstep (se 2 (by rfl) ⟨633174, by rfl⟩ : syracuseStep 1688465 = 1266349) B1266349
theorem B902035 : Blo 666309 902035 := bstep (se 1 (by rfl) ⟨676526, by rfl⟩ : syracuseStep 902035 = 1353053) B1353053
theorem B1000355 : Blo 666309 1000355 := bstep (se 1 (by rfl) ⟨750266, by rfl⟩ : syracuseStep 1000355 = 1500533) B1500533
theorem B3621809 : Blo 666309 3621809 := bstep (se 2 (by rfl) ⟨1358178, by rfl⟩ : syracuseStep 3621809 = 2716357) B2716357
theorem B1000385 : Blo 666309 1000385 := bstep (se 2 (by rfl) ⟨375144, by rfl⟩ : syracuseStep 1000385 = 750289) B750289
theorem B1000403 : Blo 666309 1000403 := bstep (se 1 (by rfl) ⟨750302, by rfl⟩ : syracuseStep 1000403 = 1500605) B1500605
theorem B1426403 : Blo 666309 1426403 := bstep (se 1 (by rfl) ⟨1069802, by rfl⟩ : syracuseStep 1426403 = 2139605) B2139605
theorem B1000433 : Blo 666309 1000433 := bstep (se 2 (by rfl) ⟨375162, by rfl⟩ : syracuseStep 1000433 = 750325) B750325
theorem B1000451 : Blo 666309 1000451 := bstep (se 1 (by rfl) ⟨750338, by rfl⟩ : syracuseStep 1000451 = 1500677) B1500677
theorem B1000481 : Blo 666309 1000481 := bstep (se 2 (by rfl) ⟨375180, by rfl⟩ : syracuseStep 1000481 = 750361) B750361
theorem B1000499 : Blo 666309 1000499 := bstep (se 1 (by rfl) ⟨750374, by rfl⟩ : syracuseStep 1000499 = 1500749) B1500749
theorem B1000529 : Blo 666309 1000529 := bstep (se 2 (by rfl) ⟨375198, by rfl⟩ : syracuseStep 1000529 = 750397) B750397
theorem B902225 : Blo 666309 902225 := bstep (se 2 (by rfl) ⟨338334, by rfl⟩ : syracuseStep 902225 = 676669) B676669
theorem B1000547 : Blo 666309 1000547 := bstep (se 1 (by rfl) ⟨750410, by rfl⟩ : syracuseStep 1000547 = 1500821) B1500821
theorem B1000577 : Blo 666309 1000577 := bstep (se 2 (by rfl) ⟨375216, by rfl⟩ : syracuseStep 1000577 = 750433) B750433
theorem B1000595 : Blo 666309 1000595 := bstep (se 1 (by rfl) ⟨750446, by rfl⟩ : syracuseStep 1000595 = 1500893) B1500893
theorem B1000625 : Blo 666309 1000625 := bstep (se 2 (by rfl) ⟨375234, by rfl⟩ : syracuseStep 1000625 = 750469) B750469
theorem B1000643 : Blo 666309 1000643 := bstep (se 1 (by rfl) ⟨750482, by rfl⟩ : syracuseStep 1000643 = 1500965) B1500965
theorem B1000673 : Blo 666309 1000673 := bstep (se 2 (by rfl) ⟨375252, by rfl⟩ : syracuseStep 1000673 = 750505) B750505
theorem B1000691 : Blo 666309 1000691 := bstep (se 1 (by rfl) ⟨750518, by rfl⟩ : syracuseStep 1000691 = 1501037) B1501037
theorem B1000721 : Blo 666309 1000721 := bstep (se 2 (by rfl) ⟨375270, by rfl⟩ : syracuseStep 1000721 = 750541) B750541
theorem B1000739 : Blo 666309 1000739 := bstep (se 1 (by rfl) ⟨750554, by rfl⟩ : syracuseStep 1000739 = 1501109) B1501109
theorem B1000769 : Blo 666309 1000769 := bstep (se 2 (by rfl) ⟨375288, by rfl⟩ : syracuseStep 1000769 = 750577) B750577
theorem B1000787 : Blo 666309 1000787 := bstep (se 1 (by rfl) ⟨750590, by rfl⟩ : syracuseStep 1000787 = 1501181) B1501181
theorem B1000817 : Blo 666309 1000817 := bstep (se 2 (by rfl) ⟨375306, by rfl⟩ : syracuseStep 1000817 = 750613) B750613
theorem B1000835 : Blo 666309 1000835 := bstep (se 1 (by rfl) ⟨750626, by rfl⟩ : syracuseStep 1000835 = 1501253) B1501253
theorem B1000865 : Blo 666309 1000865 := bstep (se 2 (by rfl) ⟨375324, by rfl⟩ : syracuseStep 1000865 = 750649) B750649
theorem B1000883 : Blo 666309 1000883 := bstep (se 1 (by rfl) ⟨750662, by rfl⟩ : syracuseStep 1000883 = 1501325) B1501325
theorem B1000913 : Blo 666309 1000913 := bstep (se 2 (by rfl) ⟨375342, by rfl⟩ : syracuseStep 1000913 = 750685) B750685
theorem B1000931 : Blo 666309 1000931 := bstep (se 1 (by rfl) ⟨750698, by rfl⟩ : syracuseStep 1000931 = 1501397) B1501397
theorem B1000961 : Blo 666309 1000961 := bstep (se 2 (by rfl) ⟨375360, by rfl⟩ : syracuseStep 1000961 = 750721) B750721
theorem B1000979 : Blo 666309 1000979 := bstep (se 1 (by rfl) ⟨750734, by rfl⟩ : syracuseStep 1000979 = 1501469) B1501469
theorem B1001009 : Blo 666309 1001009 := bstep (se 2 (by rfl) ⟨375378, by rfl⟩ : syracuseStep 1001009 = 750757) B750757
theorem B1001027 : Blo 666309 1001027 := bstep (se 1 (by rfl) ⟨750770, by rfl⟩ : syracuseStep 1001027 = 1501541) B1501541
theorem B1001057 : Blo 666309 1001057 := bstep (se 2 (by rfl) ⟨375396, by rfl⟩ : syracuseStep 1001057 = 750793) B750793
theorem B902755 : Blo 666309 902755 := bstep (se 1 (by rfl) ⟨677066, by rfl⟩ : syracuseStep 902755 = 1354133) B1354133
theorem B1001075 : Blo 666309 1001075 := bstep (se 1 (by rfl) ⟨750806, by rfl⟩ : syracuseStep 1001075 = 1501613) B1501613
theorem B1001105 : Blo 666309 1001105 := bstep (se 2 (by rfl) ⟨375414, by rfl⟩ : syracuseStep 1001105 = 750829) B750829
theorem B1001123 : Blo 666309 1001123 := bstep (se 1 (by rfl) ⟨750842, by rfl⟩ : syracuseStep 1001123 = 1501685) B1501685
theorem B2541233 : Blo 666309 2541233 := bstep (se 2 (by rfl) ⟨952962, by rfl⟩ : syracuseStep 2541233 = 1905925) B1905925
theorem B1001153 : Blo 666309 1001153 := bstep (se 2 (by rfl) ⟨375432, by rfl⟩ : syracuseStep 1001153 = 750865) B750865
theorem B1001171 : Blo 666309 1001171 := bstep (se 1 (by rfl) ⟨750878, by rfl⟩ : syracuseStep 1001171 = 1501757) B1501757
theorem B3393251 : Blo 666309 3393251 := bstep (se 1 (by rfl) ⟨2544938, by rfl⟩ : syracuseStep 3393251 = 5089877) B5089877
theorem B1001201 : Blo 666309 1001201 := bstep (se 2 (by rfl) ⟨375450, by rfl⟩ : syracuseStep 1001201 = 750901) B750901
theorem B1001219 : Blo 666309 1001219 := bstep (se 1 (by rfl) ⟨750914, by rfl⟩ : syracuseStep 1001219 = 1501829) B1501829
theorem B1001249 : Blo 666309 1001249 := bstep (se 2 (by rfl) ⟨375468, by rfl⟩ : syracuseStep 1001249 = 750937) B750937
theorem B1001267 : Blo 666309 1001267 := bstep (se 1 (by rfl) ⟨750950, by rfl⟩ : syracuseStep 1001267 = 1501901) B1501901
theorem B1001297 : Blo 666309 1001297 := bstep (se 2 (by rfl) ⟨375486, by rfl⟩ : syracuseStep 1001297 = 750973) B750973
theorem B1001315 : Blo 666309 1001315 := bstep (se 1 (by rfl) ⟨750986, by rfl⟩ : syracuseStep 1001315 = 1501973) B1501973
theorem B1689457 : Blo 666309 1689457 := bstep (se 2 (by rfl) ⟨633546, by rfl⟩ : syracuseStep 1689457 = 1267093) B1267093
theorem B1001345 : Blo 666309 1001345 := bstep (se 2 (by rfl) ⟨375504, by rfl⟩ : syracuseStep 1001345 = 751009) B751009
theorem B1001363 : Blo 666309 1001363 := bstep (se 1 (by rfl) ⟨751022, by rfl⟩ : syracuseStep 1001363 = 1502045) B1502045
theorem B1001393 : Blo 666309 1001393 := bstep (se 2 (by rfl) ⟨375522, by rfl⟩ : syracuseStep 1001393 = 751045) B751045
theorem B1427377 : Blo 666309 1427377 := bstep (se 2 (by rfl) ⟨535266, by rfl⟩ : syracuseStep 1427377 = 1070533) B1070533
theorem B1001411 : Blo 666309 1001411 := bstep (se 1 (by rfl) ⟨751058, by rfl⟩ : syracuseStep 1001411 = 1502117) B1502117
theorem B1001441 : Blo 666309 1001441 := bstep (se 2 (by rfl) ⟨375540, by rfl⟩ : syracuseStep 1001441 = 751081) B751081
theorem B1001459 : Blo 666309 1001459 := bstep (se 1 (by rfl) ⟨751094, by rfl⟩ : syracuseStep 1001459 = 1502189) B1502189
theorem B1001489 : Blo 666309 1001489 := bstep (se 2 (by rfl) ⟨375558, by rfl⟩ : syracuseStep 1001489 = 751117) B751117
theorem B903187 : Blo 666309 903187 := bstep (se 1 (by rfl) ⟨677390, by rfl⟩ : syracuseStep 903187 = 1354781) B1354781
theorem B1001507 : Blo 666309 1001507 := bstep (se 1 (by rfl) ⟨751130, by rfl⟩ : syracuseStep 1001507 = 1502261) B1502261
theorem B1001537 : Blo 666309 1001537 := bstep (se 2 (by rfl) ⟨375576, by rfl⟩ : syracuseStep 1001537 = 751153) B751153
theorem B1001555 : Blo 666309 1001555 := bstep (se 1 (by rfl) ⟨751166, by rfl⟩ : syracuseStep 1001555 = 1502333) B1502333
theorem B1001585 : Blo 666309 1001585 := bstep (se 2 (by rfl) ⟨375594, by rfl⟩ : syracuseStep 1001585 = 751189) B751189
theorem B1689731 : Blo 666309 1689731 := bstep (se 1 (by rfl) ⟨1267298, by rfl⟩ : syracuseStep 1689731 = 2534597) B2534597
theorem B1001603 : Blo 666309 1001603 := bstep (se 1 (by rfl) ⟨751202, by rfl⟩ : syracuseStep 1001603 = 1502405) B1502405
theorem B1001633 : Blo 666309 1001633 := bstep (se 2 (by rfl) ⟨375612, by rfl⟩ : syracuseStep 1001633 = 751225) B751225
theorem B1427633 : Blo 666309 1427633 := bstep (se 2 (by rfl) ⟨535362, by rfl⟩ : syracuseStep 1427633 = 1070725) B1070725
theorem B1001651 : Blo 666309 1001651 := bstep (se 1 (by rfl) ⟨751238, by rfl⟩ : syracuseStep 1001651 = 1502477) B1502477
theorem B1001681 : Blo 666309 1001681 := bstep (se 2 (by rfl) ⟨375630, by rfl⟩ : syracuseStep 1001681 = 751261) B751261
theorem B1001699 : Blo 666309 1001699 := bstep (se 1 (by rfl) ⟨751274, by rfl⟩ : syracuseStep 1001699 = 1502549) B1502549
theorem B1001729 : Blo 666309 1001729 := bstep (se 2 (by rfl) ⟨375648, by rfl⟩ : syracuseStep 1001729 = 751297) B751297
theorem B1001747 : Blo 666309 1001747 := bstep (se 1 (by rfl) ⟨751310, by rfl⟩ : syracuseStep 1001747 = 1502621) B1502621
theorem B1001777 : Blo 666309 1001777 := bstep (se 2 (by rfl) ⟨375666, by rfl⟩ : syracuseStep 1001777 = 751333) B751333
theorem B1689923 : Blo 666309 1689923 := bstep (se 1 (by rfl) ⟨1267442, by rfl⟩ : syracuseStep 1689923 = 2534885) B2534885
theorem B1001795 : Blo 666309 1001795 := bstep (se 1 (by rfl) ⟨751346, by rfl⟩ : syracuseStep 1001795 = 1502693) B1502693
theorem B2541901 : Blo 666309 2541901 := bstep (se 3 (by rfl) ⟨476606, by rfl⟩ : syracuseStep 2541901 = 953213) B953213
theorem B1001825 : Blo 666309 1001825 := bstep (se 2 (by rfl) ⟨375684, by rfl⟩ : syracuseStep 1001825 = 751369) B751369
theorem B2279789 : Blo 666309 2279789 := bstep (se 3 (by rfl) ⟨427460, by rfl⟩ : syracuseStep 2279789 = 854921) B854921
theorem B1001843 : Blo 666309 1001843 := bstep (se 1 (by rfl) ⟨751382, by rfl⟩ : syracuseStep 1001843 = 1502765) B1502765
theorem B1001873 : Blo 666309 1001873 := bstep (se 2 (by rfl) ⟨375702, by rfl⟩ : syracuseStep 1001873 = 751405) B751405
theorem B1001891 : Blo 666309 1001891 := bstep (se 1 (by rfl) ⟨751418, by rfl⟩ : syracuseStep 1001891 = 1502837) B1502837
theorem B1001921 : Blo 666309 1001921 := bstep (se 2 (by rfl) ⟨375720, by rfl⟩ : syracuseStep 1001921 = 751441) B751441
theorem B1001939 : Blo 666309 1001939 := bstep (se 1 (by rfl) ⟨751454, by rfl⟩ : syracuseStep 1001939 = 1502909) B1502909
theorem B1001969 : Blo 666309 1001969 := bstep (se 2 (by rfl) ⟨375738, by rfl⟩ : syracuseStep 1001969 = 751477) B751477
theorem B1001987 : Blo 666309 1001987 := bstep (se 1 (by rfl) ⟨751490, by rfl⟩ : syracuseStep 1001987 = 1502981) B1502981
theorem B1002017 : Blo 666309 1002017 := bstep (se 2 (by rfl) ⟨375756, by rfl⟩ : syracuseStep 1002017 = 751513) B751513
theorem B1002035 : Blo 666309 1002035 := bstep (se 1 (by rfl) ⟨751526, by rfl⟩ : syracuseStep 1002035 = 1503053) B1503053
theorem B5720645 : Blo 666309 5720645 := bstep (se 4 (by rfl) ⟨536310, by rfl⟩ : syracuseStep 5720645 = 1072621) B1072621
theorem B1002065 : Blo 666309 1002065 := bstep (se 2 (by rfl) ⟨375774, by rfl⟩ : syracuseStep 1002065 = 751549) B751549
theorem B1002083 : Blo 666309 1002083 := bstep (se 1 (by rfl) ⟨751562, by rfl⟩ : syracuseStep 1002083 = 1503125) B1503125
theorem B903793 : Blo 666309 903793 := bstep (se 2 (by rfl) ⟨338922, by rfl⟩ : syracuseStep 903793 = 677845) B677845
theorem B1002113 : Blo 666309 1002113 := bstep (se 2 (by rfl) ⟨375792, by rfl⟩ : syracuseStep 1002113 = 751585) B751585
theorem B1002131 : Blo 666309 1002131 := bstep (se 1 (by rfl) ⟨751598, by rfl⟩ : syracuseStep 1002131 = 1503197) B1503197
theorem B1002161 : Blo 666309 1002161 := bstep (se 2 (by rfl) ⟨375810, by rfl⟩ : syracuseStep 1002161 = 751621) B751621
theorem B1002179 : Blo 666309 1002179 := bstep (se 1 (by rfl) ⟨751634, by rfl⟩ : syracuseStep 1002179 = 1503269) B1503269
theorem B1002209 : Blo 666309 1002209 := bstep (se 2 (by rfl) ⟨375828, by rfl⟩ : syracuseStep 1002209 = 751657) B751657
theorem B1002227 : Blo 666309 1002227 := bstep (se 1 (by rfl) ⟨751670, by rfl⟩ : syracuseStep 1002227 = 1503341) B1503341
theorem B1002257 : Blo 666309 1002257 := bstep (se 2 (by rfl) ⟨375846, by rfl⟩ : syracuseStep 1002257 = 751693) B751693
theorem B903955 : Blo 666309 903955 := bstep (se 1 (by rfl) ⟨677966, by rfl⟩ : syracuseStep 903955 = 1355933) B1355933
theorem B1002275 : Blo 666309 1002275 := bstep (se 1 (by rfl) ⟨751706, by rfl⟩ : syracuseStep 1002275 = 1503413) B1503413
theorem B1002305 : Blo 666309 1002305 := bstep (se 2 (by rfl) ⟨375864, by rfl⟩ : syracuseStep 1002305 = 751729) B751729
theorem B1002323 : Blo 666309 1002323 := bstep (se 1 (by rfl) ⟨751742, by rfl⟩ : syracuseStep 1002323 = 1503485) B1503485
theorem B17124209 : Blo 666309 17124209 := bstep (se 2 (by rfl) ⟨6421578, by rfl⟩ : syracuseStep 17124209 = 12843157) B12843157
theorem B1002353 : Blo 666309 1002353 := bstep (se 2 (by rfl) ⟨375882, by rfl⟩ : syracuseStep 1002353 = 751765) B751765
theorem B1002371 : Blo 666309 1002371 := bstep (se 1 (by rfl) ⟨751778, by rfl⟩ : syracuseStep 1002371 = 1503557) B1503557
theorem B1002401 : Blo 666309 1002401 := bstep (se 2 (by rfl) ⟨375900, by rfl⟩ : syracuseStep 1002401 = 751801) B751801
theorem B1002419 : Blo 666309 1002419 := bstep (se 1 (by rfl) ⟨751814, by rfl⟩ : syracuseStep 1002419 = 1503629) B1503629
theorem B1002449 : Blo 666309 1002449 := bstep (se 2 (by rfl) ⟨375918, by rfl⟩ : syracuseStep 1002449 = 751837) B751837
theorem B1526737 : Blo 666309 1526737 := bstep (se 2 (by rfl) ⟨572526, by rfl⟩ : syracuseStep 1526737 = 1145053) B1145053
theorem B1002467 : Blo 666309 1002467 := bstep (se 1 (by rfl) ⟨751850, by rfl⟩ : syracuseStep 1002467 = 1503701) B1503701
theorem B1002497 : Blo 666309 1002497 := bstep (se 2 (by rfl) ⟨375936, by rfl⟩ : syracuseStep 1002497 = 751873) B751873
theorem B1002515 : Blo 666309 1002515 := bstep (se 1 (by rfl) ⟨751886, by rfl⟩ : syracuseStep 1002515 = 1503773) B1503773
theorem B1002545 : Blo 666309 1002545 := bstep (se 2 (by rfl) ⟨375954, by rfl⟩ : syracuseStep 1002545 = 751909) B751909
theorem B1002563 : Blo 666309 1002563 := bstep (se 1 (by rfl) ⟨751922, by rfl⟩ : syracuseStep 1002563 = 1503845) B1503845
theorem B1002593 : Blo 666309 1002593 := bstep (se 2 (by rfl) ⟨375972, by rfl⟩ : syracuseStep 1002593 = 751945) B751945
theorem B904289 : Blo 666309 904289 := bstep (se 2 (by rfl) ⟨339108, by rfl⟩ : syracuseStep 904289 = 678217) B678217
theorem B2542691 : Blo 666309 2542691 := bstep (se 1 (by rfl) ⟨1907018, by rfl⟩ : syracuseStep 2542691 = 3814037) B3814037
theorem B1002611 : Blo 666309 1002611 := bstep (se 1 (by rfl) ⟨751958, by rfl⟩ : syracuseStep 1002611 = 1503917) B1503917
theorem B1002641 : Blo 666309 1002641 := bstep (se 2 (by rfl) ⟨375990, by rfl⟩ : syracuseStep 1002641 = 751981) B751981
theorem B1002659 : Blo 666309 1002659 := bstep (se 1 (by rfl) ⟨751994, by rfl⟩ : syracuseStep 1002659 = 1503989) B1503989
theorem B1002689 : Blo 666309 1002689 := bstep (se 2 (by rfl) ⟨376008, by rfl⟩ : syracuseStep 1002689 = 752017) B752017
theorem B1002707 : Blo 666309 1002707 := bstep (se 1 (by rfl) ⟨752030, by rfl⟩ : syracuseStep 1002707 = 1504061) B1504061
theorem B1690865 : Blo 666309 1690865 := bstep (se 2 (by rfl) ⟨634074, by rfl⟩ : syracuseStep 1690865 = 1268149) B1268149
theorem B1002737 : Blo 666309 1002737 := bstep (se 2 (by rfl) ⟨376026, by rfl⟩ : syracuseStep 1002737 = 752053) B752053
theorem B1002755 : Blo 666309 1002755 := bstep (se 1 (by rfl) ⟨752066, by rfl⟩ : syracuseStep 1002755 = 1504133) B1504133
theorem B1002785 : Blo 666309 1002785 := bstep (se 2 (by rfl) ⟨376044, by rfl⟩ : syracuseStep 1002785 = 752089) B752089
theorem B1690915 : Blo 666309 1690915 := bstep (se 1 (by rfl) ⟨1268186, by rfl⟩ : syracuseStep 1690915 = 2536373) B2536373
theorem B1002803 : Blo 666309 1002803 := bstep (se 1 (by rfl) ⟨752102, by rfl⟩ : syracuseStep 1002803 = 1504205) B1504205
theorem B1002833 : Blo 666309 1002833 := bstep (se 2 (by rfl) ⟨376062, by rfl⟩ : syracuseStep 1002833 = 752125) B752125
theorem B1002851 : Blo 666309 1002851 := bstep (se 1 (by rfl) ⟨752138, by rfl⟩ : syracuseStep 1002851 = 1504277) B1504277
theorem B8539505 : Blo 666309 8539505 := bstep (se 2 (by rfl) ⟨3202314, by rfl⟩ : syracuseStep 8539505 = 6404629) B6404629
theorem B1002881 : Blo 666309 1002881 := bstep (se 2 (by rfl) ⟨376080, by rfl⟩ : syracuseStep 1002881 = 752161) B752161
theorem B1002899 : Blo 666309 1002899 := bstep (se 1 (by rfl) ⟨752174, by rfl⟩ : syracuseStep 1002899 = 1504349) B1504349
theorem B1691057 : Blo 666309 1691057 := bstep (se 2 (by rfl) ⟨634146, by rfl⟩ : syracuseStep 1691057 = 1268293) B1268293
theorem B1002929 : Blo 666309 1002929 := bstep (se 2 (by rfl) ⟨376098, by rfl⟩ : syracuseStep 1002929 = 752197) B752197
theorem B9293237 : Blo 666309 9293237 := bstep (se 5 (by rfl) ⟨435620, by rfl⟩ : syracuseStep 9293237 = 871241) B871241
theorem B1002947 : Blo 666309 1002947 := bstep (se 1 (by rfl) ⟨752210, by rfl⟩ : syracuseStep 1002947 = 1504421) B1504421
theorem B1428931 : Blo 666309 1428931 := bstep (se 1 (by rfl) ⟨1071698, by rfl⟩ : syracuseStep 1428931 = 2143397) B2143397
theorem B1002977 : Blo 666309 1002977 := bstep (se 2 (by rfl) ⟨376116, by rfl⟩ : syracuseStep 1002977 = 752233) B752233
theorem B1002995 : Blo 666309 1002995 := bstep (se 1 (by rfl) ⟨752246, by rfl⟩ : syracuseStep 1002995 = 1504493) B1504493
theorem B1068547 : Blo 666309 1068547 := bstep (se 1 (by rfl) ⟨801410, by rfl⟩ : syracuseStep 1068547 = 1602821) B1602821
theorem B1003025 : Blo 666309 1003025 := bstep (se 2 (by rfl) ⟨376134, by rfl⟩ : syracuseStep 1003025 = 752269) B752269
theorem B1003043 : Blo 666309 1003043 := bstep (se 1 (by rfl) ⟨752282, by rfl⟩ : syracuseStep 1003043 = 1504565) B1504565
theorem B1003073 : Blo 666309 1003073 := bstep (se 2 (by rfl) ⟨376152, by rfl⟩ : syracuseStep 1003073 = 752305) B752305
theorem B4279877 : Blo 666309 4279877 := bstep (se 4 (by rfl) ⟨401238, by rfl⟩ : syracuseStep 4279877 = 802477) B802477
theorem B1265233 : Blo 666309 1265233 := bstep (se 2 (by rfl) ⟨474462, by rfl⟩ : syracuseStep 1265233 = 948925) B948925
theorem B1003091 : Blo 666309 1003091 := bstep (se 1 (by rfl) ⟨752318, by rfl⟩ : syracuseStep 1003091 = 1504637) B1504637
theorem B1003121 : Blo 666309 1003121 := bstep (se 2 (by rfl) ⟨376170, by rfl⟩ : syracuseStep 1003121 = 752341) B752341
theorem B1003139 : Blo 666309 1003139 := bstep (se 1 (by rfl) ⟨752354, by rfl⟩ : syracuseStep 1003139 = 1504709) B1504709
theorem B1003169 : Blo 666309 1003169 := bstep (se 2 (by rfl) ⟨376188, by rfl⟩ : syracuseStep 1003169 = 752377) B752377
theorem B1003187 : Blo 666309 1003187 := bstep (se 1 (by rfl) ⟨752390, by rfl⟩ : syracuseStep 1003187 = 1504781) B1504781
theorem B4181701 : Blo 666309 4181701 := bstep (se 4 (by rfl) ⟨392034, by rfl⟩ : syracuseStep 4181701 = 784069) B784069
theorem B1003217 : Blo 666309 1003217 := bstep (se 2 (by rfl) ⟨376206, by rfl⟩ : syracuseStep 1003217 = 752413) B752413
theorem B1003235 : Blo 666309 1003235 := bstep (se 1 (by rfl) ⟨752426, by rfl⟩ : syracuseStep 1003235 = 1504853) B1504853
theorem B2543345 : Blo 666309 2543345 := bstep (se 2 (by rfl) ⟨953754, by rfl⟩ : syracuseStep 2543345 = 1907509) B1907509
theorem B1003265 : Blo 666309 1003265 := bstep (se 2 (by rfl) ⟨376224, by rfl⟩ : syracuseStep 1003265 = 752449) B752449
theorem B1068803 : Blo 666309 1068803 := bstep (se 1 (by rfl) ⟨801602, by rfl⟩ : syracuseStep 1068803 = 1603205) B1603205
theorem B1429265 : Blo 666309 1429265 := bstep (se 2 (by rfl) ⟨535974, by rfl⟩ : syracuseStep 1429265 = 1071949) B1071949
theorem B1003283 : Blo 666309 1003283 := bstep (se 1 (by rfl) ⟨752462, by rfl⟩ : syracuseStep 1003283 = 1504925) B1504925
theorem B1003313 : Blo 666309 1003313 := bstep (se 2 (by rfl) ⟨376242, by rfl⟩ : syracuseStep 1003313 = 752485) B752485
theorem B2477873 : Blo 666309 2477873 := bstep (se 2 (by rfl) ⟨929202, by rfl⟩ : syracuseStep 2477873 = 1858405) B1858405
theorem B1003331 : Blo 666309 1003331 := bstep (se 1 (by rfl) ⟨752498, by rfl⟩ : syracuseStep 1003331 = 1504997) B1504997
theorem B1003361 : Blo 666309 1003361 := bstep (se 2 (by rfl) ⟨376260, by rfl⟩ : syracuseStep 1003361 = 752521) B752521
theorem B1003379 : Blo 666309 1003379 := bstep (se 1 (by rfl) ⟨752534, by rfl⟩ : syracuseStep 1003379 = 1505069) B1505069
theorem B1003409 : Blo 666309 1003409 := bstep (se 2 (by rfl) ⟨376278, by rfl⟩ : syracuseStep 1003409 = 752557) B752557
theorem B905107 : Blo 666309 905107 := bstep (se 1 (by rfl) ⟨678830, by rfl⟩ : syracuseStep 905107 = 1357661) B1357661
theorem B1003427 : Blo 666309 1003427 := bstep (se 1 (by rfl) ⟨752570, by rfl⟩ : syracuseStep 1003427 = 1505141) B1505141
theorem B1003457 : Blo 666309 1003457 := bstep (se 2 (by rfl) ⟨376296, by rfl⟩ : syracuseStep 1003457 = 752593) B752593
theorem B1068995 : Blo 666309 1068995 := bstep (se 1 (by rfl) ⟨801746, by rfl⟩ : syracuseStep 1068995 = 1603493) B1603493
theorem B1003475 : Blo 666309 1003475 := bstep (se 1 (by rfl) ⟨752606, by rfl⟩ : syracuseStep 1003475 = 1505213) B1505213
theorem B1265635 : Blo 666309 1265635 := bstep (se 1 (by rfl) ⟨949226, by rfl⟩ : syracuseStep 1265635 = 1898453) B1898453
theorem B1003505 : Blo 666309 1003505 := bstep (se 2 (by rfl) ⟨376314, by rfl⟩ : syracuseStep 1003505 = 752629) B752629
theorem B1003523 : Blo 666309 1003523 := bstep (se 1 (by rfl) ⟨752642, by rfl⟩ : syracuseStep 1003523 = 1505285) B1505285
theorem B1265681 : Blo 666309 1265681 := bstep (se 2 (by rfl) ⟨474630, by rfl⟩ : syracuseStep 1265681 = 949261) B949261
theorem B1003553 : Blo 666309 1003553 := bstep (se 2 (by rfl) ⟨376332, by rfl⟩ : syracuseStep 1003553 = 752665) B752665
theorem B1003571 : Blo 666309 1003571 := bstep (se 1 (by rfl) ⟨752678, by rfl⟩ : syracuseStep 1003571 = 1505357) B1505357
theorem B2576461 : Blo 666309 2576461 := bstep (se 3 (by rfl) ⟨483086, by rfl⟩ : syracuseStep 2576461 = 966173) B966173
theorem B1003601 : Blo 666309 1003601 := bstep (se 2 (by rfl) ⟨376350, by rfl⟩ : syracuseStep 1003601 = 752701) B752701
theorem B1003619 : Blo 666309 1003619 := bstep (se 1 (by rfl) ⟨752714, by rfl⟩ : syracuseStep 1003619 = 1505429) B1505429
theorem B675955 : Blo 666309 675955 := bstep (se 1 (by rfl) ⟨506966, by rfl⟩ : syracuseStep 675955 = 1013933) B1013933
theorem B1003649 : Blo 666309 1003649 := bstep (se 2 (by rfl) ⟨376368, by rfl⟩ : syracuseStep 1003649 = 752737) B752737
theorem B1003667 : Blo 666309 1003667 := bstep (se 1 (by rfl) ⟨752750, by rfl⟩ : syracuseStep 1003667 = 1505501) B1505501
theorem B1003697 : Blo 666309 1003697 := bstep (se 2 (by rfl) ⟨376386, by rfl⟩ : syracuseStep 1003697 = 752773) B752773
theorem B1003715 : Blo 666309 1003715 := bstep (se 1 (by rfl) ⟨752786, by rfl⟩ : syracuseStep 1003715 = 1505573) B1505573
theorem B1003745 : Blo 666309 1003745 := bstep (se 2 (by rfl) ⟨376404, by rfl⟩ : syracuseStep 1003745 = 752809) B752809
theorem B1003763 : Blo 666309 1003763 := bstep (se 1 (by rfl) ⟨752822, by rfl⟩ : syracuseStep 1003763 = 1505645) B1505645
theorem B1003793 : Blo 666309 1003793 := bstep (se 2 (by rfl) ⟨376422, by rfl⟩ : syracuseStep 1003793 = 752845) B752845
theorem B1003811 : Blo 666309 1003811 := bstep (se 1 (by rfl) ⟨752858, by rfl⟩ : syracuseStep 1003811 = 1505717) B1505717
theorem B1265969 : Blo 666309 1265969 := bstep (se 2 (by rfl) ⟨474738, by rfl⟩ : syracuseStep 1265969 = 949477) B949477
theorem B1003841 : Blo 666309 1003841 := bstep (se 2 (by rfl) ⟨376440, by rfl⟩ : syracuseStep 1003841 = 752881) B752881
theorem B1003859 : Blo 666309 1003859 := bstep (se 1 (by rfl) ⟨752894, by rfl⟩ : syracuseStep 1003859 = 1505789) B1505789
theorem B1003889 : Blo 666309 1003889 := bstep (se 2 (by rfl) ⟨376458, by rfl⟩ : syracuseStep 1003889 = 752917) B752917
theorem B1003907 : Blo 666309 1003907 := bstep (se 1 (by rfl) ⟨752930, by rfl⟩ : syracuseStep 1003907 = 1505861) B1505861
theorem B1692049 : Blo 666309 1692049 := bstep (se 2 (by rfl) ⟨634518, by rfl⟩ : syracuseStep 1692049 = 1269037) B1269037
theorem B1003937 : Blo 666309 1003937 := bstep (se 2 (by rfl) ⟨376476, by rfl⟩ : syracuseStep 1003937 = 752953) B752953
theorem B1003955 : Blo 666309 1003955 := bstep (se 1 (by rfl) ⟨752966, by rfl⟩ : syracuseStep 1003955 = 1505933) B1505933
theorem B1003985 : Blo 666309 1003985 := bstep (se 2 (by rfl) ⟨376494, by rfl⟩ : syracuseStep 1003985 = 752989) B752989
theorem B1004003 : Blo 666309 1004003 := bstep (se 1 (by rfl) ⟨753002, by rfl⟩ : syracuseStep 1004003 = 1506005) B1506005
theorem B1004033 : Blo 666309 1004033 := bstep (se 2 (by rfl) ⟨376512, by rfl⟩ : syracuseStep 1004033 = 753025) B753025
theorem B1004051 : Blo 666309 1004051 := bstep (se 1 (by rfl) ⟨753038, by rfl⟩ : syracuseStep 1004051 = 1506077) B1506077
theorem B2249261 : Blo 666309 2249261 := bstep (se 3 (by rfl) ⟨421736, by rfl⟩ : syracuseStep 2249261 = 843473) B843473
theorem B1004081 : Blo 666309 1004081 := bstep (se 2 (by rfl) ⟨376530, by rfl⟩ : syracuseStep 1004081 = 753061) B753061
theorem B1004099 : Blo 666309 1004099 := bstep (se 1 (by rfl) ⟨753074, by rfl⟩ : syracuseStep 1004099 = 1506149) B1506149
theorem B1004129 : Blo 666309 1004129 := bstep (se 2 (by rfl) ⟨376548, by rfl⟩ : syracuseStep 1004129 = 753097) B753097
theorem B2249315 : Blo 666309 2249315 := bstep (se 1 (by rfl) ⟨1686986, by rfl⟩ : syracuseStep 2249315 = 3373973) B3373973
theorem B1004147 : Blo 666309 1004147 := bstep (se 1 (by rfl) ⟨753110, by rfl⟩ : syracuseStep 1004147 = 1506221) B1506221
theorem B8245901 : Blo 666309 8245901 := bstep (se 3 (by rfl) ⟨1546106, by rfl⟩ : syracuseStep 8245901 = 3092213) B3092213
theorem B1004177 : Blo 666309 1004177 := bstep (se 2 (by rfl) ⟨376566, by rfl⟩ : syracuseStep 1004177 = 753133) B753133
theorem B1692323 : Blo 666309 1692323 := bstep (se 1 (by rfl) ⟨1269242, by rfl⟩ : syracuseStep 1692323 = 2538485) B2538485
theorem B1004195 : Blo 666309 1004195 := bstep (se 1 (by rfl) ⟨753146, by rfl⟩ : syracuseStep 1004195 = 1506293) B1506293
theorem B1200817 : Blo 666309 1200817 := bstep (se 2 (by rfl) ⟨450306, by rfl⟩ : syracuseStep 1200817 = 900613) B900613
theorem B1004225 : Blo 666309 1004225 := bstep (se 2 (by rfl) ⟨376584, by rfl⟩ : syracuseStep 1004225 = 753169) B753169
theorem B1069777 : Blo 666309 1069777 := bstep (se 2 (by rfl) ⟨401166, by rfl⟩ : syracuseStep 1069777 = 802333) B802333
theorem B1004243 : Blo 666309 1004243 := bstep (se 1 (by rfl) ⟨753182, by rfl⟩ : syracuseStep 1004243 = 1506365) B1506365
theorem B1004273 : Blo 666309 1004273 := bstep (se 2 (by rfl) ⟨376602, by rfl⟩ : syracuseStep 1004273 = 753205) B753205
theorem B1004291 : Blo 666309 1004291 := bstep (se 1 (by rfl) ⟨753218, by rfl⟩ : syracuseStep 1004291 = 1506437) B1506437
theorem B1004321 : Blo 666309 1004321 := bstep (se 2 (by rfl) ⟨376620, by rfl⟩ : syracuseStep 1004321 = 753241) B753241
theorem B1004339 : Blo 666309 1004339 := bstep (se 1 (by rfl) ⟨753254, by rfl⟩ : syracuseStep 1004339 = 1506509) B1506509
theorem B1004369 : Blo 666309 1004369 := bstep (se 2 (by rfl) ⟨376638, by rfl⟩ : syracuseStep 1004369 = 753277) B753277
theorem B1692515 : Blo 666309 1692515 := bstep (se 1 (by rfl) ⟨1269386, by rfl⟩ : syracuseStep 1692515 = 2538773) B2538773
theorem B1004387 : Blo 666309 1004387 := bstep (se 1 (by rfl) ⟨753290, by rfl⟩ : syracuseStep 1004387 = 1506581) B1506581
theorem B2249585 : Blo 666309 2249585 := bstep (se 2 (by rfl) ⟨843594, by rfl⟩ : syracuseStep 2249585 = 1687189) B1687189
theorem B1004417 : Blo 666309 1004417 := bstep (se 2 (by rfl) ⟨376656, by rfl⟩ : syracuseStep 1004417 = 753313) B753313
theorem B1004435 : Blo 666309 1004435 := bstep (se 1 (by rfl) ⟨753326, by rfl⟩ : syracuseStep 1004435 = 1506653) B1506653
theorem B1430435 : Blo 666309 1430435 := bstep (se 1 (by rfl) ⟨1072826, by rfl⟩ : syracuseStep 1430435 = 2145653) B2145653
theorem B1004465 : Blo 666309 1004465 := bstep (se 2 (by rfl) ⟨376674, by rfl⟩ : syracuseStep 1004465 = 753349) B753349
theorem B1004483 : Blo 666309 1004483 := bstep (se 1 (by rfl) ⟨753362, by rfl⟩ : syracuseStep 1004483 = 1506725) B1506725
theorem B1004513 : Blo 666309 1004513 := bstep (se 2 (by rfl) ⟨376692, by rfl⟩ : syracuseStep 1004513 = 753385) B753385
theorem B1004531 : Blo 666309 1004531 := bstep (se 1 (by rfl) ⟨753398, by rfl⟩ : syracuseStep 1004531 = 1506797) B1506797
theorem B1266691 : Blo 666309 1266691 := bstep (se 1 (by rfl) ⟨950018, by rfl⟩ : syracuseStep 1266691 = 1900037) B1900037
theorem B1004561 : Blo 666309 1004561 := bstep (se 2 (by rfl) ⟨376710, by rfl⟩ : syracuseStep 1004561 = 753421) B753421
theorem B1004579 : Blo 666309 1004579 := bstep (se 1 (by rfl) ⟨753434, by rfl⟩ : syracuseStep 1004579 = 1506869) B1506869
theorem B1004609 : Blo 666309 1004609 := bstep (se 2 (by rfl) ⟨376728, by rfl⟩ : syracuseStep 1004609 = 753457) B753457
theorem B1758275 : Blo 666309 1758275 := bstep (se 1 (by rfl) ⟨1318706, by rfl⟩ : syracuseStep 1758275 = 2637413) B2637413
theorem B1004627 : Blo 666309 1004627 := bstep (se 1 (by rfl) ⟨753470, by rfl⟩ : syracuseStep 1004627 = 1506941) B1506941
theorem B1004657 : Blo 666309 1004657 := bstep (se 2 (by rfl) ⟨376746, by rfl⟩ : syracuseStep 1004657 = 753493) B753493
theorem B1004675 : Blo 666309 1004675 := bstep (se 1 (by rfl) ⟨753506, by rfl⟩ : syracuseStep 1004675 = 1507013) B1507013
theorem B1004705 : Blo 666309 1004705 := bstep (se 2 (by rfl) ⟨376764, by rfl⟩ : syracuseStep 1004705 = 753529) B753529
theorem B2544803 : Blo 666309 2544803 := bstep (se 1 (by rfl) ⟨1908602, by rfl⟩ : syracuseStep 2544803 = 3817205) B3817205
theorem B2413745 : Blo 666309 2413745 := bstep (se 2 (by rfl) ⟨905154, by rfl⟩ : syracuseStep 2413745 = 1810309) B1810309
theorem B2544817 : Blo 666309 2544817 := bstep (se 2 (by rfl) ⟨954306, by rfl⟩ : syracuseStep 2544817 = 1908613) B1908613
theorem B1004723 : Blo 666309 1004723 := bstep (se 1 (by rfl) ⟨753542, by rfl⟩ : syracuseStep 1004723 = 1507085) B1507085
theorem B1004753 : Blo 666309 1004753 := bstep (se 2 (by rfl) ⟨376782, by rfl⟩ : syracuseStep 1004753 = 753565) B753565
theorem B1004771 : Blo 666309 1004771 := bstep (se 1 (by rfl) ⟨753578, by rfl⟩ : syracuseStep 1004771 = 1507157) B1507157
theorem B1004801 : Blo 666309 1004801 := bstep (se 2 (by rfl) ⟨376800, by rfl⟩ : syracuseStep 1004801 = 753601) B753601
theorem B1004819 : Blo 666309 1004819 := bstep (se 1 (by rfl) ⟨753614, by rfl⟩ : syracuseStep 1004819 = 1507229) B1507229
theorem B1004849 : Blo 666309 1004849 := bstep (se 2 (by rfl) ⟨376818, by rfl⟩ : syracuseStep 1004849 = 753637) B753637
theorem B1004867 : Blo 666309 1004867 := bstep (se 1 (by rfl) ⟨753650, by rfl⟩ : syracuseStep 1004867 = 1507301) B1507301
theorem B1004897 : Blo 666309 1004897 := bstep (se 2 (by rfl) ⟨376836, by rfl⟩ : syracuseStep 1004897 = 753673) B753673
theorem B1004915 : Blo 666309 1004915 := bstep (se 1 (by rfl) ⟨753686, by rfl⟩ : syracuseStep 1004915 = 1507373) B1507373
theorem B2250125 : Blo 666309 2250125 := bstep (se 3 (by rfl) ⟨421898, by rfl⟩ : syracuseStep 2250125 = 843797) B843797
theorem B5133709 : Blo 666309 5133709 := bstep (se 3 (by rfl) ⟨962570, by rfl⟩ : syracuseStep 5133709 = 1925141) B1925141
theorem B1004945 : Blo 666309 1004945 := bstep (se 2 (by rfl) ⟨376854, by rfl⟩ : syracuseStep 1004945 = 753709) B753709
theorem B1004963 : Blo 666309 1004963 := bstep (se 1 (by rfl) ⟨753722, by rfl⟩ : syracuseStep 1004963 = 1507445) B1507445
theorem B1004993 : Blo 666309 1004993 := bstep (se 2 (by rfl) ⟨376872, by rfl⟩ : syracuseStep 1004993 = 753745) B753745
theorem B2250179 : Blo 666309 2250179 := bstep (se 1 (by rfl) ⟨1687634, by rfl⟩ : syracuseStep 2250179 = 3375269) B3375269
theorem B1267139 : Blo 666309 1267139 := bstep (se 1 (by rfl) ⟨950354, by rfl⟩ : syracuseStep 1267139 = 1900709) B1900709
theorem B1005011 : Blo 666309 1005011 := bstep (se 1 (by rfl) ⟨753758, by rfl⟩ : syracuseStep 1005011 = 1507517) B1507517
theorem B6084067 : Blo 666309 6084067 := bstep (se 1 (by rfl) ⟨4563050, by rfl⟩ : syracuseStep 6084067 = 9126101) B9126101
theorem B1005041 : Blo 666309 1005041 := bstep (se 2 (by rfl) ⟨376890, by rfl⟩ : syracuseStep 1005041 = 753781) B753781
theorem B1005059 : Blo 666309 1005059 := bstep (se 1 (by rfl) ⟨753794, by rfl⟩ : syracuseStep 1005059 = 1507589) B1507589
theorem B1005089 : Blo 666309 1005089 := bstep (se 2 (by rfl) ⟨376908, by rfl⟩ : syracuseStep 1005089 = 753817) B753817
theorem B1005107 : Blo 666309 1005107 := bstep (se 1 (by rfl) ⟨753830, by rfl⟩ : syracuseStep 1005107 = 1507661) B1507661
theorem B1005137 : Blo 666309 1005137 := bstep (se 2 (by rfl) ⟨376926, by rfl⟩ : syracuseStep 1005137 = 753853) B753853
theorem B1005155 : Blo 666309 1005155 := bstep (se 1 (by rfl) ⟨753866, by rfl⟩ : syracuseStep 1005155 = 1507733) B1507733
theorem B1005185 : Blo 666309 1005185 := bstep (se 2 (by rfl) ⟨376944, by rfl⟩ : syracuseStep 1005185 = 753889) B753889
theorem B1005203 : Blo 666309 1005203 := bstep (se 1 (by rfl) ⟨753902, by rfl⟩ : syracuseStep 1005203 = 1507805) B1507805
theorem B1005233 : Blo 666309 1005233 := bstep (se 2 (by rfl) ⟨376962, by rfl⟩ : syracuseStep 1005233 = 753925) B753925
theorem B1005251 : Blo 666309 1005251 := bstep (se 1 (by rfl) ⟨753938, by rfl⟩ : syracuseStep 1005251 = 1507877) B1507877
theorem B2250449 : Blo 666309 2250449 := bstep (se 2 (by rfl) ⟨843918, by rfl⟩ : syracuseStep 2250449 = 1687837) B1687837
theorem B1005281 : Blo 666309 1005281 := bstep (se 2 (by rfl) ⟨376980, by rfl⟩ : syracuseStep 1005281 = 753961) B753961
theorem B1267427 : Blo 666309 1267427 := bstep (se 1 (by rfl) ⟨950570, by rfl⟩ : syracuseStep 1267427 = 1901141) B1901141
theorem B1005299 : Blo 666309 1005299 := bstep (se 1 (by rfl) ⟨753974, by rfl⟩ : syracuseStep 1005299 = 1507949) B1507949
theorem B1693457 : Blo 666309 1693457 := bstep (se 2 (by rfl) ⟨635046, by rfl⟩ : syracuseStep 1693457 = 1270093) B1270093
theorem B1005329 : Blo 666309 1005329 := bstep (se 2 (by rfl) ⟨376998, by rfl⟩ : syracuseStep 1005329 = 753997) B753997
theorem B1005347 : Blo 666309 1005347 := bstep (se 1 (by rfl) ⟨754010, by rfl⟩ : syracuseStep 1005347 = 1508021) B1508021
theorem B1005377 : Blo 666309 1005377 := bstep (se 2 (by rfl) ⟨377016, by rfl⟩ : syracuseStep 1005377 = 754033) B754033
theorem B1693507 : Blo 666309 1693507 := bstep (se 1 (by rfl) ⟨1270130, by rfl⟩ : syracuseStep 1693507 = 2540261) B2540261
theorem B1005395 : Blo 666309 1005395 := bstep (se 1 (by rfl) ⟨754046, by rfl⟩ : syracuseStep 1005395 = 1508093) B1508093
theorem B10868593 : Blo 666309 10868593 := bstep (se 2 (by rfl) ⟨4075722, by rfl⟩ : syracuseStep 10868593 = 8151445) B8151445
theorem B1005425 : Blo 666309 1005425 := bstep (se 2 (by rfl) ⟨377034, by rfl⟩ : syracuseStep 1005425 = 754069) B754069
theorem B1005443 : Blo 666309 1005443 := bstep (se 1 (by rfl) ⟨754082, by rfl⟩ : syracuseStep 1005443 = 1508165) B1508165
theorem B677795 : Blo 666309 677795 := bstep (se 1 (by rfl) ⟨508346, by rfl⟩ : syracuseStep 677795 = 1016693) B1016693
theorem B8148917 : Blo 666309 8148917 := bstep (se 5 (by rfl) ⟨381980, by rfl⟩ : syracuseStep 8148917 = 763961) B763961
theorem B1693649 : Blo 666309 1693649 := bstep (se 2 (by rfl) ⟨635118, by rfl⟩ : syracuseStep 1693649 = 1270237) B1270237
theorem B2250989 : Blo 666309 2250989 := bstep (se 3 (by rfl) ⟨422060, by rfl⟩ : syracuseStep 2250989 = 844121) B844121
theorem B2251043 : Blo 666309 2251043 := bstep (se 1 (by rfl) ⟨1688282, by rfl⟩ : syracuseStep 2251043 = 3376565) B3376565
theorem B1071443 : Blo 666309 1071443 := bstep (se 1 (by rfl) ⟨803582, by rfl⟩ : syracuseStep 1071443 = 1607165) B1607165
theorem B8673733 : Blo 666309 8673733 := bstep (se 4 (by rfl) ⟨813162, by rfl⟩ : syracuseStep 8673733 = 1626325) B1626325
theorem B1071571 : Blo 666309 1071571 := bstep (se 1 (by rfl) ⟨803678, by rfl⟩ : syracuseStep 1071571 = 1607357) B1607357
theorem B2251313 : Blo 666309 2251313 := bstep (se 2 (by rfl) ⟨844242, by rfl⟩ : syracuseStep 2251313 = 1688485) B1688485
theorem B3431011 : Blo 666309 3431011 := bstep (se 1 (by rfl) ⟨2573258, by rfl⟩ : syracuseStep 3431011 = 5146517) B5146517
theorem B1268369 : Blo 666309 1268369 := bstep (se 2 (by rfl) ⟨475638, by rfl⟩ : syracuseStep 1268369 = 951277) B951277
theorem B1071955 : Blo 666309 1071955 := bstep (se 1 (by rfl) ⟨803966, by rfl⟩ : syracuseStep 1071955 = 1607933) B1607933
theorem B1694641 : Blo 666309 1694641 := bstep (se 2 (by rfl) ⟨635490, by rfl⟩ : syracuseStep 1694641 = 1270981) B1270981
theorem B711715 : Blo 666309 711715 := bstep (se 1 (by rfl) ⟨533786, by rfl⟩ : syracuseStep 711715 = 1067573) B1067573
theorem B678947 : Blo 666309 678947 := bstep (se 1 (by rfl) ⟨509210, by rfl⟩ : syracuseStep 678947 = 1018421) B1018421
theorem B2251853 : Blo 666309 2251853 := bstep (se 3 (by rfl) ⟨422222, by rfl⟩ : syracuseStep 2251853 = 844445) B844445
theorem B1072211 : Blo 666309 1072211 := bstep (se 1 (by rfl) ⟨804158, by rfl⟩ : syracuseStep 1072211 = 1608317) B1608317
theorem B2251907 : Blo 666309 2251907 := bstep (se 1 (by rfl) ⟨1688930, by rfl⟩ : syracuseStep 2251907 = 3377861) B3377861
theorem B1694915 : Blo 666309 1694915 := bstep (se 1 (by rfl) ⟨1271186, by rfl⟩ : syracuseStep 1694915 = 2542373) B2542373
theorem B1203427 : Blo 666309 1203427 := bstep (se 1 (by rfl) ⟨902570, by rfl⟩ : syracuseStep 1203427 = 1805141) B1805141
theorem B1695107 : Blo 666309 1695107 := bstep (se 1 (by rfl) ⟨1271330, by rfl⟩ : syracuseStep 1695107 = 2542661) B2542661
theorem B2252177 : Blo 666309 2252177 := bstep (se 2 (by rfl) ⟨844566, by rfl⟩ : syracuseStep 2252177 = 1689133) B1689133
theorem B1269265 : Blo 666309 1269265 := bstep (se 2 (by rfl) ⟨475974, by rfl⟩ : syracuseStep 1269265 = 951949) B951949
theorem B1072673 : Blo 666309 1072673 := bstep (se 2 (by rfl) ⟨402252, by rfl⟩ : syracuseStep 1072673 = 804505) B804505
theorem B1072769 : Blo 666309 1072769 := bstep (se 2 (by rfl) ⟨402288, by rfl⟩ : syracuseStep 1072769 = 804577) B804577
theorem B1072801 : Blo 666309 1072801 := bstep (se 2 (by rfl) ⟨402300, by rfl⟩ : syracuseStep 1072801 = 804601) B804601
theorem B1269425 : Blo 666309 1269425 := bstep (se 2 (by rfl) ⟨476034, by rfl⟩ : syracuseStep 1269425 = 952069) B952069
theorem B8576867 : Blo 666309 8576867 := bstep (se 1 (by rfl) ⟨6432650, by rfl⟩ : syracuseStep 8576867 = 12865301) B12865301
theorem B843635 : Blo 666309 843635 := bstep (se 1 (by rfl) ⟨632726, by rfl⟩ : syracuseStep 843635 = 1265453) B1265453
theorem B712595 : Blo 666309 712595 := bstep (se 1 (by rfl) ⟨534446, by rfl⟩ : syracuseStep 712595 = 1068893) B1068893
theorem B2252717 : Blo 666309 2252717 := bstep (se 3 (by rfl) ⟨422384, by rfl⟩ : syracuseStep 2252717 = 844769) B844769
theorem B2252771 : Blo 666309 2252771 := bstep (se 1 (by rfl) ⟨1689578, by rfl⟩ : syracuseStep 2252771 = 3379157) B3379157
theorem B712723 : Blo 666309 712723 := bstep (se 1 (by rfl) ⟨534542, by rfl⟩ : syracuseStep 712723 = 1069085) B1069085
theorem B1269827 : Blo 666309 1269827 := bstep (se 1 (by rfl) ⟨952370, by rfl⟩ : syracuseStep 1269827 = 1904741) B1904741
theorem B4808803 : Blo 666309 4808803 := bstep (se 1 (by rfl) ⟨3606602, by rfl⟩ : syracuseStep 4808803 = 7213205) B7213205
theorem B4284515 : Blo 666309 4284515 := bstep (se 1 (by rfl) ⟨3213386, by rfl⟩ : syracuseStep 4284515 = 6426773) B6426773
theorem B1499345 : Blo 666309 1499345 := bstep (se 2 (by rfl) ⟨562254, by rfl⟩ : syracuseStep 1499345 = 1124509) B1124509
theorem B1499363 : Blo 666309 1499363 := bstep (se 1 (by rfl) ⟨1124522, by rfl⟩ : syracuseStep 1499363 = 2249045) B2249045
theorem B2253041 : Blo 666309 2253041 := bstep (se 2 (by rfl) ⟨844890, by rfl⟩ : syracuseStep 2253041 = 1689781) B1689781
theorem B1204465 : Blo 666309 1204465 := bstep (se 2 (by rfl) ⟨451674, by rfl⟩ : syracuseStep 1204465 = 903349) B903349
theorem B1696049 : Blo 666309 1696049 := bstep (se 2 (by rfl) ⟨636018, by rfl⟩ : syracuseStep 1696049 = 1272037) B1272037
theorem B1696099 : Blo 666309 1696099 := bstep (se 1 (by rfl) ⟨1272074, by rfl⟩ : syracuseStep 1696099 = 2544149) B2544149
theorem B975235 : Blo 666309 975235 := bstep (se 1 (by rfl) ⟨731426, by rfl⟩ : syracuseStep 975235 = 1462853) B1462853
theorem B1499633 : Blo 666309 1499633 := bstep (se 2 (by rfl) ⟨562362, by rfl⟩ : syracuseStep 1499633 = 1124725) B1124725
theorem B1696241 : Blo 666309 1696241 := bstep (se 2 (by rfl) ⟨636090, by rfl⟩ : syracuseStep 1696241 = 1272181) B1272181
theorem B1499651 : Blo 666309 1499651 := bstep (se 1 (by rfl) ⟨1124738, by rfl⟩ : syracuseStep 1499651 = 2249477) B2249477
theorem B844339 : Blo 666309 844339 := bstep (se 1 (by rfl) ⟨633254, by rfl⟩ : syracuseStep 844339 = 1266509) B1266509
theorem B844435 : Blo 666309 844435 := bstep (se 1 (by rfl) ⟨633326, by rfl⟩ : syracuseStep 844435 = 1266653) B1266653
theorem B2253581 : Blo 666309 2253581 := bstep (se 3 (by rfl) ⟨422546, by rfl⟩ : syracuseStep 2253581 = 845093) B845093
theorem B1499921 : Blo 666309 1499921 := bstep (se 2 (by rfl) ⟨562470, by rfl⟩ : syracuseStep 1499921 = 1124941) B1124941
theorem B1499939 : Blo 666309 1499939 := bstep (se 1 (by rfl) ⟨1124954, by rfl⟩ : syracuseStep 1499939 = 2249909) B2249909
theorem B2253635 : Blo 666309 2253635 := bstep (se 1 (by rfl) ⟨1690226, by rfl⟩ : syracuseStep 2253635 = 3380453) B3380453
theorem B713539 : Blo 666309 713539 := bstep (se 1 (by rfl) ⟨535154, by rfl⟩ : syracuseStep 713539 = 1070309) B1070309
theorem B9659249 : Blo 666309 9659249 := bstep (se 2 (by rfl) ⟨3622218, by rfl⟩ : syracuseStep 9659249 = 7244437) B7244437
theorem B1270723 : Blo 666309 1270723 := bstep (se 1 (by rfl) ⟨953042, by rfl⟩ : syracuseStep 1270723 = 1906085) B1906085
theorem B812035 : Blo 666309 812035 := bstep (se 1 (by rfl) ⟨609026, by rfl⟩ : syracuseStep 812035 = 1218053) B1218053
theorem B1500209 : Blo 666309 1500209 := bstep (se 2 (by rfl) ⟨562578, by rfl⟩ : syracuseStep 1500209 = 1125157) B1125157
theorem B1500227 : Blo 666309 1500227 := bstep (se 1 (by rfl) ⟨1125170, by rfl⟩ : syracuseStep 1500227 = 2250341) B2250341
theorem B2253905 : Blo 666309 2253905 := bstep (se 2 (by rfl) ⟨845214, by rfl⟩ : syracuseStep 2253905 = 1690429) B1690429
theorem B1270883 : Blo 666309 1270883 := bstep (se 1 (by rfl) ⟨953162, by rfl⟩ : syracuseStep 1270883 = 1906325) B1906325
theorem B844931 : Blo 666309 844931 := bstep (se 1 (by rfl) ⟨633698, by rfl⟩ : syracuseStep 844931 = 1267397) B1267397
theorem B1500497 : Blo 666309 1500497 := bstep (se 2 (by rfl) ⟨562686, by rfl⟩ : syracuseStep 1500497 = 1125373) B1125373
theorem B1500515 : Blo 666309 1500515 := bstep (se 1 (by rfl) ⟨1125386, by rfl⟩ : syracuseStep 1500515 = 2250773) B2250773
theorem B11429261 : Blo 666309 11429261 := bstep (se 3 (by rfl) ⟨2142986, by rfl⟩ : syracuseStep 11429261 = 4285973) B4285973
theorem B2287121 : Blo 666309 2287121 := bstep (se 2 (by rfl) ⟨857670, by rfl⟩ : syracuseStep 2287121 = 1715341) B1715341
theorem B2254445 : Blo 666309 2254445 := bstep (se 3 (by rfl) ⟨422708, by rfl⟩ : syracuseStep 2254445 = 845417) B845417
theorem B1500785 : Blo 666309 1500785 := bstep (se 2 (by rfl) ⟨562794, by rfl⟩ : syracuseStep 1500785 = 1125589) B1125589
theorem B1500803 : Blo 666309 1500803 := bstep (se 1 (by rfl) ⟨1125602, by rfl⟩ : syracuseStep 1500803 = 2251205) B2251205
theorem B2254499 : Blo 666309 2254499 := bstep (se 1 (by rfl) ⟨1690874, by rfl⟩ : syracuseStep 2254499 = 3381749) B3381749
theorem B845635 : Blo 666309 845635 := bstep (se 1 (by rfl) ⟨634226, by rfl⟩ : syracuseStep 845635 = 1268453) B1268453
theorem B1501073 : Blo 666309 1501073 := bstep (se 2 (by rfl) ⟨562902, by rfl⟩ : syracuseStep 1501073 = 1125805) B1125805
theorem B1501091 : Blo 666309 1501091 := bstep (se 1 (by rfl) ⟨1125818, by rfl⟩ : syracuseStep 1501091 = 2251637) B2251637
theorem B845731 : Blo 666309 845731 := bstep (se 1 (by rfl) ⟨634298, by rfl⟩ : syracuseStep 845731 = 1268597) B1268597
theorem B2254769 : Blo 666309 2254769 := bstep (se 2 (by rfl) ⟨845538, by rfl⟩ : syracuseStep 2254769 = 1691077) B1691077
theorem B1632209 : Blo 666309 1632209 := bstep (se 2 (by rfl) ⟨612078, by rfl⟩ : syracuseStep 1632209 = 1224157) B1224157
theorem B5072867 : Blo 666309 5072867 := bstep (se 1 (by rfl) ⟨3804650, by rfl⟩ : syracuseStep 5072867 = 7609301) B7609301
theorem B1271953 : Blo 666309 1271953 := bstep (se 2 (by rfl) ⟨476982, by rfl⟩ : syracuseStep 1271953 = 953965) B953965
theorem B1501361 : Blo 666309 1501361 := bstep (se 2 (by rfl) ⟨563010, by rfl⟩ : syracuseStep 1501361 = 1126021) B1126021
theorem B4286641 : Blo 666309 4286641 := bstep (se 2 (by rfl) ⟨1607490, by rfl⟩ : syracuseStep 4286641 = 3214981) B3214981
theorem B1501379 : Blo 666309 1501379 := bstep (se 1 (by rfl) ⟨1126034, by rfl⟩ : syracuseStep 1501379 = 2252069) B2252069
theorem B846227 : Blo 666309 846227 := bstep (se 1 (by rfl) ⟨634670, by rfl⟩ : syracuseStep 846227 = 1269341) B1269341
theorem B2255309 : Blo 666309 2255309 := bstep (se 3 (by rfl) ⟨422870, by rfl⟩ : syracuseStep 2255309 = 845741) B845741
theorem B1501649 : Blo 666309 1501649 := bstep (se 2 (by rfl) ⟨563118, by rfl⟩ : syracuseStep 1501649 = 1126237) B1126237
theorem B1501667 : Blo 666309 1501667 := bstep (se 1 (by rfl) ⟨1126250, by rfl⟩ : syracuseStep 1501667 = 2252501) B2252501
theorem B2255363 : Blo 666309 2255363 := bstep (se 1 (by rfl) ⟨1691522, by rfl⟩ : syracuseStep 2255363 = 3383045) B3383045
theorem B1043027 : Blo 666309 1043027 := bstep (se 1 (by rfl) ⟨782270, by rfl⟩ : syracuseStep 1043027 = 1564541) B1564541
theorem B1141427 : Blo 666309 1141427 := bstep (se 1 (by rfl) ⟨856070, by rfl⟩ : syracuseStep 1141427 = 1712141) B1712141
theorem B1501937 : Blo 666309 1501937 := bstep (se 2 (by rfl) ⟨563226, by rfl⟩ : syracuseStep 1501937 = 1126453) B1126453
theorem B1501955 : Blo 666309 1501955 := bstep (se 1 (by rfl) ⟨1126466, by rfl⟩ : syracuseStep 1501955 = 2252933) B2252933
theorem B2255633 : Blo 666309 2255633 := bstep (se 2 (by rfl) ⟨845862, by rfl⟩ : syracuseStep 2255633 = 1691725) B1691725
theorem B2026307 : Blo 666309 2026307 := bstep (se 1 (by rfl) ⟨1519730, by rfl⟩ : syracuseStep 2026307 = 3039461) B3039461
theorem B1502225 : Blo 666309 1502225 := bstep (se 2 (by rfl) ⟨563334, by rfl⟩ : syracuseStep 1502225 = 1126669) B1126669
theorem B1502243 : Blo 666309 1502243 := bstep (se 1 (by rfl) ⟨1126682, by rfl⟩ : syracuseStep 1502243 = 2253365) B2253365
theorem B846931 : Blo 666309 846931 := bstep (se 1 (by rfl) ⟨635198, by rfl⟩ : syracuseStep 846931 = 1270397) B1270397
theorem B847027 : Blo 666309 847027 := bstep (se 1 (by rfl) ⟨635270, by rfl⟩ : syracuseStep 847027 = 1270541) B1270541
theorem B2256173 : Blo 666309 2256173 := bstep (se 3 (by rfl) ⟨423032, by rfl⟩ : syracuseStep 2256173 = 846065) B846065
theorem B1502513 : Blo 666309 1502513 := bstep (se 2 (by rfl) ⟨563442, by rfl⟩ : syracuseStep 1502513 = 1126885) B1126885
theorem B1502531 : Blo 666309 1502531 := bstep (se 1 (by rfl) ⟨1126898, by rfl⟩ : syracuseStep 1502531 = 2253797) B2253797
theorem B2256227 : Blo 666309 2256227 := bstep (se 1 (by rfl) ⟨1692170, by rfl⟩ : syracuseStep 2256227 = 3384341) B3384341
theorem B2289091 : Blo 666309 2289091 := bstep (se 1 (by rfl) ⟨1716818, by rfl⟩ : syracuseStep 2289091 = 3433637) B3433637
theorem B7597637 : Blo 666309 7597637 := bstep (se 4 (by rfl) ⟨712278, by rfl⟩ : syracuseStep 7597637 = 1424557) B1424557
theorem B1502801 : Blo 666309 1502801 := bstep (se 2 (by rfl) ⟨563550, by rfl⟩ : syracuseStep 1502801 = 1127101) B1127101
theorem B1502819 : Blo 666309 1502819 := bstep (se 1 (by rfl) ⟨1127114, by rfl⟩ : syracuseStep 1502819 = 2254229) B2254229
theorem B2256497 : Blo 666309 2256497 := bstep (se 2 (by rfl) ⟨846186, by rfl⟩ : syracuseStep 2256497 = 1692373) B1692373
theorem B847523 : Blo 666309 847523 := bstep (se 1 (by rfl) ⟨635642, by rfl⟩ : syracuseStep 847523 = 1271285) B1271285
theorem B1503089 : Blo 666309 1503089 := bstep (se 2 (by rfl) ⟨563658, by rfl⟩ : syracuseStep 1503089 = 1127317) B1127317
theorem B1503107 : Blo 666309 1503107 := bstep (se 1 (by rfl) ⟨1127330, by rfl⟩ : syracuseStep 1503107 = 2254661) B2254661
theorem B2027501 : Blo 666309 2027501 := bstep (se 3 (by rfl) ⟨380156, by rfl⟩ : syracuseStep 2027501 = 760313) B760313
theorem B2257037 : Blo 666309 2257037 := bstep (se 3 (by rfl) ⟨423194, by rfl⟩ : syracuseStep 2257037 = 846389) B846389
theorem B1503377 : Blo 666309 1503377 := bstep (se 2 (by rfl) ⟨563766, by rfl⟩ : syracuseStep 1503377 = 1127533) B1127533
theorem B749731 : Blo 666309 749731 := bstep (se 1 (by rfl) ⟨562298, by rfl⟩ : syracuseStep 749731 = 1124597) B1124597
theorem B1503395 : Blo 666309 1503395 := bstep (se 1 (by rfl) ⟨1127546, by rfl⟩ : syracuseStep 1503395 = 2255093) B2255093
theorem B2257091 : Blo 666309 2257091 := bstep (se 1 (by rfl) ⟨1692818, by rfl⟩ : syracuseStep 2257091 = 3385637) B3385637
theorem B749875 : Blo 666309 749875 := bstep (se 1 (by rfl) ⟨562406, by rfl⟩ : syracuseStep 749875 = 1124813) B1124813
theorem B1732963 : Blo 666309 1732963 := bstep (se 1 (by rfl) ⟨1299722, by rfl⟩ : syracuseStep 1732963 = 2599445) B2599445
theorem B848227 : Blo 666309 848227 := bstep (se 1 (by rfl) ⟨636170, by rfl⟩ : syracuseStep 848227 = 1272341) B1272341
theorem B1503665 : Blo 666309 1503665 := bstep (se 2 (by rfl) ⟨563874, by rfl⟩ : syracuseStep 1503665 = 1127749) B1127749
theorem B750019 : Blo 666309 750019 := bstep (se 1 (by rfl) ⟨562514, by rfl⟩ : syracuseStep 750019 = 1125029) B1125029
theorem B1503683 : Blo 666309 1503683 := bstep (se 1 (by rfl) ⟨1127762, by rfl⟩ : syracuseStep 1503683 = 2255525) B2255525
theorem B848323 : Blo 666309 848323 := bstep (se 1 (by rfl) ⟨636242, by rfl⟩ : syracuseStep 848323 = 1272485) B1272485
theorem B2257361 : Blo 666309 2257361 := bstep (se 2 (by rfl) ⟨846510, by rfl⟩ : syracuseStep 2257361 = 1693021) B1693021
theorem B750163 : Blo 666309 750163 := bstep (se 1 (by rfl) ⟨562622, by rfl⟩ : syracuseStep 750163 = 1125245) B1125245
theorem B1503953 : Blo 666309 1503953 := bstep (se 2 (by rfl) ⟨563982, by rfl⟩ : syracuseStep 1503953 = 1127965) B1127965
theorem B750307 : Blo 666309 750307 := bstep (se 1 (by rfl) ⟨562730, by rfl⟩ : syracuseStep 750307 = 1125461) B1125461
theorem B1503971 : Blo 666309 1503971 := bstep (se 1 (by rfl) ⟨1127978, by rfl⟩ : syracuseStep 1503971 = 2255957) B2255957
theorem B73331477 : Blo 666309 73331477 := bstep (se 6 (by rfl) ⟨1718706, by rfl⟩ : syracuseStep 73331477 = 3437413) B3437413
theorem B750451 : Blo 666309 750451 := bstep (se 1 (by rfl) ⟨562838, by rfl⟩ : syracuseStep 750451 = 1125677) B1125677
theorem B2257901 : Blo 666309 2257901 := bstep (se 3 (by rfl) ⟨423356, by rfl⟩ : syracuseStep 2257901 = 846713) B846713
theorem B1504241 : Blo 666309 1504241 := bstep (se 2 (by rfl) ⟨564090, by rfl⟩ : syracuseStep 1504241 = 1128181) B1128181
theorem B750595 : Blo 666309 750595 := bstep (se 1 (by rfl) ⟨562946, by rfl⟩ : syracuseStep 750595 = 1125893) B1125893
theorem B1504259 : Blo 666309 1504259 := bstep (se 1 (by rfl) ⟨1128194, by rfl⟩ : syracuseStep 1504259 = 2256389) B2256389
theorem B2257955 : Blo 666309 2257955 := bstep (se 1 (by rfl) ⟨1693466, by rfl⟩ : syracuseStep 2257955 = 3386933) B3386933
theorem B7206029 : Blo 666309 7206029 := bstep (se 3 (by rfl) ⟨1351130, by rfl⟩ : syracuseStep 7206029 = 2702261) B2702261
theorem B750739 : Blo 666309 750739 := bstep (se 1 (by rfl) ⟨563054, by rfl⟩ : syracuseStep 750739 = 1126109) B1126109
theorem B1504529 : Blo 666309 1504529 := bstep (se 2 (by rfl) ⟨564198, by rfl⟩ : syracuseStep 1504529 = 1128397) B1128397
theorem B750883 : Blo 666309 750883 := bstep (se 1 (by rfl) ⟨563162, by rfl⟩ : syracuseStep 750883 = 1126325) B1126325
theorem B1504547 : Blo 666309 1504547 := bstep (se 1 (by rfl) ⟨1128410, by rfl⟩ : syracuseStep 1504547 = 2256821) B2256821
theorem B2258225 : Blo 666309 2258225 := bstep (se 2 (by rfl) ⟨846834, by rfl⟩ : syracuseStep 2258225 = 1693669) B1693669
theorem B914755 : Blo 666309 914755 := bstep (se 1 (by rfl) ⟨686066, by rfl⟩ : syracuseStep 914755 = 1372133) B1372133
theorem B751027 : Blo 666309 751027 := bstep (se 1 (by rfl) ⟨563270, by rfl⟩ : syracuseStep 751027 = 1126541) B1126541
theorem B1013185 : Blo 666309 1013185 := bstep (se 2 (by rfl) ⟨379944, by rfl⟩ : syracuseStep 1013185 = 759889) B759889
theorem B1504817 : Blo 666309 1504817 := bstep (se 2 (by rfl) ⟨564306, by rfl⟩ : syracuseStep 1504817 = 1128613) B1128613
theorem B751171 : Blo 666309 751171 := bstep (se 1 (by rfl) ⟨563378, by rfl⟩ : syracuseStep 751171 = 1126757) B1126757
theorem B1504835 : Blo 666309 1504835 := bstep (se 1 (by rfl) ⟨1128626, by rfl⟩ : syracuseStep 1504835 = 2257253) B2257253
theorem B751315 : Blo 666309 751315 := bstep (se 1 (by rfl) ⟨563486, by rfl⟩ : syracuseStep 751315 = 1126973) B1126973
theorem B1898225 : Blo 666309 1898225 := bstep (se 2 (by rfl) ⟨711834, by rfl⟩ : syracuseStep 1898225 = 1423669) B1423669
theorem B2258765 : Blo 666309 2258765 := bstep (se 3 (by rfl) ⟨423518, by rfl⟩ : syracuseStep 2258765 = 847037) B847037
theorem B1505105 : Blo 666309 1505105 := bstep (se 2 (by rfl) ⟨564414, by rfl⟩ : syracuseStep 1505105 = 1128829) B1128829
theorem B751459 : Blo 666309 751459 := bstep (se 1 (by rfl) ⟨563594, by rfl⟩ : syracuseStep 751459 = 1127189) B1127189
theorem B1505123 : Blo 666309 1505123 := bstep (se 1 (by rfl) ⟨1128842, by rfl⟩ : syracuseStep 1505123 = 2257685) B2257685
theorem B2258819 : Blo 666309 2258819 := bstep (se 1 (by rfl) ⟨1694114, by rfl⟩ : syracuseStep 2258819 = 3388229) B3388229
theorem B751603 : Blo 666309 751603 := bstep (se 1 (by rfl) ⟨563702, by rfl⟩ : syracuseStep 751603 = 1127405) B1127405
theorem B1505393 : Blo 666309 1505393 := bstep (se 2 (by rfl) ⟨564522, by rfl⟩ : syracuseStep 1505393 = 1129045) B1129045
theorem B751747 : Blo 666309 751747 := bstep (se 1 (by rfl) ⟨563810, by rfl⟩ : syracuseStep 751747 = 1127621) B1127621
theorem B1505411 : Blo 666309 1505411 := bstep (se 1 (by rfl) ⟨1129058, by rfl⟩ : syracuseStep 1505411 = 2258117) B2258117
theorem B2259089 : Blo 666309 2259089 := bstep (se 2 (by rfl) ⟨847158, by rfl⟩ : syracuseStep 2259089 = 1694317) B1694317
theorem B3045539 : Blo 666309 3045539 := bstep (se 1 (by rfl) ⟨2284154, by rfl⟩ : syracuseStep 3045539 = 4568309) B4568309
theorem B2291939 : Blo 666309 2291939 := bstep (se 1 (by rfl) ⟨1718954, by rfl⟩ : syracuseStep 2291939 = 3437909) B3437909
theorem B3373325 : Blo 666309 3373325 := bstep (se 3 (by rfl) ⟨632498, by rfl⟩ : syracuseStep 3373325 = 1264997) B1264997
theorem B751891 : Blo 666309 751891 := bstep (se 1 (by rfl) ⟨563918, by rfl⟩ : syracuseStep 751891 = 1127837) B1127837
theorem B9632141 : Blo 666309 9632141 := bstep (se 3 (by rfl) ⟨1806026, by rfl⟩ : syracuseStep 9632141 = 3612053) B3612053
theorem B1505681 : Blo 666309 1505681 := bstep (se 2 (by rfl) ⟨564630, by rfl⟩ : syracuseStep 1505681 = 1129261) B1129261
theorem B752035 : Blo 666309 752035 := bstep (se 1 (by rfl) ⟨564026, by rfl⟩ : syracuseStep 752035 = 1128053) B1128053
theorem B1505699 : Blo 666309 1505699 := bstep (se 1 (by rfl) ⟨1129274, by rfl⟩ : syracuseStep 1505699 = 2258549) B2258549
theorem B2849251 : Blo 666309 2849251 := bstep (se 1 (by rfl) ⟨2136938, by rfl⟩ : syracuseStep 2849251 = 4273877) B4273877
theorem B752179 : Blo 666309 752179 := bstep (se 1 (by rfl) ⟨564134, by rfl⟩ : syracuseStep 752179 = 1128269) B1128269
theorem B1014401 : Blo 666309 1014401 := bstep (se 2 (by rfl) ⟨380400, by rfl⟩ : syracuseStep 1014401 = 760801) B760801
theorem B2259629 : Blo 666309 2259629 := bstep (se 3 (by rfl) ⟨423680, by rfl⟩ : syracuseStep 2259629 = 847361) B847361
theorem B1505969 : Blo 666309 1505969 := bstep (se 2 (by rfl) ⟨564738, by rfl⟩ : syracuseStep 1505969 = 1129477) B1129477
theorem B752323 : Blo 666309 752323 := bstep (se 1 (by rfl) ⟨564242, by rfl⟩ : syracuseStep 752323 = 1128485) B1128485
theorem B1505987 : Blo 666309 1505987 := bstep (se 1 (by rfl) ⟨1129490, by rfl⟩ : syracuseStep 1505987 = 2258981) B2258981
theorem B2259683 : Blo 666309 2259683 := bstep (se 1 (by rfl) ⟨1694762, by rfl⟩ : syracuseStep 2259683 = 3389525) B3389525
theorem B1604387 : Blo 666309 1604387 := bstep (se 1 (by rfl) ⟨1203290, by rfl⟩ : syracuseStep 1604387 = 2406581) B2406581
theorem B752467 : Blo 666309 752467 := bstep (se 1 (by rfl) ⟨564350, by rfl⟩ : syracuseStep 752467 = 1128701) B1128701
theorem B949153 : Blo 666309 949153 := bstep (se 2 (by rfl) ⟨355932, by rfl⟩ : syracuseStep 949153 = 711865) B711865
theorem B1506257 : Blo 666309 1506257 := bstep (se 2 (by rfl) ⟨564846, by rfl⟩ : syracuseStep 1506257 = 1129693) B1129693
theorem B752611 : Blo 666309 752611 := bstep (se 1 (by rfl) ⟨564458, by rfl⟩ : syracuseStep 752611 = 1128917) B1128917
theorem B1506275 : Blo 666309 1506275 := bstep (se 1 (by rfl) ⟨1129706, by rfl⟩ : syracuseStep 1506275 = 2259413) B2259413
theorem B2259953 : Blo 666309 2259953 := bstep (se 2 (by rfl) ⟨847482, by rfl⟩ : syracuseStep 2259953 = 1694965) B1694965
theorem B949249 : Blo 666309 949249 := bstep (se 2 (by rfl) ⟨355968, by rfl⟩ : syracuseStep 949249 = 711937) B711937
theorem B3800141 : Blo 666309 3800141 := bstep (se 3 (by rfl) ⟨712526, by rfl⟩ : syracuseStep 3800141 = 1425053) B1425053
theorem B752755 : Blo 666309 752755 := bstep (se 1 (by rfl) ⟨564566, by rfl⟩ : syracuseStep 752755 = 1129133) B1129133
theorem B1899683 : Blo 666309 1899683 := bstep (se 1 (by rfl) ⟨1424762, by rfl⟩ : syracuseStep 1899683 = 2849525) B2849525
theorem B7699637 : Blo 666309 7699637 := bstep (se 5 (by rfl) ⟨360920, by rfl⟩ : syracuseStep 7699637 = 721841) B721841
theorem B5078213 : Blo 666309 5078213 := bstep (se 4 (by rfl) ⟨476082, by rfl⟩ : syracuseStep 5078213 = 952165) B952165
theorem B1506545 : Blo 666309 1506545 := bstep (se 2 (by rfl) ⟨564954, by rfl⟩ : syracuseStep 1506545 = 1129909) B1129909
theorem B752899 : Blo 666309 752899 := bstep (se 1 (by rfl) ⟨564674, by rfl⟩ : syracuseStep 752899 = 1129349) B1129349
theorem B1506563 : Blo 666309 1506563 := bstep (se 1 (by rfl) ⟨1129922, by rfl⟩ : syracuseStep 1506563 = 2259845) B2259845
theorem B4291973 : Blo 666309 4291973 := bstep (se 4 (by rfl) ⟨402372, by rfl⟩ : syracuseStep 4291973 = 804745) B804745
theorem B3210637 : Blo 666309 3210637 := bstep (se 3 (by rfl) ⟨601994, by rfl⟩ : syracuseStep 3210637 = 1203989) B1203989
theorem B753043 : Blo 666309 753043 := bstep (se 1 (by rfl) ⟨564782, by rfl⟩ : syracuseStep 753043 = 1129565) B1129565
theorem B949745 : Blo 666309 949745 := bstep (se 2 (by rfl) ⟨356154, by rfl⟩ : syracuseStep 949745 = 712309) B712309
theorem B2260493 : Blo 666309 2260493 := bstep (se 3 (by rfl) ⟨423842, by rfl⟩ : syracuseStep 2260493 = 847685) B847685
theorem B1801745 : Blo 666309 1801745 := bstep (se 2 (by rfl) ⟨675654, by rfl⟩ : syracuseStep 1801745 = 1351309) B1351309
theorem B1506833 : Blo 666309 1506833 := bstep (se 2 (by rfl) ⟨565062, by rfl⟩ : syracuseStep 1506833 = 1130125) B1130125
theorem B753187 : Blo 666309 753187 := bstep (se 1 (by rfl) ⟨564890, by rfl⟩ : syracuseStep 753187 = 1129781) B1129781
theorem B1506851 : Blo 666309 1506851 := bstep (se 1 (by rfl) ⟨1130138, by rfl⟩ : syracuseStep 1506851 = 2260277) B2260277
theorem B2260547 : Blo 666309 2260547 := bstep (se 1 (by rfl) ⟨1695410, by rfl⟩ : syracuseStep 2260547 = 3390821) B3390821
theorem B2031245 : Blo 666309 2031245 := bstep (se 3 (by rfl) ⟨380858, by rfl⟩ : syracuseStep 2031245 = 761717) B761717
theorem B2850481 : Blo 666309 2850481 := bstep (se 2 (by rfl) ⟨1068930, by rfl⟩ : syracuseStep 2850481 = 2137861) B2137861
theorem B753331 : Blo 666309 753331 := bstep (se 1 (by rfl) ⟨564998, by rfl⟩ : syracuseStep 753331 = 1129997) B1129997
theorem B1507121 : Blo 666309 1507121 := bstep (se 2 (by rfl) ⟨565170, by rfl⟩ : syracuseStep 1507121 = 1130341) B1130341
theorem B753475 : Blo 666309 753475 := bstep (se 1 (by rfl) ⟨565106, by rfl⟩ : syracuseStep 753475 = 1130213) B1130213
theorem B1507139 : Blo 666309 1507139 := bstep (se 1 (by rfl) ⟨1130354, by rfl⟩ : syracuseStep 1507139 = 2260709) B2260709
theorem B2260817 : Blo 666309 2260817 := bstep (se 2 (by rfl) ⟨847806, by rfl⟩ : syracuseStep 2260817 = 1695613) B1695613
theorem B3604337 : Blo 666309 3604337 := bstep (se 2 (by rfl) ⟨1351626, by rfl⟩ : syracuseStep 3604337 = 2703253) B2703253
theorem B1900493 : Blo 666309 1900493 := bstep (se 3 (by rfl) ⟨356342, by rfl⟩ : syracuseStep 1900493 = 712685) B712685
theorem B753619 : Blo 666309 753619 := bstep (se 1 (by rfl) ⟨565214, by rfl⟩ : syracuseStep 753619 = 1130429) B1130429
theorem B3211235 : Blo 666309 3211235 := bstep (se 1 (by rfl) ⟨2408426, by rfl⟩ : syracuseStep 3211235 = 4816853) B4816853
theorem B950297 : Blo 666309 950297 := bstep (se 2 (by rfl) ⟨356361, by rfl⟩ : syracuseStep 950297 = 712723) B712723
theorem B950411 : Blo 666309 950411 := bstep (se 1 (by rfl) ⟨712808, by rfl⟩ : syracuseStep 950411 = 1425617) B1425617
theorem B1507481 : Blo 666309 1507481 := bstep (se 2 (by rfl) ⟨565305, by rfl⟩ : syracuseStep 1507481 = 1130611) B1130611
theorem B753835 : Blo 666309 753835 := bstep (se 1 (by rfl) ⟨565376, by rfl⟩ : syracuseStep 753835 = 1130753) B1130753
theorem B2261195 : Blo 666309 2261195 := bstep (se 1 (by rfl) ⟨1695896, by rfl⟩ : syracuseStep 2261195 = 3391793) B3391793
theorem B1507571 : Blo 666309 1507571 := bstep (se 1 (by rfl) ⟨1130678, by rfl⟩ : syracuseStep 1507571 = 2261357) B2261357
theorem B1507607 : Blo 666309 1507607 := bstep (se 1 (by rfl) ⟨1130705, by rfl⟩ : syracuseStep 1507607 = 2261411) B2261411
theorem B753943 : Blo 666309 753943 := bstep (se 1 (by rfl) ⟨565457, by rfl⟩ : syracuseStep 753943 = 1130915) B1130915
theorem B1605953 : Blo 666309 1605953 := bstep (se 2 (by rfl) ⟨602232, by rfl⟩ : syracuseStep 1605953 = 1204465) B1204465
theorem B1507787 : Blo 666309 1507787 := bstep (se 1 (by rfl) ⟨1130840, by rfl⟩ : syracuseStep 1507787 = 2261681) B2261681
theorem B2261465 : Blo 666309 2261465 := bstep (se 2 (by rfl) ⟨848049, by rfl⟩ : syracuseStep 2261465 = 1696099) B1696099
theorem B1507841 : Blo 666309 1507841 := bstep (se 2 (by rfl) ⟨565440, by rfl⟩ : syracuseStep 1507841 = 1130881) B1130881
theorem B1081931 : Blo 666309 1081931 := bstep (se 1 (by rfl) ⟨811448, by rfl⟩ : syracuseStep 1081931 = 1622897) B1622897
theorem B3605093 : Blo 666309 3605093 := bstep (se 4 (by rfl) ⟨337977, by rfl⟩ : syracuseStep 3605093 = 675955) B675955
theorem B950935 : Blo 666309 950935 := bstep (se 1 (by rfl) ⟨713201, by rfl⟩ : syracuseStep 950935 = 1426403) B1426403
theorem B1508057 : Blo 666309 1508057 := bstep (se 2 (by rfl) ⟨565521, by rfl⟩ : syracuseStep 1508057 = 1131043) B1131043
theorem B3375917 : Blo 666309 3375917 := bstep (se 3 (by rfl) ⟨632984, by rfl⟩ : syracuseStep 3375917 = 1265969) B1265969
theorem B1508147 : Blo 666309 1508147 := bstep (se 1 (by rfl) ⟨1131110, by rfl⟩ : syracuseStep 1508147 = 2262221) B2262221
theorem B9634625 : Blo 666309 9634625 := bstep (se 2 (by rfl) ⟨3612984, by rfl⟩ : syracuseStep 9634625 = 7225969) B7225969
theorem B1508183 : Blo 666309 1508183 := bstep (se 1 (by rfl) ⟨1131137, by rfl⟩ : syracuseStep 1508183 = 2262275) B2262275
theorem B5080157 : Blo 666309 5080157 := bstep (se 3 (by rfl) ⟨952529, by rfl⟩ : syracuseStep 5080157 = 1905059) B1905059
theorem B2851985 : Blo 666309 2851985 := bstep (se 2 (by rfl) ⟨1069494, by rfl⟩ : syracuseStep 2851985 = 2138989) B2138989
theorem B2262167 : Blo 666309 2262167 := bstep (se 1 (by rfl) ⟨1696625, by rfl⟩ : syracuseStep 2262167 = 3393251) B3393251
theorem B4064435 : Blo 666309 4064435 := bstep (se 1 (by rfl) ⟨3048326, by rfl⟩ : syracuseStep 4064435 = 6096653) B6096653
theorem B5637325 : Blo 666309 5637325 := bstep (se 3 (by rfl) ⟨1056998, by rfl⟩ : syracuseStep 5637325 = 2113997) B2113997
theorem B951755 : Blo 666309 951755 := bstep (se 1 (by rfl) ⟨713816, by rfl⟩ : syracuseStep 951755 = 1427633) B1427633
theorem B1803865 : Blo 666309 1803865 := bstep (se 2 (by rfl) ⟨676449, by rfl⟩ : syracuseStep 1803865 = 1352899) B1352899
theorem B2033483 : Blo 666309 2033483 := bstep (se 1 (by rfl) ⟨1525112, by rfl⟩ : syracuseStep 2033483 = 3050225) B3050225
theorem B4818781 : Blo 666309 4818781 := bstep (se 3 (by rfl) ⟨903521, by rfl⟩ : syracuseStep 4818781 = 1807043) B1807043
theorem B2197441 : Blo 666309 2197441 := bstep (se 2 (by rfl) ⟨824040, by rfl⟩ : syracuseStep 2197441 = 1648081) B1648081
theorem B5802029 : Blo 666309 5802029 := bstep (se 3 (by rfl) ⟨1087880, by rfl⟩ : syracuseStep 5802029 = 2175761) B2175761
theorem B6195491 : Blo 666309 6195491 := bstep (se 1 (by rfl) ⟨4646618, by rfl⟩ : syracuseStep 6195491 = 9293237) B9293237
theorem B2853251 : Blo 666309 2853251 := bstep (se 1 (by rfl) ⟨2139938, by rfl⟩ : syracuseStep 2853251 = 4279877) B4279877
theorem B1903169 : Blo 666309 1903169 := bstep (se 2 (by rfl) ⟨713688, by rfl⟩ : syracuseStep 1903169 = 1427377) B1427377
theorem B2034251 : Blo 666309 2034251 := bstep (se 1 (by rfl) ⟨1525688, by rfl⟩ : syracuseStep 2034251 = 3051377) B3051377
theorem B1903283 : Blo 666309 1903283 := bstep (se 1 (by rfl) ⟨1427462, by rfl⟩ : syracuseStep 1903283 = 2854925) B2854925
theorem B3804083 : Blo 666309 3804083 := bstep (se 1 (by rfl) ⟨2853062, by rfl⟩ : syracuseStep 3804083 = 5706125) B5706125
theorem B1444825 : Blo 666309 1444825 := bstep (se 2 (by rfl) ⟨541809, by rfl⟩ : syracuseStep 1444825 = 1083619) B1083619
theorem B36637717 : Blo 666309 36637717 := bstep (se 6 (by rfl) ⟨858696, by rfl⟩ : syracuseStep 36637717 = 1717393) B1717393
theorem B953623 : Blo 666309 953623 := bstep (se 1 (by rfl) ⟨715217, by rfl⟩ : syracuseStep 953623 = 1430435) B1430435
theorem B1609163 : Blo 666309 1609163 := bstep (se 1 (by rfl) ⟨1206872, by rfl⟩ : syracuseStep 1609163 = 2413745) B2413745
theorem B2035649 : Blo 666309 2035649 := bstep (se 2 (by rfl) ⟨763368, by rfl⟩ : syracuseStep 2035649 = 1526737) B1526737
theorem B6098989 : Blo 666309 6098989 := bstep (se 3 (by rfl) ⟨1143560, by rfl⟩ : syracuseStep 6098989 = 2287121) B2287121
theorem B3805541 : Blo 666309 3805541 := bstep (se 4 (by rfl) ⟨356769, by rfl⟩ : syracuseStep 3805541 = 713539) B713539
theorem B3052121 : Blo 666309 3052121 := bstep (se 2 (by rfl) ⟨1144545, by rfl⟩ : syracuseStep 3052121 = 2289091) B2289091
theorem B3379805 : Blo 666309 3379805 := bstep (se 3 (by rfl) ⟨633713, by rfl⟩ : syracuseStep 3379805 = 1267427) B1267427
theorem B4067941 : Blo 666309 4067941 := bstep (se 4 (by rfl) ⟨381369, by rfl⟩ : syracuseStep 4067941 = 762739) B762739
theorem B5575601 : Blo 666309 5575601 := bstep (se 2 (by rfl) ⟨2090850, by rfl⟩ : syracuseStep 5575601 = 4181701) B4181701
theorem B1446835 : Blo 666309 1446835 := bstep (se 1 (by rfl) ⟨1085126, by rfl⟩ : syracuseStep 1446835 = 2170253) B2170253
theorem B1807453 : Blo 666309 1807453 := bstep (se 3 (by rfl) ⟨338897, by rfl⟩ : syracuseStep 1807453 = 677795) B677795
theorem B4560229 : Blo 666309 4560229 := bstep (se 4 (by rfl) ⟨427521, by rfl⟩ : syracuseStep 4560229 = 855043) B855043
theorem B4330853 : Blo 666309 4330853 := bstep (se 4 (by rfl) ⟨406017, by rfl⟩ : syracuseStep 4330853 = 812035) B812035
theorem B2856343 : Blo 666309 2856343 := bstep (se 1 (by rfl) ⟨2142257, by rfl⟩ : syracuseStep 2856343 = 4284515) B4284515
theorem B1906199 : Blo 666309 1906199 := bstep (se 1 (by rfl) ⟨1429649, by rfl⟩ : syracuseStep 1906199 = 2859299) B2859299
theorem B7607843 : Blo 666309 7607843 := bstep (se 1 (by rfl) ⟨5705882, by rfl⟩ : syracuseStep 7607843 = 11411765) B11411765
theorem B3610669 : Blo 666309 3610669 := bstep (se 3 (by rfl) ⟨677000, by rfl⟩ : syracuseStep 3610669 = 1354001) B1354001
theorem B3381911 : Blo 666309 3381911 := bstep (se 1 (by rfl) ⟨2536433, by rfl⟩ : syracuseStep 3381911 = 5072867) B5072867
theorem B695351 : Blo 666309 695351 := bstep (se 1 (by rfl) ⟨521513, by rfl⟩ : syracuseStep 695351 = 1043027) B1043027
theorem B1219673 : Blo 666309 1219673 := bstep (se 2 (by rfl) ⟨457377, by rfl⟩ : syracuseStep 1219673 = 914755) B914755
theorem B760951 : Blo 666309 760951 := bstep (se 1 (by rfl) ⟨570713, by rfl⟩ : syracuseStep 760951 = 1141427) B1141427
theorem B1350913 : Blo 666309 1350913 := bstep (se 2 (by rfl) ⟨506592, by rfl⟩ : syracuseStep 1350913 = 1013185) B1013185
theorem B14491457 : Blo 666309 14491457 := bstep (se 2 (by rfl) ⟨5434296, by rfl⟩ : syracuseStep 14491457 = 10868593) B10868593
theorem B1908659 : Blo 666309 1908659 := bstep (se 1 (by rfl) ⟨1431494, by rfl⟩ : syracuseStep 1908659 = 2862989) B2862989
theorem B1351667 : Blo 666309 1351667 := bstep (se 1 (by rfl) ⟨1013750, by rfl⟩ : syracuseStep 1351667 = 2027501) B2027501
theorem B1810525 : Blo 666309 1810525 := bstep (se 3 (by rfl) ⟨339473, by rfl⟩ : syracuseStep 1810525 = 678947) B678947
theorem B2859229 : Blo 666309 2859229 := bstep (se 3 (by rfl) ⟨536105, by rfl⟩ : syracuseStep 2859229 = 1072211) B1072211
theorem B1286401 : Blo 666309 1286401 := bstep (se 2 (by rfl) ⟨482400, by rfl⟩ : syracuseStep 1286401 = 964801) B964801
theorem B12329489 : Blo 666309 12329489 := bstep (se 2 (by rfl) ⟨4623558, by rfl⟩ : syracuseStep 12329489 = 9247117) B9247117
theorem B2860049 : Blo 666309 2860049 := bstep (se 2 (by rfl) ⟨1072518, by rfl⟩ : syracuseStep 2860049 = 2145037) B2145037
theorem B3220555 : Blo 666309 3220555 := bstep (se 1 (by rfl) ⟨2415416, by rfl⟩ : syracuseStep 3220555 = 4830833) B4830833
theorem B2532653 : Blo 666309 2532653 := bstep (se 3 (by rfl) ⟨474872, by rfl⟩ : syracuseStep 2532653 = 949745) B949745
theorem B2893121 : Blo 666309 2893121 := bstep (se 2 (by rfl) ⟨1084920, by rfl⟩ : syracuseStep 2893121 = 2169841) B2169841
theorem B43394453 : Blo 666309 43394453 := bstep (se 6 (by rfl) ⟨1017057, by rfl⟩ : syracuseStep 43394453 = 2034115) B2034115
theorem B2860717 : Blo 666309 2860717 := bstep (se 3 (by rfl) ⟨536384, by rfl⟩ : syracuseStep 2860717 = 1072769) B1072769
theorem B2827997 : Blo 666309 2827997 := bstep (se 3 (by rfl) ⟨530249, by rfl⟩ : syracuseStep 2827997 = 1060499) B1060499
theorem B3811373 : Blo 666309 3811373 := bstep (se 3 (by rfl) ⟨714632, by rfl⟩ : syracuseStep 3811373 = 1429265) B1429265
theorem B2533427 : Blo 666309 2533427 := bstep (se 1 (by rfl) ⟨1900070, by rfl⟩ : syracuseStep 2533427 = 3800141) B3800141
theorem B3385475 : Blo 666309 3385475 := bstep (se 1 (by rfl) ⟨2539106, by rfl⟩ : syracuseStep 3385475 = 5078213) B5078213
theorem B17410229 : Blo 666309 17410229 := bstep (se 5 (by rfl) ⟨816104, by rfl⟩ : syracuseStep 17410229 = 1632209) B1632209
theorem B2861315 : Blo 666309 2861315 := bstep (se 1 (by rfl) ⟨2145986, by rfl⟩ : syracuseStep 2861315 = 4291973) B4291973
theorem B1124759 : Blo 666309 1124759 := bstep (se 1 (by rfl) ⟨843569, by rfl⟩ : syracuseStep 1124759 = 1687139) B1687139
theorem B1354163 : Blo 666309 1354163 := bstep (se 1 (by rfl) ⟨1015622, by rfl⟩ : syracuseStep 1354163 = 2031245) B2031245
theorem B1124887 : Blo 666309 1124887 := bstep (se 1 (by rfl) ⟨843665, by rfl⟩ : syracuseStep 1124887 = 1687331) B1687331
theorem B2402891 : Blo 666309 2402891 := bstep (se 1 (by rfl) ⟨1802168, by rfl⟩ : syracuseStep 2402891 = 3604337) B3604337
theorem B2140823 : Blo 666309 2140823 := bstep (se 1 (by rfl) ⟨1605617, by rfl⟩ : syracuseStep 2140823 = 3211235) B3211235
theorem B666315 : Blo 666309 666315 := bstep (se 1 (by rfl) ⟨499736, by rfl⟩ : syracuseStep 666315 = 999473) B999473
theorem B666327 : Blo 666309 666327 := bstep (se 1 (by rfl) ⟨499745, by rfl⟩ : syracuseStep 666327 = 999491) B999491
theorem B666347 : Blo 666309 666347 := bstep (se 1 (by rfl) ⟨499760, by rfl⟩ : syracuseStep 666347 = 999521) B999521
theorem B666359 : Blo 666309 666359 := bstep (se 1 (by rfl) ⟨499769, by rfl⟩ : syracuseStep 666359 = 999539) B999539
theorem B666379 : Blo 666309 666379 := bstep (se 1 (by rfl) ⟨499784, by rfl⟩ : syracuseStep 666379 = 999569) B999569
theorem B666391 : Blo 666309 666391 := bstep (se 1 (by rfl) ⟨499793, by rfl⟩ : syracuseStep 666391 = 999587) B999587
theorem B666411 : Blo 666309 666411 := bstep (se 1 (by rfl) ⟨499808, by rfl⟩ : syracuseStep 666411 = 999617) B999617
theorem B666423 : Blo 666309 666423 := bstep (se 1 (by rfl) ⟨499817, by rfl⟩ : syracuseStep 666423 = 999635) B999635
theorem B666443 : Blo 666309 666443 := bstep (se 1 (by rfl) ⟨499832, by rfl⟩ : syracuseStep 666443 = 999665) B999665
theorem B666455 : Blo 666309 666455 := bstep (se 1 (by rfl) ⟨499841, by rfl⟩ : syracuseStep 666455 = 999683) B999683
theorem B666475 : Blo 666309 666475 := bstep (se 1 (by rfl) ⟨499856, by rfl⟩ : syracuseStep 666475 = 999713) B999713
theorem B666487 : Blo 666309 666487 := bstep (se 1 (by rfl) ⟨499865, by rfl⟩ : syracuseStep 666487 = 999731) B999731
theorem B666507 : Blo 666309 666507 := bstep (se 1 (by rfl) ⟨499880, by rfl⟩ : syracuseStep 666507 = 999761) B999761
theorem B666519 : Blo 666309 666519 := bstep (se 1 (by rfl) ⟨499889, by rfl⟩ : syracuseStep 666519 = 999779) B999779
theorem B666539 : Blo 666309 666539 := bstep (se 1 (by rfl) ⟨499904, by rfl⟩ : syracuseStep 666539 = 999809) B999809
theorem B666551 : Blo 666309 666551 := bstep (se 1 (by rfl) ⟨499913, by rfl⟩ : syracuseStep 666551 = 999827) B999827
theorem B666571 : Blo 666309 666571 := bstep (se 1 (by rfl) ⟨499928, by rfl⟩ : syracuseStep 666571 = 999857) B999857
theorem B666583 : Blo 666309 666583 := bstep (se 1 (by rfl) ⟨499937, by rfl⟩ : syracuseStep 666583 = 999875) B999875
theorem B666603 : Blo 666309 666603 := bstep (se 1 (by rfl) ⟨499952, by rfl⟩ : syracuseStep 666603 = 999905) B999905
theorem B666615 : Blo 666309 666615 := bstep (se 1 (by rfl) ⟨499961, by rfl⟩ : syracuseStep 666615 = 999923) B999923
theorem B666635 : Blo 666309 666635 := bstep (se 1 (by rfl) ⟨499976, by rfl⟩ : syracuseStep 666635 = 999953) B999953
theorem B666647 : Blo 666309 666647 := bstep (se 1 (by rfl) ⟨499985, by rfl⟩ : syracuseStep 666647 = 999971) B999971
theorem B666667 : Blo 666309 666667 := bstep (se 1 (by rfl) ⟨500000, by rfl⟩ : syracuseStep 666667 = 1000001) B1000001
theorem B666679 : Blo 666309 666679 := bstep (se 1 (by rfl) ⟨500009, by rfl⟩ : syracuseStep 666679 = 1000019) B1000019
theorem B666699 : Blo 666309 666699 := bstep (se 1 (by rfl) ⟨500024, by rfl⟩ : syracuseStep 666699 = 1000049) B1000049
theorem B666711 : Blo 666309 666711 := bstep (se 1 (by rfl) ⟨500033, by rfl⟩ : syracuseStep 666711 = 1000067) B1000067
theorem B666731 : Blo 666309 666731 := bstep (se 1 (by rfl) ⟨500048, by rfl⟩ : syracuseStep 666731 = 1000097) B1000097
theorem B666743 : Blo 666309 666743 := bstep (se 1 (by rfl) ⟨500057, by rfl⟩ : syracuseStep 666743 = 1000115) B1000115
theorem B666763 : Blo 666309 666763 := bstep (se 1 (by rfl) ⟨500072, by rfl⟩ : syracuseStep 666763 = 1000145) B1000145
theorem B1125515 : Blo 666309 1125515 := bstep (se 1 (by rfl) ⟨844136, by rfl⟩ : syracuseStep 1125515 = 1688273) B1688273
theorem B666775 : Blo 666309 666775 := bstep (se 1 (by rfl) ⟨500081, by rfl⟩ : syracuseStep 666775 = 1000163) B1000163
theorem B2403479 : Blo 666309 2403479 := bstep (se 1 (by rfl) ⟨1802609, by rfl⟩ : syracuseStep 2403479 = 3605219) B3605219
theorem B666795 : Blo 666309 666795 := bstep (se 1 (by rfl) ⟨500096, by rfl⟩ : syracuseStep 666795 = 1000193) B1000193
theorem B666807 : Blo 666309 666807 := bstep (se 1 (by rfl) ⟨500105, by rfl⟩ : syracuseStep 666807 = 1000211) B1000211
theorem B666827 : Blo 666309 666827 := bstep (se 1 (by rfl) ⟨500120, by rfl⟩ : syracuseStep 666827 = 1000241) B1000241
theorem B666839 : Blo 666309 666839 := bstep (se 1 (by rfl) ⟨500129, by rfl⟩ : syracuseStep 666839 = 1000259) B1000259
theorem B666859 : Blo 666309 666859 := bstep (se 1 (by rfl) ⟨500144, by rfl⟩ : syracuseStep 666859 = 1000289) B1000289
theorem B666871 : Blo 666309 666871 := bstep (se 1 (by rfl) ⟨500153, by rfl⟩ : syracuseStep 666871 = 1000307) B1000307
theorem B666891 : Blo 666309 666891 := bstep (se 1 (by rfl) ⟨500168, by rfl⟩ : syracuseStep 666891 = 1000337) B1000337
theorem B1125643 : Blo 666309 1125643 := bstep (se 1 (by rfl) ⟨844232, by rfl⟩ : syracuseStep 1125643 = 1688465) B1688465
theorem B666903 : Blo 666309 666903 := bstep (se 1 (by rfl) ⟨500177, by rfl⟩ : syracuseStep 666903 = 1000355) B1000355
theorem B666923 : Blo 666309 666923 := bstep (se 1 (by rfl) ⟨500192, by rfl⟩ : syracuseStep 666923 = 1000385) B1000385
theorem B666935 : Blo 666309 666935 := bstep (se 1 (by rfl) ⟨500201, by rfl⟩ : syracuseStep 666935 = 1000403) B1000403
theorem B666955 : Blo 666309 666955 := bstep (se 1 (by rfl) ⟨500216, by rfl⟩ : syracuseStep 666955 = 1000433) B1000433
theorem B666967 : Blo 666309 666967 := bstep (se 1 (by rfl) ⟨500225, by rfl⟩ : syracuseStep 666967 = 1000451) B1000451
theorem B666987 : Blo 666309 666987 := bstep (se 1 (by rfl) ⟨500240, by rfl⟩ : syracuseStep 666987 = 1000481) B1000481
theorem B666999 : Blo 666309 666999 := bstep (se 1 (by rfl) ⟨500249, by rfl⟩ : syracuseStep 666999 = 1000499) B1000499
theorem B667019 : Blo 666309 667019 := bstep (se 1 (by rfl) ⟨500264, by rfl⟩ : syracuseStep 667019 = 1000529) B1000529
theorem B667031 : Blo 666309 667031 := bstep (se 1 (by rfl) ⟨500273, by rfl⟩ : syracuseStep 667031 = 1000547) B1000547
theorem B1125785 : Blo 666309 1125785 := bstep (se 2 (by rfl) ⟨422169, by rfl⟩ : syracuseStep 1125785 = 844339) B844339
theorem B667051 : Blo 666309 667051 := bstep (se 1 (by rfl) ⟨500288, by rfl⟩ : syracuseStep 667051 = 1000577) B1000577
theorem B667063 : Blo 666309 667063 := bstep (se 1 (by rfl) ⟨500297, by rfl⟩ : syracuseStep 667063 = 1000595) B1000595
theorem B667083 : Blo 666309 667083 := bstep (se 1 (by rfl) ⟨500312, by rfl⟩ : syracuseStep 667083 = 1000625) B1000625
theorem B667095 : Blo 666309 667095 := bstep (se 1 (by rfl) ⟨500321, by rfl⟩ : syracuseStep 667095 = 1000643) B1000643
theorem B667115 : Blo 666309 667115 := bstep (se 1 (by rfl) ⟨500336, by rfl⟩ : syracuseStep 667115 = 1000673) B1000673
theorem B667127 : Blo 666309 667127 := bstep (se 1 (by rfl) ⟨500345, by rfl⟩ : syracuseStep 667127 = 1000691) B1000691
theorem B2534915 : Blo 666309 2534915 := bstep (se 1 (by rfl) ⟨1901186, by rfl⟩ : syracuseStep 2534915 = 3802373) B3802373
theorem B667147 : Blo 666309 667147 := bstep (se 1 (by rfl) ⟨500360, by rfl⟩ : syracuseStep 667147 = 1000721) B1000721
theorem B667159 : Blo 666309 667159 := bstep (se 1 (by rfl) ⟨500369, by rfl⟩ : syracuseStep 667159 = 1000739) B1000739
theorem B1224215 : Blo 666309 1224215 := bstep (se 1 (by rfl) ⟨918161, by rfl⟩ : syracuseStep 1224215 = 1836323) B1836323
theorem B1125913 : Blo 666309 1125913 := bstep (se 2 (by rfl) ⟨422217, by rfl⟩ : syracuseStep 1125913 = 844435) B844435
theorem B667179 : Blo 666309 667179 := bstep (se 1 (by rfl) ⟨500384, by rfl⟩ : syracuseStep 667179 = 1000769) B1000769
theorem B667191 : Blo 666309 667191 := bstep (se 1 (by rfl) ⟨500393, by rfl⟩ : syracuseStep 667191 = 1000787) B1000787
theorem B667211 : Blo 666309 667211 := bstep (se 1 (by rfl) ⟨500408, by rfl⟩ : syracuseStep 667211 = 1000817) B1000817
theorem B667223 : Blo 666309 667223 := bstep (se 1 (by rfl) ⟨500417, by rfl⟩ : syracuseStep 667223 = 1000835) B1000835
theorem B667243 : Blo 666309 667243 := bstep (se 1 (by rfl) ⟨500432, by rfl⟩ : syracuseStep 667243 = 1000865) B1000865
theorem B667255 : Blo 666309 667255 := bstep (se 1 (by rfl) ⟨500441, by rfl⟩ : syracuseStep 667255 = 1000883) B1000883
theorem B667275 : Blo 666309 667275 := bstep (se 1 (by rfl) ⟨500456, by rfl⟩ : syracuseStep 667275 = 1000913) B1000913
theorem B667287 : Blo 666309 667287 := bstep (se 1 (by rfl) ⟨500465, by rfl⟩ : syracuseStep 667287 = 1000931) B1000931
theorem B667307 : Blo 666309 667307 := bstep (se 1 (by rfl) ⟨500480, by rfl⟩ : syracuseStep 667307 = 1000961) B1000961
theorem B9645749 : Blo 666309 9645749 := bstep (se 5 (by rfl) ⟨452144, by rfl⟩ : syracuseStep 9645749 = 904289) B904289
theorem B667319 : Blo 666309 667319 := bstep (se 1 (by rfl) ⟨500489, by rfl⟩ : syracuseStep 667319 = 1000979) B1000979
theorem B667339 : Blo 666309 667339 := bstep (se 1 (by rfl) ⟨500504, by rfl⟩ : syracuseStep 667339 = 1001009) B1001009
theorem B667351 : Blo 666309 667351 := bstep (se 1 (by rfl) ⟨500513, by rfl⟩ : syracuseStep 667351 = 1001027) B1001027
theorem B667371 : Blo 666309 667371 := bstep (se 1 (by rfl) ⟨500528, by rfl⟩ : syracuseStep 667371 = 1001057) B1001057
theorem B667383 : Blo 666309 667383 := bstep (se 1 (by rfl) ⟨500537, by rfl⟩ : syracuseStep 667383 = 1001075) B1001075
theorem B667403 : Blo 666309 667403 := bstep (se 1 (by rfl) ⟨500552, by rfl⟩ : syracuseStep 667403 = 1001105) B1001105
theorem B667415 : Blo 666309 667415 := bstep (se 1 (by rfl) ⟨500561, by rfl⟩ : syracuseStep 667415 = 1001123) B1001123
theorem B667435 : Blo 666309 667435 := bstep (se 1 (by rfl) ⟨500576, by rfl⟩ : syracuseStep 667435 = 1001153) B1001153
theorem B667447 : Blo 666309 667447 := bstep (se 1 (by rfl) ⟨500585, by rfl⟩ : syracuseStep 667447 = 1001171) B1001171
theorem B2404171 : Blo 666309 2404171 := bstep (se 1 (by rfl) ⟨1803128, by rfl⟩ : syracuseStep 2404171 = 3606257) B3606257
theorem B667467 : Blo 666309 667467 := bstep (se 1 (by rfl) ⟨500600, by rfl⟩ : syracuseStep 667467 = 1001201) B1001201
theorem B667479 : Blo 666309 667479 := bstep (se 1 (by rfl) ⟨500609, by rfl⟩ : syracuseStep 667479 = 1001219) B1001219
theorem B667499 : Blo 666309 667499 := bstep (se 1 (by rfl) ⟨500624, by rfl⟩ : syracuseStep 667499 = 1001249) B1001249
theorem B667511 : Blo 666309 667511 := bstep (se 1 (by rfl) ⟨500633, by rfl⟩ : syracuseStep 667511 = 1001267) B1001267
theorem B667531 : Blo 666309 667531 := bstep (se 1 (by rfl) ⟨500648, by rfl⟩ : syracuseStep 667531 = 1001297) B1001297
theorem B667543 : Blo 666309 667543 := bstep (se 1 (by rfl) ⟨500657, by rfl⟩ : syracuseStep 667543 = 1001315) B1001315
theorem B667563 : Blo 666309 667563 := bstep (se 1 (by rfl) ⟨500672, by rfl⟩ : syracuseStep 667563 = 1001345) B1001345
theorem B667575 : Blo 666309 667575 := bstep (se 1 (by rfl) ⟨500681, by rfl⟩ : syracuseStep 667575 = 1001363) B1001363
theorem B667595 : Blo 666309 667595 := bstep (se 1 (by rfl) ⟨500696, by rfl⟩ : syracuseStep 667595 = 1001393) B1001393
theorem B2535371 : Blo 666309 2535371 := bstep (se 1 (by rfl) ⟨1901528, by rfl⟩ : syracuseStep 2535371 = 3803057) B3803057
theorem B667607 : Blo 666309 667607 := bstep (se 1 (by rfl) ⟨500705, by rfl⟩ : syracuseStep 667607 = 1001411) B1001411
theorem B667627 : Blo 666309 667627 := bstep (se 1 (by rfl) ⟨500720, by rfl⟩ : syracuseStep 667627 = 1001441) B1001441
theorem B667639 : Blo 666309 667639 := bstep (se 1 (by rfl) ⟨500729, by rfl⟩ : syracuseStep 667639 = 1001459) B1001459
theorem B667659 : Blo 666309 667659 := bstep (se 1 (by rfl) ⟨500744, by rfl⟩ : syracuseStep 667659 = 1001489) B1001489
theorem B667671 : Blo 666309 667671 := bstep (se 1 (by rfl) ⟨500753, by rfl⟩ : syracuseStep 667671 = 1001507) B1001507
theorem B667691 : Blo 666309 667691 := bstep (se 1 (by rfl) ⟨500768, by rfl⟩ : syracuseStep 667691 = 1001537) B1001537
theorem B667703 : Blo 666309 667703 := bstep (se 1 (by rfl) ⟨500777, by rfl⟩ : syracuseStep 667703 = 1001555) B1001555
theorem B667723 : Blo 666309 667723 := bstep (se 1 (by rfl) ⟨500792, by rfl⟩ : syracuseStep 667723 = 1001585) B1001585
theorem B1126487 : Blo 666309 1126487 := bstep (se 1 (by rfl) ⟨844865, by rfl⟩ : syracuseStep 1126487 = 1689731) B1689731
theorem B667735 : Blo 666309 667735 := bstep (se 1 (by rfl) ⟨500801, by rfl⟩ : syracuseStep 667735 = 1001603) B1001603
theorem B667755 : Blo 666309 667755 := bstep (se 1 (by rfl) ⟨500816, by rfl⟩ : syracuseStep 667755 = 1001633) B1001633
theorem B667767 : Blo 666309 667767 := bstep (se 1 (by rfl) ⟨500825, by rfl⟩ : syracuseStep 667767 = 1001651) B1001651
theorem B667787 : Blo 666309 667787 := bstep (se 1 (by rfl) ⟨500840, by rfl⟩ : syracuseStep 667787 = 1001681) B1001681
theorem B1355915 : Blo 666309 1355915 := bstep (se 1 (by rfl) ⟨1016936, by rfl⟩ : syracuseStep 1355915 = 2033873) B2033873
theorem B2535569 : Blo 666309 2535569 := bstep (se 2 (by rfl) ⟨950838, by rfl⟩ : syracuseStep 2535569 = 1901677) B1901677
theorem B667799 : Blo 666309 667799 := bstep (se 1 (by rfl) ⟨500849, by rfl⟩ : syracuseStep 667799 = 1001699) B1001699
theorem B667819 : Blo 666309 667819 := bstep (se 1 (by rfl) ⟨500864, by rfl⟩ : syracuseStep 667819 = 1001729) B1001729
theorem B667831 : Blo 666309 667831 := bstep (se 1 (by rfl) ⟨500873, by rfl⟩ : syracuseStep 667831 = 1001747) B1001747
theorem B667851 : Blo 666309 667851 := bstep (se 1 (by rfl) ⟨500888, by rfl⟩ : syracuseStep 667851 = 1001777) B1001777
theorem B1126615 : Blo 666309 1126615 := bstep (se 1 (by rfl) ⟨844961, by rfl⟩ : syracuseStep 1126615 = 1689923) B1689923
theorem B667863 : Blo 666309 667863 := bstep (se 1 (by rfl) ⟨500897, by rfl⟩ : syracuseStep 667863 = 1001795) B1001795
theorem B667883 : Blo 666309 667883 := bstep (se 1 (by rfl) ⟨500912, by rfl⟩ : syracuseStep 667883 = 1001825) B1001825
theorem B1519859 : Blo 666309 1519859 := bstep (se 1 (by rfl) ⟨1139894, by rfl⟩ : syracuseStep 1519859 = 2279789) B2279789
theorem B667895 : Blo 666309 667895 := bstep (se 1 (by rfl) ⟨500921, by rfl⟩ : syracuseStep 667895 = 1001843) B1001843
theorem B667915 : Blo 666309 667915 := bstep (se 1 (by rfl) ⟨500936, by rfl⟩ : syracuseStep 667915 = 1001873) B1001873
theorem B667927 : Blo 666309 667927 := bstep (se 1 (by rfl) ⟨500945, by rfl⟩ : syracuseStep 667927 = 1001891) B1001891
theorem B667947 : Blo 666309 667947 := bstep (se 1 (by rfl) ⟨500960, by rfl⟩ : syracuseStep 667947 = 1001921) B1001921
theorem B667959 : Blo 666309 667959 := bstep (se 1 (by rfl) ⟨500969, by rfl⟩ : syracuseStep 667959 = 1001939) B1001939
theorem B667979 : Blo 666309 667979 := bstep (se 1 (by rfl) ⟨500984, by rfl⟩ : syracuseStep 667979 = 1001969) B1001969
theorem B667991 : Blo 666309 667991 := bstep (se 1 (by rfl) ⟨500993, by rfl⟩ : syracuseStep 667991 = 1001987) B1001987
theorem B668011 : Blo 666309 668011 := bstep (se 1 (by rfl) ⟨501008, by rfl⟩ : syracuseStep 668011 = 1002017) B1002017
theorem B15446389 : Blo 666309 15446389 := bstep (se 5 (by rfl) ⟨724049, by rfl⟩ : syracuseStep 15446389 = 1448099) B1448099
theorem B668023 : Blo 666309 668023 := bstep (se 1 (by rfl) ⟨501017, by rfl⟩ : syracuseStep 668023 = 1002035) B1002035
theorem B3813763 : Blo 666309 3813763 := bstep (se 1 (by rfl) ⟨2860322, by rfl⟩ : syracuseStep 3813763 = 5720645) B5720645
theorem B668043 : Blo 666309 668043 := bstep (se 1 (by rfl) ⟨501032, by rfl⟩ : syracuseStep 668043 = 1002065) B1002065
theorem B668055 : Blo 666309 668055 := bstep (se 1 (by rfl) ⟨501041, by rfl⟩ : syracuseStep 668055 = 1002083) B1002083
theorem B668075 : Blo 666309 668075 := bstep (se 1 (by rfl) ⟨501056, by rfl⟩ : syracuseStep 668075 = 1002113) B1002113
theorem B668087 : Blo 666309 668087 := bstep (se 1 (by rfl) ⟨501065, by rfl⟩ : syracuseStep 668087 = 1002131) B1002131
theorem B668107 : Blo 666309 668107 := bstep (se 1 (by rfl) ⟨501080, by rfl⟩ : syracuseStep 668107 = 1002161) B1002161
theorem B668119 : Blo 666309 668119 := bstep (se 1 (by rfl) ⟨501089, by rfl⟩ : syracuseStep 668119 = 1002179) B1002179
theorem B668139 : Blo 666309 668139 := bstep (se 1 (by rfl) ⟨501104, by rfl⟩ : syracuseStep 668139 = 1002209) B1002209
theorem B668151 : Blo 666309 668151 := bstep (se 1 (by rfl) ⟨501113, by rfl⟩ : syracuseStep 668151 = 1002227) B1002227
theorem B668171 : Blo 666309 668171 := bstep (se 1 (by rfl) ⟨501128, by rfl⟩ : syracuseStep 668171 = 1002257) B1002257
theorem B668183 : Blo 666309 668183 := bstep (se 1 (by rfl) ⟨501137, by rfl⟩ : syracuseStep 668183 = 1002275) B1002275
theorem B668203 : Blo 666309 668203 := bstep (se 1 (by rfl) ⟨501152, by rfl⟩ : syracuseStep 668203 = 1002305) B1002305
theorem B668215 : Blo 666309 668215 := bstep (se 1 (by rfl) ⟨501161, by rfl⟩ : syracuseStep 668215 = 1002323) B1002323
theorem B11416139 : Blo 666309 11416139 := bstep (se 1 (by rfl) ⟨8562104, by rfl⟩ : syracuseStep 11416139 = 17124209) B17124209
theorem B668235 : Blo 666309 668235 := bstep (se 1 (by rfl) ⟨501176, by rfl⟩ : syracuseStep 668235 = 1002353) B1002353
theorem B668247 : Blo 666309 668247 := bstep (se 1 (by rfl) ⟨501185, by rfl⟩ : syracuseStep 668247 = 1002371) B1002371
theorem B668267 : Blo 666309 668267 := bstep (se 1 (by rfl) ⟨501200, by rfl⟩ : syracuseStep 668267 = 1002401) B1002401
theorem B668279 : Blo 666309 668279 := bstep (se 1 (by rfl) ⟨501209, by rfl⟩ : syracuseStep 668279 = 1002419) B1002419
theorem B668299 : Blo 666309 668299 := bstep (se 1 (by rfl) ⟨501224, by rfl⟩ : syracuseStep 668299 = 1002449) B1002449
theorem B668311 : Blo 666309 668311 := bstep (se 1 (by rfl) ⟨501233, by rfl⟩ : syracuseStep 668311 = 1002467) B1002467
theorem B668331 : Blo 666309 668331 := bstep (se 1 (by rfl) ⟨501248, by rfl⟩ : syracuseStep 668331 = 1002497) B1002497
theorem B668343 : Blo 666309 668343 := bstep (se 1 (by rfl) ⟨501257, by rfl⟩ : syracuseStep 668343 = 1002515) B1002515
theorem B668363 : Blo 666309 668363 := bstep (se 1 (by rfl) ⟨501272, by rfl⟩ : syracuseStep 668363 = 1002545) B1002545
theorem B668375 : Blo 666309 668375 := bstep (se 1 (by rfl) ⟨501281, by rfl⟩ : syracuseStep 668375 = 1002563) B1002563
theorem B668395 : Blo 666309 668395 := bstep (se 1 (by rfl) ⟨501296, by rfl⟩ : syracuseStep 668395 = 1002593) B1002593
theorem B668407 : Blo 666309 668407 := bstep (se 1 (by rfl) ⟨501305, by rfl⟩ : syracuseStep 668407 = 1002611) B1002611
theorem B668427 : Blo 666309 668427 := bstep (se 1 (by rfl) ⟨501320, by rfl⟩ : syracuseStep 668427 = 1002641) B1002641
theorem B668439 : Blo 666309 668439 := bstep (se 1 (by rfl) ⟨501329, by rfl⟩ : syracuseStep 668439 = 1002659) B1002659
theorem B668459 : Blo 666309 668459 := bstep (se 1 (by rfl) ⟨501344, by rfl⟩ : syracuseStep 668459 = 1002689) B1002689
theorem B668471 : Blo 666309 668471 := bstep (se 1 (by rfl) ⟨501353, by rfl⟩ : syracuseStep 668471 = 1002707) B1002707
theorem B1127243 : Blo 666309 1127243 := bstep (se 1 (by rfl) ⟨845432, by rfl⟩ : syracuseStep 1127243 = 1690865) B1690865
theorem B668491 : Blo 666309 668491 := bstep (se 1 (by rfl) ⟨501368, by rfl⟩ : syracuseStep 668491 = 1002737) B1002737
theorem B668503 : Blo 666309 668503 := bstep (se 1 (by rfl) ⟨501377, by rfl⟩ : syracuseStep 668503 = 1002755) B1002755
theorem B668523 : Blo 666309 668523 := bstep (se 1 (by rfl) ⟨501392, by rfl⟩ : syracuseStep 668523 = 1002785) B1002785
theorem B668535 : Blo 666309 668535 := bstep (se 1 (by rfl) ⟨501401, by rfl⟩ : syracuseStep 668535 = 1002803) B1002803
theorem B668555 : Blo 666309 668555 := bstep (se 1 (by rfl) ⟨501416, by rfl⟩ : syracuseStep 668555 = 1002833) B1002833
theorem B2536343 : Blo 666309 2536343 := bstep (se 1 (by rfl) ⟨1902257, by rfl⟩ : syracuseStep 2536343 = 3804515) B3804515
theorem B668567 : Blo 666309 668567 := bstep (se 1 (by rfl) ⟨501425, by rfl⟩ : syracuseStep 668567 = 1002851) B1002851
theorem B668587 : Blo 666309 668587 := bstep (se 1 (by rfl) ⟨501440, by rfl⟩ : syracuseStep 668587 = 1002881) B1002881
theorem B668599 : Blo 666309 668599 := bstep (se 1 (by rfl) ⟨501449, by rfl⟩ : syracuseStep 668599 = 1002899) B1002899
theorem B1127371 : Blo 666309 1127371 := bstep (se 1 (by rfl) ⟨845528, by rfl⟩ : syracuseStep 1127371 = 1691057) B1691057
theorem B668619 : Blo 666309 668619 := bstep (se 1 (by rfl) ⟨501464, by rfl⟩ : syracuseStep 668619 = 1002929) B1002929
theorem B668631 : Blo 666309 668631 := bstep (se 1 (by rfl) ⟨501473, by rfl⟩ : syracuseStep 668631 = 1002947) B1002947
theorem B668651 : Blo 666309 668651 := bstep (se 1 (by rfl) ⟨501488, by rfl⟩ : syracuseStep 668651 = 1002977) B1002977
theorem B668663 : Blo 666309 668663 := bstep (se 1 (by rfl) ⟨501497, by rfl⟩ : syracuseStep 668663 = 1002995) B1002995
theorem B668683 : Blo 666309 668683 := bstep (se 1 (by rfl) ⟨501512, by rfl⟩ : syracuseStep 668683 = 1003025) B1003025
theorem B668695 : Blo 666309 668695 := bstep (se 1 (by rfl) ⟨501521, by rfl⟩ : syracuseStep 668695 = 1003043) B1003043
theorem B668715 : Blo 666309 668715 := bstep (se 1 (by rfl) ⟨501536, by rfl⟩ : syracuseStep 668715 = 1003073) B1003073
theorem B668727 : Blo 666309 668727 := bstep (se 1 (by rfl) ⟨501545, by rfl⟩ : syracuseStep 668727 = 1003091) B1003091
theorem B668747 : Blo 666309 668747 := bstep (se 1 (by rfl) ⟨501560, by rfl⟩ : syracuseStep 668747 = 1003121) B1003121
theorem B668759 : Blo 666309 668759 := bstep (se 1 (by rfl) ⟨501569, by rfl⟩ : syracuseStep 668759 = 1003139) B1003139
theorem B1127513 : Blo 666309 1127513 := bstep (se 2 (by rfl) ⟨422817, by rfl⟩ : syracuseStep 1127513 = 845635) B845635
theorem B2536541 : Blo 666309 2536541 := bstep (se 3 (by rfl) ⟨475601, by rfl⟩ : syracuseStep 2536541 = 951203) B951203
theorem B668779 : Blo 666309 668779 := bstep (se 1 (by rfl) ⟨501584, by rfl⟩ : syracuseStep 668779 = 1003169) B1003169
theorem B668791 : Blo 666309 668791 := bstep (se 1 (by rfl) ⟨501593, by rfl⟩ : syracuseStep 668791 = 1003187) B1003187
theorem B668811 : Blo 666309 668811 := bstep (se 1 (by rfl) ⟨501608, by rfl⟩ : syracuseStep 668811 = 1003217) B1003217
theorem B668823 : Blo 666309 668823 := bstep (se 1 (by rfl) ⟨501617, by rfl⟩ : syracuseStep 668823 = 1003235) B1003235
theorem B668843 : Blo 666309 668843 := bstep (se 1 (by rfl) ⟨501632, by rfl⟩ : syracuseStep 668843 = 1003265) B1003265
theorem B668855 : Blo 666309 668855 := bstep (se 1 (by rfl) ⟨501641, by rfl⟩ : syracuseStep 668855 = 1003283) B1003283
theorem B668875 : Blo 666309 668875 := bstep (se 1 (by rfl) ⟨501656, by rfl⟩ : syracuseStep 668875 = 1003313) B1003313
theorem B1651915 : Blo 666309 1651915 := bstep (se 1 (by rfl) ⟨1238936, by rfl⟩ : syracuseStep 1651915 = 2477873) B2477873
theorem B668887 : Blo 666309 668887 := bstep (se 1 (by rfl) ⟨501665, by rfl⟩ : syracuseStep 668887 = 1003331) B1003331
theorem B1127641 : Blo 666309 1127641 := bstep (se 2 (by rfl) ⟨422865, by rfl⟩ : syracuseStep 1127641 = 845731) B845731
theorem B668907 : Blo 666309 668907 := bstep (se 1 (by rfl) ⟨501680, by rfl⟩ : syracuseStep 668907 = 1003361) B1003361
theorem B668919 : Blo 666309 668919 := bstep (se 1 (by rfl) ⟨501689, by rfl⟩ : syracuseStep 668919 = 1003379) B1003379
theorem B668939 : Blo 666309 668939 := bstep (se 1 (by rfl) ⟨501704, by rfl⟩ : syracuseStep 668939 = 1003409) B1003409
theorem B668951 : Blo 666309 668951 := bstep (se 1 (by rfl) ⟨501713, by rfl⟩ : syracuseStep 668951 = 1003427) B1003427
theorem B668971 : Blo 666309 668971 := bstep (se 1 (by rfl) ⟨501728, by rfl⟩ : syracuseStep 668971 = 1003457) B1003457
theorem B668983 : Blo 666309 668983 := bstep (se 1 (by rfl) ⟨501737, by rfl⟩ : syracuseStep 668983 = 1003475) B1003475
theorem B3814721 : Blo 666309 3814721 := bstep (se 2 (by rfl) ⟨1430520, by rfl⟩ : syracuseStep 3814721 = 2861041) B2861041
theorem B669003 : Blo 666309 669003 := bstep (se 1 (by rfl) ⟨501752, by rfl⟩ : syracuseStep 669003 = 1003505) B1003505
theorem B669015 : Blo 666309 669015 := bstep (se 1 (by rfl) ⟨501761, by rfl⟩ : syracuseStep 669015 = 1003523) B1003523
theorem B669035 : Blo 666309 669035 := bstep (se 1 (by rfl) ⟨501776, by rfl⟩ : syracuseStep 669035 = 1003553) B1003553
theorem B669047 : Blo 666309 669047 := bstep (se 1 (by rfl) ⟨501785, by rfl⟩ : syracuseStep 669047 = 1003571) B1003571
theorem B669067 : Blo 666309 669067 := bstep (se 1 (by rfl) ⟨501800, by rfl⟩ : syracuseStep 669067 = 1003601) B1003601
theorem B669079 : Blo 666309 669079 := bstep (se 1 (by rfl) ⟨501809, by rfl⟩ : syracuseStep 669079 = 1003619) B1003619
theorem B669099 : Blo 666309 669099 := bstep (se 1 (by rfl) ⟨501824, by rfl⟩ : syracuseStep 669099 = 1003649) B1003649
theorem B669111 : Blo 666309 669111 := bstep (se 1 (by rfl) ⟨501833, by rfl⟩ : syracuseStep 669111 = 1003667) B1003667
theorem B669131 : Blo 666309 669131 := bstep (se 1 (by rfl) ⟨501848, by rfl⟩ : syracuseStep 669131 = 1003697) B1003697
theorem B669143 : Blo 666309 669143 := bstep (se 1 (by rfl) ⟨501857, by rfl⟩ : syracuseStep 669143 = 1003715) B1003715
theorem B2143705 : Blo 666309 2143705 := bstep (se 2 (by rfl) ⟨803889, by rfl⟩ : syracuseStep 2143705 = 1607779) B1607779
theorem B669163 : Blo 666309 669163 := bstep (se 1 (by rfl) ⟨501872, by rfl⟩ : syracuseStep 669163 = 1003745) B1003745
theorem B669175 : Blo 666309 669175 := bstep (se 1 (by rfl) ⟨501881, by rfl⟩ : syracuseStep 669175 = 1003763) B1003763
theorem B669195 : Blo 666309 669195 := bstep (se 1 (by rfl) ⟨501896, by rfl⟩ : syracuseStep 669195 = 1003793) B1003793
theorem B669207 : Blo 666309 669207 := bstep (se 1 (by rfl) ⟨501905, by rfl⟩ : syracuseStep 669207 = 1003811) B1003811
theorem B669227 : Blo 666309 669227 := bstep (se 1 (by rfl) ⟨501920, by rfl⟩ : syracuseStep 669227 = 1003841) B1003841
theorem B2405933 : Blo 666309 2405933 := bstep (se 3 (by rfl) ⟨451112, by rfl⟩ : syracuseStep 2405933 = 902225) B902225
theorem B669239 : Blo 666309 669239 := bstep (se 1 (by rfl) ⟨501929, by rfl⟩ : syracuseStep 669239 = 1003859) B1003859
theorem B5715521 : Blo 666309 5715521 := bstep (se 2 (by rfl) ⟨2143320, by rfl⟩ : syracuseStep 5715521 = 4286641) B4286641
theorem B669259 : Blo 666309 669259 := bstep (se 1 (by rfl) ⟨501944, by rfl⟩ : syracuseStep 669259 = 1003889) B1003889
theorem B669271 : Blo 666309 669271 := bstep (se 1 (by rfl) ⟨501953, by rfl⟩ : syracuseStep 669271 = 1003907) B1003907
theorem B669291 : Blo 666309 669291 := bstep (se 1 (by rfl) ⟨501968, by rfl⟩ : syracuseStep 669291 = 1003937) B1003937
theorem B669303 : Blo 666309 669303 := bstep (se 1 (by rfl) ⟨501977, by rfl⟩ : syracuseStep 669303 = 1003955) B1003955
theorem B669323 : Blo 666309 669323 := bstep (se 1 (by rfl) ⟨501992, by rfl⟩ : syracuseStep 669323 = 1003985) B1003985
theorem B669335 : Blo 666309 669335 := bstep (se 1 (by rfl) ⟨502001, by rfl⟩ : syracuseStep 669335 = 1004003) B1004003
theorem B669355 : Blo 666309 669355 := bstep (se 1 (by rfl) ⟨502016, by rfl⟩ : syracuseStep 669355 = 1004033) B1004033
theorem B669367 : Blo 666309 669367 := bstep (se 1 (by rfl) ⟨502025, by rfl⟩ : syracuseStep 669367 = 1004051) B1004051
theorem B669387 : Blo 666309 669387 := bstep (se 1 (by rfl) ⟨502040, by rfl⟩ : syracuseStep 669387 = 1004081) B1004081
theorem B669399 : Blo 666309 669399 := bstep (se 1 (by rfl) ⟨502049, by rfl⟩ : syracuseStep 669399 = 1004099) B1004099
theorem B669419 : Blo 666309 669419 := bstep (se 1 (by rfl) ⟨502064, by rfl⟩ : syracuseStep 669419 = 1004129) B1004129
theorem B669431 : Blo 666309 669431 := bstep (se 1 (by rfl) ⟨502073, by rfl⟩ : syracuseStep 669431 = 1004147) B1004147
theorem B669451 : Blo 666309 669451 := bstep (se 1 (by rfl) ⟨502088, by rfl⟩ : syracuseStep 669451 = 1004177) B1004177
theorem B3389201 : Blo 666309 3389201 := bstep (se 2 (by rfl) ⟨1270950, by rfl⟩ : syracuseStep 3389201 = 2541901) B2541901
theorem B1128215 : Blo 666309 1128215 := bstep (se 1 (by rfl) ⟨846161, by rfl⟩ : syracuseStep 1128215 = 1692323) B1692323
theorem B669463 : Blo 666309 669463 := bstep (se 1 (by rfl) ⟨502097, by rfl⟩ : syracuseStep 669463 = 1004195) B1004195
theorem B669483 : Blo 666309 669483 := bstep (se 1 (by rfl) ⟨502112, by rfl⟩ : syracuseStep 669483 = 1004225) B1004225
theorem B669495 : Blo 666309 669495 := bstep (se 1 (by rfl) ⟨502121, by rfl⟩ : syracuseStep 669495 = 1004243) B1004243
theorem B669515 : Blo 666309 669515 := bstep (se 1 (by rfl) ⟨502136, by rfl⟩ : syracuseStep 669515 = 1004273) B1004273
theorem B669527 : Blo 666309 669527 := bstep (se 1 (by rfl) ⟨502145, by rfl⟩ : syracuseStep 669527 = 1004291) B1004291
theorem B669547 : Blo 666309 669547 := bstep (se 1 (by rfl) ⟨502160, by rfl⟩ : syracuseStep 669547 = 1004321) B1004321
theorem B669559 : Blo 666309 669559 := bstep (se 1 (by rfl) ⟨502169, by rfl⟩ : syracuseStep 669559 = 1004339) B1004339
theorem B669579 : Blo 666309 669579 := bstep (se 1 (by rfl) ⟨502184, by rfl⟩ : syracuseStep 669579 = 1004369) B1004369
theorem B1128343 : Blo 666309 1128343 := bstep (se 1 (by rfl) ⟨846257, by rfl⟩ : syracuseStep 1128343 = 1692515) B1692515
theorem B669591 : Blo 666309 669591 := bstep (se 1 (by rfl) ⟨502193, by rfl⟩ : syracuseStep 669591 = 1004387) B1004387
theorem B669611 : Blo 666309 669611 := bstep (se 1 (by rfl) ⟨502208, by rfl⟩ : syracuseStep 669611 = 1004417) B1004417
theorem B3389363 : Blo 666309 3389363 := bstep (se 1 (by rfl) ⟨2542022, by rfl⟩ : syracuseStep 3389363 = 5084045) B5084045
theorem B669623 : Blo 666309 669623 := bstep (se 1 (by rfl) ⟨502217, by rfl⟩ : syracuseStep 669623 = 1004435) B1004435
theorem B669643 : Blo 666309 669643 := bstep (se 1 (by rfl) ⟨502232, by rfl⟩ : syracuseStep 669643 = 1004465) B1004465
theorem B669655 : Blo 666309 669655 := bstep (se 1 (by rfl) ⟨502241, by rfl⟩ : syracuseStep 669655 = 1004483) B1004483
theorem B669675 : Blo 666309 669675 := bstep (se 1 (by rfl) ⟨502256, by rfl⟩ : syracuseStep 669675 = 1004513) B1004513
theorem B669687 : Blo 666309 669687 := bstep (se 1 (by rfl) ⟨502265, by rfl⟩ : syracuseStep 669687 = 1004531) B1004531
theorem B669707 : Blo 666309 669707 := bstep (se 1 (by rfl) ⟨502280, by rfl⟩ : syracuseStep 669707 = 1004561) B1004561
theorem B669719 : Blo 666309 669719 := bstep (se 1 (by rfl) ⟨502289, by rfl⟩ : syracuseStep 669719 = 1004579) B1004579
theorem B669739 : Blo 666309 669739 := bstep (se 1 (by rfl) ⟨502304, by rfl⟩ : syracuseStep 669739 = 1004609) B1004609
theorem B669751 : Blo 666309 669751 := bstep (se 1 (by rfl) ⟨502313, by rfl⟩ : syracuseStep 669751 = 1004627) B1004627
theorem B669771 : Blo 666309 669771 := bstep (se 1 (by rfl) ⟨502328, by rfl⟩ : syracuseStep 669771 = 1004657) B1004657
theorem B669783 : Blo 666309 669783 := bstep (se 1 (by rfl) ⟨502337, by rfl⟩ : syracuseStep 669783 = 1004675) B1004675
theorem B669803 : Blo 666309 669803 := bstep (se 1 (by rfl) ⟨502352, by rfl⟩ : syracuseStep 669803 = 1004705) B1004705
theorem B669815 : Blo 666309 669815 := bstep (se 1 (by rfl) ⟨502361, by rfl⟩ : syracuseStep 669815 = 1004723) B1004723
theorem B669835 : Blo 666309 669835 := bstep (se 1 (by rfl) ⟨502376, by rfl⟩ : syracuseStep 669835 = 1004753) B1004753
theorem B669847 : Blo 666309 669847 := bstep (se 1 (by rfl) ⟨502385, by rfl⟩ : syracuseStep 669847 = 1004771) B1004771
theorem B669867 : Blo 666309 669867 := bstep (se 1 (by rfl) ⟨502400, by rfl⟩ : syracuseStep 669867 = 1004801) B1004801
theorem B669879 : Blo 666309 669879 := bstep (se 1 (by rfl) ⟨502409, by rfl⟩ : syracuseStep 669879 = 1004819) B1004819
theorem B669899 : Blo 666309 669899 := bstep (se 1 (by rfl) ⟨502424, by rfl⟩ : syracuseStep 669899 = 1004849) B1004849
theorem B669911 : Blo 666309 669911 := bstep (se 1 (by rfl) ⟨502433, by rfl⟩ : syracuseStep 669911 = 1004867) B1004867
theorem B669931 : Blo 666309 669931 := bstep (se 1 (by rfl) ⟨502448, by rfl⟩ : syracuseStep 669931 = 1004897) B1004897
theorem B669943 : Blo 666309 669943 := bstep (se 1 (by rfl) ⟨502457, by rfl⟩ : syracuseStep 669943 = 1004915) B1004915
theorem B669963 : Blo 666309 669963 := bstep (se 1 (by rfl) ⟨502472, by rfl⟩ : syracuseStep 669963 = 1004945) B1004945
theorem B669975 : Blo 666309 669975 := bstep (se 1 (by rfl) ⟨502481, by rfl⟩ : syracuseStep 669975 = 1004963) B1004963
theorem B669995 : Blo 666309 669995 := bstep (se 1 (by rfl) ⟨502496, by rfl⟩ : syracuseStep 669995 = 1004993) B1004993
theorem B670007 : Blo 666309 670007 := bstep (se 1 (by rfl) ⟨502505, by rfl⟩ : syracuseStep 670007 = 1005011) B1005011
theorem B670027 : Blo 666309 670027 := bstep (se 1 (by rfl) ⟨502520, by rfl⟩ : syracuseStep 670027 = 1005041) B1005041
theorem B1423703 : Blo 666309 1423703 := bstep (se 1 (by rfl) ⟨1067777, by rfl⟩ : syracuseStep 1423703 = 2135555) B2135555
theorem B670039 : Blo 666309 670039 := bstep (se 1 (by rfl) ⟨502529, by rfl⟩ : syracuseStep 670039 = 1005059) B1005059
theorem B670059 : Blo 666309 670059 := bstep (se 1 (by rfl) ⟨502544, by rfl⟩ : syracuseStep 670059 = 1005089) B1005089
theorem B670071 : Blo 666309 670071 := bstep (se 1 (by rfl) ⟨502553, by rfl⟩ : syracuseStep 670071 = 1005107) B1005107
theorem B670091 : Blo 666309 670091 := bstep (se 1 (by rfl) ⟨502568, by rfl⟩ : syracuseStep 670091 = 1005137) B1005137
theorem B670103 : Blo 666309 670103 := bstep (se 1 (by rfl) ⟨502577, by rfl⟩ : syracuseStep 670103 = 1005155) B1005155
theorem B670123 : Blo 666309 670123 := bstep (se 1 (by rfl) ⟨502592, by rfl⟩ : syracuseStep 670123 = 1005185) B1005185
theorem B670135 : Blo 666309 670135 := bstep (se 1 (by rfl) ⟨502601, by rfl⟩ : syracuseStep 670135 = 1005203) B1005203
theorem B670155 : Blo 666309 670155 := bstep (se 1 (by rfl) ⟨502616, by rfl⟩ : syracuseStep 670155 = 1005233) B1005233
theorem B670167 : Blo 666309 670167 := bstep (se 1 (by rfl) ⟨502625, by rfl⟩ : syracuseStep 670167 = 1005251) B1005251
theorem B670187 : Blo 666309 670187 := bstep (se 1 (by rfl) ⟨502640, by rfl⟩ : syracuseStep 670187 = 1005281) B1005281
theorem B670199 : Blo 666309 670199 := bstep (se 1 (by rfl) ⟨502649, by rfl⟩ : syracuseStep 670199 = 1005299) B1005299
theorem B1128971 : Blo 666309 1128971 := bstep (se 1 (by rfl) ⟨846728, by rfl⟩ : syracuseStep 1128971 = 1693457) B1693457
theorem B670219 : Blo 666309 670219 := bstep (se 1 (by rfl) ⟨502664, by rfl⟩ : syracuseStep 670219 = 1005329) B1005329
theorem B670231 : Blo 666309 670231 := bstep (se 1 (by rfl) ⟨502673, by rfl⟩ : syracuseStep 670231 = 1005347) B1005347
theorem B670251 : Blo 666309 670251 := bstep (se 1 (by rfl) ⟨502688, by rfl⟩ : syracuseStep 670251 = 1005377) B1005377
theorem B670263 : Blo 666309 670263 := bstep (se 1 (by rfl) ⟨502697, by rfl⟩ : syracuseStep 670263 = 1005395) B1005395
theorem B670283 : Blo 666309 670283 := bstep (se 1 (by rfl) ⟨502712, by rfl⟩ : syracuseStep 670283 = 1005425) B1005425
theorem B670295 : Blo 666309 670295 := bstep (se 1 (by rfl) ⟨502721, by rfl⟩ : syracuseStep 670295 = 1005443) B1005443
theorem B1129099 : Blo 666309 1129099 := bstep (se 1 (by rfl) ⟨846824, by rfl⟩ : syracuseStep 1129099 = 1693649) B1693649
theorem B1129241 : Blo 666309 1129241 := bstep (se 2 (by rfl) ⟨423465, by rfl⟩ : syracuseStep 1129241 = 846931) B846931
theorem B1129369 : Blo 666309 1129369 := bstep (se 2 (by rfl) ⟨423513, by rfl⟩ : syracuseStep 1129369 = 847027) B847027
theorem B2538499 : Blo 666309 2538499 := bstep (se 1 (by rfl) ⟨1903874, by rfl⟩ : syracuseStep 2538499 = 3807749) B3807749
theorem B2538803 : Blo 666309 2538803 := bstep (se 1 (by rfl) ⟨1904102, by rfl⟩ : syracuseStep 2538803 = 3808205) B3808205
theorem B1424729 : Blo 666309 1424729 := bstep (se 2 (by rfl) ⟨534273, by rfl⟩ : syracuseStep 1424729 = 1068547) B1068547
theorem B1686977 : Blo 666309 1686977 := bstep (se 2 (by rfl) ⟨632616, by rfl⟩ : syracuseStep 1686977 = 1265233) B1265233
theorem B1129943 : Blo 666309 1129943 := bstep (se 1 (by rfl) ⟨847457, by rfl⟩ : syracuseStep 1129943 = 1694915) B1694915
theorem B2145857 : Blo 666309 2145857 := bstep (se 2 (by rfl) ⟨804696, by rfl⟩ : syracuseStep 2145857 = 1609393) B1609393
theorem B1130071 : Blo 666309 1130071 := bstep (se 1 (by rfl) ⟨847553, by rfl⟩ : syracuseStep 1130071 = 1695107) B1695107
theorem B2408267 : Blo 666309 2408267 := bstep (se 1 (by rfl) ⟨1806200, by rfl⟩ : syracuseStep 2408267 = 3612401) B3612401
theorem B3391307 : Blo 666309 3391307 := bstep (se 1 (by rfl) ⟨2543480, by rfl⟩ : syracuseStep 3391307 = 5086961) B5086961
theorem B5717911 : Blo 666309 5717911 := bstep (se 1 (by rfl) ⟨4288433, by rfl⟩ : syracuseStep 5717911 = 8576867) B8576867
theorem B2539457 : Blo 666309 2539457 := bstep (se 2 (by rfl) ⟨952296, by rfl⟩ : syracuseStep 2539457 = 1904593) B1904593
theorem B1687513 : Blo 666309 1687513 := bstep (se 2 (by rfl) ⟨632817, by rfl⟩ : syracuseStep 1687513 = 1265635) B1265635
theorem B5062661 : Blo 666309 5062661 := bstep (se 4 (by rfl) ⟨474624, by rfl⟩ : syracuseStep 5062661 = 949249) B949249
theorem B3653707 : Blo 666309 3653707 := bstep (se 1 (by rfl) ⟨2740280, by rfl⟩ : syracuseStep 3653707 = 5480561) B5480561
theorem B999563 : Blo 666309 999563 := bstep (se 1 (by rfl) ⟨749672, by rfl⟩ : syracuseStep 999563 = 1499345) B1499345
theorem B999575 : Blo 666309 999575 := bstep (se 1 (by rfl) ⟨749681, by rfl⟩ : syracuseStep 999575 = 1499363) B1499363
theorem B1130699 : Blo 666309 1130699 := bstep (se 1 (by rfl) ⟨848024, by rfl⟩ : syracuseStep 1130699 = 1696049) B1696049
theorem B999641 : Blo 666309 999641 := bstep (se 2 (by rfl) ⟨374865, by rfl⟩ : syracuseStep 999641 = 749731) B749731
theorem B999755 : Blo 666309 999755 := bstep (se 1 (by rfl) ⟨749816, by rfl⟩ : syracuseStep 999755 = 1499633) B1499633
theorem B1130827 : Blo 666309 1130827 := bstep (se 1 (by rfl) ⟨848120, by rfl⟩ : syracuseStep 1130827 = 1696241) B1696241
theorem B999767 : Blo 666309 999767 := bstep (se 1 (by rfl) ⟨749825, by rfl⟩ : syracuseStep 999767 = 1499651) B1499651
theorem B999833 : Blo 666309 999833 := bstep (se 2 (by rfl) ⟨374937, by rfl⟩ : syracuseStep 999833 = 749875) B749875
theorem B2310617 : Blo 666309 2310617 := bstep (se 2 (by rfl) ⟨866481, by rfl⟩ : syracuseStep 2310617 = 1732963) B1732963
theorem B1130969 : Blo 666309 1130969 := bstep (se 2 (by rfl) ⟨424113, by rfl⟩ : syracuseStep 1130969 = 848227) B848227
theorem B999947 : Blo 666309 999947 := bstep (se 1 (by rfl) ⟨749960, by rfl⟩ : syracuseStep 999947 = 1499921) B1499921
theorem B999959 : Blo 666309 999959 := bstep (se 1 (by rfl) ⟨749969, by rfl⟩ : syracuseStep 999959 = 1499939) B1499939
theorem B6439499 : Blo 666309 6439499 := bstep (se 1 (by rfl) ⟨4829624, by rfl⟩ : syracuseStep 6439499 = 9659249) B9659249
theorem B1000025 : Blo 666309 1000025 := bstep (se 2 (by rfl) ⟨375009, by rfl⟩ : syracuseStep 1000025 = 750019) B750019
theorem B1131097 : Blo 666309 1131097 := bstep (se 2 (by rfl) ⟨424161, by rfl⟩ : syracuseStep 1131097 = 848323) B848323
theorem B770743 : Blo 666309 770743 := bstep (se 1 (by rfl) ⟨578057, by rfl⟩ : syracuseStep 770743 = 1156115) B1156115
theorem B1000139 : Blo 666309 1000139 := bstep (se 1 (by rfl) ⟨750104, by rfl⟩ : syracuseStep 1000139 = 1500209) B1500209
theorem B1000151 : Blo 666309 1000151 := bstep (se 1 (by rfl) ⟨750113, by rfl⟩ : syracuseStep 1000151 = 1500227) B1500227
theorem B1000217 : Blo 666309 1000217 := bstep (se 2 (by rfl) ⟨375081, by rfl⟩ : syracuseStep 1000217 = 750163) B750163
theorem B1000331 : Blo 666309 1000331 := bstep (se 1 (by rfl) ⟨750248, by rfl⟩ : syracuseStep 1000331 = 1500497) B1500497
theorem B1000343 : Blo 666309 1000343 := bstep (se 1 (by rfl) ⟨750257, by rfl⟩ : syracuseStep 1000343 = 1500515) B1500515
theorem B7619507 : Blo 666309 7619507 := bstep (se 1 (by rfl) ⟨5714630, by rfl⟩ : syracuseStep 7619507 = 11429261) B11429261
theorem B1426369 : Blo 666309 1426369 := bstep (se 2 (by rfl) ⟨534888, by rfl⟩ : syracuseStep 1426369 = 1069777) B1069777
theorem B1000409 : Blo 666309 1000409 := bstep (se 2 (by rfl) ⟨375153, by rfl⟩ : syracuseStep 1000409 = 750307) B750307
theorem B1688627 : Blo 666309 1688627 := bstep (se 1 (by rfl) ⟨1266470, by rfl⟩ : syracuseStep 1688627 = 2532941) B2532941
theorem B1000523 : Blo 666309 1000523 := bstep (se 1 (by rfl) ⟨750392, by rfl⟩ : syracuseStep 1000523 = 1500785) B1500785
theorem B1000535 : Blo 666309 1000535 := bstep (se 1 (by rfl) ⟨750401, by rfl⟩ : syracuseStep 1000535 = 1500803) B1500803
theorem B1000601 : Blo 666309 1000601 := bstep (se 2 (by rfl) ⟨375225, by rfl⟩ : syracuseStep 1000601 = 750451) B750451
theorem B2540717 : Blo 666309 2540717 := bstep (se 3 (by rfl) ⟨476384, by rfl⟩ : syracuseStep 2540717 = 952769) B952769
theorem B2540747 : Blo 666309 2540747 := bstep (se 1 (by rfl) ⟨1905560, by rfl⟩ : syracuseStep 2540747 = 3811121) B3811121
theorem B1000715 : Blo 666309 1000715 := bstep (se 1 (by rfl) ⟨750536, by rfl⟩ : syracuseStep 1000715 = 1501073) B1501073
theorem B1000727 : Blo 666309 1000727 := bstep (se 1 (by rfl) ⟨750545, by rfl⟩ : syracuseStep 1000727 = 1501091) B1501091
theorem B1000793 : Blo 666309 1000793 := bstep (se 2 (by rfl) ⟨375297, by rfl⟩ : syracuseStep 1000793 = 750595) B750595
theorem B1688921 : Blo 666309 1688921 := bstep (se 2 (by rfl) ⟨633345, by rfl⟩ : syracuseStep 1688921 = 1266691) B1266691
theorem B1000907 : Blo 666309 1000907 := bstep (se 1 (by rfl) ⟨750680, by rfl⟩ : syracuseStep 1000907 = 1501361) B1501361
theorem B902603 : Blo 666309 902603 := bstep (se 1 (by rfl) ⟨676952, by rfl⟩ : syracuseStep 902603 = 1353905) B1353905
theorem B1000919 : Blo 666309 1000919 := bstep (se 1 (by rfl) ⟨750689, by rfl⟩ : syracuseStep 1000919 = 1501379) B1501379
theorem B1426967 : Blo 666309 1426967 := bstep (se 1 (by rfl) ⟨1070225, by rfl⟩ : syracuseStep 1426967 = 2140451) B2140451
theorem B1000985 : Blo 666309 1000985 := bstep (se 2 (by rfl) ⟨375369, by rfl⟩ : syracuseStep 1000985 = 750739) B750739
theorem B3393089 : Blo 666309 3393089 := bstep (se 2 (by rfl) ⟨1272408, by rfl⟩ : syracuseStep 3393089 = 2544817) B2544817
theorem B1001099 : Blo 666309 1001099 := bstep (se 1 (by rfl) ⟨750824, by rfl⟩ : syracuseStep 1001099 = 1501649) B1501649
theorem B1001111 : Blo 666309 1001111 := bstep (se 1 (by rfl) ⟨750833, by rfl⟩ : syracuseStep 1001111 = 1501667) B1501667
theorem B2705069 : Blo 666309 2705069 := bstep (se 3 (by rfl) ⟨507200, by rfl⟩ : syracuseStep 2705069 = 1014401) B1014401
theorem B1001177 : Blo 666309 1001177 := bstep (se 2 (by rfl) ⟨375441, by rfl⟩ : syracuseStep 1001177 = 750883) B750883
theorem B1001291 : Blo 666309 1001291 := bstep (se 1 (by rfl) ⟨750968, by rfl⟩ : syracuseStep 1001291 = 1501937) B1501937
theorem B1001303 : Blo 666309 1001303 := bstep (se 1 (by rfl) ⟨750977, by rfl⟩ : syracuseStep 1001303 = 1501955) B1501955
theorem B2541401 : Blo 666309 2541401 := bstep (se 2 (by rfl) ⟨953025, by rfl⟩ : syracuseStep 2541401 = 1906051) B1906051
theorem B1001369 : Blo 666309 1001369 := bstep (se 2 (by rfl) ⟨375513, by rfl⟩ : syracuseStep 1001369 = 751027) B751027
theorem B8112089 : Blo 666309 8112089 := bstep (se 2 (by rfl) ⟨3042033, by rfl⟩ : syracuseStep 8112089 = 6084067) B6084067
theorem B1001483 : Blo 666309 1001483 := bstep (se 1 (by rfl) ⟨751112, by rfl⟩ : syracuseStep 1001483 = 1502225) B1502225
theorem B23152661 : Blo 666309 23152661 := bstep (se 6 (by rfl) ⟨542640, by rfl⟩ : syracuseStep 23152661 = 1085281) B1085281
theorem B1001495 : Blo 666309 1001495 := bstep (se 1 (by rfl) ⟨751121, by rfl⟩ : syracuseStep 1001495 = 1502243) B1502243
theorem B1001561 : Blo 666309 1001561 := bstep (se 2 (by rfl) ⟨375585, by rfl⟩ : syracuseStep 1001561 = 751171) B751171
theorem B4278365 : Blo 666309 4278365 := bstep (se 3 (by rfl) ⟨802193, by rfl⟩ : syracuseStep 4278365 = 1604387) B1604387
theorem B2541719 : Blo 666309 2541719 := bstep (se 1 (by rfl) ⟨1906289, by rfl⟩ : syracuseStep 2541719 = 3812579) B3812579
theorem B1001675 : Blo 666309 1001675 := bstep (se 1 (by rfl) ⟨751256, by rfl⟩ : syracuseStep 1001675 = 1502513) B1502513
theorem B1001687 : Blo 666309 1001687 := bstep (se 1 (by rfl) ⟨751265, by rfl⟩ : syracuseStep 1001687 = 1502531) B1502531
theorem B1001753 : Blo 666309 1001753 := bstep (se 2 (by rfl) ⟨375657, by rfl⟩ : syracuseStep 1001753 = 751315) B751315
theorem B7620965 : Blo 666309 7620965 := bstep (se 4 (by rfl) ⟨714465, by rfl⟩ : syracuseStep 7620965 = 1428931) B1428931
theorem B5065091 : Blo 666309 5065091 := bstep (se 1 (by rfl) ⟨3798818, by rfl⟩ : syracuseStep 5065091 = 7597637) B7597637
theorem B1001867 : Blo 666309 1001867 := bstep (se 1 (by rfl) ⟨751400, by rfl⟩ : syracuseStep 1001867 = 1502801) B1502801
theorem B1001879 : Blo 666309 1001879 := bstep (se 1 (by rfl) ⟨751409, by rfl⟩ : syracuseStep 1001879 = 1502819) B1502819
theorem B2279897 : Blo 666309 2279897 := bstep (se 2 (by rfl) ⟨854961, by rfl⟩ : syracuseStep 2279897 = 1709923) B1709923
theorem B1001945 : Blo 666309 1001945 := bstep (se 2 (by rfl) ⟨375729, by rfl⟩ : syracuseStep 1001945 = 751459) B751459
theorem B1002059 : Blo 666309 1002059 := bstep (se 1 (by rfl) ⟨751544, by rfl⟩ : syracuseStep 1002059 = 1503089) B1503089
theorem B1428043 : Blo 666309 1428043 := bstep (se 1 (by rfl) ⟨1071032, by rfl⟩ : syracuseStep 1428043 = 2142065) B2142065
theorem B1002071 : Blo 666309 1002071 := bstep (se 1 (by rfl) ⟨751553, by rfl⟩ : syracuseStep 1002071 = 1503107) B1503107
theorem B1002137 : Blo 666309 1002137 := bstep (se 2 (by rfl) ⟨375801, by rfl⟩ : syracuseStep 1002137 = 751603) B751603
theorem B1624769 : Blo 666309 1624769 := bstep (se 2 (by rfl) ⟨609288, by rfl⟩ : syracuseStep 1624769 = 1218577) B1218577
theorem B1002251 : Blo 666309 1002251 := bstep (se 1 (by rfl) ⟨751688, by rfl⟩ : syracuseStep 1002251 = 1503377) B1503377
theorem B1002263 : Blo 666309 1002263 := bstep (se 1 (by rfl) ⟨751697, by rfl⟩ : syracuseStep 1002263 = 1503395) B1503395
theorem B2542387 : Blo 666309 2542387 := bstep (se 1 (by rfl) ⟨1906790, by rfl⟩ : syracuseStep 2542387 = 3813581) B3813581
theorem B2280257 : Blo 666309 2280257 := bstep (se 2 (by rfl) ⟨855096, by rfl⟩ : syracuseStep 2280257 = 1710193) B1710193
theorem B1002329 : Blo 666309 1002329 := bstep (se 2 (by rfl) ⟨375873, by rfl⟩ : syracuseStep 1002329 = 751747) B751747
theorem B1690571 : Blo 666309 1690571 := bstep (se 1 (by rfl) ⟨1267928, by rfl⟩ : syracuseStep 1690571 = 2535857) B2535857
theorem B1002443 : Blo 666309 1002443 := bstep (se 1 (by rfl) ⟨751832, by rfl⟩ : syracuseStep 1002443 = 1503665) B1503665
theorem B1002455 : Blo 666309 1002455 := bstep (se 1 (by rfl) ⟨751841, by rfl⟩ : syracuseStep 1002455 = 1503683) B1503683
theorem B1002521 : Blo 666309 1002521 := bstep (se 2 (by rfl) ⟨375945, by rfl⟩ : syracuseStep 1002521 = 751891) B751891
theorem B1002635 : Blo 666309 1002635 := bstep (se 1 (by rfl) ⟨751976, by rfl⟩ : syracuseStep 1002635 = 1503953) B1503953
theorem B1002647 : Blo 666309 1002647 := bstep (se 1 (by rfl) ⟨751985, by rfl⟩ : syracuseStep 1002647 = 1503971) B1503971
theorem B1002713 : Blo 666309 1002713 := bstep (se 2 (by rfl) ⟨376017, by rfl⟩ : syracuseStep 1002713 = 752035) B752035
theorem B1428761 : Blo 666309 1428761 := bstep (se 2 (by rfl) ⟨535785, by rfl⟩ : syracuseStep 1428761 = 1071571) B1071571
theorem B5295395 : Blo 666309 5295395 := bstep (se 1 (by rfl) ⟨3971546, by rfl⟩ : syracuseStep 5295395 = 7943093) B7943093
theorem B1002827 : Blo 666309 1002827 := bstep (se 1 (by rfl) ⟨752120, by rfl⟩ : syracuseStep 1002827 = 1504241) B1504241
theorem B1002839 : Blo 666309 1002839 := bstep (se 1 (by rfl) ⟨752129, by rfl⟩ : syracuseStep 1002839 = 1504259) B1504259
theorem B1002905 : Blo 666309 1002905 := bstep (se 2 (by rfl) ⟨376089, by rfl⟩ : syracuseStep 1002905 = 752179) B752179
theorem B4804019 : Blo 666309 4804019 := bstep (se 1 (by rfl) ⟨3603014, by rfl⟩ : syracuseStep 4804019 = 7206029) B7206029
theorem B4574681 : Blo 666309 4574681 := bstep (se 2 (by rfl) ⟨1715505, by rfl⟩ : syracuseStep 4574681 = 3431011) B3431011
theorem B1003019 : Blo 666309 1003019 := bstep (se 1 (by rfl) ⟨752264, by rfl⟩ : syracuseStep 1003019 = 1504529) B1504529
theorem B1003031 : Blo 666309 1003031 := bstep (se 1 (by rfl) ⟨752273, by rfl⟩ : syracuseStep 1003031 = 1504547) B1504547
theorem B1003097 : Blo 666309 1003097 := bstep (se 2 (by rfl) ⟨376161, by rfl⟩ : syracuseStep 1003097 = 752323) B752323
theorem B1003211 : Blo 666309 1003211 := bstep (se 1 (by rfl) ⟨752408, by rfl⟩ : syracuseStep 1003211 = 1504817) B1504817
theorem B1003223 : Blo 666309 1003223 := bstep (se 1 (by rfl) ⟨752417, by rfl⟩ : syracuseStep 1003223 = 1504835) B1504835
theorem B1003289 : Blo 666309 1003289 := bstep (se 2 (by rfl) ⟨376233, by rfl⟩ : syracuseStep 1003289 = 752467) B752467
theorem B1429273 : Blo 666309 1429273 := bstep (se 2 (by rfl) ⟨535977, by rfl⟩ : syracuseStep 1429273 = 1071955) B1071955
theorem B1265483 : Blo 666309 1265483 := bstep (se 1 (by rfl) ⟨949112, by rfl⟩ : syracuseStep 1265483 = 1898225) B1898225
theorem B1265537 : Blo 666309 1265537 := bstep (se 2 (by rfl) ⟨474576, by rfl⟩ : syracuseStep 1265537 = 949153) B949153
theorem B1003403 : Blo 666309 1003403 := bstep (se 1 (by rfl) ⟨752552, by rfl⟩ : syracuseStep 1003403 = 1505105) B1505105
theorem B1691543 : Blo 666309 1691543 := bstep (se 1 (by rfl) ⟨1268657, by rfl⟩ : syracuseStep 1691543 = 2537315) B2537315
theorem B1003415 : Blo 666309 1003415 := bstep (se 1 (by rfl) ⟨752561, by rfl⟩ : syracuseStep 1003415 = 1505123) B1505123
theorem B1429427 : Blo 666309 1429427 := bstep (se 1 (by rfl) ⟨1072070, by rfl⟩ : syracuseStep 1429427 = 2144141) B2144141
theorem B1003481 : Blo 666309 1003481 := bstep (se 2 (by rfl) ⟨376305, by rfl⟩ : syracuseStep 1003481 = 752611) B752611
theorem B2543633 : Blo 666309 2543633 := bstep (se 2 (by rfl) ⟨953862, by rfl⟩ : syracuseStep 2543633 = 1907725) B1907725
theorem B1003595 : Blo 666309 1003595 := bstep (se 1 (by rfl) ⟨752696, by rfl⟩ : syracuseStep 1003595 = 1505393) B1505393
theorem B1003607 : Blo 666309 1003607 := bstep (se 1 (by rfl) ⟨752705, by rfl⟩ : syracuseStep 1003607 = 1505411) B1505411
theorem B1527959 : Blo 666309 1527959 := bstep (se 1 (by rfl) ⟨1145969, by rfl⟩ : syracuseStep 1527959 = 2291939) B2291939
theorem B1003673 : Blo 666309 1003673 := bstep (se 2 (by rfl) ⟨376377, by rfl⟩ : syracuseStep 1003673 = 752755) B752755
theorem B2248883 : Blo 666309 2248883 := bstep (se 1 (by rfl) ⟨1686662, by rfl⟩ : syracuseStep 2248883 = 3373325) B3373325
theorem B1003787 : Blo 666309 1003787 := bstep (se 1 (by rfl) ⟨752840, by rfl⟩ : syracuseStep 1003787 = 1505681) B1505681
theorem B1003799 : Blo 666309 1003799 := bstep (se 1 (by rfl) ⟨752849, by rfl⟩ : syracuseStep 1003799 = 1505699) B1505699
theorem B1003865 : Blo 666309 1003865 := bstep (se 2 (by rfl) ⟨376449, by rfl⟩ : syracuseStep 1003865 = 752899) B752899
theorem B2249153 : Blo 666309 2249153 := bstep (se 2 (by rfl) ⟨843432, by rfl⟩ : syracuseStep 2249153 = 1686865) B1686865
theorem B1003979 : Blo 666309 1003979 := bstep (se 1 (by rfl) ⟨752984, by rfl⟩ : syracuseStep 1003979 = 1505969) B1505969
theorem B1003991 : Blo 666309 1003991 := bstep (se 1 (by rfl) ⟨752993, by rfl⟩ : syracuseStep 1003991 = 1505987) B1505987
theorem B4280849 : Blo 666309 4280849 := bstep (se 2 (by rfl) ⟨1605318, by rfl⟩ : syracuseStep 4280849 = 3210637) B3210637
theorem B1004057 : Blo 666309 1004057 := bstep (se 2 (by rfl) ⟨376521, by rfl⟩ : syracuseStep 1004057 = 753043) B753043
theorem B1692211 : Blo 666309 1692211 := bstep (se 1 (by rfl) ⟨1269158, by rfl⟩ : syracuseStep 1692211 = 2538317) B2538317
theorem B1004171 : Blo 666309 1004171 := bstep (se 1 (by rfl) ⟨753128, by rfl⟩ : syracuseStep 1004171 = 1506257) B1506257
theorem B1004183 : Blo 666309 1004183 := bstep (se 1 (by rfl) ⟨753137, by rfl⟩ : syracuseStep 1004183 = 1506275) B1506275
theorem B1692353 : Blo 666309 1692353 := bstep (se 2 (by rfl) ⟨634632, by rfl⟩ : syracuseStep 1692353 = 1269265) B1269265
theorem B2544331 : Blo 666309 2544331 := bstep (se 1 (by rfl) ⟨1908248, by rfl⟩ : syracuseStep 2544331 = 3816497) B3816497
theorem B1004249 : Blo 666309 1004249 := bstep (se 2 (by rfl) ⟨376593, by rfl⟩ : syracuseStep 1004249 = 753187) B753187
theorem B5788421 : Blo 666309 5788421 := bstep (se 4 (by rfl) ⟨542664, by rfl⟩ : syracuseStep 5788421 = 1085329) B1085329
theorem B1266455 : Blo 666309 1266455 := bstep (se 1 (by rfl) ⟨949841, by rfl⟩ : syracuseStep 1266455 = 1899683) B1899683
theorem B5133091 : Blo 666309 5133091 := bstep (se 1 (by rfl) ⟨3849818, by rfl⟩ : syracuseStep 5133091 = 7699637) B7699637
theorem B1004363 : Blo 666309 1004363 := bstep (se 1 (by rfl) ⟨753272, by rfl⟩ : syracuseStep 1004363 = 1506545) B1506545
theorem B1004375 : Blo 666309 1004375 := bstep (se 1 (by rfl) ⟨753281, by rfl⟩ : syracuseStep 1004375 = 1506563) B1506563
theorem B1430401 : Blo 666309 1430401 := bstep (se 2 (by rfl) ⟨536400, by rfl⟩ : syracuseStep 1430401 = 1072801) B1072801
theorem B1004441 : Blo 666309 1004441 := bstep (se 2 (by rfl) ⟨376665, by rfl⟩ : syracuseStep 1004441 = 753331) B753331
theorem B2249693 : Blo 666309 2249693 := bstep (se 3 (by rfl) ⟨421817, by rfl⟩ : syracuseStep 2249693 = 843635) B843635
theorem B2544605 : Blo 666309 2544605 := bstep (se 3 (by rfl) ⟨477113, by rfl⟩ : syracuseStep 2544605 = 954227) B954227
theorem B1201163 : Blo 666309 1201163 := bstep (se 1 (by rfl) ⟨900872, by rfl⟩ : syracuseStep 1201163 = 1801745) B1801745
theorem B1004555 : Blo 666309 1004555 := bstep (se 1 (by rfl) ⟨753416, by rfl⟩ : syracuseStep 1004555 = 1506833) B1506833
theorem B1004567 : Blo 666309 1004567 := bstep (se 1 (by rfl) ⟨753425, by rfl⟩ : syracuseStep 1004567 = 1506851) B1506851
theorem B1004633 : Blo 666309 1004633 := bstep (se 2 (by rfl) ⟨376737, by rfl⟩ : syracuseStep 1004633 = 753475) B753475
theorem B1004747 : Blo 666309 1004747 := bstep (se 1 (by rfl) ⟨753560, by rfl⟩ : syracuseStep 1004747 = 1507121) B1507121
theorem B1004759 : Blo 666309 1004759 := bstep (se 1 (by rfl) ⟨753569, by rfl⟩ : syracuseStep 1004759 = 1507139) B1507139
theorem B1430743 : Blo 666309 1430743 := bstep (se 1 (by rfl) ⟨1073057, by rfl⟩ : syracuseStep 1430743 = 2146115) B2146115
theorem B4871441 : Blo 666309 4871441 := bstep (se 2 (by rfl) ⟨1826790, by rfl⟩ : syracuseStep 4871441 = 3653581) B3653581
theorem B1004825 : Blo 666309 1004825 := bstep (se 2 (by rfl) ⟨376809, by rfl⟩ : syracuseStep 1004825 = 753619) B753619
theorem B1266995 : Blo 666309 1266995 := bstep (se 1 (by rfl) ⟨950246, by rfl⟩ : syracuseStep 1266995 = 1900493) B1900493
theorem B3429697 : Blo 666309 3429697 := bstep (se 2 (by rfl) ⟨1286136, by rfl⟩ : syracuseStep 3429697 = 2572273) B2572273
theorem B21976433 : Blo 666309 21976433 := bstep (se 2 (by rfl) ⟨8241162, by rfl⟩ : syracuseStep 21976433 = 16482325) B16482325
theorem B1004939 : Blo 666309 1004939 := bstep (se 1 (by rfl) ⟨753704, by rfl⟩ : syracuseStep 1004939 = 1507409) B1507409
theorem B1004951 : Blo 666309 1004951 := bstep (se 1 (by rfl) ⟨753713, by rfl⟩ : syracuseStep 1004951 = 1507427) B1507427
theorem B1201625 : Blo 666309 1201625 := bstep (se 2 (by rfl) ⟨450609, by rfl⟩ : syracuseStep 1201625 = 901219) B901219
theorem B6411737 : Blo 666309 6411737 := bstep (se 2 (by rfl) ⟨2404401, by rfl⟩ : syracuseStep 6411737 = 4808803) B4808803
theorem B1005017 : Blo 666309 1005017 := bstep (se 2 (by rfl) ⟨376881, by rfl⟩ : syracuseStep 1005017 = 753763) B753763
theorem B1005131 : Blo 666309 1005131 := bstep (se 1 (by rfl) ⟨753848, by rfl⟩ : syracuseStep 1005131 = 1507697) B1507697
theorem B1005143 : Blo 666309 1005143 := bstep (se 1 (by rfl) ⟨753857, by rfl⟩ : syracuseStep 1005143 = 1507715) B1507715
theorem B1431179 : Blo 666309 1431179 := bstep (se 1 (by rfl) ⟨1073384, by rfl⟩ : syracuseStep 1431179 = 2146769) B2146769
theorem B1005209 : Blo 666309 1005209 := bstep (se 2 (by rfl) ⟨376953, by rfl⟩ : syracuseStep 1005209 = 753907) B753907
theorem B1005259 : Blo 666309 1005259 := bstep (se 1 (by rfl) ⟨753944, by rfl⟩ : syracuseStep 1005259 = 1507889) B1507889
theorem B5068493 : Blo 666309 5068493 := bstep (se 3 (by rfl) ⟨950342, by rfl⟩ : syracuseStep 5068493 = 1900685) B1900685
theorem B1005323 : Blo 666309 1005323 := bstep (se 1 (by rfl) ⟨753992, by rfl⟩ : syracuseStep 1005323 = 1507985) B1507985
theorem B1005335 : Blo 666309 1005335 := bstep (se 1 (by rfl) ⟨754001, by rfl⟩ : syracuseStep 1005335 = 1508003) B1508003
theorem B1267481 : Blo 666309 1267481 := bstep (se 2 (by rfl) ⟨475305, by rfl⟩ : syracuseStep 1267481 = 950611) B950611
theorem B1300313 : Blo 666309 1300313 := bstep (se 2 (by rfl) ⟨487617, by rfl⟩ : syracuseStep 1300313 = 975235) B975235
theorem B1005401 : Blo 666309 1005401 := bstep (se 2 (by rfl) ⟨377025, by rfl⟩ : syracuseStep 1005401 = 754051) B754051
theorem B1693619 : Blo 666309 1693619 := bstep (se 1 (by rfl) ⟨1270214, by rfl⟩ : syracuseStep 1693619 = 2540429) B2540429
theorem B2414539 : Blo 666309 2414539 := bstep (se 1 (by rfl) ⟨1810904, by rfl⟩ : syracuseStep 2414539 = 3621809) B3621809
theorem B1071065 : Blo 666309 1071065 := bstep (se 2 (by rfl) ⟨401649, by rfl⟩ : syracuseStep 1071065 = 803299) B803299
theorem B2250827 : Blo 666309 2250827 := bstep (se 1 (by rfl) ⟨1688120, by rfl⟩ : syracuseStep 2250827 = 3376241) B3376241
theorem B5068979 : Blo 666309 5068979 := bstep (se 1 (by rfl) ⟨3801734, by rfl⟩ : syracuseStep 5068979 = 7603469) B7603469
theorem B1202483 : Blo 666309 1202483 := bstep (se 1 (by rfl) ⟨901862, by rfl⟩ : syracuseStep 1202483 = 1803725) B1803725
theorem B2251097 : Blo 666309 2251097 := bstep (se 2 (by rfl) ⟨844161, by rfl⟩ : syracuseStep 2251097 = 1688323) B1688323
theorem B1694155 : Blo 666309 1694155 := bstep (se 1 (by rfl) ⟨1270616, by rfl⟩ : syracuseStep 1694155 = 2541233) B2541233
theorem B1694297 : Blo 666309 1694297 := bstep (se 2 (by rfl) ⟨635361, by rfl⟩ : syracuseStep 1694297 = 1270723) B1270723
theorem B1203211 : Blo 666309 1203211 := bstep (se 1 (by rfl) ⟨902408, by rfl⟩ : syracuseStep 1203211 = 1804817) B1804817
theorem B2251799 : Blo 666309 2251799 := bstep (se 1 (by rfl) ⟨1688849, by rfl⟩ : syracuseStep 2251799 = 3377699) B3377699
theorem B1268939 : Blo 666309 1268939 := bstep (se 1 (by rfl) ⟨951704, by rfl⟩ : syracuseStep 1268939 = 1903409) B1903409
theorem B679223 : Blo 666309 679223 := bstep (se 1 (by rfl) ⟨509417, by rfl⟩ : syracuseStep 679223 = 1018835) B1018835
theorem B1269121 : Blo 666309 1269121 := bstep (se 2 (by rfl) ⟨475920, by rfl⟩ : syracuseStep 1269121 = 951841) B951841
theorem B1695127 : Blo 666309 1695127 := bstep (se 1 (by rfl) ⟨1271345, by rfl⟩ : syracuseStep 1695127 = 2542691) B2542691
theorem B1203673 : Blo 666309 1203673 := bstep (se 2 (by rfl) ⟨451377, by rfl⟩ : syracuseStep 1203673 = 902755) B902755
theorem B2252339 : Blo 666309 2252339 := bstep (se 1 (by rfl) ⟨1689254, by rfl⟩ : syracuseStep 2252339 = 3378509) B3378509
theorem B5693003 : Blo 666309 5693003 := bstep (se 1 (by rfl) ⟨4269752, by rfl⟩ : syracuseStep 5693003 = 8539505) B8539505
theorem B5070437 : Blo 666309 5070437 := bstep (se 4 (by rfl) ⟨475353, by rfl⟩ : syracuseStep 5070437 = 950707) B950707
theorem B5791493 : Blo 666309 5791493 := bstep (se 4 (by rfl) ⟨542952, by rfl⟩ : syracuseStep 5791493 = 1085905) B1085905
theorem B2252609 : Blo 666309 2252609 := bstep (se 2 (by rfl) ⟨844728, by rfl⟩ : syracuseStep 2252609 = 1689457) B1689457
theorem B1269569 : Blo 666309 1269569 := bstep (se 2 (by rfl) ⟨476088, by rfl⟩ : syracuseStep 1269569 = 952177) B952177
theorem B1695563 : Blo 666309 1695563 := bstep (se 1 (by rfl) ⟨1271672, by rfl⟩ : syracuseStep 1695563 = 2543345) B2543345
theorem B712535 : Blo 666309 712535 := bstep (se 1 (by rfl) ⟨534401, by rfl⟩ : syracuseStep 712535 = 1068803) B1068803
theorem B843787 : Blo 666309 843787 := bstep (se 1 (by rfl) ⟨632840, by rfl⟩ : syracuseStep 843787 = 1265681) B1265681
theorem B1204249 : Blo 666309 1204249 := bstep (se 2 (by rfl) ⟨451593, by rfl⟩ : syracuseStep 1204249 = 903187) B903187
theorem B24404003 : Blo 666309 24404003 := bstep (se 1 (by rfl) ⟨18303002, by rfl⟩ : syracuseStep 24404003 = 36606005) B36606005
theorem B2711603 : Blo 666309 2711603 := bstep (se 1 (by rfl) ⟨2033702, by rfl⟩ : syracuseStep 2711603 = 4067405) B4067405
theorem B1499201 : Blo 666309 1499201 := bstep (se 2 (by rfl) ⟨562200, by rfl⟩ : syracuseStep 1499201 = 1124401) B1124401
theorem B5070923 : Blo 666309 5070923 := bstep (se 1 (by rfl) ⟨3803192, by rfl⟩ : syracuseStep 5070923 = 7606385) B7606385
theorem B1269911 : Blo 666309 1269911 := bstep (se 1 (by rfl) ⟨952433, by rfl⟩ : syracuseStep 1269911 = 1904867) B1904867
theorem B1695937 : Blo 666309 1695937 := bstep (se 2 (by rfl) ⟨635976, by rfl⟩ : syracuseStep 1695937 = 1271953) B1271953
theorem B1499417 : Blo 666309 1499417 := bstep (se 2 (by rfl) ⟨562281, by rfl⟩ : syracuseStep 1499417 = 1124563) B1124563
theorem B2253149 : Blo 666309 2253149 := bstep (se 3 (by rfl) ⟨422465, by rfl⟩ : syracuseStep 2253149 = 844931) B844931
theorem B1499507 : Blo 666309 1499507 := bstep (se 1 (by rfl) ⟨1124630, by rfl⟩ : syracuseStep 1499507 = 2249261) B2249261
theorem B1499543 : Blo 666309 1499543 := bstep (se 1 (by rfl) ⟨1124657, by rfl⟩ : syracuseStep 1499543 = 2249315) B2249315
theorem B5497267 : Blo 666309 5497267 := bstep (se 1 (by rfl) ⟨4122950, by rfl⟩ : syracuseStep 5497267 = 8245901) B8245901
theorem B3203545 : Blo 666309 3203545 := bstep (se 2 (by rfl) ⟨1201329, by rfl⟩ : syracuseStep 3203545 = 2402659) B2402659
theorem B1499723 : Blo 666309 1499723 := bstep (se 1 (by rfl) ⟨1124792, by rfl⟩ : syracuseStep 1499723 = 2249585) B2249585
theorem B1499777 : Blo 666309 1499777 := bstep (se 2 (by rfl) ⟨562416, by rfl⟩ : syracuseStep 1499777 = 1124833) B1124833
theorem B1172183 : Blo 666309 1172183 := bstep (se 1 (by rfl) ⟨879137, by rfl⟩ : syracuseStep 1172183 = 1758275) B1758275
theorem B1696535 : Blo 666309 1696535 := bstep (se 1 (by rfl) ⟨1272401, by rfl⟩ : syracuseStep 1696535 = 2544803) B2544803
theorem B1270579 : Blo 666309 1270579 := bstep (se 1 (by rfl) ⟨952934, by rfl⟩ : syracuseStep 1270579 = 1905869) B1905869
theorem B1205057 : Blo 666309 1205057 := bstep (se 2 (by rfl) ⟨451896, by rfl⟩ : syracuseStep 1205057 = 903793) B903793
theorem B1499993 : Blo 666309 1499993 := bstep (se 2 (by rfl) ⟨562497, by rfl⟩ : syracuseStep 1499993 = 1124995) B1124995
theorem B1500083 : Blo 666309 1500083 := bstep (se 1 (by rfl) ⟨1125062, by rfl⟩ : syracuseStep 1500083 = 2250125) B2250125
theorem B1500119 : Blo 666309 1500119 := bstep (se 1 (by rfl) ⟨1125089, by rfl⟩ : syracuseStep 1500119 = 2250179) B2250179
theorem B844759 : Blo 666309 844759 := bstep (se 1 (by rfl) ⟨633569, by rfl⟩ : syracuseStep 844759 = 1267139) B1267139
theorem B1205273 : Blo 666309 1205273 := bstep (se 2 (by rfl) ⟨451977, by rfl⟩ : syracuseStep 1205273 = 903955) B903955
theorem B3204161 : Blo 666309 3204161 := bstep (se 2 (by rfl) ⟨1201560, by rfl⟩ : syracuseStep 3204161 = 2403121) B2403121
theorem B1500299 : Blo 666309 1500299 := bstep (se 1 (by rfl) ⟨1125224, by rfl⟩ : syracuseStep 1500299 = 2250449) B2250449
theorem B1500353 : Blo 666309 1500353 := bstep (se 2 (by rfl) ⟨562632, by rfl⟩ : syracuseStep 1500353 = 1125265) B1125265
theorem B1271027 : Blo 666309 1271027 := bstep (se 1 (by rfl) ⟨953270, by rfl⟩ : syracuseStep 1271027 = 1906541) B1906541
theorem B1271065 : Blo 666309 1271065 := bstep (se 2 (by rfl) ⟨476649, by rfl⟩ : syracuseStep 1271065 = 953299) B953299
theorem B5432611 : Blo 666309 5432611 := bstep (se 1 (by rfl) ⟨4074458, by rfl⟩ : syracuseStep 5432611 = 8148917) B8148917
theorem B1500569 : Blo 666309 1500569 := bstep (se 2 (by rfl) ⟨562713, by rfl⟩ : syracuseStep 1500569 = 1125427) B1125427
theorem B2254283 : Blo 666309 2254283 := bstep (se 1 (by rfl) ⟨1690712, by rfl⟩ : syracuseStep 2254283 = 3381425) B3381425
theorem B1500659 : Blo 666309 1500659 := bstep (se 1 (by rfl) ⟨1125494, by rfl⟩ : syracuseStep 1500659 = 2250989) B2250989
theorem B1500695 : Blo 666309 1500695 := bstep (se 1 (by rfl) ⟨1125521, by rfl⟩ : syracuseStep 1500695 = 2251043) B2251043
theorem B5137955 : Blo 666309 5137955 := bstep (se 1 (by rfl) ⟨3853466, by rfl⟩ : syracuseStep 5137955 = 7706933) B7706933
theorem B714295 : Blo 666309 714295 := bstep (se 1 (by rfl) ⟨535721, by rfl⟩ : syracuseStep 714295 = 1071443) B1071443
theorem B1500875 : Blo 666309 1500875 := bstep (se 1 (by rfl) ⟨1125656, by rfl⟩ : syracuseStep 1500875 = 2251313) B2251313
theorem B2254553 : Blo 666309 2254553 := bstep (se 2 (by rfl) ⟨845457, by rfl⟩ : syracuseStep 2254553 = 1690915) B1690915
theorem B1271513 : Blo 666309 1271513 := bstep (se 2 (by rfl) ⟨476817, by rfl⟩ : syracuseStep 1271513 = 953635) B953635
theorem B1500929 : Blo 666309 1500929 := bstep (se 2 (by rfl) ⟨562848, by rfl⟩ : syracuseStep 1500929 = 1125697) B1125697
theorem B845579 : Blo 666309 845579 := bstep (se 1 (by rfl) ⟨634184, by rfl⟩ : syracuseStep 845579 = 1268369) B1268369
theorem B1501145 : Blo 666309 1501145 := bstep (se 2 (by rfl) ⟨562929, by rfl⟩ : syracuseStep 1501145 = 1125859) B1125859
theorem B1501235 : Blo 666309 1501235 := bstep (se 1 (by rfl) ⟨1125926, by rfl⟩ : syracuseStep 1501235 = 2251853) B2251853
theorem B1501271 : Blo 666309 1501271 := bstep (se 1 (by rfl) ⟨1125953, by rfl⟩ : syracuseStep 1501271 = 2251907) B2251907
theorem B4810853 : Blo 666309 4810853 := bstep (se 4 (by rfl) ⟨451017, by rfl⟩ : syracuseStep 4810853 = 902035) B902035
theorem B1501451 : Blo 666309 1501451 := bstep (se 1 (by rfl) ⟨1126088, by rfl⟩ : syracuseStep 1501451 = 2252177) B2252177
theorem B1501505 : Blo 666309 1501505 := bstep (se 2 (by rfl) ⟨563064, by rfl⟩ : syracuseStep 1501505 = 1126129) B1126129
theorem B715115 : Blo 666309 715115 := bstep (se 1 (by rfl) ⟨536336, by rfl⟩ : syracuseStep 715115 = 1072673) B1072673
theorem B2255255 : Blo 666309 2255255 := bstep (se 1 (by rfl) ⟨1691441, by rfl⟩ : syracuseStep 2255255 = 3382883) B3382883
theorem B1272257 : Blo 666309 1272257 := bstep (se 2 (by rfl) ⟨477096, by rfl⟩ : syracuseStep 1272257 = 954193) B954193
theorem B846283 : Blo 666309 846283 := bstep (se 1 (by rfl) ⟨634712, by rfl⟩ : syracuseStep 846283 = 1269425) B1269425
theorem B1501721 : Blo 666309 1501721 := bstep (se 2 (by rfl) ⟨563145, by rfl⟩ : syracuseStep 1501721 = 1126291) B1126291
theorem B1206809 : Blo 666309 1206809 := bstep (se 2 (by rfl) ⟨452553, by rfl⟩ : syracuseStep 1206809 = 905107) B905107
theorem B1501811 : Blo 666309 1501811 := bstep (se 1 (by rfl) ⟨1126358, by rfl⟩ : syracuseStep 1501811 = 2252717) B2252717
theorem B1501847 : Blo 666309 1501847 := bstep (se 1 (by rfl) ⟨1126385, by rfl⟩ : syracuseStep 1501847 = 2252771) B2252771
theorem B1272523 : Blo 666309 1272523 := bstep (se 1 (by rfl) ⟨954392, by rfl⟩ : syracuseStep 1272523 = 1908785) B1908785
theorem B846551 : Blo 666309 846551 := bstep (se 1 (by rfl) ⟨634913, by rfl⟩ : syracuseStep 846551 = 1269827) B1269827
theorem B3435281 : Blo 666309 3435281 := bstep (se 2 (by rfl) ⟨1288230, by rfl⟩ : syracuseStep 3435281 = 2576461) B2576461
theorem B1502027 : Blo 666309 1502027 := bstep (se 1 (by rfl) ⟨1126520, by rfl⟩ : syracuseStep 1502027 = 2253041) B2253041
theorem B1502081 : Blo 666309 1502081 := bstep (se 2 (by rfl) ⟨563280, by rfl⟩ : syracuseStep 1502081 = 1126561) B1126561
theorem B2255795 : Blo 666309 2255795 := bstep (se 1 (by rfl) ⟨1691846, by rfl⟩ : syracuseStep 2255795 = 3383693) B3383693
theorem B1207219 : Blo 666309 1207219 := bstep (se 1 (by rfl) ⟨905414, by rfl⟩ : syracuseStep 1207219 = 1810829) B1810829
theorem B3042379 : Blo 666309 3042379 := bstep (se 1 (by rfl) ⟨2281784, by rfl⟩ : syracuseStep 3042379 = 4563569) B4563569
theorem B1502297 : Blo 666309 1502297 := bstep (se 2 (by rfl) ⟨563361, by rfl⟩ : syracuseStep 1502297 = 1126723) B1126723
theorem B2714717 : Blo 666309 2714717 := bstep (se 3 (by rfl) ⟨509009, by rfl⟩ : syracuseStep 2714717 = 1018019) B1018019
theorem B1502387 : Blo 666309 1502387 := bstep (se 1 (by rfl) ⟨1126790, by rfl⟩ : syracuseStep 1502387 = 2253581) B2253581
theorem B2256065 : Blo 666309 2256065 := bstep (se 2 (by rfl) ⟨846024, by rfl⟩ : syracuseStep 2256065 = 1692049) B1692049
theorem B1502423 : Blo 666309 1502423 := bstep (se 1 (by rfl) ⟨1126817, by rfl⟩ : syracuseStep 1502423 = 2253635) B2253635
theorem B1502603 : Blo 666309 1502603 := bstep (se 1 (by rfl) ⟨1126952, by rfl⟩ : syracuseStep 1502603 = 2253905) B2253905
theorem B847255 : Blo 666309 847255 := bstep (se 1 (by rfl) ⟨635441, by rfl⟩ : syracuseStep 847255 = 1270883) B1270883
theorem B4287923 : Blo 666309 4287923 := bstep (se 1 (by rfl) ⟨3215942, by rfl⟩ : syracuseStep 4287923 = 6431885) B6431885
theorem B1502657 : Blo 666309 1502657 := bstep (se 2 (by rfl) ⟨563496, by rfl⟩ : syracuseStep 1502657 = 1126993) B1126993
theorem B1601089 : Blo 666309 1601089 := bstep (se 2 (by rfl) ⟨600408, by rfl⟩ : syracuseStep 1601089 = 1200817) B1200817
theorem B1502873 : Blo 666309 1502873 := bstep (se 2 (by rfl) ⟨563577, by rfl⟩ : syracuseStep 1502873 = 1127155) B1127155
theorem B2256605 : Blo 666309 2256605 := bstep (se 3 (by rfl) ⟨423113, by rfl⟩ : syracuseStep 2256605 = 846227) B846227
theorem B1502963 : Blo 666309 1502963 := bstep (se 1 (by rfl) ⟨1127222, by rfl⟩ : syracuseStep 1502963 = 2254445) B2254445
theorem B1502999 : Blo 666309 1502999 := bstep (se 1 (by rfl) ⟨1127249, by rfl⟩ : syracuseStep 1502999 = 2254499) B2254499
theorem B6418277 : Blo 666309 6418277 := bstep (se 4 (by rfl) ⟨601713, by rfl⟩ : syracuseStep 6418277 = 1203427) B1203427
theorem B1503179 : Blo 666309 1503179 := bstep (se 1 (by rfl) ⟨1127384, by rfl⟩ : syracuseStep 1503179 = 2254769) B2254769
theorem B1503233 : Blo 666309 1503233 := bstep (se 2 (by rfl) ⟨563712, by rfl⟩ : syracuseStep 1503233 = 1127425) B1127425
theorem B1142795 : Blo 666309 1142795 := bstep (se 1 (by rfl) ⟨857096, by rfl⟩ : syracuseStep 1142795 = 1714193) B1714193
theorem B749623 : Blo 666309 749623 := bstep (se 1 (by rfl) ⟨562217, by rfl⟩ : syracuseStep 749623 = 1124435) B1124435
theorem B815243 : Blo 666309 815243 := bstep (se 1 (by rfl) ⟨611432, by rfl⟩ : syracuseStep 815243 = 1222865) B1222865
theorem B4944023 : Blo 666309 4944023 := bstep (se 1 (by rfl) ⟨3708017, by rfl⟩ : syracuseStep 4944023 = 7416035) B7416035
theorem B1503449 : Blo 666309 1503449 := bstep (se 2 (by rfl) ⟨563793, by rfl⟩ : syracuseStep 1503449 = 1127587) B1127587
theorem B749803 : Blo 666309 749803 := bstep (se 1 (by rfl) ⟨562352, by rfl⟩ : syracuseStep 749803 = 1124705) B1124705
theorem B1503539 : Blo 666309 1503539 := bstep (se 1 (by rfl) ⟨1127654, by rfl⟩ : syracuseStep 1503539 = 2255309) B2255309
theorem B749911 : Blo 666309 749911 := bstep (se 1 (by rfl) ⟨562433, by rfl⟩ : syracuseStep 749911 = 1124867) B1124867
theorem B1503575 : Blo 666309 1503575 := bstep (se 1 (by rfl) ⟨1127681, by rfl⟩ : syracuseStep 1503575 = 2255363) B2255363
theorem B750091 : Blo 666309 750091 := bstep (se 1 (by rfl) ⟨562568, by rfl⟩ : syracuseStep 750091 = 1125137) B1125137
theorem B1503755 : Blo 666309 1503755 := bstep (se 1 (by rfl) ⟨1127816, by rfl⟩ : syracuseStep 1503755 = 2255633) B2255633
theorem B6844945 : Blo 666309 6844945 := bstep (se 2 (by rfl) ⟨2566854, by rfl⟩ : syracuseStep 6844945 = 5133709) B5133709
theorem B1503809 : Blo 666309 1503809 := bstep (se 2 (by rfl) ⟨563928, by rfl⟩ : syracuseStep 1503809 = 1127857) B1127857
theorem B750199 : Blo 666309 750199 := bstep (se 1 (by rfl) ⟨562649, by rfl⟩ : syracuseStep 750199 = 1125299) B1125299
theorem B1504025 : Blo 666309 1504025 := bstep (se 2 (by rfl) ⟨564009, by rfl⟩ : syracuseStep 1504025 = 1128019) B1128019
theorem B750379 : Blo 666309 750379 := bstep (se 1 (by rfl) ⟨562784, by rfl⟩ : syracuseStep 750379 = 1125569) B1125569
theorem B2257739 : Blo 666309 2257739 := bstep (se 1 (by rfl) ⟨1693304, by rfl⟩ : syracuseStep 2257739 = 3386609) B3386609
theorem B815959 : Blo 666309 815959 := bstep (se 1 (by rfl) ⟨611969, by rfl⟩ : syracuseStep 815959 = 1223939) B1223939
theorem B5403485 : Blo 666309 5403485 := bstep (se 3 (by rfl) ⟨1013153, by rfl⟩ : syracuseStep 5403485 = 2026307) B2026307
theorem B1504115 : Blo 666309 1504115 := bstep (se 1 (by rfl) ⟨1128086, by rfl⟩ : syracuseStep 1504115 = 2256173) B2256173
theorem B750487 : Blo 666309 750487 := bstep (se 1 (by rfl) ⟨562865, by rfl⟩ : syracuseStep 750487 = 1125731) B1125731
theorem B1504151 : Blo 666309 1504151 := bstep (se 1 (by rfl) ⟨1128113, by rfl⟩ : syracuseStep 1504151 = 2256227) B2256227
theorem B750667 : Blo 666309 750667 := bstep (se 1 (by rfl) ⟨563000, by rfl⟩ : syracuseStep 750667 = 1126001) B1126001
theorem B1504331 : Blo 666309 1504331 := bstep (se 1 (by rfl) ⟨1128248, by rfl⟩ : syracuseStep 1504331 = 2256497) B2256497
theorem B2258009 : Blo 666309 2258009 := bstep (se 2 (by rfl) ⟨846753, by rfl⟩ : syracuseStep 2258009 = 1693507) B1693507
theorem B1504385 : Blo 666309 1504385 := bstep (se 2 (by rfl) ⟨564144, by rfl⟩ : syracuseStep 1504385 = 1128289) B1128289
theorem B750775 : Blo 666309 750775 := bstep (se 1 (by rfl) ⟨563081, by rfl⟩ : syracuseStep 750775 = 1126163) B1126163
theorem B5862617 : Blo 666309 5862617 := bstep (se 2 (by rfl) ⟨2198481, by rfl⟩ : syracuseStep 5862617 = 4396963) B4396963
theorem B5076269 : Blo 666309 5076269 := bstep (se 3 (by rfl) ⟨951800, by rfl⟩ : syracuseStep 5076269 = 1903601) B1903601
theorem B1897793 : Blo 666309 1897793 := bstep (se 2 (by rfl) ⟨711672, by rfl⟩ : syracuseStep 1897793 = 1423345) B1423345
theorem B1504601 : Blo 666309 1504601 := bstep (se 2 (by rfl) ⟨564225, by rfl⟩ : syracuseStep 1504601 = 1128451) B1128451
theorem B750955 : Blo 666309 750955 := bstep (se 1 (by rfl) ⟨563216, by rfl⟩ : syracuseStep 750955 = 1126433) B1126433
theorem B1504691 : Blo 666309 1504691 := bstep (se 1 (by rfl) ⟨1128518, by rfl⟩ : syracuseStep 1504691 = 2257037) B2257037
theorem B2848193 : Blo 666309 2848193 := bstep (se 2 (by rfl) ⟨1068072, by rfl⟩ : syracuseStep 2848193 = 2136145) B2136145
theorem B751063 : Blo 666309 751063 := bstep (se 1 (by rfl) ⟨563297, by rfl⟩ : syracuseStep 751063 = 1126595) B1126595
theorem B1504727 : Blo 666309 1504727 := bstep (se 1 (by rfl) ⟨1128545, by rfl⟩ : syracuseStep 1504727 = 2257091) B2257091
theorem B1144343 : Blo 666309 1144343 := bstep (se 1 (by rfl) ⟨858257, by rfl⟩ : syracuseStep 1144343 = 1716515) B1716515
theorem B751243 : Blo 666309 751243 := bstep (se 1 (by rfl) ⟨563432, by rfl⟩ : syracuseStep 751243 = 1126865) B1126865
theorem B1504907 : Blo 666309 1504907 := bstep (se 1 (by rfl) ⟨1128680, by rfl⟩ : syracuseStep 1504907 = 2257361) B2257361
theorem B1504961 : Blo 666309 1504961 := bstep (se 2 (by rfl) ⟨564360, by rfl⟩ : syracuseStep 1504961 = 1128721) B1128721
theorem B751351 : Blo 666309 751351 := bstep (se 1 (by rfl) ⟨563513, by rfl⟩ : syracuseStep 751351 = 1127027) B1127027
theorem B2258711 : Blo 666309 2258711 := bstep (se 1 (by rfl) ⟨1694033, by rfl⟩ : syracuseStep 2258711 = 3388067) B3388067
theorem B48887651 : Blo 666309 48887651 := bstep (se 1 (by rfl) ⟨36665738, by rfl⟩ : syracuseStep 48887651 = 73331477) B73331477
theorem B1505177 : Blo 666309 1505177 := bstep (se 2 (by rfl) ⟨564441, by rfl⟩ : syracuseStep 1505177 = 1128883) B1128883
theorem B751531 : Blo 666309 751531 := bstep (se 1 (by rfl) ⟨563648, by rfl⟩ : syracuseStep 751531 = 1127297) B1127297
theorem B11564977 : Blo 666309 11564977 := bstep (se 2 (by rfl) ⟨4336866, by rfl⟩ : syracuseStep 11564977 = 8673733) B8673733
theorem B3799001 : Blo 666309 3799001 := bstep (se 2 (by rfl) ⟨1424625, by rfl⟩ : syracuseStep 3799001 = 2849251) B2849251
theorem B1505267 : Blo 666309 1505267 := bstep (se 1 (by rfl) ⟨1128950, by rfl⟩ : syracuseStep 1505267 = 2257901) B2257901
theorem B751639 : Blo 666309 751639 := bstep (se 1 (by rfl) ⟨563729, by rfl⟩ : syracuseStep 751639 = 1127459) B1127459
theorem B1505303 : Blo 666309 1505303 := bstep (se 1 (by rfl) ⟨1128977, by rfl⟩ : syracuseStep 1505303 = 2257955) B2257955
theorem B686155 : Blo 666309 686155 := bstep (se 1 (by rfl) ⟨514616, by rfl⟩ : syracuseStep 686155 = 1029233) B1029233
theorem B1013963 : Blo 666309 1013963 := bstep (se 1 (by rfl) ⟨760472, by rfl⟩ : syracuseStep 1013963 = 1520945) B1520945
theorem B751819 : Blo 666309 751819 := bstep (se 1 (by rfl) ⟨563864, by rfl⟩ : syracuseStep 751819 = 1127729) B1127729
theorem B1505483 : Blo 666309 1505483 := bstep (se 1 (by rfl) ⟨1129112, by rfl⟩ : syracuseStep 1505483 = 2258225) B2258225
theorem B1505537 : Blo 666309 1505537 := bstep (se 2 (by rfl) ⟨564576, by rfl⟩ : syracuseStep 1505537 = 1129153) B1129153
theorem B7239941 : Blo 666309 7239941 := bstep (se 4 (by rfl) ⟨678744, by rfl⟩ : syracuseStep 7239941 = 1357489) B1357489
theorem B2259251 : Blo 666309 2259251 := bstep (se 1 (by rfl) ⟨1694438, by rfl⟩ : syracuseStep 2259251 = 3388877) B3388877
theorem B751927 : Blo 666309 751927 := bstep (se 1 (by rfl) ⟨563945, by rfl⟩ : syracuseStep 751927 = 1127891) B1127891
theorem B1505753 : Blo 666309 1505753 := bstep (se 2 (by rfl) ⟨564657, by rfl⟩ : syracuseStep 1505753 = 1129315) B1129315
theorem B752107 : Blo 666309 752107 := bstep (se 1 (by rfl) ⟨564080, by rfl⟩ : syracuseStep 752107 = 1128161) B1128161
theorem B1505843 : Blo 666309 1505843 := bstep (se 1 (by rfl) ⟨1129382, by rfl⟩ : syracuseStep 1505843 = 2258765) B2258765
theorem B2259521 : Blo 666309 2259521 := bstep (se 2 (by rfl) ⟨847320, by rfl⟩ : syracuseStep 2259521 = 1694641) B1694641
theorem B752215 : Blo 666309 752215 := bstep (se 1 (by rfl) ⟨564161, by rfl⟩ : syracuseStep 752215 = 1128323) B1128323
theorem B1505879 : Blo 666309 1505879 := bstep (se 1 (by rfl) ⟨1129409, by rfl⟩ : syracuseStep 1505879 = 2258819) B2258819
theorem B948953 : Blo 666309 948953 := bstep (se 2 (by rfl) ⟨355857, by rfl⟩ : syracuseStep 948953 = 711715) B711715
theorem B752395 : Blo 666309 752395 := bstep (se 1 (by rfl) ⟨564296, by rfl⟩ : syracuseStep 752395 = 1128593) B1128593
theorem B1506059 : Blo 666309 1506059 := bstep (se 1 (by rfl) ⟨1129544, by rfl⟩ : syracuseStep 1506059 = 2259089) B2259089
theorem B2030359 : Blo 666309 2030359 := bstep (se 1 (by rfl) ⟨1522769, by rfl⟩ : syracuseStep 2030359 = 3045539) B3045539
theorem B1506113 : Blo 666309 1506113 := bstep (se 2 (by rfl) ⟨564792, by rfl⟩ : syracuseStep 1506113 = 1129585) B1129585
theorem B1145689 : Blo 666309 1145689 := bstep (se 2 (by rfl) ⟨429633, by rfl⟩ : syracuseStep 1145689 = 859267) B859267
theorem B752503 : Blo 666309 752503 := bstep (se 1 (by rfl) ⟨564377, by rfl⟩ : syracuseStep 752503 = 1128755) B1128755
theorem B6421427 : Blo 666309 6421427 := bstep (se 1 (by rfl) ⟨4816070, by rfl⟩ : syracuseStep 6421427 = 9632141) B9632141
theorem B1506329 : Blo 666309 1506329 := bstep (se 2 (by rfl) ⟨564873, by rfl⟩ : syracuseStep 1506329 = 1129747) B1129747
theorem B752683 : Blo 666309 752683 := bstep (se 1 (by rfl) ⟨564512, by rfl⟩ : syracuseStep 752683 = 1129025) B1129025
theorem B2849867 : Blo 666309 2849867 := bstep (se 1 (by rfl) ⟨2137400, by rfl⟩ : syracuseStep 2849867 = 4274801) B4274801
theorem B2260061 : Blo 666309 2260061 := bstep (se 3 (by rfl) ⟨423761, by rfl⟩ : syracuseStep 2260061 = 847523) B847523
theorem B1506419 : Blo 666309 1506419 := bstep (se 1 (by rfl) ⟨1129814, by rfl⟩ : syracuseStep 1506419 = 2259629) B2259629
theorem B752791 : Blo 666309 752791 := bstep (se 1 (by rfl) ⟨564593, by rfl⟩ : syracuseStep 752791 = 1129187) B1129187
theorem B1506455 : Blo 666309 1506455 := bstep (se 1 (by rfl) ⟨1129841, by rfl⟩ : syracuseStep 1506455 = 2259683) B2259683
theorem B3374297 : Blo 666309 3374297 := bstep (se 2 (by rfl) ⟨1265361, by rfl⟩ : syracuseStep 3374297 = 2530723) B2530723
theorem B752971 : Blo 666309 752971 := bstep (se 1 (by rfl) ⟨564728, by rfl⟩ : syracuseStep 752971 = 1129457) B1129457
theorem B1506635 : Blo 666309 1506635 := bstep (se 1 (by rfl) ⟨1129976, by rfl⟩ : syracuseStep 1506635 = 2259953) B2259953
theorem B949591 : Blo 666309 949591 := bstep (se 1 (by rfl) ⟨712193, by rfl⟩ : syracuseStep 949591 = 1424387) B1424387
theorem B1899865 : Blo 666309 1899865 := bstep (se 2 (by rfl) ⟨712449, by rfl⟩ : syracuseStep 1899865 = 1424899) B1424899
theorem B1506689 : Blo 666309 1506689 := bstep (se 2 (by rfl) ⟨565008, by rfl⟩ : syracuseStep 1506689 = 1130017) B1130017
theorem B753079 : Blo 666309 753079 := bstep (se 1 (by rfl) ⟨564809, by rfl⟩ : syracuseStep 753079 = 1129619) B1129619
theorem B3800641 : Blo 666309 3800641 := bstep (se 2 (by rfl) ⟨1425240, by rfl⟩ : syracuseStep 3800641 = 2850481) B2850481
theorem B1506905 : Blo 666309 1506905 := bstep (se 2 (by rfl) ⟨565089, by rfl⟩ : syracuseStep 1506905 = 1130179) B1130179
theorem B753259 : Blo 666309 753259 := bstep (se 1 (by rfl) ⟨564944, by rfl⟩ : syracuseStep 753259 = 1129889) B1129889
theorem B1506995 : Blo 666309 1506995 := bstep (se 1 (by rfl) ⟨1130246, by rfl⟩ : syracuseStep 1506995 = 2260493) B2260493
theorem B753367 : Blo 666309 753367 := bstep (se 1 (by rfl) ⟨565025, by rfl⟩ : syracuseStep 753367 = 1130051) B1130051
theorem B1507031 : Blo 666309 1507031 := bstep (se 1 (by rfl) ⟨1130273, by rfl⟩ : syracuseStep 1507031 = 2260547) B2260547
theorem B1900253 : Blo 666309 1900253 := bstep (se 3 (by rfl) ⟨356297, by rfl⟩ : syracuseStep 1900253 = 712595) B712595
theorem B2850653 : Blo 666309 2850653 := bstep (se 3 (by rfl) ⟨534497, by rfl⟩ : syracuseStep 2850653 = 1068995) B1068995
theorem B753547 : Blo 666309 753547 := bstep (se 1 (by rfl) ⟨565160, by rfl⟩ : syracuseStep 753547 = 1130321) B1130321
theorem B1507211 : Blo 666309 1507211 := bstep (se 1 (by rfl) ⟨1130408, by rfl⟩ : syracuseStep 1507211 = 2260817) B2260817
theorem B1507265 : Blo 666309 1507265 := bstep (se 2 (by rfl) ⟨565224, by rfl⟩ : syracuseStep 1507265 = 1130449) B1130449
theorem B1015769 : Blo 666309 1015769 := bstep (se 2 (by rfl) ⟨380913, by rfl⟩ : syracuseStep 1015769 = 761827) B761827
theorem B753655 : Blo 666309 753655 := bstep (se 1 (by rfl) ⟨565241, by rfl⟩ : syracuseStep 753655 = 1130483) B1130483
theorem B3375107 : Blo 666309 3375107 := bstep (se 1 (by rfl) ⟨2531330, by rfl⟩ : syracuseStep 3375107 = 5062661) B5062661
theorem B3047453 : Blo 666309 3047453 := bstep (se 3 (by rfl) ⟨571397, by rfl⟩ : syracuseStep 3047453 = 1142795) B1142795
theorem B1605665 : Blo 666309 1605665 := bstep (se 2 (by rfl) ⟨602124, by rfl⟩ : syracuseStep 1605665 = 1204249) B1204249
theorem B1507463 : Blo 666309 1507463 := bstep (se 1 (by rfl) ⟨1130597, by rfl⟩ : syracuseStep 1507463 = 2261195) B2261195
theorem B753799 : Blo 666309 753799 := bstep (se 1 (by rfl) ⟨565349, by rfl⟩ : syracuseStep 753799 = 1130699) B1130699
theorem B2261249 : Blo 666309 2261249 := bstep (se 2 (by rfl) ⟨847968, by rfl⟩ : syracuseStep 2261249 = 1695937) B1695937
theorem B1507643 : Blo 666309 1507643 := bstep (se 1 (by rfl) ⟨1130732, by rfl⟩ : syracuseStep 1507643 = 2261465) B2261465
theorem B753979 : Blo 666309 753979 := bstep (se 1 (by rfl) ⟨565484, by rfl⟩ : syracuseStep 753979 = 1130969) B1130969
theorem B4292999 : Blo 666309 4292999 := bstep (se 1 (by rfl) ⟨3219749, by rfl⟩ : syracuseStep 4292999 = 6439499) B6439499
theorem B1507769 : Blo 666309 1507769 := bstep (se 2 (by rfl) ⟨565413, by rfl⟩ : syracuseStep 1507769 = 1130827) B1130827
theorem B6423083 : Blo 666309 6423083 := bstep (se 1 (by rfl) ⟨4817312, by rfl⟩ : syracuseStep 6423083 = 9634625) B9634625
theorem B5079671 : Blo 666309 5079671 := bstep (se 1 (by rfl) ⟨3809753, by rfl⟩ : syracuseStep 5079671 = 7619507) B7619507
theorem B1901323 : Blo 666309 1901323 := bstep (se 1 (by rfl) ⟨1425992, by rfl⟩ : syracuseStep 1901323 = 2851985) B2851985
theorem B1508111 : Blo 666309 1508111 := bstep (se 1 (by rfl) ⟨1131083, by rfl⟩ : syracuseStep 1508111 = 2262167) B2262167
theorem B1508129 : Blo 666309 1508129 := bstep (se 2 (by rfl) ⟨565548, by rfl⟩ : syracuseStep 1508129 = 1131097) B1131097
theorem B951311 : Blo 666309 951311 := bstep (se 1 (by rfl) ⟨713483, by rfl⟩ : syracuseStep 951311 = 1426967) B1426967
theorem B2262059 : Blo 666309 2262059 := bstep (se 1 (by rfl) ⟨1696544, by rfl⟩ : syracuseStep 2262059 = 3393089) B3393089
theorem B1803379 : Blo 666309 1803379 := bstep (se 1 (by rfl) ⟨1352534, by rfl⟩ : syracuseStep 1803379 = 2705069) B2705069
theorem B6161645 : Blo 666309 6161645 := bstep (se 3 (by rfl) ⟨1155308, by rfl⟩ : syracuseStep 6161645 = 2310617) B2310617
theorem B1901825 : Blo 666309 1901825 := bstep (se 2 (by rfl) ⟨713184, by rfl⟩ : syracuseStep 1901825 = 1426369) B1426369
theorem B5408059 : Blo 666309 5408059 := bstep (se 1 (by rfl) ⟨4056044, by rfl⟩ : syracuseStep 5408059 = 8112089) B8112089
theorem B15435107 : Blo 666309 15435107 := bstep (se 1 (by rfl) ⟨11576330, by rfl⟩ : syracuseStep 15435107 = 23152661) B23152661
theorem B3868019 : Blo 666309 3868019 := bstep (se 1 (by rfl) ⟨2901014, by rfl⟩ : syracuseStep 3868019 = 5802029) B5802029
theorem B2852243 : Blo 666309 2852243 := bstep (se 1 (by rfl) ⟨2139182, by rfl⟩ : syracuseStep 2852243 = 4278365) B4278365
theorem B4294073 : Blo 666309 4294073 := bstep (se 2 (by rfl) ⟨1610277, by rfl⟩ : syracuseStep 4294073 = 3220555) B3220555
theorem B4130327 : Blo 666309 4130327 := bstep (se 1 (by rfl) ⟨3097745, by rfl⟩ : syracuseStep 4130327 = 6195491) B6195491
theorem B2885149 : Blo 666309 2885149 := bstep (se 3 (by rfl) ⟨540965, by rfl⟩ : syracuseStep 2885149 = 1081931) B1081931
theorem B5080643 : Blo 666309 5080643 := bstep (se 1 (by rfl) ⟨3810482, by rfl⟩ : syracuseStep 5080643 = 7620965) B7620965
theorem B3376727 : Blo 666309 3376727 := bstep (se 1 (by rfl) ⟨2532545, by rfl⟩ : syracuseStep 3376727 = 5065091) B5065091
theorem B1902167 : Blo 666309 1902167 := bstep (se 1 (by rfl) ⟨1426625, by rfl⟩ : syracuseStep 1902167 = 2853251) B2853251
theorem B7243481 : Blo 666309 7243481 := bstep (se 2 (by rfl) ⟨2716305, by rfl⟩ : syracuseStep 7243481 = 5432611) B5432611
theorem B1083179 : Blo 666309 1083179 := bstep (se 1 (by rfl) ⟨812384, by rfl⟩ : syracuseStep 1083179 = 1624769) B1624769
theorem B3377213 : Blo 666309 3377213 := bstep (se 3 (by rfl) ⟨633227, by rfl⟩ : syracuseStep 3377213 = 1266455) B1266455
theorem B952393 : Blo 666309 952393 := bstep (se 2 (by rfl) ⟨357147, by rfl⟩ : syracuseStep 952393 = 714295) B714295
theorem B10815605 : Blo 666309 10815605 := bstep (se 5 (by rfl) ⟨506981, by rfl⟩ : syracuseStep 10815605 = 1013963) B1013963
theorem B952507 : Blo 666309 952507 := bstep (se 1 (by rfl) ⟨714380, by rfl⟩ : syracuseStep 952507 = 1428761) B1428761
theorem B3049787 : Blo 666309 3049787 := bstep (se 1 (by rfl) ⟨2287340, by rfl⟩ : syracuseStep 3049787 = 4574681) B4574681
theorem B6425041 : Blo 666309 6425041 := bstep (se 2 (by rfl) ⟨2409390, by rfl⟩ : syracuseStep 6425041 = 4818781) B4818781
theorem B1018639 : Blo 666309 1018639 := bstep (se 1 (by rfl) ⟨763979, by rfl⟩ : syracuseStep 1018639 = 1527959) B1527959
theorem B2853899 : Blo 666309 2853899 := bstep (se 1 (by rfl) ⟨2140424, by rfl⟩ : syracuseStep 2853899 = 4280849) B4280849
theorem B1904057 : Blo 666309 1904057 := bstep (se 2 (by rfl) ⟨714021, by rfl⟩ : syracuseStep 1904057 = 1428043) B1428043
theorem B3247627 : Blo 666309 3247627 := bstep (se 1 (by rfl) ⟨2435720, by rfl⟩ : syracuseStep 3247627 = 4871441) B4871441
theorem B2887235 : Blo 666309 2887235 := bstep (se 1 (by rfl) ⟨2165426, by rfl⟩ : syracuseStep 2887235 = 4330853) B4330853
theorem B14650955 : Blo 666309 14650955 := bstep (se 1 (by rfl) ⟨10988216, by rfl⟩ : syracuseStep 14650955 = 21976433) B21976433
theorem B954119 : Blo 666309 954119 := bstep (se 1 (by rfl) ⟨715589, by rfl⟩ : syracuseStep 954119 = 1431179) B1431179
theorem B3378995 : Blo 666309 3378995 := bstep (se 1 (by rfl) ⟨2534246, by rfl⟩ : syracuseStep 3378995 = 5068493) B5068493
theorem B1609625 : Blo 666309 1609625 := bstep (se 2 (by rfl) ⟨603609, by rfl⟩ : syracuseStep 1609625 = 1207219) B1207219
theorem B3379319 : Blo 666309 3379319 := bstep (se 1 (by rfl) ⟨2534489, by rfl⟩ : syracuseStep 3379319 = 5068979) B5068979
theorem B1905697 : Blo 666309 1905697 := bstep (se 2 (by rfl) ⟨714636, by rfl⟩ : syracuseStep 1905697 = 1429273) B1429273
theorem B3380291 : Blo 666309 3380291 := bstep (se 1 (by rfl) ⟨2535218, by rfl⟩ : syracuseStep 3380291 = 5070437) B5070437
theorem B3380615 : Blo 666309 3380615 := bstep (se 1 (by rfl) ⟨2535461, by rfl⟩ : syracuseStep 3380615 = 5070923) B5070923
theorem B8131985 : Blo 666309 8131985 := bstep (se 2 (by rfl) ⟨3049494, by rfl⟩ : syracuseStep 8131985 = 6098989) B6098989
theorem B16226021 : Blo 666309 16226021 := bstep (se 4 (by rfl) ⟨1521189, by rfl⟩ : syracuseStep 16226021 = 3042379) B3042379
theorem B9639749 : Blo 666309 9639749 := bstep (se 4 (by rfl) ⟨903726, by rfl⟩ : syracuseStep 9639749 = 1807453) B1807453
theorem B5085017 : Blo 666309 5085017 := bstep (se 2 (by rfl) ⟨1906881, by rfl⟩ : syracuseStep 5085017 = 3813763) B3813763
theorem B2136107 : Blo 666309 2136107 := bstep (se 1 (by rfl) ⟨1602080, by rfl⟩ : syracuseStep 2136107 = 3204161) B3204161
theorem B1906973 : Blo 666309 1906973 := bstep (se 3 (by rfl) ⟨357557, by rfl⟩ : syracuseStep 1906973 = 715115) B715115
theorem B1907201 : Blo 666309 1907201 := bstep (se 2 (by rfl) ⟨715200, by rfl⟩ : syracuseStep 1907201 = 1430401) B1430401
theorem B11606819 : Blo 666309 11606819 := bstep (se 1 (by rfl) ⟨8705114, by rfl⟩ : syracuseStep 11606819 = 17410229) B17410229
theorem B5085989 : Blo 666309 5085989 := bstep (se 4 (by rfl) ⟨476811, by rfl⟩ : syracuseStep 5085989 = 953623) B953623
theorem B1907543 : Blo 666309 1907543 := bstep (se 1 (by rfl) ⟨1430657, by rfl⟩ : syracuseStep 1907543 = 2861315) B2861315
theorem B2202553 : Blo 666309 2202553 := bstep (se 2 (by rfl) ⟨825957, by rfl⟩ : syracuseStep 2202553 = 1651915) B1651915
theorem B1907657 : Blo 666309 1907657 := bstep (se 2 (by rfl) ⟨715371, by rfl⟩ : syracuseStep 1907657 = 1430743) B1430743
theorem B3808457 : Blo 666309 3808457 := bstep (se 2 (by rfl) ⟨1428171, by rfl⟩ : syracuseStep 3808457 = 2856343) B2856343
theorem B2530541 : Blo 666309 2530541 := bstep (se 3 (by rfl) ⟨474476, by rfl⟩ : syracuseStep 2530541 = 948953) B948953
theorem B2858273 : Blo 666309 2858273 := bstep (se 2 (by rfl) ⟨1071852, by rfl⟩ : syracuseStep 2858273 = 2143705) B2143705
theorem B1809811 : Blo 666309 1809811 := bstep (se 1 (by rfl) ⟨1357358, by rfl⟩ : syracuseStep 1809811 = 2714717) B2714717
theorem B2858615 : Blo 666309 2858615 := bstep (se 1 (by rfl) ⟨2143961, by rfl⟩ : syracuseStep 2858615 = 4287923) B4287923
theorem B6430499 : Blo 666309 6430499 := bstep (se 1 (by rfl) ⟨4822874, by rfl⟩ : syracuseStep 6430499 = 9645749) B9645749
theorem B3219385 : Blo 666309 3219385 := bstep (se 2 (by rfl) ⟨1207269, by rfl⟩ : syracuseStep 3219385 = 2414539) B2414539
theorem B7610759 : Blo 666309 7610759 := bstep (se 1 (by rfl) ⟨5708069, by rfl⟩ : syracuseStep 7610759 = 11416139) B11416139
theorem B3908411 : Blo 666309 3908411 := bstep (se 1 (by rfl) ⟨2931308, by rfl⟩ : syracuseStep 3908411 = 5862617) B5862617
theorem B1811261 : Blo 666309 1811261 := bstep (se 3 (by rfl) ⟨339611, by rfl⟩ : syracuseStep 1811261 = 679223) B679223
theorem B3384179 : Blo 666309 3384179 := bstep (se 1 (by rfl) ⟨2538134, by rfl⟩ : syracuseStep 3384179 = 5076269) B5076269
theorem B762895 : Blo 666309 762895 := bstep (se 1 (by rfl) ⟨572171, by rfl⟩ : syracuseStep 762895 = 1144343) B1144343
theorem B3810347 : Blo 666309 3810347 := bstep (se 1 (by rfl) ⟨2857760, by rfl⟩ : syracuseStep 3810347 = 5715521) B5715521
theorem B2532667 : Blo 666309 2532667 := bstep (se 1 (by rfl) ⟨1899500, by rfl⟩ : syracuseStep 2532667 = 3799001) B3799001
theorem B3384665 : Blo 666309 3384665 := bstep (se 2 (by rfl) ⟨1269249, by rfl⟩ : syracuseStep 3384665 = 2538499) B2538499
theorem B4826627 : Blo 666309 4826627 := bstep (se 1 (by rfl) ⟨3619970, by rfl⟩ : syracuseStep 4826627 = 7239941) B7239941
theorem B12822245 : Blo 666309 12822245 := bstep (se 4 (by rfl) ⟨1202085, by rfl⟩ : syracuseStep 12822245 = 2404171) B2404171
theorem B2533153 : Blo 666309 2533153 := bstep (se 2 (by rfl) ⟨949932, by rfl⟩ : syracuseStep 2533153 = 1899865) B1899865
theorem B1124651 : Blo 666309 1124651 := bstep (se 1 (by rfl) ⟨843488, by rfl⟩ : syracuseStep 1124651 = 1686977) B1686977
theorem B3811805 : Blo 666309 3811805 := bstep (se 3 (by rfl) ⟨714713, by rfl⟩ : syracuseStep 3811805 = 1429427) B1429427
theorem B1125049 : Blo 666309 1125049 := bstep (se 2 (by rfl) ⟨421893, by rfl⟩ : syracuseStep 1125049 = 843787) B843787
theorem B2534125 : Blo 666309 2534125 := bstep (se 3 (by rfl) ⟨475148, by rfl⟩ : syracuseStep 2534125 = 950297) B950297
theorem B666375 : Blo 666309 666375 := bstep (se 1 (by rfl) ⟨499781, by rfl⟩ : syracuseStep 666375 = 999563) B999563
theorem B666383 : Blo 666309 666383 := bstep (se 1 (by rfl) ⟨499787, by rfl⟩ : syracuseStep 666383 = 999575) B999575
theorem B666427 : Blo 666309 666427 := bstep (se 1 (by rfl) ⟨499820, by rfl⟩ : syracuseStep 666427 = 999641) B999641
theorem B666503 : Blo 666309 666503 := bstep (se 1 (by rfl) ⟨499877, by rfl⟩ : syracuseStep 666503 = 999755) B999755
theorem B666511 : Blo 666309 666511 := bstep (se 1 (by rfl) ⟨499883, by rfl⟩ : syracuseStep 666511 = 999767) B999767
theorem B666555 : Blo 666309 666555 := bstep (se 1 (by rfl) ⟨499916, by rfl⟩ : syracuseStep 666555 = 999833) B999833
theorem B3812305 : Blo 666309 3812305 := bstep (se 2 (by rfl) ⟨1429614, by rfl⟩ : syracuseStep 3812305 = 2859229) B2859229
theorem B1715201 : Blo 666309 1715201 := bstep (se 2 (by rfl) ⟨643200, by rfl⟩ : syracuseStep 1715201 = 1286401) B1286401
theorem B666631 : Blo 666309 666631 := bstep (se 1 (by rfl) ⟨499973, by rfl⟩ : syracuseStep 666631 = 999947) B999947
theorem B666639 : Blo 666309 666639 := bstep (se 1 (by rfl) ⟨499979, by rfl⟩ : syracuseStep 666639 = 999959) B999959
theorem B2173981 : Blo 666309 2173981 := bstep (se 3 (by rfl) ⟨407621, by rfl⟩ : syracuseStep 2173981 = 815243) B815243
theorem B2534429 : Blo 666309 2534429 := bstep (se 3 (by rfl) ⟨475205, by rfl⟩ : syracuseStep 2534429 = 950411) B950411
theorem B666683 : Blo 666309 666683 := bstep (se 1 (by rfl) ⟨500012, by rfl⟩ : syracuseStep 666683 = 1000025) B1000025
theorem B2403395 : Blo 666309 2403395 := bstep (se 1 (by rfl) ⟨1802546, by rfl⟩ : syracuseStep 2403395 = 3605093) B3605093
theorem B666759 : Blo 666309 666759 := bstep (se 1 (by rfl) ⟨500069, by rfl⟩ : syracuseStep 666759 = 1000139) B1000139
theorem B666767 : Blo 666309 666767 := bstep (se 1 (by rfl) ⟨500075, by rfl⟩ : syracuseStep 666767 = 1000151) B1000151
theorem B666811 : Blo 666309 666811 := bstep (se 1 (by rfl) ⟨500108, by rfl⟩ : syracuseStep 666811 = 1000217) B1000217
theorem B666887 : Blo 666309 666887 := bstep (se 1 (by rfl) ⟨500165, by rfl⟩ : syracuseStep 666887 = 1000331) B1000331
theorem B666895 : Blo 666309 666895 := bstep (se 1 (by rfl) ⟨500171, by rfl⟩ : syracuseStep 666895 = 1000343) B1000343
theorem B4271393 : Blo 666309 4271393 := bstep (se 2 (by rfl) ⟨1601772, by rfl⟩ : syracuseStep 4271393 = 3203545) B3203545
theorem B666939 : Blo 666309 666939 := bstep (se 1 (by rfl) ⟨500204, by rfl⟩ : syracuseStep 666939 = 1000409) B1000409
theorem B1125751 : Blo 666309 1125751 := bstep (se 1 (by rfl) ⟨844313, by rfl⟩ : syracuseStep 1125751 = 1688627) B1688627
theorem B667015 : Blo 666309 667015 := bstep (se 1 (by rfl) ⟨500261, by rfl⟩ : syracuseStep 667015 = 1000523) B1000523
theorem B667023 : Blo 666309 667023 := bstep (se 1 (by rfl) ⟨500267, by rfl⟩ : syracuseStep 667023 = 1000535) B1000535
theorem B3386771 : Blo 666309 3386771 := bstep (se 1 (by rfl) ⟨2540078, by rfl⟩ : syracuseStep 3386771 = 5080157) B5080157
theorem B667067 : Blo 666309 667067 := bstep (se 1 (by rfl) ⟨500300, by rfl⟩ : syracuseStep 667067 = 1000601) B1000601
theorem B667143 : Blo 666309 667143 := bstep (se 1 (by rfl) ⟨500357, by rfl⟩ : syracuseStep 667143 = 1000715) B1000715
theorem B667151 : Blo 666309 667151 := bstep (se 1 (by rfl) ⟨500363, by rfl⟩ : syracuseStep 667151 = 1000727) B1000727
theorem B667195 : Blo 666309 667195 := bstep (se 1 (by rfl) ⟨500396, by rfl⟩ : syracuseStep 667195 = 1000793) B1000793
theorem B1125947 : Blo 666309 1125947 := bstep (se 1 (by rfl) ⟨844460, by rfl⟩ : syracuseStep 1125947 = 1688921) B1688921
theorem B1027657 : Blo 666309 1027657 := bstep (se 2 (by rfl) ⟨385371, by rfl⟩ : syracuseStep 1027657 = 770743) B770743
theorem B667271 : Blo 666309 667271 := bstep (se 1 (by rfl) ⟨500453, by rfl⟩ : syracuseStep 667271 = 1000907) B1000907
theorem B667279 : Blo 666309 667279 := bstep (se 1 (by rfl) ⟨500459, by rfl⟩ : syracuseStep 667279 = 1000919) B1000919
theorem B667323 : Blo 666309 667323 := bstep (se 1 (by rfl) ⟨500492, by rfl⟩ : syracuseStep 667323 = 1000985) B1000985
theorem B667399 : Blo 666309 667399 := bstep (se 1 (by rfl) ⟨500549, by rfl⟩ : syracuseStep 667399 = 1001099) B1001099
theorem B667407 : Blo 666309 667407 := bstep (se 1 (by rfl) ⟨500555, by rfl⟩ : syracuseStep 667407 = 1001111) B1001111
theorem B667451 : Blo 666309 667451 := bstep (se 1 (by rfl) ⟨500588, by rfl⟩ : syracuseStep 667451 = 1001177) B1001177
theorem B667527 : Blo 666309 667527 := bstep (se 1 (by rfl) ⟨500645, by rfl⟩ : syracuseStep 667527 = 1001291) B1001291
theorem B667535 : Blo 666309 667535 := bstep (se 1 (by rfl) ⟨500651, by rfl⟩ : syracuseStep 667535 = 1001303) B1001303
theorem B667579 : Blo 666309 667579 := bstep (se 1 (by rfl) ⟨500684, by rfl⟩ : syracuseStep 667579 = 1001369) B1001369
theorem B1126345 : Blo 666309 1126345 := bstep (se 2 (by rfl) ⟨422379, by rfl⟩ : syracuseStep 1126345 = 844759) B844759
theorem B667655 : Blo 666309 667655 := bstep (se 1 (by rfl) ⟨500741, by rfl⟩ : syracuseStep 667655 = 1001483) B1001483
theorem B667663 : Blo 666309 667663 := bstep (se 1 (by rfl) ⟨500747, by rfl⟩ : syracuseStep 667663 = 1001495) B1001495
theorem B667707 : Blo 666309 667707 := bstep (se 1 (by rfl) ⟨500780, by rfl⟩ : syracuseStep 667707 = 1001561) B1001561
theorem B667783 : Blo 666309 667783 := bstep (se 1 (by rfl) ⟨500837, by rfl⟩ : syracuseStep 667783 = 1001675) B1001675
theorem B667791 : Blo 666309 667791 := bstep (se 1 (by rfl) ⟨500843, by rfl⟩ : syracuseStep 667791 = 1001687) B1001687
theorem B667835 : Blo 666309 667835 := bstep (se 1 (by rfl) ⟨500876, by rfl⟩ : syracuseStep 667835 = 1001753) B1001753
theorem B8138989 : Blo 666309 8138989 := bstep (se 3 (by rfl) ⟨1526060, by rfl⟩ : syracuseStep 8138989 = 3052121) B3052121
theorem B667911 : Blo 666309 667911 := bstep (se 1 (by rfl) ⟨500933, by rfl⟩ : syracuseStep 667911 = 1001867) B1001867
theorem B667919 : Blo 666309 667919 := bstep (se 1 (by rfl) ⟨500939, by rfl⟩ : syracuseStep 667919 = 1001879) B1001879
theorem B7516433 : Blo 666309 7516433 := bstep (se 2 (by rfl) ⟨2818662, by rfl⟩ : syracuseStep 7516433 = 5637325) B5637325
theorem B1519931 : Blo 666309 1519931 := bstep (se 1 (by rfl) ⟨1139948, by rfl⟩ : syracuseStep 1519931 = 2279897) B2279897
theorem B667963 : Blo 666309 667963 := bstep (se 1 (by rfl) ⟨500972, by rfl⟩ : syracuseStep 667963 = 1001945) B1001945
theorem B668039 : Blo 666309 668039 := bstep (se 1 (by rfl) ⟨501029, by rfl⟩ : syracuseStep 668039 = 1002059) B1002059
theorem B1356167 : Blo 666309 1356167 := bstep (se 1 (by rfl) ⟨1017125, by rfl⟩ : syracuseStep 1356167 = 2034251) B2034251
theorem B668047 : Blo 666309 668047 := bstep (se 1 (by rfl) ⟨501035, by rfl⟩ : syracuseStep 668047 = 1002071) B1002071
theorem B668091 : Blo 666309 668091 := bstep (se 1 (by rfl) ⟨501068, by rfl⟩ : syracuseStep 668091 = 1002137) B1002137
theorem B668167 : Blo 666309 668167 := bstep (se 1 (by rfl) ⟨501125, by rfl⟩ : syracuseStep 668167 = 1002251) B1002251
theorem B668175 : Blo 666309 668175 := bstep (se 1 (by rfl) ⟨501131, by rfl⟩ : syracuseStep 668175 = 1002263) B1002263
theorem B1520171 : Blo 666309 1520171 := bstep (se 1 (by rfl) ⟨1140128, by rfl⟩ : syracuseStep 1520171 = 2280257) B2280257
theorem B668219 : Blo 666309 668219 := bstep (se 1 (by rfl) ⟨501164, by rfl⟩ : syracuseStep 668219 = 1002329) B1002329
theorem B2536055 : Blo 666309 2536055 := bstep (se 1 (by rfl) ⟨1902041, by rfl⟩ : syracuseStep 2536055 = 3804083) B3804083
theorem B1127047 : Blo 666309 1127047 := bstep (se 1 (by rfl) ⟨845285, by rfl⟩ : syracuseStep 1127047 = 1690571) B1690571
theorem B668295 : Blo 666309 668295 := bstep (se 1 (by rfl) ⟨501221, by rfl⟩ : syracuseStep 668295 = 1002443) B1002443
theorem B668303 : Blo 666309 668303 := bstep (se 1 (by rfl) ⟨501227, by rfl⟩ : syracuseStep 668303 = 1002455) B1002455
theorem B668347 : Blo 666309 668347 := bstep (se 1 (by rfl) ⟨501260, by rfl⟩ : syracuseStep 668347 = 1002521) B1002521
theorem B668423 : Blo 666309 668423 := bstep (se 1 (by rfl) ⟨501317, by rfl⟩ : syracuseStep 668423 = 1002635) B1002635
theorem B668431 : Blo 666309 668431 := bstep (se 1 (by rfl) ⟨501323, by rfl⟩ : syracuseStep 668431 = 1002647) B1002647
theorem B2405153 : Blo 666309 2405153 := bstep (se 2 (by rfl) ⟨901932, by rfl⟩ : syracuseStep 2405153 = 1803865) B1803865
theorem B668475 : Blo 666309 668475 := bstep (se 1 (by rfl) ⟨501356, by rfl⟩ : syracuseStep 668475 = 1002713) B1002713
theorem B668551 : Blo 666309 668551 := bstep (se 1 (by rfl) ⟨501413, by rfl⟩ : syracuseStep 668551 = 1002827) B1002827
theorem B668559 : Blo 666309 668559 := bstep (se 1 (by rfl) ⟨501419, by rfl⟩ : syracuseStep 668559 = 1002839) B1002839
theorem B3814289 : Blo 666309 3814289 := bstep (se 2 (by rfl) ⟨1430358, by rfl⟩ : syracuseStep 3814289 = 2860717) B2860717
theorem B668603 : Blo 666309 668603 := bstep (se 1 (by rfl) ⟨501452, by rfl⟩ : syracuseStep 668603 = 1002905) B1002905
theorem B668679 : Blo 666309 668679 := bstep (se 1 (by rfl) ⟨501509, by rfl⟩ : syracuseStep 668679 = 1003019) B1003019
theorem B668687 : Blo 666309 668687 := bstep (se 1 (by rfl) ⟨501515, by rfl⟩ : syracuseStep 668687 = 1003031) B1003031
theorem B668731 : Blo 666309 668731 := bstep (se 1 (by rfl) ⟨501548, by rfl⟩ : syracuseStep 668731 = 1003097) B1003097
theorem B668807 : Blo 666309 668807 := bstep (se 1 (by rfl) ⟨501605, by rfl⟩ : syracuseStep 668807 = 1003211) B1003211
theorem B668815 : Blo 666309 668815 := bstep (se 1 (by rfl) ⟨501611, by rfl⟩ : syracuseStep 668815 = 1003223) B1003223
theorem B668859 : Blo 666309 668859 := bstep (se 1 (by rfl) ⟨501644, by rfl⟩ : syracuseStep 668859 = 1003289) B1003289
theorem B668935 : Blo 666309 668935 := bstep (se 1 (by rfl) ⟨501701, by rfl⟩ : syracuseStep 668935 = 1003403) B1003403
theorem B1127695 : Blo 666309 1127695 := bstep (se 1 (by rfl) ⟨845771, by rfl⟩ : syracuseStep 1127695 = 1691543) B1691543
theorem B668943 : Blo 666309 668943 := bstep (se 1 (by rfl) ⟨501707, by rfl⟩ : syracuseStep 668943 = 1003415) B1003415
theorem B668987 : Blo 666309 668987 := bstep (se 1 (by rfl) ⟨501740, by rfl⟩ : syracuseStep 668987 = 1003481) B1003481
theorem B669063 : Blo 666309 669063 := bstep (se 1 (by rfl) ⟨501797, by rfl⟩ : syracuseStep 669063 = 1003595) B1003595
theorem B669071 : Blo 666309 669071 := bstep (se 1 (by rfl) ⟨501803, by rfl⟩ : syracuseStep 669071 = 1003607) B1003607
theorem B669115 : Blo 666309 669115 := bstep (se 1 (by rfl) ⟨501836, by rfl⟩ : syracuseStep 669115 = 1003673) B1003673
theorem B669191 : Blo 666309 669191 := bstep (se 1 (by rfl) ⟨501893, by rfl⟩ : syracuseStep 669191 = 1003787) B1003787
theorem B669199 : Blo 666309 669199 := bstep (se 1 (by rfl) ⟨501899, by rfl⟩ : syracuseStep 669199 = 1003799) B1003799
theorem B669243 : Blo 666309 669243 := bstep (se 1 (by rfl) ⟨501932, by rfl⟩ : syracuseStep 669243 = 1003865) B1003865
theorem B2537027 : Blo 666309 2537027 := bstep (se 1 (by rfl) ⟨1902770, by rfl⟩ : syracuseStep 2537027 = 3805541) B3805541
theorem B669319 : Blo 666309 669319 := bstep (se 1 (by rfl) ⟨501989, by rfl⟩ : syracuseStep 669319 = 1003979) B1003979
theorem B669327 : Blo 666309 669327 := bstep (se 1 (by rfl) ⟨501995, by rfl⟩ : syracuseStep 669327 = 1003991) B1003991
theorem B669371 : Blo 666309 669371 := bstep (se 1 (by rfl) ⟨502028, by rfl⟩ : syracuseStep 669371 = 1004057) B1004057
theorem B669447 : Blo 666309 669447 := bstep (se 1 (by rfl) ⟨502085, by rfl⟩ : syracuseStep 669447 = 1004171) B1004171
theorem B669455 : Blo 666309 669455 := bstep (se 1 (by rfl) ⟨502091, by rfl⟩ : syracuseStep 669455 = 1004183) B1004183
theorem B1128235 : Blo 666309 1128235 := bstep (se 1 (by rfl) ⟨846176, by rfl⟩ : syracuseStep 1128235 = 1692353) B1692353
theorem B669499 : Blo 666309 669499 := bstep (se 1 (by rfl) ⟨502124, by rfl⟩ : syracuseStep 669499 = 1004249) B1004249
theorem B669575 : Blo 666309 669575 := bstep (se 1 (by rfl) ⟨502181, by rfl⟩ : syracuseStep 669575 = 1004363) B1004363
theorem B669583 : Blo 666309 669583 := bstep (se 1 (by rfl) ⟨502187, by rfl⟩ : syracuseStep 669583 = 1004375) B1004375
theorem B1128377 : Blo 666309 1128377 := bstep (se 2 (by rfl) ⟨423141, by rfl⟩ : syracuseStep 1128377 = 846283) B846283
theorem B669627 : Blo 666309 669627 := bstep (se 1 (by rfl) ⟨502220, by rfl⟩ : syracuseStep 669627 = 1004441) B1004441
theorem B669703 : Blo 666309 669703 := bstep (se 1 (by rfl) ⟨502277, by rfl⟩ : syracuseStep 669703 = 1004555) B1004555
theorem B669711 : Blo 666309 669711 := bstep (se 1 (by rfl) ⟨502283, by rfl⟩ : syracuseStep 669711 = 1004567) B1004567
theorem B669755 : Blo 666309 669755 := bstep (se 1 (by rfl) ⟨502316, by rfl⟩ : syracuseStep 669755 = 1004633) B1004633
theorem B669831 : Blo 666309 669831 := bstep (se 1 (by rfl) ⟨502373, by rfl⟩ : syracuseStep 669831 = 1004747) B1004747
theorem B669839 : Blo 666309 669839 := bstep (se 1 (by rfl) ⟨502379, by rfl⟩ : syracuseStep 669839 = 1004759) B1004759
theorem B669883 : Blo 666309 669883 := bstep (se 1 (by rfl) ⟨502412, by rfl⟩ : syracuseStep 669883 = 1004825) B1004825
theorem B669959 : Blo 666309 669959 := bstep (se 1 (by rfl) ⟨502469, by rfl⟩ : syracuseStep 669959 = 1004939) B1004939
theorem B669967 : Blo 666309 669967 := bstep (se 1 (by rfl) ⟨502475, by rfl⟩ : syracuseStep 669967 = 1004951) B1004951
theorem B801083 : Blo 666309 801083 := bstep (se 1 (by rfl) ⟨600812, by rfl⟩ : syracuseStep 801083 = 1201625) B1201625
theorem B670011 : Blo 666309 670011 := bstep (se 1 (by rfl) ⟨502508, by rfl⟩ : syracuseStep 670011 = 1005017) B1005017
theorem B670087 : Blo 666309 670087 := bstep (se 1 (by rfl) ⟨502565, by rfl⟩ : syracuseStep 670087 = 1005131) B1005131
theorem B670095 : Blo 666309 670095 := bstep (se 1 (by rfl) ⟨502571, by rfl⟩ : syracuseStep 670095 = 1005143) B1005143
theorem B3389849 : Blo 666309 3389849 := bstep (se 2 (by rfl) ⟨1271193, by rfl⟩ : syracuseStep 3389849 = 2542387) B2542387
theorem B670139 : Blo 666309 670139 := bstep (se 1 (by rfl) ⟨502604, by rfl⟩ : syracuseStep 670139 = 1005209) B1005209
theorem B670215 : Blo 666309 670215 := bstep (se 1 (by rfl) ⟨502661, by rfl⟩ : syracuseStep 670215 = 1005323) B1005323
theorem B670223 : Blo 666309 670223 := bstep (se 1 (by rfl) ⟨502667, by rfl⟩ : syracuseStep 670223 = 1005335) B1005335
theorem B2406941 : Blo 666309 2406941 := bstep (se 3 (by rfl) ⟨451301, by rfl⟩ : syracuseStep 2406941 = 902603) B902603
theorem B2538013 : Blo 666309 2538013 := bstep (se 3 (by rfl) ⟨475877, by rfl⟩ : syracuseStep 2538013 = 951755) B951755
theorem B670267 : Blo 666309 670267 := bstep (se 1 (by rfl) ⟨502700, by rfl⟩ : syracuseStep 670267 = 1005401) B1005401
theorem B1129079 : Blo 666309 1129079 := bstep (se 1 (by rfl) ⟨846809, by rfl⟩ : syracuseStep 1129079 = 1693619) B1693619
theorem B1129531 : Blo 666309 1129531 := bstep (se 1 (by rfl) ⟨847148, by rfl⟩ : syracuseStep 1129531 = 1694297) B1694297
theorem B1129673 : Blo 666309 1129673 := bstep (se 2 (by rfl) ⟨423627, by rfl⟩ : syracuseStep 1129673 = 847255) B847255
theorem B5422621 : Blo 666309 5422621 := bstep (se 3 (by rfl) ⟨1016741, by rfl⟩ : syracuseStep 5422621 = 2033483) B2033483
theorem B1130375 : Blo 666309 1130375 := bstep (se 1 (by rfl) ⟨847781, by rfl⟩ : syracuseStep 1130375 = 1695563) B1695563
theorem B901111 : Blo 666309 901111 := bstep (se 1 (by rfl) ⟨675833, by rfl⟩ : syracuseStep 901111 = 1351667) B1351667
theorem B16269335 : Blo 666309 16269335 := bstep (se 1 (by rfl) ⟨12202001, by rfl⟩ : syracuseStep 16269335 = 24404003) B24404003
theorem B999467 : Blo 666309 999467 := bstep (se 1 (by rfl) ⟨749600, by rfl⟩ : syracuseStep 999467 = 1499201) B1499201
theorem B999497 : Blo 666309 999497 := bstep (se 2 (by rfl) ⟨374811, by rfl⟩ : syracuseStep 999497 = 749623) B749623
theorem B999611 : Blo 666309 999611 := bstep (se 1 (by rfl) ⟨749708, by rfl⟩ : syracuseStep 999611 = 1499417) B1499417
theorem B999671 : Blo 666309 999671 := bstep (se 1 (by rfl) ⟨749753, by rfl⟩ : syracuseStep 999671 = 1499507) B1499507
theorem B12828941 : Blo 666309 12828941 := bstep (se 3 (by rfl) ⟨2405426, by rfl⟩ : syracuseStep 12828941 = 4810853) B4810853
theorem B999695 : Blo 666309 999695 := bstep (se 1 (by rfl) ⟨749771, by rfl⟩ : syracuseStep 999695 = 1499543) B1499543
theorem B999737 : Blo 666309 999737 := bstep (se 2 (by rfl) ⟨374901, by rfl⟩ : syracuseStep 999737 = 749803) B749803
theorem B54804853 : Blo 666309 54804853 := bstep (se 5 (by rfl) ⟨2568977, by rfl⟩ : syracuseStep 54804853 = 5137955) B5137955
theorem B999815 : Blo 666309 999815 := bstep (se 1 (by rfl) ⟨749861, by rfl⟩ : syracuseStep 999815 = 1499723) B1499723
theorem B999851 : Blo 666309 999851 := bstep (se 1 (by rfl) ⟨749888, by rfl⟩ : syracuseStep 999851 = 1499777) B1499777
theorem B999881 : Blo 666309 999881 := bstep (se 2 (by rfl) ⟨374955, by rfl⟩ : syracuseStep 999881 = 749911) B749911
theorem B20595185 : Blo 666309 20595185 := bstep (se 2 (by rfl) ⟨7723194, by rfl⟩ : syracuseStep 20595185 = 15446389) B15446389
theorem B1131023 : Blo 666309 1131023 := bstep (se 1 (by rfl) ⟨848267, by rfl⟩ : syracuseStep 1131023 = 1696535) B1696535
theorem B803371 : Blo 666309 803371 := bstep (se 1 (by rfl) ⟨602528, by rfl⟩ : syracuseStep 803371 = 1205057) B1205057
theorem B999995 : Blo 666309 999995 := bstep (se 1 (by rfl) ⟨749996, by rfl⟩ : syracuseStep 999995 = 1499993) B1499993
theorem B1000055 : Blo 666309 1000055 := bstep (se 1 (by rfl) ⟨750041, by rfl⟩ : syracuseStep 1000055 = 1500083) B1500083
theorem B1000079 : Blo 666309 1000079 := bstep (se 1 (by rfl) ⟨750059, by rfl⟩ : syracuseStep 1000079 = 1500119) B1500119
theorem B1000121 : Blo 666309 1000121 := bstep (se 2 (by rfl) ⟨375045, by rfl⟩ : syracuseStep 1000121 = 750091) B750091
theorem B803515 : Blo 666309 803515 := bstep (se 1 (by rfl) ⟨602636, by rfl⟩ : syracuseStep 803515 = 1205273) B1205273
theorem B9126593 : Blo 666309 9126593 := bstep (se 2 (by rfl) ⟨3422472, by rfl⟩ : syracuseStep 9126593 = 6844945) B6844945
theorem B1000199 : Blo 666309 1000199 := bstep (se 1 (by rfl) ⟨750149, by rfl⟩ : syracuseStep 1000199 = 1500299) B1500299
theorem B1000235 : Blo 666309 1000235 := bstep (se 1 (by rfl) ⟨750176, by rfl⟩ : syracuseStep 1000235 = 1500353) B1500353
theorem B5423921 : Blo 666309 5423921 := bstep (se 2 (by rfl) ⟨2033970, by rfl⟩ : syracuseStep 5423921 = 4067941) B4067941
theorem B1000265 : Blo 666309 1000265 := bstep (se 2 (by rfl) ⟨375099, by rfl⟩ : syracuseStep 1000265 = 750199) B750199
theorem B1688435 : Blo 666309 1688435 := bstep (se 1 (by rfl) ⟨1266326, by rfl⟩ : syracuseStep 1688435 = 2532653) B2532653
theorem B3392441 : Blo 666309 3392441 := bstep (se 2 (by rfl) ⟨1272165, by rfl⟩ : syracuseStep 3392441 = 2544331) B2544331
theorem B1000379 : Blo 666309 1000379 := bstep (se 1 (by rfl) ⟨750284, by rfl⟩ : syracuseStep 1000379 = 1500569) B1500569
theorem B1000439 : Blo 666309 1000439 := bstep (se 1 (by rfl) ⟨750329, by rfl⟩ : syracuseStep 1000439 = 1500659) B1500659
theorem B1000463 : Blo 666309 1000463 := bstep (se 1 (by rfl) ⟨750347, by rfl⟩ : syracuseStep 1000463 = 1500695) B1500695
theorem B1000505 : Blo 666309 1000505 := bstep (se 2 (by rfl) ⟨375189, by rfl⟩ : syracuseStep 1000505 = 750379) B750379
theorem B1000583 : Blo 666309 1000583 := bstep (se 1 (by rfl) ⟨750437, by rfl⟩ : syracuseStep 1000583 = 1500875) B1500875
theorem B1885331 : Blo 666309 1885331 := bstep (se 1 (by rfl) ⟨1413998, by rfl⟩ : syracuseStep 1885331 = 2827997) B2827997
theorem B1000619 : Blo 666309 1000619 := bstep (se 1 (by rfl) ⟨750464, by rfl⟩ : syracuseStep 1000619 = 1500929) B1500929
theorem B1000649 : Blo 666309 1000649 := bstep (se 2 (by rfl) ⟨375243, by rfl⟩ : syracuseStep 1000649 = 750487) B750487
theorem B1000763 : Blo 666309 1000763 := bstep (se 1 (by rfl) ⟨750572, by rfl⟩ : syracuseStep 1000763 = 1501145) B1501145
theorem B2540915 : Blo 666309 2540915 := bstep (se 1 (by rfl) ⟨1905686, by rfl⟩ : syracuseStep 2540915 = 3811373) B3811373
theorem B1000823 : Blo 666309 1000823 := bstep (se 1 (by rfl) ⟨750617, by rfl⟩ : syracuseStep 1000823 = 1501235) B1501235
theorem B1688951 : Blo 666309 1688951 := bstep (se 1 (by rfl) ⟨1266713, by rfl⟩ : syracuseStep 1688951 = 2533427) B2533427
theorem B1000847 : Blo 666309 1000847 := bstep (se 1 (by rfl) ⟨750635, by rfl⟩ : syracuseStep 1000847 = 1501271) B1501271
theorem B1000889 : Blo 666309 1000889 := bstep (se 2 (by rfl) ⟨375333, by rfl⟩ : syracuseStep 1000889 = 750667) B750667
theorem B1000967 : Blo 666309 1000967 := bstep (se 1 (by rfl) ⟨750725, by rfl⟩ : syracuseStep 1000967 = 1501451) B1501451
theorem B1001003 : Blo 666309 1001003 := bstep (se 1 (by rfl) ⟨750752, by rfl⟩ : syracuseStep 1001003 = 1501505) B1501505
theorem B1001033 : Blo 666309 1001033 := bstep (se 2 (by rfl) ⟨375387, by rfl⟩ : syracuseStep 1001033 = 750775) B750775
theorem B1001147 : Blo 666309 1001147 := bstep (se 1 (by rfl) ⟨750860, by rfl⟩ : syracuseStep 1001147 = 1501721) B1501721
theorem B804539 : Blo 666309 804539 := bstep (se 1 (by rfl) ⟨603404, by rfl⟩ : syracuseStep 804539 = 1206809) B1206809
theorem B1001207 : Blo 666309 1001207 := bstep (se 1 (by rfl) ⟨750905, by rfl⟩ : syracuseStep 1001207 = 1501811) B1501811
theorem B4572929 : Blo 666309 4572929 := bstep (se 2 (by rfl) ⟨1714848, by rfl⟩ : syracuseStep 4572929 = 3429697) B3429697
theorem B1001231 : Blo 666309 1001231 := bstep (se 1 (by rfl) ⟨750923, by rfl⟩ : syracuseStep 1001231 = 1501847) B1501847
theorem B1427215 : Blo 666309 1427215 := bstep (se 1 (by rfl) ⟨1070411, by rfl⟩ : syracuseStep 1427215 = 2140823) B2140823
theorem B6080305 : Blo 666309 6080305 := bstep (se 2 (by rfl) ⟨2280114, by rfl⟩ : syracuseStep 6080305 = 4560229) B4560229
theorem B1001273 : Blo 666309 1001273 := bstep (se 2 (by rfl) ⟨375477, by rfl⟩ : syracuseStep 1001273 = 750955) B750955
theorem B1001351 : Blo 666309 1001351 := bstep (se 1 (by rfl) ⟨751013, by rfl⟩ : syracuseStep 1001351 = 1502027) B1502027
theorem B1001387 : Blo 666309 1001387 := bstep (se 1 (by rfl) ⟨751040, by rfl⟩ : syracuseStep 1001387 = 1502081) B1502081
theorem B1001417 : Blo 666309 1001417 := bstep (se 2 (by rfl) ⟨375531, by rfl⟩ : syracuseStep 1001417 = 751063) B751063
theorem B1001531 : Blo 666309 1001531 := bstep (se 1 (by rfl) ⟨751148, by rfl⟩ : syracuseStep 1001531 = 1502297) B1502297
theorem B1001591 : Blo 666309 1001591 := bstep (se 1 (by rfl) ⟨751193, by rfl⟩ : syracuseStep 1001591 = 1502387) B1502387
theorem B1001615 : Blo 666309 1001615 := bstep (se 1 (by rfl) ⟨751211, by rfl⟩ : syracuseStep 1001615 = 1502423) B1502423
theorem B1001657 : Blo 666309 1001657 := bstep (se 2 (by rfl) ⟨375621, by rfl⟩ : syracuseStep 1001657 = 751243) B751243
theorem B12503285 : Blo 666309 12503285 := bstep (se 5 (by rfl) ⟨586091, by rfl⟩ : syracuseStep 12503285 = 1172183) B1172183
theorem B1001735 : Blo 666309 1001735 := bstep (se 1 (by rfl) ⟨751301, by rfl⟩ : syracuseStep 1001735 = 1502603) B1502603
theorem B1001771 : Blo 666309 1001771 := bstep (se 1 (by rfl) ⟨751328, by rfl⟩ : syracuseStep 1001771 = 1502657) B1502657
theorem B1001801 : Blo 666309 1001801 := bstep (se 2 (by rfl) ⟨375675, by rfl⟩ : syracuseStep 1001801 = 751351) B751351
theorem B1689943 : Blo 666309 1689943 := bstep (se 1 (by rfl) ⟨1267457, by rfl⟩ : syracuseStep 1689943 = 2534915) B2534915
theorem B1001915 : Blo 666309 1001915 := bstep (se 1 (by rfl) ⟨751436, by rfl⟩ : syracuseStep 1001915 = 1502873) B1502873
theorem B1001975 : Blo 666309 1001975 := bstep (se 1 (by rfl) ⟨751481, by rfl⟩ : syracuseStep 1001975 = 1502963) B1502963
theorem B1001999 : Blo 666309 1001999 := bstep (se 1 (by rfl) ⟨751499, by rfl⟩ : syracuseStep 1001999 = 1502999) B1502999
theorem B1002041 : Blo 666309 1002041 := bstep (se 2 (by rfl) ⟨375765, by rfl⟩ : syracuseStep 1002041 = 751531) B751531
theorem B15419969 : Blo 666309 15419969 := bstep (se 2 (by rfl) ⟨5782488, by rfl⟩ : syracuseStep 15419969 = 11564977) B11564977
theorem B4278851 : Blo 666309 4278851 := bstep (se 1 (by rfl) ⟨3209138, by rfl⟩ : syracuseStep 4278851 = 6418277) B6418277
theorem B1690247 : Blo 666309 1690247 := bstep (se 1 (by rfl) ⟨1267685, by rfl⟩ : syracuseStep 1690247 = 2535371) B2535371
theorem B1002119 : Blo 666309 1002119 := bstep (se 1 (by rfl) ⟨751589, by rfl⟩ : syracuseStep 1002119 = 1503179) B1503179
theorem B1002155 : Blo 666309 1002155 := bstep (se 1 (by rfl) ⟨751616, by rfl⟩ : syracuseStep 1002155 = 1503233) B1503233
theorem B1002185 : Blo 666309 1002185 := bstep (se 2 (by rfl) ⟨375819, by rfl⟩ : syracuseStep 1002185 = 751639) B751639
theorem B903943 : Blo 666309 903943 := bstep (se 1 (by rfl) ⟨677957, by rfl⟩ : syracuseStep 903943 = 1355915) B1355915
theorem B1690379 : Blo 666309 1690379 := bstep (se 1 (by rfl) ⟨1267784, by rfl⟩ : syracuseStep 1690379 = 2535569) B2535569
theorem B3296015 : Blo 666309 3296015 := bstep (se 1 (by rfl) ⟨2472011, by rfl⟩ : syracuseStep 3296015 = 4944023) B4944023
theorem B1002299 : Blo 666309 1002299 := bstep (se 1 (by rfl) ⟨751724, by rfl⟩ : syracuseStep 1002299 = 1503449) B1503449
theorem B1854269 : Blo 666309 1854269 := bstep (se 3 (by rfl) ⟨347675, by rfl⟩ : syracuseStep 1854269 = 695351) B695351
theorem B1002359 : Blo 666309 1002359 := bstep (se 1 (by rfl) ⟨751769, by rfl⟩ : syracuseStep 1002359 = 1503539) B1503539
theorem B1002383 : Blo 666309 1002383 := bstep (se 1 (by rfl) ⟨751787, by rfl⟩ : syracuseStep 1002383 = 1503575) B1503575
theorem B1002425 : Blo 666309 1002425 := bstep (se 2 (by rfl) ⟨375909, by rfl⟩ : syracuseStep 1002425 = 751819) B751819
theorem B8539141 : Blo 666309 8539141 := bstep (se 4 (by rfl) ⟨800544, by rfl⟩ : syracuseStep 8539141 = 1601089) B1601089
theorem B1002503 : Blo 666309 1002503 := bstep (se 1 (by rfl) ⟨751877, by rfl⟩ : syracuseStep 1002503 = 1503755) B1503755
theorem B1002539 : Blo 666309 1002539 := bstep (se 1 (by rfl) ⟨751904, by rfl⟩ : syracuseStep 1002539 = 1503809) B1503809
theorem B6409277 : Blo 666309 6409277 := bstep (se 3 (by rfl) ⟨1201739, by rfl⟩ : syracuseStep 6409277 = 2403479) B2403479
theorem B1002569 : Blo 666309 1002569 := bstep (se 2 (by rfl) ⟨375963, by rfl⟩ : syracuseStep 1002569 = 751927) B751927
theorem B1002683 : Blo 666309 1002683 := bstep (se 1 (by rfl) ⟨752012, by rfl⟩ : syracuseStep 1002683 = 1504025) B1504025
theorem B1002743 : Blo 666309 1002743 := bstep (se 1 (by rfl) ⟨752057, by rfl⟩ : syracuseStep 1002743 = 1504115) B1504115
theorem B1690895 : Blo 666309 1690895 := bstep (se 1 (by rfl) ⟨1268171, by rfl⟩ : syracuseStep 1690895 = 2536343) B2536343
theorem B1002767 : Blo 666309 1002767 := bstep (se 1 (by rfl) ⟨752075, by rfl⟩ : syracuseStep 1002767 = 1504151) B1504151
theorem B1002809 : Blo 666309 1002809 := bstep (se 2 (by rfl) ⟨376053, by rfl⟩ : syracuseStep 1002809 = 752107) B752107
theorem B1002887 : Blo 666309 1002887 := bstep (se 1 (by rfl) ⟨752165, by rfl⟩ : syracuseStep 1002887 = 1504331) B1504331
theorem B1691027 : Blo 666309 1691027 := bstep (se 1 (by rfl) ⟨1268270, by rfl⟩ : syracuseStep 1691027 = 2536541) B2536541
theorem B1002923 : Blo 666309 1002923 := bstep (se 1 (by rfl) ⟨752192, by rfl⟩ : syracuseStep 1002923 = 1504385) B1504385
theorem B1002953 : Blo 666309 1002953 := bstep (se 2 (by rfl) ⟨376107, by rfl⟩ : syracuseStep 1002953 = 752215) B752215
theorem B1265195 : Blo 666309 1265195 := bstep (se 1 (by rfl) ⟨948896, by rfl⟩ : syracuseStep 1265195 = 1897793) B1897793
theorem B2543147 : Blo 666309 2543147 := bstep (se 1 (by rfl) ⟨1907360, by rfl⟩ : syracuseStep 2543147 = 3814721) B3814721
theorem B1003067 : Blo 666309 1003067 := bstep (se 1 (by rfl) ⟨752300, by rfl⟩ : syracuseStep 1003067 = 1504601) B1504601
theorem B1003127 : Blo 666309 1003127 := bstep (se 1 (by rfl) ⟨752345, by rfl⟩ : syracuseStep 1003127 = 1504691) B1504691
theorem B1003151 : Blo 666309 1003151 := bstep (se 1 (by rfl) ⟨752363, by rfl⟩ : syracuseStep 1003151 = 1504727) B1504727
theorem B1003193 : Blo 666309 1003193 := bstep (se 2 (by rfl) ⟨376197, by rfl⟩ : syracuseStep 1003193 = 752395) B752395
theorem B2707145 : Blo 666309 2707145 := bstep (se 2 (by rfl) ⟨1015179, by rfl⟩ : syracuseStep 2707145 = 2030359) B2030359
theorem B1003271 : Blo 666309 1003271 := bstep (se 1 (by rfl) ⟨752453, by rfl⟩ : syracuseStep 1003271 = 1504907) B1504907
theorem B1003307 : Blo 666309 1003307 := bstep (se 1 (by rfl) ⟨752480, by rfl⟩ : syracuseStep 1003307 = 1504961) B1504961
theorem B1003337 : Blo 666309 1003337 := bstep (se 2 (by rfl) ⟨376251, by rfl⟩ : syracuseStep 1003337 = 752503) B752503
theorem B32591767 : Blo 666309 32591767 := bstep (se 1 (by rfl) ⟨24443825, by rfl⟩ : syracuseStep 32591767 = 48887651) B48887651
theorem B1003451 : Blo 666309 1003451 := bstep (se 1 (by rfl) ⟨752588, by rfl⟩ : syracuseStep 1003451 = 1505177) B1505177
theorem B1003511 : Blo 666309 1003511 := bstep (se 1 (by rfl) ⟨752633, by rfl⟩ : syracuseStep 1003511 = 1505267) B1505267
theorem B1003535 : Blo 666309 1003535 := bstep (se 1 (by rfl) ⟨752651, by rfl⟩ : syracuseStep 1003535 = 1505303) B1505303
theorem B1003577 : Blo 666309 1003577 := bstep (se 2 (by rfl) ⟨376341, by rfl⟩ : syracuseStep 1003577 = 752683) B752683
theorem B1003655 : Blo 666309 1003655 := bstep (se 1 (by rfl) ⟨752741, by rfl⟩ : syracuseStep 1003655 = 1505483) B1505483
theorem B1003691 : Blo 666309 1003691 := bstep (se 1 (by rfl) ⟨752768, by rfl⟩ : syracuseStep 1003691 = 1505537) B1505537
theorem B5722285 : Blo 666309 5722285 := bstep (se 3 (by rfl) ⟨1072928, by rfl⟩ : syracuseStep 5722285 = 2145857) B2145857
theorem B1003721 : Blo 666309 1003721 := bstep (se 2 (by rfl) ⟨376395, by rfl⟩ : syracuseStep 1003721 = 752791) B752791
theorem B1003835 : Blo 666309 1003835 := bstep (se 1 (by rfl) ⟨752876, by rfl⟩ : syracuseStep 1003835 = 1505753) B1505753
theorem B1003895 : Blo 666309 1003895 := bstep (se 1 (by rfl) ⟨752921, by rfl⟩ : syracuseStep 1003895 = 1505843) B1505843
theorem B1003919 : Blo 666309 1003919 := bstep (se 1 (by rfl) ⟨752939, by rfl⟩ : syracuseStep 1003919 = 1505879) B1505879
theorem B1003961 : Blo 666309 1003961 := bstep (se 2 (by rfl) ⟨376485, by rfl⟩ : syracuseStep 1003961 = 752971) B752971
theorem B1266121 : Blo 666309 1266121 := bstep (se 2 (by rfl) ⟨474795, by rfl⟩ : syracuseStep 1266121 = 949591) B949591
theorem B1692161 : Blo 666309 1692161 := bstep (se 2 (by rfl) ⟨634560, by rfl⟩ : syracuseStep 1692161 = 1269121) B1269121
theorem B1004039 : Blo 666309 1004039 := bstep (se 1 (by rfl) ⟨753029, by rfl⟩ : syracuseStep 1004039 = 1506059) B1506059
theorem B1004075 : Blo 666309 1004075 := bstep (se 1 (by rfl) ⟨753056, by rfl⟩ : syracuseStep 1004075 = 1506113) B1506113
theorem B1004105 : Blo 666309 1004105 := bstep (se 2 (by rfl) ⟨376539, by rfl⟩ : syracuseStep 1004105 = 753079) B753079
theorem B4280951 : Blo 666309 4280951 := bstep (se 1 (by rfl) ⟨3210713, by rfl⟩ : syracuseStep 4280951 = 6421427) B6421427
theorem B1004219 : Blo 666309 1004219 := bstep (se 1 (by rfl) ⟨753164, by rfl⟩ : syracuseStep 1004219 = 1506329) B1506329
theorem B1004279 : Blo 666309 1004279 := bstep (se 1 (by rfl) ⟨753209, by rfl⟩ : syracuseStep 1004279 = 1506419) B1506419
theorem B5067521 : Blo 666309 5067521 := bstep (se 2 (by rfl) ⟨1900320, by rfl⟩ : syracuseStep 5067521 = 3800641) B3800641
theorem B1004303 : Blo 666309 1004303 := bstep (se 1 (by rfl) ⟨753227, by rfl⟩ : syracuseStep 1004303 = 1506455) B1506455
theorem B1004345 : Blo 666309 1004345 := bstep (se 2 (by rfl) ⟨376629, by rfl⟩ : syracuseStep 1004345 = 753259) B753259
theorem B2249531 : Blo 666309 2249531 := bstep (se 1 (by rfl) ⟨1687148, by rfl⟩ : syracuseStep 2249531 = 3374297) B3374297
theorem B1692535 : Blo 666309 1692535 := bstep (se 1 (by rfl) ⟨1269401, by rfl⟩ : syracuseStep 1692535 = 2538803) B2538803
theorem B1004423 : Blo 666309 1004423 := bstep (se 1 (by rfl) ⟨753317, by rfl⟩ : syracuseStep 1004423 = 1506635) B1506635
theorem B1004459 : Blo 666309 1004459 := bstep (se 1 (by rfl) ⟨753344, by rfl⟩ : syracuseStep 1004459 = 1506689) B1506689
theorem B1004489 : Blo 666309 1004489 := bstep (se 2 (by rfl) ⟨376683, by rfl⟩ : syracuseStep 1004489 = 753367) B753367
theorem B11719685 : Blo 666309 11719685 := bstep (se 4 (by rfl) ⟨1098720, by rfl⟩ : syracuseStep 11719685 = 2197441) B2197441
theorem B1004603 : Blo 666309 1004603 := bstep (se 1 (by rfl) ⟨753452, by rfl⟩ : syracuseStep 1004603 = 1506905) B1506905
theorem B1004663 : Blo 666309 1004663 := bstep (se 1 (by rfl) ⟨753497, by rfl⟩ : syracuseStep 1004663 = 1506995) B1506995
theorem B1004687 : Blo 666309 1004687 := bstep (se 1 (by rfl) ⟨753515, by rfl⟩ : syracuseStep 1004687 = 1507031) B1507031
theorem B1266835 : Blo 666309 1266835 := bstep (se 1 (by rfl) ⟨950126, by rfl⟩ : syracuseStep 1266835 = 1900253) B1900253
theorem B5428397 : Blo 666309 5428397 := bstep (se 3 (by rfl) ⟨1017824, by rfl⟩ : syracuseStep 5428397 = 2035649) B2035649
theorem B1004729 : Blo 666309 1004729 := bstep (se 2 (by rfl) ⟨376773, by rfl⟩ : syracuseStep 1004729 = 753547) B753547
theorem B7623881 : Blo 666309 7623881 := bstep (se 2 (by rfl) ⟨2858955, by rfl⟩ : syracuseStep 7623881 = 5717911) B5717911
theorem B1004807 : Blo 666309 1004807 := bstep (se 1 (by rfl) ⟨753605, by rfl⟩ : syracuseStep 1004807 = 1507211) B1507211
theorem B2250017 : Blo 666309 2250017 := bstep (se 2 (by rfl) ⟨843756, by rfl⟩ : syracuseStep 2250017 = 1687513) B1687513
theorem B1692971 : Blo 666309 1692971 := bstep (se 1 (by rfl) ⟨1269728, by rfl⟩ : syracuseStep 1692971 = 2539457) B2539457
theorem B1004843 : Blo 666309 1004843 := bstep (se 1 (by rfl) ⟨753632, by rfl⟩ : syracuseStep 1004843 = 1507265) B1507265
theorem B677179 : Blo 666309 677179 := bstep (se 1 (by rfl) ⟨507884, by rfl⟩ : syracuseStep 677179 = 1015769) B1015769
theorem B1004873 : Blo 666309 1004873 := bstep (se 2 (by rfl) ⟨376827, by rfl⟩ : syracuseStep 1004873 = 753655) B753655
theorem B4871609 : Blo 666309 4871609 := bstep (se 2 (by rfl) ⟨1826853, by rfl⟩ : syracuseStep 4871609 = 3653707) B3653707
theorem B1004987 : Blo 666309 1004987 := bstep (se 1 (by rfl) ⟨753740, by rfl⟩ : syracuseStep 1004987 = 1507481) B1507481
theorem B2414033 : Blo 666309 2414033 := bstep (se 2 (by rfl) ⟨905262, by rfl⟩ : syracuseStep 2414033 = 1810525) B1810525
theorem B7230941 : Blo 666309 7230941 := bstep (se 3 (by rfl) ⟨1355801, by rfl⟩ : syracuseStep 7230941 = 2711603) B2711603
theorem B1005047 : Blo 666309 1005047 := bstep (se 1 (by rfl) ⟨753785, by rfl⟩ : syracuseStep 1005047 = 1507571) B1507571
theorem B1005071 : Blo 666309 1005071 := bstep (se 1 (by rfl) ⟨753803, by rfl⟩ : syracuseStep 1005071 = 1507607) B1507607
theorem B1005113 : Blo 666309 1005113 := bstep (se 2 (by rfl) ⟨376917, by rfl⟩ : syracuseStep 1005113 = 753835) B753835
theorem B1005191 : Blo 666309 1005191 := bstep (se 1 (by rfl) ⟨753893, by rfl⟩ : syracuseStep 1005191 = 1507787) B1507787
theorem B1005227 : Blo 666309 1005227 := bstep (se 1 (by rfl) ⟨753920, by rfl⟩ : syracuseStep 1005227 = 1507841) B1507841
theorem B1005257 : Blo 666309 1005257 := bstep (se 2 (by rfl) ⟨376971, by rfl⟩ : syracuseStep 1005257 = 753943) B753943
theorem B1005371 : Blo 666309 1005371 := bstep (se 1 (by rfl) ⟨754028, by rfl⟩ : syracuseStep 1005371 = 1508057) B1508057
theorem B2250611 : Blo 666309 2250611 := bstep (se 1 (by rfl) ⟨1687958, by rfl⟩ : syracuseStep 2250611 = 3375917) B3375917
theorem B1005431 : Blo 666309 1005431 := bstep (se 1 (by rfl) ⟨754073, by rfl⟩ : syracuseStep 1005431 = 1508147) B1508147
theorem B1005455 : Blo 666309 1005455 := bstep (se 1 (by rfl) ⟨754091, by rfl⟩ : syracuseStep 1005455 = 1508183) B1508183
theorem B7329689 : Blo 666309 7329689 := bstep (se 2 (by rfl) ⟨2748633, by rfl⟩ : syracuseStep 7329689 = 5497267) B5497267
theorem B1693811 : Blo 666309 1693811 := bstep (se 1 (by rfl) ⟨1270358, by rfl⟩ : syracuseStep 1693811 = 2540717) B2540717
theorem B2709623 : Blo 666309 2709623 := bstep (se 1 (by rfl) ⟨2032217, by rfl⟩ : syracuseStep 2709623 = 4064435) B4064435
theorem B1693831 : Blo 666309 1693831 := bstep (se 1 (by rfl) ⟨1270373, by rfl⟩ : syracuseStep 1693831 = 2540747) B2540747
theorem B4282541 : Blo 666309 4282541 := bstep (se 3 (by rfl) ⟨802976, by rfl⟩ : syracuseStep 4282541 = 1605953) B1605953
theorem B1267913 : Blo 666309 1267913 := bstep (se 2 (by rfl) ⟨475467, by rfl⟩ : syracuseStep 1267913 = 950935) B950935
theorem B1694105 : Blo 666309 1694105 := bstep (se 2 (by rfl) ⟨635289, by rfl⟩ : syracuseStep 1694105 = 1270579) B1270579
theorem B1694267 : Blo 666309 1694267 := bstep (se 1 (by rfl) ⟨1270700, by rfl⟩ : syracuseStep 1694267 = 2541401) B2541401
theorem B1694479 : Blo 666309 1694479 := bstep (se 1 (by rfl) ⟨1270859, by rfl⟩ : syracuseStep 1694479 = 2541719) B2541719
theorem B1694753 : Blo 666309 1694753 := bstep (se 2 (by rfl) ⟨635532, by rfl⟩ : syracuseStep 1694753 = 1271065) B1271065
theorem B1268779 : Blo 666309 1268779 := bstep (se 1 (by rfl) ⟨951584, by rfl⟩ : syracuseStep 1268779 = 1903169) B1903169
theorem B1268855 : Blo 666309 1268855 := bstep (se 1 (by rfl) ⟨951641, by rfl⟩ : syracuseStep 1268855 = 1903283) B1903283
theorem B3530263 : Blo 666309 3530263 := bstep (se 1 (by rfl) ⟨2647697, by rfl⟩ : syracuseStep 3530263 = 5295395) B5295395
theorem B3202679 : Blo 666309 3202679 := bstep (se 1 (by rfl) ⟨2402009, by rfl⟩ : syracuseStep 3202679 = 4804019) B4804019
theorem B1072775 : Blo 666309 1072775 := bstep (se 1 (by rfl) ⟨804581, by rfl⟩ : syracuseStep 1072775 = 1609163) B1609163
theorem B14868269 : Blo 666309 14868269 := bstep (se 3 (by rfl) ⟨2787800, by rfl⟩ : syracuseStep 14868269 = 5575601) B5575601
theorem B843691 : Blo 666309 843691 := bstep (se 1 (by rfl) ⟨632768, by rfl⟩ : syracuseStep 843691 = 1265537) B1265537
theorem B1695755 : Blo 666309 1695755 := bstep (se 1 (by rfl) ⟨1271816, by rfl⟩ : syracuseStep 1695755 = 2543633) B2543633
theorem B3203101 : Blo 666309 3203101 := bstep (se 3 (by rfl) ⟨600581, by rfl⟩ : syracuseStep 3203101 = 1201163) B1201163
theorem B7626797 : Blo 666309 7626797 := bstep (se 3 (by rfl) ⟨1430024, by rfl⟩ : syracuseStep 7626797 = 2860049) B2860049
theorem B1499255 : Blo 666309 1499255 := bstep (se 1 (by rfl) ⟨1124441, by rfl⟩ : syracuseStep 1499255 = 2248883) B2248883
theorem B1499435 : Blo 666309 1499435 := bstep (se 1 (by rfl) ⟨1124576, by rfl⟩ : syracuseStep 1499435 = 2249153) B2249153
theorem B2253203 : Blo 666309 2253203 := bstep (se 1 (by rfl) ⟨1689902, by rfl⟩ : syracuseStep 2253203 = 3379805) B3379805
theorem B3858947 : Blo 666309 3858947 := bstep (se 1 (by rfl) ⟨2894210, by rfl⟩ : syracuseStep 3858947 = 5788421) B5788421
theorem B1499795 : Blo 666309 1499795 := bstep (se 1 (by rfl) ⟨1124846, by rfl⟩ : syracuseStep 1499795 = 2249693) B2249693
theorem B1696403 : Blo 666309 1696403 := bstep (se 1 (by rfl) ⟨1272302, by rfl⟩ : syracuseStep 1696403 = 2544605) B2544605
theorem B1499849 : Blo 666309 1499849 := bstep (se 2 (by rfl) ⟨562443, by rfl⟩ : syracuseStep 1499849 = 1124887) B1124887
theorem B844663 : Blo 666309 844663 := bstep (se 1 (by rfl) ⟨633497, by rfl⟩ : syracuseStep 844663 = 1266995) B1266995
theorem B1696697 : Blo 666309 1696697 := bstep (se 2 (by rfl) ⟨636261, by rfl⟩ : syracuseStep 1696697 = 1272523) B1272523
theorem B1270799 : Blo 666309 1270799 := bstep (se 1 (by rfl) ⟨953099, by rfl⟩ : syracuseStep 1270799 = 1906199) B1906199
theorem B5071895 : Blo 666309 5071895 := bstep (se 1 (by rfl) ⟨3803921, by rfl⟩ : syracuseStep 5071895 = 7607843) B7607843
theorem B844987 : Blo 666309 844987 := bstep (se 1 (by rfl) ⟨633740, by rfl⟩ : syracuseStep 844987 = 1267481) B1267481
theorem B17097965 : Blo 666309 17097965 := bstep (se 3 (by rfl) ⟨3205868, by rfl⟩ : syracuseStep 17097965 = 6411737) B6411737
theorem B1926433 : Blo 666309 1926433 := bstep (se 2 (by rfl) ⟨722412, by rfl⟩ : syracuseStep 1926433 = 1444825) B1444825
theorem B714043 : Blo 666309 714043 := bstep (se 1 (by rfl) ⟨535532, by rfl⟩ : syracuseStep 714043 = 1071065) B1071065
theorem B48850289 : Blo 666309 48850289 := bstep (se 2 (by rfl) ⟨18318858, by rfl⟩ : syracuseStep 48850289 = 36637717) B36637717
theorem B1500551 : Blo 666309 1500551 := bstep (se 1 (by rfl) ⟨1125413, by rfl⟩ : syracuseStep 1500551 = 2250827) B2250827
theorem B1500731 : Blo 666309 1500731 := bstep (se 1 (by rfl) ⟨1125548, by rfl⟩ : syracuseStep 1500731 = 2251097) B2251097
theorem B1500857 : Blo 666309 1500857 := bstep (se 2 (by rfl) ⟨562821, by rfl⟩ : syracuseStep 1500857 = 1125643) B1125643
theorem B2254607 : Blo 666309 2254607 := bstep (se 1 (by rfl) ⟨1690955, by rfl⟩ : syracuseStep 2254607 = 3381911) B3381911
theorem B4351781 : Blo 666309 4351781 := bstep (se 4 (by rfl) ⟨407979, by rfl⟩ : syracuseStep 4351781 = 815959) B815959
theorem B14444405 : Blo 666309 14444405 := bstep (se 5 (by rfl) ⟨677081, by rfl⟩ : syracuseStep 14444405 = 1354163) B1354163
theorem B1501199 : Blo 666309 1501199 := bstep (se 1 (by rfl) ⟨1125899, by rfl⟩ : syracuseStep 1501199 = 2251799) B2251799
theorem B2254877 : Blo 666309 2254877 := bstep (se 3 (by rfl) ⟨422789, by rfl⟩ : syracuseStep 2254877 = 845579) B845579
theorem B1501217 : Blo 666309 1501217 := bstep (se 2 (by rfl) ⟨562956, by rfl⟩ : syracuseStep 1501217 = 1125913) B1125913
theorem B813115 : Blo 666309 813115 := bstep (se 1 (by rfl) ⟨609836, by rfl⟩ : syracuseStep 813115 = 1219673) B1219673
theorem B845959 : Blo 666309 845959 := bstep (se 1 (by rfl) ⟨634469, by rfl⟩ : syracuseStep 845959 = 1268939) B1268939
theorem B3467501 : Blo 666309 3467501 := bstep (se 3 (by rfl) ⟨650156, by rfl⟩ : syracuseStep 3467501 = 1300313) B1300313
theorem B1501559 : Blo 666309 1501559 := bstep (se 1 (by rfl) ⟨1126169, by rfl⟩ : syracuseStep 1501559 = 2252339) B2252339
theorem B3795335 : Blo 666309 3795335 := bstep (se 1 (by rfl) ⟨2846501, by rfl⟩ : syracuseStep 3795335 = 5693003) B5693003
theorem B3860995 : Blo 666309 3860995 := bstep (se 1 (by rfl) ⟨2895746, by rfl⟩ : syracuseStep 3860995 = 5791493) B5791493
theorem B1501739 : Blo 666309 1501739 := bstep (se 1 (by rfl) ⟨1126304, by rfl⟩ : syracuseStep 1501739 = 2252609) B2252609
theorem B846379 : Blo 666309 846379 := bstep (se 1 (by rfl) ⟨634784, by rfl⟩ : syracuseStep 846379 = 1269569) B1269569
theorem B9660971 : Blo 666309 9660971 := bstep (se 1 (by rfl) ⟨7245728, by rfl⟩ : syracuseStep 9660971 = 14491457) B14491457
theorem B1272439 : Blo 666309 1272439 := bstep (se 1 (by rfl) ⟨954329, by rfl⟩ : syracuseStep 1272439 = 1908659) B1908659
theorem B846607 : Blo 666309 846607 := bstep (se 1 (by rfl) ⟨634955, by rfl⟩ : syracuseStep 846607 = 1269911) B1269911
theorem B1502099 : Blo 666309 1502099 := bstep (se 1 (by rfl) ⟨1126574, by rfl⟩ : syracuseStep 1502099 = 2253149) B2253149
theorem B1502153 : Blo 666309 1502153 := bstep (se 2 (by rfl) ⟨563307, by rfl⟩ : syracuseStep 1502153 = 1126615) B1126615
theorem B8219659 : Blo 666309 8219659 := bstep (se 1 (by rfl) ⟨6164744, by rfl⟩ : syracuseStep 8219659 = 12329489) B12329489
theorem B2256281 : Blo 666309 2256281 := bstep (se 2 (by rfl) ⟨846105, by rfl⟩ : syracuseStep 2256281 = 1692211) B1692211
theorem B3206621 : Blo 666309 3206621 := bstep (se 3 (by rfl) ⟨601241, by rfl⟩ : syracuseStep 3206621 = 1202483) B1202483
theorem B847351 : Blo 666309 847351 := bstep (se 1 (by rfl) ⟨635513, by rfl⟩ : syracuseStep 847351 = 1271027) B1271027
theorem B1928747 : Blo 666309 1928747 := bstep (se 1 (by rfl) ⟨1446560, by rfl⟩ : syracuseStep 1928747 = 2893121) B2893121
theorem B3796541 : Blo 666309 3796541 := bstep (se 3 (by rfl) ⟨711851, by rfl⟩ : syracuseStep 3796541 = 1423703) B1423703
theorem B28929635 : Blo 666309 28929635 := bstep (se 1 (by rfl) ⟨21697226, by rfl⟩ : syracuseStep 28929635 = 43394453) B43394453
theorem B1502855 : Blo 666309 1502855 := bstep (se 1 (by rfl) ⟨1127141, by rfl⟩ : syracuseStep 1502855 = 2254283) B2254283
theorem B6844121 : Blo 666309 6844121 := bstep (se 2 (by rfl) ⟨2566545, by rfl⟩ : syracuseStep 6844121 = 5133091) B5133091
theorem B1503035 : Blo 666309 1503035 := bstep (se 1 (by rfl) ⟨1127276, by rfl⟩ : syracuseStep 1503035 = 2254553) B2254553
theorem B847675 : Blo 666309 847675 := bstep (se 1 (by rfl) ⟨635756, by rfl⟩ : syracuseStep 847675 = 1271513) B1271513
theorem B1929113 : Blo 666309 1929113 := bstep (se 2 (by rfl) ⟨723417, by rfl⟩ : syracuseStep 1929113 = 1446835) B1446835
theorem B1503161 : Blo 666309 1503161 := bstep (se 2 (by rfl) ⟨563685, by rfl⟩ : syracuseStep 1503161 = 1127371) B1127371
theorem B2256983 : Blo 666309 2256983 := bstep (se 1 (by rfl) ⟨1692737, by rfl⟩ : syracuseStep 2256983 = 3385475) B3385475
theorem B749839 : Blo 666309 749839 := bstep (se 1 (by rfl) ⟨562379, by rfl⟩ : syracuseStep 749839 = 1124759) B1124759
theorem B1503503 : Blo 666309 1503503 := bstep (se 1 (by rfl) ⟨1127627, by rfl⟩ : syracuseStep 1503503 = 2255255) B2255255
theorem B1503521 : Blo 666309 1503521 := bstep (se 2 (by rfl) ⟨563820, by rfl⟩ : syracuseStep 1503521 = 1127641) B1127641
theorem B848171 : Blo 666309 848171 := bstep (se 1 (by rfl) ⟨636128, by rfl⟩ : syracuseStep 848171 = 1272257) B1272257
theorem B1601927 : Blo 666309 1601927 := bstep (se 1 (by rfl) ⟨1201445, by rfl⟩ : syracuseStep 1601927 = 2402891) B2402891
theorem B2290187 : Blo 666309 2290187 := bstep (se 1 (by rfl) ⟨1717640, by rfl⟩ : syracuseStep 2290187 = 3435281) B3435281
theorem B24441365 : Blo 666309 24441365 := bstep (se 6 (by rfl) ⟨572844, by rfl⟩ : syracuseStep 24441365 = 1145689) B1145689
theorem B2257469 : Blo 666309 2257469 := bstep (se 3 (by rfl) ⟨423275, by rfl⟩ : syracuseStep 2257469 = 846551) B846551
theorem B1503863 : Blo 666309 1503863 := bstep (se 1 (by rfl) ⟨1127897, by rfl⟩ : syracuseStep 1503863 = 2255795) B2255795
theorem B750343 : Blo 666309 750343 := bstep (se 1 (by rfl) ⟨562757, by rfl⟩ : syracuseStep 750343 = 1125515) B1125515
theorem B1504043 : Blo 666309 1504043 := bstep (se 1 (by rfl) ⟨1128032, by rfl⟩ : syracuseStep 1504043 = 2256065) B2256065
theorem B1340345 : Blo 666309 1340345 := bstep (se 2 (by rfl) ⟨502629, by rfl⟩ : syracuseStep 1340345 = 1005259) B1005259
theorem B750523 : Blo 666309 750523 := bstep (se 1 (by rfl) ⟨562892, by rfl⟩ : syracuseStep 750523 = 1125785) B1125785
theorem B816143 : Blo 666309 816143 := bstep (se 1 (by rfl) ⟨612107, by rfl⟩ : syracuseStep 816143 = 1224215) B1224215
theorem B1504403 : Blo 666309 1504403 := bstep (se 1 (by rfl) ⟨1128302, by rfl⟩ : syracuseStep 1504403 = 2256605) B2256605
theorem B1504457 : Blo 666309 1504457 := bstep (se 2 (by rfl) ⟨564171, by rfl⟩ : syracuseStep 1504457 = 1128343) B1128343
theorem B750991 : Blo 666309 750991 := bstep (se 1 (by rfl) ⟨563243, by rfl⟩ : syracuseStep 750991 = 1126487) B1126487
theorem B4814225 : Blo 666309 4814225 := bstep (se 2 (by rfl) ⟨1805334, by rfl⟩ : syracuseStep 4814225 = 3610669) B3610669
theorem B914873 : Blo 666309 914873 := bstep (se 2 (by rfl) ⟨343077, by rfl⟩ : syracuseStep 914873 = 686155) B686155
theorem B1013239 : Blo 666309 1013239 := bstep (se 1 (by rfl) ⟨759929, by rfl⟩ : syracuseStep 1013239 = 1519859) B1519859
theorem B751495 : Blo 666309 751495 := bstep (se 1 (by rfl) ⟨563621, by rfl⟩ : syracuseStep 751495 = 1127243) B1127243
theorem B1505159 : Blo 666309 1505159 := bstep (se 1 (by rfl) ⟨1128869, by rfl⟩ : syracuseStep 1505159 = 2257739) B2257739
theorem B3602323 : Blo 666309 3602323 := bstep (se 1 (by rfl) ⟨2701742, by rfl⟩ : syracuseStep 3602323 = 5403485) B5403485
theorem B2258873 : Blo 666309 2258873 := bstep (se 2 (by rfl) ⟨847077, by rfl⟩ : syracuseStep 2258873 = 1694155) B1694155
theorem B751675 : Blo 666309 751675 := bstep (se 1 (by rfl) ⟨563756, by rfl⟩ : syracuseStep 751675 = 1127513) B1127513
theorem B1505339 : Blo 666309 1505339 := bstep (se 1 (by rfl) ⟨1129004, by rfl⟩ : syracuseStep 1505339 = 2258009) B2258009
theorem B1505465 : Blo 666309 1505465 := bstep (se 2 (by rfl) ⟨564549, by rfl⟩ : syracuseStep 1505465 = 1129099) B1129099
theorem B1898795 : Blo 666309 1898795 := bstep (se 1 (by rfl) ⟨1424096, by rfl⟩ : syracuseStep 1898795 = 2848193) B2848193
theorem B1603955 : Blo 666309 1603955 := bstep (se 1 (by rfl) ⟨1202966, by rfl⟩ : syracuseStep 1603955 = 2405933) B2405933
theorem B2259467 : Blo 666309 2259467 := bstep (se 1 (by rfl) ⟨1694600, by rfl⟩ : syracuseStep 2259467 = 3389201) B3389201
theorem B752143 : Blo 666309 752143 := bstep (se 1 (by rfl) ⟨564107, by rfl⟩ : syracuseStep 752143 = 1128215) B1128215
theorem B1505807 : Blo 666309 1505807 := bstep (se 1 (by rfl) ⟨1129355, by rfl⟩ : syracuseStep 1505807 = 2258711) B2258711
theorem B1505825 : Blo 666309 1505825 := bstep (se 2 (by rfl) ⟨564684, by rfl⟩ : syracuseStep 1505825 = 1129369) B1129369
theorem B2259575 : Blo 666309 2259575 := bstep (se 1 (by rfl) ⟨1694681, by rfl⟩ : syracuseStep 2259575 = 3389363) B3389363
theorem B1604281 : Blo 666309 1604281 := bstep (se 2 (by rfl) ⟨601605, by rfl⟩ : syracuseStep 1604281 = 1203211) B1203211
theorem B1014601 : Blo 666309 1014601 := bstep (se 2 (by rfl) ⟨380475, by rfl⟩ : syracuseStep 1014601 = 760951) B760951
theorem B1506167 : Blo 666309 1506167 := bstep (se 1 (by rfl) ⟨1129625, by rfl⟩ : syracuseStep 1506167 = 2259251) B2259251
theorem B1801217 : Blo 666309 1801217 := bstep (se 2 (by rfl) ⟨675456, by rfl⟩ : syracuseStep 1801217 = 1350913) B1350913
theorem B752647 : Blo 666309 752647 := bstep (se 1 (by rfl) ⟨564485, by rfl⟩ : syracuseStep 752647 = 1128971) B1128971
theorem B1506347 : Blo 666309 1506347 := bstep (se 1 (by rfl) ⟨1129760, by rfl⟩ : syracuseStep 1506347 = 2259521) B2259521
theorem B752827 : Blo 666309 752827 := bstep (se 1 (by rfl) ⟨564620, by rfl⟩ : syracuseStep 752827 = 1129241) B1129241
theorem B2260169 : Blo 666309 2260169 := bstep (se 2 (by rfl) ⟨847563, by rfl⟩ : syracuseStep 2260169 = 1695127) B1695127
theorem B1604897 : Blo 666309 1604897 := bstep (se 2 (by rfl) ⟨601836, by rfl⟩ : syracuseStep 1604897 = 1203673) B1203673
theorem B1899911 : Blo 666309 1899911 := bstep (se 1 (by rfl) ⟨1424933, by rfl⟩ : syracuseStep 1899911 = 2849867) B2849867
theorem B1506707 : Blo 666309 1506707 := bstep (se 1 (by rfl) ⟨1130030, by rfl⟩ : syracuseStep 1506707 = 2260061) B2260061
theorem B1506761 : Blo 666309 1506761 := bstep (se 2 (by rfl) ⟨565035, by rfl⟩ : syracuseStep 1506761 = 1130071) B1130071
theorem B3374621 : Blo 666309 3374621 := bstep (se 3 (by rfl) ⟨632741, by rfl⟩ : syracuseStep 3374621 = 1265483) B1265483
theorem B949819 : Blo 666309 949819 := bstep (se 1 (by rfl) ⟨712364, by rfl⟩ : syracuseStep 949819 = 1424729) B1424729
theorem B1900093 : Blo 666309 1900093 := bstep (se 3 (by rfl) ⟨356267, by rfl⟩ : syracuseStep 1900093 = 712535) B712535
theorem B753295 : Blo 666309 753295 := bstep (se 1 (by rfl) ⟨564971, by rfl⟩ : syracuseStep 753295 = 1129943) B1129943
theorem B1605511 : Blo 666309 1605511 := bstep (se 1 (by rfl) ⟨1204133, by rfl⟩ : syracuseStep 1605511 = 2408267) B2408267
theorem B2260871 : Blo 666309 2260871 := bstep (se 1 (by rfl) ⟨1695653, by rfl⟩ : syracuseStep 2260871 = 3391307) B3391307
theorem B1900435 : Blo 666309 1900435 := bstep (se 1 (by rfl) ⟨1425326, by rfl⟩ : syracuseStep 1900435 = 2850653) B2850653
theorem B10846223 : Blo 666309 10846223 := bstep (se 1 (by rfl) ⟨8134667, by rfl⟩ : syracuseStep 10846223 = 16269335) B16269335
theorem B2031635 : Blo 666309 2031635 := bstep (se 1 (by rfl) ⟨1523726, by rfl⟩ : syracuseStep 2031635 = 3047453) B3047453
theorem B1507499 : Blo 666309 1507499 := bstep (se 1 (by rfl) ⟨1130624, by rfl⟩ : syracuseStep 1507499 = 2261249) B2261249
theorem B8552627 : Blo 666309 8552627 := bstep (se 1 (by rfl) ⟨6414470, by rfl⟩ : syracuseStep 8552627 = 12828941) B12828941
theorem B13730123 : Blo 666309 13730123 := bstep (se 1 (by rfl) ⟨10297592, by rfl⟩ : syracuseStep 13730123 = 20595185) B20595185
theorem B754015 : Blo 666309 754015 := bstep (se 1 (by rfl) ⟨565511, by rfl⟩ : syracuseStep 754015 = 1131023) B1131023
theorem B73073137 : Blo 666309 73073137 := bstep (se 2 (by rfl) ⟨27402426, by rfl⟩ : syracuseStep 73073137 = 54804853) B54804853
theorem B2261627 : Blo 666309 2261627 := bstep (se 1 (by rfl) ⟨1696220, by rfl⟩ : syracuseStep 2261627 = 3392441) B3392441
theorem B1508039 : Blo 666309 1508039 := bstep (se 1 (by rfl) ⟨1131029, by rfl⟩ : syracuseStep 1508039 = 2262059) B2262059
theorem B2261789 : Blo 666309 2261789 := bstep (se 3 (by rfl) ⟨424085, by rfl⟩ : syracuseStep 2261789 = 848171) B848171
theorem B10290071 : Blo 666309 10290071 := bstep (se 1 (by rfl) ⟨7717553, by rfl⟩ : syracuseStep 10290071 = 15435107) B15435107
theorem B1901495 : Blo 666309 1901495 := bstep (se 1 (by rfl) ⟨1426121, by rfl⟩ : syracuseStep 1901495 = 2852243) B2852243
theorem B2753551 : Blo 666309 2753551 := bstep (se 1 (by rfl) ⟨2065163, by rfl⟩ : syracuseStep 2753551 = 4130327) B4130327
theorem B3048619 : Blo 666309 3048619 := bstep (se 1 (by rfl) ⟨2286464, by rfl⟩ : syracuseStep 3048619 = 4572929) B4572929
theorem B722119 : Blo 666309 722119 := bstep (se 1 (by rfl) ⟨541589, by rfl⟩ : syracuseStep 722119 = 1083179) B1083179
theorem B1017193 : Blo 666309 1017193 := bstep (se 2 (by rfl) ⟨381447, by rfl⟩ : syracuseStep 1017193 = 762895) B762895
theorem B7210403 : Blo 666309 7210403 := bstep (se 1 (by rfl) ⟨5407802, by rfl⟩ : syracuseStep 7210403 = 10815605) B10815605
theorem B2033191 : Blo 666309 2033191 := bstep (se 1 (by rfl) ⟨1524893, by rfl⟩ : syracuseStep 2033191 = 3049787) B3049787
theorem B2852567 : Blo 666309 2852567 := bstep (se 1 (by rfl) ⟨2139425, by rfl⟩ : syracuseStep 2852567 = 4278851) B4278851
theorem B7210745 : Blo 666309 7210745 := bstep (se 2 (by rfl) ⟨2704029, by rfl⟩ : syracuseStep 7210745 = 5408059) B5408059
theorem B3376889 : Blo 666309 3376889 := bstep (se 2 (by rfl) ⟨1266333, by rfl⟩ : syracuseStep 3376889 = 2532667) B2532667
theorem B952057 : Blo 666309 952057 := bstep (se 2 (by rfl) ⟨357021, by rfl⟩ : syracuseStep 952057 = 714043) B714043
theorem B2197343 : Blo 666309 2197343 := bstep (se 1 (by rfl) ⟨1648007, by rfl⟩ : syracuseStep 2197343 = 3296015) B3296015
theorem B1902599 : Blo 666309 1902599 := bstep (se 1 (by rfl) ⟨1426949, by rfl⟩ : syracuseStep 1902599 = 2853899) B2853899
theorem B1902953 : Blo 666309 1902953 := bstep (se 2 (by rfl) ⟨713607, by rfl⟩ : syracuseStep 1902953 = 1427215) B1427215
theorem B3377537 : Blo 666309 3377537 := bstep (se 2 (by rfl) ⟨1266576, by rfl⟩ : syracuseStep 3377537 = 2533153) B2533153
theorem B9767303 : Blo 666309 9767303 := bstep (se 1 (by rfl) ⟨7325477, by rfl⟩ : syracuseStep 9767303 = 14650955) B14650955
theorem B1804763 : Blo 666309 1804763 := bstep (se 1 (by rfl) ⟨1353572, by rfl⟩ : syracuseStep 1804763 = 2707145) B2707145
theorem B3574253 : Blo 666309 3574253 := bstep (se 3 (by rfl) ⟨670172, by rfl⟩ : syracuseStep 3574253 = 1340345) B1340345
theorem B1084153 : Blo 666309 1084153 := bstep (se 2 (by rfl) ⟨406557, by rfl⟩ : syracuseStep 1084153 = 813115) B813115
theorem B2853967 : Blo 666309 2853967 := bstep (se 1 (by rfl) ⟨2140475, by rfl⟩ : syracuseStep 2853967 = 4280951) B4280951
theorem B3378347 : Blo 666309 3378347 := bstep (se 1 (by rfl) ⟨2533760, by rfl⟩ : syracuseStep 3378347 = 5067521) B5067521
theorem B5147993 : Blo 666309 5147993 := bstep (se 2 (by rfl) ⟨1930497, by rfl⟩ : syracuseStep 5147993 = 3860995) B3860995
theorem B5082587 : Blo 666309 5082587 := bstep (se 1 (by rfl) ⟨3811940, by rfl⟩ : syracuseStep 5082587 = 7623881) B7623881
theorem B3247739 : Blo 666309 3247739 := bstep (se 1 (by rfl) ⟨2435804, by rfl⟩ : syracuseStep 3247739 = 4871609) B4871609
theorem B1609355 : Blo 666309 1609355 := bstep (se 1 (by rfl) ⟨1207016, by rfl⟩ : syracuseStep 1609355 = 2414033) B2414033
theorem B3378833 : Blo 666309 3378833 := bstep (se 2 (by rfl) ⟨1267062, by rfl⟩ : syracuseStep 3378833 = 2534125) B2534125
theorem B4820627 : Blo 666309 4820627 := bstep (se 1 (by rfl) ⟨3615470, by rfl⟩ : syracuseStep 4820627 = 7230941) B7230941
theorem B10817347 : Blo 666309 10817347 := bstep (se 1 (by rfl) ⟨8113010, by rfl⟩ : syracuseStep 10817347 = 16226021) B16226021
theorem B4886459 : Blo 666309 4886459 := bstep (se 1 (by rfl) ⟨3664844, by rfl⟩ : syracuseStep 4886459 = 7329689) B7329689
theorem B5083073 : Blo 666309 5083073 := bstep (se 2 (by rfl) ⟨1906152, by rfl⟩ : syracuseStep 5083073 = 3812305) B3812305
theorem B4821029 : Blo 666309 4821029 := bstep (se 4 (by rfl) ⟨451971, by rfl⟩ : syracuseStep 4821029 = 903943) B903943
theorem B2855027 : Blo 666309 2855027 := bstep (se 1 (by rfl) ⟨2141270, by rfl⟩ : syracuseStep 2855027 = 4282541) B4282541
theorem B4330169 : Blo 666309 4330169 := bstep (se 2 (by rfl) ⟨1623813, by rfl⟩ : syracuseStep 4330169 = 3247627) B3247627
theorem B1905515 : Blo 666309 1905515 := bstep (se 1 (by rfl) ⟨1429136, by rfl⟩ : syracuseStep 1905515 = 2858273) B2858273
theorem B1905743 : Blo 666309 1905743 := bstep (se 1 (by rfl) ⟨1429307, by rfl⟩ : syracuseStep 1905743 = 2858615) B2858615
theorem B43455689 : Blo 666309 43455689 := bstep (se 2 (by rfl) ⟨16295883, by rfl⟩ : syracuseStep 43455689 = 32591767) B32591767
theorem B5084531 : Blo 666309 5084531 := bstep (se 1 (by rfl) ⟨3813398, by rfl⟩ : syracuseStep 5084531 = 7626797) B7626797
theorem B10851985 : Blo 666309 10851985 := bstep (se 2 (by rfl) ⟨4069494, by rfl⟩ : syracuseStep 10851985 = 8138989) B8138989
theorem B3381101 : Blo 666309 3381101 := bstep (se 3 (by rfl) ⟨633956, by rfl⟩ : syracuseStep 3381101 = 1267913) B1267913
theorem B3381263 : Blo 666309 3381263 := bstep (se 1 (by rfl) ⟨2535947, by rfl⟩ : syracuseStep 3381263 = 5071895) B5071895
theorem B2136221 : Blo 666309 2136221 := bstep (se 3 (by rfl) ⟨400541, by rfl⟩ : syracuseStep 2136221 = 801083) B801083
theorem B3217751 : Blo 666309 3217751 := bstep (se 1 (by rfl) ⟨2413313, by rfl⟩ : syracuseStep 3217751 = 4826627) B4826627
theorem B2530223 : Blo 666309 2530223 := bstep (se 1 (by rfl) ⟨1897667, by rfl⟩ : syracuseStep 2530223 = 3795335) B3795335
theorem B3611621 : Blo 666309 3611621 := bstep (se 4 (by rfl) ⟨338589, by rfl⟩ : syracuseStep 3611621 = 677179) B677179
theorem B2137747 : Blo 666309 2137747 := bstep (se 1 (by rfl) ⟨1603310, by rfl⟩ : syracuseStep 2137747 = 3206621) B3206621
theorem B1285831 : Blo 666309 1285831 := bstep (se 1 (by rfl) ⟨964373, by rfl⟩ : syracuseStep 1285831 = 1928747) B1928747
theorem B2531027 : Blo 666309 2531027 := bstep (se 1 (by rfl) ⟨1898270, by rfl⟩ : syracuseStep 2531027 = 3796541) B3796541
theorem B4562747 : Blo 666309 4562747 := bstep (se 1 (by rfl) ⟨3422060, by rfl⟩ : syracuseStep 4562747 = 6844121) B6844121
theorem B1286075 : Blo 666309 1286075 := bstep (se 1 (by rfl) ⟨964556, by rfl⟩ : syracuseStep 1286075 = 1929113) B1929113
theorem B16294243 : Blo 666309 16294243 := bstep (se 1 (by rfl) ⟨12220682, by rfl⟩ : syracuseStep 16294243 = 24441365) B24441365
theorem B3384017 : Blo 666309 3384017 := bstep (se 2 (by rfl) ⟨1269006, by rfl⟩ : syracuseStep 3384017 = 2538013) B2538013
theorem B2139041 : Blo 666309 2139041 := bstep (se 2 (by rfl) ⟨802140, by rfl⟩ : syracuseStep 2139041 = 1604281) B1604281
theorem B1352801 : Blo 666309 1352801 := bstep (se 2 (by rfl) ⟨507300, by rfl⟩ : syracuseStep 1352801 = 1014601) B1014601
theorem B2860733 : Blo 666309 2860733 := bstep (se 3 (by rfl) ⟨536387, by rfl⟩ : syracuseStep 2860733 = 1072775) B1072775
theorem B2533457 : Blo 666309 2533457 := bstep (se 2 (by rfl) ⟨950046, by rfl⟩ : syracuseStep 2533457 = 1900093) B1900093
theorem B2140681 : Blo 666309 2140681 := bstep (se 2 (by rfl) ⟨802755, by rfl⟩ : syracuseStep 2140681 = 1605511) B1605511
theorem B2533913 : Blo 666309 2533913 := bstep (se 2 (by rfl) ⟨950217, by rfl⟩ : syracuseStep 2533913 = 1900435) B1900435
theorem B1124921 : Blo 666309 1124921 := bstep (se 2 (by rfl) ⟨421845, by rfl⟩ : syracuseStep 1124921 = 843691) B843691
theorem B666311 : Blo 666309 666311 := bstep (se 1 (by rfl) ⟨499733, by rfl⟩ : syracuseStep 666311 = 999467) B999467
theorem B4270801 : Blo 666309 4270801 := bstep (se 2 (by rfl) ⟨1601550, by rfl⟩ : syracuseStep 4270801 = 3203101) B3203101
theorem B666331 : Blo 666309 666331 := bstep (se 1 (by rfl) ⟨499748, by rfl⟩ : syracuseStep 666331 = 999497) B999497
theorem B666407 : Blo 666309 666407 := bstep (se 1 (by rfl) ⟨499805, by rfl⟩ : syracuseStep 666407 = 999611) B999611
theorem B666447 : Blo 666309 666447 := bstep (se 1 (by rfl) ⟨499835, by rfl⟩ : syracuseStep 666447 = 999671) B999671
theorem B666463 : Blo 666309 666463 := bstep (se 1 (by rfl) ⟨499847, by rfl⟩ : syracuseStep 666463 = 999695) B999695
theorem B666491 : Blo 666309 666491 := bstep (se 1 (by rfl) ⟨499868, by rfl⟩ : syracuseStep 666491 = 999737) B999737
theorem B666543 : Blo 666309 666543 := bstep (se 1 (by rfl) ⟨499907, by rfl⟩ : syracuseStep 666543 = 999815) B999815
theorem B2861999 : Blo 666309 2861999 := bstep (se 1 (by rfl) ⟨2146499, by rfl⟩ : syracuseStep 2861999 = 4292999) B4292999
theorem B666567 : Blo 666309 666567 := bstep (se 1 (by rfl) ⟨499925, by rfl⟩ : syracuseStep 666567 = 999851) B999851
theorem B666587 : Blo 666309 666587 := bstep (se 1 (by rfl) ⟨499940, by rfl⟩ : syracuseStep 666587 = 999881) B999881
theorem B666663 : Blo 666309 666663 := bstep (se 1 (by rfl) ⟨499997, by rfl⟩ : syracuseStep 666663 = 999995) B999995
theorem B666703 : Blo 666309 666703 := bstep (se 1 (by rfl) ⟨500027, by rfl⟩ : syracuseStep 666703 = 1000055) B1000055
theorem B3386447 : Blo 666309 3386447 := bstep (se 1 (by rfl) ⟨2539835, by rfl⟩ : syracuseStep 3386447 = 5079671) B5079671
theorem B666719 : Blo 666309 666719 := bstep (se 1 (by rfl) ⟨500039, by rfl⟩ : syracuseStep 666719 = 1000079) B1000079
theorem B666747 : Blo 666309 666747 := bstep (se 1 (by rfl) ⟨500060, by rfl⟩ : syracuseStep 666747 = 1000121) B1000121
theorem B666799 : Blo 666309 666799 := bstep (se 1 (by rfl) ⟨500099, by rfl⟩ : syracuseStep 666799 = 1000199) B1000199
theorem B666823 : Blo 666309 666823 := bstep (se 1 (by rfl) ⟨500117, by rfl⟩ : syracuseStep 666823 = 1000235) B1000235
theorem B3615947 : Blo 666309 3615947 := bstep (se 1 (by rfl) ⟨2711960, by rfl⟩ : syracuseStep 3615947 = 5423921) B5423921
theorem B666843 : Blo 666309 666843 := bstep (se 1 (by rfl) ⟨500132, by rfl⟩ : syracuseStep 666843 = 1000265) B1000265
theorem B1125623 : Blo 666309 1125623 := bstep (se 1 (by rfl) ⟨844217, by rfl⟩ : syracuseStep 1125623 = 1688435) B1688435
theorem B666919 : Blo 666309 666919 := bstep (se 1 (by rfl) ⟨500189, by rfl⟩ : syracuseStep 666919 = 1000379) B1000379
theorem B666959 : Blo 666309 666959 := bstep (se 1 (by rfl) ⟨500219, by rfl⟩ : syracuseStep 666959 = 1000439) B1000439
theorem B666975 : Blo 666309 666975 := bstep (se 1 (by rfl) ⟨500231, by rfl⟩ : syracuseStep 666975 = 1000463) B1000463
theorem B667003 : Blo 666309 667003 := bstep (se 1 (by rfl) ⟨500252, by rfl⟩ : syracuseStep 667003 = 1000505) B1000505
theorem B667055 : Blo 666309 667055 := bstep (se 1 (by rfl) ⟨500291, by rfl⟩ : syracuseStep 667055 = 1000583) B1000583
theorem B1256887 : Blo 666309 1256887 := bstep (se 1 (by rfl) ⟨942665, by rfl⟩ : syracuseStep 1256887 = 1885331) B1885331
theorem B667079 : Blo 666309 667079 := bstep (se 1 (by rfl) ⟨500309, by rfl⟩ : syracuseStep 667079 = 1000619) B1000619
theorem B667099 : Blo 666309 667099 := bstep (se 1 (by rfl) ⟨500324, by rfl⟩ : syracuseStep 667099 = 1000649) B1000649
theorem B4107763 : Blo 666309 4107763 := bstep (se 1 (by rfl) ⟨3080822, by rfl⟩ : syracuseStep 4107763 = 6161645) B6161645
theorem B667175 : Blo 666309 667175 := bstep (se 1 (by rfl) ⟨500381, by rfl⟩ : syracuseStep 667175 = 1000763) B1000763
theorem B667215 : Blo 666309 667215 := bstep (se 1 (by rfl) ⟨500411, by rfl⟩ : syracuseStep 667215 = 1000823) B1000823
theorem B1125967 : Blo 666309 1125967 := bstep (se 1 (by rfl) ⟨844475, by rfl⟩ : syracuseStep 1125967 = 1688951) B1688951
theorem B667231 : Blo 666309 667231 := bstep (se 1 (by rfl) ⟨500423, by rfl⟩ : syracuseStep 667231 = 1000847) B1000847
theorem B667259 : Blo 666309 667259 := bstep (se 1 (by rfl) ⟨500444, by rfl⟩ : syracuseStep 667259 = 1000889) B1000889
theorem B2862715 : Blo 666309 2862715 := bstep (se 1 (by rfl) ⟨2147036, by rfl⟩ : syracuseStep 2862715 = 4294073) B4294073
theorem B667311 : Blo 666309 667311 := bstep (se 1 (by rfl) ⟨500483, by rfl⟩ : syracuseStep 667311 = 1000967) B1000967
theorem B2535097 : Blo 666309 2535097 := bstep (se 2 (by rfl) ⟨950661, by rfl⟩ : syracuseStep 2535097 = 1901323) B1901323
theorem B667335 : Blo 666309 667335 := bstep (se 1 (by rfl) ⟨500501, by rfl⟩ : syracuseStep 667335 = 1001003) B1001003
theorem B3387095 : Blo 666309 3387095 := bstep (se 1 (by rfl) ⟨2540321, by rfl⟩ : syracuseStep 3387095 = 5080643) B5080643
theorem B667355 : Blo 666309 667355 := bstep (se 1 (by rfl) ⟨500516, by rfl⟩ : syracuseStep 667355 = 1001033) B1001033
theorem B667431 : Blo 666309 667431 := bstep (se 1 (by rfl) ⟨500573, by rfl⟩ : syracuseStep 667431 = 1001147) B1001147
theorem B4828987 : Blo 666309 4828987 := bstep (se 1 (by rfl) ⟨3621740, by rfl⟩ : syracuseStep 4828987 = 7243481) B7243481
theorem B1126217 : Blo 666309 1126217 := bstep (se 2 (by rfl) ⟨422331, by rfl⟩ : syracuseStep 1126217 = 844663) B844663
theorem B667471 : Blo 666309 667471 := bstep (se 1 (by rfl) ⟨500603, by rfl⟩ : syracuseStep 667471 = 1001207) B1001207
theorem B667487 : Blo 666309 667487 := bstep (se 1 (by rfl) ⟨500615, by rfl⟩ : syracuseStep 667487 = 1001231) B1001231
theorem B667515 : Blo 666309 667515 := bstep (se 1 (by rfl) ⟨500636, by rfl⟩ : syracuseStep 667515 = 1001273) B1001273
theorem B667567 : Blo 666309 667567 := bstep (se 1 (by rfl) ⟨500675, by rfl⟩ : syracuseStep 667567 = 1001351) B1001351
theorem B667591 : Blo 666309 667591 := bstep (se 1 (by rfl) ⟨500693, by rfl⟩ : syracuseStep 667591 = 1001387) B1001387
theorem B667611 : Blo 666309 667611 := bstep (se 1 (by rfl) ⟨500708, by rfl⟩ : syracuseStep 667611 = 1001417) B1001417
theorem B667687 : Blo 666309 667687 := bstep (se 1 (by rfl) ⟨500765, by rfl⟩ : syracuseStep 667687 = 1001531) B1001531
theorem B667727 : Blo 666309 667727 := bstep (se 1 (by rfl) ⟨500795, by rfl⟩ : syracuseStep 667727 = 1001591) B1001591
theorem B667743 : Blo 666309 667743 := bstep (se 1 (by rfl) ⟨500807, by rfl⟩ : syracuseStep 667743 = 1001615) B1001615
theorem B667771 : Blo 666309 667771 := bstep (se 1 (by rfl) ⟨500828, by rfl⟩ : syracuseStep 667771 = 1001657) B1001657
theorem B2404505 : Blo 666309 2404505 := bstep (se 2 (by rfl) ⟨901689, by rfl⟩ : syracuseStep 2404505 = 1803379) B1803379
theorem B8335523 : Blo 666309 8335523 := bstep (se 1 (by rfl) ⟨6251642, by rfl⟩ : syracuseStep 8335523 = 12503285) B12503285
theorem B667823 : Blo 666309 667823 := bstep (se 1 (by rfl) ⟨500867, by rfl⟩ : syracuseStep 667823 = 1001735) B1001735
theorem B667847 : Blo 666309 667847 := bstep (se 1 (by rfl) ⟨500885, by rfl⟩ : syracuseStep 667847 = 1001771) B1001771
theorem B667867 : Blo 666309 667867 := bstep (se 1 (by rfl) ⟨500900, by rfl⟩ : syracuseStep 667867 = 1001801) B1001801
theorem B1126649 : Blo 666309 1126649 := bstep (se 2 (by rfl) ⟨422493, by rfl⟩ : syracuseStep 1126649 = 844987) B844987
theorem B667943 : Blo 666309 667943 := bstep (se 1 (by rfl) ⟨500957, by rfl⟩ : syracuseStep 667943 = 1001915) B1001915
theorem B667983 : Blo 666309 667983 := bstep (se 1 (by rfl) ⟨500987, by rfl⟩ : syracuseStep 667983 = 1001975) B1001975
theorem B667999 : Blo 666309 667999 := bstep (se 1 (by rfl) ⟨500999, by rfl⟩ : syracuseStep 667999 = 1001999) B1001999
theorem B668027 : Blo 666309 668027 := bstep (se 1 (by rfl) ⟨501020, by rfl⟩ : syracuseStep 668027 = 1002041) B1002041
theorem B2568577 : Blo 666309 2568577 := bstep (se 2 (by rfl) ⟨963216, by rfl⟩ : syracuseStep 2568577 = 1926433) B1926433
theorem B1126831 : Blo 666309 1126831 := bstep (se 1 (by rfl) ⟨845123, by rfl⟩ : syracuseStep 1126831 = 1690247) B1690247
theorem B668079 : Blo 666309 668079 := bstep (se 1 (by rfl) ⟨501059, by rfl⟩ : syracuseStep 668079 = 1002119) B1002119
theorem B668103 : Blo 666309 668103 := bstep (se 1 (by rfl) ⟨501077, by rfl⟩ : syracuseStep 668103 = 1002155) B1002155
theorem B668123 : Blo 666309 668123 := bstep (se 1 (by rfl) ⟨501092, by rfl⟩ : syracuseStep 668123 = 1002185) B1002185
theorem B1126919 : Blo 666309 1126919 := bstep (se 1 (by rfl) ⟨845189, by rfl⟩ : syracuseStep 1126919 = 1690379) B1690379
theorem B668199 : Blo 666309 668199 := bstep (se 1 (by rfl) ⟨501149, by rfl⟩ : syracuseStep 668199 = 1002299) B1002299
theorem B668239 : Blo 666309 668239 := bstep (se 1 (by rfl) ⟨501179, by rfl⟩ : syracuseStep 668239 = 1002359) B1002359
theorem B668255 : Blo 666309 668255 := bstep (se 1 (by rfl) ⟨501191, by rfl⟩ : syracuseStep 668255 = 1002383) B1002383
theorem B668283 : Blo 666309 668283 := bstep (se 1 (by rfl) ⟨501212, by rfl⟩ : syracuseStep 668283 = 1002425) B1002425
theorem B668335 : Blo 666309 668335 := bstep (se 1 (by rfl) ⟨501251, by rfl⟩ : syracuseStep 668335 = 1002503) B1002503
theorem B668359 : Blo 666309 668359 := bstep (se 1 (by rfl) ⟨501269, by rfl⟩ : syracuseStep 668359 = 1002539) B1002539
theorem B3846865 : Blo 666309 3846865 := bstep (se 2 (by rfl) ⟨1442574, by rfl⟩ : syracuseStep 3846865 = 2885149) B2885149
theorem B4272851 : Blo 666309 4272851 := bstep (se 1 (by rfl) ⟨3204638, by rfl⟩ : syracuseStep 4272851 = 6409277) B6409277
theorem B668379 : Blo 666309 668379 := bstep (se 1 (by rfl) ⟨501284, by rfl⟩ : syracuseStep 668379 = 1002569) B1002569
theorem B668455 : Blo 666309 668455 := bstep (se 1 (by rfl) ⟨501341, by rfl⟩ : syracuseStep 668455 = 1002683) B1002683
theorem B668495 : Blo 666309 668495 := bstep (se 1 (by rfl) ⟨501371, by rfl⟩ : syracuseStep 668495 = 1002743) B1002743
theorem B1127263 : Blo 666309 1127263 := bstep (se 1 (by rfl) ⟨845447, by rfl⟩ : syracuseStep 1127263 = 1690895) B1690895
theorem B668511 : Blo 666309 668511 := bstep (se 1 (by rfl) ⟨501383, by rfl⟩ : syracuseStep 668511 = 1002767) B1002767
theorem B668539 : Blo 666309 668539 := bstep (se 1 (by rfl) ⟨501404, by rfl⟩ : syracuseStep 668539 = 1002809) B1002809
theorem B668591 : Blo 666309 668591 := bstep (se 1 (by rfl) ⟨501443, by rfl⟩ : syracuseStep 668591 = 1002887) B1002887
theorem B1127351 : Blo 666309 1127351 := bstep (se 1 (by rfl) ⟨845513, by rfl⟩ : syracuseStep 1127351 = 1691027) B1691027
theorem B668615 : Blo 666309 668615 := bstep (se 1 (by rfl) ⟨501461, by rfl⟩ : syracuseStep 668615 = 1002923) B1002923
theorem B668635 : Blo 666309 668635 := bstep (se 1 (by rfl) ⟨501476, by rfl⟩ : syracuseStep 668635 = 1002953) B1002953
theorem B668711 : Blo 666309 668711 := bstep (se 1 (by rfl) ⟨501533, by rfl⟩ : syracuseStep 668711 = 1003067) B1003067
theorem B8107073 : Blo 666309 8107073 := bstep (se 2 (by rfl) ⟨3040152, by rfl⟩ : syracuseStep 8107073 = 6080305) B6080305
theorem B668751 : Blo 666309 668751 := bstep (se 1 (by rfl) ⟨501563, by rfl⟩ : syracuseStep 668751 = 1003127) B1003127
theorem B668767 : Blo 666309 668767 := bstep (se 1 (by rfl) ⟨501575, by rfl⟩ : syracuseStep 668767 = 1003151) B1003151
theorem B668795 : Blo 666309 668795 := bstep (se 1 (by rfl) ⟨501596, by rfl⟩ : syracuseStep 668795 = 1003193) B1003193
theorem B668847 : Blo 666309 668847 := bstep (se 1 (by rfl) ⟨501635, by rfl⟩ : syracuseStep 668847 = 1003271) B1003271
theorem B668871 : Blo 666309 668871 := bstep (se 1 (by rfl) ⟨501653, by rfl⟩ : syracuseStep 668871 = 1003307) B1003307
theorem B668891 : Blo 666309 668891 := bstep (se 1 (by rfl) ⟨501668, by rfl⟩ : syracuseStep 668891 = 1003337) B1003337
theorem B668967 : Blo 666309 668967 := bstep (se 1 (by rfl) ⟨501725, by rfl⟩ : syracuseStep 668967 = 1003451) B1003451
theorem B669007 : Blo 666309 669007 := bstep (se 1 (by rfl) ⟨501755, by rfl⟩ : syracuseStep 669007 = 1003511) B1003511
theorem B669023 : Blo 666309 669023 := bstep (se 1 (by rfl) ⟨501767, by rfl⟩ : syracuseStep 669023 = 1003535) B1003535
theorem B669051 : Blo 666309 669051 := bstep (se 1 (by rfl) ⟨501788, by rfl⟩ : syracuseStep 669051 = 1003577) B1003577
theorem B2536829 : Blo 666309 2536829 := bstep (se 3 (by rfl) ⟨475655, by rfl⟩ : syracuseStep 2536829 = 951311) B951311
theorem B2176381 : Blo 666309 2176381 := bstep (se 3 (by rfl) ⟨408071, by rfl⟩ : syracuseStep 2176381 = 816143) B816143
theorem B669103 : Blo 666309 669103 := bstep (se 1 (by rfl) ⟨501827, by rfl⟩ : syracuseStep 669103 = 1003655) B1003655
theorem B669127 : Blo 666309 669127 := bstep (se 1 (by rfl) ⟨501845, by rfl⟩ : syracuseStep 669127 = 1003691) B1003691
theorem B669147 : Blo 666309 669147 := bstep (se 1 (by rfl) ⟨501860, by rfl⟩ : syracuseStep 669147 = 1003721) B1003721
theorem B1127945 : Blo 666309 1127945 := bstep (se 2 (by rfl) ⟨422979, by rfl⟩ : syracuseStep 1127945 = 845959) B845959
theorem B669223 : Blo 666309 669223 := bstep (se 1 (by rfl) ⟨501917, by rfl⟩ : syracuseStep 669223 = 1003835) B1003835
theorem B669263 : Blo 666309 669263 := bstep (se 1 (by rfl) ⟨501947, by rfl⟩ : syracuseStep 669263 = 1003895) B1003895
theorem B669279 : Blo 666309 669279 := bstep (se 1 (by rfl) ⟨501959, by rfl⟩ : syracuseStep 669279 = 1003919) B1003919
theorem B669307 : Blo 666309 669307 := bstep (se 1 (by rfl) ⟨501980, by rfl⟩ : syracuseStep 669307 = 1003961) B1003961
theorem B1128107 : Blo 666309 1128107 := bstep (se 1 (by rfl) ⟨846080, by rfl⟩ : syracuseStep 1128107 = 1692161) B1692161
theorem B669359 : Blo 666309 669359 := bstep (se 1 (by rfl) ⟨502019, by rfl⟩ : syracuseStep 669359 = 1004039) B1004039
theorem B669383 : Blo 666309 669383 := bstep (se 1 (by rfl) ⟨502037, by rfl⟩ : syracuseStep 669383 = 1004075) B1004075
theorem B669403 : Blo 666309 669403 := bstep (se 1 (by rfl) ⟨502052, by rfl⟩ : syracuseStep 669403 = 1004105) B1004105
theorem B669479 : Blo 666309 669479 := bstep (se 1 (by rfl) ⟨502109, by rfl⟩ : syracuseStep 669479 = 1004219) B1004219
theorem B669519 : Blo 666309 669519 := bstep (se 1 (by rfl) ⟨502139, by rfl⟩ : syracuseStep 669519 = 1004279) B1004279
theorem B669535 : Blo 666309 669535 := bstep (se 1 (by rfl) ⟨502151, by rfl⟩ : syracuseStep 669535 = 1004303) B1004303
theorem B669563 : Blo 666309 669563 := bstep (se 1 (by rfl) ⟨502172, by rfl⟩ : syracuseStep 669563 = 1004345) B1004345
theorem B669615 : Blo 666309 669615 := bstep (se 1 (by rfl) ⟨502211, by rfl⟩ : syracuseStep 669615 = 1004423) B1004423
theorem B8566721 : Blo 666309 8566721 := bstep (se 2 (by rfl) ⟨3212520, by rfl⟩ : syracuseStep 8566721 = 6425041) B6425041
theorem B669639 : Blo 666309 669639 := bstep (se 1 (by rfl) ⟨502229, by rfl⟩ : syracuseStep 669639 = 1004459) B1004459
theorem B669659 : Blo 666309 669659 := bstep (se 1 (by rfl) ⟨502244, by rfl⟩ : syracuseStep 669659 = 1004489) B1004489
theorem B669735 : Blo 666309 669735 := bstep (se 1 (by rfl) ⟨502301, by rfl⟩ : syracuseStep 669735 = 1004603) B1004603
theorem B1128505 : Blo 666309 1128505 := bstep (se 2 (by rfl) ⟨423189, by rfl⟩ : syracuseStep 1128505 = 846379) B846379
theorem B669775 : Blo 666309 669775 := bstep (se 1 (by rfl) ⟨502331, by rfl⟩ : syracuseStep 669775 = 1004663) B1004663
theorem B669791 : Blo 666309 669791 := bstep (se 1 (by rfl) ⟨502343, by rfl⟩ : syracuseStep 669791 = 1004687) B1004687
theorem B3618931 : Blo 666309 3618931 := bstep (se 1 (by rfl) ⟨2714198, by rfl⟩ : syracuseStep 3618931 = 5428397) B5428397
theorem B669819 : Blo 666309 669819 := bstep (se 1 (by rfl) ⟨502364, by rfl⟩ : syracuseStep 669819 = 1004729) B1004729
theorem B669871 : Blo 666309 669871 := bstep (se 1 (by rfl) ⟨502403, by rfl⟩ : syracuseStep 669871 = 1004807) B1004807
theorem B1128647 : Blo 666309 1128647 := bstep (se 1 (by rfl) ⟨846485, by rfl⟩ : syracuseStep 1128647 = 1692971) B1692971
theorem B669895 : Blo 666309 669895 := bstep (se 1 (by rfl) ⟨502421, by rfl⟩ : syracuseStep 669895 = 1004843) B1004843
theorem B669915 : Blo 666309 669915 := bstep (se 1 (by rfl) ⟨502436, by rfl⟩ : syracuseStep 669915 = 1004873) B1004873
theorem B5421323 : Blo 666309 5421323 := bstep (se 1 (by rfl) ⟨4065992, by rfl⟩ : syracuseStep 5421323 = 8131985) B8131985
theorem B669991 : Blo 666309 669991 := bstep (se 1 (by rfl) ⟨502493, by rfl⟩ : syracuseStep 669991 = 1004987) B1004987
theorem B670031 : Blo 666309 670031 := bstep (se 1 (by rfl) ⟨502523, by rfl⟩ : syracuseStep 670031 = 1005047) B1005047
theorem B670047 : Blo 666309 670047 := bstep (se 1 (by rfl) ⟨502535, by rfl⟩ : syracuseStep 670047 = 1005071) B1005071
theorem B1128809 : Blo 666309 1128809 := bstep (se 2 (by rfl) ⟨423303, by rfl⟩ : syracuseStep 1128809 = 846607) B846607
theorem B670075 : Blo 666309 670075 := bstep (se 1 (by rfl) ⟨502556, by rfl⟩ : syracuseStep 670075 = 1005113) B1005113
theorem B670127 : Blo 666309 670127 := bstep (se 1 (by rfl) ⟨502595, by rfl⟩ : syracuseStep 670127 = 1005191) B1005191
theorem B670151 : Blo 666309 670151 := bstep (se 1 (by rfl) ⟨502613, by rfl⟩ : syracuseStep 670151 = 1005227) B1005227
theorem B670171 : Blo 666309 670171 := bstep (se 1 (by rfl) ⟨502628, by rfl⟩ : syracuseStep 670171 = 1005257) B1005257
theorem B2439661 : Blo 666309 2439661 := bstep (se 3 (by rfl) ⟨457436, by rfl⟩ : syracuseStep 2439661 = 914873) B914873
theorem B670247 : Blo 666309 670247 := bstep (se 1 (by rfl) ⟨502685, by rfl⟩ : syracuseStep 670247 = 1005371) B1005371
theorem B3390011 : Blo 666309 3390011 := bstep (se 1 (by rfl) ⟨2542508, by rfl⟩ : syracuseStep 3390011 = 5085017) B5085017
theorem B670287 : Blo 666309 670287 := bstep (se 1 (by rfl) ⟨502715, by rfl⟩ : syracuseStep 670287 = 1005431) B1005431
theorem B670303 : Blo 666309 670303 := bstep (se 1 (by rfl) ⟨502727, by rfl⟩ : syracuseStep 670303 = 1005455) B1005455
theorem B11385521 : Blo 666309 11385521 := bstep (se 2 (by rfl) ⟨4269570, by rfl⟩ : syracuseStep 11385521 = 8539141) B8539141
theorem B10959545 : Blo 666309 10959545 := bstep (se 2 (by rfl) ⟨4109829, by rfl⟩ : syracuseStep 10959545 = 8219659) B8219659
theorem B1424071 : Blo 666309 1424071 := bstep (se 1 (by rfl) ⟨1068053, by rfl⟩ : syracuseStep 1424071 = 2136107) B2136107
theorem B2898641 : Blo 666309 2898641 := bstep (se 2 (by rfl) ⟨1086990, by rfl⟩ : syracuseStep 2898641 = 2173981) B2173981
theorem B1129207 : Blo 666309 1129207 := bstep (se 1 (by rfl) ⟨846905, by rfl⟩ : syracuseStep 1129207 = 1693811) B1693811
theorem B1129403 : Blo 666309 1129403 := bstep (se 1 (by rfl) ⟨847052, by rfl⟩ : syracuseStep 1129403 = 1694105) B1694105
theorem B1129511 : Blo 666309 1129511 := bstep (se 1 (by rfl) ⟨847133, by rfl⟩ : syracuseStep 1129511 = 1694267) B1694267
theorem B2145437 : Blo 666309 2145437 := bstep (se 3 (by rfl) ⟨402269, by rfl⟩ : syracuseStep 2145437 = 804539) B804539
theorem B3390659 : Blo 666309 3390659 := bstep (se 1 (by rfl) ⟨2542994, by rfl⟩ : syracuseStep 3390659 = 5085989) B5085989
theorem B1129801 : Blo 666309 1129801 := bstep (se 2 (by rfl) ⟨423675, by rfl⟩ : syracuseStep 1129801 = 847351) B847351
theorem B1129835 : Blo 666309 1129835 := bstep (se 1 (by rfl) ⟨847376, by rfl⟩ : syracuseStep 1129835 = 1694753) B1694753
theorem B2538971 : Blo 666309 2538971 := bstep (se 1 (by rfl) ⟨1904228, by rfl⟩ : syracuseStep 2538971 = 3808457) B3808457
theorem B1687027 : Blo 666309 1687027 := bstep (se 1 (by rfl) ⟨1265270, by rfl⟩ : syracuseStep 1687027 = 2530541) B2530541
theorem B25705997 : Blo 666309 25705997 := bstep (se 3 (by rfl) ⟨4819874, by rfl⟩ : syracuseStep 25705997 = 9639749) B9639749
theorem B1130233 : Blo 666309 1130233 := bstep (se 2 (by rfl) ⟨423837, by rfl⟩ : syracuseStep 1130233 = 847675) B847675
theorem B9912179 : Blo 666309 9912179 := bstep (se 1 (by rfl) ⟨7434134, by rfl⟩ : syracuseStep 9912179 = 14868269) B14868269
theorem B1130503 : Blo 666309 1130503 := bstep (se 1 (by rfl) ⟨847877, by rfl⟩ : syracuseStep 1130503 = 1695755) B1695755
theorem B999503 : Blo 666309 999503 := bstep (se 1 (by rfl) ⟨749627, by rfl⟩ : syracuseStep 999503 = 1499255) B1499255
theorem B999623 : Blo 666309 999623 := bstep (se 1 (by rfl) ⟨749717, by rfl⟩ : syracuseStep 999623 = 1499435) B1499435
theorem B7225661 : Blo 666309 7225661 := bstep (se 3 (by rfl) ⟨1354811, by rfl⟩ : syracuseStep 7225661 = 2709623) B2709623
theorem B2572631 : Blo 666309 2572631 := bstep (se 1 (by rfl) ⟨1929473, by rfl⟩ : syracuseStep 2572631 = 3858947) B3858947
theorem B999785 : Blo 666309 999785 := bstep (se 2 (by rfl) ⟨374919, by rfl⟩ : syracuseStep 999785 = 749839) B749839
theorem B999863 : Blo 666309 999863 := bstep (se 1 (by rfl) ⟨749897, by rfl⟩ : syracuseStep 999863 = 1499795) B1499795
theorem B1130935 : Blo 666309 1130935 := bstep (se 1 (by rfl) ⟨848201, by rfl⟩ : syracuseStep 1130935 = 1696403) B1696403
theorem B999899 : Blo 666309 999899 := bstep (se 1 (by rfl) ⟨749924, by rfl⟩ : syracuseStep 999899 = 1499849) B1499849
theorem B2605607 : Blo 666309 2605607 := bstep (se 1 (by rfl) ⟨1954205, by rfl⟩ : syracuseStep 2605607 = 3908411) B3908411
theorem B1688161 : Blo 666309 1688161 := bstep (se 2 (by rfl) ⟨633060, by rfl⟩ : syracuseStep 1688161 = 1266121) B1266121
theorem B1131131 : Blo 666309 1131131 := bstep (se 1 (by rfl) ⟨848348, by rfl⟩ : syracuseStep 1131131 = 1696697) B1696697
theorem B2540231 : Blo 666309 2540231 := bstep (se 1 (by rfl) ⟨1905173, by rfl⟩ : syracuseStep 2540231 = 3810347) B3810347
theorem B1000367 : Blo 666309 1000367 := bstep (se 1 (by rfl) ⟨750275, by rfl⟩ : syracuseStep 1000367 = 1500551) B1500551
theorem B1000457 : Blo 666309 1000457 := bstep (se 2 (by rfl) ⟨375171, by rfl⟩ : syracuseStep 1000457 = 750343) B750343
theorem B1000487 : Blo 666309 1000487 := bstep (se 1 (by rfl) ⟨750365, by rfl⟩ : syracuseStep 1000487 = 1500731) B1500731
theorem B1000571 : Blo 666309 1000571 := bstep (se 1 (by rfl) ⟨750428, by rfl⟩ : syracuseStep 1000571 = 1500857) B1500857
theorem B2901187 : Blo 666309 2901187 := bstep (se 1 (by rfl) ⟨2175890, by rfl⟩ : syracuseStep 2901187 = 4351781) B4351781
theorem B1000697 : Blo 666309 1000697 := bstep (se 2 (by rfl) ⟨375261, by rfl⟩ : syracuseStep 1000697 = 750523) B750523
theorem B1000799 : Blo 666309 1000799 := bstep (se 1 (by rfl) ⟨750599, by rfl⟩ : syracuseStep 1000799 = 1501199) B1501199
theorem B1000811 : Blo 666309 1000811 := bstep (se 1 (by rfl) ⟨750608, by rfl⟩ : syracuseStep 1000811 = 1501217) B1501217
theorem B2540929 : Blo 666309 2540929 := bstep (se 2 (by rfl) ⟨952848, by rfl⟩ : syracuseStep 2540929 = 1905697) B1905697
theorem B2311667 : Blo 666309 2311667 := bstep (se 1 (by rfl) ⟨1733750, by rfl⟩ : syracuseStep 2311667 = 3467501) B3467501
theorem B1689113 : Blo 666309 1689113 := bstep (se 2 (by rfl) ⟨633417, by rfl⟩ : syracuseStep 1689113 = 1266835) B1266835
theorem B1001039 : Blo 666309 1001039 := bstep (se 1 (by rfl) ⟨750779, by rfl⟩ : syracuseStep 1001039 = 1501559) B1501559
theorem B2541203 : Blo 666309 2541203 := bstep (se 1 (by rfl) ⟨1905902, by rfl⟩ : syracuseStep 2541203 = 3811805) B3811805
theorem B1001159 : Blo 666309 1001159 := bstep (se 1 (by rfl) ⟨750869, by rfl⟩ : syracuseStep 1001159 = 1501739) B1501739
theorem B6440647 : Blo 666309 6440647 := bstep (se 1 (by rfl) ⟨4830485, by rfl⟩ : syracuseStep 6440647 = 9660971) B9660971
theorem B1001321 : Blo 666309 1001321 := bstep (se 2 (by rfl) ⟨375495, by rfl⟩ : syracuseStep 1001321 = 750991) B750991
theorem B1001399 : Blo 666309 1001399 := bstep (se 1 (by rfl) ⟨751049, by rfl⟩ : syracuseStep 1001399 = 1502099) B1502099
theorem B1001435 : Blo 666309 1001435 := bstep (se 1 (by rfl) ⟨751076, by rfl⟩ : syracuseStep 1001435 = 1502153) B1502153
theorem B1689619 : Blo 666309 1689619 := bstep (se 1 (by rfl) ⟨1267214, by rfl⟩ : syracuseStep 1689619 = 2534429) B2534429
theorem B30951517 : Blo 666309 30951517 := bstep (se 3 (by rfl) ⟨5803409, by rfl⟩ : syracuseStep 30951517 = 11606819) B11606819
theorem B19286423 : Blo 666309 19286423 := bstep (se 1 (by rfl) ⟨14464817, by rfl⟩ : syracuseStep 19286423 = 28929635) B28929635
theorem B1001903 : Blo 666309 1001903 := bstep (se 1 (by rfl) ⟨751427, by rfl⟩ : syracuseStep 1001903 = 1502855) B1502855
theorem B1001993 : Blo 666309 1001993 := bstep (se 2 (by rfl) ⟨375747, by rfl⟩ : syracuseStep 1001993 = 751495) B751495
theorem B4803097 : Blo 666309 4803097 := bstep (se 2 (by rfl) ⟨1801161, by rfl⟩ : syracuseStep 4803097 = 3602323) B3602323
theorem B1002023 : Blo 666309 1002023 := bstep (se 1 (by rfl) ⟨751517, by rfl⟩ : syracuseStep 1002023 = 1503035) B1503035
theorem B1002107 : Blo 666309 1002107 := bstep (se 1 (by rfl) ⟨751580, by rfl⟩ : syracuseStep 1002107 = 1503161) B1503161
theorem B4803245 : Blo 666309 4803245 := bstep (se 3 (by rfl) ⟨900608, by rfl⟩ : syracuseStep 4803245 = 1801217) B1801217
theorem B1002233 : Blo 666309 1002233 := bstep (se 2 (by rfl) ⟨375837, by rfl⟩ : syracuseStep 1002233 = 751675) B751675
theorem B1002335 : Blo 666309 1002335 := bstep (se 1 (by rfl) ⟨751751, by rfl⟩ : syracuseStep 1002335 = 1503503) B1503503
theorem B1002347 : Blo 666309 1002347 := bstep (se 1 (by rfl) ⟨751760, by rfl⟩ : syracuseStep 1002347 = 1503521) B1503521
theorem B904111 : Blo 666309 904111 := bstep (se 1 (by rfl) ⟨678083, by rfl⟩ : syracuseStep 904111 = 1356167) B1356167
theorem B1067951 : Blo 666309 1067951 := bstep (se 1 (by rfl) ⟨800963, by rfl⟩ : syracuseStep 1067951 = 1601927) B1601927
theorem B1526791 : Blo 666309 1526791 := bstep (se 1 (by rfl) ⟨1145093, by rfl⟩ : syracuseStep 1526791 = 2290187) B2290187
theorem B1690703 : Blo 666309 1690703 := bstep (se 1 (by rfl) ⟨1268027, by rfl⟩ : syracuseStep 1690703 = 2536055) B2536055
theorem B1002575 : Blo 666309 1002575 := bstep (se 1 (by rfl) ⟨751931, by rfl⟩ : syracuseStep 1002575 = 1503863) B1503863
theorem B1002695 : Blo 666309 1002695 := bstep (se 1 (by rfl) ⟨752021, by rfl⟩ : syracuseStep 1002695 = 1504043) B1504043
theorem B2542859 : Blo 666309 2542859 := bstep (se 1 (by rfl) ⟨1907144, by rfl⟩ : syracuseStep 2542859 = 3814289) B3814289
theorem B1002857 : Blo 666309 1002857 := bstep (se 2 (by rfl) ⟨376071, by rfl⟩ : syracuseStep 1002857 = 752143) B752143
theorem B1002935 : Blo 666309 1002935 := bstep (se 1 (by rfl) ⟨752201, by rfl⟩ : syracuseStep 1002935 = 1504403) B1504403
theorem B1002971 : Blo 666309 1002971 := bstep (se 1 (by rfl) ⟨752228, by rfl⟩ : syracuseStep 1002971 = 1504457) B1504457
theorem B1691351 : Blo 666309 1691351 := bstep (se 1 (by rfl) ⟨1268513, by rfl⟩ : syracuseStep 1691351 = 2537027) B2537027
theorem B2936737 : Blo 666309 2936737 := bstep (se 2 (by rfl) ⟨1101276, by rfl⟩ : syracuseStep 2936737 = 2202553) B2202553
theorem B1003439 : Blo 666309 1003439 := bstep (se 1 (by rfl) ⟨752579, by rfl⟩ : syracuseStep 1003439 = 1505159) B1505159
theorem B1003529 : Blo 666309 1003529 := bstep (se 2 (by rfl) ⟨376323, by rfl⟩ : syracuseStep 1003529 = 752647) B752647
theorem B1003559 : Blo 666309 1003559 := bstep (se 1 (by rfl) ⟨752669, by rfl⟩ : syracuseStep 1003559 = 1505339) B1505339
theorem B1691705 : Blo 666309 1691705 := bstep (se 2 (by rfl) ⟨634389, by rfl⟩ : syracuseStep 1691705 = 1268779) B1268779
theorem B1003643 : Blo 666309 1003643 := bstep (se 1 (by rfl) ⟨752732, by rfl⟩ : syracuseStep 1003643 = 1505465) B1505465
theorem B1265863 : Blo 666309 1265863 := bstep (se 1 (by rfl) ⟨949397, by rfl⟩ : syracuseStep 1265863 = 1898795) B1898795
theorem B1069303 : Blo 666309 1069303 := bstep (se 1 (by rfl) ⟨801977, by rfl⟩ : syracuseStep 1069303 = 1603955) B1603955
theorem B1003769 : Blo 666309 1003769 := bstep (se 2 (by rfl) ⟨376413, by rfl⟩ : syracuseStep 1003769 = 752827) B752827
theorem B8540477 : Blo 666309 8540477 := bstep (se 3 (by rfl) ⟨1601339, by rfl⟩ : syracuseStep 8540477 = 3202679) B3202679
theorem B1003871 : Blo 666309 1003871 := bstep (se 1 (by rfl) ⟨752903, by rfl⟩ : syracuseStep 1003871 = 1505807) B1505807
theorem B1003883 : Blo 666309 1003883 := bstep (se 1 (by rfl) ⟨752912, by rfl⟩ : syracuseStep 1003883 = 1505825) B1505825
theorem B2413081 : Blo 666309 2413081 := bstep (se 2 (by rfl) ⟨904905, by rfl⟩ : syracuseStep 2413081 = 1809811) B1809811
theorem B1004111 : Blo 666309 1004111 := bstep (se 1 (by rfl) ⟨753083, by rfl⟩ : syracuseStep 1004111 = 1506167) B1506167
theorem B2544317 : Blo 666309 2544317 := bstep (se 3 (by rfl) ⟨477059, by rfl⟩ : syracuseStep 2544317 = 954119) B954119
theorem B1004231 : Blo 666309 1004231 := bstep (se 1 (by rfl) ⟨753173, by rfl⟩ : syracuseStep 1004231 = 1506347) B1506347
theorem B4707017 : Blo 666309 4707017 := bstep (se 2 (by rfl) ⟨1765131, by rfl⟩ : syracuseStep 4707017 = 3530263) B3530263
theorem B7230161 : Blo 666309 7230161 := bstep (se 2 (by rfl) ⟨2711310, by rfl⟩ : syracuseStep 7230161 = 5422621) B5422621
theorem B1266425 : Blo 666309 1266425 := bstep (se 2 (by rfl) ⟨474909, by rfl⟩ : syracuseStep 1266425 = 949819) B949819
theorem B1004393 : Blo 666309 1004393 := bstep (se 2 (by rfl) ⟨376647, by rfl⟩ : syracuseStep 1004393 = 753295) B753295
theorem B1069931 : Blo 666309 1069931 := bstep (se 1 (by rfl) ⟨802448, by rfl⟩ : syracuseStep 1069931 = 1604897) B1604897
theorem B1266607 : Blo 666309 1266607 := bstep (se 1 (by rfl) ⟨949955, by rfl⟩ : syracuseStep 1266607 = 1899911) B1899911
theorem B1004471 : Blo 666309 1004471 := bstep (se 1 (by rfl) ⟨753353, by rfl⟩ : syracuseStep 1004471 = 1506707) B1506707
theorem B1004507 : Blo 666309 1004507 := bstep (se 1 (by rfl) ⟨753380, by rfl⟩ : syracuseStep 1004507 = 1506761) B1506761
theorem B2249747 : Blo 666309 2249747 := bstep (se 1 (by rfl) ⟨1687310, by rfl⟩ : syracuseStep 2249747 = 3374621) B3374621
theorem B1201481 : Blo 666309 1201481 := bstep (se 2 (by rfl) ⟨450555, by rfl⟩ : syracuseStep 1201481 = 901111) B901111
theorem B2250071 : Blo 666309 2250071 := bstep (se 1 (by rfl) ⟨1687553, by rfl⟩ : syracuseStep 2250071 = 3375107) B3375107
theorem B1070443 : Blo 666309 1070443 := bstep (se 1 (by rfl) ⟨802832, by rfl⟩ : syracuseStep 1070443 = 1605665) B1605665
theorem B1004975 : Blo 666309 1004975 := bstep (se 1 (by rfl) ⟨753731, by rfl⟩ : syracuseStep 1004975 = 1507463) B1507463
theorem B1005065 : Blo 666309 1005065 := bstep (se 2 (by rfl) ⟨376899, by rfl⟩ : syracuseStep 1005065 = 753799) B753799
theorem B1005095 : Blo 666309 1005095 := bstep (se 1 (by rfl) ⟨753821, by rfl⟩ : syracuseStep 1005095 = 1507643) B1507643
theorem B1005179 : Blo 666309 1005179 := bstep (se 1 (by rfl) ⟨753884, by rfl⟩ : syracuseStep 1005179 = 1507769) B1507769
theorem B4282055 : Blo 666309 4282055 := bstep (se 1 (by rfl) ⟨3211541, by rfl⟩ : syracuseStep 4282055 = 6423083) B6423083
theorem B1005305 : Blo 666309 1005305 := bstep (se 2 (by rfl) ⟨376989, by rfl⟩ : syracuseStep 1005305 = 753979) B753979
theorem B6084395 : Blo 666309 6084395 := bstep (se 1 (by rfl) ⟨4563296, by rfl⟩ : syracuseStep 6084395 = 9126593) B9126593
theorem B1005407 : Blo 666309 1005407 := bstep (se 1 (by rfl) ⟨754055, by rfl⟩ : syracuseStep 1005407 = 1508111) B1508111
theorem B1005419 : Blo 666309 1005419 := bstep (se 1 (by rfl) ⟨754064, by rfl⟩ : syracuseStep 1005419 = 1508129) B1508129
theorem B20043821 : Blo 666309 20043821 := bstep (se 3 (by rfl) ⟨3758216, by rfl⟩ : syracuseStep 20043821 = 7516433) B7516433
theorem B1071161 : Blo 666309 1071161 := bstep (se 2 (by rfl) ⟨401685, by rfl⟩ : syracuseStep 1071161 = 803371) B803371
theorem B4053149 : Blo 666309 4053149 := bstep (se 3 (by rfl) ⟨759965, by rfl⟩ : syracuseStep 4053149 = 1519931) B1519931
theorem B1267883 : Blo 666309 1267883 := bstep (se 1 (by rfl) ⟨950912, by rfl⟩ : syracuseStep 1267883 = 1901825) B1901825
theorem B1693943 : Blo 666309 1693943 := bstep (se 1 (by rfl) ⟨1270457, by rfl⟩ : syracuseStep 1693943 = 2540915) B2540915
theorem B2578679 : Blo 666309 2578679 := bstep (se 1 (by rfl) ⟨1934009, by rfl⟩ : syracuseStep 2578679 = 3868019) B3868019
theorem B1071353 : Blo 666309 1071353 := bstep (se 2 (by rfl) ⟨401757, by rfl⟩ : syracuseStep 1071353 = 803515) B803515
theorem B2251151 : Blo 666309 2251151 := bstep (se 1 (by rfl) ⟨1688363, by rfl⟩ : syracuseStep 2251151 = 3376727) B3376727
theorem B1268111 : Blo 666309 1268111 := bstep (se 1 (by rfl) ⟨951083, by rfl⟩ : syracuseStep 1268111 = 1902167) B1902167
theorem B2251475 : Blo 666309 2251475 := bstep (se 1 (by rfl) ⟨1688606, by rfl⟩ : syracuseStep 2251475 = 3377213) B3377213
theorem B10279979 : Blo 666309 10279979 := bstep (se 1 (by rfl) ⟨7709984, by rfl⟩ : syracuseStep 10279979 = 15419969) B15419969
theorem B1236179 : Blo 666309 1236179 := bstep (se 1 (by rfl) ⟨927134, by rfl⟩ : syracuseStep 1236179 = 1854269) B1854269
theorem B6413741 : Blo 666309 6413741 := bstep (se 3 (by rfl) ⟨1202576, by rfl⟩ : syracuseStep 6413741 = 2405153) B2405153
theorem B1269371 : Blo 666309 1269371 := bstep (se 1 (by rfl) ⟨952028, by rfl⟩ : syracuseStep 1269371 = 1904057) B1904057
theorem B843463 : Blo 666309 843463 := bstep (se 1 (by rfl) ⟨632597, by rfl⟩ : syracuseStep 843463 = 1265195) B1265195
theorem B1695431 : Blo 666309 1695431 := bstep (se 1 (by rfl) ⟨1271573, by rfl⟩ : syracuseStep 1695431 = 2543147) B2543147
theorem B1924823 : Blo 666309 1924823 := bstep (se 1 (by rfl) ⟨1443617, by rfl⟩ : syracuseStep 1924823 = 2887235) B2887235
theorem B2252663 : Blo 666309 2252663 := bstep (se 1 (by rfl) ⟨1689497, by rfl⟩ : syracuseStep 2252663 = 3378995) B3378995
theorem B1073083 : Blo 666309 1073083 := bstep (se 1 (by rfl) ⟨804812, by rfl⟩ : syracuseStep 1073083 = 1609625) B1609625
theorem B31252493 : Blo 666309 31252493 := bstep (se 3 (by rfl) ⟨5859842, by rfl⟩ : syracuseStep 31252493 = 11719685) B11719685
theorem B2252879 : Blo 666309 2252879 := bstep (se 1 (by rfl) ⟨1689659, by rfl⟩ : syracuseStep 2252879 = 3379319) B3379319
theorem B1269857 : Blo 666309 1269857 := bstep (se 2 (by rfl) ⟨476196, by rfl⟩ : syracuseStep 1269857 = 952393) B952393
theorem B1270009 : Blo 666309 1270009 := bstep (se 2 (by rfl) ⟨476253, by rfl⟩ : syracuseStep 1270009 = 952507) B952507
theorem B2253257 : Blo 666309 2253257 := bstep (se 2 (by rfl) ⟨844971, by rfl⟩ : syracuseStep 2253257 = 1689943) B1689943
theorem B1499687 : Blo 666309 1499687 := bstep (se 1 (by rfl) ⟨1124765, by rfl⟩ : syracuseStep 1499687 = 2249531) B2249531
theorem B2253527 : Blo 666309 2253527 := bstep (se 1 (by rfl) ⟨1690145, by rfl⟩ : syracuseStep 2253527 = 3380291) B3380291
theorem B1696585 : Blo 666309 1696585 := bstep (se 2 (by rfl) ⟨636219, by rfl⟩ : syracuseStep 1696585 = 1272439) B1272439
theorem B1500011 : Blo 666309 1500011 := bstep (se 1 (by rfl) ⟨1125008, by rfl⟩ : syracuseStep 1500011 = 2250017) B2250017
theorem B1500065 : Blo 666309 1500065 := bstep (se 2 (by rfl) ⟨562524, by rfl⟩ : syracuseStep 1500065 = 1125049) B1125049
theorem B2253743 : Blo 666309 2253743 := bstep (se 1 (by rfl) ⟨1690307, by rfl⟩ : syracuseStep 2253743 = 3380615) B3380615
theorem B1500407 : Blo 666309 1500407 := bstep (se 1 (by rfl) ⟨1125305, by rfl⟩ : syracuseStep 1500407 = 2250611) B2250611
theorem B5432741 : Blo 666309 5432741 := bstep (se 4 (by rfl) ⟨509319, by rfl⟩ : syracuseStep 5432741 = 1018639) B1018639
theorem B1271315 : Blo 666309 1271315 := bstep (se 1 (by rfl) ⟨953486, by rfl⟩ : syracuseStep 1271315 = 1906973) B1906973
theorem B1271467 : Blo 666309 1271467 := bstep (se 1 (by rfl) ⟨953600, by rfl⟩ : syracuseStep 1271467 = 1907201) B1907201
theorem B1501001 : Blo 666309 1501001 := bstep (se 2 (by rfl) ⟨562875, by rfl⟩ : syracuseStep 1501001 = 1125751) B1125751
theorem B1271695 : Blo 666309 1271695 := bstep (se 1 (by rfl) ⟨953771, by rfl⟩ : syracuseStep 1271695 = 1907543) B1907543
theorem B1271771 : Blo 666309 1271771 := bstep (se 1 (by rfl) ⟨953828, by rfl⟩ : syracuseStep 1271771 = 1907657) B1907657
theorem B845903 : Blo 666309 845903 := bstep (se 1 (by rfl) ⟨634427, by rfl⟩ : syracuseStep 845903 = 1268855) B1268855
theorem B1370209 : Blo 666309 1370209 := bstep (se 2 (by rfl) ⟨513828, by rfl⟩ : syracuseStep 1370209 = 1027657) B1027657
theorem B4286999 : Blo 666309 4286999 := bstep (se 1 (by rfl) ⟨3215249, by rfl⟩ : syracuseStep 4286999 = 6430499) B6430499
theorem B1501793 : Blo 666309 1501793 := bstep (se 2 (by rfl) ⟨563172, by rfl⟩ : syracuseStep 1501793 = 1126345) B1126345
theorem B7629713 : Blo 666309 7629713 := bstep (se 2 (by rfl) ⟨2861142, by rfl⟩ : syracuseStep 7629713 = 5722285) B5722285
theorem B5073839 : Blo 666309 5073839 := bstep (se 1 (by rfl) ⟨3805379, by rfl⟩ : syracuseStep 5073839 = 7610759) B7610759
theorem B1502135 : Blo 666309 1502135 := bstep (se 1 (by rfl) ⟨1126601, by rfl⟩ : syracuseStep 1502135 = 2253203) B2253203
theorem B1207507 : Blo 666309 1207507 := bstep (se 1 (by rfl) ⟨905630, by rfl⟩ : syracuseStep 1207507 = 1811261) B1811261
theorem B2256119 : Blo 666309 2256119 := bstep (se 1 (by rfl) ⟨1692089, by rfl⟩ : syracuseStep 2256119 = 3384179) B3384179
theorem B847199 : Blo 666309 847199 := bstep (se 1 (by rfl) ⟨635399, by rfl⟩ : syracuseStep 847199 = 1270799) B1270799
theorem B11398643 : Blo 666309 11398643 := bstep (se 1 (by rfl) ⟨8548982, by rfl⟩ : syracuseStep 11398643 = 17097965) B17097965
theorem B1502729 : Blo 666309 1502729 := bstep (se 2 (by rfl) ⟨563523, by rfl⟩ : syracuseStep 1502729 = 1127047) B1127047
theorem B2256443 : Blo 666309 2256443 := bstep (se 1 (by rfl) ⟨1692332, by rfl⟩ : syracuseStep 2256443 = 3384665) B3384665
theorem B32566859 : Blo 666309 32566859 := bstep (se 1 (by rfl) ⟨24425144, by rfl⟩ : syracuseStep 32566859 = 48850289) B48850289
theorem B8548163 : Blo 666309 8548163 := bstep (se 1 (by rfl) ⟨6411122, by rfl⟩ : syracuseStep 8548163 = 12822245) B12822245
theorem B2256713 : Blo 666309 2256713 := bstep (se 2 (by rfl) ⟨846267, by rfl⟩ : syracuseStep 2256713 = 1692535) B1692535
theorem B1503071 : Blo 666309 1503071 := bstep (se 1 (by rfl) ⟨1127303, by rfl⟩ : syracuseStep 1503071 = 2254607) B2254607
theorem B9629603 : Blo 666309 9629603 := bstep (se 1 (by rfl) ⟨7222202, by rfl⟩ : syracuseStep 9629603 = 14444405) B14444405
theorem B1503251 : Blo 666309 1503251 := bstep (se 1 (by rfl) ⟨1127438, by rfl⟩ : syracuseStep 1503251 = 2254877) B2254877
theorem B749767 : Blo 666309 749767 := bstep (se 1 (by rfl) ⟨562325, by rfl⟩ : syracuseStep 749767 = 1124651) B1124651
theorem B1503593 : Blo 666309 1503593 := bstep (se 2 (by rfl) ⟨563847, by rfl⟩ : syracuseStep 1503593 = 1127695) B1127695
theorem B1143467 : Blo 666309 1143467 := bstep (se 1 (by rfl) ⟨857600, by rfl⟩ : syracuseStep 1143467 = 1715201) B1715201
theorem B1602263 : Blo 666309 1602263 := bstep (se 1 (by rfl) ⟨1201697, by rfl⟩ : syracuseStep 1602263 = 2403395) B2403395
theorem B2847595 : Blo 666309 2847595 := bstep (se 1 (by rfl) ⟨2135696, by rfl⟩ : syracuseStep 2847595 = 4271393) B4271393
theorem B2257847 : Blo 666309 2257847 := bstep (se 1 (by rfl) ⟨1693385, by rfl⟩ : syracuseStep 2257847 = 3386771) B3386771
theorem B1504187 : Blo 666309 1504187 := bstep (se 1 (by rfl) ⟨1128140, by rfl⟩ : syracuseStep 1504187 = 2256281) B2256281
theorem B750631 : Blo 666309 750631 := bstep (se 1 (by rfl) ⟨562973, by rfl⟩ : syracuseStep 750631 = 1125947) B1125947
theorem B1504313 : Blo 666309 1504313 := bstep (se 2 (by rfl) ⟨564117, by rfl⟩ : syracuseStep 1504313 = 1128235) B1128235
theorem B5403941 : Blo 666309 5403941 := bstep (se 4 (by rfl) ⟨506619, by rfl⟩ : syracuseStep 5403941 = 1013239) B1013239
theorem B1504655 : Blo 666309 1504655 := bstep (se 1 (by rfl) ⟨1128491, by rfl⟩ : syracuseStep 1504655 = 2256983) B2256983
theorem B2258441 : Blo 666309 2258441 := bstep (se 2 (by rfl) ⟨846915, by rfl⟩ : syracuseStep 2258441 = 1693831) B1693831
theorem B1013447 : Blo 666309 1013447 := bstep (se 1 (by rfl) ⟨760085, by rfl⟩ : syracuseStep 1013447 = 1520171) B1520171
theorem B1504979 : Blo 666309 1504979 := bstep (se 1 (by rfl) ⟨1128734, by rfl⟩ : syracuseStep 1504979 = 2257469) B2257469
theorem B3209483 : Blo 666309 3209483 := bstep (se 1 (by rfl) ⟨2407112, by rfl⟩ : syracuseStep 3209483 = 4814225) B4814225
theorem B2259305 : Blo 666309 2259305 := bstep (se 2 (by rfl) ⟨847239, by rfl⟩ : syracuseStep 2259305 = 1694479) B1694479
theorem B752251 : Blo 666309 752251 := bstep (se 1 (by rfl) ⟨564188, by rfl⟩ : syracuseStep 752251 = 1128377) B1128377
theorem B1505915 : Blo 666309 1505915 := bstep (se 1 (by rfl) ⟨1129436, by rfl⟩ : syracuseStep 1505915 = 2258873) B2258873
theorem B1506041 : Blo 666309 1506041 := bstep (se 2 (by rfl) ⟨564765, by rfl⟩ : syracuseStep 1506041 = 1129531) B1129531
theorem B2259899 : Blo 666309 2259899 := bstep (se 1 (by rfl) ⟨1694924, by rfl⟩ : syracuseStep 2259899 = 3389849) B3389849
theorem B1506311 : Blo 666309 1506311 := bstep (se 1 (by rfl) ⟨1129733, by rfl⟩ : syracuseStep 1506311 = 2259467) B2259467
theorem B1604627 : Blo 666309 1604627 := bstep (se 1 (by rfl) ⟨1203470, by rfl⟩ : syracuseStep 1604627 = 2406941) B2406941
theorem B752719 : Blo 666309 752719 := bstep (se 1 (by rfl) ⟨564539, by rfl⟩ : syracuseStep 752719 = 1129079) B1129079
theorem B1506383 : Blo 666309 1506383 := bstep (se 1 (by rfl) ⟨1129787, by rfl⟩ : syracuseStep 1506383 = 2259575) B2259575
theorem B753115 : Blo 666309 753115 := bstep (se 1 (by rfl) ⟨564836, by rfl⟩ : syracuseStep 753115 = 1129673) B1129673
theorem B1506779 : Blo 666309 1506779 := bstep (se 1 (by rfl) ⟨1130084, by rfl⟩ : syracuseStep 1506779 = 2260169) B2260169
theorem B4292513 : Blo 666309 4292513 := bstep (se 2 (by rfl) ⟨1609692, by rfl⟩ : syracuseStep 4292513 = 3219385) B3219385
theorem B753583 : Blo 666309 753583 := bstep (se 1 (by rfl) ⟨565187, by rfl⟩ : syracuseStep 753583 = 1130375) B1130375
theorem B1507247 : Blo 666309 1507247 := bstep (se 1 (by rfl) ⟨1130435, by rfl⟩ : syracuseStep 1507247 = 2260871) B2260871
theorem B1507337 : Blo 666309 1507337 := bstep (se 2 (by rfl) ⟨565251, by rfl⟩ : syracuseStep 1507337 = 1130503) B1130503
theorem B5701751 : Blo 666309 5701751 := bstep (se 1 (by rfl) ⟨4276313, by rfl⟩ : syracuseStep 5701751 = 8552627) B8552627
theorem B4817107 : Blo 666309 4817107 := bstep (se 1 (by rfl) ⟨3612830, by rfl⟩ : syracuseStep 4817107 = 7225661) B7225661
theorem B1737071 : Blo 666309 1737071 := bstep (se 1 (by rfl) ⟨1302803, by rfl⟩ : syracuseStep 1737071 = 2605607) B2605607
theorem B1507751 : Blo 666309 1507751 := bstep (se 1 (by rfl) ⟨1130813, by rfl⟩ : syracuseStep 1507751 = 2261627) B2261627
theorem B754087 : Blo 666309 754087 := bstep (se 1 (by rfl) ⟨565565, by rfl⟩ : syracuseStep 754087 = 1131131) B1131131
theorem B21725657 : Blo 666309 21725657 := bstep (se 2 (by rfl) ⟨8147121, by rfl⟩ : syracuseStep 21725657 = 16294243) B16294243
theorem B1507859 : Blo 666309 1507859 := bstep (se 1 (by rfl) ⟨1130894, by rfl⟩ : syracuseStep 1507859 = 2261789) B2261789
theorem B1507913 : Blo 666309 1507913 := bstep (se 2 (by rfl) ⟨565467, by rfl⟩ : syracuseStep 1507913 = 1130935) B1130935
theorem B1541111 : Blo 666309 1541111 := bstep (se 1 (by rfl) ⟨1155833, by rfl⟩ : syracuseStep 1541111 = 2311667) B2311667
theorem B2262113 : Blo 666309 2262113 := bstep (se 2 (by rfl) ⟨848292, by rfl⟩ : syracuseStep 2262113 = 1696585) B1696585
theorem B1901711 : Blo 666309 1901711 := bstep (se 1 (by rfl) ⟨1426283, by rfl⟩ : syracuseStep 1901711 = 2852567) B2852567
theorem B3671401 : Blo 666309 3671401 := bstep (se 2 (by rfl) ⟨1376775, by rfl⟩ : syracuseStep 3671401 = 2753551) B2753551
theorem B4064825 : Blo 666309 4064825 := bstep (se 2 (by rfl) ⟨1524309, by rfl⟩ : syracuseStep 4064825 = 3048619) B3048619
theorem B3868249 : Blo 666309 3868249 := bstep (se 2 (by rfl) ⟨1450593, by rfl⟩ : syracuseStep 3868249 = 2901187) B2901187
theorem B8587529 : Blo 666309 8587529 := bstep (se 2 (by rfl) ⟨3220323, by rfl⟩ : syracuseStep 8587529 = 6440647) B6440647
theorem B2165159 : Blo 666309 2165159 := bstep (se 1 (by rfl) ⟨1623869, by rfl⟩ : syracuseStep 2165159 = 3247739) B3247739
theorem B3213751 : Blo 666309 3213751 := bstep (se 1 (by rfl) ⟨2410313, by rfl⟩ : syracuseStep 3213751 = 4820627) B4820627
theorem B3214019 : Blo 666309 3214019 := bstep (se 1 (by rfl) ⟨2410514, by rfl⟩ : syracuseStep 3214019 = 4821029) B4821029
theorem B1903351 : Blo 666309 1903351 := bstep (se 1 (by rfl) ⟨1427513, by rfl⟩ : syracuseStep 1903351 = 2855027) B2855027
theorem B3607469 : Blo 666309 3607469 := bstep (se 3 (by rfl) ⟨676400, by rfl⟩ : syracuseStep 3607469 = 1352801) B1352801
theorem B2886779 : Blo 666309 2886779 := bstep (se 1 (by rfl) ⟨2165084, by rfl⟩ : syracuseStep 2886779 = 4330169) B4330169
theorem B4820107 : Blo 666309 4820107 := bstep (se 1 (by rfl) ⟨3615080, by rfl⟩ : syracuseStep 4820107 = 7230161) B7230161
theorem B2854241 : Blo 666309 2854241 := bstep (se 2 (by rfl) ⟨1070340, by rfl⟩ : syracuseStep 2854241 = 2140681) B2140681
theorem B28970459 : Blo 666309 28970459 := bstep (se 1 (by rfl) ⟨21727844, by rfl⟩ : syracuseStep 28970459 = 43455689) B43455689
theorem B1445537 : Blo 666309 1445537 := bstep (se 2 (by rfl) ⟨542076, by rfl⟩ : syracuseStep 1445537 = 1084153) B1084153
theorem B2854703 : Blo 666309 2854703 := bstep (se 1 (by rfl) ⟨2141027, by rfl⟩ : syracuseStep 2854703 = 4282055) B4282055
theorem B2035721 : Blo 666309 2035721 := bstep (se 2 (by rfl) ⟨763395, by rfl⟩ : syracuseStep 2035721 = 1526791) B1526791
theorem B3805289 : Blo 666309 3805289 := bstep (se 2 (by rfl) ⟨1426983, by rfl⟩ : syracuseStep 3805289 = 2853967) B2853967
theorem B1610009 : Blo 666309 1610009 := bstep (se 2 (by rfl) ⟨603753, by rfl⟩ : syracuseStep 1610009 = 1207507) B1207507
theorem B6853319 : Blo 666309 6853319 := bstep (se 1 (by rfl) ⟨5139989, by rfl⟩ : syracuseStep 6853319 = 10279979) B10279979
theorem B3380129 : Blo 666309 3380129 := bstep (se 2 (by rfl) ⟨1267548, by rfl⟩ : syracuseStep 3380129 = 2535097) B2535097
theorem B4821925 : Blo 666309 4821925 := bstep (se 4 (by rfl) ⟨452055, by rfl⟩ : syracuseStep 4821925 = 904111) B904111
theorem B14423129 : Blo 666309 14423129 := bstep (se 2 (by rfl) ⟨5408673, by rfl⟩ : syracuseStep 14423129 = 10817347) B10817347
theorem B1283215 : Blo 666309 1283215 := bstep (se 1 (by rfl) ⟨962411, by rfl⟩ : syracuseStep 1283215 = 1924823) B1924823
theorem B53450189 : Blo 666309 53450189 := bstep (se 3 (by rfl) ⟨10021910, by rfl⟩ : syracuseStep 53450189 = 20043821) B20043821
theorem B2856941 : Blo 666309 2856941 := bstep (se 3 (by rfl) ⟨535676, by rfl⟩ : syracuseStep 2856941 = 1071353) B1071353
theorem B8558621 : Blo 666309 8558621 := bstep (se 3 (by rfl) ⟨1604741, by rfl⟩ : syracuseStep 8558621 = 3209483) B3209483
theorem B1907155 : Blo 666309 1907155 := bstep (se 1 (by rfl) ⟨1430366, by rfl⟩ : syracuseStep 1907155 = 2860733) B2860733
theorem B2857999 : Blo 666309 2857999 := bstep (se 1 (by rfl) ⟨2143499, by rfl⟩ : syracuseStep 2857999 = 4286999) B4286999
theorem B5086475 : Blo 666309 5086475 := bstep (se 1 (by rfl) ⟨3814856, by rfl⟩ : syracuseStep 5086475 = 7629713) B7629713
theorem B3382559 : Blo 666309 3382559 := bstep (se 1 (by rfl) ⟨2536919, by rfl⟩ : syracuseStep 3382559 = 5073839) B5073839
theorem B1907999 : Blo 666309 1907999 := bstep (se 1 (by rfl) ⟨1430999, by rfl⟩ : syracuseStep 1907999 = 2861999) B2861999
theorem B4825241 : Blo 666309 4825241 := bstep (se 2 (by rfl) ⟨1809465, by rfl⟩ : syracuseStep 4825241 = 3618931) B3618931
theorem B762311 : Blo 666309 762311 := bstep (se 1 (by rfl) ⟨571733, by rfl⟩ : syracuseStep 762311 = 1143467) B1143467
theorem B5711147 : Blo 666309 5711147 := bstep (se 1 (by rfl) ⟨4283360, by rfl⟩ : syracuseStep 5711147 = 8566721) B8566721
theorem B3614215 : Blo 666309 3614215 := bstep (se 1 (by rfl) ⟨2710661, by rfl⟩ : syracuseStep 3614215 = 5421323) B5421323
theorem B3384989 : Blo 666309 3384989 := bstep (se 3 (by rfl) ⟨634685, by rfl⟩ : syracuseStep 3384989 = 1269371) B1269371
theorem B1124617 : Blo 666309 1124617 := bstep (se 2 (by rfl) ⟨421731, by rfl⟩ : syracuseStep 1124617 = 843463) B843463
theorem B1714441 : Blo 666309 1714441 := bstep (se 2 (by rfl) ⟨642915, by rfl⟩ : syracuseStep 1714441 = 1285831) B1285831
theorem B52046101 : Blo 666309 52046101 := bstep (se 6 (by rfl) ⟨1219830, by rfl⟩ : syracuseStep 52046101 = 2439661) B2439661
theorem B2861675 : Blo 666309 2861675 := bstep (se 1 (by rfl) ⟨2146256, by rfl⟩ : syracuseStep 2861675 = 4292513) B4292513
theorem B1354423 : Blo 666309 1354423 := bstep (se 1 (by rfl) ⟨1015817, by rfl⟩ : syracuseStep 1354423 = 2031635) B2031635
theorem B666335 : Blo 666309 666335 := bstep (se 1 (by rfl) ⟨499751, by rfl⟩ : syracuseStep 666335 = 999503) B999503
theorem B666415 : Blo 666309 666415 := bstep (se 1 (by rfl) ⟨499811, by rfl⟩ : syracuseStep 666415 = 999623) B999623
theorem B9153415 : Blo 666309 9153415 := bstep (se 1 (by rfl) ⟨6865061, by rfl⟩ : syracuseStep 9153415 = 13730123) B13730123
theorem B1715087 : Blo 666309 1715087 := bstep (se 1 (by rfl) ⟨1286315, by rfl⟩ : syracuseStep 1715087 = 2572631) B2572631
theorem B666523 : Blo 666309 666523 := bstep (se 1 (by rfl) ⟨499892, by rfl⟩ : syracuseStep 666523 = 999785) B999785
theorem B3386285 : Blo 666309 3386285 := bstep (se 3 (by rfl) ⟨634928, by rfl⟩ : syracuseStep 3386285 = 1269857) B1269857
theorem B666575 : Blo 666309 666575 := bstep (se 1 (by rfl) ⟨499931, by rfl⟩ : syracuseStep 666575 = 999863) B999863
theorem B666599 : Blo 666309 666599 := bstep (se 1 (by rfl) ⟨499949, by rfl⟩ : syracuseStep 666599 = 999899) B999899
theorem B6860047 : Blo 666309 6860047 := bstep (se 1 (by rfl) ⟨5145035, by rfl⟩ : syracuseStep 6860047 = 10290071) B10290071
theorem B666911 : Blo 666309 666911 := bstep (se 1 (by rfl) ⟨500183, by rfl⟩ : syracuseStep 666911 = 1000367) B1000367
theorem B97430849 : Blo 666309 97430849 := bstep (se 2 (by rfl) ⟨36536568, by rfl⟩ : syracuseStep 97430849 = 73073137) B73073137
theorem B666971 : Blo 666309 666971 := bstep (se 1 (by rfl) ⟨500228, by rfl⟩ : syracuseStep 666971 = 1000457) B1000457
theorem B666991 : Blo 666309 666991 := bstep (se 1 (by rfl) ⟨500243, by rfl⟩ : syracuseStep 666991 = 1000487) B1000487
theorem B667047 : Blo 666309 667047 := bstep (se 1 (by rfl) ⟨500285, by rfl⟩ : syracuseStep 667047 = 1000571) B1000571
theorem B667131 : Blo 666309 667131 := bstep (se 1 (by rfl) ⟨500348, by rfl⟩ : syracuseStep 667131 = 1000697) B1000697
theorem B667199 : Blo 666309 667199 := bstep (se 1 (by rfl) ⟨500399, by rfl⟩ : syracuseStep 667199 = 1000799) B1000799
theorem B667207 : Blo 666309 667207 := bstep (se 1 (by rfl) ⟨500405, by rfl⟩ : syracuseStep 667207 = 1000811) B1000811
theorem B1126075 : Blo 666309 1126075 := bstep (se 1 (by rfl) ⟨844556, by rfl⟩ : syracuseStep 1126075 = 1689113) B1689113
theorem B667359 : Blo 666309 667359 := bstep (se 1 (by rfl) ⟨500519, by rfl⟩ : syracuseStep 667359 = 1001039) B1001039
theorem B667439 : Blo 666309 667439 := bstep (se 1 (by rfl) ⟨500579, by rfl⟩ : syracuseStep 667439 = 1001159) B1001159
theorem B667547 : Blo 666309 667547 := bstep (se 1 (by rfl) ⟨500660, by rfl⟩ : syracuseStep 667547 = 1001321) B1001321
theorem B667599 : Blo 666309 667599 := bstep (se 1 (by rfl) ⟨500699, by rfl⟩ : syracuseStep 667599 = 1001399) B1001399
theorem B667623 : Blo 666309 667623 := bstep (se 1 (by rfl) ⟨500717, by rfl⟩ : syracuseStep 667623 = 1001435) B1001435
theorem B962825 : Blo 666309 962825 := bstep (se 2 (by rfl) ⟨361059, by rfl⟩ : syracuseStep 962825 = 722119) B722119
theorem B12857615 : Blo 666309 12857615 := bstep (se 1 (by rfl) ⟨9643211, by rfl⟩ : syracuseStep 12857615 = 19286423) B19286423
theorem B667935 : Blo 666309 667935 := bstep (se 1 (by rfl) ⟨500951, by rfl⟩ : syracuseStep 667935 = 1001903) B1001903
theorem B667995 : Blo 666309 667995 := bstep (se 1 (by rfl) ⟨500996, by rfl⟩ : syracuseStep 667995 = 1001993) B1001993
theorem B668015 : Blo 666309 668015 := bstep (se 1 (by rfl) ⟨501011, by rfl⟩ : syracuseStep 668015 = 1002023) B1002023
theorem B668071 : Blo 666309 668071 := bstep (se 1 (by rfl) ⟨501053, by rfl⟩ : syracuseStep 668071 = 1002107) B1002107
theorem B1356257 : Blo 666309 1356257 := bstep (se 2 (by rfl) ⟨508596, by rfl⟩ : syracuseStep 1356257 = 1017193) B1017193
theorem B668155 : Blo 666309 668155 := bstep (se 1 (by rfl) ⟨501116, by rfl⟩ : syracuseStep 668155 = 1002233) B1002233
theorem B3387905 : Blo 666309 3387905 := bstep (se 2 (by rfl) ⟨1270464, by rfl⟩ : syracuseStep 3387905 = 2540929) B2540929
theorem B668223 : Blo 666309 668223 := bstep (se 1 (by rfl) ⟨501167, by rfl⟩ : syracuseStep 668223 = 1002335) B1002335
theorem B668231 : Blo 666309 668231 := bstep (se 1 (by rfl) ⟨501173, by rfl⟩ : syracuseStep 668231 = 1002347) B1002347
theorem B1127135 : Blo 666309 1127135 := bstep (se 1 (by rfl) ⟨845351, by rfl⟩ : syracuseStep 1127135 = 1690703) B1690703
theorem B668383 : Blo 666309 668383 := bstep (se 1 (by rfl) ⟨501287, by rfl⟩ : syracuseStep 668383 = 1002575) B1002575
theorem B668463 : Blo 666309 668463 := bstep (se 1 (by rfl) ⟨501347, by rfl⟩ : syracuseStep 668463 = 1002695) B1002695
theorem B668571 : Blo 666309 668571 := bstep (se 1 (by rfl) ⟨501428, by rfl⟩ : syracuseStep 668571 = 1002857) B1002857
theorem B668623 : Blo 666309 668623 := bstep (se 1 (by rfl) ⟨501467, by rfl⟩ : syracuseStep 668623 = 1002935) B1002935
theorem B668647 : Blo 666309 668647 := bstep (se 1 (by rfl) ⟨501485, by rfl⟩ : syracuseStep 668647 = 1002971) B1002971
theorem B3388391 : Blo 666309 3388391 := bstep (se 1 (by rfl) ⟨2541293, by rfl⟩ : syracuseStep 3388391 = 5082587) B5082587
theorem B1127567 : Blo 666309 1127567 := bstep (se 1 (by rfl) ⟨845675, by rfl⟩ : syracuseStep 1127567 = 1691351) B1691351
theorem B668959 : Blo 666309 668959 := bstep (se 1 (by rfl) ⟨501719, by rfl⟩ : syracuseStep 668959 = 1003439) B1003439
theorem B3257639 : Blo 666309 3257639 := bstep (se 1 (by rfl) ⟨2443229, by rfl⟩ : syracuseStep 3257639 = 4886459) B4886459
theorem B3388715 : Blo 666309 3388715 := bstep (se 1 (by rfl) ⟨2541536, by rfl⟩ : syracuseStep 3388715 = 5083073) B5083073
theorem B669019 : Blo 666309 669019 := bstep (se 1 (by rfl) ⟨501764, by rfl⟩ : syracuseStep 669019 = 1003529) B1003529
theorem B669039 : Blo 666309 669039 := bstep (se 1 (by rfl) ⟨501779, by rfl⟩ : syracuseStep 669039 = 1003559) B1003559
theorem B1127803 : Blo 666309 1127803 := bstep (se 1 (by rfl) ⟨845852, by rfl⟩ : syracuseStep 1127803 = 1691705) B1691705
theorem B669095 : Blo 666309 669095 := bstep (se 1 (by rfl) ⟨501821, by rfl⟩ : syracuseStep 669095 = 1003643) B1003643
theorem B41268689 : Blo 666309 41268689 := bstep (se 2 (by rfl) ⟨15475758, by rfl⟩ : syracuseStep 41268689 = 30951517) B30951517
theorem B669179 : Blo 666309 669179 := bstep (se 1 (by rfl) ⟨501884, by rfl⟩ : syracuseStep 669179 = 1003769) B1003769
theorem B669247 : Blo 666309 669247 := bstep (se 1 (by rfl) ⟨501935, by rfl⟩ : syracuseStep 669247 = 1003871) B1003871
theorem B669255 : Blo 666309 669255 := bstep (se 1 (by rfl) ⟨501941, by rfl⟩ : syracuseStep 669255 = 1003883) B1003883
theorem B669407 : Blo 666309 669407 := bstep (se 1 (by rfl) ⟨502055, by rfl⟩ : syracuseStep 669407 = 1004111) B1004111
theorem B669487 : Blo 666309 669487 := bstep (se 1 (by rfl) ⟨502115, by rfl⟩ : syracuseStep 669487 = 1004231) B1004231
theorem B669595 : Blo 666309 669595 := bstep (se 1 (by rfl) ⟨502196, by rfl⟩ : syracuseStep 669595 = 1004393) B1004393
theorem B669647 : Blo 666309 669647 := bstep (se 1 (by rfl) ⟨502235, by rfl⟩ : syracuseStep 669647 = 1004471) B1004471
theorem B669671 : Blo 666309 669671 := bstep (se 1 (by rfl) ⟨502253, by rfl⟩ : syracuseStep 669671 = 1004507) B1004507
theorem B6404129 : Blo 666309 6404129 := bstep (se 2 (by rfl) ⟨2401548, by rfl⟩ : syracuseStep 6404129 = 4803097) B4803097
theorem B800987 : Blo 666309 800987 := bstep (se 1 (by rfl) ⟨600740, by rfl⟩ : syracuseStep 800987 = 1201481) B1201481
theorem B3389687 : Blo 666309 3389687 := bstep (se 1 (by rfl) ⟨2542265, by rfl⟩ : syracuseStep 3389687 = 5084531) B5084531
theorem B669983 : Blo 666309 669983 := bstep (se 1 (by rfl) ⟨502487, by rfl⟩ : syracuseStep 669983 = 1004975) B1004975
theorem B670043 : Blo 666309 670043 := bstep (se 1 (by rfl) ⟨502532, by rfl⟩ : syracuseStep 670043 = 1005065) B1005065
theorem B670063 : Blo 666309 670063 := bstep (se 1 (by rfl) ⟨502547, by rfl⟩ : syracuseStep 670063 = 1005095) B1005095
theorem B670119 : Blo 666309 670119 := bstep (se 1 (by rfl) ⟨502589, by rfl⟩ : syracuseStep 670119 = 1005179) B1005179
theorem B670203 : Blo 666309 670203 := bstep (se 1 (by rfl) ⟨502652, by rfl⟩ : syracuseStep 670203 = 1005305) B1005305
theorem B670271 : Blo 666309 670271 := bstep (se 1 (by rfl) ⟨502703, by rfl⟩ : syracuseStep 670271 = 1005407) B1005407
theorem B670279 : Blo 666309 670279 := bstep (se 1 (by rfl) ⟨502709, by rfl⟩ : syracuseStep 670279 = 1005419) B1005419
theorem B3390173 : Blo 666309 3390173 := bstep (se 3 (by rfl) ⟨635657, by rfl⟩ : syracuseStep 3390173 = 1271315) B1271315
theorem B2702099 : Blo 666309 2702099 := bstep (se 1 (by rfl) ⟨2026574, by rfl⟩ : syracuseStep 2702099 = 4053149) B4053149
theorem B1424147 : Blo 666309 1424147 := bstep (se 1 (by rfl) ⟨1068110, by rfl⟩ : syracuseStep 1424147 = 2136221) B2136221
theorem B1129295 : Blo 666309 1129295 := bstep (se 1 (by rfl) ⟨846971, by rfl⟩ : syracuseStep 1129295 = 1693943) B1693943
theorem B1719119 : Blo 666309 1719119 := bstep (se 1 (by rfl) ⟨1289339, by rfl⟩ : syracuseStep 1719119 = 2578679) B2578679
theorem B2145167 : Blo 666309 2145167 := bstep (se 1 (by rfl) ⟨1608875, by rfl⟩ : syracuseStep 2145167 = 3217751) B3217751
theorem B1686815 : Blo 666309 1686815 := bstep (se 1 (by rfl) ⟨1265111, by rfl⟩ : syracuseStep 1686815 = 2530223) B2530223
theorem B2407747 : Blo 666309 2407747 := bstep (se 1 (by rfl) ⟨1805810, by rfl⟩ : syracuseStep 2407747 = 3611621) B3611621
theorem B3816953 : Blo 666309 3816953 := bstep (se 2 (by rfl) ⟨1431357, by rfl⟩ : syracuseStep 3816953 = 2862715) B2862715
theorem B4275827 : Blo 666309 4275827 := bstep (se 1 (by rfl) ⟨3206870, by rfl⟩ : syracuseStep 4275827 = 6413741) B6413741
theorem B6438649 : Blo 666309 6438649 := bstep (se 2 (by rfl) ⟨2414493, by rfl⟩ : syracuseStep 6438649 = 4828987) B4828987
theorem B1130287 : Blo 666309 1130287 := bstep (se 1 (by rfl) ⟨847715, by rfl⟩ : syracuseStep 1130287 = 1695431) B1695431
theorem B1687351 : Blo 666309 1687351 := bstep (se 1 (by rfl) ⟨1265513, by rfl⟩ : syracuseStep 1687351 = 2531027) B2531027
theorem B3915649 : Blo 666309 3915649 := bstep (se 2 (by rfl) ⟨1468368, by rfl⟩ : syracuseStep 3915649 = 2936737) B2936737
theorem B999689 : Blo 666309 999689 := bstep (se 2 (by rfl) ⟨374883, by rfl⟩ : syracuseStep 999689 = 749767) B749767
theorem B1687817 : Blo 666309 1687817 := bstep (se 2 (by rfl) ⟨632931, by rfl⟩ : syracuseStep 1687817 = 1265863) B1265863
theorem B1425737 : Blo 666309 1425737 := bstep (se 2 (by rfl) ⟨534651, by rfl⟩ : syracuseStep 1425737 = 1069303) B1069303
theorem B999791 : Blo 666309 999791 := bstep (se 1 (by rfl) ⟨749843, by rfl⟩ : syracuseStep 999791 = 1499687) B1499687
theorem B3424769 : Blo 666309 3424769 := bstep (se 2 (by rfl) ⟨1284288, by rfl⟩ : syracuseStep 3424769 = 2568577) B2568577
theorem B1000007 : Blo 666309 1000007 := bstep (se 1 (by rfl) ⟨750005, by rfl⟩ : syracuseStep 1000007 = 1500011) B1500011
theorem B1000043 : Blo 666309 1000043 := bstep (se 1 (by rfl) ⟨750032, by rfl⟩ : syracuseStep 1000043 = 1500065) B1500065
theorem B1426027 : Blo 666309 1426027 := bstep (se 1 (by rfl) ⟨1069520, by rfl⟩ : syracuseStep 1426027 = 2139041) B2139041
theorem B1000271 : Blo 666309 1000271 := bstep (se 1 (by rfl) ⟨750203, by rfl⟩ : syracuseStep 1000271 = 1500407) B1500407
theorem B5129153 : Blo 666309 5129153 := bstep (se 2 (by rfl) ⟨1923432, by rfl⟩ : syracuseStep 5129153 = 3846865) B3846865
theorem B3621827 : Blo 666309 3621827 := bstep (se 1 (by rfl) ⟨2716370, by rfl⟩ : syracuseStep 3621827 = 5432741) B5432741
theorem B1000667 : Blo 666309 1000667 := bstep (se 1 (by rfl) ⟨750500, by rfl⟩ : syracuseStep 1000667 = 1501001) B1501001
theorem B1688809 : Blo 666309 1688809 := bstep (se 2 (by rfl) ⟨633303, by rfl⟩ : syracuseStep 1688809 = 1266607) B1266607
theorem B1000841 : Blo 666309 1000841 := bstep (se 2 (by rfl) ⟨375315, by rfl⟩ : syracuseStep 1000841 = 750631) B750631
theorem B1688971 : Blo 666309 1688971 := bstep (se 1 (by rfl) ⟨1266728, by rfl⟩ : syracuseStep 1688971 = 2533457) B2533457
theorem B1689275 : Blo 666309 1689275 := bstep (se 1 (by rfl) ⟨1266956, by rfl⟩ : syracuseStep 1689275 = 2533913) B2533913
theorem B1001195 : Blo 666309 1001195 := bstep (se 1 (by rfl) ⟨750896, by rfl⟩ : syracuseStep 1001195 = 1501793) B1501793
theorem B1427257 : Blo 666309 1427257 := bstep (se 2 (by rfl) ⟨535221, by rfl⟩ : syracuseStep 1427257 = 1070443) B1070443
theorem B2901841 : Blo 666309 2901841 := bstep (se 2 (by rfl) ⟨1088190, by rfl⟩ : syracuseStep 2901841 = 2176381) B2176381
theorem B1001423 : Blo 666309 1001423 := bstep (se 1 (by rfl) ⟨751067, by rfl⟩ : syracuseStep 1001423 = 1502135) B1502135
theorem B2410631 : Blo 666309 2410631 := bstep (se 1 (by rfl) ⟨1807973, by rfl⟩ : syracuseStep 2410631 = 3615947) B3615947
theorem B14469313 : Blo 666309 14469313 := bstep (se 2 (by rfl) ⟨5425992, by rfl⟩ : syracuseStep 14469313 = 10851985) B10851985
theorem B6703397 : Blo 666309 6703397 := bstep (se 4 (by rfl) ⟨628443, by rfl⟩ : syracuseStep 6703397 = 1256887) B1256887
theorem B1001819 : Blo 666309 1001819 := bstep (se 1 (by rfl) ⟨751364, by rfl⟩ : syracuseStep 1001819 = 1502729) B1502729
theorem B21711239 : Blo 666309 21711239 := bstep (se 1 (by rfl) ⟨16283429, by rfl⟩ : syracuseStep 21711239 = 32566859) B32566859
theorem B1002047 : Blo 666309 1002047 := bstep (se 1 (by rfl) ⟨751535, by rfl⟩ : syracuseStep 1002047 = 1503071) B1503071
theorem B21908069 : Blo 666309 21908069 := bstep (se 4 (by rfl) ⟨2053881, by rfl⟩ : syracuseStep 21908069 = 4107763) B4107763
theorem B1002167 : Blo 666309 1002167 := bstep (se 1 (by rfl) ⟨751625, by rfl⟩ : syracuseStep 1002167 = 1503251) B1503251
theorem B5557015 : Blo 666309 5557015 := bstep (se 1 (by rfl) ⟨4167761, by rfl⟩ : syracuseStep 5557015 = 8335523) B8335523
theorem B1002395 : Blo 666309 1002395 := bstep (se 1 (by rfl) ⟨751796, by rfl⟩ : syracuseStep 1002395 = 1503593) B1503593
theorem B1068175 : Blo 666309 1068175 := bstep (se 1 (by rfl) ⟨801131, by rfl⟩ : syracuseStep 1068175 = 1602263) B1602263
theorem B3296477 : Blo 666309 3296477 := bstep (se 3 (by rfl) ⟨618089, by rfl⟩ : syracuseStep 3296477 = 1236179) B1236179
theorem B1002791 : Blo 666309 1002791 := bstep (se 1 (by rfl) ⟨752093, by rfl⟩ : syracuseStep 1002791 = 1504187) B1504187
theorem B1002875 : Blo 666309 1002875 := bstep (se 1 (by rfl) ⟨752156, by rfl⟩ : syracuseStep 1002875 = 1504313) B1504313
theorem B1003001 : Blo 666309 1003001 := bstep (se 2 (by rfl) ⟨376125, by rfl⟩ : syracuseStep 1003001 = 752251) B752251
theorem B1691219 : Blo 666309 1691219 := bstep (se 1 (by rfl) ⟨1268414, by rfl⟩ : syracuseStep 1691219 = 2536829) B2536829
theorem B1003103 : Blo 666309 1003103 := bstep (se 1 (by rfl) ⟨752327, by rfl⟩ : syracuseStep 1003103 = 1504655) B1504655
theorem B675631 : Blo 666309 675631 := bstep (se 1 (by rfl) ⟨506723, by rfl⟩ : syracuseStep 675631 = 1013447) B1013447
theorem B1003319 : Blo 666309 1003319 := bstep (se 1 (by rfl) ⟨752489, by rfl⟩ : syracuseStep 1003319 = 1504979) B1504979
theorem B1003625 : Blo 666309 1003625 := bstep (se 2 (by rfl) ⟨376359, by rfl⟩ : syracuseStep 1003625 = 752719) B752719
theorem B1003943 : Blo 666309 1003943 := bstep (se 1 (by rfl) ⟨752957, by rfl⟩ : syracuseStep 1003943 = 1505915) B1505915
theorem B7590347 : Blo 666309 7590347 := bstep (se 1 (by rfl) ⟨5692760, by rfl⟩ : syracuseStep 7590347 = 11385521) B11385521
theorem B1004027 : Blo 666309 1004027 := bstep (se 1 (by rfl) ⟨753020, by rfl⟩ : syracuseStep 1004027 = 1506041) B1506041
theorem B1004153 : Blo 666309 1004153 := bstep (se 2 (by rfl) ⟨376557, by rfl⟩ : syracuseStep 1004153 = 753115) B753115
theorem B2249369 : Blo 666309 2249369 := bstep (se 2 (by rfl) ⟨843513, by rfl⟩ : syracuseStep 2249369 = 1687027) B1687027
theorem B1004207 : Blo 666309 1004207 := bstep (se 1 (by rfl) ⟨753155, by rfl⟩ : syracuseStep 1004207 = 1506311) B1506311
theorem B1069751 : Blo 666309 1069751 := bstep (se 1 (by rfl) ⟨802313, by rfl⟩ : syracuseStep 1069751 = 1604627) B1604627
theorem B1004255 : Blo 666309 1004255 := bstep (se 1 (by rfl) ⟨753191, by rfl⟩ : syracuseStep 1004255 = 1506383) B1506383
theorem B1430291 : Blo 666309 1430291 := bstep (se 1 (by rfl) ⟨1072718, by rfl⟩ : syracuseStep 1430291 = 2145437) B2145437
theorem B26432477 : Blo 666309 26432477 := bstep (se 3 (by rfl) ⟨4956089, by rfl⟩ : syracuseStep 26432477 = 9912179) B9912179
theorem B1692647 : Blo 666309 1692647 := bstep (se 1 (by rfl) ⟨1269485, by rfl⟩ : syracuseStep 1692647 = 2538971) B2538971
theorem B1004519 : Blo 666309 1004519 := bstep (se 1 (by rfl) ⟨753389, by rfl⟩ : syracuseStep 1004519 = 1506779) B1506779
theorem B3429533 : Blo 666309 3429533 := bstep (se 3 (by rfl) ⟨643037, by rfl⟩ : syracuseStep 3429533 = 1286075) B1286075
theorem B1004777 : Blo 666309 1004777 := bstep (se 2 (by rfl) ⟨376791, by rfl⟩ : syracuseStep 1004777 = 753583) B753583
theorem B1430777 : Blo 666309 1430777 := bstep (se 2 (by rfl) ⟨536541, by rfl⟩ : syracuseStep 1430777 = 1073083) B1073083
theorem B1004831 : Blo 666309 1004831 := bstep (se 1 (by rfl) ⟨753623, by rfl⟩ : syracuseStep 1004831 = 1507247) B1507247
theorem B7230815 : Blo 666309 7230815 := bstep (se 1 (by rfl) ⟨5423111, by rfl⟩ : syracuseStep 7230815 = 10846223) B10846223
theorem B1004999 : Blo 666309 1004999 := bstep (se 1 (by rfl) ⟨753749, by rfl⟩ : syracuseStep 1004999 = 1507499) B1507499
theorem B1693345 : Blo 666309 1693345 := bstep (se 2 (by rfl) ⟨635004, by rfl⟩ : syracuseStep 1693345 = 1270009) B1270009
theorem B1005353 : Blo 666309 1005353 := bstep (se 2 (by rfl) ⟨377007, by rfl⟩ : syracuseStep 1005353 = 754015) B754015
theorem B1693487 : Blo 666309 1693487 := bstep (se 1 (by rfl) ⟨1270115, by rfl⟩ : syracuseStep 1693487 = 2540231) B2540231
theorem B1005359 : Blo 666309 1005359 := bstep (se 1 (by rfl) ⟨754019, by rfl⟩ : syracuseStep 1005359 = 1508039) B1508039
theorem B1267663 : Blo 666309 1267663 := bstep (se 1 (by rfl) ⟨950747, by rfl⟩ : syracuseStep 1267663 = 1901495) B1901495
theorem B2250881 : Blo 666309 2250881 := bstep (se 2 (by rfl) ⟨844080, by rfl⟩ : syracuseStep 2250881 = 1688161) B1688161
theorem B4806935 : Blo 666309 4806935 := bstep (se 1 (by rfl) ⟨3605201, by rfl⟩ : syracuseStep 4806935 = 7210403) B7210403
theorem B1694135 : Blo 666309 1694135 := bstep (se 1 (by rfl) ⟨1270601, by rfl⟩ : syracuseStep 1694135 = 2541203) B2541203
theorem B4807163 : Blo 666309 4807163 := bstep (se 1 (by rfl) ⟨3605372, by rfl⟩ : syracuseStep 4807163 = 7210745) B7210745
theorem B2251259 : Blo 666309 2251259 := bstep (se 1 (by rfl) ⟨1688444, by rfl⟩ : syracuseStep 2251259 = 3376889) B3376889
theorem B1464895 : Blo 666309 1464895 := bstep (se 1 (by rfl) ⟨1098671, by rfl⟩ : syracuseStep 1464895 = 2197343) B2197343
theorem B1268399 : Blo 666309 1268399 := bstep (se 1 (by rfl) ⟨951299, by rfl⟩ : syracuseStep 1268399 = 1902599) B1902599
theorem B1268635 : Blo 666309 1268635 := bstep (se 1 (by rfl) ⟨951476, by rfl⟩ : syracuseStep 1268635 = 1902953) B1902953
theorem B2251691 : Blo 666309 2251691 := bstep (se 1 (by rfl) ⟨1688768, by rfl⟩ : syracuseStep 2251691 = 3377537) B3377537
theorem B6511535 : Blo 666309 6511535 := bstep (se 1 (by rfl) ⟨4883651, by rfl⟩ : syracuseStep 6511535 = 9767303) B9767303
theorem B1203175 : Blo 666309 1203175 := bstep (se 1 (by rfl) ⟨902381, by rfl⟩ : syracuseStep 1203175 = 1804763) B1804763
theorem B3202163 : Blo 666309 3202163 := bstep (se 1 (by rfl) ⟨2401622, by rfl⟩ : syracuseStep 3202163 = 4803245) B4803245
theorem B11394269 : Blo 666309 11394269 := bstep (se 3 (by rfl) ⟨2136425, by rfl⟩ : syracuseStep 11394269 = 4272851) B4272851
theorem B2710921 : Blo 666309 2710921 := bstep (se 2 (by rfl) ⟨1016595, by rfl⟩ : syracuseStep 2710921 = 2033191) B2033191
theorem B2252231 : Blo 666309 2252231 := bstep (se 1 (by rfl) ⟨1689173, by rfl⟩ : syracuseStep 2252231 = 3378347) B3378347
theorem B1695239 : Blo 666309 1695239 := bstep (se 1 (by rfl) ⟨1271429, by rfl⟩ : syracuseStep 1695239 = 2542859) B2542859
theorem B1695289 : Blo 666309 1695289 := bstep (se 2 (by rfl) ⟨635733, by rfl⟩ : syracuseStep 1695289 = 1271467) B1271467
theorem B2252555 : Blo 666309 2252555 := bstep (se 1 (by rfl) ⟨1689416, by rfl⟩ : syracuseStep 2252555 = 3378833) B3378833
theorem B1695593 : Blo 666309 1695593 := bstep (se 2 (by rfl) ⟨635847, by rfl⟩ : syracuseStep 1695593 = 1271695) B1271695
theorem B2252825 : Blo 666309 2252825 := bstep (se 2 (by rfl) ⟨844809, by rfl⟩ : syracuseStep 2252825 = 1689619) B1689619
theorem B1826945 : Blo 666309 1826945 := bstep (se 2 (by rfl) ⟨685104, by rfl⟩ : syracuseStep 1826945 = 1370209) B1370209
theorem B12869765 : Blo 666309 12869765 := bstep (se 4 (by rfl) ⟨1206540, by rfl⟩ : syracuseStep 12869765 = 2413081) B2413081
theorem B5693651 : Blo 666309 5693651 := bstep (se 1 (by rfl) ⟨4270238, by rfl⟩ : syracuseStep 5693651 = 8540477) B8540477
theorem B1696211 : Blo 666309 1696211 := bstep (se 1 (by rfl) ⟨1272158, by rfl⟩ : syracuseStep 1696211 = 2544317) B2544317
theorem B3138011 : Blo 666309 3138011 := bstep (se 1 (by rfl) ⟨2353508, by rfl⟩ : syracuseStep 3138011 = 4707017) B4707017
theorem B844283 : Blo 666309 844283 := bstep (se 1 (by rfl) ⟨633212, by rfl⟩ : syracuseStep 844283 = 1266425) B1266425
theorem B713287 : Blo 666309 713287 := bstep (se 1 (by rfl) ⟨534965, by rfl⟩ : syracuseStep 713287 = 1069931) B1069931
theorem B1270343 : Blo 666309 1270343 := bstep (se 1 (by rfl) ⟨952757, by rfl⟩ : syracuseStep 1270343 = 1905515) B1905515
theorem B1499831 : Blo 666309 1499831 := bstep (se 1 (by rfl) ⟨1124873, by rfl⟩ : syracuseStep 1499831 = 2249747) B2249747
theorem B1270495 : Blo 666309 1270495 := bstep (se 1 (by rfl) ⟨952871, by rfl⟩ : syracuseStep 1270495 = 1905743) B1905743
theorem B1500047 : Blo 666309 1500047 := bstep (se 1 (by rfl) ⟨1125035, by rfl⟩ : syracuseStep 1500047 = 2250071) B2250071
theorem B5694401 : Blo 666309 5694401 := bstep (se 2 (by rfl) ⟨2135400, by rfl⟩ : syracuseStep 5694401 = 4270801) B4270801
theorem B4056263 : Blo 666309 4056263 := bstep (se 1 (by rfl) ⟨3042197, by rfl⟩ : syracuseStep 4056263 = 6084395) B6084395
theorem B2254067 : Blo 666309 2254067 := bstep (se 1 (by rfl) ⟨1690550, by rfl⟩ : syracuseStep 2254067 = 3381101) B3381101
theorem B2254175 : Blo 666309 2254175 := bstep (se 1 (by rfl) ⟨1690631, by rfl⟩ : syracuseStep 2254175 = 3381263) B3381263
theorem B714107 : Blo 666309 714107 := bstep (se 1 (by rfl) ⟨535580, by rfl⟩ : syracuseStep 714107 = 1071161) B1071161
theorem B845255 : Blo 666309 845255 := bstep (se 1 (by rfl) ⟨633941, by rfl⟩ : syracuseStep 845255 = 1267883) B1267883
theorem B1500767 : Blo 666309 1500767 := bstep (se 1 (by rfl) ⟨1125575, by rfl⟩ : syracuseStep 1500767 = 2251151) B2251151
theorem B845407 : Blo 666309 845407 := bstep (se 1 (by rfl) ⟨634055, by rfl⟩ : syracuseStep 845407 = 1268111) B1268111
theorem B1500983 : Blo 666309 1500983 := bstep (se 1 (by rfl) ⟨1125737, by rfl⟩ : syracuseStep 1500983 = 2251475) B2251475
theorem B1501289 : Blo 666309 1501289 := bstep (se 2 (by rfl) ⟨562983, by rfl⟩ : syracuseStep 1501289 = 1125967) B1125967
theorem B3041831 : Blo 666309 3041831 := bstep (se 1 (by rfl) ⟨2281373, by rfl⟩ : syracuseStep 3041831 = 4562747) B4562747
theorem B1501775 : Blo 666309 1501775 := bstep (se 1 (by rfl) ⟨1126331, by rfl⟩ : syracuseStep 1501775 = 2252663) B2252663
theorem B20834995 : Blo 666309 20834995 := bstep (se 1 (by rfl) ⟨15626246, by rfl⟩ : syracuseStep 20834995 = 31252493) B31252493
theorem B1501919 : Blo 666309 1501919 := bstep (se 1 (by rfl) ⟨1126439, by rfl⟩ : syracuseStep 1501919 = 2252879) B2252879
theorem B2255741 : Blo 666309 2255741 := bstep (se 3 (by rfl) ⟨422951, by rfl⟩ : syracuseStep 2255741 = 845903) B845903
theorem B1502171 : Blo 666309 1502171 := bstep (se 1 (by rfl) ⟨1126628, by rfl⟩ : syracuseStep 1502171 = 2253257) B2253257
theorem B2256011 : Blo 666309 2256011 := bstep (se 1 (by rfl) ⟨1692008, by rfl⟩ : syracuseStep 2256011 = 3384017) B3384017
theorem B1502351 : Blo 666309 1502351 := bstep (se 1 (by rfl) ⟨1126763, by rfl⟩ : syracuseStep 1502351 = 2253527) B2253527
theorem B1502441 : Blo 666309 1502441 := bstep (se 2 (by rfl) ⟨563415, by rfl⟩ : syracuseStep 1502441 = 1126831) B1126831
theorem B1502495 : Blo 666309 1502495 := bstep (se 1 (by rfl) ⟨1126871, by rfl⟩ : syracuseStep 1502495 = 2253743) B2253743
theorem B1503017 : Blo 666309 1503017 := bstep (se 2 (by rfl) ⟨563631, by rfl⟩ : syracuseStep 1503017 = 1127263) B1127263
theorem B3796793 : Blo 666309 3796793 := bstep (se 2 (by rfl) ⟨1423797, by rfl⟩ : syracuseStep 3796793 = 2847595) B2847595
theorem B9531341 : Blo 666309 9531341 := bstep (se 3 (by rfl) ⟨1787126, by rfl⟩ : syracuseStep 9531341 = 3574253) B3574253
theorem B847847 : Blo 666309 847847 := bstep (se 1 (by rfl) ⟨635885, by rfl⟩ : syracuseStep 847847 = 1271771) B1271771
theorem B749947 : Blo 666309 749947 := bstep (se 1 (by rfl) ⟨562460, by rfl⟩ : syracuseStep 749947 = 1124921) B1124921
theorem B2257631 : Blo 666309 2257631 := bstep (se 1 (by rfl) ⟨1693223, by rfl⟩ : syracuseStep 2257631 = 3386447) B3386447
theorem B750415 : Blo 666309 750415 := bstep (se 1 (by rfl) ⟨562811, by rfl⟩ : syracuseStep 750415 = 1125623) B1125623
theorem B1504079 : Blo 666309 1504079 := bstep (se 1 (by rfl) ⟨1128059, by rfl⟩ : syracuseStep 1504079 = 2256119) B2256119
theorem B7599095 : Blo 666309 7599095 := bstep (se 1 (by rfl) ⟨5699321, by rfl⟩ : syracuseStep 7599095 = 11398643) B11398643
theorem B1504295 : Blo 666309 1504295 := bstep (se 1 (by rfl) ⟨1128221, by rfl⟩ : syracuseStep 1504295 = 2256443) B2256443
theorem B2847869 : Blo 666309 2847869 := bstep (se 3 (by rfl) ⟨533975, by rfl⟩ : syracuseStep 2847869 = 1067951) B1067951
theorem B2258063 : Blo 666309 2258063 := bstep (se 1 (by rfl) ⟨1693547, by rfl⟩ : syracuseStep 2258063 = 3387095) B3387095
theorem B5698775 : Blo 666309 5698775 := bstep (se 1 (by rfl) ⟨4274081, by rfl⟩ : syracuseStep 5698775 = 8548163) B8548163
theorem B750811 : Blo 666309 750811 := bstep (se 1 (by rfl) ⟨563108, by rfl⟩ : syracuseStep 750811 = 1126217) B1126217
theorem B1504475 : Blo 666309 1504475 := bstep (se 1 (by rfl) ⟨1128356, by rfl⟩ : syracuseStep 1504475 = 2256713) B2256713
theorem B6419735 : Blo 666309 6419735 := bstep (se 1 (by rfl) ⟨4814801, by rfl⟩ : syracuseStep 6419735 = 9629603) B9629603
theorem B1504673 : Blo 666309 1504673 := bstep (se 2 (by rfl) ⟨564252, by rfl⟩ : syracuseStep 1504673 = 1128505) B1128505
theorem B1603003 : Blo 666309 1603003 := bstep (se 1 (by rfl) ⟨1202252, by rfl⟩ : syracuseStep 1603003 = 2404505) B2404505
theorem B751099 : Blo 666309 751099 := bstep (se 1 (by rfl) ⟨563324, by rfl⟩ : syracuseStep 751099 = 1126649) B1126649
theorem B751279 : Blo 666309 751279 := bstep (se 1 (by rfl) ⟨563459, by rfl⟩ : syracuseStep 751279 = 1126919) B1126919
theorem B751567 : Blo 666309 751567 := bstep (se 1 (by rfl) ⟨563675, by rfl⟩ : syracuseStep 751567 = 1127351) B1127351
theorem B1505231 : Blo 666309 1505231 := bstep (se 1 (by rfl) ⟨1128923, by rfl⟩ : syracuseStep 1505231 = 2257847) B2257847
theorem B5404715 : Blo 666309 5404715 := bstep (se 1 (by rfl) ⟨4053536, by rfl⟩ : syracuseStep 5404715 = 8107073) B8107073
theorem B3602627 : Blo 666309 3602627 := bstep (se 1 (by rfl) ⟨2701970, by rfl⟩ : syracuseStep 3602627 = 5403941) B5403941
theorem B13727981 : Blo 666309 13727981 := bstep (se 3 (by rfl) ⟨2573996, by rfl⟩ : syracuseStep 13727981 = 5147993) B5147993
theorem B2259197 : Blo 666309 2259197 := bstep (se 3 (by rfl) ⟨423599, by rfl⟩ : syracuseStep 2259197 = 847199) B847199
theorem B1898761 : Blo 666309 1898761 := bstep (se 2 (by rfl) ⟨712035, by rfl⟩ : syracuseStep 1898761 = 1424071) B1424071
theorem B1505609 : Blo 666309 1505609 := bstep (se 2 (by rfl) ⟨564603, by rfl⟩ : syracuseStep 1505609 = 1129207) B1129207
theorem B751963 : Blo 666309 751963 := bstep (se 1 (by rfl) ⟨563972, by rfl⟩ : syracuseStep 751963 = 1127945) B1127945
theorem B1505627 : Blo 666309 1505627 := bstep (se 1 (by rfl) ⟨1129220, by rfl⟩ : syracuseStep 1505627 = 2258441) B2258441
theorem B752071 : Blo 666309 752071 := bstep (se 1 (by rfl) ⟨564053, by rfl⟩ : syracuseStep 752071 = 1128107) B1128107
theorem B5077637 : Blo 666309 5077637 := bstep (se 4 (by rfl) ⟨476028, by rfl⟩ : syracuseStep 5077637 = 952057) B952057
theorem B752431 : Blo 666309 752431 := bstep (se 1 (by rfl) ⟨564323, by rfl⟩ : syracuseStep 752431 = 1128647) B1128647
theorem B752539 : Blo 666309 752539 := bstep (se 1 (by rfl) ⟨564404, by rfl⟩ : syracuseStep 752539 = 1128809) B1128809
theorem B1506203 : Blo 666309 1506203 := bstep (se 1 (by rfl) ⟨1129652, by rfl⟩ : syracuseStep 1506203 = 2259305) B2259305
theorem B4291613 : Blo 666309 4291613 := bstep (se 3 (by rfl) ⟨804677, by rfl⟩ : syracuseStep 4291613 = 1609355) B1609355
theorem B2260007 : Blo 666309 2260007 := bstep (se 1 (by rfl) ⟨1695005, by rfl⟩ : syracuseStep 2260007 = 3390011) B3390011
theorem B1506401 : Blo 666309 1506401 := bstep (se 2 (by rfl) ⟨564900, by rfl⟩ : syracuseStep 1506401 = 1129801) B1129801
theorem B7306363 : Blo 666309 7306363 := bstep (se 1 (by rfl) ⟨5479772, by rfl⟩ : syracuseStep 7306363 = 10959545) B10959545
theorem B1932427 : Blo 666309 1932427 := bstep (se 1 (by rfl) ⟨1449320, by rfl⟩ : syracuseStep 1932427 = 2898641) B2898641
theorem B752935 : Blo 666309 752935 := bstep (se 1 (by rfl) ⟨564701, by rfl⟩ : syracuseStep 752935 = 1129403) B1129403
theorem B1506599 : Blo 666309 1506599 := bstep (se 1 (by rfl) ⟨1129949, by rfl⟩ : syracuseStep 1506599 = 2259899) B2259899
theorem B753007 : Blo 666309 753007 := bstep (se 1 (by rfl) ⟨564755, by rfl⟩ : syracuseStep 753007 = 1129511) B1129511
theorem B2260439 : Blo 666309 2260439 := bstep (se 1 (by rfl) ⟨1695329, by rfl⟩ : syracuseStep 2260439 = 3390659) B3390659
theorem B2850329 : Blo 666309 2850329 := bstep (se 2 (by rfl) ⟨1068873, by rfl⟩ : syracuseStep 2850329 = 2137747) B2137747
theorem B753223 : Blo 666309 753223 := bstep (se 1 (by rfl) ⟨564917, by rfl⟩ : syracuseStep 753223 = 1129835) B1129835
theorem B1506977 : Blo 666309 1506977 := bstep (se 2 (by rfl) ⟨565116, by rfl⟩ : syracuseStep 1506977 = 1130233) B1130233
theorem B17137331 : Blo 666309 17137331 := bstep (se 1 (by rfl) ⟨12852998, by rfl⟩ : syracuseStep 17137331 = 25705997) B25705997
theorem B3801167 : Blo 666309 3801167 := bstep (se 1 (by rfl) ⟨2850875, by rfl⟩ : syracuseStep 3801167 = 5701751) B5701751
theorem B950491 : Blo 666309 950491 := bstep (se 1 (by rfl) ⟨712868, by rfl⟩ : syracuseStep 950491 = 1425737) B1425737
theorem B6422809 : Blo 666309 6422809 := bstep (se 2 (by rfl) ⟨2408553, by rfl⟩ : syracuseStep 6422809 = 4817107) B4817107
theorem B14483771 : Blo 666309 14483771 := bstep (se 1 (by rfl) ⟨10862828, by rfl⟩ : syracuseStep 14483771 = 21725657) B21725657
theorem B1508075 : Blo 666309 1508075 := bstep (se 1 (by rfl) ⟨1131056, by rfl⟩ : syracuseStep 1508075 = 2262113) B2262113
theorem B951049 : Blo 666309 951049 := bstep (se 2 (by rfl) ⟨356643, by rfl⟩ : syracuseStep 951049 = 713287) B713287
theorem B1901369 : Blo 666309 1901369 := bstep (se 2 (by rfl) ⟨713013, by rfl⟩ : syracuseStep 1901369 = 1426027) B1426027
theorem B2032829 : Blo 666309 2032829 := bstep (se 3 (by rfl) ⟨381155, by rfl⟩ : syracuseStep 2032829 = 762311) B762311
theorem B1607087 : Blo 666309 1607087 := bstep (se 1 (by rfl) ⟨1205315, by rfl⟩ : syracuseStep 1607087 = 2410631) B2410631
theorem B1443439 : Blo 666309 1443439 := bstep (se 1 (by rfl) ⟨1082579, by rfl⟩ : syracuseStep 1443439 = 2165159) B2165159
theorem B4818953 : Blo 666309 4818953 := bstep (se 2 (by rfl) ⟨1807107, by rfl⟩ : syracuseStep 4818953 = 3614215) B3614215
theorem B2197651 : Blo 666309 2197651 := bstep (se 1 (by rfl) ⟨1648238, by rfl⟩ : syracuseStep 2197651 = 3296477) B3296477
theorem B1902827 : Blo 666309 1902827 := bstep (se 1 (by rfl) ⟨1427120, by rfl⟩ : syracuseStep 1902827 = 2854241) B2854241
theorem B1903009 : Blo 666309 1903009 := bstep (se 2 (by rfl) ⟨713628, by rfl⟩ : syracuseStep 1903009 = 1427257) B1427257
theorem B1903135 : Blo 666309 1903135 := bstep (se 1 (by rfl) ⟨1427351, by rfl⟩ : syracuseStep 1903135 = 2854703) B2854703
theorem B953527 : Blo 666309 953527 := bstep (se 1 (by rfl) ⟨715145, by rfl⟩ : syracuseStep 953527 = 1430291) B1430291
theorem B953851 : Blo 666309 953851 := bstep (se 1 (by rfl) ⟨715388, by rfl⟩ : syracuseStep 953851 = 1430777) B1430777
theorem B4820543 : Blo 666309 4820543 := bstep (se 1 (by rfl) ⟨3615407, by rfl⟩ : syracuseStep 4820543 = 7230815) B7230815
theorem B1805897 : Blo 666309 1805897 := bstep (se 2 (by rfl) ⟨677211, by rfl⟩ : syracuseStep 1805897 = 1354423) B1354423
theorem B1904285 : Blo 666309 1904285 := bstep (se 3 (by rfl) ⟨357053, by rfl⟩ : syracuseStep 1904285 = 714107) B714107
theorem B1904627 : Blo 666309 1904627 := bstep (se 1 (by rfl) ⟨1428470, by rfl⟩ : syracuseStep 1904627 = 2856941) B2856941
theorem B5705747 : Blo 666309 5705747 := bstep (se 1 (by rfl) ⟨4279310, by rfl⟩ : syracuseStep 5705747 = 8558621) B8558621
theorem B6426809 : Blo 666309 6426809 := bstep (se 2 (by rfl) ⟨2410053, by rfl⟩ : syracuseStep 6426809 = 4820107) B4820107
theorem B9146729 : Blo 666309 9146729 := bstep (se 2 (by rfl) ⟨3430023, by rfl⟩ : syracuseStep 9146729 = 6860047) B6860047
theorem B2134775 : Blo 666309 2134775 := bstep (se 1 (by rfl) ⟨1601081, by rfl⟩ : syracuseStep 2134775 = 3202163) B3202163
theorem B1217963 : Blo 666309 1217963 := bstep (se 1 (by rfl) ⟨913472, by rfl⟩ : syracuseStep 1217963 = 1826945) B1826945
theorem B3216827 : Blo 666309 3216827 := bstep (se 1 (by rfl) ⟨2412620, by rfl⟩ : syracuseStep 3216827 = 4825241) B4825241
theorem B2135965 : Blo 666309 2135965 := bstep (se 3 (by rfl) ⟨400493, by rfl⟩ : syracuseStep 2135965 = 800987) B800987
theorem B3807431 : Blo 666309 3807431 := bstep (se 1 (by rfl) ⟨2855573, by rfl⟩ : syracuseStep 3807431 = 5711147) B5711147
theorem B6429233 : Blo 666309 6429233 := bstep (se 2 (by rfl) ⟨2410962, by rfl⟩ : syracuseStep 6429233 = 4821925) B4821925
theorem B1710953 : Blo 666309 1710953 := bstep (se 2 (by rfl) ⟨641607, by rfl⟩ : syracuseStep 1710953 = 1283215) B1283215
theorem B61905941 : Blo 666309 61905941 := bstep (se 6 (by rfl) ⟨1450920, by rfl⟩ : syracuseStep 61905941 = 2901841) B2901841
theorem B1907783 : Blo 666309 1907783 := bstep (se 1 (by rfl) ⟨1430837, by rfl⟩ : syracuseStep 1907783 = 2861675) B2861675
theorem B3382397 : Blo 666309 3382397 := bstep (se 3 (by rfl) ⟨634199, by rfl⟩ : syracuseStep 3382397 = 1268399) B1268399
theorem B2137337 : Blo 666309 2137337 := bstep (se 2 (by rfl) ⟨801501, by rfl⟩ : syracuseStep 2137337 = 1603003) B1603003
theorem B64953899 : Blo 666309 64953899 := bstep (se 1 (by rfl) ⟨48715424, by rfl⟩ : syracuseStep 64953899 = 97430849) B97430849
theorem B2531195 : Blo 666309 2531195 := bstep (se 1 (by rfl) ⟨1898396, by rfl⟩ : syracuseStep 2531195 = 3796793) B3796793
theorem B2531681 : Blo 666309 2531681 := bstep (se 2 (by rfl) ⟨949380, by rfl⟩ : syracuseStep 2531681 = 1898761) B1898761
theorem B3810665 : Blo 666309 3810665 := bstep (se 2 (by rfl) ⟨1428999, by rfl⟩ : syracuseStep 3810665 = 2857999) B2857999
theorem B4269419 : Blo 666309 4269419 := bstep (se 1 (by rfl) ⟨3202064, by rfl⟩ : syracuseStep 4269419 = 6404129) B6404129
theorem B2401751 : Blo 666309 2401751 := bstep (se 1 (by rfl) ⟨1801313, by rfl⟩ : syracuseStep 2401751 = 3602627) B3602627
theorem B9151987 : Blo 666309 9151987 := bstep (se 1 (by rfl) ⟨6863990, by rfl⟩ : syracuseStep 9151987 = 13727981) B13727981
theorem B9741817 : Blo 666309 9741817 := bstep (se 2 (by rfl) ⟨3653181, by rfl⟩ : syracuseStep 9741817 = 7306363) B7306363
theorem B3385091 : Blo 666309 3385091 := bstep (se 1 (by rfl) ⟨2538818, by rfl⟩ : syracuseStep 3385091 = 5077637) B5077637
theorem B3614561 : Blo 666309 3614561 := bstep (se 2 (by rfl) ⟨1355460, by rfl⟩ : syracuseStep 3614561 = 2710921) B2710921
theorem B2861075 : Blo 666309 2861075 := bstep (se 1 (by rfl) ⟨2145806, by rfl⟩ : syracuseStep 2861075 = 4291613) B4291613
theorem B1124543 : Blo 666309 1124543 := bstep (se 1 (by rfl) ⟨843407, by rfl⟩ : syracuseStep 1124543 = 1686815) B1686815
theorem B5220865 : Blo 666309 5220865 := bstep (se 2 (by rfl) ⟨1957824, by rfl⟩ : syracuseStep 5220865 = 3915649) B3915649
theorem B666459 : Blo 666309 666459 := bstep (se 1 (by rfl) ⟨499844, by rfl⟩ : syracuseStep 666459 = 999689) B999689
theorem B1125211 : Blo 666309 1125211 := bstep (se 1 (by rfl) ⟨843908, by rfl⟩ : syracuseStep 1125211 = 1687817) B1687817
theorem B666527 : Blo 666309 666527 := bstep (se 1 (by rfl) ⟨499895, by rfl⟩ : syracuseStep 666527 = 999791) B999791
theorem B1158047 : Blo 666309 1158047 := bstep (se 1 (by rfl) ⟨868535, by rfl⟩ : syracuseStep 1158047 = 1737071) B1737071
theorem B666671 : Blo 666309 666671 := bstep (se 1 (by rfl) ⟨500003, by rfl⟩ : syracuseStep 666671 = 1000007) B1000007
theorem B666695 : Blo 666309 666695 := bstep (se 1 (by rfl) ⟨500021, by rfl⟩ : syracuseStep 666695 = 1000043) B1000043
theorem B666847 : Blo 666309 666847 := bstep (se 1 (by rfl) ⟨500135, by rfl⟩ : syracuseStep 666847 = 1000271) B1000271
theorem B3419435 : Blo 666309 3419435 := bstep (se 1 (by rfl) ⟨2564576, by rfl⟩ : syracuseStep 3419435 = 5129153) B5129153
theorem B2567533 : Blo 666309 2567533 := bstep (se 3 (by rfl) ⟨481412, by rfl⟩ : syracuseStep 2567533 = 962825) B962825
theorem B667111 : Blo 666309 667111 := bstep (se 1 (by rfl) ⟨500333, by rfl⟩ : syracuseStep 667111 = 1000667) B1000667
theorem B667227 : Blo 666309 667227 := bstep (se 1 (by rfl) ⟨500420, by rfl⟩ : syracuseStep 667227 = 1000841) B1000841
theorem B1126183 : Blo 666309 1126183 := bstep (se 1 (by rfl) ⟨844637, by rfl⟩ : syracuseStep 1126183 = 1689275) B1689275
theorem B667463 : Blo 666309 667463 := bstep (se 1 (by rfl) ⟨500597, by rfl⟩ : syracuseStep 667463 = 1001195) B1001195
theorem B667615 : Blo 666309 667615 := bstep (se 1 (by rfl) ⟨500711, by rfl⟩ : syracuseStep 667615 = 1001423) B1001423
theorem B3387581 : Blo 666309 3387581 := bstep (se 3 (by rfl) ⟨635171, by rfl⟩ : syracuseStep 3387581 = 1270343) B1270343
theorem B4468931 : Blo 666309 4468931 := bstep (se 1 (by rfl) ⟨3351698, by rfl⟩ : syracuseStep 4468931 = 6703397) B6703397
theorem B667879 : Blo 666309 667879 := bstep (se 1 (by rfl) ⟨500909, by rfl⟩ : syracuseStep 667879 = 1001819) B1001819
theorem B668031 : Blo 666309 668031 := bstep (se 1 (by rfl) ⟨501023, by rfl⟩ : syracuseStep 668031 = 1002047) B1002047
theorem B668111 : Blo 666309 668111 := bstep (se 1 (by rfl) ⟨501083, by rfl⟩ : syracuseStep 668111 = 1002167) B1002167
theorem B4895201 : Blo 666309 4895201 := bstep (se 2 (by rfl) ⟨1835700, by rfl⟩ : syracuseStep 4895201 = 3671401) B3671401
theorem B668263 : Blo 666309 668263 := bstep (se 1 (by rfl) ⟨501197, by rfl⟩ : syracuseStep 668263 = 1002395) B1002395
theorem B2404979 : Blo 666309 2404979 := bstep (se 1 (by rfl) ⟨1803734, by rfl⟩ : syracuseStep 2404979 = 3607469) B3607469
theorem B5157665 : Blo 666309 5157665 := bstep (se 2 (by rfl) ⟨1934124, by rfl⟩ : syracuseStep 5157665 = 3868249) B3868249
theorem B1127209 : Blo 666309 1127209 := bstep (se 2 (by rfl) ⟨422703, by rfl⟩ : syracuseStep 1127209 = 845407) B845407
theorem B668527 : Blo 666309 668527 := bstep (se 1 (by rfl) ⟨501395, by rfl⟩ : syracuseStep 668527 = 1002791) B1002791
theorem B668583 : Blo 666309 668583 := bstep (se 1 (by rfl) ⟨501437, by rfl⟩ : syracuseStep 668583 = 1002875) B1002875
theorem B19313639 : Blo 666309 19313639 := bstep (se 1 (by rfl) ⟨14485229, by rfl⟩ : syracuseStep 19313639 = 28970459) B28970459
theorem B668667 : Blo 666309 668667 := bstep (se 1 (by rfl) ⟨501500, by rfl⟩ : syracuseStep 668667 = 1003001) B1003001
theorem B1127479 : Blo 666309 1127479 := bstep (se 1 (by rfl) ⟨845609, by rfl⟩ : syracuseStep 1127479 = 1691219) B1691219
theorem B668735 : Blo 666309 668735 := bstep (se 1 (by rfl) ⟨501551, by rfl⟩ : syracuseStep 668735 = 1003103) B1003103
theorem B668879 : Blo 666309 668879 := bstep (se 1 (by rfl) ⟨501659, by rfl⟩ : syracuseStep 668879 = 1003319) B1003319
theorem B4109629 : Blo 666309 4109629 := bstep (se 3 (by rfl) ⟨770555, by rfl⟩ : syracuseStep 4109629 = 1541111) B1541111
theorem B1357147 : Blo 666309 1357147 := bstep (se 1 (by rfl) ⟨1017860, by rfl⟩ : syracuseStep 1357147 = 2035721) B2035721
theorem B2536859 : Blo 666309 2536859 := bstep (se 1 (by rfl) ⟨1902644, by rfl⟩ : syracuseStep 2536859 = 3805289) B3805289
theorem B669083 : Blo 666309 669083 := bstep (se 1 (by rfl) ⟨501812, by rfl⟩ : syracuseStep 669083 = 1003625) B1003625
theorem B669295 : Blo 666309 669295 := bstep (se 1 (by rfl) ⟨501971, by rfl⟩ : syracuseStep 669295 = 1003943) B1003943
theorem B5060231 : Blo 666309 5060231 := bstep (se 1 (by rfl) ⟨3795173, by rfl⟩ : syracuseStep 5060231 = 7590347) B7590347
theorem B669351 : Blo 666309 669351 := bstep (se 1 (by rfl) ⟨502013, by rfl⟩ : syracuseStep 669351 = 1004027) B1004027
theorem B34748149 : Blo 666309 34748149 := bstep (se 5 (by rfl) ⟨1628819, by rfl⟩ : syracuseStep 34748149 = 3257639) B3257639
theorem B669435 : Blo 666309 669435 := bstep (se 1 (by rfl) ⟨502076, by rfl⟩ : syracuseStep 669435 = 1004153) B1004153
theorem B669471 : Blo 666309 669471 := bstep (se 1 (by rfl) ⟨502103, by rfl⟩ : syracuseStep 669471 = 1004207) B1004207
theorem B4568879 : Blo 666309 4568879 := bstep (se 1 (by rfl) ⟨3426659, by rfl⟩ : syracuseStep 4568879 = 6853319) B6853319
theorem B669503 : Blo 666309 669503 := bstep (se 1 (by rfl) ⟨502127, by rfl⟩ : syracuseStep 669503 = 1004255) B1004255
theorem B1128431 : Blo 666309 1128431 := bstep (se 1 (by rfl) ⟨846323, by rfl⟩ : syracuseStep 1128431 = 1692647) B1692647
theorem B669679 : Blo 666309 669679 := bstep (se 1 (by rfl) ⟨502259, by rfl⟩ : syracuseStep 669679 = 1004519) B1004519
theorem B9615419 : Blo 666309 9615419 := bstep (se 1 (by rfl) ⟨7211564, by rfl⟩ : syracuseStep 9615419 = 14423129) B14423129
theorem B669851 : Blo 666309 669851 := bstep (se 1 (by rfl) ⟨502388, by rfl⟩ : syracuseStep 669851 = 1004777) B1004777
theorem B669887 : Blo 666309 669887 := bstep (se 1 (by rfl) ⟨502415, by rfl⟩ : syracuseStep 669887 = 1004831) B1004831
theorem B669999 : Blo 666309 669999 := bstep (se 1 (by rfl) ⟨502499, by rfl⟩ : syracuseStep 669999 = 1004999) B1004999
theorem B35633459 : Blo 666309 35633459 := bstep (se 1 (by rfl) ⟨26725094, by rfl⟩ : syracuseStep 35633459 = 53450189) B53450189
theorem B2537801 : Blo 666309 2537801 := bstep (se 2 (by rfl) ⟨951675, by rfl⟩ : syracuseStep 2537801 = 1903351) B1903351
theorem B12204553 : Blo 666309 12204553 := bstep (se 2 (by rfl) ⟨4576707, by rfl⟩ : syracuseStep 12204553 = 9153415) B9153415
theorem B670235 : Blo 666309 670235 := bstep (se 1 (by rfl) ⟨502676, by rfl⟩ : syracuseStep 670235 = 1005353) B1005353
theorem B1128991 : Blo 666309 1128991 := bstep (se 1 (by rfl) ⟨846743, by rfl⟩ : syracuseStep 1128991 = 1693487) B1693487
theorem B670239 : Blo 666309 670239 := bstep (se 1 (by rfl) ⟨502679, by rfl⟩ : syracuseStep 670239 = 1005359) B1005359
theorem B29637413 : Blo 666309 29637413 := bstep (se 4 (by rfl) ⟨2778507, by rfl⟩ : syracuseStep 29637413 = 5557015) B5557015
theorem B1424233 : Blo 666309 1424233 := bstep (se 2 (by rfl) ⟨534087, by rfl⟩ : syracuseStep 1424233 = 1068175) B1068175
theorem B1129423 : Blo 666309 1129423 := bstep (se 1 (by rfl) ⟨847067, by rfl⟩ : syracuseStep 1129423 = 1694135) B1694135
theorem B4341023 : Blo 666309 4341023 := bstep (se 1 (by rfl) ⟨3255767, by rfl⟩ : syracuseStep 4341023 = 6511535) B6511535
theorem B3390983 : Blo 666309 3390983 := bstep (se 1 (by rfl) ⟨2543237, by rfl⟩ : syracuseStep 3390983 = 5086475) B5086475
theorem B1130159 : Blo 666309 1130159 := bstep (se 1 (by rfl) ⟨847619, by rfl⟩ : syracuseStep 1130159 = 1695239) B1695239
theorem B1130395 : Blo 666309 1130395 := bstep (se 1 (by rfl) ⟨847796, by rfl⟩ : syracuseStep 1130395 = 1695593) B1695593
theorem B1130807 : Blo 666309 1130807 := bstep (se 1 (by rfl) ⟨848105, by rfl⟩ : syracuseStep 1130807 = 1696211) B1696211
theorem B999887 : Blo 666309 999887 := bstep (se 1 (by rfl) ⟨749915, by rfl⟩ : syracuseStep 999887 = 1499831) B1499831
theorem B999929 : Blo 666309 999929 := bstep (se 2 (by rfl) ⟨374973, by rfl⟩ : syracuseStep 999929 = 749947) B749947
theorem B1000031 : Blo 666309 1000031 := bstep (se 1 (by rfl) ⟨750023, by rfl⟩ : syracuseStep 1000031 = 1500047) B1500047
theorem B2704175 : Blo 666309 2704175 := bstep (se 1 (by rfl) ⟨2028131, by rfl⟩ : syracuseStep 2704175 = 4056263) B4056263
theorem B1000511 : Blo 666309 1000511 := bstep (se 1 (by rfl) ⟨750383, by rfl⟩ : syracuseStep 1000511 = 1500767) B1500767
theorem B1000553 : Blo 666309 1000553 := bstep (se 2 (by rfl) ⟨375207, by rfl⟩ : syracuseStep 1000553 = 750415) B750415
theorem B1000655 : Blo 666309 1000655 := bstep (se 1 (by rfl) ⟨750491, by rfl⟩ : syracuseStep 1000655 = 1500983) B1500983
theorem B1000859 : Blo 666309 1000859 := bstep (se 1 (by rfl) ⟨750644, by rfl⟩ : syracuseStep 1000859 = 1501289) B1501289
theorem B8111549 : Blo 666309 8111549 := bstep (se 3 (by rfl) ⟨1520915, by rfl⟩ : syracuseStep 8111549 = 3041831) B3041831
theorem B1001081 : Blo 666309 1001081 := bstep (se 2 (by rfl) ⟨375405, by rfl⟩ : syracuseStep 1001081 = 750811) B750811
theorem B1001183 : Blo 666309 1001183 := bstep (se 1 (by rfl) ⟨750887, by rfl⟩ : syracuseStep 1001183 = 1501775) B1501775
theorem B1001279 : Blo 666309 1001279 := bstep (se 1 (by rfl) ⟨750959, by rfl⟩ : syracuseStep 1001279 = 1501919) B1501919
theorem B8570717 : Blo 666309 8570717 := bstep (se 3 (by rfl) ⟨1607009, by rfl⟩ : syracuseStep 8570717 = 3214019) B3214019
theorem B1001447 : Blo 666309 1001447 := bstep (se 1 (by rfl) ⟨751085, by rfl⟩ : syracuseStep 1001447 = 1502171) B1502171
theorem B1001465 : Blo 666309 1001465 := bstep (se 2 (by rfl) ⟨375549, by rfl⟩ : syracuseStep 1001465 = 751099) B751099
theorem B1001567 : Blo 666309 1001567 := bstep (se 1 (by rfl) ⟨751175, by rfl⟩ : syracuseStep 1001567 = 1502351) B1502351
theorem B1001627 : Blo 666309 1001627 := bstep (se 1 (by rfl) ⟨751220, by rfl⟩ : syracuseStep 1001627 = 1502441) B1502441
theorem B1001663 : Blo 666309 1001663 := bstep (se 1 (by rfl) ⟨751247, by rfl⟩ : syracuseStep 1001663 = 1502495) B1502495
theorem B1001705 : Blo 666309 1001705 := bstep (se 2 (by rfl) ⟨375639, by rfl⟩ : syracuseStep 1001705 = 751279) B751279
theorem B1002011 : Blo 666309 1002011 := bstep (se 1 (by rfl) ⟨751508, by rfl⟩ : syracuseStep 1002011 = 1503017) B1503017
theorem B1690217 : Blo 666309 1690217 := bstep (se 2 (by rfl) ⟨633831, by rfl⟩ : syracuseStep 1690217 = 1267663) B1267663
theorem B1002089 : Blo 666309 1002089 := bstep (se 2 (by rfl) ⟨375783, by rfl⟩ : syracuseStep 1002089 = 751567) B751567
theorem B8571743 : Blo 666309 8571743 := bstep (se 1 (by rfl) ⟨6428807, by rfl⟩ : syracuseStep 8571743 = 12857615) B12857615
theorem B904171 : Blo 666309 904171 := bstep (se 1 (by rfl) ⟨678128, by rfl⟩ : syracuseStep 904171 = 1356257) B1356257
theorem B1002617 : Blo 666309 1002617 := bstep (se 2 (by rfl) ⟨375981, by rfl⟩ : syracuseStep 1002617 = 751963) B751963
theorem B1002719 : Blo 666309 1002719 := bstep (se 1 (by rfl) ⟨752039, by rfl⟩ : syracuseStep 1002719 = 1504079) B1504079
theorem B1002761 : Blo 666309 1002761 := bstep (se 2 (by rfl) ⟨376035, by rfl⟩ : syracuseStep 1002761 = 752071) B752071
theorem B2542873 : Blo 666309 2542873 := bstep (se 2 (by rfl) ⟨953577, by rfl⟩ : syracuseStep 2542873 = 1907155) B1907155
theorem B5066063 : Blo 666309 5066063 := bstep (se 1 (by rfl) ⟨3799547, by rfl⟩ : syracuseStep 5066063 = 7599095) B7599095
theorem B1002863 : Blo 666309 1002863 := bstep (se 1 (by rfl) ⟨752147, by rfl⟩ : syracuseStep 1002863 = 1504295) B1504295
theorem B1953193 : Blo 666309 1953193 := bstep (se 2 (by rfl) ⟨732447, by rfl⟩ : syracuseStep 1953193 = 1464895) B1464895
theorem B1002983 : Blo 666309 1002983 := bstep (se 1 (by rfl) ⟨752237, by rfl⟩ : syracuseStep 1002983 = 1504475) B1504475
theorem B4279823 : Blo 666309 4279823 := bstep (se 1 (by rfl) ⟨3209867, by rfl⟩ : syracuseStep 4279823 = 6419735) B6419735
theorem B1003115 : Blo 666309 1003115 := bstep (se 1 (by rfl) ⟨752336, by rfl⟩ : syracuseStep 1003115 = 1504673) B1504673
theorem B27512459 : Blo 666309 27512459 := bstep (se 1 (by rfl) ⟨20634344, by rfl⟩ : syracuseStep 27512459 = 41268689) B41268689
theorem B1003241 : Blo 666309 1003241 := bstep (se 2 (by rfl) ⟨376215, by rfl⟩ : syracuseStep 1003241 = 752431) B752431
theorem B1691513 : Blo 666309 1691513 := bstep (se 2 (by rfl) ⟨634317, by rfl⟩ : syracuseStep 1691513 = 1268635) B1268635
theorem B1003385 : Blo 666309 1003385 := bstep (se 2 (by rfl) ⟨376269, by rfl⟩ : syracuseStep 1003385 = 752539) B752539
theorem B1003487 : Blo 666309 1003487 := bstep (se 1 (by rfl) ⟨752615, by rfl⟩ : syracuseStep 1003487 = 1505231) B1505231
theorem B2576569 : Blo 666309 2576569 := bstep (se 2 (by rfl) ⟨966213, by rfl⟩ : syracuseStep 2576569 = 1932427) B1932427
theorem B1003739 : Blo 666309 1003739 := bstep (se 1 (by rfl) ⟨752804, by rfl⟩ : syracuseStep 1003739 = 1505609) B1505609
theorem B1003751 : Blo 666309 1003751 := bstep (se 1 (by rfl) ⟨752813, by rfl⟩ : syracuseStep 1003751 = 1505627) B1505627
theorem B1003913 : Blo 666309 1003913 := bstep (se 2 (by rfl) ⟨376467, by rfl⟩ : syracuseStep 1003913 = 752935) B752935
theorem B3854765 : Blo 666309 3854765 := bstep (se 3 (by rfl) ⟨722768, by rfl⟩ : syracuseStep 3854765 = 1445537) B1445537
theorem B1004009 : Blo 666309 1004009 := bstep (se 2 (by rfl) ⟨376503, by rfl⟩ : syracuseStep 1004009 = 753007) B753007
theorem B1430111 : Blo 666309 1430111 := bstep (se 1 (by rfl) ⟨1072583, by rfl⟩ : syracuseStep 1430111 = 2145167) B2145167
theorem B1004135 : Blo 666309 1004135 := bstep (se 1 (by rfl) ⟨753101, by rfl⟩ : syracuseStep 1004135 = 1506203) B1506203
theorem B1004267 : Blo 666309 1004267 := bstep (se 1 (by rfl) ⟨753200, by rfl⟩ : syracuseStep 1004267 = 1506401) B1506401
theorem B1004297 : Blo 666309 1004297 := bstep (se 2 (by rfl) ⟨376611, by rfl⟩ : syracuseStep 1004297 = 753223) B753223
theorem B1004399 : Blo 666309 1004399 := bstep (se 1 (by rfl) ⟨753299, by rfl⟩ : syracuseStep 1004399 = 1506599) B1506599
theorem B2544635 : Blo 666309 2544635 := bstep (se 1 (by rfl) ⟨1908476, by rfl⟩ : syracuseStep 2544635 = 3816953) B3816953
theorem B2249801 : Blo 666309 2249801 := bstep (se 2 (by rfl) ⟨843675, by rfl⟩ : syracuseStep 2249801 = 1687351) B1687351
theorem B1004651 : Blo 666309 1004651 := bstep (se 1 (by rfl) ⟨753488, by rfl⟩ : syracuseStep 1004651 = 1506977) B1506977
theorem B11424887 : Blo 666309 11424887 := bstep (se 1 (by rfl) ⟨8568665, by rfl⟩ : syracuseStep 11424887 = 17137331) B17137331
theorem B1004891 : Blo 666309 1004891 := bstep (se 1 (by rfl) ⟨753668, by rfl⟩ : syracuseStep 1004891 = 1507337) B1507337
theorem B1005167 : Blo 666309 1005167 := bstep (se 1 (by rfl) ⟨753875, by rfl⟩ : syracuseStep 1005167 = 1507751) B1507751
theorem B2283179 : Blo 666309 2283179 := bstep (se 1 (by rfl) ⟨1712384, by rfl⟩ : syracuseStep 2283179 = 3424769) B3424769
theorem B1005239 : Blo 666309 1005239 := bstep (se 1 (by rfl) ⟨753929, by rfl⟩ : syracuseStep 1005239 = 1507859) B1507859
theorem B1005275 : Blo 666309 1005275 := bstep (se 1 (by rfl) ⟨753956, by rfl⟩ : syracuseStep 1005275 = 1507913) B1507913
theorem B1005449 : Blo 666309 1005449 := bstep (se 2 (by rfl) ⟨377043, by rfl⟩ : syracuseStep 1005449 = 754087) B754087
theorem B2414551 : Blo 666309 2414551 := bstep (se 1 (by rfl) ⟨1810913, by rfl⟩ : syracuseStep 2414551 = 3621827) B3621827
theorem B1267807 : Blo 666309 1267807 := bstep (se 1 (by rfl) ⟨950855, by rfl⟩ : syracuseStep 1267807 = 1901711) B1901711
theorem B1693993 : Blo 666309 1693993 := bstep (se 2 (by rfl) ⟨635247, by rfl⟩ : syracuseStep 1693993 = 1270495) B1270495
theorem B2709883 : Blo 666309 2709883 := bstep (se 1 (by rfl) ⟨2032412, by rfl⟩ : syracuseStep 2709883 = 4064825) B4064825
theorem B2251421 : Blo 666309 2251421 := bstep (se 3 (by rfl) ⟨422141, by rfl⟩ : syracuseStep 2251421 = 844283) B844283
theorem B5725019 : Blo 666309 5725019 := bstep (se 1 (by rfl) ⟨4293764, by rfl⟩ : syracuseStep 5725019 = 8587529) B8587529
theorem B14474159 : Blo 666309 14474159 := bstep (se 1 (by rfl) ⟨10855619, by rfl⟩ : syracuseStep 14474159 = 21711239) B21711239
theorem B2251745 : Blo 666309 2251745 := bstep (se 2 (by rfl) ⟨844404, by rfl⟩ : syracuseStep 2251745 = 1688809) B1688809
theorem B14605379 : Blo 666309 14605379 := bstep (se 1 (by rfl) ⟨10954034, by rfl⟩ : syracuseStep 14605379 = 21908069) B21908069
theorem B2251961 : Blo 666309 2251961 := bstep (se 2 (by rfl) ⟨844485, by rfl⟩ : syracuseStep 2251961 = 1688971) B1688971
theorem B1924519 : Blo 666309 1924519 := bstep (se 1 (by rfl) ⟨1443389, by rfl⟩ : syracuseStep 1924519 = 2886779) B2886779
theorem B1073339 : Blo 666309 1073339 := bstep (se 1 (by rfl) ⟨805004, by rfl⟩ : syracuseStep 1073339 = 1610009) B1610009
theorem B19292417 : Blo 666309 19292417 := bstep (se 2 (by rfl) ⟨7234656, by rfl⟩ : syracuseStep 19292417 = 14469313) B14469313
theorem B1499489 : Blo 666309 1499489 := bstep (se 2 (by rfl) ⟨562308, by rfl⟩ : syracuseStep 1499489 = 1124617) B1124617
theorem B2285921 : Blo 666309 2285921 := bstep (se 2 (by rfl) ⟨857220, by rfl⟩ : syracuseStep 2285921 = 1714441) B1714441
theorem B69394801 : Blo 666309 69394801 := bstep (se 2 (by rfl) ⟨26023050, by rfl⟩ : syracuseStep 69394801 = 52046101) B52046101
theorem B1499579 : Blo 666309 1499579 := bstep (se 1 (by rfl) ⟨1124684, by rfl⟩ : syracuseStep 1499579 = 2249369) B2249369
theorem B713167 : Blo 666309 713167 := bstep (se 1 (by rfl) ⟨534875, by rfl⟩ : syracuseStep 713167 = 1069751) B1069751
theorem B4285001 : Blo 666309 4285001 := bstep (se 2 (by rfl) ⟨1606875, by rfl⟩ : syracuseStep 4285001 = 3213751) B3213751
theorem B2253419 : Blo 666309 2253419 := bstep (se 1 (by rfl) ⟨1690064, by rfl⟩ : syracuseStep 2253419 = 3380129) B3380129
theorem B17621651 : Blo 666309 17621651 := bstep (se 1 (by rfl) ⟨13216238, by rfl⟩ : syracuseStep 17621651 = 26432477) B26432477
theorem B2286355 : Blo 666309 2286355 := bstep (se 1 (by rfl) ⟨1714766, by rfl⟩ : syracuseStep 2286355 = 3429533) B3429533
theorem B27779993 : Blo 666309 27779993 := bstep (se 2 (by rfl) ⟨10417497, by rfl⟩ : syracuseStep 27779993 = 20834995) B20834995
theorem B2254013 : Blo 666309 2254013 := bstep (se 3 (by rfl) ⟨422627, by rfl⟩ : syracuseStep 2254013 = 845255) B845255
theorem B1500587 : Blo 666309 1500587 := bstep (se 1 (by rfl) ⟨1125440, by rfl⟩ : syracuseStep 1500587 = 2250881) B2250881
theorem B3204623 : Blo 666309 3204623 := bstep (se 1 (by rfl) ⟨2403467, by rfl⟩ : syracuseStep 3204623 = 4806935) B4806935
theorem B3204775 : Blo 666309 3204775 := bstep (se 1 (by rfl) ⟨2403581, by rfl⟩ : syracuseStep 3204775 = 4807163) B4807163
theorem B1500839 : Blo 666309 1500839 := bstep (se 1 (by rfl) ⟨1125629, by rfl⟩ : syracuseStep 1500839 = 2251259) B2251259
theorem B1501127 : Blo 666309 1501127 := bstep (se 1 (by rfl) ⟨1125845, by rfl⟩ : syracuseStep 1501127 = 2251691) B2251691
theorem B7596179 : Blo 666309 7596179 := bstep (se 1 (by rfl) ⟨5697134, by rfl⟩ : syracuseStep 7596179 = 11394269) B11394269
theorem B2255039 : Blo 666309 2255039 := bstep (se 1 (by rfl) ⟨1691279, by rfl⟩ : syracuseStep 2255039 = 3382559) B3382559
theorem B1271999 : Blo 666309 1271999 := bstep (se 1 (by rfl) ⟨953999, by rfl⟩ : syracuseStep 1271999 = 1907999) B1907999
theorem B1501433 : Blo 666309 1501433 := bstep (se 2 (by rfl) ⟨563037, by rfl⟩ : syracuseStep 1501433 = 1126075) B1126075
theorem B1501487 : Blo 666309 1501487 := bstep (se 1 (by rfl) ⟨1126115, by rfl⟩ : syracuseStep 1501487 = 2252231) B2252231
theorem B1501703 : Blo 666309 1501703 := bstep (se 1 (by rfl) ⟨1126277, by rfl⟩ : syracuseStep 1501703 = 2252555) B2252555
theorem B1501883 : Blo 666309 1501883 := bstep (se 1 (by rfl) ⟨1126412, by rfl⟩ : syracuseStep 1501883 = 2252825) B2252825
theorem B8579843 : Blo 666309 8579843 := bstep (se 1 (by rfl) ⟨6434882, by rfl⟩ : syracuseStep 8579843 = 12869765) B12869765
theorem B3795767 : Blo 666309 3795767 := bstep (se 1 (by rfl) ⟨2846825, by rfl⟩ : syracuseStep 3795767 = 5693651) B5693651
theorem B2092007 : Blo 666309 2092007 := bstep (se 1 (by rfl) ⟨1569005, by rfl⟩ : syracuseStep 2092007 = 3138011) B3138011
theorem B3796267 : Blo 666309 3796267 := bstep (se 1 (by rfl) ⟨2847200, by rfl⟩ : syracuseStep 3796267 = 5694401) B5694401
theorem B1502711 : Blo 666309 1502711 := bstep (se 1 (by rfl) ⟨1127033, by rfl⟩ : syracuseStep 1502711 = 2254067) B2254067
theorem B1502783 : Blo 666309 1502783 := bstep (se 1 (by rfl) ⟨1127087, by rfl⟩ : syracuseStep 1502783 = 2254175) B2254175
theorem B2256659 : Blo 666309 2256659 := bstep (se 1 (by rfl) ⟨1692494, by rfl⟩ : syracuseStep 2256659 = 3384989) B3384989
theorem B1503737 : Blo 666309 1503737 := bstep (se 2 (by rfl) ⟨563901, by rfl⟩ : syracuseStep 1503737 = 1127803) B1127803
theorem B1503827 : Blo 666309 1503827 := bstep (se 1 (by rfl) ⟨1127870, by rfl⟩ : syracuseStep 1503827 = 2255741) B2255741
theorem B1143391 : Blo 666309 1143391 := bstep (se 1 (by rfl) ⟨857543, by rfl⟩ : syracuseStep 1143391 = 1715087) B1715087
theorem B2257523 : Blo 666309 2257523 := bstep (se 1 (by rfl) ⟨1693142, by rfl⟩ : syracuseStep 2257523 = 3386285) B3386285
theorem B7205597 : Blo 666309 7205597 := bstep (se 3 (by rfl) ⟨1351049, by rfl⟩ : syracuseStep 7205597 = 2702099) B2702099
theorem B3797725 : Blo 666309 3797725 := bstep (se 3 (by rfl) ⟨712073, by rfl⟩ : syracuseStep 3797725 = 1424147) B1424147
theorem B1504007 : Blo 666309 1504007 := bstep (se 1 (by rfl) ⟨1128005, by rfl⟩ : syracuseStep 1504007 = 2256011) B2256011
theorem B2257793 : Blo 666309 2257793 := bstep (se 2 (by rfl) ⟨846672, by rfl⟩ : syracuseStep 2257793 = 1693345) B1693345
theorem B6354227 : Blo 666309 6354227 := bstep (se 1 (by rfl) ⟨4765670, by rfl⟩ : syracuseStep 6354227 = 9531341) B9531341
theorem B2258603 : Blo 666309 2258603 := bstep (se 1 (by rfl) ⟨1693952, by rfl⟩ : syracuseStep 2258603 = 3387905) B3387905
theorem B751423 : Blo 666309 751423 := bstep (se 1 (by rfl) ⟨563567, by rfl⟩ : syracuseStep 751423 = 1127135) B1127135
theorem B1505087 : Blo 666309 1505087 := bstep (se 1 (by rfl) ⟨1128815, by rfl⟩ : syracuseStep 1505087 = 2257631) B2257631
theorem B2258927 : Blo 666309 2258927 := bstep (se 1 (by rfl) ⟨1694195, by rfl⟩ : syracuseStep 2258927 = 3388391) B3388391
theorem B1898579 : Blo 666309 1898579 := bstep (se 1 (by rfl) ⟨1423934, by rfl⟩ : syracuseStep 1898579 = 2847869) B2847869
theorem B751711 : Blo 666309 751711 := bstep (se 1 (by rfl) ⟨563783, by rfl⟩ : syracuseStep 751711 = 1127567) B1127567
theorem B1505375 : Blo 666309 1505375 := bstep (se 1 (by rfl) ⟨1129031, by rfl⟩ : syracuseStep 1505375 = 2258063) B2258063
theorem B3799183 : Blo 666309 3799183 := bstep (se 1 (by rfl) ⟨2849387, by rfl⟩ : syracuseStep 3799183 = 5698775) B5698775
theorem B2259143 : Blo 666309 2259143 := bstep (se 1 (by rfl) ⟨1694357, by rfl⟩ : syracuseStep 2259143 = 3388715) B3388715
theorem B1604233 : Blo 666309 1604233 := bstep (se 2 (by rfl) ⟨601587, by rfl⟩ : syracuseStep 1604233 = 1203175) B1203175
theorem B3603143 : Blo 666309 3603143 := bstep (se 1 (by rfl) ⟨2702357, by rfl⟩ : syracuseStep 3603143 = 5404715) B5404715
theorem B2259791 : Blo 666309 2259791 := bstep (se 1 (by rfl) ⟨1694843, by rfl⟩ : syracuseStep 2259791 = 3389687) B3389687
theorem B1506131 : Blo 666309 1506131 := bstep (se 1 (by rfl) ⟨1129598, by rfl⟩ : syracuseStep 1506131 = 2259197) B2259197
theorem B3603365 : Blo 666309 3603365 := bstep (se 4 (by rfl) ⟨337815, by rfl⟩ : syracuseStep 3603365 = 675631) B675631
theorem B3210329 : Blo 666309 3210329 := bstep (se 2 (by rfl) ⟨1203873, by rfl⟩ : syracuseStep 3210329 = 2407747) B2407747
theorem B2260115 : Blo 666309 2260115 := bstep (se 1 (by rfl) ⟨1695086, by rfl⟩ : syracuseStep 2260115 = 3390173) B3390173
theorem B752863 : Blo 666309 752863 := bstep (se 1 (by rfl) ⟨564647, by rfl⟩ : syracuseStep 752863 = 1129295) B1129295
theorem B1146079 : Blo 666309 1146079 := bstep (se 1 (by rfl) ⟨859559, by rfl⟩ : syracuseStep 1146079 = 1719119) B1719119
theorem B1506671 : Blo 666309 1506671 := bstep (se 1 (by rfl) ⟨1130003, by rfl⟩ : syracuseStep 1506671 = 2260007) B2260007
theorem B2260385 : Blo 666309 2260385 := bstep (se 2 (by rfl) ⟨847644, by rfl⟩ : syracuseStep 2260385 = 1695289) B1695289
theorem B1506959 : Blo 666309 1506959 := bstep (se 1 (by rfl) ⟨1130219, by rfl⟩ : syracuseStep 1506959 = 2260439) B2260439
theorem B8584865 : Blo 666309 8584865 := bstep (se 2 (by rfl) ⟨3219324, by rfl⟩ : syracuseStep 8584865 = 6438649) B6438649
theorem B1900219 : Blo 666309 1900219 := bstep (se 1 (by rfl) ⟨1425164, by rfl⟩ : syracuseStep 1900219 = 2850329) B2850329
theorem B1507049 : Blo 666309 1507049 := bstep (se 2 (by rfl) ⟨565143, by rfl⟩ : syracuseStep 1507049 = 1130287) B1130287
theorem B2850551 : Blo 666309 2850551 := bstep (se 1 (by rfl) ⟨2137913, by rfl⟩ : syracuseStep 2850551 = 4275827) B4275827
theorem B2260925 : Blo 666309 2260925 := bstep (se 3 (by rfl) ⟨423923, by rfl⟩ : syracuseStep 2260925 = 847847) B847847
theorem B753871 : Blo 666309 753871 := bstep (se 1 (by rfl) ⟨565403, by rfl⟩ : syracuseStep 753871 = 1130807) B1130807
theorem B1802783 : Blo 666309 1802783 := bstep (se 1 (by rfl) ⟨1352087, by rfl⟩ : syracuseStep 1802783 = 2704175) B2704175
theorem B3048473 : Blo 666309 3048473 := bstep (se 2 (by rfl) ⟨1143177, by rfl⟩ : syracuseStep 3048473 = 2286355) B2286355
theorem B3212635 : Blo 666309 3212635 := bstep (se 1 (by rfl) ⟨2409476, by rfl⟩ : syracuseStep 3212635 = 4818953) B4818953
theorem B3377375 : Blo 666309 3377375 := bstep (se 1 (by rfl) ⟨2533031, by rfl⟩ : syracuseStep 3377375 = 5066063) B5066063
theorem B2853215 : Blo 666309 2853215 := bstep (se 1 (by rfl) ⟨2139911, by rfl⟩ : syracuseStep 2853215 = 4279823) B4279823
theorem B3213695 : Blo 666309 3213695 := bstep (se 1 (by rfl) ⟨2410271, by rfl⟩ : syracuseStep 3213695 = 4820543) B4820543
theorem B3803557 : Blo 666309 3803557 := bstep (se 4 (by rfl) ⟨356583, by rfl⟩ : syracuseStep 3803557 = 713167) B713167
theorem B3803831 : Blo 666309 3803831 := bstep (se 1 (by rfl) ⟨2852873, by rfl⟩ : syracuseStep 3803831 = 5705747) B5705747
theorem B953407 : Blo 666309 953407 := bstep (se 1 (by rfl) ⟨715055, by rfl⟩ : syracuseStep 953407 = 1430111) B1430111
theorem B3247901 : Blo 666309 3247901 := bstep (se 3 (by rfl) ⟨608981, by rfl⟩ : syracuseStep 3247901 = 1217963) B1217963
theorem B21630797 : Blo 666309 21630797 := bstep (se 3 (by rfl) ⟨4055774, by rfl⟩ : syracuseStep 21630797 = 8111549) B8111549
theorem B9736919 : Blo 666309 9736919 := bstep (se 1 (by rfl) ⟨7302689, by rfl⟩ : syracuseStep 9736919 = 14605379) B14605379
theorem B2856667 : Blo 666309 2856667 := bstep (se 1 (by rfl) ⟨2142500, by rfl⟩ : syracuseStep 2856667 = 4285001) B4285001
theorem B18519995 : Blo 666309 18519995 := bstep (se 1 (by rfl) ⟨13889996, by rfl⟩ : syracuseStep 18519995 = 27779993) B27779993
theorem B2136415 : Blo 666309 2136415 := bstep (se 1 (by rfl) ⟨1602311, by rfl⟩ : syracuseStep 2136415 = 3204623) B3204623
theorem B1907383 : Blo 666309 1907383 := bstep (se 1 (by rfl) ⟨1430537, by rfl⟩ : syracuseStep 1907383 = 2861075) B2861075
theorem B5479505 : Blo 666309 5479505 := bstep (se 2 (by rfl) ⟨2054814, by rfl⟩ : syracuseStep 5479505 = 4109629) B4109629
theorem B24353909 : Blo 666309 24353909 := bstep (se 5 (by rfl) ⟨1141589, by rfl⟩ : syracuseStep 24353909 = 2283179) B2283179
theorem B1809529 : Blo 666309 1809529 := bstep (se 2 (by rfl) ⟨678573, by rfl⟩ : syracuseStep 1809529 = 1357147) B1357147
theorem B9608381 : Blo 666309 9608381 := bstep (se 3 (by rfl) ⟨1801571, by rfl⟩ : syracuseStep 9608381 = 3603143) B3603143
theorem B2530511 : Blo 666309 2530511 := bstep (se 1 (by rfl) ⟨1897883, by rfl⟩ : syracuseStep 2530511 = 3795767) B3795767
theorem B3219401 : Blo 666309 3219401 := bstep (se 2 (by rfl) ⟨1207275, by rfl⟩ : syracuseStep 3219401 = 2414551) B2414551
theorem B3613177 : Blo 666309 3613177 := bstep (se 2 (by rfl) ⟨1354941, by rfl⟩ : syracuseStep 3613177 = 2709883) B2709883
theorem B9118493 : Blo 666309 9118493 := bstep (se 3 (by rfl) ⟨1709717, by rfl⟩ : syracuseStep 9118493 = 3419435) B3419435
theorem B2138977 : Blo 666309 2138977 := bstep (se 2 (by rfl) ⟨802116, by rfl⟩ : syracuseStep 2138977 = 1604233) B1604233
theorem B4236151 : Blo 666309 4236151 := bstep (se 1 (by rfl) ⟨3177113, by rfl⟩ : syracuseStep 4236151 = 6354227) B6354227
theorem B2566025 : Blo 666309 2566025 := bstep (se 2 (by rfl) ⟨962259, by rfl⟩ : syracuseStep 2566025 = 1924519) B1924519
theorem B2402243 : Blo 666309 2402243 := bstep (se 1 (by rfl) ⟨1801682, by rfl⟩ : syracuseStep 2402243 = 3603365) B3603365
theorem B2140219 : Blo 666309 2140219 := bstep (se 1 (by rfl) ⟨1605164, by rfl⟩ : syracuseStep 2140219 = 3210329) B3210329
theorem B2894015 : Blo 666309 2894015 := bstep (se 1 (by rfl) ⟨2170511, by rfl⟩ : syracuseStep 2894015 = 4341023) B4341023
theorem B2533625 : Blo 666309 2533625 := bstep (se 2 (by rfl) ⟨950109, by rfl⟩ : syracuseStep 2533625 = 1900219) B1900219
theorem B2534111 : Blo 666309 2534111 := bstep (se 1 (by rfl) ⟨1900583, by rfl⟩ : syracuseStep 2534111 = 3801167) B3801167
theorem B666591 : Blo 666309 666591 := bstep (se 1 (by rfl) ⟨499943, by rfl⟩ : syracuseStep 666591 = 999887) B999887
theorem B666619 : Blo 666309 666619 := bstep (se 1 (by rfl) ⟨499964, by rfl⟩ : syracuseStep 666619 = 999929) B999929
theorem B8563745 : Blo 666309 8563745 := bstep (se 2 (by rfl) ⟨3211404, by rfl⟩ : syracuseStep 8563745 = 6422809) B6422809
theorem B666687 : Blo 666309 666687 := bstep (se 1 (by rfl) ⟨500015, by rfl⟩ : syracuseStep 666687 = 1000031) B1000031
theorem B667007 : Blo 666309 667007 := bstep (se 1 (by rfl) ⟨500255, by rfl⟩ : syracuseStep 667007 = 1000511) B1000511
theorem B667035 : Blo 666309 667035 := bstep (se 1 (by rfl) ⟨500276, by rfl⟩ : syracuseStep 667035 = 1000553) B1000553
theorem B1355219 : Blo 666309 1355219 := bstep (se 1 (by rfl) ⟨1016414, by rfl⟩ : syracuseStep 1355219 = 2032829) B2032829
theorem B667103 : Blo 666309 667103 := bstep (se 1 (by rfl) ⟨500327, by rfl⟩ : syracuseStep 667103 = 1000655) B1000655
theorem B667239 : Blo 666309 667239 := bstep (se 1 (by rfl) ⟨500429, by rfl⟩ : syracuseStep 667239 = 1000859) B1000859
theorem B24391277 : Blo 666309 24391277 := bstep (se 3 (by rfl) ⟨4573364, by rfl⟩ : syracuseStep 24391277 = 9146729) B9146729
theorem B667387 : Blo 666309 667387 := bstep (se 1 (by rfl) ⟨500540, by rfl⟩ : syracuseStep 667387 = 1001081) B1001081
theorem B667455 : Blo 666309 667455 := bstep (se 1 (by rfl) ⟨500591, by rfl⟩ : syracuseStep 667455 = 1001183) B1001183
theorem B667519 : Blo 666309 667519 := bstep (se 1 (by rfl) ⟨500639, by rfl⟩ : syracuseStep 667519 = 1001279) B1001279
theorem B5713811 : Blo 666309 5713811 := bstep (se 1 (by rfl) ⟨4285358, by rfl⟩ : syracuseStep 5713811 = 8570717) B8570717
theorem B13053869 : Blo 666309 13053869 := bstep (se 3 (by rfl) ⟨2447600, by rfl⟩ : syracuseStep 13053869 = 4895201) B4895201
theorem B667631 : Blo 666309 667631 := bstep (se 1 (by rfl) ⟨500723, by rfl⟩ : syracuseStep 667631 = 1001447) B1001447
theorem B667643 : Blo 666309 667643 := bstep (se 1 (by rfl) ⟨500732, by rfl⟩ : syracuseStep 667643 = 1001465) B1001465
theorem B667711 : Blo 666309 667711 := bstep (se 1 (by rfl) ⟨500783, by rfl⟩ : syracuseStep 667711 = 1001567) B1001567
theorem B667751 : Blo 666309 667751 := bstep (se 1 (by rfl) ⟨500813, by rfl⟩ : syracuseStep 667751 = 1001627) B1001627
theorem B667775 : Blo 666309 667775 := bstep (se 1 (by rfl) ⟨500831, by rfl⟩ : syracuseStep 667775 = 1001663) B1001663
theorem B667803 : Blo 666309 667803 := bstep (se 1 (by rfl) ⟨500852, by rfl⟩ : syracuseStep 667803 = 1001705) B1001705
theorem B668007 : Blo 666309 668007 := bstep (se 1 (by rfl) ⟨501005, by rfl⟩ : syracuseStep 668007 = 1002011) B1002011
theorem B1126811 : Blo 666309 1126811 := bstep (se 1 (by rfl) ⟨845108, by rfl⟩ : syracuseStep 1126811 = 1690217) B1690217
theorem B668059 : Blo 666309 668059 := bstep (se 1 (by rfl) ⟨501044, by rfl⟩ : syracuseStep 668059 = 1002089) B1002089
theorem B5714495 : Blo 666309 5714495 := bstep (se 1 (by rfl) ⟨4285871, by rfl⟩ : syracuseStep 5714495 = 8571743) B8571743
theorem B12202649 : Blo 666309 12202649 := bstep (se 2 (by rfl) ⟨4575993, by rfl⟩ : syracuseStep 12202649 = 9151987) B9151987
theorem B12989089 : Blo 666309 12989089 := bstep (se 2 (by rfl) ⟨4870908, by rfl⟩ : syracuseStep 12989089 = 9741817) B9741817
theorem B668411 : Blo 666309 668411 := bstep (se 1 (by rfl) ⟨501308, by rfl⟩ : syracuseStep 668411 = 1002617) B1002617
theorem B668479 : Blo 666309 668479 := bstep (se 1 (by rfl) ⟨501359, by rfl⟩ : syracuseStep 668479 = 1002719) B1002719
theorem B668507 : Blo 666309 668507 := bstep (se 1 (by rfl) ⟨501380, by rfl⟩ : syracuseStep 668507 = 1002761) B1002761
theorem B4273033 : Blo 666309 4273033 := bstep (se 2 (by rfl) ⟨1602387, by rfl⟩ : syracuseStep 4273033 = 3204775) B3204775
theorem B668575 : Blo 666309 668575 := bstep (se 1 (by rfl) ⟨501431, by rfl⟩ : syracuseStep 668575 = 1002863) B1002863
theorem B668655 : Blo 666309 668655 := bstep (se 1 (by rfl) ⟨501491, by rfl⟩ : syracuseStep 668655 = 1002983) B1002983
theorem B668743 : Blo 666309 668743 := bstep (se 1 (by rfl) ⟨501557, by rfl⟩ : syracuseStep 668743 = 1003115) B1003115
theorem B668827 : Blo 666309 668827 := bstep (se 1 (by rfl) ⟨501620, by rfl⟩ : syracuseStep 668827 = 1003241) B1003241
theorem B1127675 : Blo 666309 1127675 := bstep (se 1 (by rfl) ⟨845756, by rfl⟩ : syracuseStep 1127675 = 1691513) B1691513
theorem B668923 : Blo 666309 668923 := bstep (se 1 (by rfl) ⟨501692, by rfl⟩ : syracuseStep 668923 = 1003385) B1003385
theorem B668991 : Blo 666309 668991 := bstep (se 1 (by rfl) ⟨501743, by rfl⟩ : syracuseStep 668991 = 1003487) B1003487
theorem B669159 : Blo 666309 669159 := bstep (se 1 (by rfl) ⟨501869, by rfl⟩ : syracuseStep 669159 = 1003739) B1003739
theorem B669167 : Blo 666309 669167 := bstep (se 1 (by rfl) ⟨501875, by rfl⟩ : syracuseStep 669167 = 1003751) B1003751
theorem B2930201 : Blo 666309 2930201 := bstep (se 2 (by rfl) ⟨1098825, by rfl⟩ : syracuseStep 2930201 = 2197651) B2197651
theorem B669275 : Blo 666309 669275 := bstep (se 1 (by rfl) ⟨501956, by rfl⟩ : syracuseStep 669275 = 1003913) B1003913
theorem B2569843 : Blo 666309 2569843 := bstep (se 1 (by rfl) ⟨1927382, by rfl⟩ : syracuseStep 2569843 = 3854765) B3854765
theorem B669339 : Blo 666309 669339 := bstep (se 1 (by rfl) ⟨502004, by rfl⟩ : syracuseStep 669339 = 1004009) B1004009
theorem B669423 : Blo 666309 669423 := bstep (se 1 (by rfl) ⟨502067, by rfl⟩ : syracuseStep 669423 = 1004135) B1004135
theorem B669511 : Blo 666309 669511 := bstep (se 1 (by rfl) ⟨502133, by rfl⟩ : syracuseStep 669511 = 1004267) B1004267
theorem B1423183 : Blo 666309 1423183 := bstep (se 1 (by rfl) ⟨1067387, by rfl⟩ : syracuseStep 1423183 = 2134775) B2134775
theorem B669531 : Blo 666309 669531 := bstep (se 1 (by rfl) ⟨502148, by rfl⟩ : syracuseStep 669531 = 1004297) B1004297
theorem B2537345 : Blo 666309 2537345 := bstep (se 2 (by rfl) ⟨951504, by rfl⟩ : syracuseStep 2537345 = 1903009) B1903009
theorem B669599 : Blo 666309 669599 := bstep (se 1 (by rfl) ⟨502199, by rfl⟩ : syracuseStep 669599 = 1004399) B1004399
theorem B6961153 : Blo 666309 6961153 := bstep (se 2 (by rfl) ⟨2610432, by rfl⟩ : syracuseStep 6961153 = 5220865) B5220865
theorem B2537513 : Blo 666309 2537513 := bstep (se 2 (by rfl) ⟨951567, by rfl⟩ : syracuseStep 2537513 = 1903135) B1903135
theorem B669767 : Blo 666309 669767 := bstep (se 1 (by rfl) ⟨502325, by rfl⟩ : syracuseStep 669767 = 1004651) B1004651
theorem B7616591 : Blo 666309 7616591 := bstep (se 1 (by rfl) ⟨5712443, by rfl⟩ : syracuseStep 7616591 = 11424887) B11424887
theorem B669927 : Blo 666309 669927 := bstep (se 1 (by rfl) ⟨502445, by rfl⟩ : syracuseStep 669927 = 1004891) B1004891
theorem B2144551 : Blo 666309 2144551 := bstep (se 1 (by rfl) ⟨1608413, by rfl⟩ : syracuseStep 2144551 = 3216827) B3216827
theorem B670111 : Blo 666309 670111 := bstep (se 1 (by rfl) ⟨502583, by rfl⟩ : syracuseStep 670111 = 1005167) B1005167
theorem B670159 : Blo 666309 670159 := bstep (se 1 (by rfl) ⟨502619, by rfl⟩ : syracuseStep 670159 = 1005239) B1005239
theorem B670183 : Blo 666309 670183 := bstep (se 1 (by rfl) ⟨502637, by rfl⟩ : syracuseStep 670183 = 1005275) B1005275
theorem B670299 : Blo 666309 670299 := bstep (se 1 (by rfl) ⟨502724, by rfl⟩ : syracuseStep 670299 = 1005449) B1005449
theorem B2538287 : Blo 666309 2538287 := bstep (se 1 (by rfl) ⟨1903715, by rfl⟩ : syracuseStep 2538287 = 3807431) B3807431
theorem B3390497 : Blo 666309 3390497 := bstep (se 2 (by rfl) ⟨1271436, by rfl⟩ : syracuseStep 3390497 = 2542873) B2542873
theorem B5061689 : Blo 666309 5061689 := bstep (se 2 (by rfl) ⟨1898133, by rfl⟩ : syracuseStep 5061689 = 3796267) B3796267
theorem B3423377 : Blo 666309 3423377 := bstep (se 2 (by rfl) ⟨1283766, by rfl⟩ : syracuseStep 3423377 = 2567533) B2567533
theorem B2604257 : Blo 666309 2604257 := bstep (se 2 (by rfl) ⟨976596, by rfl⟩ : syracuseStep 2604257 = 1953193) B1953193
theorem B3816679 : Blo 666309 3816679 := bstep (se 1 (by rfl) ⟨2862509, by rfl⟩ : syracuseStep 3816679 = 5725019) B5725019
theorem B9649439 : Blo 666309 9649439 := bstep (se 1 (by rfl) ⟨7237079, by rfl⟩ : syracuseStep 9649439 = 14474159) B14474159
theorem B41270627 : Blo 666309 41270627 := bstep (se 1 (by rfl) ⟨30952970, by rfl⟩ : syracuseStep 41270627 = 61905941) B61905941
theorem B1424891 : Blo 666309 1424891 := bstep (se 1 (by rfl) ⟨1068668, by rfl⟩ : syracuseStep 1424891 = 2137337) B2137337
theorem B43302599 : Blo 666309 43302599 := bstep (se 1 (by rfl) ⟨32476949, by rfl⟩ : syracuseStep 43302599 = 64953899) B64953899
theorem B1687463 : Blo 666309 1687463 := bstep (se 1 (by rfl) ⟨1265597, by rfl⟩ : syracuseStep 1687463 = 2531195) B2531195
theorem B12861611 : Blo 666309 12861611 := bstep (se 1 (by rfl) ⟨9646208, by rfl⟩ : syracuseStep 12861611 = 19292417) B19292417
theorem B999659 : Blo 666309 999659 := bstep (se 1 (by rfl) ⟨749744, by rfl⟩ : syracuseStep 999659 = 1499489) B1499489
theorem B1687787 : Blo 666309 1687787 := bstep (se 1 (by rfl) ⟨1265840, by rfl⟩ : syracuseStep 1687787 = 2531681) B2531681
theorem B1523947 : Blo 666309 1523947 := bstep (se 1 (by rfl) ⟨1142960, by rfl⟩ : syracuseStep 1523947 = 2285921) B2285921
theorem B999719 : Blo 666309 999719 := bstep (se 1 (by rfl) ⟨749789, by rfl⟩ : syracuseStep 999719 = 1499579) B1499579
theorem B11747767 : Blo 666309 11747767 := bstep (se 1 (by rfl) ⟨8810825, by rfl⟩ : syracuseStep 11747767 = 17621651) B17621651
theorem B1524521 : Blo 666309 1524521 := bstep (se 2 (by rfl) ⟨571695, by rfl⟩ : syracuseStep 1524521 = 1143391) B1143391
theorem B2540443 : Blo 666309 2540443 := bstep (se 1 (by rfl) ⟨1905332, by rfl⟩ : syracuseStep 2540443 = 3810665) B3810665
theorem B1000391 : Blo 666309 1000391 := bstep (se 1 (by rfl) ⟨750293, by rfl⟩ : syracuseStep 1000391 = 1500587) B1500587
theorem B5063633 : Blo 666309 5063633 := bstep (se 2 (by rfl) ⟨1898862, by rfl⟩ : syracuseStep 5063633 = 3797725) B3797725
theorem B1000559 : Blo 666309 1000559 := bstep (se 1 (by rfl) ⟨750419, by rfl⟩ : syracuseStep 1000559 = 1500839) B1500839
theorem B6112421 : Blo 666309 6112421 := bstep (se 4 (by rfl) ⟨573039, by rfl⟩ : syracuseStep 6112421 = 1146079) B1146079
theorem B2409707 : Blo 666309 2409707 := bstep (se 1 (by rfl) ⟨1807280, by rfl⟩ : syracuseStep 2409707 = 3614561) B3614561
theorem B1000751 : Blo 666309 1000751 := bstep (se 1 (by rfl) ⟨750563, by rfl⟩ : syracuseStep 1000751 = 1501127) B1501127
theorem B5064119 : Blo 666309 5064119 := bstep (se 1 (by rfl) ⟨3798089, by rfl⟩ : syracuseStep 5064119 = 7596179) B7596179
theorem B1000955 : Blo 666309 1000955 := bstep (se 1 (by rfl) ⟨750716, by rfl⟩ : syracuseStep 1000955 = 1501433) B1501433
theorem B1000991 : Blo 666309 1000991 := bstep (se 1 (by rfl) ⟨750743, by rfl⟩ : syracuseStep 1000991 = 1501487) B1501487
theorem B1001135 : Blo 666309 1001135 := bstep (se 1 (by rfl) ⟨750851, by rfl⟩ : syracuseStep 1001135 = 1501703) B1501703
theorem B1001255 : Blo 666309 1001255 := bstep (se 1 (by rfl) ⟨750941, by rfl⟩ : syracuseStep 1001255 = 1501883) B1501883
theorem B5719895 : Blo 666309 5719895 := bstep (se 1 (by rfl) ⟨4289921, by rfl⟩ : syracuseStep 5719895 = 8579843) B8579843
theorem B1394671 : Blo 666309 1394671 := bstep (se 1 (by rfl) ⟨1046003, by rfl⟩ : syracuseStep 1394671 = 2092007) B2092007
theorem B1001807 : Blo 666309 1001807 := bstep (se 1 (by rfl) ⟨751355, by rfl⟩ : syracuseStep 1001807 = 1502711) B1502711
theorem B1001855 : Blo 666309 1001855 := bstep (se 1 (by rfl) ⟨751391, by rfl⟩ : syracuseStep 1001855 = 1502783) B1502783
theorem B1001897 : Blo 666309 1001897 := bstep (se 2 (by rfl) ⟨375711, by rfl⟩ : syracuseStep 1001897 = 751423) B751423
theorem B1690409 : Blo 666309 1690409 := bstep (se 2 (by rfl) ⟨633903, by rfl⟩ : syracuseStep 1690409 = 1267807) B1267807
theorem B1002281 : Blo 666309 1002281 := bstep (se 2 (by rfl) ⟨375855, by rfl⟩ : syracuseStep 1002281 = 751711) B751711
theorem B5065577 : Blo 666309 5065577 := bstep (se 2 (by rfl) ⟨1899591, by rfl⟩ : syracuseStep 5065577 = 3799183) B3799183
theorem B1002491 : Blo 666309 1002491 := bstep (se 1 (by rfl) ⟨751868, by rfl⟩ : syracuseStep 1002491 = 1503737) B1503737
theorem B1002551 : Blo 666309 1002551 := bstep (se 1 (by rfl) ⟨751913, by rfl⟩ : syracuseStep 1002551 = 1503827) B1503827
theorem B4803731 : Blo 666309 4803731 := bstep (se 1 (by rfl) ⟨3602798, by rfl⟩ : syracuseStep 4803731 = 7205597) B7205597
theorem B1002671 : Blo 666309 1002671 := bstep (se 1 (by rfl) ⟨752003, by rfl⟩ : syracuseStep 1002671 = 1504007) B1504007
theorem B16272737 : Blo 666309 16272737 := bstep (se 2 (by rfl) ⟨6102276, by rfl⟩ : syracuseStep 16272737 = 12204553) B12204553
theorem B1691239 : Blo 666309 1691239 := bstep (se 1 (by rfl) ⟨1268429, by rfl⟩ : syracuseStep 1691239 = 2536859) B2536859
theorem B1003391 : Blo 666309 1003391 := bstep (se 1 (by rfl) ⟨752543, by rfl⟩ : syracuseStep 1003391 = 1505087) B1505087
theorem B6410279 : Blo 666309 6410279 := bstep (se 1 (by rfl) ⟨4807709, by rfl⟩ : syracuseStep 6410279 = 9615419) B9615419
theorem B1265719 : Blo 666309 1265719 := bstep (se 1 (by rfl) ⟨949289, by rfl⟩ : syracuseStep 1265719 = 1898579) B1898579
theorem B1003583 : Blo 666309 1003583 := bstep (se 1 (by rfl) ⟨752687, by rfl⟩ : syracuseStep 1003583 = 1505375) B1505375
theorem B1691867 : Blo 666309 1691867 := bstep (se 1 (by rfl) ⟨1268900, by rfl⟩ : syracuseStep 1691867 = 2537801) B2537801
theorem B1003817 : Blo 666309 1003817 := bstep (se 2 (by rfl) ⟨376431, by rfl⟩ : syracuseStep 1003817 = 752863) B752863
theorem B1004087 : Blo 666309 1004087 := bstep (se 1 (by rfl) ⟨753065, by rfl⟩ : syracuseStep 1004087 = 1506131) B1506131
theorem B1004447 : Blo 666309 1004447 := bstep (se 1 (by rfl) ⟨753335, by rfl⟩ : syracuseStep 1004447 = 1506671) B1506671
theorem B1004639 : Blo 666309 1004639 := bstep (se 1 (by rfl) ⟨753479, by rfl⟩ : syracuseStep 1004639 = 1506959) B1506959
theorem B5723243 : Blo 666309 5723243 := bstep (se 1 (by rfl) ⟨4292432, by rfl⟩ : syracuseStep 5723243 = 8584865) B8584865
theorem B1004699 : Blo 666309 1004699 := bstep (se 1 (by rfl) ⟨753524, by rfl⟩ : syracuseStep 1004699 = 1507049) B1507049
theorem B9655847 : Blo 666309 9655847 := bstep (se 1 (by rfl) ⟨7241885, by rfl⟩ : syracuseStep 9655847 = 14483771) B14483771
theorem B1267321 : Blo 666309 1267321 := bstep (se 2 (by rfl) ⟨475245, by rfl⟩ : syracuseStep 1267321 = 950491) B950491
theorem B92526401 : Blo 666309 92526401 := bstep (se 2 (by rfl) ⟨34697400, by rfl⟩ : syracuseStep 92526401 = 69394801) B69394801
theorem B1005383 : Blo 666309 1005383 := bstep (se 1 (by rfl) ⟨754037, by rfl⟩ : syracuseStep 1005383 = 1508075) B1508075
theorem B1267579 : Blo 666309 1267579 := bstep (se 1 (by rfl) ⟨950684, by rfl⟩ : syracuseStep 1267579 = 1901369) B1901369
theorem B1071391 : Blo 666309 1071391 := bstep (se 1 (by rfl) ⟨803543, by rfl⟩ : syracuseStep 1071391 = 1607087) B1607087
theorem B1268065 : Blo 666309 1268065 := bstep (se 2 (by rfl) ⟨475524, by rfl⟩ : syracuseStep 1268065 = 951049) B951049
theorem B1268551 : Blo 666309 1268551 := bstep (se 1 (by rfl) ⟨951413, by rfl⟩ : syracuseStep 1268551 = 1902827) B1902827
theorem B1203931 : Blo 666309 1203931 := bstep (se 1 (by rfl) ⟨902948, by rfl⟩ : syracuseStep 1203931 = 1805897) B1805897
theorem B18341639 : Blo 666309 18341639 := bstep (se 1 (by rfl) ⟨13756229, by rfl⟩ : syracuseStep 18341639 = 27512459) B27512459
theorem B1269523 : Blo 666309 1269523 := bstep (se 1 (by rfl) ⟨952142, by rfl⟩ : syracuseStep 1269523 = 1904285) B1904285
theorem B1269751 : Blo 666309 1269751 := bstep (se 1 (by rfl) ⟨952313, by rfl⟩ : syracuseStep 1269751 = 1904627) B1904627
theorem B4284539 : Blo 666309 4284539 := bstep (se 1 (by rfl) ⟨3213404, by rfl⟩ : syracuseStep 4284539 = 6426809) B6426809
theorem B1696423 : Blo 666309 1696423 := bstep (se 1 (by rfl) ⟨1272317, by rfl⟩ : syracuseStep 1696423 = 2544635) B2544635
theorem B1499867 : Blo 666309 1499867 := bstep (se 1 (by rfl) ⟨1124900, by rfl⟩ : syracuseStep 1499867 = 2249801) B2249801
theorem B1500281 : Blo 666309 1500281 := bstep (se 2 (by rfl) ⟨562605, by rfl⟩ : syracuseStep 1500281 = 1125211) B1125211
theorem B1205561 : Blo 666309 1205561 := bstep (se 2 (by rfl) ⟨452085, by rfl⟩ : syracuseStep 1205561 = 904171) B904171
theorem B1271369 : Blo 666309 1271369 := bstep (se 2 (by rfl) ⟨476763, by rfl⟩ : syracuseStep 1271369 = 953527) B953527
theorem B4286155 : Blo 666309 4286155 := bstep (se 1 (by rfl) ⟨3214616, by rfl⟩ : syracuseStep 4286155 = 6429233) B6429233
theorem B1500947 : Blo 666309 1500947 := bstep (se 1 (by rfl) ⟨1125710, by rfl⟩ : syracuseStep 1500947 = 2251421) B2251421
theorem B1140635 : Blo 666309 1140635 := bstep (se 1 (by rfl) ⟨855476, by rfl⟩ : syracuseStep 1140635 = 1710953) B1710953
theorem B1501163 : Blo 666309 1501163 := bstep (se 1 (by rfl) ⟨1125872, by rfl⟩ : syracuseStep 1501163 = 2251745) B2251745
theorem B1271801 : Blo 666309 1271801 := bstep (se 2 (by rfl) ⟨476925, by rfl⟩ : syracuseStep 1271801 = 953851) B953851
theorem B1271855 : Blo 666309 1271855 := bstep (se 1 (by rfl) ⟨953891, by rfl⟩ : syracuseStep 1271855 = 1907783) B1907783
theorem B2254931 : Blo 666309 2254931 := bstep (se 1 (by rfl) ⟨1691198, by rfl⟩ : syracuseStep 2254931 = 3382397) B3382397
theorem B1501307 : Blo 666309 1501307 := bstep (se 1 (by rfl) ⟨1125980, by rfl⟩ : syracuseStep 1501307 = 2251961) B2251961
theorem B1501577 : Blo 666309 1501577 := bstep (se 2 (by rfl) ⟨563091, by rfl⟩ : syracuseStep 1501577 = 1126183) B1126183
theorem B715559 : Blo 666309 715559 := bstep (se 1 (by rfl) ⟨536669, by rfl⟩ : syracuseStep 715559 = 1073339) B1073339
theorem B3435425 : Blo 666309 3435425 := bstep (se 2 (by rfl) ⟨1288284, by rfl⟩ : syracuseStep 3435425 = 2576569) B2576569
theorem B1502279 : Blo 666309 1502279 := bstep (se 1 (by rfl) ⟨1126709, by rfl⟩ : syracuseStep 1502279 = 2253419) B2253419
theorem B1502675 : Blo 666309 1502675 := bstep (se 1 (by rfl) ⟨1127006, by rfl⟩ : syracuseStep 1502675 = 2254013) B2254013
theorem B2846279 : Blo 666309 2846279 := bstep (se 1 (by rfl) ⟨2134709, by rfl⟩ : syracuseStep 2846279 = 4269419) B4269419
theorem B1601167 : Blo 666309 1601167 := bstep (se 1 (by rfl) ⟨1200875, by rfl⟩ : syracuseStep 1601167 = 2401751) B2401751
theorem B1502945 : Blo 666309 1502945 := bstep (se 2 (by rfl) ⟨563604, by rfl⟩ : syracuseStep 1502945 = 1127209) B1127209
theorem B2256727 : Blo 666309 2256727 := bstep (se 1 (by rfl) ⟨1692545, by rfl⟩ : syracuseStep 2256727 = 3385091) B3385091
theorem B1503305 : Blo 666309 1503305 := bstep (se 2 (by rfl) ⟨563739, by rfl⟩ : syracuseStep 1503305 = 1127479) B1127479
theorem B749695 : Blo 666309 749695 := bstep (se 1 (by rfl) ⟨562271, by rfl⟩ : syracuseStep 749695 = 1124543) B1124543
theorem B1503359 : Blo 666309 1503359 := bstep (se 1 (by rfl) ⟨1127519, by rfl⟩ : syracuseStep 1503359 = 2255039) B2255039
theorem B847999 : Blo 666309 847999 := bstep (se 1 (by rfl) ⟨635999, by rfl⟩ : syracuseStep 847999 = 1271999) B1271999
theorem B46330865 : Blo 666309 46330865 := bstep (se 2 (by rfl) ⟨17374074, by rfl⟩ : syracuseStep 46330865 = 34748149) B34748149
theorem B1504439 : Blo 666309 1504439 := bstep (se 1 (by rfl) ⟨1128329, by rfl⟩ : syracuseStep 1504439 = 2256659) B2256659
theorem B2847953 : Blo 666309 2847953 := bstep (se 2 (by rfl) ⟨1067982, by rfl⟩ : syracuseStep 2847953 = 2135965) B2135965
theorem B2258387 : Blo 666309 2258387 := bstep (se 1 (by rfl) ⟨1693790, by rfl⟩ : syracuseStep 2258387 = 3387581) B3387581
theorem B2979287 : Blo 666309 2979287 := bstep (se 1 (by rfl) ⟨2234465, by rfl⟩ : syracuseStep 2979287 = 4468931) B4468931
theorem B2258657 : Blo 666309 2258657 := bstep (se 2 (by rfl) ⟨846996, by rfl⟩ : syracuseStep 2258657 = 1693993) B1693993
theorem B1603319 : Blo 666309 1603319 := bstep (se 1 (by rfl) ⟨1202489, by rfl⟩ : syracuseStep 1603319 = 2404979) B2404979
theorem B1505015 : Blo 666309 1505015 := bstep (se 1 (by rfl) ⟨1128761, by rfl⟩ : syracuseStep 1505015 = 2257523) B2257523
theorem B3438443 : Blo 666309 3438443 := bstep (se 1 (by rfl) ⟨2578832, by rfl⟩ : syracuseStep 3438443 = 5157665) B5157665
theorem B7698341 : Blo 666309 7698341 := bstep (se 4 (by rfl) ⟨721719, by rfl⟩ : syracuseStep 7698341 = 1443439) B1443439
theorem B1505195 : Blo 666309 1505195 := bstep (se 1 (by rfl) ⟨1128896, by rfl⟩ : syracuseStep 1505195 = 2257793) B2257793
theorem B12875759 : Blo 666309 12875759 := bstep (se 1 (by rfl) ⟨9656819, by rfl⟩ : syracuseStep 12875759 = 19313639) B19313639
theorem B1505321 : Blo 666309 1505321 := bstep (se 2 (by rfl) ⟨564495, by rfl⟩ : syracuseStep 1505321 = 1128991) B1128991
theorem B3373487 : Blo 666309 3373487 := bstep (se 1 (by rfl) ⟨2530115, by rfl⟩ : syracuseStep 3373487 = 5060231) B5060231
theorem B1505735 : Blo 666309 1505735 := bstep (se 1 (by rfl) ⟨1129301, by rfl⟩ : syracuseStep 1505735 = 2258603) B2258603
theorem B1898977 : Blo 666309 1898977 := bstep (se 2 (by rfl) ⟨712116, by rfl⟩ : syracuseStep 1898977 = 1424233) B1424233
theorem B3045919 : Blo 666309 3045919 := bstep (se 1 (by rfl) ⟨2284439, by rfl⟩ : syracuseStep 3045919 = 4568879) B4568879
theorem B1505897 : Blo 666309 1505897 := bstep (se 2 (by rfl) ⟨564711, by rfl⟩ : syracuseStep 1505897 = 1129423) B1129423
theorem B752287 : Blo 666309 752287 := bstep (se 1 (by rfl) ⟨564215, by rfl⟩ : syracuseStep 752287 = 1128431) B1128431
theorem B1505951 : Blo 666309 1505951 := bstep (se 1 (by rfl) ⟨1129463, by rfl⟩ : syracuseStep 1505951 = 2258927) B2258927
theorem B1506095 : Blo 666309 1506095 := bstep (se 1 (by rfl) ⟨1129571, by rfl⟩ : syracuseStep 1506095 = 2259143) B2259143
theorem B23755639 : Blo 666309 23755639 := bstep (se 1 (by rfl) ⟨17816729, by rfl⟩ : syracuseStep 23755639 = 35633459) B35633459
theorem B12352501 : Blo 666309 12352501 := bstep (se 5 (by rfl) ⟨579023, by rfl⟩ : syracuseStep 12352501 = 1158047) B1158047
theorem B19758275 : Blo 666309 19758275 := bstep (se 1 (by rfl) ⟨14818706, by rfl⟩ : syracuseStep 19758275 = 29637413) B29637413
theorem B1506527 : Blo 666309 1506527 := bstep (se 1 (by rfl) ⟨1129895, by rfl⟩ : syracuseStep 1506527 = 2259791) B2259791
theorem B1506743 : Blo 666309 1506743 := bstep (se 1 (by rfl) ⟨1130057, by rfl⟩ : syracuseStep 1506743 = 2260115) B2260115
theorem B1506923 : Blo 666309 1506923 := bstep (se 1 (by rfl) ⟨1130192, by rfl⟩ : syracuseStep 1506923 = 2260385) B2260385
theorem B2260655 : Blo 666309 2260655 := bstep (se 1 (by rfl) ⟨1695491, by rfl⟩ : syracuseStep 2260655 = 3390983) B3390983
theorem B753439 : Blo 666309 753439 := bstep (se 1 (by rfl) ⟨565079, by rfl⟩ : syracuseStep 753439 = 1130159) B1130159
theorem B1900367 : Blo 666309 1900367 := bstep (se 1 (by rfl) ⟨1425275, by rfl⟩ : syracuseStep 1900367 = 2850551) B2850551
theorem B1507193 : Blo 666309 1507193 := bstep (se 2 (by rfl) ⟨565197, by rfl⟩ : syracuseStep 1507193 = 1130395) B1130395
theorem B1507283 : Blo 666309 1507283 := bstep (se 1 (by rfl) ⟨1130462, by rfl⟩ : syracuseStep 1507283 = 2260925) B2260925
theorem B2031929 : Blo 666309 2031929 := bstep (se 2 (by rfl) ⟨761973, by rfl⟩ : syracuseStep 2031929 = 1523947) B1523947
theorem B15663689 : Blo 666309 15663689 := bstep (se 2 (by rfl) ⟨5873883, by rfl⟩ : syracuseStep 15663689 = 11747767) B11747767
theorem B3375755 : Blo 666309 3375755 := bstep (se 1 (by rfl) ⟨2531816, by rfl⟩ : syracuseStep 3375755 = 5063633) B5063633
theorem B4817569 : Blo 666309 4817569 := bstep (se 2 (by rfl) ⟨1806588, by rfl⟩ : syracuseStep 4817569 = 3613177) B3613177
theorem B2261897 : Blo 666309 2261897 := bstep (se 2 (by rfl) ⟨848211, by rfl⟩ : syracuseStep 2261897 = 1696423) B1696423
theorem B3376079 : Blo 666309 3376079 := bstep (se 1 (by rfl) ⟨2532059, by rfl⟩ : syracuseStep 3376079 = 5064119) B5064119
theorem B2851969 : Blo 666309 2851969 := bstep (se 2 (by rfl) ⟨1069488, by rfl⟩ : syracuseStep 2851969 = 2138977) B2138977
theorem B1902143 : Blo 666309 1902143 := bstep (se 1 (by rfl) ⟨1426607, by rfl⟩ : syracuseStep 1902143 = 2853215) B2853215
theorem B3377051 : Blo 666309 3377051 := bstep (se 1 (by rfl) ⟨2532788, by rfl⟩ : syracuseStep 3377051 = 5065577) B5065577
theorem B4065389 : Blo 666309 4065389 := bstep (se 3 (by rfl) ⟨762260, by rfl⟩ : syracuseStep 4065389 = 1524521) B1524521
theorem B10848491 : Blo 666309 10848491 := bstep (se 1 (by rfl) ⟨8136368, by rfl⟩ : syracuseStep 10848491 = 16272737) B16272737
theorem B2165267 : Blo 666309 2165267 := bstep (se 1 (by rfl) ⟨1623950, by rfl⟩ : syracuseStep 2165267 = 3247901) B3247901
theorem B14420531 : Blo 666309 14420531 := bstep (se 1 (by rfl) ⟨10815398, by rfl⟩ : syracuseStep 14420531 = 21630797) B21630797
theorem B8129261 : Blo 666309 8129261 := bstep (se 3 (by rfl) ⟨1524236, by rfl⟩ : syracuseStep 8129261 = 3048473) B3048473
theorem B2853625 : Blo 666309 2853625 := bstep (se 2 (by rfl) ⟨1070109, by rfl⟩ : syracuseStep 2853625 = 2140219) B2140219
theorem B6491279 : Blo 666309 6491279 := bstep (se 1 (by rfl) ⟨4868459, by rfl⟩ : syracuseStep 6491279 = 9736919) B9736919
theorem B6425885 : Blo 666309 6425885 := bstep (se 3 (by rfl) ⟨1204853, by rfl⟩ : syracuseStep 6425885 = 2409707) B2409707
theorem B3214829 : Blo 666309 3214829 := bstep (se 3 (by rfl) ⟨602780, by rfl⟩ : syracuseStep 3214829 = 1205561) B1205561
theorem B2134889 : Blo 666309 2134889 := bstep (se 2 (by rfl) ⟨800583, by rfl⟩ : syracuseStep 2134889 = 1601167) B1601167
theorem B12227759 : Blo 666309 12227759 := bstep (se 1 (by rfl) ⟨9170819, by rfl⟩ : syracuseStep 12227759 = 18341639) B18341639
theorem B2856359 : Blo 666309 2856359 := bstep (se 1 (by rfl) ⟨2142269, by rfl⟩ : syracuseStep 2856359 = 4284539) B4284539
theorem B1710683 : Blo 666309 1710683 := bstep (se 1 (by rfl) ⟨1283012, by rfl⟩ : syracuseStep 1710683 = 2566025) B2566025
theorem B760423 : Blo 666309 760423 := bstep (se 1 (by rfl) ⟨570317, by rfl⟩ : syracuseStep 760423 = 1140635) B1140635
theorem B5709163 : Blo 666309 5709163 := bstep (se 1 (by rfl) ⟨4281872, by rfl⟩ : syracuseStep 5709163 = 8563745) B8563745
theorem B3808889 : Blo 666309 3808889 := bstep (se 2 (by rfl) ⟨1428333, by rfl⟩ : syracuseStep 3808889 = 2856667) B2856667
theorem B16260851 : Blo 666309 16260851 := bstep (se 1 (by rfl) ⟨12195638, by rfl⟩ : syracuseStep 16260851 = 24391277) B24391277
theorem B3809207 : Blo 666309 3809207 := bstep (se 1 (by rfl) ⟨2856905, by rfl⟩ : syracuseStep 3809207 = 5713811) B5713811
theorem B9281537 : Blo 666309 9281537 := bstep (se 2 (by rfl) ⟨3480576, by rfl⟩ : syracuseStep 9281537 = 6961153) B6961153
theorem B3809663 : Blo 666309 3809663 := bstep (se 1 (by rfl) ⟨2857247, by rfl⟩ : syracuseStep 3809663 = 5714495) B5714495
theorem B2859401 : Blo 666309 2859401 := bstep (se 2 (by rfl) ⟨1072275, by rfl⟩ : syracuseStep 2859401 = 2144551) B2144551
theorem B8135099 : Blo 666309 8135099 := bstep (se 1 (by rfl) ⟨6101324, by rfl⟩ : syracuseStep 8135099 = 12202649) B12202649
theorem B2531969 : Blo 666309 2531969 := bstep (se 2 (by rfl) ⟨949488, by rfl⟩ : syracuseStep 2531969 = 1898977) B1898977
theorem B5088905 : Blo 666309 5088905 := bstep (se 2 (by rfl) ⟨1908339, by rfl⟩ : syracuseStep 5088905 = 3816679) B3816679
theorem B6432959 : Blo 666309 6432959 := bstep (se 1 (by rfl) ⟨4824719, by rfl⟩ : syracuseStep 6432959 = 9649439) B9649439
theorem B1124975 : Blo 666309 1124975 := bstep (se 1 (by rfl) ⟨843731, by rfl⟩ : syracuseStep 1124975 = 1687463) B1687463
theorem B666439 : Blo 666309 666439 := bstep (se 1 (by rfl) ⟨499829, by rfl⟩ : syracuseStep 666439 = 999659) B999659
theorem B1125191 : Blo 666309 1125191 := bstep (se 1 (by rfl) ⟨843893, by rfl⟩ : syracuseStep 1125191 = 1687787) B1687787
theorem B666479 : Blo 666309 666479 := bstep (se 1 (by rfl) ⟨499859, by rfl⟩ : syracuseStep 666479 = 999719) B999719
theorem B666927 : Blo 666309 666927 := bstep (se 1 (by rfl) ⟨500195, by rfl⟩ : syracuseStep 666927 = 1000391) B1000391
theorem B667039 : Blo 666309 667039 := bstep (se 1 (by rfl) ⟨500279, by rfl⟩ : syracuseStep 667039 = 1000559) B1000559
theorem B4074947 : Blo 666309 4074947 := bstep (se 1 (by rfl) ⟨3056210, by rfl⟩ : syracuseStep 4074947 = 6112421) B6112421
theorem B667167 : Blo 666309 667167 := bstep (se 1 (by rfl) ⟨500375, by rfl⟩ : syracuseStep 667167 = 1000751) B1000751
theorem B667303 : Blo 666309 667303 := bstep (se 1 (by rfl) ⟨500477, by rfl⟩ : syracuseStep 667303 = 1000955) B1000955
theorem B667327 : Blo 666309 667327 := bstep (se 1 (by rfl) ⟨500495, by rfl⟩ : syracuseStep 667327 = 1000991) B1000991
theorem B667423 : Blo 666309 667423 := bstep (se 1 (by rfl) ⟨500567, by rfl⟩ : syracuseStep 667423 = 1001135) B1001135
theorem B5648201 : Blo 666309 5648201 := bstep (se 2 (by rfl) ⟨2118075, by rfl⟩ : syracuseStep 5648201 = 4236151) B4236151
theorem B667503 : Blo 666309 667503 := bstep (se 1 (by rfl) ⟨500627, by rfl⟩ : syracuseStep 667503 = 1001255) B1001255
theorem B3387257 : Blo 666309 3387257 := bstep (se 2 (by rfl) ⟨1270221, by rfl⟩ : syracuseStep 3387257 = 2540443) B2540443
theorem B3813263 : Blo 666309 3813263 := bstep (se 1 (by rfl) ⟨2859947, by rfl⟩ : syracuseStep 3813263 = 5719895) B5719895
theorem B667871 : Blo 666309 667871 := bstep (se 1 (by rfl) ⟨500903, by rfl⟩ : syracuseStep 667871 = 1001807) B1001807
theorem B667903 : Blo 666309 667903 := bstep (se 1 (by rfl) ⟨500927, by rfl⟩ : syracuseStep 667903 = 1001855) B1001855
theorem B2142463 : Blo 666309 2142463 := bstep (se 1 (by rfl) ⟨1606847, by rfl⟩ : syracuseStep 2142463 = 3213695) B3213695
theorem B667931 : Blo 666309 667931 := bstep (se 1 (by rfl) ⟨500948, by rfl⟩ : syracuseStep 667931 = 1001897) B1001897
theorem B2535887 : Blo 666309 2535887 := bstep (se 1 (by rfl) ⟨1901915, by rfl⟩ : syracuseStep 2535887 = 3803831) B3803831
theorem B1126939 : Blo 666309 1126939 := bstep (se 1 (by rfl) ⟨845204, by rfl⟩ : syracuseStep 1126939 = 1690409) B1690409
theorem B668187 : Blo 666309 668187 := bstep (se 1 (by rfl) ⟨501140, by rfl⟩ : syracuseStep 668187 = 1002281) B1002281
theorem B668327 : Blo 666309 668327 := bstep (se 1 (by rfl) ⟨501245, by rfl⟩ : syracuseStep 668327 = 1002491) B1002491
theorem B668367 : Blo 666309 668367 := bstep (se 1 (by rfl) ⟨501275, by rfl⟩ : syracuseStep 668367 = 1002551) B1002551
theorem B668447 : Blo 666309 668447 := bstep (se 1 (by rfl) ⟨501335, by rfl⟩ : syracuseStep 668447 = 1002671) B1002671
theorem B5714873 : Blo 666309 5714873 := bstep (se 2 (by rfl) ⟨2143077, by rfl⟩ : syracuseStep 5714873 = 4286155) B4286155
theorem B668927 : Blo 666309 668927 := bstep (se 1 (by rfl) ⟨501695, by rfl⟩ : syracuseStep 668927 = 1003391) B1003391
theorem B4273519 : Blo 666309 4273519 := bstep (se 1 (by rfl) ⟨3205139, by rfl⟩ : syracuseStep 4273519 = 6410279) B6410279
theorem B669055 : Blo 666309 669055 := bstep (se 1 (by rfl) ⟨501791, by rfl⟩ : syracuseStep 669055 = 1003583) B1003583
theorem B1127911 : Blo 666309 1127911 := bstep (se 1 (by rfl) ⟨845933, by rfl⟩ : syracuseStep 1127911 = 1691867) B1691867
theorem B669211 : Blo 666309 669211 := bstep (se 1 (by rfl) ⟨501908, by rfl⟩ : syracuseStep 669211 = 1003817) B1003817
theorem B669391 : Blo 666309 669391 := bstep (se 1 (by rfl) ⟨502043, by rfl⟩ : syracuseStep 669391 = 1004087) B1004087
theorem B669631 : Blo 666309 669631 := bstep (se 1 (by rfl) ⟨502223, by rfl⟩ : syracuseStep 669631 = 1004447) B1004447
theorem B669759 : Blo 666309 669759 := bstep (se 1 (by rfl) ⟨502319, by rfl⟩ : syracuseStep 669759 = 1004639) B1004639
theorem B3815495 : Blo 666309 3815495 := bstep (se 1 (by rfl) ⟨2861621, by rfl⟩ : syracuseStep 3815495 = 5723243) B5723243
theorem B669799 : Blo 666309 669799 := bstep (se 1 (by rfl) ⟨502349, by rfl⟩ : syracuseStep 669799 = 1004699) B1004699
theorem B6437231 : Blo 666309 6437231 := bstep (se 1 (by rfl) ⟨4827923, by rfl⟩ : syracuseStep 6437231 = 9655847) B9655847
theorem B61684267 : Blo 666309 61684267 := bstep (se 1 (by rfl) ⟨46263200, by rfl⟩ : syracuseStep 61684267 = 92526401) B92526401
theorem B670255 : Blo 666309 670255 := bstep (se 1 (by rfl) ⟨502691, by rfl⟩ : syracuseStep 670255 = 1005383) B1005383
theorem B4275517 : Blo 666309 4275517 := bstep (se 3 (by rfl) ⟨801659, by rfl⟩ : syracuseStep 4275517 = 1603319) B1603319
theorem B3653003 : Blo 666309 3653003 := bstep (se 1 (by rfl) ⟨2739752, by rfl⟩ : syracuseStep 3653003 = 5479505) B5479505
theorem B16235939 : Blo 666309 16235939 := bstep (se 1 (by rfl) ⟨12176954, by rfl⟩ : syracuseStep 16235939 = 24353909) B24353909
theorem B6405587 : Blo 666309 6405587 := bstep (se 1 (by rfl) ⟨4804190, by rfl⟩ : syracuseStep 6405587 = 9608381) B9608381
theorem B1687007 : Blo 666309 1687007 := bstep (se 1 (by rfl) ⟨1265255, by rfl⟩ : syracuseStep 1687007 = 2530511) B2530511
theorem B20528909 : Blo 666309 20528909 := bstep (se 3 (by rfl) ⟨3849170, by rfl⟩ : syracuseStep 20528909 = 7698341) B7698341
theorem B2146267 : Blo 666309 2146267 := bstep (se 1 (by rfl) ⟨1609700, by rfl⟩ : syracuseStep 2146267 = 3219401) B3219401
theorem B3391469 : Blo 666309 3391469 := bstep (se 3 (by rfl) ⟨635900, by rfl⟩ : syracuseStep 3391469 = 1271801) B1271801
theorem B1687625 : Blo 666309 1687625 := bstep (se 2 (by rfl) ⟨632859, by rfl⟩ : syracuseStep 1687625 = 1265719) B1265719
theorem B999593 : Blo 666309 999593 := bstep (se 2 (by rfl) ⟨374847, by rfl⟩ : syracuseStep 999593 = 749695) B749695
theorem B1130665 : Blo 666309 1130665 := bstep (se 2 (by rfl) ⟨423999, by rfl⟩ : syracuseStep 1130665 = 847999) B847999
theorem B999911 : Blo 666309 999911 := bstep (se 1 (by rfl) ⟨749933, by rfl⟩ : syracuseStep 999911 = 1499867) B1499867
theorem B6078995 : Blo 666309 6078995 := bstep (se 1 (by rfl) ⟨4559246, by rfl⟩ : syracuseStep 6078995 = 9118493) B9118493
theorem B9650821 : Blo 666309 9650821 := bstep (se 4 (by rfl) ⟨904764, by rfl⟩ : syracuseStep 9650821 = 1809529) B1809529
theorem B1000187 : Blo 666309 1000187 := bstep (se 1 (by rfl) ⟨750140, by rfl⟩ : syracuseStep 1000187 = 1500281) B1500281
theorem B17318785 : Blo 666309 17318785 := bstep (se 2 (by rfl) ⟨6494544, by rfl⟩ : syracuseStep 17318785 = 12989089) B12989089
theorem B1000631 : Blo 666309 1000631 := bstep (se 1 (by rfl) ⟨750473, by rfl⟩ : syracuseStep 1000631 = 1500947) B1500947
theorem B1000775 : Blo 666309 1000775 := bstep (se 1 (by rfl) ⟨750581, by rfl⟩ : syracuseStep 1000775 = 1501163) B1501163
theorem B1000871 : Blo 666309 1000871 := bstep (se 1 (by rfl) ⟨750653, by rfl⟩ : syracuseStep 1000871 = 1501307) B1501307
theorem B1689083 : Blo 666309 1689083 := bstep (se 1 (by rfl) ⟨1266812, by rfl⟩ : syracuseStep 1689083 = 2533625) B2533625
theorem B1001051 : Blo 666309 1001051 := bstep (se 1 (by rfl) ⟨750788, by rfl⟩ : syracuseStep 1001051 = 1501577) B1501577
theorem B1689407 : Blo 666309 1689407 := bstep (se 1 (by rfl) ⟨1267055, by rfl⟩ : syracuseStep 1689407 = 2534111) B2534111
theorem B1001519 : Blo 666309 1001519 := bstep (se 1 (by rfl) ⟨751139, by rfl⟩ : syracuseStep 1001519 = 1502279) B1502279
theorem B3426457 : Blo 666309 3426457 := bstep (se 2 (by rfl) ⟨1284921, by rfl⟩ : syracuseStep 3426457 = 2569843) B2569843
theorem B1689761 : Blo 666309 1689761 := bstep (se 2 (by rfl) ⟨633660, by rfl⟩ : syracuseStep 1689761 = 1267321) B1267321
theorem B1001783 : Blo 666309 1001783 := bstep (se 1 (by rfl) ⟨751337, by rfl⟩ : syracuseStep 1001783 = 1502675) B1502675
theorem B903479 : Blo 666309 903479 := bstep (se 1 (by rfl) ⟨677609, by rfl⟩ : syracuseStep 903479 = 1355219) B1355219
theorem B1001963 : Blo 666309 1001963 := bstep (se 1 (by rfl) ⟨751472, by rfl⟩ : syracuseStep 1001963 = 1502945) B1502945
theorem B1690105 : Blo 666309 1690105 := bstep (se 2 (by rfl) ⟨633789, by rfl⟩ : syracuseStep 1690105 = 1267579) B1267579
theorem B8702579 : Blo 666309 8702579 := bstep (se 1 (by rfl) ⟨6526934, by rfl⟩ : syracuseStep 8702579 = 13053869) B13053869
theorem B1002203 : Blo 666309 1002203 := bstep (se 1 (by rfl) ⟨751652, by rfl⟩ : syracuseStep 1002203 = 1503305) B1503305
theorem B1002239 : Blo 666309 1002239 := bstep (se 1 (by rfl) ⟨751679, by rfl⟩ : syracuseStep 1002239 = 1503359) B1503359
theorem B1428521 : Blo 666309 1428521 := bstep (se 2 (by rfl) ⟨535695, by rfl⟩ : syracuseStep 1428521 = 1071391) B1071391
theorem B1690753 : Blo 666309 1690753 := bstep (se 2 (by rfl) ⟨634032, by rfl⟩ : syracuseStep 1690753 = 1268065) B1268065
theorem B30887243 : Blo 666309 30887243 := bstep (se 1 (by rfl) ⟨23165432, by rfl⟩ : syracuseStep 30887243 = 46330865) B46330865
theorem B1002959 : Blo 666309 1002959 := bstep (se 1 (by rfl) ⟨752219, by rfl⟩ : syracuseStep 1002959 = 1504439) B1504439
theorem B1003049 : Blo 666309 1003049 := bstep (se 2 (by rfl) ⟨376143, by rfl⟩ : syracuseStep 1003049 = 752287) B752287
theorem B2543177 : Blo 666309 2543177 := bstep (se 2 (by rfl) ⟨953691, by rfl⟩ : syracuseStep 2543177 = 1907383) B1907383
theorem B1986191 : Blo 666309 1986191 := bstep (se 1 (by rfl) ⟨1489643, by rfl⟩ : syracuseStep 1986191 = 2979287) B2979287
theorem B1953467 : Blo 666309 1953467 := bstep (se 1 (by rfl) ⟨1465100, by rfl⟩ : syracuseStep 1953467 = 2930201) B2930201
theorem B1691401 : Blo 666309 1691401 := bstep (se 2 (by rfl) ⟨634275, by rfl⟩ : syracuseStep 1691401 = 1268551) B1268551
theorem B31674185 : Blo 666309 31674185 := bstep (se 2 (by rfl) ⟨11877819, by rfl⟩ : syracuseStep 31674185 = 23755639) B23755639
theorem B1003343 : Blo 666309 1003343 := bstep (se 1 (by rfl) ⟨752507, by rfl⟩ : syracuseStep 1003343 = 1505015) B1505015
theorem B1691563 : Blo 666309 1691563 := bstep (se 1 (by rfl) ⟨1268672, by rfl⟩ : syracuseStep 1691563 = 2537345) B2537345
theorem B1003463 : Blo 666309 1003463 := bstep (se 1 (by rfl) ⟨752597, by rfl⟩ : syracuseStep 1003463 = 1505195) B1505195
theorem B16470001 : Blo 666309 16470001 := bstep (se 2 (by rfl) ⟨6176250, by rfl⟩ : syracuseStep 16470001 = 12352501) B12352501
theorem B1691675 : Blo 666309 1691675 := bstep (se 1 (by rfl) ⟨1268756, by rfl⟩ : syracuseStep 1691675 = 2537513) B2537513
theorem B1003547 : Blo 666309 1003547 := bstep (se 1 (by rfl) ⟨752660, by rfl⟩ : syracuseStep 1003547 = 1505321) B1505321
theorem B2248991 : Blo 666309 2248991 := bstep (se 1 (by rfl) ⟨1686743, by rfl⟩ : syracuseStep 2248991 = 3373487) B3373487
theorem B1003823 : Blo 666309 1003823 := bstep (se 1 (by rfl) ⟨752867, by rfl⟩ : syracuseStep 1003823 = 1505735) B1505735
theorem B1003931 : Blo 666309 1003931 := bstep (se 1 (by rfl) ⟨752948, by rfl⟩ : syracuseStep 1003931 = 1505897) B1505897
theorem B1003967 : Blo 666309 1003967 := bstep (se 1 (by rfl) ⟨752975, by rfl⟩ : syracuseStep 1003967 = 1505951) B1505951
theorem B1692191 : Blo 666309 1692191 := bstep (se 1 (by rfl) ⟨1269143, by rfl⟩ : syracuseStep 1692191 = 2538287) B2538287
theorem B1004063 : Blo 666309 1004063 := bstep (se 1 (by rfl) ⟨753047, by rfl⟩ : syracuseStep 1004063 = 1506095) B1506095
theorem B2282251 : Blo 666309 2282251 := bstep (se 1 (by rfl) ⟨1711688, by rfl⟩ : syracuseStep 2282251 = 3423377) B3423377
theorem B1004351 : Blo 666309 1004351 := bstep (se 1 (by rfl) ⟨753263, by rfl⟩ : syracuseStep 1004351 = 1506527) B1506527
theorem B27513751 : Blo 666309 27513751 := bstep (se 1 (by rfl) ⟨20635313, by rfl⟩ : syracuseStep 27513751 = 41270627) B41270627
theorem B1004495 : Blo 666309 1004495 := bstep (se 1 (by rfl) ⟨753371, by rfl⟩ : syracuseStep 1004495 = 1506743) B1506743
theorem B1692697 : Blo 666309 1692697 := bstep (se 2 (by rfl) ⟨634761, by rfl⟩ : syracuseStep 1692697 = 1269523) B1269523
theorem B1004585 : Blo 666309 1004585 := bstep (se 2 (by rfl) ⟨376719, by rfl⟩ : syracuseStep 1004585 = 753439) B753439
theorem B1004615 : Blo 666309 1004615 := bstep (se 1 (by rfl) ⟨753461, by rfl⟩ : syracuseStep 1004615 = 1506923) B1506923
theorem B1266911 : Blo 666309 1266911 := bstep (se 1 (by rfl) ⟨950183, by rfl⟩ : syracuseStep 1266911 = 1900367) B1900367
theorem B1004795 : Blo 666309 1004795 := bstep (se 1 (by rfl) ⟨753596, by rfl⟩ : syracuseStep 1004795 = 1507193) B1507193
theorem B1004855 : Blo 666309 1004855 := bstep (se 1 (by rfl) ⟨753641, by rfl⟩ : syracuseStep 1004855 = 1507283) B1507283
theorem B1693001 : Blo 666309 1693001 := bstep (se 2 (by rfl) ⟨634875, by rfl⟩ : syracuseStep 1693001 = 1269751) B1269751
theorem B8574407 : Blo 666309 8574407 := bstep (se 1 (by rfl) ⟨6430805, by rfl⟩ : syracuseStep 8574407 = 12861611) B12861611
theorem B1005161 : Blo 666309 1005161 := bstep (se 2 (by rfl) ⟨376935, by rfl⟩ : syracuseStep 1005161 = 753871) B753871
theorem B4807421 : Blo 666309 4807421 := bstep (se 3 (by rfl) ⟨901391, by rfl⟩ : syracuseStep 4807421 = 1802783) B1802783
theorem B2251583 : Blo 666309 2251583 := bstep (se 1 (by rfl) ⟨1688687, by rfl⟩ : syracuseStep 2251583 = 3377375) B3377375
theorem B4283513 : Blo 666309 4283513 := bstep (se 2 (by rfl) ⟨1606317, by rfl⟩ : syracuseStep 4283513 = 3212635) B3212635
theorem B3202487 : Blo 666309 3202487 := bstep (se 1 (by rfl) ⟨2401865, by rfl⟩ : syracuseStep 3202487 = 4803731) B4803731
theorem B1859561 : Blo 666309 1859561 := bstep (se 2 (by rfl) ⟨697335, by rfl⟩ : syracuseStep 1859561 = 1394671) B1394671
theorem B5071409 : Blo 666309 5071409 := bstep (se 2 (by rfl) ⟨1901778, by rfl⟩ : syracuseStep 5071409 = 3803557) B3803557
theorem B12346663 : Blo 666309 12346663 := bstep (se 1 (by rfl) ⟨9259997, by rfl⟩ : syracuseStep 12346663 = 18519995) B18519995
theorem B1271209 : Blo 666309 1271209 := bstep (se 2 (by rfl) ⟨476703, by rfl⟩ : syracuseStep 1271209 = 953407) B953407
theorem B2254985 : Blo 666309 2254985 := bstep (se 2 (by rfl) ⟨845619, by rfl⟩ : syracuseStep 2254985 = 1691239) B1691239
theorem B3008969 : Blo 666309 3008969 := bstep (se 2 (by rfl) ⟨1128363, by rfl⟩ : syracuseStep 3008969 = 2256727) B2256727
theorem B847579 : Blo 666309 847579 := bstep (se 1 (by rfl) ⟨635684, by rfl⟩ : syracuseStep 847579 = 1271369) B1271369
theorem B5697377 : Blo 666309 5697377 := bstep (se 2 (by rfl) ⟨2136516, by rfl⟩ : syracuseStep 5697377 = 4273033) B4273033
theorem B1601495 : Blo 666309 1601495 := bstep (se 1 (by rfl) ⟨1201121, by rfl⟩ : syracuseStep 1601495 = 2402243) B2402243
theorem B847903 : Blo 666309 847903 := bstep (se 1 (by rfl) ⟨635927, by rfl⟩ : syracuseStep 847903 = 1271855) B1271855
theorem B1503287 : Blo 666309 1503287 := bstep (se 1 (by rfl) ⟨1127465, by rfl⟩ : syracuseStep 1503287 = 2254931) B2254931
theorem B1929343 : Blo 666309 1929343 := bstep (se 1 (by rfl) ⟨1447007, by rfl⟩ : syracuseStep 1929343 = 2894015) B2894015
theorem B2290283 : Blo 666309 2290283 := bstep (se 1 (by rfl) ⟨1717712, by rfl⟩ : syracuseStep 2290283 = 3435425) B3435425
theorem B1897519 : Blo 666309 1897519 := bstep (se 1 (by rfl) ⟨1423139, by rfl⟩ : syracuseStep 1897519 = 2846279) B2846279
theorem B1897577 : Blo 666309 1897577 := bstep (se 2 (by rfl) ⟨711591, by rfl⟩ : syracuseStep 1897577 = 1423183) B1423183
theorem B751207 : Blo 666309 751207 := bstep (se 1 (by rfl) ⟨563405, by rfl⟩ : syracuseStep 751207 = 1126811) B1126811
theorem B7632629 : Blo 666309 7632629 := bstep (se 5 (by rfl) ⟨357779, by rfl⟩ : syracuseStep 7632629 = 715559) B715559
theorem B2848553 : Blo 666309 2848553 := bstep (se 2 (by rfl) ⟨1068207, by rfl⟩ : syracuseStep 2848553 = 2136415) B2136415
theorem B4061225 : Blo 666309 4061225 := bstep (se 2 (by rfl) ⟨1522959, by rfl⟩ : syracuseStep 4061225 = 3045919) B3045919
theorem B1898635 : Blo 666309 1898635 := bstep (se 1 (by rfl) ⟨1423976, by rfl⟩ : syracuseStep 1898635 = 2847953) B2847953
theorem B751783 : Blo 666309 751783 := bstep (se 1 (by rfl) ⟨563837, by rfl⟩ : syracuseStep 751783 = 1127675) B1127675
theorem B1505591 : Blo 666309 1505591 := bstep (se 1 (by rfl) ⟨1129193, by rfl⟩ : syracuseStep 1505591 = 2258387) B2258387
theorem B1505771 : Blo 666309 1505771 := bstep (se 1 (by rfl) ⟨1129328, by rfl⟩ : syracuseStep 1505771 = 2258657) B2258657
theorem B2292295 : Blo 666309 2292295 := bstep (se 1 (by rfl) ⟨1719221, by rfl⟩ : syracuseStep 2292295 = 3438443) B3438443
theorem B3799709 : Blo 666309 3799709 := bstep (se 3 (by rfl) ⟨712445, by rfl⟩ : syracuseStep 3799709 = 1424891) B1424891
theorem B8583839 : Blo 666309 8583839 := bstep (se 1 (by rfl) ⟨6437879, by rfl⟩ : syracuseStep 8583839 = 12875759) B12875759
theorem B5077727 : Blo 666309 5077727 := bstep (se 1 (by rfl) ⟨3808295, by rfl⟩ : syracuseStep 5077727 = 7616591) B7616591
theorem B2260331 : Blo 666309 2260331 := bstep (se 1 (by rfl) ⟨1695248, by rfl⟩ : syracuseStep 2260331 = 3390497) B3390497
theorem B3374459 : Blo 666309 3374459 := bstep (se 1 (by rfl) ⟨2530844, by rfl⟩ : syracuseStep 3374459 = 5061689) B5061689
theorem B13172183 : Blo 666309 13172183 := bstep (se 1 (by rfl) ⟨9879137, by rfl⟩ : syracuseStep 13172183 = 19758275) B19758275
theorem B1736171 : Blo 666309 1736171 := bstep (se 1 (by rfl) ⟨1302128, by rfl⟩ : syracuseStep 1736171 = 2604257) B2604257
theorem B1605241 : Blo 666309 1605241 := bstep (se 2 (by rfl) ⟨601965, by rfl⟩ : syracuseStep 1605241 = 1203931) B1203931
theorem B1507103 : Blo 666309 1507103 := bstep (se 1 (by rfl) ⟨1130327, by rfl⟩ : syracuseStep 1507103 = 2260655) B2260655
theorem B28868399 : Blo 666309 28868399 := bstep (se 1 (by rfl) ⟨21651299, by rfl⟩ : syracuseStep 28868399 = 43302599) B43302599
theorem B1507553 : Blo 666309 1507553 := bstep (se 2 (by rfl) ⟨565332, by rfl⟩ : syracuseStep 1507553 = 1130665) B1130665
theorem B1507931 : Blo 666309 1507931 := bstep (se 1 (by rfl) ⟨1130948, by rfl⟩ : syracuseStep 1507931 = 2261897) B2261897
theorem B6423425 : Blo 666309 6423425 := bstep (se 2 (by rfl) ⟨2408784, by rfl⟩ : syracuseStep 6423425 = 4817569) B4817569
theorem B3802625 : Blo 666309 3802625 := bstep (se 2 (by rfl) ⟨1425984, by rfl⟩ : syracuseStep 3802625 = 2851969) B2851969
theorem B1443511 : Blo 666309 1443511 := bstep (se 1 (by rfl) ⟨1082633, by rfl⟩ : syracuseStep 1443511 = 2165267) B2165267
theorem B5801719 : Blo 666309 5801719 := bstep (se 1 (by rfl) ⟨4351289, by rfl⟩ : syracuseStep 5801719 = 8702579) B8702579
theorem B4327519 : Blo 666309 4327519 := bstep (se 1 (by rfl) ⟨3245639, by rfl⟩ : syracuseStep 4327519 = 6491279) B6491279
theorem B1904239 : Blo 666309 1904239 := bstep (se 1 (by rfl) ⟨1428179, by rfl⟩ : syracuseStep 1904239 = 2856359) B2856359
theorem B3804833 : Blo 666309 3804833 := bstep (se 2 (by rfl) ⟨1426812, by rfl⟩ : syracuseStep 3804833 = 2853625) B2853625
theorem B2855675 : Blo 666309 2855675 := bstep (se 1 (by rfl) ⟨2141756, by rfl⟩ : syracuseStep 2855675 = 4283513) B4283513
theorem B2134991 : Blo 666309 2134991 := bstep (se 1 (by rfl) ⟨1601243, by rfl⟩ : syracuseStep 2134991 = 3202487) B3202487
theorem B21960001 : Blo 666309 21960001 := bstep (se 2 (by rfl) ⟨8235000, by rfl⟩ : syracuseStep 21960001 = 16470001) B16470001
theorem B1906267 : Blo 666309 1906267 := bstep (se 1 (by rfl) ⟨1429700, by rfl⟩ : syracuseStep 1906267 = 2859401) B2859401
theorem B2856617 : Blo 666309 2856617 := bstep (se 2 (by rfl) ⟨1071231, by rfl⟩ : syracuseStep 2856617 = 2142463) B2142463
theorem B3380939 : Blo 666309 3380939 := bstep (se 1 (by rfl) ⟨2535704, by rfl⟩ : syracuseStep 3380939 = 5071409) B5071409
theorem B2530025 : Blo 666309 2530025 := bstep (se 2 (by rfl) ⟨948759, by rfl⟩ : syracuseStep 2530025 = 1897519) B1897519
theorem B2005979 : Blo 666309 2005979 := bstep (se 1 (by rfl) ⟨1504484, by rfl⟩ : syracuseStep 2005979 = 3008969) B3008969
theorem B3809389 : Blo 666309 3809389 := bstep (se 3 (by rfl) ⟨714260, by rfl⟩ : syracuseStep 3809389 = 1428521) B1428521
theorem B2531513 : Blo 666309 2531513 := bstep (se 2 (by rfl) ⟨949317, by rfl⟩ : syracuseStep 2531513 = 1898635) B1898635
theorem B3809915 : Blo 666309 3809915 := bstep (se 1 (by rfl) ⟨2857436, by rfl⟩ : syracuseStep 3809915 = 5714873) B5714873
theorem B8561285 : Blo 666309 8561285 := bstep (se 4 (by rfl) ⟨802620, by rfl⟩ : syracuseStep 8561285 = 1605241) B1605241
theorem B3056393 : Blo 666309 3056393 := bstep (se 2 (by rfl) ⟨1146147, by rfl⟩ : syracuseStep 3056393 = 2292295) B2292295
theorem B9741341 : Blo 666309 9741341 := bstep (se 3 (by rfl) ⟨1826501, by rfl⟩ : syracuseStep 9741341 = 3653003) B3653003
theorem B5088419 : Blo 666309 5088419 := bstep (se 1 (by rfl) ⟨3816314, by rfl⟩ : syracuseStep 5088419 = 7632629) B7632629
theorem B2533139 : Blo 666309 2533139 := bstep (se 1 (by rfl) ⟨1899854, by rfl⟩ : syracuseStep 2533139 = 3799709) B3799709
theorem B7612217 : Blo 666309 7612217 := bstep (se 2 (by rfl) ⟨2854581, by rfl⟩ : syracuseStep 7612217 = 5709163) B5709163
theorem B3385151 : Blo 666309 3385151 := bstep (se 1 (by rfl) ⟨2538863, by rfl⟩ : syracuseStep 3385151 = 5077727) B5077727
theorem B10823959 : Blo 666309 10823959 := bstep (se 1 (by rfl) ⟨8117969, by rfl⟩ : syracuseStep 10823959 = 16235939) B16235939
theorem B4270391 : Blo 666309 4270391 := bstep (se 1 (by rfl) ⟨3202793, by rfl⟩ : syracuseStep 4270391 = 6405587) B6405587
theorem B1124671 : Blo 666309 1124671 := bstep (se 1 (by rfl) ⟨843503, by rfl⟩ : syracuseStep 1124671 = 1687007) B1687007
theorem B1157447 : Blo 666309 1157447 := bstep (se 1 (by rfl) ⟨868085, by rfl⟩ : syracuseStep 1157447 = 1736171) B1736171
theorem B11446757 : Blo 666309 11446757 := bstep (se 4 (by rfl) ⟨1073133, by rfl⟩ : syracuseStep 11446757 = 2146267) B2146267
theorem B19245599 : Blo 666309 19245599 := bstep (se 1 (by rfl) ⟨14434199, by rfl⟩ : syracuseStep 19245599 = 28868399) B28868399
theorem B1125083 : Blo 666309 1125083 := bstep (se 1 (by rfl) ⟨843812, by rfl⟩ : syracuseStep 1125083 = 1687625) B1687625
theorem B666395 : Blo 666309 666395 := bstep (se 1 (by rfl) ⟨499796, by rfl⟩ : syracuseStep 666395 = 999593) B999593
theorem B1354619 : Blo 666309 1354619 := bstep (se 1 (by rfl) ⟨1015964, by rfl⟩ : syracuseStep 1354619 = 2031929) B2031929
theorem B666607 : Blo 666309 666607 := bstep (se 1 (by rfl) ⟨499955, by rfl⟩ : syracuseStep 666607 = 999911) B999911
theorem B666791 : Blo 666309 666791 := bstep (se 1 (by rfl) ⟨500093, by rfl⟩ : syracuseStep 666791 = 1000187) B1000187
theorem B667087 : Blo 666309 667087 := bstep (se 1 (by rfl) ⟨500315, by rfl⟩ : syracuseStep 667087 = 1000631) B1000631
theorem B667183 : Blo 666309 667183 := bstep (se 1 (by rfl) ⟨500387, by rfl⟩ : syracuseStep 667183 = 1000775) B1000775
theorem B667247 : Blo 666309 667247 := bstep (se 1 (by rfl) ⟨500435, by rfl⟩ : syracuseStep 667247 = 1000871) B1000871
theorem B1126055 : Blo 666309 1126055 := bstep (se 1 (by rfl) ⟨844541, by rfl⟩ : syracuseStep 1126055 = 1689083) B1689083
theorem B667367 : Blo 666309 667367 := bstep (se 1 (by rfl) ⟨500525, by rfl⟩ : syracuseStep 667367 = 1001051) B1001051
theorem B1126271 : Blo 666309 1126271 := bstep (se 1 (by rfl) ⟨844703, by rfl⟩ : syracuseStep 1126271 = 1689407) B1689407
theorem B667679 : Blo 666309 667679 := bstep (se 1 (by rfl) ⟨500759, by rfl⟩ : syracuseStep 667679 = 1001519) B1001519
theorem B1126507 : Blo 666309 1126507 := bstep (se 1 (by rfl) ⟨844880, by rfl⟩ : syracuseStep 1126507 = 1689761) B1689761
theorem B667855 : Blo 666309 667855 := bstep (se 1 (by rfl) ⟨500891, by rfl⟩ : syracuseStep 667855 = 1001783) B1001783
theorem B667975 : Blo 666309 667975 := bstep (se 1 (by rfl) ⟨500981, by rfl⟩ : syracuseStep 667975 = 1001963) B1001963
theorem B9613687 : Blo 666309 9613687 := bstep (se 1 (by rfl) ⟨7210265, by rfl⟩ : syracuseStep 9613687 = 14420531) B14420531
theorem B16462217 : Blo 666309 16462217 := bstep (se 2 (by rfl) ⟨6173331, by rfl⟩ : syracuseStep 16462217 = 12346663) B12346663
theorem B668135 : Blo 666309 668135 := bstep (se 1 (by rfl) ⟨501101, by rfl⟩ : syracuseStep 668135 = 1002203) B1002203
theorem B5419507 : Blo 666309 5419507 := bstep (se 1 (by rfl) ⟨4064630, by rfl⟩ : syracuseStep 5419507 = 8129261) B8129261
theorem B668159 : Blo 666309 668159 := bstep (se 1 (by rfl) ⟨501119, by rfl⟩ : syracuseStep 668159 = 1002239) B1002239
theorem B20591495 : Blo 666309 20591495 := bstep (se 1 (by rfl) ⟨15443621, by rfl⟩ : syracuseStep 20591495 = 30887243) B30887243
theorem B668639 : Blo 666309 668639 := bstep (se 1 (by rfl) ⟨501479, by rfl⟩ : syracuseStep 668639 = 1002959) B1002959
theorem B2143219 : Blo 666309 2143219 := bstep (se 1 (by rfl) ⟨1607414, by rfl⟩ : syracuseStep 2143219 = 3214829) B3214829
theorem B668699 : Blo 666309 668699 := bstep (se 1 (by rfl) ⟨501524, by rfl⟩ : syracuseStep 668699 = 1003049) B1003049
theorem B1324127 : Blo 666309 1324127 := bstep (se 1 (by rfl) ⟨993095, by rfl⟩ : syracuseStep 1324127 = 1986191) B1986191
theorem B21116123 : Blo 666309 21116123 := bstep (se 1 (by rfl) ⟨15837092, by rfl⟩ : syracuseStep 21116123 = 31674185) B31674185
theorem B668895 : Blo 666309 668895 := bstep (se 1 (by rfl) ⟨501671, by rfl⟩ : syracuseStep 668895 = 1003343) B1003343
theorem B668975 : Blo 666309 668975 := bstep (se 1 (by rfl) ⟨501731, by rfl⟩ : syracuseStep 668975 = 1003463) B1003463
theorem B1127783 : Blo 666309 1127783 := bstep (se 1 (by rfl) ⟨845837, by rfl⟩ : syracuseStep 1127783 = 1691675) B1691675
theorem B669031 : Blo 666309 669031 := bstep (se 1 (by rfl) ⟨501773, by rfl⟩ : syracuseStep 669031 = 1003547) B1003547
theorem B669215 : Blo 666309 669215 := bstep (se 1 (by rfl) ⟨501911, by rfl⟩ : syracuseStep 669215 = 1003823) B1003823
theorem B4568609 : Blo 666309 4568609 := bstep (se 2 (by rfl) ⟨1713228, by rfl⟩ : syracuseStep 4568609 = 3426457) B3426457
theorem B669287 : Blo 666309 669287 := bstep (se 1 (by rfl) ⟨501965, by rfl⟩ : syracuseStep 669287 = 1003931) B1003931
theorem B669311 : Blo 666309 669311 := bstep (se 1 (by rfl) ⟨501983, by rfl⟩ : syracuseStep 669311 = 1003967) B1003967
theorem B1128127 : Blo 666309 1128127 := bstep (se 1 (by rfl) ⟨846095, by rfl⟩ : syracuseStep 1128127 = 1692191) B1692191
theorem B669375 : Blo 666309 669375 := bstep (se 1 (by rfl) ⟨502031, by rfl⟩ : syracuseStep 669375 = 1004063) B1004063
theorem B669567 : Blo 666309 669567 := bstep (se 1 (by rfl) ⟨502175, by rfl⟩ : syracuseStep 669567 = 1004351) B1004351
theorem B1423259 : Blo 666309 1423259 := bstep (se 1 (by rfl) ⟨1067444, by rfl⟩ : syracuseStep 1423259 = 2134889) B2134889
theorem B669663 : Blo 666309 669663 := bstep (se 1 (by rfl) ⟨502247, by rfl⟩ : syracuseStep 669663 = 1004495) B1004495
theorem B669723 : Blo 666309 669723 := bstep (se 1 (by rfl) ⟨502292, by rfl⟩ : syracuseStep 669723 = 1004585) B1004585
theorem B669743 : Blo 666309 669743 := bstep (se 1 (by rfl) ⟨502307, by rfl⟩ : syracuseStep 669743 = 1004615) B1004615
theorem B669863 : Blo 666309 669863 := bstep (se 1 (by rfl) ⟨502397, by rfl⟩ : syracuseStep 669863 = 1004795) B1004795
theorem B669903 : Blo 666309 669903 := bstep (se 1 (by rfl) ⟨502427, by rfl⟩ : syracuseStep 669903 = 1004855) B1004855
theorem B1128667 : Blo 666309 1128667 := bstep (se 1 (by rfl) ⟨846500, by rfl⟩ : syracuseStep 1128667 = 1693001) B1693001
theorem B5716271 : Blo 666309 5716271 := bstep (se 1 (by rfl) ⟨4287203, by rfl⟩ : syracuseStep 5716271 = 8574407) B8574407
theorem B670107 : Blo 666309 670107 := bstep (se 1 (by rfl) ⟨502580, by rfl⟩ : syracuseStep 670107 = 1005161) B1005161
theorem B1130105 : Blo 666309 1130105 := bstep (se 2 (by rfl) ⟨423789, by rfl⟩ : syracuseStep 1130105 = 847579) B847579
theorem B2539259 : Blo 666309 2539259 := bstep (se 1 (by rfl) ⟨1904444, by rfl⟩ : syracuseStep 2539259 = 3808889) B3808889
theorem B2539471 : Blo 666309 2539471 := bstep (se 1 (by rfl) ⟨1904603, by rfl⟩ : syracuseStep 2539471 = 3809207) B3809207
theorem B1130537 : Blo 666309 1130537 := bstep (se 2 (by rfl) ⟨423951, by rfl⟩ : syracuseStep 1130537 = 847903) B847903
theorem B10829933 : Blo 666309 10829933 := bstep (se 3 (by rfl) ⟨2030612, by rfl⟩ : syracuseStep 10829933 = 4061225) B4061225
theorem B2572457 : Blo 666309 2572457 := bstep (se 2 (by rfl) ⟨964671, by rfl⟩ : syracuseStep 2572457 = 1929343) B1929343
theorem B2539775 : Blo 666309 2539775 := bstep (se 1 (by rfl) ⟨1904831, by rfl⟩ : syracuseStep 2539775 = 3809663) B3809663
theorem B5423399 : Blo 666309 5423399 := bstep (se 1 (by rfl) ⟨4067549, by rfl⟩ : syracuseStep 5423399 = 8135099) B8135099
theorem B1687979 : Blo 666309 1687979 := bstep (se 1 (by rfl) ⟨1265984, by rfl⟩ : syracuseStep 1687979 = 2531969) B2531969
theorem B2409277 : Blo 666309 2409277 := bstep (se 3 (by rfl) ⟨451739, by rfl⟩ : syracuseStep 2409277 = 903479) B903479
theorem B3392603 : Blo 666309 3392603 := bstep (se 1 (by rfl) ⟨2544452, by rfl⟩ : syracuseStep 3392603 = 5088905) B5088905
theorem B36685001 : Blo 666309 36685001 := bstep (se 2 (by rfl) ⟨13756875, by rfl⟩ : syracuseStep 36685001 = 27513751) B27513751
theorem B1001609 : Blo 666309 1001609 := bstep (se 2 (by rfl) ⟨375603, by rfl⟩ : syracuseStep 1001609 = 751207) B751207
theorem B2542175 : Blo 666309 2542175 := bstep (se 1 (by rfl) ⟨1906631, by rfl⟩ : syracuseStep 2542175 = 3813263) B3813263
theorem B1067663 : Blo 666309 1067663 := bstep (se 1 (by rfl) ⟨800747, by rfl⟩ : syracuseStep 1067663 = 1601495) B1601495
theorem B1002191 : Blo 666309 1002191 := bstep (se 1 (by rfl) ⟨751643, by rfl⟩ : syracuseStep 1002191 = 1503287) B1503287
theorem B1002377 : Blo 666309 1002377 := bstep (se 2 (by rfl) ⟨375891, by rfl⟩ : syracuseStep 1002377 = 751783) B751783
theorem B1690591 : Blo 666309 1690591 := bstep (se 1 (by rfl) ⟨1267943, by rfl⟩ : syracuseStep 1690591 = 2535887) B2535887
theorem B1526855 : Blo 666309 1526855 := bstep (se 1 (by rfl) ⟨1145141, by rfl⟩ : syracuseStep 1526855 = 2290283) B2290283
theorem B1265051 : Blo 666309 1265051 := bstep (se 1 (by rfl) ⟨948788, by rfl⟩ : syracuseStep 1265051 = 1897577) B1897577
theorem B2543663 : Blo 666309 2543663 := bstep (se 1 (by rfl) ⟨1907747, by rfl⟩ : syracuseStep 2543663 = 3815495) B3815495
theorem B1003727 : Blo 666309 1003727 := bstep (se 1 (by rfl) ⟨752795, by rfl⟩ : syracuseStep 1003727 = 1505591) B1505591
theorem B1003847 : Blo 666309 1003847 := bstep (se 1 (by rfl) ⟨752885, by rfl⟩ : syracuseStep 1003847 = 1505771) B1505771
theorem B5722559 : Blo 666309 5722559 := bstep (se 1 (by rfl) ⟨4291919, by rfl⟩ : syracuseStep 5722559 = 8583839) B8583839
theorem B2249639 : Blo 666309 2249639 := bstep (se 1 (by rfl) ⟨1687229, by rfl⟩ : syracuseStep 2249639 = 3374459) B3374459
theorem B13685939 : Blo 666309 13685939 := bstep (se 1 (by rfl) ⟨10264454, by rfl⟩ : syracuseStep 13685939 = 20528909) B20528909
theorem B1004735 : Blo 666309 1004735 := bstep (se 1 (by rfl) ⟨753551, by rfl⟩ : syracuseStep 1004735 = 1507103) B1507103
theorem B4052663 : Blo 666309 4052663 := bstep (se 1 (by rfl) ⟨3039497, by rfl⟩ : syracuseStep 4052663 = 6078995) B6078995
theorem B10442459 : Blo 666309 10442459 := bstep (se 1 (by rfl) ⟨7831844, by rfl⟩ : syracuseStep 10442459 = 15663689) B15663689
theorem B2250503 : Blo 666309 2250503 := bstep (se 1 (by rfl) ⟨1687877, by rfl⟩ : syracuseStep 2250503 = 3375755) B3375755
theorem B2250719 : Blo 666309 2250719 := bstep (se 1 (by rfl) ⟨1688039, by rfl⟩ : syracuseStep 2250719 = 3376079) B3376079
theorem B12867761 : Blo 666309 12867761 := bstep (se 2 (by rfl) ⟨4825410, by rfl⟩ : syracuseStep 12867761 = 9650821) B9650821
theorem B23091713 : Blo 666309 23091713 := bstep (se 2 (by rfl) ⟨8659392, by rfl⟩ : syracuseStep 23091713 = 17318785) B17318785
theorem B2251367 : Blo 666309 2251367 := bstep (se 1 (by rfl) ⟨1688525, by rfl⟩ : syracuseStep 2251367 = 3377051) B3377051
theorem B2710259 : Blo 666309 2710259 := bstep (se 1 (by rfl) ⟨2032694, by rfl⟩ : syracuseStep 2710259 = 4065389) B4065389
theorem B7232327 : Blo 666309 7232327 := bstep (se 1 (by rfl) ⟨5424245, by rfl⟩ : syracuseStep 7232327 = 10848491) B10848491
theorem B1694945 : Blo 666309 1694945 := bstep (se 2 (by rfl) ⟨635604, by rfl⟩ : syracuseStep 1694945 = 1271209) B1271209
theorem B4283923 : Blo 666309 4283923 := bstep (se 1 (by rfl) ⟨3212942, by rfl⟩ : syracuseStep 4283923 = 6425885) B6425885
theorem B1695451 : Blo 666309 1695451 := bstep (se 1 (by rfl) ⟨1271588, by rfl⟩ : syracuseStep 1695451 = 2543177) B2543177
theorem B1302311 : Blo 666309 1302311 := bstep (se 1 (by rfl) ⟨976733, by rfl⟩ : syracuseStep 1302311 = 1953467) B1953467
theorem B1499327 : Blo 666309 1499327 := bstep (se 1 (by rfl) ⟨1124495, by rfl⟩ : syracuseStep 1499327 = 2248991) B2248991
theorem B2253473 : Blo 666309 2253473 := bstep (se 2 (by rfl) ⟨845052, by rfl⟩ : syracuseStep 2253473 = 1690105) B1690105
theorem B8151839 : Blo 666309 8151839 := bstep (se 1 (by rfl) ⟨6113879, by rfl⟩ : syracuseStep 8151839 = 12227759) B12227759
theorem B844607 : Blo 666309 844607 := bstep (se 1 (by rfl) ⟨633455, by rfl⟩ : syracuseStep 844607 = 1266911) B1266911
theorem B5072381 : Blo 666309 5072381 := bstep (se 3 (by rfl) ⟨951071, by rfl⟩ : syracuseStep 5072381 = 1902143) B1902143
theorem B2254337 : Blo 666309 2254337 := bstep (se 2 (by rfl) ⟨845376, by rfl⟩ : syracuseStep 2254337 = 1690753) B1690753
theorem B1140455 : Blo 666309 1140455 := bstep (se 1 (by rfl) ⟨855341, by rfl⟩ : syracuseStep 1140455 = 1710683) B1710683
theorem B3204947 : Blo 666309 3204947 := bstep (se 1 (by rfl) ⟨2403710, by rfl⟩ : syracuseStep 3204947 = 4807421) B4807421
theorem B1501055 : Blo 666309 1501055 := bstep (se 1 (by rfl) ⟨1125791, by rfl⟩ : syracuseStep 1501055 = 2251583) B2251583
theorem B2255201 : Blo 666309 2255201 := bstep (se 2 (by rfl) ⟨845700, by rfl⟩ : syracuseStep 2255201 = 1691401) B1691401
theorem B10840567 : Blo 666309 10840567 := bstep (se 1 (by rfl) ⟨8130425, by rfl⟩ : syracuseStep 10840567 = 16260851) B16260851
theorem B2255417 : Blo 666309 2255417 := bstep (se 2 (by rfl) ⟨845781, by rfl⟩ : syracuseStep 2255417 = 1691563) B1691563
theorem B1239707 : Blo 666309 1239707 := bstep (se 1 (by rfl) ⟨929780, by rfl⟩ : syracuseStep 1239707 = 1859561) B1859561
theorem B6187691 : Blo 666309 6187691 := bstep (se 1 (by rfl) ⟨4640768, by rfl⟩ : syracuseStep 6187691 = 9281537) B9281537
theorem B1502585 : Blo 666309 1502585 := bstep (se 2 (by rfl) ⟨563469, by rfl⟩ : syracuseStep 1502585 = 1126939) B1126939
theorem B3043001 : Blo 666309 3043001 := bstep (se 2 (by rfl) ⟨1141125, by rfl⟩ : syracuseStep 3043001 = 2282251) B2282251
theorem B2256929 : Blo 666309 2256929 := bstep (se 2 (by rfl) ⟨846348, by rfl⟩ : syracuseStep 2256929 = 1692697) B1692697
theorem B1503323 : Blo 666309 1503323 := bstep (se 1 (by rfl) ⟨1127492, by rfl⟩ : syracuseStep 1503323 = 2254985) B2254985
theorem B4288639 : Blo 666309 4288639 := bstep (se 1 (by rfl) ⟨3216479, by rfl⟩ : syracuseStep 4288639 = 6432959) B6432959
theorem B749983 : Blo 666309 749983 := bstep (se 1 (by rfl) ⟨562487, by rfl⟩ : syracuseStep 749983 = 1124975) B1124975
theorem B5698025 : Blo 666309 5698025 := bstep (se 2 (by rfl) ⟨2136759, by rfl⟩ : syracuseStep 5698025 = 4273519) B4273519
theorem B750127 : Blo 666309 750127 := bstep (se 1 (by rfl) ⟨562595, by rfl⟩ : syracuseStep 750127 = 1125191) B1125191
theorem B1503881 : Blo 666309 1503881 := bstep (se 2 (by rfl) ⟨563955, by rfl⟩ : syracuseStep 1503881 = 1127911) B1127911
theorem B2716631 : Blo 666309 2716631 := bstep (se 1 (by rfl) ⟨2037473, by rfl⟩ : syracuseStep 2716631 = 4074947) B4074947
theorem B3765467 : Blo 666309 3765467 := bstep (se 1 (by rfl) ⟨2824100, by rfl⟩ : syracuseStep 3765467 = 5648201) B5648201
theorem B3798251 : Blo 666309 3798251 := bstep (se 1 (by rfl) ⟨2848688, by rfl⟩ : syracuseStep 3798251 = 5697377) B5697377
theorem B2258171 : Blo 666309 2258171 := bstep (se 1 (by rfl) ⟨1693628, by rfl⟩ : syracuseStep 2258171 = 3387257) B3387257
theorem B82245689 : Blo 666309 82245689 := bstep (se 2 (by rfl) ⟨30842133, by rfl⟩ : syracuseStep 82245689 = 61684267) B61684267
theorem B1013897 : Blo 666309 1013897 := bstep (se 2 (by rfl) ⟨380211, by rfl⟩ : syracuseStep 1013897 = 760423) B760423
theorem B1899035 : Blo 666309 1899035 := bstep (se 1 (by rfl) ⟨1424276, by rfl⟩ : syracuseStep 1899035 = 2848553) B2848553
theorem B4291487 : Blo 666309 4291487 := bstep (se 1 (by rfl) ⟨3218615, by rfl⟩ : syracuseStep 4291487 = 6437231) B6437231
theorem B5700689 : Blo 666309 5700689 := bstep (se 2 (by rfl) ⟨2137758, by rfl⟩ : syracuseStep 5700689 = 4275517) B4275517
theorem B1506887 : Blo 666309 1506887 := bstep (se 1 (by rfl) ⟨1130165, by rfl⟩ : syracuseStep 1506887 = 2260331) B2260331
theorem B8781455 : Blo 666309 8781455 := bstep (se 1 (by rfl) ⟨6586091, by rfl⟩ : syracuseStep 8781455 = 13172183) B13172183
theorem B2260979 : Blo 666309 2260979 := bstep (se 1 (by rfl) ⟨1695734, by rfl⟩ : syracuseStep 2260979 = 3391469) B3391469
theorem B753691 : Blo 666309 753691 := bstep (se 1 (by rfl) ⟨565268, by rfl⟩ : syracuseStep 753691 = 1130537) B1130537
theorem B5079185 : Blo 666309 5079185 := bstep (se 2 (by rfl) ⟨1904694, by rfl⟩ : syracuseStep 5079185 = 3809389) B3809389
theorem B2261735 : Blo 666309 2261735 := bstep (se 1 (by rfl) ⟨1696301, by rfl⟩ : syracuseStep 2261735 = 3392603) B3392603
theorem B16286453 : Blo 666309 16286453 := bstep (se 5 (by rfl) ⟨763427, by rfl⟩ : syracuseStep 16286453 = 1526855) B1526855
theorem B3212369 : Blo 666309 3212369 := bstep (se 2 (by rfl) ⟨1204638, by rfl⟩ : syracuseStep 3212369 = 2409277) B2409277
theorem B7735625 : Blo 666309 7735625 := bstep (se 2 (by rfl) ⟨2900859, by rfl⟩ : syracuseStep 7735625 = 5801719) B5801719
theorem B5770025 : Blo 666309 5770025 := bstep (se 2 (by rfl) ⟨2163759, by rfl⟩ : syracuseStep 5770025 = 4327519) B4327519
theorem B14454089 : Blo 666309 14454089 := bstep (se 2 (by rfl) ⟨5420283, by rfl⟩ : syracuseStep 14454089 = 10840567) B10840567
theorem B1904411 : Blo 666309 1904411 := bstep (se 1 (by rfl) ⟨1428308, by rfl⟩ : syracuseStep 1904411 = 2856617) B2856617
theorem B1806839 : Blo 666309 1806839 := bstep (se 1 (by rfl) ⟨1355129, by rfl⟩ : syracuseStep 1806839 = 2710259) B2710259
theorem B4821551 : Blo 666309 4821551 := bstep (se 1 (by rfl) ⟨3616163, by rfl⟩ : syracuseStep 4821551 = 7232327) B7232327
theorem B5707523 : Blo 666309 5707523 := bstep (se 1 (by rfl) ⟨4280642, by rfl⟩ : syracuseStep 5707523 = 8561285) B8561285
theorem B12818249 : Blo 666309 12818249 := bstep (se 2 (by rfl) ⟨4806843, by rfl⟩ : syracuseStep 12818249 = 9613687) B9613687
theorem B3086525 : Blo 666309 3086525 := bstep (se 3 (by rfl) ⟨578723, by rfl⟩ : syracuseStep 3086525 = 1157447) B1157447
theorem B3381587 : Blo 666309 3381587 := bstep (se 1 (by rfl) ⟨2536190, by rfl⟩ : syracuseStep 3381587 = 5072381) B5072381
theorem B760303 : Blo 666309 760303 := bstep (se 1 (by rfl) ⟨570227, by rfl⟩ : syracuseStep 760303 = 1140455) B1140455
theorem B2136631 : Blo 666309 2136631 := bstep (se 1 (by rfl) ⟨1602473, by rfl⟩ : syracuseStep 2136631 = 3204947) B3204947
theorem B2857625 : Blo 666309 2857625 := bstep (se 2 (by rfl) ⟨1071609, by rfl⟩ : syracuseStep 2857625 = 2143219) B2143219
theorem B826471 : Blo 666309 826471 := bstep (se 1 (by rfl) ⟨619853, by rfl⟩ : syracuseStep 826471 = 1239707) B1239707
theorem B5349277 : Blo 666309 5349277 := bstep (se 3 (by rfl) ⟨1002989, by rfl⟩ : syracuseStep 5349277 = 2005979) B2005979
theorem B1811087 : Blo 666309 1811087 := bstep (se 1 (by rfl) ⟨1358315, by rfl⟩ : syracuseStep 1811087 = 2716631) B2716631
theorem B2532167 : Blo 666309 2532167 := bstep (se 1 (by rfl) ⟨1899125, by rfl⟩ : syracuseStep 2532167 = 3798251) B3798251
theorem B54830459 : Blo 666309 54830459 := bstep (se 1 (by rfl) ⟨41122844, by rfl⟩ : syracuseStep 54830459 = 82245689) B82245689
theorem B3810847 : Blo 666309 3810847 := bstep (se 1 (by rfl) ⟨2858135, by rfl⟩ : syracuseStep 3810847 = 5716271) B5716271
theorem B2860991 : Blo 666309 2860991 := bstep (se 1 (by rfl) ⟨2145743, by rfl⟩ : syracuseStep 2860991 = 4291487) B4291487
theorem B5711897 : Blo 666309 5711897 := bstep (se 2 (by rfl) ⟨2141961, by rfl⟩ : syracuseStep 5711897 = 4283923) B4283923
theorem B3385961 : Blo 666309 3385961 := bstep (se 2 (by rfl) ⟨1269735, by rfl⟩ : syracuseStep 3385961 = 2539471) B2539471
theorem B7219955 : Blo 666309 7219955 := bstep (se 1 (by rfl) ⟨5414966, by rfl⟩ : syracuseStep 7219955 = 10829933) B10829933
theorem B3615599 : Blo 666309 3615599 := bstep (se 1 (by rfl) ⟨2711699, by rfl⟩ : syracuseStep 3615599 = 5423399) B5423399
theorem B1125319 : Blo 666309 1125319 := bstep (se 1 (by rfl) ⟨843989, by rfl⟩ : syracuseStep 1125319 = 1687979) B1687979
theorem B6859885 : Blo 666309 6859885 := bstep (se 3 (by rfl) ⟨1286228, by rfl⟩ : syracuseStep 6859885 = 2572457) B2572457
theorem B24456667 : Blo 666309 24456667 := bstep (se 1 (by rfl) ⟨18342500, by rfl⟩ : syracuseStep 24456667 = 36685001) B36685001
theorem B2535083 : Blo 666309 2535083 := bstep (se 1 (by rfl) ⟨1901312, by rfl⟩ : syracuseStep 2535083 = 3802625) B3802625
theorem B667739 : Blo 666309 667739 := bstep (se 1 (by rfl) ⟨500804, by rfl⟩ : syracuseStep 667739 = 1001609) B1001609
theorem B668127 : Blo 666309 668127 := bstep (se 1 (by rfl) ⟨501095, by rfl⟩ : syracuseStep 668127 = 1002191) B1002191
theorem B668251 : Blo 666309 668251 := bstep (se 1 (by rfl) ⟨501188, by rfl⟩ : syracuseStep 668251 = 1002377) B1002377
theorem B7615133 : Blo 666309 7615133 := bstep (se 3 (by rfl) ⟨1427837, by rfl⟩ : syracuseStep 7615133 = 2855675) B2855675
theorem B2536555 : Blo 666309 2536555 := bstep (se 1 (by rfl) ⟨1902416, by rfl⟩ : syracuseStep 2536555 = 3804833) B3804833
theorem B669151 : Blo 666309 669151 := bstep (se 1 (by rfl) ⟨501863, by rfl⟩ : syracuseStep 669151 = 1003727) B1003727
theorem B669231 : Blo 666309 669231 := bstep (se 1 (by rfl) ⟨501923, by rfl⟩ : syracuseStep 669231 = 1003847) B1003847
theorem B3815039 : Blo 666309 3815039 := bstep (se 1 (by rfl) ⟨2861279, by rfl⟩ : syracuseStep 3815039 = 5722559) B5722559
theorem B14431945 : Blo 666309 14431945 := bstep (se 2 (by rfl) ⟨5411979, by rfl⟩ : syracuseStep 14431945 = 10823959) B10823959
theorem B10041245 : Blo 666309 10041245 := bstep (se 3 (by rfl) ⟨1882733, by rfl⟩ : syracuseStep 10041245 = 3765467) B3765467
theorem B1507319 : Blo 666309 1507319 := bstep (se 1 (by rfl) ⟨1130489, by rfl⟩ : syracuseStep 1507319 = 2260979) B2260979
theorem B1423327 : Blo 666309 1423327 := bstep (se 1 (by rfl) ⟨1067495, by rfl⟩ : syracuseStep 1423327 = 2134991) B2134991
theorem B9123959 : Blo 666309 9123959 := bstep (se 1 (by rfl) ⟨6842969, by rfl⟩ : syracuseStep 9123959 = 13685939) B13685939
theorem B669823 : Blo 666309 669823 := bstep (se 1 (by rfl) ⟨502367, by rfl⟩ : syracuseStep 669823 = 1004735) B1004735
theorem B2701775 : Blo 666309 2701775 := bstep (se 1 (by rfl) ⟨2026331, by rfl⟩ : syracuseStep 2701775 = 4052663) B4052663
theorem B6961639 : Blo 666309 6961639 := bstep (se 1 (by rfl) ⟨5221229, by rfl⟩ : syracuseStep 6961639 = 10442459) B10442459
theorem B1686683 : Blo 666309 1686683 := bstep (se 1 (by rfl) ⟨1265012, by rfl⟩ : syracuseStep 1686683 = 2530025) B2530025
theorem B2538985 : Blo 666309 2538985 := bstep (se 2 (by rfl) ⟨952119, by rfl⟩ : syracuseStep 2538985 = 1904239) B1904239
theorem B1129963 : Blo 666309 1129963 := bstep (se 1 (by rfl) ⟨847472, by rfl⟩ : syracuseStep 1129963 = 1694945) B1694945
theorem B868207 : Blo 666309 868207 := bstep (se 1 (by rfl) ⟨651155, by rfl⟩ : syracuseStep 868207 = 1302311) B1302311
theorem B1687675 : Blo 666309 1687675 := bstep (se 1 (by rfl) ⟨1265756, by rfl⟩ : syracuseStep 1687675 = 2531513) B2531513
theorem B999551 : Blo 666309 999551 := bstep (se 1 (by rfl) ⟨749663, by rfl⟩ : syracuseStep 999551 = 1499327) B1499327
theorem B5718185 : Blo 666309 5718185 := bstep (se 2 (by rfl) ⟨2144319, by rfl⟩ : syracuseStep 5718185 = 4288639) B4288639
theorem B2703725 : Blo 666309 2703725 := bstep (se 3 (by rfl) ⟨506948, by rfl⟩ : syracuseStep 2703725 = 1013897) B1013897
theorem B2539943 : Blo 666309 2539943 := bstep (se 1 (by rfl) ⟨1904957, by rfl⟩ : syracuseStep 2539943 = 3809915) B3809915
theorem B999977 : Blo 666309 999977 := bstep (se 2 (by rfl) ⟨374991, by rfl⟩ : syracuseStep 999977 = 749983) B749983
theorem B7226009 : Blo 666309 7226009 := bstep (se 2 (by rfl) ⟨2709753, by rfl⟩ : syracuseStep 7226009 = 5419507) B5419507
theorem B1000169 : Blo 666309 1000169 := bstep (se 2 (by rfl) ⟨375063, by rfl⟩ : syracuseStep 1000169 = 750127) B750127
theorem B3392279 : Blo 666309 3392279 := bstep (se 1 (by rfl) ⟨2544209, by rfl⟩ : syracuseStep 3392279 = 5088419) B5088419
theorem B1688759 : Blo 666309 1688759 := bstep (se 1 (by rfl) ⟨1266569, by rfl⟩ : syracuseStep 1688759 = 2533139) B2533139
theorem B1000703 : Blo 666309 1000703 := bstep (se 1 (by rfl) ⟨750527, by rfl⟩ : syracuseStep 1000703 = 1501055) B1501055
theorem B12830399 : Blo 666309 12830399 := bstep (se 1 (by rfl) ⟨9622799, by rfl⟩ : syracuseStep 12830399 = 19245599) B19245599
theorem B29280001 : Blo 666309 29280001 := bstep (se 2 (by rfl) ⟨10980000, by rfl⟩ : syracuseStep 29280001 = 21960001) B21960001
theorem B903079 : Blo 666309 903079 := bstep (se 1 (by rfl) ⟨677309, by rfl⟩ : syracuseStep 903079 = 1354619) B1354619
theorem B2541689 : Blo 666309 2541689 := bstep (se 2 (by rfl) ⟨953133, by rfl⟩ : syracuseStep 2541689 = 1906267) B1906267
theorem B1001723 : Blo 666309 1001723 := bstep (se 1 (by rfl) ⟨751292, by rfl⟩ : syracuseStep 1001723 = 1502585) B1502585
theorem B1002215 : Blo 666309 1002215 := bstep (se 1 (by rfl) ⟨751661, by rfl⟩ : syracuseStep 1002215 = 1503323) B1503323
theorem B1002587 : Blo 666309 1002587 := bstep (se 1 (by rfl) ⟨751940, by rfl⟩ : syracuseStep 1002587 = 1503881) B1503881
theorem B14077415 : Blo 666309 14077415 := bstep (se 1 (by rfl) ⟨10558061, by rfl⟩ : syracuseStep 14077415 = 21116123) B21116123
theorem B1266023 : Blo 666309 1266023 := bstep (se 1 (by rfl) ⟨949517, by rfl⟩ : syracuseStep 1266023 = 1899035) B1899035
theorem B1004591 : Blo 666309 1004591 := bstep (se 1 (by rfl) ⟨753443, by rfl⟩ : syracuseStep 1004591 = 1506887) B1506887
theorem B5854303 : Blo 666309 5854303 := bstep (se 1 (by rfl) ⟨4390727, by rfl⟩ : syracuseStep 5854303 = 8781455) B8781455
theorem B1692839 : Blo 666309 1692839 := bstep (se 1 (by rfl) ⟨1269629, by rfl⟩ : syracuseStep 1692839 = 2539259) B2539259
theorem B1005035 : Blo 666309 1005035 := bstep (se 1 (by rfl) ⟨753776, by rfl⟩ : syracuseStep 1005035 = 1507553) B1507553
theorem B1693183 : Blo 666309 1693183 := bstep (se 1 (by rfl) ⟨1269887, by rfl⟩ : syracuseStep 1693183 = 2539775) B2539775
theorem B1005287 : Blo 666309 1005287 := bstep (se 1 (by rfl) ⟨753965, by rfl⟩ : syracuseStep 1005287 = 1507931) B1507931
theorem B4282283 : Blo 666309 4282283 := bstep (se 1 (by rfl) ⟨3211712, by rfl⟩ : syracuseStep 4282283 = 6423425) B6423425
theorem B1694783 : Blo 666309 1694783 := bstep (se 1 (by rfl) ⟨1271087, by rfl⟩ : syracuseStep 1694783 = 2542175) B2542175
theorem B711775 : Blo 666309 711775 := bstep (se 1 (by rfl) ⟨533831, by rfl⟩ : syracuseStep 711775 = 1067663) B1067663
theorem B8150381 : Blo 666309 8150381 := bstep (se 3 (by rfl) ⟨1528196, by rfl⟩ : syracuseStep 8150381 = 3056393) B3056393
theorem B2252285 : Blo 666309 2252285 := bstep (se 3 (by rfl) ⟨422303, by rfl⟩ : syracuseStep 2252285 = 844607) B844607
theorem B1924681 : Blo 666309 1924681 := bstep (se 2 (by rfl) ⟨721755, by rfl⟩ : syracuseStep 1924681 = 1443511) B1443511
theorem B843367 : Blo 666309 843367 := bstep (se 1 (by rfl) ⟨632525, by rfl⟩ : syracuseStep 843367 = 1265051) B1265051
theorem B1695775 : Blo 666309 1695775 := bstep (se 1 (by rfl) ⟨1271831, by rfl⟩ : syracuseStep 1695775 = 2543663) B2543663
theorem B25976909 : Blo 666309 25976909 := bstep (se 3 (by rfl) ⟨4870670, by rfl⟩ : syracuseStep 25976909 = 9741341) B9741341
theorem B3531005 : Blo 666309 3531005 := bstep (se 3 (by rfl) ⟨662063, by rfl⟩ : syracuseStep 3531005 = 1324127) B1324127
theorem B1499561 : Blo 666309 1499561 := bstep (se 2 (by rfl) ⟨562335, by rfl⟩ : syracuseStep 1499561 = 1124671) B1124671
theorem B1499759 : Blo 666309 1499759 := bstep (se 1 (by rfl) ⟨1124819, by rfl⟩ : syracuseStep 1499759 = 2249639) B2249639
theorem B2253959 : Blo 666309 2253959 := bstep (se 1 (by rfl) ⟨1690469, by rfl⟩ : syracuseStep 2253959 = 3380939) B3380939
theorem B1500335 : Blo 666309 1500335 := bstep (se 1 (by rfl) ⟨1125251, by rfl⟩ : syracuseStep 1500335 = 2250503) B2250503
theorem B2254121 : Blo 666309 2254121 := bstep (se 2 (by rfl) ⟨845295, by rfl⟩ : syracuseStep 2254121 = 1690591) B1690591
theorem B1500479 : Blo 666309 1500479 := bstep (se 1 (by rfl) ⟨1125359, by rfl⟩ : syracuseStep 1500479 = 2250719) B2250719
theorem B12182957 : Blo 666309 12182957 := bstep (se 3 (by rfl) ⟨2284304, by rfl⟩ : syracuseStep 12182957 = 4568609) B4568609
theorem B8578507 : Blo 666309 8578507 := bstep (se 1 (by rfl) ⟨6433880, by rfl⟩ : syracuseStep 8578507 = 12867761) B12867761
theorem B15394475 : Blo 666309 15394475 := bstep (se 1 (by rfl) ⟨11545856, by rfl⟩ : syracuseStep 15394475 = 23091713) B23091713
theorem B1500911 : Blo 666309 1500911 := bstep (se 1 (by rfl) ⟨1125683, by rfl⟩ : syracuseStep 1500911 = 2251367) B2251367
theorem B1502009 : Blo 666309 1502009 := bstep (se 2 (by rfl) ⟨563253, by rfl⟩ : syracuseStep 1502009 = 1126507) B1126507
theorem B1502315 : Blo 666309 1502315 := bstep (se 1 (by rfl) ⟨1126736, by rfl⟩ : syracuseStep 1502315 = 2253473) B2253473
theorem B5434559 : Blo 666309 5434559 := bstep (se 1 (by rfl) ⟨4075919, by rfl⟩ : syracuseStep 5434559 = 8151839) B8151839
theorem B1502891 : Blo 666309 1502891 := bstep (se 1 (by rfl) ⟨1127168, by rfl⟩ : syracuseStep 1502891 = 2254337) B2254337
theorem B5074811 : Blo 666309 5074811 := bstep (se 1 (by rfl) ⟨3806108, by rfl⟩ : syracuseStep 5074811 = 7612217) B7612217
theorem B2256767 : Blo 666309 2256767 := bstep (se 1 (by rfl) ⟨1692575, by rfl⟩ : syracuseStep 2256767 = 3385151) B3385151
theorem B2846927 : Blo 666309 2846927 := bstep (se 1 (by rfl) ⟨2135195, by rfl⟩ : syracuseStep 2846927 = 4270391) B4270391
theorem B1503467 : Blo 666309 1503467 := bstep (se 1 (by rfl) ⟨1127600, by rfl⟩ : syracuseStep 1503467 = 2255201) B2255201
theorem B7631171 : Blo 666309 7631171 := bstep (se 1 (by rfl) ⟨5723378, by rfl⟩ : syracuseStep 7631171 = 11446757) B11446757
theorem B1503611 : Blo 666309 1503611 := bstep (se 1 (by rfl) ⟨1127708, by rfl⟩ : syracuseStep 1503611 = 2255417) B2255417
theorem B4125127 : Blo 666309 4125127 := bstep (se 1 (by rfl) ⟨3093845, by rfl⟩ : syracuseStep 4125127 = 6187691) B6187691
theorem B750055 : Blo 666309 750055 := bstep (se 1 (by rfl) ⟨562541, by rfl⟩ : syracuseStep 750055 = 1125083) B1125083
theorem B1504169 : Blo 666309 1504169 := bstep (se 2 (by rfl) ⟨564063, by rfl⟩ : syracuseStep 1504169 = 1128127) B1128127
theorem B750703 : Blo 666309 750703 := bstep (se 1 (by rfl) ⟨563027, by rfl⟩ : syracuseStep 750703 = 1126055) B1126055
theorem B2028667 : Blo 666309 2028667 := bstep (se 1 (by rfl) ⟨1521500, by rfl⟩ : syracuseStep 2028667 = 3043001) B3043001
theorem B750847 : Blo 666309 750847 := bstep (se 1 (by rfl) ⟨563135, by rfl⟩ : syracuseStep 750847 = 1126271) B1126271
theorem B1504619 : Blo 666309 1504619 := bstep (se 1 (by rfl) ⟨1128464, by rfl⟩ : syracuseStep 1504619 = 2256929) B2256929
theorem B10974811 : Blo 666309 10974811 := bstep (se 1 (by rfl) ⟨8231108, by rfl⟩ : syracuseStep 10974811 = 16462217) B16462217
theorem B1504889 : Blo 666309 1504889 := bstep (se 2 (by rfl) ⟨564333, by rfl⟩ : syracuseStep 1504889 = 1128667) B1128667
theorem B3798683 : Blo 666309 3798683 := bstep (se 1 (by rfl) ⟨2849012, by rfl⟩ : syracuseStep 3798683 = 5698025) B5698025
theorem B13727663 : Blo 666309 13727663 := bstep (se 1 (by rfl) ⟨10295747, by rfl⟩ : syracuseStep 13727663 = 20591495) B20591495
theorem B1505447 : Blo 666309 1505447 := bstep (se 1 (by rfl) ⟨1129085, by rfl⟩ : syracuseStep 1505447 = 2258171) B2258171
theorem B751855 : Blo 666309 751855 := bstep (se 1 (by rfl) ⟨563891, by rfl⟩ : syracuseStep 751855 = 1127783) B1127783
theorem B948839 : Blo 666309 948839 := bstep (se 1 (by rfl) ⟨711629, by rfl⟩ : syracuseStep 948839 = 1423259) B1423259
theorem B3800459 : Blo 666309 3800459 := bstep (se 1 (by rfl) ⟨2850344, by rfl⟩ : syracuseStep 3800459 = 5700689) B5700689
theorem B2260601 : Blo 666309 2260601 := bstep (se 2 (by rfl) ⟨847725, by rfl⟩ : syracuseStep 2260601 = 1695451) B1695451
theorem B753403 : Blo 666309 753403 := bstep (se 1 (by rfl) ⟨565052, by rfl⟩ : syracuseStep 753403 = 1130105) B1130105
theorem B2261033 : Blo 666309 2261033 := bstep (se 2 (by rfl) ⟨847887, by rfl⟩ : syracuseStep 2261033 = 1695775) B1695775
theorem B69271757 : Blo 666309 69271757 := bstep (se 3 (by rfl) ⟨12988454, by rfl⟩ : syracuseStep 69271757 = 25976909) B25976909
theorem B1802483 : Blo 666309 1802483 := bstep (se 1 (by rfl) ⟨1351862, by rfl⟩ : syracuseStep 1802483 = 2703725) B2703725
theorem B4817339 : Blo 666309 4817339 := bstep (se 1 (by rfl) ⟨3613004, by rfl⟩ : syracuseStep 4817339 = 7226009) B7226009
theorem B1507823 : Blo 666309 1507823 := bstep (se 1 (by rfl) ⟨1130867, by rfl⟩ : syracuseStep 1507823 = 2261735) B2261735
theorem B2261519 : Blo 666309 2261519 := bstep (se 1 (by rfl) ⟨1696139, by rfl⟩ : syracuseStep 2261519 = 3392279) B3392279
theorem B8553599 : Blo 666309 8553599 := bstep (se 1 (by rfl) ⟨6415199, by rfl⟩ : syracuseStep 8553599 = 12830399) B12830399
theorem B11438009 : Blo 666309 11438009 := bstep (se 2 (by rfl) ⟨4289253, by rfl⟩ : syracuseStep 11438009 = 8578507) B8578507
theorem B5081129 : Blo 666309 5081129 := bstep (se 2 (by rfl) ⟨1905423, by rfl⟩ : syracuseStep 5081129 = 3810847) B3810847
theorem B9636059 : Blo 666309 9636059 := bstep (se 1 (by rfl) ⟨7227044, by rfl⟩ : syracuseStep 9636059 = 14454089) B14454089
theorem B3214367 : Blo 666309 3214367 := bstep (se 1 (by rfl) ⟨2410775, by rfl⟩ : syracuseStep 3214367 = 4821551) B4821551
theorem B3805015 : Blo 666309 3805015 := bstep (se 1 (by rfl) ⟨2853761, by rfl⟩ : syracuseStep 3805015 = 5707523) B5707523
theorem B2854855 : Blo 666309 2854855 := bstep (se 1 (by rfl) ⟨2141141, by rfl⟩ : syracuseStep 2854855 = 4282283) B4282283
theorem B9146513 : Blo 666309 9146513 := bstep (se 2 (by rfl) ⟨3429942, by rfl⟩ : syracuseStep 9146513 = 6859885) B6859885
theorem B1905083 : Blo 666309 1905083 := bstep (se 1 (by rfl) ⟨1428812, by rfl⟩ : syracuseStep 1905083 = 2857625) B2857625
theorem B32608889 : Blo 666309 32608889 := bstep (se 2 (by rfl) ⟨12228333, by rfl⟩ : syracuseStep 32608889 = 24456667) B24456667
theorem B10262983 : Blo 666309 10262983 := bstep (se 1 (by rfl) ⟨7697237, by rfl⟩ : syracuseStep 10262983 = 15394475) B15394475
theorem B1907327 : Blo 666309 1907327 := bstep (se 1 (by rfl) ⟨1430495, by rfl⟩ : syracuseStep 1907327 = 2860991) B2860991
theorem B3807931 : Blo 666309 3807931 := bstep (se 1 (by rfl) ⟨2855948, by rfl⟩ : syracuseStep 3807931 = 5711897) B5711897
theorem B7805737 : Blo 666309 7805737 := bstep (se 2 (by rfl) ⟨2927151, by rfl⟩ : syracuseStep 7805737 = 5854303) B5854303
theorem B3382073 : Blo 666309 3382073 := bstep (se 2 (by rfl) ⟨1268277, by rfl⟩ : syracuseStep 3382073 = 2536555) B2536555
theorem B2530237 : Blo 666309 2530237 := bstep (se 3 (by rfl) ⟨474419, by rfl⟩ : syracuseStep 2530237 = 948839) B948839
theorem B19242593 : Blo 666309 19242593 := bstep (se 2 (by rfl) ⟨7215972, by rfl⟩ : syracuseStep 19242593 = 14431945) B14431945
theorem B3383207 : Blo 666309 3383207 := bstep (se 1 (by rfl) ⟨2537405, by rfl⟩ : syracuseStep 3383207 = 5074811) B5074811
theorem B5087447 : Blo 666309 5087447 := bstep (se 1 (by rfl) ⟨3815585, by rfl⟩ : syracuseStep 5087447 = 7631171) B7631171
theorem B9282185 : Blo 666309 9282185 := bstep (se 2 (by rfl) ⟨3480819, by rfl⟩ : syracuseStep 9282185 = 6961639) B6961639
theorem B2532455 : Blo 666309 2532455 := bstep (se 1 (by rfl) ⟨1899341, by rfl⟩ : syracuseStep 2532455 = 3798683) B3798683
theorem B6694163 : Blo 666309 6694163 := bstep (se 1 (by rfl) ⟨5020622, by rfl⟩ : syracuseStep 6694163 = 10041245) B10041245
theorem B9151775 : Blo 666309 9151775 := bstep (se 1 (by rfl) ⟨6863831, by rfl⟩ : syracuseStep 9151775 = 13727663) B13727663
theorem B3385313 : Blo 666309 3385313 := bstep (se 2 (by rfl) ⟨1269492, by rfl⟩ : syracuseStep 3385313 = 2538985) B2538985
theorem B2566241 : Blo 666309 2566241 := bstep (se 2 (by rfl) ⟨962340, by rfl⟩ : syracuseStep 2566241 = 1924681) B1924681
theorem B1124455 : Blo 666309 1124455 := bstep (se 1 (by rfl) ⟨843341, by rfl⟩ : syracuseStep 1124455 = 1686683) B1686683
theorem B1124489 : Blo 666309 1124489 := bstep (se 2 (by rfl) ⟨421683, by rfl⟩ : syracuseStep 1124489 = 843367) B843367
theorem B2533639 : Blo 666309 2533639 := bstep (se 1 (by rfl) ⟨1900229, by rfl⟩ : syracuseStep 2533639 = 3800459) B3800459
theorem B1157609 : Blo 666309 1157609 := bstep (se 2 (by rfl) ⟨434103, by rfl⟩ : syracuseStep 1157609 = 868207) B868207
theorem B666367 : Blo 666309 666367 := bstep (se 1 (by rfl) ⟨499775, by rfl⟩ : syracuseStep 666367 = 999551) B999551
theorem B3386123 : Blo 666309 3386123 := bstep (se 1 (by rfl) ⟨2539592, by rfl⟩ : syracuseStep 3386123 = 5079185) B5079185
theorem B3812123 : Blo 666309 3812123 := bstep (se 1 (by rfl) ⟨2859092, by rfl⟩ : syracuseStep 3812123 = 5718185) B5718185
theorem B666651 : Blo 666309 666651 := bstep (se 1 (by rfl) ⟨499988, by rfl⟩ : syracuseStep 666651 = 999977) B999977
theorem B666779 : Blo 666309 666779 := bstep (se 1 (by rfl) ⟨500084, by rfl⟩ : syracuseStep 666779 = 1000169) B1000169
theorem B10857635 : Blo 666309 10857635 := bstep (se 1 (by rfl) ⟨8143226, by rfl⟩ : syracuseStep 10857635 = 16286453) B16286453
theorem B2141579 : Blo 666309 2141579 := bstep (se 1 (by rfl) ⟨1606184, by rfl⟩ : syracuseStep 2141579 = 3212369) B3212369
theorem B1125839 : Blo 666309 1125839 := bstep (se 1 (by rfl) ⟨844379, by rfl⟩ : syracuseStep 1125839 = 1688759) B1688759
theorem B667135 : Blo 666309 667135 := bstep (se 1 (by rfl) ⟨500351, by rfl⟩ : syracuseStep 667135 = 1000703) B1000703
theorem B667815 : Blo 666309 667815 := bstep (se 1 (by rfl) ⟨500861, by rfl⟩ : syracuseStep 667815 = 1001723) B1001723
theorem B5157083 : Blo 666309 5157083 := bstep (se 1 (by rfl) ⟨3867812, by rfl⟩ : syracuseStep 5157083 = 7735625) B7735625
theorem B668143 : Blo 666309 668143 := bstep (se 1 (by rfl) ⟨501107, by rfl⟩ : syracuseStep 668143 = 1002215) B1002215
theorem B3846683 : Blo 666309 3846683 := bstep (se 1 (by rfl) ⟨2885012, by rfl⟩ : syracuseStep 3846683 = 5770025) B5770025
theorem B668391 : Blo 666309 668391 := bstep (se 1 (by rfl) ⟨501293, by rfl⟩ : syracuseStep 668391 = 1002587) B1002587
theorem B39040001 : Blo 666309 39040001 := bstep (se 2 (by rfl) ⟨14640000, by rfl⟩ : syracuseStep 39040001 = 29280001) B29280001
theorem B669727 : Blo 666309 669727 := bstep (se 1 (by rfl) ⟨502295, by rfl⟩ : syracuseStep 669727 = 1004591) B1004591
theorem B1128559 : Blo 666309 1128559 := bstep (se 1 (by rfl) ⟨846419, by rfl⟩ : syracuseStep 1128559 = 1692839) B1692839
theorem B670023 : Blo 666309 670023 := bstep (se 1 (by rfl) ⟨502517, by rfl⟩ : syracuseStep 670023 = 1005035) B1005035
theorem B670191 : Blo 666309 670191 := bstep (se 1 (by rfl) ⟨502643, by rfl⟩ : syracuseStep 670191 = 1005287) B1005287
theorem B1129855 : Blo 666309 1129855 := bstep (se 1 (by rfl) ⟨847391, by rfl⟩ : syracuseStep 1129855 = 1694783) B1694783
theorem B999707 : Blo 666309 999707 := bstep (se 1 (by rfl) ⟨749780, by rfl⟩ : syracuseStep 999707 = 1499561) B1499561
theorem B24330557 : Blo 666309 24330557 := bstep (se 3 (by rfl) ⟨4561979, by rfl⟩ : syracuseStep 24330557 = 9123959) B9123959
theorem B999839 : Blo 666309 999839 := bstep (se 1 (by rfl) ⟨749879, by rfl⟩ : syracuseStep 999839 = 1499759) B1499759
theorem B1688111 : Blo 666309 1688111 := bstep (se 1 (by rfl) ⟨1266083, by rfl⟩ : syracuseStep 1688111 = 2532167) B2532167
theorem B1000073 : Blo 666309 1000073 := bstep (se 2 (by rfl) ⟨375027, by rfl⟩ : syracuseStep 1000073 = 750055) B750055
theorem B1000223 : Blo 666309 1000223 := bstep (se 1 (by rfl) ⟨750167, by rfl⟩ : syracuseStep 1000223 = 1500335) B1500335
theorem B1000319 : Blo 666309 1000319 := bstep (se 1 (by rfl) ⟨750239, by rfl⟩ : syracuseStep 1000319 = 1500479) B1500479
theorem B36553639 : Blo 666309 36553639 := bstep (se 1 (by rfl) ⟨27415229, by rfl⟩ : syracuseStep 36553639 = 54830459) B54830459
theorem B1000607 : Blo 666309 1000607 := bstep (se 1 (by rfl) ⟨750455, by rfl⟩ : syracuseStep 1000607 = 1500911) B1500911
theorem B1000937 : Blo 666309 1000937 := bstep (se 2 (by rfl) ⟨375351, by rfl⟩ : syracuseStep 1000937 = 750703) B750703
theorem B2704889 : Blo 666309 2704889 := bstep (se 2 (by rfl) ⟨1014333, by rfl⟩ : syracuseStep 2704889 = 2028667) B2028667
theorem B1001129 : Blo 666309 1001129 := bstep (se 2 (by rfl) ⟨375423, by rfl⟩ : syracuseStep 1001129 = 750847) B750847
theorem B1001339 : Blo 666309 1001339 := bstep (se 1 (by rfl) ⟨751004, by rfl⟩ : syracuseStep 1001339 = 1502009) B1502009
theorem B2410399 : Blo 666309 2410399 := bstep (se 1 (by rfl) ⟨1807799, by rfl⟩ : syracuseStep 2410399 = 3615599) B3615599
theorem B1001543 : Blo 666309 1001543 := bstep (se 1 (by rfl) ⟨751157, by rfl⟩ : syracuseStep 1001543 = 1502315) B1502315
theorem B14633081 : Blo 666309 14633081 := bstep (se 2 (by rfl) ⟨5487405, by rfl⟩ : syracuseStep 14633081 = 10974811) B10974811
theorem B3623039 : Blo 666309 3623039 := bstep (se 1 (by rfl) ⟨2717279, by rfl⟩ : syracuseStep 3623039 = 5434559) B5434559
theorem B1690055 : Blo 666309 1690055 := bstep (se 1 (by rfl) ⟨1267541, by rfl⟩ : syracuseStep 1690055 = 2535083) B2535083
theorem B1001927 : Blo 666309 1001927 := bstep (se 1 (by rfl) ⟨751445, by rfl⟩ : syracuseStep 1001927 = 1502891) B1502891
theorem B1002311 : Blo 666309 1002311 := bstep (se 1 (by rfl) ⟨751733, by rfl⟩ : syracuseStep 1002311 = 1503467) B1503467
theorem B1002407 : Blo 666309 1002407 := bstep (se 1 (by rfl) ⟨751805, by rfl⟩ : syracuseStep 1002407 = 1503611) B1503611
theorem B1002473 : Blo 666309 1002473 := bstep (se 2 (by rfl) ⟨375927, by rfl⟩ : syracuseStep 1002473 = 751855) B751855
theorem B1002779 : Blo 666309 1002779 := bstep (se 1 (by rfl) ⟨752084, by rfl⟩ : syracuseStep 1002779 = 1504169) B1504169
theorem B1003079 : Blo 666309 1003079 := bstep (se 1 (by rfl) ⟨752309, by rfl⟩ : syracuseStep 1003079 = 1504619) B1504619
theorem B1003259 : Blo 666309 1003259 := bstep (se 1 (by rfl) ⟨752444, by rfl⟩ : syracuseStep 1003259 = 1504889) B1504889
theorem B2543359 : Blo 666309 2543359 := bstep (se 1 (by rfl) ⟨1907519, by rfl⟩ : syracuseStep 2543359 = 3815039) B3815039
theorem B37539773 : Blo 666309 37539773 := bstep (se 3 (by rfl) ⟨7038707, by rfl⟩ : syracuseStep 37539773 = 14077415) B14077415
theorem B1003631 : Blo 666309 1003631 := bstep (se 1 (by rfl) ⟨752723, by rfl⟩ : syracuseStep 1003631 = 1505447) B1505447
theorem B1101961 : Blo 666309 1101961 := bstep (se 2 (by rfl) ⟨413235, by rfl⟩ : syracuseStep 1101961 = 826471) B826471
theorem B1004537 : Blo 666309 1004537 := bstep (se 2 (by rfl) ⟨376701, by rfl⟩ : syracuseStep 1004537 = 753403) B753403
theorem B7132369 : Blo 666309 7132369 := bstep (se 2 (by rfl) ⟨2674638, by rfl⟩ : syracuseStep 7132369 = 5349277) B5349277
theorem B1004879 : Blo 666309 1004879 := bstep (se 1 (by rfl) ⟨753659, by rfl⟩ : syracuseStep 1004879 = 1507319) B1507319
theorem B1004921 : Blo 666309 1004921 := bstep (se 2 (by rfl) ⟨376845, by rfl⟩ : syracuseStep 1004921 = 753691) B753691
theorem B2250233 : Blo 666309 2250233 := bstep (se 2 (by rfl) ⟨843837, by rfl⟩ : syracuseStep 2250233 = 1687675) B1687675
theorem B1693295 : Blo 666309 1693295 := bstep (se 1 (by rfl) ⟨1269971, by rfl⟩ : syracuseStep 1693295 = 2539943) B2539943
theorem B7591805 : Blo 666309 7591805 := bstep (se 3 (by rfl) ⟨1423463, by rfl⟩ : syracuseStep 7591805 = 2846927) B2846927
theorem B1694459 : Blo 666309 1694459 := bstep (se 1 (by rfl) ⟨1270844, by rfl⟩ : syracuseStep 1694459 = 2541689) B2541689
theorem B1269607 : Blo 666309 1269607 := bstep (se 1 (by rfl) ⟨952205, by rfl⟩ : syracuseStep 1269607 = 1904411) B1904411
theorem B1204105 : Blo 666309 1204105 := bstep (se 2 (by rfl) ⟨451539, by rfl⟩ : syracuseStep 1204105 = 903079) B903079
theorem B4054949 : Blo 666309 4054949 := bstep (se 4 (by rfl) ⟨380151, by rfl⟩ : syracuseStep 4054949 = 760303) B760303
theorem B844015 : Blo 666309 844015 := bstep (se 1 (by rfl) ⟨633011, by rfl⟩ : syracuseStep 844015 = 1266023) B1266023
theorem B1204559 : Blo 666309 1204559 := bstep (se 1 (by rfl) ⟨903419, by rfl⟩ : syracuseStep 1204559 = 1806839) B1806839
theorem B8545499 : Blo 666309 8545499 := bstep (se 1 (by rfl) ⟨6409124, by rfl⟩ : syracuseStep 8545499 = 12818249) B12818249
theorem B1500425 : Blo 666309 1500425 := bstep (se 2 (by rfl) ⟨562659, by rfl⟩ : syracuseStep 1500425 = 1125319) B1125319
theorem B2057683 : Blo 666309 2057683 := bstep (se 1 (by rfl) ⟨1543262, by rfl⟩ : syracuseStep 2057683 = 3086525) B3086525
theorem B2254391 : Blo 666309 2254391 := bstep (se 1 (by rfl) ⟨1690793, by rfl⟩ : syracuseStep 2254391 = 3381587) B3381587
theorem B5433587 : Blo 666309 5433587 := bstep (se 1 (by rfl) ⟨4075190, by rfl⟩ : syracuseStep 5433587 = 8150381) B8150381
theorem B1501523 : Blo 666309 1501523 := bstep (se 1 (by rfl) ⟨1126142, by rfl⟩ : syracuseStep 1501523 = 2252285) B2252285
theorem B2354003 : Blo 666309 2354003 := bstep (se 1 (by rfl) ⟨1765502, by rfl⟩ : syracuseStep 2354003 = 3531005) B3531005
theorem B1207391 : Blo 666309 1207391 := bstep (se 1 (by rfl) ⟨905543, by rfl⟩ : syracuseStep 1207391 = 1811087) B1811087
theorem B5500169 : Blo 666309 5500169 := bstep (se 2 (by rfl) ⟨2062563, by rfl⟩ : syracuseStep 5500169 = 4125127) B4125127
theorem B1502639 : Blo 666309 1502639 := bstep (se 1 (by rfl) ⟨1126979, by rfl⟩ : syracuseStep 1502639 = 2253959) B2253959
theorem B1502747 : Blo 666309 1502747 := bstep (se 1 (by rfl) ⟨1127060, by rfl⟩ : syracuseStep 1502747 = 2254121) B2254121
theorem B8121971 : Blo 666309 8121971 := bstep (se 1 (by rfl) ⟨6091478, by rfl⟩ : syracuseStep 8121971 = 12182957) B12182957
theorem B2257307 : Blo 666309 2257307 := bstep (se 1 (by rfl) ⟨1692980, by rfl⟩ : syracuseStep 2257307 = 3385961) B3385961
theorem B4813303 : Blo 666309 4813303 := bstep (se 1 (by rfl) ⟨3609977, by rfl⟩ : syracuseStep 4813303 = 7219955) B7219955
theorem B2257577 : Blo 666309 2257577 := bstep (se 2 (by rfl) ⟨846591, by rfl⟩ : syracuseStep 2257577 = 1693183) B1693183
theorem B1504511 : Blo 666309 1504511 := bstep (se 1 (by rfl) ⟨1128383, by rfl⟩ : syracuseStep 1504511 = 2256767) B2256767
theorem B1897769 : Blo 666309 1897769 := bstep (se 2 (by rfl) ⟨711663, by rfl⟩ : syracuseStep 1897769 = 1423327) B1423327
theorem B5076755 : Blo 666309 5076755 := bstep (se 1 (by rfl) ⟨3807566, by rfl⟩ : syracuseStep 5076755 = 7615133) B7615133
theorem B2848841 : Blo 666309 2848841 := bstep (se 2 (by rfl) ⟨1068315, by rfl⟩ : syracuseStep 2848841 = 2136631) B2136631
theorem B949033 : Blo 666309 949033 := bstep (se 2 (by rfl) ⟨355887, by rfl⟩ : syracuseStep 949033 = 711775) B711775
theorem B1801183 : Blo 666309 1801183 := bstep (se 1 (by rfl) ⟨1350887, by rfl⟩ : syracuseStep 1801183 = 2701775) B2701775
theorem B1506617 : Blo 666309 1506617 := bstep (se 2 (by rfl) ⟨564981, by rfl⟩ : syracuseStep 1506617 = 1129963) B1129963
theorem B1507067 : Blo 666309 1507067 := bstep (se 1 (by rfl) ⟨1130300, by rfl⟩ : syracuseStep 1507067 = 2260601) B2260601
theorem B1507355 : Blo 666309 1507355 := bstep (se 1 (by rfl) ⟨1130516, by rfl⟩ : syracuseStep 1507355 = 2261033) B2261033
theorem B16220371 : Blo 666309 16220371 := bstep (se 1 (by rfl) ⟨12165278, by rfl⟩ : syracuseStep 16220371 = 24330557) B24330557
theorem B3211559 : Blo 666309 3211559 := bstep (se 1 (by rfl) ⟨2408669, by rfl⟩ : syracuseStep 3211559 = 4817339) B4817339
theorem B1507679 : Blo 666309 1507679 := bstep (se 1 (by rfl) ⟨1130759, by rfl⟩ : syracuseStep 1507679 = 2261519) B2261519
theorem B5702399 : Blo 666309 5702399 := bstep (se 1 (by rfl) ⟨4276799, by rfl⟩ : syracuseStep 5702399 = 8553599) B8553599
theorem B1803259 : Blo 666309 1803259 := bstep (se 1 (by rfl) ⟨1352444, by rfl⟩ : syracuseStep 1803259 = 2704889) B2704889
theorem B6424039 : Blo 666309 6424039 := bstep (se 1 (by rfl) ⟨4818029, by rfl⟩ : syracuseStep 6424039 = 9636059) B9636059
theorem B3213865 : Blo 666309 3213865 := bstep (se 2 (by rfl) ⟨1205199, by rfl⟩ : syracuseStep 3213865 = 2410399) B2410399
theorem B6097675 : Blo 666309 6097675 := bstep (se 1 (by rfl) ⟨4573256, by rfl⟩ : syracuseStep 6097675 = 9146513) B9146513
theorem B3378185 : Blo 666309 3378185 := bstep (se 2 (by rfl) ⟨1266819, by rfl⟩ : syracuseStep 3378185 = 2533639) B2533639
theorem B3806473 : Blo 666309 3806473 := bstep (se 2 (by rfl) ⟨1427427, by rfl⟩ : syracuseStep 3806473 = 2854855) B2854855
theorem B4462775 : Blo 666309 4462775 := bstep (se 1 (by rfl) ⟨3347081, by rfl⟩ : syracuseStep 4462775 = 6694163) B6694163
theorem B6101183 : Blo 666309 6101183 := bstep (se 1 (by rfl) ⟨4575887, by rfl⟩ : syracuseStep 6101183 = 9151775) B9151775
theorem B3086957 : Blo 666309 3086957 := bstep (se 3 (by rfl) ⟨578804, by rfl⟩ : syracuseStep 3086957 = 1157609) B1157609
theorem B1710827 : Blo 666309 1710827 := bstep (se 1 (by rfl) ⟨1283120, by rfl⟩ : syracuseStep 1710827 = 2566241) B2566241
theorem B9509825 : Blo 666309 9509825 := bstep (se 2 (by rfl) ⟨3566184, by rfl⟩ : syracuseStep 9509825 = 7132369) B7132369
theorem B5414647 : Blo 666309 5414647 := bstep (se 1 (by rfl) ⟨4060985, by rfl⟩ : syracuseStep 5414647 = 8121971) B8121971
theorem B3219709 : Blo 666309 3219709 := bstep (se 3 (by rfl) ⟨603695, by rfl⟩ : syracuseStep 3219709 = 1207391) B1207391
theorem B2564455 : Blo 666309 2564455 := bstep (se 1 (by rfl) ⟨1923341, by rfl⟩ : syracuseStep 2564455 = 3846683) B3846683
theorem B26026667 : Blo 666309 26026667 := bstep (se 1 (by rfl) ⟨19520000, by rfl⟩ : syracuseStep 26026667 = 39040001) B39040001
theorem B25109365 : Blo 666309 25109365 := bstep (se 5 (by rfl) ⟨1177001, by rfl⟩ : syracuseStep 25109365 = 2354003) B2354003
theorem B3384503 : Blo 666309 3384503 := bstep (se 1 (by rfl) ⟨2538377, by rfl⟩ : syracuseStep 3384503 = 5076755) B5076755
theorem B2401577 : Blo 666309 2401577 := bstep (se 2 (by rfl) ⟨900591, by rfl⟩ : syracuseStep 2401577 = 1801183) B1801183
theorem B46181171 : Blo 666309 46181171 := bstep (se 1 (by rfl) ⟨34635878, by rfl⟩ : syracuseStep 46181171 = 69271757) B69271757
theorem B666471 : Blo 666309 666471 := bstep (se 1 (by rfl) ⟨499853, by rfl⟩ : syracuseStep 666471 = 999707) B999707
theorem B666559 : Blo 666309 666559 := bstep (se 1 (by rfl) ⟨499919, by rfl⟩ : syracuseStep 666559 = 999839) B999839
theorem B1125353 : Blo 666309 1125353 := bstep (se 2 (by rfl) ⟨422007, by rfl⟩ : syracuseStep 1125353 = 844015) B844015
theorem B1125407 : Blo 666309 1125407 := bstep (se 1 (by rfl) ⟨844055, by rfl⟩ : syracuseStep 1125407 = 1688111) B1688111
theorem B666715 : Blo 666309 666715 := bstep (se 1 (by rfl) ⟨500036, by rfl⟩ : syracuseStep 666715 = 1000073) B1000073
theorem B666815 : Blo 666309 666815 := bstep (se 1 (by rfl) ⟨500111, by rfl⟩ : syracuseStep 666815 = 1000223) B1000223
theorem B666879 : Blo 666309 666879 := bstep (se 1 (by rfl) ⟨500159, by rfl⟩ : syracuseStep 666879 = 1000319) B1000319
theorem B667071 : Blo 666309 667071 := bstep (se 1 (by rfl) ⟨500303, by rfl⟩ : syracuseStep 667071 = 1000607) B1000607
theorem B667291 : Blo 666309 667291 := bstep (se 1 (by rfl) ⟨500468, by rfl⟩ : syracuseStep 667291 = 1000937) B1000937
theorem B667419 : Blo 666309 667419 := bstep (se 1 (by rfl) ⟨500564, by rfl⟩ : syracuseStep 667419 = 1001129) B1001129
theorem B48738185 : Blo 666309 48738185 := bstep (se 2 (by rfl) ⟨18276819, by rfl⟩ : syracuseStep 48738185 = 36553639) B36553639
theorem B667559 : Blo 666309 667559 := bstep (se 1 (by rfl) ⟨500669, by rfl⟩ : syracuseStep 667559 = 1001339) B1001339
theorem B3387419 : Blo 666309 3387419 := bstep (se 1 (by rfl) ⟨2540564, by rfl⟩ : syracuseStep 3387419 = 5081129) B5081129
theorem B667695 : Blo 666309 667695 := bstep (se 1 (by rfl) ⟨500771, by rfl⟩ : syracuseStep 667695 = 1001543) B1001543
theorem B1126703 : Blo 666309 1126703 := bstep (se 1 (by rfl) ⟨845027, by rfl⟩ : syracuseStep 1126703 = 1690055) B1690055
theorem B667951 : Blo 666309 667951 := bstep (se 1 (by rfl) ⟨500963, by rfl⟩ : syracuseStep 667951 = 1001927) B1001927
theorem B668207 : Blo 666309 668207 := bstep (se 1 (by rfl) ⟨501155, by rfl⟩ : syracuseStep 668207 = 1002311) B1002311
theorem B668271 : Blo 666309 668271 := bstep (se 1 (by rfl) ⟨501203, by rfl⟩ : syracuseStep 668271 = 1002407) B1002407
theorem B668315 : Blo 666309 668315 := bstep (se 1 (by rfl) ⟨501236, by rfl⟩ : syracuseStep 668315 = 1002473) B1002473
theorem B2142911 : Blo 666309 2142911 := bstep (se 1 (by rfl) ⟨1607183, by rfl⟩ : syracuseStep 2142911 = 3214367) B3214367
theorem B668519 : Blo 666309 668519 := bstep (se 1 (by rfl) ⟨501389, by rfl⟩ : syracuseStep 668519 = 1002779) B1002779
theorem B668719 : Blo 666309 668719 := bstep (se 1 (by rfl) ⟨501539, by rfl⟩ : syracuseStep 668719 = 1003079) B1003079
theorem B668839 : Blo 666309 668839 := bstep (se 1 (by rfl) ⟨501629, by rfl⟩ : syracuseStep 668839 = 1003259) B1003259
theorem B669087 : Blo 666309 669087 := bstep (se 1 (by rfl) ⟨501815, by rfl⟩ : syracuseStep 669087 = 1003631) B1003631
theorem B21739259 : Blo 666309 21739259 := bstep (se 1 (by rfl) ⟨16304444, by rfl⟩ : syracuseStep 21739259 = 32608889) B32608889
theorem B669691 : Blo 666309 669691 := bstep (se 1 (by rfl) ⟨502268, by rfl⟩ : syracuseStep 669691 = 1004537) B1004537
theorem B5060717 : Blo 666309 5060717 := bstep (se 3 (by rfl) ⟨948884, by rfl⟩ : syracuseStep 5060717 = 1897769) B1897769
theorem B669919 : Blo 666309 669919 := bstep (se 1 (by rfl) ⟨502439, by rfl⟩ : syracuseStep 669919 = 1004879) B1004879
theorem B669947 : Blo 666309 669947 := bstep (se 1 (by rfl) ⟨502460, by rfl⟩ : syracuseStep 669947 = 1004921) B1004921
theorem B1128863 : Blo 666309 1128863 := bstep (se 1 (by rfl) ⟨846647, by rfl⟩ : syracuseStep 1128863 = 1693295) B1693295
theorem B5061203 : Blo 666309 5061203 := bstep (se 1 (by rfl) ⟨3795902, by rfl⟩ : syracuseStep 5061203 = 7591805) B7591805
theorem B1129639 : Blo 666309 1129639 := bstep (se 1 (by rfl) ⟨847229, by rfl⟩ : syracuseStep 1129639 = 1694459) B1694459
theorem B3391145 : Blo 666309 3391145 := bstep (se 2 (by rfl) ⟨1271679, by rfl⟩ : syracuseStep 3391145 = 2543359) B2543359
theorem B12828395 : Blo 666309 12828395 := bstep (se 1 (by rfl) ⟨9621296, by rfl⟩ : syracuseStep 12828395 = 19242593) B19242593
theorem B2703299 : Blo 666309 2703299 := bstep (se 1 (by rfl) ⟨2027474, by rfl⟩ : syracuseStep 2703299 = 4054949) B4054949
theorem B3391631 : Blo 666309 3391631 := bstep (se 1 (by rfl) ⟨2543723, by rfl⟩ : syracuseStep 3391631 = 5087447) B5087447
theorem B803039 : Blo 666309 803039 := bstep (se 1 (by rfl) ⟨602279, by rfl⟩ : syracuseStep 803039 = 1204559) B1204559
theorem B1688303 : Blo 666309 1688303 := bstep (se 1 (by rfl) ⟨1266227, by rfl⟩ : syracuseStep 1688303 = 2532455) B2532455
theorem B1000283 : Blo 666309 1000283 := bstep (se 1 (by rfl) ⟨750212, by rfl⟩ : syracuseStep 1000283 = 1500425) B1500425
theorem B3622391 : Blo 666309 3622391 := bstep (se 1 (by rfl) ⟨2716793, by rfl⟩ : syracuseStep 3622391 = 5433587) B5433587
theorem B1001015 : Blo 666309 1001015 := bstep (se 1 (by rfl) ⟨750761, by rfl⟩ : syracuseStep 1001015 = 1501523) B1501523
theorem B2541415 : Blo 666309 2541415 := bstep (se 1 (by rfl) ⟨1906061, by rfl⟩ : syracuseStep 2541415 = 3812123) B3812123
theorem B1427719 : Blo 666309 1427719 := bstep (se 1 (by rfl) ⟨1070789, by rfl⟩ : syracuseStep 1427719 = 2141579) B2141579
theorem B1001759 : Blo 666309 1001759 := bstep (se 1 (by rfl) ⟨751319, by rfl⟩ : syracuseStep 1001759 = 1502639) B1502639
theorem B1001831 : Blo 666309 1001831 := bstep (se 1 (by rfl) ⟨751373, by rfl⟩ : syracuseStep 1001831 = 1502747) B1502747
theorem B13683977 : Blo 666309 13683977 := bstep (se 2 (by rfl) ⟨5131491, by rfl⟩ : syracuseStep 13683977 = 10262983) B10262983
theorem B1003007 : Blo 666309 1003007 := bstep (se 1 (by rfl) ⟨752255, by rfl⟩ : syracuseStep 1003007 = 1504511) B1504511
theorem B1265377 : Blo 666309 1265377 := bstep (se 2 (by rfl) ⟨474516, by rfl⟩ : syracuseStep 1265377 = 949033) B949033
theorem B10407649 : Blo 666309 10407649 := bstep (se 2 (by rfl) ⟨3902868, by rfl⟩ : syracuseStep 10407649 = 7805737) B7805737
theorem B1004411 : Blo 666309 1004411 := bstep (se 1 (by rfl) ⟨753308, by rfl⟩ : syracuseStep 1004411 = 1506617) B1506617
theorem B1692809 : Blo 666309 1692809 := bstep (se 2 (by rfl) ⟨634803, by rfl⟩ : syracuseStep 1692809 = 1269607) B1269607
theorem B1004711 : Blo 666309 1004711 := bstep (se 1 (by rfl) ⟨753533, by rfl⟩ : syracuseStep 1004711 = 1507067) B1507067
theorem B1201655 : Blo 666309 1201655 := bstep (se 1 (by rfl) ⟨901241, by rfl⟩ : syracuseStep 1201655 = 1802483) B1802483
theorem B1005215 : Blo 666309 1005215 := bstep (se 1 (by rfl) ⟨753911, by rfl⟩ : syracuseStep 1005215 = 1507823) B1507823
theorem B7625339 : Blo 666309 7625339 := bstep (se 1 (by rfl) ⟨5719004, by rfl⟩ : syracuseStep 7625339 = 11438009) B11438009
theorem B9755387 : Blo 666309 9755387 := bstep (se 1 (by rfl) ⟨7316540, by rfl⟩ : syracuseStep 9755387 = 14633081) B14633081
theorem B2415359 : Blo 666309 2415359 := bstep (se 1 (by rfl) ⟨1811519, by rfl⟩ : syracuseStep 2415359 = 3623039) B3623039
theorem B2743577 : Blo 666309 2743577 := bstep (se 2 (by rfl) ⟨1028841, by rfl⟩ : syracuseStep 2743577 = 2057683) B2057683
theorem B25026515 : Blo 666309 25026515 := bstep (se 1 (by rfl) ⟨18769886, by rfl⟩ : syracuseStep 25026515 = 37539773) B37539773
theorem B1499273 : Blo 666309 1499273 := bstep (se 2 (by rfl) ⟨562227, by rfl⟩ : syracuseStep 1499273 = 1124455) B1124455
theorem B1270055 : Blo 666309 1270055 := bstep (se 1 (by rfl) ⟨952541, by rfl⟩ : syracuseStep 1270055 = 1905083) B1905083
theorem B1500155 : Blo 666309 1500155 := bstep (se 1 (by rfl) ⟨1125116, by rfl⟩ : syracuseStep 1500155 = 2250233) B2250233
theorem B1271551 : Blo 666309 1271551 := bstep (se 1 (by rfl) ⟨953663, by rfl⟩ : syracuseStep 1271551 = 1907327) B1907327
theorem B2254715 : Blo 666309 2254715 := bstep (se 1 (by rfl) ⟨1691036, by rfl⟩ : syracuseStep 2254715 = 3382073) B3382073
theorem B5073353 : Blo 666309 5073353 := bstep (se 2 (by rfl) ⟨1902507, by rfl⟩ : syracuseStep 5073353 = 3805015) B3805015
theorem B2255471 : Blo 666309 2255471 := bstep (se 1 (by rfl) ⟨1691603, by rfl⟩ : syracuseStep 2255471 = 3383207) B3383207
theorem B1469281 : Blo 666309 1469281 := bstep (se 2 (by rfl) ⟨550980, by rfl⟩ : syracuseStep 1469281 = 1101961) B1101961
theorem B6188123 : Blo 666309 6188123 := bstep (se 1 (by rfl) ⟨4641092, by rfl⟩ : syracuseStep 6188123 = 9282185) B9282185
theorem B6417737 : Blo 666309 6417737 := bstep (se 2 (by rfl) ⟨2406651, by rfl⟩ : syracuseStep 6417737 = 4813303) B4813303
theorem B5696999 : Blo 666309 5696999 := bstep (se 1 (by rfl) ⟨4272749, by rfl⟩ : syracuseStep 5696999 = 8545499) B8545499
theorem B1502927 : Blo 666309 1502927 := bstep (se 1 (by rfl) ⟨1127195, by rfl⟩ : syracuseStep 1502927 = 2254391) B2254391
theorem B2256875 : Blo 666309 2256875 := bstep (se 1 (by rfl) ⟨1692656, by rfl⟩ : syracuseStep 2256875 = 3385313) B3385313
theorem B749659 : Blo 666309 749659 := bstep (se 1 (by rfl) ⟨562244, by rfl⟩ : syracuseStep 749659 = 1124489) B1124489
theorem B2257415 : Blo 666309 2257415 := bstep (se 1 (by rfl) ⟨1693061, by rfl⟩ : syracuseStep 2257415 = 3386123) B3386123
theorem B7238423 : Blo 666309 7238423 := bstep (se 1 (by rfl) ⟨5428817, by rfl⟩ : syracuseStep 7238423 = 10857635) B10857635
theorem B3666779 : Blo 666309 3666779 := bstep (se 1 (by rfl) ⟨2750084, by rfl⟩ : syracuseStep 3666779 = 5500169) B5500169
theorem B750559 : Blo 666309 750559 := bstep (se 1 (by rfl) ⟨562919, by rfl⟩ : syracuseStep 750559 = 1125839) B1125839
theorem B3438055 : Blo 666309 3438055 := bstep (se 1 (by rfl) ⟨2578541, by rfl⟩ : syracuseStep 3438055 = 5157083) B5157083
theorem B1504745 : Blo 666309 1504745 := bstep (se 2 (by rfl) ⟨564279, by rfl⟩ : syracuseStep 1504745 = 1128559) B1128559
theorem B1504871 : Blo 666309 1504871 := bstep (se 1 (by rfl) ⟨1128653, by rfl⟩ : syracuseStep 1504871 = 2257307) B2257307
theorem B1505051 : Blo 666309 1505051 := bstep (se 1 (by rfl) ⟨1128788, by rfl⟩ : syracuseStep 1505051 = 2257577) B2257577
theorem B5077241 : Blo 666309 5077241 := bstep (se 2 (by rfl) ⟨1903965, by rfl⟩ : syracuseStep 5077241 = 3807931) B3807931
theorem B3373649 : Blo 666309 3373649 := bstep (se 2 (by rfl) ⟨1265118, by rfl⟩ : syracuseStep 3373649 = 2530237) B2530237
theorem B1899227 : Blo 666309 1899227 := bstep (se 1 (by rfl) ⟨1424420, by rfl⟩ : syracuseStep 1899227 = 2848841) B2848841
theorem B1506473 : Blo 666309 1506473 := bstep (se 2 (by rfl) ⟨564927, by rfl⟩ : syracuseStep 1506473 = 1129855) B1129855
theorem B1605473 : Blo 666309 1605473 := bstep (se 2 (by rfl) ⟨602052, by rfl⟩ : syracuseStep 1605473 = 1204105) B1204105
theorem B2261087 : Blo 666309 2261087 := bstep (se 1 (by rfl) ⟨1695815, by rfl⟩ : syracuseStep 2261087 = 3391631) B3391631
theorem B21627161 : Blo 666309 21627161 := bstep (se 2 (by rfl) ⟨8110185, by rfl⟩ : syracuseStep 21627161 = 16220371) B16220371
theorem B4292945 : Blo 666309 4292945 := bstep (se 2 (by rfl) ⟨1609854, by rfl⟩ : syracuseStep 4292945 = 3219709) B3219709
theorem B3801599 : Blo 666309 3801599 := bstep (se 1 (by rfl) ⟨2851199, by rfl⟩ : syracuseStep 3801599 = 5702399) B5702399
theorem B19302461 : Blo 666309 19302461 := bstep (se 3 (by rfl) ⟨3619211, by rfl⟩ : syracuseStep 19302461 = 7238423) B7238423
theorem B1903625 : Blo 666309 1903625 := bstep (se 2 (by rfl) ⟨713859, by rfl⟩ : syracuseStep 1903625 = 1427719) B1427719
theorem B8130233 : Blo 666309 8130233 := bstep (se 2 (by rfl) ⟨3048837, by rfl⟩ : syracuseStep 8130233 = 6097675) B6097675
theorem B4067455 : Blo 666309 4067455 := bstep (se 1 (by rfl) ⟨3050591, by rfl⟩ : syracuseStep 4067455 = 6101183) B6101183
theorem B5083559 : Blo 666309 5083559 := bstep (se 1 (by rfl) ⟨3812669, by rfl⟩ : syracuseStep 5083559 = 7625339) B7625339
theorem B16684343 : Blo 666309 16684343 := bstep (se 1 (by rfl) ⟨12513257, by rfl⟩ : syracuseStep 16684343 = 25026515) B25026515
theorem B3382235 : Blo 666309 3382235 := bstep (se 1 (by rfl) ⟨2536676, by rfl⟩ : syracuseStep 3382235 = 5073353) B5073353
theorem B14492839 : Blo 666309 14492839 := bstep (se 1 (by rfl) ⟨10869629, by rfl⟩ : syracuseStep 14492839 = 21739259) B21739259
theorem B3384827 : Blo 666309 3384827 := bstep (se 1 (by rfl) ⟨2538620, by rfl⟩ : syracuseStep 3384827 = 5077241) B5077241
theorem B7219529 : Blo 666309 7219529 := bstep (se 2 (by rfl) ⟨2707323, by rfl⟩ : syracuseStep 7219529 = 5414647) B5414647
theorem B2141039 : Blo 666309 2141039 := bstep (se 1 (by rfl) ⟨1605779, by rfl⟩ : syracuseStep 2141039 = 3211559) B3211559
theorem B3419273 : Blo 666309 3419273 := bstep (se 2 (by rfl) ⟨1282227, by rfl⟩ : syracuseStep 3419273 = 2564455) B2564455
theorem B1125535 : Blo 666309 1125535 := bstep (se 1 (by rfl) ⟨844151, by rfl⟩ : syracuseStep 1125535 = 1688303) B1688303
theorem B666855 : Blo 666309 666855 := bstep (se 1 (by rfl) ⟨500141, by rfl⟩ : syracuseStep 666855 = 1000283) B1000283
theorem B667343 : Blo 666309 667343 := bstep (se 1 (by rfl) ⟨500507, by rfl⟩ : syracuseStep 667343 = 1001015) B1001015
theorem B2404345 : Blo 666309 2404345 := bstep (se 2 (by rfl) ⟨901629, by rfl⟩ : syracuseStep 2404345 = 1803259) B1803259
theorem B667839 : Blo 666309 667839 := bstep (se 1 (by rfl) ⟨500879, by rfl⟩ : syracuseStep 667839 = 1001759) B1001759
theorem B667887 : Blo 666309 667887 := bstep (se 1 (by rfl) ⟨500915, by rfl⟩ : syracuseStep 667887 = 1001831) B1001831
theorem B8565385 : Blo 666309 8565385 := bstep (se 2 (by rfl) ⟨3212019, by rfl⟩ : syracuseStep 8565385 = 6424039) B6424039
theorem B9122651 : Blo 666309 9122651 := bstep (se 1 (by rfl) ⟨6841988, by rfl⟩ : syracuseStep 9122651 = 13683977) B13683977
theorem B8565749 : Blo 666309 8565749 := bstep (se 5 (by rfl) ⟨401519, by rfl⟩ : syracuseStep 8565749 = 803039) B803039
theorem B668671 : Blo 666309 668671 := bstep (se 1 (by rfl) ⟨501503, by rfl⟩ : syracuseStep 668671 = 1003007) B1003007
theorem B3388553 : Blo 666309 3388553 := bstep (se 2 (by rfl) ⟨1270707, by rfl⟩ : syracuseStep 3388553 = 2541415) B2541415
theorem B669607 : Blo 666309 669607 := bstep (se 1 (by rfl) ⟨502205, by rfl⟩ : syracuseStep 669607 = 1004411) B1004411
theorem B1128539 : Blo 666309 1128539 := bstep (se 1 (by rfl) ⟨846404, by rfl⟩ : syracuseStep 1128539 = 1692809) B1692809
theorem B669807 : Blo 666309 669807 := bstep (se 1 (by rfl) ⟨502355, by rfl⟩ : syracuseStep 669807 = 1004711) B1004711
theorem B801103 : Blo 666309 801103 := bstep (se 1 (by rfl) ⟨600827, by rfl⟩ : syracuseStep 801103 = 1201655) B1201655
theorem B670143 : Blo 666309 670143 := bstep (se 1 (by rfl) ⟨502607, by rfl⟩ : syracuseStep 670143 = 1005215) B1005215
theorem B6503591 : Blo 666309 6503591 := bstep (se 1 (by rfl) ⟨4877693, by rfl⟩ : syracuseStep 6503591 = 9755387) B9755387
theorem B6339883 : Blo 666309 6339883 := bstep (se 1 (by rfl) ⟨4754912, by rfl⟩ : syracuseStep 6339883 = 9509825) B9509825
theorem B1687169 : Blo 666309 1687169 := bstep (se 2 (by rfl) ⟨632688, by rfl⟩ : syracuseStep 1687169 = 1265377) B1265377
theorem B13876865 : Blo 666309 13876865 := bstep (se 2 (by rfl) ⟨5203824, by rfl⟩ : syracuseStep 13876865 = 10407649) B10407649
theorem B999515 : Blo 666309 999515 := bstep (se 1 (by rfl) ⟨749636, by rfl⟩ : syracuseStep 999515 = 1499273) B1499273
theorem B999545 : Blo 666309 999545 := bstep (se 2 (by rfl) ⟨374829, by rfl⟩ : syracuseStep 999545 = 749659) B749659
theorem B17351111 : Blo 666309 17351111 := bstep (se 1 (by rfl) ⟨13013333, by rfl⟩ : syracuseStep 17351111 = 26026667) B26026667
theorem B1000103 : Blo 666309 1000103 := bstep (se 1 (by rfl) ⟨750077, by rfl⟩ : syracuseStep 1000103 = 1500155) B1500155
theorem B1000745 : Blo 666309 1000745 := bstep (se 2 (by rfl) ⟨375279, by rfl⟩ : syracuseStep 1000745 = 750559) B750559
theorem B30787447 : Blo 666309 30787447 := bstep (se 1 (by rfl) ⟨23090585, by rfl⟩ : syracuseStep 30787447 = 46181171) B46181171
theorem B5064605 : Blo 666309 5064605 := bstep (se 3 (by rfl) ⟨949613, by rfl⟩ : syracuseStep 5064605 = 1899227) B1899227
theorem B6440957 : Blo 666309 6440957 := bstep (se 3 (by rfl) ⟨1207679, by rfl⟩ : syracuseStep 6440957 = 2415359) B2415359
theorem B4278491 : Blo 666309 4278491 := bstep (se 1 (by rfl) ⟨3208868, by rfl⟩ : syracuseStep 4278491 = 6417737) B6417737
theorem B1001951 : Blo 666309 1001951 := bstep (se 1 (by rfl) ⟨751463, by rfl⟩ : syracuseStep 1001951 = 1502927) B1502927
theorem B32492123 : Blo 666309 32492123 := bstep (se 1 (by rfl) ⟨24369092, by rfl⟩ : syracuseStep 32492123 = 48738185) B48738185
theorem B1428607 : Blo 666309 1428607 := bstep (se 1 (by rfl) ⟨1071455, by rfl⟩ : syracuseStep 1428607 = 2142911) B2142911
theorem B2444519 : Blo 666309 2444519 := bstep (se 1 (by rfl) ⟨1833389, by rfl⟩ : syracuseStep 2444519 = 3666779) B3666779
theorem B1003163 : Blo 666309 1003163 := bstep (se 1 (by rfl) ⟨752372, by rfl⟩ : syracuseStep 1003163 = 1504745) B1504745
theorem B1003247 : Blo 666309 1003247 := bstep (se 1 (by rfl) ⟨752435, by rfl⟩ : syracuseStep 1003247 = 1504871) B1504871
theorem B1003367 : Blo 666309 1003367 := bstep (se 1 (by rfl) ⟨752525, by rfl⟩ : syracuseStep 1003367 = 1505051) B1505051
theorem B2249099 : Blo 666309 2249099 := bstep (se 1 (by rfl) ⟨1686824, by rfl⟩ : syracuseStep 2249099 = 3373649) B3373649
theorem B1004315 : Blo 666309 1004315 := bstep (se 1 (by rfl) ⟨753236, by rfl⟩ : syracuseStep 1004315 = 1506473) B1506473
theorem B1070315 : Blo 666309 1070315 := bstep (se 1 (by rfl) ⟨802736, by rfl⟩ : syracuseStep 1070315 = 1605473) B1605473
theorem B1004903 : Blo 666309 1004903 := bstep (se 1 (by rfl) ⟨753677, by rfl⟩ : syracuseStep 1004903 = 1507355) B1507355
theorem B1005119 : Blo 666309 1005119 := bstep (se 1 (by rfl) ⟨753839, by rfl⟩ : syracuseStep 1005119 = 1507679) B1507679
theorem B2414927 : Blo 666309 2414927 := bstep (se 1 (by rfl) ⟨1811195, by rfl⟩ : syracuseStep 2414927 = 3622391) B3622391
theorem B33479153 : Blo 666309 33479153 := bstep (se 2 (by rfl) ⟨12554682, by rfl⟩ : syracuseStep 33479153 = 25109365) B25109365
theorem B2252123 : Blo 666309 2252123 := bstep (se 1 (by rfl) ⟨1689092, by rfl⟩ : syracuseStep 2252123 = 3378185) B3378185
theorem B1695401 : Blo 666309 1695401 := bstep (se 2 (by rfl) ⟨635775, by rfl⟩ : syracuseStep 1695401 = 1271551) B1271551
theorem B4285153 : Blo 666309 4285153 := bstep (se 2 (by rfl) ⟨1606932, by rfl⟩ : syracuseStep 4285153 = 3213865) B3213865
theorem B1959041 : Blo 666309 1959041 := bstep (se 2 (by rfl) ⟨734640, by rfl⟩ : syracuseStep 1959041 = 1469281) B1469281
theorem B2975183 : Blo 666309 2975183 := bstep (se 1 (by rfl) ⟨2231387, by rfl⟩ : syracuseStep 2975183 = 4462775) B4462775
theorem B2057971 : Blo 666309 2057971 := bstep (se 1 (by rfl) ⟨1543478, by rfl⟩ : syracuseStep 2057971 = 3086957) B3086957
theorem B1140551 : Blo 666309 1140551 := bstep (se 1 (by rfl) ⟨855413, by rfl⟩ : syracuseStep 1140551 = 1710827) B1710827
theorem B1829051 : Blo 666309 1829051 := bstep (se 1 (by rfl) ⟨1371788, by rfl⟩ : syracuseStep 1829051 = 2743577) B2743577
theorem B846703 : Blo 666309 846703 := bstep (se 1 (by rfl) ⟨635027, by rfl⟩ : syracuseStep 846703 = 1270055) B1270055
theorem B2256335 : Blo 666309 2256335 := bstep (se 1 (by rfl) ⟨1692251, by rfl⟩ : syracuseStep 2256335 = 3384503) B3384503
theorem B1601051 : Blo 666309 1601051 := bstep (se 1 (by rfl) ⟨1200788, by rfl⟩ : syracuseStep 1601051 = 2401577) B2401577
theorem B1503143 : Blo 666309 1503143 := bstep (se 1 (by rfl) ⟨1127357, by rfl⟩ : syracuseStep 1503143 = 2254715) B2254715
theorem B5075297 : Blo 666309 5075297 := bstep (se 2 (by rfl) ⟨1903236, by rfl⟩ : syracuseStep 5075297 = 3806473) B3806473
theorem B1503647 : Blo 666309 1503647 := bstep (se 1 (by rfl) ⟨1127735, by rfl⟩ : syracuseStep 1503647 = 2255471) B2255471
theorem B4584073 : Blo 666309 4584073 := bstep (se 2 (by rfl) ⟨1719027, by rfl⟩ : syracuseStep 4584073 = 3438055) B3438055
theorem B750235 : Blo 666309 750235 := bstep (se 1 (by rfl) ⟨562676, by rfl⟩ : syracuseStep 750235 = 1125353) B1125353
theorem B750271 : Blo 666309 750271 := bstep (se 1 (by rfl) ⟨562703, by rfl⟩ : syracuseStep 750271 = 1125407) B1125407
theorem B4125415 : Blo 666309 4125415 := bstep (se 1 (by rfl) ⟨3094061, by rfl⟩ : syracuseStep 4125415 = 6188123) B6188123
theorem B3797999 : Blo 666309 3797999 := bstep (se 1 (by rfl) ⟨2848499, by rfl⟩ : syracuseStep 3797999 = 5696999) B5696999
theorem B1504583 : Blo 666309 1504583 := bstep (se 1 (by rfl) ⟨1128437, by rfl⟩ : syracuseStep 1504583 = 2256875) B2256875
theorem B2258279 : Blo 666309 2258279 := bstep (se 1 (by rfl) ⟨1693709, by rfl⟩ : syracuseStep 2258279 = 3387419) B3387419
theorem B751135 : Blo 666309 751135 := bstep (se 1 (by rfl) ⟨563351, by rfl⟩ : syracuseStep 751135 = 1126703) B1126703
theorem B1504943 : Blo 666309 1504943 := bstep (se 1 (by rfl) ⟨1128707, by rfl⟩ : syracuseStep 1504943 = 2257415) B2257415
theorem B3373811 : Blo 666309 3373811 := bstep (se 1 (by rfl) ⟨2530358, by rfl⟩ : syracuseStep 3373811 = 5060717) B5060717
theorem B1506185 : Blo 666309 1506185 := bstep (se 2 (by rfl) ⟨564819, by rfl⟩ : syracuseStep 1506185 = 1129639) B1129639
theorem B752575 : Blo 666309 752575 := bstep (se 1 (by rfl) ⟨564431, by rfl⟩ : syracuseStep 752575 = 1128863) B1128863
theorem B3374135 : Blo 666309 3374135 := bstep (se 1 (by rfl) ⟨2530601, by rfl⟩ : syracuseStep 3374135 = 5061203) B5061203
theorem B2260763 : Blo 666309 2260763 := bstep (se 1 (by rfl) ⟨1695572, by rfl⟩ : syracuseStep 2260763 = 3391145) B3391145
theorem B8552263 : Blo 666309 8552263 := bstep (se 1 (by rfl) ⟨6414197, by rfl⟩ : syracuseStep 8552263 = 12828395) B12828395
theorem B7208797 : Blo 666309 7208797 := bstep (se 3 (by rfl) ⟨1351649, by rfl⟩ : syracuseStep 7208797 = 2703299) B2703299
theorem B1507391 : Blo 666309 1507391 := bstep (se 1 (by rfl) ⟨1130543, by rfl⟩ : syracuseStep 1507391 = 2261087) B2261087
theorem B14418107 : Blo 666309 14418107 := bstep (se 1 (by rfl) ⟨10813580, by rfl⟩ : syracuseStep 14418107 = 21627161) B21627161
theorem B46269629 : Blo 666309 46269629 := bstep (se 3 (by rfl) ⟨8675555, by rfl⟩ : syracuseStep 46269629 = 17351111) B17351111
theorem B3376403 : Blo 666309 3376403 := bstep (se 1 (by rfl) ⟨2532302, by rfl⟩ : syracuseStep 3376403 = 5064605) B5064605
theorem B4293971 : Blo 666309 4293971 := bstep (se 1 (by rfl) ⟨3220478, by rfl⟩ : syracuseStep 4293971 = 6440957) B6440957
theorem B2852327 : Blo 666309 2852327 := bstep (se 1 (by rfl) ⟨2139245, by rfl⟩ : syracuseStep 2852327 = 4278491) B4278491
theorem B21661415 : Blo 666309 21661415 := bstep (se 1 (by rfl) ⟨16246061, by rfl⟩ : syracuseStep 21661415 = 32492123) B32492123
theorem B1904809 : Blo 666309 1904809 := bstep (se 2 (by rfl) ⟨714303, by rfl⟩ : syracuseStep 1904809 = 1428607) B1428607
theorem B1609951 : Blo 666309 1609951 := bstep (se 1 (by rfl) ⟨1207463, by rfl⟩ : syracuseStep 1609951 = 2414927) B2414927
theorem B22319435 : Blo 666309 22319435 := bstep (se 1 (by rfl) ⟨16739576, by rfl⟩ : syracuseStep 22319435 = 33479153) B33479153
theorem B760367 : Blo 666309 760367 := bstep (se 1 (by rfl) ⟨570275, by rfl⟩ : syracuseStep 760367 = 1140551) B1140551
theorem B1219367 : Blo 666309 1219367 := bstep (se 1 (by rfl) ⟨914525, by rfl⟩ : syracuseStep 1219367 = 1829051) B1829051
theorem B5709437 : Blo 666309 5709437 := bstep (se 3 (by rfl) ⟨1070519, by rfl⟩ : syracuseStep 5709437 = 2141039) B2141039
theorem B3383531 : Blo 666309 3383531 := bstep (se 1 (by rfl) ⟨2537648, by rfl⟩ : syracuseStep 3383531 = 5075297) B5075297
theorem B17342909 : Blo 666309 17342909 := bstep (se 3 (by rfl) ⟨3251795, by rfl⟩ : syracuseStep 17342909 = 6503591) B6503591
theorem B2531999 : Blo 666309 2531999 := bstep (se 1 (by rfl) ⟨1898999, by rfl⟩ : syracuseStep 2531999 = 3797999) B3797999
theorem B5710499 : Blo 666309 5710499 := bstep (se 1 (by rfl) ⟨4282874, by rfl⟩ : syracuseStep 5710499 = 8565749) B8565749
theorem B4269469 : Blo 666309 4269469 := bstep (se 3 (by rfl) ⟨800525, by rfl⟩ : syracuseStep 4269469 = 1601051) B1601051
theorem B1124779 : Blo 666309 1124779 := bstep (se 1 (by rfl) ⟨843584, by rfl⟩ : syracuseStep 1124779 = 1687169) B1687169
theorem B9251243 : Blo 666309 9251243 := bstep (se 1 (by rfl) ⟨6938432, by rfl⟩ : syracuseStep 9251243 = 13876865) B13876865
theorem B9611729 : Blo 666309 9611729 := bstep (se 2 (by rfl) ⟨3604398, by rfl⟩ : syracuseStep 9611729 = 7208797) B7208797
theorem B666343 : Blo 666309 666343 := bstep (se 1 (by rfl) ⟨499757, by rfl⟩ : syracuseStep 666343 = 999515) B999515
theorem B666363 : Blo 666309 666363 := bstep (se 1 (by rfl) ⟨499772, by rfl⟩ : syracuseStep 666363 = 999545) B999545
theorem B2861963 : Blo 666309 2861963 := bstep (se 1 (by rfl) ⟨2146472, by rfl⟩ : syracuseStep 2861963 = 4292945) B4292945
theorem B2534399 : Blo 666309 2534399 := bstep (se 1 (by rfl) ⟨1900799, by rfl⟩ : syracuseStep 2534399 = 3801599) B3801599
theorem B666735 : Blo 666309 666735 := bstep (se 1 (by rfl) ⟨500051, by rfl⟩ : syracuseStep 666735 = 1000103) B1000103
theorem B667163 : Blo 666309 667163 := bstep (se 1 (by rfl) ⟨500372, by rfl⟩ : syracuseStep 667163 = 1000745) B1000745
theorem B5713537 : Blo 666309 5713537 := bstep (se 2 (by rfl) ⟨2142576, by rfl⟩ : syracuseStep 5713537 = 4285153) B4285153
theorem B667967 : Blo 666309 667967 := bstep (se 1 (by rfl) ⟨500975, by rfl⟩ : syracuseStep 667967 = 1001951) B1001951
theorem B668775 : Blo 666309 668775 := bstep (se 1 (by rfl) ⟨501581, by rfl⟩ : syracuseStep 668775 = 1003163) B1003163
theorem B668831 : Blo 666309 668831 := bstep (se 1 (by rfl) ⟨501623, by rfl⟩ : syracuseStep 668831 = 1003247) B1003247
theorem B668911 : Blo 666309 668911 := bstep (se 1 (by rfl) ⟨501683, by rfl⟩ : syracuseStep 668911 = 1003367) B1003367
theorem B3389039 : Blo 666309 3389039 := bstep (se 1 (by rfl) ⟨2541779, by rfl⟩ : syracuseStep 3389039 = 5083559) B5083559
theorem B669543 : Blo 666309 669543 := bstep (se 1 (by rfl) ⟨502157, by rfl⟩ : syracuseStep 669543 = 1004315) B1004315
theorem B11122895 : Blo 666309 11122895 := bstep (se 1 (by rfl) ⟨8342171, by rfl⟩ : syracuseStep 11122895 = 16684343) B16684343
theorem B669935 : Blo 666309 669935 := bstep (se 1 (by rfl) ⟨502451, by rfl⟩ : syracuseStep 669935 = 1004903) B1004903
theorem B670079 : Blo 666309 670079 := bstep (se 1 (by rfl) ⟨502559, by rfl⟩ : syracuseStep 670079 = 1005119) B1005119
theorem B1128937 : Blo 666309 1128937 := bstep (se 2 (by rfl) ⟨423351, by rfl⟩ : syracuseStep 1128937 = 846703) B846703
theorem B1130267 : Blo 666309 1130267 := bstep (se 1 (by rfl) ⟨847700, by rfl⟩ : syracuseStep 1130267 = 1695401) B1695401
theorem B5423273 : Blo 666309 5423273 := bstep (se 2 (by rfl) ⟨2033727, by rfl⟩ : syracuseStep 5423273 = 4067455) B4067455
theorem B11420513 : Blo 666309 11420513 := bstep (se 2 (by rfl) ⟨4282692, by rfl⟩ : syracuseStep 11420513 = 8565385) B8565385
theorem B6112097 : Blo 666309 6112097 := bstep (se 2 (by rfl) ⟨2292036, by rfl⟩ : syracuseStep 6112097 = 4584073) B4584073
theorem B1000313 : Blo 666309 1000313 := bstep (se 2 (by rfl) ⟨375117, by rfl⟩ : syracuseStep 1000313 = 750235) B750235
theorem B1000361 : Blo 666309 1000361 := bstep (se 2 (by rfl) ⟨375135, by rfl⟩ : syracuseStep 1000361 = 750271) B750271
theorem B1983455 : Blo 666309 1983455 := bstep (se 1 (by rfl) ⟨1487591, by rfl⟩ : syracuseStep 1983455 = 2975183) B2975183
theorem B1001513 : Blo 666309 1001513 := bstep (se 2 (by rfl) ⟨375567, by rfl⟩ : syracuseStep 1001513 = 751135) B751135
theorem B2279515 : Blo 666309 2279515 := bstep (se 1 (by rfl) ⟨1709636, by rfl⟩ : syracuseStep 2279515 = 3419273) B3419273
theorem B1002095 : Blo 666309 1002095 := bstep (se 1 (by rfl) ⟨751571, by rfl⟩ : syracuseStep 1002095 = 1503143) B1503143
theorem B1002431 : Blo 666309 1002431 := bstep (se 1 (by rfl) ⟨751823, by rfl⟩ : syracuseStep 1002431 = 1503647) B1503647
theorem B1068137 : Blo 666309 1068137 := bstep (se 2 (by rfl) ⟨400551, by rfl⟩ : syracuseStep 1068137 = 801103) B801103
theorem B6081767 : Blo 666309 6081767 := bstep (se 1 (by rfl) ⟨4561325, by rfl⟩ : syracuseStep 6081767 = 9122651) B9122651
theorem B1003055 : Blo 666309 1003055 := bstep (se 1 (by rfl) ⟨752291, by rfl⟩ : syracuseStep 1003055 = 1504583) B1504583
theorem B1003295 : Blo 666309 1003295 := bstep (se 1 (by rfl) ⟨752471, by rfl⟩ : syracuseStep 1003295 = 1504943) B1504943
theorem B1003433 : Blo 666309 1003433 := bstep (se 2 (by rfl) ⟨376287, by rfl⟩ : syracuseStep 1003433 = 752575) B752575
theorem B21680621 : Blo 666309 21680621 := bstep (se 3 (by rfl) ⟨4065116, by rfl⟩ : syracuseStep 21680621 = 8130233) B8130233
theorem B2249207 : Blo 666309 2249207 := bstep (se 1 (by rfl) ⟨1686905, by rfl⟩ : syracuseStep 2249207 = 3373811) B3373811
theorem B1004123 : Blo 666309 1004123 := bstep (se 1 (by rfl) ⟨753092, by rfl⟩ : syracuseStep 1004123 = 1506185) B1506185
theorem B2249423 : Blo 666309 2249423 := bstep (se 1 (by rfl) ⟨1687067, by rfl⟩ : syracuseStep 2249423 = 3374135) B3374135
theorem B12868307 : Blo 666309 12868307 := bstep (se 1 (by rfl) ⟨9651230, by rfl⟩ : syracuseStep 12868307 = 19302461) B19302461
theorem B19323785 : Blo 666309 19323785 := bstep (se 2 (by rfl) ⟨7246419, by rfl⟩ : syracuseStep 19323785 = 14492839) B14492839
theorem B1269083 : Blo 666309 1269083 := bstep (se 1 (by rfl) ⟨951812, by rfl⟩ : syracuseStep 1269083 = 1903625) B1903625
theorem B2743961 : Blo 666309 2743961 := bstep (se 2 (by rfl) ⟨1028985, by rfl⟩ : syracuseStep 2743961 = 2057971) B2057971
theorem B41049929 : Blo 666309 41049929 := bstep (se 2 (by rfl) ⟨15393723, by rfl⟩ : syracuseStep 41049929 = 30787447) B30787447
theorem B1499399 : Blo 666309 1499399 := bstep (se 1 (by rfl) ⟨1124549, by rfl⟩ : syracuseStep 1499399 = 2249099) B2249099
theorem B713543 : Blo 666309 713543 := bstep (se 1 (by rfl) ⟨535157, by rfl⟩ : syracuseStep 713543 = 1070315) B1070315
theorem B1500713 : Blo 666309 1500713 := bstep (se 2 (by rfl) ⟨562767, by rfl⟩ : syracuseStep 1500713 = 1125535) B1125535
theorem B2254823 : Blo 666309 2254823 := bstep (se 1 (by rfl) ⟨1691117, by rfl⟩ : syracuseStep 2254823 = 3382235) B3382235
theorem B1501415 : Blo 666309 1501415 := bstep (se 1 (by rfl) ⟨1126061, by rfl⟩ : syracuseStep 1501415 = 2252123) B2252123
theorem B3205793 : Blo 666309 3205793 := bstep (se 2 (by rfl) ⟨1202172, by rfl⟩ : syracuseStep 3205793 = 2404345) B2404345
theorem B1306027 : Blo 666309 1306027 := bstep (se 1 (by rfl) ⟨979520, by rfl⟩ : syracuseStep 1306027 = 1959041) B1959041
theorem B5500553 : Blo 666309 5500553 := bstep (se 2 (by rfl) ⟨2062707, by rfl⟩ : syracuseStep 5500553 = 4125415) B4125415
theorem B2256551 : Blo 666309 2256551 := bstep (se 1 (by rfl) ⟨1692413, by rfl⟩ : syracuseStep 2256551 = 3384827) B3384827
theorem B4813019 : Blo 666309 4813019 := bstep (se 1 (by rfl) ⟨3609764, by rfl⟩ : syracuseStep 4813019 = 7219529) B7219529
theorem B1504223 : Blo 666309 1504223 := bstep (se 1 (by rfl) ⟨1128167, by rfl⟩ : syracuseStep 1504223 = 2256335) B2256335
theorem B6518717 : Blo 666309 6518717 := bstep (se 3 (by rfl) ⟨1222259, by rfl⟩ : syracuseStep 6518717 = 2444519) B2444519
theorem B2259035 : Blo 666309 2259035 := bstep (se 1 (by rfl) ⟨1694276, by rfl⟩ : syracuseStep 2259035 = 3388553) B3388553
theorem B1505519 : Blo 666309 1505519 := bstep (se 1 (by rfl) ⟨1129139, by rfl⟩ : syracuseStep 1505519 = 2258279) B2258279
theorem B752359 : Blo 666309 752359 := bstep (se 1 (by rfl) ⟨564269, by rfl⟩ : syracuseStep 752359 = 1128539) B1128539
theorem B8453177 : Blo 666309 8453177 := bstep (se 2 (by rfl) ⟨3169941, by rfl⟩ : syracuseStep 8453177 = 6339883) B6339883
theorem B11403017 : Blo 666309 11403017 := bstep (se 2 (by rfl) ⟨4276131, by rfl⟩ : syracuseStep 11403017 = 8552263) B8552263
theorem B1507175 : Blo 666309 1507175 := bstep (se 1 (by rfl) ⟨1130381, by rfl⟩ : syracuseStep 1507175 = 2260763) B2260763
theorem B1901551 : Blo 666309 1901551 := bstep (se 1 (by rfl) ⟨1426163, by rfl⟩ : syracuseStep 1901551 = 2852327) B2852327
theorem B1902781 : Blo 666309 1902781 := bstep (se 3 (by rfl) ⟨356771, by rfl⟩ : syracuseStep 1902781 = 713543) B713543
theorem B14879623 : Blo 666309 14879623 := bstep (se 1 (by rfl) ⟨11159717, by rfl⟩ : syracuseStep 14879623 = 22319435) B22319435
theorem B14453747 : Blo 666309 14453747 := bstep (se 1 (by rfl) ⟨10840310, by rfl⟩ : syracuseStep 14453747 = 21680621) B21680621
theorem B12882523 : Blo 666309 12882523 := bstep (se 1 (by rfl) ⟨9661892, by rfl⟩ : syracuseStep 12882523 = 19323785) B19323785
theorem B3806291 : Blo 666309 3806291 := bstep (se 1 (by rfl) ⟨2854718, by rfl⟩ : syracuseStep 3806291 = 5709437) B5709437
theorem B27366619 : Blo 666309 27366619 := bstep (se 1 (by rfl) ⟨20524964, by rfl⟩ : syracuseStep 27366619 = 41049929) B41049929
theorem B3806999 : Blo 666309 3806999 := bstep (se 1 (by rfl) ⟨2855249, by rfl⟩ : syracuseStep 3806999 = 5710499) B5710499
theorem B6167495 : Blo 666309 6167495 := bstep (se 1 (by rfl) ⟨4625621, by rfl⟩ : syracuseStep 6167495 = 9251243) B9251243
theorem B2137195 : Blo 666309 2137195 := bstep (se 1 (by rfl) ⟨1602896, by rfl⟩ : syracuseStep 2137195 = 3205793) B3205793
theorem B1907975 : Blo 666309 1907975 := bstep (se 1 (by rfl) ⟨1430981, by rfl⟩ : syracuseStep 1907975 = 2861963) B2861963
theorem B7415263 : Blo 666309 7415263 := bstep (se 1 (by rfl) ⟨5561447, by rfl⟩ : syracuseStep 7415263 = 11122895) B11122895
theorem B7317229 : Blo 666309 7317229 := bstep (se 3 (by rfl) ⟨1371980, by rfl⟩ : syracuseStep 7317229 = 2743961) B2743961
theorem B3615515 : Blo 666309 3615515 := bstep (se 1 (by rfl) ⟨2711636, by rfl⟩ : syracuseStep 3615515 = 5423273) B5423273
theorem B9612071 : Blo 666309 9612071 := bstep (se 1 (by rfl) ⟨7209053, by rfl⟩ : syracuseStep 9612071 = 14418107) B14418107
theorem B7613675 : Blo 666309 7613675 := bstep (se 1 (by rfl) ⟨5710256, by rfl⟩ : syracuseStep 7613675 = 11420513) B11420513
theorem B4074731 : Blo 666309 4074731 := bstep (se 1 (by rfl) ⟨3056048, by rfl⟩ : syracuseStep 4074731 = 6112097) B6112097
theorem B666875 : Blo 666309 666875 := bstep (se 1 (by rfl) ⟨500156, by rfl⟩ : syracuseStep 666875 = 1000313) B1000313
theorem B666907 : Blo 666309 666907 := bstep (se 1 (by rfl) ⟨500180, by rfl⟩ : syracuseStep 666907 = 1000361) B1000361
theorem B1322303 : Blo 666309 1322303 := bstep (se 1 (by rfl) ⟨991727, by rfl⟩ : syracuseStep 1322303 = 1983455) B1983455
theorem B30846419 : Blo 666309 30846419 := bstep (se 1 (by rfl) ⟨23134814, by rfl⟩ : syracuseStep 30846419 = 46269629) B46269629
theorem B2862647 : Blo 666309 2862647 := bstep (se 1 (by rfl) ⟨2146985, by rfl⟩ : syracuseStep 2862647 = 4293971) B4293971
theorem B667675 : Blo 666309 667675 := bstep (se 1 (by rfl) ⟨500756, by rfl⟩ : syracuseStep 667675 = 1001513) B1001513
theorem B668063 : Blo 666309 668063 := bstep (se 1 (by rfl) ⟨501047, by rfl⟩ : syracuseStep 668063 = 1002095) B1002095
theorem B668287 : Blo 666309 668287 := bstep (se 1 (by rfl) ⟨501215, by rfl⟩ : syracuseStep 668287 = 1002431) B1002431
theorem B668703 : Blo 666309 668703 := bstep (se 1 (by rfl) ⟨501527, by rfl⟩ : syracuseStep 668703 = 1003055) B1003055
theorem B668863 : Blo 666309 668863 := bstep (se 1 (by rfl) ⟨501647, by rfl⟩ : syracuseStep 668863 = 1003295) B1003295
theorem B668955 : Blo 666309 668955 := bstep (se 1 (by rfl) ⟨501716, by rfl⟩ : syracuseStep 668955 = 1003433) B1003433
theorem B669415 : Blo 666309 669415 := bstep (se 1 (by rfl) ⟨502061, by rfl⟩ : syracuseStep 669415 = 1004123) B1004123
theorem B7618049 : Blo 666309 7618049 := bstep (se 2 (by rfl) ⟨2856768, by rfl⟩ : syracuseStep 7618049 = 5713537) B5713537
theorem B999599 : Blo 666309 999599 := bstep (se 1 (by rfl) ⟨749699, by rfl⟩ : syracuseStep 999599 = 1499399) B1499399
theorem B2539745 : Blo 666309 2539745 := bstep (se 2 (by rfl) ⟨952404, by rfl⟩ : syracuseStep 2539745 = 1904809) B1904809
theorem B2146601 : Blo 666309 2146601 := bstep (se 2 (by rfl) ⟨804975, by rfl⟩ : syracuseStep 2146601 = 1609951) B1609951
theorem B1687999 : Blo 666309 1687999 := bstep (se 1 (by rfl) ⟨1265999, by rfl⟩ : syracuseStep 1687999 = 2531999) B2531999
theorem B1000475 : Blo 666309 1000475 := bstep (se 1 (by rfl) ⟨750356, by rfl⟩ : syracuseStep 1000475 = 1500713) B1500713
theorem B1000943 : Blo 666309 1000943 := bstep (se 1 (by rfl) ⟨750707, by rfl⟩ : syracuseStep 1000943 = 1501415) B1501415
theorem B6407819 : Blo 666309 6407819 := bstep (se 1 (by rfl) ⟨4805864, by rfl⟩ : syracuseStep 6407819 = 9611729) B9611729
theorem B1689599 : Blo 666309 1689599 := bstep (se 1 (by rfl) ⟨1267199, by rfl⟩ : syracuseStep 1689599 = 2534399) B2534399
theorem B6965477 : Blo 666309 6965477 := bstep (se 4 (by rfl) ⟨653013, by rfl⟩ : syracuseStep 6965477 = 1306027) B1306027
theorem B1002815 : Blo 666309 1002815 := bstep (se 1 (by rfl) ⟨752111, by rfl⟩ : syracuseStep 1002815 = 1504223) B1504223
theorem B1003145 : Blo 666309 1003145 := bstep (se 2 (by rfl) ⟨376179, by rfl⟩ : syracuseStep 1003145 = 752359) B752359
theorem B4345811 : Blo 666309 4345811 := bstep (se 1 (by rfl) ⟨3259358, by rfl⟩ : syracuseStep 4345811 = 6518717) B6518717
theorem B1003679 : Blo 666309 1003679 := bstep (se 1 (by rfl) ⟨752759, by rfl⟩ : syracuseStep 1003679 = 1505519) B1505519
theorem B14668141 : Blo 666309 14668141 := bstep (se 3 (by rfl) ⟨2750276, by rfl⟩ : syracuseStep 14668141 = 5500553) B5500553
theorem B1004783 : Blo 666309 1004783 := bstep (se 1 (by rfl) ⟨753587, by rfl⟩ : syracuseStep 1004783 = 1507175) B1507175
theorem B1004927 : Blo 666309 1004927 := bstep (se 1 (by rfl) ⟨753695, by rfl⟩ : syracuseStep 1004927 = 1507391) B1507391
theorem B2250935 : Blo 666309 2250935 := bstep (se 1 (by rfl) ⟨1688201, by rfl⟩ : syracuseStep 2250935 = 3376403) B3376403
theorem B14440943 : Blo 666309 14440943 := bstep (se 1 (by rfl) ⟨10830707, by rfl⟩ : syracuseStep 14440943 = 21661415) B21661415
theorem B5692625 : Blo 666309 5692625 := bstep (se 2 (by rfl) ⟨2134734, by rfl⟩ : syracuseStep 5692625 = 4269469) B4269469
theorem B712091 : Blo 666309 712091 := bstep (se 1 (by rfl) ⟨534068, by rfl⟩ : syracuseStep 712091 = 1068137) B1068137
theorem B4054511 : Blo 666309 4054511 := bstep (se 1 (by rfl) ⟨3040883, by rfl⟩ : syracuseStep 4054511 = 6081767) B6081767
theorem B3039353 : Blo 666309 3039353 := bstep (se 2 (by rfl) ⟨1139757, by rfl⟩ : syracuseStep 3039353 = 2279515) B2279515
theorem B1499471 : Blo 666309 1499471 := bstep (se 1 (by rfl) ⟨1124603, by rfl⟩ : syracuseStep 1499471 = 2249207) B2249207
theorem B1499615 : Blo 666309 1499615 := bstep (se 1 (by rfl) ⟨1124711, by rfl⟩ : syracuseStep 1499615 = 2249423) B2249423
theorem B1499705 : Blo 666309 1499705 := bstep (se 2 (by rfl) ⟨562389, by rfl⟩ : syracuseStep 1499705 = 1124779) B1124779
theorem B8578871 : Blo 666309 8578871 := bstep (se 1 (by rfl) ⟨6434153, by rfl⟩ : syracuseStep 8578871 = 12868307) B12868307
theorem B812911 : Blo 666309 812911 := bstep (se 1 (by rfl) ⟨609683, by rfl⟩ : syracuseStep 812911 = 1219367) B1219367
theorem B846055 : Blo 666309 846055 := bstep (se 1 (by rfl) ⟨634541, by rfl⟩ : syracuseStep 846055 = 1269083) B1269083
theorem B2255687 : Blo 666309 2255687 := bstep (se 1 (by rfl) ⟨1691765, by rfl⟩ : syracuseStep 2255687 = 3383531) B3383531
theorem B11561939 : Blo 666309 11561939 := bstep (se 1 (by rfl) ⟨8671454, by rfl⟩ : syracuseStep 11561939 = 17342909) B17342909
theorem B1503215 : Blo 666309 1503215 := bstep (se 1 (by rfl) ⟨1127411, by rfl⟩ : syracuseStep 1503215 = 2254823) B2254823
theorem B2027645 : Blo 666309 2027645 := bstep (se 3 (by rfl) ⟨380183, by rfl⟩ : syracuseStep 2027645 = 760367) B760367
theorem B1504367 : Blo 666309 1504367 := bstep (se 1 (by rfl) ⟨1128275, by rfl⟩ : syracuseStep 1504367 = 2256551) B2256551
theorem B3208679 : Blo 666309 3208679 := bstep (se 1 (by rfl) ⟨2406509, by rfl⟩ : syracuseStep 3208679 = 4813019) B4813019
theorem B1505249 : Blo 666309 1505249 := bstep (se 2 (by rfl) ⟨564468, by rfl⟩ : syracuseStep 1505249 = 1128937) B1128937
theorem B2259359 : Blo 666309 2259359 := bstep (se 1 (by rfl) ⟨1694519, by rfl⟩ : syracuseStep 2259359 = 3389039) B3389039
theorem B1506023 : Blo 666309 1506023 := bstep (se 1 (by rfl) ⟨1129517, by rfl⟩ : syracuseStep 1506023 = 2259035) B2259035
theorem B5635451 : Blo 666309 5635451 := bstep (se 1 (by rfl) ⟨4226588, by rfl⟩ : syracuseStep 5635451 = 8453177) B8453177
theorem B7602011 : Blo 666309 7602011 := bstep (se 1 (by rfl) ⟨5701508, by rfl⟩ : syracuseStep 7602011 = 11403017) B11403017
theorem B753511 : Blo 666309 753511 := bstep (se 1 (by rfl) ⟨565133, by rfl⟩ : syracuseStep 753511 = 1130267) B1130267
theorem B9635831 : Blo 666309 9635831 := bstep (se 1 (by rfl) ⟨7226873, by rfl⟩ : syracuseStep 9635831 = 14453747) B14453747
theorem B1083881 : Blo 666309 1083881 := bstep (se 2 (by rfl) ⟨406455, by rfl⟩ : syracuseStep 1083881 = 812911) B812911
theorem B17176697 : Blo 666309 17176697 := bstep (se 2 (by rfl) ⟨6441261, by rfl⟩ : syracuseStep 17176697 = 12882523) B12882523
theorem B7707959 : Blo 666309 7707959 := bstep (se 1 (by rfl) ⟨5780969, by rfl⟩ : syracuseStep 7707959 = 11561939) B11561939
theorem B1908431 : Blo 666309 1908431 := bstep (se 1 (by rfl) ⟨1431323, by rfl⟩ : syracuseStep 1908431 = 2862647) B2862647
theorem B1351763 : Blo 666309 1351763 := bstep (se 1 (by rfl) ⟨1013822, by rfl⟩ : syracuseStep 1351763 = 2027645) B2027645
theorem B5087933 : Blo 666309 5087933 := bstep (se 3 (by rfl) ⟨953987, by rfl⟩ : syracuseStep 5087933 = 1907975) B1907975
theorem B2139119 : Blo 666309 2139119 := bstep (se 1 (by rfl) ⟨1604339, by rfl⟩ : syracuseStep 2139119 = 3208679) B3208679
theorem B666399 : Blo 666309 666399 := bstep (se 1 (by rfl) ⟨499799, by rfl⟩ : syracuseStep 666399 = 999599) B999599
theorem B666983 : Blo 666309 666983 := bstep (se 1 (by rfl) ⟨500237, by rfl⟩ : syracuseStep 666983 = 1000475) B1000475
theorem B667295 : Blo 666309 667295 := bstep (se 1 (by rfl) ⟨500471, by rfl⟩ : syracuseStep 667295 = 1000943) B1000943
theorem B4271879 : Blo 666309 4271879 := bstep (se 1 (by rfl) ⟨3203909, by rfl⟩ : syracuseStep 4271879 = 6407819) B6407819
theorem B2535401 : Blo 666309 2535401 := bstep (se 2 (by rfl) ⟨950775, by rfl⟩ : syracuseStep 2535401 = 1901551) B1901551
theorem B1126399 : Blo 666309 1126399 := bstep (se 1 (by rfl) ⟨844799, by rfl⟩ : syracuseStep 1126399 = 1689599) B1689599
theorem B668543 : Blo 666309 668543 := bstep (se 1 (by rfl) ⟨501407, by rfl⟩ : syracuseStep 668543 = 1002815) B1002815
theorem B668763 : Blo 666309 668763 := bstep (se 1 (by rfl) ⟨501572, by rfl⟩ : syracuseStep 668763 = 1003145) B1003145
theorem B2897207 : Blo 666309 2897207 := bstep (se 1 (by rfl) ⟨2172905, by rfl⟩ : syracuseStep 2897207 = 4345811) B4345811
theorem B669119 : Blo 666309 669119 := bstep (se 1 (by rfl) ⟨501839, by rfl⟩ : syracuseStep 669119 = 1003679) B1003679
theorem B2537041 : Blo 666309 2537041 := bstep (se 2 (by rfl) ⟨951390, by rfl⟩ : syracuseStep 2537041 = 1902781) B1902781
theorem B1128073 : Blo 666309 1128073 := bstep (se 2 (by rfl) ⟨423027, by rfl⟩ : syracuseStep 1128073 = 846055) B846055
theorem B2537527 : Blo 666309 2537527 := bstep (se 1 (by rfl) ⟨1903145, by rfl⟩ : syracuseStep 2537527 = 3806291) B3806291
theorem B669855 : Blo 666309 669855 := bstep (se 1 (by rfl) ⟨502391, by rfl⟩ : syracuseStep 669855 = 1004783) B1004783
theorem B669951 : Blo 666309 669951 := bstep (se 1 (by rfl) ⟨502463, by rfl⟩ : syracuseStep 669951 = 1004927) B1004927
theorem B19839497 : Blo 666309 19839497 := bstep (se 2 (by rfl) ⟨7439811, by rfl⟩ : syracuseStep 19839497 = 14879623) B14879623
theorem B2537999 : Blo 666309 2537999 := bstep (se 1 (by rfl) ⟨1903499, by rfl⟩ : syracuseStep 2537999 = 3806999) B3806999
theorem B4111663 : Blo 666309 4111663 := bstep (se 1 (by rfl) ⟨3083747, by rfl⟩ : syracuseStep 4111663 = 6167495) B6167495
theorem B2703007 : Blo 666309 2703007 := bstep (se 1 (by rfl) ⟨2027255, by rfl⟩ : syracuseStep 2703007 = 4054511) B4054511
theorem B999647 : Blo 666309 999647 := bstep (se 1 (by rfl) ⟨749735, by rfl⟩ : syracuseStep 999647 = 1499471) B1499471
theorem B999743 : Blo 666309 999743 := bstep (se 1 (by rfl) ⟨749807, by rfl⟩ : syracuseStep 999743 = 1499615) B1499615
theorem B999803 : Blo 666309 999803 := bstep (se 1 (by rfl) ⟨749852, by rfl⟩ : syracuseStep 999803 = 1499705) B1499705
theorem B5719247 : Blo 666309 5719247 := bstep (se 1 (by rfl) ⟨4289435, by rfl⟩ : syracuseStep 5719247 = 8578871) B8578871
theorem B36488825 : Blo 666309 36488825 := bstep (se 2 (by rfl) ⟨13683309, by rfl⟩ : syracuseStep 36488825 = 27366619) B27366619
theorem B2410343 : Blo 666309 2410343 := bstep (se 1 (by rfl) ⟨1807757, by rfl⟩ : syracuseStep 2410343 = 3615515) B3615515
theorem B6408047 : Blo 666309 6408047 := bstep (se 1 (by rfl) ⟨4806035, by rfl⟩ : syracuseStep 6408047 = 9612071) B9612071
theorem B20564279 : Blo 666309 20564279 := bstep (se 1 (by rfl) ⟨15423209, by rfl⟩ : syracuseStep 20564279 = 30846419) B30846419
theorem B1002143 : Blo 666309 1002143 := bstep (se 1 (by rfl) ⟨751607, by rfl⟩ : syracuseStep 1002143 = 1503215) B1503215
theorem B1002911 : Blo 666309 1002911 := bstep (se 1 (by rfl) ⟨752183, by rfl⟩ : syracuseStep 1002911 = 1504367) B1504367
theorem B3526141 : Blo 666309 3526141 := bstep (se 3 (by rfl) ⟨661151, by rfl⟩ : syracuseStep 3526141 = 1322303) B1322303
theorem B15027869 : Blo 666309 15027869 := bstep (se 3 (by rfl) ⟨2817725, by rfl⟩ : syracuseStep 15027869 = 5635451) B5635451
theorem B1003499 : Blo 666309 1003499 := bstep (se 1 (by rfl) ⟨752624, by rfl⟩ : syracuseStep 1003499 = 1505249) B1505249
theorem B1004015 : Blo 666309 1004015 := bstep (se 1 (by rfl) ⟨753011, by rfl⟩ : syracuseStep 1004015 = 1506023) B1506023
theorem B1004681 : Blo 666309 1004681 := bstep (se 2 (by rfl) ⟨376755, by rfl⟩ : syracuseStep 1004681 = 753511) B753511
theorem B5068007 : Blo 666309 5068007 := bstep (se 1 (by rfl) ⟨3801005, by rfl⟩ : syracuseStep 5068007 = 7602011) B7602011
theorem B1693163 : Blo 666309 1693163 := bstep (se 1 (by rfl) ⟨1269872, by rfl⟩ : syracuseStep 1693163 = 2539745) B2539745
theorem B2250665 : Blo 666309 2250665 := bstep (se 2 (by rfl) ⟨843999, by rfl⟩ : syracuseStep 2250665 = 1687999) B1687999
theorem B5724269 : Blo 666309 5724269 := bstep (se 3 (by rfl) ⟨1073300, by rfl⟩ : syracuseStep 5724269 = 2146601) B2146601
theorem B4643651 : Blo 666309 4643651 := bstep (se 1 (by rfl) ⟨3482738, by rfl⟩ : syracuseStep 4643651 = 6965477) B6965477
theorem B9887017 : Blo 666309 9887017 := bstep (se 2 (by rfl) ⟨3707631, by rfl⟩ : syracuseStep 9887017 = 7415263) B7415263
theorem B9756305 : Blo 666309 9756305 := bstep (se 2 (by rfl) ⟨3658614, by rfl⟩ : syracuseStep 9756305 = 7317229) B7317229
theorem B1500623 : Blo 666309 1500623 := bstep (se 1 (by rfl) ⟨1125467, by rfl⟩ : syracuseStep 1500623 = 2250935) B2250935
theorem B9627295 : Blo 666309 9627295 := bstep (se 1 (by rfl) ⟨7220471, by rfl⟩ : syracuseStep 9627295 = 14440943) B14440943
theorem B3795083 : Blo 666309 3795083 := bstep (se 1 (by rfl) ⟨2846312, by rfl⟩ : syracuseStep 3795083 = 5692625) B5692625
theorem B2026235 : Blo 666309 2026235 := bstep (se 1 (by rfl) ⟨1519676, by rfl⟩ : syracuseStep 2026235 = 3039353) B3039353
theorem B19557521 : Blo 666309 19557521 := bstep (se 2 (by rfl) ⟨7334070, by rfl⟩ : syracuseStep 19557521 = 14668141) B14668141
theorem B1503791 : Blo 666309 1503791 := bstep (se 1 (by rfl) ⟨1127843, by rfl⟩ : syracuseStep 1503791 = 2255687) B2255687
theorem B5075783 : Blo 666309 5075783 := bstep (se 1 (by rfl) ⟨3806837, by rfl⟩ : syracuseStep 5075783 = 7613675) B7613675
theorem B2716487 : Blo 666309 2716487 := bstep (se 1 (by rfl) ⟨2037365, by rfl⟩ : syracuseStep 2716487 = 4074731) B4074731
theorem B1898909 : Blo 666309 1898909 := bstep (se 3 (by rfl) ⟨356045, by rfl⟩ : syracuseStep 1898909 = 712091) B712091
theorem B2849593 : Blo 666309 2849593 := bstep (se 2 (by rfl) ⟨1068597, by rfl⟩ : syracuseStep 2849593 = 2137195) B2137195
theorem B1506239 : Blo 666309 1506239 := bstep (se 1 (by rfl) ⟨1129679, by rfl⟩ : syracuseStep 1506239 = 2259359) B2259359
theorem B5078699 : Blo 666309 5078699 := bstep (se 1 (by rfl) ⟨3809024, by rfl⟩ : syracuseStep 5078699 = 7618049) B7618049
theorem B1606895 : Blo 666309 1606895 := bstep (se 1 (by rfl) ⟨1205171, by rfl⟩ : syracuseStep 1606895 = 2410343) B2410343
theorem B6423887 : Blo 666309 6423887 := bstep (se 1 (by rfl) ⟨4817915, by rfl⟩ : syracuseStep 6423887 = 9635831) B9635831
theorem B3378671 : Blo 666309 3378671 := bstep (se 1 (by rfl) ⟨2534003, by rfl⟩ : syracuseStep 3378671 = 5068007) B5068007
theorem B2890349 : Blo 666309 2890349 := bstep (se 3 (by rfl) ⟨541940, by rfl⟩ : syracuseStep 2890349 = 1083881) B1083881
theorem B2530055 : Blo 666309 2530055 := bstep (se 1 (by rfl) ⟨1897541, by rfl⟩ : syracuseStep 2530055 = 3795083) B3795083
theorem B3382721 : Blo 666309 3382721 := bstep (se 2 (by rfl) ⟨1268520, by rfl⟩ : syracuseStep 3382721 = 2537041) B2537041
theorem B3383369 : Blo 666309 3383369 := bstep (se 2 (by rfl) ⟨1268763, by rfl⟩ : syracuseStep 3383369 = 2537527) B2537527
theorem B3383855 : Blo 666309 3383855 := bstep (se 1 (by rfl) ⟨2537891, by rfl⟩ : syracuseStep 3383855 = 5075783) B5075783
theorem B1810991 : Blo 666309 1810991 := bstep (se 1 (by rfl) ⟨1358243, by rfl⟩ : syracuseStep 1810991 = 2716487) B2716487
theorem B13182689 : Blo 666309 13182689 := bstep (se 2 (by rfl) ⟨4943508, by rfl⟩ : syracuseStep 13182689 = 9887017) B9887017
theorem B5482217 : Blo 666309 5482217 := bstep (se 2 (by rfl) ⟨2055831, by rfl⟩ : syracuseStep 5482217 = 4111663) B4111663
theorem B3385799 : Blo 666309 3385799 := bstep (se 1 (by rfl) ⟨2539349, by rfl⟩ : syracuseStep 3385799 = 5078699) B5078699
theorem B666431 : Blo 666309 666431 := bstep (se 1 (by rfl) ⟨499823, by rfl⟩ : syracuseStep 666431 = 999647) B999647
theorem B666495 : Blo 666309 666495 := bstep (se 1 (by rfl) ⟨499871, by rfl⟩ : syracuseStep 666495 = 999743) B999743
theorem B666535 : Blo 666309 666535 := bstep (se 1 (by rfl) ⟨499901, by rfl⟩ : syracuseStep 666535 = 999803) B999803
theorem B3812831 : Blo 666309 3812831 := bstep (se 1 (by rfl) ⟨2859623, by rfl⟩ : syracuseStep 3812831 = 5719247) B5719247
theorem B24325883 : Blo 666309 24325883 := bstep (se 1 (by rfl) ⟨18244412, by rfl⟩ : syracuseStep 24325883 = 36488825) B36488825
theorem B4272031 : Blo 666309 4272031 := bstep (se 1 (by rfl) ⟨3204023, by rfl⟩ : syracuseStep 4272031 = 6408047) B6408047
theorem B13709519 : Blo 666309 13709519 := bstep (se 1 (by rfl) ⟨10282139, by rfl⟩ : syracuseStep 13709519 = 20564279) B20564279
theorem B668095 : Blo 666309 668095 := bstep (se 1 (by rfl) ⟨501071, by rfl⟩ : syracuseStep 668095 = 1002143) B1002143
theorem B668607 : Blo 666309 668607 := bstep (se 1 (by rfl) ⟨501455, by rfl⟩ : syracuseStep 668607 = 1002911) B1002911
theorem B668999 : Blo 666309 668999 := bstep (se 1 (by rfl) ⟨501749, by rfl⟩ : syracuseStep 668999 = 1003499) B1003499
theorem B669343 : Blo 666309 669343 := bstep (se 1 (by rfl) ⟨502007, by rfl⟩ : syracuseStep 669343 = 1004015) B1004015
theorem B669787 : Blo 666309 669787 := bstep (se 1 (by rfl) ⟨502340, by rfl⟩ : syracuseStep 669787 = 1004681) B1004681
theorem B1128775 : Blo 666309 1128775 := bstep (se 1 (by rfl) ⟨846581, by rfl⟩ : syracuseStep 1128775 = 1693163) B1693163
theorem B3816179 : Blo 666309 3816179 := bstep (se 1 (by rfl) ⟨2862134, by rfl⟩ : syracuseStep 3816179 = 5724269) B5724269
theorem B11451131 : Blo 666309 11451131 := bstep (se 1 (by rfl) ⟨8588348, by rfl⟩ : syracuseStep 11451131 = 17176697) B17176697
theorem B3095767 : Blo 666309 3095767 := bstep (se 1 (by rfl) ⟨2321825, by rfl⟩ : syracuseStep 3095767 = 4643651) B4643651
theorem B4701521 : Blo 666309 4701521 := bstep (se 2 (by rfl) ⟨1763070, by rfl⟩ : syracuseStep 4701521 = 3526141) B3526141
theorem B6504203 : Blo 666309 6504203 := bstep (se 1 (by rfl) ⟨4878152, by rfl⟩ : syracuseStep 6504203 = 9756305) B9756305
theorem B901175 : Blo 666309 901175 := bstep (se 1 (by rfl) ⟨675881, by rfl⟩ : syracuseStep 901175 = 1351763) B1351763
theorem B3391955 : Blo 666309 3391955 := bstep (se 1 (by rfl) ⟨2543966, by rfl⟩ : syracuseStep 3391955 = 5087933) B5087933
theorem B1426079 : Blo 666309 1426079 := bstep (se 1 (by rfl) ⟨1069559, by rfl⟩ : syracuseStep 1426079 = 2139119) B2139119
theorem B1000415 : Blo 666309 1000415 := bstep (se 1 (by rfl) ⟨750311, by rfl⟩ : syracuseStep 1000415 = 1500623) B1500623
theorem B52905325 : Blo 666309 52905325 := bstep (se 3 (by rfl) ⟨9919748, by rfl⟩ : syracuseStep 52905325 = 19839497) B19839497
theorem B1690267 : Blo 666309 1690267 := bstep (se 1 (by rfl) ⟨1267700, by rfl⟩ : syracuseStep 1690267 = 2535401) B2535401
theorem B1002527 : Blo 666309 1002527 := bstep (se 1 (by rfl) ⟨751895, by rfl⟩ : syracuseStep 1002527 = 1503791) B1503791
theorem B1265939 : Blo 666309 1265939 := bstep (se 1 (by rfl) ⟨949454, by rfl⟩ : syracuseStep 1265939 = 1898909) B1898909
theorem B1691999 : Blo 666309 1691999 := bstep (se 1 (by rfl) ⟨1268999, by rfl⟩ : syracuseStep 1691999 = 2537999) B2537999
theorem B1004159 : Blo 666309 1004159 := bstep (se 1 (by rfl) ⟨753119, by rfl⟩ : syracuseStep 1004159 = 1506239) B1506239
theorem B12836393 : Blo 666309 12836393 := bstep (se 2 (by rfl) ⟨4813647, by rfl⟩ : syracuseStep 12836393 = 9627295) B9627295
theorem B10018579 : Blo 666309 10018579 := bstep (se 1 (by rfl) ⟨7513934, by rfl⟩ : syracuseStep 10018579 = 15027869) B15027869
theorem B1500443 : Blo 666309 1500443 := bstep (se 1 (by rfl) ⟨1125332, by rfl⟩ : syracuseStep 1500443 = 2250665) B2250665
theorem B5138639 : Blo 666309 5138639 := bstep (se 1 (by rfl) ⟨3853979, by rfl⟩ : syracuseStep 5138639 = 7707959) B7707959
theorem B1272287 : Blo 666309 1272287 := bstep (se 1 (by rfl) ⟨954215, by rfl⟩ : syracuseStep 1272287 = 1908431) B1908431
theorem B1501865 : Blo 666309 1501865 := bstep (se 2 (by rfl) ⟨563199, by rfl⟩ : syracuseStep 1501865 = 1126399) B1126399
theorem B5403293 : Blo 666309 5403293 := bstep (se 3 (by rfl) ⟨1013117, by rfl⟩ : syracuseStep 5403293 = 2026235) B2026235
theorem B13038347 : Blo 666309 13038347 := bstep (se 1 (by rfl) ⟨9778760, by rfl⟩ : syracuseStep 13038347 = 19557521) B19557521
theorem B1504097 : Blo 666309 1504097 := bstep (se 2 (by rfl) ⟨564036, by rfl⟩ : syracuseStep 1504097 = 1128073) B1128073
theorem B2847919 : Blo 666309 2847919 := bstep (se 1 (by rfl) ⟨2135939, by rfl⟩ : syracuseStep 2847919 = 4271879) B4271879
theorem B1931471 : Blo 666309 1931471 := bstep (se 1 (by rfl) ⟨1448603, by rfl⟩ : syracuseStep 1931471 = 2897207) B2897207
theorem B3799457 : Blo 666309 3799457 := bstep (se 2 (by rfl) ⟨1424796, by rfl⟩ : syracuseStep 3799457 = 2849593) B2849593
theorem B3604009 : Blo 666309 3604009 := bstep (se 2 (by rfl) ⟨1351503, by rfl⟩ : syracuseStep 3604009 = 2703007) B2703007
theorem B2261303 : Blo 666309 2261303 := bstep (se 1 (by rfl) ⟨1695977, by rfl⟩ : syracuseStep 2261303 = 3391955) B3391955
theorem B950719 : Blo 666309 950719 := bstep (se 1 (by rfl) ⟨713039, by rfl⟩ : syracuseStep 950719 = 1426079) B1426079
theorem B8557595 : Blo 666309 8557595 := bstep (se 1 (by rfl) ⟨6418196, by rfl⟩ : syracuseStep 8557595 = 12836393) B12836393
theorem B8788459 : Blo 666309 8788459 := bstep (se 1 (by rfl) ⟨6591344, by rfl⟩ : syracuseStep 8788459 = 13182689) B13182689
theorem B8692231 : Blo 666309 8692231 := bstep (se 1 (by rfl) ⟨6519173, by rfl⟩ : syracuseStep 8692231 = 13038347) B13038347
theorem B1287647 : Blo 666309 1287647 := bstep (se 1 (by rfl) ⟨965735, by rfl⟩ : syracuseStep 1287647 = 1931471) B1931471
theorem B2532971 : Blo 666309 2532971 := bstep (se 1 (by rfl) ⟨1899728, by rfl⟩ : syracuseStep 2532971 = 3799457) B3799457
theorem B4336135 : Blo 666309 4336135 := bstep (se 1 (by rfl) ⟨3252101, by rfl⟩ : syracuseStep 4336135 = 6504203) B6504203
theorem B9612533 : Blo 666309 9612533 := bstep (se 5 (by rfl) ⟨450587, by rfl⟩ : syracuseStep 9612533 = 901175) B901175
theorem B666943 : Blo 666309 666943 := bstep (se 1 (by rfl) ⟨500207, by rfl⟩ : syracuseStep 666943 = 1000415) B1000415
theorem B668351 : Blo 666309 668351 := bstep (se 1 (by rfl) ⟨501263, by rfl⟩ : syracuseStep 668351 = 1002527) B1002527
theorem B1127999 : Blo 666309 1127999 := bstep (se 1 (by rfl) ⟨845999, by rfl⟩ : syracuseStep 1127999 = 1691999) B1691999
theorem B669439 : Blo 666309 669439 := bstep (se 1 (by rfl) ⟨502079, by rfl⟩ : syracuseStep 669439 = 1004159) B1004159
theorem B1686703 : Blo 666309 1686703 := bstep (se 1 (by rfl) ⟨1265027, by rfl⟩ : syracuseStep 1686703 = 2530055) B2530055
theorem B1000295 : Blo 666309 1000295 := bstep (se 1 (by rfl) ⟨750221, by rfl⟩ : syracuseStep 1000295 = 1500443) B1500443
theorem B3654811 : Blo 666309 3654811 := bstep (se 1 (by rfl) ⟨2741108, by rfl⟩ : syracuseStep 3654811 = 5482217) B5482217
theorem B3392765 : Blo 666309 3392765 := bstep (se 3 (by rfl) ⟨636143, by rfl⟩ : syracuseStep 3392765 = 1272287) B1272287
theorem B3425759 : Blo 666309 3425759 := bstep (se 1 (by rfl) ⟨2569319, by rfl⟩ : syracuseStep 3425759 = 5138639) B5138639
theorem B1001243 : Blo 666309 1001243 := bstep (se 1 (by rfl) ⟨750932, by rfl⟩ : syracuseStep 1001243 = 1501865) B1501865
theorem B2541887 : Blo 666309 2541887 := bstep (se 1 (by rfl) ⟨1906415, by rfl⟩ : syracuseStep 2541887 = 3812831) B3812831
theorem B1002731 : Blo 666309 1002731 := bstep (se 1 (by rfl) ⟨752048, by rfl⟩ : syracuseStep 1002731 = 1504097) B1504097
theorem B12537389 : Blo 666309 12537389 := bstep (se 3 (by rfl) ⟨2350760, by rfl⟩ : syracuseStep 12537389 = 4701521) B4701521
theorem B2544119 : Blo 666309 2544119 := bstep (se 1 (by rfl) ⟨1908089, by rfl⟩ : syracuseStep 2544119 = 3816179) B3816179
theorem B4805345 : Blo 666309 4805345 := bstep (se 2 (by rfl) ⟨1802004, by rfl⟩ : syracuseStep 4805345 = 3604009) B3604009
theorem B13358105 : Blo 666309 13358105 := bstep (se 2 (by rfl) ⟨5009289, by rfl⟩ : syracuseStep 13358105 = 10018579) B10018579
theorem B1071263 : Blo 666309 1071263 := bstep (se 1 (by rfl) ⟨803447, by rfl⟩ : syracuseStep 1071263 = 1606895) B1606895
theorem B4282591 : Blo 666309 4282591 := bstep (se 1 (by rfl) ⟨3211943, by rfl⟩ : syracuseStep 4282591 = 6423887) B6423887
theorem B70540433 : Blo 666309 70540433 := bstep (se 2 (by rfl) ⟨26452662, by rfl⟩ : syracuseStep 70540433 = 52905325) B52905325
theorem B2252447 : Blo 666309 2252447 := bstep (se 1 (by rfl) ⟨1689335, by rfl⟩ : syracuseStep 2252447 = 3378671) B3378671
theorem B843959 : Blo 666309 843959 := bstep (se 1 (by rfl) ⟨632969, by rfl⟩ : syracuseStep 843959 = 1265939) B1265939
theorem B2253689 : Blo 666309 2253689 := bstep (se 2 (by rfl) ⟨845133, by rfl⟩ : syracuseStep 2253689 = 1690267) B1690267
theorem B1926899 : Blo 666309 1926899 := bstep (se 1 (by rfl) ⟨1445174, by rfl⟩ : syracuseStep 1926899 = 2890349) B2890349
theorem B2255147 : Blo 666309 2255147 := bstep (se 1 (by rfl) ⟨1691360, by rfl⟩ : syracuseStep 2255147 = 3382721) B3382721
theorem B5696041 : Blo 666309 5696041 := bstep (se 2 (by rfl) ⟨2136015, by rfl⟩ : syracuseStep 5696041 = 4272031) B4272031
theorem B2255579 : Blo 666309 2255579 := bstep (se 1 (by rfl) ⟨1691684, by rfl⟩ : syracuseStep 2255579 = 3383369) B3383369
theorem B2255903 : Blo 666309 2255903 := bstep (se 1 (by rfl) ⟨1691927, by rfl⟩ : syracuseStep 2255903 = 3383855) B3383855
theorem B1207327 : Blo 666309 1207327 := bstep (se 1 (by rfl) ⟨905495, by rfl⟩ : syracuseStep 1207327 = 1810991) B1810991
theorem B3797225 : Blo 666309 3797225 := bstep (se 2 (by rfl) ⟨1423959, by rfl⟩ : syracuseStep 3797225 = 2847919) B2847919
theorem B2257199 : Blo 666309 2257199 := bstep (se 1 (by rfl) ⟨1692899, by rfl⟩ : syracuseStep 2257199 = 3385799) B3385799
theorem B16217255 : Blo 666309 16217255 := bstep (se 1 (by rfl) ⟨12162941, by rfl⟩ : syracuseStep 16217255 = 24325883) B24325883
theorem B9139679 : Blo 666309 9139679 := bstep (se 1 (by rfl) ⟨6854759, by rfl⟩ : syracuseStep 9139679 = 13709519) B13709519
theorem B1505033 : Blo 666309 1505033 := bstep (se 2 (by rfl) ⟨564387, by rfl⟩ : syracuseStep 1505033 = 1128775) B1128775
theorem B3602195 : Blo 666309 3602195 := bstep (se 1 (by rfl) ⟨2701646, by rfl⟩ : syracuseStep 3602195 = 5403293) B5403293
theorem B4127689 : Blo 666309 4127689 := bstep (se 2 (by rfl) ⟨1547883, by rfl⟩ : syracuseStep 4127689 = 3095767) B3095767
theorem B7634087 : Blo 666309 7634087 := bstep (se 1 (by rfl) ⟨5725565, by rfl⟩ : syracuseStep 7634087 = 11451131) B11451131
theorem B92504213 : Blo 666309 92504213 := bstep (se 6 (by rfl) ⟨2168067, by rfl⟩ : syracuseStep 92504213 = 4336135) B4336135
theorem B1507535 : Blo 666309 1507535 := bstep (se 1 (by rfl) ⟨1130651, by rfl⟩ : syracuseStep 1507535 = 2261303) B2261303
theorem B2261843 : Blo 666309 2261843 := bstep (se 1 (by rfl) ⟨1696382, by rfl⟩ : syracuseStep 2261843 = 3392765) B3392765
theorem B5705063 : Blo 666309 5705063 := bstep (se 1 (by rfl) ⟨4278797, by rfl⟩ : syracuseStep 5705063 = 8557595) B8557595
theorem B1609769 : Blo 666309 1609769 := bstep (se 2 (by rfl) ⟨603663, by rfl⟩ : syracuseStep 1609769 = 1207327) B1207327
theorem B47026955 : Blo 666309 47026955 := bstep (se 1 (by rfl) ⟨35270216, by rfl⟩ : syracuseStep 47026955 = 70540433) B70540433
theorem B2856701 : Blo 666309 2856701 := bstep (se 3 (by rfl) ⟨535631, by rfl⟩ : syracuseStep 2856701 = 1071263) B1071263
theorem B858431 : Blo 666309 858431 := bstep (se 1 (by rfl) ⟨643823, by rfl⟩ : syracuseStep 858431 = 1287647) B1287647
theorem B1284599 : Blo 666309 1284599 := bstep (se 1 (by rfl) ⟨963449, by rfl⟩ : syracuseStep 1284599 = 1926899) B1926899
theorem B2531483 : Blo 666309 2531483 := bstep (se 1 (by rfl) ⟨1898612, by rfl⟩ : syracuseStep 2531483 = 3797225) B3797225
theorem B5710121 : Blo 666309 5710121 := bstep (se 2 (by rfl) ⟨2141295, by rfl⟩ : syracuseStep 5710121 = 4282591) B4282591
theorem B2401463 : Blo 666309 2401463 := bstep (se 1 (by rfl) ⟨1801097, by rfl⟩ : syracuseStep 2401463 = 3602195) B3602195
theorem B33433037 : Blo 666309 33433037 := bstep (se 3 (by rfl) ⟨6268694, by rfl⟩ : syracuseStep 33433037 = 12537389) B12537389
theorem B5089391 : Blo 666309 5089391 := bstep (se 1 (by rfl) ⟨3817043, by rfl⟩ : syracuseStep 5089391 = 7634087) B7634087
theorem B666863 : Blo 666309 666863 := bstep (se 1 (by rfl) ⟨500147, by rfl⟩ : syracuseStep 666863 = 1000295) B1000295
theorem B667495 : Blo 666309 667495 := bstep (se 1 (by rfl) ⟨500621, by rfl⟩ : syracuseStep 667495 = 1001243) B1001243
theorem B668487 : Blo 666309 668487 := bstep (se 1 (by rfl) ⟨501365, by rfl⟩ : syracuseStep 668487 = 1002731) B1002731
theorem B1688647 : Blo 666309 1688647 := bstep (se 1 (by rfl) ⟨1266485, by rfl⟩ : syracuseStep 1688647 = 2532971) B2532971
theorem B6408355 : Blo 666309 6408355 := bstep (se 1 (by rfl) ⟨4806266, by rfl⟩ : syracuseStep 6408355 = 9612533) B9612533
theorem B11717945 : Blo 666309 11717945 := bstep (se 2 (by rfl) ⟨4394229, by rfl⟩ : syracuseStep 11717945 = 8788459) B8788459
theorem B1003355 : Blo 666309 1003355 := bstep (se 1 (by rfl) ⟨752516, by rfl⟩ : syracuseStep 1003355 = 1505033) B1505033
theorem B2248937 : Blo 666309 2248937 := bstep (se 2 (by rfl) ⟨843351, by rfl⟩ : syracuseStep 2248937 = 1686703) B1686703
theorem B2250557 : Blo 666309 2250557 := bstep (se 3 (by rfl) ⟨421979, by rfl⟩ : syracuseStep 2250557 = 843959) B843959
theorem B1267625 : Blo 666309 1267625 := bstep (se 2 (by rfl) ⟨475359, by rfl⟩ : syracuseStep 1267625 = 950719) B950719
theorem B11589641 : Blo 666309 11589641 := bstep (se 2 (by rfl) ⟨4346115, by rfl⟩ : syracuseStep 11589641 = 8692231) B8692231
theorem B2283839 : Blo 666309 2283839 := bstep (se 1 (by rfl) ⟨1712879, by rfl⟩ : syracuseStep 2283839 = 3425759) B3425759
theorem B4873081 : Blo 666309 4873081 := bstep (se 2 (by rfl) ⟨1827405, by rfl⟩ : syracuseStep 4873081 = 3654811) B3654811
theorem B1694591 : Blo 666309 1694591 := bstep (se 1 (by rfl) ⟨1270943, by rfl⟩ : syracuseStep 1694591 = 2541887) B2541887
theorem B1696079 : Blo 666309 1696079 := bstep (se 1 (by rfl) ⟨1272059, by rfl⟩ : syracuseStep 1696079 = 2544119) B2544119
theorem B3203563 : Blo 666309 3203563 := bstep (se 1 (by rfl) ⟨2402672, by rfl⟩ : syracuseStep 3203563 = 4805345) B4805345
theorem B8905403 : Blo 666309 8905403 := bstep (se 1 (by rfl) ⟨6679052, by rfl⟩ : syracuseStep 8905403 = 13358105) B13358105
theorem B7594721 : Blo 666309 7594721 := bstep (se 2 (by rfl) ⟨2848020, by rfl⟩ : syracuseStep 7594721 = 5696041) B5696041
theorem B1501631 : Blo 666309 1501631 := bstep (se 1 (by rfl) ⟨1126223, by rfl⟩ : syracuseStep 1501631 = 2252447) B2252447
theorem B1502459 : Blo 666309 1502459 := bstep (se 1 (by rfl) ⟨1126844, by rfl⟩ : syracuseStep 1502459 = 2253689) B2253689
theorem B1503431 : Blo 666309 1503431 := bstep (se 1 (by rfl) ⟨1127573, by rfl⟩ : syracuseStep 1503431 = 2255147) B2255147
theorem B1503719 : Blo 666309 1503719 := bstep (se 1 (by rfl) ⟨1127789, by rfl⟩ : syracuseStep 1503719 = 2255579) B2255579
theorem B1503935 : Blo 666309 1503935 := bstep (se 1 (by rfl) ⟨1127951, by rfl⟩ : syracuseStep 1503935 = 2255903) B2255903
theorem B1504799 : Blo 666309 1504799 := bstep (se 1 (by rfl) ⟨1128599, by rfl⟩ : syracuseStep 1504799 = 2257199) B2257199
theorem B10811503 : Blo 666309 10811503 := bstep (se 1 (by rfl) ⟨8108627, by rfl⟩ : syracuseStep 10811503 = 16217255) B16217255
theorem B6093119 : Blo 666309 6093119 := bstep (se 1 (by rfl) ⟨4569839, by rfl⟩ : syracuseStep 6093119 = 9139679) B9139679
theorem B751999 : Blo 666309 751999 := bstep (se 1 (by rfl) ⟨563999, by rfl⟩ : syracuseStep 751999 = 1127999) B1127999
theorem B5503585 : Blo 666309 5503585 := bstep (se 2 (by rfl) ⟨2063844, by rfl⟩ : syracuseStep 5503585 = 4127689) B4127689
theorem B61669475 : Blo 666309 61669475 := bstep (se 1 (by rfl) ⟨46252106, by rfl⟩ : syracuseStep 61669475 = 92504213) B92504213
theorem B1507895 : Blo 666309 1507895 := bstep (se 1 (by rfl) ⟨1130921, by rfl⟩ : syracuseStep 1507895 = 2261843) B2261843
theorem B3803375 : Blo 666309 3803375 := bstep (se 1 (by rfl) ⟨2852531, by rfl⟩ : syracuseStep 3803375 = 5705063) B5705063
theorem B1904467 : Blo 666309 1904467 := bstep (se 1 (by rfl) ⟨1428350, by rfl⟩ : syracuseStep 1904467 = 2856701) B2856701
theorem B856399 : Blo 666309 856399 := bstep (se 1 (by rfl) ⟨642299, by rfl⟩ : syracuseStep 856399 = 1284599) B1284599
theorem B3806747 : Blo 666309 3806747 := bstep (se 1 (by rfl) ⟨2855060, by rfl⟩ : syracuseStep 3806747 = 5710121) B5710121
theorem B5936935 : Blo 666309 5936935 := bstep (se 1 (by rfl) ⟨4452701, by rfl⟩ : syracuseStep 5936935 = 8905403) B8905403
theorem B22288691 : Blo 666309 22288691 := bstep (se 1 (by rfl) ⟨16716518, by rfl⟩ : syracuseStep 22288691 = 33433037) B33433037
theorem B6497441 : Blo 666309 6497441 := bstep (se 2 (by rfl) ⟨2436540, by rfl⟩ : syracuseStep 6497441 = 4873081) B4873081
theorem B4271417 : Blo 666309 4271417 := bstep (se 2 (by rfl) ⟨1601781, by rfl⟩ : syracuseStep 4271417 = 3203563) B3203563
theorem B7811963 : Blo 666309 7811963 := bstep (se 1 (by rfl) ⟨5858972, by rfl⟩ : syracuseStep 7811963 = 11717945) B11717945
theorem B668903 : Blo 666309 668903 := bstep (se 1 (by rfl) ⟨501677, by rfl⟩ : syracuseStep 668903 = 1003355) B1003355
theorem B1522559 : Blo 666309 1522559 := bstep (se 1 (by rfl) ⟨1141919, by rfl⟩ : syracuseStep 1522559 = 2283839) B2283839
theorem B1129727 : Blo 666309 1129727 := bstep (se 1 (by rfl) ⟨847295, by rfl⟩ : syracuseStep 1129727 = 1694591) B1694591
theorem B1687655 : Blo 666309 1687655 := bstep (se 1 (by rfl) ⟨1265741, by rfl⟩ : syracuseStep 1687655 = 2531483) B2531483
theorem B1130719 : Blo 666309 1130719 := bstep (se 1 (by rfl) ⟨848039, by rfl⟩ : syracuseStep 1130719 = 1696079) B1696079
theorem B5063147 : Blo 666309 5063147 := bstep (se 1 (by rfl) ⟨3797360, by rfl⟩ : syracuseStep 5063147 = 7594721) B7594721
theorem B3392927 : Blo 666309 3392927 := bstep (se 1 (by rfl) ⟨2544695, by rfl⟩ : syracuseStep 3392927 = 5089391) B5089391
theorem B1001087 : Blo 666309 1001087 := bstep (se 1 (by rfl) ⟨750815, by rfl⟩ : syracuseStep 1001087 = 1501631) B1501631
theorem B1001639 : Blo 666309 1001639 := bstep (se 1 (by rfl) ⟨751229, by rfl⟩ : syracuseStep 1001639 = 1502459) B1502459
theorem B1002287 : Blo 666309 1002287 := bstep (se 1 (by rfl) ⟨751715, by rfl⟩ : syracuseStep 1002287 = 1503431) B1503431
theorem B1002479 : Blo 666309 1002479 := bstep (se 1 (by rfl) ⟨751859, by rfl⟩ : syracuseStep 1002479 = 1503719) B1503719
theorem B1002623 : Blo 666309 1002623 := bstep (se 1 (by rfl) ⟨751967, by rfl⟩ : syracuseStep 1002623 = 1503935) B1503935
theorem B1002665 : Blo 666309 1002665 := bstep (se 2 (by rfl) ⟨375999, by rfl⟩ : syracuseStep 1002665 = 751999) B751999
theorem B1003199 : Blo 666309 1003199 := bstep (se 1 (by rfl) ⟨752399, by rfl⟩ : syracuseStep 1003199 = 1504799) B1504799
theorem B1005023 : Blo 666309 1005023 := bstep (se 1 (by rfl) ⟨753767, by rfl⟩ : syracuseStep 1005023 = 1507535) B1507535
theorem B2251529 : Blo 666309 2251529 := bstep (se 2 (by rfl) ⟨844323, by rfl⟩ : syracuseStep 2251529 = 1688647) B1688647
theorem B1073179 : Blo 666309 1073179 := bstep (se 1 (by rfl) ⟨804884, by rfl⟩ : syracuseStep 1073179 = 1609769) B1609769
theorem B1499291 : Blo 666309 1499291 := bstep (se 1 (by rfl) ⟨1124468, by rfl⟩ : syracuseStep 1499291 = 2248937) B2248937
theorem B8544473 : Blo 666309 8544473 := bstep (se 2 (by rfl) ⟨3204177, by rfl⟩ : syracuseStep 8544473 = 6408355) B6408355
theorem B31351303 : Blo 666309 31351303 := bstep (se 1 (by rfl) ⟨23513477, by rfl⟩ : syracuseStep 31351303 = 47026955) B47026955
theorem B1500371 : Blo 666309 1500371 := bstep (se 1 (by rfl) ⟨1125278, by rfl⟩ : syracuseStep 1500371 = 2250557) B2250557
theorem B845083 : Blo 666309 845083 := bstep (se 1 (by rfl) ⟨633812, by rfl⟩ : syracuseStep 845083 = 1267625) B1267625
theorem B7726427 : Blo 666309 7726427 := bstep (se 1 (by rfl) ⟨5794820, by rfl⟩ : syracuseStep 7726427 = 11589641) B11589641
theorem B1600975 : Blo 666309 1600975 := bstep (se 1 (by rfl) ⟨1200731, by rfl⟩ : syracuseStep 1600975 = 2401463) B2401463
theorem B2289149 : Blo 666309 2289149 := bstep (se 3 (by rfl) ⟨429215, by rfl⟩ : syracuseStep 2289149 = 858431) B858431
theorem B14415337 : Blo 666309 14415337 := bstep (se 2 (by rfl) ⟨5405751, by rfl⟩ : syracuseStep 14415337 = 10811503) B10811503
theorem B7338113 : Blo 666309 7338113 := bstep (se 2 (by rfl) ⟨2751792, by rfl⟩ : syracuseStep 7338113 = 5503585) B5503585
theorem B4062079 : Blo 666309 4062079 := bstep (se 1 (by rfl) ⟨3046559, by rfl⟩ : syracuseStep 4062079 = 6093119) B6093119
theorem B1507625 : Blo 666309 1507625 := bstep (se 2 (by rfl) ⟨565359, by rfl⟩ : syracuseStep 1507625 = 1130719) B1130719
theorem B3375431 : Blo 666309 3375431 := bstep (se 1 (by rfl) ⟨2531573, by rfl⟩ : syracuseStep 3375431 = 5063147) B5063147
theorem B2261951 : Blo 666309 2261951 := bstep (se 1 (by rfl) ⟨1696463, by rfl⟩ : syracuseStep 2261951 = 3392927) B3392927
theorem B2134633 : Blo 666309 2134633 := bstep (se 2 (by rfl) ⟨800487, by rfl⟩ : syracuseStep 2134633 = 1600975) B1600975
theorem B21664421 : Blo 666309 21664421 := bstep (se 4 (by rfl) ⟨2031039, by rfl⟩ : syracuseStep 21664421 = 4062079) B4062079
theorem B4331627 : Blo 666309 4331627 := bstep (se 1 (by rfl) ⟨3248720, by rfl⟩ : syracuseStep 4331627 = 6497441) B6497441
theorem B5150951 : Blo 666309 5150951 := bstep (se 1 (by rfl) ⟨3863213, by rfl⟩ : syracuseStep 5150951 = 7726427) B7726427
theorem B4892075 : Blo 666309 4892075 := bstep (se 1 (by rfl) ⟨3669056, by rfl⟩ : syracuseStep 4892075 = 7338113) B7338113
theorem B1125103 : Blo 666309 1125103 := bstep (se 1 (by rfl) ⟨843827, by rfl⟩ : syracuseStep 1125103 = 1687655) B1687655
theorem B667391 : Blo 666309 667391 := bstep (se 1 (by rfl) ⟨500543, by rfl⟩ : syracuseStep 667391 = 1001087) B1001087
theorem B667759 : Blo 666309 667759 := bstep (se 1 (by rfl) ⟨500819, by rfl⟩ : syracuseStep 667759 = 1001639) B1001639
theorem B2535583 : Blo 666309 2535583 := bstep (se 1 (by rfl) ⟨1901687, by rfl⟩ : syracuseStep 2535583 = 3803375) B3803375
theorem B1126777 : Blo 666309 1126777 := bstep (se 2 (by rfl) ⟨422541, by rfl⟩ : syracuseStep 1126777 = 845083) B845083
theorem B668191 : Blo 666309 668191 := bstep (se 1 (by rfl) ⟨501143, by rfl⟩ : syracuseStep 668191 = 1002287) B1002287
theorem B668319 : Blo 666309 668319 := bstep (se 1 (by rfl) ⟨501239, by rfl⟩ : syracuseStep 668319 = 1002479) B1002479
theorem B668415 : Blo 666309 668415 := bstep (se 1 (by rfl) ⟨501311, by rfl⟩ : syracuseStep 668415 = 1002623) B1002623
theorem B668443 : Blo 666309 668443 := bstep (se 1 (by rfl) ⟨501332, by rfl⟩ : syracuseStep 668443 = 1002665) B1002665
theorem B668799 : Blo 666309 668799 := bstep (se 1 (by rfl) ⟨501599, by rfl⟩ : syracuseStep 668799 = 1003199) B1003199
theorem B670015 : Blo 666309 670015 := bstep (se 1 (by rfl) ⟨502511, by rfl⟩ : syracuseStep 670015 = 1005023) B1005023
theorem B2537831 : Blo 666309 2537831 := bstep (se 1 (by rfl) ⟨1903373, by rfl⟩ : syracuseStep 2537831 = 3806747) B3806747
theorem B2539289 : Blo 666309 2539289 := bstep (se 2 (by rfl) ⟨952233, by rfl⟩ : syracuseStep 2539289 = 1904467) B1904467
theorem B999527 : Blo 666309 999527 := bstep (se 1 (by rfl) ⟨749645, by rfl⟩ : syracuseStep 999527 = 1499291) B1499291
theorem B1000247 : Blo 666309 1000247 := bstep (se 1 (by rfl) ⟨750185, by rfl⟩ : syracuseStep 1000247 = 1500371) B1500371
theorem B19220449 : Blo 666309 19220449 := bstep (se 2 (by rfl) ⟨7207668, by rfl⟩ : syracuseStep 19220449 = 14415337) B14415337
theorem B1526099 : Blo 666309 1526099 := bstep (se 1 (by rfl) ⟨1144574, by rfl⟩ : syracuseStep 1526099 = 2289149) B2289149
theorem B7915913 : Blo 666309 7915913 := bstep (se 2 (by rfl) ⟨2968467, by rfl⟩ : syracuseStep 7915913 = 5936935) B5936935
theorem B41112983 : Blo 666309 41112983 := bstep (se 1 (by rfl) ⟨30834737, by rfl⟩ : syracuseStep 41112983 = 61669475) B61669475
theorem B5723621 : Blo 666309 5723621 := bstep (se 4 (by rfl) ⟨536589, by rfl⟩ : syracuseStep 5723621 = 1073179) B1073179
theorem B1005263 : Blo 666309 1005263 := bstep (se 1 (by rfl) ⟨753947, by rfl⟩ : syracuseStep 1005263 = 1507895) B1507895
theorem B167206949 : Blo 666309 167206949 := bstep (se 4 (by rfl) ⟨15675651, by rfl⟩ : syracuseStep 167206949 = 31351303) B31351303
theorem B1501019 : Blo 666309 1501019 := bstep (se 1 (by rfl) ⟨1125764, by rfl⟩ : syracuseStep 1501019 = 2251529) B2251529
theorem B5696315 : Blo 666309 5696315 := bstep (se 1 (by rfl) ⟨4272236, by rfl⟩ : syracuseStep 5696315 = 8544473) B8544473
theorem B1141865 : Blo 666309 1141865 := bstep (se 2 (by rfl) ⟨428199, by rfl⟩ : syracuseStep 1141865 = 856399) B856399
theorem B59436509 : Blo 666309 59436509 := bstep (se 3 (by rfl) ⟨11144345, by rfl⟩ : syracuseStep 59436509 = 22288691) B22288691
theorem B2847611 : Blo 666309 2847611 := bstep (se 1 (by rfl) ⟨2135708, by rfl⟩ : syracuseStep 2847611 = 4271417) B4271417
theorem B5207975 : Blo 666309 5207975 := bstep (se 1 (by rfl) ⟨3905981, by rfl⟩ : syracuseStep 5207975 = 7811963) B7811963
theorem B1015039 : Blo 666309 1015039 := bstep (se 1 (by rfl) ⟨761279, by rfl⟩ : syracuseStep 1015039 = 1522559) B1522559
theorem B753151 : Blo 666309 753151 := bstep (se 1 (by rfl) ⟨564863, by rfl⟩ : syracuseStep 753151 = 1129727) B1129727
theorem B1507967 : Blo 666309 1507967 := bstep (se 1 (by rfl) ⟨1130975, by rfl⟩ : syracuseStep 1507967 = 2261951) B2261951
theorem B5277275 : Blo 666309 5277275 := bstep (se 1 (by rfl) ⟨3957956, by rfl⟩ : syracuseStep 5277275 = 7915913) B7915913
theorem B25627265 : Blo 666309 25627265 := bstep (se 2 (by rfl) ⟨9610224, by rfl⟩ : syracuseStep 25627265 = 19220449) B19220449
theorem B2887751 : Blo 666309 2887751 := bstep (se 1 (by rfl) ⟨2165813, by rfl⟩ : syracuseStep 2887751 = 4331627) B4331627
theorem B3380777 : Blo 666309 3380777 := bstep (se 2 (by rfl) ⟨1267791, by rfl⟩ : syracuseStep 3380777 = 2535583) B2535583
theorem B4069597 : Blo 666309 4069597 := bstep (se 3 (by rfl) ⟨763049, by rfl⟩ : syracuseStep 4069597 = 1526099) B1526099
theorem B761243 : Blo 666309 761243 := bstep (se 1 (by rfl) ⟨570932, by rfl⟩ : syracuseStep 761243 = 1141865) B1141865
theorem B1353385 : Blo 666309 1353385 := bstep (se 2 (by rfl) ⟨507519, by rfl⟩ : syracuseStep 1353385 = 1015039) B1015039
theorem B666351 : Blo 666309 666351 := bstep (se 1 (by rfl) ⟨499763, by rfl⟩ : syracuseStep 666351 = 999527) B999527
theorem B666831 : Blo 666309 666831 := bstep (se 1 (by rfl) ⟨500123, by rfl⟩ : syracuseStep 666831 = 1000247) B1000247
theorem B27408655 : Blo 666309 27408655 := bstep (se 1 (by rfl) ⟨20556491, by rfl⟩ : syracuseStep 27408655 = 41112983) B41112983
theorem B3815747 : Blo 666309 3815747 := bstep (se 1 (by rfl) ⟨2861810, by rfl⟩ : syracuseStep 3815747 = 5723621) B5723621
theorem B670175 : Blo 666309 670175 := bstep (se 1 (by rfl) ⟨502631, by rfl⟩ : syracuseStep 670175 = 1005263) B1005263
theorem B3261383 : Blo 666309 3261383 := bstep (se 1 (by rfl) ⟨2446037, by rfl⟩ : syracuseStep 3261383 = 4892075) B4892075
theorem B1000679 : Blo 666309 1000679 := bstep (se 1 (by rfl) ⟨750509, by rfl⟩ : syracuseStep 1000679 = 1501019) B1501019
theorem B1691887 : Blo 666309 1691887 := bstep (se 1 (by rfl) ⟨1268915, by rfl⟩ : syracuseStep 1691887 = 2537831) B2537831
theorem B1004201 : Blo 666309 1004201 := bstep (se 2 (by rfl) ⟨376575, by rfl⟩ : syracuseStep 1004201 = 753151) B753151
theorem B1692859 : Blo 666309 1692859 := bstep (se 1 (by rfl) ⟨1269644, by rfl⟩ : syracuseStep 1692859 = 2539289) B2539289
theorem B1005083 : Blo 666309 1005083 := bstep (se 1 (by rfl) ⟨753812, by rfl⟩ : syracuseStep 1005083 = 1507625) B1507625
theorem B2250287 : Blo 666309 2250287 := bstep (se 1 (by rfl) ⟨1687715, by rfl⟩ : syracuseStep 2250287 = 3375431) B3375431
theorem B14442947 : Blo 666309 14442947 := bstep (se 1 (by rfl) ⟨10832210, by rfl⟩ : syracuseStep 14442947 = 21664421) B21664421
theorem B1500137 : Blo 666309 1500137 := bstep (se 2 (by rfl) ⟨562551, by rfl⟩ : syracuseStep 1500137 = 1125103) B1125103
theorem B3433967 : Blo 666309 3433967 := bstep (se 1 (by rfl) ⟨2575475, by rfl⟩ : syracuseStep 3433967 = 5150951) B5150951
theorem B111471299 : Blo 666309 111471299 := bstep (se 1 (by rfl) ⟨83603474, by rfl⟩ : syracuseStep 111471299 = 167206949) B167206949
theorem B1502369 : Blo 666309 1502369 := bstep (se 2 (by rfl) ⟨563388, by rfl⟩ : syracuseStep 1502369 = 1126777) B1126777
theorem B2846177 : Blo 666309 2846177 := bstep (se 2 (by rfl) ⟨1067316, by rfl⟩ : syracuseStep 2846177 = 2134633) B2134633
theorem B3797543 : Blo 666309 3797543 := bstep (se 1 (by rfl) ⟨2848157, by rfl⟩ : syracuseStep 3797543 = 5696315) B5696315
theorem B1898407 : Blo 666309 1898407 := bstep (se 1 (by rfl) ⟨1423805, by rfl⟩ : syracuseStep 1898407 = 2847611) B2847611
theorem B158497357 : Blo 666309 158497357 := bstep (se 3 (by rfl) ⟨29718254, by rfl⟩ : syracuseStep 158497357 = 59436509) B59436509
theorem B3471983 : Blo 666309 3471983 := bstep (se 1 (by rfl) ⟨2603987, by rfl⟩ : syracuseStep 3471983 = 5207975) B5207975
theorem B7700669 : Blo 666309 7700669 := bstep (se 3 (by rfl) ⟨1443875, by rfl⟩ : syracuseStep 7700669 = 2887751) B2887751
theorem B1804513 : Blo 666309 1804513 := bstep (se 2 (by rfl) ⟨676692, by rfl⟩ : syracuseStep 1804513 = 1353385) B1353385
theorem B2531209 : Blo 666309 2531209 := bstep (se 2 (by rfl) ⟨949203, by rfl⟩ : syracuseStep 2531209 = 1898407) B1898407
theorem B36544873 : Blo 666309 36544873 := bstep (se 2 (by rfl) ⟨13704327, by rfl⟩ : syracuseStep 36544873 = 27408655) B27408655
theorem B2531695 : Blo 666309 2531695 := bstep (se 1 (by rfl) ⟨1898771, by rfl⟩ : syracuseStep 2531695 = 3797543) B3797543
theorem B211329809 : Blo 666309 211329809 := bstep (se 2 (by rfl) ⟨79248678, by rfl⟩ : syracuseStep 211329809 = 158497357) B158497357
theorem B2174255 : Blo 666309 2174255 := bstep (se 1 (by rfl) ⟨1630691, by rfl⟩ : syracuseStep 2174255 = 3261383) B3261383
theorem B667119 : Blo 666309 667119 := bstep (se 1 (by rfl) ⟨500339, by rfl⟩ : syracuseStep 667119 = 1000679) B1000679
theorem B3518183 : Blo 666309 3518183 := bstep (se 1 (by rfl) ⟨2638637, by rfl⟩ : syracuseStep 3518183 = 5277275) B5277275
theorem B17084843 : Blo 666309 17084843 := bstep (se 1 (by rfl) ⟨12813632, by rfl⟩ : syracuseStep 17084843 = 25627265) B25627265
theorem B669467 : Blo 666309 669467 := bstep (se 1 (by rfl) ⟨502100, by rfl⟩ : syracuseStep 669467 = 1004201) B1004201
theorem B670055 : Blo 666309 670055 := bstep (se 1 (by rfl) ⟨502541, by rfl⟩ : syracuseStep 670055 = 1005083) B1005083
theorem B1000091 : Blo 666309 1000091 := bstep (se 1 (by rfl) ⟨750068, by rfl⟩ : syracuseStep 1000091 = 1500137) B1500137
theorem B1001579 : Blo 666309 1001579 := bstep (se 1 (by rfl) ⟨751184, by rfl⟩ : syracuseStep 1001579 = 1502369) B1502369
theorem B5426129 : Blo 666309 5426129 := bstep (se 2 (by rfl) ⟨2034798, by rfl⟩ : syracuseStep 5426129 = 4069597) B4069597
theorem B2543831 : Blo 666309 2543831 := bstep (se 1 (by rfl) ⟨1907873, by rfl⟩ : syracuseStep 2543831 = 3815747) B3815747
theorem B2314655 : Blo 666309 2314655 := bstep (se 1 (by rfl) ⟨1735991, by rfl⟩ : syracuseStep 2314655 = 3471983) B3471983
theorem B1005311 : Blo 666309 1005311 := bstep (se 1 (by rfl) ⟨753983, by rfl⟩ : syracuseStep 1005311 = 1507967) B1507967
theorem B2253851 : Blo 666309 2253851 := bstep (se 1 (by rfl) ⟨1690388, by rfl⟩ : syracuseStep 2253851 = 3380777) B3380777
theorem B1500191 : Blo 666309 1500191 := bstep (se 1 (by rfl) ⟨1125143, by rfl⟩ : syracuseStep 1500191 = 2250287) B2250287
theorem B9628631 : Blo 666309 9628631 := bstep (se 1 (by rfl) ⟨7221473, by rfl⟩ : syracuseStep 9628631 = 14442947) B14442947
theorem B2255849 : Blo 666309 2255849 := bstep (se 2 (by rfl) ⟨845943, by rfl⟩ : syracuseStep 2255849 = 1691887) B1691887
theorem B2289311 : Blo 666309 2289311 := bstep (se 1 (by rfl) ⟨1716983, by rfl⟩ : syracuseStep 2289311 = 3433967) B3433967
theorem B2257145 : Blo 666309 2257145 := bstep (se 2 (by rfl) ⟨846429, by rfl⟩ : syracuseStep 2257145 = 1692859) B1692859
theorem B74314199 : Blo 666309 74314199 := bstep (se 1 (by rfl) ⟨55735649, by rfl⟩ : syracuseStep 74314199 = 111471299) B111471299
theorem B1897451 : Blo 666309 1897451 := bstep (se 1 (by rfl) ⟨1423088, by rfl⟩ : syracuseStep 1897451 = 2846177) B2846177
theorem B2029981 : Blo 666309 2029981 := bstep (se 3 (by rfl) ⟨380621, by rfl⟩ : syracuseStep 2029981 = 761243) B761243
theorem B48726497 : Blo 666309 48726497 := bstep (se 2 (by rfl) ⟨18272436, by rfl⟩ : syracuseStep 48726497 = 36544873) B36544873
theorem B3375593 : Blo 666309 3375593 := bstep (se 2 (by rfl) ⟨1265847, by rfl⟩ : syracuseStep 3375593 = 2531695) B2531695
theorem B1543103 : Blo 666309 1543103 := bstep (se 1 (by rfl) ⟨1157327, by rfl⟩ : syracuseStep 1543103 = 2314655) B2314655
theorem B1449503 : Blo 666309 1449503 := bstep (se 1 (by rfl) ⟨1087127, by rfl⟩ : syracuseStep 1449503 = 2174255) B2174255
theorem B666727 : Blo 666309 666727 := bstep (se 1 (by rfl) ⟨500045, by rfl⟩ : syracuseStep 666727 = 1000091) B1000091
theorem B667719 : Blo 666309 667719 := bstep (se 1 (by rfl) ⟨500789, by rfl⟩ : syracuseStep 667719 = 1001579) B1001579
theorem B3617419 : Blo 666309 3617419 := bstep (se 1 (by rfl) ⟨2713064, by rfl⟩ : syracuseStep 3617419 = 5426129) B5426129
theorem B2406017 : Blo 666309 2406017 := bstep (se 2 (by rfl) ⟨902256, by rfl⟩ : syracuseStep 2406017 = 1804513) B1804513
theorem B670207 : Blo 666309 670207 := bstep (se 1 (by rfl) ⟨502655, by rfl⟩ : syracuseStep 670207 = 1005311) B1005311
theorem B140886539 : Blo 666309 140886539 := bstep (se 1 (by rfl) ⟨105664904, by rfl⟩ : syracuseStep 140886539 = 211329809) B211329809
theorem B1000127 : Blo 666309 1000127 := bstep (se 1 (by rfl) ⟨750095, by rfl⟩ : syracuseStep 1000127 = 1500191) B1500191
theorem B1526207 : Blo 666309 1526207 := bstep (se 1 (by rfl) ⟨1144655, by rfl⟩ : syracuseStep 1526207 = 2289311) B2289311
theorem B2345455 : Blo 666309 2345455 := bstep (se 1 (by rfl) ⟨1759091, by rfl⟩ : syracuseStep 2345455 = 3518183) B3518183
theorem B11389895 : Blo 666309 11389895 := bstep (se 1 (by rfl) ⟨8542421, by rfl⟩ : syracuseStep 11389895 = 17084843) B17084843
theorem B2706641 : Blo 666309 2706641 := bstep (se 2 (by rfl) ⟨1014990, by rfl⟩ : syracuseStep 2706641 = 2029981) B2029981
theorem B1264967 : Blo 666309 1264967 := bstep (se 1 (by rfl) ⟨948725, by rfl⟩ : syracuseStep 1264967 = 1897451) B1897451
theorem B5133779 : Blo 666309 5133779 := bstep (se 1 (by rfl) ⟨3850334, by rfl⟩ : syracuseStep 5133779 = 7700669) B7700669
theorem B1695887 : Blo 666309 1695887 := bstep (se 1 (by rfl) ⟨1271915, by rfl⟩ : syracuseStep 1695887 = 2543831) B2543831
theorem B1502567 : Blo 666309 1502567 := bstep (se 1 (by rfl) ⟨1126925, by rfl⟩ : syracuseStep 1502567 = 2253851) B2253851
theorem B6419087 : Blo 666309 6419087 := bstep (se 1 (by rfl) ⟨4814315, by rfl⟩ : syracuseStep 6419087 = 9628631) B9628631
theorem B1503899 : Blo 666309 1503899 := bstep (se 1 (by rfl) ⟨1127924, by rfl⟩ : syracuseStep 1503899 = 2255849) B2255849
theorem B1504763 : Blo 666309 1504763 := bstep (se 1 (by rfl) ⟨1128572, by rfl⟩ : syracuseStep 1504763 = 2257145) B2257145
theorem B49542799 : Blo 666309 49542799 := bstep (se 1 (by rfl) ⟨37157099, by rfl⟩ : syracuseStep 49542799 = 74314199) B74314199
theorem B3374945 : Blo 666309 3374945 := bstep (se 2 (by rfl) ⟨1265604, by rfl⟩ : syracuseStep 3374945 = 2531209) B2531209
theorem B1804427 : Blo 666309 1804427 := bstep (se 1 (by rfl) ⟨1353320, by rfl⟩ : syracuseStep 1804427 = 2706641) B2706641
theorem B4823225 : Blo 666309 4823225 := bstep (se 2 (by rfl) ⟨1808709, by rfl⟩ : syracuseStep 4823225 = 3617419) B3617419
theorem B4069885 : Blo 666309 4069885 := bstep (se 3 (by rfl) ⟨763103, by rfl⟩ : syracuseStep 4069885 = 1526207) B1526207
theorem B32484331 : Blo 666309 32484331 := bstep (se 1 (by rfl) ⟨24363248, by rfl⟩ : syracuseStep 32484331 = 48726497) B48726497
theorem B93924359 : Blo 666309 93924359 := bstep (se 1 (by rfl) ⟨70443269, by rfl⟩ : syracuseStep 93924359 = 140886539) B140886539
theorem B666751 : Blo 666309 666751 := bstep (se 1 (by rfl) ⟨500063, by rfl⟩ : syracuseStep 666751 = 1000127) B1000127
theorem B1028735 : Blo 666309 1028735 := bstep (se 1 (by rfl) ⟨771551, by rfl⟩ : syracuseStep 1028735 = 1543103) B1543103
theorem B3422519 : Blo 666309 3422519 := bstep (se 1 (by rfl) ⟨2566889, by rfl⟩ : syracuseStep 3422519 = 5133779) B5133779
theorem B966335 : Blo 666309 966335 := bstep (se 1 (by rfl) ⟨724751, by rfl⟩ : syracuseStep 966335 = 1449503) B1449503
theorem B1130591 : Blo 666309 1130591 := bstep (se 1 (by rfl) ⟨847943, by rfl⟩ : syracuseStep 1130591 = 1695887) B1695887
theorem B1001711 : Blo 666309 1001711 := bstep (se 1 (by rfl) ⟨751283, by rfl⟩ : syracuseStep 1001711 = 1502567) B1502567
theorem B4279391 : Blo 666309 4279391 := bstep (se 1 (by rfl) ⟨3209543, by rfl⟩ : syracuseStep 4279391 = 6419087) B6419087
theorem B1002599 : Blo 666309 1002599 := bstep (se 1 (by rfl) ⟨751949, by rfl⟩ : syracuseStep 1002599 = 1503899) B1503899
theorem B1003175 : Blo 666309 1003175 := bstep (se 1 (by rfl) ⟨752381, by rfl⟩ : syracuseStep 1003175 = 1504763) B1504763
theorem B2249963 : Blo 666309 2249963 := bstep (se 1 (by rfl) ⟨1687472, by rfl⟩ : syracuseStep 2249963 = 3374945) B3374945
theorem B2250395 : Blo 666309 2250395 := bstep (se 1 (by rfl) ⟨1687796, by rfl⟩ : syracuseStep 2250395 = 3375593) B3375593
theorem B7593263 : Blo 666309 7593263 := bstep (se 1 (by rfl) ⟨5694947, by rfl⟩ : syracuseStep 7593263 = 11389895) B11389895
theorem B843311 : Blo 666309 843311 := bstep (se 1 (by rfl) ⟨632483, by rfl⟩ : syracuseStep 843311 = 1264967) B1264967
theorem B12509093 : Blo 666309 12509093 := bstep (se 4 (by rfl) ⟨1172727, by rfl⟩ : syracuseStep 12509093 = 2345455) B2345455
theorem B66057065 : Blo 666309 66057065 := bstep (se 2 (by rfl) ⟨24771399, by rfl⟩ : syracuseStep 66057065 = 49542799) B49542799
theorem B1604011 : Blo 666309 1604011 := bstep (se 1 (by rfl) ⟨1203008, by rfl⟩ : syracuseStep 1604011 = 2406017) B2406017
theorem B753727 : Blo 666309 753727 := bstep (se 1 (by rfl) ⟨565295, by rfl⟩ : syracuseStep 753727 = 1130591) B1130591
theorem B2852927 : Blo 666309 2852927 := bstep (se 1 (by rfl) ⟨2139695, by rfl⟩ : syracuseStep 2852927 = 4279391) B4279391
theorem B3215483 : Blo 666309 3215483 := bstep (se 1 (by rfl) ⟨2411612, by rfl⟩ : syracuseStep 3215483 = 4823225) B4823225
theorem B2138681 : Blo 666309 2138681 := bstep (se 2 (by rfl) ⟨802005, by rfl⟩ : syracuseStep 2138681 = 1604011) B1604011
theorem B667807 : Blo 666309 667807 := bstep (se 1 (by rfl) ⟨500855, by rfl⟩ : syracuseStep 667807 = 1001711) B1001711
theorem B668399 : Blo 666309 668399 := bstep (se 1 (by rfl) ⟨501299, by rfl⟩ : syracuseStep 668399 = 1002599) B1002599
theorem B668783 : Blo 666309 668783 := bstep (se 1 (by rfl) ⟨501587, by rfl⟩ : syracuseStep 668783 = 1003175) B1003175
theorem B5062175 : Blo 666309 5062175 := bstep (se 1 (by rfl) ⟨3796631, by rfl⟩ : syracuseStep 5062175 = 7593263) B7593263
theorem B10307573 : Blo 666309 10307573 := bstep (se 5 (by rfl) ⟨483167, by rfl⟩ : syracuseStep 10307573 = 966335) B966335
theorem B5426513 : Blo 666309 5426513 := bstep (se 2 (by rfl) ⟨2034942, by rfl⟩ : syracuseStep 5426513 = 4069885) B4069885
theorem B2248829 : Blo 666309 2248829 := bstep (se 3 (by rfl) ⟨421655, by rfl⟩ : syracuseStep 2248829 = 843311) B843311
theorem B2281679 : Blo 666309 2281679 := bstep (se 1 (by rfl) ⟨1711259, by rfl⟩ : syracuseStep 2281679 = 3422519) B3422519
theorem B1202951 : Blo 666309 1202951 := bstep (se 1 (by rfl) ⟨902213, by rfl⟩ : syracuseStep 1202951 = 1804427) B1804427
theorem B1499975 : Blo 666309 1499975 := bstep (se 1 (by rfl) ⟨1124981, by rfl⟩ : syracuseStep 1499975 = 2249963) B2249963
theorem B1500263 : Blo 666309 1500263 := bstep (se 1 (by rfl) ⟨1125197, by rfl⟩ : syracuseStep 1500263 = 2250395) B2250395
theorem B43312441 : Blo 666309 43312441 := bstep (se 2 (by rfl) ⟨16242165, by rfl⟩ : syracuseStep 43312441 = 32484331) B32484331
theorem B62616239 : Blo 666309 62616239 := bstep (se 1 (by rfl) ⟨46962179, by rfl⟩ : syracuseStep 62616239 = 93924359) B93924359
theorem B685823 : Blo 666309 685823 := bstep (se 1 (by rfl) ⟨514367, by rfl⟩ : syracuseStep 685823 = 1028735) B1028735
theorem B44038043 : Blo 666309 44038043 := bstep (se 1 (by rfl) ⟨33028532, by rfl⟩ : syracuseStep 44038043 = 66057065) B66057065
theorem B33357581 : Blo 666309 33357581 := bstep (se 3 (by rfl) ⟨6254546, by rfl⟩ : syracuseStep 33357581 = 12509093) B12509093
theorem B1901951 : Blo 666309 1901951 := bstep (se 1 (by rfl) ⟨1426463, by rfl⟩ : syracuseStep 1901951 = 2852927) B2852927
theorem B5703149 : Blo 666309 5703149 := bstep (se 3 (by rfl) ⟨1069340, by rfl⟩ : syracuseStep 5703149 = 2138681) B2138681
theorem B7315445 : Blo 666309 7315445 := bstep (se 5 (by rfl) ⟨342911, by rfl⟩ : syracuseStep 7315445 = 685823) B685823
theorem B57749921 : Blo 666309 57749921 := bstep (se 2 (by rfl) ⟨21656220, by rfl⟩ : syracuseStep 57749921 = 43312441) B43312441
theorem B3617675 : Blo 666309 3617675 := bstep (se 1 (by rfl) ⟨2713256, by rfl⟩ : syracuseStep 3617675 = 5426513) B5426513
theorem B2143655 : Blo 666309 2143655 := bstep (se 1 (by rfl) ⟨1607741, by rfl⟩ : syracuseStep 2143655 = 3215483) B3215483
theorem B1521119 : Blo 666309 1521119 := bstep (se 1 (by rfl) ⟨1140839, by rfl⟩ : syracuseStep 1521119 = 2281679) B2281679
theorem B999983 : Blo 666309 999983 := bstep (se 1 (by rfl) ⟨749987, by rfl⟩ : syracuseStep 999983 = 1499975) B1499975
theorem B1000175 : Blo 666309 1000175 := bstep (se 1 (by rfl) ⟨750131, by rfl⟩ : syracuseStep 1000175 = 1500263) B1500263
theorem B22238387 : Blo 666309 22238387 := bstep (se 1 (by rfl) ⟨16678790, by rfl⟩ : syracuseStep 22238387 = 33357581) B33357581
theorem B1004969 : Blo 666309 1004969 := bstep (se 2 (by rfl) ⟨376863, by rfl⟩ : syracuseStep 1004969 = 753727) B753727
theorem B6871715 : Blo 666309 6871715 := bstep (se 1 (by rfl) ⟨5153786, by rfl⟩ : syracuseStep 6871715 = 10307573) B10307573
theorem B1499219 : Blo 666309 1499219 := bstep (se 1 (by rfl) ⟨1124414, by rfl⟩ : syracuseStep 1499219 = 2248829) B2248829
theorem B3207869 : Blo 666309 3207869 := bstep (se 3 (by rfl) ⟨601475, by rfl⟩ : syracuseStep 3207869 = 1202951) B1202951
theorem B41744159 : Blo 666309 41744159 := bstep (se 1 (by rfl) ⟨31308119, by rfl⟩ : syracuseStep 41744159 = 62616239) B62616239
theorem B29358695 : Blo 666309 29358695 := bstep (se 1 (by rfl) ⟨22019021, by rfl⟩ : syracuseStep 29358695 = 44038043) B44038043
theorem B3374783 : Blo 666309 3374783 := bstep (se 1 (by rfl) ⟨2531087, by rfl⟩ : syracuseStep 3374783 = 5062175) B5062175
theorem B3802099 : Blo 666309 3802099 := bstep (se 1 (by rfl) ⟨2851574, by rfl⟩ : syracuseStep 3802099 = 5703149) B5703149
theorem B2138579 : Blo 666309 2138579 := bstep (se 1 (by rfl) ⟨1603934, by rfl⟩ : syracuseStep 2138579 = 3207869) B3207869
theorem B27829439 : Blo 666309 27829439 := bstep (se 1 (by rfl) ⟨20872079, by rfl⟩ : syracuseStep 27829439 = 41744159) B41744159
theorem B19572463 : Blo 666309 19572463 := bstep (se 1 (by rfl) ⟨14679347, by rfl⟩ : syracuseStep 19572463 = 29358695) B29358695
theorem B19507853 : Blo 666309 19507853 := bstep (se 3 (by rfl) ⟨3657722, by rfl⟩ : syracuseStep 19507853 = 7315445) B7315445
theorem B666655 : Blo 666309 666655 := bstep (se 1 (by rfl) ⟨499991, by rfl⟩ : syracuseStep 666655 = 999983) B999983
theorem B666783 : Blo 666309 666783 := bstep (se 1 (by rfl) ⟨500087, by rfl⟩ : syracuseStep 666783 = 1000175) B1000175
theorem B14825591 : Blo 666309 14825591 := bstep (se 1 (by rfl) ⟨11119193, by rfl⟩ : syracuseStep 14825591 = 22238387) B22238387
theorem B669979 : Blo 666309 669979 := bstep (se 1 (by rfl) ⟨502484, by rfl⟩ : syracuseStep 669979 = 1004969) B1004969
theorem B999479 : Blo 666309 999479 := bstep (se 1 (by rfl) ⟨749609, by rfl⟩ : syracuseStep 999479 = 1499219) B1499219
theorem B2411783 : Blo 666309 2411783 := bstep (se 1 (by rfl) ⟨1808837, by rfl⟩ : syracuseStep 2411783 = 3617675) B3617675
theorem B1429103 : Blo 666309 1429103 := bstep (se 1 (by rfl) ⟨1071827, by rfl⟩ : syracuseStep 1429103 = 2143655) B2143655
theorem B2249855 : Blo 666309 2249855 := bstep (se 1 (by rfl) ⟨1687391, by rfl⟩ : syracuseStep 2249855 = 3374783) B3374783
theorem B1267967 : Blo 666309 1267967 := bstep (se 1 (by rfl) ⟨950975, by rfl⟩ : syracuseStep 1267967 = 1901951) B1901951
theorem B4056317 : Blo 666309 4056317 := bstep (se 3 (by rfl) ⟨760559, by rfl⟩ : syracuseStep 4056317 = 1521119) B1521119
theorem B4581143 : Blo 666309 4581143 := bstep (se 1 (by rfl) ⟨3435857, by rfl⟩ : syracuseStep 4581143 = 6871715) B6871715
theorem B38499947 : Blo 666309 38499947 := bstep (se 1 (by rfl) ⟨28874960, by rfl⟩ : syracuseStep 38499947 = 57749921) B57749921
theorem B1607855 : Blo 666309 1607855 := bstep (se 1 (by rfl) ⟨1205891, by rfl⟩ : syracuseStep 1607855 = 2411783) B2411783
theorem B952735 : Blo 666309 952735 := bstep (se 1 (by rfl) ⟨714551, by rfl⟩ : syracuseStep 952735 = 1429103) B1429103
theorem B18552959 : Blo 666309 18552959 := bstep (se 1 (by rfl) ⟨13914719, by rfl⟩ : syracuseStep 18552959 = 27829439) B27829439
theorem B3054095 : Blo 666309 3054095 := bstep (se 1 (by rfl) ⟨2290571, by rfl⟩ : syracuseStep 3054095 = 4581143) B4581143
theorem B25666631 : Blo 666309 25666631 := bstep (se 1 (by rfl) ⟨19249973, by rfl⟩ : syracuseStep 25666631 = 38499947) B38499947
theorem B666319 : Blo 666309 666319 := bstep (se 1 (by rfl) ⟨499739, by rfl⟩ : syracuseStep 666319 = 999479) B999479
theorem B26096617 : Blo 666309 26096617 := bstep (se 2 (by rfl) ⟨9786231, by rfl⟩ : syracuseStep 26096617 = 19572463) B19572463
theorem B1425719 : Blo 666309 1425719 := bstep (se 1 (by rfl) ⟨1069289, by rfl⟩ : syracuseStep 1425719 = 2138579) B2138579
theorem B2704211 : Blo 666309 2704211 := bstep (se 1 (by rfl) ⟨2028158, by rfl⟩ : syracuseStep 2704211 = 4056317) B4056317
theorem B9883727 : Blo 666309 9883727 := bstep (se 1 (by rfl) ⟨7412795, by rfl⟩ : syracuseStep 9883727 = 14825591) B14825591
theorem B5069465 : Blo 666309 5069465 := bstep (se 2 (by rfl) ⟨1901049, by rfl⟩ : syracuseStep 5069465 = 3802099) B3802099
theorem B1499903 : Blo 666309 1499903 := bstep (se 1 (by rfl) ⟨1124927, by rfl⟩ : syracuseStep 1499903 = 2249855) B2249855
theorem B845311 : Blo 666309 845311 := bstep (se 1 (by rfl) ⟨633983, by rfl⟩ : syracuseStep 845311 = 1267967) B1267967
theorem B13005235 : Blo 666309 13005235 := bstep (se 1 (by rfl) ⟨9753926, by rfl⟩ : syracuseStep 13005235 = 19507853) B19507853
theorem B1802807 : Blo 666309 1802807 := bstep (se 1 (by rfl) ⟨1352105, by rfl⟩ : syracuseStep 1802807 = 2704211) B2704211
theorem B3801917 : Blo 666309 3801917 := bstep (se 3 (by rfl) ⟨712859, by rfl⟩ : syracuseStep 3801917 = 1425719) B1425719
theorem B6589151 : Blo 666309 6589151 := bstep (se 1 (by rfl) ⟨4941863, by rfl⟩ : syracuseStep 6589151 = 9883727) B9883727
theorem B2036063 : Blo 666309 2036063 := bstep (se 1 (by rfl) ⟨1527047, by rfl⟩ : syracuseStep 2036063 = 3054095) B3054095
theorem B3379643 : Blo 666309 3379643 := bstep (se 1 (by rfl) ⟨2534732, by rfl⟩ : syracuseStep 3379643 = 5069465) B5069465
theorem B17340313 : Blo 666309 17340313 := bstep (se 2 (by rfl) ⟨6502617, by rfl⟩ : syracuseStep 17340313 = 13005235) B13005235
theorem B17111087 : Blo 666309 17111087 := bstep (se 1 (by rfl) ⟨12833315, by rfl⟩ : syracuseStep 17111087 = 25666631) B25666631
theorem B17150453 : Blo 666309 17150453 := bstep (se 5 (by rfl) ⟨803927, by rfl⟩ : syracuseStep 17150453 = 1607855) B1607855
theorem B1127081 : Blo 666309 1127081 := bstep (se 2 (by rfl) ⟨422655, by rfl⟩ : syracuseStep 1127081 = 845311) B845311
theorem B12368639 : Blo 666309 12368639 := bstep (se 1 (by rfl) ⟨9276479, by rfl⟩ : syracuseStep 12368639 = 18552959) B18552959
theorem B999935 : Blo 666309 999935 := bstep (se 1 (by rfl) ⟨749951, by rfl⟩ : syracuseStep 999935 = 1499903) B1499903
theorem B1270313 : Blo 666309 1270313 := bstep (se 2 (by rfl) ⟨476367, by rfl⟩ : syracuseStep 1270313 = 952735) B952735
theorem B34795489 : Blo 666309 34795489 := bstep (se 2 (by rfl) ⟨13048308, by rfl⟩ : syracuseStep 34795489 = 26096617) B26096617
theorem B4392767 : Blo 666309 4392767 := bstep (se 1 (by rfl) ⟨3294575, by rfl⟩ : syracuseStep 4392767 = 6589151) B6589151
theorem B11407391 : Blo 666309 11407391 := bstep (se 1 (by rfl) ⟨8555543, by rfl⟩ : syracuseStep 11407391 = 17111087) B17111087
theorem B666623 : Blo 666309 666623 := bstep (se 1 (by rfl) ⟨499967, by rfl⟩ : syracuseStep 666623 = 999935) B999935
theorem B2534611 : Blo 666309 2534611 := bstep (se 1 (by rfl) ⟨1900958, by rfl⟩ : syracuseStep 2534611 = 3801917) B3801917
theorem B32983037 : Blo 666309 32983037 := bstep (se 3 (by rfl) ⟨6184319, by rfl⟩ : syracuseStep 32983037 = 12368639) B12368639
theorem B23120417 : Blo 666309 23120417 := bstep (se 2 (by rfl) ⟨8670156, by rfl⟩ : syracuseStep 23120417 = 17340313) B17340313
theorem B1201871 : Blo 666309 1201871 := bstep (se 1 (by rfl) ⟨901403, by rfl⟩ : syracuseStep 1201871 = 1802807) B1802807
theorem B5429501 : Blo 666309 5429501 := bstep (se 3 (by rfl) ⟨1018031, by rfl⟩ : syracuseStep 5429501 = 2036063) B2036063
theorem B2253095 : Blo 666309 2253095 := bstep (se 1 (by rfl) ⟨1689821, by rfl⟩ : syracuseStep 2253095 = 3379643) B3379643
theorem B46393985 : Blo 666309 46393985 := bstep (se 2 (by rfl) ⟨17397744, by rfl⟩ : syracuseStep 46393985 = 34795489) B34795489
theorem B846875 : Blo 666309 846875 := bstep (se 1 (by rfl) ⟨635156, by rfl⟩ : syracuseStep 846875 = 1270313) B1270313
theorem B11433635 : Blo 666309 11433635 := bstep (se 1 (by rfl) ⟨8575226, by rfl⟩ : syracuseStep 11433635 = 17150453) B17150453
theorem B751387 : Blo 666309 751387 := bstep (se 1 (by rfl) ⟨563540, by rfl⟩ : syracuseStep 751387 = 1127081) B1127081
theorem B21988691 : Blo 666309 21988691 := bstep (se 1 (by rfl) ⟨16491518, by rfl⟩ : syracuseStep 21988691 = 32983037) B32983037
theorem B7604927 : Blo 666309 7604927 := bstep (se 1 (by rfl) ⟨5703695, by rfl⟩ : syracuseStep 7604927 = 11407391) B11407391
theorem B3379481 : Blo 666309 3379481 := bstep (se 2 (by rfl) ⟨1267305, by rfl⟩ : syracuseStep 3379481 = 2534611) B2534611
theorem B15413611 : Blo 666309 15413611 := bstep (se 1 (by rfl) ⟨11560208, by rfl⟩ : syracuseStep 15413611 = 23120417) B23120417
theorem B801247 : Blo 666309 801247 := bstep (se 1 (by rfl) ⟨600935, by rfl⟩ : syracuseStep 801247 = 1201871) B1201871
theorem B3619667 : Blo 666309 3619667 := bstep (se 1 (by rfl) ⟨2714750, by rfl⟩ : syracuseStep 3619667 = 5429501) B5429501
theorem B11714045 : Blo 666309 11714045 := bstep (se 3 (by rfl) ⟨2196383, by rfl⟩ : syracuseStep 11714045 = 4392767) B4392767
theorem B123717293 : Blo 666309 123717293 := bstep (se 3 (by rfl) ⟨23196992, by rfl⟩ : syracuseStep 123717293 = 46393985) B46393985
theorem B1001849 : Blo 666309 1001849 := bstep (se 2 (by rfl) ⟨375693, by rfl⟩ : syracuseStep 1001849 = 751387) B751387
theorem B7622423 : Blo 666309 7622423 := bstep (se 1 (by rfl) ⟨5716817, by rfl⟩ : syracuseStep 7622423 = 11433635) B11433635
theorem B1502063 : Blo 666309 1502063 := bstep (se 1 (by rfl) ⟨1126547, by rfl⟩ : syracuseStep 1502063 = 2253095) B2253095
theorem B2258333 : Blo 666309 2258333 := bstep (se 3 (by rfl) ⟨423437, by rfl⟩ : syracuseStep 2258333 = 846875) B846875
theorem B82478195 : Blo 666309 82478195 := bstep (se 1 (by rfl) ⟨61858646, by rfl⟩ : syracuseStep 82478195 = 123717293) B123717293
theorem B5081615 : Blo 666309 5081615 := bstep (se 1 (by rfl) ⟨3811211, by rfl⟩ : syracuseStep 5081615 = 7622423) B7622423
theorem B20551481 : Blo 666309 20551481 := bstep (se 2 (by rfl) ⟨7706805, by rfl⟩ : syracuseStep 20551481 = 15413611) B15413611
theorem B31237453 : Blo 666309 31237453 := bstep (se 3 (by rfl) ⟨5857022, by rfl⟩ : syracuseStep 31237453 = 11714045) B11714045
theorem B14659127 : Blo 666309 14659127 := bstep (se 1 (by rfl) ⟨10994345, by rfl⟩ : syracuseStep 14659127 = 21988691) B21988691
theorem B667899 : Blo 666309 667899 := bstep (se 1 (by rfl) ⟨500924, by rfl⟩ : syracuseStep 667899 = 1001849) B1001849
theorem B1001375 : Blo 666309 1001375 := bstep (se 1 (by rfl) ⟨751031, by rfl⟩ : syracuseStep 1001375 = 1502063) B1502063
theorem B1068329 : Blo 666309 1068329 := bstep (se 2 (by rfl) ⟨400623, by rfl⟩ : syracuseStep 1068329 = 801247) B801247
theorem B2413111 : Blo 666309 2413111 := bstep (se 1 (by rfl) ⟨1809833, by rfl⟩ : syracuseStep 2413111 = 3619667) B3619667
theorem B5069951 : Blo 666309 5069951 := bstep (se 1 (by rfl) ⟨3802463, by rfl⟩ : syracuseStep 5069951 = 7604927) B7604927
theorem B2252987 : Blo 666309 2252987 := bstep (se 1 (by rfl) ⟨1689740, by rfl⟩ : syracuseStep 2252987 = 3379481) B3379481
theorem B1505555 : Blo 666309 1505555 := bstep (se 1 (by rfl) ⟨1129166, by rfl⟩ : syracuseStep 1505555 = 2258333) B2258333
theorem B54985463 : Blo 666309 54985463 := bstep (se 1 (by rfl) ⟨41239097, by rfl⟩ : syracuseStep 54985463 = 82478195) B82478195
theorem B13700987 : Blo 666309 13700987 := bstep (se 1 (by rfl) ⟨10275740, by rfl⟩ : syracuseStep 13700987 = 20551481) B20551481
theorem B3379967 : Blo 666309 3379967 := bstep (se 1 (by rfl) ⟨2534975, by rfl⟩ : syracuseStep 3379967 = 5069951) B5069951
theorem B3217481 : Blo 666309 3217481 := bstep (se 2 (by rfl) ⟨1206555, by rfl⟩ : syracuseStep 3217481 = 2413111) B2413111
theorem B166599749 : Blo 666309 166599749 := bstep (se 4 (by rfl) ⟨15618726, by rfl⟩ : syracuseStep 166599749 = 31237453) B31237453
theorem B9772751 : Blo 666309 9772751 := bstep (se 1 (by rfl) ⟨7329563, by rfl⟩ : syracuseStep 9772751 = 14659127) B14659127
theorem B667583 : Blo 666309 667583 := bstep (se 1 (by rfl) ⟨500687, by rfl⟩ : syracuseStep 667583 = 1001375) B1001375
theorem B3387743 : Blo 666309 3387743 := bstep (se 1 (by rfl) ⟨2540807, by rfl⟩ : syracuseStep 3387743 = 5081615) B5081615
theorem B1003703 : Blo 666309 1003703 := bstep (se 1 (by rfl) ⟨752777, by rfl⟩ : syracuseStep 1003703 = 1505555) B1505555
theorem B1501991 : Blo 666309 1501991 := bstep (se 1 (by rfl) ⟨1126493, by rfl⟩ : syracuseStep 1501991 = 2252987) B2252987
theorem B2848877 : Blo 666309 2848877 := bstep (se 3 (by rfl) ⟨534164, by rfl⟩ : syracuseStep 2848877 = 1068329) B1068329
theorem B26060669 : Blo 666309 26060669 := bstep (se 3 (by rfl) ⟨4886375, by rfl⟩ : syracuseStep 26060669 = 9772751) B9772751
theorem B669135 : Blo 666309 669135 := bstep (se 1 (by rfl) ⟨501851, by rfl⟩ : syracuseStep 669135 = 1003703) B1003703
theorem B2144987 : Blo 666309 2144987 := bstep (se 1 (by rfl) ⟨1608740, by rfl⟩ : syracuseStep 2144987 = 3217481) B3217481
theorem B111066499 : Blo 666309 111066499 := bstep (se 1 (by rfl) ⟨83299874, by rfl⟩ : syracuseStep 111066499 = 166599749) B166599749
theorem B1001327 : Blo 666309 1001327 := bstep (se 1 (by rfl) ⟨750995, by rfl⟩ : syracuseStep 1001327 = 1501991) B1501991
theorem B36656975 : Blo 666309 36656975 := bstep (se 1 (by rfl) ⟨27492731, by rfl⟩ : syracuseStep 36656975 = 54985463) B54985463
theorem B9133991 : Blo 666309 9133991 := bstep (se 1 (by rfl) ⟨6850493, by rfl⟩ : syracuseStep 9133991 = 13700987) B13700987
theorem B2253311 : Blo 666309 2253311 := bstep (se 1 (by rfl) ⟨1689983, by rfl⟩ : syracuseStep 2253311 = 3379967) B3379967
theorem B2258495 : Blo 666309 2258495 := bstep (se 1 (by rfl) ⟨1693871, by rfl⟩ : syracuseStep 2258495 = 3387743) B3387743
theorem B1899251 : Blo 666309 1899251 := bstep (se 1 (by rfl) ⟨1424438, by rfl⟩ : syracuseStep 1899251 = 2848877) B2848877
theorem B17373779 : Blo 666309 17373779 := bstep (se 1 (by rfl) ⟨13030334, by rfl⟩ : syracuseStep 17373779 = 26060669) B26060669
theorem B148088665 : Blo 666309 148088665 := bstep (se 2 (by rfl) ⟨55533249, by rfl⟩ : syracuseStep 148088665 = 111066499) B111066499
theorem B667551 : Blo 666309 667551 := bstep (se 1 (by rfl) ⟨500663, by rfl⟩ : syracuseStep 667551 = 1001327) B1001327
theorem B1429991 : Blo 666309 1429991 := bstep (se 1 (by rfl) ⟨1072493, by rfl⟩ : syracuseStep 1429991 = 2144987) B2144987
theorem B1266167 : Blo 666309 1266167 := bstep (se 1 (by rfl) ⟨949625, by rfl⟩ : syracuseStep 1266167 = 1899251) B1899251
theorem B24437983 : Blo 666309 24437983 := bstep (se 1 (by rfl) ⟨18328487, by rfl⟩ : syracuseStep 24437983 = 36656975) B36656975
theorem B6089327 : Blo 666309 6089327 := bstep (se 1 (by rfl) ⟨4566995, by rfl⟩ : syracuseStep 6089327 = 9133991) B9133991
theorem B1502207 : Blo 666309 1502207 := bstep (se 1 (by rfl) ⟨1126655, by rfl⟩ : syracuseStep 1502207 = 2253311) B2253311
theorem B1505663 : Blo 666309 1505663 := bstep (se 1 (by rfl) ⟨1129247, by rfl⟩ : syracuseStep 1505663 = 2258495) B2258495
theorem B953327 : Blo 666309 953327 := bstep (se 1 (by rfl) ⟨714995, by rfl⟩ : syracuseStep 953327 = 1429991) B1429991
theorem B32583977 : Blo 666309 32583977 := bstep (se 2 (by rfl) ⟨12218991, by rfl⟩ : syracuseStep 32583977 = 24437983) B24437983
theorem B11582519 : Blo 666309 11582519 := bstep (se 1 (by rfl) ⟨8686889, by rfl⟩ : syracuseStep 11582519 = 17373779) B17373779
theorem B1001471 : Blo 666309 1001471 := bstep (se 1 (by rfl) ⟨751103, by rfl⟩ : syracuseStep 1001471 = 1502207) B1502207
theorem B1003775 : Blo 666309 1003775 := bstep (se 1 (by rfl) ⟨752831, by rfl⟩ : syracuseStep 1003775 = 1505663) B1505663
theorem B197451553 : Blo 666309 197451553 := bstep (se 2 (by rfl) ⟨74044332, by rfl⟩ : syracuseStep 197451553 = 148088665) B148088665
theorem B844111 : Blo 666309 844111 := bstep (se 1 (by rfl) ⟨633083, by rfl⟩ : syracuseStep 844111 = 1266167) B1266167
theorem B4059551 : Blo 666309 4059551 := bstep (se 1 (by rfl) ⟨3044663, by rfl⟩ : syracuseStep 4059551 = 6089327) B6089327
theorem B263268737 : Blo 666309 263268737 := bstep (se 2 (by rfl) ⟨98725776, by rfl⟩ : syracuseStep 263268737 = 197451553) B197451553
theorem B1125481 : Blo 666309 1125481 := bstep (se 2 (by rfl) ⟨422055, by rfl⟩ : syracuseStep 1125481 = 844111) B844111
theorem B123546869 : Blo 666309 123546869 := bstep (se 5 (by rfl) ⟨5791259, by rfl⟩ : syracuseStep 123546869 = 11582519) B11582519
theorem B667647 : Blo 666309 667647 := bstep (se 1 (by rfl) ⟨500735, by rfl⟩ : syracuseStep 667647 = 1001471) B1001471
theorem B669183 : Blo 666309 669183 := bstep (se 1 (by rfl) ⟨501887, by rfl⟩ : syracuseStep 669183 = 1003775) B1003775
theorem B2542205 : Blo 666309 2542205 := bstep (se 3 (by rfl) ⟨476663, by rfl⟩ : syracuseStep 2542205 = 953327) B953327
theorem B2706367 : Blo 666309 2706367 := bstep (se 1 (by rfl) ⟨2029775, by rfl⟩ : syracuseStep 2706367 = 4059551) B4059551
theorem B21722651 : Blo 666309 21722651 := bstep (se 1 (by rfl) ⟨16291988, by rfl⟩ : syracuseStep 21722651 = 32583977) B32583977
theorem B3608489 : Blo 666309 3608489 := bstep (se 2 (by rfl) ⟨1353183, by rfl⟩ : syracuseStep 3608489 = 2706367) B2706367
theorem B175512491 : Blo 666309 175512491 := bstep (se 1 (by rfl) ⟨131634368, by rfl⟩ : syracuseStep 175512491 = 263268737) B263268737
theorem B82364579 : Blo 666309 82364579 := bstep (se 1 (by rfl) ⟨61773434, by rfl⟩ : syracuseStep 82364579 = 123546869) B123546869
theorem B1694803 : Blo 666309 1694803 := bstep (se 1 (by rfl) ⟨1271102, by rfl⟩ : syracuseStep 1694803 = 2542205) B2542205
theorem B1500641 : Blo 666309 1500641 := bstep (se 2 (by rfl) ⟨562740, by rfl⟩ : syracuseStep 1500641 = 1125481) B1125481
theorem B14481767 : Blo 666309 14481767 := bstep (se 1 (by rfl) ⟨10861325, by rfl⟩ : syracuseStep 14481767 = 21722651) B21722651
theorem B2405659 : Blo 666309 2405659 := bstep (se 1 (by rfl) ⟨1804244, by rfl⟩ : syracuseStep 2405659 = 3608489) B3608489
theorem B38618045 : Blo 666309 38618045 := bstep (se 3 (by rfl) ⟨7240883, by rfl⟩ : syracuseStep 38618045 = 14481767) B14481767
theorem B1000427 : Blo 666309 1000427 := bstep (se 1 (by rfl) ⟨750320, by rfl⟩ : syracuseStep 1000427 = 1500641) B1500641
theorem B54909719 : Blo 666309 54909719 := bstep (se 1 (by rfl) ⟨41182289, by rfl⟩ : syracuseStep 54909719 = 82364579) B82364579
theorem B117008327 : Blo 666309 117008327 := bstep (se 1 (by rfl) ⟨87756245, by rfl⟩ : syracuseStep 117008327 = 175512491) B175512491
theorem B2259737 : Blo 666309 2259737 := bstep (se 2 (by rfl) ⟨847401, by rfl⟩ : syracuseStep 2259737 = 1694803) B1694803
theorem B36606479 : Blo 666309 36606479 := bstep (se 1 (by rfl) ⟨27454859, by rfl⟩ : syracuseStep 36606479 = 54909719) B54909719
theorem B666951 : Blo 666309 666951 := bstep (se 1 (by rfl) ⟨500213, by rfl⟩ : syracuseStep 666951 = 1000427) B1000427
theorem B78005551 : Blo 666309 78005551 := bstep (se 1 (by rfl) ⟨58504163, by rfl⟩ : syracuseStep 78005551 = 117008327) B117008327
theorem B25745363 : Blo 666309 25745363 := bstep (se 1 (by rfl) ⟨19309022, by rfl⟩ : syracuseStep 25745363 = 38618045) B38618045
theorem B3207545 : Blo 666309 3207545 := bstep (se 2 (by rfl) ⟨1202829, by rfl⟩ : syracuseStep 3207545 = 2405659) B2405659
theorem B1506491 : Blo 666309 1506491 := bstep (se 1 (by rfl) ⟨1129868, by rfl⟩ : syracuseStep 1506491 = 2259737) B2259737
theorem B97617277 : Blo 666309 97617277 := bstep (se 3 (by rfl) ⟨18303239, by rfl⟩ : syracuseStep 97617277 = 36606479) B36606479
theorem B104007401 : Blo 666309 104007401 := bstep (se 2 (by rfl) ⟨39002775, by rfl⟩ : syracuseStep 104007401 = 78005551) B78005551
theorem B2138363 : Blo 666309 2138363 := bstep (se 1 (by rfl) ⟨1603772, by rfl⟩ : syracuseStep 2138363 = 3207545) B3207545
theorem B1004327 : Blo 666309 1004327 := bstep (se 1 (by rfl) ⟨753245, by rfl⟩ : syracuseStep 1004327 = 1506491) B1506491
theorem B17163575 : Blo 666309 17163575 := bstep (se 1 (by rfl) ⟨12872681, by rfl⟩ : syracuseStep 17163575 = 25745363) B25745363
theorem B69338267 : Blo 666309 69338267 := bstep (se 1 (by rfl) ⟨52003700, by rfl⟩ : syracuseStep 69338267 = 104007401) B104007401
theorem B11442383 : Blo 666309 11442383 := bstep (se 1 (by rfl) ⟨8581787, by rfl⟩ : syracuseStep 11442383 = 17163575) B17163575
theorem B520625477 : Blo 666309 520625477 := bstep (se 4 (by rfl) ⟨48808638, by rfl⟩ : syracuseStep 520625477 = 97617277) B97617277
theorem B669551 : Blo 666309 669551 := bstep (se 1 (by rfl) ⟨502163, by rfl⟩ : syracuseStep 669551 = 1004327) B1004327
theorem B1425575 : Blo 666309 1425575 := bstep (se 1 (by rfl) ⟨1069181, by rfl⟩ : syracuseStep 1425575 = 2138363) B2138363
theorem B950383 : Blo 666309 950383 := bstep (se 1 (by rfl) ⟨712787, by rfl⟩ : syracuseStep 950383 = 1425575) B1425575
theorem B347083651 : Blo 666309 347083651 := bstep (se 1 (by rfl) ⟨260312738, by rfl⟩ : syracuseStep 347083651 = 520625477) B520625477
theorem B46225511 : Blo 666309 46225511 := bstep (se 1 (by rfl) ⟨34669133, by rfl⟩ : syracuseStep 46225511 = 69338267) B69338267
theorem B7628255 : Blo 666309 7628255 := bstep (se 1 (by rfl) ⟨5721191, by rfl⟩ : syracuseStep 7628255 = 11442383) B11442383
theorem B5085503 : Blo 666309 5085503 := bstep (se 1 (by rfl) ⟨3814127, by rfl⟩ : syracuseStep 5085503 = 7628255) B7628255
theorem B30817007 : Blo 666309 30817007 := bstep (se 1 (by rfl) ⟨23112755, by rfl⟩ : syracuseStep 30817007 = 46225511) B46225511
theorem B1267177 : Blo 666309 1267177 := bstep (se 2 (by rfl) ⟨475191, by rfl⟩ : syracuseStep 1267177 = 950383) B950383
theorem B462778201 : Blo 666309 462778201 := bstep (se 2 (by rfl) ⟨173541825, by rfl⟩ : syracuseStep 462778201 = 347083651) B347083651
theorem B3390335 : Blo 666309 3390335 := bstep (se 1 (by rfl) ⟨2542751, by rfl⟩ : syracuseStep 3390335 = 5085503) B5085503
theorem B617037601 : Blo 666309 617037601 := bstep (se 2 (by rfl) ⟨231389100, by rfl⟩ : syracuseStep 617037601 = 462778201) B462778201
theorem B1689569 : Blo 666309 1689569 := bstep (se 2 (by rfl) ⟨633588, by rfl⟩ : syracuseStep 1689569 = 1267177) B1267177
theorem B20544671 : Blo 666309 20544671 := bstep (se 1 (by rfl) ⟨15408503, by rfl⟩ : syracuseStep 20544671 = 30817007) B30817007
theorem B822716801 : Blo 666309 822716801 := bstep (se 2 (by rfl) ⟨308518800, by rfl⟩ : syracuseStep 822716801 = 617037601) B617037601
theorem B1126379 : Blo 666309 1126379 := bstep (se 1 (by rfl) ⟨844784, by rfl⟩ : syracuseStep 1126379 = 1689569) B1689569
theorem B2260223 : Blo 666309 2260223 := bstep (se 1 (by rfl) ⟨1695167, by rfl⟩ : syracuseStep 2260223 = 3390335) B3390335
theorem B13696447 : Blo 666309 13696447 := bstep (se 1 (by rfl) ⟨10272335, by rfl⟩ : syracuseStep 13696447 = 20544671) B20544671
theorem B548477867 : Blo 666309 548477867 := bstep (se 1 (by rfl) ⟨411358400, by rfl⟩ : syracuseStep 548477867 = 822716801) B822716801
theorem B18261929 : Blo 666309 18261929 := bstep (se 2 (by rfl) ⟨6848223, by rfl⟩ : syracuseStep 18261929 = 13696447) B13696447
theorem B750919 : Blo 666309 750919 := bstep (se 1 (by rfl) ⟨563189, by rfl⟩ : syracuseStep 750919 = 1126379) B1126379
theorem B1506815 : Blo 666309 1506815 := bstep (se 1 (by rfl) ⟨1130111, by rfl⟩ : syracuseStep 1506815 = 2260223) B2260223
theorem B12174619 : Blo 666309 12174619 := bstep (se 1 (by rfl) ⟨9130964, by rfl⟩ : syracuseStep 12174619 = 18261929) B18261929
theorem B1001225 : Blo 666309 1001225 := bstep (se 2 (by rfl) ⟨375459, by rfl⟩ : syracuseStep 1001225 = 750919) B750919
theorem B1004543 : Blo 666309 1004543 := bstep (se 1 (by rfl) ⟨753407, by rfl⟩ : syracuseStep 1004543 = 1506815) B1506815
theorem B365651911 : Blo 666309 365651911 := bstep (se 1 (by rfl) ⟨274238933, by rfl⟩ : syracuseStep 365651911 = 548477867) B548477867
theorem B667483 : Blo 666309 667483 := bstep (se 1 (by rfl) ⟨500612, by rfl⟩ : syracuseStep 667483 = 1001225) B1001225
theorem B16232825 : Blo 666309 16232825 := bstep (se 2 (by rfl) ⟨6087309, by rfl⟩ : syracuseStep 16232825 = 12174619) B12174619
theorem B487535881 : Blo 666309 487535881 := bstep (se 2 (by rfl) ⟨182825955, by rfl⟩ : syracuseStep 487535881 = 365651911) B365651911
theorem B669695 : Blo 666309 669695 := bstep (se 1 (by rfl) ⟨502271, by rfl⟩ : syracuseStep 669695 = 1004543) B1004543
theorem B43287533 : Blo 666309 43287533 := bstep (se 3 (by rfl) ⟨8116412, by rfl⟩ : syracuseStep 43287533 = 16232825) B16232825
theorem B650047841 : Blo 666309 650047841 := bstep (se 2 (by rfl) ⟨243767940, by rfl⟩ : syracuseStep 650047841 = 487535881) B487535881
theorem B433365227 : Blo 666309 433365227 := bstep (se 1 (by rfl) ⟨325023920, by rfl⟩ : syracuseStep 433365227 = 650047841) B650047841
theorem B28858355 : Blo 666309 28858355 := bstep (se 1 (by rfl) ⟨21643766, by rfl⟩ : syracuseStep 28858355 = 43287533) B43287533
theorem B19238903 : Blo 666309 19238903 := bstep (se 1 (by rfl) ⟨14429177, by rfl⟩ : syracuseStep 19238903 = 28858355) B28858355
theorem B288910151 : Blo 666309 288910151 := bstep (se 1 (by rfl) ⟨216682613, by rfl⟩ : syracuseStep 288910151 = 433365227) B433365227
theorem B12825935 : Blo 666309 12825935 := bstep (se 1 (by rfl) ⟨9619451, by rfl⟩ : syracuseStep 12825935 = 19238903) B19238903
theorem B192606767 : Blo 666309 192606767 := bstep (se 1 (by rfl) ⟨144455075, by rfl⟩ : syracuseStep 192606767 = 288910151) B288910151
theorem B128404511 : Blo 666309 128404511 := bstep (se 1 (by rfl) ⟨96303383, by rfl⟩ : syracuseStep 128404511 = 192606767) B192606767
theorem B8550623 : Blo 666309 8550623 := bstep (se 1 (by rfl) ⟨6412967, by rfl⟩ : syracuseStep 8550623 = 12825935) B12825935
theorem B85603007 : Blo 666309 85603007 := bstep (se 1 (by rfl) ⟨64202255, by rfl⟩ : syracuseStep 85603007 = 128404511) B128404511
theorem B5700415 : Blo 666309 5700415 := bstep (se 1 (by rfl) ⟨4275311, by rfl⟩ : syracuseStep 5700415 = 8550623) B8550623
theorem B57068671 : Blo 666309 57068671 := bstep (se 1 (by rfl) ⟨42801503, by rfl⟩ : syracuseStep 57068671 = 85603007) B85603007
theorem B7600553 : Blo 666309 7600553 := bstep (se 2 (by rfl) ⟨2850207, by rfl⟩ : syracuseStep 7600553 = 5700415) B5700415
theorem B76091561 : Blo 666309 76091561 := bstep (se 2 (by rfl) ⟨28534335, by rfl⟩ : syracuseStep 76091561 = 57068671) B57068671
theorem B5067035 : Blo 666309 5067035 := bstep (se 1 (by rfl) ⟨3800276, by rfl⟩ : syracuseStep 5067035 = 7600553) B7600553
theorem B50727707 : Blo 666309 50727707 := bstep (se 1 (by rfl) ⟨38045780, by rfl⟩ : syracuseStep 50727707 = 76091561) B76091561
theorem B3378023 : Blo 666309 3378023 := bstep (se 1 (by rfl) ⟨2533517, by rfl⟩ : syracuseStep 3378023 = 5067035) B5067035
theorem B33818471 : Blo 666309 33818471 := bstep (se 1 (by rfl) ⟨25363853, by rfl⟩ : syracuseStep 33818471 = 50727707) B50727707
theorem B2252015 : Blo 666309 2252015 := bstep (se 1 (by rfl) ⟨1689011, by rfl⟩ : syracuseStep 2252015 = 3378023) B3378023
theorem B22545647 : Blo 666309 22545647 := bstep (se 1 (by rfl) ⟨16909235, by rfl⟩ : syracuseStep 22545647 = 33818471) B33818471
theorem B1501343 : Blo 666309 1501343 := bstep (se 1 (by rfl) ⟨1126007, by rfl⟩ : syracuseStep 1501343 = 2252015) B2252015
theorem B1000895 : Blo 666309 1000895 := bstep (se 1 (by rfl) ⟨750671, by rfl⟩ : syracuseStep 1000895 = 1501343) B1501343
theorem B15030431 : Blo 666309 15030431 := bstep (se 1 (by rfl) ⟨11272823, by rfl⟩ : syracuseStep 15030431 = 22545647) B22545647
theorem B667263 : Blo 666309 667263 := bstep (se 1 (by rfl) ⟨500447, by rfl⟩ : syracuseStep 667263 = 1000895) B1000895
theorem B10020287 : Blo 666309 10020287 := bstep (se 1 (by rfl) ⟨7515215, by rfl⟩ : syracuseStep 10020287 = 15030431) B15030431
theorem B6680191 : Blo 666309 6680191 := bstep (se 1 (by rfl) ⟨5010143, by rfl⟩ : syracuseStep 6680191 = 10020287) B10020287
theorem B8906921 : Blo 666309 8906921 := bstep (se 2 (by rfl) ⟨3340095, by rfl⟩ : syracuseStep 8906921 = 6680191) B6680191
theorem B5937947 : Blo 666309 5937947 := bstep (se 1 (by rfl) ⟨4453460, by rfl⟩ : syracuseStep 5937947 = 8906921) B8906921
theorem B3958631 : Blo 666309 3958631 := bstep (se 1 (by rfl) ⟨2968973, by rfl⟩ : syracuseStep 3958631 = 5937947) B5937947
theorem B2639087 : Blo 666309 2639087 := bstep (se 1 (by rfl) ⟨1979315, by rfl⟩ : syracuseStep 2639087 = 3958631) B3958631
theorem B1759391 : Blo 666309 1759391 := bstep (se 1 (by rfl) ⟨1319543, by rfl⟩ : syracuseStep 1759391 = 2639087) B2639087
theorem B1172927 : Blo 666309 1172927 := bstep (se 1 (by rfl) ⟨879695, by rfl⟩ : syracuseStep 1172927 = 1759391) B1759391
theorem B781951 : Blo 666309 781951 := bstep (se 1 (by rfl) ⟨586463, by rfl⟩ : syracuseStep 781951 = 1172927) B1172927
theorem B1042601 : Blo 666309 1042601 := bstep (se 2 (by rfl) ⟨390975, by rfl⟩ : syracuseStep 1042601 = 781951) B781951
theorem B11121077 : Blo 666309 11121077 := bstep (se 5 (by rfl) ⟨521300, by rfl⟩ : syracuseStep 11121077 = 1042601) B1042601
theorem B7414051 : Blo 666309 7414051 := bstep (se 1 (by rfl) ⟨5560538, by rfl⟩ : syracuseStep 7414051 = 11121077) B11121077
theorem B9885401 : Blo 666309 9885401 := bstep (se 2 (by rfl) ⟨3707025, by rfl⟩ : syracuseStep 9885401 = 7414051) B7414051
theorem B6590267 : Blo 666309 6590267 := bstep (se 1 (by rfl) ⟨4942700, by rfl⟩ : syracuseStep 6590267 = 9885401) B9885401
theorem B4393511 : Blo 666309 4393511 := bstep (se 1 (by rfl) ⟨3295133, by rfl⟩ : syracuseStep 4393511 = 6590267) B6590267
theorem B2929007 : Blo 666309 2929007 := bstep (se 1 (by rfl) ⟨2196755, by rfl⟩ : syracuseStep 2929007 = 4393511) B4393511
theorem B1952671 : Blo 666309 1952671 := bstep (se 1 (by rfl) ⟨1464503, by rfl⟩ : syracuseStep 1952671 = 2929007) B2929007
theorem B2603561 : Blo 666309 2603561 := bstep (se 2 (by rfl) ⟨976335, by rfl⟩ : syracuseStep 2603561 = 1952671) B1952671
theorem B6942829 : Blo 666309 6942829 := bstep (se 3 (by rfl) ⟨1301780, by rfl⟩ : syracuseStep 6942829 = 2603561) B2603561
theorem B9257105 : Blo 666309 9257105 := bstep (se 2 (by rfl) ⟨3471414, by rfl⟩ : syracuseStep 9257105 = 6942829) B6942829
theorem B6171403 : Blo 666309 6171403 := bstep (se 1 (by rfl) ⟨4628552, by rfl⟩ : syracuseStep 6171403 = 9257105) B9257105
theorem B8228537 : Blo 666309 8228537 := bstep (se 2 (by rfl) ⟨3085701, by rfl⟩ : syracuseStep 8228537 = 6171403) B6171403
theorem B5485691 : Blo 666309 5485691 := bstep (se 1 (by rfl) ⟨4114268, by rfl⟩ : syracuseStep 5485691 = 8228537) B8228537
theorem B14628509 : Blo 666309 14628509 := bstep (se 3 (by rfl) ⟨2742845, by rfl⟩ : syracuseStep 14628509 = 5485691) B5485691
theorem B9752339 : Blo 666309 9752339 := bstep (se 1 (by rfl) ⟨7314254, by rfl⟩ : syracuseStep 9752339 = 14628509) B14628509
theorem B6501559 : Blo 666309 6501559 := bstep (se 1 (by rfl) ⟨4876169, by rfl⟩ : syracuseStep 6501559 = 9752339) B9752339
theorem B8668745 : Blo 666309 8668745 := bstep (se 2 (by rfl) ⟨3250779, by rfl⟩ : syracuseStep 8668745 = 6501559) B6501559
theorem B5779163 : Blo 666309 5779163 := bstep (se 1 (by rfl) ⟨4334372, by rfl⟩ : syracuseStep 5779163 = 8668745) B8668745
theorem B3852775 : Blo 666309 3852775 := bstep (se 1 (by rfl) ⟨2889581, by rfl⟩ : syracuseStep 3852775 = 5779163) B5779163
theorem B5137033 : Blo 666309 5137033 := bstep (se 2 (by rfl) ⟨1926387, by rfl⟩ : syracuseStep 5137033 = 3852775) B3852775
theorem B6849377 : Blo 666309 6849377 := bstep (se 2 (by rfl) ⟨2568516, by rfl⟩ : syracuseStep 6849377 = 5137033) B5137033
theorem B4566251 : Blo 666309 4566251 := bstep (se 1 (by rfl) ⟨3424688, by rfl⟩ : syracuseStep 4566251 = 6849377) B6849377
theorem B12176669 : Blo 666309 12176669 := bstep (se 3 (by rfl) ⟨2283125, by rfl⟩ : syracuseStep 12176669 = 4566251) B4566251
theorem B8117779 : Blo 666309 8117779 := bstep (se 1 (by rfl) ⟨6088334, by rfl⟩ : syracuseStep 8117779 = 12176669) B12176669
theorem B10823705 : Blo 666309 10823705 := bstep (se 2 (by rfl) ⟨4058889, by rfl⟩ : syracuseStep 10823705 = 8117779) B8117779
theorem B7215803 : Blo 666309 7215803 := bstep (se 1 (by rfl) ⟨5411852, by rfl⟩ : syracuseStep 7215803 = 10823705) B10823705
theorem B4810535 : Blo 666309 4810535 := bstep (se 1 (by rfl) ⟨3607901, by rfl⟩ : syracuseStep 4810535 = 7215803) B7215803
theorem B3207023 : Blo 666309 3207023 := bstep (se 1 (by rfl) ⟨2405267, by rfl⟩ : syracuseStep 3207023 = 4810535) B4810535
theorem B2138015 : Blo 666309 2138015 := bstep (se 1 (by rfl) ⟨1603511, by rfl⟩ : syracuseStep 2138015 = 3207023) B3207023
theorem B5701373 : Blo 666309 5701373 := bstep (se 3 (by rfl) ⟨1069007, by rfl⟩ : syracuseStep 5701373 = 2138015) B2138015
theorem B3800915 : Blo 666309 3800915 := bstep (se 1 (by rfl) ⟨2850686, by rfl⟩ : syracuseStep 3800915 = 5701373) B5701373
theorem B2533943 : Blo 666309 2533943 := bstep (se 1 (by rfl) ⟨1900457, by rfl⟩ : syracuseStep 2533943 = 3800915) B3800915
theorem B1689295 : Blo 666309 1689295 := bstep (se 1 (by rfl) ⟨1266971, by rfl⟩ : syracuseStep 1689295 = 2533943) B2533943
theorem B2252393 : Blo 666309 2252393 := bstep (se 2 (by rfl) ⟨844647, by rfl⟩ : syracuseStep 2252393 = 1689295) B1689295
theorem B1501595 : Blo 666309 1501595 := bstep (se 1 (by rfl) ⟨1126196, by rfl⟩ : syracuseStep 1501595 = 2252393) B2252393
theorem B1001063 : Blo 666309 1001063 := bstep (se 1 (by rfl) ⟨750797, by rfl⟩ : syracuseStep 1001063 = 1501595) B1501595
theorem B667375 : Blo 666309 667375 := bstep (se 1 (by rfl) ⟨500531, by rfl⟩ : syracuseStep 667375 = 1001063) B1001063

theorem C0 (j : ℕ) (h1 : 166577 ≤ j) (h2 : j ≤ 167276) : Blo 666309 (4 * j + 3) := by
  interval_cases j
  · exact B666311
  · exact B666315
  · exact B666319
  · exact B666323
  · exact B666327
  · exact B666331
  · exact B666335
  · exact B666339
  · exact B666343
  · exact B666347
  · exact B666351
  · exact B666355
  · exact B666359
  · exact B666363
  · exact B666367
  · exact B666371
  · exact B666375
  · exact B666379
  · exact B666383
  · exact B666387
  · exact B666391
  · exact B666395
  · exact B666399
  · exact B666403
  · exact B666407
  · exact B666411
  · exact B666415
  · exact B666419
  · exact B666423
  · exact B666427
  · exact B666431
  · exact B666435
  · exact B666439
  · exact B666443
  · exact B666447
  · exact B666451
  · exact B666455
  · exact B666459
  · exact B666463
  · exact B666467
  · exact B666471
  · exact B666475
  · exact B666479
  · exact B666483
  · exact B666487
  · exact B666491
  · exact B666495
  · exact B666499
  · exact B666503
  · exact B666507
  · exact B666511
  · exact B666515
  · exact B666519
  · exact B666523
  · exact B666527
  · exact B666531
  · exact B666535
  · exact B666539
  · exact B666543
  · exact B666547
  · exact B666551
  · exact B666555
  · exact B666559
  · exact B666563
  · exact B666567
  · exact B666571
  · exact B666575
  · exact B666579
  · exact B666583
  · exact B666587
  · exact B666591
  · exact B666595
  · exact B666599
  · exact B666603
  · exact B666607
  · exact B666611
  · exact B666615
  · exact B666619
  · exact B666623
  · exact B666627
  · exact B666631
  · exact B666635
  · exact B666639
  · exact B666643
  · exact B666647
  · exact B666651
  · exact B666655
  · exact B666659
  · exact B666663
  · exact B666667
  · exact B666671
  · exact B666675
  · exact B666679
  · exact B666683
  · exact B666687
  · exact B666691
  · exact B666695
  · exact B666699
  · exact B666703
  · exact B666707
  · exact B666711
  · exact B666715
  · exact B666719
  · exact B666723
  · exact B666727
  · exact B666731
  · exact B666735
  · exact B666739
  · exact B666743
  · exact B666747
  · exact B666751
  · exact B666755
  · exact B666759
  · exact B666763
  · exact B666767
  · exact B666771
  · exact B666775
  · exact B666779
  · exact B666783
  · exact B666787
  · exact B666791
  · exact B666795
  · exact B666799
  · exact B666803
  · exact B666807
  · exact B666811
  · exact B666815
  · exact B666819
  · exact B666823
  · exact B666827
  · exact B666831
  · exact B666835
  · exact B666839
  · exact B666843
  · exact B666847
  · exact B666851
  · exact B666855
  · exact B666859
  · exact B666863
  · exact B666867
  · exact B666871
  · exact B666875
  · exact B666879
  · exact B666883
  · exact B666887
  · exact B666891
  · exact B666895
  · exact B666899
  · exact B666903
  · exact B666907
  · exact B666911
  · exact B666915
  · exact B666919
  · exact B666923
  · exact B666927
  · exact B666931
  · exact B666935
  · exact B666939
  · exact B666943
  · exact B666947
  · exact B666951
  · exact B666955
  · exact B666959
  · exact B666963
  · exact B666967
  · exact B666971
  · exact B666975
  · exact B666979
  · exact B666983
  · exact B666987
  · exact B666991
  · exact B666995
  · exact B666999
  · exact B667003
  · exact B667007
  · exact B667011
  · exact B667015
  · exact B667019
  · exact B667023
  · exact B667027
  · exact B667031
  · exact B667035
  · exact B667039
  · exact B667043
  · exact B667047
  · exact B667051
  · exact B667055
  · exact B667059
  · exact B667063
  · exact B667067
  · exact B667071
  · exact B667075
  · exact B667079
  · exact B667083
  · exact B667087
  · exact B667091
  · exact B667095
  · exact B667099
  · exact B667103
  · exact B667107
  · exact B667111
  · exact B667115
  · exact B667119
  · exact B667123
  · exact B667127
  · exact B667131
  · exact B667135
  · exact B667139
  · exact B667143
  · exact B667147
  · exact B667151
  · exact B667155
  · exact B667159
  · exact B667163
  · exact B667167
  · exact B667171
  · exact B667175
  · exact B667179
  · exact B667183
  · exact B667187
  · exact B667191
  · exact B667195
  · exact B667199
  · exact B667203
  · exact B667207
  · exact B667211
  · exact B667215
  · exact B667219
  · exact B667223
  · exact B667227
  · exact B667231
  · exact B667235
  · exact B667239
  · exact B667243
  · exact B667247
  · exact B667251
  · exact B667255
  · exact B667259
  · exact B667263
  · exact B667267
  · exact B667271
  · exact B667275
  · exact B667279
  · exact B667283
  · exact B667287
  · exact B667291
  · exact B667295
  · exact B667299
  · exact B667303
  · exact B667307
  · exact B667311
  · exact B667315
  · exact B667319
  · exact B667323
  · exact B667327
  · exact B667331
  · exact B667335
  · exact B667339
  · exact B667343
  · exact B667347
  · exact B667351
  · exact B667355
  · exact B667359
  · exact B667363
  · exact B667367
  · exact B667371
  · exact B667375
  · exact B667379
  · exact B667383
  · exact B667387
  · exact B667391
  · exact B667395
  · exact B667399
  · exact B667403
  · exact B667407
  · exact B667411
  · exact B667415
  · exact B667419
  · exact B667423
  · exact B667427
  · exact B667431
  · exact B667435
  · exact B667439
  · exact B667443
  · exact B667447
  · exact B667451
  · exact B667455
  · exact B667459
  · exact B667463
  · exact B667467
  · exact B667471
  · exact B667475
  · exact B667479
  · exact B667483
  · exact B667487
  · exact B667491
  · exact B667495
  · exact B667499
  · exact B667503
  · exact B667507
  · exact B667511
  · exact B667515
  · exact B667519
  · exact B667523
  · exact B667527
  · exact B667531
  · exact B667535
  · exact B667539
  · exact B667543
  · exact B667547
  · exact B667551
  · exact B667555
  · exact B667559
  · exact B667563
  · exact B667567
  · exact B667571
  · exact B667575
  · exact B667579
  · exact B667583
  · exact B667587
  · exact B667591
  · exact B667595
  · exact B667599
  · exact B667603
  · exact B667607
  · exact B667611
  · exact B667615
  · exact B667619
  · exact B667623
  · exact B667627
  · exact B667631
  · exact B667635
  · exact B667639
  · exact B667643
  · exact B667647
  · exact B667651
  · exact B667655
  · exact B667659
  · exact B667663
  · exact B667667
  · exact B667671
  · exact B667675
  · exact B667679
  · exact B667683
  · exact B667687
  · exact B667691
  · exact B667695
  · exact B667699
  · exact B667703
  · exact B667707
  · exact B667711
  · exact B667715
  · exact B667719
  · exact B667723
  · exact B667727
  · exact B667731
  · exact B667735
  · exact B667739
  · exact B667743
  · exact B667747
  · exact B667751
  · exact B667755
  · exact B667759
  · exact B667763
  · exact B667767
  · exact B667771
  · exact B667775
  · exact B667779
  · exact B667783
  · exact B667787
  · exact B667791
  · exact B667795
  · exact B667799
  · exact B667803
  · exact B667807
  · exact B667811
  · exact B667815
  · exact B667819
  · exact B667823
  · exact B667827
  · exact B667831
  · exact B667835
  · exact B667839
  · exact B667843
  · exact B667847
  · exact B667851
  · exact B667855
  · exact B667859
  · exact B667863
  · exact B667867
  · exact B667871
  · exact B667875
  · exact B667879
  · exact B667883
  · exact B667887
  · exact B667891
  · exact B667895
  · exact B667899
  · exact B667903
  · exact B667907
  · exact B667911
  · exact B667915
  · exact B667919
  · exact B667923
  · exact B667927
  · exact B667931
  · exact B667935
  · exact B667939
  · exact B667943
  · exact B667947
  · exact B667951
  · exact B667955
  · exact B667959
  · exact B667963
  · exact B667967
  · exact B667971
  · exact B667975
  · exact B667979
  · exact B667983
  · exact B667987
  · exact B667991
  · exact B667995
  · exact B667999
  · exact B668003
  · exact B668007
  · exact B668011
  · exact B668015
  · exact B668019
  · exact B668023
  · exact B668027
  · exact B668031
  · exact B668035
  · exact B668039
  · exact B668043
  · exact B668047
  · exact B668051
  · exact B668055
  · exact B668059
  · exact B668063
  · exact B668067
  · exact B668071
  · exact B668075
  · exact B668079
  · exact B668083
  · exact B668087
  · exact B668091
  · exact B668095
  · exact B668099
  · exact B668103
  · exact B668107
  · exact B668111
  · exact B668115
  · exact B668119
  · exact B668123
  · exact B668127
  · exact B668131
  · exact B668135
  · exact B668139
  · exact B668143
  · exact B668147
  · exact B668151
  · exact B668155
  · exact B668159
  · exact B668163
  · exact B668167
  · exact B668171
  · exact B668175
  · exact B668179
  · exact B668183
  · exact B668187
  · exact B668191
  · exact B668195
  · exact B668199
  · exact B668203
  · exact B668207
  · exact B668211
  · exact B668215
  · exact B668219
  · exact B668223
  · exact B668227
  · exact B668231
  · exact B668235
  · exact B668239
  · exact B668243
  · exact B668247
  · exact B668251
  · exact B668255
  · exact B668259
  · exact B668263
  · exact B668267
  · exact B668271
  · exact B668275
  · exact B668279
  · exact B668283
  · exact B668287
  · exact B668291
  · exact B668295
  · exact B668299
  · exact B668303
  · exact B668307
  · exact B668311
  · exact B668315
  · exact B668319
  · exact B668323
  · exact B668327
  · exact B668331
  · exact B668335
  · exact B668339
  · exact B668343
  · exact B668347
  · exact B668351
  · exact B668355
  · exact B668359
  · exact B668363
  · exact B668367
  · exact B668371
  · exact B668375
  · exact B668379
  · exact B668383
  · exact B668387
  · exact B668391
  · exact B668395
  · exact B668399
  · exact B668403
  · exact B668407
  · exact B668411
  · exact B668415
  · exact B668419
  · exact B668423
  · exact B668427
  · exact B668431
  · exact B668435
  · exact B668439
  · exact B668443
  · exact B668447
  · exact B668451
  · exact B668455
  · exact B668459
  · exact B668463
  · exact B668467
  · exact B668471
  · exact B668475
  · exact B668479
  · exact B668483
  · exact B668487
  · exact B668491
  · exact B668495
  · exact B668499
  · exact B668503
  · exact B668507
  · exact B668511
  · exact B668515
  · exact B668519
  · exact B668523
  · exact B668527
  · exact B668531
  · exact B668535
  · exact B668539
  · exact B668543
  · exact B668547
  · exact B668551
  · exact B668555
  · exact B668559
  · exact B668563
  · exact B668567
  · exact B668571
  · exact B668575
  · exact B668579
  · exact B668583
  · exact B668587
  · exact B668591
  · exact B668595
  · exact B668599
  · exact B668603
  · exact B668607
  · exact B668611
  · exact B668615
  · exact B668619
  · exact B668623
  · exact B668627
  · exact B668631
  · exact B668635
  · exact B668639
  · exact B668643
  · exact B668647
  · exact B668651
  · exact B668655
  · exact B668659
  · exact B668663
  · exact B668667
  · exact B668671
  · exact B668675
  · exact B668679
  · exact B668683
  · exact B668687
  · exact B668691
  · exact B668695
  · exact B668699
  · exact B668703
  · exact B668707
  · exact B668711
  · exact B668715
  · exact B668719
  · exact B668723
  · exact B668727
  · exact B668731
  · exact B668735
  · exact B668739
  · exact B668743
  · exact B668747
  · exact B668751
  · exact B668755
  · exact B668759
  · exact B668763
  · exact B668767
  · exact B668771
  · exact B668775
  · exact B668779
  · exact B668783
  · exact B668787
  · exact B668791
  · exact B668795
  · exact B668799
  · exact B668803
  · exact B668807
  · exact B668811
  · exact B668815
  · exact B668819
  · exact B668823
  · exact B668827
  · exact B668831
  · exact B668835
  · exact B668839
  · exact B668843
  · exact B668847
  · exact B668851
  · exact B668855
  · exact B668859
  · exact B668863
  · exact B668867
  · exact B668871
  · exact B668875
  · exact B668879
  · exact B668883
  · exact B668887
  · exact B668891
  · exact B668895
  · exact B668899
  · exact B668903
  · exact B668907
  · exact B668911
  · exact B668915
  · exact B668919
  · exact B668923
  · exact B668927
  · exact B668931
  · exact B668935
  · exact B668939
  · exact B668943
  · exact B668947
  · exact B668951
  · exact B668955
  · exact B668959
  · exact B668963
  · exact B668967
  · exact B668971
  · exact B668975
  · exact B668979
  · exact B668983
  · exact B668987
  · exact B668991
  · exact B668995
  · exact B668999
  · exact B669003
  · exact B669007
  · exact B669011
  · exact B669015
  · exact B669019
  · exact B669023
  · exact B669027
  · exact B669031
  · exact B669035
  · exact B669039
  · exact B669043
  · exact B669047
  · exact B669051
  · exact B669055
  · exact B669059
  · exact B669063
  · exact B669067
  · exact B669071
  · exact B669075
  · exact B669079
  · exact B669083
  · exact B669087
  · exact B669091
  · exact B669095
  · exact B669099
  · exact B669103
  · exact B669107

theorem C1 (j : ℕ) (h1 : 167277 ≤ j) (h2 : j ≤ 167576) : Blo 666309 (4 * j + 3) := by
  interval_cases j
  · exact B669111
  · exact B669115
  · exact B669119
  · exact B669123
  · exact B669127
  · exact B669131
  · exact B669135
  · exact B669139
  · exact B669143
  · exact B669147
  · exact B669151
  · exact B669155
  · exact B669159
  · exact B669163
  · exact B669167
  · exact B669171
  · exact B669175
  · exact B669179
  · exact B669183
  · exact B669187
  · exact B669191
  · exact B669195
  · exact B669199
  · exact B669203
  · exact B669207
  · exact B669211
  · exact B669215
  · exact B669219
  · exact B669223
  · exact B669227
  · exact B669231
  · exact B669235
  · exact B669239
  · exact B669243
  · exact B669247
  · exact B669251
  · exact B669255
  · exact B669259
  · exact B669263
  · exact B669267
  · exact B669271
  · exact B669275
  · exact B669279
  · exact B669283
  · exact B669287
  · exact B669291
  · exact B669295
  · exact B669299
  · exact B669303
  · exact B669307
  · exact B669311
  · exact B669315
  · exact B669319
  · exact B669323
  · exact B669327
  · exact B669331
  · exact B669335
  · exact B669339
  · exact B669343
  · exact B669347
  · exact B669351
  · exact B669355
  · exact B669359
  · exact B669363
  · exact B669367
  · exact B669371
  · exact B669375
  · exact B669379
  · exact B669383
  · exact B669387
  · exact B669391
  · exact B669395
  · exact B669399
  · exact B669403
  · exact B669407
  · exact B669411
  · exact B669415
  · exact B669419
  · exact B669423
  · exact B669427
  · exact B669431
  · exact B669435
  · exact B669439
  · exact B669443
  · exact B669447
  · exact B669451
  · exact B669455
  · exact B669459
  · exact B669463
  · exact B669467
  · exact B669471
  · exact B669475
  · exact B669479
  · exact B669483
  · exact B669487
  · exact B669491
  · exact B669495
  · exact B669499
  · exact B669503
  · exact B669507
  · exact B669511
  · exact B669515
  · exact B669519
  · exact B669523
  · exact B669527
  · exact B669531
  · exact B669535
  · exact B669539
  · exact B669543
  · exact B669547
  · exact B669551
  · exact B669555
  · exact B669559
  · exact B669563
  · exact B669567
  · exact B669571
  · exact B669575
  · exact B669579
  · exact B669583
  · exact B669587
  · exact B669591
  · exact B669595
  · exact B669599
  · exact B669603
  · exact B669607
  · exact B669611
  · exact B669615
  · exact B669619
  · exact B669623
  · exact B669627
  · exact B669631
  · exact B669635
  · exact B669639
  · exact B669643
  · exact B669647
  · exact B669651
  · exact B669655
  · exact B669659
  · exact B669663
  · exact B669667
  · exact B669671
  · exact B669675
  · exact B669679
  · exact B669683
  · exact B669687
  · exact B669691
  · exact B669695
  · exact B669699
  · exact B669703
  · exact B669707
  · exact B669711
  · exact B669715
  · exact B669719
  · exact B669723
  · exact B669727
  · exact B669731
  · exact B669735
  · exact B669739
  · exact B669743
  · exact B669747
  · exact B669751
  · exact B669755
  · exact B669759
  · exact B669763
  · exact B669767
  · exact B669771
  · exact B669775
  · exact B669779
  · exact B669783
  · exact B669787
  · exact B669791
  · exact B669795
  · exact B669799
  · exact B669803
  · exact B669807
  · exact B669811
  · exact B669815
  · exact B669819
  · exact B669823
  · exact B669827
  · exact B669831
  · exact B669835
  · exact B669839
  · exact B669843
  · exact B669847
  · exact B669851
  · exact B669855
  · exact B669859
  · exact B669863
  · exact B669867
  · exact B669871
  · exact B669875
  · exact B669879
  · exact B669883
  · exact B669887
  · exact B669891
  · exact B669895
  · exact B669899
  · exact B669903
  · exact B669907
  · exact B669911
  · exact B669915
  · exact B669919
  · exact B669923
  · exact B669927
  · exact B669931
  · exact B669935
  · exact B669939
  · exact B669943
  · exact B669947
  · exact B669951
  · exact B669955
  · exact B669959
  · exact B669963
  · exact B669967
  · exact B669971
  · exact B669975
  · exact B669979
  · exact B669983
  · exact B669987
  · exact B669991
  · exact B669995
  · exact B669999
  · exact B670003
  · exact B670007
  · exact B670011
  · exact B670015
  · exact B670019
  · exact B670023
  · exact B670027
  · exact B670031
  · exact B670035
  · exact B670039
  · exact B670043
  · exact B670047
  · exact B670051
  · exact B670055
  · exact B670059
  · exact B670063
  · exact B670067
  · exact B670071
  · exact B670075
  · exact B670079
  · exact B670083
  · exact B670087
  · exact B670091
  · exact B670095
  · exact B670099
  · exact B670103
  · exact B670107
  · exact B670111
  · exact B670115
  · exact B670119
  · exact B670123
  · exact B670127
  · exact B670131
  · exact B670135
  · exact B670139
  · exact B670143
  · exact B670147
  · exact B670151
  · exact B670155
  · exact B670159
  · exact B670163
  · exact B670167
  · exact B670171
  · exact B670175
  · exact B670179
  · exact B670183
  · exact B670187
  · exact B670191
  · exact B670195
  · exact B670199
  · exact B670203
  · exact B670207
  · exact B670211
  · exact B670215
  · exact B670219
  · exact B670223
  · exact B670227
  · exact B670231
  · exact B670235
  · exact B670239
  · exact B670243
  · exact B670247
  · exact B670251
  · exact B670255
  · exact B670259
  · exact B670263
  · exact B670267
  · exact B670271
  · exact B670275
  · exact B670279
  · exact B670283
  · exact B670287
  · exact B670291
  · exact B670295
  · exact B670299
  · exact B670303
  · exact B670307

theorem solution (m : ℕ) (hlo : 666309 ≤ m) (hhi : m ≤ 670309) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 166577 ≤ j := by omega
    have hj2 : j ≤ 167576 := by omega
    have hb : Blo 666309 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 167277 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
