-- Prove2me | solution 1 for syracuse_descends_range_1503572_1505448
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:48:19.41461+00:00
-- url     : https://prove2.me/submissions/fd6f0ae4-8e83-4217-9b2d-0275fe9a16d5

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


theorem B2539525 : Blo 1503572 2539525 := bbase (se 4 (by rfl) ⟨238080, by rfl⟩ : syracuseStep 2539525 = 476161) (by norm_num)
theorem B16482325 : Blo 1503572 16482325 := bbase (se 6 (by rfl) ⟨386304, by rfl⟩ : syracuseStep 16482325 = 772609) (by norm_num)
theorem B3383333 : Blo 1503572 3383333 := bbase (se 4 (by rfl) ⟨317187, by rfl⟩ : syracuseStep 3383333 = 634375) (by norm_num)
theorem B5079077 : Blo 1503572 5079077 := bbase (se 4 (by rfl) ⟨476163, by rfl⟩ : syracuseStep 5079077 = 952327) (by norm_num)
theorem B12845141 : Blo 1503572 12845141 := bbase (se 8 (by rfl) ⟨75264, by rfl⟩ : syracuseStep 12845141 = 150529) (by norm_num)
theorem B2539613 : Blo 1503572 2539613 := bbase (se 3 (by rfl) ⟨476177, by rfl⟩ : syracuseStep 2539613 = 952355) (by norm_num)
theorem B3383405 : Blo 1503572 3383405 := bbase (se 3 (by rfl) ⟨634388, by rfl⟩ : syracuseStep 3383405 = 1268777) (by norm_num)
theorem B3809389 : Blo 1503572 3809389 := bbase (se 3 (by rfl) ⟨714260, by rfl⟩ : syracuseStep 3809389 = 1428521) (by norm_num)
theorem B3211397 : Blo 1503572 3211397 := bbase (se 4 (by rfl) ⟨301068, by rfl⟩ : syracuseStep 3211397 = 602137) (by norm_num)
theorem B2711693 : Blo 1503572 2711693 := bbase (se 3 (by rfl) ⟨508442, by rfl⟩ : syracuseStep 2711693 = 1016885) (by norm_num)
theorem B3383477 : Blo 1503572 3383477 := bbase (se 5 (by rfl) ⟨158600, by rfl⟩ : syracuseStep 3383477 = 317201) (by norm_num)
theorem B3809501 : Blo 1503572 3809501 := bbase (se 3 (by rfl) ⟨714281, by rfl⟩ : syracuseStep 3809501 = 1428563) (by norm_num)
theorem B2539741 : Blo 1503572 2539741 := bbase (se 3 (by rfl) ⟨476201, by rfl⟩ : syracuseStep 2539741 = 952403) (by norm_num)
theorem B3383549 : Blo 1503572 3383549 := bbase (se 3 (by rfl) ⟨634415, by rfl⟩ : syracuseStep 3383549 = 1268831) (by norm_num)
theorem B2539829 : Blo 1503572 2539829 := bbase (se 5 (by rfl) ⟨119054, by rfl⟩ : syracuseStep 2539829 = 238109) (by norm_num)
theorem B3383621 : Blo 1503572 3383621 := bbase (se 4 (by rfl) ⟨317214, by rfl⟩ : syracuseStep 3383621 = 634429) (by norm_num)
theorem B3383693 : Blo 1503572 3383693 := bbase (se 3 (by rfl) ⟨634442, by rfl⟩ : syracuseStep 3383693 = 1268885) (by norm_num)
theorem B3809693 : Blo 1503572 3809693 := bbase (se 3 (by rfl) ⟨714317, by rfl⟩ : syracuseStep 3809693 = 1428635) (by norm_num)
theorem B2539957 : Blo 1503572 2539957 := bbase (se 5 (by rfl) ⟨119060, by rfl⟩ : syracuseStep 2539957 = 238121) (by norm_num)
theorem B3383765 : Blo 1503572 3383765 := bbase (se 7 (by rfl) ⟨39653, by rfl⟩ : syracuseStep 3383765 = 79307) (by norm_num)
theorem B5079509 : Blo 1503572 5079509 := bbase (se 7 (by rfl) ⟨59525, by rfl⟩ : syracuseStep 5079509 = 119051) (by norm_num)
theorem B3858941 : Blo 1503572 3858941 := bbase (se 3 (by rfl) ⟨723551, by rfl⟩ : syracuseStep 3858941 = 1447103) (by norm_num)
theorem B5792261 : Blo 1503572 5792261 := bbase (se 4 (by rfl) ⟨543024, by rfl⟩ : syracuseStep 5792261 = 1086049) (by norm_num)
theorem B2540045 : Blo 1503572 2540045 := bbase (se 3 (by rfl) ⟨476258, by rfl⟩ : syracuseStep 2540045 = 952517) (by norm_num)
theorem B3383837 : Blo 1503572 3383837 := bbase (se 3 (by rfl) ⟨634469, by rfl⟩ : syracuseStep 3383837 = 1268939) (by norm_num)
theorem B1606177 : Blo 1503572 1606177 := bbase (se 2 (by rfl) ⟨602316, by rfl⟩ : syracuseStep 1606177 = 1204633) (by norm_num)
theorem B3383909 : Blo 1503572 3383909 := bbase (se 4 (by rfl) ⟨317241, by rfl⟩ : syracuseStep 3383909 = 634483) (by norm_num)
theorem B1606249 : Blo 1503572 1606249 := bbase (se 2 (by rfl) ⟨602343, by rfl⟩ : syracuseStep 1606249 = 1204687) (by norm_num)
theorem B2540173 : Blo 1503572 2540173 := bbase (se 3 (by rfl) ⟨476282, by rfl⟩ : syracuseStep 2540173 = 952565) (by norm_num)
theorem B2286245 : Blo 1503572 2286245 := bbase (se 4 (by rfl) ⟨214335, by rfl⟩ : syracuseStep 2286245 = 428671) (by norm_num)
theorem B3383981 : Blo 1503572 3383981 := bbase (se 3 (by rfl) ⟨634496, by rfl⟩ : syracuseStep 3383981 = 1268993) (by norm_num)
theorem B2540261 : Blo 1503572 2540261 := bbase (se 4 (by rfl) ⟨238149, by rfl⟩ : syracuseStep 2540261 = 476299) (by norm_num)
theorem B3384053 : Blo 1503572 3384053 := bbase (se 5 (by rfl) ⟨158627, by rfl⟩ : syracuseStep 3384053 = 317255) (by norm_num)
theorem B3810037 : Blo 1503572 3810037 := bbase (se 5 (by rfl) ⟨178595, by rfl⟩ : syracuseStep 3810037 = 357191) (by norm_num)
theorem B1606429 : Blo 1503572 1606429 := bbase (se 3 (by rfl) ⟨301205, by rfl⟩ : syracuseStep 1606429 = 602411) (by norm_num)
theorem B3384125 : Blo 1503572 3384125 := bbase (se 3 (by rfl) ⟨634523, by rfl⟩ : syracuseStep 3384125 = 1269047) (by norm_num)
theorem B3810149 : Blo 1503572 3810149 := bbase (se 4 (by rfl) ⟨357201, by rfl⟩ : syracuseStep 3810149 = 714403) (by norm_num)
theorem B2540389 : Blo 1503572 2540389 := bbase (se 4 (by rfl) ⟨238161, by rfl⟩ : syracuseStep 2540389 = 476323) (by norm_num)
theorem B3212149 : Blo 1503572 3212149 := bbase (se 5 (by rfl) ⟨150569, by rfl⟩ : syracuseStep 3212149 = 301139) (by norm_num)
theorem B3384197 : Blo 1503572 3384197 := bbase (se 4 (by rfl) ⟨317268, by rfl⟩ : syracuseStep 3384197 = 634537) (by norm_num)
theorem B5079941 : Blo 1503572 5079941 := bbase (se 4 (by rfl) ⟨476244, by rfl⟩ : syracuseStep 5079941 = 952489) (by norm_num)
theorem B4285381 : Blo 1503572 4285381 := bbase (se 4 (by rfl) ⟨401754, by rfl⟩ : syracuseStep 4285381 = 803509) (by norm_num)
theorem B3384269 : Blo 1503572 3384269 := bbase (se 3 (by rfl) ⟨634550, by rfl⟩ : syracuseStep 3384269 = 1269101) (by norm_num)
theorem B54887381 : Blo 1503572 54887381 := bbase (se 7 (by rfl) ⟨643211, by rfl⟩ : syracuseStep 54887381 = 1286423) (by norm_num)
theorem B3212293 : Blo 1503572 3212293 := bbase (se 4 (by rfl) ⟨301152, by rfl⟩ : syracuseStep 3212293 = 602305) (by norm_num)
theorem B2032661 : Blo 1503572 2032661 := bbase (se 6 (by rfl) ⟨47640, by rfl⟩ : syracuseStep 2032661 = 95281) (by norm_num)
theorem B3384341 : Blo 1503572 3384341 := bbase (se 6 (by rfl) ⟨79320, by rfl⟩ : syracuseStep 3384341 = 158641) (by norm_num)
theorem B3810341 : Blo 1503572 3810341 := bbase (se 4 (by rfl) ⟨357219, by rfl⟩ : syracuseStep 3810341 = 714439) (by norm_num)
theorem B7619669 : Blo 1503572 7619669 := bbase (se 8 (by rfl) ⟨44646, by rfl⟩ : syracuseStep 7619669 = 89293) (by norm_num)
theorem B3384413 : Blo 1503572 3384413 := bbase (se 3 (by rfl) ⟨634577, by rfl⟩ : syracuseStep 3384413 = 1269155) (by norm_num)
theorem B4285541 : Blo 1503572 4285541 := bbase (se 4 (by rfl) ⟨401769, by rfl⟩ : syracuseStep 4285541 = 803539) (by norm_num)
theorem B2409605 : Blo 1503572 2409605 := bbase (se 4 (by rfl) ⟨225900, by rfl⟩ : syracuseStep 2409605 = 451801) (by norm_num)
theorem B3384485 : Blo 1503572 3384485 := bbase (se 4 (by rfl) ⟨317295, by rfl⟩ : syracuseStep 3384485 = 634591) (by norm_num)
theorem B1606873 : Blo 1503572 1606873 := bbase (se 2 (by rfl) ⟨602577, by rfl⟩ : syracuseStep 1606873 = 1205155) (by norm_num)
theorem B2172133 : Blo 1503572 2172133 := bbase (se 4 (by rfl) ⟨203637, by rfl⟩ : syracuseStep 2172133 = 407275) (by norm_num)
theorem B3384557 : Blo 1503572 3384557 := bbase (se 3 (by rfl) ⟨634604, by rfl⟩ : syracuseStep 3384557 = 1269209) (by norm_num)
theorem B5711093 : Blo 1503572 5711093 := bbase (se 5 (by rfl) ⟨267707, by rfl⟩ : syracuseStep 5711093 = 535415) (by norm_num)
theorem B1983745 : Blo 1503572 1983745 := bbase (se 2 (by rfl) ⟨743904, by rfl⟩ : syracuseStep 1983745 = 1487809) (by norm_num)
theorem B3048749 : Blo 1503572 3048749 := bbase (se 3 (by rfl) ⟨571640, by rfl⟩ : syracuseStep 3048749 = 1143281) (by norm_num)
theorem B3384629 : Blo 1503572 3384629 := bbase (se 5 (by rfl) ⟨158654, by rfl⟩ : syracuseStep 3384629 = 317309) (by norm_num)
theorem B5080373 : Blo 1503572 5080373 := bbase (se 5 (by rfl) ⟨238142, by rfl⟩ : syracuseStep 5080373 = 476285) (by norm_num)
theorem B2409797 : Blo 1503572 2409797 := bbase (se 4 (by rfl) ⟨225918, by rfl⟩ : syracuseStep 2409797 = 451837) (by norm_num)
theorem B1606997 : Blo 1503572 1606997 := bbase (se 12 (by rfl) ⟨588, by rfl⟩ : syracuseStep 1606997 = 1177) (by norm_num)
theorem B4285781 : Blo 1503572 4285781 := bbase (se 12 (by rfl) ⟨1569, by rfl⟩ : syracuseStep 4285781 = 3139) (by norm_num)
theorem B3212669 : Blo 1503572 3212669 := bbase (se 3 (by rfl) ⟨602375, by rfl⟩ : syracuseStep 3212669 = 1204751) (by norm_num)
theorem B3384701 : Blo 1503572 3384701 := bbase (se 3 (by rfl) ⟨634631, by rfl⟩ : syracuseStep 3384701 = 1269263) (by norm_num)
theorem B3048845 : Blo 1503572 3048845 := bbase (se 3 (by rfl) ⟨571658, by rfl⟩ : syracuseStep 3048845 = 1143317) (by norm_num)
theorem B1525169 : Blo 1503572 1525169 := bbase (se 2 (by rfl) ⟨571938, by rfl⟩ : syracuseStep 1525169 = 1143877) (by norm_num)
theorem B3384773 : Blo 1503572 3384773 := bbase (se 4 (by rfl) ⟨317322, by rfl⟩ : syracuseStep 3384773 = 634645) (by norm_num)
theorem B7611893 : Blo 1503572 7611893 := bbase (se 5 (by rfl) ⟨356807, by rfl⟩ : syracuseStep 7611893 = 713615) (by norm_num)
theorem B3384845 : Blo 1503572 3384845 := bbase (se 3 (by rfl) ⟨634658, by rfl⟩ : syracuseStep 3384845 = 1269317) (by norm_num)
theorem B5711381 : Blo 1503572 5711381 := bbase (se 6 (by rfl) ⟨133860, by rfl⟩ : syracuseStep 5711381 = 267721) (by norm_num)
theorem B4285973 : Blo 1503572 4285973 := bbase (se 6 (by rfl) ⟨100452, by rfl⟩ : syracuseStep 4285973 = 200905) (by norm_num)
theorem B1607249 : Blo 1503572 1607249 := bbase (se 2 (by rfl) ⟨602718, by rfl⟩ : syracuseStep 1607249 = 1205437) (by norm_num)
theorem B3384917 : Blo 1503572 3384917 := bbase (se 8 (by rfl) ⟨19833, by rfl⟩ : syracuseStep 3384917 = 39667) (by norm_num)
theorem B3384989 : Blo 1503572 3384989 := bbase (se 3 (by rfl) ⟨634685, by rfl⟩ : syracuseStep 3384989 = 1269371) (by norm_num)
theorem B3385061 : Blo 1503572 3385061 := bbase (se 4 (by rfl) ⟨317349, by rfl⟩ : syracuseStep 3385061 = 634699) (by norm_num)
theorem B5080805 : Blo 1503572 5080805 := bbase (se 4 (by rfl) ⟨476325, by rfl⟩ : syracuseStep 5080805 = 952651) (by norm_num)
theorem B3213037 : Blo 1503572 3213037 := bbase (se 3 (by rfl) ⟨602444, by rfl⟩ : syracuseStep 3213037 = 1204889) (by norm_num)
theorem B3385133 : Blo 1503572 3385133 := bbase (se 3 (by rfl) ⟨634712, by rfl⟩ : syracuseStep 3385133 = 1269425) (by norm_num)
theorem B117253973 : Blo 1503572 117253973 := bbase (se 9 (by rfl) ⟨343517, by rfl⟩ : syracuseStep 117253973 = 687035) (by norm_num)
theorem B3385205 : Blo 1503572 3385205 := bbase (se 5 (by rfl) ⟨158681, by rfl⟩ : syracuseStep 3385205 = 317363) (by norm_num)
theorem B5146517 : Blo 1503572 5146517 := bbase (se 6 (by rfl) ⟨120621, by rfl⟩ : syracuseStep 5146517 = 241243) (by norm_num)
theorem B3385277 : Blo 1503572 3385277 := bbase (se 3 (by rfl) ⟨634739, by rfl⟩ : syracuseStep 3385277 = 1269479) (by norm_num)
theorem B3049429 : Blo 1503572 3049429 := bbase (se 7 (by rfl) ⟨35735, by rfl⟩ : syracuseStep 3049429 = 71471) (by norm_num)
theorem B1525753 : Blo 1503572 1525753 := bbase (se 2 (by rfl) ⟨572157, by rfl⟩ : syracuseStep 1525753 = 1144315) (by norm_num)
theorem B3385349 : Blo 1503572 3385349 := bbase (se 4 (by rfl) ⟨317376, by rfl⟩ : syracuseStep 3385349 = 634753) (by norm_num)
theorem B23152661 : Blo 1503572 23152661 := bbase (se 6 (by rfl) ⟨542640, by rfl⟩ : syracuseStep 23152661 = 1085281) (by norm_num)
theorem B2287669 : Blo 1503572 2287669 := bbase (se 5 (by rfl) ⟨107234, by rfl⟩ : syracuseStep 2287669 = 214469) (by norm_num)
theorem B3385421 : Blo 1503572 3385421 := bbase (se 3 (by rfl) ⟨634766, by rfl⟩ : syracuseStep 3385421 = 1269533) (by norm_num)
theorem B3385493 : Blo 1503572 3385493 := bbase (se 6 (by rfl) ⟨79347, by rfl⟩ : syracuseStep 3385493 = 158695) (by norm_num)
theorem B4343989 : Blo 1503572 4343989 := bbase (se 5 (by rfl) ⟨203624, by rfl⟩ : syracuseStep 4343989 = 407249) (by norm_num)
theorem B3385565 : Blo 1503572 3385565 := bbase (se 3 (by rfl) ⟨634793, by rfl⟩ : syracuseStep 3385565 = 1269587) (by norm_num)
theorem B3385637 : Blo 1503572 3385637 := bbase (se 4 (by rfl) ⟨317403, by rfl⟩ : syracuseStep 3385637 = 634807) (by norm_num)
theorem B7227701 : Blo 1503572 7227701 := bbase (se 5 (by rfl) ⟨338798, by rfl⟩ : syracuseStep 7227701 = 677597) (by norm_num)
theorem B2034013 : Blo 1503572 2034013 := bbase (se 3 (by rfl) ⟨381377, by rfl⟩ : syracuseStep 2034013 = 762755) (by norm_num)
theorem B7620965 : Blo 1503572 7620965 := bbase (se 4 (by rfl) ⟨714465, by rfl⟩ : syracuseStep 7620965 = 1428931) (by norm_num)
theorem B3385709 : Blo 1503572 3385709 := bbase (se 3 (by rfl) ⟨634820, by rfl⟩ : syracuseStep 3385709 = 1269641) (by norm_num)
theorem B1903009 : Blo 1503572 1903009 := bbase (se 2 (by rfl) ⟨713628, by rfl⟩ : syracuseStep 1903009 = 1427257) (by norm_num)
theorem B3385781 : Blo 1503572 3385781 := bbase (se 5 (by rfl) ⟨158708, by rfl⟩ : syracuseStep 3385781 = 317417) (by norm_num)
theorem B5425589 : Blo 1503572 5425589 := bbase (se 5 (by rfl) ⟨254324, by rfl⟩ : syracuseStep 5425589 = 508649) (by norm_num)
theorem B3049949 : Blo 1503572 3049949 := bbase (se 3 (by rfl) ⟨571865, by rfl⟩ : syracuseStep 3049949 = 1143731) (by norm_num)
theorem B4286965 : Blo 1503572 4286965 := bbase (se 5 (by rfl) ⟨200951, by rfl⟩ : syracuseStep 4286965 = 401903) (by norm_num)
theorem B3385853 : Blo 1503572 3385853 := bbase (se 3 (by rfl) ⟨634847, by rfl⟩ : syracuseStep 3385853 = 1269695) (by norm_num)
theorem B1903105 : Blo 1503572 1903105 := bbase (se 2 (by rfl) ⟨713664, by rfl⟩ : syracuseStep 1903105 = 1427329) (by norm_num)
theorem B2255381 : Blo 1503572 2255381 := bbase (se 6 (by rfl) ⟨52860, by rfl⟩ : syracuseStep 2255381 = 105721) (by norm_num)
theorem B5147173 : Blo 1503572 5147173 := bbase (se 4 (by rfl) ⟨482547, by rfl⟩ : syracuseStep 5147173 = 965095) (by norm_num)
theorem B2255405 : Blo 1503572 2255405 := bbase (se 3 (by rfl) ⟨422888, by rfl⟩ : syracuseStep 2255405 = 845777) (by norm_num)
theorem B2034229 : Blo 1503572 2034229 := bbase (se 5 (by rfl) ⟨95354, by rfl⟩ : syracuseStep 2034229 = 190709) (by norm_num)
theorem B2255429 : Blo 1503572 2255429 := bbase (se 4 (by rfl) ⟨211446, by rfl⟩ : syracuseStep 2255429 = 422893) (by norm_num)
theorem B3385925 : Blo 1503572 3385925 := bbase (se 4 (by rfl) ⟨317430, by rfl⟩ : syracuseStep 3385925 = 634861) (by norm_num)
theorem B2255453 : Blo 1503572 2255453 := bbase (se 3 (by rfl) ⟨422897, by rfl⟩ : syracuseStep 2255453 = 845795) (by norm_num)
theorem B2411117 : Blo 1503572 2411117 := bbase (se 3 (by rfl) ⟨452084, by rfl⟩ : syracuseStep 2411117 = 904169) (by norm_num)
theorem B2255477 : Blo 1503572 2255477 := bbase (se 5 (by rfl) ⟨105725, by rfl⟩ : syracuseStep 2255477 = 211451) (by norm_num)
theorem B2255501 : Blo 1503572 2255501 := bbase (se 3 (by rfl) ⟨422906, by rfl⟩ : syracuseStep 2255501 = 845813) (by norm_num)
theorem B3385997 : Blo 1503572 3385997 := bbase (se 3 (by rfl) ⟨634874, by rfl⟩ : syracuseStep 3385997 = 1269749) (by norm_num)
theorem B2255525 : Blo 1503572 2255525 := bbase (se 4 (by rfl) ⟨211455, by rfl⟩ : syracuseStep 2255525 = 422911) (by norm_num)
theorem B1903277 : Blo 1503572 1903277 := bbase (se 3 (by rfl) ⟨356864, by rfl⟩ : syracuseStep 1903277 = 713729) (by norm_num)
theorem B5712565 : Blo 1503572 5712565 := bbase (se 5 (by rfl) ⟨267776, by rfl⟩ : syracuseStep 5712565 = 535553) (by norm_num)
theorem B2255549 : Blo 1503572 2255549 := bbase (se 3 (by rfl) ⟨422915, by rfl⟩ : syracuseStep 2255549 = 845831) (by norm_num)
theorem B2411213 : Blo 1503572 2411213 := bbase (se 3 (by rfl) ⟨452102, by rfl⟩ : syracuseStep 2411213 = 904205) (by norm_num)
theorem B2255573 : Blo 1503572 2255573 := bbase (se 7 (by rfl) ⟨26432, by rfl⟩ : syracuseStep 2255573 = 52865) (by norm_num)
theorem B3615445 : Blo 1503572 3615445 := bbase (se 7 (by rfl) ⟨42368, by rfl⟩ : syracuseStep 3615445 = 84737) (by norm_num)
theorem B3386069 : Blo 1503572 3386069 := bbase (se 7 (by rfl) ⟨39680, by rfl⟩ : syracuseStep 3386069 = 79361) (by norm_num)
theorem B1903333 : Blo 1503572 1903333 := bbase (se 4 (by rfl) ⟨178437, by rfl⟩ : syracuseStep 1903333 = 356875) (by norm_num)
theorem B2255597 : Blo 1503572 2255597 := bbase (se 3 (by rfl) ⟨422924, by rfl⟩ : syracuseStep 2255597 = 845849) (by norm_num)
theorem B2411245 : Blo 1503572 2411245 := bbase (se 3 (by rfl) ⟨452108, by rfl⟩ : syracuseStep 2411245 = 904217) (by norm_num)
theorem B2255621 : Blo 1503572 2255621 := bbase (se 4 (by rfl) ⟨211464, by rfl⟩ : syracuseStep 2255621 = 422929) (by norm_num)
theorem B7613189 : Blo 1503572 7613189 := bbase (se 4 (by rfl) ⟨713736, by rfl⟩ : syracuseStep 7613189 = 1427473) (by norm_num)
theorem B2255645 : Blo 1503572 2255645 := bbase (se 3 (by rfl) ⟨422933, by rfl⟩ : syracuseStep 2255645 = 845867) (by norm_num)
theorem B3386141 : Blo 1503572 3386141 := bbase (se 3 (by rfl) ⟨634901, by rfl⟩ : syracuseStep 3386141 = 1269803) (by norm_num)
theorem B2255669 : Blo 1503572 2255669 := bbase (se 5 (by rfl) ⟨105734, by rfl⟩ : syracuseStep 2255669 = 211469) (by norm_num)
theorem B1903429 : Blo 1503572 1903429 := bbase (se 4 (by rfl) ⟨178446, by rfl⟩ : syracuseStep 1903429 = 356893) (by norm_num)
theorem B2141005 : Blo 1503572 2141005 := bbase (se 3 (by rfl) ⟨401438, by rfl⟩ : syracuseStep 2141005 = 802877) (by norm_num)
theorem B2255693 : Blo 1503572 2255693 := bbase (se 3 (by rfl) ⟨422942, by rfl⟩ : syracuseStep 2255693 = 845885) (by norm_num)
theorem B2255717 : Blo 1503572 2255717 := bbase (se 4 (by rfl) ⟨211473, by rfl⟩ : syracuseStep 2255717 = 422947) (by norm_num)
theorem B3386213 : Blo 1503572 3386213 := bbase (se 4 (by rfl) ⟨317457, by rfl⟩ : syracuseStep 3386213 = 634915) (by norm_num)
theorem B2255741 : Blo 1503572 2255741 := bbase (se 3 (by rfl) ⟨422951, by rfl⟩ : syracuseStep 2255741 = 845903) (by norm_num)
theorem B2255765 : Blo 1503572 2255765 := bbase (se 6 (by rfl) ⟨52869, by rfl⟩ : syracuseStep 2255765 = 105739) (by norm_num)
theorem B2255789 : Blo 1503572 2255789 := bbase (se 3 (by rfl) ⟨422960, by rfl⟩ : syracuseStep 2255789 = 845921) (by norm_num)
theorem B3386285 : Blo 1503572 3386285 := bbase (se 3 (by rfl) ⟨634928, by rfl⟩ : syracuseStep 3386285 = 1269857) (by norm_num)
theorem B2255813 : Blo 1503572 2255813 := bbase (se 4 (by rfl) ⟨211482, by rfl⟩ : syracuseStep 2255813 = 422965) (by norm_num)
theorem B2255837 : Blo 1503572 2255837 := bbase (se 3 (by rfl) ⟨422969, by rfl⟩ : syracuseStep 2255837 = 845939) (by norm_num)
theorem B5712869 : Blo 1503572 5712869 := bbase (se 4 (by rfl) ⟨535581, by rfl⟩ : syracuseStep 5712869 = 1071163) (by norm_num)
theorem B1903601 : Blo 1503572 1903601 := bbase (se 2 (by rfl) ⟨713850, by rfl⟩ : syracuseStep 1903601 = 1427701) (by norm_num)
theorem B2255861 : Blo 1503572 2255861 := bbase (se 5 (by rfl) ⟨105743, by rfl⟩ : syracuseStep 2255861 = 211487) (by norm_num)
theorem B3386357 : Blo 1503572 3386357 := bbase (se 5 (by rfl) ⟨158735, by rfl⟩ : syracuseStep 3386357 = 317471) (by norm_num)
theorem B2255885 : Blo 1503572 2255885 := bbase (se 3 (by rfl) ⟨422978, by rfl⟩ : syracuseStep 2255885 = 845957) (by norm_num)
theorem B2255909 : Blo 1503572 2255909 := bbase (se 4 (by rfl) ⟨211491, by rfl⟩ : syracuseStep 2255909 = 422983) (by norm_num)
theorem B1903657 : Blo 1503572 1903657 := bbase (se 2 (by rfl) ⟨713871, by rfl⟩ : syracuseStep 1903657 = 1427743) (by norm_num)
theorem B2255933 : Blo 1503572 2255933 := bbase (se 3 (by rfl) ⟨422987, by rfl⟩ : syracuseStep 2255933 = 845975) (by norm_num)
theorem B3386429 : Blo 1503572 3386429 := bbase (se 3 (by rfl) ⟨634955, by rfl⟩ : syracuseStep 3386429 = 1269911) (by norm_num)
theorem B2255957 : Blo 1503572 2255957 := bbase (se 8 (by rfl) ⟨13218, by rfl⟩ : syracuseStep 2255957 = 26437) (by norm_num)
theorem B3050597 : Blo 1503572 3050597 := bbase (se 4 (by rfl) ⟨285993, by rfl⟩ : syracuseStep 3050597 = 571987) (by norm_num)
theorem B2255981 : Blo 1503572 2255981 := bbase (se 3 (by rfl) ⟨422996, by rfl⟩ : syracuseStep 2255981 = 845993) (by norm_num)
theorem B8244341 : Blo 1503572 8244341 := bbase (se 5 (by rfl) ⟨386453, by rfl⟩ : syracuseStep 8244341 = 772907) (by norm_num)
theorem B2256005 : Blo 1503572 2256005 := bbase (se 4 (by rfl) ⟨211500, by rfl⟩ : syracuseStep 2256005 = 423001) (by norm_num)
theorem B3386501 : Blo 1503572 3386501 := bbase (se 4 (by rfl) ⟨317484, by rfl⟩ : syracuseStep 3386501 = 634969) (by norm_num)
theorem B1903753 : Blo 1503572 1903753 := bbase (se 2 (by rfl) ⟨713907, by rfl⟩ : syracuseStep 1903753 = 1427815) (by norm_num)
theorem B1715341 : Blo 1503572 1715341 := bbase (se 3 (by rfl) ⟨321626, by rfl⟩ : syracuseStep 1715341 = 643253) (by norm_num)
theorem B2256029 : Blo 1503572 2256029 := bbase (se 3 (by rfl) ⟨423005, by rfl⟩ : syracuseStep 2256029 = 846011) (by norm_num)
theorem B1715377 : Blo 1503572 1715377 := bbase (se 2 (by rfl) ⟨643266, by rfl⟩ : syracuseStep 1715377 = 1286533) (by norm_num)
theorem B2256053 : Blo 1503572 2256053 := bbase (se 5 (by rfl) ⟨105752, by rfl⟩ : syracuseStep 2256053 = 211505) (by norm_num)
theorem B2256077 : Blo 1503572 2256077 := bbase (se 3 (by rfl) ⟨423014, by rfl⟩ : syracuseStep 2256077 = 846029) (by norm_num)
theorem B3214541 : Blo 1503572 3214541 := bbase (se 3 (by rfl) ⟨602726, by rfl⟩ : syracuseStep 3214541 = 1205453) (by norm_num)
theorem B3386573 : Blo 1503572 3386573 := bbase (se 3 (by rfl) ⟨634982, by rfl⟩ : syracuseStep 3386573 = 1269965) (by norm_num)
theorem B2256101 : Blo 1503572 2256101 := bbase (se 4 (by rfl) ⟨211509, by rfl⟩ : syracuseStep 2256101 = 423019) (by norm_num)
theorem B2256125 : Blo 1503572 2256125 := bbase (se 3 (by rfl) ⟨423023, by rfl⟩ : syracuseStep 2256125 = 846047) (by norm_num)
theorem B2256149 : Blo 1503572 2256149 := bbase (se 6 (by rfl) ⟨52878, by rfl⟩ : syracuseStep 2256149 = 105757) (by norm_num)
theorem B3386645 : Blo 1503572 3386645 := bbase (se 6 (by rfl) ⟨79374, by rfl⟩ : syracuseStep 3386645 = 158749) (by norm_num)
theorem B2256173 : Blo 1503572 2256173 := bbase (se 3 (by rfl) ⟨423032, by rfl⟩ : syracuseStep 2256173 = 846065) (by norm_num)
theorem B1903925 : Blo 1503572 1903925 := bbase (se 5 (by rfl) ⟨89246, by rfl⟩ : syracuseStep 1903925 = 178493) (by norm_num)
theorem B2256197 : Blo 1503572 2256197 := bbase (se 4 (by rfl) ⟨211518, by rfl⟩ : syracuseStep 2256197 = 423037) (by norm_num)
theorem B2256221 : Blo 1503572 2256221 := bbase (se 3 (by rfl) ⟨423041, by rfl⟩ : syracuseStep 2256221 = 846083) (by norm_num)
theorem B3214685 : Blo 1503572 3214685 := bbase (se 3 (by rfl) ⟨602753, by rfl⟩ : syracuseStep 3214685 = 1205507) (by norm_num)
theorem B3386717 : Blo 1503572 3386717 := bbase (se 3 (by rfl) ⟨635009, by rfl⟩ : syracuseStep 3386717 = 1270019) (by norm_num)
theorem B1903981 : Blo 1503572 1903981 := bbase (se 3 (by rfl) ⟨356996, by rfl⟩ : syracuseStep 1903981 = 713993) (by norm_num)
theorem B2256245 : Blo 1503572 2256245 := bbase (se 5 (by rfl) ⟨105761, by rfl⟩ : syracuseStep 2256245 = 211523) (by norm_num)
theorem B2256269 : Blo 1503572 2256269 := bbase (se 3 (by rfl) ⟨423050, by rfl⟩ : syracuseStep 2256269 = 846101) (by norm_num)
theorem B2141597 : Blo 1503572 2141597 := bbase (se 3 (by rfl) ⟨401549, by rfl⟩ : syracuseStep 2141597 = 803099) (by norm_num)
theorem B2256293 : Blo 1503572 2256293 := bbase (se 4 (by rfl) ⟨211527, by rfl⟩ : syracuseStep 2256293 = 423055) (by norm_num)
theorem B3386789 : Blo 1503572 3386789 := bbase (se 4 (by rfl) ⟨317511, by rfl⟩ : syracuseStep 3386789 = 635023) (by norm_num)
theorem B2256317 : Blo 1503572 2256317 := bbase (se 3 (by rfl) ⟨423059, by rfl⟩ : syracuseStep 2256317 = 846119) (by norm_num)
theorem B1904077 : Blo 1503572 1904077 := bbase (se 3 (by rfl) ⟨357014, by rfl⟩ : syracuseStep 1904077 = 714029) (by norm_num)
theorem B2256341 : Blo 1503572 2256341 := bbase (se 7 (by rfl) ⟨26441, by rfl⟩ : syracuseStep 2256341 = 52883) (by norm_num)
theorem B2141677 : Blo 1503572 2141677 := bbase (se 3 (by rfl) ⟨401564, by rfl⟩ : syracuseStep 2141677 = 803129) (by norm_num)
theorem B2256365 : Blo 1503572 2256365 := bbase (se 3 (by rfl) ⟨423068, by rfl⟩ : syracuseStep 2256365 = 846137) (by norm_num)
theorem B3386861 : Blo 1503572 3386861 := bbase (se 3 (by rfl) ⟨635036, by rfl⟩ : syracuseStep 3386861 = 1270073) (by norm_num)
theorem B2747893 : Blo 1503572 2747893 := bbase (se 5 (by rfl) ⟨128807, by rfl⟩ : syracuseStep 2747893 = 257615) (by norm_num)
theorem B2256389 : Blo 1503572 2256389 := bbase (se 4 (by rfl) ⟨211536, by rfl⟩ : syracuseStep 2256389 = 423073) (by norm_num)
theorem B2256413 : Blo 1503572 2256413 := bbase (se 3 (by rfl) ⟨423077, by rfl⟩ : syracuseStep 2256413 = 846155) (by norm_num)
theorem B2854453 : Blo 1503572 2854453 := bbase (se 5 (by rfl) ⟨133802, by rfl⟩ : syracuseStep 2854453 = 267605) (by norm_num)
theorem B2256437 : Blo 1503572 2256437 := bbase (se 5 (by rfl) ⟨105770, by rfl⟩ : syracuseStep 2256437 = 211541) (by norm_num)
theorem B3386933 : Blo 1503572 3386933 := bbase (se 5 (by rfl) ⟨158762, by rfl⟩ : syracuseStep 3386933 = 317525) (by norm_num)
theorem B6098501 : Blo 1503572 6098501 := bbase (se 4 (by rfl) ⟨571734, by rfl⟩ : syracuseStep 6098501 = 1143469) (by norm_num)
theorem B2256461 : Blo 1503572 2256461 := bbase (se 3 (by rfl) ⟨423086, by rfl⟩ : syracuseStep 2256461 = 846173) (by norm_num)
theorem B14462549 : Blo 1503572 14462549 := bbase (se 8 (by rfl) ⟨84741, by rfl⟩ : syracuseStep 14462549 = 169483) (by norm_num)
theorem B2141797 : Blo 1503572 2141797 := bbase (se 4 (by rfl) ⟨200793, by rfl⟩ : syracuseStep 2141797 = 401587) (by norm_num)
theorem B2256485 : Blo 1503572 2256485 := bbase (se 4 (by rfl) ⟨211545, by rfl⟩ : syracuseStep 2256485 = 423091) (by norm_num)
theorem B1904249 : Blo 1503572 1904249 := bbase (se 2 (by rfl) ⟨714093, by rfl⟩ : syracuseStep 1904249 = 1428187) (by norm_num)
theorem B2256509 : Blo 1503572 2256509 := bbase (se 3 (by rfl) ⟨423095, by rfl⟩ : syracuseStep 2256509 = 846191) (by norm_num)
theorem B3387005 : Blo 1503572 3387005 := bbase (se 3 (by rfl) ⟨635063, by rfl⟩ : syracuseStep 3387005 = 1270127) (by norm_num)
theorem B2256533 : Blo 1503572 2256533 := bbase (se 6 (by rfl) ⟨52887, by rfl⟩ : syracuseStep 2256533 = 105775) (by norm_num)
theorem B3051173 : Blo 1503572 3051173 := bbase (se 4 (by rfl) ⟨286047, by rfl⟩ : syracuseStep 3051173 = 572095) (by norm_num)
theorem B2256557 : Blo 1503572 2256557 := bbase (se 3 (by rfl) ⟨423104, by rfl⟩ : syracuseStep 2256557 = 846209) (by norm_num)
theorem B1904305 : Blo 1503572 1904305 := bbase (se 2 (by rfl) ⟨714114, by rfl⟩ : syracuseStep 1904305 = 1428229) (by norm_num)
theorem B9645749 : Blo 1503572 9645749 := bbase (se 5 (by rfl) ⟨452144, by rfl⟩ : syracuseStep 9645749 = 904289) (by norm_num)
theorem B2854597 : Blo 1503572 2854597 := bbase (se 4 (by rfl) ⟨267618, by rfl⟩ : syracuseStep 2854597 = 535237) (by norm_num)
theorem B2141893 : Blo 1503572 2141893 := bbase (se 4 (by rfl) ⟨200802, by rfl⟩ : syracuseStep 2141893 = 401605) (by norm_num)
theorem B2256581 : Blo 1503572 2256581 := bbase (se 4 (by rfl) ⟨211554, by rfl⟩ : syracuseStep 2256581 = 423109) (by norm_num)
theorem B3215045 : Blo 1503572 3215045 := bbase (se 4 (by rfl) ⟨301410, by rfl⟩ : syracuseStep 3215045 = 602821) (by norm_num)
theorem B3387077 : Blo 1503572 3387077 := bbase (se 4 (by rfl) ⟨317538, by rfl⟩ : syracuseStep 3387077 = 635077) (by norm_num)
theorem B2256605 : Blo 1503572 2256605 := bbase (se 3 (by rfl) ⟨423113, by rfl⟩ : syracuseStep 2256605 = 846227) (by norm_num)
theorem B2256629 : Blo 1503572 2256629 := bbase (se 5 (by rfl) ⟨105779, by rfl⟩ : syracuseStep 2256629 = 211559) (by norm_num)
theorem B2256653 : Blo 1503572 2256653 := bbase (se 3 (by rfl) ⟨423122, by rfl⟩ : syracuseStep 2256653 = 846245) (by norm_num)
theorem B1904401 : Blo 1503572 1904401 := bbase (se 2 (by rfl) ⟨714150, by rfl⟩ : syracuseStep 1904401 = 1428301) (by norm_num)
theorem B3387149 : Blo 1503572 3387149 := bbase (se 3 (by rfl) ⟨635090, by rfl⟩ : syracuseStep 3387149 = 1270181) (by norm_num)
theorem B2256677 : Blo 1503572 2256677 := bbase (se 4 (by rfl) ⟨211563, by rfl⟩ : syracuseStep 2256677 = 423127) (by norm_num)
theorem B2608949 : Blo 1503572 2608949 := bbase (se 5 (by rfl) ⟨122294, by rfl⟩ : syracuseStep 2608949 = 244589) (by norm_num)
theorem B2256701 : Blo 1503572 2256701 := bbase (se 3 (by rfl) ⟨423131, by rfl⟩ : syracuseStep 2256701 = 846263) (by norm_num)
theorem B5074757 : Blo 1503572 5074757 := bbase (se 4 (by rfl) ⟨475758, by rfl⟩ : syracuseStep 5074757 = 951517) (by norm_num)
theorem B2256725 : Blo 1503572 2256725 := bbase (se 9 (by rfl) ⟨6611, by rfl⟩ : syracuseStep 2256725 = 13223) (by norm_num)
theorem B3387221 : Blo 1503572 3387221 := bbase (se 9 (by rfl) ⟨9923, by rfl⟩ : syracuseStep 3387221 = 19847) (by norm_num)
theorem B2854757 : Blo 1503572 2854757 := bbase (se 4 (by rfl) ⟨267633, by rfl⟩ : syracuseStep 2854757 = 535267) (by norm_num)
theorem B2256749 : Blo 1503572 2256749 := bbase (se 3 (by rfl) ⟨423140, by rfl⟩ : syracuseStep 2256749 = 846281) (by norm_num)
theorem B6426485 : Blo 1503572 6426485 := bbase (se 5 (by rfl) ⟨301241, by rfl⟩ : syracuseStep 6426485 = 602483) (by norm_num)
theorem B2256773 : Blo 1503572 2256773 := bbase (se 4 (by rfl) ⟨211572, by rfl⟩ : syracuseStep 2256773 = 423145) (by norm_num)
theorem B12857237 : Blo 1503572 12857237 := bbase (se 6 (by rfl) ⟨301341, by rfl⟩ : syracuseStep 12857237 = 602683) (by norm_num)
theorem B1691545 : Blo 1503572 1691545 := bbase (se 2 (by rfl) ⟨634329, by rfl⟩ : syracuseStep 1691545 = 1268659) (by norm_num)
theorem B2256797 : Blo 1503572 2256797 := bbase (se 3 (by rfl) ⟨423149, by rfl⟩ : syracuseStep 2256797 = 846299) (by norm_num)
theorem B2256821 : Blo 1503572 2256821 := bbase (se 5 (by rfl) ⟨105788, by rfl⟩ : syracuseStep 2256821 = 211577) (by norm_num)
theorem B1691581 : Blo 1503572 1691581 := bbase (se 3 (by rfl) ⟨317171, by rfl⟩ : syracuseStep 1691581 = 634343) (by norm_num)
theorem B1904573 : Blo 1503572 1904573 := bbase (se 3 (by rfl) ⟨357107, by rfl⟩ : syracuseStep 1904573 = 714215) (by norm_num)
theorem B2256845 : Blo 1503572 2256845 := bbase (se 3 (by rfl) ⟨423158, by rfl⟩ : syracuseStep 2256845 = 846317) (by norm_num)
theorem B1691617 : Blo 1503572 1691617 := bbase (se 2 (by rfl) ⟨634356, by rfl⟩ : syracuseStep 1691617 = 1268713) (by norm_num)
theorem B2256869 : Blo 1503572 2256869 := bbase (se 4 (by rfl) ⟨211581, by rfl⟩ : syracuseStep 2256869 = 423163) (by norm_num)
theorem B1929205 : Blo 1503572 1929205 := bbase (se 5 (by rfl) ⟨90431, by rfl⟩ : syracuseStep 1929205 = 180863) (by norm_num)
theorem B2854901 : Blo 1503572 2854901 := bbase (se 5 (by rfl) ⟨133823, by rfl⟩ : syracuseStep 2854901 = 267647) (by norm_num)
theorem B1904629 : Blo 1503572 1904629 := bbase (se 5 (by rfl) ⟨89279, by rfl⟩ : syracuseStep 1904629 = 178559) (by norm_num)
theorem B2256893 : Blo 1503572 2256893 := bbase (se 3 (by rfl) ⟨423167, by rfl⟩ : syracuseStep 2256893 = 846335) (by norm_num)
theorem B1691653 : Blo 1503572 1691653 := bbase (se 4 (by rfl) ⟨158592, by rfl⟩ : syracuseStep 1691653 = 317185) (by norm_num)
theorem B7614485 : Blo 1503572 7614485 := bbase (se 6 (by rfl) ⟨178464, by rfl⟩ : syracuseStep 7614485 = 356929) (by norm_num)
theorem B2256917 : Blo 1503572 2256917 := bbase (se 6 (by rfl) ⟨52896, by rfl⟩ : syracuseStep 2256917 = 105793) (by norm_num)
theorem B8572949 : Blo 1503572 8572949 := bbase (se 6 (by rfl) ⟨200928, by rfl⟩ : syracuseStep 8572949 = 401857) (by norm_num)
theorem B4821029 : Blo 1503572 4821029 := bbase (se 4 (by rfl) ⟨451971, by rfl⟩ : syracuseStep 4821029 = 903943) (by norm_num)
theorem B1691689 : Blo 1503572 1691689 := bbase (se 2 (by rfl) ⟨634383, by rfl⟩ : syracuseStep 1691689 = 1268767) (by norm_num)
theorem B2256941 : Blo 1503572 2256941 := bbase (se 3 (by rfl) ⟨423176, by rfl⟩ : syracuseStep 2256941 = 846353) (by norm_num)
theorem B3616829 : Blo 1503572 3616829 := bbase (se 3 (by rfl) ⟨678155, by rfl⟩ : syracuseStep 3616829 = 1356311) (by norm_num)
theorem B2256965 : Blo 1503572 2256965 := bbase (se 4 (by rfl) ⟨211590, by rfl⟩ : syracuseStep 2256965 = 423181) (by norm_num)
theorem B1691725 : Blo 1503572 1691725 := bbase (se 3 (by rfl) ⟨317198, by rfl⟩ : syracuseStep 1691725 = 634397) (by norm_num)
theorem B7721045 : Blo 1503572 7721045 := bbase (se 8 (by rfl) ⟨45240, by rfl⟩ : syracuseStep 7721045 = 90481) (by norm_num)
theorem B1904725 : Blo 1503572 1904725 := bbase (se 8 (by rfl) ⟨11160, by rfl⟩ : syracuseStep 1904725 = 22321) (by norm_num)
theorem B2256989 : Blo 1503572 2256989 := bbase (se 3 (by rfl) ⟨423185, by rfl⟩ : syracuseStep 2256989 = 846371) (by norm_num)
theorem B1691761 : Blo 1503572 1691761 := bbase (se 2 (by rfl) ⟨634410, by rfl⟩ : syracuseStep 1691761 = 1268821) (by norm_num)
theorem B2257013 : Blo 1503572 2257013 := bbase (se 5 (by rfl) ⟨105797, by rfl⟩ : syracuseStep 2257013 = 211595) (by norm_num)
theorem B2257037 : Blo 1503572 2257037 := bbase (se 3 (by rfl) ⟨423194, by rfl⟩ : syracuseStep 2257037 = 846389) (by norm_num)
theorem B1691797 : Blo 1503572 1691797 := bbase (se 6 (by rfl) ⟨39651, by rfl⟩ : syracuseStep 1691797 = 79303) (by norm_num)
theorem B8564885 : Blo 1503572 8564885 := bbase (se 6 (by rfl) ⟨200739, by rfl⟩ : syracuseStep 8564885 = 401479) (by norm_num)
theorem B6426773 : Blo 1503572 6426773 := bbase (se 6 (by rfl) ⟨150627, by rfl⟩ : syracuseStep 6426773 = 301255) (by norm_num)
theorem B2257061 : Blo 1503572 2257061 := bbase (se 4 (by rfl) ⟨211599, by rfl⟩ : syracuseStep 2257061 = 423199) (by norm_num)
theorem B2142389 : Blo 1503572 2142389 := bbase (se 5 (by rfl) ⟨100424, by rfl⟩ : syracuseStep 2142389 = 200849) (by norm_num)
theorem B1691833 : Blo 1503572 1691833 := bbase (se 2 (by rfl) ⟨634437, by rfl⟩ : syracuseStep 1691833 = 1268875) (by norm_num)
theorem B2257085 : Blo 1503572 2257085 := bbase (se 3 (by rfl) ⟨423203, by rfl⟩ : syracuseStep 2257085 = 846407) (by norm_num)
theorem B2257109 : Blo 1503572 2257109 := bbase (se 7 (by rfl) ⟨26450, by rfl⟩ : syracuseStep 2257109 = 52901) (by norm_num)
theorem B1691869 : Blo 1503572 1691869 := bbase (se 3 (by rfl) ⟨317225, by rfl⟩ : syracuseStep 1691869 = 634451) (by norm_num)
theorem B1716445 : Blo 1503572 1716445 := bbase (se 3 (by rfl) ⟨321833, by rfl⟩ : syracuseStep 1716445 = 643667) (by norm_num)
theorem B1806565 : Blo 1503572 1806565 := bbase (se 4 (by rfl) ⟨169365, by rfl⟩ : syracuseStep 1806565 = 338731) (by norm_num)
theorem B2257133 : Blo 1503572 2257133 := bbase (se 3 (by rfl) ⟨423212, by rfl⟩ : syracuseStep 2257133 = 846425) (by norm_num)
theorem B5075189 : Blo 1503572 5075189 := bbase (se 5 (by rfl) ⟨237899, by rfl⟩ : syracuseStep 5075189 = 475799) (by norm_num)
theorem B3617021 : Blo 1503572 3617021 := bbase (se 3 (by rfl) ⟨678191, by rfl⟩ : syracuseStep 3617021 = 1356383) (by norm_num)
theorem B1691905 : Blo 1503572 1691905 := bbase (se 2 (by rfl) ⟨634464, by rfl⟩ : syracuseStep 1691905 = 1268929) (by norm_num)
theorem B1904897 : Blo 1503572 1904897 := bbase (se 2 (by rfl) ⟨714336, by rfl⟩ : syracuseStep 1904897 = 1428673) (by norm_num)
theorem B2257157 : Blo 1503572 2257157 := bbase (se 4 (by rfl) ⟨211608, by rfl⟩ : syracuseStep 2257157 = 423217) (by norm_num)
theorem B2855189 : Blo 1503572 2855189 := bbase (se 6 (by rfl) ⟨66918, by rfl⟩ : syracuseStep 2855189 = 133837) (by norm_num)
theorem B2257181 : Blo 1503572 2257181 := bbase (se 3 (by rfl) ⟨423221, by rfl⟩ : syracuseStep 2257181 = 846443) (by norm_num)
theorem B1691941 : Blo 1503572 1691941 := bbase (se 4 (by rfl) ⟨158619, by rfl⟩ : syracuseStep 1691941 = 317239) (by norm_num)
theorem B2257205 : Blo 1503572 2257205 := bbase (se 5 (by rfl) ⟨105806, by rfl⟩ : syracuseStep 2257205 = 211613) (by norm_num)
theorem B1904953 : Blo 1503572 1904953 := bbase (se 2 (by rfl) ⟨714357, by rfl⟩ : syracuseStep 1904953 = 1428715) (by norm_num)
theorem B1691977 : Blo 1503572 1691977 := bbase (se 2 (by rfl) ⟨634491, by rfl⟩ : syracuseStep 1691977 = 1268983) (by norm_num)
theorem B2257229 : Blo 1503572 2257229 := bbase (se 3 (by rfl) ⟨423230, by rfl⟩ : syracuseStep 2257229 = 846461) (by norm_num)
theorem B2257253 : Blo 1503572 2257253 := bbase (se 4 (by rfl) ⟨211617, by rfl⟩ : syracuseStep 2257253 = 423235) (by norm_num)
theorem B1692013 : Blo 1503572 1692013 := bbase (se 3 (by rfl) ⟨317252, by rfl⟩ : syracuseStep 1692013 = 634505) (by norm_num)
theorem B12374389 : Blo 1503572 12374389 := bbase (se 5 (by rfl) ⟨580049, by rfl⟩ : syracuseStep 12374389 = 1160099) (by norm_num)
theorem B2257277 : Blo 1503572 2257277 := bbase (se 3 (by rfl) ⟨423239, by rfl⟩ : syracuseStep 2257277 = 846479) (by norm_num)
theorem B1806733 : Blo 1503572 1806733 := bbase (se 3 (by rfl) ⟨338762, by rfl⟩ : syracuseStep 1806733 = 677525) (by norm_num)
theorem B1692049 : Blo 1503572 1692049 := bbase (se 2 (by rfl) ⟨634518, by rfl⟩ : syracuseStep 1692049 = 1269037) (by norm_num)
theorem B2257301 : Blo 1503572 2257301 := bbase (se 6 (by rfl) ⟨52905, by rfl⟩ : syracuseStep 2257301 = 105811) (by norm_num)
theorem B1905049 : Blo 1503572 1905049 := bbase (se 2 (by rfl) ⟨714393, by rfl⟩ : syracuseStep 1905049 = 1428787) (by norm_num)
theorem B2855341 : Blo 1503572 2855341 := bbase (se 3 (by rfl) ⟨535376, by rfl⟩ : syracuseStep 2855341 = 1070753) (by norm_num)
theorem B2257325 : Blo 1503572 2257325 := bbase (se 3 (by rfl) ⟨423248, by rfl⟩ : syracuseStep 2257325 = 846497) (by norm_num)
theorem B1692085 : Blo 1503572 1692085 := bbase (se 5 (by rfl) ⟨79316, by rfl⟩ : syracuseStep 1692085 = 158633) (by norm_num)
theorem B1806781 : Blo 1503572 1806781 := bbase (se 3 (by rfl) ⟨338771, by rfl⟩ : syracuseStep 1806781 = 677543) (by norm_num)
theorem B2257349 : Blo 1503572 2257349 := bbase (se 4 (by rfl) ⟨211626, by rfl⟩ : syracuseStep 2257349 = 423253) (by norm_num)
theorem B5419477 : Blo 1503572 5419477 := bbase (se 7 (by rfl) ⟨63509, by rfl⟩ : syracuseStep 5419477 = 127019) (by norm_num)
theorem B1692121 : Blo 1503572 1692121 := bbase (se 2 (by rfl) ⟨634545, by rfl⟩ : syracuseStep 1692121 = 1269091) (by norm_num)
theorem B2257373 : Blo 1503572 2257373 := bbase (se 3 (by rfl) ⟨423257, by rfl⟩ : syracuseStep 2257373 = 846515) (by norm_num)
theorem B2257397 : Blo 1503572 2257397 := bbase (se 5 (by rfl) ⟨105815, by rfl⟩ : syracuseStep 2257397 = 211631) (by norm_num)
theorem B1692157 : Blo 1503572 1692157 := bbase (se 3 (by rfl) ⟨317279, by rfl⟩ : syracuseStep 1692157 = 634559) (by norm_num)
theorem B2257421 : Blo 1503572 2257421 := bbase (se 3 (by rfl) ⟨423266, by rfl⟩ : syracuseStep 2257421 = 846533) (by norm_num)
theorem B2060821 : Blo 1503572 2060821 := bbase (se 6 (by rfl) ⟨48300, by rfl⟩ : syracuseStep 2060821 = 96601) (by norm_num)
theorem B1806877 : Blo 1503572 1806877 := bbase (se 3 (by rfl) ⟨338789, by rfl⟩ : syracuseStep 1806877 = 677579) (by norm_num)
theorem B1692193 : Blo 1503572 1692193 := bbase (se 2 (by rfl) ⟨634572, by rfl⟩ : syracuseStep 1692193 = 1269145) (by norm_num)
theorem B2257445 : Blo 1503572 2257445 := bbase (se 4 (by rfl) ⟨211635, by rfl⟩ : syracuseStep 2257445 = 423271) (by norm_num)
theorem B2257469 : Blo 1503572 2257469 := bbase (se 3 (by rfl) ⟨423275, by rfl⟩ : syracuseStep 2257469 = 846551) (by norm_num)
theorem B1692229 : Blo 1503572 1692229 := bbase (se 4 (by rfl) ⟨158646, by rfl⟩ : syracuseStep 1692229 = 317293) (by norm_num)
theorem B1905221 : Blo 1503572 1905221 := bbase (se 4 (by rfl) ⟨178614, by rfl⟩ : syracuseStep 1905221 = 357229) (by norm_num)
theorem B2257493 : Blo 1503572 2257493 := bbase (se 8 (by rfl) ⟨13227, by rfl⟩ : syracuseStep 2257493 = 26455) (by norm_num)
theorem B1692265 : Blo 1503572 1692265 := bbase (se 2 (by rfl) ⟨634599, by rfl⟩ : syracuseStep 1692265 = 1269199) (by norm_num)
theorem B2257517 : Blo 1503572 2257517 := bbase (se 3 (by rfl) ⟨423284, by rfl⟩ : syracuseStep 2257517 = 846569) (by norm_num)
theorem B1905277 : Blo 1503572 1905277 := bbase (se 3 (by rfl) ⟨357239, by rfl⟩ : syracuseStep 1905277 = 714479) (by norm_num)
theorem B2257541 : Blo 1503572 2257541 := bbase (se 4 (by rfl) ⟨211644, by rfl⟩ : syracuseStep 2257541 = 423289) (by norm_num)
theorem B1692301 : Blo 1503572 1692301 := bbase (se 3 (by rfl) ⟨317306, by rfl⟩ : syracuseStep 1692301 = 634613) (by norm_num)
theorem B2257565 : Blo 1503572 2257565 := bbase (se 3 (by rfl) ⟨423293, by rfl⟩ : syracuseStep 2257565 = 846587) (by norm_num)
theorem B5075621 : Blo 1503572 5075621 := bbase (se 4 (by rfl) ⟨475839, by rfl⟩ : syracuseStep 5075621 = 951679) (by norm_num)
theorem B1692337 : Blo 1503572 1692337 := bbase (se 2 (by rfl) ⟨634626, by rfl⟩ : syracuseStep 1692337 = 1269253) (by norm_num)
theorem B13718197 : Blo 1503572 13718197 := bbase (se 5 (by rfl) ⟨643040, by rfl⟩ : syracuseStep 13718197 = 1286081) (by norm_num)
theorem B2257589 : Blo 1503572 2257589 := bbase (se 5 (by rfl) ⟨105824, by rfl⟩ : syracuseStep 2257589 = 211649) (by norm_num)
theorem B2257613 : Blo 1503572 2257613 := bbase (se 3 (by rfl) ⟨423302, by rfl⟩ : syracuseStep 2257613 = 846605) (by norm_num)
theorem B1692373 : Blo 1503572 1692373 := bbase (se 7 (by rfl) ⟨19832, by rfl⟩ : syracuseStep 1692373 = 39665) (by norm_num)
theorem B21983957 : Blo 1503572 21983957 := bbase (se 7 (by rfl) ⟨257624, by rfl⟩ : syracuseStep 21983957 = 515249) (by norm_num)
theorem B2855645 : Blo 1503572 2855645 := bbase (se 3 (by rfl) ⟨535433, by rfl⟩ : syracuseStep 2855645 = 1070867) (by norm_num)
theorem B2142941 : Blo 1503572 2142941 := bbase (se 3 (by rfl) ⟨401801, by rfl⟩ : syracuseStep 2142941 = 803603) (by norm_num)
theorem B2257637 : Blo 1503572 2257637 := bbase (se 4 (by rfl) ⟨211653, by rfl⟩ : syracuseStep 2257637 = 423307) (by norm_num)
theorem B1692409 : Blo 1503572 1692409 := bbase (se 2 (by rfl) ⟨634653, by rfl⟩ : syracuseStep 1692409 = 1269307) (by norm_num)
theorem B2257661 : Blo 1503572 2257661 := bbase (se 3 (by rfl) ⟨423311, by rfl⟩ : syracuseStep 2257661 = 846623) (by norm_num)
theorem B2257685 : Blo 1503572 2257685 := bbase (se 6 (by rfl) ⟨52914, by rfl⟩ : syracuseStep 2257685 = 105829) (by norm_num)
theorem B1692445 : Blo 1503572 1692445 := bbase (se 3 (by rfl) ⟨317333, by rfl⟩ : syracuseStep 1692445 = 634667) (by norm_num)
theorem B2257709 : Blo 1503572 2257709 := bbase (se 3 (by rfl) ⟨423320, by rfl⟩ : syracuseStep 2257709 = 846641) (by norm_num)
theorem B1692481 : Blo 1503572 1692481 := bbase (se 2 (by rfl) ⟨634680, by rfl⟩ : syracuseStep 1692481 = 1269361) (by norm_num)
theorem B2257733 : Blo 1503572 2257733 := bbase (se 4 (by rfl) ⟨211662, by rfl⟩ : syracuseStep 2257733 = 423325) (by norm_num)
theorem B2257757 : Blo 1503572 2257757 := bbase (se 3 (by rfl) ⟨423329, by rfl⟩ : syracuseStep 2257757 = 846659) (by norm_num)
theorem B1692517 : Blo 1503572 1692517 := bbase (se 4 (by rfl) ⟨158673, by rfl⟩ : syracuseStep 1692517 = 317347) (by norm_num)
theorem B2257781 : Blo 1503572 2257781 := bbase (se 5 (by rfl) ⟨105833, by rfl⟩ : syracuseStep 2257781 = 211667) (by norm_num)
theorem B6427525 : Blo 1503572 6427525 := bbase (se 4 (by rfl) ⟨602580, by rfl⟩ : syracuseStep 6427525 = 1205161) (by norm_num)
theorem B1692553 : Blo 1503572 1692553 := bbase (se 2 (by rfl) ⟨634707, by rfl⟩ : syracuseStep 1692553 = 1269415) (by norm_num)
theorem B2257805 : Blo 1503572 2257805 := bbase (se 3 (by rfl) ⟨423338, by rfl⟩ : syracuseStep 2257805 = 846677) (by norm_num)
theorem B4821925 : Blo 1503572 4821925 := bbase (se 4 (by rfl) ⟨452055, by rfl⟩ : syracuseStep 4821925 = 904111) (by norm_num)
theorem B2257829 : Blo 1503572 2257829 := bbase (se 4 (by rfl) ⟨211671, by rfl⟩ : syracuseStep 2257829 = 423343) (by norm_num)
theorem B1692589 : Blo 1503572 1692589 := bbase (se 3 (by rfl) ⟨317360, by rfl⟩ : syracuseStep 1692589 = 634721) (by norm_num)
theorem B2257853 : Blo 1503572 2257853 := bbase (se 3 (by rfl) ⟨423347, by rfl⟩ : syracuseStep 2257853 = 846695) (by norm_num)
theorem B3806149 : Blo 1503572 3806149 := bbase (se 4 (by rfl) ⟨356826, by rfl⟩ : syracuseStep 3806149 = 713653) (by norm_num)
theorem B1692625 : Blo 1503572 1692625 := bbase (se 2 (by rfl) ⟨634734, by rfl⟩ : syracuseStep 1692625 = 1269469) (by norm_num)
theorem B2257877 : Blo 1503572 2257877 := bbase (se 7 (by rfl) ⟨26459, by rfl⟩ : syracuseStep 2257877 = 52919) (by norm_num)
theorem B2257901 : Blo 1503572 2257901 := bbase (se 3 (by rfl) ⟨423356, by rfl⟩ : syracuseStep 2257901 = 846713) (by norm_num)
theorem B1692661 : Blo 1503572 1692661 := bbase (se 5 (by rfl) ⟨79343, by rfl⟩ : syracuseStep 1692661 = 158687) (by norm_num)
theorem B2257925 : Blo 1503572 2257925 := bbase (se 4 (by rfl) ⟨211680, by rfl⟩ : syracuseStep 2257925 = 423361) (by norm_num)
theorem B28931093 : Blo 1503572 28931093 := bbase (se 6 (by rfl) ⟨678072, by rfl⟩ : syracuseStep 28931093 = 1356145) (by norm_num)
theorem B1692697 : Blo 1503572 1692697 := bbase (se 2 (by rfl) ⟨634761, by rfl⟩ : syracuseStep 1692697 = 1269523) (by norm_num)
theorem B2257949 : Blo 1503572 2257949 := bbase (se 3 (by rfl) ⟨423365, by rfl⟩ : syracuseStep 2257949 = 846731) (by norm_num)
theorem B5714981 : Blo 1503572 5714981 := bbase (se 4 (by rfl) ⟨535779, by rfl⟩ : syracuseStep 5714981 = 1071559) (by norm_num)
theorem B3806261 : Blo 1503572 3806261 := bbase (se 5 (by rfl) ⟨178418, by rfl⟩ : syracuseStep 3806261 = 356837) (by norm_num)
theorem B2257973 : Blo 1503572 2257973 := bbase (se 5 (by rfl) ⟨105842, by rfl⟩ : syracuseStep 2257973 = 211685) (by norm_num)
theorem B1692733 : Blo 1503572 1692733 := bbase (se 3 (by rfl) ⟨317387, by rfl⟩ : syracuseStep 1692733 = 634775) (by norm_num)
theorem B2257997 : Blo 1503572 2257997 := bbase (se 3 (by rfl) ⟨423374, by rfl⟩ : syracuseStep 2257997 = 846749) (by norm_num)
theorem B5076053 : Blo 1503572 5076053 := bbase (se 8 (by rfl) ⟨29742, by rfl⟩ : syracuseStep 5076053 = 59485) (by norm_num)
theorem B1807453 : Blo 1503572 1807453 := bbase (se 3 (by rfl) ⟨338897, by rfl⟩ : syracuseStep 1807453 = 677795) (by norm_num)
theorem B3257437 : Blo 1503572 3257437 := bbase (se 3 (by rfl) ⟨610769, by rfl⟩ : syracuseStep 3257437 = 1221539) (by norm_num)
theorem B1692769 : Blo 1503572 1692769 := bbase (se 2 (by rfl) ⟨634788, by rfl⟩ : syracuseStep 1692769 = 1269577) (by norm_num)
theorem B2258021 : Blo 1503572 2258021 := bbase (se 4 (by rfl) ⟨211689, by rfl⟩ : syracuseStep 2258021 = 423379) (by norm_num)
theorem B2258045 : Blo 1503572 2258045 := bbase (se 3 (by rfl) ⟨423383, by rfl⟩ : syracuseStep 2258045 = 846767) (by norm_num)
theorem B1692805 : Blo 1503572 1692805 := bbase (se 4 (by rfl) ⟨158700, by rfl⟩ : syracuseStep 1692805 = 317401) (by norm_num)
theorem B2258069 : Blo 1503572 2258069 := bbase (se 6 (by rfl) ⟨52923, by rfl⟩ : syracuseStep 2258069 = 105847) (by norm_num)
theorem B3429533 : Blo 1503572 3429533 := bbase (se 3 (by rfl) ⟨643037, by rfl⟩ : syracuseStep 3429533 = 1286075) (by norm_num)
theorem B1692841 : Blo 1503572 1692841 := bbase (se 2 (by rfl) ⟨634815, by rfl⟩ : syracuseStep 1692841 = 1269631) (by norm_num)
theorem B2258093 : Blo 1503572 2258093 := bbase (se 3 (by rfl) ⟨423392, by rfl⟩ : syracuseStep 2258093 = 846785) (by norm_num)
theorem B2258117 : Blo 1503572 2258117 := bbase (se 4 (by rfl) ⟨211698, by rfl⟩ : syracuseStep 2258117 = 423397) (by norm_num)
theorem B1692877 : Blo 1503572 1692877 := bbase (se 3 (by rfl) ⟨317414, by rfl⟩ : syracuseStep 1692877 = 634829) (by norm_num)
theorem B2258141 : Blo 1503572 2258141 := bbase (se 3 (by rfl) ⟨423401, by rfl⟩ : syracuseStep 2258141 = 846803) (by norm_num)
theorem B1692913 : Blo 1503572 1692913 := bbase (se 2 (by rfl) ⟨634842, by rfl⟩ : syracuseStep 1692913 = 1269685) (by norm_num)
theorem B3806453 : Blo 1503572 3806453 := bbase (se 5 (by rfl) ⟨178427, by rfl⟩ : syracuseStep 3806453 = 356855) (by norm_num)
theorem B2258165 : Blo 1503572 2258165 := bbase (se 5 (by rfl) ⟨105851, by rfl⟩ : syracuseStep 2258165 = 211703) (by norm_num)
theorem B1692949 : Blo 1503572 1692949 := bbase (se 6 (by rfl) ⟨39678, by rfl⟩ : syracuseStep 1692949 = 79357) (by norm_num)
theorem B3429661 : Blo 1503572 3429661 := bbase (se 3 (by rfl) ⟨643061, by rfl⟩ : syracuseStep 3429661 = 1286123) (by norm_num)
theorem B7615781 : Blo 1503572 7615781 := bbase (se 4 (by rfl) ⟨713979, by rfl⟩ : syracuseStep 7615781 = 1427959) (by norm_num)
theorem B4822325 : Blo 1503572 4822325 := bbase (se 5 (by rfl) ⟨226046, by rfl⟩ : syracuseStep 4822325 = 452093) (by norm_num)
theorem B1692985 : Blo 1503572 1692985 := bbase (se 2 (by rfl) ⟨634869, by rfl⟩ : syracuseStep 1692985 = 1269739) (by norm_num)
theorem B5715269 : Blo 1503572 5715269 := bbase (se 4 (by rfl) ⟨535806, by rfl⟩ : syracuseStep 5715269 = 1071613) (by norm_num)
theorem B1693021 : Blo 1503572 1693021 := bbase (se 3 (by rfl) ⟨317441, by rfl⟩ : syracuseStep 1693021 = 634883) (by norm_num)
theorem B1693057 : Blo 1503572 1693057 := bbase (se 2 (by rfl) ⟨634896, by rfl⟩ : syracuseStep 1693057 = 1269793) (by norm_num)
theorem B10843541 : Blo 1503572 10843541 := bbase (se 6 (by rfl) ⟨254145, by rfl⟩ : syracuseStep 10843541 = 508291) (by norm_num)
theorem B3429797 : Blo 1503572 3429797 := bbase (se 4 (by rfl) ⟨321543, by rfl⟩ : syracuseStep 3429797 = 643087) (by norm_num)
theorem B1693093 : Blo 1503572 1693093 := bbase (se 4 (by rfl) ⟨158727, by rfl⟩ : syracuseStep 1693093 = 317455) (by norm_num)
theorem B1693129 : Blo 1503572 1693129 := bbase (se 2 (by rfl) ⟨634923, by rfl⟩ : syracuseStep 1693129 = 1269847) (by norm_num)
theorem B2856397 : Blo 1503572 2856397 := bbase (se 3 (by rfl) ⟨535574, by rfl⟩ : syracuseStep 2856397 = 1071149) (by norm_num)
theorem B1693165 : Blo 1503572 1693165 := bbase (se 3 (by rfl) ⟨317468, by rfl⟩ : syracuseStep 1693165 = 634937) (by norm_num)
theorem B5076485 : Blo 1503572 5076485 := bbase (se 4 (by rfl) ⟨475920, by rfl⟩ : syracuseStep 5076485 = 951841) (by norm_num)
theorem B1693201 : Blo 1503572 1693201 := bbase (se 2 (by rfl) ⟨634950, by rfl⟩ : syracuseStep 1693201 = 1269901) (by norm_num)
theorem B2823725 : Blo 1503572 2823725 := bbase (se 3 (by rfl) ⟨529448, by rfl⟩ : syracuseStep 2823725 = 1058897) (by norm_num)
theorem B1693237 : Blo 1503572 1693237 := bbase (se 5 (by rfl) ⟨79370, by rfl⟩ : syracuseStep 1693237 = 158741) (by norm_num)
theorem B3806797 : Blo 1503572 3806797 := bbase (se 3 (by rfl) ⟨713774, by rfl⟩ : syracuseStep 3806797 = 1427549) (by norm_num)
theorem B19273301 : Blo 1503572 19273301 := bbase (se 8 (by rfl) ⟨112929, by rfl⟩ : syracuseStep 19273301 = 225859) (by norm_num)
theorem B1693273 : Blo 1503572 1693273 := bbase (se 2 (by rfl) ⟨634977, by rfl⟩ : syracuseStep 1693273 = 1269955) (by norm_num)
theorem B2856541 : Blo 1503572 2856541 := bbase (se 3 (by rfl) ⟨535601, by rfl⟩ : syracuseStep 2856541 = 1071203) (by norm_num)
theorem B6428261 : Blo 1503572 6428261 := bbase (se 4 (by rfl) ⟨602649, by rfl⟩ : syracuseStep 6428261 = 1205299) (by norm_num)
theorem B1693309 : Blo 1503572 1693309 := bbase (se 3 (by rfl) ⟨317495, by rfl⟩ : syracuseStep 1693309 = 634991) (by norm_num)
theorem B1693345 : Blo 1503572 1693345 := bbase (se 2 (by rfl) ⟨635004, by rfl⟩ : syracuseStep 1693345 = 1270009) (by norm_num)
theorem B3806909 : Blo 1503572 3806909 := bbase (se 3 (by rfl) ⟨713795, by rfl⟩ : syracuseStep 3806909 = 1427591) (by norm_num)
theorem B1693381 : Blo 1503572 1693381 := bbase (se 4 (by rfl) ⟨158754, by rfl⟩ : syracuseStep 1693381 = 317509) (by norm_num)
theorem B17127125 : Blo 1503572 17127125 := bbase (se 7 (by rfl) ⟨200708, by rfl⟩ : syracuseStep 17127125 = 401417) (by norm_num)
theorem B8132309 : Blo 1503572 8132309 := bbase (se 7 (by rfl) ⟨95300, by rfl⟩ : syracuseStep 8132309 = 190601) (by norm_num)
theorem B1693417 : Blo 1503572 1693417 := bbase (se 2 (by rfl) ⟨635031, by rfl⟩ : syracuseStep 1693417 = 1270063) (by norm_num)
theorem B2856701 : Blo 1503572 2856701 := bbase (se 3 (by rfl) ⟨535631, by rfl⟩ : syracuseStep 2856701 = 1071263) (by norm_num)
theorem B1693453 : Blo 1503572 1693453 := bbase (se 3 (by rfl) ⟨317522, by rfl⟩ : syracuseStep 1693453 = 635045) (by norm_num)
theorem B1693489 : Blo 1503572 1693489 := bbase (se 2 (by rfl) ⟨635058, by rfl⟩ : syracuseStep 1693489 = 1270117) (by norm_num)
theorem B1693525 : Blo 1503572 1693525 := bbase (se 9 (by rfl) ⟨4961, by rfl⟩ : syracuseStep 1693525 = 9923) (by norm_num)
theorem B1693561 : Blo 1503572 1693561 := bbase (se 2 (by rfl) ⟨635085, by rfl⟩ : syracuseStep 1693561 = 1270171) (by norm_num)
theorem B3807101 : Blo 1503572 3807101 := bbase (se 3 (by rfl) ⟨713831, by rfl⟩ : syracuseStep 3807101 = 1427663) (by norm_num)
theorem B2856845 : Blo 1503572 2856845 := bbase (se 3 (by rfl) ⟨535658, by rfl⟩ : syracuseStep 2856845 = 1071317) (by norm_num)
theorem B2537365 : Blo 1503572 2537365 := bbase (se 6 (by rfl) ⟨59469, by rfl⟩ : syracuseStep 2537365 = 118939) (by norm_num)
theorem B1693597 : Blo 1503572 1693597 := bbase (se 3 (by rfl) ⟨317549, by rfl⟩ : syracuseStep 1693597 = 635099) (by norm_num)
theorem B5076917 : Blo 1503572 5076917 := bbase (se 5 (by rfl) ⟨237980, by rfl⟩ : syracuseStep 5076917 = 475961) (by norm_num)
theorem B2537453 : Blo 1503572 2537453 := bbase (se 3 (by rfl) ⟨475772, by rfl⟩ : syracuseStep 2537453 = 951545) (by norm_num)
theorem B6510581 : Blo 1503572 6510581 := bbase (se 5 (by rfl) ⟨305183, by rfl⟩ : syracuseStep 6510581 = 610367) (by norm_num)
theorem B1808453 : Blo 1503572 1808453 := bbase (se 4 (by rfl) ⟨169542, by rfl⟩ : syracuseStep 1808453 = 339085) (by norm_num)
theorem B2537581 : Blo 1503572 2537581 := bbase (se 3 (by rfl) ⟨475796, by rfl⟩ : syracuseStep 2537581 = 951593) (by norm_num)
theorem B1808501 : Blo 1503572 1808501 := bbase (se 5 (by rfl) ⟨84773, by rfl⟩ : syracuseStep 1808501 = 169547) (by norm_num)
theorem B28194965 : Blo 1503572 28194965 := bbase (se 6 (by rfl) ⟨660819, by rfl⟩ : syracuseStep 28194965 = 1321639) (by norm_num)
theorem B2857133 : Blo 1503572 2857133 := bbase (se 3 (by rfl) ⟨535712, by rfl⟩ : syracuseStep 2857133 = 1071425) (by norm_num)
theorem B2537669 : Blo 1503572 2537669 := bbase (se 4 (by rfl) ⟨237906, by rfl⟩ : syracuseStep 2537669 = 475813) (by norm_num)
theorem B1833161 : Blo 1503572 1833161 := bbase (se 2 (by rfl) ⟨687435, by rfl⟩ : syracuseStep 1833161 = 1374871) (by norm_num)
theorem B3807445 : Blo 1503572 3807445 := bbase (se 7 (by rfl) ⟨44618, by rfl⟩ : syracuseStep 3807445 = 89237) (by norm_num)
theorem B2537797 : Blo 1503572 2537797 := bbase (se 4 (by rfl) ⟨237918, by rfl⟩ : syracuseStep 2537797 = 475837) (by norm_num)
theorem B3807557 : Blo 1503572 3807557 := bbase (se 4 (by rfl) ⟨356958, by rfl⟩ : syracuseStep 3807557 = 713917) (by norm_num)
theorem B2857285 : Blo 1503572 2857285 := bbase (se 4 (by rfl) ⟨267870, by rfl⟩ : syracuseStep 2857285 = 535741) (by norm_num)
theorem B8690005 : Blo 1503572 8690005 := bbase (se 10 (by rfl) ⟨12729, by rfl⟩ : syracuseStep 8690005 = 25459) (by norm_num)
theorem B5077349 : Blo 1503572 5077349 := bbase (se 4 (by rfl) ⟨476001, by rfl⟩ : syracuseStep 5077349 = 952003) (by norm_num)
theorem B2537885 : Blo 1503572 2537885 := bbase (se 3 (by rfl) ⟨475853, by rfl⟩ : syracuseStep 2537885 = 951707) (by norm_num)
theorem B3807749 : Blo 1503572 3807749 := bbase (se 4 (by rfl) ⟨356976, by rfl⟩ : syracuseStep 3807749 = 713953) (by norm_num)
theorem B2538013 : Blo 1503572 2538013 := bbase (se 3 (by rfl) ⟨475877, by rfl⟩ : syracuseStep 2538013 = 951755) (by norm_num)
theorem B7617077 : Blo 1503572 7617077 := bbase (se 5 (by rfl) ⟨357050, by rfl⟩ : syracuseStep 7617077 = 714101) (by norm_num)
theorem B2538101 : Blo 1503572 2538101 := bbase (se 5 (by rfl) ⟨118973, by rfl⟩ : syracuseStep 2538101 = 237947) (by norm_num)
theorem B2857589 : Blo 1503572 2857589 := bbase (se 5 (by rfl) ⟨133949, by rfl⟩ : syracuseStep 2857589 = 267899) (by norm_num)
theorem B2538229 : Blo 1503572 2538229 := bbase (se 5 (by rfl) ⟨118979, by rfl⟩ : syracuseStep 2538229 = 237959) (by norm_num)
theorem B5077781 : Blo 1503572 5077781 := bbase (se 6 (by rfl) ⟨119010, by rfl⟩ : syracuseStep 5077781 = 238021) (by norm_num)
theorem B2538317 : Blo 1503572 2538317 := bbase (se 3 (by rfl) ⟨475934, by rfl⟩ : syracuseStep 2538317 = 951869) (by norm_num)
theorem B3808093 : Blo 1503572 3808093 := bbase (se 3 (by rfl) ⟨714017, by rfl⟩ : syracuseStep 3808093 = 1428035) (by norm_num)
theorem B3431285 : Blo 1503572 3431285 := bbase (se 5 (by rfl) ⟨160841, by rfl⟩ : syracuseStep 3431285 = 321683) (by norm_num)
theorem B2538445 : Blo 1503572 2538445 := bbase (se 3 (by rfl) ⟨475958, by rfl⟩ : syracuseStep 2538445 = 951917) (by norm_num)
theorem B3808205 : Blo 1503572 3808205 := bbase (se 3 (by rfl) ⟨714038, by rfl⟩ : syracuseStep 3808205 = 1428077) (by norm_num)
theorem B2538533 : Blo 1503572 2538533 := bbase (se 4 (by rfl) ⟨237987, by rfl⟩ : syracuseStep 2538533 = 475975) (by norm_num)
theorem B3808397 : Blo 1503572 3808397 := bbase (se 3 (by rfl) ⟨714074, by rfl⟩ : syracuseStep 3808397 = 1428149) (by norm_num)
theorem B2538661 : Blo 1503572 2538661 := bbase (se 4 (by rfl) ⟨237999, by rfl⟩ : syracuseStep 2538661 = 475999) (by norm_num)
theorem B5708981 : Blo 1503572 5708981 := bbase (se 5 (by rfl) ⟨267608, by rfl⟩ : syracuseStep 5708981 = 535217) (by norm_num)
theorem B5078213 : Blo 1503572 5078213 := bbase (se 4 (by rfl) ⟨476082, by rfl⟩ : syracuseStep 5078213 = 952165) (by norm_num)
theorem B2538749 : Blo 1503572 2538749 := bbase (se 3 (by rfl) ⟨476015, by rfl⟩ : syracuseStep 2538749 = 952031) (by norm_num)
theorem B2538877 : Blo 1503572 2538877 := bbase (se 3 (by rfl) ⟨476039, by rfl⟩ : syracuseStep 2538877 = 952079) (by norm_num)
theorem B3431813 : Blo 1503572 3431813 := bbase (se 4 (by rfl) ⟨321732, by rfl⟩ : syracuseStep 3431813 = 643465) (by norm_num)
theorem B2710949 : Blo 1503572 2710949 := bbase (se 4 (by rfl) ⟨254151, by rfl⟩ : syracuseStep 2710949 = 508303) (by norm_num)
theorem B2538965 : Blo 1503572 2538965 := bbase (se 7 (by rfl) ⟨29753, by rfl⟩ : syracuseStep 2538965 = 59507) (by norm_num)
theorem B3808741 : Blo 1503572 3808741 := bbase (se 4 (by rfl) ⟨357069, by rfl⟩ : syracuseStep 3808741 = 714139) (by norm_num)
theorem B11427317 : Blo 1503572 11427317 := bbase (se 5 (by rfl) ⟨535655, by rfl⟩ : syracuseStep 11427317 = 1071311) (by norm_num)
theorem B2539093 : Blo 1503572 2539093 := bbase (se 8 (by rfl) ⟨14877, by rfl⟩ : syracuseStep 2539093 = 29755) (by norm_num)
theorem B3808853 : Blo 1503572 3808853 := bbase (se 8 (by rfl) ⟨22317, by rfl⟩ : syracuseStep 3808853 = 44635) (by norm_num)
theorem B10288757 : Blo 1503572 10288757 := bbase (se 5 (by rfl) ⟨482285, by rfl⟩ : syracuseStep 10288757 = 964571) (by norm_num)
theorem B5078645 : Blo 1503572 5078645 := bbase (se 5 (by rfl) ⟨238061, by rfl⟩ : syracuseStep 5078645 = 476123) (by norm_num)
theorem B2539181 : Blo 1503572 2539181 := bbase (se 3 (by rfl) ⟨476096, by rfl⟩ : syracuseStep 2539181 = 952193) (by norm_num)
theorem B3383045 : Blo 1503572 3383045 := bbase (se 4 (by rfl) ⟨317160, by rfl⟩ : syracuseStep 3383045 = 634321) (by norm_num)
theorem B5791493 : Blo 1503572 5791493 := bbase (se 4 (by rfl) ⟨542952, by rfl⟩ : syracuseStep 5791493 = 1085905) (by norm_num)
theorem B3809045 : Blo 1503572 3809045 := bbase (se 6 (by rfl) ⟨89274, by rfl⟩ : syracuseStep 3809045 = 178549) (by norm_num)
theorem B4284197 : Blo 1503572 4284197 := bbase (se 4 (by rfl) ⟨401643, by rfl⟩ : syracuseStep 4284197 = 803287) (by norm_num)
theorem B2539309 : Blo 1503572 2539309 := bbase (se 3 (by rfl) ⟨476120, by rfl⟩ : syracuseStep 2539309 = 952241) (by norm_num)
theorem B7618373 : Blo 1503572 7618373 := bbase (se 4 (by rfl) ⟨714222, by rfl⟩ : syracuseStep 7618373 = 1428445) (by norm_num)
theorem B3383117 : Blo 1503572 3383117 := bbase (se 3 (by rfl) ⟨634334, by rfl⟩ : syracuseStep 3383117 = 1268669) (by norm_num)
theorem B2236285 : Blo 1503572 2236285 := bbase (se 3 (by rfl) ⟨419303, by rfl⟩ : syracuseStep 2236285 = 838607) (by norm_num)
theorem B2539397 : Blo 1503572 2539397 := bbase (se 4 (by rfl) ⟨238068, by rfl⟩ : syracuseStep 2539397 = 476137) (by norm_num)
theorem B3383189 : Blo 1503572 3383189 := bbase (se 6 (by rfl) ⟨79293, by rfl⟩ : syracuseStep 3383189 = 158587) (by norm_num)
theorem B11419541 : Blo 1503572 11419541 := bbase (se 6 (by rfl) ⟨267645, by rfl⟩ : syracuseStep 11419541 = 535291) (by norm_num)
theorem B4120501 : Blo 1503572 4120501 := bbase (se 5 (by rfl) ⟨193148, by rfl⟩ : syracuseStep 4120501 = 386297) (by norm_num)
theorem B3383261 : Blo 1503572 3383261 := bbase (se 3 (by rfl) ⟨634361, by rfl⟩ : syracuseStep 3383261 = 1268723) (by norm_num)
theorem B61784117 : Blo 1503572 61784117 := bstep (se 5 (by rfl) ⟨2896130, by rfl⟩ : syracuseStep 61784117 = 5792261) B5792261
theorem B5709923 : Blo 1503572 5709923 := bstep (se 1 (by rfl) ⟨4282442, by rfl⟩ : syracuseStep 5709923 = 8564885) B8564885
theorem B4284515 : Blo 1503572 4284515 := bstep (se 1 (by rfl) ⟨3213386, by rfl⟩ : syracuseStep 4284515 = 6426773) B6426773
theorem B2539633 : Blo 1503572 2539633 := bstep (se 2 (by rfl) ⟨952362, by rfl⟩ : syracuseStep 2539633 = 1904725) B1904725
theorem B3383441 : Blo 1503572 3383441 := bstep (se 2 (by rfl) ⟨1268790, by rfl⟩ : syracuseStep 3383441 = 2537581) B2537581
theorem B5079185 : Blo 1503572 5079185 := bstep (se 2 (by rfl) ⟨1904694, by rfl⟩ : syracuseStep 5079185 = 3809389) B3809389
theorem B2539667 : Blo 1503572 2539667 := bstep (se 1 (by rfl) ⟨1904750, by rfl⟩ : syracuseStep 2539667 = 3809501) B3809501
theorem B3383459 : Blo 1503572 3383459 := bstep (se 1 (by rfl) ⟨2537594, by rfl⟩ : syracuseStep 3383459 = 5075189) B5075189
theorem B5791985 : Blo 1503572 5791985 := bstep (se 2 (by rfl) ⟨2171994, by rfl⟩ : syracuseStep 5791985 = 4343989) B4343989
theorem B2539795 : Blo 1503572 2539795 := bstep (se 1 (by rfl) ⟨1904846, by rfl⟩ : syracuseStep 2539795 = 3809693) B3809693
theorem B2408753 : Blo 1503572 2408753 := bstep (se 2 (by rfl) ⟨903282, by rfl⟩ : syracuseStep 2408753 = 1806565) B1806565
theorem B2572627 : Blo 1503572 2572627 := bstep (se 1 (by rfl) ⟨1929470, by rfl⟩ : syracuseStep 2572627 = 3858941) B3858941
theorem B2539937 : Blo 1503572 2539937 := bstep (se 2 (by rfl) ⟨952476, by rfl⟩ : syracuseStep 2539937 = 1904953) B1904953
theorem B3383729 : Blo 1503572 3383729 := bstep (se 2 (by rfl) ⟨1268898, by rfl⟩ : syracuseStep 3383729 = 2537797) B2537797
theorem B3809713 : Blo 1503572 3809713 := bstep (se 2 (by rfl) ⟨1428642, by rfl⟩ : syracuseStep 3809713 = 2857285) B2857285
theorem B3383747 : Blo 1503572 3383747 := bstep (se 1 (by rfl) ⟨2537810, by rfl⟩ : syracuseStep 3383747 = 5075621) B5075621
theorem B7619021 : Blo 1503572 7619021 := bstep (se 3 (by rfl) ⟨1428566, by rfl⟩ : syracuseStep 7619021 = 2857133) B2857133
theorem B2712017 : Blo 1503572 2712017 := bstep (se 2 (by rfl) ⟨1017006, by rfl⟩ : syracuseStep 2712017 = 2034013) B2034013
theorem B14655971 : Blo 1503572 14655971 := bstep (se 1 (by rfl) ⟨10991978, by rfl⟩ : syracuseStep 14655971 = 21983957) B21983957
theorem B2408977 : Blo 1503572 2408977 := bstep (se 2 (by rfl) ⟨903366, by rfl⟩ : syracuseStep 2408977 = 1806733) B1806733
theorem B2540065 : Blo 1503572 2540065 := bstep (se 2 (by rfl) ⟨952524, by rfl⟩ : syracuseStep 2540065 = 1905049) B1905049
theorem B2540099 : Blo 1503572 2540099 := bstep (se 1 (by rfl) ⟨1905074, by rfl⟩ : syracuseStep 2540099 = 3810149) B3810149
theorem B2409041 : Blo 1503572 2409041 := bstep (se 2 (by rfl) ⟨903390, by rfl⟩ : syracuseStep 2409041 = 1806781) B1806781
theorem B7225969 : Blo 1503572 7225969 := bstep (se 2 (by rfl) ⟨2709738, by rfl⟩ : syracuseStep 7225969 = 5419477) B5419477
theorem B5079725 : Blo 1503572 5079725 := bstep (se 3 (by rfl) ⟨952448, by rfl⟩ : syracuseStep 5079725 = 1904897) B1904897
theorem B3809987 : Blo 1503572 3809987 := bstep (se 1 (by rfl) ⟨2857490, by rfl⟩ : syracuseStep 3809987 = 5714981) B5714981
theorem B2540227 : Blo 1503572 2540227 := bstep (se 1 (by rfl) ⟨1905170, by rfl⟩ : syracuseStep 2540227 = 3810341) B3810341
theorem B3384017 : Blo 1503572 3384017 := bstep (se 2 (by rfl) ⟨1269006, by rfl⟩ : syracuseStep 3384017 = 2538013) B2538013
theorem B2409169 : Blo 1503572 2409169 := bstep (se 2 (by rfl) ⟨903438, by rfl⟩ : syracuseStep 2409169 = 1806877) B1806877
theorem B3384035 : Blo 1503572 3384035 := bstep (se 1 (by rfl) ⟨2538026, by rfl⟩ : syracuseStep 3384035 = 5076053) B5076053
theorem B5079779 : Blo 1503572 5079779 := bstep (se 1 (by rfl) ⟨3809834, by rfl⟩ : syracuseStep 5079779 = 7619669) B7619669
theorem B2712305 : Blo 1503572 2712305 := bstep (se 2 (by rfl) ⟨1017114, by rfl⟩ : syracuseStep 2712305 = 2034229) B2034229
theorem B1606403 : Blo 1503572 1606403 := bstep (se 1 (by rfl) ⟨1204802, by rfl⟩ : syracuseStep 1606403 = 2409605) B2409605
theorem B2286355 : Blo 1503572 2286355 := bstep (se 1 (by rfl) ⟨1714766, by rfl⟩ : syracuseStep 2286355 = 3429533) B3429533
theorem B2540369 : Blo 1503572 2540369 := bstep (se 2 (by rfl) ⟨952638, by rfl⟩ : syracuseStep 2540369 = 1905277) B1905277
theorem B2032499 : Blo 1503572 2032499 := bstep (se 1 (by rfl) ⟨1524374, by rfl⟩ : syracuseStep 2032499 = 3048749) B3048749
theorem B3810179 : Blo 1503572 3810179 := bstep (se 1 (by rfl) ⟨2857634, by rfl⟩ : syracuseStep 3810179 = 5715269) B5715269
theorem B4285325 : Blo 1503572 4285325 := bstep (se 3 (by rfl) ⟨803498, by rfl⟩ : syracuseStep 4285325 = 1606997) B1606997
theorem B3384305 : Blo 1503572 3384305 := bstep (se 2 (by rfl) ⟨1269114, by rfl⟩ : syracuseStep 3384305 = 2538229) B2538229
theorem B5080049 : Blo 1503572 5080049 := bstep (se 2 (by rfl) ⟨1905018, by rfl⟩ : syracuseStep 5080049 = 3810037) B3810037
theorem B3384323 : Blo 1503572 3384323 := bstep (se 1 (by rfl) ⟨2538242, by rfl⟩ : syracuseStep 3384323 = 5076485) B5076485
theorem B4285507 : Blo 1503572 4285507 := bstep (se 1 (by rfl) ⟨3214130, by rfl⟩ : syracuseStep 4285507 = 6428261) B6428261
theorem B5710925 : Blo 1503572 5710925 := bstep (se 3 (by rfl) ⟨1070798, by rfl⟩ : syracuseStep 5710925 = 2141597) B2141597
theorem B8570033 : Blo 1503572 8570033 := bstep (se 2 (by rfl) ⟨3213762, by rfl⟩ : syracuseStep 8570033 = 6427525) B6427525
theorem B78169315 : Blo 1503572 78169315 := bstep (se 1 (by rfl) ⟨58626986, by rfl⟩ : syracuseStep 78169315 = 117253973) B117253973
theorem B3384593 : Blo 1503572 3384593 := bstep (se 2 (by rfl) ⟨1269222, by rfl⟩ : syracuseStep 3384593 = 2538445) B2538445
theorem B3384611 : Blo 1503572 3384611 := bstep (se 1 (by rfl) ⟨2538458, by rfl⟩ : syracuseStep 3384611 = 5076917) B5076917
theorem B15435107 : Blo 1503572 15435107 := bstep (se 1 (by rfl) ⟨11576330, by rfl⟩ : syracuseStep 15435107 = 23152661) B23152661
theorem B11429261 : Blo 1503572 11429261 := bstep (se 3 (by rfl) ⟨2142986, by rfl⟩ : syracuseStep 11429261 = 4285973) B4285973
theorem B4343249 : Blo 1503572 4343249 := bstep (se 2 (by rfl) ⟨1628718, by rfl⟩ : syracuseStep 4343249 = 3257437) B3257437
theorem B16262669 : Blo 1503572 16262669 := bstep (se 3 (by rfl) ⟨3049250, by rfl⟩ : syracuseStep 16262669 = 6098501) B6098501
theorem B5080589 : Blo 1503572 5080589 := bstep (se 3 (by rfl) ⟨952610, by rfl⟩ : syracuseStep 5080589 = 1905221) B1905221
theorem B2287121 : Blo 1503572 2287121 := bstep (se 2 (by rfl) ⟨857670, by rfl⟩ : syracuseStep 2287121 = 1715341) B1715341
theorem B4818467 : Blo 1503572 4818467 := bstep (se 1 (by rfl) ⟨3613850, by rfl⟩ : syracuseStep 4818467 = 7227701) B7227701
theorem B4285997 : Blo 1503572 4285997 := bstep (se 3 (by rfl) ⟨803624, by rfl⟩ : syracuseStep 4285997 = 1607249) B1607249
theorem B3384881 : Blo 1503572 3384881 := bstep (se 2 (by rfl) ⟨1269330, by rfl⟩ : syracuseStep 3384881 = 2538661) B2538661
theorem B2287169 : Blo 1503572 2287169 := bstep (se 2 (by rfl) ⟨857688, by rfl⟩ : syracuseStep 2287169 = 1715377) B1715377
theorem B3384899 : Blo 1503572 3384899 := bstep (se 1 (by rfl) ⟨2538674, by rfl⟩ : syracuseStep 3384899 = 5077349) B5077349
theorem B5080643 : Blo 1503572 5080643 := bstep (se 1 (by rfl) ⟨3810482, by rfl⟩ : syracuseStep 5080643 = 7620965) B7620965
theorem B2033299 : Blo 1503572 2033299 := bstep (se 1 (by rfl) ⟨1524974, by rfl⟩ : syracuseStep 2033299 = 3049949) B3049949
theorem B4572881 : Blo 1503572 4572881 := bstep (se 2 (by rfl) ⟨1714830, by rfl⟩ : syracuseStep 4572881 = 3429661) B3429661
theorem B1607411 : Blo 1503572 1607411 := bstep (se 1 (by rfl) ⟨1205558, by rfl⟩ : syracuseStep 1607411 = 2411117) B2411117
theorem B6096653 : Blo 1503572 6096653 := bstep (se 3 (by rfl) ⟨1143122, by rfl⟩ : syracuseStep 6096653 = 2286245) B2286245
theorem B3385169 : Blo 1503572 3385169 := bstep (se 2 (by rfl) ⟨1269438, by rfl⟩ : syracuseStep 3385169 = 2538877) B2538877
theorem B3385187 : Blo 1503572 3385187 := bstep (se 1 (by rfl) ⟨2538890, by rfl⟩ : syracuseStep 3385187 = 5077781) B5077781
theorem B2287523 : Blo 1503572 2287523 := bstep (se 1 (by rfl) ⟨1715642, by rfl⟩ : syracuseStep 2287523 = 3431285) B3431285
theorem B65996741 : Blo 1503572 65996741 := bstep (se 4 (by rfl) ⟨6187194, by rfl⟩ : syracuseStep 65996741 = 12374389) B12374389
theorem B3663857 : Blo 1503572 3663857 := bstep (se 2 (by rfl) ⟨1373946, by rfl⟩ : syracuseStep 3663857 = 2747893) B2747893
theorem B2033731 : Blo 1503572 2033731 := bstep (se 1 (by rfl) ⟨1525298, by rfl⟩ : syracuseStep 2033731 = 3050597) B3050597
theorem B3385457 : Blo 1503572 3385457 := bstep (se 2 (by rfl) ⟨1269546, by rfl⟩ : syracuseStep 3385457 = 2539093) B2539093
theorem B3385475 : Blo 1503572 3385475 := bstep (se 1 (by rfl) ⟨2539106, by rfl⟩ : syracuseStep 3385475 = 5078213) B5078213
theorem B6957197 : Blo 1503572 6957197 := bstep (se 3 (by rfl) ⟨1304474, by rfl⟩ : syracuseStep 6957197 = 2608949) B2608949
theorem B3385745 : Blo 1503572 3385745 := bstep (se 2 (by rfl) ⟨1269654, by rfl⟩ : syracuseStep 3385745 = 2539309) B2539309
theorem B6859171 : Blo 1503572 6859171 := bstep (se 1 (by rfl) ⟨5144378, by rfl⟩ : syracuseStep 6859171 = 10288757) B10288757
theorem B3385763 : Blo 1503572 3385763 := bstep (se 1 (by rfl) ⟨2539322, by rfl⟩ : syracuseStep 3385763 = 5078645) B5078645
theorem B2034115 : Blo 1503572 2034115 := bstep (se 1 (by rfl) ⟨1525586, by rfl⟩ : syracuseStep 2034115 = 3051173) B3051173
theorem B2255363 : Blo 1503572 2255363 := bstep (se 1 (by rfl) ⟨1691522, by rfl⟩ : syracuseStep 2255363 = 3383045) B3383045
theorem B3860995 : Blo 1503572 3860995 := bstep (se 1 (by rfl) ⟨2895746, by rfl⟩ : syracuseStep 3860995 = 5791493) B5791493
theorem B2255393 : Blo 1503572 2255393 := bstep (se 2 (by rfl) ⟨845772, by rfl⟩ : syracuseStep 2255393 = 1691545) B1691545
theorem B2255411 : Blo 1503572 2255411 := bstep (se 1 (by rfl) ⟨1691558, by rfl⟩ : syracuseStep 2255411 = 3383117) B3383117
theorem B1903171 : Blo 1503572 1903171 := bstep (se 1 (by rfl) ⟨1427378, by rfl⟩ : syracuseStep 1903171 = 2854757) B2854757
theorem B2255441 : Blo 1503572 2255441 := bstep (se 2 (by rfl) ⟨845790, by rfl⟩ : syracuseStep 2255441 = 1691581) B1691581
theorem B2255459 : Blo 1503572 2255459 := bstep (se 1 (by rfl) ⟨1691594, by rfl⟩ : syracuseStep 2255459 = 3383189) B3383189
theorem B7613027 : Blo 1503572 7613027 := bstep (se 1 (by rfl) ⟨5709770, by rfl⟩ : syracuseStep 7613027 = 11419541) B11419541
theorem B8571491 : Blo 1503572 8571491 := bstep (se 1 (by rfl) ⟨6428618, by rfl⟩ : syracuseStep 8571491 = 12857237) B12857237
theorem B4065905 : Blo 1503572 4065905 := bstep (se 2 (by rfl) ⟨1524714, by rfl⟩ : syracuseStep 4065905 = 3049429) B3049429
theorem B2255489 : Blo 1503572 2255489 := bstep (se 2 (by rfl) ⟨845808, by rfl⟩ : syracuseStep 2255489 = 1691617) B1691617
theorem B2255507 : Blo 1503572 2255507 := bstep (se 1 (by rfl) ⟨1691630, by rfl⟩ : syracuseStep 2255507 = 3383261) B3383261
theorem B2034337 : Blo 1503572 2034337 := bstep (se 2 (by rfl) ⟨762876, by rfl⟩ : syracuseStep 2034337 = 1525753) B1525753
theorem B1903267 : Blo 1503572 1903267 := bstep (se 1 (by rfl) ⟨1427450, by rfl⟩ : syracuseStep 1903267 = 2854901) B2854901
theorem B2255537 : Blo 1503572 2255537 := bstep (se 2 (by rfl) ⟨845826, by rfl⟩ : syracuseStep 2255537 = 1691653) B1691653
theorem B3386033 : Blo 1503572 3386033 := bstep (se 2 (by rfl) ⟨1269762, by rfl⟩ : syracuseStep 3386033 = 2539525) B2539525
theorem B2255555 : Blo 1503572 2255555 := bstep (se 1 (by rfl) ⟨1691666, by rfl⟩ : syracuseStep 2255555 = 3383333) B3383333
theorem B3214019 : Blo 1503572 3214019 := bstep (se 1 (by rfl) ⟨2410514, by rfl⟩ : syracuseStep 3214019 = 4821029) B4821029
theorem B3386051 : Blo 1503572 3386051 := bstep (se 1 (by rfl) ⟨2539538, by rfl⟩ : syracuseStep 3386051 = 5079077) B5079077
theorem B2411219 : Blo 1503572 2411219 := bstep (se 1 (by rfl) ⟨1808414, by rfl⟩ : syracuseStep 2411219 = 3616829) B3616829
theorem B2255585 : Blo 1503572 2255585 := bstep (se 2 (by rfl) ⟨845844, by rfl⟩ : syracuseStep 2255585 = 1691689) B1691689
theorem B8563427 : Blo 1503572 8563427 := bstep (se 1 (by rfl) ⟨6422570, by rfl⟩ : syracuseStep 8563427 = 12845141) B12845141
theorem B5147363 : Blo 1503572 5147363 := bstep (se 1 (by rfl) ⟨3860522, by rfl⟩ : syracuseStep 5147363 = 7721045) B7721045
theorem B3050225 : Blo 1503572 3050225 := bstep (se 2 (by rfl) ⟨1143834, by rfl⟩ : syracuseStep 3050225 = 2287669) B2287669
theorem B2255603 : Blo 1503572 2255603 := bstep (se 1 (by rfl) ⟨1691702, by rfl⟩ : syracuseStep 2255603 = 3383405) B3383405
theorem B2140931 : Blo 1503572 2140931 := bstep (se 1 (by rfl) ⟨1605698, by rfl⟩ : syracuseStep 2140931 = 3211397) B3211397
theorem B2255633 : Blo 1503572 2255633 := bstep (se 2 (by rfl) ⟨845862, by rfl⟩ : syracuseStep 2255633 = 1691725) B1691725
theorem B2255651 : Blo 1503572 2255651 := bstep (se 1 (by rfl) ⟨1691738, by rfl⟩ : syracuseStep 2255651 = 3383477) B3383477
theorem B2255681 : Blo 1503572 2255681 := bstep (se 2 (by rfl) ⟨845880, by rfl⟩ : syracuseStep 2255681 = 1691761) B1691761
theorem B2255699 : Blo 1503572 2255699 := bstep (se 1 (by rfl) ⟨1691774, by rfl⟩ : syracuseStep 2255699 = 3383549) B3383549
theorem B2255729 : Blo 1503572 2255729 := bstep (se 2 (by rfl) ⟨845898, by rfl⟩ : syracuseStep 2255729 = 1691797) B1691797
theorem B2255747 : Blo 1503572 2255747 := bstep (se 1 (by rfl) ⟨1691810, by rfl⟩ : syracuseStep 2255747 = 3383621) B3383621
theorem B2255777 : Blo 1503572 2255777 := bstep (se 2 (by rfl) ⟨845916, by rfl⟩ : syracuseStep 2255777 = 1691833) B1691833
theorem B2255795 : Blo 1503572 2255795 := bstep (se 1 (by rfl) ⟨1691846, by rfl⟩ : syracuseStep 2255795 = 3383693) B3383693
theorem B2255825 : Blo 1503572 2255825 := bstep (se 2 (by rfl) ⟨845934, by rfl⟩ : syracuseStep 2255825 = 1691869) B1691869
theorem B3386321 : Blo 1503572 3386321 := bstep (se 2 (by rfl) ⟨1269870, by rfl⟩ : syracuseStep 3386321 = 2539741) B2539741
theorem B2288593 : Blo 1503572 2288593 := bstep (se 2 (by rfl) ⟨858222, by rfl⟩ : syracuseStep 2288593 = 1716445) B1716445
theorem B2255843 : Blo 1503572 2255843 := bstep (se 1 (by rfl) ⟨1691882, by rfl⟩ : syracuseStep 2255843 = 3383765) B3383765
theorem B3386339 : Blo 1503572 3386339 := bstep (se 1 (by rfl) ⟨2539754, by rfl⟩ : syracuseStep 3386339 = 5079509) B5079509
theorem B2255873 : Blo 1503572 2255873 := bstep (se 2 (by rfl) ⟨845952, by rfl⟩ : syracuseStep 2255873 = 1691905) B1691905
theorem B2255891 : Blo 1503572 2255891 := bstep (se 1 (by rfl) ⟨1691918, by rfl⟩ : syracuseStep 2255891 = 3383837) B3383837
theorem B2255921 : Blo 1503572 2255921 := bstep (se 2 (by rfl) ⟨845970, by rfl⟩ : syracuseStep 2255921 = 1691941) B1691941
theorem B2255939 : Blo 1503572 2255939 := bstep (se 1 (by rfl) ⟨1691954, by rfl⟩ : syracuseStep 2255939 = 3383909) B3383909
theorem B2255969 : Blo 1503572 2255969 := bstep (se 2 (by rfl) ⟨845988, by rfl⟩ : syracuseStep 2255969 = 1691977) B1691977
theorem B11586673 : Blo 1503572 11586673 := bstep (se 2 (by rfl) ⟨4345002, by rfl⟩ : syracuseStep 11586673 = 8690005) B8690005
theorem B2255987 : Blo 1503572 2255987 := bstep (se 1 (by rfl) ⟨1691990, by rfl⟩ : syracuseStep 2255987 = 3383981) B3383981
theorem B5713037 : Blo 1503572 5713037 := bstep (se 3 (by rfl) ⟨1071194, by rfl⟩ : syracuseStep 5713037 = 2142389) B2142389
theorem B2256017 : Blo 1503572 2256017 := bstep (se 2 (by rfl) ⟨846006, by rfl⟩ : syracuseStep 2256017 = 1692013) B1692013
theorem B1903763 : Blo 1503572 1903763 := bstep (se 1 (by rfl) ⟨1427822, by rfl⟩ : syracuseStep 1903763 = 2855645) B2855645
theorem B2256035 : Blo 1503572 2256035 := bstep (se 1 (by rfl) ⟨1692026, by rfl⟩ : syracuseStep 2256035 = 3384053) B3384053
theorem B2256065 : Blo 1503572 2256065 := bstep (se 2 (by rfl) ⟨846024, by rfl⟩ : syracuseStep 2256065 = 1692049) B1692049
theorem B2256083 : Blo 1503572 2256083 := bstep (se 1 (by rfl) ⟨1692062, by rfl⟩ : syracuseStep 2256083 = 3384125) B3384125
theorem B2256113 : Blo 1503572 2256113 := bstep (se 2 (by rfl) ⟨846042, by rfl⟩ : syracuseStep 2256113 = 1692085) B1692085
theorem B3386609 : Blo 1503572 3386609 := bstep (se 2 (by rfl) ⟨1269978, by rfl⟩ : syracuseStep 3386609 = 2539957) B2539957
theorem B2256131 : Blo 1503572 2256131 := bstep (se 1 (by rfl) ⟨1692098, by rfl⟩ : syracuseStep 2256131 = 3384197) B3384197
theorem B3386627 : Blo 1503572 3386627 := bstep (se 1 (by rfl) ⟨2539970, by rfl⟩ : syracuseStep 3386627 = 5079941) B5079941
theorem B2256161 : Blo 1503572 2256161 := bstep (se 2 (by rfl) ⟨846060, by rfl⟩ : syracuseStep 2256161 = 1692121) B1692121
theorem B2256179 : Blo 1503572 2256179 := bstep (se 1 (by rfl) ⟨1692134, by rfl⟩ : syracuseStep 2256179 = 3384269) B3384269
theorem B9645389 : Blo 1503572 9645389 := bstep (se 3 (by rfl) ⟨1808510, by rfl⟩ : syracuseStep 9645389 = 3617021) B3617021
theorem B2256209 : Blo 1503572 2256209 := bstep (se 2 (by rfl) ⟨846078, by rfl⟩ : syracuseStep 2256209 = 1692157) B1692157
theorem B2256227 : Blo 1503572 2256227 := bstep (se 1 (by rfl) ⟨1692170, by rfl⟩ : syracuseStep 2256227 = 3384341) B3384341
theorem B19287395 : Blo 1503572 19287395 := bstep (se 1 (by rfl) ⟨14465546, by rfl⟩ : syracuseStep 19287395 = 28931093) B28931093
theorem B2141569 : Blo 1503572 2141569 := bstep (se 2 (by rfl) ⟨803088, by rfl⟩ : syracuseStep 2141569 = 1606177) B1606177
theorem B2256257 : Blo 1503572 2256257 := bstep (se 2 (by rfl) ⟨846096, by rfl⟩ : syracuseStep 2256257 = 1692193) B1692193
theorem B7613837 : Blo 1503572 7613837 := bstep (se 3 (by rfl) ⟨1427594, by rfl⟩ : syracuseStep 7613837 = 2855189) B2855189
theorem B2256275 : Blo 1503572 2256275 := bstep (se 1 (by rfl) ⟨1692206, by rfl⟩ : syracuseStep 2256275 = 3384413) B3384413
theorem B2256305 : Blo 1503572 2256305 := bstep (se 2 (by rfl) ⟨846114, by rfl⟩ : syracuseStep 2256305 = 1692229) B1692229
theorem B2256323 : Blo 1503572 2256323 := bstep (se 1 (by rfl) ⟨1692242, by rfl⟩ : syracuseStep 2256323 = 3384485) B3384485
theorem B2256353 : Blo 1503572 2256353 := bstep (se 2 (by rfl) ⟨846132, by rfl⟩ : syracuseStep 2256353 = 1692265) B1692265
theorem B2256371 : Blo 1503572 2256371 := bstep (se 1 (by rfl) ⟨1692278, by rfl⟩ : syracuseStep 2256371 = 3384557) B3384557
theorem B6426125 : Blo 1503572 6426125 := bstep (se 3 (by rfl) ⟨1204898, by rfl⟩ : syracuseStep 6426125 = 2409797) B2409797
theorem B2256401 : Blo 1503572 2256401 := bstep (se 2 (by rfl) ⟨846150, by rfl⟩ : syracuseStep 2256401 = 1692301) B1692301
theorem B3386897 : Blo 1503572 3386897 := bstep (se 2 (by rfl) ⟨1270086, by rfl⟩ : syracuseStep 3386897 = 2540173) B2540173
theorem B2256419 : Blo 1503572 2256419 := bstep (se 1 (by rfl) ⟨1692314, by rfl⟩ : syracuseStep 2256419 = 3384629) B3384629
theorem B3214883 : Blo 1503572 3214883 := bstep (se 1 (by rfl) ⟨2411162, by rfl⟩ : syracuseStep 3214883 = 4822325) B4822325
theorem B3386915 : Blo 1503572 3386915 := bstep (se 1 (by rfl) ⟨2540186, by rfl⟩ : syracuseStep 3386915 = 5080373) B5080373
theorem B2256449 : Blo 1503572 2256449 := bstep (se 2 (by rfl) ⟨846168, by rfl⟩ : syracuseStep 2256449 = 1692337) B1692337
theorem B8572493 : Blo 1503572 8572493 := bstep (se 3 (by rfl) ⟨1607342, by rfl⟩ : syracuseStep 8572493 = 3214685) B3214685
theorem B2256467 : Blo 1503572 2256467 := bstep (se 1 (by rfl) ⟨1692350, by rfl⟩ : syracuseStep 2256467 = 3384701) B3384701
theorem B7229027 : Blo 1503572 7229027 := bstep (se 1 (by rfl) ⟨5421770, by rfl⟩ : syracuseStep 7229027 = 10843541) B10843541
theorem B2256497 : Blo 1503572 2256497 := bstep (se 2 (by rfl) ⟨846186, by rfl⟩ : syracuseStep 2256497 = 1692373) B1692373
theorem B4820593 : Blo 1503572 4820593 := bstep (se 2 (by rfl) ⟨1807722, by rfl⟩ : syracuseStep 4820593 = 3615445) B3615445
theorem B2256515 : Blo 1503572 2256515 := bstep (se 1 (by rfl) ⟨1692386, by rfl⟩ : syracuseStep 2256515 = 3384773) B3384773
theorem B3214993 : Blo 1503572 3214993 := bstep (se 2 (by rfl) ⟨1205622, by rfl⟩ : syracuseStep 3214993 = 2411245) B2411245
theorem B2256545 : Blo 1503572 2256545 := bstep (se 2 (by rfl) ⟨846204, by rfl⟩ : syracuseStep 2256545 = 1692409) B1692409
theorem B5074595 : Blo 1503572 5074595 := bstep (se 1 (by rfl) ⟨3805946, by rfl⟩ : syracuseStep 5074595 = 7611893) B7611893
theorem B2256563 : Blo 1503572 2256563 := bstep (se 1 (by rfl) ⟨1692422, by rfl⟩ : syracuseStep 2256563 = 3384845) B3384845
theorem B11423429 : Blo 1503572 11423429 := bstep (se 4 (by rfl) ⟨1070946, by rfl⟩ : syracuseStep 11423429 = 2141893) B2141893
theorem B8130253 : Blo 1503572 8130253 := bstep (se 3 (by rfl) ⟨1524422, by rfl⟩ : syracuseStep 8130253 = 3048845) B3048845
theorem B2141905 : Blo 1503572 2141905 := bstep (se 2 (by rfl) ⟨803214, by rfl⟩ : syracuseStep 2141905 = 1606429) B1606429
theorem B2256593 : Blo 1503572 2256593 := bstep (se 2 (by rfl) ⟨846222, by rfl⟩ : syracuseStep 2256593 = 1692445) B1692445
theorem B12848867 : Blo 1503572 12848867 := bstep (se 1 (by rfl) ⟨9636650, by rfl⟩ : syracuseStep 12848867 = 19273301) B19273301
theorem B2256611 : Blo 1503572 2256611 := bstep (se 1 (by rfl) ⟨1692458, by rfl⟩ : syracuseStep 2256611 = 3384917) B3384917
theorem B2256641 : Blo 1503572 2256641 := bstep (se 2 (by rfl) ⟨846240, by rfl⟩ : syracuseStep 2256641 = 1692481) B1692481
theorem B9146125 : Blo 1503572 9146125 := bstep (se 3 (by rfl) ⟨1714898, by rfl⟩ : syracuseStep 9146125 = 3429797) B3429797
theorem B7229197 : Blo 1503572 7229197 := bstep (se 3 (by rfl) ⟨1355474, by rfl⟩ : syracuseStep 7229197 = 2710949) B2710949
theorem B2854673 : Blo 1503572 2854673 := bstep (se 2 (by rfl) ⟨1070502, by rfl⟩ : syracuseStep 2854673 = 2141005) B2141005
theorem B2256659 : Blo 1503572 2256659 := bstep (se 1 (by rfl) ⟨1692494, by rfl⟩ : syracuseStep 2256659 = 3384989) B3384989
theorem B4067117 : Blo 1503572 4067117 := bstep (se 3 (by rfl) ⟨762584, by rfl⟩ : syracuseStep 4067117 = 1525169) B1525169
theorem B2256689 : Blo 1503572 2256689 := bstep (se 2 (by rfl) ⟨846258, by rfl⟩ : syracuseStep 2256689 = 1692517) B1692517
theorem B3387185 : Blo 1503572 3387185 := bstep (se 2 (by rfl) ⟨1270194, by rfl⟩ : syracuseStep 3387185 = 2540389) B2540389
theorem B2256707 : Blo 1503572 2256707 := bstep (se 1 (by rfl) ⟨1692530, by rfl⟩ : syracuseStep 2256707 = 3385061) B3385061
theorem B3387203 : Blo 1503572 3387203 := bstep (se 1 (by rfl) ⟨2540402, by rfl⟩ : syracuseStep 3387203 = 5080805) B5080805
theorem B1904467 : Blo 1503572 1904467 := bstep (se 1 (by rfl) ⟨1428350, by rfl⟩ : syracuseStep 1904467 = 2856701) B2856701
theorem B2256737 : Blo 1503572 2256737 := bstep (se 2 (by rfl) ⟨846276, by rfl⟩ : syracuseStep 2256737 = 1692553) B1692553
theorem B2256755 : Blo 1503572 2256755 := bstep (se 1 (by rfl) ⟨1692566, by rfl⟩ : syracuseStep 2256755 = 3385133) B3385133
theorem B2256785 : Blo 1503572 2256785 := bstep (se 2 (by rfl) ⟨846294, by rfl⟩ : syracuseStep 2256785 = 1692589) B1692589
theorem B2256803 : Blo 1503572 2256803 := bstep (se 1 (by rfl) ⟨1692602, by rfl⟩ : syracuseStep 2256803 = 3385205) B3385205
theorem B5074865 : Blo 1503572 5074865 := bstep (se 2 (by rfl) ⟨1903074, by rfl⟩ : syracuseStep 5074865 = 3806149) B3806149
theorem B5713841 : Blo 1503572 5713841 := bstep (se 2 (by rfl) ⟨2142690, by rfl⟩ : syracuseStep 5713841 = 4285381) B4285381
theorem B1904563 : Blo 1503572 1904563 := bstep (se 1 (by rfl) ⟨1428422, by rfl⟩ : syracuseStep 1904563 = 2856845) B2856845
theorem B2256833 : Blo 1503572 2256833 := bstep (se 2 (by rfl) ⟨846312, by rfl⟩ : syracuseStep 2256833 = 1692625) B1692625
theorem B2256851 : Blo 1503572 2256851 := bstep (se 1 (by rfl) ⟨1692638, by rfl⟩ : syracuseStep 2256851 = 3385277) B3385277
theorem B2256881 : Blo 1503572 2256881 := bstep (se 2 (by rfl) ⟨846330, by rfl⟩ : syracuseStep 2256881 = 1692661) B1692661
theorem B1691635 : Blo 1503572 1691635 := bstep (se 1 (by rfl) ⟨1268726, by rfl⟩ : syracuseStep 1691635 = 2537453) B2537453
theorem B2256899 : Blo 1503572 2256899 := bstep (se 1 (by rfl) ⟨1692674, by rfl⟩ : syracuseStep 2256899 = 3385349) B3385349
theorem B2256929 : Blo 1503572 2256929 := bstep (se 2 (by rfl) ⟨846348, by rfl⟩ : syracuseStep 2256929 = 1692697) B1692697
theorem B2256947 : Blo 1503572 2256947 := bstep (se 1 (by rfl) ⟨1692710, by rfl⟩ : syracuseStep 2256947 = 3385421) B3385421
theorem B36606005 : Blo 1503572 36606005 := bstep (se 5 (by rfl) ⟨1715906, by rfl⟩ : syracuseStep 36606005 = 3431813) B3431813
theorem B2256977 : Blo 1503572 2256977 := bstep (se 2 (by rfl) ⟨846366, by rfl⟩ : syracuseStep 2256977 = 1692733) B1692733
theorem B18796643 : Blo 1503572 18796643 := bstep (se 1 (by rfl) ⟨14097482, by rfl⟩ : syracuseStep 18796643 = 28194965) B28194965
theorem B2256995 : Blo 1503572 2256995 := bstep (se 1 (by rfl) ⟨1692746, by rfl⟩ : syracuseStep 2256995 = 3385493) B3385493
theorem B2257025 : Blo 1503572 2257025 := bstep (se 2 (by rfl) ⟨846384, by rfl⟩ : syracuseStep 2257025 = 1692769) B1692769
theorem B1691779 : Blo 1503572 1691779 := bstep (se 1 (by rfl) ⟨1268834, by rfl⟩ : syracuseStep 1691779 = 2537669) B2537669
theorem B2257043 : Blo 1503572 2257043 := bstep (se 1 (by rfl) ⟨1692782, by rfl⟩ : syracuseStep 2257043 = 3385565) B3385565
theorem B2257073 : Blo 1503572 2257073 := bstep (se 2 (by rfl) ⟨846402, by rfl⟩ : syracuseStep 2257073 = 1692805) B1692805
theorem B2257091 : Blo 1503572 2257091 := bstep (se 1 (by rfl) ⟨1692818, by rfl⟩ : syracuseStep 2257091 = 3385637) B3385637
theorem B2257121 : Blo 1503572 2257121 := bstep (se 2 (by rfl) ⟨846420, by rfl⟩ : syracuseStep 2257121 = 1692841) B1692841
theorem B2257139 : Blo 1503572 2257139 := bstep (se 1 (by rfl) ⟨1692854, by rfl⟩ : syracuseStep 2257139 = 3385709) B3385709
theorem B2257169 : Blo 1503572 2257169 := bstep (se 2 (by rfl) ⟨846438, by rfl⟩ : syracuseStep 2257169 = 1692877) B1692877
theorem B1691923 : Blo 1503572 1691923 := bstep (se 1 (by rfl) ⟨1268942, by rfl⟩ : syracuseStep 1691923 = 2537885) B2537885
theorem B2142497 : Blo 1503572 2142497 := bstep (se 2 (by rfl) ⟨803436, by rfl⟩ : syracuseStep 2142497 = 1606873) B1606873
theorem B2257187 : Blo 1503572 2257187 := bstep (se 1 (by rfl) ⟨1692890, by rfl⟩ : syracuseStep 2257187 = 3385781) B3385781
theorem B3617059 : Blo 1503572 3617059 := bstep (se 1 (by rfl) ⟨2712794, by rfl⟩ : syracuseStep 3617059 = 5425589) B5425589
theorem B2896177 : Blo 1503572 2896177 := bstep (se 2 (by rfl) ⟨1086066, by rfl⟩ : syracuseStep 2896177 = 2172133) B2172133
theorem B2257217 : Blo 1503572 2257217 := bstep (se 2 (by rfl) ⟨846456, by rfl⟩ : syracuseStep 2257217 = 1692913) B1692913
theorem B2257235 : Blo 1503572 2257235 := bstep (se 1 (by rfl) ⟨1692926, by rfl⟩ : syracuseStep 2257235 = 3385853) B3385853
theorem B1503587 : Blo 1503572 1503587 := bstep (se 1 (by rfl) ⟨1127690, by rfl⟩ : syracuseStep 1503587 = 2255381) B2255381
theorem B2257265 : Blo 1503572 2257265 := bstep (se 2 (by rfl) ⟨846474, by rfl⟩ : syracuseStep 2257265 = 1692949) B1692949
theorem B1503603 : Blo 1503572 1503603 := bstep (se 1 (by rfl) ⟨1127702, by rfl⟩ : syracuseStep 1503603 = 2255405) B2255405
theorem B1503619 : Blo 1503572 1503619 := bstep (se 1 (by rfl) ⟨1127714, by rfl⟩ : syracuseStep 1503619 = 2255429) B2255429
theorem B2257283 : Blo 1503572 2257283 := bstep (se 1 (by rfl) ⟨1692962, by rfl⟩ : syracuseStep 2257283 = 3385925) B3385925
theorem B1503635 : Blo 1503572 1503635 := bstep (se 1 (by rfl) ⟨1127726, by rfl⟩ : syracuseStep 1503635 = 2255453) B2255453
theorem B2257313 : Blo 1503572 2257313 := bstep (se 2 (by rfl) ⟨846492, by rfl⟩ : syracuseStep 2257313 = 1692985) B1692985
theorem B1503651 : Blo 1503572 1503651 := bstep (se 1 (by rfl) ⟨1127738, by rfl⟩ : syracuseStep 1503651 = 2255477) B2255477
theorem B1692067 : Blo 1503572 1692067 := bstep (se 1 (by rfl) ⟨1269050, by rfl⟩ : syracuseStep 1692067 = 2538101) B2538101
theorem B1905059 : Blo 1503572 1905059 := bstep (se 1 (by rfl) ⟨1428794, by rfl⟩ : syracuseStep 1905059 = 2857589) B2857589
theorem B1503667 : Blo 1503572 1503667 := bstep (se 1 (by rfl) ⟨1127750, by rfl⟩ : syracuseStep 1503667 = 2255501) B2255501
theorem B2257331 : Blo 1503572 2257331 := bstep (se 1 (by rfl) ⟨1692998, by rfl⟩ : syracuseStep 2257331 = 3385997) B3385997
theorem B1503683 : Blo 1503572 1503683 := bstep (se 1 (by rfl) ⟨1127762, by rfl⟩ : syracuseStep 1503683 = 2255525) B2255525
theorem B5075405 : Blo 1503572 5075405 := bstep (se 3 (by rfl) ⟨951638, by rfl⟩ : syracuseStep 5075405 = 1903277) B1903277
theorem B2257361 : Blo 1503572 2257361 := bstep (se 2 (by rfl) ⟨846510, by rfl⟩ : syracuseStep 2257361 = 1693021) B1693021
theorem B1503699 : Blo 1503572 1503699 := bstep (se 1 (by rfl) ⟨1127774, by rfl⟩ : syracuseStep 1503699 = 2255549) B2255549
theorem B1503715 : Blo 1503572 1503715 := bstep (se 1 (by rfl) ⟨1127786, by rfl⟩ : syracuseStep 1503715 = 2255573) B2255573
theorem B2257379 : Blo 1503572 2257379 := bstep (se 1 (by rfl) ⟨1693034, by rfl⟩ : syracuseStep 2257379 = 3386069) B3386069
theorem B1503731 : Blo 1503572 1503731 := bstep (se 1 (by rfl) ⟨1127798, by rfl⟩ : syracuseStep 1503731 = 2255597) B2255597
theorem B2257409 : Blo 1503572 2257409 := bstep (se 2 (by rfl) ⟨846528, by rfl⟩ : syracuseStep 2257409 = 1693057) B1693057
theorem B1503747 : Blo 1503572 1503747 := bstep (se 1 (by rfl) ⟨1127810, by rfl⟩ : syracuseStep 1503747 = 2255621) B2255621
theorem B5075459 : Blo 1503572 5075459 := bstep (se 1 (by rfl) ⟨3806594, by rfl⟩ : syracuseStep 5075459 = 7613189) B7613189
theorem B1503763 : Blo 1503572 1503763 := bstep (se 1 (by rfl) ⟨1127822, by rfl⟩ : syracuseStep 1503763 = 2255645) B2255645
theorem B2257427 : Blo 1503572 2257427 := bstep (se 1 (by rfl) ⟨1693070, by rfl⟩ : syracuseStep 2257427 = 3386141) B3386141
theorem B1503779 : Blo 1503572 1503779 := bstep (se 1 (by rfl) ⟨1127834, by rfl⟩ : syracuseStep 1503779 = 2255669) B2255669
theorem B2257457 : Blo 1503572 2257457 := bstep (se 2 (by rfl) ⟨846546, by rfl⟩ : syracuseStep 2257457 = 1693093) B1693093
theorem B1503795 : Blo 1503572 1503795 := bstep (se 1 (by rfl) ⟨1127846, by rfl⟩ : syracuseStep 1503795 = 2255693) B2255693
theorem B1692211 : Blo 1503572 1692211 := bstep (se 1 (by rfl) ⟨1269158, by rfl⟩ : syracuseStep 1692211 = 2538317) B2538317
theorem B1503811 : Blo 1503572 1503811 := bstep (se 1 (by rfl) ⟨1127858, by rfl⟩ : syracuseStep 1503811 = 2255717) B2255717
theorem B2257475 : Blo 1503572 2257475 := bstep (se 1 (by rfl) ⟨1693106, by rfl⟩ : syracuseStep 2257475 = 3386213) B3386213
theorem B5714509 : Blo 1503572 5714509 := bstep (se 3 (by rfl) ⟨1071470, by rfl⟩ : syracuseStep 5714509 = 2142941) B2142941
theorem B1503827 : Blo 1503572 1503827 := bstep (se 1 (by rfl) ⟨1127870, by rfl⟩ : syracuseStep 1503827 = 2255741) B2255741
theorem B2257505 : Blo 1503572 2257505 := bstep (se 2 (by rfl) ⟨846564, by rfl⟩ : syracuseStep 2257505 = 1693129) B1693129
theorem B1503843 : Blo 1503572 1503843 := bstep (se 1 (by rfl) ⟨1127882, by rfl⟩ : syracuseStep 1503843 = 2255765) B2255765
theorem B1503859 : Blo 1503572 1503859 := bstep (se 1 (by rfl) ⟨1127894, by rfl⟩ : syracuseStep 1503859 = 2255789) B2255789
theorem B2257523 : Blo 1503572 2257523 := bstep (se 1 (by rfl) ⟨1693142, by rfl⟩ : syracuseStep 2257523 = 3386285) B3386285
theorem B1503875 : Blo 1503572 1503875 := bstep (se 1 (by rfl) ⟨1127906, by rfl⟩ : syracuseStep 1503875 = 2255813) B2255813
theorem B2855569 : Blo 1503572 2855569 := bstep (se 2 (by rfl) ⟨1070838, by rfl⟩ : syracuseStep 2855569 = 2141677) B2141677
theorem B1503891 : Blo 1503572 1503891 := bstep (se 1 (by rfl) ⟨1127918, by rfl⟩ : syracuseStep 1503891 = 2255837) B2255837
theorem B2257553 : Blo 1503572 2257553 := bstep (se 2 (by rfl) ⟨846582, by rfl⟩ : syracuseStep 2257553 = 1693165) B1693165
theorem B1503907 : Blo 1503572 1503907 := bstep (se 1 (by rfl) ⟨1127930, by rfl⟩ : syracuseStep 1503907 = 2255861) B2255861
theorem B2257571 : Blo 1503572 2257571 := bstep (se 1 (by rfl) ⟨1693178, by rfl⟩ : syracuseStep 2257571 = 3386357) B3386357
theorem B1503923 : Blo 1503572 1503923 := bstep (se 1 (by rfl) ⟨1127942, by rfl⟩ : syracuseStep 1503923 = 2255885) B2255885
theorem B2257601 : Blo 1503572 2257601 := bstep (se 2 (by rfl) ⟨846600, by rfl⟩ : syracuseStep 2257601 = 1693201) B1693201
theorem B1503939 : Blo 1503572 1503939 := bstep (se 1 (by rfl) ⟨1127954, by rfl⟩ : syracuseStep 1503939 = 2255909) B2255909
theorem B1692355 : Blo 1503572 1692355 := bstep (se 1 (by rfl) ⟨1269266, by rfl⟩ : syracuseStep 1692355 = 2538533) B2538533
theorem B1503955 : Blo 1503572 1503955 := bstep (se 1 (by rfl) ⟨1127966, by rfl⟩ : syracuseStep 1503955 = 2255933) B2255933
theorem B2257619 : Blo 1503572 2257619 := bstep (se 1 (by rfl) ⟨1693214, by rfl⟩ : syracuseStep 2257619 = 3386429) B3386429
theorem B1503971 : Blo 1503572 1503971 := bstep (se 1 (by rfl) ⟨1127978, by rfl⟩ : syracuseStep 1503971 = 2255957) B2255957
theorem B3805937 : Blo 1503572 3805937 := bstep (se 2 (by rfl) ⟨1427226, by rfl⟩ : syracuseStep 3805937 = 2854453) B2854453
theorem B2257649 : Blo 1503572 2257649 := bstep (se 2 (by rfl) ⟨846618, by rfl⟩ : syracuseStep 2257649 = 1693237) B1693237
theorem B1503987 : Blo 1503572 1503987 := bstep (se 1 (by rfl) ⟨1127990, by rfl⟩ : syracuseStep 1503987 = 2255981) B2255981
theorem B1504003 : Blo 1503572 1504003 := bstep (se 1 (by rfl) ⟨1128002, by rfl⟩ : syracuseStep 1504003 = 2256005) B2256005
theorem B2257667 : Blo 1503572 2257667 := bstep (se 1 (by rfl) ⟨1693250, by rfl⟩ : syracuseStep 2257667 = 3386501) B3386501
theorem B5075729 : Blo 1503572 5075729 := bstep (se 2 (by rfl) ⟨1903398, by rfl⟩ : syracuseStep 5075729 = 3806797) B3806797
theorem B1504019 : Blo 1503572 1504019 := bstep (se 1 (by rfl) ⟨1128014, by rfl⟩ : syracuseStep 1504019 = 2256029) B2256029
theorem B2257697 : Blo 1503572 2257697 := bstep (se 2 (by rfl) ⟨846636, by rfl⟩ : syracuseStep 2257697 = 1693273) B1693273
theorem B3805987 : Blo 1503572 3805987 := bstep (se 1 (by rfl) ⟨2854490, by rfl⟩ : syracuseStep 3805987 = 5708981) B5708981
theorem B1504035 : Blo 1503572 1504035 := bstep (se 1 (by rfl) ⟨1128026, by rfl⟩ : syracuseStep 1504035 = 2256053) B2256053
theorem B2855729 : Blo 1503572 2855729 := bstep (se 2 (by rfl) ⟨1070898, by rfl⟩ : syracuseStep 2855729 = 2141797) B2141797
theorem B1504051 : Blo 1503572 1504051 := bstep (se 1 (by rfl) ⟨1128038, by rfl⟩ : syracuseStep 1504051 = 2256077) B2256077
theorem B2143027 : Blo 1503572 2143027 := bstep (se 1 (by rfl) ⟨1607270, by rfl⟩ : syracuseStep 2143027 = 3214541) B3214541
theorem B2257715 : Blo 1503572 2257715 := bstep (se 1 (by rfl) ⟨1693286, by rfl⟩ : syracuseStep 2257715 = 3386573) B3386573
theorem B1504067 : Blo 1503572 1504067 := bstep (se 1 (by rfl) ⟨1128050, by rfl⟩ : syracuseStep 1504067 = 2256101) B2256101
theorem B2257745 : Blo 1503572 2257745 := bstep (se 2 (by rfl) ⟨846654, by rfl⟩ : syracuseStep 2257745 = 1693309) B1693309
theorem B1504083 : Blo 1503572 1504083 := bstep (se 1 (by rfl) ⟨1128062, by rfl⟩ : syracuseStep 1504083 = 2256125) B2256125
theorem B1692499 : Blo 1503572 1692499 := bstep (se 1 (by rfl) ⟨1269374, by rfl⟩ : syracuseStep 1692499 = 2538749) B2538749
theorem B1504099 : Blo 1503572 1504099 := bstep (se 1 (by rfl) ⟨1128074, by rfl⟩ : syracuseStep 1504099 = 2256149) B2256149
theorem B2257763 : Blo 1503572 2257763 := bstep (se 1 (by rfl) ⟨1693322, by rfl⟩ : syracuseStep 2257763 = 3386645) B3386645
theorem B1504115 : Blo 1503572 1504115 := bstep (se 1 (by rfl) ⟨1128086, by rfl⟩ : syracuseStep 1504115 = 2256173) B2256173
theorem B2257793 : Blo 1503572 2257793 := bstep (se 2 (by rfl) ⟨846672, by rfl⟩ : syracuseStep 2257793 = 1693345) B1693345
theorem B1504131 : Blo 1503572 1504131 := bstep (se 1 (by rfl) ⟨1128098, by rfl⟩ : syracuseStep 1504131 = 2256197) B2256197
theorem B1504147 : Blo 1503572 1504147 := bstep (se 1 (by rfl) ⟨1128110, by rfl⟩ : syracuseStep 1504147 = 2256221) B2256221
theorem B2257811 : Blo 1503572 2257811 := bstep (se 1 (by rfl) ⟨1693358, by rfl⟩ : syracuseStep 2257811 = 3386717) B3386717
theorem B1504163 : Blo 1503572 1504163 := bstep (se 1 (by rfl) ⟨1128122, by rfl⟩ : syracuseStep 1504163 = 2256245) B2256245
theorem B3806129 : Blo 1503572 3806129 := bstep (se 2 (by rfl) ⟨1427298, by rfl⟩ : syracuseStep 3806129 = 2854597) B2854597
theorem B2257841 : Blo 1503572 2257841 := bstep (se 2 (by rfl) ⟨846690, by rfl⟩ : syracuseStep 2257841 = 1693381) B1693381
theorem B1504179 : Blo 1503572 1504179 := bstep (se 1 (by rfl) ⟨1128134, by rfl⟩ : syracuseStep 1504179 = 2256269) B2256269
theorem B1504195 : Blo 1503572 1504195 := bstep (se 1 (by rfl) ⟨1128146, by rfl⟩ : syracuseStep 1504195 = 2256293) B2256293
theorem B2257859 : Blo 1503572 2257859 := bstep (se 1 (by rfl) ⟨1693394, by rfl⟩ : syracuseStep 2257859 = 3386789) B3386789
theorem B1504211 : Blo 1503572 1504211 := bstep (se 1 (by rfl) ⟨1128158, by rfl⟩ : syracuseStep 1504211 = 2256317) B2256317
theorem B1504227 : Blo 1503572 1504227 := bstep (se 1 (by rfl) ⟨1128170, by rfl⟩ : syracuseStep 1504227 = 2256341) B2256341
theorem B1692643 : Blo 1503572 1692643 := bstep (se 1 (by rfl) ⟨1269482, by rfl⟩ : syracuseStep 1692643 = 2538965) B2538965
theorem B2257889 : Blo 1503572 2257889 := bstep (se 2 (by rfl) ⟨846708, by rfl⟩ : syracuseStep 2257889 = 1693417) B1693417
theorem B1504243 : Blo 1503572 1504243 := bstep (se 1 (by rfl) ⟨1128182, by rfl⟩ : syracuseStep 1504243 = 2256365) B2256365
theorem B2257907 : Blo 1503572 2257907 := bstep (se 1 (by rfl) ⟨1693430, by rfl⟩ : syracuseStep 2257907 = 3386861) B3386861
theorem B1504259 : Blo 1503572 1504259 := bstep (se 1 (by rfl) ⟨1128194, by rfl⟩ : syracuseStep 1504259 = 2256389) B2256389
theorem B1504275 : Blo 1503572 1504275 := bstep (se 1 (by rfl) ⟨1128206, by rfl⟩ : syracuseStep 1504275 = 2256413) B2256413
theorem B2257937 : Blo 1503572 2257937 := bstep (se 2 (by rfl) ⟨846726, by rfl⟩ : syracuseStep 2257937 = 1693453) B1693453
theorem B1504291 : Blo 1503572 1504291 := bstep (se 1 (by rfl) ⟨1128218, by rfl⟩ : syracuseStep 1504291 = 2256437) B2256437
theorem B2257955 : Blo 1503572 2257955 := bstep (se 1 (by rfl) ⟨1693466, by rfl⟩ : syracuseStep 2257955 = 3386933) B3386933
theorem B1504307 : Blo 1503572 1504307 := bstep (se 1 (by rfl) ⟨1128230, by rfl⟩ : syracuseStep 1504307 = 2256461) B2256461
theorem B2257985 : Blo 1503572 2257985 := bstep (se 2 (by rfl) ⟨846744, by rfl⟩ : syracuseStep 2257985 = 1693489) B1693489
theorem B1504323 : Blo 1503572 1504323 := bstep (se 1 (by rfl) ⟨1128242, by rfl⟩ : syracuseStep 1504323 = 2256485) B2256485
theorem B1504339 : Blo 1503572 1504339 := bstep (se 1 (by rfl) ⟨1128254, by rfl⟩ : syracuseStep 1504339 = 2256509) B2256509
theorem B2258003 : Blo 1503572 2258003 := bstep (se 1 (by rfl) ⟨1693502, by rfl⟩ : syracuseStep 2258003 = 3387005) B3387005
theorem B1504355 : Blo 1503572 1504355 := bstep (se 1 (by rfl) ⟨1128266, by rfl⟩ : syracuseStep 1504355 = 2256533) B2256533
theorem B2258033 : Blo 1503572 2258033 := bstep (se 2 (by rfl) ⟨846762, by rfl⟩ : syracuseStep 2258033 = 1693525) B1693525
theorem B1504371 : Blo 1503572 1504371 := bstep (se 1 (by rfl) ⟨1128278, by rfl⟩ : syracuseStep 1504371 = 2256557) B2256557
theorem B1692787 : Blo 1503572 1692787 := bstep (se 1 (by rfl) ⟨1269590, by rfl⟩ : syracuseStep 1692787 = 2539181) B2539181
theorem B1504387 : Blo 1503572 1504387 := bstep (se 1 (by rfl) ⟨1128290, by rfl⟩ : syracuseStep 1504387 = 2256581) B2256581
theorem B2143363 : Blo 1503572 2143363 := bstep (se 1 (by rfl) ⟨1607522, by rfl⟩ : syracuseStep 2143363 = 3215045) B3215045
theorem B2258051 : Blo 1503572 2258051 := bstep (se 1 (by rfl) ⟨1693538, by rfl⟩ : syracuseStep 2258051 = 3387077) B3387077
theorem B1504403 : Blo 1503572 1504403 := bstep (se 1 (by rfl) ⟨1128302, by rfl⟩ : syracuseStep 1504403 = 2256605) B2256605
theorem B2258081 : Blo 1503572 2258081 := bstep (se 2 (by rfl) ⟨846780, by rfl⟩ : syracuseStep 2258081 = 1693561) B1693561
theorem B1504419 : Blo 1503572 1504419 := bstep (se 1 (by rfl) ⟨1128314, by rfl⟩ : syracuseStep 1504419 = 2256629) B2256629
theorem B1504435 : Blo 1503572 1504435 := bstep (se 1 (by rfl) ⟨1128326, by rfl⟩ : syracuseStep 1504435 = 2256653) B2256653
theorem B2258099 : Blo 1503572 2258099 := bstep (se 1 (by rfl) ⟨1693574, by rfl⟩ : syracuseStep 2258099 = 3387149) B3387149
theorem B1504451 : Blo 1503572 1504451 := bstep (se 1 (by rfl) ⟨1128338, by rfl⟩ : syracuseStep 1504451 = 2256677) B2256677
theorem B2856131 : Blo 1503572 2856131 := bstep (se 1 (by rfl) ⟨2142098, by rfl⟩ : syracuseStep 2856131 = 4284197) B4284197
theorem B2258129 : Blo 1503572 2258129 := bstep (se 2 (by rfl) ⟨846798, by rfl⟩ : syracuseStep 2258129 = 1693597) B1693597
theorem B1504467 : Blo 1503572 1504467 := bstep (se 1 (by rfl) ⟨1128350, by rfl⟩ : syracuseStep 1504467 = 2256701) B2256701
theorem B1504483 : Blo 1503572 1504483 := bstep (se 1 (by rfl) ⟨1128362, by rfl⟩ : syracuseStep 1504483 = 2256725) B2256725
theorem B2258147 : Blo 1503572 2258147 := bstep (se 1 (by rfl) ⟨1693610, by rfl⟩ : syracuseStep 2258147 = 3387221) B3387221
theorem B5494001 : Blo 1503572 5494001 := bstep (se 2 (by rfl) ⟨2060250, by rfl⟩ : syracuseStep 5494001 = 4120501) B4120501
theorem B1504499 : Blo 1503572 1504499 := bstep (se 1 (by rfl) ⟨1128374, by rfl⟩ : syracuseStep 1504499 = 2256749) B2256749
theorem B1504515 : Blo 1503572 1504515 := bstep (se 1 (by rfl) ⟨1128386, by rfl⟩ : syracuseStep 1504515 = 2256773) B2256773
theorem B1692931 : Blo 1503572 1692931 := bstep (se 1 (by rfl) ⟨1269698, by rfl⟩ : syracuseStep 1692931 = 2539397) B2539397
theorem B1504531 : Blo 1503572 1504531 := bstep (se 1 (by rfl) ⟨1128398, by rfl⟩ : syracuseStep 1504531 = 2256797) B2256797
theorem B1504547 : Blo 1503572 1504547 := bstep (se 1 (by rfl) ⟨1128410, by rfl⟩ : syracuseStep 1504547 = 2256821) B2256821
theorem B5076269 : Blo 1503572 5076269 := bstep (se 3 (by rfl) ⟨951800, by rfl⟩ : syracuseStep 5076269 = 1903601) B1903601
theorem B1504563 : Blo 1503572 1504563 := bstep (se 1 (by rfl) ⟨1128422, by rfl⟩ : syracuseStep 1504563 = 2256845) B2256845
theorem B1504579 : Blo 1503572 1504579 := bstep (se 1 (by rfl) ⟨1128434, by rfl⟩ : syracuseStep 1504579 = 2256869) B2256869
theorem B1504595 : Blo 1503572 1504595 := bstep (se 1 (by rfl) ⟨1128446, by rfl⟩ : syracuseStep 1504595 = 2256893) B2256893
theorem B5076323 : Blo 1503572 5076323 := bstep (se 1 (by rfl) ⟨3807242, by rfl⟩ : syracuseStep 5076323 = 7614485) B7614485
theorem B1504611 : Blo 1503572 1504611 := bstep (se 1 (by rfl) ⟨1128458, by rfl⟩ : syracuseStep 1504611 = 2256917) B2256917
theorem B5715299 : Blo 1503572 5715299 := bstep (se 1 (by rfl) ⟨4286474, by rfl⟩ : syracuseStep 5715299 = 8572949) B8572949
theorem B21976433 : Blo 1503572 21976433 := bstep (se 2 (by rfl) ⟨8241162, by rfl⟩ : syracuseStep 21976433 = 16482325) B16482325
theorem B1504627 : Blo 1503572 1504627 := bstep (se 1 (by rfl) ⟨1128470, by rfl⟩ : syracuseStep 1504627 = 2256941) B2256941
theorem B1504643 : Blo 1503572 1504643 := bstep (se 1 (by rfl) ⟨1128482, by rfl⟩ : syracuseStep 1504643 = 2256965) B2256965
theorem B5420429 : Blo 1503572 5420429 := bstep (se 3 (by rfl) ⟨1016330, by rfl⟩ : syracuseStep 5420429 = 2032661) B2032661
theorem B1504659 : Blo 1503572 1504659 := bstep (se 1 (by rfl) ⟨1128494, by rfl⟩ : syracuseStep 1504659 = 2256989) B2256989
theorem B1693075 : Blo 1503572 1693075 := bstep (se 1 (by rfl) ⟨1269806, by rfl⟩ : syracuseStep 1693075 = 2539613) B2539613
theorem B1504675 : Blo 1503572 1504675 := bstep (se 1 (by rfl) ⟨1128506, by rfl⟩ : syracuseStep 1504675 = 2257013) B2257013
theorem B1504691 : Blo 1503572 1504691 := bstep (se 1 (by rfl) ⟨1128518, by rfl⟩ : syracuseStep 1504691 = 2257037) B2257037
theorem B1807795 : Blo 1503572 1807795 := bstep (se 1 (by rfl) ⟨1355846, by rfl⟩ : syracuseStep 1807795 = 2711693) B2711693
theorem B1504707 : Blo 1503572 1504707 := bstep (se 1 (by rfl) ⟨1128530, by rfl⟩ : syracuseStep 1504707 = 2257061) B2257061
theorem B10991045 : Blo 1503572 10991045 := bstep (se 4 (by rfl) ⟨1030410, by rfl⟩ : syracuseStep 10991045 = 2060821) B2060821
theorem B1504723 : Blo 1503572 1504723 := bstep (se 1 (by rfl) ⟨1128542, by rfl⟩ : syracuseStep 1504723 = 2257085) B2257085
theorem B1504739 : Blo 1503572 1504739 := bstep (se 1 (by rfl) ⟨1128554, by rfl⟩ : syracuseStep 1504739 = 2257109) B2257109
theorem B1504755 : Blo 1503572 1504755 := bstep (se 1 (by rfl) ⟨1128566, by rfl⟩ : syracuseStep 1504755 = 2257133) B2257133
theorem B1504771 : Blo 1503572 1504771 := bstep (se 1 (by rfl) ⟨1128578, by rfl⟩ : syracuseStep 1504771 = 2257157) B2257157
theorem B4822541 : Blo 1503572 4822541 := bstep (se 3 (by rfl) ⟨904226, by rfl⟩ : syracuseStep 4822541 = 1808453) B1808453
theorem B1504787 : Blo 1503572 1504787 := bstep (se 1 (by rfl) ⟨1128590, by rfl⟩ : syracuseStep 1504787 = 2257181) B2257181
theorem B1504803 : Blo 1503572 1504803 := bstep (se 1 (by rfl) ⟨1128602, by rfl⟩ : syracuseStep 1504803 = 2257205) B2257205
theorem B1693219 : Blo 1503572 1693219 := bstep (se 1 (by rfl) ⟨1269914, by rfl⟩ : syracuseStep 1693219 = 2539829) B2539829
theorem B1504819 : Blo 1503572 1504819 := bstep (se 1 (by rfl) ⟨1128614, by rfl⟩ : syracuseStep 1504819 = 2257229) B2257229
theorem B1504835 : Blo 1503572 1504835 := bstep (se 1 (by rfl) ⟨1128626, by rfl⟩ : syracuseStep 1504835 = 2257253) B2257253
theorem B1504851 : Blo 1503572 1504851 := bstep (se 1 (by rfl) ⟨1128638, by rfl⟩ : syracuseStep 1504851 = 2257277) B2257277
theorem B1504867 : Blo 1503572 1504867 := bstep (se 1 (by rfl) ⟨1128650, by rfl⟩ : syracuseStep 1504867 = 2257301) B2257301
theorem B5076593 : Blo 1503572 5076593 := bstep (se 2 (by rfl) ⟨1903722, by rfl⟩ : syracuseStep 5076593 = 3807445) B3807445
theorem B1504883 : Blo 1503572 1504883 := bstep (se 1 (by rfl) ⟨1128662, by rfl⟩ : syracuseStep 1504883 = 2257325) B2257325
theorem B1504899 : Blo 1503572 1504899 := bstep (se 1 (by rfl) ⟨1128674, by rfl⟩ : syracuseStep 1504899 = 2257349) B2257349
theorem B4822669 : Blo 1503572 4822669 := bstep (se 3 (by rfl) ⟨904250, by rfl⟩ : syracuseStep 4822669 = 1808501) B1808501
theorem B1504915 : Blo 1503572 1504915 := bstep (se 1 (by rfl) ⟨1128686, by rfl⟩ : syracuseStep 1504915 = 2257373) B2257373
theorem B1504931 : Blo 1503572 1504931 := bstep (se 1 (by rfl) ⟨1128698, by rfl⟩ : syracuseStep 1504931 = 2257397) B2257397
theorem B1504947 : Blo 1503572 1504947 := bstep (se 1 (by rfl) ⟨1128710, by rfl⟩ : syracuseStep 1504947 = 2257421) B2257421
theorem B1693363 : Blo 1503572 1693363 := bstep (se 1 (by rfl) ⟨1270022, by rfl⟩ : syracuseStep 1693363 = 2540045) B2540045
theorem B1504963 : Blo 1503572 1504963 := bstep (se 1 (by rfl) ⟨1128722, by rfl⟩ : syracuseStep 1504963 = 2257445) B2257445
theorem B1504979 : Blo 1503572 1504979 := bstep (se 1 (by rfl) ⟨1128734, by rfl⟩ : syracuseStep 1504979 = 2257469) B2257469
theorem B1504995 : Blo 1503572 1504995 := bstep (se 1 (by rfl) ⟨1128746, by rfl⟩ : syracuseStep 1504995 = 2257493) B2257493
theorem B1505011 : Blo 1503572 1505011 := bstep (se 1 (by rfl) ⟨1128758, by rfl⟩ : syracuseStep 1505011 = 2257517) B2257517
theorem B1505027 : Blo 1503572 1505027 := bstep (se 1 (by rfl) ⟨1128770, by rfl⟩ : syracuseStep 1505027 = 2257541) B2257541
theorem B1505043 : Blo 1503572 1505043 := bstep (se 1 (by rfl) ⟨1128782, by rfl⟩ : syracuseStep 1505043 = 2257565) B2257565
theorem B1505059 : Blo 1503572 1505059 := bstep (se 1 (by rfl) ⟨1128794, by rfl⟩ : syracuseStep 1505059 = 2257589) B2257589
theorem B1505075 : Blo 1503572 1505075 := bstep (se 1 (by rfl) ⟨1128806, by rfl⟩ : syracuseStep 1505075 = 2257613) B2257613
theorem B1505091 : Blo 1503572 1505091 := bstep (se 1 (by rfl) ⟨1128818, by rfl⟩ : syracuseStep 1505091 = 2257637) B2257637
theorem B9639749 : Blo 1503572 9639749 := bstep (se 4 (by rfl) ⟨903726, by rfl⟩ : syracuseStep 9639749 = 1807453) B1807453
theorem B1693507 : Blo 1503572 1693507 := bstep (se 1 (by rfl) ⟨1270130, by rfl⟩ : syracuseStep 1693507 = 2540261) B2540261
theorem B1505107 : Blo 1503572 1505107 := bstep (se 1 (by rfl) ⟨1128830, by rfl⟩ : syracuseStep 1505107 = 2257661) B2257661
theorem B1505123 : Blo 1503572 1505123 := bstep (se 1 (by rfl) ⟨1128842, by rfl⟩ : syracuseStep 1505123 = 2257685) B2257685
theorem B1505139 : Blo 1503572 1505139 := bstep (se 1 (by rfl) ⟨1128854, by rfl⟩ : syracuseStep 1505139 = 2257709) B2257709
theorem B2537345 : Blo 1503572 2537345 := bstep (se 2 (by rfl) ⟨951504, by rfl⟩ : syracuseStep 2537345 = 1903009) B1903009
theorem B1505155 : Blo 1503572 1505155 := bstep (se 1 (by rfl) ⟨1128866, by rfl⟩ : syracuseStep 1505155 = 2257733) B2257733
theorem B8566661 : Blo 1503572 8566661 := bstep (se 4 (by rfl) ⟨803124, by rfl⟩ : syracuseStep 8566661 = 1606249) B1606249
theorem B3807121 : Blo 1503572 3807121 := bstep (se 2 (by rfl) ⟨1427670, by rfl⟩ : syracuseStep 3807121 = 2855341) B2855341
theorem B1505171 : Blo 1503572 1505171 := bstep (se 1 (by rfl) ⟨1128878, by rfl⟩ : syracuseStep 1505171 = 2257757) B2257757
theorem B1505187 : Blo 1503572 1505187 := bstep (se 1 (by rfl) ⟨1128890, by rfl⟩ : syracuseStep 1505187 = 2257781) B2257781
theorem B1505203 : Blo 1503572 1505203 := bstep (se 1 (by rfl) ⟨1128902, by rfl⟩ : syracuseStep 1505203 = 2257805) B2257805
theorem B1505219 : Blo 1503572 1505219 := bstep (se 1 (by rfl) ⟨1128914, by rfl⟩ : syracuseStep 1505219 = 2257829) B2257829
theorem B1505235 : Blo 1503572 1505235 := bstep (se 1 (by rfl) ⟨1128926, by rfl⟩ : syracuseStep 1505235 = 2257853) B2257853
theorem B36591587 : Blo 1503572 36591587 := bstep (se 1 (by rfl) ⟨27443690, by rfl⟩ : syracuseStep 36591587 = 54887381) B54887381
theorem B1505251 : Blo 1503572 1505251 := bstep (se 1 (by rfl) ⟨1128938, by rfl⟩ : syracuseStep 1505251 = 2257877) B2257877
theorem B5715953 : Blo 1503572 5715953 := bstep (se 2 (by rfl) ⟨2143482, by rfl⟩ : syracuseStep 5715953 = 4286965) B4286965
theorem B1505267 : Blo 1503572 1505267 := bstep (se 1 (by rfl) ⟨1128950, by rfl⟩ : syracuseStep 1505267 = 2257901) B2257901
theorem B2537473 : Blo 1503572 2537473 := bstep (se 2 (by rfl) ⟨951552, by rfl⟩ : syracuseStep 2537473 = 1903105) B1903105
theorem B1505283 : Blo 1503572 1505283 := bstep (se 1 (by rfl) ⟨1128962, by rfl⟩ : syracuseStep 1505283 = 2257925) B2257925
theorem B1505299 : Blo 1503572 1505299 := bstep (se 1 (by rfl) ⟨1128974, by rfl⟩ : syracuseStep 1505299 = 2257949) B2257949
theorem B2537507 : Blo 1503572 2537507 := bstep (se 1 (by rfl) ⟨1903130, by rfl⟩ : syracuseStep 2537507 = 3806261) B3806261
theorem B1505315 : Blo 1503572 1505315 := bstep (se 1 (by rfl) ⟨1128986, by rfl⟩ : syracuseStep 1505315 = 2257973) B2257973
theorem B6862897 : Blo 1503572 6862897 := bstep (se 2 (by rfl) ⟨2573586, by rfl⟩ : syracuseStep 6862897 = 5147173) B5147173
theorem B1505331 : Blo 1503572 1505331 := bstep (se 1 (by rfl) ⟨1128998, by rfl⟩ : syracuseStep 1505331 = 2257997) B2257997
theorem B2857027 : Blo 1503572 2857027 := bstep (se 1 (by rfl) ⟨2142770, by rfl⟩ : syracuseStep 2857027 = 4285541) B4285541
theorem B1505347 : Blo 1503572 1505347 := bstep (se 1 (by rfl) ⟨1129010, by rfl⟩ : syracuseStep 1505347 = 2258021) B2258021
theorem B1505363 : Blo 1503572 1505363 := bstep (se 1 (by rfl) ⟨1129022, by rfl⟩ : syracuseStep 1505363 = 2258045) B2258045
theorem B1505379 : Blo 1503572 1505379 := bstep (se 1 (by rfl) ⟨1129034, by rfl⟩ : syracuseStep 1505379 = 2258069) B2258069
theorem B1505395 : Blo 1503572 1505395 := bstep (se 1 (by rfl) ⟨1129046, by rfl⟩ : syracuseStep 1505395 = 2258093) B2258093
theorem B1505411 : Blo 1503572 1505411 := bstep (se 1 (by rfl) ⟨1129058, by rfl⟩ : syracuseStep 1505411 = 2258117) B2258117
theorem B5077133 : Blo 1503572 5077133 := bstep (se 3 (by rfl) ⟨951962, by rfl⟩ : syracuseStep 5077133 = 1903925) B1903925
theorem B1505427 : Blo 1503572 1505427 := bstep (se 1 (by rfl) ⟨1129070, by rfl⟩ : syracuseStep 1505427 = 2258141) B2258141
theorem B2537635 : Blo 1503572 2537635 := bstep (se 1 (by rfl) ⟨1903226, by rfl⟩ : syracuseStep 2537635 = 3806453) B3806453
theorem B3807395 : Blo 1503572 3807395 := bstep (se 1 (by rfl) ⟨2855546, by rfl⟩ : syracuseStep 3807395 = 5711093) B5711093
theorem B1505443 : Blo 1503572 1505443 := bstep (se 1 (by rfl) ⟨1129082, by rfl⟩ : syracuseStep 1505443 = 2258165) B2258165
theorem B5077187 : Blo 1503572 5077187 := bstep (se 1 (by rfl) ⟨3807890, by rfl⟩ : syracuseStep 5077187 = 7615781) B7615781
theorem B2857187 : Blo 1503572 2857187 := bstep (se 1 (by rfl) ⟨2142890, by rfl⟩ : syracuseStep 2857187 = 4285781) B4285781
theorem B18290929 : Blo 1503572 18290929 := bstep (se 2 (by rfl) ⟨6859098, by rfl⟩ : syracuseStep 18290929 = 13718197) B13718197
theorem B7616753 : Blo 1503572 7616753 := bstep (se 2 (by rfl) ⟨2856282, by rfl⟩ : syracuseStep 7616753 = 5712565) B5712565
theorem B2537777 : Blo 1503572 2537777 := bstep (se 2 (by rfl) ⟨951666, by rfl⟩ : syracuseStep 2537777 = 1903333) B1903333
theorem B8567117 : Blo 1503572 8567117 := bstep (se 3 (by rfl) ⟨1606334, by rfl⟩ : syracuseStep 8567117 = 3212669) B3212669
theorem B3807587 : Blo 1503572 3807587 := bstep (se 1 (by rfl) ⟨2855690, by rfl⟩ : syracuseStep 3807587 = 5711381) B5711381
theorem B1882483 : Blo 1503572 1882483 := bstep (se 1 (by rfl) ⟨1411862, by rfl⟩ : syracuseStep 1882483 = 2823725) B2823725
theorem B2537905 : Blo 1503572 2537905 := bstep (se 2 (by rfl) ⟨951714, by rfl⟩ : syracuseStep 2537905 = 1903429) B1903429
theorem B5077457 : Blo 1503572 5077457 := bstep (se 2 (by rfl) ⟨1904046, by rfl⟩ : syracuseStep 5077457 = 3808093) B3808093
theorem B2537939 : Blo 1503572 2537939 := bstep (se 1 (by rfl) ⟨1903454, by rfl⟩ : syracuseStep 2537939 = 3806909) B3806909
theorem B11418083 : Blo 1503572 11418083 := bstep (se 1 (by rfl) ⟨8563562, by rfl⟩ : syracuseStep 11418083 = 17127125) B17127125
theorem B5421539 : Blo 1503572 5421539 := bstep (se 1 (by rfl) ⟨4066154, by rfl⟩ : syracuseStep 5421539 = 8132309) B8132309
theorem B4282865 : Blo 1503572 4282865 := bstep (se 2 (by rfl) ⟨1606074, by rfl⟩ : syracuseStep 4282865 = 3212149) B3212149
theorem B6429233 : Blo 1503572 6429233 := bstep (se 2 (by rfl) ⟨2410962, by rfl⟩ : syracuseStep 6429233 = 4821925) B4821925
theorem B2538067 : Blo 1503572 2538067 := bstep (se 1 (by rfl) ⟨1903550, by rfl⟩ : syracuseStep 2538067 = 3807101) B3807101
theorem B3431011 : Blo 1503572 3431011 := bstep (se 1 (by rfl) ⟨2573258, by rfl⟩ : syracuseStep 3431011 = 5146517) B5146517
theorem B4340387 : Blo 1503572 4340387 := bstep (se 1 (by rfl) ⟨3255290, by rfl⟩ : syracuseStep 4340387 = 6510581) B6510581
theorem B4283057 : Blo 1503572 4283057 := bstep (se 2 (by rfl) ⟨1606146, by rfl⟩ : syracuseStep 4283057 = 3212293) B3212293
theorem B2538209 : Blo 1503572 2538209 := bstep (se 2 (by rfl) ⟨951828, by rfl⟩ : syracuseStep 2538209 = 1903657) B1903657
theorem B2538337 : Blo 1503572 2538337 := bstep (se 2 (by rfl) ⟨951876, by rfl⟩ : syracuseStep 2538337 = 1903753) B1903753
theorem B2538371 : Blo 1503572 2538371 := bstep (se 1 (by rfl) ⟨1903778, by rfl⟩ : syracuseStep 2538371 = 3807557) B3807557
theorem B5077997 : Blo 1503572 5077997 := bstep (se 3 (by rfl) ⟨952124, by rfl⟩ : syracuseStep 5077997 = 1904249) B1904249
theorem B2644993 : Blo 1503572 2644993 := bstep (se 2 (by rfl) ⟨991872, by rfl⟩ : syracuseStep 2644993 = 1983745) B1983745
theorem B2538499 : Blo 1503572 2538499 := bstep (se 1 (by rfl) ⟨1903874, by rfl⟩ : syracuseStep 2538499 = 3807749) B3807749
theorem B5078051 : Blo 1503572 5078051 := bstep (se 1 (by rfl) ⟨3808538, by rfl⟩ : syracuseStep 5078051 = 7617077) B7617077
theorem B2538641 : Blo 1503572 2538641 := bstep (se 2 (by rfl) ⟨951990, by rfl⟩ : syracuseStep 2538641 = 1903981) B1903981
theorem B6429901 : Blo 1503572 6429901 := bstep (se 3 (by rfl) ⟨1205606, by rfl⟩ : syracuseStep 6429901 = 2411213) B2411213
theorem B2538769 : Blo 1503572 2538769 := bstep (se 2 (by rfl) ⟨952038, by rfl⟩ : syracuseStep 2538769 = 1904077) B1904077
theorem B3808529 : Blo 1503572 3808529 := bstep (se 2 (by rfl) ⟨1428198, by rfl⟩ : syracuseStep 3808529 = 2856397) B2856397
theorem B5078321 : Blo 1503572 5078321 := bstep (se 2 (by rfl) ⟨1904370, by rfl⟩ : syracuseStep 5078321 = 3808741) B3808741
theorem B2538803 : Blo 1503572 2538803 := bstep (se 1 (by rfl) ⟨1904102, by rfl⟩ : syracuseStep 2538803 = 3808205) B3808205
theorem B3808579 : Blo 1503572 3808579 := bstep (se 1 (by rfl) ⟨2856434, by rfl⟩ : syracuseStep 3808579 = 5712869) B5712869
theorem B5496227 : Blo 1503572 5496227 := bstep (se 1 (by rfl) ⟨4122170, by rfl⟩ : syracuseStep 5496227 = 8244341) B8244341
theorem B2538931 : Blo 1503572 2538931 := bstep (se 1 (by rfl) ⟨1904198, by rfl⟩ : syracuseStep 2538931 = 3808397) B3808397
theorem B19553717 : Blo 1503572 19553717 := bstep (se 5 (by rfl) ⟨916580, by rfl⟩ : syracuseStep 19553717 = 1833161) B1833161
theorem B3808721 : Blo 1503572 3808721 := bstep (se 2 (by rfl) ⟨1428270, by rfl⟩ : syracuseStep 3808721 = 2856541) B2856541
theorem B2539073 : Blo 1503572 2539073 := bstep (se 2 (by rfl) ⟨952152, by rfl⟩ : syracuseStep 2539073 = 1904305) B1904305
theorem B4284049 : Blo 1503572 4284049 := bstep (se 2 (by rfl) ⟨1606518, by rfl⟩ : syracuseStep 4284049 = 3213037) B3213037
theorem B7618211 : Blo 1503572 7618211 := bstep (se 1 (by rfl) ⟨5713658, by rfl⟩ : syracuseStep 7618211 = 11427317) B11427317
theorem B2539201 : Blo 1503572 2539201 := bstep (se 2 (by rfl) ⟨952200, by rfl⟩ : syracuseStep 2539201 = 1904401) B1904401
theorem B2539235 : Blo 1503572 2539235 := bstep (se 1 (by rfl) ⟨1904426, by rfl⟩ : syracuseStep 2539235 = 3808853) B3808853
theorem B9641699 : Blo 1503572 9641699 := bstep (se 1 (by rfl) ⟨7231274, by rfl⟩ : syracuseStep 9641699 = 14462549) B14462549
theorem B6430499 : Blo 1503572 6430499 := bstep (se 1 (by rfl) ⟨4822874, by rfl⟩ : syracuseStep 6430499 = 9645749) B9645749
theorem B5078861 : Blo 1503572 5078861 := bstep (se 3 (by rfl) ⟨952286, by rfl⟩ : syracuseStep 5078861 = 1904573) B1904573
theorem B2981713 : Blo 1503572 2981713 := bstep (se 2 (by rfl) ⟨1118142, by rfl⟩ : syracuseStep 2981713 = 2236285) B2236285
theorem B2539363 : Blo 1503572 2539363 := bstep (se 1 (by rfl) ⟨1904522, by rfl⟩ : syracuseStep 2539363 = 3809045) B3809045
theorem B3383153 : Blo 1503572 3383153 := bstep (se 2 (by rfl) ⟨1268682, by rfl⟩ : syracuseStep 3383153 = 2537365) B2537365
theorem B3383171 : Blo 1503572 3383171 := bstep (se 1 (by rfl) ⟨2537378, by rfl⟩ : syracuseStep 3383171 = 5074757) B5074757
theorem B5078915 : Blo 1503572 5078915 := bstep (se 1 (by rfl) ⟨3809186, by rfl⟩ : syracuseStep 5078915 = 7618373) B7618373
theorem B4284323 : Blo 1503572 4284323 := bstep (se 1 (by rfl) ⟨3213242, by rfl⟩ : syracuseStep 4284323 = 6426485) B6426485
theorem B2572273 : Blo 1503572 2572273 := bstep (se 2 (by rfl) ⟨964602, by rfl⟩ : syracuseStep 2572273 = 1929205) B1929205
theorem B2539505 : Blo 1503572 2539505 := bstep (se 2 (by rfl) ⟨952314, by rfl⟩ : syracuseStep 2539505 = 1904629) B1904629
theorem B3383297 : Blo 1503572 3383297 := bstep (se 2 (by rfl) ⟨1268736, by rfl⟩ : syracuseStep 3383297 = 2537473) B2537473
theorem B14106629 : Blo 1503572 14106629 := bstep (se 4 (by rfl) ⟨1322496, by rfl⟩ : syracuseStep 14106629 = 2644993) B2644993
theorem B24404003 : Blo 1503572 24404003 := bstep (se 1 (by rfl) ⟨18303002, by rfl⟩ : syracuseStep 24404003 = 36606005) B36606005
theorem B41189411 : Blo 1503572 41189411 := bstep (se 1 (by rfl) ⟨30892058, by rfl⟩ : syracuseStep 41189411 = 61784117) B61784117
theorem B9150529 : Blo 1503572 9150529 := bstep (se 2 (by rfl) ⟨3431448, by rfl⟩ : syracuseStep 9150529 = 6862897) B6862897
theorem B2711641 : Blo 1503572 2711641 := bstep (se 2 (by rfl) ⟨1016865, by rfl⟩ : syracuseStep 2711641 = 2033731) B2033731
theorem B3809369 : Blo 1503572 3809369 := bstep (se 2 (by rfl) ⟨1428513, by rfl⟩ : syracuseStep 3809369 = 2857027) B2857027
theorem B1605835 : Blo 1503572 1605835 := bstep (se 1 (by rfl) ⟨1204376, by rfl⟩ : syracuseStep 1605835 = 2408753) B2408753
theorem B3383513 : Blo 1503572 3383513 := bstep (se 2 (by rfl) ⟨1268817, by rfl⟩ : syracuseStep 3383513 = 2537635) B2537635
theorem B3383603 : Blo 1503572 3383603 := bstep (se 1 (by rfl) ⟨2537702, by rfl⟩ : syracuseStep 3383603 = 5075405) B5075405
theorem B5079347 : Blo 1503572 5079347 := bstep (se 1 (by rfl) ⟨3809510, by rfl⟩ : syracuseStep 5079347 = 7619021) B7619021
theorem B24387905 : Blo 1503572 24387905 := bstep (se 2 (by rfl) ⟨9145464, by rfl⟩ : syracuseStep 24387905 = 18290929) B18290929
theorem B3383639 : Blo 1503572 3383639 := bstep (se 1 (by rfl) ⟨2537729, by rfl⟩ : syracuseStep 3383639 = 5075459) B5075459
theorem B2539991 : Blo 1503572 2539991 := bstep (se 1 (by rfl) ⟨1904993, by rfl⟩ : syracuseStep 2539991 = 3809987) B3809987
theorem B3383819 : Blo 1503572 3383819 := bstep (se 1 (by rfl) ⟨2537864, by rfl⟩ : syracuseStep 3383819 = 5075729) B5075729
theorem B3383873 : Blo 1503572 3383873 := bstep (se 2 (by rfl) ⟨1268952, by rfl⟩ : syracuseStep 3383873 = 2537905) B2537905
theorem B5079617 : Blo 1503572 5079617 := bstep (se 2 (by rfl) ⟨1904856, by rfl⟩ : syracuseStep 5079617 = 3809713) B3809713
theorem B2540119 : Blo 1503572 2540119 := bstep (se 1 (by rfl) ⟨1905089, by rfl⟩ : syracuseStep 2540119 = 3810179) B3810179
theorem B3211969 : Blo 1503572 3211969 := bstep (se 2 (by rfl) ⟨1204488, by rfl⟩ : syracuseStep 3211969 = 2408977) B2408977
theorem B7619345 : Blo 1503572 7619345 := bstep (se 2 (by rfl) ⟨2857254, by rfl⟩ : syracuseStep 7619345 = 5714509) B5714509
theorem B3384089 : Blo 1503572 3384089 := bstep (se 2 (by rfl) ⟨1269033, by rfl⟩ : syracuseStep 3384089 = 2538067) B2538067
theorem B9634625 : Blo 1503572 9634625 := bstep (se 2 (by rfl) ⟨3612984, by rfl⟩ : syracuseStep 9634625 = 7225969) B7225969
theorem B3384179 : Blo 1503572 3384179 := bstep (se 1 (by rfl) ⟨2538134, by rfl⟩ : syracuseStep 3384179 = 5076269) B5076269
theorem B2712449 : Blo 1503572 2712449 := bstep (se 2 (by rfl) ⟨1017168, by rfl⟩ : syracuseStep 2712449 = 2034337) B2034337
theorem B10290071 : Blo 1503572 10290071 := bstep (se 1 (by rfl) ⟨7717553, by rfl⟩ : syracuseStep 10290071 = 15435107) B15435107
theorem B3384215 : Blo 1503572 3384215 := bstep (se 1 (by rfl) ⟨2538161, by rfl⟩ : syracuseStep 3384215 = 5076323) B5076323
theorem B3810199 : Blo 1503572 3810199 := bstep (se 1 (by rfl) ⟨2857649, by rfl⟩ : syracuseStep 3810199 = 5715299) B5715299
theorem B3613619 : Blo 1503572 3613619 := bstep (se 1 (by rfl) ⟨2710214, by rfl⟩ : syracuseStep 3613619 = 5420429) B5420429
theorem B7619507 : Blo 1503572 7619507 := bstep (se 1 (by rfl) ⟨5714630, by rfl⟩ : syracuseStep 7619507 = 11429261) B11429261
theorem B3212225 : Blo 1503572 3212225 := bstep (se 2 (by rfl) ⟨1204584, by rfl⟩ : syracuseStep 3212225 = 2409169) B2409169
theorem B3212311 : Blo 1503572 3212311 := bstep (se 1 (by rfl) ⟨2409233, by rfl⟩ : syracuseStep 3212311 = 4818467) B4818467
theorem B3048473 : Blo 1503572 3048473 := bstep (se 2 (by rfl) ⟨1143177, by rfl⟩ : syracuseStep 3048473 = 2286355) B2286355
theorem B1524779 : Blo 1503572 1524779 := bstep (se 1 (by rfl) ⟨1143584, by rfl⟩ : syracuseStep 1524779 = 2287169) B2287169
theorem B3384395 : Blo 1503572 3384395 := bstep (se 1 (by rfl) ⟨2538296, by rfl⟩ : syracuseStep 3384395 = 5076593) B5076593
theorem B5080157 : Blo 1503572 5080157 := bstep (se 3 (by rfl) ⟨952529, by rfl⟩ : syracuseStep 5080157 = 1905059) B1905059
theorem B3384449 : Blo 1503572 3384449 := bstep (se 2 (by rfl) ⟨1269168, by rfl⟩ : syracuseStep 3384449 = 2538337) B2538337
theorem B3048587 : Blo 1503572 3048587 := bstep (se 1 (by rfl) ⟨2286440, by rfl⟩ : syracuseStep 3048587 = 4572881) B4572881
theorem B4064435 : Blo 1503572 4064435 := bstep (se 1 (by rfl) ⟨3048326, by rfl⟩ : syracuseStep 4064435 = 6096653) B6096653
theorem B5711107 : Blo 1503572 5711107 := bstep (se 1 (by rfl) ⟨4283330, by rfl⟩ : syracuseStep 5711107 = 8566661) B8566661
theorem B1525015 : Blo 1503572 1525015 := bstep (se 1 (by rfl) ⟨1143761, by rfl⟩ : syracuseStep 1525015 = 2287523) B2287523
theorem B2442571 : Blo 1503572 2442571 := bstep (se 1 (by rfl) ⟨1831928, by rfl⟩ : syracuseStep 2442571 = 3663857) B3663857
theorem B3810635 : Blo 1503572 3810635 := bstep (se 1 (by rfl) ⟨2857976, by rfl⟩ : syracuseStep 3810635 = 5715953) B5715953
theorem B3384665 : Blo 1503572 3384665 := bstep (se 2 (by rfl) ⟨1269249, by rfl⟩ : syracuseStep 3384665 = 2538499) B2538499
theorem B43394453 : Blo 1503572 43394453 := bstep (se 6 (by rfl) ⟨1017057, by rfl⟩ : syracuseStep 43394453 = 2034115) B2034115
theorem B3384755 : Blo 1503572 3384755 := bstep (se 1 (by rfl) ⟨2538566, by rfl⟩ : syracuseStep 3384755 = 5077133) B5077133
theorem B4638131 : Blo 1503572 4638131 := bstep (se 1 (by rfl) ⟨3478598, by rfl⟩ : syracuseStep 4638131 = 6957197) B6957197
theorem B3384791 : Blo 1503572 3384791 := bstep (se 1 (by rfl) ⟨2538593, by rfl⟩ : syracuseStep 3384791 = 5077187) B5077187
theorem B6424109 : Blo 1503572 6424109 := bstep (se 3 (by rfl) ⟨1204520, by rfl⟩ : syracuseStep 6424109 = 2409041) B2409041
theorem B5711411 : Blo 1503572 5711411 := bstep (se 1 (by rfl) ⟨4283558, by rfl⟩ : syracuseStep 5711411 = 8567117) B8567117
theorem B3384971 : Blo 1503572 3384971 := bstep (se 1 (by rfl) ⟨2538728, by rfl⟩ : syracuseStep 3384971 = 5077457) B5077457
theorem B7612055 : Blo 1503572 7612055 := bstep (se 1 (by rfl) ⟨5709041, by rfl⟩ : syracuseStep 7612055 = 11418083) B11418083
theorem B3385025 : Blo 1503572 3385025 := bstep (se 2 (by rfl) ⟨1269384, by rfl⟩ : syracuseStep 3385025 = 2538769) B2538769
theorem B2893591 : Blo 1503572 2893591 := bstep (se 1 (by rfl) ⟨2170193, by rfl⟩ : syracuseStep 2893591 = 4340387) B4340387
theorem B11421485 : Blo 1503572 11421485 := bstep (se 3 (by rfl) ⟨2141528, by rfl⟩ : syracuseStep 11421485 = 4283057) B4283057
theorem B2033483 : Blo 1503572 2033483 := bstep (se 1 (by rfl) ⟨1525112, by rfl⟩ : syracuseStep 2033483 = 3050225) B3050225
theorem B8570717 : Blo 1503572 8570717 := bstep (se 3 (by rfl) ⟨1607009, by rfl⟩ : syracuseStep 8570717 = 3214019) B3214019
theorem B3385241 : Blo 1503572 3385241 := bstep (se 2 (by rfl) ⟨1269465, by rfl⟩ : syracuseStep 3385241 = 2538931) B2538931
theorem B2410393 : Blo 1503572 2410393 := bstep (se 2 (by rfl) ⟨903897, by rfl⟩ : syracuseStep 2410393 = 1807795) B1807795
theorem B4286429 : Blo 1503572 4286429 := bstep (se 3 (by rfl) ⟨803705, by rfl⟩ : syracuseStep 4286429 = 1607411) B1607411
theorem B3385331 : Blo 1503572 3385331 := bstep (se 1 (by rfl) ⟨2538998, by rfl⟩ : syracuseStep 3385331 = 5077997) B5077997
theorem B3385367 : Blo 1503572 3385367 := bstep (se 1 (by rfl) ⟨2539025, by rfl⟩ : syracuseStep 3385367 = 5078051) B5078051
theorem B5712065 : Blo 1503572 5712065 := bstep (se 2 (by rfl) ⟨2142024, by rfl⟩ : syracuseStep 5712065 = 4284049) B4284049
theorem B4286657 : Blo 1503572 4286657 := bstep (se 2 (by rfl) ⟨1607496, by rfl⟩ : syracuseStep 4286657 = 3214993) B3214993
theorem B3385547 : Blo 1503572 3385547 := bstep (se 1 (by rfl) ⟨2539160, by rfl⟩ : syracuseStep 3385547 = 5078321) B5078321
theorem B3385601 : Blo 1503572 3385601 := bstep (se 2 (by rfl) ⟨1269600, by rfl⟩ : syracuseStep 3385601 = 2539201) B2539201
theorem B10840337 : Blo 1503572 10840337 := bstep (se 2 (by rfl) ⟨4065126, by rfl⟩ : syracuseStep 10840337 = 8130253) B8130253
theorem B3664151 : Blo 1503572 3664151 := bstep (se 1 (by rfl) ⟨2748113, by rfl⟩ : syracuseStep 3664151 = 5496227) B5496227
theorem B13035811 : Blo 1503572 13035811 := bstep (se 1 (by rfl) ⟨9776858, by rfl⟩ : syracuseStep 13035811 = 19553717) B19553717
theorem B4819351 : Blo 1503572 4819351 := bstep (se 1 (by rfl) ⟨3614513, by rfl⟩ : syracuseStep 4819351 = 7229027) B7229027
theorem B3975617 : Blo 1503572 3975617 := bstep (se 2 (by rfl) ⟨1490856, by rfl⟩ : syracuseStep 3975617 = 2981713) B2981713
theorem B3385817 : Blo 1503572 3385817 := bstep (se 2 (by rfl) ⟨1269681, by rfl⟩ : syracuseStep 3385817 = 2539363) B2539363
theorem B1903115 : Blo 1503572 1903115 := bstep (se 1 (by rfl) ⟨1427336, by rfl⟩ : syracuseStep 1903115 = 2854673) B2854673
theorem B4286999 : Blo 1503572 4286999 := bstep (se 1 (by rfl) ⟨3215249, by rfl⟩ : syracuseStep 4286999 = 6430499) B6430499
theorem B3385907 : Blo 1503572 3385907 := bstep (se 1 (by rfl) ⟨2539430, by rfl⟩ : syracuseStep 3385907 = 5078861) B5078861
theorem B2255435 : Blo 1503572 2255435 := bstep (se 1 (by rfl) ⟨1691576, by rfl⟩ : syracuseStep 2255435 = 3383153) B3383153
theorem B2255447 : Blo 1503572 2255447 := bstep (se 1 (by rfl) ⟨1691585, by rfl⟩ : syracuseStep 2255447 = 3383171) B3383171
theorem B3385943 : Blo 1503572 3385943 := bstep (se 1 (by rfl) ⟨2539457, by rfl⟩ : syracuseStep 3385943 = 5078915) B5078915
theorem B2255513 : Blo 1503572 2255513 := bstep (se 2 (by rfl) ⟨845817, by rfl⟩ : syracuseStep 2255513 = 1691635) B1691635
theorem B2255627 : Blo 1503572 2255627 := bstep (se 1 (by rfl) ⟨1691720, by rfl⟩ : syracuseStep 2255627 = 3383441) B3383441
theorem B3386123 : Blo 1503572 3386123 := bstep (se 1 (by rfl) ⟨2539592, by rfl⟩ : syracuseStep 3386123 = 5079185) B5079185
theorem B2255639 : Blo 1503572 2255639 := bstep (se 1 (by rfl) ⟨1691729, by rfl⟩ : syracuseStep 2255639 = 3383459) B3383459
theorem B3386177 : Blo 1503572 3386177 := bstep (se 2 (by rfl) ⟨1269816, by rfl⟩ : syracuseStep 3386177 = 2539633) B2539633
theorem B3861323 : Blo 1503572 3861323 := bstep (se 1 (by rfl) ⟨2895992, by rfl⟩ : syracuseStep 3861323 = 5791985) B5791985
theorem B2255705 : Blo 1503572 2255705 := bstep (se 2 (by rfl) ⟨845889, by rfl⟩ : syracuseStep 2255705 = 1691779) B1691779
theorem B2255819 : Blo 1503572 2255819 := bstep (se 1 (by rfl) ⟨1691864, by rfl⟩ : syracuseStep 2255819 = 3383729) B3383729
theorem B2255831 : Blo 1503572 2255831 := bstep (se 1 (by rfl) ⟨1691873, by rfl⟩ : syracuseStep 2255831 = 3383747) B3383747
theorem B2255897 : Blo 1503572 2255897 := bstep (se 2 (by rfl) ⟨845961, by rfl⟩ : syracuseStep 2255897 = 1691923) B1691923
theorem B3386393 : Blo 1503572 3386393 := bstep (se 2 (by rfl) ⟨1269897, by rfl⟩ : syracuseStep 3386393 = 2539795) B2539795
theorem B3861569 : Blo 1503572 3861569 := bstep (se 2 (by rfl) ⟨1448088, by rfl⟩ : syracuseStep 3861569 = 2896177) B2896177
theorem B3386483 : Blo 1503572 3386483 := bstep (se 1 (by rfl) ⟨2539862, by rfl⟩ : syracuseStep 3386483 = 5079725) B5079725
theorem B2256011 : Blo 1503572 2256011 := bstep (se 1 (by rfl) ⟨1692008, by rfl⟩ : syracuseStep 2256011 = 3384017) B3384017
theorem B2256023 : Blo 1503572 2256023 := bstep (se 1 (by rfl) ⟨1692017, by rfl⟩ : syracuseStep 2256023 = 3384035) B3384035
theorem B3386519 : Blo 1503572 3386519 := bstep (se 1 (by rfl) ⟨2539889, by rfl⟩ : syracuseStep 3386519 = 5079779) B5079779
theorem B1903819 : Blo 1503572 1903819 := bstep (se 1 (by rfl) ⟨1427864, by rfl⟩ : syracuseStep 1903819 = 2855729) B2855729
theorem B9145561 : Blo 1503572 9145561 := bstep (se 2 (by rfl) ⟨3429585, by rfl⟩ : syracuseStep 9145561 = 6859171) B6859171
theorem B2256089 : Blo 1503572 2256089 := bstep (se 2 (by rfl) ⟨846033, by rfl⟩ : syracuseStep 2256089 = 1692067) B1692067
theorem B14650669 : Blo 1503572 14650669 := bstep (se 3 (by rfl) ⟨2747000, by rfl⟩ : syracuseStep 14650669 = 5494001) B5494001
theorem B2256203 : Blo 1503572 2256203 := bstep (se 1 (by rfl) ⟨1692152, by rfl⟩ : syracuseStep 2256203 = 3384305) B3384305
theorem B3386699 : Blo 1503572 3386699 := bstep (se 1 (by rfl) ⟨2540024, by rfl⟩ : syracuseStep 3386699 = 5080049) B5080049
theorem B2256215 : Blo 1503572 2256215 := bstep (se 1 (by rfl) ⟨1692161, by rfl⟩ : syracuseStep 2256215 = 3384323) B3384323
theorem B5147993 : Blo 1503572 5147993 := bstep (se 2 (by rfl) ⟨1930497, by rfl⟩ : syracuseStep 5147993 = 3860995) B3860995
theorem B3386753 : Blo 1503572 3386753 := bstep (se 2 (by rfl) ⟨1270032, by rfl⟩ : syracuseStep 3386753 = 2540065) B2540065
theorem B2256281 : Blo 1503572 2256281 := bstep (se 2 (by rfl) ⟨846105, by rfl⟩ : syracuseStep 2256281 = 1692211) B1692211
theorem B5713325 : Blo 1503572 5713325 := bstep (se 3 (by rfl) ⟨1071248, by rfl⟩ : syracuseStep 5713325 = 2142497) B2142497
theorem B5713355 : Blo 1503572 5713355 := bstep (se 1 (by rfl) ⟨4285016, by rfl⟩ : syracuseStep 5713355 = 8570033) B8570033
theorem B1904087 : Blo 1503572 1904087 := bstep (se 1 (by rfl) ⟨1428065, by rfl⟩ : syracuseStep 1904087 = 2856131) B2856131
theorem B4574681 : Blo 1503572 4574681 := bstep (se 2 (by rfl) ⟨1715505, by rfl⟩ : syracuseStep 4574681 = 3431011) B3431011
theorem B2256395 : Blo 1503572 2256395 := bstep (se 1 (by rfl) ⟨1692296, by rfl⟩ : syracuseStep 2256395 = 3384593) B3384593
theorem B2256407 : Blo 1503572 2256407 := bstep (se 1 (by rfl) ⟨1692305, by rfl⟩ : syracuseStep 2256407 = 3384611) B3384611
theorem B14650955 : Blo 1503572 14650955 := bstep (se 1 (by rfl) ⟨10988216, by rfl⟩ : syracuseStep 14650955 = 21976433) B21976433
theorem B2256473 : Blo 1503572 2256473 := bstep (se 2 (by rfl) ⟨846177, by rfl⟩ : syracuseStep 2256473 = 1692355) B1692355
theorem B3386969 : Blo 1503572 3386969 := bstep (se 2 (by rfl) ⟨1270113, by rfl⟩ : syracuseStep 3386969 = 2540227) B2540227
theorem B7327363 : Blo 1503572 7327363 := bstep (se 1 (by rfl) ⟨5495522, by rfl⟩ : syracuseStep 7327363 = 10991045) B10991045
theorem B2895499 : Blo 1503572 2895499 := bstep (se 1 (by rfl) ⟨2171624, by rfl⟩ : syracuseStep 2895499 = 4343249) B4343249
theorem B10841779 : Blo 1503572 10841779 := bstep (se 1 (by rfl) ⟨8131334, by rfl⟩ : syracuseStep 10841779 = 16262669) B16262669
theorem B3215027 : Blo 1503572 3215027 := bstep (se 1 (by rfl) ⟨2411270, by rfl⟩ : syracuseStep 3215027 = 4822541) B4822541
theorem B3387059 : Blo 1503572 3387059 := bstep (se 1 (by rfl) ⟨2540294, by rfl⟩ : syracuseStep 3387059 = 5080589) B5080589
theorem B2256587 : Blo 1503572 2256587 := bstep (se 1 (by rfl) ⟨1692440, by rfl⟩ : syracuseStep 2256587 = 3384881) B3384881
theorem B2256599 : Blo 1503572 2256599 := bstep (se 1 (by rfl) ⟨1692449, by rfl⟩ : syracuseStep 2256599 = 3384899) B3384899
theorem B3387095 : Blo 1503572 3387095 := bstep (se 1 (by rfl) ⟨2540321, by rfl⟩ : syracuseStep 3387095 = 5080643) B5080643
theorem B5074649 : Blo 1503572 5074649 := bstep (se 2 (by rfl) ⟨1902993, by rfl⟩ : syracuseStep 5074649 = 3805987) B3805987
theorem B2256665 : Blo 1503572 2256665 := bstep (se 2 (by rfl) ⟨846249, by rfl⟩ : syracuseStep 2256665 = 1692499) B1692499
theorem B2256779 : Blo 1503572 2256779 := bstep (se 1 (by rfl) ⟨1692584, by rfl⟩ : syracuseStep 2256779 = 3385169) B3385169
theorem B2256791 : Blo 1503572 2256791 := bstep (se 1 (by rfl) ⟨1692593, by rfl⟩ : syracuseStep 2256791 = 3385187) B3385187
theorem B1691563 : Blo 1503572 1691563 := bstep (se 1 (by rfl) ⟨1268672, by rfl⟩ : syracuseStep 1691563 = 2537345) B2537345
theorem B2256857 : Blo 1503572 2256857 := bstep (se 2 (by rfl) ⟨846321, by rfl⟩ : syracuseStep 2256857 = 1692643) B1692643
theorem B1691671 : Blo 1503572 1691671 := bstep (se 1 (by rfl) ⟨1268753, by rfl⟩ : syracuseStep 1691671 = 2537507) B2537507
theorem B6098989 : Blo 1503572 6098989 := bstep (se 3 (by rfl) ⟨1143560, by rfl⟩ : syracuseStep 6098989 = 2287121) B2287121
theorem B2256971 : Blo 1503572 2256971 := bstep (se 1 (by rfl) ⟨1692728, by rfl⟩ : syracuseStep 2256971 = 3385457) B3385457
theorem B2256983 : Blo 1503572 2256983 := bstep (se 1 (by rfl) ⟨1692737, by rfl⟩ : syracuseStep 2256983 = 3385475) B3385475
theorem B5714009 : Blo 1503572 5714009 := bstep (se 2 (by rfl) ⟨2142753, by rfl⟩ : syracuseStep 5714009 = 4285507) B4285507
theorem B1904791 : Blo 1503572 1904791 := bstep (se 1 (by rfl) ⟨1428593, by rfl⟩ : syracuseStep 1904791 = 2857187) B2857187
theorem B2257049 : Blo 1503572 2257049 := bstep (se 2 (by rfl) ⟨846393, by rfl⟩ : syracuseStep 2257049 = 1692787) B1692787
theorem B1691851 : Blo 1503572 1691851 := bstep (se 1 (by rfl) ⟨1268888, by rfl⟩ : syracuseStep 1691851 = 2537777) B2537777
theorem B2257163 : Blo 1503572 2257163 := bstep (se 1 (by rfl) ⟨1692872, by rfl⟩ : syracuseStep 2257163 = 3385745) B3385745
theorem B8573201 : Blo 1503572 8573201 := bstep (se 2 (by rfl) ⟨3214950, by rfl⟩ : syracuseStep 8573201 = 6429901) B6429901
theorem B2257175 : Blo 1503572 2257175 := bstep (se 1 (by rfl) ⟨1692881, by rfl⟩ : syracuseStep 2257175 = 3385763) B3385763
theorem B1691959 : Blo 1503572 1691959 := bstep (se 1 (by rfl) ⟨1268969, by rfl⟩ : syracuseStep 1691959 = 2537939) B2537939
theorem B2855243 : Blo 1503572 2855243 := bstep (se 1 (by rfl) ⟨2141432, by rfl⟩ : syracuseStep 2855243 = 4282865) B4282865
theorem B1503575 : Blo 1503572 1503575 := bstep (se 1 (by rfl) ⟨1127681, by rfl⟩ : syracuseStep 1503575 = 2255363) B2255363
theorem B2257241 : Blo 1503572 2257241 := bstep (se 2 (by rfl) ⟨846465, by rfl⟩ : syracuseStep 2257241 = 1692931) B1692931
theorem B1503595 : Blo 1503572 1503595 := bstep (se 1 (by rfl) ⟨1127696, by rfl⟩ : syracuseStep 1503595 = 2255393) B2255393
theorem B1503607 : Blo 1503572 1503607 := bstep (se 1 (by rfl) ⟨1127705, by rfl⟩ : syracuseStep 1503607 = 2255411) B2255411
theorem B1503627 : Blo 1503572 1503627 := bstep (se 1 (by rfl) ⟨1127720, by rfl⟩ : syracuseStep 1503627 = 2255441) B2255441
theorem B1503639 : Blo 1503572 1503639 := bstep (se 1 (by rfl) ⟨1127729, by rfl⟩ : syracuseStep 1503639 = 2255459) B2255459
theorem B5075351 : Blo 1503572 5075351 := bstep (se 1 (by rfl) ⟨3806513, by rfl⟩ : syracuseStep 5075351 = 7613027) B7613027
theorem B5714327 : Blo 1503572 5714327 := bstep (se 1 (by rfl) ⟨4285745, by rfl⟩ : syracuseStep 5714327 = 8571491) B8571491
theorem B1503659 : Blo 1503572 1503659 := bstep (se 1 (by rfl) ⟨1127744, by rfl⟩ : syracuseStep 1503659 = 2255489) B2255489
theorem B1503671 : Blo 1503572 1503671 := bstep (se 1 (by rfl) ⟨1127753, by rfl⟩ : syracuseStep 1503671 = 2255507) B2255507
theorem B1503691 : Blo 1503572 1503691 := bstep (se 1 (by rfl) ⟨1127768, by rfl⟩ : syracuseStep 1503691 = 2255537) B2255537
theorem B2257355 : Blo 1503572 2257355 := bstep (se 1 (by rfl) ⟨1693016, by rfl⟩ : syracuseStep 2257355 = 3386033) B3386033
theorem B1503703 : Blo 1503572 1503703 := bstep (se 1 (by rfl) ⟨1127777, by rfl⟩ : syracuseStep 1503703 = 2255555) B2255555
theorem B2257367 : Blo 1503572 2257367 := bstep (se 1 (by rfl) ⟨1693025, by rfl⟩ : syracuseStep 2257367 = 3386051) B3386051
theorem B1503723 : Blo 1503572 1503723 := bstep (se 1 (by rfl) ⟨1127792, by rfl⟩ : syracuseStep 1503723 = 2255585) B2255585
theorem B1692139 : Blo 1503572 1692139 := bstep (se 1 (by rfl) ⟨1269104, by rfl⟩ : syracuseStep 1692139 = 2538209) B2538209
theorem B1503735 : Blo 1503572 1503735 := bstep (se 1 (by rfl) ⟨1127801, by rfl⟩ : syracuseStep 1503735 = 2255603) B2255603
theorem B2855425 : Blo 1503572 2855425 := bstep (se 2 (by rfl) ⟨1070784, by rfl⟩ : syracuseStep 2855425 = 2141569) B2141569
theorem B1503755 : Blo 1503572 1503755 := bstep (se 1 (by rfl) ⟨1127816, by rfl⟩ : syracuseStep 1503755 = 2255633) B2255633
theorem B1503767 : Blo 1503572 1503767 := bstep (se 1 (by rfl) ⟨1127825, by rfl⟩ : syracuseStep 1503767 = 2255651) B2255651
theorem B2257433 : Blo 1503572 2257433 := bstep (se 2 (by rfl) ⟨846537, by rfl⟩ : syracuseStep 2257433 = 1693075) B1693075
theorem B1503787 : Blo 1503572 1503787 := bstep (se 1 (by rfl) ⟨1127840, by rfl⟩ : syracuseStep 1503787 = 2255681) B2255681
theorem B1503799 : Blo 1503572 1503799 := bstep (se 1 (by rfl) ⟨1127849, by rfl⟩ : syracuseStep 1503799 = 2255699) B2255699
theorem B1503819 : Blo 1503572 1503819 := bstep (se 1 (by rfl) ⟨1127864, by rfl⟩ : syracuseStep 1503819 = 2255729) B2255729
theorem B1503831 : Blo 1503572 1503831 := bstep (se 1 (by rfl) ⟨1127873, by rfl⟩ : syracuseStep 1503831 = 2255747) B2255747
theorem B1692247 : Blo 1503572 1692247 := bstep (se 1 (by rfl) ⟨1269185, by rfl⟩ : syracuseStep 1692247 = 2538371) B2538371
theorem B10039909 : Blo 1503572 10039909 := bstep (se 4 (by rfl) ⟨941241, by rfl⟩ : syracuseStep 10039909 = 1882483) B1882483
theorem B1503851 : Blo 1503572 1503851 := bstep (se 1 (by rfl) ⟨1127888, by rfl⟩ : syracuseStep 1503851 = 2255777) B2255777
theorem B1503863 : Blo 1503572 1503863 := bstep (se 1 (by rfl) ⟨1127897, by rfl⟩ : syracuseStep 1503863 = 2255795) B2255795
theorem B1503883 : Blo 1503572 1503883 := bstep (se 1 (by rfl) ⟨1127912, by rfl⟩ : syracuseStep 1503883 = 2255825) B2255825
theorem B2257547 : Blo 1503572 2257547 := bstep (se 1 (by rfl) ⟨1693160, by rfl⟩ : syracuseStep 2257547 = 3386321) B3386321
theorem B1503895 : Blo 1503572 1503895 := bstep (se 1 (by rfl) ⟨1127921, by rfl⟩ : syracuseStep 1503895 = 2255843) B2255843
theorem B2257559 : Blo 1503572 2257559 := bstep (se 1 (by rfl) ⟨1693169, by rfl⟩ : syracuseStep 2257559 = 3386339) B3386339
theorem B1503915 : Blo 1503572 1503915 := bstep (se 1 (by rfl) ⟨1127936, by rfl⟩ : syracuseStep 1503915 = 2255873) B2255873
theorem B1503927 : Blo 1503572 1503927 := bstep (se 1 (by rfl) ⟨1127945, by rfl⟩ : syracuseStep 1503927 = 2255891) B2255891
theorem B1503947 : Blo 1503572 1503947 := bstep (se 1 (by rfl) ⟨1127960, by rfl⟩ : syracuseStep 1503947 = 2255921) B2255921
theorem B1503959 : Blo 1503572 1503959 := bstep (se 1 (by rfl) ⟨1127969, by rfl⟩ : syracuseStep 1503959 = 2255939) B2255939
theorem B2257625 : Blo 1503572 2257625 := bstep (se 2 (by rfl) ⟨846609, by rfl⟩ : syracuseStep 2257625 = 1693219) B1693219
theorem B1503979 : Blo 1503572 1503979 := bstep (se 1 (by rfl) ⟨1127984, by rfl⟩ : syracuseStep 1503979 = 2255969) B2255969
theorem B1503991 : Blo 1503572 1503991 := bstep (se 1 (by rfl) ⟨1127993, by rfl⟩ : syracuseStep 1503991 = 2255987) B2255987
theorem B1504011 : Blo 1503572 1504011 := bstep (se 1 (by rfl) ⟨1128008, by rfl⟩ : syracuseStep 1504011 = 2256017) B2256017
theorem B1692427 : Blo 1503572 1692427 := bstep (se 1 (by rfl) ⟨1269320, by rfl⟩ : syracuseStep 1692427 = 2538641) B2538641
theorem B1504023 : Blo 1503572 1504023 := bstep (se 1 (by rfl) ⟨1128017, by rfl⟩ : syracuseStep 1504023 = 2256035) B2256035
theorem B1504043 : Blo 1503572 1504043 := bstep (se 1 (by rfl) ⟨1128032, by rfl⟩ : syracuseStep 1504043 = 2256065) B2256065
theorem B1504055 : Blo 1503572 1504055 := bstep (se 1 (by rfl) ⟨1128041, by rfl⟩ : syracuseStep 1504055 = 2256083) B2256083
theorem B6427457 : Blo 1503572 6427457 := bstep (se 2 (by rfl) ⟨2410296, by rfl⟩ : syracuseStep 6427457 = 4820593) B4820593
theorem B1504075 : Blo 1503572 1504075 := bstep (se 1 (by rfl) ⟨1128056, by rfl⟩ : syracuseStep 1504075 = 2256113) B2256113
theorem B2257739 : Blo 1503572 2257739 := bstep (se 1 (by rfl) ⟨1693304, by rfl⟩ : syracuseStep 2257739 = 3386609) B3386609
theorem B1504087 : Blo 1503572 1504087 := bstep (se 1 (by rfl) ⟨1128065, by rfl⟩ : syracuseStep 1504087 = 2256131) B2256131
theorem B2257751 : Blo 1503572 2257751 := bstep (se 1 (by rfl) ⟨1693313, by rfl⟩ : syracuseStep 2257751 = 3386627) B3386627
theorem B1504107 : Blo 1503572 1504107 := bstep (se 1 (by rfl) ⟨1128080, by rfl⟩ : syracuseStep 1504107 = 2256161) B2256161
theorem B1504119 : Blo 1503572 1504119 := bstep (se 1 (by rfl) ⟨1128089, by rfl⟩ : syracuseStep 1504119 = 2256179) B2256179
theorem B1692535 : Blo 1503572 1692535 := bstep (se 1 (by rfl) ⟨1269401, by rfl⟩ : syracuseStep 1692535 = 2538803) B2538803
theorem B1504139 : Blo 1503572 1504139 := bstep (se 1 (by rfl) ⟨1128104, by rfl⟩ : syracuseStep 1504139 = 2256209) B2256209
theorem B1504151 : Blo 1503572 1504151 := bstep (se 1 (by rfl) ⟨1128113, by rfl⟩ : syracuseStep 1504151 = 2256227) B2256227
theorem B12858263 : Blo 1503572 12858263 := bstep (se 1 (by rfl) ⟨9643697, by rfl⟩ : syracuseStep 12858263 = 19287395) B19287395
theorem B2257817 : Blo 1503572 2257817 := bstep (se 2 (by rfl) ⟨846681, by rfl⟩ : syracuseStep 2257817 = 1693363) B1693363
theorem B1504171 : Blo 1503572 1504171 := bstep (se 1 (by rfl) ⟨1128128, by rfl⟩ : syracuseStep 1504171 = 2256257) B2256257
theorem B5075891 : Blo 1503572 5075891 := bstep (se 1 (by rfl) ⟨3806918, by rfl⟩ : syracuseStep 5075891 = 7613837) B7613837
theorem B1504183 : Blo 1503572 1504183 := bstep (se 1 (by rfl) ⟨1128137, by rfl⟩ : syracuseStep 1504183 = 2256275) B2256275
theorem B2855873 : Blo 1503572 2855873 := bstep (se 2 (by rfl) ⟨1070952, by rfl⟩ : syracuseStep 2855873 = 2141905) B2141905
theorem B1504203 : Blo 1503572 1504203 := bstep (se 1 (by rfl) ⟨1128152, by rfl⟩ : syracuseStep 1504203 = 2256305) B2256305
theorem B1504215 : Blo 1503572 1504215 := bstep (se 1 (by rfl) ⟨1128161, by rfl⟩ : syracuseStep 1504215 = 2256323) B2256323
theorem B5419997 : Blo 1503572 5419997 := bstep (se 3 (by rfl) ⟨1016249, by rfl⟩ : syracuseStep 5419997 = 2032499) B2032499
theorem B1504235 : Blo 1503572 1504235 := bstep (se 1 (by rfl) ⟨1128176, by rfl⟩ : syracuseStep 1504235 = 2256353) B2256353
theorem B1504247 : Blo 1503572 1504247 := bstep (se 1 (by rfl) ⟨1128185, by rfl⟩ : syracuseStep 1504247 = 2256371) B2256371
theorem B1504267 : Blo 1503572 1504267 := bstep (se 1 (by rfl) ⟨1128200, by rfl⟩ : syracuseStep 1504267 = 2256401) B2256401
theorem B2257931 : Blo 1503572 2257931 := bstep (se 1 (by rfl) ⟨1693448, by rfl⟩ : syracuseStep 2257931 = 3386897) B3386897
theorem B12194833 : Blo 1503572 12194833 := bstep (se 2 (by rfl) ⟨4573062, by rfl⟩ : syracuseStep 12194833 = 9146125) B9146125
theorem B9638929 : Blo 1503572 9638929 := bstep (se 2 (by rfl) ⟨3614598, by rfl⟩ : syracuseStep 9638929 = 7229197) B7229197
theorem B1504279 : Blo 1503572 1504279 := bstep (se 1 (by rfl) ⟨1128209, by rfl⟩ : syracuseStep 1504279 = 2256419) B2256419
theorem B2143255 : Blo 1503572 2143255 := bstep (se 1 (by rfl) ⟨1607441, by rfl⟩ : syracuseStep 2143255 = 3214883) B3214883
theorem B2257943 : Blo 1503572 2257943 := bstep (se 1 (by rfl) ⟨1693457, by rfl⟩ : syracuseStep 2257943 = 3386915) B3386915
theorem B1504299 : Blo 1503572 1504299 := bstep (se 1 (by rfl) ⟨1128224, by rfl⟩ : syracuseStep 1504299 = 2256449) B2256449
theorem B1692715 : Blo 1503572 1692715 := bstep (se 1 (by rfl) ⟨1269536, by rfl⟩ : syracuseStep 1692715 = 2539073) B2539073
theorem B5714995 : Blo 1503572 5714995 := bstep (se 1 (by rfl) ⟨4286246, by rfl⟩ : syracuseStep 5714995 = 8572493) B8572493
theorem B1504311 : Blo 1503572 1504311 := bstep (se 1 (by rfl) ⟨1128233, by rfl⟩ : syracuseStep 1504311 = 2256467) B2256467
theorem B1504331 : Blo 1503572 1504331 := bstep (se 1 (by rfl) ⟨1128248, by rfl⟩ : syracuseStep 1504331 = 2256497) B2256497
theorem B1504343 : Blo 1503572 1504343 := bstep (se 1 (by rfl) ⟨1128257, by rfl⟩ : syracuseStep 1504343 = 2256515) B2256515
theorem B2258009 : Blo 1503572 2258009 := bstep (se 2 (by rfl) ⟨846753, by rfl⟩ : syracuseStep 2258009 = 1693507) B1693507
theorem B1504363 : Blo 1503572 1504363 := bstep (se 1 (by rfl) ⟨1128272, by rfl⟩ : syracuseStep 1504363 = 2256545) B2256545
theorem B1504375 : Blo 1503572 1504375 := bstep (se 1 (by rfl) ⟨1128281, by rfl⟩ : syracuseStep 1504375 = 2256563) B2256563
theorem B7615619 : Blo 1503572 7615619 := bstep (se 1 (by rfl) ⟨5711714, by rfl⟩ : syracuseStep 7615619 = 11423429) B11423429
theorem B1504395 : Blo 1503572 1504395 := bstep (se 1 (by rfl) ⟨1128296, by rfl⟩ : syracuseStep 1504395 = 2256593) B2256593
theorem B8565911 : Blo 1503572 8565911 := bstep (se 1 (by rfl) ⟨6424433, by rfl⟩ : syracuseStep 8565911 = 12848867) B12848867
theorem B1504407 : Blo 1503572 1504407 := bstep (se 1 (by rfl) ⟨1128305, by rfl⟩ : syracuseStep 1504407 = 2256611) B2256611
theorem B1692823 : Blo 1503572 1692823 := bstep (se 1 (by rfl) ⟨1269617, by rfl⟩ : syracuseStep 1692823 = 2539235) B2539235
theorem B6427799 : Blo 1503572 6427799 := bstep (se 1 (by rfl) ⟨4820849, by rfl⟩ : syracuseStep 6427799 = 9641699) B9641699
theorem B1504427 : Blo 1503572 1504427 := bstep (se 1 (by rfl) ⟨1128320, by rfl⟩ : syracuseStep 1504427 = 2256641) B2256641
theorem B1504439 : Blo 1503572 1504439 := bstep (se 1 (by rfl) ⟨1128329, by rfl⟩ : syracuseStep 1504439 = 2256659) B2256659
theorem B5076161 : Blo 1503572 5076161 := bstep (se 2 (by rfl) ⟨1903560, by rfl⟩ : syracuseStep 5076161 = 3807121) B3807121
theorem B1504459 : Blo 1503572 1504459 := bstep (se 1 (by rfl) ⟨1128344, by rfl⟩ : syracuseStep 1504459 = 2256689) B2256689
theorem B2258123 : Blo 1503572 2258123 := bstep (se 1 (by rfl) ⟨1693592, by rfl⟩ : syracuseStep 2258123 = 3387185) B3387185
theorem B1504471 : Blo 1503572 1504471 := bstep (se 1 (by rfl) ⟨1128353, by rfl⟩ : syracuseStep 1504471 = 2256707) B2256707
theorem B2258135 : Blo 1503572 2258135 := bstep (se 1 (by rfl) ⟨1693601, by rfl⟩ : syracuseStep 2258135 = 3387203) B3387203
theorem B1504491 : Blo 1503572 1504491 := bstep (se 1 (by rfl) ⟨1128368, by rfl⟩ : syracuseStep 1504491 = 2256737) B2256737
theorem B1504503 : Blo 1503572 1504503 := bstep (se 1 (by rfl) ⟨1128377, by rfl⟩ : syracuseStep 1504503 = 2256755) B2256755
theorem B1504523 : Blo 1503572 1504523 := bstep (se 1 (by rfl) ⟨1128392, by rfl⟩ : syracuseStep 1504523 = 2256785) B2256785
theorem B2856215 : Blo 1503572 2856215 := bstep (se 1 (by rfl) ⟨2142161, by rfl⟩ : syracuseStep 2856215 = 4284323) B4284323
theorem B1504535 : Blo 1503572 1504535 := bstep (se 1 (by rfl) ⟨1128401, by rfl⟩ : syracuseStep 1504535 = 2256803) B2256803
theorem B1504555 : Blo 1503572 1504555 := bstep (se 1 (by rfl) ⟨1128416, by rfl⟩ : syracuseStep 1504555 = 2256833) B2256833
theorem B1504567 : Blo 1503572 1504567 := bstep (se 1 (by rfl) ⟨1128425, by rfl⟩ : syracuseStep 1504567 = 2256851) B2256851
theorem B3429697 : Blo 1503572 3429697 := bstep (se 2 (by rfl) ⟨1286136, by rfl⟩ : syracuseStep 3429697 = 2572273) B2572273
theorem B1504587 : Blo 1503572 1504587 := bstep (se 1 (by rfl) ⟨1128440, by rfl⟩ : syracuseStep 1504587 = 2256881) B2256881
theorem B1693003 : Blo 1503572 1693003 := bstep (se 1 (by rfl) ⟨1269752, by rfl⟩ : syracuseStep 1693003 = 2539505) B2539505
theorem B1504599 : Blo 1503572 1504599 := bstep (se 1 (by rfl) ⟨1128449, by rfl⟩ : syracuseStep 1504599 = 2256899) B2256899
theorem B1504619 : Blo 1503572 1504619 := bstep (se 1 (by rfl) ⟨1128464, by rfl⟩ : syracuseStep 1504619 = 2256929) B2256929
theorem B1504631 : Blo 1503572 1504631 := bstep (se 1 (by rfl) ⟨1128473, by rfl⟩ : syracuseStep 1504631 = 2256947) B2256947
theorem B1504651 : Blo 1503572 1504651 := bstep (se 1 (by rfl) ⟨1128488, by rfl⟩ : syracuseStep 1504651 = 2256977) B2256977
theorem B3806615 : Blo 1503572 3806615 := bstep (se 1 (by rfl) ⟨2854961, by rfl⟩ : syracuseStep 3806615 = 5709923) B5709923
theorem B12531095 : Blo 1503572 12531095 := bstep (se 1 (by rfl) ⟨9398321, by rfl⟩ : syracuseStep 12531095 = 18796643) B18796643
theorem B1504663 : Blo 1503572 1504663 := bstep (se 1 (by rfl) ⟨1128497, by rfl⟩ : syracuseStep 1504663 = 2256995) B2256995
theorem B1504683 : Blo 1503572 1504683 := bstep (se 1 (by rfl) ⟨1128512, by rfl⟩ : syracuseStep 1504683 = 2257025) B2257025
theorem B1504695 : Blo 1503572 1504695 := bstep (se 1 (by rfl) ⟨1128521, by rfl⟩ : syracuseStep 1504695 = 2257043) B2257043
theorem B1693111 : Blo 1503572 1693111 := bstep (se 1 (by rfl) ⟨1269833, by rfl⟩ : syracuseStep 1693111 = 2539667) B2539667
theorem B1504715 : Blo 1503572 1504715 := bstep (se 1 (by rfl) ⟨1128536, by rfl⟩ : syracuseStep 1504715 = 2257073) B2257073
theorem B1504727 : Blo 1503572 1504727 := bstep (se 1 (by rfl) ⟨1128545, by rfl⟩ : syracuseStep 1504727 = 2257091) B2257091
theorem B1504747 : Blo 1503572 1504747 := bstep (se 1 (by rfl) ⟨1128560, by rfl⟩ : syracuseStep 1504747 = 2257121) B2257121
theorem B1504759 : Blo 1503572 1504759 := bstep (se 1 (by rfl) ⟨1128569, by rfl⟩ : syracuseStep 1504759 = 2257139) B2257139
theorem B1504779 : Blo 1503572 1504779 := bstep (se 1 (by rfl) ⟨1128584, by rfl⟩ : syracuseStep 1504779 = 2257169) B2257169
theorem B1504791 : Blo 1503572 1504791 := bstep (se 1 (by rfl) ⟨1128593, by rfl⟩ : syracuseStep 1504791 = 2257187) B2257187
theorem B1504811 : Blo 1503572 1504811 := bstep (se 1 (by rfl) ⟨1128608, by rfl⟩ : syracuseStep 1504811 = 2257217) B2257217
theorem B1504823 : Blo 1503572 1504823 := bstep (se 1 (by rfl) ⟨1128617, by rfl⟩ : syracuseStep 1504823 = 2257235) B2257235
theorem B1504843 : Blo 1503572 1504843 := bstep (se 1 (by rfl) ⟨1128632, by rfl⟩ : syracuseStep 1504843 = 2257265) B2257265
theorem B1504855 : Blo 1503572 1504855 := bstep (se 1 (by rfl) ⟨1128641, by rfl⟩ : syracuseStep 1504855 = 2257283) B2257283
theorem B11425373 : Blo 1503572 11425373 := bstep (se 3 (by rfl) ⟨2142257, by rfl⟩ : syracuseStep 11425373 = 4284515) B4284515
theorem B1504875 : Blo 1503572 1504875 := bstep (se 1 (by rfl) ⟨1128656, by rfl⟩ : syracuseStep 1504875 = 2257313) B2257313
theorem B1693291 : Blo 1503572 1693291 := bstep (se 1 (by rfl) ⟨1269968, by rfl⟩ : syracuseStep 1693291 = 2539937) B2539937
theorem B1504887 : Blo 1503572 1504887 := bstep (se 1 (by rfl) ⟨1128665, by rfl⟩ : syracuseStep 1504887 = 2257331) B2257331
theorem B1504907 : Blo 1503572 1504907 := bstep (se 1 (by rfl) ⟨1128680, by rfl⟩ : syracuseStep 1504907 = 2257361) B2257361
theorem B1808011 : Blo 1503572 1808011 := bstep (se 1 (by rfl) ⟨1356008, by rfl⟩ : syracuseStep 1808011 = 2712017) B2712017
theorem B9770647 : Blo 1503572 9770647 := bstep (se 1 (by rfl) ⟨7327985, by rfl⟩ : syracuseStep 9770647 = 14655971) B14655971
theorem B1504919 : Blo 1503572 1504919 := bstep (se 1 (by rfl) ⟨1128689, by rfl⟩ : syracuseStep 1504919 = 2257379) B2257379
theorem B1504939 : Blo 1503572 1504939 := bstep (se 1 (by rfl) ⟨1128704, by rfl⟩ : syracuseStep 1504939 = 2257409) B2257409
theorem B1504951 : Blo 1503572 1504951 := bstep (se 1 (by rfl) ⟨1128713, by rfl⟩ : syracuseStep 1504951 = 2257427) B2257427
theorem B1504971 : Blo 1503572 1504971 := bstep (se 1 (by rfl) ⟨1128728, by rfl⟩ : syracuseStep 1504971 = 2257457) B2257457
theorem B1504983 : Blo 1503572 1504983 := bstep (se 1 (by rfl) ⟨1128737, by rfl⟩ : syracuseStep 1504983 = 2257475) B2257475
theorem B1693399 : Blo 1503572 1693399 := bstep (se 1 (by rfl) ⟨1270049, by rfl⟩ : syracuseStep 1693399 = 2540099) B2540099
theorem B4822745 : Blo 1503572 4822745 := bstep (se 2 (by rfl) ⟨1808529, by rfl⟩ : syracuseStep 4822745 = 3617059) B3617059
theorem B5076701 : Blo 1503572 5076701 := bstep (se 3 (by rfl) ⟨951881, by rfl⟩ : syracuseStep 5076701 = 1903763) B1903763
theorem B1505003 : Blo 1503572 1505003 := bstep (se 1 (by rfl) ⟨1128752, by rfl⟩ : syracuseStep 1505003 = 2257505) B2257505
theorem B1505015 : Blo 1503572 1505015 := bstep (se 1 (by rfl) ⟨1128761, by rfl⟩ : syracuseStep 1505015 = 2257523) B2257523
theorem B1505035 : Blo 1503572 1505035 := bstep (se 1 (by rfl) ⟨1128776, by rfl⟩ : syracuseStep 1505035 = 2257553) B2257553
theorem B1505047 : Blo 1503572 1505047 := bstep (se 1 (by rfl) ⟨1128785, by rfl⟩ : syracuseStep 1505047 = 2257571) B2257571
theorem B3430169 : Blo 1503572 3430169 := bstep (se 2 (by rfl) ⟨1286313, by rfl⟩ : syracuseStep 3430169 = 2572627) B2572627
theorem B1505067 : Blo 1503572 1505067 := bstep (se 1 (by rfl) ⟨1128800, by rfl⟩ : syracuseStep 1505067 = 2257601) B2257601
theorem B1505079 : Blo 1503572 1505079 := bstep (se 1 (by rfl) ⟨1128809, by rfl⟩ : syracuseStep 1505079 = 2257619) B2257619
theorem B2537291 : Blo 1503572 2537291 := bstep (se 1 (by rfl) ⟨1902968, by rfl⟩ : syracuseStep 2537291 = 3805937) B3805937
theorem B1505099 : Blo 1503572 1505099 := bstep (se 1 (by rfl) ⟨1128824, by rfl⟩ : syracuseStep 1505099 = 2257649) B2257649
theorem B1505111 : Blo 1503572 1505111 := bstep (se 1 (by rfl) ⟨1128833, by rfl⟩ : syracuseStep 1505111 = 2257667) B2257667
theorem B1505131 : Blo 1503572 1505131 := bstep (se 1 (by rfl) ⟨1128848, by rfl⟩ : syracuseStep 1505131 = 2257697) B2257697
theorem B1505143 : Blo 1503572 1505143 := bstep (se 1 (by rfl) ⟨1128857, by rfl⟩ : syracuseStep 1505143 = 2257715) B2257715
theorem B1505163 : Blo 1503572 1505163 := bstep (se 1 (by rfl) ⟨1128872, by rfl⟩ : syracuseStep 1505163 = 2257745) B2257745
theorem B1693579 : Blo 1503572 1693579 := bstep (se 1 (by rfl) ⟨1270184, by rfl⟩ : syracuseStep 1693579 = 2540369) B2540369
theorem B1505175 : Blo 1503572 1505175 := bstep (se 1 (by rfl) ⟨1128881, by rfl⟩ : syracuseStep 1505175 = 2257763) B2257763
theorem B1505195 : Blo 1503572 1505195 := bstep (se 1 (by rfl) ⟨1128896, by rfl⟩ : syracuseStep 1505195 = 2257793) B2257793
theorem B2856883 : Blo 1503572 2856883 := bstep (se 1 (by rfl) ⟨2142662, by rfl⟩ : syracuseStep 2856883 = 4285325) B4285325
theorem B1505207 : Blo 1503572 1505207 := bstep (se 1 (by rfl) ⟨1128905, by rfl⟩ : syracuseStep 1505207 = 2257811) B2257811
theorem B2537419 : Blo 1503572 2537419 := bstep (se 1 (by rfl) ⟨1903064, by rfl⟩ : syracuseStep 2537419 = 3806129) B3806129
theorem B1505227 : Blo 1503572 1505227 := bstep (se 1 (by rfl) ⟨1128920, by rfl⟩ : syracuseStep 1505227 = 2257841) B2257841
theorem B1505239 : Blo 1503572 1505239 := bstep (se 1 (by rfl) ⟨1128929, by rfl⟩ : syracuseStep 1505239 = 2257859) B2257859
theorem B1505259 : Blo 1503572 1505259 := bstep (se 1 (by rfl) ⟨1128944, by rfl⟩ : syracuseStep 1505259 = 2257889) B2257889
theorem B1505271 : Blo 1503572 1505271 := bstep (se 1 (by rfl) ⟨1128953, by rfl⟩ : syracuseStep 1505271 = 2257907) B2257907
theorem B1505291 : Blo 1503572 1505291 := bstep (se 1 (by rfl) ⟨1128968, by rfl⟩ : syracuseStep 1505291 = 2257937) B2257937
theorem B1505303 : Blo 1503572 1505303 := bstep (se 1 (by rfl) ⟨1128977, by rfl⟩ : syracuseStep 1505303 = 2257955) B2257955
theorem B1505323 : Blo 1503572 1505323 := bstep (se 1 (by rfl) ⟨1128992, by rfl⟩ : syracuseStep 1505323 = 2257985) B2257985
theorem B3807283 : Blo 1503572 3807283 := bstep (se 1 (by rfl) ⟨2855462, by rfl⟩ : syracuseStep 3807283 = 5710925) B5710925
theorem B1505335 : Blo 1503572 1505335 := bstep (se 1 (by rfl) ⟨1129001, by rfl⟩ : syracuseStep 1505335 = 2258003) B2258003
theorem B1505355 : Blo 1503572 1505355 := bstep (se 1 (by rfl) ⟨1129016, by rfl⟩ : syracuseStep 1505355 = 2258033) B2258033
theorem B1505367 : Blo 1503572 1505367 := bstep (se 1 (by rfl) ⟨1129025, by rfl⟩ : syracuseStep 1505367 = 2258051) B2258051
theorem B2537561 : Blo 1503572 2537561 := bstep (se 2 (by rfl) ⟨951585, by rfl⟩ : syracuseStep 2537561 = 1903171) B1903171
theorem B1505387 : Blo 1503572 1505387 := bstep (se 1 (by rfl) ⟨1129040, by rfl⟩ : syracuseStep 1505387 = 2258081) B2258081
theorem B1505399 : Blo 1503572 1505399 := bstep (se 1 (by rfl) ⟨1129049, by rfl⟩ : syracuseStep 1505399 = 2258099) B2258099
theorem B1505419 : Blo 1503572 1505419 := bstep (se 1 (by rfl) ⟨1129064, by rfl⟩ : syracuseStep 1505419 = 2258129) B2258129
theorem B1505431 : Blo 1503572 1505431 := bstep (se 1 (by rfl) ⟨1129073, by rfl⟩ : syracuseStep 1505431 = 2258147) B2258147
theorem B3807425 : Blo 1503572 3807425 := bstep (se 2 (by rfl) ⟨1427784, by rfl⟩ : syracuseStep 3807425 = 2855569) B2855569
theorem B2537689 : Blo 1503572 2537689 := bstep (se 2 (by rfl) ⟨951633, by rfl⟩ : syracuseStep 2537689 = 1903267) B1903267
theorem B2857331 : Blo 1503572 2857331 := bstep (se 1 (by rfl) ⟨2142998, by rfl⟩ : syracuseStep 2857331 = 4285997) B4285997
theorem B2857369 : Blo 1503572 2857369 := bstep (se 2 (by rfl) ⟨1071513, by rfl⟩ : syracuseStep 2857369 = 2143027) B2143027
theorem B14457437 : Blo 1503572 14457437 := bstep (se 3 (by rfl) ⟨2710769, by rfl⟩ : syracuseStep 14457437 = 5421539) B5421539
theorem B43997827 : Blo 1503572 43997827 := bstep (se 1 (by rfl) ⟨32998370, by rfl⟩ : syracuseStep 43997827 = 65996741) B65996741
theorem B24394391 : Blo 1503572 24394391 := bstep (se 1 (by rfl) ⟨18295793, by rfl⟩ : syracuseStep 24394391 = 36591587) B36591587
theorem B2538263 : Blo 1503572 2538263 := bstep (se 1 (by rfl) ⟨1903697, by rfl⟩ : syracuseStep 2538263 = 3807395) B3807395
theorem B17144621 : Blo 1503572 17144621 := bstep (se 3 (by rfl) ⟨3214616, by rfl⟩ : syracuseStep 17144621 = 6429233) B6429233
theorem B15448897 : Blo 1503572 15448897 := bstep (se 2 (by rfl) ⟨5793336, by rfl⟩ : syracuseStep 15448897 = 11586673) B11586673
theorem B5077835 : Blo 1503572 5077835 := bstep (se 1 (by rfl) ⟨3808376, by rfl⟩ : syracuseStep 5077835 = 7616753) B7616753
theorem B2857817 : Blo 1503572 2857817 := bstep (se 2 (by rfl) ⟨1071681, by rfl⟩ : syracuseStep 2857817 = 2143363) B2143363
theorem B2538391 : Blo 1503572 2538391 := bstep (se 1 (by rfl) ⟨1903793, by rfl⟩ : syracuseStep 2538391 = 3807587) B3807587
theorem B104225753 : Blo 1503572 104225753 := bstep (se 2 (by rfl) ⟨39084657, by rfl⟩ : syracuseStep 104225753 = 78169315) B78169315
theorem B2710603 : Blo 1503572 2710603 := bstep (se 1 (by rfl) ⟨2032952, by rfl⟩ : syracuseStep 2710603 = 4065905) B4065905
theorem B5078105 : Blo 1503572 5078105 := bstep (se 2 (by rfl) ⟨1904289, by rfl⟩ : syracuseStep 5078105 = 3808579) B3808579
theorem B5708951 : Blo 1503572 5708951 := bstep (se 1 (by rfl) ⟨4281713, by rfl⟩ : syracuseStep 5708951 = 8563427) B8563427
theorem B3431575 : Blo 1503572 3431575 := bstep (se 1 (by rfl) ⟨2573681, by rfl⟩ : syracuseStep 3431575 = 5147363) B5147363
theorem B6429917 : Blo 1503572 6429917 := bstep (se 3 (by rfl) ⟨1205609, by rfl⟩ : syracuseStep 6429917 = 2411219) B2411219
theorem B7232813 : Blo 1503572 7232813 := bstep (se 3 (by rfl) ⟨1356152, by rfl⟩ : syracuseStep 7232813 = 2712305) B2712305
theorem B5709149 : Blo 1503572 5709149 := bstep (se 3 (by rfl) ⟨1070465, by rfl⟩ : syracuseStep 5709149 = 2140931) B2140931
theorem B4283741 : Blo 1503572 4283741 := bstep (se 3 (by rfl) ⟨803201, by rfl⟩ : syracuseStep 4283741 = 1606403) B1606403
theorem B3808691 : Blo 1503572 3808691 := bstep (se 1 (by rfl) ⟨2856518, by rfl⟩ : syracuseStep 3808691 = 5713037) B5713037
theorem B2539019 : Blo 1503572 2539019 := bstep (se 1 (by rfl) ⟨1904264, by rfl⟩ : syracuseStep 2539019 = 3808529) B3808529
theorem B25705997 : Blo 1503572 25705997 := bstep (se 3 (by rfl) ⟨4819874, by rfl⟩ : syracuseStep 25705997 = 9639749) B9639749
theorem B6430225 : Blo 1503572 6430225 := bstep (se 2 (by rfl) ⟨2411334, by rfl⟩ : syracuseStep 6430225 = 4822669) B4822669
theorem B2711065 : Blo 1503572 2711065 := bstep (se 2 (by rfl) ⟨1016649, by rfl⟩ : syracuseStep 2711065 = 2033299) B2033299
theorem B6430259 : Blo 1503572 6430259 := bstep (se 1 (by rfl) ⟨4822694, by rfl⟩ : syracuseStep 6430259 = 9645389) B9645389
theorem B2539147 : Blo 1503572 2539147 := bstep (se 1 (by rfl) ⟨1904360, by rfl⟩ : syracuseStep 2539147 = 3808721) B3808721
theorem B4284083 : Blo 1503572 4284083 := bstep (se 1 (by rfl) ⟨3213062, by rfl⟩ : syracuseStep 4284083 = 6426125) B6426125
theorem B12205829 : Blo 1503572 12205829 := bstep (se 4 (by rfl) ⟨1144296, by rfl⟩ : syracuseStep 12205829 = 2288593) B2288593
theorem B3383063 : Blo 1503572 3383063 := bstep (se 1 (by rfl) ⟨2537297, by rfl⟩ : syracuseStep 3383063 = 5074595) B5074595
theorem B5078807 : Blo 1503572 5078807 := bstep (se 1 (by rfl) ⟨3809105, by rfl⟩ : syracuseStep 5078807 = 7618211) B7618211
theorem B2539289 : Blo 1503572 2539289 := bstep (se 2 (by rfl) ⟨952233, by rfl⟩ : syracuseStep 2539289 = 1904467) B1904467
theorem B2711411 : Blo 1503572 2711411 := bstep (se 1 (by rfl) ⟨2033558, by rfl⟩ : syracuseStep 2711411 = 4067117) B4067117
theorem B2539417 : Blo 1503572 2539417 := bstep (se 2 (by rfl) ⟨952281, by rfl⟩ : syracuseStep 2539417 = 1904563) B1904563
theorem B3383243 : Blo 1503572 3383243 := bstep (se 1 (by rfl) ⟨2537432, by rfl⟩ : syracuseStep 3383243 = 5074865) B5074865
theorem B3809227 : Blo 1503572 3809227 := bstep (se 1 (by rfl) ⟨2856920, by rfl⟩ : syracuseStep 3809227 = 5713841) B5713841
theorem B9404419 : Blo 1503572 9404419 := bstep (se 1 (by rfl) ⟨7053314, by rfl⟩ : syracuseStep 9404419 = 14106629) B14106629
theorem B16269335 : Blo 1503572 16269335 := bstep (se 1 (by rfl) ⟨12202001, by rfl⟩ : syracuseStep 16269335 = 24404003) B24404003
theorem B27459607 : Blo 1503572 27459607 := bstep (se 1 (by rfl) ⟨20594705, by rfl⟩ : syracuseStep 27459607 = 41189411) B41189411
theorem B3809339 : Blo 1503572 3809339 := bstep (se 1 (by rfl) ⟨2857004, by rfl⟩ : syracuseStep 3809339 = 5714009) B5714009
theorem B2539579 : Blo 1503572 2539579 := bstep (se 1 (by rfl) ⟨1904684, by rfl⟩ : syracuseStep 2539579 = 3809369) B3809369
theorem B2539721 : Blo 1503572 2539721 := bstep (se 2 (by rfl) ⟨952395, by rfl⟩ : syracuseStep 2539721 = 1904791) B1904791
theorem B3383567 : Blo 1503572 3383567 := bstep (se 1 (by rfl) ⟨2537675, by rfl⟩ : syracuseStep 3383567 = 5075351) B5075351
theorem B3809551 : Blo 1503572 3809551 := bstep (se 1 (by rfl) ⟨2857163, by rfl⟩ : syracuseStep 3809551 = 5714327) B5714327
theorem B3383585 : Blo 1503572 3383585 := bstep (se 2 (by rfl) ⟨1268844, by rfl⟩ : syracuseStep 3383585 = 2537689) B2537689
theorem B5079563 : Blo 1503572 5079563 := bstep (se 1 (by rfl) ⟨3809672, by rfl⟩ : syracuseStep 5079563 = 7619345) B7619345
theorem B3809825 : Blo 1503572 3809825 := bstep (se 2 (by rfl) ⟨1428684, by rfl⟩ : syracuseStep 3809825 = 2857369) B2857369
theorem B6423083 : Blo 1503572 6423083 := bstep (se 1 (by rfl) ⟨4817312, by rfl⟩ : syracuseStep 6423083 = 9634625) B9634625
theorem B4284971 : Blo 1503572 4284971 := bstep (se 1 (by rfl) ⟨3213728, by rfl⟩ : syracuseStep 4284971 = 6427457) B6427457
theorem B3383927 : Blo 1503572 3383927 := bstep (se 1 (by rfl) ⟨2537945, by rfl⟩ : syracuseStep 3383927 = 5075891) B5075891
theorem B5079671 : Blo 1503572 5079671 := bstep (se 1 (by rfl) ⟨3809753, by rfl⟩ : syracuseStep 5079671 = 7619507) B7619507
theorem B3613331 : Blo 1503572 3613331 := bstep (se 1 (by rfl) ⟨2709998, by rfl⟩ : syracuseStep 3613331 = 5419997) B5419997
theorem B9642725 : Blo 1503572 9642725 := bstep (se 4 (by rfl) ⟨904005, by rfl⟩ : syracuseStep 9642725 = 1808011) B1808011
theorem B2032391 : Blo 1503572 2032391 := bstep (se 1 (by rfl) ⟨1524293, by rfl⟩ : syracuseStep 2032391 = 3048587) B3048587
theorem B5710607 : Blo 1503572 5710607 := bstep (se 1 (by rfl) ⟨4282955, by rfl⟩ : syracuseStep 5710607 = 8565911) B8565911
theorem B4285199 : Blo 1503572 4285199 := bstep (se 1 (by rfl) ⟨3213899, by rfl⟩ : syracuseStep 4285199 = 6427799) B6427799
theorem B18301733 : Blo 1503572 18301733 := bstep (se 4 (by rfl) ⟨1715787, by rfl⟩ : syracuseStep 18301733 = 3431575) B3431575
theorem B3384107 : Blo 1503572 3384107 := bstep (se 1 (by rfl) ⟨2538080, by rfl⟩ : syracuseStep 3384107 = 5076161) B5076161
theorem B13386545 : Blo 1503572 13386545 := bstep (se 2 (by rfl) ⟨5019954, by rfl⟩ : syracuseStep 13386545 = 10039909) B10039909
theorem B58663769 : Blo 1503572 58663769 := bstep (se 2 (by rfl) ⟨21998913, by rfl⟩ : syracuseStep 58663769 = 43997827) B43997827
theorem B2540423 : Blo 1503572 2540423 := bstep (se 1 (by rfl) ⟨1905317, by rfl⟩ : syracuseStep 2540423 = 3810635) B3810635
theorem B3384467 : Blo 1503572 3384467 := bstep (se 1 (by rfl) ⟨2538350, by rfl⟩ : syracuseStep 3384467 = 5076701) B5076701
theorem B3384521 : Blo 1503572 3384521 := bstep (se 2 (by rfl) ⟨1269195, by rfl⟩ : syracuseStep 3384521 = 2538391) B2538391
theorem B5080265 : Blo 1503572 5080265 := bstep (se 2 (by rfl) ⟨1905099, by rfl⟩ : syracuseStep 5080265 = 3810199) B3810199
theorem B7619993 : Blo 1503572 7619993 := bstep (se 2 (by rfl) ⟨2857497, by rfl⟩ : syracuseStep 7619993 = 5714995) B5714995
theorem B7226891 : Blo 1503572 7226891 := bstep (se 1 (by rfl) ⟨5420168, by rfl⟩ : syracuseStep 7226891 = 10840337) B10840337
theorem B2442767 : Blo 1503572 2442767 := bstep (se 1 (by rfl) ⟨1832075, by rfl⟩ : syracuseStep 2442767 = 3664151) B3664151
theorem B2033353 : Blo 1503572 2033353 := bstep (se 2 (by rfl) ⟨762507, by rfl⟩ : syracuseStep 2033353 = 1525015) B1525015
theorem B4572929 : Blo 1503572 4572929 := bstep (se 2 (by rfl) ⟨1714848, by rfl⟩ : syracuseStep 4572929 = 3429697) B3429697
theorem B16262927 : Blo 1503572 16262927 := bstep (se 1 (by rfl) ⟨12197195, by rfl⟩ : syracuseStep 16262927 = 24394391) B24394391
theorem B11429747 : Blo 1503572 11429747 := bstep (se 1 (by rfl) ⟨8572310, by rfl⟩ : syracuseStep 11429747 = 17144621) B17144621
theorem B3385223 : Blo 1503572 3385223 := bstep (se 1 (by rfl) ⟨2538917, by rfl⟩ : syracuseStep 3385223 = 5077835) B5077835
theorem B2574215 : Blo 1503572 2574215 := bstep (se 1 (by rfl) ⟨1930661, by rfl⟩ : syracuseStep 2574215 = 3861323) B3861323
theorem B3614753 : Blo 1503572 3614753 := bstep (se 2 (by rfl) ⟨1355532, by rfl⟩ : syracuseStep 3614753 = 2711065) B2711065
theorem B2574379 : Blo 1503572 2574379 := bstep (se 1 (by rfl) ⟨1930784, by rfl⟩ : syracuseStep 2574379 = 3861569) B3861569
theorem B3385403 : Blo 1503572 3385403 := bstep (se 1 (by rfl) ⟨2539052, by rfl⟩ : syracuseStep 3385403 = 5078105) B5078105
theorem B4286611 : Blo 1503572 4286611 := bstep (se 1 (by rfl) ⟨3214958, by rfl⟩ : syracuseStep 4286611 = 6429917) B6429917
theorem B3860665 : Blo 1503572 3860665 := bstep (se 2 (by rfl) ⟨1447749, by rfl⟩ : syracuseStep 3860665 = 2895499) B2895499
theorem B3385529 : Blo 1503572 3385529 := bstep (se 2 (by rfl) ⟨1269573, by rfl⟩ : syracuseStep 3385529 = 2539147) B2539147
theorem B13027529 : Blo 1503572 13027529 := bstep (se 2 (by rfl) ⟨4885323, by rfl⟩ : syracuseStep 13027529 = 9770647) B9770647
theorem B3049787 : Blo 1503572 3049787 := bstep (se 1 (by rfl) ⟨2287340, by rfl⟩ : syracuseStep 3049787 = 4574681) B4574681
theorem B4286839 : Blo 1503572 4286839 := bstep (se 1 (by rfl) ⟨3215129, by rfl⟩ : syracuseStep 4286839 = 6430259) B6430259
theorem B9767303 : Blo 1503572 9767303 := bstep (se 1 (by rfl) ⟨7325477, by rfl⟩ : syracuseStep 9767303 = 14650955) B14650955
theorem B9636317 : Blo 1503572 9636317 := bstep (se 3 (by rfl) ⟨1806809, by rfl⟩ : syracuseStep 9636317 = 3613619) B3613619
theorem B8137219 : Blo 1503572 8137219 := bstep (se 1 (by rfl) ⟨6102914, by rfl⟩ : syracuseStep 8137219 = 12205829) B12205829
theorem B2255375 : Blo 1503572 2255375 := bstep (se 1 (by rfl) ⟨1691531, by rfl⟩ : syracuseStep 2255375 = 3383063) B3383063
theorem B3385871 : Blo 1503572 3385871 := bstep (se 1 (by rfl) ⟨2539403, by rfl⟩ : syracuseStep 3385871 = 5078807) B5078807
theorem B3213857 : Blo 1503572 3213857 := bstep (se 2 (by rfl) ⟨1205196, by rfl⟩ : syracuseStep 3213857 = 2410393) B2410393
theorem B3385889 : Blo 1503572 3385889 := bstep (se 2 (by rfl) ⟨1269708, by rfl⟩ : syracuseStep 3385889 = 2539417) B2539417
theorem B2255417 : Blo 1503572 2255417 := bstep (se 2 (by rfl) ⟨845781, by rfl⟩ : syracuseStep 2255417 = 1691563) B1691563
theorem B2255495 : Blo 1503572 2255495 := bstep (se 1 (by rfl) ⟨1691621, by rfl⟩ : syracuseStep 2255495 = 3383243) B3383243
theorem B2255531 : Blo 1503572 2255531 := bstep (se 1 (by rfl) ⟨1691648, by rfl⟩ : syracuseStep 2255531 = 3383297) B3383297
theorem B2255561 : Blo 1503572 2255561 := bstep (se 2 (by rfl) ⟨845835, by rfl⟩ : syracuseStep 2255561 = 1691671) B1691671
theorem B8129261 : Blo 1503572 8129261 := bstep (se 3 (by rfl) ⟨1524236, by rfl⟩ : syracuseStep 8129261 = 3048473) B3048473
theorem B12200705 : Blo 1503572 12200705 := bstep (se 2 (by rfl) ⟨4575264, by rfl⟩ : syracuseStep 12200705 = 9150529) B9150529
theorem B3615521 : Blo 1503572 3615521 := bstep (se 2 (by rfl) ⟨1355820, by rfl⟩ : syracuseStep 3615521 = 2711641) B2711641
theorem B2255675 : Blo 1503572 2255675 := bstep (se 1 (by rfl) ⟨1691756, by rfl⟩ : syracuseStep 2255675 = 3383513) B3383513
theorem B2255735 : Blo 1503572 2255735 := bstep (se 1 (by rfl) ⟨1691801, by rfl⟩ : syracuseStep 2255735 = 3383603) B3383603
theorem B3386231 : Blo 1503572 3386231 := bstep (se 1 (by rfl) ⟨2539673, by rfl⟩ : syracuseStep 3386231 = 5079347) B5079347
theorem B1903495 : Blo 1503572 1903495 := bstep (se 1 (by rfl) ⟨1427621, by rfl⟩ : syracuseStep 1903495 = 2855243) B2855243
theorem B2255759 : Blo 1503572 2255759 := bstep (se 1 (by rfl) ⟨1691819, by rfl⟩ : syracuseStep 2255759 = 3383639) B3383639
theorem B36588469 : Blo 1503572 36588469 := bstep (se 5 (by rfl) ⟨1715084, by rfl⟩ : syracuseStep 36588469 = 3430169) B3430169
theorem B2255801 : Blo 1503572 2255801 := bstep (se 2 (by rfl) ⟨845925, by rfl⟩ : syracuseStep 2255801 = 1691851) B1691851
theorem B2255879 : Blo 1503572 2255879 := bstep (se 1 (by rfl) ⟨1691909, by rfl⟩ : syracuseStep 2255879 = 3383819) B3383819
theorem B2255915 : Blo 1503572 2255915 := bstep (se 1 (by rfl) ⟨1691936, by rfl⟩ : syracuseStep 2255915 = 3383873) B3383873
theorem B3386411 : Blo 1503572 3386411 := bstep (se 1 (by rfl) ⟨2539808, by rfl⟩ : syracuseStep 3386411 = 5079617) B5079617
theorem B2255945 : Blo 1503572 2255945 := bstep (se 2 (by rfl) ⟨845979, by rfl⟩ : syracuseStep 2255945 = 1691959) B1691959
theorem B16264309 : Blo 1503572 16264309 := bstep (se 5 (by rfl) ⟨762389, by rfl⟩ : syracuseStep 16264309 = 1524779) B1524779
theorem B2256059 : Blo 1503572 2256059 := bstep (se 1 (by rfl) ⟨1692044, by rfl⟩ : syracuseStep 2256059 = 3384089) B3384089
theorem B6425801 : Blo 1503572 6425801 := bstep (se 2 (by rfl) ⟨2409675, by rfl⟩ : syracuseStep 6425801 = 4819351) B4819351
theorem B2256119 : Blo 1503572 2256119 := bstep (se 1 (by rfl) ⟨1692089, by rfl⟩ : syracuseStep 2256119 = 3384179) B3384179
theorem B6860047 : Blo 1503572 6860047 := bstep (se 1 (by rfl) ⟨5145035, by rfl⟩ : syracuseStep 6860047 = 10290071) B10290071
theorem B2256143 : Blo 1503572 2256143 := bstep (se 1 (by rfl) ⟨1692107, by rfl⟩ : syracuseStep 2256143 = 3384215) B3384215
theorem B8572175 : Blo 1503572 8572175 := bstep (se 1 (by rfl) ⟨6429131, by rfl⟩ : syracuseStep 8572175 = 12858263) B12858263
theorem B2141483 : Blo 1503572 2141483 := bstep (se 1 (by rfl) ⟨1606112, by rfl⟩ : syracuseStep 2141483 = 3212225) B3212225
theorem B1903915 : Blo 1503572 1903915 := bstep (se 1 (by rfl) ⟨1427936, by rfl⟩ : syracuseStep 1903915 = 2855873) B2855873
theorem B2256185 : Blo 1503572 2256185 := bstep (se 2 (by rfl) ⟨846069, by rfl⟩ : syracuseStep 2256185 = 1692139) B1692139
theorem B2256263 : Blo 1503572 2256263 := bstep (se 1 (by rfl) ⟨1692197, by rfl⟩ : syracuseStep 2256263 = 3384395) B3384395
theorem B3386771 : Blo 1503572 3386771 := bstep (se 1 (by rfl) ⟨2540078, by rfl⟩ : syracuseStep 3386771 = 5080157) B5080157
theorem B2256299 : Blo 1503572 2256299 := bstep (se 1 (by rfl) ⟨1692224, by rfl⟩ : syracuseStep 2256299 = 3384449) B3384449
theorem B2256329 : Blo 1503572 2256329 := bstep (se 2 (by rfl) ⟨846123, by rfl⟩ : syracuseStep 2256329 = 1692247) B1692247
theorem B3386825 : Blo 1503572 3386825 := bstep (se 2 (by rfl) ⟨1270059, by rfl⟩ : syracuseStep 3386825 = 2540119) B2540119
theorem B1904143 : Blo 1503572 1904143 := bstep (se 1 (by rfl) ⟨1428107, by rfl⟩ : syracuseStep 1904143 = 2856215) B2856215
theorem B2256443 : Blo 1503572 2256443 := bstep (se 1 (by rfl) ⟨1692332, by rfl⟩ : syracuseStep 2256443 = 3384665) B3384665
theorem B28929635 : Blo 1503572 28929635 := bstep (se 1 (by rfl) ⟨21697226, by rfl⟩ : syracuseStep 28929635 = 43394453) B43394453
theorem B2256503 : Blo 1503572 2256503 := bstep (se 1 (by rfl) ⟨1692377, by rfl⟩ : syracuseStep 2256503 = 3384755) B3384755
theorem B3092087 : Blo 1503572 3092087 := bstep (se 1 (by rfl) ⟨2319065, by rfl⟩ : syracuseStep 3092087 = 4638131) B4638131
theorem B2256527 : Blo 1503572 2256527 := bstep (se 1 (by rfl) ⟨1692395, by rfl⟩ : syracuseStep 2256527 = 3384791) B3384791
theorem B2256569 : Blo 1503572 2256569 := bstep (se 2 (by rfl) ⟨846213, by rfl⟩ : syracuseStep 2256569 = 1692427) B1692427
theorem B8564453 : Blo 1503572 8564453 := bstep (se 4 (by rfl) ⟨802917, by rfl⟩ : syracuseStep 8564453 = 1605835) B1605835
theorem B2256647 : Blo 1503572 2256647 := bstep (se 1 (by rfl) ⟨1692485, by rfl⟩ : syracuseStep 2256647 = 3384971) B3384971
theorem B5074703 : Blo 1503572 5074703 := bstep (se 1 (by rfl) ⟨3806027, by rfl⟩ : syracuseStep 5074703 = 7612055) B7612055
theorem B2256683 : Blo 1503572 2256683 := bstep (se 1 (by rfl) ⟨1692512, by rfl⟩ : syracuseStep 2256683 = 3385025) B3385025
theorem B2256713 : Blo 1503572 2256713 := bstep (se 2 (by rfl) ⟨846267, by rfl⟩ : syracuseStep 2256713 = 1692535) B1692535
theorem B7614323 : Blo 1503572 7614323 := bstep (se 1 (by rfl) ⟨5710742, by rfl⟩ : syracuseStep 7614323 = 11421485) B11421485
theorem B1691527 : Blo 1503572 1691527 := bstep (se 1 (by rfl) ⟨1268645, by rfl⟩ : syracuseStep 1691527 = 2537291) B2537291
theorem B5713811 : Blo 1503572 5713811 := bstep (se 1 (by rfl) ⟨4285358, by rfl⟩ : syracuseStep 5713811 = 8570717) B8570717
theorem B2256827 : Blo 1503572 2256827 := bstep (se 1 (by rfl) ⟨1692620, by rfl⟩ : syracuseStep 2256827 = 3385241) B3385241
theorem B2256887 : Blo 1503572 2256887 := bstep (se 1 (by rfl) ⟨1692665, by rfl⟩ : syracuseStep 2256887 = 3385331) B3385331
theorem B2256911 : Blo 1503572 2256911 := bstep (se 1 (by rfl) ⟨1692683, by rfl⟩ : syracuseStep 2256911 = 3385367) B3385367
theorem B5074973 : Blo 1503572 5074973 := bstep (se 3 (by rfl) ⟨951557, by rfl⟩ : syracuseStep 5074973 = 1903115) B1903115
theorem B2256953 : Blo 1503572 2256953 := bstep (se 2 (by rfl) ⟨846357, by rfl⟩ : syracuseStep 2256953 = 1692715) B1692715
theorem B1691707 : Blo 1503572 1691707 := bstep (se 1 (by rfl) ⟨1268780, by rfl⟩ : syracuseStep 1691707 = 2537561) B2537561
theorem B2257031 : Blo 1503572 2257031 := bstep (se 1 (by rfl) ⟨1692773, by rfl⟩ : syracuseStep 2257031 = 3385547) B3385547
theorem B2257067 : Blo 1503572 2257067 := bstep (se 1 (by rfl) ⟨1692800, by rfl⟩ : syracuseStep 2257067 = 3385601) B3385601
theorem B2257097 : Blo 1503572 2257097 := bstep (se 2 (by rfl) ⟨846411, by rfl⟩ : syracuseStep 2257097 = 1692823) B1692823
theorem B1904887 : Blo 1503572 1904887 := bstep (se 1 (by rfl) ⟨1428665, by rfl⟩ : syracuseStep 1904887 = 2857331) B2857331
theorem B12194081 : Blo 1503572 12194081 := bstep (se 2 (by rfl) ⟨4572780, by rfl⟩ : syracuseStep 12194081 = 9145561) B9145561
theorem B2650411 : Blo 1503572 2650411 := bstep (se 1 (by rfl) ⟨1987808, by rfl⟩ : syracuseStep 2650411 = 3975617) B3975617
theorem B2257211 : Blo 1503572 2257211 := bstep (se 1 (by rfl) ⟨1692908, by rfl⟩ : syracuseStep 2257211 = 3385817) B3385817
theorem B7614809 : Blo 1503572 7614809 := bstep (se 2 (by rfl) ⟨2855553, by rfl⟩ : syracuseStep 7614809 = 5711107) B5711107
theorem B2257271 : Blo 1503572 2257271 := bstep (se 1 (by rfl) ⟨1692953, by rfl⟩ : syracuseStep 2257271 = 3385907) B3385907
theorem B1503623 : Blo 1503572 1503623 := bstep (se 1 (by rfl) ⟨1127717, by rfl⟩ : syracuseStep 1503623 = 2255435) B2255435
theorem B1503631 : Blo 1503572 1503631 := bstep (se 1 (by rfl) ⟨1127723, by rfl⟩ : syracuseStep 1503631 = 2255447) B2255447
theorem B2257295 : Blo 1503572 2257295 := bstep (se 1 (by rfl) ⟨1692971, by rfl⟩ : syracuseStep 2257295 = 3385943) B3385943
theorem B19534225 : Blo 1503572 19534225 := bstep (se 2 (by rfl) ⟨7325334, by rfl⟩ : syracuseStep 19534225 = 14650669) B14650669
theorem B9638291 : Blo 1503572 9638291 := bstep (se 1 (by rfl) ⟨7228718, by rfl⟩ : syracuseStep 9638291 = 14457437) B14457437
theorem B2257337 : Blo 1503572 2257337 := bstep (se 2 (by rfl) ⟨846501, by rfl⟩ : syracuseStep 2257337 = 1693003) B1693003
theorem B1503675 : Blo 1503572 1503675 := bstep (se 1 (by rfl) ⟨1127756, by rfl⟩ : syracuseStep 1503675 = 2255513) B2255513
theorem B1503751 : Blo 1503572 1503751 := bstep (se 1 (by rfl) ⟨1127813, by rfl⟩ : syracuseStep 1503751 = 2255627) B2255627
theorem B2257415 : Blo 1503572 2257415 := bstep (se 1 (by rfl) ⟨1693061, by rfl⟩ : syracuseStep 2257415 = 3386123) B3386123
theorem B1503759 : Blo 1503572 1503759 := bstep (se 1 (by rfl) ⟨1127819, by rfl⟩ : syracuseStep 1503759 = 2255639) B2255639
theorem B1692175 : Blo 1503572 1692175 := bstep (se 1 (by rfl) ⟨1269131, by rfl⟩ : syracuseStep 1692175 = 2538263) B2538263
theorem B2257451 : Blo 1503572 2257451 := bstep (se 1 (by rfl) ⟨1693088, by rfl⟩ : syracuseStep 2257451 = 3386177) B3386177
theorem B1503803 : Blo 1503572 1503803 := bstep (se 1 (by rfl) ⟨1127852, by rfl⟩ : syracuseStep 1503803 = 2255705) B2255705
theorem B1905211 : Blo 1503572 1905211 := bstep (se 1 (by rfl) ⟨1428908, by rfl⟩ : syracuseStep 1905211 = 2857817) B2857817
theorem B2257481 : Blo 1503572 2257481 := bstep (se 2 (by rfl) ⟨846555, by rfl⟩ : syracuseStep 2257481 = 1693111) B1693111
theorem B1503879 : Blo 1503572 1503879 := bstep (se 1 (by rfl) ⟨1127909, by rfl⟩ : syracuseStep 1503879 = 2255819) B2255819
theorem B1503887 : Blo 1503572 1503887 := bstep (se 1 (by rfl) ⟨1127915, by rfl⟩ : syracuseStep 1503887 = 2255831) B2255831
theorem B1503931 : Blo 1503572 1503931 := bstep (se 1 (by rfl) ⟨1127948, by rfl⟩ : syracuseStep 1503931 = 2255897) B2255897
theorem B2257595 : Blo 1503572 2257595 := bstep (se 1 (by rfl) ⟨1693196, by rfl⟩ : syracuseStep 2257595 = 3386393) B3386393
theorem B8573633 : Blo 1503572 8573633 := bstep (se 2 (by rfl) ⟨3215112, by rfl⟩ : syracuseStep 8573633 = 6430225) B6430225
theorem B2257655 : Blo 1503572 2257655 := bstep (se 1 (by rfl) ⟨1693241, by rfl⟩ : syracuseStep 2257655 = 3386483) B3386483
theorem B1504007 : Blo 1503572 1504007 := bstep (se 1 (by rfl) ⟨1128005, by rfl⟩ : syracuseStep 1504007 = 2256011) B2256011
theorem B3805967 : Blo 1503572 3805967 := bstep (se 1 (by rfl) ⟨2854475, by rfl⟩ : syracuseStep 3805967 = 5708951) B5708951
theorem B1504015 : Blo 1503572 1504015 := bstep (se 1 (by rfl) ⟨1128011, by rfl⟩ : syracuseStep 1504015 = 2256023) B2256023
theorem B2257679 : Blo 1503572 2257679 := bstep (se 1 (by rfl) ⟨1693259, by rfl⟩ : syracuseStep 2257679 = 3386519) B3386519
theorem B2257721 : Blo 1503572 2257721 := bstep (se 2 (by rfl) ⟨846645, by rfl⟩ : syracuseStep 2257721 = 1693291) B1693291
theorem B1504059 : Blo 1503572 1504059 := bstep (se 1 (by rfl) ⟨1128044, by rfl⟩ : syracuseStep 1504059 = 2256089) B2256089
theorem B9769817 : Blo 1503572 9769817 := bstep (se 2 (by rfl) ⟨3663681, by rfl⟩ : syracuseStep 9769817 = 7327363) B7327363
theorem B4821875 : Blo 1503572 4821875 := bstep (se 1 (by rfl) ⟨3616406, by rfl⟩ : syracuseStep 4821875 = 7232813) B7232813
theorem B1504135 : Blo 1503572 1504135 := bstep (se 1 (by rfl) ⟨1128101, by rfl⟩ : syracuseStep 1504135 = 2256203) B2256203
theorem B2257799 : Blo 1503572 2257799 := bstep (se 1 (by rfl) ⟨1693349, by rfl⟩ : syracuseStep 2257799 = 3386699) B3386699
theorem B1504143 : Blo 1503572 1504143 := bstep (se 1 (by rfl) ⟨1128107, by rfl⟩ : syracuseStep 1504143 = 2256215) B2256215
theorem B3806099 : Blo 1503572 3806099 := bstep (se 1 (by rfl) ⟨2854574, by rfl⟩ : syracuseStep 3806099 = 5709149) B5709149
theorem B2855827 : Blo 1503572 2855827 := bstep (se 1 (by rfl) ⟨2141870, by rfl⟩ : syracuseStep 2855827 = 4283741) B4283741
theorem B14455705 : Blo 1503572 14455705 := bstep (se 2 (by rfl) ⟨5420889, by rfl⟩ : syracuseStep 14455705 = 10841779) B10841779
theorem B2257835 : Blo 1503572 2257835 := bstep (se 1 (by rfl) ⟨1693376, by rfl⟩ : syracuseStep 2257835 = 3386753) B3386753
theorem B1504187 : Blo 1503572 1504187 := bstep (se 1 (by rfl) ⟨1128140, by rfl⟩ : syracuseStep 1504187 = 2256281) B2256281
theorem B2257865 : Blo 1503572 2257865 := bstep (se 2 (by rfl) ⟨846699, by rfl⟩ : syracuseStep 2257865 = 1693399) B1693399
theorem B1504263 : Blo 1503572 1504263 := bstep (se 1 (by rfl) ⟨1128197, by rfl⟩ : syracuseStep 1504263 = 2256395) B2256395
theorem B1692679 : Blo 1503572 1692679 := bstep (se 1 (by rfl) ⟨1269509, by rfl⟩ : syracuseStep 1692679 = 2539019) B2539019
theorem B1504271 : Blo 1503572 1504271 := bstep (se 1 (by rfl) ⟨1128203, by rfl⟩ : syracuseStep 1504271 = 2256407) B2256407
theorem B1504315 : Blo 1503572 1504315 := bstep (se 1 (by rfl) ⟨1128236, by rfl⟩ : syracuseStep 1504315 = 2256473) B2256473
theorem B2257979 : Blo 1503572 2257979 := bstep (se 1 (by rfl) ⟨1693484, by rfl⟩ : syracuseStep 2257979 = 3386969) B3386969
theorem B2856055 : Blo 1503572 2856055 := bstep (se 1 (by rfl) ⟨2142041, by rfl⟩ : syracuseStep 2856055 = 4284083) B4284083
theorem B2143351 : Blo 1503572 2143351 := bstep (se 1 (by rfl) ⟨1607513, by rfl⟩ : syracuseStep 2143351 = 3215027) B3215027
theorem B2258039 : Blo 1503572 2258039 := bstep (se 1 (by rfl) ⟨1693529, by rfl⟩ : syracuseStep 2258039 = 3387059) B3387059
theorem B1504391 : Blo 1503572 1504391 := bstep (se 1 (by rfl) ⟨1128293, by rfl⟩ : syracuseStep 1504391 = 2256587) B2256587
theorem B1504399 : Blo 1503572 1504399 := bstep (se 1 (by rfl) ⟨1128299, by rfl⟩ : syracuseStep 1504399 = 2256599) B2256599
theorem B2258063 : Blo 1503572 2258063 := bstep (se 1 (by rfl) ⟨1693547, by rfl⟩ : syracuseStep 2258063 = 3387095) B3387095
theorem B2258105 : Blo 1503572 2258105 := bstep (se 2 (by rfl) ⟨846789, by rfl⟩ : syracuseStep 2258105 = 1693579) B1693579
theorem B1504443 : Blo 1503572 1504443 := bstep (se 1 (by rfl) ⟨1128332, by rfl⟩ : syracuseStep 1504443 = 2256665) B2256665
theorem B1692859 : Blo 1503572 1692859 := bstep (se 1 (by rfl) ⟨1269644, by rfl⟩ : syracuseStep 1692859 = 2539289) B2539289
theorem B1807607 : Blo 1503572 1807607 := bstep (se 1 (by rfl) ⟨1355705, by rfl⟩ : syracuseStep 1807607 = 2711411) B2711411
theorem B1504519 : Blo 1503572 1504519 := bstep (se 1 (by rfl) ⟨1128389, by rfl⟩ : syracuseStep 1504519 = 2256779) B2256779
theorem B1504527 : Blo 1503572 1504527 := bstep (se 1 (by rfl) ⟨1128395, by rfl⟩ : syracuseStep 1504527 = 2256791) B2256791
theorem B1504571 : Blo 1503572 1504571 := bstep (se 1 (by rfl) ⟨1128428, by rfl⟩ : syracuseStep 1504571 = 2256857) B2256857
theorem B1504647 : Blo 1503572 1504647 := bstep (se 1 (by rfl) ⟨1128485, by rfl⟩ : syracuseStep 1504647 = 2256971) B2256971
theorem B1504655 : Blo 1503572 1504655 := bstep (se 1 (by rfl) ⟨1128491, by rfl⟩ : syracuseStep 1504655 = 2256983) B2256983
theorem B8131985 : Blo 1503572 8131985 := bstep (se 2 (by rfl) ⟨3049494, by rfl⟩ : syracuseStep 8131985 = 6098989) B6098989
theorem B5076377 : Blo 1503572 5076377 := bstep (se 2 (by rfl) ⟨1903641, by rfl⟩ : syracuseStep 5076377 = 3807283) B3807283
theorem B1504699 : Blo 1503572 1504699 := bstep (se 1 (by rfl) ⟨1128524, by rfl⟩ : syracuseStep 1504699 = 2257049) B2257049
theorem B1504775 : Blo 1503572 1504775 := bstep (se 1 (by rfl) ⟨1128581, by rfl⟩ : syracuseStep 1504775 = 2257163) B2257163
theorem B5715467 : Blo 1503572 5715467 := bstep (se 1 (by rfl) ⟨4286600, by rfl⟩ : syracuseStep 5715467 = 8573201) B8573201
theorem B1504783 : Blo 1503572 1504783 := bstep (se 1 (by rfl) ⟨1128587, by rfl⟩ : syracuseStep 1504783 = 2257175) B2257175
theorem B16258603 : Blo 1503572 16258603 := bstep (se 1 (by rfl) ⟨12193952, by rfl⟩ : syracuseStep 16258603 = 24387905) B24387905
theorem B1504827 : Blo 1503572 1504827 := bstep (se 1 (by rfl) ⟨1128620, by rfl⟩ : syracuseStep 1504827 = 2257241) B2257241
theorem B1504903 : Blo 1503572 1504903 := bstep (se 1 (by rfl) ⟨1128677, by rfl⟩ : syracuseStep 1504903 = 2257355) B2257355
theorem B1504911 : Blo 1503572 1504911 := bstep (se 1 (by rfl) ⟨1128683, by rfl⟩ : syracuseStep 1504911 = 2257367) B2257367
theorem B1693327 : Blo 1503572 1693327 := bstep (se 1 (by rfl) ⟨1269995, by rfl⟩ : syracuseStep 1693327 = 2539991) B2539991
theorem B1504955 : Blo 1503572 1504955 := bstep (se 1 (by rfl) ⟨1128716, by rfl⟩ : syracuseStep 1504955 = 2257433) B2257433
theorem B17381081 : Blo 1503572 17381081 := bstep (se 2 (by rfl) ⟨6517905, by rfl⟩ : syracuseStep 17381081 = 13035811) B13035811
theorem B14456549 : Blo 1503572 14456549 := bstep (se 4 (by rfl) ⟨1355301, by rfl⟩ : syracuseStep 14456549 = 2710603) B2710603
theorem B1505031 : Blo 1503572 1505031 := bstep (se 1 (by rfl) ⟨1128773, by rfl⟩ : syracuseStep 1505031 = 2257547) B2257547
theorem B1505039 : Blo 1503572 1505039 := bstep (se 1 (by rfl) ⟨1128779, by rfl⟩ : syracuseStep 1505039 = 2257559) B2257559
theorem B1505083 : Blo 1503572 1505083 := bstep (se 1 (by rfl) ⟨1128812, by rfl⟩ : syracuseStep 1505083 = 2257625) B2257625
theorem B1505159 : Blo 1503572 1505159 := bstep (se 1 (by rfl) ⟨1128869, by rfl⟩ : syracuseStep 1505159 = 2257739) B2257739
theorem B1505167 : Blo 1503572 1505167 := bstep (se 1 (by rfl) ⟨1128875, by rfl⟩ : syracuseStep 1505167 = 2257751) B2257751
theorem B1808299 : Blo 1503572 1808299 := bstep (se 1 (by rfl) ⟨1356224, by rfl⟩ : syracuseStep 1808299 = 2712449) B2712449
theorem B1505211 : Blo 1503572 1505211 := bstep (se 1 (by rfl) ⟨1128908, by rfl⟩ : syracuseStep 1505211 = 2257817) B2257817
theorem B3807233 : Blo 1503572 3807233 := bstep (se 2 (by rfl) ⟨1427712, by rfl⟩ : syracuseStep 3807233 = 2855425) B2855425
theorem B1505287 : Blo 1503572 1505287 := bstep (se 1 (by rfl) ⟨1128965, by rfl⟩ : syracuseStep 1505287 = 2257931) B2257931
theorem B1505295 : Blo 1503572 1505295 := bstep (se 1 (by rfl) ⟨1128971, by rfl⟩ : syracuseStep 1505295 = 2257943) B2257943
theorem B1505339 : Blo 1503572 1505339 := bstep (se 1 (by rfl) ⟨1129004, by rfl⟩ : syracuseStep 1505339 = 2258009) B2258009
theorem B5077079 : Blo 1503572 5077079 := bstep (se 1 (by rfl) ⟨3807809, by rfl⟩ : syracuseStep 5077079 = 7615619) B7615619
theorem B2709623 : Blo 1503572 2709623 := bstep (se 1 (by rfl) ⟨2032217, by rfl⟩ : syracuseStep 2709623 = 4064435) B4064435
theorem B1505415 : Blo 1503572 1505415 := bstep (se 1 (by rfl) ⟨1129061, by rfl⟩ : syracuseStep 1505415 = 2258123) B2258123
theorem B1505423 : Blo 1503572 1505423 := bstep (se 1 (by rfl) ⟨1129067, by rfl⟩ : syracuseStep 1505423 = 2258135) B2258135
theorem B13727981 : Blo 1503572 13727981 := bstep (se 3 (by rfl) ⟨2573996, by rfl⟩ : syracuseStep 13727981 = 5147993) B5147993
theorem B4282625 : Blo 1503572 4282625 := bstep (se 2 (by rfl) ⟨1605984, by rfl⟩ : syracuseStep 4282625 = 3211969) B3211969
theorem B2537743 : Blo 1503572 2537743 := bstep (se 1 (by rfl) ⟨1903307, by rfl⟩ : syracuseStep 2537743 = 3806615) B3806615
theorem B8354063 : Blo 1503572 8354063 := bstep (se 1 (by rfl) ⟨6265547, by rfl⟩ : syracuseStep 8354063 = 12531095) B12531095
theorem B4282739 : Blo 1503572 4282739 := bstep (se 1 (by rfl) ⟨3212054, by rfl⟩ : syracuseStep 4282739 = 6424109) B6424109
theorem B3807607 : Blo 1503572 3807607 := bstep (se 1 (by rfl) ⟨2855705, by rfl⟩ : syracuseStep 3807607 = 5711411) B5711411
theorem B7616915 : Blo 1503572 7616915 := bstep (se 1 (by rfl) ⟨5712686, by rfl⟩ : syracuseStep 7616915 = 11425373) B11425373
theorem B5077565 : Blo 1503572 5077565 := bstep (se 3 (by rfl) ⟨952043, by rfl⟩ : syracuseStep 5077565 = 1904087) B1904087
theorem B2857619 : Blo 1503572 2857619 := bstep (se 1 (by rfl) ⟨2143214, by rfl⟩ : syracuseStep 2857619 = 4286429) B4286429
theorem B16259777 : Blo 1503572 16259777 := bstep (se 2 (by rfl) ⟨6097416, by rfl⟩ : syracuseStep 16259777 = 12194833) B12194833
theorem B12851905 : Blo 1503572 12851905 := bstep (se 2 (by rfl) ⟨4819464, by rfl⟩ : syracuseStep 12851905 = 9638929) B9638929
theorem B4283081 : Blo 1503572 4283081 := bstep (se 2 (by rfl) ⟨1606155, by rfl⟩ : syracuseStep 4283081 = 3212311) B3212311
theorem B2857673 : Blo 1503572 2857673 := bstep (se 2 (by rfl) ⟨1071627, by rfl⟩ : syracuseStep 2857673 = 2143255) B2143255
theorem B3808043 : Blo 1503572 3808043 := bstep (se 1 (by rfl) ⟨2856032, by rfl⟩ : syracuseStep 3808043 = 5712065) B5712065
theorem B2538283 : Blo 1503572 2538283 := bstep (se 1 (by rfl) ⟨1903712, by rfl⟩ : syracuseStep 2538283 = 3807425) B3807425
theorem B2857771 : Blo 1503572 2857771 := bstep (se 1 (by rfl) ⟨2143328, by rfl⟩ : syracuseStep 2857771 = 4286657) B4286657
theorem B52108181 : Blo 1503572 52108181 := bstep (se 6 (by rfl) ⟨1221285, by rfl⟩ : syracuseStep 52108181 = 2442571) B2442571
theorem B2538425 : Blo 1503572 2538425 := bstep (se 2 (by rfl) ⟨951909, by rfl⟩ : syracuseStep 2538425 = 1903819) B1903819
theorem B82394117 : Blo 1503572 82394117 := bstep (se 4 (by rfl) ⟨7724448, by rfl⟩ : syracuseStep 82394117 = 15448897) B15448897
theorem B2857999 : Blo 1503572 2857999 := bstep (se 1 (by rfl) ⟨2143499, by rfl⟩ : syracuseStep 2857999 = 4286999) B4286999
theorem B12860653 : Blo 1503572 12860653 := bstep (se 3 (by rfl) ⟨2411372, by rfl⟩ : syracuseStep 12860653 = 4822745) B4822745
theorem B69483835 : Blo 1503572 69483835 := bstep (se 1 (by rfl) ⟨52112876, by rfl⟩ : syracuseStep 69483835 = 104225753) B104225753
theorem B5422621 : Blo 1503572 5422621 := bstep (se 3 (by rfl) ⟨1016741, by rfl⟩ : syracuseStep 5422621 = 2033483) B2033483
theorem B3808883 : Blo 1503572 3808883 := bstep (se 1 (by rfl) ⟨2856662, by rfl⟩ : syracuseStep 3808883 = 5713325) B5713325
theorem B2539127 : Blo 1503572 2539127 := bstep (se 1 (by rfl) ⟨1904345, by rfl⟩ : syracuseStep 2539127 = 3808691) B3808691
theorem B3808903 : Blo 1503572 3808903 := bstep (se 1 (by rfl) ⟨2856677, by rfl⟩ : syracuseStep 3808903 = 5713355) B5713355
theorem B17137331 : Blo 1503572 17137331 := bstep (se 1 (by rfl) ⟨12852998, by rfl⟩ : syracuseStep 17137331 = 25705997) B25705997
theorem B3858121 : Blo 1503572 3858121 := bstep (se 2 (by rfl) ⟨1446795, by rfl⟩ : syracuseStep 3858121 = 2893591) B2893591
theorem B3383099 : Blo 1503572 3383099 := bstep (se 1 (by rfl) ⟨2537324, by rfl⟩ : syracuseStep 3383099 = 5074649) B5074649
theorem B3809177 : Blo 1503572 3809177 := bstep (se 2 (by rfl) ⟨1428441, by rfl⟩ : syracuseStep 3809177 = 2856883) B2856883
theorem B3383225 : Blo 1503572 3383225 := bstep (se 2 (by rfl) ⟨1268709, by rfl⟩ : syracuseStep 3383225 = 2537419) B2537419
theorem B5078969 : Blo 1503572 5078969 := bstep (se 2 (by rfl) ⟨1904613, by rfl⟩ : syracuseStep 5078969 = 3809227) B3809227
theorem B10846223 : Blo 1503572 10846223 := bstep (se 1 (by rfl) ⟨8134667, by rfl⟩ : syracuseStep 10846223 = 16269335) B16269335
theorem B3383315 : Blo 1503572 3383315 := bstep (se 1 (by rfl) ⟨2537486, by rfl⟩ : syracuseStep 3383315 = 5074973) B5074973
theorem B2539559 : Blo 1503572 2539559 := bstep (se 1 (by rfl) ⟨1904669, by rfl⟩ : syracuseStep 2539559 = 3809339) B3809339
theorem B3432505 : Blo 1503572 3432505 := bstep (se 2 (by rfl) ⟨1287189, by rfl⟩ : syracuseStep 3432505 = 2574379) B2574379
theorem B7225661 : Blo 1503572 7225661 := bstep (se 3 (by rfl) ⟨1354811, by rfl⟩ : syracuseStep 7225661 = 2709623) B2709623
theorem B2539849 : Blo 1503572 2539849 := bstep (se 2 (by rfl) ⟨952443, by rfl⟩ : syracuseStep 2539849 = 1904887) B1904887
theorem B3383657 : Blo 1503572 3383657 := bstep (se 2 (by rfl) ⟨1268871, by rfl⟩ : syracuseStep 3383657 = 2537743) B2537743
theorem B5079401 : Blo 1503572 5079401 := bstep (se 2 (by rfl) ⟨1904775, by rfl⟩ : syracuseStep 5079401 = 3809551) B3809551
theorem B2539883 : Blo 1503572 2539883 := bstep (se 1 (by rfl) ⟨1904912, by rfl⟩ : syracuseStep 2539883 = 3809825) B3809825
theorem B2408887 : Blo 1503572 2408887 := bstep (se 1 (by rfl) ⟨1806665, by rfl⟩ : syracuseStep 2408887 = 3613331) B3613331
theorem B6513211 : Blo 1503572 6513211 := bstep (se 1 (by rfl) ⟨4884908, by rfl⟩ : syracuseStep 6513211 = 9769817) B9769817
theorem B2540281 : Blo 1503572 2540281 := bstep (se 2 (by rfl) ⟨952605, by rfl⟩ : syracuseStep 2540281 = 1905211) B1905211
theorem B5710621 : Blo 1503572 5710621 := bstep (se 3 (by rfl) ⟨1070741, by rfl⟩ : syracuseStep 5710621 = 2141483) B2141483
theorem B625746869 : Blo 1503572 625746869 := bstep (se 5 (by rfl) ⟨29331884, by rfl⟩ : syracuseStep 625746869 = 58663769) B58663769
theorem B3384251 : Blo 1503572 3384251 := bstep (se 1 (by rfl) ⟨2538188, by rfl⟩ : syracuseStep 3384251 = 5076377) B5076377
theorem B5079995 : Blo 1503572 5079995 := bstep (se 1 (by rfl) ⟨3809996, by rfl⟩ : syracuseStep 5079995 = 7619993) B7619993
theorem B4817927 : Blo 1503572 4817927 := bstep (se 1 (by rfl) ⟨3613445, by rfl⟩ : syracuseStep 4817927 = 7226891) B7226891
theorem B3810311 : Blo 1503572 3810311 := bstep (se 1 (by rfl) ⟨2857733, by rfl⟩ : syracuseStep 3810311 = 5715467) B5715467
theorem B3384377 : Blo 1503572 3384377 := bstep (se 2 (by rfl) ⟨1269141, by rfl⟩ : syracuseStep 3384377 = 2538283) B2538283
theorem B3810361 : Blo 1503572 3810361 := bstep (se 2 (by rfl) ⟨1428885, by rfl⟩ : syracuseStep 3810361 = 2857771) B2857771
theorem B3048619 : Blo 1503572 3048619 := bstep (se 1 (by rfl) ⟨2286464, by rfl⟩ : syracuseStep 3048619 = 4572929) B4572929
theorem B48784625 : Blo 1503572 48784625 := bstep (se 2 (by rfl) ⟨18294234, by rfl⟩ : syracuseStep 48784625 = 36588469) B36588469
theorem B7619831 : Blo 1503572 7619831 := bstep (se 1 (by rfl) ⟨5714873, by rfl⟩ : syracuseStep 7619831 = 11429747) B11429747
theorem B3810665 : Blo 1503572 3810665 := bstep (se 2 (by rfl) ⟨1428999, by rfl⟩ : syracuseStep 3810665 = 2857999) B2857999
theorem B2409835 : Blo 1503572 2409835 := bstep (se 1 (by rfl) ⟨1807376, by rfl⟩ : syracuseStep 2409835 = 3614753) B3614753
theorem B3384719 : Blo 1503572 3384719 := bstep (se 1 (by rfl) ⟨2538539, by rfl⟩ : syracuseStep 3384719 = 5077079) B5077079
theorem B8570285 : Blo 1503572 8570285 := bstep (se 3 (by rfl) ⟨1606928, by rfl⟩ : syracuseStep 8570285 = 3213857) B3213857
theorem B8685019 : Blo 1503572 8685019 := bstep (se 1 (by rfl) ⟨6513764, by rfl⟩ : syracuseStep 8685019 = 13027529) B13027529
theorem B21685745 : Blo 1503572 21685745 := bstep (se 2 (by rfl) ⟨8132154, by rfl⟩ : syracuseStep 21685745 = 16264309) B16264309
theorem B9151987 : Blo 1503572 9151987 := bstep (se 1 (by rfl) ⟨6863990, by rfl⟩ : syracuseStep 9151987 = 13727981) B13727981
theorem B2033191 : Blo 1503572 2033191 := bstep (se 1 (by rfl) ⟨1524893, by rfl⟩ : syracuseStep 2033191 = 3049787) B3049787
theorem B17147537 : Blo 1503572 17147537 := bstep (se 2 (by rfl) ⟨6430326, by rfl⟩ : syracuseStep 17147537 = 12860653) B12860653
theorem B6424211 : Blo 1503572 6424211 := bstep (se 1 (by rfl) ⟨4818158, by rfl⟩ : syracuseStep 6424211 = 9636317) B9636317
theorem B3385043 : Blo 1503572 3385043 := bstep (se 1 (by rfl) ⟨2538782, by rfl⟩ : syracuseStep 3385043 = 5077565) B5077565
theorem B7620317 : Blo 1503572 7620317 := bstep (se 3 (by rfl) ⟨1428809, by rfl⟩ : syracuseStep 7620317 = 2857619) B2857619
theorem B10839851 : Blo 1503572 10839851 := bstep (se 1 (by rfl) ⟨8129888, by rfl⟩ : syracuseStep 10839851 = 16259777) B16259777
theorem B54929411 : Blo 1503572 54929411 := bstep (se 1 (by rfl) ⟨41197058, by rfl⟩ : syracuseStep 54929411 = 82394117) B82394117
theorem B21678137 : Blo 1503572 21678137 := bstep (se 2 (by rfl) ⟨8129301, by rfl⟩ : syracuseStep 21678137 = 16258603) B16258603
theorem B19286423 : Blo 1503572 19286423 := bstep (se 1 (by rfl) ⟨14464817, by rfl⟩ : syracuseStep 19286423 = 28929635) B28929635
theorem B2255369 : Blo 1503572 2255369 := bstep (se 2 (by rfl) ⟨845763, by rfl⟩ : syracuseStep 2255369 = 1691527) B1691527
theorem B2255399 : Blo 1503572 2255399 := bstep (se 1 (by rfl) ⟨1691549, by rfl⟩ : syracuseStep 2255399 = 3383099) B3383099
theorem B2411065 : Blo 1503572 2411065 := bstep (se 2 (by rfl) ⟨904149, by rfl⟩ : syracuseStep 2411065 = 1808299) B1808299
theorem B2255483 : Blo 1503572 2255483 := bstep (se 1 (by rfl) ⟨1691612, by rfl⟩ : syracuseStep 2255483 = 3383225) B3383225
theorem B3385979 : Blo 1503572 3385979 := bstep (se 1 (by rfl) ⟨2539484, by rfl⟩ : syracuseStep 3385979 = 5078969) B5078969
theorem B36612809 : Blo 1503572 36612809 := bstep (se 2 (by rfl) ⟨13729803, by rfl⟩ : syracuseStep 36612809 = 27459607) B27459607
theorem B2255609 : Blo 1503572 2255609 := bstep (se 2 (by rfl) ⟨845853, by rfl⟩ : syracuseStep 2255609 = 1691707) B1691707
theorem B3386105 : Blo 1503572 3386105 := bstep (se 2 (by rfl) ⟨1269789, by rfl⟩ : syracuseStep 3386105 = 2539579) B2539579
theorem B2255711 : Blo 1503572 2255711 := bstep (se 1 (by rfl) ⟨1691783, by rfl⟩ : syracuseStep 2255711 = 3383567) B3383567
theorem B8129387 : Blo 1503572 8129387 := bstep (se 1 (by rfl) ⟨6097040, by rfl⟩ : syracuseStep 8129387 = 12194081) B12194081
theorem B2255723 : Blo 1503572 2255723 := bstep (se 1 (by rfl) ⟨1691792, by rfl⟩ : syracuseStep 2255723 = 3383585) B3383585
theorem B6425527 : Blo 1503572 6425527 := bstep (se 1 (by rfl) ⟨4819145, by rfl⟩ : syracuseStep 6425527 = 9638291) B9638291
theorem B3386375 : Blo 1503572 3386375 := bstep (se 1 (by rfl) ⟨2539781, by rfl⟩ : syracuseStep 3386375 = 5079563) B5079563
theorem B3533881 : Blo 1503572 3533881 := bstep (se 2 (by rfl) ⟨1325205, by rfl⟩ : syracuseStep 3533881 = 2650411) B2650411
theorem B2255951 : Blo 1503572 2255951 := bstep (se 1 (by rfl) ⟨1691963, by rfl⟩ : syracuseStep 2255951 = 3383927) B3383927
theorem B3386447 : Blo 1503572 3386447 := bstep (se 1 (by rfl) ⟨2539835, by rfl⟩ : syracuseStep 3386447 = 5079671) B5079671
theorem B26045633 : Blo 1503572 26045633 := bstep (se 2 (by rfl) ⟨9767112, by rfl⟩ : syracuseStep 26045633 = 19534225) B19534225
theorem B12201155 : Blo 1503572 12201155 := bstep (se 1 (by rfl) ⟨9150866, by rfl⟩ : syracuseStep 12201155 = 18301733) B18301733
theorem B2256071 : Blo 1503572 2256071 := bstep (se 1 (by rfl) ⟨1692053, by rfl⟩ : syracuseStep 2256071 = 3384107) B3384107
theorem B8924363 : Blo 1503572 8924363 := bstep (se 1 (by rfl) ⟨6693272, by rfl⟩ : syracuseStep 8924363 = 13386545) B13386545
theorem B3214583 : Blo 1503572 3214583 := bstep (se 1 (by rfl) ⟨2410937, by rfl⟩ : syracuseStep 3214583 = 4821875) B4821875
theorem B11431205 : Blo 1503572 11431205 := bstep (se 4 (by rfl) ⟨1071675, by rfl⟩ : syracuseStep 11431205 = 2143351) B2143351
theorem B4820285 : Blo 1503572 4820285 := bstep (se 3 (by rfl) ⟨903803, by rfl⟩ : syracuseStep 4820285 = 1807607) B1807607
theorem B10849625 : Blo 1503572 10849625 := bstep (se 2 (by rfl) ⟨4068609, by rfl⟩ : syracuseStep 10849625 = 8137219) B8137219
theorem B2256233 : Blo 1503572 2256233 := bstep (se 2 (by rfl) ⟨846087, by rfl⟩ : syracuseStep 2256233 = 1692175) B1692175
theorem B22277501 : Blo 1503572 22277501 := bstep (se 3 (by rfl) ⟨4177031, by rfl⟩ : syracuseStep 22277501 = 8354063) B8354063
theorem B2256311 : Blo 1503572 2256311 := bstep (se 1 (by rfl) ⟨1692233, by rfl⟩ : syracuseStep 2256311 = 3384467) B3384467
theorem B2256347 : Blo 1503572 2256347 := bstep (se 1 (by rfl) ⟨1692260, by rfl⟩ : syracuseStep 2256347 = 3384521) B3384521
theorem B3386843 : Blo 1503572 3386843 := bstep (se 1 (by rfl) ⟨2540132, by rfl⟩ : syracuseStep 3386843 = 5080265) B5080265
theorem B20590213 : Blo 1503572 20590213 := bstep (se 4 (by rfl) ⟨1930332, by rfl⟩ : syracuseStep 20590213 = 3860665) B3860665
theorem B11587387 : Blo 1503572 11587387 := bstep (se 1 (by rfl) ⟨8690540, by rfl⟩ : syracuseStep 11587387 = 17381081) B17381081
theorem B9637699 : Blo 1503572 9637699 := bstep (se 1 (by rfl) ⟨7228274, by rfl⟩ : syracuseStep 9637699 = 14456549) B14456549
theorem B10841951 : Blo 1503572 10841951 := bstep (se 1 (by rfl) ⟨8131463, by rfl⟩ : syracuseStep 10841951 = 16262927) B16262927
theorem B2256815 : Blo 1503572 2256815 := bstep (se 1 (by rfl) ⟨1692611, by rfl⟩ : syracuseStep 2256815 = 3385223) B3385223
theorem B1716143 : Blo 1503572 1716143 := bstep (se 1 (by rfl) ⟨1287107, by rfl⟩ : syracuseStep 1716143 = 2574215) B2574215
theorem B2256905 : Blo 1503572 2256905 := bstep (se 2 (by rfl) ⟨846339, by rfl⟩ : syracuseStep 2256905 = 1692679) B1692679
theorem B2256935 : Blo 1503572 2256935 := bstep (se 1 (by rfl) ⟨1692701, by rfl⟩ : syracuseStep 2256935 = 3385403) B3385403
theorem B2257019 : Blo 1503572 2257019 := bstep (se 1 (by rfl) ⟨1692764, by rfl⟩ : syracuseStep 2257019 = 3385529) B3385529
theorem B2855083 : Blo 1503572 2855083 := bstep (se 1 (by rfl) ⟨2141312, by rfl⟩ : syracuseStep 2855083 = 4282625) B4282625
theorem B2855159 : Blo 1503572 2855159 := bstep (se 1 (by rfl) ⟨2141369, by rfl⟩ : syracuseStep 2855159 = 4282739) B4282739
theorem B2257145 : Blo 1503572 2257145 := bstep (se 2 (by rfl) ⟨846429, by rfl⟩ : syracuseStep 2257145 = 1692859) B1692859
theorem B1503583 : Blo 1503572 1503583 := bstep (se 1 (by rfl) ⟨1127687, by rfl⟩ : syracuseStep 1503583 = 2255375) B2255375
theorem B2257247 : Blo 1503572 2257247 := bstep (se 1 (by rfl) ⟨1692935, by rfl⟩ : syracuseStep 2257247 = 3385871) B3385871
theorem B9146729 : Blo 1503572 9146729 := bstep (se 2 (by rfl) ⟨3430023, by rfl⟩ : syracuseStep 9146729 = 6860047) B6860047
theorem B2257259 : Blo 1503572 2257259 := bstep (se 1 (by rfl) ⟨1692944, by rfl⟩ : syracuseStep 2257259 = 3385889) B3385889
theorem B1503611 : Blo 1503572 1503611 := bstep (se 1 (by rfl) ⟨1127708, by rfl⟩ : syracuseStep 1503611 = 2255417) B2255417
theorem B1503663 : Blo 1503572 1503663 := bstep (se 1 (by rfl) ⟨1127747, by rfl⟩ : syracuseStep 1503663 = 2255495) B2255495
theorem B1503687 : Blo 1503572 1503687 := bstep (se 1 (by rfl) ⟨1127765, by rfl⟩ : syracuseStep 1503687 = 2255531) B2255531
theorem B1503707 : Blo 1503572 1503707 := bstep (se 1 (by rfl) ⟨1127780, by rfl⟩ : syracuseStep 1503707 = 2255561) B2255561
theorem B2855387 : Blo 1503572 2855387 := bstep (se 1 (by rfl) ⟨2141540, by rfl⟩ : syracuseStep 2855387 = 4283081) B4283081
theorem B1905115 : Blo 1503572 1905115 := bstep (se 1 (by rfl) ⟨1428836, by rfl⟩ : syracuseStep 1905115 = 2857673) B2857673
theorem B5419507 : Blo 1503572 5419507 := bstep (se 1 (by rfl) ⟨4064630, by rfl⟩ : syracuseStep 5419507 = 8129261) B8129261
theorem B1503783 : Blo 1503572 1503783 := bstep (se 1 (by rfl) ⟨1127837, by rfl⟩ : syracuseStep 1503783 = 2255675) B2255675
theorem B1503823 : Blo 1503572 1503823 := bstep (se 1 (by rfl) ⟨1127867, by rfl⟩ : syracuseStep 1503823 = 2255735) B2255735
theorem B2257487 : Blo 1503572 2257487 := bstep (se 1 (by rfl) ⟨1693115, by rfl⟩ : syracuseStep 2257487 = 3386231) B3386231
theorem B1503839 : Blo 1503572 1503839 := bstep (se 1 (by rfl) ⟨1127879, by rfl⟩ : syracuseStep 1503839 = 2255759) B2255759
theorem B34738787 : Blo 1503572 34738787 := bstep (se 1 (by rfl) ⟨26054090, by rfl⟩ : syracuseStep 34738787 = 52108181) B52108181
theorem B1503867 : Blo 1503572 1503867 := bstep (se 1 (by rfl) ⟨1127900, by rfl⟩ : syracuseStep 1503867 = 2255801) B2255801
theorem B1692283 : Blo 1503572 1692283 := bstep (se 1 (by rfl) ⟨1269212, by rfl⟩ : syracuseStep 1692283 = 2538425) B2538425
theorem B1503919 : Blo 1503572 1503919 := bstep (se 1 (by rfl) ⟨1127939, by rfl⟩ : syracuseStep 1503919 = 2255879) B2255879
theorem B5419709 : Blo 1503572 5419709 := bstep (se 3 (by rfl) ⟨1016195, by rfl⟩ : syracuseStep 5419709 = 2032391) B2032391
theorem B1503943 : Blo 1503572 1503943 := bstep (se 1 (by rfl) ⟨1127957, by rfl⟩ : syracuseStep 1503943 = 2255915) B2255915
theorem B2257607 : Blo 1503572 2257607 := bstep (se 1 (by rfl) ⟨1693205, by rfl⟩ : syracuseStep 2257607 = 3386411) B3386411
theorem B7230161 : Blo 1503572 7230161 := bstep (se 2 (by rfl) ⟨2711310, by rfl⟩ : syracuseStep 7230161 = 5422621) B5422621
theorem B1503963 : Blo 1503572 1503963 := bstep (se 1 (by rfl) ⟨1127972, by rfl⟩ : syracuseStep 1503963 = 2255945) B2255945
theorem B1504039 : Blo 1503572 1504039 := bstep (se 1 (by rfl) ⟨1128029, by rfl⟩ : syracuseStep 1504039 = 2256059) B2256059
theorem B1504079 : Blo 1503572 1504079 := bstep (se 1 (by rfl) ⟨1128059, by rfl⟩ : syracuseStep 1504079 = 2256119) B2256119
theorem B1504095 : Blo 1503572 1504095 := bstep (se 1 (by rfl) ⟨1128071, by rfl⟩ : syracuseStep 1504095 = 2256143) B2256143
theorem B5714783 : Blo 1503572 5714783 := bstep (se 1 (by rfl) ⟨4286087, by rfl⟩ : syracuseStep 5714783 = 8572175) B8572175
theorem B2257769 : Blo 1503572 2257769 := bstep (se 2 (by rfl) ⟨846663, by rfl⟩ : syracuseStep 2257769 = 1693327) B1693327
theorem B1504123 : Blo 1503572 1504123 := bstep (se 1 (by rfl) ⟨1128092, by rfl⟩ : syracuseStep 1504123 = 2256185) B2256185
theorem B1504175 : Blo 1503572 1504175 := bstep (se 1 (by rfl) ⟨1128131, by rfl⟩ : syracuseStep 1504175 = 2256263) B2256263
theorem B2257847 : Blo 1503572 2257847 := bstep (se 1 (by rfl) ⟨1693385, by rfl⟩ : syracuseStep 2257847 = 3386771) B3386771
theorem B1504199 : Blo 1503572 1504199 := bstep (se 1 (by rfl) ⟨1128149, by rfl⟩ : syracuseStep 1504199 = 2256299) B2256299
theorem B1504219 : Blo 1503572 1504219 := bstep (se 1 (by rfl) ⟨1128164, by rfl⟩ : syracuseStep 1504219 = 2256329) B2256329
theorem B2257883 : Blo 1503572 2257883 := bstep (se 1 (by rfl) ⟨1693412, by rfl⟩ : syracuseStep 2257883 = 3386825) B3386825
theorem B1504295 : Blo 1503572 1504295 := bstep (se 1 (by rfl) ⟨1128221, by rfl⟩ : syracuseStep 1504295 = 2256443) B2256443
theorem B1504335 : Blo 1503572 1504335 := bstep (se 1 (by rfl) ⟨1128251, by rfl⟩ : syracuseStep 1504335 = 2256503) B2256503
theorem B1692751 : Blo 1503572 1692751 := bstep (se 1 (by rfl) ⟨1269563, by rfl⟩ : syracuseStep 1692751 = 2539127) B2539127
theorem B2061391 : Blo 1503572 2061391 := bstep (se 1 (by rfl) ⟨1546043, by rfl⟩ : syracuseStep 2061391 = 3092087) B3092087
theorem B1504351 : Blo 1503572 1504351 := bstep (se 1 (by rfl) ⟨1128263, by rfl⟩ : syracuseStep 1504351 = 2256527) B2256527
theorem B11424887 : Blo 1503572 11424887 := bstep (se 1 (by rfl) ⟨8568665, by rfl⟩ : syracuseStep 11424887 = 17137331) B17137331
theorem B1504379 : Blo 1503572 1504379 := bstep (se 1 (by rfl) ⟨1128284, by rfl⟩ : syracuseStep 1504379 = 2256569) B2256569
theorem B1504431 : Blo 1503572 1504431 := bstep (se 1 (by rfl) ⟨1128323, by rfl⟩ : syracuseStep 1504431 = 2256647) B2256647
theorem B1504455 : Blo 1503572 1504455 := bstep (se 1 (by rfl) ⟨1128341, by rfl⟩ : syracuseStep 1504455 = 2256683) B2256683
theorem B1504475 : Blo 1503572 1504475 := bstep (se 1 (by rfl) ⟨1128356, by rfl⟩ : syracuseStep 1504475 = 2256713) B2256713
theorem B5076215 : Blo 1503572 5076215 := bstep (se 1 (by rfl) ⟨3807161, by rfl⟩ : syracuseStep 5076215 = 7614323) B7614323
theorem B1504551 : Blo 1503572 1504551 := bstep (se 1 (by rfl) ⟨1128413, by rfl⟩ : syracuseStep 1504551 = 2256827) B2256827
theorem B1504591 : Blo 1503572 1504591 := bstep (se 1 (by rfl) ⟨1128443, by rfl⟩ : syracuseStep 1504591 = 2256887) B2256887
theorem B12539225 : Blo 1503572 12539225 := bstep (se 2 (by rfl) ⟨4702209, by rfl⟩ : syracuseStep 12539225 = 9404419) B9404419
theorem B1504607 : Blo 1503572 1504607 := bstep (se 1 (by rfl) ⟨1128455, by rfl⟩ : syracuseStep 1504607 = 2256911) B2256911
theorem B1504635 : Blo 1503572 1504635 := bstep (se 1 (by rfl) ⟨1128476, by rfl⟩ : syracuseStep 1504635 = 2256953) B2256953
theorem B1504687 : Blo 1503572 1504687 := bstep (se 1 (by rfl) ⟨1128515, by rfl⟩ : syracuseStep 1504687 = 2257031) B2257031
theorem B1504711 : Blo 1503572 1504711 := bstep (se 1 (by rfl) ⟨1128533, by rfl⟩ : syracuseStep 1504711 = 2257067) B2257067
theorem B1504731 : Blo 1503572 1504731 := bstep (se 1 (by rfl) ⟨1128548, by rfl⟩ : syracuseStep 1504731 = 2257097) B2257097
theorem B1693147 : Blo 1503572 1693147 := bstep (se 1 (by rfl) ⟨1269860, by rfl⟩ : syracuseStep 1693147 = 2539721) B2539721
theorem B26056181 : Blo 1503572 26056181 := bstep (se 5 (by rfl) ⟨1221383, by rfl⟩ : syracuseStep 26056181 = 2442767) B2442767
theorem B5715481 : Blo 1503572 5715481 := bstep (se 2 (by rfl) ⟨2143305, by rfl⟩ : syracuseStep 5715481 = 4286611) B4286611
theorem B1504807 : Blo 1503572 1504807 := bstep (se 1 (by rfl) ⟨1128605, by rfl⟩ : syracuseStep 1504807 = 2257211) B2257211
theorem B5076539 : Blo 1503572 5076539 := bstep (se 1 (by rfl) ⟨3807404, by rfl⟩ : syracuseStep 5076539 = 7614809) B7614809
theorem B1504847 : Blo 1503572 1504847 := bstep (se 1 (by rfl) ⟨1128635, by rfl⟩ : syracuseStep 1504847 = 2257271) B2257271
theorem B1504863 : Blo 1503572 1504863 := bstep (se 1 (by rfl) ⟨1128647, by rfl⟩ : syracuseStep 1504863 = 2257295) B2257295
theorem B1504891 : Blo 1503572 1504891 := bstep (se 1 (by rfl) ⟨1128668, by rfl⟩ : syracuseStep 1504891 = 2257337) B2257337
theorem B1504943 : Blo 1503572 1504943 := bstep (se 1 (by rfl) ⟨1128707, by rfl⟩ : syracuseStep 1504943 = 2257415) B2257415
theorem B38565557 : Blo 1503572 38565557 := bstep (se 5 (by rfl) ⟨1807760, by rfl⟩ : syracuseStep 38565557 = 3615521) B3615521
theorem B4282055 : Blo 1503572 4282055 := bstep (se 1 (by rfl) ⟨3211541, by rfl⟩ : syracuseStep 4282055 = 6423083) B6423083
theorem B2856647 : Blo 1503572 2856647 := bstep (se 1 (by rfl) ⟨2142485, by rfl⟩ : syracuseStep 2856647 = 4284971) B4284971
theorem B1504967 : Blo 1503572 1504967 := bstep (se 1 (by rfl) ⟨1128725, by rfl⟩ : syracuseStep 1504967 = 2257451) B2257451
theorem B1504987 : Blo 1503572 1504987 := bstep (se 1 (by rfl) ⟨1128740, by rfl⟩ : syracuseStep 1504987 = 2257481) B2257481
theorem B1505063 : Blo 1503572 1505063 := bstep (se 1 (by rfl) ⟨1128797, by rfl⟩ : syracuseStep 1505063 = 2257595) B2257595
theorem B5715755 : Blo 1503572 5715755 := bstep (se 1 (by rfl) ⟨4286816, by rfl⟩ : syracuseStep 5715755 = 8573633) B8573633
theorem B6428483 : Blo 1503572 6428483 := bstep (se 1 (by rfl) ⟨4821362, by rfl⟩ : syracuseStep 6428483 = 9642725) B9642725
theorem B5076809 : Blo 1503572 5076809 := bstep (se 2 (by rfl) ⟨1903803, by rfl⟩ : syracuseStep 5076809 = 3807607) B3807607
theorem B5715785 : Blo 1503572 5715785 := bstep (se 2 (by rfl) ⟨2143419, by rfl⟩ : syracuseStep 5715785 = 4286839) B4286839
theorem B1505103 : Blo 1503572 1505103 := bstep (se 1 (by rfl) ⟨1128827, by rfl⟩ : syracuseStep 1505103 = 2257655) B2257655
theorem B2537311 : Blo 1503572 2537311 := bstep (se 1 (by rfl) ⟨1902983, by rfl⟩ : syracuseStep 2537311 = 3805967) B3805967
theorem B3807071 : Blo 1503572 3807071 := bstep (se 1 (by rfl) ⟨2855303, by rfl⟩ : syracuseStep 3807071 = 5710607) B5710607
theorem B2856799 : Blo 1503572 2856799 := bstep (se 1 (by rfl) ⟨2142599, by rfl⟩ : syracuseStep 2856799 = 4285199) B4285199
theorem B1505119 : Blo 1503572 1505119 := bstep (se 1 (by rfl) ⟨1128839, by rfl⟩ : syracuseStep 1505119 = 2257679) B2257679
theorem B1505147 : Blo 1503572 1505147 := bstep (se 1 (by rfl) ⟨1128860, by rfl⟩ : syracuseStep 1505147 = 2257721) B2257721
theorem B1505199 : Blo 1503572 1505199 := bstep (se 1 (by rfl) ⟨1128899, by rfl⟩ : syracuseStep 1505199 = 2257799) B2257799
theorem B1693615 : Blo 1503572 1693615 := bstep (se 1 (by rfl) ⟨1270211, by rfl⟩ : syracuseStep 1693615 = 2540423) B2540423
theorem B2537399 : Blo 1503572 2537399 := bstep (se 1 (by rfl) ⟨1903049, by rfl⟩ : syracuseStep 2537399 = 3806099) B3806099
theorem B1505223 : Blo 1503572 1505223 := bstep (se 1 (by rfl) ⟨1128917, by rfl⟩ : syracuseStep 1505223 = 2257835) B2257835
theorem B1505243 : Blo 1503572 1505243 := bstep (se 1 (by rfl) ⟨1128932, by rfl⟩ : syracuseStep 1505243 = 2257865) B2257865
theorem B1505319 : Blo 1503572 1505319 := bstep (se 1 (by rfl) ⟨1128989, by rfl⟩ : syracuseStep 1505319 = 2257979) B2257979
theorem B1505359 : Blo 1503572 1505359 := bstep (se 1 (by rfl) ⟨1129019, by rfl⟩ : syracuseStep 1505359 = 2258039) B2258039
theorem B1505375 : Blo 1503572 1505375 := bstep (se 1 (by rfl) ⟨1129031, by rfl⟩ : syracuseStep 1505375 = 2258063) B2258063
theorem B1505403 : Blo 1503572 1505403 := bstep (se 1 (by rfl) ⟨1129052, by rfl⟩ : syracuseStep 1505403 = 2258105) B2258105
theorem B17135873 : Blo 1503572 17135873 := bstep (se 2 (by rfl) ⟨6425952, by rfl⟩ : syracuseStep 17135873 = 12851905) B12851905
theorem B5421323 : Blo 1503572 5421323 := bstep (se 1 (by rfl) ⟨4065992, by rfl⟩ : syracuseStep 5421323 = 8131985) B8131985
theorem B10844549 : Blo 1503572 10844549 := bstep (se 4 (by rfl) ⟨1016676, by rfl⟩ : syracuseStep 10844549 = 2033353) B2033353
theorem B2537993 : Blo 1503572 2537993 := bstep (se 2 (by rfl) ⟨951747, by rfl⟩ : syracuseStep 2537993 = 1903495) B1903495
theorem B3807769 : Blo 1503572 3807769 := bstep (se 2 (by rfl) ⟨1427913, by rfl⟩ : syracuseStep 3807769 = 2855827) B2855827
theorem B19274273 : Blo 1503572 19274273 := bstep (se 2 (by rfl) ⟨7227852, by rfl⟩ : syracuseStep 19274273 = 14455705) B14455705
theorem B2538155 : Blo 1503572 2538155 := bstep (se 1 (by rfl) ⟨1903616, by rfl⟩ : syracuseStep 2538155 = 3807233) B3807233
theorem B3808073 : Blo 1503572 3808073 := bstep (se 2 (by rfl) ⟨1428027, by rfl⟩ : syracuseStep 3808073 = 2856055) B2856055
theorem B6511535 : Blo 1503572 6511535 := bstep (se 1 (by rfl) ⟨4883651, by rfl⟩ : syracuseStep 6511535 = 9767303) B9767303
theorem B5077943 : Blo 1503572 5077943 := bstep (se 1 (by rfl) ⟨3808457, by rfl⟩ : syracuseStep 5077943 = 7616915) B7616915
theorem B370580453 : Blo 1503572 370580453 := bstep (se 4 (by rfl) ⟨34741917, by rfl⟩ : syracuseStep 370580453 = 69483835) B69483835
theorem B2538553 : Blo 1503572 2538553 := bstep (se 2 (by rfl) ⟨951957, by rfl⟩ : syracuseStep 2538553 = 1903915) B1903915
theorem B8133803 : Blo 1503572 8133803 := bstep (se 1 (by rfl) ⟨6100352, by rfl⟩ : syracuseStep 8133803 = 12200705) B12200705
theorem B2538695 : Blo 1503572 2538695 := bstep (se 1 (by rfl) ⟨1904021, by rfl⟩ : syracuseStep 2538695 = 3808043) B3808043
theorem B2538857 : Blo 1503572 2538857 := bstep (se 2 (by rfl) ⟨952071, by rfl⟩ : syracuseStep 2538857 = 1904143) B1904143
theorem B4283867 : Blo 1503572 4283867 := bstep (se 1 (by rfl) ⟨3212900, by rfl⟩ : syracuseStep 4283867 = 6425801) B6425801
theorem B5078537 : Blo 1503572 5078537 := bstep (se 2 (by rfl) ⟨1904451, by rfl⟩ : syracuseStep 5078537 = 3808903) B3808903
theorem B5144161 : Blo 1503572 5144161 := bstep (se 2 (by rfl) ⟨1929060, by rfl⟩ : syracuseStep 5144161 = 3858121) B3858121
theorem B2539255 : Blo 1503572 2539255 := bstep (se 1 (by rfl) ⟨1904441, by rfl⟩ : syracuseStep 2539255 = 3808883) B3808883
theorem B5709635 : Blo 1503572 5709635 := bstep (se 1 (by rfl) ⟨4282226, by rfl⟩ : syracuseStep 5709635 = 8564453) B8564453
theorem B3383135 : Blo 1503572 3383135 := bstep (se 1 (by rfl) ⟨2537351, by rfl⟩ : syracuseStep 3383135 = 5074703) B5074703
theorem B3809207 : Blo 1503572 3809207 := bstep (se 1 (by rfl) ⟨2856905, by rfl⟩ : syracuseStep 3809207 = 5713811) B5713811
theorem B2539451 : Blo 1503572 2539451 := bstep (se 1 (by rfl) ⟨1904588, by rfl⟩ : syracuseStep 2539451 = 3809177) B3809177
theorem B4817107 : Blo 1503572 4817107 := bstep (se 1 (by rfl) ⟨3612830, by rfl⟩ : syracuseStep 4817107 = 7225661) B7225661
theorem B23159191 : Blo 1503572 23159191 := bstep (se 1 (by rfl) ⟨17369393, by rfl⟩ : syracuseStep 23159191 = 34738787) B34738787
theorem B3613139 : Blo 1503572 3613139 := bstep (se 1 (by rfl) ⟨2709854, by rfl⟩ : syracuseStep 3613139 = 5419709) B5419709
theorem B3809855 : Blo 1503572 3809855 := bstep (se 1 (by rfl) ⟨2857391, by rfl⟩ : syracuseStep 3809855 = 5714783) B5714783
theorem B3211849 : Blo 1503572 3211849 := bstep (se 2 (by rfl) ⟨1204443, by rfl⟩ : syracuseStep 3211849 = 2408887) B2408887
theorem B2540153 : Blo 1503572 2540153 := bstep (se 2 (by rfl) ⟨952557, by rfl⟩ : syracuseStep 2540153 = 1905115) B1905115
theorem B7226009 : Blo 1503572 7226009 := bstep (se 2 (by rfl) ⟨2709753, by rfl⟩ : syracuseStep 7226009 = 5419507) B5419507
theorem B2540207 : Blo 1503572 2540207 := bstep (se 1 (by rfl) ⟨1905155, by rfl⟩ : syracuseStep 2540207 = 3810311) B3810311
theorem B8684281 : Blo 1503572 8684281 := bstep (se 2 (by rfl) ⟨3256605, by rfl⟩ : syracuseStep 8684281 = 6513211) B6513211
theorem B32523083 : Blo 1503572 32523083 := bstep (se 1 (by rfl) ⟨24392312, by rfl⟩ : syracuseStep 32523083 = 48784625) B48784625
theorem B3384143 : Blo 1503572 3384143 := bstep (se 1 (by rfl) ⟨2538107, by rfl⟩ : syracuseStep 3384143 = 5076215) B5076215
theorem B5079887 : Blo 1503572 5079887 := bstep (se 1 (by rfl) ⟨3809915, by rfl⟩ : syracuseStep 5079887 = 7619831) B7619831
theorem B2540443 : Blo 1503572 2540443 := bstep (se 1 (by rfl) ⟨1905332, by rfl⟩ : syracuseStep 2540443 = 3810665) B3810665
theorem B3384359 : Blo 1503572 3384359 := bstep (se 1 (by rfl) ⟨2538269, by rfl⟩ : syracuseStep 3384359 = 5076539) B5076539
theorem B5080211 : Blo 1503572 5080211 := bstep (se 1 (by rfl) ⟨3810158, by rfl⟩ : syracuseStep 5080211 = 7620317) B7620317
theorem B7226567 : Blo 1503572 7226567 := bstep (se 1 (by rfl) ⟨5419925, by rfl⟩ : syracuseStep 7226567 = 10839851) B10839851
theorem B3810503 : Blo 1503572 3810503 := bstep (se 1 (by rfl) ⟨2857877, by rfl⟩ : syracuseStep 3810503 = 5715755) B5715755
theorem B4285655 : Blo 1503572 4285655 := bstep (se 1 (by rfl) ⟨3214241, by rfl⟩ : syracuseStep 4285655 = 6428483) B6428483
theorem B3384539 : Blo 1503572 3384539 := bstep (se 1 (by rfl) ⟨2538404, by rfl⟩ : syracuseStep 3384539 = 5076809) B5076809
theorem B3810523 : Blo 1503572 3810523 := bstep (se 1 (by rfl) ⟨2857892, by rfl⟩ : syracuseStep 3810523 = 5715785) B5715785
theorem B57828653 : Blo 1503572 57828653 := bstep (se 3 (by rfl) ⟨10842872, by rfl⟩ : syracuseStep 57828653 = 21685745) B21685745
theorem B36619607 : Blo 1503572 36619607 := bstep (se 1 (by rfl) ⟨27464705, by rfl⟩ : syracuseStep 36619607 = 54929411) B54929411
theorem B14452091 : Blo 1503572 14452091 := bstep (se 1 (by rfl) ⟨10839068, by rfl⟩ : syracuseStep 14452091 = 21678137) B21678137
theorem B3384737 : Blo 1503572 3384737 := bstep (se 2 (by rfl) ⟨1269276, by rfl⟩ : syracuseStep 3384737 = 2538553) B2538553
theorem B4711841 : Blo 1503572 4711841 := bstep (se 2 (by rfl) ⟨1766940, by rfl⟩ : syracuseStep 4711841 = 3533881) B3533881
theorem B5080481 : Blo 1503572 5080481 := bstep (se 2 (by rfl) ⟨1905180, by rfl⟩ : syracuseStep 5080481 = 3810361) B3810361
theorem B3614215 : Blo 1503572 3614215 := bstep (se 1 (by rfl) ⟨2710661, by rfl⟩ : syracuseStep 3614215 = 5421323) B5421323
theorem B4064825 : Blo 1503572 4064825 := bstep (se 2 (by rfl) ⟨1524309, by rfl⟩ : syracuseStep 4064825 = 3048619) B3048619
theorem B3213113 : Blo 1503572 3213113 := bstep (se 2 (by rfl) ⟨1204917, by rfl⟩ : syracuseStep 3213113 = 2409835) B2409835
theorem B3385295 : Blo 1503572 3385295 := bstep (se 1 (by rfl) ⟨2538971, by rfl⟩ : syracuseStep 3385295 = 5077943) B5077943
theorem B7620641 : Blo 1503572 7620641 := bstep (se 2 (by rfl) ⟨2857740, by rfl⟩ : syracuseStep 7620641 = 5715481) B5715481
theorem B6858881 : Blo 1503572 6858881 := bstep (se 2 (by rfl) ⟨2572080, by rfl⟩ : syracuseStep 6858881 = 5144161) B5144161
theorem B5949575 : Blo 1503572 5949575 := bstep (se 1 (by rfl) ⟨4462181, by rfl⟩ : syracuseStep 5949575 = 8924363) B8924363
theorem B27453617 : Blo 1503572 27453617 := bstep (se 2 (by rfl) ⟨10295106, by rfl⟩ : syracuseStep 27453617 = 20590213) B20590213
theorem B7620803 : Blo 1503572 7620803 := bstep (se 1 (by rfl) ⟨5715602, by rfl⟩ : syracuseStep 7620803 = 11431205) B11431205
theorem B3213523 : Blo 1503572 3213523 := bstep (se 1 (by rfl) ⟨2410142, by rfl⟩ : syracuseStep 3213523 = 4820285) B4820285
theorem B3385673 : Blo 1503572 3385673 := bstep (se 2 (by rfl) ⟨1269627, by rfl⟩ : syracuseStep 3385673 = 2539255) B2539255
theorem B3385691 : Blo 1503572 3385691 := bstep (se 1 (by rfl) ⟨2539268, by rfl⟩ : syracuseStep 3385691 = 5078537) B5078537
theorem B2255423 : Blo 1503572 2255423 := bstep (se 1 (by rfl) ⟨1691567, by rfl⟩ : syracuseStep 2255423 = 3383135) B3383135
theorem B7227967 : Blo 1503572 7227967 := bstep (se 1 (by rfl) ⟨5420975, by rfl⟩ : syracuseStep 7227967 = 10841951) B10841951
theorem B2255543 : Blo 1503572 2255543 := bstep (se 1 (by rfl) ⟨1691657, by rfl⟩ : syracuseStep 2255543 = 3383315) B3383315
theorem B12847805 : Blo 1503572 12847805 := bstep (se 3 (by rfl) ⟨2408963, by rfl⟩ : syracuseStep 12847805 = 4817927) B4817927
theorem B1903439 : Blo 1503572 1903439 := bstep (se 1 (by rfl) ⟨1427579, by rfl⟩ : syracuseStep 1903439 = 2855159) B2855159
theorem B2255771 : Blo 1503572 2255771 := bstep (se 1 (by rfl) ⟨1691828, by rfl⟩ : syracuseStep 2255771 = 3383657) B3383657
theorem B3386267 : Blo 1503572 3386267 := bstep (se 1 (by rfl) ⟨2539700, by rfl⟩ : syracuseStep 3386267 = 5079401) B5079401
theorem B1903591 : Blo 1503572 1903591 := bstep (se 1 (by rfl) ⟨1427693, by rfl⟩ : syracuseStep 1903591 = 2855387) B2855387
theorem B3386465 : Blo 1503572 3386465 := bstep (se 2 (by rfl) ⟨1269924, by rfl⟩ : syracuseStep 3386465 = 2539849) B2539849
theorem B4820107 : Blo 1503572 4820107 := bstep (se 1 (by rfl) ⟨3615080, by rfl⟩ : syracuseStep 4820107 = 7230161) B7230161
theorem B417164579 : Blo 1503572 417164579 := bstep (se 1 (by rfl) ⟨312873434, by rfl⟩ : syracuseStep 417164579 = 625746869) B625746869
theorem B2256167 : Blo 1503572 2256167 := bstep (se 1 (by rfl) ⟨1692125, by rfl⟩ : syracuseStep 2256167 = 3384251) B3384251
theorem B3386663 : Blo 1503572 3386663 := bstep (se 1 (by rfl) ⟨2539997, by rfl⟩ : syracuseStep 3386663 = 5079995) B5079995
theorem B2256251 : Blo 1503572 2256251 := bstep (se 1 (by rfl) ⟨1692188, by rfl⟩ : syracuseStep 2256251 = 3384377) B3384377
theorem B2256377 : Blo 1503572 2256377 := bstep (se 2 (by rfl) ⟨846141, by rfl⟩ : syracuseStep 2256377 = 1692283) B1692283
theorem B2256479 : Blo 1503572 2256479 := bstep (se 1 (by rfl) ⟨1692359, by rfl⟩ : syracuseStep 2256479 = 3384719) B3384719
theorem B24391277 : Blo 1503572 24391277 := bstep (se 3 (by rfl) ⟨4573364, by rfl⟩ : syracuseStep 24391277 = 9146729) B9146729
theorem B5713523 : Blo 1503572 5713523 := bstep (se 1 (by rfl) ⟨4285142, by rfl⟩ : syracuseStep 5713523 = 8570285) B8570285
theorem B17370787 : Blo 1503572 17370787 := bstep (se 1 (by rfl) ⟨13028090, by rfl⟩ : syracuseStep 17370787 = 26056181) B26056181
theorem B3387041 : Blo 1503572 3387041 := bstep (se 2 (by rfl) ⟨1270140, by rfl⟩ : syracuseStep 3387041 = 2540281) B2540281
theorem B7614161 : Blo 1503572 7614161 := bstep (se 2 (by rfl) ⟨2855310, by rfl⟩ : syracuseStep 7614161 = 5710621) B5710621
theorem B11431691 : Blo 1503572 11431691 := bstep (se 1 (by rfl) ⟨8573768, by rfl⟩ : syracuseStep 11431691 = 17147537) B17147537
theorem B25710371 : Blo 1503572 25710371 := bstep (se 1 (by rfl) ⟨19282778, by rfl⟩ : syracuseStep 25710371 = 38565557) B38565557
theorem B2854703 : Blo 1503572 2854703 := bstep (se 1 (by rfl) ⟨2141027, by rfl⟩ : syracuseStep 2854703 = 4282055) B4282055
theorem B2256695 : Blo 1503572 2256695 := bstep (se 1 (by rfl) ⟨1692521, by rfl⟩ : syracuseStep 2256695 = 3385043) B3385043
theorem B1691599 : Blo 1503572 1691599 := bstep (se 1 (by rfl) ⟨1268699, by rfl⟩ : syracuseStep 1691599 = 2537399) B2537399
theorem B2257001 : Blo 1503572 2257001 := bstep (se 2 (by rfl) ⟨846375, by rfl⟩ : syracuseStep 2257001 = 1692751) B1692751
theorem B2748521 : Blo 1503572 2748521 := bstep (se 2 (by rfl) ⟨1030695, by rfl⟩ : syracuseStep 2748521 = 2061391) B2061391
theorem B11423915 : Blo 1503572 11423915 := bstep (se 1 (by rfl) ⟨8567936, by rfl⟩ : syracuseStep 11423915 = 17135873) B17135873
theorem B7229699 : Blo 1503572 7229699 := bstep (se 1 (by rfl) ⟨5422274, by rfl⟩ : syracuseStep 7229699 = 10844549) B10844549
theorem B12857615 : Blo 1503572 12857615 := bstep (se 1 (by rfl) ⟨9643211, by rfl⟩ : syracuseStep 12857615 = 19286423) B19286423
theorem B1503579 : Blo 1503572 1503579 := bstep (se 1 (by rfl) ⟨1127684, by rfl⟩ : syracuseStep 1503579 = 2255369) B2255369
theorem B1691995 : Blo 1503572 1691995 := bstep (se 1 (by rfl) ⟨1268996, by rfl⟩ : syracuseStep 1691995 = 2537993) B2537993
theorem B12849515 : Blo 1503572 12849515 := bstep (se 1 (by rfl) ⟨9637136, by rfl⟩ : syracuseStep 12849515 = 19274273) B19274273
theorem B1503599 : Blo 1503572 1503599 := bstep (se 1 (by rfl) ⟨1127699, by rfl⟩ : syracuseStep 1503599 = 2255399) B2255399
theorem B1503655 : Blo 1503572 1503655 := bstep (se 1 (by rfl) ⟨1127741, by rfl⟩ : syracuseStep 1503655 = 2255483) B2255483
theorem B2257319 : Blo 1503572 2257319 := bstep (se 1 (by rfl) ⟨1692989, by rfl⟩ : syracuseStep 2257319 = 3385979) B3385979
theorem B1692103 : Blo 1503572 1692103 := bstep (se 1 (by rfl) ⟨1269077, by rfl⟩ : syracuseStep 1692103 = 2538155) B2538155
theorem B24408539 : Blo 1503572 24408539 := bstep (se 1 (by rfl) ⟨18306404, by rfl⟩ : syracuseStep 24408539 = 36612809) B36612809
theorem B1503739 : Blo 1503572 1503739 := bstep (se 1 (by rfl) ⟨1127804, by rfl⟩ : syracuseStep 1503739 = 2255609) B2255609
theorem B2257403 : Blo 1503572 2257403 := bstep (se 1 (by rfl) ⟨1693052, by rfl⟩ : syracuseStep 2257403 = 3386105) B3386105
theorem B1503807 : Blo 1503572 1503807 := bstep (se 1 (by rfl) ⟨1127855, by rfl⟩ : syracuseStep 1503807 = 2255711) B2255711
theorem B5419591 : Blo 1503572 5419591 := bstep (se 1 (by rfl) ⟨4064693, by rfl⟩ : syracuseStep 5419591 = 8129387) B8129387
theorem B1503815 : Blo 1503572 1503815 := bstep (se 1 (by rfl) ⟨1127861, by rfl⟩ : syracuseStep 1503815 = 2255723) B2255723
theorem B11580025 : Blo 1503572 11580025 := bstep (se 2 (by rfl) ⟨4342509, by rfl⟩ : syracuseStep 11580025 = 8685019) B8685019
theorem B2257529 : Blo 1503572 2257529 := bstep (se 2 (by rfl) ⟨846573, by rfl⟩ : syracuseStep 2257529 = 1693147) B1693147
theorem B12202649 : Blo 1503572 12202649 := bstep (se 2 (by rfl) ⟨4575993, by rfl⟩ : syracuseStep 12202649 = 9151987) B9151987
theorem B2257583 : Blo 1503572 2257583 := bstep (se 1 (by rfl) ⟨1693187, by rfl⟩ : syracuseStep 2257583 = 3386375) B3386375
theorem B1503967 : Blo 1503572 1503967 := bstep (se 1 (by rfl) ⟨1127975, by rfl⟩ : syracuseStep 1503967 = 2255951) B2255951
theorem B2257631 : Blo 1503572 2257631 := bstep (se 1 (by rfl) ⟨1693223, by rfl⟩ : syracuseStep 2257631 = 3386447) B3386447
theorem B17363755 : Blo 1503572 17363755 := bstep (se 1 (by rfl) ⟨13022816, by rfl⟩ : syracuseStep 17363755 = 26045633) B26045633
theorem B1504047 : Blo 1503572 1504047 := bstep (se 1 (by rfl) ⟨1128035, by rfl⟩ : syracuseStep 1504047 = 2256071) B2256071
theorem B1692463 : Blo 1503572 1692463 := bstep (se 1 (by rfl) ⟨1269347, by rfl⟩ : syracuseStep 1692463 = 2538695) B2538695
theorem B2143055 : Blo 1503572 2143055 := bstep (se 1 (by rfl) ⟨1607291, by rfl⟩ : syracuseStep 2143055 = 3214583) B3214583
theorem B1504155 : Blo 1503572 1504155 := bstep (se 1 (by rfl) ⟨1128116, by rfl⟩ : syracuseStep 1504155 = 2256233) B2256233
theorem B1692571 : Blo 1503572 1692571 := bstep (se 1 (by rfl) ⟨1269428, by rfl⟩ : syracuseStep 1692571 = 2538857) B2538857
theorem B1504207 : Blo 1503572 1504207 := bstep (se 1 (by rfl) ⟨1128155, by rfl⟩ : syracuseStep 1504207 = 2256311) B2256311
theorem B1504231 : Blo 1503572 1504231 := bstep (se 1 (by rfl) ⟨1128173, by rfl⟩ : syracuseStep 1504231 = 2256347) B2256347
theorem B2855911 : Blo 1503572 2855911 := bstep (se 1 (by rfl) ⟨2141933, by rfl⟩ : syracuseStep 2855911 = 4283867) B4283867
theorem B2257895 : Blo 1503572 2257895 := bstep (se 1 (by rfl) ⟨1693421, by rfl⟩ : syracuseStep 2257895 = 3386843) B3386843
theorem B12850265 : Blo 1503572 12850265 := bstep (se 2 (by rfl) ⟨4818849, by rfl⟩ : syracuseStep 12850265 = 9637699) B9637699
theorem B4576381 : Blo 1503572 4576381 := bstep (se 3 (by rfl) ⟨858071, by rfl⟩ : syracuseStep 4576381 = 1716143) B1716143
theorem B3806423 : Blo 1503572 3806423 := bstep (se 1 (by rfl) ⟨2854817, by rfl⟩ : syracuseStep 3806423 = 5709635) B5709635
theorem B2258153 : Blo 1503572 2258153 := bstep (se 2 (by rfl) ⟨846807, by rfl⟩ : syracuseStep 2258153 = 1693615) B1693615
theorem B1504543 : Blo 1503572 1504543 := bstep (se 1 (by rfl) ⟨1128407, by rfl⟩ : syracuseStep 1504543 = 2256815) B2256815
theorem B1692967 : Blo 1503572 1692967 := bstep (se 1 (by rfl) ⟨1269725, by rfl⟩ : syracuseStep 1692967 = 2539451) B2539451
theorem B1504603 : Blo 1503572 1504603 := bstep (se 1 (by rfl) ⟨1128452, by rfl⟩ : syracuseStep 1504603 = 2256905) B2256905
theorem B7230815 : Blo 1503572 7230815 := bstep (se 1 (by rfl) ⟨5423111, by rfl⟩ : syracuseStep 7230815 = 10846223) B10846223
theorem B1504623 : Blo 1503572 1504623 := bstep (se 1 (by rfl) ⟨1128467, by rfl⟩ : syracuseStep 1504623 = 2256935) B2256935
theorem B1693039 : Blo 1503572 1693039 := bstep (se 1 (by rfl) ⟨1269779, by rfl⟩ : syracuseStep 1693039 = 2539559) B2539559
theorem B4576673 : Blo 1503572 4576673 := bstep (se 2 (by rfl) ⟨1716252, by rfl⟩ : syracuseStep 4576673 = 3432505) B3432505
theorem B1504679 : Blo 1503572 1504679 := bstep (se 1 (by rfl) ⟨1128509, by rfl⟩ : syracuseStep 1504679 = 2257019) B2257019
theorem B1504763 : Blo 1503572 1504763 := bstep (se 1 (by rfl) ⟨1128572, by rfl⟩ : syracuseStep 1504763 = 2257145) B2257145
theorem B3806777 : Blo 1503572 3806777 := bstep (se 2 (by rfl) ⟨1427541, by rfl⟩ : syracuseStep 3806777 = 2855083) B2855083
theorem B1504831 : Blo 1503572 1504831 := bstep (se 1 (by rfl) ⟨1128623, by rfl⟩ : syracuseStep 1504831 = 2257247) B2257247
theorem B1504839 : Blo 1503572 1504839 := bstep (se 1 (by rfl) ⟨1128629, by rfl⟩ : syracuseStep 1504839 = 2257259) B2257259
theorem B1693255 : Blo 1503572 1693255 := bstep (se 1 (by rfl) ⟨1269941, by rfl⟩ : syracuseStep 1693255 = 2539883) B2539883
theorem B12859013 : Blo 1503572 12859013 := bstep (se 4 (by rfl) ⟨1205532, by rfl⟩ : syracuseStep 12859013 = 2411065) B2411065
theorem B1504991 : Blo 1503572 1504991 := bstep (se 1 (by rfl) ⟨1128743, by rfl⟩ : syracuseStep 1504991 = 2257487) B2257487
theorem B1505071 : Blo 1503572 1505071 := bstep (se 1 (by rfl) ⟨1128803, by rfl⟩ : syracuseStep 1505071 = 2257607) B2257607
theorem B1505179 : Blo 1503572 1505179 := bstep (se 1 (by rfl) ⟨1128884, by rfl⟩ : syracuseStep 1505179 = 2257769) B2257769
theorem B1505231 : Blo 1503572 1505231 := bstep (se 1 (by rfl) ⟨1128923, by rfl⟩ : syracuseStep 1505231 = 2257847) B2257847
theorem B1505255 : Blo 1503572 1505255 := bstep (se 1 (by rfl) ⟨1128941, by rfl⟩ : syracuseStep 1505255 = 2257883) B2257883
theorem B5077025 : Blo 1503572 5077025 := bstep (se 2 (by rfl) ⟨1903884, by rfl⟩ : syracuseStep 5077025 = 3807769) B3807769
theorem B7616591 : Blo 1503572 7616591 := bstep (se 1 (by rfl) ⟨5712443, by rfl⟩ : syracuseStep 7616591 = 11424887) B11424887
theorem B33437933 : Blo 1503572 33437933 := bstep (se 3 (by rfl) ⟨6269612, by rfl⟩ : syracuseStep 33437933 = 12539225) B12539225
theorem B4282807 : Blo 1503572 4282807 := bstep (se 1 (by rfl) ⟨3212105, by rfl⟩ : syracuseStep 4282807 = 6424211) B6424211
theorem B2538047 : Blo 1503572 2538047 := bstep (se 1 (by rfl) ⟨1903535, by rfl⟩ : syracuseStep 2538047 = 3807071) B3807071
theorem B8567369 : Blo 1503572 8567369 := bstep (se 2 (by rfl) ⟨3212763, by rfl⟩ : syracuseStep 8567369 = 6425527) B6425527
theorem B7617725 : Blo 1503572 7617725 := bstep (se 3 (by rfl) ⟨1428323, by rfl⟩ : syracuseStep 7617725 = 2856647) B2856647
theorem B2538715 : Blo 1503572 2538715 := bstep (se 1 (by rfl) ⟨1904036, by rfl⟩ : syracuseStep 2538715 = 3808073) B3808073
theorem B4341023 : Blo 1503572 4341023 := bstep (se 1 (by rfl) ⟨3255767, by rfl⟩ : syracuseStep 4341023 = 6511535) B6511535
theorem B247053635 : Blo 1503572 247053635 := bstep (se 1 (by rfl) ⟨185290226, by rfl⟩ : syracuseStep 247053635 = 370580453) B370580453
theorem B2710921 : Blo 1503572 2710921 := bstep (se 2 (by rfl) ⟨1016595, by rfl⟩ : syracuseStep 2710921 = 2033191) B2033191
theorem B5422535 : Blo 1503572 5422535 := bstep (se 1 (by rfl) ⟨4066901, by rfl⟩ : syracuseStep 5422535 = 8133803) B8133803
theorem B8134103 : Blo 1503572 8134103 := bstep (se 1 (by rfl) ⟨6100577, by rfl⟩ : syracuseStep 8134103 = 12201155) B12201155
theorem B7233083 : Blo 1503572 7233083 := bstep (se 1 (by rfl) ⟨5424812, by rfl⟩ : syracuseStep 7233083 = 10849625) B10849625
theorem B14851667 : Blo 1503572 14851667 := bstep (se 1 (by rfl) ⟨11138750, by rfl⟩ : syracuseStep 14851667 = 22277501) B22277501
theorem B15449849 : Blo 1503572 15449849 := bstep (se 2 (by rfl) ⟨5793693, by rfl⟩ : syracuseStep 15449849 = 11587387) B11587387
theorem B3383081 : Blo 1503572 3383081 := bstep (se 2 (by rfl) ⟨1268655, by rfl⟩ : syracuseStep 3383081 = 2537311) B2537311
theorem B3809065 : Blo 1503572 3809065 := bstep (se 2 (by rfl) ⟨1428399, by rfl⟩ : syracuseStep 3809065 = 2856799) B2856799
theorem B2539471 : Blo 1503572 2539471 := bstep (se 1 (by rfl) ⟨1904603, by rfl⟩ : syracuseStep 2539471 = 3809207) B3809207
theorem B6422809 : Blo 1503572 6422809 := bstep (se 2 (by rfl) ⟨2408553, by rfl⟩ : syracuseStep 6422809 = 4817107) B4817107
theorem B2408759 : Blo 1503572 2408759 := bstep (se 1 (by rfl) ⟨1806569, by rfl⟩ : syracuseStep 2408759 = 3613139) B3613139
theorem B2539903 : Blo 1503572 2539903 := bstep (se 1 (by rfl) ⟨1904927, by rfl⟩ : syracuseStep 2539903 = 3809855) B3809855
theorem B4817339 : Blo 1503572 4817339 := bstep (se 1 (by rfl) ⟨3613004, by rfl⟩ : syracuseStep 4817339 = 7226009) B7226009
theorem B8135099 : Blo 1503572 8135099 := bstep (se 1 (by rfl) ⟨6101324, by rfl⟩ : syracuseStep 8135099 = 12202649) B12202649
theorem B5710409 : Blo 1503572 5710409 := bstep (se 2 (by rfl) ⟨2141403, by rfl⟩ : syracuseStep 5710409 = 4282807) B4282807
theorem B4817711 : Blo 1503572 4817711 := bstep (se 1 (by rfl) ⟨3613283, by rfl⟩ : syracuseStep 4817711 = 7226567) B7226567
theorem B2540335 : Blo 1503572 2540335 := bstep (se 1 (by rfl) ⟨1905251, by rfl⟩ : syracuseStep 2540335 = 3810503) B3810503
theorem B38552435 : Blo 1503572 38552435 := bstep (se 1 (by rfl) ⟨28914326, by rfl⟩ : syracuseStep 38552435 = 57828653) B57828653
theorem B24413071 : Blo 1503572 24413071 := bstep (se 1 (by rfl) ⟨18309803, by rfl⟩ : syracuseStep 24413071 = 36619607) B36619607
theorem B9634727 : Blo 1503572 9634727 := bstep (se 1 (by rfl) ⟨7226045, by rfl⟩ : syracuseStep 9634727 = 14452091) B14452091
theorem B23151673 : Blo 1503572 23151673 := bstep (se 2 (by rfl) ⟨8681877, by rfl⟩ : syracuseStep 23151673 = 17363755) B17363755
theorem B17138789 : Blo 1503572 17138789 := bstep (se 4 (by rfl) ⟨1606761, by rfl⟩ : syracuseStep 17138789 = 3213523) B3213523
theorem B3384683 : Blo 1503572 3384683 := bstep (se 1 (by rfl) ⟨2538512, by rfl⟩ : syracuseStep 3384683 = 5077025) B5077025
theorem B5080427 : Blo 1503572 5080427 := bstep (se 1 (by rfl) ⟨3810320, by rfl⟩ : syracuseStep 5080427 = 7620641) B7620641
theorem B4572587 : Blo 1503572 4572587 := bstep (se 1 (by rfl) ⟨3429440, by rfl⟩ : syracuseStep 4572587 = 6858881) B6858881
theorem B3966383 : Blo 1503572 3966383 := bstep (se 1 (by rfl) ⟨2974787, by rfl⟩ : syracuseStep 3966383 = 5949575) B5949575
theorem B18302411 : Blo 1503572 18302411 := bstep (se 1 (by rfl) ⟨13726808, by rfl⟩ : syracuseStep 18302411 = 27453617) B27453617
theorem B5080535 : Blo 1503572 5080535 := bstep (se 1 (by rfl) ⟨3810401, by rfl⟩ : syracuseStep 5080535 = 7620803) B7620803
theorem B22291955 : Blo 1503572 22291955 := bstep (se 1 (by rfl) ⟨16718966, by rfl⟩ : syracuseStep 22291955 = 33437933) B33437933
theorem B3384953 : Blo 1503572 3384953 := bstep (se 2 (by rfl) ⟨1269357, by rfl⟩ : syracuseStep 3384953 = 2538715) B2538715
theorem B5080697 : Blo 1503572 5080697 := bstep (se 2 (by rfl) ⟨1905261, by rfl⟩ : syracuseStep 5080697 = 3810523) B3810523
theorem B5711579 : Blo 1503572 5711579 := bstep (se 1 (by rfl) ⟨4283684, by rfl⟩ : syracuseStep 5711579 = 8567369) B8567369
theorem B3614561 : Blo 1503572 3614561 := bstep (se 2 (by rfl) ⟨1355460, by rfl⟩ : syracuseStep 3614561 = 2710921) B2710921
theorem B4818953 : Blo 1503572 4818953 := bstep (se 2 (by rfl) ⟨1807107, by rfl⟩ : syracuseStep 4818953 = 3614215) B3614215
theorem B7612541 : Blo 1503572 7612541 := bstep (se 3 (by rfl) ⟨1427351, by rfl⟩ : syracuseStep 7612541 = 2854703) B2854703
theorem B2894015 : Blo 1503572 2894015 := bstep (se 1 (by rfl) ⟨2170511, by rfl⟩ : syracuseStep 2894015 = 4341023) B4341023
theorem B164702423 : Blo 1503572 164702423 := bstep (se 1 (by rfl) ⟨123526817, by rfl⟩ : syracuseStep 164702423 = 247053635) B247053635
theorem B23161049 : Blo 1503572 23161049 := bstep (se 2 (by rfl) ⟨8685393, by rfl⟩ : syracuseStep 23161049 = 17370787) B17370787
theorem B3615023 : Blo 1503572 3615023 := bstep (se 1 (by rfl) ⟨2711267, by rfl⟩ : syracuseStep 3615023 = 5422535) B5422535
theorem B10299899 : Blo 1503572 10299899 := bstep (se 1 (by rfl) ⟨7724924, by rfl⟩ : syracuseStep 10299899 = 15449849) B15449849
theorem B7621127 : Blo 1503572 7621127 := bstep (se 1 (by rfl) ⟨5715845, by rfl⟩ : syracuseStep 7621127 = 11431691) B11431691
theorem B17140247 : Blo 1503572 17140247 := bstep (se 1 (by rfl) ⟨12855185, by rfl⟩ : syracuseStep 17140247 = 25710371) B25710371
theorem B2255387 : Blo 1503572 2255387 := bstep (se 1 (by rfl) ⟨1691540, by rfl⟩ : syracuseStep 2255387 = 3383081) B3383081
theorem B2255465 : Blo 1503572 2255465 := bstep (se 2 (by rfl) ⟨845799, by rfl⟩ : syracuseStep 2255465 = 1691599) B1691599
theorem B3385961 : Blo 1503572 3385961 := bstep (se 2 (by rfl) ⟨1269735, by rfl⟩ : syracuseStep 3385961 = 2539471) B2539471
theorem B4819799 : Blo 1503572 4819799 := bstep (se 1 (by rfl) ⟨3614849, by rfl⟩ : syracuseStep 4819799 = 7229699) B7229699
theorem B8571743 : Blo 1503572 8571743 := bstep (se 1 (by rfl) ⟨6428807, by rfl⟩ : syracuseStep 8571743 = 12857615) B12857615
theorem B16272359 : Blo 1503572 16272359 := bstep (se 1 (by rfl) ⟨12204269, by rfl⟩ : syracuseStep 16272359 = 24408539) B24408539
theorem B28904485 : Blo 1503572 28904485 := bstep (se 4 (by rfl) ⟨2709795, by rfl⟩ : syracuseStep 28904485 = 5419591) B5419591
theorem B2255993 : Blo 1503572 2255993 := bstep (se 2 (by rfl) ⟨845997, by rfl⟩ : syracuseStep 2255993 = 1691995) B1691995
theorem B30878921 : Blo 1503572 30878921 := bstep (se 2 (by rfl) ⟨11579595, by rfl⟩ : syracuseStep 30878921 = 23159191) B23159191
theorem B2256095 : Blo 1503572 2256095 := bstep (se 1 (by rfl) ⟨1692071, by rfl⟩ : syracuseStep 2256095 = 3384143) B3384143
theorem B3386591 : Blo 1503572 3386591 := bstep (se 1 (by rfl) ⟨2539943, by rfl⟩ : syracuseStep 3386591 = 5079887) B5079887
theorem B2256137 : Blo 1503572 2256137 := bstep (se 2 (by rfl) ⟨846051, by rfl⟩ : syracuseStep 2256137 = 1692103) B1692103
theorem B24407365 : Blo 1503572 24407365 := bstep (se 4 (by rfl) ⟨2288190, by rfl⟩ : syracuseStep 24407365 = 4576381) B4576381
theorem B2256239 : Blo 1503572 2256239 := bstep (se 1 (by rfl) ⟨1692179, by rfl⟩ : syracuseStep 2256239 = 3384359) B3384359
theorem B9637289 : Blo 1503572 9637289 := bstep (se 2 (by rfl) ⟨3613983, by rfl⟩ : syracuseStep 9637289 = 7227967) B7227967
theorem B3386807 : Blo 1503572 3386807 := bstep (se 1 (by rfl) ⟨2540105, by rfl⟩ : syracuseStep 3386807 = 5080211) B5080211
theorem B2256359 : Blo 1503572 2256359 := bstep (se 1 (by rfl) ⟨1692269, by rfl⟩ : syracuseStep 2256359 = 3384539) B3384539
theorem B4820543 : Blo 1503572 4820543 := bstep (se 1 (by rfl) ⟨3615407, by rfl⟩ : syracuseStep 4820543 = 7230815) B7230815
theorem B2256491 : Blo 1503572 2256491 := bstep (se 1 (by rfl) ⟨1692368, by rfl⟩ : syracuseStep 2256491 = 3384737) B3384737
theorem B3141227 : Blo 1503572 3141227 := bstep (se 1 (by rfl) ⟨2355920, by rfl⟩ : syracuseStep 3141227 = 4711841) B4711841
theorem B3051115 : Blo 1503572 3051115 := bstep (se 1 (by rfl) ⟨2288336, by rfl⟩ : syracuseStep 3051115 = 4576673) B4576673
theorem B3386987 : Blo 1503572 3386987 := bstep (se 1 (by rfl) ⟨2540240, by rfl⟩ : syracuseStep 3386987 = 5080481) B5080481
theorem B11579041 : Blo 1503572 11579041 := bstep (se 2 (by rfl) ⟨4342140, by rfl⟩ : syracuseStep 11579041 = 8684281) B8684281
theorem B2256617 : Blo 1503572 2256617 := bstep (se 2 (by rfl) ⟨846231, by rfl⟩ : syracuseStep 2256617 = 1692463) B1692463
theorem B8572675 : Blo 1503572 8572675 := bstep (se 1 (by rfl) ⟨6429506, by rfl⟩ : syracuseStep 8572675 = 12859013) B12859013
theorem B2256761 : Blo 1503572 2256761 := bstep (se 2 (by rfl) ⟨846285, by rfl⟩ : syracuseStep 2256761 = 1692571) B1692571
theorem B3387257 : Blo 1503572 3387257 := bstep (se 2 (by rfl) ⟨1270221, by rfl⟩ : syracuseStep 3387257 = 2540443) B2540443
theorem B2256863 : Blo 1503572 2256863 := bstep (se 1 (by rfl) ⟨1692647, by rfl⟩ : syracuseStep 2256863 = 3385295) B3385295
theorem B6426809 : Blo 1503572 6426809 := bstep (se 2 (by rfl) ⟨2410053, by rfl⟩ : syracuseStep 6426809 = 4820107) B4820107
theorem B2257115 : Blo 1503572 2257115 := bstep (se 1 (by rfl) ⟨1692836, by rfl⟩ : syracuseStep 2257115 = 3385673) B3385673
theorem B2257127 : Blo 1503572 2257127 := bstep (se 1 (by rfl) ⟨1692845, by rfl⟩ : syracuseStep 2257127 = 3385691) B3385691
theorem B1503615 : Blo 1503572 1503615 := bstep (se 1 (by rfl) ⟨1127711, by rfl⟩ : syracuseStep 1503615 = 2255423) B2255423
theorem B1692031 : Blo 1503572 1692031 := bstep (se 1 (by rfl) ⟨1269023, by rfl⟩ : syracuseStep 1692031 = 2538047) B2538047
theorem B2257289 : Blo 1503572 2257289 := bstep (se 2 (by rfl) ⟨846483, by rfl⟩ : syracuseStep 2257289 = 1692967) B1692967
theorem B1503695 : Blo 1503572 1503695 := bstep (se 1 (by rfl) ⟨1127771, by rfl⟩ : syracuseStep 1503695 = 2255543) B2255543
theorem B8565203 : Blo 1503572 8565203 := bstep (se 1 (by rfl) ⟨6423902, by rfl⟩ : syracuseStep 8565203 = 12847805) B12847805
theorem B2257385 : Blo 1503572 2257385 := bstep (se 2 (by rfl) ⟨846519, by rfl⟩ : syracuseStep 2257385 = 1693039) B1693039
theorem B1503847 : Blo 1503572 1503847 := bstep (se 1 (by rfl) ⟨1127885, by rfl⟩ : syracuseStep 1503847 = 2255771) B2255771
theorem B2257511 : Blo 1503572 2257511 := bstep (se 1 (by rfl) ⟨1693133, by rfl⟩ : syracuseStep 2257511 = 3386267) B3386267
theorem B2257643 : Blo 1503572 2257643 := bstep (se 1 (by rfl) ⟨1693232, by rfl⟩ : syracuseStep 2257643 = 3386465) B3386465
theorem B2257673 : Blo 1503572 2257673 := bstep (se 2 (by rfl) ⟨846627, by rfl⟩ : syracuseStep 2257673 = 1693255) B1693255
theorem B1504111 : Blo 1503572 1504111 := bstep (se 1 (by rfl) ⟨1128083, by rfl⟩ : syracuseStep 1504111 = 2256167) B2256167
theorem B2257775 : Blo 1503572 2257775 := bstep (se 1 (by rfl) ⟨1693331, by rfl⟩ : syracuseStep 2257775 = 3386663) B3386663
theorem B5075837 : Blo 1503572 5075837 := bstep (se 3 (by rfl) ⟨951719, by rfl⟩ : syracuseStep 5075837 = 1903439) B1903439
theorem B5714813 : Blo 1503572 5714813 := bstep (se 3 (by rfl) ⟨1071527, by rfl⟩ : syracuseStep 5714813 = 2143055) B2143055
theorem B1504167 : Blo 1503572 1504167 := bstep (se 1 (by rfl) ⟨1128125, by rfl⟩ : syracuseStep 1504167 = 2256251) B2256251
theorem B1504251 : Blo 1503572 1504251 := bstep (se 1 (by rfl) ⟨1128188, by rfl⟩ : syracuseStep 1504251 = 2256377) B2256377
theorem B4822055 : Blo 1503572 4822055 := bstep (se 1 (by rfl) ⟨3616541, by rfl⟩ : syracuseStep 4822055 = 7233083) B7233083
theorem B9901111 : Blo 1503572 9901111 := bstep (se 1 (by rfl) ⟨7425833, by rfl⟩ : syracuseStep 9901111 = 14851667) B14851667
theorem B1504319 : Blo 1503572 1504319 := bstep (se 1 (by rfl) ⟨1128239, by rfl⟩ : syracuseStep 1504319 = 2256479) B2256479
theorem B2258027 : Blo 1503572 2258027 := bstep (se 1 (by rfl) ⟨1693520, by rfl⟩ : syracuseStep 2258027 = 3387041) B3387041
theorem B5076107 : Blo 1503572 5076107 := bstep (se 1 (by rfl) ⟨3807080, by rfl⟩ : syracuseStep 5076107 = 7614161) B7614161
theorem B1504463 : Blo 1503572 1504463 := bstep (se 1 (by rfl) ⟨1128347, by rfl⟩ : syracuseStep 1504463 = 2256695) B2256695
theorem B1504667 : Blo 1503572 1504667 := bstep (se 1 (by rfl) ⟨1128500, by rfl⟩ : syracuseStep 1504667 = 2257001) B2257001
theorem B1832347 : Blo 1503572 1832347 := bstep (se 1 (by rfl) ⟨1374260, by rfl⟩ : syracuseStep 1832347 = 2748521) B2748521
theorem B7615943 : Blo 1503572 7615943 := bstep (se 1 (by rfl) ⟨5711957, by rfl⟩ : syracuseStep 7615943 = 11423915) B11423915
theorem B8566343 : Blo 1503572 8566343 := bstep (se 1 (by rfl) ⟨6424757, by rfl⟩ : syracuseStep 8566343 = 12849515) B12849515
theorem B1504879 : Blo 1503572 1504879 := bstep (se 1 (by rfl) ⟨1128659, by rfl⟩ : syracuseStep 1504879 = 2257319) B2257319
theorem B1504935 : Blo 1503572 1504935 := bstep (se 1 (by rfl) ⟨1128701, by rfl⟩ : syracuseStep 1504935 = 2257403) B2257403
theorem B1505019 : Blo 1503572 1505019 := bstep (se 1 (by rfl) ⟨1128764, by rfl⟩ : syracuseStep 1505019 = 2257529) B2257529
theorem B1693435 : Blo 1503572 1693435 := bstep (se 1 (by rfl) ⟨1270076, by rfl⟩ : syracuseStep 1693435 = 2540153) B2540153
theorem B1505055 : Blo 1503572 1505055 := bstep (se 1 (by rfl) ⟨1128791, by rfl⟩ : syracuseStep 1505055 = 2257583) B2257583
theorem B1693471 : Blo 1503572 1693471 := bstep (se 1 (by rfl) ⟨1270103, by rfl⟩ : syracuseStep 1693471 = 2540207) B2540207
theorem B1505087 : Blo 1503572 1505087 := bstep (se 1 (by rfl) ⟨1128815, by rfl⟩ : syracuseStep 1505087 = 2257631) B2257631
theorem B21682055 : Blo 1503572 21682055 := bstep (se 1 (by rfl) ⟨16261541, by rfl⟩ : syracuseStep 21682055 = 32523083) B32523083
theorem B1505263 : Blo 1503572 1505263 := bstep (se 1 (by rfl) ⟨1128947, by rfl⟩ : syracuseStep 1505263 = 2257895) B2257895
theorem B8566843 : Blo 1503572 8566843 := bstep (se 1 (by rfl) ⟨6425132, by rfl⟩ : syracuseStep 8566843 = 12850265) B12850265
theorem B4282465 : Blo 1503572 4282465 := bstep (se 2 (by rfl) ⟨1605924, by rfl⟩ : syracuseStep 4282465 = 3211849) B3211849
theorem B2537615 : Blo 1503572 2537615 := bstep (se 1 (by rfl) ⟨1903211, by rfl⟩ : syracuseStep 2537615 = 3806423) B3806423
theorem B2857103 : Blo 1503572 2857103 := bstep (se 1 (by rfl) ⟨2142827, by rfl⟩ : syracuseStep 2857103 = 4285655) B4285655
theorem B1505435 : Blo 1503572 1505435 := bstep (se 1 (by rfl) ⟨1129076, by rfl⟩ : syracuseStep 1505435 = 2258153) B2258153
theorem B15440033 : Blo 1503572 15440033 := bstep (se 2 (by rfl) ⟨5790012, by rfl⟩ : syracuseStep 15440033 = 11580025) B11580025
theorem B2709883 : Blo 1503572 2709883 := bstep (se 1 (by rfl) ⟨2032412, by rfl⟩ : syracuseStep 2709883 = 4064825) B4064825
theorem B2537851 : Blo 1503572 2537851 := bstep (se 1 (by rfl) ⟨1903388, by rfl⟩ : syracuseStep 2537851 = 3806777) B3806777
theorem B2538121 : Blo 1503572 2538121 := bstep (se 2 (by rfl) ⟨951795, by rfl⟩ : syracuseStep 2538121 = 1903591) B1903591
theorem B3807881 : Blo 1503572 3807881 := bstep (se 2 (by rfl) ⟨1427955, by rfl⟩ : syracuseStep 3807881 = 2855911) B2855911
theorem B5077727 : Blo 1503572 5077727 := bstep (se 1 (by rfl) ⟨3808295, by rfl⟩ : syracuseStep 5077727 = 7616591) B7616591
theorem B5078483 : Blo 1503572 5078483 := bstep (se 1 (by rfl) ⟨3808862, by rfl⟩ : syracuseStep 5078483 = 7617725) B7617725
theorem B8568301 : Blo 1503572 8568301 := bstep (se 3 (by rfl) ⟨1606556, by rfl⟩ : syracuseStep 8568301 = 3213113) B3213113
theorem B278109719 : Blo 1503572 278109719 := bstep (se 1 (by rfl) ⟨208582289, by rfl⟩ : syracuseStep 278109719 = 417164579) B417164579
theorem B5422735 : Blo 1503572 5422735 := bstep (se 1 (by rfl) ⟨4067051, by rfl⟩ : syracuseStep 5422735 = 8134103) B8134103
theorem B5078753 : Blo 1503572 5078753 := bstep (se 2 (by rfl) ⟨1904532, by rfl⟩ : syracuseStep 5078753 = 3809065) B3809065
theorem B16260851 : Blo 1503572 16260851 := bstep (se 1 (by rfl) ⟨12195638, by rfl⟩ : syracuseStep 16260851 = 24391277) B24391277
theorem B3809015 : Blo 1503572 3809015 := bstep (se 1 (by rfl) ⟨2856761, by rfl⟩ : syracuseStep 3809015 = 5713523) B5713523
theorem B4284539 : Blo 1503572 4284539 := bstep (se 1 (by rfl) ⟨3213404, by rfl⟩ : syracuseStep 4284539 = 6426809) B6426809
theorem B5709953 : Blo 1503572 5709953 := bstep (se 2 (by rfl) ⟨2141232, by rfl⟩ : syracuseStep 5709953 = 4282465) B4282465
theorem B1605839 : Blo 1503572 1605839 := bstep (se 1 (by rfl) ⟨1204379, by rfl⟩ : syracuseStep 1605839 = 2408759) B2408759
theorem B3211559 : Blo 1503572 3211559 := bstep (se 1 (by rfl) ⟨2408669, by rfl⟩ : syracuseStep 3211559 = 4817339) B4817339
theorem B5423399 : Blo 1503572 5423399 := bstep (se 1 (by rfl) ⟨4067549, by rfl⟩ : syracuseStep 5423399 = 8135099) B8135099
theorem B5710135 : Blo 1503572 5710135 := bstep (se 1 (by rfl) ⟨4282601, by rfl⟩ : syracuseStep 5710135 = 8565203) B8565203
theorem B3613177 : Blo 1503572 3613177 := bstep (se 2 (by rfl) ⟨1354941, by rfl⟩ : syracuseStep 3613177 = 2709883) B2709883
theorem B3383801 : Blo 1503572 3383801 := bstep (se 2 (by rfl) ⟨1268925, by rfl⟩ : syracuseStep 3383801 = 2537851) B2537851
theorem B3211807 : Blo 1503572 3211807 := bstep (se 1 (by rfl) ⟨2408855, by rfl⟩ : syracuseStep 3211807 = 4817711) B4817711
theorem B3383891 : Blo 1503572 3383891 := bstep (se 1 (by rfl) ⟨2537918, by rfl⟩ : syracuseStep 3383891 = 5075837) B5075837
theorem B3809875 : Blo 1503572 3809875 := bstep (se 1 (by rfl) ⟨2857406, by rfl⟩ : syracuseStep 3809875 = 5714813) B5714813
theorem B6423151 : Blo 1503572 6423151 := bstep (se 1 (by rfl) ⟨4817363, by rfl⟩ : syracuseStep 6423151 = 9634727) B9634727
theorem B3384071 : Blo 1503572 3384071 := bstep (se 1 (by rfl) ⟨2538053, by rfl⟩ : syracuseStep 3384071 = 5076107) B5076107
theorem B3384161 : Blo 1503572 3384161 := bstep (se 2 (by rfl) ⟨1269060, by rfl⟩ : syracuseStep 3384161 = 2538121) B2538121
theorem B3048391 : Blo 1503572 3048391 := bstep (se 1 (by rfl) ⟨2286293, by rfl⟩ : syracuseStep 3048391 = 4572587) B4572587
theorem B14861303 : Blo 1503572 14861303 := bstep (se 1 (by rfl) ⟨11145977, by rfl⟩ : syracuseStep 14861303 = 22291955) B22291955
theorem B5710895 : Blo 1503572 5710895 := bstep (se 1 (by rfl) ⟨4283171, by rfl⟩ : syracuseStep 5710895 = 8566343) B8566343
theorem B2409707 : Blo 1503572 2409707 := bstep (se 1 (by rfl) ⟨1807280, by rfl⟩ : syracuseStep 2409707 = 3614561) B3614561
theorem B3212635 : Blo 1503572 3212635 := bstep (se 1 (by rfl) ⟨2409476, by rfl⟩ : syracuseStep 3212635 = 4818953) B4818953
theorem B30868897 : Blo 1503572 30868897 := bstep (se 2 (by rfl) ⟨11575836, by rfl⟩ : syracuseStep 30868897 = 23151673) B23151673
theorem B2410015 : Blo 1503572 2410015 := bstep (se 1 (by rfl) ⟨1807511, by rfl⟩ : syracuseStep 2410015 = 3615023) B3615023
theorem B5080751 : Blo 1503572 5080751 := bstep (se 1 (by rfl) ⟨3810563, by rfl⟩ : syracuseStep 5080751 = 7621127) B7621127
theorem B3385151 : Blo 1503572 3385151 := bstep (se 1 (by rfl) ⟨2538863, by rfl⟩ : syracuseStep 3385151 = 5077727) B5077727
theorem B2443129 : Blo 1503572 2443129 := bstep (se 2 (by rfl) ⟨916173, by rfl⟩ : syracuseStep 2443129 = 1832347) B1832347
theorem B3213199 : Blo 1503572 3213199 := bstep (se 1 (by rfl) ⟨2409899, by rfl⟩ : syracuseStep 3213199 = 4819799) B4819799
theorem B10848239 : Blo 1503572 10848239 := bstep (se 1 (by rfl) ⟨8136179, by rfl⟩ : syracuseStep 10848239 = 16272359) B16272359
theorem B6424859 : Blo 1503572 6424859 := bstep (se 1 (by rfl) ⟨4818644, by rfl⟩ : syracuseStep 6424859 = 9637289) B9637289
theorem B3385655 : Blo 1503572 3385655 := bstep (se 1 (by rfl) ⟨2539241, by rfl⟩ : syracuseStep 3385655 = 5078483) B5078483
theorem B11430233 : Blo 1503572 11430233 := bstep (se 2 (by rfl) ⟨4286337, by rfl⟩ : syracuseStep 11430233 = 8572675) B8572675
theorem B3213695 : Blo 1503572 3213695 := bstep (se 1 (by rfl) ⟨2410271, by rfl⟩ : syracuseStep 3213695 = 4820543) B4820543
theorem B3385835 : Blo 1503572 3385835 := bstep (se 1 (by rfl) ⟨2539376, by rfl⟩ : syracuseStep 3385835 = 5078753) B5078753
theorem B10840567 : Blo 1503572 10840567 := bstep (se 1 (by rfl) ⟨8130425, by rfl⟩ : syracuseStep 10840567 = 16260851) B16260851
theorem B11422457 : Blo 1503572 11422457 := bstep (se 2 (by rfl) ⟨4283421, by rfl⟩ : syracuseStep 11422457 = 8566843) B8566843
theorem B8563745 : Blo 1503572 8563745 := bstep (se 2 (by rfl) ⟨3211404, by rfl⟩ : syracuseStep 8563745 = 6422809) B6422809
theorem B2256041 : Blo 1503572 2256041 := bstep (se 2 (by rfl) ⟨846015, by rfl⟩ : syracuseStep 2256041 = 1692031) B1692031
theorem B3386537 : Blo 1503572 3386537 := bstep (se 2 (by rfl) ⟨1269951, by rfl⟩ : syracuseStep 3386537 = 2539903) B2539903
theorem B16272613 : Blo 1503572 16272613 := bstep (se 4 (by rfl) ⟨1525557, by rfl⟩ : syracuseStep 16272613 = 3051115) B3051115
theorem B25701623 : Blo 1503572 25701623 := bstep (se 1 (by rfl) ⟨19276217, by rfl⟩ : syracuseStep 25701623 = 38552435) B38552435
theorem B3214703 : Blo 1503572 3214703 := bstep (se 1 (by rfl) ⟨2411027, by rfl⟩ : syracuseStep 3214703 = 4822055) B4822055
theorem B2256455 : Blo 1503572 2256455 := bstep (se 1 (by rfl) ⟨1692341, by rfl⟩ : syracuseStep 2256455 = 3384683) B3384683
theorem B3386951 : Blo 1503572 3386951 := bstep (se 1 (by rfl) ⟨2540213, by rfl⟩ : syracuseStep 3386951 = 5080427) B5080427
theorem B12201607 : Blo 1503572 12201607 := bstep (se 1 (by rfl) ⟨9151205, by rfl⟩ : syracuseStep 12201607 = 18302411) B18302411
theorem B3387023 : Blo 1503572 3387023 := bstep (se 1 (by rfl) ⟨2540267, by rfl⟩ : syracuseStep 3387023 = 5080535) B5080535
theorem B3387113 : Blo 1503572 3387113 := bstep (se 2 (by rfl) ⟨1270167, by rfl⟩ : syracuseStep 3387113 = 2540335) B2540335
theorem B2256635 : Blo 1503572 2256635 := bstep (se 1 (by rfl) ⟨1692476, by rfl⟩ : syracuseStep 2256635 = 3384953) B3384953
theorem B3387131 : Blo 1503572 3387131 := bstep (se 1 (by rfl) ⟨2540348, by rfl⟩ : syracuseStep 3387131 = 5080697) B5080697
theorem B32550761 : Blo 1503572 32550761 := bstep (se 2 (by rfl) ⟨12206535, by rfl⟩ : syracuseStep 32550761 = 24413071) B24413071
theorem B14454703 : Blo 1503572 14454703 := bstep (se 1 (by rfl) ⟨10841027, by rfl⟩ : syracuseStep 14454703 = 21682055) B21682055
theorem B38539313 : Blo 1503572 38539313 := bstep (se 2 (by rfl) ⟨14452242, by rfl⟩ : syracuseStep 38539313 = 28904485) B28904485
theorem B13201481 : Blo 1503572 13201481 := bstep (se 2 (by rfl) ⟨4950555, by rfl⟩ : syracuseStep 13201481 = 9901111) B9901111
theorem B5075027 : Blo 1503572 5075027 := bstep (se 1 (by rfl) ⟨3806270, by rfl⟩ : syracuseStep 5075027 = 7612541) B7612541
theorem B1691743 : Blo 1503572 1691743 := bstep (se 1 (by rfl) ⟨1268807, by rfl⟩ : syracuseStep 1691743 = 2537615) B2537615
theorem B1904735 : Blo 1503572 1904735 := bstep (se 1 (by rfl) ⟨1428551, by rfl⟩ : syracuseStep 1904735 = 2857103) B2857103
theorem B10293355 : Blo 1503572 10293355 := bstep (se 1 (by rfl) ⟨7720016, by rfl⟩ : syracuseStep 10293355 = 15440033) B15440033
theorem B1929343 : Blo 1503572 1929343 := bstep (se 1 (by rfl) ⟨1447007, by rfl⟩ : syracuseStep 1929343 = 2894015) B2894015
theorem B109801615 : Blo 1503572 109801615 := bstep (se 1 (by rfl) ⟨82351211, by rfl⟩ : syracuseStep 109801615 = 164702423) B164702423
theorem B8376605 : Blo 1503572 8376605 := bstep (se 3 (by rfl) ⟨1570613, by rfl⟩ : syracuseStep 8376605 = 3141227) B3141227
theorem B1503591 : Blo 1503572 1503591 := bstep (se 1 (by rfl) ⟨1127693, by rfl⟩ : syracuseStep 1503591 = 2255387) B2255387
theorem B1503643 : Blo 1503572 1503643 := bstep (se 1 (by rfl) ⟨1127732, by rfl⟩ : syracuseStep 1503643 = 2255465) B2255465
theorem B2257307 : Blo 1503572 2257307 := bstep (se 1 (by rfl) ⟨1692980, by rfl⟩ : syracuseStep 2257307 = 3385961) B3385961
theorem B32543153 : Blo 1503572 32543153 := bstep (se 2 (by rfl) ⟨12203682, by rfl⟩ : syracuseStep 32543153 = 24407365) B24407365
theorem B5714495 : Blo 1503572 5714495 := bstep (se 1 (by rfl) ⟨4285871, by rfl⟩ : syracuseStep 5714495 = 8571743) B8571743
theorem B11424401 : Blo 1503572 11424401 := bstep (se 2 (by rfl) ⟨4284150, by rfl⟩ : syracuseStep 11424401 = 8568301) B8568301
theorem B1503995 : Blo 1503572 1503995 := bstep (se 1 (by rfl) ⟨1127996, by rfl⟩ : syracuseStep 1503995 = 2255993) B2255993
theorem B1504063 : Blo 1503572 1504063 := bstep (se 1 (by rfl) ⟨1128047, by rfl⟩ : syracuseStep 1504063 = 2256095) B2256095
theorem B2257727 : Blo 1503572 2257727 := bstep (se 1 (by rfl) ⟨1693295, by rfl⟩ : syracuseStep 2257727 = 3386591) B3386591
theorem B1504091 : Blo 1503572 1504091 := bstep (se 1 (by rfl) ⟨1128068, by rfl⟩ : syracuseStep 1504091 = 2256137) B2256137
theorem B7230313 : Blo 1503572 7230313 := bstep (se 2 (by rfl) ⟨2711367, by rfl⟩ : syracuseStep 7230313 = 5422735) B5422735
theorem B15438721 : Blo 1503572 15438721 := bstep (se 2 (by rfl) ⟨5789520, by rfl⟩ : syracuseStep 15438721 = 11579041) B11579041
theorem B1504159 : Blo 1503572 1504159 := bstep (se 1 (by rfl) ⟨1128119, by rfl⟩ : syracuseStep 1504159 = 2256239) B2256239
theorem B2257871 : Blo 1503572 2257871 := bstep (se 1 (by rfl) ⟨1693403, by rfl⟩ : syracuseStep 2257871 = 3386807) B3386807
theorem B1504239 : Blo 1503572 1504239 := bstep (se 1 (by rfl) ⟨1128179, by rfl⟩ : syracuseStep 1504239 = 2256359) B2256359
theorem B2257913 : Blo 1503572 2257913 := bstep (se 2 (by rfl) ⟨846717, by rfl⟩ : syracuseStep 2257913 = 1693435) B1693435
theorem B185406479 : Blo 1503572 185406479 := bstep (se 1 (by rfl) ⟨139054859, by rfl⟩ : syracuseStep 185406479 = 278109719) B278109719
theorem B2257961 : Blo 1503572 2257961 := bstep (se 2 (by rfl) ⟨846735, by rfl⟩ : syracuseStep 2257961 = 1693471) B1693471
theorem B1504327 : Blo 1503572 1504327 := bstep (se 1 (by rfl) ⟨1128245, by rfl⟩ : syracuseStep 1504327 = 2256491) B2256491
theorem B2257991 : Blo 1503572 2257991 := bstep (se 1 (by rfl) ⟨1693493, by rfl⟩ : syracuseStep 2257991 = 3386987) B3386987
theorem B1504411 : Blo 1503572 1504411 := bstep (se 1 (by rfl) ⟨1128308, by rfl⟩ : syracuseStep 1504411 = 2256617) B2256617
theorem B1504507 : Blo 1503572 1504507 := bstep (se 1 (by rfl) ⟨1128380, by rfl⟩ : syracuseStep 1504507 = 2256761) B2256761
theorem B2258171 : Blo 1503572 2258171 := bstep (se 1 (by rfl) ⟨1693628, by rfl⟩ : syracuseStep 2258171 = 3387257) B3387257
theorem B1504575 : Blo 1503572 1504575 := bstep (se 1 (by rfl) ⟨1128431, by rfl⟩ : syracuseStep 1504575 = 2256863) B2256863
theorem B1504743 : Blo 1503572 1504743 := bstep (se 1 (by rfl) ⟨1128557, by rfl⟩ : syracuseStep 1504743 = 2257115) B2257115
theorem B1504751 : Blo 1503572 1504751 := bstep (se 1 (by rfl) ⟨1128563, by rfl⟩ : syracuseStep 1504751 = 2257127) B2257127
theorem B1504859 : Blo 1503572 1504859 := bstep (se 1 (by rfl) ⟨1128644, by rfl⟩ : syracuseStep 1504859 = 2257289) B2257289
theorem B1504923 : Blo 1503572 1504923 := bstep (se 1 (by rfl) ⟨1128692, by rfl⟩ : syracuseStep 1504923 = 2257385) B2257385
theorem B3806939 : Blo 1503572 3806939 := bstep (se 1 (by rfl) ⟨2855204, by rfl⟩ : syracuseStep 3806939 = 5710409) B5710409
theorem B1505007 : Blo 1503572 1505007 := bstep (se 1 (by rfl) ⟨1128755, by rfl⟩ : syracuseStep 1505007 = 2257511) B2257511
theorem B1505095 : Blo 1503572 1505095 := bstep (se 1 (by rfl) ⟨1128821, by rfl⟩ : syracuseStep 1505095 = 2257643) B2257643
theorem B1505115 : Blo 1503572 1505115 := bstep (se 1 (by rfl) ⟨1128836, by rfl⟩ : syracuseStep 1505115 = 2257673) B2257673
theorem B1505183 : Blo 1503572 1505183 := bstep (se 1 (by rfl) ⟨1128887, by rfl⟩ : syracuseStep 1505183 = 2257775) B2257775
theorem B11425859 : Blo 1503572 11425859 := bstep (se 1 (by rfl) ⟨8569394, by rfl⟩ : syracuseStep 11425859 = 17138789) B17138789
theorem B1505351 : Blo 1503572 1505351 := bstep (se 1 (by rfl) ⟨1129013, by rfl⟩ : syracuseStep 1505351 = 2258027) B2258027
theorem B2644255 : Blo 1503572 2644255 := bstep (se 1 (by rfl) ⟨1983191, by rfl⟩ : syracuseStep 2644255 = 3966383) B3966383
theorem B5077295 : Blo 1503572 5077295 := bstep (se 1 (by rfl) ⟨3807971, by rfl⟩ : syracuseStep 5077295 = 7615943) B7615943
theorem B3807719 : Blo 1503572 3807719 := bstep (se 1 (by rfl) ⟨2855789, by rfl⟩ : syracuseStep 3807719 = 5711579) B5711579
theorem B27466397 : Blo 1503572 27466397 := bstep (se 3 (by rfl) ⟨5149949, by rfl⟩ : syracuseStep 27466397 = 10299899) B10299899
theorem B15440699 : Blo 1503572 15440699 := bstep (se 1 (by rfl) ⟨11580524, by rfl⟩ : syracuseStep 15440699 = 23161049) B23161049
theorem B11426831 : Blo 1503572 11426831 := bstep (se 1 (by rfl) ⟨8570123, by rfl⟩ : syracuseStep 11426831 = 17140247) B17140247
theorem B2538587 : Blo 1503572 2538587 := bstep (se 1 (by rfl) ⟨1903940, by rfl⟩ : syracuseStep 2538587 = 3807881) B3807881
theorem B20585947 : Blo 1503572 20585947 := bstep (se 1 (by rfl) ⟨15439460, by rfl⟩ : syracuseStep 20585947 = 30878921) B30878921
theorem B2539343 : Blo 1503572 2539343 := bstep (se 1 (by rfl) ⟨1904507, by rfl⟩ : syracuseStep 2539343 = 3809015) B3809015
theorem B3383351 : Blo 1503572 3383351 := bstep (se 1 (by rfl) ⟨2537513, by rfl⟩ : syracuseStep 3383351 = 5075027) B5075027
theorem B2572457 : Blo 1503572 2572457 := bstep (se 2 (by rfl) ⟨964671, by rfl⟩ : syracuseStep 2572457 = 1929343) B1929343
theorem B5079293 : Blo 1503572 5079293 := bstep (se 3 (by rfl) ⟨952367, by rfl⟩ : syracuseStep 5079293 = 1904735) B1904735
theorem B3809663 : Blo 1503572 3809663 := bstep (se 1 (by rfl) ⟨2857247, by rfl⟩ : syracuseStep 3809663 = 5714495) B5714495
theorem B4817569 : Blo 1503572 4817569 := bstep (se 2 (by rfl) ⟨1806588, by rfl⟩ : syracuseStep 4817569 = 3613177) B3613177
theorem B5079833 : Blo 1503572 5079833 := bstep (se 2 (by rfl) ⟨1904937, by rfl⟩ : syracuseStep 5079833 = 3809875) B3809875
theorem B4064521 : Blo 1503572 4064521 := bstep (se 2 (by rfl) ⟨1524195, by rfl⟩ : syracuseStep 4064521 = 3048391) B3048391
theorem B3384863 : Blo 1503572 3384863 := bstep (se 1 (by rfl) ⟨2538647, by rfl⟩ : syracuseStep 3384863 = 5077295) B5077295
theorem B7620155 : Blo 1503572 7620155 := bstep (se 1 (by rfl) ⟨5715116, by rfl⟩ : syracuseStep 7620155 = 11430233) B11430233
theorem B18310931 : Blo 1503572 18310931 := bstep (se 1 (by rfl) ⟨13733198, by rfl⟩ : syracuseStep 18310931 = 27466397) B27466397
theorem B41158529 : Blo 1503572 41158529 := bstep (se 2 (by rfl) ⟨15434448, by rfl⟩ : syracuseStep 41158529 = 30868897) B30868897
theorem B3213353 : Blo 1503572 3213353 := bstep (se 2 (by rfl) ⟨1205007, by rfl⟩ : syracuseStep 3213353 = 2410015) B2410015
theorem B25692875 : Blo 1503572 25692875 := bstep (se 1 (by rfl) ⟨19269656, by rfl⟩ : syracuseStep 25692875 = 38539313) B38539313
theorem B8800987 : Blo 1503572 8800987 := bstep (se 1 (by rfl) ⟨6600740, by rfl⟩ : syracuseStep 8800987 = 13201481) B13201481
theorem B2255657 : Blo 1503572 2255657 := bstep (se 2 (by rfl) ⟨845871, by rfl⟩ : syracuseStep 2255657 = 1691743) B1691743
theorem B13724473 : Blo 1503572 13724473 := bstep (se 2 (by rfl) ⟨5146677, by rfl⟩ : syracuseStep 13724473 = 10293355) B10293355
theorem B146402153 : Blo 1503572 146402153 := bstep (se 2 (by rfl) ⟨54900807, by rfl⟩ : syracuseStep 146402153 = 109801615) B109801615
theorem B2141039 : Blo 1503572 2141039 := bstep (se 1 (by rfl) ⟨1605779, by rfl⟩ : syracuseStep 2141039 = 3211559) B3211559
theorem B3615599 : Blo 1503572 3615599 := bstep (se 1 (by rfl) ⟨2711699, by rfl⟩ : syracuseStep 3615599 = 5423399) B5423399
theorem B21695435 : Blo 1503572 21695435 := bstep (se 1 (by rfl) ⟨16271576, by rfl⟩ : syracuseStep 21695435 = 32543153) B32543153
theorem B2255867 : Blo 1503572 2255867 := bstep (se 1 (by rfl) ⟨1691900, by rfl⟩ : syracuseStep 2255867 = 3383801) B3383801
theorem B2255927 : Blo 1503572 2255927 := bstep (se 1 (by rfl) ⟨1691945, by rfl⟩ : syracuseStep 2255927 = 3383891) B3383891
theorem B7613513 : Blo 1503572 7613513 := bstep (se 2 (by rfl) ⟨2855067, by rfl⟩ : syracuseStep 7613513 = 5710135) B5710135
theorem B2256047 : Blo 1503572 2256047 := bstep (se 1 (by rfl) ⟨1692035, by rfl⟩ : syracuseStep 2256047 = 3384071) B3384071
theorem B2256107 : Blo 1503572 2256107 := bstep (se 1 (by rfl) ⟨1692080, by rfl⟩ : syracuseStep 2256107 = 3384161) B3384161
theorem B6425885 : Blo 1503572 6425885 := bstep (se 3 (by rfl) ⟨1204853, by rfl⟩ : syracuseStep 6425885 = 2409707) B2409707
theorem B14454089 : Blo 1503572 14454089 := bstep (se 2 (by rfl) ⟨5420283, by rfl⟩ : syracuseStep 14454089 = 10840567) B10840567
theorem B9907535 : Blo 1503572 9907535 := bstep (se 1 (by rfl) ⟨7430651, by rfl⟩ : syracuseStep 9907535 = 14861303) B14861303
theorem B123604319 : Blo 1503572 123604319 := bstep (se 1 (by rfl) ⟨92703239, by rfl⟩ : syracuseStep 123604319 = 185406479) B185406479
theorem B17132957 : Blo 1503572 17132957 := bstep (se 3 (by rfl) ⟨3212429, by rfl⟩ : syracuseStep 17132957 = 6424859) B6424859
theorem B8564201 : Blo 1503572 8564201 := bstep (se 2 (by rfl) ⟨3211575, by rfl⟩ : syracuseStep 8564201 = 6423151) B6423151
theorem B3387167 : Blo 1503572 3387167 := bstep (se 1 (by rfl) ⟨2540375, by rfl⟩ : syracuseStep 3387167 = 5080751) B5080751
theorem B2256767 : Blo 1503572 2256767 := bstep (se 1 (by rfl) ⟨1692575, by rfl⟩ : syracuseStep 2256767 = 3385151) B3385151
theorem B14102693 : Blo 1503572 14102693 := bstep (se 4 (by rfl) ⟨1322127, by rfl⟩ : syracuseStep 14102693 = 2644255) B2644255
theorem B2257103 : Blo 1503572 2257103 := bstep (se 1 (by rfl) ⟨1692827, by rfl⟩ : syracuseStep 2257103 = 3385655) B3385655
theorem B2142463 : Blo 1503572 2142463 := bstep (se 1 (by rfl) ⟨1606847, by rfl⟩ : syracuseStep 2142463 = 3213695) B3213695
theorem B21696817 : Blo 1503572 21696817 := bstep (se 2 (by rfl) ⟨8136306, by rfl⟩ : syracuseStep 21696817 = 16272613) B16272613
theorem B2257223 : Blo 1503572 2257223 := bstep (se 1 (by rfl) ⟨1692917, by rfl⟩ : syracuseStep 2257223 = 3385835) B3385835
theorem B7614971 : Blo 1503572 7614971 := bstep (se 1 (by rfl) ⟨5711228, by rfl⟩ : syracuseStep 7614971 = 11422457) B11422457
theorem B10293799 : Blo 1503572 10293799 := bstep (se 1 (by rfl) ⟨7720349, by rfl⟩ : syracuseStep 10293799 = 15440699) B15440699
theorem B27447929 : Blo 1503572 27447929 := bstep (se 2 (by rfl) ⟨10292973, by rfl⟩ : syracuseStep 27447929 = 20585947) B20585947
theorem B13030021 : Blo 1503572 13030021 := bstep (se 4 (by rfl) ⟨1221564, by rfl⟩ : syracuseStep 13030021 = 2443129) B2443129
theorem B1692391 : Blo 1503572 1692391 := bstep (se 1 (by rfl) ⟨1269293, by rfl⟩ : syracuseStep 1692391 = 2538587) B2538587
theorem B1504027 : Blo 1503572 1504027 := bstep (se 1 (by rfl) ⟨1128020, by rfl⟩ : syracuseStep 1504027 = 2256041) B2256041
theorem B2257691 : Blo 1503572 2257691 := bstep (se 1 (by rfl) ⟨1693268, by rfl⟩ : syracuseStep 2257691 = 3386537) B3386537
theorem B17134415 : Blo 1503572 17134415 := bstep (se 1 (by rfl) ⟨12850811, by rfl⟩ : syracuseStep 17134415 = 25701623) B25701623
theorem B2143135 : Blo 1503572 2143135 := bstep (se 1 (by rfl) ⟨1607351, by rfl⟩ : syracuseStep 2143135 = 3214703) B3214703
theorem B1504303 : Blo 1503572 1504303 := bstep (se 1 (by rfl) ⟨1128227, by rfl⟩ : syracuseStep 1504303 = 2256455) B2256455
theorem B2257967 : Blo 1503572 2257967 := bstep (se 1 (by rfl) ⟨1693475, by rfl⟩ : syracuseStep 2257967 = 3386951) B3386951
theorem B2258015 : Blo 1503572 2258015 := bstep (se 1 (by rfl) ⟨1693511, by rfl⟩ : syracuseStep 2258015 = 3387023) B3387023
theorem B2258075 : Blo 1503572 2258075 := bstep (se 1 (by rfl) ⟨1693556, by rfl⟩ : syracuseStep 2258075 = 3387113) B3387113
theorem B1504423 : Blo 1503572 1504423 := bstep (se 1 (by rfl) ⟨1128317, by rfl⟩ : syracuseStep 1504423 = 2256635) B2256635
theorem B2258087 : Blo 1503572 2258087 := bstep (se 1 (by rfl) ⟨1693565, by rfl⟩ : syracuseStep 2258087 = 3387131) B3387131
theorem B1692895 : Blo 1503572 1692895 := bstep (se 1 (by rfl) ⟨1269671, by rfl⟩ : syracuseStep 1692895 = 2539343) B2539343
theorem B19272937 : Blo 1503572 19272937 := bstep (se 2 (by rfl) ⟨7227351, by rfl⟩ : syracuseStep 19272937 = 14454703) B14454703
theorem B2856359 : Blo 1503572 2856359 := bstep (se 1 (by rfl) ⟨2142269, by rfl⟩ : syracuseStep 2856359 = 4284539) B4284539
theorem B3806635 : Blo 1503572 3806635 := bstep (se 1 (by rfl) ⟨2854976, by rfl⟩ : syracuseStep 3806635 = 5709953) B5709953
theorem B5584403 : Blo 1503572 5584403 := bstep (se 1 (by rfl) ⟨4188302, by rfl⟩ : syracuseStep 5584403 = 8376605) B8376605
theorem B1504871 : Blo 1503572 1504871 := bstep (se 1 (by rfl) ⟨1128653, by rfl⟩ : syracuseStep 1504871 = 2257307) B2257307
theorem B7616267 : Blo 1503572 7616267 := bstep (se 1 (by rfl) ⟨5712200, by rfl⟩ : syracuseStep 7616267 = 11424401) B11424401
theorem B4282237 : Blo 1503572 4282237 := bstep (se 3 (by rfl) ⟨802919, by rfl⟩ : syracuseStep 4282237 = 1605839) B1605839
theorem B1505151 : Blo 1503572 1505151 := bstep (se 1 (by rfl) ⟨1128863, by rfl⟩ : syracuseStep 1505151 = 2257727) B2257727
theorem B1505247 : Blo 1503572 1505247 := bstep (se 1 (by rfl) ⟨1128935, by rfl⟩ : syracuseStep 1505247 = 2257871) B2257871
theorem B1505275 : Blo 1503572 1505275 := bstep (se 1 (by rfl) ⟨1128956, by rfl⟩ : syracuseStep 1505275 = 2257913) B2257913
theorem B1505307 : Blo 1503572 1505307 := bstep (se 1 (by rfl) ⟨1128980, by rfl⟩ : syracuseStep 1505307 = 2257961) B2257961
theorem B3807263 : Blo 1503572 3807263 := bstep (se 1 (by rfl) ⟨2855447, by rfl⟩ : syracuseStep 3807263 = 5710895) B5710895
theorem B4282409 : Blo 1503572 4282409 := bstep (se 2 (by rfl) ⟨1605903, by rfl⟩ : syracuseStep 4282409 = 3211807) B3211807
theorem B1505327 : Blo 1503572 1505327 := bstep (se 1 (by rfl) ⟨1128995, by rfl⟩ : syracuseStep 1505327 = 2257991) B2257991
theorem B1505447 : Blo 1503572 1505447 := bstep (se 1 (by rfl) ⟨1129085, by rfl⟩ : syracuseStep 1505447 = 2258171) B2258171
theorem B9640417 : Blo 1503572 9640417 := bstep (se 2 (by rfl) ⟨3615156, by rfl⟩ : syracuseStep 9640417 = 7230313) B7230313
theorem B2537959 : Blo 1503572 2537959 := bstep (se 1 (by rfl) ⟨1903469, by rfl⟩ : syracuseStep 2537959 = 3806939) B3806939
theorem B20584961 : Blo 1503572 20584961 := bstep (se 2 (by rfl) ⟨7719360, by rfl⟩ : syracuseStep 20584961 = 15438721) B15438721
theorem B7232159 : Blo 1503572 7232159 := bstep (se 1 (by rfl) ⟨5424119, by rfl⟩ : syracuseStep 7232159 = 10848239) B10848239
theorem B7617239 : Blo 1503572 7617239 := bstep (se 1 (by rfl) ⟨5712929, by rfl⟩ : syracuseStep 7617239 = 11425859) B11425859
theorem B2538479 : Blo 1503572 2538479 := bstep (se 1 (by rfl) ⟨1903859, by rfl⟩ : syracuseStep 2538479 = 3807719) B3807719
theorem B4283513 : Blo 1503572 4283513 := bstep (se 2 (by rfl) ⟨1606317, by rfl⟩ : syracuseStep 4283513 = 3212635) B3212635
theorem B7617887 : Blo 1503572 7617887 := bstep (se 1 (by rfl) ⟨5713415, by rfl⟩ : syracuseStep 7617887 = 11426831) B11426831
theorem B5709163 : Blo 1503572 5709163 := bstep (se 1 (by rfl) ⟨4281872, by rfl⟩ : syracuseStep 5709163 = 8563745) B8563745
theorem B16268809 : Blo 1503572 16268809 := bstep (se 2 (by rfl) ⟨6100803, by rfl⟩ : syracuseStep 16268809 = 12201607) B12201607
theorem B86802029 : Blo 1503572 86802029 := bstep (se 3 (by rfl) ⟨16275380, by rfl⟩ : syracuseStep 86802029 = 32550761) B32550761
theorem B4284265 : Blo 1503572 4284265 := bstep (se 2 (by rfl) ⟨1606599, by rfl⟩ : syracuseStep 4284265 = 3213199) B3213199
theorem B2539775 : Blo 1503572 2539775 := bstep (se 1 (by rfl) ⟨1904831, by rfl⟩ : syracuseStep 2539775 = 3809663) B3809663
theorem B12853889 : Blo 1503572 12853889 := bstep (se 2 (by rfl) ⟨4820208, by rfl⟩ : syracuseStep 12853889 = 9640417) B9640417
theorem B3383945 : Blo 1503572 3383945 := bstep (se 2 (by rfl) ⟨1268979, by rfl⟩ : syracuseStep 3383945 = 2537959) B2537959
theorem B26420093 : Blo 1503572 26420093 := bstep (se 3 (by rfl) ⟨4953767, by rfl⟩ : syracuseStep 26420093 = 9907535) B9907535
theorem B6423425 : Blo 1503572 6423425 := bstep (se 2 (by rfl) ⟨2408784, by rfl⟩ : syracuseStep 6423425 = 4817569) B4817569
theorem B5080103 : Blo 1503572 5080103 := bstep (se 1 (by rfl) ⟨3810077, by rfl⟩ : syracuseStep 5080103 = 7620155) B7620155
theorem B12207287 : Blo 1503572 12207287 := bstep (se 1 (by rfl) ⟨9155465, by rfl⟩ : syracuseStep 12207287 = 18310931) B18310931
theorem B13723307 : Blo 1503572 13723307 := bstep (se 1 (by rfl) ⟨10292480, by rfl⟩ : syracuseStep 13723307 = 20584961) B20584961
theorem B7612217 : Blo 1503572 7612217 := bstep (se 2 (by rfl) ⟨2854581, by rfl⟩ : syracuseStep 7612217 = 5709163) B5709163
theorem B97601435 : Blo 1503572 97601435 := bstep (se 1 (by rfl) ⟨73201076, by rfl⟩ : syracuseStep 97601435 = 146402153) B146402153
theorem B2410399 : Blo 1503572 2410399 := bstep (se 1 (by rfl) ⟨1807799, by rfl⟩ : syracuseStep 2410399 = 3615599) B3615599
theorem B9636059 : Blo 1503572 9636059 := bstep (se 1 (by rfl) ⟨7227044, by rfl⟩ : syracuseStep 9636059 = 14454089) B14454089
theorem B11421971 : Blo 1503572 11421971 := bstep (se 1 (by rfl) ⟨8566478, by rfl⟩ : syracuseStep 11421971 = 17132957) B17132957
theorem B5712353 : Blo 1503572 5712353 := bstep (se 2 (by rfl) ⟨2142132, by rfl⟩ : syracuseStep 5712353 = 4284265) B4284265
theorem B2255567 : Blo 1503572 2255567 := bstep (se 1 (by rfl) ⟨1691675, by rfl⟩ : syracuseStep 2255567 = 3383351) B3383351
theorem B3386195 : Blo 1503572 3386195 := bstep (se 1 (by rfl) ⟨2539646, by rfl⟩ : syracuseStep 3386195 = 5079293) B5079293
theorem B28929089 : Blo 1503572 28929089 := bstep (se 2 (by rfl) ⟨10848408, by rfl⟩ : syracuseStep 28929089 = 21696817) B21696817
theorem B6859885 : Blo 1503572 6859885 := bstep (se 3 (by rfl) ⟨1286228, by rfl⟩ : syracuseStep 6859885 = 2572457) B2572457
theorem B3386555 : Blo 1503572 3386555 := bstep (se 1 (by rfl) ⟨2539916, by rfl⟩ : syracuseStep 3386555 = 5079833) B5079833
theorem B11422943 : Blo 1503572 11422943 := bstep (se 1 (by rfl) ⟨8567207, by rfl⟩ : syracuseStep 11422943 = 17134415) B17134415
theorem B13725065 : Blo 1503572 13725065 := bstep (se 2 (by rfl) ⟨5146899, by rfl⟩ : syracuseStep 13725065 = 10293799) B10293799
theorem B1904239 : Blo 1503572 1904239 := bstep (se 1 (by rfl) ⟨1428179, by rfl⟩ : syracuseStep 1904239 = 2856359) B2856359
theorem B11734649 : Blo 1503572 11734649 := bstep (se 2 (by rfl) ⟨4400493, by rfl⟩ : syracuseStep 11734649 = 8800987) B8800987
theorem B2256521 : Blo 1503572 2256521 := bstep (se 2 (by rfl) ⟨846195, by rfl⟩ : syracuseStep 2256521 = 1692391) B1692391
theorem B3722935 : Blo 1503572 3722935 := bstep (se 1 (by rfl) ⟨2792201, by rfl⟩ : syracuseStep 3722935 = 5584403) B5584403
theorem B2256575 : Blo 1503572 2256575 := bstep (se 1 (by rfl) ⟨1692431, by rfl⟩ : syracuseStep 2256575 = 3384863) B3384863
theorem B27439019 : Blo 1503572 27439019 := bstep (se 1 (by rfl) ⟨20579264, by rfl⟩ : syracuseStep 27439019 = 41158529) B41158529
theorem B2854939 : Blo 1503572 2854939 := bstep (se 1 (by rfl) ⟨2141204, by rfl⟩ : syracuseStep 2854939 = 4282409) B4282409
theorem B2142235 : Blo 1503572 2142235 := bstep (se 1 (by rfl) ⟨1606676, by rfl⟩ : syracuseStep 2142235 = 3213353) B3213353
theorem B2257193 : Blo 1503572 2257193 := bstep (se 2 (by rfl) ⟨846447, by rfl⟩ : syracuseStep 2257193 = 1692895) B1692895
theorem B5419361 : Blo 1503572 5419361 := bstep (se 2 (by rfl) ⟨2032260, by rfl⟩ : syracuseStep 5419361 = 4064521) B4064521
theorem B4821439 : Blo 1503572 4821439 := bstep (se 1 (by rfl) ⟨3616079, by rfl⟩ : syracuseStep 4821439 = 7232159) B7232159
theorem B1503771 : Blo 1503572 1503771 := bstep (se 1 (by rfl) ⟨1127828, by rfl⟩ : syracuseStep 1503771 = 2255657) B2255657
theorem B5075513 : Blo 1503572 5075513 := bstep (se 2 (by rfl) ⟨1903317, by rfl⟩ : syracuseStep 5075513 = 3806635) B3806635
theorem B14463623 : Blo 1503572 14463623 := bstep (se 1 (by rfl) ⟨10847717, by rfl⟩ : syracuseStep 14463623 = 21695435) B21695435
theorem B1692319 : Blo 1503572 1692319 := bstep (se 1 (by rfl) ⟨1269239, by rfl⟩ : syracuseStep 1692319 = 2538479) B2538479
theorem B1503911 : Blo 1503572 1503911 := bstep (se 1 (by rfl) ⟨1127933, by rfl⟩ : syracuseStep 1503911 = 2255867) B2255867
theorem B1503951 : Blo 1503572 1503951 := bstep (se 1 (by rfl) ⟨1127963, by rfl⟩ : syracuseStep 1503951 = 2255927) B2255927
theorem B5075675 : Blo 1503572 5075675 := bstep (se 1 (by rfl) ⟨3806756, by rfl⟩ : syracuseStep 5075675 = 7613513) B7613513
theorem B2855675 : Blo 1503572 2855675 := bstep (se 1 (by rfl) ⟨2141756, by rfl⟩ : syracuseStep 2855675 = 4283513) B4283513
theorem B1504031 : Blo 1503572 1504031 := bstep (se 1 (by rfl) ⟨1128023, by rfl⟩ : syracuseStep 1504031 = 2256047) B2256047
theorem B1504071 : Blo 1503572 1504071 := bstep (se 1 (by rfl) ⟨1128053, by rfl⟩ : syracuseStep 1504071 = 2256107) B2256107
theorem B2258111 : Blo 1503572 2258111 := bstep (se 1 (by rfl) ⟨1693583, by rfl⟩ : syracuseStep 2258111 = 3387167) B3387167
theorem B1504511 : Blo 1503572 1504511 := bstep (se 1 (by rfl) ⟨1128383, by rfl⟩ : syracuseStep 1504511 = 2256767) B2256767
theorem B9401795 : Blo 1503572 9401795 := bstep (se 1 (by rfl) ⟨7051346, by rfl⟩ : syracuseStep 9401795 = 14102693) B14102693
theorem B1504735 : Blo 1503572 1504735 := bstep (se 1 (by rfl) ⟨1128551, by rfl⟩ : syracuseStep 1504735 = 2257103) B2257103
theorem B1504815 : Blo 1503572 1504815 := bstep (se 1 (by rfl) ⟨1128611, by rfl⟩ : syracuseStep 1504815 = 2257223) B2257223
theorem B5076647 : Blo 1503572 5076647 := bstep (se 1 (by rfl) ⟨3807485, by rfl⟩ : syracuseStep 5076647 = 7614971) B7614971
theorem B2856617 : Blo 1503572 2856617 := bstep (se 2 (by rfl) ⟨1071231, by rfl⟩ : syracuseStep 2856617 = 2142463) B2142463
theorem B18298619 : Blo 1503572 18298619 := bstep (se 1 (by rfl) ⟨13723964, by rfl⟩ : syracuseStep 18298619 = 27447929) B27447929
theorem B1505127 : Blo 1503572 1505127 := bstep (se 1 (by rfl) ⟨1128845, by rfl⟩ : syracuseStep 1505127 = 2257691) B2257691
theorem B1505311 : Blo 1503572 1505311 := bstep (se 1 (by rfl) ⟨1128983, by rfl⟩ : syracuseStep 1505311 = 2257967) B2257967
theorem B1505343 : Blo 1503572 1505343 := bstep (se 1 (by rfl) ⟨1129007, by rfl⟩ : syracuseStep 1505343 = 2258015) B2258015
theorem B1505383 : Blo 1503572 1505383 := bstep (se 1 (by rfl) ⟨1129037, by rfl⟩ : syracuseStep 1505383 = 2258075) B2258075
theorem B1505391 : Blo 1503572 1505391 := bstep (se 1 (by rfl) ⟨1129043, by rfl⟩ : syracuseStep 1505391 = 2258087) B2258087
theorem B17373361 : Blo 1503572 17373361 := bstep (se 2 (by rfl) ⟨6515010, by rfl⟩ : syracuseStep 17373361 = 13030021) B13030021
theorem B329611517 : Blo 1503572 329611517 := bstep (se 3 (by rfl) ⟨61802159, by rfl⟩ : syracuseStep 329611517 = 123604319) B123604319
theorem B18299297 : Blo 1503572 18299297 := bstep (se 2 (by rfl) ⟨6862236, by rfl⟩ : syracuseStep 18299297 = 13724473) B13724473
theorem B5077511 : Blo 1503572 5077511 := bstep (se 1 (by rfl) ⟨3808133, by rfl⟩ : syracuseStep 5077511 = 7616267) B7616267
theorem B2857513 : Blo 1503572 2857513 := bstep (se 2 (by rfl) ⟨1071567, by rfl⟩ : syracuseStep 2857513 = 2143135) B2143135
theorem B2538175 : Blo 1503572 2538175 := bstep (se 1 (by rfl) ⟨1903631, by rfl⟩ : syracuseStep 2538175 = 3807263) B3807263
theorem B25697249 : Blo 1503572 25697249 := bstep (se 2 (by rfl) ⟨9636468, by rfl⟩ : syracuseStep 25697249 = 19272937) B19272937
theorem B17128583 : Blo 1503572 17128583 := bstep (se 1 (by rfl) ⟨12846437, by rfl⟩ : syracuseStep 17128583 = 25692875) B25692875
theorem B5078159 : Blo 1503572 5078159 := bstep (se 1 (by rfl) ⟨3808619, by rfl⟩ : syracuseStep 5078159 = 7617239) B7617239
theorem B21691745 : Blo 1503572 21691745 := bstep (se 2 (by rfl) ⟨8134404, by rfl⟩ : syracuseStep 21691745 = 16268809) B16268809
theorem B4283923 : Blo 1503572 4283923 := bstep (se 1 (by rfl) ⟨3212942, by rfl⟩ : syracuseStep 4283923 = 6425885) B6425885
theorem B5078591 : Blo 1503572 5078591 := bstep (se 1 (by rfl) ⟨3808943, by rfl⟩ : syracuseStep 5078591 = 7617887) B7617887
theorem B5709437 : Blo 1503572 5709437 := bstep (se 3 (by rfl) ⟨1070519, by rfl⟩ : syracuseStep 5709437 = 2141039) B2141039
theorem B5709467 : Blo 1503572 5709467 := bstep (se 1 (by rfl) ⟨4282100, by rfl⟩ : syracuseStep 5709467 = 8564201) B8564201
theorem B57868019 : Blo 1503572 57868019 := bstep (se 1 (by rfl) ⟨43401014, by rfl⟩ : syracuseStep 57868019 = 86802029) B86802029
theorem B5709649 : Blo 1503572 5709649 := bstep (se 2 (by rfl) ⟨2141118, by rfl⟩ : syracuseStep 5709649 = 4282237) B4282237
theorem B3612907 : Blo 1503572 3612907 := bstep (se 1 (by rfl) ⟨2709680, by rfl⟩ : syracuseStep 3612907 = 5419361) B5419361
theorem B3383675 : Blo 1503572 3383675 := bstep (se 1 (by rfl) ⟨2537756, by rfl⟩ : syracuseStep 3383675 = 5075513) B5075513
theorem B8569259 : Blo 1503572 8569259 := bstep (se 1 (by rfl) ⟨6426944, by rfl⟩ : syracuseStep 8569259 = 12853889) B12853889
theorem B9642415 : Blo 1503572 9642415 := bstep (se 1 (by rfl) ⟨7231811, by rfl⟩ : syracuseStep 9642415 = 14463623) B14463623
theorem B3383783 : Blo 1503572 3383783 := bstep (se 1 (by rfl) ⟨2537837, by rfl⟩ : syracuseStep 3383783 = 5075675) B5075675
theorem B17613395 : Blo 1503572 17613395 := bstep (se 1 (by rfl) ⟨13210046, by rfl⟩ : syracuseStep 17613395 = 26420093) B26420093
theorem B3810017 : Blo 1503572 3810017 := bstep (se 2 (by rfl) ⟨1428756, by rfl⟩ : syracuseStep 3810017 = 2857513) B2857513
theorem B3384233 : Blo 1503572 3384233 := bstep (se 2 (by rfl) ⟨1269087, by rfl⟩ : syracuseStep 3384233 = 2538175) B2538175
theorem B6267863 : Blo 1503572 6267863 := bstep (se 1 (by rfl) ⟨4700897, by rfl⟩ : syracuseStep 6267863 = 9401795) B9401795
theorem B3384431 : Blo 1503572 3384431 := bstep (se 1 (by rfl) ⟨2538323, by rfl⟩ : syracuseStep 3384431 = 5076647) B5076647
theorem B12199079 : Blo 1503572 12199079 := bstep (se 1 (by rfl) ⟨9149309, by rfl⟩ : syracuseStep 12199079 = 18298619) B18298619
theorem B6424039 : Blo 1503572 6424039 := bstep (se 1 (by rfl) ⟨4818029, by rfl⟩ : syracuseStep 6424039 = 9636059) B9636059
theorem B12199531 : Blo 1503572 12199531 := bstep (se 1 (by rfl) ⟨9149648, by rfl⟩ : syracuseStep 12199531 = 18299297) B18299297
theorem B3385007 : Blo 1503572 3385007 := bstep (se 1 (by rfl) ⟨2538755, by rfl⟩ : syracuseStep 3385007 = 5077511) B5077511
theorem B17131499 : Blo 1503572 17131499 := bstep (se 1 (by rfl) ⟨12848624, by rfl⟩ : syracuseStep 17131499 = 25697249) B25697249
theorem B5711897 : Blo 1503572 5711897 := bstep (se 2 (by rfl) ⟨2141961, by rfl⟩ : syracuseStep 5711897 = 4283923) B4283923
theorem B19286059 : Blo 1503572 19286059 := bstep (se 1 (by rfl) ⟨14464544, by rfl⟩ : syracuseStep 19286059 = 28929089) B28929089
theorem B3385439 : Blo 1503572 3385439 := bstep (se 1 (by rfl) ⟨2539079, by rfl⟩ : syracuseStep 3385439 = 5078159) B5078159
theorem B14461163 : Blo 1503572 14461163 := bstep (se 1 (by rfl) ⟨10845872, by rfl⟩ : syracuseStep 14461163 = 21691745) B21691745
theorem B3385727 : Blo 1503572 3385727 := bstep (se 1 (by rfl) ⟨2539295, by rfl⟩ : syracuseStep 3385727 = 5078591) B5078591
theorem B7612865 : Blo 1503572 7612865 := bstep (se 2 (by rfl) ⟨2854824, by rfl⟩ : syracuseStep 7612865 = 5709649) B5709649
theorem B38578679 : Blo 1503572 38578679 := bstep (se 1 (by rfl) ⟨28934009, by rfl⟩ : syracuseStep 38578679 = 57868019) B57868019
theorem B3213865 : Blo 1503572 3213865 := bstep (se 2 (by rfl) ⟨1205199, by rfl⟩ : syracuseStep 3213865 = 2410399) B2410399
theorem B2255963 : Blo 1503572 2255963 := bstep (se 1 (by rfl) ⟨1691972, by rfl⟩ : syracuseStep 2255963 = 3383945) B3383945
theorem B3386735 : Blo 1503572 3386735 := bstep (se 1 (by rfl) ⟨2540051, by rfl⟩ : syracuseStep 3386735 = 5080103) B5080103
theorem B2256425 : Blo 1503572 2256425 := bstep (se 2 (by rfl) ⟨846159, by rfl⟩ : syracuseStep 2256425 = 1692319) B1692319
theorem B1904411 : Blo 1503572 1904411 := bstep (se 1 (by rfl) ⟨1428308, by rfl⟩ : syracuseStep 1904411 = 2856617) B2856617
theorem B5074811 : Blo 1503572 5074811 := bstep (se 1 (by rfl) ⟨3806108, by rfl⟩ : syracuseStep 5074811 = 7612217) B7612217
theorem B9146513 : Blo 1503572 9146513 := bstep (se 2 (by rfl) ⟨3429942, by rfl⟩ : syracuseStep 9146513 = 6859885) B6859885
theorem B7614647 : Blo 1503572 7614647 := bstep (se 1 (by rfl) ⟨5710985, by rfl⟩ : syracuseStep 7614647 = 11421971) B11421971
theorem B1503711 : Blo 1503572 1503711 := bstep (se 1 (by rfl) ⟨1127783, by rfl⟩ : syracuseStep 1503711 = 2255567) B2255567
theorem B2257463 : Blo 1503572 2257463 := bstep (se 1 (by rfl) ⟨1693097, by rfl⟩ : syracuseStep 2257463 = 3386195) B3386195
theorem B7615133 : Blo 1503572 7615133 := bstep (se 3 (by rfl) ⟨1427837, by rfl⟩ : syracuseStep 7615133 = 2855675) B2855675
theorem B2257703 : Blo 1503572 2257703 := bstep (se 1 (by rfl) ⟨1693277, by rfl⟩ : syracuseStep 2257703 = 3386555) B3386555
theorem B7615295 : Blo 1503572 7615295 := bstep (se 1 (by rfl) ⟨5711471, by rfl⟩ : syracuseStep 7615295 = 11422943) B11422943
theorem B3806291 : Blo 1503572 3806291 := bstep (se 1 (by rfl) ⟨2854718, by rfl⟩ : syracuseStep 3806291 = 5709437) B5709437
theorem B1504347 : Blo 1503572 1504347 := bstep (se 1 (by rfl) ⟨1128260, by rfl⟩ : syracuseStep 1504347 = 2256521) B2256521
theorem B3806311 : Blo 1503572 3806311 := bstep (se 1 (by rfl) ⟨2854733, by rfl⟩ : syracuseStep 3806311 = 5709467) B5709467
theorem B1504383 : Blo 1503572 1504383 := bstep (se 1 (by rfl) ⟨1128287, by rfl⟩ : syracuseStep 1504383 = 2256575) B2256575
theorem B3806585 : Blo 1503572 3806585 := bstep (se 2 (by rfl) ⟨1427469, by rfl⟩ : syracuseStep 3806585 = 2854939) B2854939
theorem B2856313 : Blo 1503572 2856313 := bstep (se 2 (by rfl) ⟨1071117, by rfl⟩ : syracuseStep 2856313 = 2142235) B2142235
theorem B1693183 : Blo 1503572 1693183 := bstep (se 1 (by rfl) ⟨1269887, by rfl⟩ : syracuseStep 1693183 = 2539775) B2539775
theorem B1504795 : Blo 1503572 1504795 := bstep (se 1 (by rfl) ⟨1128596, by rfl⟩ : syracuseStep 1504795 = 2257193) B2257193
theorem B23164481 : Blo 1503572 23164481 := bstep (se 2 (by rfl) ⟨8686680, by rfl⟩ : syracuseStep 23164481 = 17373361) B17373361
theorem B32552765 : Blo 1503572 32552765 := bstep (se 3 (by rfl) ⟨6103643, by rfl⟩ : syracuseStep 32552765 = 12207287) B12207287
theorem B6428585 : Blo 1503572 6428585 := bstep (se 2 (by rfl) ⟨2410719, by rfl⟩ : syracuseStep 6428585 = 4821439) B4821439
theorem B4282283 : Blo 1503572 4282283 := bstep (se 1 (by rfl) ⟨3211712, by rfl⟩ : syracuseStep 4282283 = 6423425) B6423425
theorem B1505407 : Blo 1503572 1505407 := bstep (se 1 (by rfl) ⟨1129055, by rfl⟩ : syracuseStep 1505407 = 2258111) B2258111
theorem B9148871 : Blo 1503572 9148871 := bstep (se 1 (by rfl) ⟨6861653, by rfl⟩ : syracuseStep 9148871 = 13723307) B13723307
theorem B65067623 : Blo 1503572 65067623 := bstep (se 1 (by rfl) ⟨48800717, by rfl⟩ : syracuseStep 65067623 = 97601435) B97601435
theorem B219741011 : Blo 1503572 219741011 := bstep (se 1 (by rfl) ⟨164805758, by rfl⟩ : syracuseStep 219741011 = 329611517) B329611517
theorem B3808235 : Blo 1503572 3808235 := bstep (se 1 (by rfl) ⟨2856176, by rfl⟩ : syracuseStep 3808235 = 5712353) B5712353
theorem B11419055 : Blo 1503572 11419055 := bstep (se 1 (by rfl) ⟨8564291, by rfl⟩ : syracuseStep 11419055 = 17128583) B17128583
theorem B2538985 : Blo 1503572 2538985 := bstep (se 2 (by rfl) ⟨952119, by rfl⟩ : syracuseStep 2538985 = 1904239) B1904239
theorem B4963913 : Blo 1503572 4963913 := bstep (se 2 (by rfl) ⟨1861467, by rfl⟩ : syracuseStep 4963913 = 3722935) B3722935
theorem B9150043 : Blo 1503572 9150043 := bstep (se 1 (by rfl) ⟨6862532, by rfl⟩ : syracuseStep 9150043 = 13725065) B13725065
theorem B7823099 : Blo 1503572 7823099 := bstep (se 1 (by rfl) ⟨5867324, by rfl⟩ : syracuseStep 7823099 = 11734649) B11734649
theorem B18292679 : Blo 1503572 18292679 := bstep (se 1 (by rfl) ⟨13719509, by rfl⟩ : syracuseStep 18292679 = 27439019) B27439019
theorem B25714745 : Blo 1503572 25714745 := bstep (se 2 (by rfl) ⟨9643029, by rfl⟩ : syracuseStep 25714745 = 19286059) B19286059
theorem B2540011 : Blo 1503572 2540011 := bstep (se 1 (by rfl) ⟨1905008, by rfl⟩ : syracuseStep 2540011 = 3810017) B3810017
theorem B4178575 : Blo 1503572 4178575 := bstep (se 1 (by rfl) ⟨3133931, by rfl⟩ : syracuseStep 4178575 = 6267863) B6267863
theorem B4285153 : Blo 1503572 4285153 := bstep (se 2 (by rfl) ⟨1606932, by rfl⟩ : syracuseStep 4285153 = 3213865) B3213865
theorem B15442987 : Blo 1503572 15442987 := bstep (se 1 (by rfl) ⟨11582240, by rfl⟩ : syracuseStep 15442987 = 23164481) B23164481
theorem B21701843 : Blo 1503572 21701843 := bstep (se 1 (by rfl) ⟨16276382, by rfl⟩ : syracuseStep 21701843 = 32552765) B32552765
theorem B19268837 : Blo 1503572 19268837 := bstep (se 4 (by rfl) ⟨1806453, by rfl⟩ : syracuseStep 19268837 = 3612907) B3612907
theorem B4285723 : Blo 1503572 4285723 := bstep (se 1 (by rfl) ⟨3214292, by rfl⟩ : syracuseStep 4285723 = 6428585) B6428585
theorem B11420999 : Blo 1503572 11420999 := bstep (se 1 (by rfl) ⟨8565749, by rfl⟩ : syracuseStep 11420999 = 17131499) B17131499
theorem B43378415 : Blo 1503572 43378415 := bstep (se 1 (by rfl) ⟨32533811, by rfl⟩ : syracuseStep 43378415 = 65067623) B65067623
theorem B3385313 : Blo 1503572 3385313 := bstep (se 2 (by rfl) ⟨1269492, by rfl⟩ : syracuseStep 3385313 = 2538985) B2538985
theorem B12200057 : Blo 1503572 12200057 := bstep (se 2 (by rfl) ⟨4575021, by rfl⟩ : syracuseStep 12200057 = 9150043) B9150043
theorem B7612703 : Blo 1503572 7612703 := bstep (se 1 (by rfl) ⟨5709527, by rfl⟩ : syracuseStep 7612703 = 11419055) B11419055
theorem B6097675 : Blo 1503572 6097675 := bstep (se 1 (by rfl) ⟨4573256, by rfl⟩ : syracuseStep 6097675 = 9146513) B9146513
theorem B2255783 : Blo 1503572 2255783 := bstep (se 1 (by rfl) ⟨1691837, by rfl⟩ : syracuseStep 2255783 = 3383675) B3383675
theorem B5712839 : Blo 1503572 5712839 := bstep (se 1 (by rfl) ⟨4284629, by rfl⟩ : syracuseStep 5712839 = 8569259) B8569259
theorem B2255855 : Blo 1503572 2255855 := bstep (se 1 (by rfl) ⟨1691891, by rfl⟩ : syracuseStep 2255855 = 3383783) B3383783
theorem B11742263 : Blo 1503572 11742263 := bstep (se 1 (by rfl) ⟨8806697, by rfl⟩ : syracuseStep 11742263 = 17613395) B17613395
theorem B12856553 : Blo 1503572 12856553 := bstep (se 2 (by rfl) ⟨4821207, by rfl⟩ : syracuseStep 12856553 = 9642415) B9642415
theorem B2256155 : Blo 1503572 2256155 := bstep (se 1 (by rfl) ⟨1692116, by rfl⟩ : syracuseStep 2256155 = 3384233) B3384233
theorem B2256287 : Blo 1503572 2256287 := bstep (se 1 (by rfl) ⟨1692215, by rfl⟩ : syracuseStep 2256287 = 3384431) B3384431
theorem B2256671 : Blo 1503572 2256671 := bstep (se 1 (by rfl) ⟨1692503, by rfl⟩ : syracuseStep 2256671 = 3385007) B3385007
theorem B2854855 : Blo 1503572 2854855 := bstep (se 1 (by rfl) ⟨2141141, by rfl⟩ : syracuseStep 2854855 = 4282283) B4282283
theorem B2256959 : Blo 1503572 2256959 := bstep (se 1 (by rfl) ⟨1692719, by rfl⟩ : syracuseStep 2256959 = 3385439) B3385439
theorem B5075081 : Blo 1503572 5075081 := bstep (se 2 (by rfl) ⟨1903155, by rfl⟩ : syracuseStep 5075081 = 3806311) B3806311
theorem B2257151 : Blo 1503572 2257151 := bstep (se 1 (by rfl) ⟨1692863, by rfl⟩ : syracuseStep 2257151 = 3385727) B3385727
theorem B5075243 : Blo 1503572 5075243 := bstep (se 1 (by rfl) ⟨3806432, by rfl⟩ : syracuseStep 5075243 = 7612865) B7612865
theorem B6099247 : Blo 1503572 6099247 := bstep (se 1 (by rfl) ⟨4574435, by rfl⟩ : syracuseStep 6099247 = 9148871) B9148871
theorem B25719119 : Blo 1503572 25719119 := bstep (se 1 (by rfl) ⟨19289339, by rfl⟩ : syracuseStep 25719119 = 38578679) B38578679
theorem B146494007 : Blo 1503572 146494007 := bstep (se 1 (by rfl) ⟨109870505, by rfl⟩ : syracuseStep 146494007 = 219741011) B219741011
theorem B8565385 : Blo 1503572 8565385 := bstep (se 2 (by rfl) ⟨3212019, by rfl⟩ : syracuseStep 8565385 = 6424039) B6424039
theorem B20861597 : Blo 1503572 20861597 := bstep (se 3 (by rfl) ⟨3911549, by rfl⟩ : syracuseStep 20861597 = 7823099) B7823099
theorem B2257577 : Blo 1503572 2257577 := bstep (se 2 (by rfl) ⟨846591, by rfl⟩ : syracuseStep 2257577 = 1693183) B1693183
theorem B1503975 : Blo 1503572 1503975 := bstep (se 1 (by rfl) ⟨1127981, by rfl⟩ : syracuseStep 1503975 = 2255963) B2255963
theorem B16266041 : Blo 1503572 16266041 := bstep (se 2 (by rfl) ⟨6099765, by rfl⟩ : syracuseStep 16266041 = 12199531) B12199531
theorem B2257823 : Blo 1503572 2257823 := bstep (se 1 (by rfl) ⟨1693367, by rfl⟩ : syracuseStep 2257823 = 3386735) B3386735
theorem B1504283 : Blo 1503572 1504283 := bstep (se 1 (by rfl) ⟨1128212, by rfl⟩ : syracuseStep 1504283 = 2256425) B2256425
theorem B12195119 : Blo 1503572 12195119 := bstep (se 1 (by rfl) ⟨9146339, by rfl⟩ : syracuseStep 12195119 = 18292679) B18292679
theorem B5076431 : Blo 1503572 5076431 := bstep (se 1 (by rfl) ⟨3807323, by rfl⟩ : syracuseStep 5076431 = 7614647) B7614647
theorem B1504975 : Blo 1503572 1504975 := bstep (se 1 (by rfl) ⟨1128731, by rfl⟩ : syracuseStep 1504975 = 2257463) B2257463
theorem B5076755 : Blo 1503572 5076755 := bstep (se 1 (by rfl) ⟨3807566, by rfl⟩ : syracuseStep 5076755 = 7615133) B7615133
theorem B1505135 : Blo 1503572 1505135 := bstep (se 1 (by rfl) ⟨1128851, by rfl⟩ : syracuseStep 1505135 = 2257703) B2257703
theorem B5076863 : Blo 1503572 5076863 := bstep (se 1 (by rfl) ⟨3807647, by rfl⟩ : syracuseStep 5076863 = 7615295) B7615295
theorem B2537527 : Blo 1503572 2537527 := bstep (se 1 (by rfl) ⟨1903145, by rfl⟩ : syracuseStep 2537527 = 3806291) B3806291
theorem B8132719 : Blo 1503572 8132719 := bstep (se 1 (by rfl) ⟨6099539, by rfl⟩ : syracuseStep 8132719 = 12199079) B12199079
theorem B2537723 : Blo 1503572 2537723 := bstep (se 1 (by rfl) ⟨1903292, by rfl⟩ : syracuseStep 2537723 = 3806585) B3806585
theorem B3807931 : Blo 1503572 3807931 := bstep (se 1 (by rfl) ⟨2855948, by rfl⟩ : syracuseStep 3807931 = 5711897) B5711897
theorem B9640775 : Blo 1503572 9640775 := bstep (se 1 (by rfl) ⟨7230581, by rfl⟩ : syracuseStep 9640775 = 14461163) B14461163
theorem B3808417 : Blo 1503572 3808417 := bstep (se 2 (by rfl) ⟨1428156, by rfl⟩ : syracuseStep 3808417 = 2856313) B2856313
theorem B2538823 : Blo 1503572 2538823 := bstep (se 1 (by rfl) ⟨1904117, by rfl⟩ : syracuseStep 2538823 = 3808235) B3808235
theorem B5078429 : Blo 1503572 5078429 := bstep (se 3 (by rfl) ⟨952205, by rfl⟩ : syracuseStep 5078429 = 1904411) B1904411
theorem B3309275 : Blo 1503572 3309275 := bstep (se 1 (by rfl) ⟨2481956, by rfl⟩ : syracuseStep 3309275 = 4963913) B4963913
theorem B3383207 : Blo 1503572 3383207 := bstep (se 1 (by rfl) ⟨2537405, by rfl⟩ : syracuseStep 3383207 = 5074811) B5074811
theorem B3383369 : Blo 1503572 3383369 := bstep (se 2 (by rfl) ⟨1268763, by rfl⟩ : syracuseStep 3383369 = 2537527) B2537527
theorem B3383387 : Blo 1503572 3383387 := bstep (se 1 (by rfl) ⟨2537540, by rfl⟩ : syracuseStep 3383387 = 5075081) B5075081
theorem B3383495 : Blo 1503572 3383495 := bstep (se 1 (by rfl) ⟨2537621, by rfl⟩ : syracuseStep 3383495 = 5075243) B5075243
theorem B17146079 : Blo 1503572 17146079 := bstep (se 1 (by rfl) ⟨12859559, by rfl⟩ : syracuseStep 17146079 = 25719119) B25719119
theorem B14467895 : Blo 1503572 14467895 := bstep (se 1 (by rfl) ⟨10850921, by rfl⟩ : syracuseStep 14467895 = 21701843) B21701843
theorem B12845891 : Blo 1503572 12845891 := bstep (se 1 (by rfl) ⟨9634418, by rfl⟩ : syracuseStep 12845891 = 19268837) B19268837
theorem B11420513 : Blo 1503572 11420513 := bstep (se 2 (by rfl) ⟨4282692, by rfl⟩ : syracuseStep 11420513 = 8565385) B8565385
theorem B5571433 : Blo 1503572 5571433 := bstep (se 2 (by rfl) ⟨2089287, by rfl⟩ : syracuseStep 5571433 = 4178575) B4178575
theorem B3384287 : Blo 1503572 3384287 := bstep (se 1 (by rfl) ⟨2538215, by rfl⟩ : syracuseStep 3384287 = 5076431) B5076431
theorem B28918943 : Blo 1503572 28918943 := bstep (se 1 (by rfl) ⟨21689207, by rfl⟩ : syracuseStep 28918943 = 43378415) B43378415
theorem B3384503 : Blo 1503572 3384503 := bstep (se 1 (by rfl) ⟨2538377, by rfl⟩ : syracuseStep 3384503 = 5076755) B5076755
theorem B3384575 : Blo 1503572 3384575 := bstep (se 1 (by rfl) ⟨2538431, by rfl⟩ : syracuseStep 3384575 = 5076863) B5076863
theorem B3385097 : Blo 1503572 3385097 := bstep (se 2 (by rfl) ⟨1269411, by rfl⟩ : syracuseStep 3385097 = 2538823) B2538823
theorem B8824733 : Blo 1503572 8824733 := bstep (se 3 (by rfl) ⟨1654637, by rfl⟩ : syracuseStep 8824733 = 3309275) B3309275
theorem B8571035 : Blo 1503572 8571035 := bstep (se 1 (by rfl) ⟨6428276, by rfl⟩ : syracuseStep 8571035 = 12856553) B12856553
theorem B3385619 : Blo 1503572 3385619 := bstep (se 1 (by rfl) ⟨2539214, by rfl⟩ : syracuseStep 3385619 = 5078429) B5078429
theorem B2255471 : Blo 1503572 2255471 := bstep (se 1 (by rfl) ⟨1691603, by rfl⟩ : syracuseStep 2255471 = 3383207) B3383207
theorem B3386681 : Blo 1503572 3386681 := bstep (se 2 (by rfl) ⟨1270005, by rfl⟩ : syracuseStep 3386681 = 2540011) B2540011
theorem B8130079 : Blo 1503572 8130079 := bstep (se 1 (by rfl) ⟨6097559, by rfl⟩ : syracuseStep 8130079 = 12195119) B12195119
theorem B7613999 : Blo 1503572 7613999 := bstep (se 1 (by rfl) ⟨5710499, by rfl⟩ : syracuseStep 7613999 = 11420999) B11420999
theorem B5713537 : Blo 1503572 5713537 := bstep (se 2 (by rfl) ⟨2142576, by rfl⟩ : syracuseStep 5713537 = 4285153) B4285153
theorem B8130233 : Blo 1503572 8130233 := bstep (se 2 (by rfl) ⟨3048837, by rfl⟩ : syracuseStep 8130233 = 6097675) B6097675
theorem B2256875 : Blo 1503572 2256875 := bstep (se 1 (by rfl) ⟨1692656, by rfl⟩ : syracuseStep 2256875 = 3385313) B3385313
theorem B20590649 : Blo 1503572 20590649 := bstep (se 2 (by rfl) ⟨7721493, by rfl⟩ : syracuseStep 20590649 = 15442987) B15442987
theorem B1691815 : Blo 1503572 1691815 := bstep (se 1 (by rfl) ⟨1268861, by rfl⟩ : syracuseStep 1691815 = 2537723) B2537723
theorem B5075135 : Blo 1503572 5075135 := bstep (se 1 (by rfl) ⟨3806351, by rfl⟩ : syracuseStep 5075135 = 7612703) B7612703
theorem B5714297 : Blo 1503572 5714297 := bstep (se 2 (by rfl) ⟨2142861, by rfl⟩ : syracuseStep 5714297 = 4285723) B4285723
theorem B6427183 : Blo 1503572 6427183 := bstep (se 1 (by rfl) ⟨4820387, by rfl⟩ : syracuseStep 6427183 = 9640775) B9640775
theorem B1503855 : Blo 1503572 1503855 := bstep (se 1 (by rfl) ⟨1127891, by rfl⟩ : syracuseStep 1503855 = 2255783) B2255783
theorem B1503903 : Blo 1503572 1503903 := bstep (se 1 (by rfl) ⟨1127927, by rfl⟩ : syracuseStep 1503903 = 2255855) B2255855
theorem B7828175 : Blo 1503572 7828175 := bstep (se 1 (by rfl) ⟨5871131, by rfl⟩ : syracuseStep 7828175 = 11742263) B11742263
theorem B1504103 : Blo 1503572 1504103 := bstep (se 1 (by rfl) ⟨1128077, by rfl⟩ : syracuseStep 1504103 = 2256155) B2256155
theorem B1504191 : Blo 1503572 1504191 := bstep (se 1 (by rfl) ⟨1128143, by rfl⟩ : syracuseStep 1504191 = 2256287) B2256287
theorem B1504447 : Blo 1503572 1504447 := bstep (se 1 (by rfl) ⟨1128335, by rfl⟩ : syracuseStep 1504447 = 2256671) B2256671
theorem B3806473 : Blo 1503572 3806473 := bstep (se 2 (by rfl) ⟨1427427, by rfl⟩ : syracuseStep 3806473 = 2854855) B2854855
theorem B17143163 : Blo 1503572 17143163 := bstep (se 1 (by rfl) ⟨12857372, by rfl⟩ : syracuseStep 17143163 = 25714745) B25714745
theorem B1504639 : Blo 1503572 1504639 := bstep (se 1 (by rfl) ⟨1128479, by rfl⟩ : syracuseStep 1504639 = 2256959) B2256959
theorem B10843625 : Blo 1503572 10843625 := bstep (se 2 (by rfl) ⟨4066359, by rfl⟩ : syracuseStep 10843625 = 8132719) B8132719
theorem B1504767 : Blo 1503572 1504767 := bstep (se 1 (by rfl) ⟨1128575, by rfl⟩ : syracuseStep 1504767 = 2257151) B2257151
theorem B97662671 : Blo 1503572 97662671 := bstep (se 1 (by rfl) ⟨73247003, by rfl⟩ : syracuseStep 97662671 = 146494007) B146494007
theorem B8132329 : Blo 1503572 8132329 := bstep (se 2 (by rfl) ⟨3049623, by rfl⟩ : syracuseStep 8132329 = 6099247) B6099247
theorem B1505051 : Blo 1503572 1505051 := bstep (se 1 (by rfl) ⟨1128788, by rfl⟩ : syracuseStep 1505051 = 2257577) B2257577
theorem B10844027 : Blo 1503572 10844027 := bstep (se 1 (by rfl) ⟨8133020, by rfl⟩ : syracuseStep 10844027 = 16266041) B16266041
theorem B1505215 : Blo 1503572 1505215 := bstep (se 1 (by rfl) ⟨1128911, by rfl⟩ : syracuseStep 1505215 = 2257823) B2257823
theorem B5077241 : Blo 1503572 5077241 := bstep (se 2 (by rfl) ⟨1903965, by rfl⟩ : syracuseStep 5077241 = 3807931) B3807931
theorem B8133371 : Blo 1503572 8133371 := bstep (se 1 (by rfl) ⟨6100028, by rfl⟩ : syracuseStep 8133371 = 12200057) B12200057
theorem B5077889 : Blo 1503572 5077889 := bstep (se 2 (by rfl) ⟨1904208, by rfl⟩ : syracuseStep 5077889 = 3808417) B3808417
theorem B55630925 : Blo 1503572 55630925 := bstep (se 3 (by rfl) ⟨10430798, by rfl⟩ : syracuseStep 55630925 = 20861597) B20861597
theorem B3808559 : Blo 1503572 3808559 := bstep (se 1 (by rfl) ⟨2856419, by rfl⟩ : syracuseStep 3808559 = 5712839) B5712839
theorem B3383423 : Blo 1503572 3383423 := bstep (se 1 (by rfl) ⟨2537567, by rfl⟩ : syracuseStep 3383423 = 5075135) B5075135
theorem B3809531 : Blo 1503572 3809531 := bstep (se 1 (by rfl) ⟨2857148, by rfl⟩ : syracuseStep 3809531 = 5714297) B5714297
theorem B8569577 : Blo 1503572 8569577 := bstep (se 2 (by rfl) ⟨3213591, by rfl⟩ : syracuseStep 8569577 = 6427183) B6427183
theorem B11428775 : Blo 1503572 11428775 := bstep (se 1 (by rfl) ⟨8571581, by rfl⟩ : syracuseStep 11428775 = 17143163) B17143163
theorem B5883155 : Blo 1503572 5883155 := bstep (se 1 (by rfl) ⟨4412366, by rfl⟩ : syracuseStep 5883155 = 8824733) B8824733
theorem B3384827 : Blo 1503572 3384827 := bstep (se 1 (by rfl) ⟨2538620, by rfl⟩ : syracuseStep 3384827 = 5077241) B5077241
theorem B20875133 : Blo 1503572 20875133 := bstep (se 3 (by rfl) ⟨3914087, by rfl⟩ : syracuseStep 20875133 = 7828175) B7828175
theorem B29714309 : Blo 1503572 29714309 := bstep (se 4 (by rfl) ⟨2785716, by rfl⟩ : syracuseStep 29714309 = 5571433) B5571433
theorem B3385259 : Blo 1503572 3385259 := bstep (se 1 (by rfl) ⟨2538944, by rfl⟩ : syracuseStep 3385259 = 5077889) B5077889
theorem B10840105 : Blo 1503572 10840105 := bstep (se 2 (by rfl) ⟨4065039, by rfl⟩ : syracuseStep 10840105 = 8130079) B8130079
theorem B37087283 : Blo 1503572 37087283 := bstep (se 1 (by rfl) ⟨27815462, by rfl⟩ : syracuseStep 37087283 = 55630925) B55630925
theorem B2255579 : Blo 1503572 2255579 := bstep (se 1 (by rfl) ⟨1691684, by rfl⟩ : syracuseStep 2255579 = 3383369) B3383369
theorem B2255591 : Blo 1503572 2255591 := bstep (se 1 (by rfl) ⟨1691693, by rfl⟩ : syracuseStep 2255591 = 3383387) B3383387
theorem B2255663 : Blo 1503572 2255663 := bstep (se 1 (by rfl) ⟨1691747, by rfl⟩ : syracuseStep 2255663 = 3383495) B3383495
theorem B11430719 : Blo 1503572 11430719 := bstep (se 1 (by rfl) ⟨8573039, by rfl⟩ : syracuseStep 11430719 = 17146079) B17146079
theorem B2255753 : Blo 1503572 2255753 := bstep (se 2 (by rfl) ⟨845907, by rfl⟩ : syracuseStep 2255753 = 1691815) B1691815
theorem B9645263 : Blo 1503572 9645263 := bstep (se 1 (by rfl) ⟨7233947, by rfl⟩ : syracuseStep 9645263 = 14467895) B14467895
theorem B8563927 : Blo 1503572 8563927 := bstep (se 1 (by rfl) ⟨6422945, by rfl⟩ : syracuseStep 8563927 = 12845891) B12845891
theorem B7613675 : Blo 1503572 7613675 := bstep (se 1 (by rfl) ⟨5710256, by rfl⟩ : syracuseStep 7613675 = 11420513) B11420513
theorem B2256191 : Blo 1503572 2256191 := bstep (se 1 (by rfl) ⟨1692143, by rfl⟩ : syracuseStep 2256191 = 3384287) B3384287
theorem B19279295 : Blo 1503572 19279295 := bstep (se 1 (by rfl) ⟨14459471, by rfl⟩ : syracuseStep 19279295 = 28918943) B28918943
theorem B2256335 : Blo 1503572 2256335 := bstep (se 1 (by rfl) ⟨1692251, by rfl⟩ : syracuseStep 2256335 = 3384503) B3384503
theorem B2256383 : Blo 1503572 2256383 := bstep (se 1 (by rfl) ⟨1692287, by rfl⟩ : syracuseStep 2256383 = 3384575) B3384575
theorem B7229083 : Blo 1503572 7229083 := bstep (se 1 (by rfl) ⟨5421812, by rfl⟩ : syracuseStep 7229083 = 10843625) B10843625
theorem B2256731 : Blo 1503572 2256731 := bstep (se 1 (by rfl) ⟨1692548, by rfl⟩ : syracuseStep 2256731 = 3385097) B3385097
theorem B7229351 : Blo 1503572 7229351 := bstep (se 1 (by rfl) ⟨5422013, by rfl⟩ : syracuseStep 7229351 = 10844027) B10844027
theorem B5714023 : Blo 1503572 5714023 := bstep (se 1 (by rfl) ⟨4285517, by rfl⟩ : syracuseStep 5714023 = 8571035) B8571035
theorem B2257079 : Blo 1503572 2257079 := bstep (se 1 (by rfl) ⟨1692809, by rfl⟩ : syracuseStep 2257079 = 3385619) B3385619
theorem B5075297 : Blo 1503572 5075297 := bstep (se 2 (by rfl) ⟨1903236, by rfl⟩ : syracuseStep 5075297 = 3806473) B3806473
theorem B1503647 : Blo 1503572 1503647 := bstep (se 1 (by rfl) ⟨1127735, by rfl⟩ : syracuseStep 1503647 = 2255471) B2255471
theorem B21680621 : Blo 1503572 21680621 := bstep (se 3 (by rfl) ⟨4065116, by rfl⟩ : syracuseStep 21680621 = 8130233) B8130233
theorem B2257787 : Blo 1503572 2257787 := bstep (se 1 (by rfl) ⟨1693340, by rfl⟩ : syracuseStep 2257787 = 3386681) B3386681
theorem B10843105 : Blo 1503572 10843105 := bstep (se 2 (by rfl) ⟨4066164, by rfl⟩ : syracuseStep 10843105 = 8132329) B8132329
theorem B5075999 : Blo 1503572 5075999 := bstep (se 1 (by rfl) ⟨3806999, by rfl⟩ : syracuseStep 5075999 = 7613999) B7613999
theorem B1504583 : Blo 1503572 1504583 := bstep (se 1 (by rfl) ⟨1128437, by rfl⟩ : syracuseStep 1504583 = 2256875) B2256875
theorem B13727099 : Blo 1503572 13727099 := bstep (se 1 (by rfl) ⟨10295324, by rfl⟩ : syracuseStep 13727099 = 20590649) B20590649
theorem B65108447 : Blo 1503572 65108447 := bstep (se 1 (by rfl) ⟨48831335, by rfl⟩ : syracuseStep 65108447 = 97662671) B97662671
theorem B5422247 : Blo 1503572 5422247 := bstep (se 1 (by rfl) ⟨4066685, by rfl⟩ : syracuseStep 5422247 = 8133371) B8133371
theorem B7618049 : Blo 1503572 7618049 := bstep (se 2 (by rfl) ⟨2856768, by rfl⟩ : syracuseStep 7618049 = 5713537) B5713537
theorem B2539039 : Blo 1503572 2539039 := bstep (se 1 (by rfl) ⟨1904279, by rfl⟩ : syracuseStep 2539039 = 3808559) B3808559
theorem B7618697 : Blo 1503572 7618697 := bstep (se 2 (by rfl) ⟨2857011, by rfl⟩ : syracuseStep 7618697 = 5714023) B5714023
theorem B2539687 : Blo 1503572 2539687 := bstep (se 1 (by rfl) ⟨1904765, by rfl⟩ : syracuseStep 2539687 = 3809531) B3809531
theorem B3383531 : Blo 1503572 3383531 := bstep (se 1 (by rfl) ⟨2537648, by rfl⟩ : syracuseStep 3383531 = 5075297) B5075297
theorem B7619183 : Blo 1503572 7619183 := bstep (se 1 (by rfl) ⟨5714387, by rfl⟩ : syracuseStep 7619183 = 11428775) B11428775
theorem B3383999 : Blo 1503572 3383999 := bstep (se 1 (by rfl) ⟨2537999, by rfl⟩ : syracuseStep 3383999 = 5075999) B5075999
theorem B9151399 : Blo 1503572 9151399 := bstep (se 1 (by rfl) ⟨6863549, by rfl⟩ : syracuseStep 9151399 = 13727099) B13727099
theorem B19809539 : Blo 1503572 19809539 := bstep (se 1 (by rfl) ⟨14857154, by rfl⟩ : syracuseStep 19809539 = 29714309) B29714309
theorem B24724855 : Blo 1503572 24724855 := bstep (se 1 (by rfl) ⟨18543641, by rfl⟩ : syracuseStep 24724855 = 37087283) B37087283
theorem B7620479 : Blo 1503572 7620479 := bstep (se 1 (by rfl) ⟨5715359, by rfl⟩ : syracuseStep 7620479 = 11430719) B11430719
theorem B3385385 : Blo 1503572 3385385 := bstep (se 2 (by rfl) ⟨1269519, by rfl⟩ : syracuseStep 3385385 = 2539039) B2539039
theorem B3614831 : Blo 1503572 3614831 := bstep (se 1 (by rfl) ⟨2711123, by rfl⟩ : syracuseStep 3614831 = 5422247) B5422247
theorem B19278269 : Blo 1503572 19278269 := bstep (se 3 (by rfl) ⟨3614675, by rfl⟩ : syracuseStep 19278269 = 7229351) B7229351
theorem B14453473 : Blo 1503572 14453473 := bstep (se 2 (by rfl) ⟨5420052, by rfl⟩ : syracuseStep 14453473 = 10840105) B10840105
theorem B2255615 : Blo 1503572 2255615 := bstep (se 1 (by rfl) ⟨1691711, by rfl⟩ : syracuseStep 2255615 = 3383423) B3383423
theorem B14453747 : Blo 1503572 14453747 := bstep (se 1 (by rfl) ⟨10840310, by rfl⟩ : syracuseStep 14453747 = 21680621) B21680621
theorem B5713051 : Blo 1503572 5713051 := bstep (se 1 (by rfl) ⟨4284788, by rfl⟩ : syracuseStep 5713051 = 8569577) B8569577
theorem B2256551 : Blo 1503572 2256551 := bstep (se 1 (by rfl) ⟨1692413, by rfl⟩ : syracuseStep 2256551 = 3384827) B3384827
theorem B2256839 : Blo 1503572 2256839 := bstep (se 1 (by rfl) ⟨1692629, by rfl⟩ : syracuseStep 2256839 = 3385259) B3385259
theorem B43405631 : Blo 1503572 43405631 := bstep (se 1 (by rfl) ⟨32554223, by rfl⟩ : syracuseStep 43405631 = 65108447) B65108447
theorem B1503719 : Blo 1503572 1503719 := bstep (se 1 (by rfl) ⟨1127789, by rfl⟩ : syracuseStep 1503719 = 2255579) B2255579
theorem B1503727 : Blo 1503572 1503727 := bstep (se 1 (by rfl) ⟨1127795, by rfl⟩ : syracuseStep 1503727 = 2255591) B2255591
theorem B1503775 : Blo 1503572 1503775 := bstep (se 1 (by rfl) ⟨1127831, by rfl⟩ : syracuseStep 1503775 = 2255663) B2255663
theorem B1503835 : Blo 1503572 1503835 := bstep (se 1 (by rfl) ⟨1127876, by rfl⟩ : syracuseStep 1503835 = 2255753) B2255753
theorem B5075783 : Blo 1503572 5075783 := bstep (se 1 (by rfl) ⟨3806837, by rfl⟩ : syracuseStep 5075783 = 7613675) B7613675
theorem B9638777 : Blo 1503572 9638777 := bstep (se 2 (by rfl) ⟨3614541, by rfl⟩ : syracuseStep 9638777 = 7229083) B7229083
theorem B1504127 : Blo 1503572 1504127 := bstep (se 1 (by rfl) ⟨1128095, by rfl⟩ : syracuseStep 1504127 = 2256191) B2256191
theorem B1504223 : Blo 1503572 1504223 := bstep (se 1 (by rfl) ⟨1128167, by rfl⟩ : syracuseStep 1504223 = 2256335) B2256335
theorem B1504255 : Blo 1503572 1504255 := bstep (se 1 (by rfl) ⟨1128191, by rfl⟩ : syracuseStep 1504255 = 2256383) B2256383
theorem B1504487 : Blo 1503572 1504487 := bstep (se 1 (by rfl) ⟨1128365, by rfl⟩ : syracuseStep 1504487 = 2256731) B2256731
theorem B1504719 : Blo 1503572 1504719 := bstep (se 1 (by rfl) ⟨1128539, by rfl⟩ : syracuseStep 1504719 = 2257079) B2257079
theorem B1505191 : Blo 1503572 1505191 := bstep (se 1 (by rfl) ⟨1128893, by rfl⟩ : syracuseStep 1505191 = 2257787) B2257787
theorem B3922103 : Blo 1503572 3922103 := bstep (se 1 (by rfl) ⟨2941577, by rfl⟩ : syracuseStep 3922103 = 5883155) B5883155
theorem B13916755 : Blo 1503572 13916755 := bstep (se 1 (by rfl) ⟨10437566, by rfl⟩ : syracuseStep 13916755 = 20875133) B20875133
theorem B14457473 : Blo 1503572 14457473 := bstep (se 2 (by rfl) ⟨5421552, by rfl⟩ : syracuseStep 14457473 = 10843105) B10843105
theorem B11418569 : Blo 1503572 11418569 := bstep (se 2 (by rfl) ⟨4281963, by rfl⟩ : syracuseStep 11418569 = 8563927) B8563927
theorem B6430175 : Blo 1503572 6430175 := bstep (se 1 (by rfl) ⟨4822631, by rfl⟩ : syracuseStep 6430175 = 9645263) B9645263
theorem B12852863 : Blo 1503572 12852863 := bstep (se 1 (by rfl) ⟨9639647, by rfl⟩ : syracuseStep 12852863 = 19279295) B19279295
theorem B5078699 : Blo 1503572 5078699 := bstep (se 1 (by rfl) ⟨3809024, by rfl⟩ : syracuseStep 5078699 = 7618049) B7618049
theorem B5079131 : Blo 1503572 5079131 := bstep (se 1 (by rfl) ⟨3809348, by rfl⟩ : syracuseStep 5079131 = 7618697) B7618697
theorem B5079455 : Blo 1503572 5079455 := bstep (se 1 (by rfl) ⟨3809591, by rfl⟩ : syracuseStep 5079455 = 7619183) B7619183
theorem B3383855 : Blo 1503572 3383855 := bstep (se 1 (by rfl) ⟨2537891, by rfl⟩ : syracuseStep 3383855 = 5075783) B5075783
theorem B18555673 : Blo 1503572 18555673 := bstep (se 2 (by rfl) ⟨6958377, by rfl⟩ : syracuseStep 18555673 = 13916755) B13916755
theorem B13206359 : Blo 1503572 13206359 := bstep (se 1 (by rfl) ⟨9904769, by rfl⟩ : syracuseStep 13206359 = 19809539) B19809539
theorem B5080319 : Blo 1503572 5080319 := bstep (se 1 (by rfl) ⟨3810239, by rfl⟩ : syracuseStep 5080319 = 7620479) B7620479
theorem B2409887 : Blo 1503572 2409887 := bstep (se 1 (by rfl) ⟨1807415, by rfl⟩ : syracuseStep 2409887 = 3614831) B3614831
theorem B2614735 : Blo 1503572 2614735 := bstep (se 1 (by rfl) ⟨1961051, by rfl⟩ : syracuseStep 2614735 = 3922103) B3922103
theorem B32966473 : Blo 1503572 32966473 := bstep (se 2 (by rfl) ⟨12362427, by rfl⟩ : syracuseStep 32966473 = 24724855) B24724855
theorem B7612379 : Blo 1503572 7612379 := bstep (se 1 (by rfl) ⟨5709284, by rfl⟩ : syracuseStep 7612379 = 11418569) B11418569
theorem B9635831 : Blo 1503572 9635831 := bstep (se 1 (by rfl) ⟨7226873, by rfl⟩ : syracuseStep 9635831 = 14453747) B14453747
theorem B4286783 : Blo 1503572 4286783 := bstep (se 1 (by rfl) ⟨3215087, by rfl⟩ : syracuseStep 4286783 = 6430175) B6430175
theorem B3385799 : Blo 1503572 3385799 := bstep (se 1 (by rfl) ⟨2539349, by rfl⟩ : syracuseStep 3385799 = 5078699) B5078699
theorem B2255687 : Blo 1503572 2255687 := bstep (se 1 (by rfl) ⟨1691765, by rfl⟩ : syracuseStep 2255687 = 3383531) B3383531
theorem B28937087 : Blo 1503572 28937087 := bstep (se 1 (by rfl) ⟨21702815, by rfl⟩ : syracuseStep 28937087 = 43405631) B43405631
theorem B3386249 : Blo 1503572 3386249 := bstep (se 2 (by rfl) ⟨1269843, by rfl⟩ : syracuseStep 3386249 = 2539687) B2539687
theorem B2255999 : Blo 1503572 2255999 := bstep (se 1 (by rfl) ⟨1691999, by rfl⟩ : syracuseStep 2255999 = 3383999) B3383999
theorem B6425851 : Blo 1503572 6425851 := bstep (se 1 (by rfl) ⟨4819388, by rfl⟩ : syracuseStep 6425851 = 9638777) B9638777
theorem B19271297 : Blo 1503572 19271297 := bstep (se 2 (by rfl) ⟨7226736, by rfl⟩ : syracuseStep 19271297 = 14453473) B14453473
theorem B2256923 : Blo 1503572 2256923 := bstep (se 1 (by rfl) ⟨1692692, by rfl⟩ : syracuseStep 2256923 = 3385385) B3385385
theorem B9638315 : Blo 1503572 9638315 := bstep (se 1 (by rfl) ⟨7228736, by rfl⟩ : syracuseStep 9638315 = 14457473) B14457473
theorem B1503743 : Blo 1503572 1503743 := bstep (se 1 (by rfl) ⟨1127807, by rfl⟩ : syracuseStep 1503743 = 2255615) B2255615
theorem B1504367 : Blo 1503572 1504367 := bstep (se 1 (by rfl) ⟨1128275, by rfl⟩ : syracuseStep 1504367 = 2256551) B2256551
theorem B1504559 : Blo 1503572 1504559 := bstep (se 1 (by rfl) ⟨1128419, by rfl⟩ : syracuseStep 1504559 = 2256839) B2256839
theorem B7617401 : Blo 1503572 7617401 := bstep (se 2 (by rfl) ⟨2856525, by rfl⟩ : syracuseStep 7617401 = 5713051) B5713051
theorem B12852179 : Blo 1503572 12852179 := bstep (se 1 (by rfl) ⟨9639134, by rfl⟩ : syracuseStep 12852179 = 19278269) B19278269
theorem B48807461 : Blo 1503572 48807461 := bstep (se 4 (by rfl) ⟨4575699, by rfl⟩ : syracuseStep 48807461 = 9151399) B9151399
theorem B8568575 : Blo 1503572 8568575 := bstep (se 1 (by rfl) ⟨6426431, by rfl⟩ : syracuseStep 8568575 = 12852863) B12852863
theorem B1606591 : Blo 1503572 1606591 := bstep (se 1 (by rfl) ⟨1204943, by rfl⟩ : syracuseStep 1606591 = 2409887) B2409887
theorem B24740897 : Blo 1503572 24740897 := bstep (se 2 (by rfl) ⟨9277836, by rfl⟩ : syracuseStep 24740897 = 18555673) B18555673
theorem B6423887 : Blo 1503572 6423887 := bstep (se 1 (by rfl) ⟨4817915, by rfl⟩ : syracuseStep 6423887 = 9635831) B9635831
theorem B12847531 : Blo 1503572 12847531 := bstep (se 1 (by rfl) ⟨9635648, by rfl⟩ : syracuseStep 12847531 = 19271297) B19271297
theorem B5712383 : Blo 1503572 5712383 := bstep (se 1 (by rfl) ⟨4284287, by rfl⟩ : syracuseStep 5712383 = 8568575) B8568575
theorem B3386087 : Blo 1503572 3386087 := bstep (se 1 (by rfl) ⟨2539565, by rfl⟩ : syracuseStep 3386087 = 5079131) B5079131
theorem B3386303 : Blo 1503572 3386303 := bstep (se 1 (by rfl) ⟨2539727, by rfl⟩ : syracuseStep 3386303 = 5079455) B5079455
theorem B6425543 : Blo 1503572 6425543 := bstep (se 1 (by rfl) ⟨4819157, by rfl⟩ : syracuseStep 6425543 = 9638315) B9638315
theorem B2255903 : Blo 1503572 2255903 := bstep (se 1 (by rfl) ⟨1691927, by rfl⟩ : syracuseStep 2255903 = 3383855) B3383855
theorem B3386879 : Blo 1503572 3386879 := bstep (se 1 (by rfl) ⟨2540159, by rfl⟩ : syracuseStep 3386879 = 5080319) B5080319
theorem B5074919 : Blo 1503572 5074919 := bstep (se 1 (by rfl) ⟨3806189, by rfl⟩ : syracuseStep 5074919 = 7612379) B7612379
theorem B2257199 : Blo 1503572 2257199 := bstep (se 1 (by rfl) ⟨1692899, by rfl⟩ : syracuseStep 2257199 = 3385799) B3385799
theorem B1503791 : Blo 1503572 1503791 := bstep (se 1 (by rfl) ⟨1127843, by rfl⟩ : syracuseStep 1503791 = 2255687) B2255687
theorem B2257499 : Blo 1503572 2257499 := bstep (se 1 (by rfl) ⟨1693124, by rfl⟩ : syracuseStep 2257499 = 3386249) B3386249
theorem B3486313 : Blo 1503572 3486313 := bstep (se 2 (by rfl) ⟨1307367, by rfl⟩ : syracuseStep 3486313 = 2614735) B2614735
theorem B1503999 : Blo 1503572 1503999 := bstep (se 1 (by rfl) ⟨1127999, by rfl⟩ : syracuseStep 1503999 = 2255999) B2255999
theorem B43955297 : Blo 1503572 43955297 := bstep (se 2 (by rfl) ⟨16483236, by rfl⟩ : syracuseStep 43955297 = 32966473) B32966473
theorem B1504615 : Blo 1503572 1504615 := bstep (se 1 (by rfl) ⟨1128461, by rfl⟩ : syracuseStep 1504615 = 2256923) B2256923
theorem B2857855 : Blo 1503572 2857855 := bstep (se 1 (by rfl) ⟨2143391, by rfl⟩ : syracuseStep 2857855 = 4286783) B4286783
theorem B8567801 : Blo 1503572 8567801 := bstep (se 2 (by rfl) ⟨3212925, by rfl⟩ : syracuseStep 8567801 = 6425851) B6425851
theorem B5078267 : Blo 1503572 5078267 := bstep (se 1 (by rfl) ⟨3808700, by rfl⟩ : syracuseStep 5078267 = 7617401) B7617401
theorem B19291391 : Blo 1503572 19291391 := bstep (se 1 (by rfl) ⟨14468543, by rfl⟩ : syracuseStep 19291391 = 28937087) B28937087
theorem B8568119 : Blo 1503572 8568119 := bstep (se 1 (by rfl) ⟨6426089, by rfl⟩ : syracuseStep 8568119 = 12852179) B12852179
theorem B35216957 : Blo 1503572 35216957 := bstep (se 3 (by rfl) ⟨6603179, by rfl⟩ : syracuseStep 35216957 = 13206359) B13206359
theorem B32538307 : Blo 1503572 32538307 := bstep (se 1 (by rfl) ⟨24403730, by rfl⟩ : syracuseStep 32538307 = 48807461) B48807461
theorem B17130041 : Blo 1503572 17130041 := bstep (se 2 (by rfl) ⟨6423765, by rfl⟩ : syracuseStep 17130041 = 12847531) B12847531
theorem B29303531 : Blo 1503572 29303531 := bstep (se 1 (by rfl) ⟨21977648, by rfl⟩ : syracuseStep 29303531 = 43955297) B43955297
theorem B3810473 : Blo 1503572 3810473 := bstep (se 2 (by rfl) ⟨1428927, by rfl⟩ : syracuseStep 3810473 = 2857855) B2857855
theorem B5711867 : Blo 1503572 5711867 := bstep (se 1 (by rfl) ⟨4283900, by rfl⟩ : syracuseStep 5711867 = 8567801) B8567801
theorem B3385511 : Blo 1503572 3385511 := bstep (se 1 (by rfl) ⟨2539133, by rfl⟩ : syracuseStep 3385511 = 5078267) B5078267
theorem B5712079 : Blo 1503572 5712079 := bstep (se 1 (by rfl) ⟨4284059, by rfl⟩ : syracuseStep 5712079 = 8568119) B8568119
theorem B4648417 : Blo 1503572 4648417 := bstep (se 2 (by rfl) ⟨1743156, by rfl⟩ : syracuseStep 4648417 = 3486313) B3486313
theorem B2142121 : Blo 1503572 2142121 := bstep (se 2 (by rfl) ⟨803295, by rfl⟩ : syracuseStep 2142121 = 1606591) B1606591
theorem B2257391 : Blo 1503572 2257391 := bstep (se 1 (by rfl) ⟨1693043, by rfl⟩ : syracuseStep 2257391 = 3386087) B3386087
theorem B2257535 : Blo 1503572 2257535 := bstep (se 1 (by rfl) ⟨1693151, by rfl⟩ : syracuseStep 2257535 = 3386303) B3386303
theorem B1503935 : Blo 1503572 1503935 := bstep (se 1 (by rfl) ⟨1127951, by rfl⟩ : syracuseStep 1503935 = 2255903) B2255903
theorem B2257919 : Blo 1503572 2257919 := bstep (se 1 (by rfl) ⟨1693439, by rfl⟩ : syracuseStep 2257919 = 3386879) B3386879
theorem B65975725 : Blo 1503572 65975725 := bstep (se 3 (by rfl) ⟨12370448, by rfl⟩ : syracuseStep 65975725 = 24740897) B24740897
theorem B1504799 : Blo 1503572 1504799 := bstep (se 1 (by rfl) ⟨1128599, by rfl⟩ : syracuseStep 1504799 = 2257199) B2257199
theorem B1504999 : Blo 1503572 1504999 := bstep (se 1 (by rfl) ⟨1128749, by rfl⟩ : syracuseStep 1504999 = 2257499) B2257499
theorem B4282591 : Blo 1503572 4282591 := bstep (se 1 (by rfl) ⟨3211943, by rfl⟩ : syracuseStep 4282591 = 6423887) B6423887
theorem B93911885 : Blo 1503572 93911885 := bstep (se 3 (by rfl) ⟨17608478, by rfl⟩ : syracuseStep 93911885 = 35216957) B35216957
theorem B3808255 : Blo 1503572 3808255 := bstep (se 1 (by rfl) ⟨2856191, by rfl⟩ : syracuseStep 3808255 = 5712383) B5712383
theorem B4283695 : Blo 1503572 4283695 := bstep (se 1 (by rfl) ⟨3212771, by rfl⟩ : syracuseStep 4283695 = 6425543) B6425543
theorem B12860927 : Blo 1503572 12860927 := bstep (se 1 (by rfl) ⟨9645695, by rfl⟩ : syracuseStep 12860927 = 19291391) B19291391
theorem B43384409 : Blo 1503572 43384409 := bstep (se 2 (by rfl) ⟨16269153, by rfl⟩ : syracuseStep 43384409 = 32538307) B32538307
theorem B3383279 : Blo 1503572 3383279 := bstep (se 1 (by rfl) ⟨2537459, by rfl⟩ : syracuseStep 3383279 = 5074919) B5074919
theorem B5710121 : Blo 1503572 5710121 := bstep (se 2 (by rfl) ⟨2141295, by rfl⟩ : syracuseStep 5710121 = 4282591) B4282591
theorem B11420027 : Blo 1503572 11420027 := bstep (se 1 (by rfl) ⟨8565020, by rfl⟩ : syracuseStep 11420027 = 17130041) B17130041
theorem B2540315 : Blo 1503572 2540315 := bstep (se 1 (by rfl) ⟨1905236, by rfl⟩ : syracuseStep 2540315 = 3810473) B3810473
theorem B5711593 : Blo 1503572 5711593 := bstep (se 2 (by rfl) ⟨2141847, by rfl⟩ : syracuseStep 5711593 = 4283695) B4283695
theorem B87967633 : Blo 1503572 87967633 := bstep (se 2 (by rfl) ⟨32987862, by rfl⟩ : syracuseStep 87967633 = 65975725) B65975725
theorem B24791557 : Blo 1503572 24791557 := bstep (se 4 (by rfl) ⟨2324208, by rfl⟩ : syracuseStep 24791557 = 4648417) B4648417
theorem B2255519 : Blo 1503572 2255519 := bstep (se 1 (by rfl) ⟨1691639, by rfl⟩ : syracuseStep 2255519 = 3383279) B3383279
theorem B2257007 : Blo 1503572 2257007 := bstep (se 1 (by rfl) ⟨1692755, by rfl⟩ : syracuseStep 2257007 = 3385511) B3385511
theorem B62607923 : Blo 1503572 62607923 := bstep (se 1 (by rfl) ⟨46955942, by rfl⟩ : syracuseStep 62607923 = 93911885) B93911885
theorem B8573951 : Blo 1503572 8573951 := bstep (se 1 (by rfl) ⟨6430463, by rfl⟩ : syracuseStep 8573951 = 12860927) B12860927
theorem B28922939 : Blo 1503572 28922939 := bstep (se 1 (by rfl) ⟨21692204, by rfl⟩ : syracuseStep 28922939 = 43384409) B43384409
theorem B2856161 : Blo 1503572 2856161 := bstep (se 2 (by rfl) ⟨1071060, by rfl⟩ : syracuseStep 2856161 = 2142121) B2142121
theorem B7616105 : Blo 1503572 7616105 := bstep (se 2 (by rfl) ⟨2856039, by rfl⟩ : syracuseStep 7616105 = 5712079) B5712079
theorem B1504927 : Blo 1503572 1504927 := bstep (se 1 (by rfl) ⟨1128695, by rfl⟩ : syracuseStep 1504927 = 2257391) B2257391
theorem B1505023 : Blo 1503572 1505023 := bstep (se 1 (by rfl) ⟨1128767, by rfl⟩ : syracuseStep 1505023 = 2257535) B2257535
theorem B19535687 : Blo 1503572 19535687 := bstep (se 1 (by rfl) ⟨14651765, by rfl⟩ : syracuseStep 19535687 = 29303531) B29303531
theorem B1505279 : Blo 1503572 1505279 := bstep (se 1 (by rfl) ⟨1128959, by rfl⟩ : syracuseStep 1505279 = 2257919) B2257919
theorem B3807911 : Blo 1503572 3807911 := bstep (se 1 (by rfl) ⟨2855933, by rfl⟩ : syracuseStep 3807911 = 5711867) B5711867
theorem B5077673 : Blo 1503572 5077673 := bstep (se 2 (by rfl) ⟨1904127, by rfl⟩ : syracuseStep 5077673 = 3808255) B3808255
theorem B41738615 : Blo 1503572 41738615 := bstep (se 1 (by rfl) ⟨31303961, by rfl⟩ : syracuseStep 41738615 = 62607923) B62607923
theorem B33055409 : Blo 1503572 33055409 := bstep (se 2 (by rfl) ⟨12395778, by rfl⟩ : syracuseStep 33055409 = 24791557) B24791557
theorem B3385115 : Blo 1503572 3385115 := bstep (se 1 (by rfl) ⟨2538836, by rfl⟩ : syracuseStep 3385115 = 5077673) B5077673
theorem B7613351 : Blo 1503572 7613351 := bstep (se 1 (by rfl) ⟨5710013, by rfl⟩ : syracuseStep 7613351 = 11420027) B11420027
theorem B1503679 : Blo 1503572 1503679 := bstep (se 1 (by rfl) ⟨1127759, by rfl⟩ : syracuseStep 1503679 = 2255519) B2255519
theorem B7615457 : Blo 1503572 7615457 := bstep (se 2 (by rfl) ⟨2855796, by rfl⟩ : syracuseStep 7615457 = 5711593) B5711593
theorem B117290177 : Blo 1503572 117290177 := bstep (se 2 (by rfl) ⟨43983816, by rfl⟩ : syracuseStep 117290177 = 87967633) B87967633
theorem B1504671 : Blo 1503572 1504671 := bstep (se 1 (by rfl) ⟨1128503, by rfl⟩ : syracuseStep 1504671 = 2257007) B2257007
theorem B3806747 : Blo 1503572 3806747 := bstep (se 1 (by rfl) ⟨2855060, by rfl⟩ : syracuseStep 3806747 = 5710121) B5710121
theorem B1693543 : Blo 1503572 1693543 := bstep (se 1 (by rfl) ⟨1270157, by rfl⟩ : syracuseStep 1693543 = 2540315) B2540315
theorem B7616429 : Blo 1503572 7616429 := bstep (se 3 (by rfl) ⟨1428080, by rfl⟩ : syracuseStep 7616429 = 2856161) B2856161
theorem B5715967 : Blo 1503572 5715967 := bstep (se 1 (by rfl) ⟨4286975, by rfl⟩ : syracuseStep 5715967 = 8573951) B8573951
theorem B19281959 : Blo 1503572 19281959 := bstep (se 1 (by rfl) ⟨14461469, by rfl⟩ : syracuseStep 19281959 = 28922939) B28922939
theorem B5077403 : Blo 1503572 5077403 := bstep (se 1 (by rfl) ⟨3808052, by rfl⟩ : syracuseStep 5077403 = 7616105) B7616105
theorem B13023791 : Blo 1503572 13023791 := bstep (se 1 (by rfl) ⟨9767843, by rfl⟩ : syracuseStep 13023791 = 19535687) B19535687
theorem B2538607 : Blo 1503572 2538607 := bstep (se 1 (by rfl) ⟨1903955, by rfl⟩ : syracuseStep 2538607 = 3807911) B3807911
theorem B78193451 : Blo 1503572 78193451 := bstep (se 1 (by rfl) ⟨58645088, by rfl⟩ : syracuseStep 78193451 = 117290177) B117290177
theorem B12854639 : Blo 1503572 12854639 := bstep (se 1 (by rfl) ⟨9640979, by rfl⟩ : syracuseStep 12854639 = 19281959) B19281959
theorem B3384809 : Blo 1503572 3384809 := bstep (se 2 (by rfl) ⟨1269303, by rfl⟩ : syracuseStep 3384809 = 2538607) B2538607
theorem B3384935 : Blo 1503572 3384935 := bstep (se 1 (by rfl) ⟨2538701, by rfl⟩ : syracuseStep 3384935 = 5077403) B5077403
theorem B88147757 : Blo 1503572 88147757 := bstep (se 3 (by rfl) ⟨16527704, by rfl⟩ : syracuseStep 88147757 = 33055409) B33055409
theorem B7621289 : Blo 1503572 7621289 := bstep (se 2 (by rfl) ⟨2857983, by rfl⟩ : syracuseStep 7621289 = 5715967) B5715967
theorem B2256743 : Blo 1503572 2256743 := bstep (se 1 (by rfl) ⟨1692557, by rfl⟩ : syracuseStep 2256743 = 3385115) B3385115
theorem B5075567 : Blo 1503572 5075567 := bstep (se 1 (by rfl) ⟨3806675, by rfl⟩ : syracuseStep 5075567 = 7613351) B7613351
theorem B2258057 : Blo 1503572 2258057 := bstep (se 2 (by rfl) ⟨846771, by rfl⟩ : syracuseStep 2258057 = 1693543) B1693543
theorem B27825743 : Blo 1503572 27825743 := bstep (se 1 (by rfl) ⟨20869307, by rfl⟩ : syracuseStep 27825743 = 41738615) B41738615
theorem B5076971 : Blo 1503572 5076971 := bstep (se 1 (by rfl) ⟨3807728, by rfl⟩ : syracuseStep 5076971 = 7615457) B7615457
theorem B2537831 : Blo 1503572 2537831 := bstep (se 1 (by rfl) ⟨1903373, by rfl⟩ : syracuseStep 2537831 = 3806747) B3806747
theorem B5077619 : Blo 1503572 5077619 := bstep (se 1 (by rfl) ⟨3808214, by rfl⟩ : syracuseStep 5077619 = 7616429) B7616429
theorem B8682527 : Blo 1503572 8682527 := bstep (se 1 (by rfl) ⟨6511895, by rfl⟩ : syracuseStep 8682527 = 13023791) B13023791
theorem B3383711 : Blo 1503572 3383711 := bstep (se 1 (by rfl) ⟨2537783, by rfl⟩ : syracuseStep 3383711 = 5075567) B5075567
theorem B8569759 : Blo 1503572 8569759 := bstep (se 1 (by rfl) ⟨6427319, by rfl⟩ : syracuseStep 8569759 = 12854639) B12854639
theorem B3384647 : Blo 1503572 3384647 := bstep (se 1 (by rfl) ⟨2538485, by rfl⟩ : syracuseStep 3384647 = 5076971) B5076971
theorem B3385079 : Blo 1503572 3385079 := bstep (se 1 (by rfl) ⟨2538809, by rfl⟩ : syracuseStep 3385079 = 5077619) B5077619
theorem B5080859 : Blo 1503572 5080859 := bstep (se 1 (by rfl) ⟨3810644, by rfl⟩ : syracuseStep 5080859 = 7621289) B7621289
theorem B52128967 : Blo 1503572 52128967 := bstep (se 1 (by rfl) ⟨39096725, by rfl⟩ : syracuseStep 52128967 = 78193451) B78193451
theorem B2256539 : Blo 1503572 2256539 := bstep (se 1 (by rfl) ⟨1692404, by rfl⟩ : syracuseStep 2256539 = 3384809) B3384809
theorem B18550495 : Blo 1503572 18550495 := bstep (se 1 (by rfl) ⟨13912871, by rfl⟩ : syracuseStep 18550495 = 27825743) B27825743
theorem B2256623 : Blo 1503572 2256623 := bstep (se 1 (by rfl) ⟨1692467, by rfl⟩ : syracuseStep 2256623 = 3384935) B3384935
theorem B58765171 : Blo 1503572 58765171 := bstep (se 1 (by rfl) ⟨44073878, by rfl⟩ : syracuseStep 58765171 = 88147757) B88147757
theorem B1691887 : Blo 1503572 1691887 := bstep (se 1 (by rfl) ⟨1268915, by rfl⟩ : syracuseStep 1691887 = 2537831) B2537831
theorem B5788351 : Blo 1503572 5788351 := bstep (se 1 (by rfl) ⟨4341263, by rfl⟩ : syracuseStep 5788351 = 8682527) B8682527
theorem B1504495 : Blo 1503572 1504495 := bstep (se 1 (by rfl) ⟨1128371, by rfl⟩ : syracuseStep 1504495 = 2256743) B2256743
theorem B1505371 : Blo 1503572 1505371 := bstep (se 1 (by rfl) ⟨1129028, by rfl⟩ : syracuseStep 1505371 = 2258057) B2258057
theorem B7717801 : Blo 1503572 7717801 := bstep (se 2 (by rfl) ⟨2894175, by rfl⟩ : syracuseStep 7717801 = 5788351) B5788351
theorem B24733993 : Blo 1503572 24733993 := bstep (se 2 (by rfl) ⟨9275247, by rfl⟩ : syracuseStep 24733993 = 18550495) B18550495
theorem B2255807 : Blo 1503572 2255807 := bstep (se 1 (by rfl) ⟨1691855, by rfl⟩ : syracuseStep 2255807 = 3383711) B3383711
theorem B2255849 : Blo 1503572 2255849 := bstep (se 2 (by rfl) ⟨845943, by rfl⟩ : syracuseStep 2255849 = 1691887) B1691887
theorem B2256431 : Blo 1503572 2256431 := bstep (se 1 (by rfl) ⟨1692323, by rfl⟩ : syracuseStep 2256431 = 3384647) B3384647
theorem B2256719 : Blo 1503572 2256719 := bstep (se 1 (by rfl) ⟨1692539, by rfl⟩ : syracuseStep 2256719 = 3385079) B3385079
theorem B3387239 : Blo 1503572 3387239 := bstep (se 1 (by rfl) ⟨2540429, by rfl⟩ : syracuseStep 3387239 = 5080859) B5080859
theorem B69505289 : Blo 1503572 69505289 := bstep (se 2 (by rfl) ⟨26064483, by rfl⟩ : syracuseStep 69505289 = 52128967) B52128967
theorem B1504359 : Blo 1503572 1504359 := bstep (se 1 (by rfl) ⟨1128269, by rfl⟩ : syracuseStep 1504359 = 2256539) B2256539
theorem B78353561 : Blo 1503572 78353561 := bstep (se 2 (by rfl) ⟨29382585, by rfl⟩ : syracuseStep 78353561 = 58765171) B58765171
theorem B1504415 : Blo 1503572 1504415 := bstep (se 1 (by rfl) ⟨1128311, by rfl⟩ : syracuseStep 1504415 = 2256623) B2256623
theorem B11426345 : Blo 1503572 11426345 := bstep (se 2 (by rfl) ⟨4284879, by rfl⟩ : syracuseStep 11426345 = 8569759) B8569759
theorem B10290401 : Blo 1503572 10290401 := bstep (se 2 (by rfl) ⟨3858900, by rfl⟩ : syracuseStep 10290401 = 7717801) B7717801
theorem B46336859 : Blo 1503572 46336859 := bstep (se 1 (by rfl) ⟨34752644, by rfl⟩ : syracuseStep 46336859 = 69505289) B69505289
theorem B52235707 : Blo 1503572 52235707 := bstep (se 1 (by rfl) ⟨39176780, by rfl⟩ : syracuseStep 52235707 = 78353561) B78353561
theorem B1503871 : Blo 1503572 1503871 := bstep (se 1 (by rfl) ⟨1127903, by rfl⟩ : syracuseStep 1503871 = 2255807) B2255807
theorem B1503899 : Blo 1503572 1503899 := bstep (se 1 (by rfl) ⟨1127924, by rfl⟩ : syracuseStep 1503899 = 2255849) B2255849
theorem B1504287 : Blo 1503572 1504287 := bstep (se 1 (by rfl) ⟨1128215, by rfl⟩ : syracuseStep 1504287 = 2256431) B2256431
theorem B1504479 : Blo 1503572 1504479 := bstep (se 1 (by rfl) ⟨1128359, by rfl⟩ : syracuseStep 1504479 = 2256719) B2256719
theorem B2258159 : Blo 1503572 2258159 := bstep (se 1 (by rfl) ⟨1693619, by rfl⟩ : syracuseStep 2258159 = 3387239) B3387239
theorem B32978657 : Blo 1503572 32978657 := bstep (se 2 (by rfl) ⟨12366996, by rfl⟩ : syracuseStep 32978657 = 24733993) B24733993
theorem B7617563 : Blo 1503572 7617563 := bstep (se 1 (by rfl) ⟨5713172, by rfl⟩ : syracuseStep 7617563 = 11426345) B11426345
theorem B6860267 : Blo 1503572 6860267 := bstep (se 1 (by rfl) ⟨5145200, by rfl⟩ : syracuseStep 6860267 = 10290401) B10290401
theorem B1505439 : Blo 1503572 1505439 := bstep (se 1 (by rfl) ⟨1129079, by rfl⟩ : syracuseStep 1505439 = 2258159) B2258159
theorem B21985771 : Blo 1503572 21985771 := bstep (se 1 (by rfl) ⟨16489328, by rfl⟩ : syracuseStep 21985771 = 32978657) B32978657
theorem B30891239 : Blo 1503572 30891239 := bstep (se 1 (by rfl) ⟨23168429, by rfl⟩ : syracuseStep 30891239 = 46336859) B46336859
theorem B69647609 : Blo 1503572 69647609 := bstep (se 2 (by rfl) ⟨26117853, by rfl⟩ : syracuseStep 69647609 = 52235707) B52235707
theorem B5078375 : Blo 1503572 5078375 := bstep (se 1 (by rfl) ⟨3808781, by rfl⟩ : syracuseStep 5078375 = 7617563) B7617563
theorem B3385583 : Blo 1503572 3385583 := bstep (se 1 (by rfl) ⟨2539187, by rfl⟩ : syracuseStep 3385583 = 5078375) B5078375
theorem B4573511 : Blo 1503572 4573511 := bstep (se 1 (by rfl) ⟨3430133, by rfl⟩ : syracuseStep 4573511 = 6860267) B6860267
theorem B29314361 : Blo 1503572 29314361 := bstep (se 2 (by rfl) ⟨10992885, by rfl⟩ : syracuseStep 29314361 = 21985771) B21985771
theorem B20594159 : Blo 1503572 20594159 := bstep (se 1 (by rfl) ⟨15445619, by rfl⟩ : syracuseStep 20594159 = 30891239) B30891239
theorem B46431739 : Blo 1503572 46431739 := bstep (se 1 (by rfl) ⟨34823804, by rfl⟩ : syracuseStep 46431739 = 69647609) B69647609
theorem B3049007 : Blo 1503572 3049007 := bstep (se 1 (by rfl) ⟨2286755, by rfl⟩ : syracuseStep 3049007 = 4573511) B4573511
theorem B61908985 : Blo 1503572 61908985 := bstep (se 2 (by rfl) ⟨23215869, by rfl⟩ : syracuseStep 61908985 = 46431739) B46431739
theorem B2257055 : Blo 1503572 2257055 := bstep (se 1 (by rfl) ⟨1692791, by rfl⟩ : syracuseStep 2257055 = 3385583) B3385583
theorem B19542907 : Blo 1503572 19542907 := bstep (se 1 (by rfl) ⟨14657180, by rfl⟩ : syracuseStep 19542907 = 29314361) B29314361
theorem B13729439 : Blo 1503572 13729439 := bstep (se 1 (by rfl) ⟨10297079, by rfl⟩ : syracuseStep 13729439 = 20594159) B20594159
theorem B32522741 : Blo 1503572 32522741 := bstep (se 5 (by rfl) ⟨1524503, by rfl⟩ : syracuseStep 32522741 = 3049007) B3049007
theorem B9152959 : Blo 1503572 9152959 := bstep (se 1 (by rfl) ⟨6864719, by rfl⟩ : syracuseStep 9152959 = 13729439) B13729439
theorem B82545313 : Blo 1503572 82545313 := bstep (se 2 (by rfl) ⟨30954492, by rfl⟩ : syracuseStep 82545313 = 61908985) B61908985
theorem B1504703 : Blo 1503572 1504703 := bstep (se 1 (by rfl) ⟨1128527, by rfl⟩ : syracuseStep 1504703 = 2257055) B2257055
theorem B26057209 : Blo 1503572 26057209 := bstep (se 2 (by rfl) ⟨9771453, by rfl⟩ : syracuseStep 26057209 = 19542907) B19542907
theorem B34742945 : Blo 1503572 34742945 := bstep (se 2 (by rfl) ⟨13028604, by rfl⟩ : syracuseStep 34742945 = 26057209) B26057209
theorem B110060417 : Blo 1503572 110060417 := bstep (se 2 (by rfl) ⟨41272656, by rfl⟩ : syracuseStep 110060417 = 82545313) B82545313
theorem B21681827 : Blo 1503572 21681827 := bstep (se 1 (by rfl) ⟨16261370, by rfl⟩ : syracuseStep 21681827 = 32522741) B32522741
theorem B12203945 : Blo 1503572 12203945 := bstep (se 2 (by rfl) ⟨4576479, by rfl⟩ : syracuseStep 12203945 = 9152959) B9152959
theorem B8135963 : Blo 1503572 8135963 := bstep (se 1 (by rfl) ⟨6101972, by rfl⟩ : syracuseStep 8135963 = 12203945) B12203945
theorem B23161963 : Blo 1503572 23161963 := bstep (se 1 (by rfl) ⟨17371472, by rfl⟩ : syracuseStep 23161963 = 34742945) B34742945
theorem B14454551 : Blo 1503572 14454551 := bstep (se 1 (by rfl) ⟨10840913, by rfl⟩ : syracuseStep 14454551 = 21681827) B21681827
theorem B73373611 : Blo 1503572 73373611 := bstep (se 1 (by rfl) ⟨55030208, by rfl⟩ : syracuseStep 73373611 = 110060417) B110060417
theorem B5423975 : Blo 1503572 5423975 := bstep (se 1 (by rfl) ⟨4067981, by rfl⟩ : syracuseStep 5423975 = 8135963) B8135963
theorem B9636367 : Blo 1503572 9636367 := bstep (se 1 (by rfl) ⟨7227275, by rfl⟩ : syracuseStep 9636367 = 14454551) B14454551
theorem B97831481 : Blo 1503572 97831481 := bstep (se 2 (by rfl) ⟨36686805, by rfl⟩ : syracuseStep 97831481 = 73373611) B73373611
theorem B30882617 : Blo 1503572 30882617 := bstep (se 2 (by rfl) ⟨11580981, by rfl⟩ : syracuseStep 30882617 = 23161963) B23161963
theorem B20588411 : Blo 1503572 20588411 := bstep (se 1 (by rfl) ⟨15441308, by rfl⟩ : syracuseStep 20588411 = 30882617) B30882617
theorem B3615983 : Blo 1503572 3615983 := bstep (se 1 (by rfl) ⟨2711987, by rfl⟩ : syracuseStep 3615983 = 5423975) B5423975
theorem B12848489 : Blo 1503572 12848489 := bstep (se 2 (by rfl) ⟨4818183, by rfl⟩ : syracuseStep 12848489 = 9636367) B9636367
theorem B1043535797 : Blo 1503572 1043535797 := bstep (se 5 (by rfl) ⟨48915740, by rfl⟩ : syracuseStep 1043535797 = 97831481) B97831481
theorem B695690531 : Blo 1503572 695690531 := bstep (se 1 (by rfl) ⟨521767898, by rfl⟩ : syracuseStep 695690531 = 1043535797) B1043535797
theorem B2410655 : Blo 1503572 2410655 := bstep (se 1 (by rfl) ⟨1807991, by rfl⟩ : syracuseStep 2410655 = 3615983) B3615983
theorem B13725607 : Blo 1503572 13725607 := bstep (se 1 (by rfl) ⟨10294205, by rfl⟩ : syracuseStep 13725607 = 20588411) B20588411
theorem B8565659 : Blo 1503572 8565659 := bstep (se 1 (by rfl) ⟨6424244, by rfl⟩ : syracuseStep 8565659 = 12848489) B12848489
theorem B5710439 : Blo 1503572 5710439 := bstep (se 1 (by rfl) ⟨4282829, by rfl⟩ : syracuseStep 5710439 = 8565659) B8565659
theorem B463793687 : Blo 1503572 463793687 := bstep (se 1 (by rfl) ⟨347845265, by rfl⟩ : syracuseStep 463793687 = 695690531) B695690531
theorem B6428413 : Blo 1503572 6428413 := bstep (se 3 (by rfl) ⟨1205327, by rfl⟩ : syracuseStep 6428413 = 2410655) B2410655
theorem B18300809 : Blo 1503572 18300809 := bstep (se 2 (by rfl) ⟨6862803, by rfl⟩ : syracuseStep 18300809 = 13725607) B13725607
theorem B8571217 : Blo 1503572 8571217 := bstep (se 2 (by rfl) ⟨3214206, by rfl⟩ : syracuseStep 8571217 = 6428413) B6428413
theorem B12200539 : Blo 1503572 12200539 := bstep (se 1 (by rfl) ⟨9150404, by rfl⟩ : syracuseStep 12200539 = 18300809) B18300809
theorem B309195791 : Blo 1503572 309195791 := bstep (se 1 (by rfl) ⟨231896843, by rfl⟩ : syracuseStep 309195791 = 463793687) B463793687
theorem B3806959 : Blo 1503572 3806959 := bstep (se 1 (by rfl) ⟨2855219, by rfl⟩ : syracuseStep 3806959 = 5710439) B5710439
theorem B11428289 : Blo 1503572 11428289 := bstep (se 2 (by rfl) ⟨4285608, by rfl⟩ : syracuseStep 11428289 = 8571217) B8571217
theorem B206130527 : Blo 1503572 206130527 := bstep (se 1 (by rfl) ⟨154597895, by rfl⟩ : syracuseStep 206130527 = 309195791) B309195791
theorem B5075945 : Blo 1503572 5075945 := bstep (se 2 (by rfl) ⟨1903479, by rfl⟩ : syracuseStep 5075945 = 3806959) B3806959
theorem B16267385 : Blo 1503572 16267385 := bstep (se 2 (by rfl) ⟨6100269, by rfl⟩ : syracuseStep 16267385 = 12200539) B12200539
theorem B7618859 : Blo 1503572 7618859 := bstep (se 1 (by rfl) ⟨5714144, by rfl⟩ : syracuseStep 7618859 = 11428289) B11428289
theorem B3383963 : Blo 1503572 3383963 := bstep (se 1 (by rfl) ⟨2537972, by rfl⟩ : syracuseStep 3383963 = 5075945) B5075945
theorem B10844923 : Blo 1503572 10844923 := bstep (se 1 (by rfl) ⟨8133692, by rfl⟩ : syracuseStep 10844923 = 16267385) B16267385
theorem B137420351 : Blo 1503572 137420351 := bstep (se 1 (by rfl) ⟨103065263, by rfl⟩ : syracuseStep 137420351 = 206130527) B206130527
theorem B5079239 : Blo 1503572 5079239 := bstep (se 1 (by rfl) ⟨3809429, by rfl⟩ : syracuseStep 5079239 = 7618859) B7618859
theorem B14459897 : Blo 1503572 14459897 := bstep (se 2 (by rfl) ⟨5422461, by rfl⟩ : syracuseStep 14459897 = 10844923) B10844923
theorem B91613567 : Blo 1503572 91613567 := bstep (se 1 (by rfl) ⟨68710175, by rfl⟩ : syracuseStep 91613567 = 137420351) B137420351
theorem B2255975 : Blo 1503572 2255975 := bstep (se 1 (by rfl) ⟨1691981, by rfl⟩ : syracuseStep 2255975 = 3383963) B3383963
theorem B3386159 : Blo 1503572 3386159 := bstep (se 1 (by rfl) ⟨2539619, by rfl⟩ : syracuseStep 3386159 = 5079239) B5079239
theorem B61075711 : Blo 1503572 61075711 := bstep (se 1 (by rfl) ⟨45806783, by rfl⟩ : syracuseStep 61075711 = 91613567) B91613567
theorem B1503983 : Blo 1503572 1503983 := bstep (se 1 (by rfl) ⟨1127987, by rfl⟩ : syracuseStep 1503983 = 2255975) B2255975
theorem B9639931 : Blo 1503572 9639931 := bstep (se 1 (by rfl) ⟨7229948, by rfl⟩ : syracuseStep 9639931 = 14459897) B14459897
theorem B2257439 : Blo 1503572 2257439 := bstep (se 1 (by rfl) ⟨1693079, by rfl⟩ : syracuseStep 2257439 = 3386159) B3386159
theorem B81434281 : Blo 1503572 81434281 := bstep (se 2 (by rfl) ⟨30537855, by rfl⟩ : syracuseStep 81434281 = 61075711) B61075711
theorem B12853241 : Blo 1503572 12853241 := bstep (se 2 (by rfl) ⟨4819965, by rfl⟩ : syracuseStep 12853241 = 9639931) B9639931
theorem B108579041 : Blo 1503572 108579041 := bstep (se 2 (by rfl) ⟨40717140, by rfl⟩ : syracuseStep 108579041 = 81434281) B81434281
theorem B1504959 : Blo 1503572 1504959 := bstep (se 1 (by rfl) ⟨1128719, by rfl⟩ : syracuseStep 1504959 = 2257439) B2257439
theorem B8568827 : Blo 1503572 8568827 := bstep (se 1 (by rfl) ⟨6426620, by rfl⟩ : syracuseStep 8568827 = 12853241) B12853241
theorem B72386027 : Blo 1503572 72386027 := bstep (se 1 (by rfl) ⟨54289520, by rfl⟩ : syracuseStep 72386027 = 108579041) B108579041
theorem B5712551 : Blo 1503572 5712551 := bstep (se 1 (by rfl) ⟨4284413, by rfl⟩ : syracuseStep 5712551 = 8568827) B8568827
theorem B48257351 : Blo 1503572 48257351 := bstep (se 1 (by rfl) ⟨36193013, by rfl⟩ : syracuseStep 48257351 = 72386027) B72386027
theorem B3808367 : Blo 1503572 3808367 := bstep (se 1 (by rfl) ⟨2856275, by rfl⟩ : syracuseStep 3808367 = 5712551) B5712551
theorem B32171567 : Blo 1503572 32171567 := bstep (se 1 (by rfl) ⟨24128675, by rfl⟩ : syracuseStep 32171567 = 48257351) B48257351
theorem B2538911 : Blo 1503572 2538911 := bstep (se 1 (by rfl) ⟨1904183, by rfl⟩ : syracuseStep 2538911 = 3808367) B3808367
theorem B85790845 : Blo 1503572 85790845 := bstep (se 3 (by rfl) ⟨16085783, by rfl⟩ : syracuseStep 85790845 = 32171567) B32171567
theorem B1692607 : Blo 1503572 1692607 := bstep (se 1 (by rfl) ⟨1269455, by rfl⟩ : syracuseStep 1692607 = 2538911) B2538911
theorem B457551173 : Blo 1503572 457551173 := bstep (se 4 (by rfl) ⟨42895422, by rfl⟩ : syracuseStep 457551173 = 85790845) B85790845
theorem B2256809 : Blo 1503572 2256809 := bstep (se 2 (by rfl) ⟨846303, by rfl⟩ : syracuseStep 2256809 = 1692607) B1692607
theorem B305034115 : Blo 1503572 305034115 := bstep (se 1 (by rfl) ⟨228775586, by rfl⟩ : syracuseStep 305034115 = 457551173) B457551173
theorem B1504539 : Blo 1503572 1504539 := bstep (se 1 (by rfl) ⟨1128404, by rfl⟩ : syracuseStep 1504539 = 2256809) B2256809
theorem B406712153 : Blo 1503572 406712153 := bstep (se 2 (by rfl) ⟨152517057, by rfl⟩ : syracuseStep 406712153 = 305034115) B305034115
theorem B271141435 : Blo 1503572 271141435 := bstep (se 1 (by rfl) ⟨203356076, by rfl⟩ : syracuseStep 271141435 = 406712153) B406712153
theorem B1446087653 : Blo 1503572 1446087653 := bstep (se 4 (by rfl) ⟨135570717, by rfl⟩ : syracuseStep 1446087653 = 271141435) B271141435
theorem B964058435 : Blo 1503572 964058435 := bstep (se 1 (by rfl) ⟨723043826, by rfl⟩ : syracuseStep 964058435 = 1446087653) B1446087653
theorem B642705623 : Blo 1503572 642705623 := bstep (se 1 (by rfl) ⟨482029217, by rfl⟩ : syracuseStep 642705623 = 964058435) B964058435
theorem B428470415 : Blo 1503572 428470415 := bstep (se 1 (by rfl) ⟨321352811, by rfl⟩ : syracuseStep 428470415 = 642705623) B642705623
theorem B285646943 : Blo 1503572 285646943 := bstep (se 1 (by rfl) ⟨214235207, by rfl⟩ : syracuseStep 285646943 = 428470415) B428470415
theorem B761725181 : Blo 1503572 761725181 := bstep (se 3 (by rfl) ⟨142823471, by rfl⟩ : syracuseStep 761725181 = 285646943) B285646943
theorem B507816787 : Blo 1503572 507816787 := bstep (se 1 (by rfl) ⟨380862590, by rfl⟩ : syracuseStep 507816787 = 761725181) B761725181
theorem B677089049 : Blo 1503572 677089049 := bstep (se 2 (by rfl) ⟨253908393, by rfl⟩ : syracuseStep 677089049 = 507816787) B507816787
theorem B1805570797 : Blo 1503572 1805570797 := bstep (se 3 (by rfl) ⟨338544524, by rfl⟩ : syracuseStep 1805570797 = 677089049) B677089049
theorem B2407427729 : Blo 1503572 2407427729 := bstep (se 2 (by rfl) ⟨902785398, by rfl⟩ : syracuseStep 2407427729 = 1805570797) B1805570797
theorem B1604951819 : Blo 1503572 1604951819 := bstep (se 1 (by rfl) ⟨1203713864, by rfl⟩ : syracuseStep 1604951819 = 2407427729) B2407427729
theorem B1069967879 : Blo 1503572 1069967879 := bstep (se 1 (by rfl) ⟨802475909, by rfl⟩ : syracuseStep 1069967879 = 1604951819) B1604951819
theorem B713311919 : Blo 1503572 713311919 := bstep (se 1 (by rfl) ⟨534983939, by rfl⟩ : syracuseStep 713311919 = 1069967879) B1069967879
theorem B475541279 : Blo 1503572 475541279 := bstep (se 1 (by rfl) ⟨356655959, by rfl⟩ : syracuseStep 475541279 = 713311919) B713311919
theorem B317027519 : Blo 1503572 317027519 := bstep (se 1 (by rfl) ⟨237770639, by rfl⟩ : syracuseStep 317027519 = 475541279) B475541279
theorem B211351679 : Blo 1503572 211351679 := bstep (se 1 (by rfl) ⟨158513759, by rfl⟩ : syracuseStep 211351679 = 317027519) B317027519
theorem B140901119 : Blo 1503572 140901119 := bstep (se 1 (by rfl) ⟨105675839, by rfl⟩ : syracuseStep 140901119 = 211351679) B211351679
theorem B93934079 : Blo 1503572 93934079 := bstep (se 1 (by rfl) ⟨70450559, by rfl⟩ : syracuseStep 93934079 = 140901119) B140901119
theorem B62622719 : Blo 1503572 62622719 := bstep (se 1 (by rfl) ⟨46967039, by rfl⟩ : syracuseStep 62622719 = 93934079) B93934079
theorem B41748479 : Blo 1503572 41748479 := bstep (se 1 (by rfl) ⟨31311359, by rfl⟩ : syracuseStep 41748479 = 62622719) B62622719
theorem B27832319 : Blo 1503572 27832319 := bstep (se 1 (by rfl) ⟨20874239, by rfl⟩ : syracuseStep 27832319 = 41748479) B41748479
theorem B18554879 : Blo 1503572 18554879 := bstep (se 1 (by rfl) ⟨13916159, by rfl⟩ : syracuseStep 18554879 = 27832319) B27832319
theorem B12369919 : Blo 1503572 12369919 := bstep (se 1 (by rfl) ⟨9277439, by rfl⟩ : syracuseStep 12369919 = 18554879) B18554879
theorem B16493225 : Blo 1503572 16493225 := bstep (se 2 (by rfl) ⟨6184959, by rfl⟩ : syracuseStep 16493225 = 12369919) B12369919
theorem B175927733 : Blo 1503572 175927733 := bstep (se 5 (by rfl) ⟨8246612, by rfl⟩ : syracuseStep 175927733 = 16493225) B16493225
theorem B117285155 : Blo 1503572 117285155 := bstep (se 1 (by rfl) ⟨87963866, by rfl⟩ : syracuseStep 117285155 = 175927733) B175927733
theorem B78190103 : Blo 1503572 78190103 := bstep (se 1 (by rfl) ⟨58642577, by rfl⟩ : syracuseStep 78190103 = 117285155) B117285155
theorem B52126735 : Blo 1503572 52126735 := bstep (se 1 (by rfl) ⟨39095051, by rfl⟩ : syracuseStep 52126735 = 78190103) B78190103
theorem B69502313 : Blo 1503572 69502313 := bstep (se 2 (by rfl) ⟨26063367, by rfl⟩ : syracuseStep 69502313 = 52126735) B52126735
theorem B46334875 : Blo 1503572 46334875 := bstep (se 1 (by rfl) ⟨34751156, by rfl⟩ : syracuseStep 46334875 = 69502313) B69502313
theorem B61779833 : Blo 1503572 61779833 := bstep (se 2 (by rfl) ⟨23167437, by rfl⟩ : syracuseStep 61779833 = 46334875) B46334875
theorem B41186555 : Blo 1503572 41186555 := bstep (se 1 (by rfl) ⟨30889916, by rfl⟩ : syracuseStep 41186555 = 61779833) B61779833
theorem B27457703 : Blo 1503572 27457703 := bstep (se 1 (by rfl) ⟨20593277, by rfl⟩ : syracuseStep 27457703 = 41186555) B41186555
theorem B18305135 : Blo 1503572 18305135 := bstep (se 1 (by rfl) ⟨13728851, by rfl⟩ : syracuseStep 18305135 = 27457703) B27457703
theorem B12203423 : Blo 1503572 12203423 := bstep (se 1 (by rfl) ⟨9152567, by rfl⟩ : syracuseStep 12203423 = 18305135) B18305135
theorem B8135615 : Blo 1503572 8135615 := bstep (se 1 (by rfl) ⟨6101711, by rfl⟩ : syracuseStep 8135615 = 12203423) B12203423
theorem B5423743 : Blo 1503572 5423743 := bstep (se 1 (by rfl) ⟨4067807, by rfl⟩ : syracuseStep 5423743 = 8135615) B8135615
theorem B28926629 : Blo 1503572 28926629 := bstep (se 4 (by rfl) ⟨2711871, by rfl⟩ : syracuseStep 28926629 = 5423743) B5423743
theorem B19284419 : Blo 1503572 19284419 := bstep (se 1 (by rfl) ⟨14463314, by rfl⟩ : syracuseStep 19284419 = 28926629) B28926629
theorem B12856279 : Blo 1503572 12856279 := bstep (se 1 (by rfl) ⟨9642209, by rfl⟩ : syracuseStep 12856279 = 19284419) B19284419
theorem B17141705 : Blo 1503572 17141705 := bstep (se 2 (by rfl) ⟨6428139, by rfl⟩ : syracuseStep 17141705 = 12856279) B12856279
theorem B11427803 : Blo 1503572 11427803 := bstep (se 1 (by rfl) ⟨8570852, by rfl⟩ : syracuseStep 11427803 = 17141705) B17141705
theorem B7618535 : Blo 1503572 7618535 := bstep (se 1 (by rfl) ⟨5713901, by rfl⟩ : syracuseStep 7618535 = 11427803) B11427803
theorem B5079023 : Blo 1503572 5079023 := bstep (se 1 (by rfl) ⟨3809267, by rfl⟩ : syracuseStep 5079023 = 7618535) B7618535
theorem B3386015 : Blo 1503572 3386015 := bstep (se 1 (by rfl) ⟨2539511, by rfl⟩ : syracuseStep 3386015 = 5079023) B5079023
theorem B2257343 : Blo 1503572 2257343 := bstep (se 1 (by rfl) ⟨1693007, by rfl⟩ : syracuseStep 2257343 = 3386015) B3386015
theorem B1504895 : Blo 1503572 1504895 := bstep (se 1 (by rfl) ⟨1128671, by rfl⟩ : syracuseStep 1504895 = 2257343) B2257343

theorem C0 (j : ℕ) (h1 : 375893 ≤ j) (h2 : j ≤ 376361) : Blo 1503572 (4 * j + 3) := by
  interval_cases j
  · exact B1503575
  · exact B1503579
  · exact B1503583
  · exact B1503587
  · exact B1503591
  · exact B1503595
  · exact B1503599
  · exact B1503603
  · exact B1503607
  · exact B1503611
  · exact B1503615
  · exact B1503619
  · exact B1503623
  · exact B1503627
  · exact B1503631
  · exact B1503635
  · exact B1503639
  · exact B1503643
  · exact B1503647
  · exact B1503651
  · exact B1503655
  · exact B1503659
  · exact B1503663
  · exact B1503667
  · exact B1503671
  · exact B1503675
  · exact B1503679
  · exact B1503683
  · exact B1503687
  · exact B1503691
  · exact B1503695
  · exact B1503699
  · exact B1503703
  · exact B1503707
  · exact B1503711
  · exact B1503715
  · exact B1503719
  · exact B1503723
  · exact B1503727
  · exact B1503731
  · exact B1503735
  · exact B1503739
  · exact B1503743
  · exact B1503747
  · exact B1503751
  · exact B1503755
  · exact B1503759
  · exact B1503763
  · exact B1503767
  · exact B1503771
  · exact B1503775
  · exact B1503779
  · exact B1503783
  · exact B1503787
  · exact B1503791
  · exact B1503795
  · exact B1503799
  · exact B1503803
  · exact B1503807
  · exact B1503811
  · exact B1503815
  · exact B1503819
  · exact B1503823
  · exact B1503827
  · exact B1503831
  · exact B1503835
  · exact B1503839
  · exact B1503843
  · exact B1503847
  · exact B1503851
  · exact B1503855
  · exact B1503859
  · exact B1503863
  · exact B1503867
  · exact B1503871
  · exact B1503875
  · exact B1503879
  · exact B1503883
  · exact B1503887
  · exact B1503891
  · exact B1503895
  · exact B1503899
  · exact B1503903
  · exact B1503907
  · exact B1503911
  · exact B1503915
  · exact B1503919
  · exact B1503923
  · exact B1503927
  · exact B1503931
  · exact B1503935
  · exact B1503939
  · exact B1503943
  · exact B1503947
  · exact B1503951
  · exact B1503955
  · exact B1503959
  · exact B1503963
  · exact B1503967
  · exact B1503971
  · exact B1503975
  · exact B1503979
  · exact B1503983
  · exact B1503987
  · exact B1503991
  · exact B1503995
  · exact B1503999
  · exact B1504003
  · exact B1504007
  · exact B1504011
  · exact B1504015
  · exact B1504019
  · exact B1504023
  · exact B1504027
  · exact B1504031
  · exact B1504035
  · exact B1504039
  · exact B1504043
  · exact B1504047
  · exact B1504051
  · exact B1504055
  · exact B1504059
  · exact B1504063
  · exact B1504067
  · exact B1504071
  · exact B1504075
  · exact B1504079
  · exact B1504083
  · exact B1504087
  · exact B1504091
  · exact B1504095
  · exact B1504099
  · exact B1504103
  · exact B1504107
  · exact B1504111
  · exact B1504115
  · exact B1504119
  · exact B1504123
  · exact B1504127
  · exact B1504131
  · exact B1504135
  · exact B1504139
  · exact B1504143
  · exact B1504147
  · exact B1504151
  · exact B1504155
  · exact B1504159
  · exact B1504163
  · exact B1504167
  · exact B1504171
  · exact B1504175
  · exact B1504179
  · exact B1504183
  · exact B1504187
  · exact B1504191
  · exact B1504195
  · exact B1504199
  · exact B1504203
  · exact B1504207
  · exact B1504211
  · exact B1504215
  · exact B1504219
  · exact B1504223
  · exact B1504227
  · exact B1504231
  · exact B1504235
  · exact B1504239
  · exact B1504243
  · exact B1504247
  · exact B1504251
  · exact B1504255
  · exact B1504259
  · exact B1504263
  · exact B1504267
  · exact B1504271
  · exact B1504275
  · exact B1504279
  · exact B1504283
  · exact B1504287
  · exact B1504291
  · exact B1504295
  · exact B1504299
  · exact B1504303
  · exact B1504307
  · exact B1504311
  · exact B1504315
  · exact B1504319
  · exact B1504323
  · exact B1504327
  · exact B1504331
  · exact B1504335
  · exact B1504339
  · exact B1504343
  · exact B1504347
  · exact B1504351
  · exact B1504355
  · exact B1504359
  · exact B1504363
  · exact B1504367
  · exact B1504371
  · exact B1504375
  · exact B1504379
  · exact B1504383
  · exact B1504387
  · exact B1504391
  · exact B1504395
  · exact B1504399
  · exact B1504403
  · exact B1504407
  · exact B1504411
  · exact B1504415
  · exact B1504419
  · exact B1504423
  · exact B1504427
  · exact B1504431
  · exact B1504435
  · exact B1504439
  · exact B1504443
  · exact B1504447
  · exact B1504451
  · exact B1504455
  · exact B1504459
  · exact B1504463
  · exact B1504467
  · exact B1504471
  · exact B1504475
  · exact B1504479
  · exact B1504483
  · exact B1504487
  · exact B1504491
  · exact B1504495
  · exact B1504499
  · exact B1504503
  · exact B1504507
  · exact B1504511
  · exact B1504515
  · exact B1504519
  · exact B1504523
  · exact B1504527
  · exact B1504531
  · exact B1504535
  · exact B1504539
  · exact B1504543
  · exact B1504547
  · exact B1504551
  · exact B1504555
  · exact B1504559
  · exact B1504563
  · exact B1504567
  · exact B1504571
  · exact B1504575
  · exact B1504579
  · exact B1504583
  · exact B1504587
  · exact B1504591
  · exact B1504595
  · exact B1504599
  · exact B1504603
  · exact B1504607
  · exact B1504611
  · exact B1504615
  · exact B1504619
  · exact B1504623
  · exact B1504627
  · exact B1504631
  · exact B1504635
  · exact B1504639
  · exact B1504643
  · exact B1504647
  · exact B1504651
  · exact B1504655
  · exact B1504659
  · exact B1504663
  · exact B1504667
  · exact B1504671
  · exact B1504675
  · exact B1504679
  · exact B1504683
  · exact B1504687
  · exact B1504691
  · exact B1504695
  · exact B1504699
  · exact B1504703
  · exact B1504707
  · exact B1504711
  · exact B1504715
  · exact B1504719
  · exact B1504723
  · exact B1504727
  · exact B1504731
  · exact B1504735
  · exact B1504739
  · exact B1504743
  · exact B1504747
  · exact B1504751
  · exact B1504755
  · exact B1504759
  · exact B1504763
  · exact B1504767
  · exact B1504771
  · exact B1504775
  · exact B1504779
  · exact B1504783
  · exact B1504787
  · exact B1504791
  · exact B1504795
  · exact B1504799
  · exact B1504803
  · exact B1504807
  · exact B1504811
  · exact B1504815
  · exact B1504819
  · exact B1504823
  · exact B1504827
  · exact B1504831
  · exact B1504835
  · exact B1504839
  · exact B1504843
  · exact B1504847
  · exact B1504851
  · exact B1504855
  · exact B1504859
  · exact B1504863
  · exact B1504867
  · exact B1504871
  · exact B1504875
  · exact B1504879
  · exact B1504883
  · exact B1504887
  · exact B1504891
  · exact B1504895
  · exact B1504899
  · exact B1504903
  · exact B1504907
  · exact B1504911
  · exact B1504915
  · exact B1504919
  · exact B1504923
  · exact B1504927
  · exact B1504931
  · exact B1504935
  · exact B1504939
  · exact B1504943
  · exact B1504947
  · exact B1504951
  · exact B1504955
  · exact B1504959
  · exact B1504963
  · exact B1504967
  · exact B1504971
  · exact B1504975
  · exact B1504979
  · exact B1504983
  · exact B1504987
  · exact B1504991
  · exact B1504995
  · exact B1504999
  · exact B1505003
  · exact B1505007
  · exact B1505011
  · exact B1505015
  · exact B1505019
  · exact B1505023
  · exact B1505027
  · exact B1505031
  · exact B1505035
  · exact B1505039
  · exact B1505043
  · exact B1505047
  · exact B1505051
  · exact B1505055
  · exact B1505059
  · exact B1505063
  · exact B1505067
  · exact B1505071
  · exact B1505075
  · exact B1505079
  · exact B1505083
  · exact B1505087
  · exact B1505091
  · exact B1505095
  · exact B1505099
  · exact B1505103
  · exact B1505107
  · exact B1505111
  · exact B1505115
  · exact B1505119
  · exact B1505123
  · exact B1505127
  · exact B1505131
  · exact B1505135
  · exact B1505139
  · exact B1505143
  · exact B1505147
  · exact B1505151
  · exact B1505155
  · exact B1505159
  · exact B1505163
  · exact B1505167
  · exact B1505171
  · exact B1505175
  · exact B1505179
  · exact B1505183
  · exact B1505187
  · exact B1505191
  · exact B1505195
  · exact B1505199
  · exact B1505203
  · exact B1505207
  · exact B1505211
  · exact B1505215
  · exact B1505219
  · exact B1505223
  · exact B1505227
  · exact B1505231
  · exact B1505235
  · exact B1505239
  · exact B1505243
  · exact B1505247
  · exact B1505251
  · exact B1505255
  · exact B1505259
  · exact B1505263
  · exact B1505267
  · exact B1505271
  · exact B1505275
  · exact B1505279
  · exact B1505283
  · exact B1505287
  · exact B1505291
  · exact B1505295
  · exact B1505299
  · exact B1505303
  · exact B1505307
  · exact B1505311
  · exact B1505315
  · exact B1505319
  · exact B1505323
  · exact B1505327
  · exact B1505331
  · exact B1505335
  · exact B1505339
  · exact B1505343
  · exact B1505347
  · exact B1505351
  · exact B1505355
  · exact B1505359
  · exact B1505363
  · exact B1505367
  · exact B1505371
  · exact B1505375
  · exact B1505379
  · exact B1505383
  · exact B1505387
  · exact B1505391
  · exact B1505395
  · exact B1505399
  · exact B1505403
  · exact B1505407
  · exact B1505411
  · exact B1505415
  · exact B1505419
  · exact B1505423
  · exact B1505427
  · exact B1505431
  · exact B1505435
  · exact B1505439
  · exact B1505443
  · exact B1505447

theorem solution (m : ℕ) (hlo : 1503572 ≤ m) (hhi : m ≤ 1505448) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 375893 ≤ j := by omega
    have hj2 : j ≤ 376361 := by omega
    have hb : Blo 1503572 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
