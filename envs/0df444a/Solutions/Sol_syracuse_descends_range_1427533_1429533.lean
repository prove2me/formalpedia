-- Prove2me | solution 1 for syracuse_descends_range_1427533_1429533
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:41:48.108616+00:00
-- url     : https://prove2.me/submissions/a9d1ec5f-97bc-434c-962e-3366f8f7531b

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


theorem B3964933 : Blo 1427533 3964933 := bbase (se 4 (by rfl) ⟨371712, by rfl⟩ : syracuseStep 3964933 = 743425) (by norm_num)
theorem B3432493 : Blo 1427533 3432493 := bbase (se 3 (by rfl) ⟨643592, by rfl⟩ : syracuseStep 3432493 = 1287185) (by norm_num)
theorem B5791877 : Blo 1427533 5791877 := bbase (se 4 (by rfl) ⟨542988, by rfl⟩ : syracuseStep 5791877 = 1085977) (by norm_num)
theorem B46309589 : Blo 1427533 46309589 := bbase (se 7 (by rfl) ⟨542690, by rfl⟩ : syracuseStep 46309589 = 1085381) (by norm_num)
theorem B2711789 : Blo 1427533 2711789 := bbase (se 3 (by rfl) ⟨508460, by rfl⟩ : syracuseStep 2711789 = 1016921) (by norm_num)
theorem B3432685 : Blo 1427533 3432685 := bbase (se 3 (by rfl) ⟨643628, by rfl⟩ : syracuseStep 3432685 = 1287257) (by norm_num)
theorem B2171141 : Blo 1427533 2171141 := bbase (se 4 (by rfl) ⟨203544, by rfl⟩ : syracuseStep 2171141 = 407089) (by norm_num)
theorem B5423381 : Blo 1427533 5423381 := bbase (se 6 (by rfl) ⟨127110, by rfl⟩ : syracuseStep 5423381 = 254221) (by norm_num)
theorem B3432725 : Blo 1427533 3432725 := bbase (se 6 (by rfl) ⟨80454, by rfl⟩ : syracuseStep 3432725 = 160909) (by norm_num)
theorem B4579669 : Blo 1427533 4579669 := bbase (se 10 (by rfl) ⟨6708, by rfl⟩ : syracuseStep 4579669 = 13417) (by norm_num)
theorem B1606009 : Blo 1427533 1606009 := bbase (se 2 (by rfl) ⟨602253, by rfl⟩ : syracuseStep 1606009 = 1204507) (by norm_num)
theorem B1606045 : Blo 1427533 1606045 := bbase (se 3 (by rfl) ⟨301133, by rfl⟩ : syracuseStep 1606045 = 602267) (by norm_num)
theorem B8135093 : Blo 1427533 8135093 := bbase (se 5 (by rfl) ⟨381332, by rfl⟩ : syracuseStep 8135093 = 762665) (by norm_num)
theorem B1606081 : Blo 1427533 1606081 := bbase (se 2 (by rfl) ⟨602280, by rfl⟩ : syracuseStep 1606081 = 1204561) (by norm_num)
theorem B1606117 : Blo 1427533 1606117 := bbase (se 4 (by rfl) ⟨150573, by rfl⟩ : syracuseStep 1606117 = 301147) (by norm_num)
theorem B1606153 : Blo 1427533 1606153 := bbase (se 2 (by rfl) ⟨602307, by rfl⟩ : syracuseStep 1606153 = 1204615) (by norm_num)
theorem B1606189 : Blo 1427533 1606189 := bbase (se 3 (by rfl) ⟨301160, by rfl⟩ : syracuseStep 1606189 = 602321) (by norm_num)
theorem B5423669 : Blo 1427533 5423669 := bbase (se 5 (by rfl) ⟨254234, by rfl⟩ : syracuseStep 5423669 = 508469) (by norm_num)
theorem B3433013 : Blo 1427533 3433013 := bbase (se 5 (by rfl) ⟨160922, by rfl⟩ : syracuseStep 3433013 = 321845) (by norm_num)
theorem B1606225 : Blo 1427533 1606225 := bbase (se 2 (by rfl) ⟨602334, by rfl⟩ : syracuseStep 1606225 = 1204669) (by norm_num)
theorem B2409061 : Blo 1427533 2409061 := bbase (se 4 (by rfl) ⟨225849, by rfl⟩ : syracuseStep 2409061 = 451699) (by norm_num)
theorem B1606261 : Blo 1427533 1606261 := bbase (se 5 (by rfl) ⟨75293, by rfl⟩ : syracuseStep 1606261 = 150587) (by norm_num)
theorem B1606297 : Blo 1427533 1606297 := bbase (se 2 (by rfl) ⟨602361, by rfl⟩ : syracuseStep 1606297 = 1204723) (by norm_num)
theorem B1983133 : Blo 1427533 1983133 := bbase (se 3 (by rfl) ⟨371837, by rfl⟩ : syracuseStep 1983133 = 743675) (by norm_num)
theorem B2441917 : Blo 1427533 2441917 := bbase (se 3 (by rfl) ⟨457859, by rfl⟩ : syracuseStep 2441917 = 915719) (by norm_num)
theorem B2409149 : Blo 1427533 2409149 := bbase (se 3 (by rfl) ⟨451715, by rfl⟩ : syracuseStep 2409149 = 903431) (by norm_num)
theorem B1606333 : Blo 1427533 1606333 := bbase (se 3 (by rfl) ⟨301187, by rfl⟩ : syracuseStep 1606333 = 602375) (by norm_num)
theorem B3211973 : Blo 1427533 3211973 := bbase (se 4 (by rfl) ⟨301122, by rfl⟩ : syracuseStep 3211973 = 602245) (by norm_num)
theorem B23478997 : Blo 1427533 23478997 := bbase (se 7 (by rfl) ⟨275144, by rfl⟩ : syracuseStep 23478997 = 550289) (by norm_num)
theorem B1606369 : Blo 1427533 1606369 := bbase (se 2 (by rfl) ⟨602388, by rfl⟩ : syracuseStep 1606369 = 1204777) (by norm_num)
theorem B6103781 : Blo 1427533 6103781 := bbase (se 4 (by rfl) ⟨572229, by rfl⟩ : syracuseStep 6103781 = 1144459) (by norm_num)
theorem B1606405 : Blo 1427533 1606405 := bbase (se 4 (by rfl) ⟨150600, by rfl⟩ : syracuseStep 1606405 = 301201) (by norm_num)
theorem B3212045 : Blo 1427533 3212045 := bbase (se 3 (by rfl) ⟨602258, by rfl⟩ : syracuseStep 3212045 = 1204517) (by norm_num)
theorem B1606441 : Blo 1427533 1606441 := bbase (se 2 (by rfl) ⟨602415, by rfl⟩ : syracuseStep 1606441 = 1204831) (by norm_num)
theorem B12362549 : Blo 1427533 12362549 := bbase (se 5 (by rfl) ⟨579494, by rfl⟩ : syracuseStep 12362549 = 1158989) (by norm_num)
theorem B2409277 : Blo 1427533 2409277 := bbase (se 3 (by rfl) ⟨451739, by rfl⟩ : syracuseStep 2409277 = 903479) (by norm_num)
theorem B1606477 : Blo 1427533 1606477 := bbase (se 3 (by rfl) ⟨301214, by rfl⟩ : syracuseStep 1606477 = 602429) (by norm_num)
theorem B3212117 : Blo 1427533 3212117 := bbase (se 9 (by rfl) ⟨9410, by rfl⟩ : syracuseStep 3212117 = 18821) (by norm_num)
theorem B1606513 : Blo 1427533 1606513 := bbase (se 2 (by rfl) ⟨602442, by rfl⟩ : syracuseStep 1606513 = 1204885) (by norm_num)
theorem B2409365 : Blo 1427533 2409365 := bbase (se 6 (by rfl) ⟨56469, by rfl⟩ : syracuseStep 2409365 = 112939) (by norm_num)
theorem B1606549 : Blo 1427533 1606549 := bbase (se 6 (by rfl) ⟨37653, by rfl⟩ : syracuseStep 1606549 = 75307) (by norm_num)
theorem B6865813 : Blo 1427533 6865813 := bbase (se 6 (by rfl) ⟨160917, by rfl⟩ : syracuseStep 6865813 = 321835) (by norm_num)
theorem B3212189 : Blo 1427533 3212189 := bbase (se 3 (by rfl) ⟨602285, by rfl⟩ : syracuseStep 3212189 = 1204571) (by norm_num)
theorem B1606585 : Blo 1427533 1606585 := bbase (se 2 (by rfl) ⟨602469, by rfl⟩ : syracuseStep 1606585 = 1204939) (by norm_num)
theorem B18301909 : Blo 1427533 18301909 := bbase (se 7 (by rfl) ⟨214475, by rfl⟩ : syracuseStep 18301909 = 428951) (by norm_num)
theorem B1606621 : Blo 1427533 1606621 := bbase (se 3 (by rfl) ⟨301241, by rfl⟩ : syracuseStep 1606621 = 602483) (by norm_num)
theorem B2712541 : Blo 1427533 2712541 := bbase (se 3 (by rfl) ⟨508601, by rfl⟩ : syracuseStep 2712541 = 1017203) (by norm_num)
theorem B3212261 : Blo 1427533 3212261 := bbase (se 4 (by rfl) ⟨301149, by rfl⟩ : syracuseStep 3212261 = 602299) (by norm_num)
theorem B3613693 : Blo 1427533 3613693 := bbase (se 3 (by rfl) ⟨677567, by rfl⟩ : syracuseStep 3613693 = 1355135) (by norm_num)
theorem B1606657 : Blo 1427533 1606657 := bbase (se 2 (by rfl) ⟨602496, by rfl⟩ : syracuseStep 1606657 = 1204993) (by norm_num)
theorem B1524749 : Blo 1427533 1524749 := bbase (se 3 (by rfl) ⟨285890, by rfl⟩ : syracuseStep 1524749 = 571781) (by norm_num)
theorem B2409493 : Blo 1427533 2409493 := bbase (se 6 (by rfl) ⟨56472, by rfl⟩ : syracuseStep 2409493 = 112945) (by norm_num)
theorem B1606693 : Blo 1427533 1606693 := bbase (se 4 (by rfl) ⟨150627, by rfl⟩ : syracuseStep 1606693 = 301255) (by norm_num)
theorem B3212333 : Blo 1427533 3212333 := bbase (se 3 (by rfl) ⟨602312, by rfl⟩ : syracuseStep 3212333 = 1204625) (by norm_num)
theorem B1606729 : Blo 1427533 1606729 := bbase (se 2 (by rfl) ⟨602523, by rfl⟩ : syracuseStep 1606729 = 1205047) (by norm_num)
theorem B3613805 : Blo 1427533 3613805 := bbase (se 3 (by rfl) ⟨677588, by rfl⟩ : syracuseStep 3613805 = 1355177) (by norm_num)
theorem B2409581 : Blo 1427533 2409581 := bbase (se 3 (by rfl) ⟨451796, by rfl⟩ : syracuseStep 2409581 = 903593) (by norm_num)
theorem B1606765 : Blo 1427533 1606765 := bbase (se 3 (by rfl) ⟨301268, by rfl⟩ : syracuseStep 1606765 = 602537) (by norm_num)
theorem B2712685 : Blo 1427533 2712685 := bbase (se 3 (by rfl) ⟨508628, by rfl⟩ : syracuseStep 2712685 = 1017257) (by norm_num)
theorem B3212405 : Blo 1427533 3212405 := bbase (se 5 (by rfl) ⟨150581, by rfl⟩ : syracuseStep 3212405 = 301163) (by norm_num)
theorem B1606801 : Blo 1427533 1606801 := bbase (se 2 (by rfl) ⟨602550, by rfl⟩ : syracuseStep 1606801 = 1205101) (by norm_num)
theorem B1606837 : Blo 1427533 1606837 := bbase (se 5 (by rfl) ⟨75320, by rfl⟩ : syracuseStep 1606837 = 150641) (by norm_num)
theorem B3212477 : Blo 1427533 3212477 := bbase (se 3 (by rfl) ⟨602339, by rfl⟩ : syracuseStep 3212477 = 1204679) (by norm_num)
theorem B7234757 : Blo 1427533 7234757 := bbase (se 4 (by rfl) ⟨678258, by rfl⟩ : syracuseStep 7234757 = 1356517) (by norm_num)
theorem B1606873 : Blo 1427533 1606873 := bbase (se 2 (by rfl) ⟨602577, by rfl⟩ : syracuseStep 1606873 = 1205155) (by norm_num)
theorem B3302621 : Blo 1427533 3302621 := bbase (se 3 (by rfl) ⟨619241, by rfl⟩ : syracuseStep 3302621 = 1238483) (by norm_num)
theorem B4818149 : Blo 1427533 4818149 := bbase (se 4 (by rfl) ⟨451701, by rfl⟩ : syracuseStep 4818149 = 903403) (by norm_num)
theorem B2409709 : Blo 1427533 2409709 := bbase (se 3 (by rfl) ⟨451820, by rfl⟩ : syracuseStep 2409709 = 903641) (by norm_num)
theorem B2573549 : Blo 1427533 2573549 := bbase (se 3 (by rfl) ⟨482540, by rfl⟩ : syracuseStep 2573549 = 965081) (by norm_num)
theorem B2032885 : Blo 1427533 2032885 := bbase (se 5 (by rfl) ⟨95291, by rfl⟩ : syracuseStep 2032885 = 190583) (by norm_num)
theorem B2172149 : Blo 1427533 2172149 := bbase (se 5 (by rfl) ⟨101819, by rfl⟩ : syracuseStep 2172149 = 203639) (by norm_num)
theorem B1606909 : Blo 1427533 1606909 := bbase (se 3 (by rfl) ⟨301295, by rfl⟩ : syracuseStep 1606909 = 602591) (by norm_num)
theorem B3212549 : Blo 1427533 3212549 := bbase (se 4 (by rfl) ⟨301176, by rfl⟩ : syracuseStep 3212549 = 602353) (by norm_num)
theorem B1524997 : Blo 1427533 1524997 := bbase (se 4 (by rfl) ⟨142968, by rfl⟩ : syracuseStep 1524997 = 285937) (by norm_num)
theorem B2712845 : Blo 1427533 2712845 := bbase (se 3 (by rfl) ⟨508658, by rfl⟩ : syracuseStep 2712845 = 1017317) (by norm_num)
theorem B1606945 : Blo 1427533 1606945 := bbase (se 2 (by rfl) ⟨602604, by rfl⟩ : syracuseStep 1606945 = 1205209) (by norm_num)
theorem B3613997 : Blo 1427533 3613997 := bbase (se 3 (by rfl) ⟨677624, by rfl⟩ : syracuseStep 3613997 = 1355249) (by norm_num)
theorem B2573621 : Blo 1427533 2573621 := bbase (se 5 (by rfl) ⟨120638, by rfl⟩ : syracuseStep 2573621 = 241277) (by norm_num)
theorem B2409797 : Blo 1427533 2409797 := bbase (se 4 (by rfl) ⟨225918, by rfl⟩ : syracuseStep 2409797 = 451837) (by norm_num)
theorem B1606981 : Blo 1427533 1606981 := bbase (se 4 (by rfl) ⟨150654, by rfl⟩ : syracuseStep 1606981 = 301309) (by norm_num)
theorem B3212621 : Blo 1427533 3212621 := bbase (se 3 (by rfl) ⟨602366, by rfl⟩ : syracuseStep 3212621 = 1204733) (by norm_num)
theorem B296912213 : Blo 1427533 296912213 := bbase (se 12 (by rfl) ⟨108732, by rfl⟩ : syracuseStep 296912213 = 217465) (by norm_num)
theorem B1607017 : Blo 1427533 1607017 := bbase (se 2 (by rfl) ⟨602631, by rfl⟩ : syracuseStep 1607017 = 1205263) (by norm_num)
theorem B1607053 : Blo 1427533 1607053 := bbase (se 3 (by rfl) ⟨301322, by rfl⟩ : syracuseStep 1607053 = 602645) (by norm_num)
theorem B3212693 : Blo 1427533 3212693 := bbase (se 6 (by rfl) ⟨75297, by rfl⟩ : syracuseStep 3212693 = 150595) (by norm_num)
theorem B2712989 : Blo 1427533 2712989 := bbase (se 3 (by rfl) ⟨508685, by rfl⟩ : syracuseStep 2712989 = 1017371) (by norm_num)
theorem B1607089 : Blo 1427533 1607089 := bbase (se 2 (by rfl) ⟨602658, by rfl⟩ : syracuseStep 1607089 = 1205317) (by norm_num)
theorem B2409925 : Blo 1427533 2409925 := bbase (se 4 (by rfl) ⟨225930, by rfl⟩ : syracuseStep 2409925 = 451861) (by norm_num)
theorem B2573765 : Blo 1427533 2573765 := bbase (se 4 (by rfl) ⟨241290, by rfl⟩ : syracuseStep 2573765 = 482581) (by norm_num)
theorem B1607125 : Blo 1427533 1607125 := bbase (se 7 (by rfl) ⟨18833, by rfl⟩ : syracuseStep 1607125 = 37667) (by norm_num)
theorem B3212765 : Blo 1427533 3212765 := bbase (se 3 (by rfl) ⟨602393, by rfl⟩ : syracuseStep 3212765 = 1204787) (by norm_num)
theorem B1607161 : Blo 1427533 1607161 := bbase (se 2 (by rfl) ⟨602685, by rfl⟩ : syracuseStep 1607161 = 1205371) (by norm_num)
theorem B3663389 : Blo 1427533 3663389 := bbase (se 3 (by rfl) ⟨686885, by rfl⟩ : syracuseStep 3663389 = 1373771) (by norm_num)
theorem B2410013 : Blo 1427533 2410013 := bbase (se 3 (by rfl) ⟨451877, by rfl⟩ : syracuseStep 2410013 = 903755) (by norm_num)
theorem B1607197 : Blo 1427533 1607197 := bbase (se 3 (by rfl) ⟨301349, by rfl⟩ : syracuseStep 1607197 = 602699) (by norm_num)
theorem B3212837 : Blo 1427533 3212837 := bbase (se 4 (by rfl) ⟨301203, by rfl⟩ : syracuseStep 3212837 = 602407) (by norm_num)
theorem B1607233 : Blo 1427533 1607233 := bbase (se 2 (by rfl) ⟨602712, by rfl⟩ : syracuseStep 1607233 = 1205425) (by norm_num)
theorem B7226981 : Blo 1427533 7226981 := bbase (se 4 (by rfl) ⟨677529, by rfl⟩ : syracuseStep 7226981 = 1355059) (by norm_num)
theorem B1607269 : Blo 1427533 1607269 := bbase (se 4 (by rfl) ⟨150681, by rfl⟩ : syracuseStep 1607269 = 301363) (by norm_num)
theorem B3212909 : Blo 1427533 3212909 := bbase (se 3 (by rfl) ⟨602420, by rfl⟩ : syracuseStep 3212909 = 1204841) (by norm_num)
theorem B3614341 : Blo 1427533 3614341 := bbase (se 4 (by rfl) ⟨338844, by rfl⟩ : syracuseStep 3614341 = 677689) (by norm_num)
theorem B1607305 : Blo 1427533 1607305 := bbase (se 2 (by rfl) ⟨602739, by rfl⟩ : syracuseStep 1607305 = 1205479) (by norm_num)
theorem B4818581 : Blo 1427533 4818581 := bbase (se 6 (by rfl) ⟨112935, by rfl⟩ : syracuseStep 4818581 = 225871) (by norm_num)
theorem B2287253 : Blo 1427533 2287253 := bbase (se 6 (by rfl) ⟨53607, by rfl⟩ : syracuseStep 2287253 = 107215) (by norm_num)
theorem B2410141 : Blo 1427533 2410141 := bbase (se 3 (by rfl) ⟨451901, by rfl⟩ : syracuseStep 2410141 = 903803) (by norm_num)
theorem B1607341 : Blo 1427533 1607341 := bbase (se 3 (by rfl) ⟨301376, by rfl⟩ : syracuseStep 1607341 = 602753) (by norm_num)
theorem B3212981 : Blo 1427533 3212981 := bbase (se 5 (by rfl) ⟨150608, by rfl⟩ : syracuseStep 3212981 = 301217) (by norm_num)
theorem B1525429 : Blo 1427533 1525429 := bbase (se 5 (by rfl) ⟨71504, by rfl⟩ : syracuseStep 1525429 = 143009) (by norm_num)
theorem B2713277 : Blo 1427533 2713277 := bbase (se 3 (by rfl) ⟨508739, by rfl⟩ : syracuseStep 2713277 = 1017479) (by norm_num)
theorem B3049157 : Blo 1427533 3049157 := bbase (se 4 (by rfl) ⟨285858, by rfl⟩ : syracuseStep 3049157 = 571717) (by norm_num)
theorem B1607377 : Blo 1427533 1607377 := bbase (se 2 (by rfl) ⟨602766, by rfl⟩ : syracuseStep 1607377 = 1205533) (by norm_num)
theorem B5424853 : Blo 1427533 5424853 := bbase (se 7 (by rfl) ⟨63572, by rfl⟩ : syracuseStep 5424853 = 127145) (by norm_num)
theorem B1787617 : Blo 1427533 1787617 := bbase (se 2 (by rfl) ⟨670356, by rfl⟩ : syracuseStep 1787617 = 1340713) (by norm_num)
theorem B3614453 : Blo 1427533 3614453 := bbase (se 5 (by rfl) ⟨169427, by rfl⟩ : syracuseStep 3614453 = 338855) (by norm_num)
theorem B2410229 : Blo 1427533 2410229 := bbase (se 5 (by rfl) ⟨112979, by rfl⟩ : syracuseStep 2410229 = 225959) (by norm_num)
theorem B1607413 : Blo 1427533 1607413 := bbase (se 5 (by rfl) ⟨75347, by rfl⟩ : syracuseStep 1607413 = 150695) (by norm_num)
theorem B3213053 : Blo 1427533 3213053 := bbase (se 3 (by rfl) ⟨602447, by rfl⟩ : syracuseStep 3213053 = 1204895) (by norm_num)
theorem B1525501 : Blo 1427533 1525501 := bbase (se 3 (by rfl) ⟨286031, by rfl⟩ : syracuseStep 1525501 = 572063) (by norm_num)
theorem B1607449 : Blo 1427533 1607449 := bbase (se 2 (by rfl) ⟨602793, by rfl⟩ : syracuseStep 1607449 = 1205587) (by norm_num)
theorem B1607485 : Blo 1427533 1607485 := bbase (se 3 (by rfl) ⟨301403, by rfl⟩ : syracuseStep 1607485 = 602807) (by norm_num)
theorem B3213125 : Blo 1427533 3213125 := bbase (se 4 (by rfl) ⟨301230, by rfl⟩ : syracuseStep 3213125 = 602461) (by norm_num)
theorem B2713429 : Blo 1427533 2713429 := bbase (se 9 (by rfl) ⟨7949, by rfl⟩ : syracuseStep 2713429 = 15899) (by norm_num)
theorem B1607521 : Blo 1427533 1607521 := bbase (se 2 (by rfl) ⟨602820, by rfl⟩ : syracuseStep 1607521 = 1205641) (by norm_num)
theorem B2287477 : Blo 1427533 2287477 := bbase (se 5 (by rfl) ⟨107225, by rfl⟩ : syracuseStep 2287477 = 214451) (by norm_num)
theorem B2410357 : Blo 1427533 2410357 := bbase (se 5 (by rfl) ⟨112985, by rfl⟩ : syracuseStep 2410357 = 225971) (by norm_num)
theorem B1607557 : Blo 1427533 1607557 := bbase (se 4 (by rfl) ⟨150708, by rfl⟩ : syracuseStep 1607557 = 301417) (by norm_num)
theorem B3213197 : Blo 1427533 3213197 := bbase (se 3 (by rfl) ⟨602474, by rfl⟩ : syracuseStep 3213197 = 1204949) (by norm_num)
theorem B1607593 : Blo 1427533 1607593 := bbase (se 2 (by rfl) ⟨602847, by rfl⟩ : syracuseStep 1607593 = 1205695) (by norm_num)
theorem B3614645 : Blo 1427533 3614645 := bbase (se 5 (by rfl) ⟨169436, by rfl⟩ : syracuseStep 3614645 = 338873) (by norm_num)
theorem B2410445 : Blo 1427533 2410445 := bbase (se 3 (by rfl) ⟨451958, by rfl⟩ : syracuseStep 2410445 = 903917) (by norm_num)
theorem B1607629 : Blo 1427533 1607629 := bbase (se 3 (by rfl) ⟨301430, by rfl⟩ : syracuseStep 1607629 = 602861) (by norm_num)
theorem B3213269 : Blo 1427533 3213269 := bbase (se 7 (by rfl) ⟨37655, by rfl⟩ : syracuseStep 3213269 = 75311) (by norm_num)
theorem B1607665 : Blo 1427533 1607665 := bbase (se 2 (by rfl) ⟨602874, by rfl⟩ : syracuseStep 1607665 = 1205749) (by norm_num)
theorem B5425157 : Blo 1427533 5425157 := bbase (se 4 (by rfl) ⟨508608, by rfl⟩ : syracuseStep 5425157 = 1017217) (by norm_num)
theorem B2033677 : Blo 1427533 2033677 := bbase (se 3 (by rfl) ⟨381314, by rfl⟩ : syracuseStep 2033677 = 762629) (by norm_num)
theorem B1607701 : Blo 1427533 1607701 := bbase (se 6 (by rfl) ⟨37680, by rfl⟩ : syracuseStep 1607701 = 75361) (by norm_num)
theorem B3213341 : Blo 1427533 3213341 := bbase (se 3 (by rfl) ⟨602501, by rfl⟩ : syracuseStep 3213341 = 1205003) (by norm_num)
theorem B2443301 : Blo 1427533 2443301 := bbase (se 4 (by rfl) ⟨229059, by rfl⟩ : syracuseStep 2443301 = 458119) (by norm_num)
theorem B4343861 : Blo 1427533 4343861 := bbase (se 5 (by rfl) ⟨203618, by rfl⟩ : syracuseStep 4343861 = 407237) (by norm_num)
theorem B1607737 : Blo 1427533 1607737 := bbase (se 2 (by rfl) ⟨602901, by rfl⟩ : syracuseStep 1607737 = 1205803) (by norm_num)
theorem B4065349 : Blo 1427533 4065349 := bbase (se 4 (by rfl) ⟨381126, by rfl⟩ : syracuseStep 4065349 = 762253) (by norm_num)
theorem B4819013 : Blo 1427533 4819013 := bbase (se 4 (by rfl) ⟨451782, by rfl⟩ : syracuseStep 4819013 = 903565) (by norm_num)
theorem B2410573 : Blo 1427533 2410573 := bbase (se 3 (by rfl) ⟨451982, by rfl⟩ : syracuseStep 2410573 = 903965) (by norm_num)
theorem B1607773 : Blo 1427533 1607773 := bbase (se 3 (by rfl) ⟨301457, by rfl⟩ : syracuseStep 1607773 = 602915) (by norm_num)
theorem B3213413 : Blo 1427533 3213413 := bbase (se 4 (by rfl) ⟨301257, by rfl⟩ : syracuseStep 3213413 = 602515) (by norm_num)
theorem B1525873 : Blo 1427533 1525873 := bbase (se 2 (by rfl) ⟨572202, by rfl⟩ : syracuseStep 1525873 = 1144405) (by norm_num)
theorem B1607809 : Blo 1427533 1607809 := bbase (se 2 (by rfl) ⟨602928, by rfl⟩ : syracuseStep 1607809 = 1205857) (by norm_num)
theorem B2713733 : Blo 1427533 2713733 := bbase (se 4 (by rfl) ⟨254412, by rfl⟩ : syracuseStep 2713733 = 508825) (by norm_num)
theorem B2410661 : Blo 1427533 2410661 := bbase (se 4 (by rfl) ⟨225999, by rfl⟩ : syracuseStep 2410661 = 451999) (by norm_num)
theorem B1607845 : Blo 1427533 1607845 := bbase (se 4 (by rfl) ⟨150735, by rfl⟩ : syracuseStep 1607845 = 301471) (by norm_num)
theorem B3213485 : Blo 1427533 3213485 := bbase (se 3 (by rfl) ⟨602528, by rfl⟩ : syracuseStep 3213485 = 1205057) (by norm_num)
theorem B1607881 : Blo 1427533 1607881 := bbase (se 2 (by rfl) ⟨602955, by rfl⟩ : syracuseStep 1607881 = 1205911) (by norm_num)
theorem B1607917 : Blo 1427533 1607917 := bbase (se 3 (by rfl) ⟨301484, by rfl⟩ : syracuseStep 1607917 = 602969) (by norm_num)
theorem B3213557 : Blo 1427533 3213557 := bbase (se 5 (by rfl) ⟨150635, by rfl⟩ : syracuseStep 3213557 = 301271) (by norm_num)
theorem B3614989 : Blo 1427533 3614989 := bbase (se 3 (by rfl) ⟨677810, by rfl⟩ : syracuseStep 3614989 = 1355621) (by norm_num)
theorem B1607953 : Blo 1427533 1607953 := bbase (se 2 (by rfl) ⟨602982, by rfl⟩ : syracuseStep 1607953 = 1205965) (by norm_num)
theorem B2410789 : Blo 1427533 2410789 := bbase (se 4 (by rfl) ⟨226011, by rfl⟩ : syracuseStep 2410789 = 452023) (by norm_num)
theorem B5794085 : Blo 1427533 5794085 := bbase (se 4 (by rfl) ⟨543195, by rfl⟩ : syracuseStep 5794085 = 1086391) (by norm_num)
theorem B1607989 : Blo 1427533 1607989 := bbase (se 5 (by rfl) ⟨75374, by rfl⟩ : syracuseStep 1607989 = 150749) (by norm_num)
theorem B3213629 : Blo 1427533 3213629 := bbase (se 3 (by rfl) ⟨602555, by rfl⟩ : syracuseStep 3213629 = 1205111) (by norm_num)
theorem B1608025 : Blo 1427533 1608025 := bbase (se 2 (by rfl) ⟨603009, by rfl⟩ : syracuseStep 1608025 = 1206019) (by norm_num)
theorem B2034013 : Blo 1427533 2034013 := bbase (se 3 (by rfl) ⟨381377, by rfl⟩ : syracuseStep 2034013 = 762755) (by norm_num)
theorem B3615101 : Blo 1427533 3615101 := bbase (se 3 (by rfl) ⟨677831, by rfl⟩ : syracuseStep 3615101 = 1355663) (by norm_num)
theorem B2410877 : Blo 1427533 2410877 := bbase (se 3 (by rfl) ⟨452039, by rfl⟩ : syracuseStep 2410877 = 904079) (by norm_num)
theorem B1608061 : Blo 1427533 1608061 := bbase (se 3 (by rfl) ⟨301511, by rfl⟩ : syracuseStep 1608061 = 603023) (by norm_num)
theorem B3213701 : Blo 1427533 3213701 := bbase (se 4 (by rfl) ⟨301284, by rfl⟩ : syracuseStep 3213701 = 602569) (by norm_num)
theorem B1608097 : Blo 1427533 1608097 := bbase (se 2 (by rfl) ⟨603036, by rfl⟩ : syracuseStep 1608097 = 1206073) (by norm_num)
theorem B1608133 : Blo 1427533 1608133 := bbase (se 4 (by rfl) ⟨150762, by rfl⟩ : syracuseStep 1608133 = 301525) (by norm_num)
theorem B3213773 : Blo 1427533 3213773 := bbase (se 3 (by rfl) ⟨602582, by rfl⟩ : syracuseStep 3213773 = 1205165) (by norm_num)
theorem B7236053 : Blo 1427533 7236053 := bbase (se 7 (by rfl) ⟨84797, by rfl⟩ : syracuseStep 7236053 = 169595) (by norm_num)
theorem B6105557 : Blo 1427533 6105557 := bbase (se 7 (by rfl) ⟨71549, by rfl⟩ : syracuseStep 6105557 = 143099) (by norm_num)
theorem B1526249 : Blo 1427533 1526249 := bbase (se 2 (by rfl) ⟨572343, by rfl⟩ : syracuseStep 1526249 = 1144687) (by norm_num)
theorem B1608169 : Blo 1427533 1608169 := bbase (se 2 (by rfl) ⟨603063, by rfl⟩ : syracuseStep 1608169 = 1206127) (by norm_num)
theorem B4573685 : Blo 1427533 4573685 := bbase (se 5 (by rfl) ⟨214391, by rfl⟩ : syracuseStep 4573685 = 428783) (by norm_num)
theorem B4819445 : Blo 1427533 4819445 := bbase (se 5 (by rfl) ⟨225911, by rfl⟩ : syracuseStep 4819445 = 451823) (by norm_num)
theorem B2411005 : Blo 1427533 2411005 := bbase (se 3 (by rfl) ⟨452063, by rfl⟩ : syracuseStep 2411005 = 904127) (by norm_num)
theorem B1608205 : Blo 1427533 1608205 := bbase (se 3 (by rfl) ⟨301538, by rfl⟩ : syracuseStep 1608205 = 603077) (by norm_num)
theorem B3213845 : Blo 1427533 3213845 := bbase (se 6 (by rfl) ⟨75324, by rfl⟩ : syracuseStep 3213845 = 150649) (by norm_num)
theorem B2034229 : Blo 1427533 2034229 := bbase (se 5 (by rfl) ⟨95354, by rfl⟩ : syracuseStep 2034229 = 190709) (by norm_num)
theorem B1526321 : Blo 1427533 1526321 := bbase (se 2 (by rfl) ⟨572370, by rfl⟩ : syracuseStep 1526321 = 1144741) (by norm_num)
theorem B3615293 : Blo 1427533 3615293 := bbase (se 3 (by rfl) ⟨677867, by rfl⟩ : syracuseStep 3615293 = 1355735) (by norm_num)
theorem B2411093 : Blo 1427533 2411093 := bbase (se 8 (by rfl) ⟨14127, by rfl⟩ : syracuseStep 2411093 = 28255) (by norm_num)
theorem B3213917 : Blo 1427533 3213917 := bbase (se 3 (by rfl) ⟨602609, by rfl⟩ : syracuseStep 3213917 = 1205219) (by norm_num)
theorem B3213989 : Blo 1427533 3213989 := bbase (se 4 (by rfl) ⟨301311, by rfl⟩ : syracuseStep 3213989 = 602623) (by norm_num)
theorem B2411221 : Blo 1427533 2411221 := bbase (se 7 (by rfl) ⟨28256, by rfl⟩ : syracuseStep 2411221 = 56513) (by norm_num)
theorem B3214061 : Blo 1427533 3214061 := bbase (se 3 (by rfl) ⟨602636, by rfl⟩ : syracuseStep 3214061 = 1205273) (by norm_num)
theorem B1526509 : Blo 1427533 1526509 := bbase (se 3 (by rfl) ⟨286220, by rfl⟩ : syracuseStep 1526509 = 572441) (by norm_num)
theorem B4639493 : Blo 1427533 4639493 := bbase (se 4 (by rfl) ⟨434952, by rfl⟩ : syracuseStep 4639493 = 869905) (by norm_num)
theorem B2411309 : Blo 1427533 2411309 := bbase (se 3 (by rfl) ⟨452120, by rfl⟩ : syracuseStep 2411309 = 904241) (by norm_num)
theorem B3214133 : Blo 1427533 3214133 := bbase (se 5 (by rfl) ⟨150662, by rfl⟩ : syracuseStep 3214133 = 301325) (by norm_num)
theorem B7228277 : Blo 1427533 7228277 := bbase (se 5 (by rfl) ⟨338825, by rfl⟩ : syracuseStep 7228277 = 677651) (by norm_num)
theorem B3214205 : Blo 1427533 3214205 := bbase (se 3 (by rfl) ⟨602663, by rfl⟩ : syracuseStep 3214205 = 1205327) (by norm_num)
theorem B3615637 : Blo 1427533 3615637 := bbase (se 6 (by rfl) ⟨84741, by rfl⟩ : syracuseStep 3615637 = 169483) (by norm_num)
theorem B4819877 : Blo 1427533 4819877 := bbase (se 4 (by rfl) ⟨451863, by rfl⟩ : syracuseStep 4819877 = 903727) (by norm_num)
theorem B2034605 : Blo 1427533 2034605 := bbase (se 3 (by rfl) ⟨381488, by rfl⟩ : syracuseStep 2034605 = 762977) (by norm_num)
theorem B2411437 : Blo 1427533 2411437 := bbase (se 3 (by rfl) ⟨452144, by rfl⟩ : syracuseStep 2411437 = 904289) (by norm_num)
theorem B3214277 : Blo 1427533 3214277 := bbase (se 4 (by rfl) ⟨301338, by rfl⟩ : syracuseStep 3214277 = 602677) (by norm_num)
theorem B1715161 : Blo 1427533 1715161 := bbase (se 2 (by rfl) ⟨643185, by rfl⟩ : syracuseStep 1715161 = 1286371) (by norm_num)
theorem B1715185 : Blo 1427533 1715185 := bbase (se 2 (by rfl) ⟨643194, by rfl⟩ : syracuseStep 1715185 = 1286389) (by norm_num)
theorem B1715189 : Blo 1427533 1715189 := bbase (se 5 (by rfl) ⟨80399, by rfl⟩ : syracuseStep 1715189 = 160799) (by norm_num)
theorem B3615749 : Blo 1427533 3615749 := bbase (se 4 (by rfl) ⟨338976, by rfl⟩ : syracuseStep 3615749 = 677953) (by norm_num)
theorem B2411525 : Blo 1427533 2411525 := bbase (se 4 (by rfl) ⟨226080, by rfl⟩ : syracuseStep 2411525 = 452161) (by norm_num)
theorem B3214349 : Blo 1427533 3214349 := bbase (se 3 (by rfl) ⟨602690, by rfl⟩ : syracuseStep 3214349 = 1205381) (by norm_num)
theorem B2894869 : Blo 1427533 2894869 := bbase (se 6 (by rfl) ⟨67848, by rfl⟩ : syracuseStep 2894869 = 135697) (by norm_num)
theorem B3214421 : Blo 1427533 3214421 := bbase (se 8 (by rfl) ⟨18834, by rfl⟩ : syracuseStep 3214421 = 37669) (by norm_num)
theorem B2141309 : Blo 1427533 2141309 := bbase (se 3 (by rfl) ⟨401495, by rfl⟩ : syracuseStep 2141309 = 802991) (by norm_num)
theorem B2411653 : Blo 1427533 2411653 := bbase (se 4 (by rfl) ⟨226092, by rfl⟩ : syracuseStep 2411653 = 452185) (by norm_num)
theorem B2141333 : Blo 1427533 2141333 := bbase (se 6 (by rfl) ⟨50187, by rfl⟩ : syracuseStep 2141333 = 100375) (by norm_num)
theorem B4066453 : Blo 1427533 4066453 := bbase (se 6 (by rfl) ⟨95307, by rfl⟩ : syracuseStep 4066453 = 190615) (by norm_num)
theorem B3214493 : Blo 1427533 3214493 := bbase (se 3 (by rfl) ⟨602717, by rfl⟩ : syracuseStep 3214493 = 1205435) (by norm_num)
theorem B2141357 : Blo 1427533 2141357 := bbase (se 3 (by rfl) ⟨401504, by rfl⟩ : syracuseStep 2141357 = 803009) (by norm_num)
theorem B2141381 : Blo 1427533 2141381 := bbase (se 4 (by rfl) ⟨200754, by rfl⟩ : syracuseStep 2141381 = 401509) (by norm_num)
theorem B3615941 : Blo 1427533 3615941 := bbase (se 4 (by rfl) ⟨338994, by rfl⟩ : syracuseStep 3615941 = 677989) (by norm_num)
theorem B2141405 : Blo 1427533 2141405 := bbase (se 3 (by rfl) ⟨401513, by rfl⟩ : syracuseStep 2141405 = 803027) (by norm_num)
theorem B2411741 : Blo 1427533 2411741 := bbase (se 3 (by rfl) ⟨452201, by rfl⟩ : syracuseStep 2411741 = 904403) (by norm_num)
theorem B3214565 : Blo 1427533 3214565 := bbase (se 4 (by rfl) ⟨301365, by rfl⟩ : syracuseStep 3214565 = 602731) (by norm_num)
theorem B2141429 : Blo 1427533 2141429 := bbase (se 5 (by rfl) ⟨100379, by rfl⟩ : syracuseStep 2141429 = 200759) (by norm_num)
theorem B2288893 : Blo 1427533 2288893 := bbase (se 3 (by rfl) ⟨429167, by rfl⟩ : syracuseStep 2288893 = 858335) (by norm_num)
theorem B2141453 : Blo 1427533 2141453 := bbase (se 3 (by rfl) ⟨401522, by rfl⟩ : syracuseStep 2141453 = 803045) (by norm_num)
theorem B2141477 : Blo 1427533 2141477 := bbase (se 4 (by rfl) ⟨200763, by rfl⟩ : syracuseStep 2141477 = 401527) (by norm_num)
theorem B3050797 : Blo 1427533 3050797 := bbase (se 3 (by rfl) ⟨572024, by rfl⟩ : syracuseStep 3050797 = 1144049) (by norm_num)
theorem B3214637 : Blo 1427533 3214637 := bbase (se 3 (by rfl) ⟨602744, by rfl⟩ : syracuseStep 3214637 = 1205489) (by norm_num)
theorem B2141501 : Blo 1427533 2141501 := bbase (se 3 (by rfl) ⟨401531, by rfl⟩ : syracuseStep 2141501 = 803063) (by norm_num)
theorem B2141525 : Blo 1427533 2141525 := bbase (se 11 (by rfl) ⟨1568, by rfl⟩ : syracuseStep 2141525 = 3137) (by norm_num)
theorem B4820309 : Blo 1427533 4820309 := bbase (se 11 (by rfl) ⟨3530, by rfl⟩ : syracuseStep 4820309 = 7061) (by norm_num)
theorem B2411869 : Blo 1427533 2411869 := bbase (se 3 (by rfl) ⟨452225, by rfl⟩ : syracuseStep 2411869 = 904451) (by norm_num)
theorem B2141549 : Blo 1427533 2141549 := bbase (se 3 (by rfl) ⟨401540, by rfl⟩ : syracuseStep 2141549 = 803081) (by norm_num)
theorem B3214709 : Blo 1427533 3214709 := bbase (se 5 (by rfl) ⟨150689, by rfl⟩ : syracuseStep 3214709 = 301379) (by norm_num)
theorem B2141573 : Blo 1427533 2141573 := bbase (se 4 (by rfl) ⟨200772, by rfl⟩ : syracuseStep 2141573 = 401545) (by norm_num)
theorem B2141597 : Blo 1427533 2141597 := bbase (se 3 (by rfl) ⟨401549, by rfl⟩ : syracuseStep 2141597 = 803099) (by norm_num)
theorem B2141621 : Blo 1427533 2141621 := bbase (se 5 (by rfl) ⟨100388, by rfl⟩ : syracuseStep 2141621 = 200777) (by norm_num)
theorem B2411957 : Blo 1427533 2411957 := bbase (se 5 (by rfl) ⟨113060, by rfl⟩ : syracuseStep 2411957 = 226121) (by norm_num)
theorem B3214781 : Blo 1427533 3214781 := bbase (se 3 (by rfl) ⟨602771, by rfl⟩ : syracuseStep 3214781 = 1205543) (by norm_num)
theorem B2141645 : Blo 1427533 2141645 := bbase (se 3 (by rfl) ⟨401558, by rfl⟩ : syracuseStep 2141645 = 803117) (by norm_num)
theorem B2141669 : Blo 1427533 2141669 := bbase (se 4 (by rfl) ⟨200781, by rfl⟩ : syracuseStep 2141669 = 401563) (by norm_num)
theorem B1715689 : Blo 1427533 1715689 := bbase (se 2 (by rfl) ⟨643383, by rfl⟩ : syracuseStep 1715689 = 1286767) (by norm_num)
theorem B2141693 : Blo 1427533 2141693 := bbase (se 3 (by rfl) ⟨401567, by rfl⟩ : syracuseStep 2141693 = 803135) (by norm_num)
theorem B2289149 : Blo 1427533 2289149 := bbase (se 3 (by rfl) ⟨429215, by rfl⟩ : syracuseStep 2289149 = 858431) (by norm_num)
theorem B3214853 : Blo 1427533 3214853 := bbase (se 4 (by rfl) ⟨301392, by rfl⟩ : syracuseStep 3214853 = 602785) (by norm_num)
theorem B2141717 : Blo 1427533 2141717 := bbase (se 6 (by rfl) ⟨50196, by rfl⟩ : syracuseStep 2141717 = 100393) (by norm_num)
theorem B3616285 : Blo 1427533 3616285 := bbase (se 3 (by rfl) ⟨678053, by rfl⟩ : syracuseStep 3616285 = 1356107) (by norm_num)
theorem B2141741 : Blo 1427533 2141741 := bbase (se 3 (by rfl) ⟨401576, by rfl⟩ : syracuseStep 2141741 = 803153) (by norm_num)
theorem B2412085 : Blo 1427533 2412085 := bbase (se 5 (by rfl) ⟨113066, by rfl⟩ : syracuseStep 2412085 = 226133) (by norm_num)
theorem B2141765 : Blo 1427533 2141765 := bbase (se 4 (by rfl) ⟨200790, by rfl⟩ : syracuseStep 2141765 = 401581) (by norm_num)
theorem B1715785 : Blo 1427533 1715785 := bbase (se 2 (by rfl) ⟨643419, by rfl⟩ : syracuseStep 1715785 = 1286839) (by norm_num)
theorem B3214925 : Blo 1427533 3214925 := bbase (se 3 (by rfl) ⟨602798, by rfl⟩ : syracuseStep 3214925 = 1205597) (by norm_num)
theorem B2141789 : Blo 1427533 2141789 := bbase (se 3 (by rfl) ⟨401585, by rfl⟩ : syracuseStep 2141789 = 803171) (by norm_num)
theorem B3862117 : Blo 1427533 3862117 := bbase (se 4 (by rfl) ⟨362073, by rfl⟩ : syracuseStep 3862117 = 724147) (by norm_num)
theorem B2141813 : Blo 1427533 2141813 := bbase (se 5 (by rfl) ⟨100397, by rfl⟩ : syracuseStep 2141813 = 200795) (by norm_num)
theorem B2141837 : Blo 1427533 2141837 := bbase (se 3 (by rfl) ⟨401594, by rfl⟩ : syracuseStep 2141837 = 803189) (by norm_num)
theorem B3616397 : Blo 1427533 3616397 := bbase (se 3 (by rfl) ⟨678074, by rfl⟩ : syracuseStep 3616397 = 1356149) (by norm_num)
theorem B2412173 : Blo 1427533 2412173 := bbase (se 3 (by rfl) ⟨452282, by rfl⟩ : syracuseStep 2412173 = 904565) (by norm_num)
theorem B17370773 : Blo 1427533 17370773 := bbase (se 6 (by rfl) ⟨407127, by rfl⟩ : syracuseStep 17370773 = 814255) (by norm_num)
theorem B3214997 : Blo 1427533 3214997 := bbase (se 6 (by rfl) ⟨75351, by rfl⟩ : syracuseStep 3214997 = 150703) (by norm_num)
theorem B2141861 : Blo 1427533 2141861 := bbase (se 4 (by rfl) ⟨200799, by rfl⟩ : syracuseStep 2141861 = 401599) (by norm_num)
theorem B1740461 : Blo 1427533 1740461 := bbase (se 3 (by rfl) ⟨326336, by rfl⟩ : syracuseStep 1740461 = 652673) (by norm_num)
theorem B2141885 : Blo 1427533 2141885 := bbase (se 3 (by rfl) ⟨401603, by rfl⟩ : syracuseStep 2141885 = 803207) (by norm_num)
theorem B2289341 : Blo 1427533 2289341 := bbase (se 3 (by rfl) ⟨429251, by rfl⟩ : syracuseStep 2289341 = 858503) (by norm_num)
theorem B2141909 : Blo 1427533 2141909 := bbase (se 7 (by rfl) ⟨25100, by rfl⟩ : syracuseStep 2141909 = 50201) (by norm_num)
theorem B3215069 : Blo 1427533 3215069 := bbase (se 3 (by rfl) ⟨602825, by rfl⟩ : syracuseStep 3215069 = 1205651) (by norm_num)
theorem B2141933 : Blo 1427533 2141933 := bbase (se 3 (by rfl) ⟨401612, by rfl⟩ : syracuseStep 2141933 = 803225) (by norm_num)
theorem B3092213 : Blo 1427533 3092213 := bbase (se 5 (by rfl) ⟨144947, by rfl⟩ : syracuseStep 3092213 = 289895) (by norm_num)
theorem B2141957 : Blo 1427533 2141957 := bbase (se 4 (by rfl) ⟨200808, by rfl⟩ : syracuseStep 2141957 = 401617) (by norm_num)
theorem B4820741 : Blo 1427533 4820741 := bbase (se 4 (by rfl) ⟨451944, by rfl⟩ : syracuseStep 4820741 = 903889) (by norm_num)
theorem B2412301 : Blo 1427533 2412301 := bbase (se 3 (by rfl) ⟨452306, by rfl⟩ : syracuseStep 2412301 = 904613) (by norm_num)
theorem B2141981 : Blo 1427533 2141981 := bbase (se 3 (by rfl) ⟨401621, by rfl⟩ : syracuseStep 2141981 = 803243) (by norm_num)
theorem B3215141 : Blo 1427533 3215141 := bbase (se 4 (by rfl) ⟨301419, by rfl⟩ : syracuseStep 3215141 = 602839) (by norm_num)
theorem B2142005 : Blo 1427533 2142005 := bbase (se 5 (by rfl) ⟨100406, by rfl⟩ : syracuseStep 2142005 = 200813) (by norm_num)
theorem B2142029 : Blo 1427533 2142029 := bbase (se 3 (by rfl) ⟨401630, by rfl⟩ : syracuseStep 2142029 = 803261) (by norm_num)
theorem B3616589 : Blo 1427533 3616589 := bbase (se 3 (by rfl) ⟨678110, by rfl⟩ : syracuseStep 3616589 = 1356221) (by norm_num)
theorem B2142053 : Blo 1427533 2142053 := bbase (se 4 (by rfl) ⟨200817, by rfl⟩ : syracuseStep 2142053 = 401635) (by norm_num)
theorem B3215213 : Blo 1427533 3215213 := bbase (se 3 (by rfl) ⟨602852, by rfl⟩ : syracuseStep 3215213 = 1205705) (by norm_num)
theorem B2142077 : Blo 1427533 2142077 := bbase (se 3 (by rfl) ⟨401639, by rfl⟩ : syracuseStep 2142077 = 803279) (by norm_num)
theorem B2142101 : Blo 1427533 2142101 := bbase (se 6 (by rfl) ⟨50205, by rfl⟩ : syracuseStep 2142101 = 100411) (by norm_num)
theorem B2142125 : Blo 1427533 2142125 := bbase (se 3 (by rfl) ⟨401648, by rfl⟩ : syracuseStep 2142125 = 803297) (by norm_num)
theorem B13733813 : Blo 1427533 13733813 := bbase (se 5 (by rfl) ⟨643772, by rfl⟩ : syracuseStep 13733813 = 1287545) (by norm_num)
theorem B3215285 : Blo 1427533 3215285 := bbase (se 5 (by rfl) ⟨150716, by rfl⟩ : syracuseStep 3215285 = 301433) (by norm_num)
theorem B2936765 : Blo 1427533 2936765 := bbase (se 3 (by rfl) ⟨550643, by rfl⟩ : syracuseStep 2936765 = 1101287) (by norm_num)
theorem B2142149 : Blo 1427533 2142149 := bbase (se 4 (by rfl) ⟨200826, by rfl⟩ : syracuseStep 2142149 = 401653) (by norm_num)
theorem B16707541 : Blo 1427533 16707541 := bbase (se 7 (by rfl) ⟨195791, by rfl⟩ : syracuseStep 16707541 = 391583) (by norm_num)
theorem B2142173 : Blo 1427533 2142173 := bbase (se 3 (by rfl) ⟨401657, by rfl⟩ : syracuseStep 2142173 = 803315) (by norm_num)
theorem B2142197 : Blo 1427533 2142197 := bbase (se 5 (by rfl) ⟨100415, by rfl⟩ : syracuseStep 2142197 = 200831) (by norm_num)
theorem B3215357 : Blo 1427533 3215357 := bbase (se 3 (by rfl) ⟨602879, by rfl⟩ : syracuseStep 3215357 = 1205759) (by norm_num)
theorem B2142221 : Blo 1427533 2142221 := bbase (se 3 (by rfl) ⟨401666, by rfl⟩ : syracuseStep 2142221 = 803333) (by norm_num)
theorem B2142245 : Blo 1427533 2142245 := bbase (se 4 (by rfl) ⟨200835, by rfl⟩ : syracuseStep 2142245 = 401671) (by norm_num)
theorem B2142269 : Blo 1427533 2142269 := bbase (se 3 (by rfl) ⟨401675, by rfl⟩ : syracuseStep 2142269 = 803351) (by norm_num)
theorem B3215429 : Blo 1427533 3215429 := bbase (se 4 (by rfl) ⟨301446, by rfl⟩ : syracuseStep 3215429 = 602893) (by norm_num)
theorem B5427269 : Blo 1427533 5427269 := bbase (se 4 (by rfl) ⟨508806, by rfl⟩ : syracuseStep 5427269 = 1017613) (by norm_num)
theorem B2142293 : Blo 1427533 2142293 := bbase (se 8 (by rfl) ⟨12552, by rfl⟩ : syracuseStep 2142293 = 25105) (by norm_num)
theorem B2142317 : Blo 1427533 2142317 := bbase (se 3 (by rfl) ⟨401684, by rfl⟩ : syracuseStep 2142317 = 803369) (by norm_num)
theorem B7229573 : Blo 1427533 7229573 := bbase (se 4 (by rfl) ⟨677772, by rfl⟩ : syracuseStep 7229573 = 1355545) (by norm_num)
theorem B2142341 : Blo 1427533 2142341 := bbase (se 4 (by rfl) ⟨200844, by rfl⟩ : syracuseStep 2142341 = 401689) (by norm_num)
theorem B3215501 : Blo 1427533 3215501 := bbase (se 3 (by rfl) ⟨602906, by rfl⟩ : syracuseStep 3215501 = 1205813) (by norm_num)
theorem B2142365 : Blo 1427533 2142365 := bbase (se 3 (by rfl) ⟨401693, by rfl⟩ : syracuseStep 2142365 = 803387) (by norm_num)
theorem B3051685 : Blo 1427533 3051685 := bbase (se 4 (by rfl) ⟨286095, by rfl⟩ : syracuseStep 3051685 = 572191) (by norm_num)
theorem B3616933 : Blo 1427533 3616933 := bbase (se 4 (by rfl) ⟨339087, by rfl⟩ : syracuseStep 3616933 = 678175) (by norm_num)
theorem B2142389 : Blo 1427533 2142389 := bbase (se 5 (by rfl) ⟨100424, by rfl⟩ : syracuseStep 2142389 = 200849) (by norm_num)
theorem B4821173 : Blo 1427533 4821173 := bbase (se 5 (by rfl) ⟨225992, by rfl⟩ : syracuseStep 4821173 = 451985) (by norm_num)
theorem B2142413 : Blo 1427533 2142413 := bbase (se 3 (by rfl) ⟨401702, by rfl⟩ : syracuseStep 2142413 = 803405) (by norm_num)
theorem B3215573 : Blo 1427533 3215573 := bbase (se 7 (by rfl) ⟨37682, by rfl⟩ : syracuseStep 3215573 = 75365) (by norm_num)
theorem B2142437 : Blo 1427533 2142437 := bbase (se 4 (by rfl) ⟨200853, by rfl⟩ : syracuseStep 2142437 = 401707) (by norm_num)
theorem B2142461 : Blo 1427533 2142461 := bbase (se 3 (by rfl) ⟨401711, by rfl⟩ : syracuseStep 2142461 = 803423) (by norm_num)
theorem B4403461 : Blo 1427533 4403461 := bbase (se 4 (by rfl) ⟨412824, by rfl⟩ : syracuseStep 4403461 = 825649) (by norm_num)
theorem B2142485 : Blo 1427533 2142485 := bbase (se 6 (by rfl) ⟨50214, by rfl⟩ : syracuseStep 2142485 = 100429) (by norm_num)
theorem B3617045 : Blo 1427533 3617045 := bbase (se 6 (by rfl) ⟨84774, by rfl⟩ : syracuseStep 3617045 = 169549) (by norm_num)
theorem B3215645 : Blo 1427533 3215645 := bbase (se 3 (by rfl) ⟨602933, by rfl⟩ : syracuseStep 3215645 = 1205867) (by norm_num)
theorem B2142509 : Blo 1427533 2142509 := bbase (se 3 (by rfl) ⟨401720, by rfl⟩ : syracuseStep 2142509 = 803441) (by norm_num)
theorem B2142533 : Blo 1427533 2142533 := bbase (se 4 (by rfl) ⟨200862, by rfl⟩ : syracuseStep 2142533 = 401725) (by norm_num)
theorem B8130901 : Blo 1427533 8130901 := bbase (se 10 (by rfl) ⟨11910, by rfl⟩ : syracuseStep 8130901 = 23821) (by norm_num)
theorem B2142557 : Blo 1427533 2142557 := bbase (se 3 (by rfl) ⟨401729, by rfl⟩ : syracuseStep 2142557 = 803459) (by norm_num)
theorem B3215717 : Blo 1427533 3215717 := bbase (se 4 (by rfl) ⟨301473, by rfl⟩ : syracuseStep 3215717 = 602947) (by norm_num)
theorem B5427557 : Blo 1427533 5427557 := bbase (se 4 (by rfl) ⟨508833, by rfl⟩ : syracuseStep 5427557 = 1017667) (by norm_num)
theorem B2142581 : Blo 1427533 2142581 := bbase (se 5 (by rfl) ⟨100433, by rfl⟩ : syracuseStep 2142581 = 200867) (by norm_num)
theorem B8687989 : Blo 1427533 8687989 := bbase (se 5 (by rfl) ⟨407249, by rfl⟩ : syracuseStep 8687989 = 814499) (by norm_num)
theorem B1806725 : Blo 1427533 1806725 := bbase (se 4 (by rfl) ⟨169380, by rfl⟩ : syracuseStep 1806725 = 338761) (by norm_num)
theorem B2142605 : Blo 1427533 2142605 := bbase (se 3 (by rfl) ⟨401738, by rfl⟩ : syracuseStep 2142605 = 803477) (by norm_num)
theorem B5501333 : Blo 1427533 5501333 := bbase (se 6 (by rfl) ⟨128937, by rfl⟩ : syracuseStep 5501333 = 257875) (by norm_num)
theorem B2142629 : Blo 1427533 2142629 := bbase (se 4 (by rfl) ⟨200871, by rfl⟩ : syracuseStep 2142629 = 401743) (by norm_num)
theorem B3215789 : Blo 1427533 3215789 := bbase (se 3 (by rfl) ⟨602960, by rfl⟩ : syracuseStep 3215789 = 1205921) (by norm_num)
theorem B1806781 : Blo 1427533 1806781 := bbase (se 3 (by rfl) ⟨338771, by rfl⟩ : syracuseStep 1806781 = 677543) (by norm_num)
theorem B2142653 : Blo 1427533 2142653 := bbase (se 3 (by rfl) ⟨401747, by rfl⟩ : syracuseStep 2142653 = 803495) (by norm_num)
theorem B2142677 : Blo 1427533 2142677 := bbase (se 7 (by rfl) ⟨25109, by rfl⟩ : syracuseStep 2142677 = 50219) (by norm_num)
theorem B3617237 : Blo 1427533 3617237 := bbase (se 7 (by rfl) ⟨42389, by rfl⟩ : syracuseStep 3617237 = 84779) (by norm_num)
theorem B2142701 : Blo 1427533 2142701 := bbase (se 3 (by rfl) ⟨401756, by rfl⟩ : syracuseStep 2142701 = 803513) (by norm_num)
theorem B3215861 : Blo 1427533 3215861 := bbase (se 5 (by rfl) ⟨150743, by rfl⟩ : syracuseStep 3215861 = 301487) (by norm_num)
theorem B2142725 : Blo 1427533 2142725 := bbase (se 4 (by rfl) ⟨200880, by rfl⟩ : syracuseStep 2142725 = 401761) (by norm_num)
theorem B6517253 : Blo 1427533 6517253 := bbase (se 4 (by rfl) ⟨610992, by rfl⟩ : syracuseStep 6517253 = 1221985) (by norm_num)
theorem B5788181 : Blo 1427533 5788181 := bbase (se 6 (by rfl) ⟨135660, by rfl⟩ : syracuseStep 5788181 = 271321) (by norm_num)
theorem B1716761 : Blo 1427533 1716761 := bbase (se 2 (by rfl) ⟨643785, by rfl⟩ : syracuseStep 1716761 = 1287571) (by norm_num)
theorem B1806877 : Blo 1427533 1806877 := bbase (se 3 (by rfl) ⟨338789, by rfl⟩ : syracuseStep 1806877 = 677579) (by norm_num)
theorem B2142749 : Blo 1427533 2142749 := bbase (se 3 (by rfl) ⟨401765, by rfl⟩ : syracuseStep 2142749 = 803531) (by norm_num)
theorem B2142773 : Blo 1427533 2142773 := bbase (se 5 (by rfl) ⟨100442, by rfl⟩ : syracuseStep 2142773 = 200885) (by norm_num)
theorem B3215933 : Blo 1427533 3215933 := bbase (se 3 (by rfl) ⟨602987, by rfl⟩ : syracuseStep 3215933 = 1205975) (by norm_num)
theorem B2142797 : Blo 1427533 2142797 := bbase (se 3 (by rfl) ⟨401774, by rfl⟩ : syracuseStep 2142797 = 803549) (by norm_num)
theorem B2142821 : Blo 1427533 2142821 := bbase (se 4 (by rfl) ⟨200889, by rfl⟩ : syracuseStep 2142821 = 401779) (by norm_num)
theorem B4821605 : Blo 1427533 4821605 := bbase (se 4 (by rfl) ⟨452025, by rfl⟩ : syracuseStep 4821605 = 904051) (by norm_num)
theorem B4067957 : Blo 1427533 4067957 := bbase (se 5 (by rfl) ⟨190685, by rfl⟩ : syracuseStep 4067957 = 381371) (by norm_num)
theorem B2142845 : Blo 1427533 2142845 := bbase (se 3 (by rfl) ⟨401783, by rfl⟩ : syracuseStep 2142845 = 803567) (by norm_num)
theorem B3216005 : Blo 1427533 3216005 := bbase (se 4 (by rfl) ⟨301500, by rfl⟩ : syracuseStep 3216005 = 603001) (by norm_num)
theorem B2142869 : Blo 1427533 2142869 := bbase (se 6 (by rfl) ⟨50223, by rfl⟩ : syracuseStep 2142869 = 100447) (by norm_num)
theorem B3052181 : Blo 1427533 3052181 := bbase (se 6 (by rfl) ⟨71535, by rfl⟩ : syracuseStep 3052181 = 143071) (by norm_num)
theorem B2142893 : Blo 1427533 2142893 := bbase (se 3 (by rfl) ⟨401792, by rfl⟩ : syracuseStep 2142893 = 803585) (by norm_num)
theorem B6861509 : Blo 1427533 6861509 := bbase (se 4 (by rfl) ⟨643266, by rfl⟩ : syracuseStep 6861509 = 1286533) (by norm_num)
theorem B2142917 : Blo 1427533 2142917 := bbase (se 4 (by rfl) ⟨200898, by rfl⟩ : syracuseStep 2142917 = 401797) (by norm_num)
theorem B1807049 : Blo 1427533 1807049 := bbase (se 2 (by rfl) ⟨677643, by rfl⟩ : syracuseStep 1807049 = 1355287) (by norm_num)
theorem B3216077 : Blo 1427533 3216077 := bbase (se 3 (by rfl) ⟨603014, by rfl⟩ : syracuseStep 3216077 = 1206029) (by norm_num)
theorem B2142941 : Blo 1427533 2142941 := bbase (se 3 (by rfl) ⟨401801, by rfl⟩ : syracuseStep 2142941 = 803603) (by norm_num)
theorem B2142965 : Blo 1427533 2142965 := bbase (se 5 (by rfl) ⟨100451, by rfl⟩ : syracuseStep 2142965 = 200903) (by norm_num)
theorem B3863285 : Blo 1427533 3863285 := bbase (se 5 (by rfl) ⟨181091, by rfl⟩ : syracuseStep 3863285 = 362183) (by norm_num)
theorem B2749181 : Blo 1427533 2749181 := bbase (se 3 (by rfl) ⟨515471, by rfl⟩ : syracuseStep 2749181 = 1030943) (by norm_num)
theorem B1807105 : Blo 1427533 1807105 := bbase (se 2 (by rfl) ⟨677664, by rfl⟩ : syracuseStep 1807105 = 1355329) (by norm_num)
theorem B2142989 : Blo 1427533 2142989 := bbase (se 3 (by rfl) ⟨401810, by rfl⟩ : syracuseStep 2142989 = 803621) (by norm_num)
theorem B3216149 : Blo 1427533 3216149 := bbase (se 6 (by rfl) ⟨75378, by rfl⟩ : syracuseStep 3216149 = 150757) (by norm_num)
theorem B2896669 : Blo 1427533 2896669 := bbase (se 3 (by rfl) ⟨543125, by rfl⟩ : syracuseStep 2896669 = 1086251) (by norm_num)
theorem B6099749 : Blo 1427533 6099749 := bbase (se 4 (by rfl) ⟨571851, by rfl⟩ : syracuseStep 6099749 = 1143703) (by norm_num)
theorem B2143013 : Blo 1427533 2143013 := bbase (se 4 (by rfl) ⟨200907, by rfl⟩ : syracuseStep 2143013 = 401815) (by norm_num)
theorem B3617581 : Blo 1427533 3617581 := bbase (se 3 (by rfl) ⟨678296, by rfl⟩ : syracuseStep 3617581 = 1356593) (by norm_num)
theorem B2143037 : Blo 1427533 2143037 := bbase (se 3 (by rfl) ⟨401819, by rfl⟩ : syracuseStep 2143037 = 803639) (by norm_num)
theorem B3912533 : Blo 1427533 3912533 := bbase (se 9 (by rfl) ⟨11462, by rfl⟩ : syracuseStep 3912533 = 22925) (by norm_num)
theorem B2143061 : Blo 1427533 2143061 := bbase (se 9 (by rfl) ⟨6278, by rfl⟩ : syracuseStep 2143061 = 12557) (by norm_num)
theorem B3216221 : Blo 1427533 3216221 := bbase (se 3 (by rfl) ⟨603041, by rfl⟩ : syracuseStep 3216221 = 1206083) (by norm_num)
theorem B1807201 : Blo 1427533 1807201 := bbase (se 2 (by rfl) ⟨677700, by rfl⟩ : syracuseStep 1807201 = 1355401) (by norm_num)
theorem B2143085 : Blo 1427533 2143085 := bbase (se 3 (by rfl) ⟨401828, by rfl⟩ : syracuseStep 2143085 = 803657) (by norm_num)
theorem B2143109 : Blo 1427533 2143109 := bbase (se 4 (by rfl) ⟨200916, by rfl⟩ : syracuseStep 2143109 = 401833) (by norm_num)
theorem B3478421 : Blo 1427533 3478421 := bbase (se 6 (by rfl) ⟨81525, by rfl⟩ : syracuseStep 3478421 = 163051) (by norm_num)
theorem B2143133 : Blo 1427533 2143133 := bbase (se 3 (by rfl) ⟨401837, by rfl⟩ : syracuseStep 2143133 = 803675) (by norm_num)
theorem B3617693 : Blo 1427533 3617693 := bbase (se 3 (by rfl) ⟨678317, by rfl⟩ : syracuseStep 3617693 = 1356635) (by norm_num)
theorem B3216293 : Blo 1427533 3216293 := bbase (se 4 (by rfl) ⟨301527, by rfl⟩ : syracuseStep 3216293 = 603055) (by norm_num)
theorem B2143157 : Blo 1427533 2143157 := bbase (se 5 (by rfl) ⟨100460, by rfl⟩ : syracuseStep 2143157 = 200921) (by norm_num)
theorem B2749373 : Blo 1427533 2749373 := bbase (se 3 (by rfl) ⟨515507, by rfl⟩ : syracuseStep 2749373 = 1031015) (by norm_num)
theorem B2143181 : Blo 1427533 2143181 := bbase (se 3 (by rfl) ⟨401846, by rfl⟩ : syracuseStep 2143181 = 803693) (by norm_num)
theorem B1831889 : Blo 1427533 1831889 := bbase (se 2 (by rfl) ⟨686958, by rfl⟩ : syracuseStep 1831889 = 1373917) (by norm_num)
theorem B2143205 : Blo 1427533 2143205 := bbase (se 4 (by rfl) ⟨200925, by rfl⟩ : syracuseStep 2143205 = 401851) (by norm_num)
theorem B3216365 : Blo 1427533 3216365 := bbase (se 3 (by rfl) ⟨603068, by rfl⟩ : syracuseStep 3216365 = 1206137) (by norm_num)
theorem B1717237 : Blo 1427533 1717237 := bbase (se 5 (by rfl) ⟨80495, by rfl⟩ : syracuseStep 1717237 = 160991) (by norm_num)
theorem B2143229 : Blo 1427533 2143229 := bbase (se 3 (by rfl) ⟨401855, by rfl⟩ : syracuseStep 2143229 = 803711) (by norm_num)
theorem B1807373 : Blo 1427533 1807373 := bbase (se 3 (by rfl) ⟨338882, by rfl⟩ : syracuseStep 1807373 = 677765) (by norm_num)
theorem B1717265 : Blo 1427533 1717265 := bbase (se 2 (by rfl) ⟨643974, by rfl⟩ : syracuseStep 1717265 = 1287949) (by norm_num)
theorem B4822037 : Blo 1427533 4822037 := bbase (se 6 (by rfl) ⟨113016, by rfl⟩ : syracuseStep 4822037 = 226033) (by norm_num)
theorem B2143253 : Blo 1427533 2143253 := bbase (se 6 (by rfl) ⟨50232, by rfl⟩ : syracuseStep 2143253 = 100465) (by norm_num)
theorem B2143277 : Blo 1427533 2143277 := bbase (se 3 (by rfl) ⟨401864, by rfl⟩ : syracuseStep 2143277 = 803729) (by norm_num)
theorem B3216437 : Blo 1427533 3216437 := bbase (se 5 (by rfl) ⟨150770, by rfl⟩ : syracuseStep 3216437 = 301541) (by norm_num)
theorem B3093565 : Blo 1427533 3093565 := bbase (se 3 (by rfl) ⟨580043, by rfl⟩ : syracuseStep 3093565 = 1160087) (by norm_num)
theorem B1807429 : Blo 1427533 1807429 := bbase (se 4 (by rfl) ⟨169446, by rfl⟩ : syracuseStep 1807429 = 338893) (by norm_num)
theorem B2143301 : Blo 1427533 2143301 := bbase (se 4 (by rfl) ⟨200934, by rfl⟩ : syracuseStep 2143301 = 401869) (by norm_num)
theorem B3667021 : Blo 1427533 3667021 := bbase (se 3 (by rfl) ⟨687566, by rfl⟩ : syracuseStep 3667021 = 1375133) (by norm_num)
theorem B2143325 : Blo 1427533 2143325 := bbase (se 3 (by rfl) ⟨401873, by rfl⟩ : syracuseStep 2143325 = 803747) (by norm_num)
theorem B3617885 : Blo 1427533 3617885 := bbase (se 3 (by rfl) ⟨678353, by rfl⟩ : syracuseStep 3617885 = 1356707) (by norm_num)
theorem B2143349 : Blo 1427533 2143349 := bbase (se 5 (by rfl) ⟨100469, by rfl⟩ : syracuseStep 2143349 = 200939) (by norm_num)
theorem B2143373 : Blo 1427533 2143373 := bbase (se 3 (by rfl) ⟨401882, by rfl⟩ : syracuseStep 2143373 = 803765) (by norm_num)
theorem B1807525 : Blo 1427533 1807525 := bbase (se 4 (by rfl) ⟨169455, by rfl⟩ : syracuseStep 1807525 = 338911) (by norm_num)
theorem B2143397 : Blo 1427533 2143397 := bbase (se 4 (by rfl) ⟨200943, by rfl⟩ : syracuseStep 2143397 = 401887) (by norm_num)
theorem B2143421 : Blo 1427533 2143421 := bbase (se 3 (by rfl) ⟨401891, by rfl⟩ : syracuseStep 2143421 = 803783) (by norm_num)
theorem B2143445 : Blo 1427533 2143445 := bbase (se 7 (by rfl) ⟨25118, by rfl⟩ : syracuseStep 2143445 = 50237) (by norm_num)
theorem B2143469 : Blo 1427533 2143469 := bbase (se 3 (by rfl) ⟨401900, by rfl⟩ : syracuseStep 2143469 = 803801) (by norm_num)
theorem B3257605 : Blo 1427533 3257605 := bbase (se 4 (by rfl) ⟨305400, by rfl⟩ : syracuseStep 3257605 = 610801) (by norm_num)
theorem B2143493 : Blo 1427533 2143493 := bbase (se 4 (by rfl) ⟨200952, by rfl⟩ : syracuseStep 2143493 = 401905) (by norm_num)
theorem B2143517 : Blo 1427533 2143517 := bbase (se 3 (by rfl) ⟨401909, by rfl⟩ : syracuseStep 2143517 = 803819) (by norm_num)
theorem B2143541 : Blo 1427533 2143541 := bbase (se 5 (by rfl) ⟨100478, by rfl⟩ : syracuseStep 2143541 = 200957) (by norm_num)
theorem B2143565 : Blo 1427533 2143565 := bbase (se 3 (by rfl) ⟨401918, by rfl⟩ : syracuseStep 2143565 = 803837) (by norm_num)
theorem B1807697 : Blo 1427533 1807697 := bbase (se 2 (by rfl) ⟨677886, by rfl⟩ : syracuseStep 1807697 = 1355773) (by norm_num)
theorem B2143589 : Blo 1427533 2143589 := bbase (se 4 (by rfl) ⟨200961, by rfl⟩ : syracuseStep 2143589 = 401923) (by norm_num)
theorem B2143613 : Blo 1427533 2143613 := bbase (se 3 (by rfl) ⟨401927, by rfl⟩ : syracuseStep 2143613 = 803855) (by norm_num)
theorem B1807753 : Blo 1427533 1807753 := bbase (se 2 (by rfl) ⟨677907, by rfl⟩ : syracuseStep 1807753 = 1355815) (by norm_num)
theorem B7230869 : Blo 1427533 7230869 := bbase (se 6 (by rfl) ⟨169473, by rfl⟩ : syracuseStep 7230869 = 338947) (by norm_num)
theorem B2143637 : Blo 1427533 2143637 := bbase (se 6 (by rfl) ⟨50241, by rfl⟩ : syracuseStep 2143637 = 100483) (by norm_num)
theorem B2143661 : Blo 1427533 2143661 := bbase (se 3 (by rfl) ⟨401936, by rfl⟩ : syracuseStep 2143661 = 803873) (by norm_num)
theorem B3618229 : Blo 1427533 3618229 := bbase (se 5 (by rfl) ⟨169604, by rfl⟩ : syracuseStep 3618229 = 339209) (by norm_num)
theorem B4822469 : Blo 1427533 4822469 := bbase (se 4 (by rfl) ⟨452106, by rfl⟩ : syracuseStep 4822469 = 904213) (by norm_num)
theorem B2143685 : Blo 1427533 2143685 := bbase (se 4 (by rfl) ⟨200970, by rfl⟩ : syracuseStep 2143685 = 401941) (by norm_num)
theorem B2143709 : Blo 1427533 2143709 := bbase (se 3 (by rfl) ⟨401945, by rfl⟩ : syracuseStep 2143709 = 803891) (by norm_num)
theorem B1807849 : Blo 1427533 1807849 := bbase (se 2 (by rfl) ⟨677943, by rfl⟩ : syracuseStep 1807849 = 1355887) (by norm_num)
theorem B2143733 : Blo 1427533 2143733 := bbase (se 5 (by rfl) ⟨100487, by rfl⟩ : syracuseStep 2143733 = 200975) (by norm_num)
theorem B3053045 : Blo 1427533 3053045 := bbase (se 5 (by rfl) ⟨143111, by rfl⟩ : syracuseStep 3053045 = 286223) (by norm_num)
theorem B2143757 : Blo 1427533 2143757 := bbase (se 3 (by rfl) ⟨401954, by rfl⟩ : syracuseStep 2143757 = 803909) (by norm_num)
theorem B2143781 : Blo 1427533 2143781 := bbase (se 4 (by rfl) ⟨200979, by rfl⟩ : syracuseStep 2143781 = 401959) (by norm_num)
theorem B3618341 : Blo 1427533 3618341 := bbase (se 4 (by rfl) ⟨339219, by rfl⟩ : syracuseStep 3618341 = 678439) (by norm_num)
theorem B10851893 : Blo 1427533 10851893 := bbase (se 5 (by rfl) ⟨508682, by rfl⟩ : syracuseStep 10851893 = 1017365) (by norm_num)
theorem B2143805 : Blo 1427533 2143805 := bbase (se 3 (by rfl) ⟨401963, by rfl⟩ : syracuseStep 2143805 = 803927) (by norm_num)
theorem B4576837 : Blo 1427533 4576837 := bbase (se 4 (by rfl) ⟨429078, by rfl⟩ : syracuseStep 4576837 = 858157) (by norm_num)
theorem B2143829 : Blo 1427533 2143829 := bbase (se 8 (by rfl) ⟨12561, by rfl⟩ : syracuseStep 2143829 = 25123) (by norm_num)
theorem B2143853 : Blo 1427533 2143853 := bbase (se 3 (by rfl) ⟨401972, by rfl⟩ : syracuseStep 2143853 = 803945) (by norm_num)
theorem B2143877 : Blo 1427533 2143877 := bbase (se 4 (by rfl) ⟨200988, by rfl⟩ : syracuseStep 2143877 = 401977) (by norm_num)
theorem B1808021 : Blo 1427533 1808021 := bbase (se 6 (by rfl) ⟨42375, by rfl⟩ : syracuseStep 1808021 = 84751) (by norm_num)
theorem B2143901 : Blo 1427533 2143901 := bbase (se 3 (by rfl) ⟨401981, by rfl⟩ : syracuseStep 2143901 = 803963) (by norm_num)
theorem B9148085 : Blo 1427533 9148085 := bbase (se 5 (by rfl) ⟨428816, by rfl⟩ : syracuseStep 9148085 = 857633) (by norm_num)
theorem B7722677 : Blo 1427533 7722677 := bbase (se 5 (by rfl) ⟨362000, by rfl⟩ : syracuseStep 7722677 = 724001) (by norm_num)
theorem B2143925 : Blo 1427533 2143925 := bbase (se 5 (by rfl) ⟨100496, by rfl⟩ : syracuseStep 2143925 = 200993) (by norm_num)
theorem B1808077 : Blo 1427533 1808077 := bbase (se 3 (by rfl) ⟨339014, by rfl⟩ : syracuseStep 1808077 = 678029) (by norm_num)
theorem B2143949 : Blo 1427533 2143949 := bbase (se 3 (by rfl) ⟨401990, by rfl⟩ : syracuseStep 2143949 = 803981) (by norm_num)
theorem B14669525 : Blo 1427533 14669525 := bbase (se 7 (by rfl) ⟨171908, by rfl⟩ : syracuseStep 14669525 = 343817) (by norm_num)
theorem B2143973 : Blo 1427533 2143973 := bbase (se 4 (by rfl) ⟨200997, by rfl⟩ : syracuseStep 2143973 = 401995) (by norm_num)
theorem B10295029 : Blo 1427533 10295029 := bbase (se 5 (by rfl) ⟨482579, by rfl⟩ : syracuseStep 10295029 = 965159) (by norm_num)
theorem B2143997 : Blo 1427533 2143997 := bbase (se 3 (by rfl) ⟨401999, by rfl⟩ : syracuseStep 2143997 = 803999) (by norm_num)
theorem B2144021 : Blo 1427533 2144021 := bbase (se 6 (by rfl) ⟨50250, by rfl⟩ : syracuseStep 2144021 = 100501) (by norm_num)
theorem B1808173 : Blo 1427533 1808173 := bbase (se 3 (by rfl) ⟨339032, by rfl⟩ : syracuseStep 1808173 = 678065) (by norm_num)
theorem B2144045 : Blo 1427533 2144045 := bbase (se 3 (by rfl) ⟨402008, by rfl⟩ : syracuseStep 2144045 = 804017) (by norm_num)
theorem B2144069 : Blo 1427533 2144069 := bbase (se 4 (by rfl) ⟨201006, by rfl⟩ : syracuseStep 2144069 = 402013) (by norm_num)
theorem B22288213 : Blo 1427533 22288213 := bbase (se 9 (by rfl) ⟨65297, by rfl⟩ : syracuseStep 22288213 = 130595) (by norm_num)
theorem B2144093 : Blo 1427533 2144093 := bbase (se 3 (by rfl) ⟨402017, by rfl⟩ : syracuseStep 2144093 = 804035) (by norm_num)
theorem B4822901 : Blo 1427533 4822901 := bbase (se 5 (by rfl) ⟨226073, by rfl⟩ : syracuseStep 4822901 = 452147) (by norm_num)
theorem B2144117 : Blo 1427533 2144117 := bbase (se 5 (by rfl) ⟨100505, by rfl⟩ : syracuseStep 2144117 = 201011) (by norm_num)
theorem B2144141 : Blo 1427533 2144141 := bbase (se 3 (by rfl) ⟨402026, by rfl⟩ : syracuseStep 2144141 = 804053) (by norm_num)
theorem B5420965 : Blo 1427533 5420965 := bbase (se 4 (by rfl) ⟨508215, by rfl⟩ : syracuseStep 5420965 = 1016431) (by norm_num)
theorem B2144165 : Blo 1427533 2144165 := bbase (se 4 (by rfl) ⟨201015, by rfl⟩ : syracuseStep 2144165 = 402031) (by norm_num)
theorem B2144189 : Blo 1427533 2144189 := bbase (se 3 (by rfl) ⟨402035, by rfl⟩ : syracuseStep 2144189 = 804071) (by norm_num)
theorem B10844117 : Blo 1427533 10844117 := bbase (se 7 (by rfl) ⟨127079, by rfl⟩ : syracuseStep 10844117 = 254159) (by norm_num)
theorem B2144213 : Blo 1427533 2144213 := bbase (se 7 (by rfl) ⟨25127, by rfl⟩ : syracuseStep 2144213 = 50255) (by norm_num)
theorem B1808345 : Blo 1427533 1808345 := bbase (se 2 (by rfl) ⟨678129, by rfl⟩ : syracuseStep 1808345 = 1356259) (by norm_num)
theorem B2144237 : Blo 1427533 2144237 := bbase (se 3 (by rfl) ⟨402044, by rfl⟩ : syracuseStep 2144237 = 804089) (by norm_num)
theorem B2144261 : Blo 1427533 2144261 := bbase (se 4 (by rfl) ⟨201024, by rfl⟩ : syracuseStep 2144261 = 402049) (by norm_num)
theorem B1808401 : Blo 1427533 1808401 := bbase (se 2 (by rfl) ⟨678150, by rfl⟩ : syracuseStep 1808401 = 1356301) (by norm_num)
theorem B2144285 : Blo 1427533 2144285 := bbase (se 3 (by rfl) ⟨402053, by rfl⟩ : syracuseStep 2144285 = 804107) (by norm_num)
theorem B1628209 : Blo 1427533 1628209 := bbase (se 2 (by rfl) ⟨610578, by rfl⟩ : syracuseStep 1628209 = 1221157) (by norm_num)
theorem B5150789 : Blo 1427533 5150789 := bbase (se 4 (by rfl) ⟨482886, by rfl⟩ : syracuseStep 5150789 = 965773) (by norm_num)
theorem B1628273 : Blo 1427533 1628273 := bbase (se 2 (by rfl) ⟨610602, by rfl⟩ : syracuseStep 1628273 = 1221205) (by norm_num)
theorem B1808497 : Blo 1427533 1808497 := bbase (se 2 (by rfl) ⟨678186, by rfl⟩ : syracuseStep 1808497 = 1356373) (by norm_num)
theorem B3479669 : Blo 1427533 3479669 := bbase (se 5 (by rfl) ⟨163109, by rfl⟩ : syracuseStep 3479669 = 326219) (by norm_num)
theorem B1628309 : Blo 1427533 1628309 := bbase (se 6 (by rfl) ⟨38163, by rfl⟩ : syracuseStep 1628309 = 76327) (by norm_num)
theorem B1833121 : Blo 1427533 1833121 := bbase (se 2 (by rfl) ⟨687420, by rfl⟩ : syracuseStep 1833121 = 1374841) (by norm_num)
theorem B4069541 : Blo 1427533 4069541 := bbase (se 4 (by rfl) ⟨381519, by rfl⟩ : syracuseStep 4069541 = 763039) (by norm_num)
theorem B1833161 : Blo 1427533 1833161 := bbase (se 2 (by rfl) ⟨687435, by rfl⟩ : syracuseStep 1833161 = 1374871) (by norm_num)
theorem B5421269 : Blo 1427533 5421269 := bbase (se 7 (by rfl) ⟨63530, by rfl⟩ : syracuseStep 5421269 = 127061) (by norm_num)
theorem B8132885 : Blo 1427533 8132885 := bbase (se 6 (by rfl) ⟨190614, by rfl⟩ : syracuseStep 8132885 = 381229) (by norm_num)
theorem B1808669 : Blo 1427533 1808669 := bbase (se 3 (by rfl) ⟨339125, by rfl⟩ : syracuseStep 1808669 = 678251) (by norm_num)
theorem B4823333 : Blo 1427533 4823333 := bbase (se 4 (by rfl) ⟨452187, by rfl⟩ : syracuseStep 4823333 = 904375) (by norm_num)
theorem B1808725 : Blo 1427533 1808725 := bbase (se 10 (by rfl) ⟨2649, by rfl⟩ : syracuseStep 1808725 = 5299) (by norm_num)
theorem B23181653 : Blo 1427533 23181653 := bbase (se 10 (by rfl) ⟨33957, by rfl⟩ : syracuseStep 23181653 = 67915) (by norm_num)
theorem B1808821 : Blo 1427533 1808821 := bbase (se 5 (by rfl) ⟨84788, by rfl⟩ : syracuseStep 1808821 = 169577) (by norm_num)
theorem B1833445 : Blo 1427533 1833445 := bbase (se 4 (by rfl) ⟨171885, by rfl⟩ : syracuseStep 1833445 = 343771) (by norm_num)
theorem B5151205 : Blo 1427533 5151205 := bbase (se 4 (by rfl) ⟨482925, by rfl⟩ : syracuseStep 5151205 = 965851) (by norm_num)
theorem B5151221 : Blo 1427533 5151221 := bbase (se 5 (by rfl) ⟨241463, by rfl⟩ : syracuseStep 5151221 = 482927) (by norm_num)
theorem B1808993 : Blo 1427533 1808993 := bbase (se 2 (by rfl) ⟨678372, by rfl⟩ : syracuseStep 1808993 = 1356745) (by norm_num)
theorem B1809049 : Blo 1427533 1809049 := bbase (se 2 (by rfl) ⟨678393, by rfl⟩ : syracuseStep 1809049 = 1356787) (by norm_num)
theorem B6863525 : Blo 1427533 6863525 := bbase (se 4 (by rfl) ⟨643455, by rfl⟩ : syracuseStep 6863525 = 1286911) (by norm_num)
theorem B7232165 : Blo 1427533 7232165 := bbase (se 4 (by rfl) ⟨678015, by rfl⟩ : syracuseStep 7232165 = 1356031) (by norm_num)
theorem B4823765 : Blo 1427533 4823765 := bbase (se 7 (by rfl) ⟨56528, by rfl⟩ : syracuseStep 4823765 = 113057) (by norm_num)
theorem B1628893 : Blo 1427533 1628893 := bbase (se 3 (by rfl) ⟨305417, by rfl⟩ : syracuseStep 1628893 = 610835) (by norm_num)
theorem B5790437 : Blo 1427533 5790437 := bbase (se 4 (by rfl) ⟨542853, by rfl⟩ : syracuseStep 5790437 = 1085707) (by norm_num)
theorem B1809145 : Blo 1427533 1809145 := bbase (se 2 (by rfl) ⟨678429, by rfl⟩ : syracuseStep 1809145 = 1356859) (by norm_num)
theorem B5151509 : Blo 1427533 5151509 := bbase (se 6 (by rfl) ⟨120738, by rfl⟩ : syracuseStep 5151509 = 241477) (by norm_num)
theorem B4070213 : Blo 1427533 4070213 := bbase (se 4 (by rfl) ⟨381582, by rfl⟩ : syracuseStep 4070213 = 763165) (by norm_num)
theorem B6863717 : Blo 1427533 6863717 := bbase (se 4 (by rfl) ⟨643473, by rfl⟩ : syracuseStep 6863717 = 1286947) (by norm_num)
theorem B5790581 : Blo 1427533 5790581 := bbase (se 5 (by rfl) ⟨271433, by rfl⟩ : syracuseStep 5790581 = 542867) (by norm_num)
theorem B2710597 : Blo 1427533 2710597 := bbase (se 4 (by rfl) ⟨254118, by rfl⟩ : syracuseStep 2710597 = 508237) (by norm_num)
theorem B4824197 : Blo 1427533 4824197 := bbase (se 4 (by rfl) ⟨452268, by rfl⟩ : syracuseStep 4824197 = 904537) (by norm_num)
theorem B2710741 : Blo 1427533 2710741 := bbase (se 7 (by rfl) ⟨31766, by rfl⟩ : syracuseStep 2710741 = 63533) (by norm_num)
theorem B4070645 : Blo 1427533 4070645 := bbase (se 5 (by rfl) ⟨190811, by rfl⟩ : syracuseStep 4070645 = 381623) (by norm_num)
theorem B12197141 : Blo 1427533 12197141 := bbase (se 6 (by rfl) ⟨285870, by rfl⟩ : syracuseStep 12197141 = 571741) (by norm_num)
theorem B4341077 : Blo 1427533 4341077 := bbase (se 11 (by rfl) ⟨3179, by rfl⟩ : syracuseStep 4341077 = 6359) (by norm_num)
theorem B2710901 : Blo 1427533 2710901 := bbase (se 5 (by rfl) ⟨127073, by rfl⟩ : syracuseStep 2710901 = 254147) (by norm_num)
theorem B1629605 : Blo 1427533 1629605 := bbase (se 4 (by rfl) ⟨152775, by rfl⟩ : syracuseStep 1629605 = 305551) (by norm_num)
theorem B2711045 : Blo 1427533 2711045 := bbase (se 4 (by rfl) ⟨254160, by rfl⟩ : syracuseStep 2711045 = 508321) (by norm_num)
theorem B1629733 : Blo 1427533 1629733 := bbase (se 4 (by rfl) ⟨152787, by rfl⟩ : syracuseStep 1629733 = 305575) (by norm_num)
theorem B4824629 : Blo 1427533 4824629 := bbase (se 5 (by rfl) ⟨226154, by rfl⟩ : syracuseStep 4824629 = 452309) (by norm_num)
theorem B1629769 : Blo 1427533 1629769 := bbase (se 2 (by rfl) ⟨611163, by rfl⟩ : syracuseStep 1629769 = 1222327) (by norm_num)
theorem B2711333 : Blo 1427533 2711333 := bbase (se 4 (by rfl) ⟨254187, by rfl⟩ : syracuseStep 2711333 = 508375) (by norm_num)
theorem B7233461 : Blo 1427533 7233461 := bbase (se 5 (by rfl) ⟨339068, by rfl⟩ : syracuseStep 7233461 = 678137) (by norm_num)
theorem B1630133 : Blo 1427533 1630133 := bbase (se 5 (by rfl) ⟨76412, by rfl⟩ : syracuseStep 1630133 = 152825) (by norm_num)
theorem B2711485 : Blo 1427533 2711485 := bbase (se 3 (by rfl) ⟨508403, by rfl⟩ : syracuseStep 2711485 = 1016807) (by norm_num)
theorem B2711569 : Blo 1427533 2711569 := bstep (se 2 (by rfl) ⟨1016838, by rfl⟩ : syracuseStep 2711569 = 2033677) B2033677
theorem B4579373 : Blo 1427533 4579373 := bstep (se 3 (by rfl) ⟨858632, by rfl⟩ : syracuseStep 4579373 = 1717265) B1717265
theorem B2170945 : Blo 1427533 2170945 := bstep (se 2 (by rfl) ⟨814104, by rfl⟩ : syracuseStep 2170945 = 1628209) B1628209
theorem B5423395 : Blo 1427533 5423395 := bstep (se 1 (by rfl) ⟨4067546, by rfl⟩ : syracuseStep 5423395 = 8135093) B8135093
theorem B4342061 : Blo 1427533 4342061 := bstep (se 3 (by rfl) ⟨814136, by rfl⟩ : syracuseStep 4342061 = 1628273) B1628273
theorem B3858787 : Blo 1427533 3858787 := bstep (se 1 (by rfl) ⟨2894090, by rfl⟩ : syracuseStep 3858787 = 5788181) B5788181
theorem B9150853 : Blo 1427533 9150853 := bstep (se 4 (by rfl) ⟨857892, by rfl⟩ : syracuseStep 9150853 = 1715785) B1715785
theorem B4342157 : Blo 1427533 4342157 := bstep (se 3 (by rfl) ⟨814154, by rfl⟩ : syracuseStep 4342157 = 1628309) B1628309
theorem B2711971 : Blo 1427533 2711971 := bstep (se 1 (by rfl) ⟨2033978, by rfl⟩ : syracuseStep 2711971 = 4067957) B4067957
theorem B2712017 : Blo 1427533 2712017 := bstep (se 2 (by rfl) ⟨1017006, by rfl⟩ : syracuseStep 2712017 = 2034013) B2034013
theorem B1606099 : Blo 1427533 1606099 := bstep (se 1 (by rfl) ⟨1204574, by rfl⟩ : syracuseStep 1606099 = 2409149) B2409149
theorem B11583985 : Blo 1427533 11583985 := bstep (se 2 (by rfl) ⟨4343994, by rfl⟩ : syracuseStep 11583985 = 8687989) B8687989
theorem B2409041 : Blo 1427533 2409041 := bstep (se 2 (by rfl) ⟨903390, by rfl⟩ : syracuseStep 2409041 = 1806781) B1806781
theorem B1606243 : Blo 1427533 1606243 := bstep (se 1 (by rfl) ⟨1204682, by rfl⟩ : syracuseStep 1606243 = 2409365) B2409365
theorem B2409169 : Blo 1427533 2409169 := bstep (se 2 (by rfl) ⟨903438, by rfl⟩ : syracuseStep 2409169 = 1806877) B1806877
theorem B2712305 : Blo 1427533 2712305 := bstep (se 2 (by rfl) ⟨1017114, by rfl⟩ : syracuseStep 2712305 = 2034229) B2034229
theorem B2409203 : Blo 1427533 2409203 := bstep (se 1 (by rfl) ⟨1806902, by rfl⟩ : syracuseStep 2409203 = 3613805) B3613805
theorem B1606387 : Blo 1427533 1606387 := bstep (se 1 (by rfl) ⟨1204790, by rfl⟩ : syracuseStep 1606387 = 2409581) B2409581
theorem B3212081 : Blo 1427533 3212081 := bstep (se 2 (by rfl) ⟨1204530, by rfl⟩ : syracuseStep 3212081 = 2409061) B2409061
theorem B3212099 : Blo 1427533 3212099 := bstep (se 1 (by rfl) ⟨2409074, by rfl⟩ : syracuseStep 3212099 = 4818149) B4818149
theorem B2409331 : Blo 1427533 2409331 := bstep (se 1 (by rfl) ⟨1806998, by rfl⟩ : syracuseStep 2409331 = 3613997) B3613997
theorem B1606531 : Blo 1427533 1606531 := bstep (se 1 (by rfl) ⟨1204898, by rfl⟩ : syracuseStep 1606531 = 2409797) B2409797
theorem B61817741 : Blo 1427533 61817741 := bstep (se 3 (by rfl) ⟨11590826, by rfl⟩ : syracuseStep 61817741 = 23181653) B23181653
theorem B2171857 : Blo 1427533 2171857 := bstep (se 2 (by rfl) ⟨814446, by rfl⟩ : syracuseStep 2171857 = 1628893) B1628893
theorem B2409473 : Blo 1427533 2409473 := bstep (se 2 (by rfl) ⟨903552, by rfl⟩ : syracuseStep 2409473 = 1807105) B1807105
theorem B4817933 : Blo 1427533 4817933 := bstep (se 3 (by rfl) ⟨903362, by rfl⟩ : syracuseStep 4817933 = 1806725) B1806725
theorem B2442259 : Blo 1427533 2442259 := bstep (se 1 (by rfl) ⟨1831694, by rfl⟩ : syracuseStep 2442259 = 3663389) B3663389
theorem B1606675 : Blo 1427533 1606675 := bstep (se 1 (by rfl) ⟨1205006, by rfl⟩ : syracuseStep 1606675 = 2410013) B2410013
theorem B7234595 : Blo 1427533 7234595 := bstep (se 1 (by rfl) ⟨5425946, by rfl⟩ : syracuseStep 7234595 = 10851893) B10851893
theorem B4817987 : Blo 1427533 4817987 := bstep (se 1 (by rfl) ⟨3613490, by rfl⟩ : syracuseStep 4817987 = 7226981) B7226981
theorem B3212369 : Blo 1427533 3212369 := bstep (se 2 (by rfl) ⟨1204638, by rfl⟩ : syracuseStep 3212369 = 2409277) B2409277
theorem B3212387 : Blo 1427533 3212387 := bstep (se 1 (by rfl) ⟨2409290, by rfl⟩ : syracuseStep 3212387 = 4818581) B4818581
theorem B1524835 : Blo 1427533 1524835 := bstep (se 1 (by rfl) ⟨1143626, by rfl⟩ : syracuseStep 1524835 = 2287253) B2287253
theorem B2409601 : Blo 1427533 2409601 := bstep (se 2 (by rfl) ⟨903600, by rfl⟩ : syracuseStep 2409601 = 1807201) B1807201
theorem B2032771 : Blo 1427533 2032771 := bstep (se 1 (by rfl) ⟨1524578, by rfl⟩ : syracuseStep 2032771 = 3049157) B3049157
theorem B2409635 : Blo 1427533 2409635 := bstep (se 1 (by rfl) ⟨1807226, by rfl⟩ : syracuseStep 2409635 = 3614453) B3614453
theorem B1606819 : Blo 1427533 1606819 := bstep (se 1 (by rfl) ⟨1205114, by rfl⟩ : syracuseStep 1606819 = 2410229) B2410229
theorem B2286881 : Blo 1427533 2286881 := bstep (se 2 (by rfl) ⟨857580, by rfl⟩ : syracuseStep 2286881 = 1715161) B1715161
theorem B2409763 : Blo 1427533 2409763 := bstep (se 1 (by rfl) ⟨1807322, by rfl⟩ : syracuseStep 2409763 = 3614645) B3614645
theorem B1606963 : Blo 1427533 1606963 := bstep (se 1 (by rfl) ⟨1205222, by rfl⟩ : syracuseStep 1606963 = 2410445) B2410445
theorem B4818257 : Blo 1427533 4818257 := bstep (se 2 (by rfl) ⟨1806846, by rfl⟩ : syracuseStep 4818257 = 3613693) B3613693
theorem B3212657 : Blo 1427533 3212657 := bstep (se 2 (by rfl) ⟨1204746, by rfl⟩ : syracuseStep 3212657 = 2409493) B2409493
theorem B3859825 : Blo 1427533 3859825 := bstep (se 2 (by rfl) ⟨1447434, by rfl⟩ : syracuseStep 3859825 = 2894869) B2894869
theorem B3212675 : Blo 1427533 3212675 := bstep (se 1 (by rfl) ⟨2409506, by rfl⟩ : syracuseStep 3212675 = 4819013) B4819013
theorem B3433859 : Blo 1427533 3433859 := bstep (se 1 (by rfl) ⟨2575394, by rfl⟩ : syracuseStep 3433859 = 5150789) B5150789
theorem B2319779 : Blo 1427533 2319779 := bstep (se 1 (by rfl) ⟨1739834, by rfl⟩ : syracuseStep 2319779 = 3479669) B3479669
theorem B3614129 : Blo 1427533 3614129 := bstep (se 2 (by rfl) ⟨1355298, by rfl⟩ : syracuseStep 3614129 = 2710597) B2710597
theorem B2409905 : Blo 1427533 2409905 := bstep (se 2 (by rfl) ⟨903714, by rfl⟩ : syracuseStep 2409905 = 1807429) B1807429
theorem B1607107 : Blo 1427533 1607107 := bstep (se 1 (by rfl) ⟨1205330, by rfl⟩ : syracuseStep 1607107 = 2410661) B2410661
theorem B2713027 : Blo 1427533 2713027 := bstep (se 1 (by rfl) ⟨2034770, by rfl⟩ : syracuseStep 2713027 = 4069541) B4069541
theorem B3614179 : Blo 1427533 3614179 := bstep (se 1 (by rfl) ⟨2710634, by rfl⟩ : syracuseStep 3614179 = 5421269) B5421269
theorem B2410033 : Blo 1427533 2410033 := bstep (se 2 (by rfl) ⟨903762, by rfl⟩ : syracuseStep 2410033 = 1807525) B1807525
theorem B2410067 : Blo 1427533 2410067 := bstep (se 1 (by rfl) ⟨1807550, by rfl⟩ : syracuseStep 2410067 = 3615101) B3615101
theorem B1607251 : Blo 1427533 1607251 := bstep (se 1 (by rfl) ⟨1205438, by rfl⟩ : syracuseStep 1607251 = 2410877) B2410877
theorem B3614321 : Blo 1427533 3614321 := bstep (se 2 (by rfl) ⟨1355370, by rfl⟩ : syracuseStep 3614321 = 2710741) B2710741
theorem B3212945 : Blo 1427533 3212945 := bstep (se 2 (by rfl) ⟨1204854, by rfl⟩ : syracuseStep 3212945 = 2409709) B2409709
theorem B3049123 : Blo 1427533 3049123 := bstep (se 1 (by rfl) ⟨2286842, by rfl⟩ : syracuseStep 3049123 = 4573685) B4573685
theorem B3212963 : Blo 1427533 3212963 := bstep (se 1 (by rfl) ⟨2409722, by rfl⟩ : syracuseStep 3212963 = 4819445) B4819445
theorem B3434147 : Blo 1427533 3434147 := bstep (se 1 (by rfl) ⟨2575610, by rfl⟩ : syracuseStep 3434147 = 5151221) B5151221
theorem B4343473 : Blo 1427533 4343473 := bstep (se 2 (by rfl) ⟨1628802, by rfl⟩ : syracuseStep 4343473 = 3257605) B3257605
theorem B2410195 : Blo 1427533 2410195 := bstep (se 1 (by rfl) ⟨1807646, by rfl⟩ : syracuseStep 2410195 = 3615293) B3615293
theorem B1607395 : Blo 1427533 1607395 := bstep (se 1 (by rfl) ⟨1205546, by rfl⟩ : syracuseStep 1607395 = 2411093) B2411093
theorem B3860291 : Blo 1427533 3860291 := bstep (se 1 (by rfl) ⟨2895218, by rfl⟩ : syracuseStep 3860291 = 5790437) B5790437
theorem B7235405 : Blo 1427533 7235405 := bstep (se 3 (by rfl) ⟨1356638, by rfl⟩ : syracuseStep 7235405 = 2713277) B2713277
theorem B6104909 : Blo 1427533 6104909 := bstep (se 3 (by rfl) ⟨1144670, by rfl⟩ : syracuseStep 6104909 = 2289341) B2289341
theorem B2410337 : Blo 1427533 2410337 := bstep (se 2 (by rfl) ⟨903876, by rfl⟩ : syracuseStep 2410337 = 1807753) B1807753
theorem B3434339 : Blo 1427533 3434339 := bstep (se 1 (by rfl) ⟨2575754, by rfl⟩ : syracuseStep 3434339 = 5151509) B5151509
theorem B4818797 : Blo 1427533 4818797 := bstep (se 3 (by rfl) ⟨903524, by rfl⟩ : syracuseStep 4818797 = 1807049) B1807049
theorem B1607539 : Blo 1427533 1607539 := bstep (se 1 (by rfl) ⟨1205654, by rfl⟩ : syracuseStep 1607539 = 2411309) B2411309
theorem B2713475 : Blo 1427533 2713475 := bstep (se 1 (by rfl) ⟨2035106, by rfl⟩ : syracuseStep 2713475 = 4070213) B4070213
theorem B39118733 : Blo 1427533 39118733 := bstep (se 3 (by rfl) ⟨7334762, by rfl⟩ : syracuseStep 39118733 = 14669525) B14669525
theorem B4818851 : Blo 1427533 4818851 := bstep (se 1 (by rfl) ⟨3614138, by rfl⟩ : syracuseStep 4818851 = 7228277) B7228277
theorem B3860387 : Blo 1427533 3860387 := bstep (se 1 (by rfl) ⟨2895290, by rfl⟩ : syracuseStep 3860387 = 5790581) B5790581
theorem B3213233 : Blo 1427533 3213233 := bstep (se 2 (by rfl) ⟨1204962, by rfl⟩ : syracuseStep 3213233 = 2409925) B2409925
theorem B3213251 : Blo 1427533 3213251 := bstep (se 1 (by rfl) ⟨2409938, by rfl⟩ : syracuseStep 3213251 = 4819877) B4819877
theorem B2287585 : Blo 1427533 2287585 := bstep (se 2 (by rfl) ⟨857844, by rfl⟩ : syracuseStep 2287585 = 1715689) B1715689
theorem B2410465 : Blo 1427533 2410465 := bstep (se 2 (by rfl) ⟨903924, by rfl⟩ : syracuseStep 2410465 = 1807849) B1807849
theorem B2410499 : Blo 1427533 2410499 := bstep (se 1 (by rfl) ⟨1807874, by rfl⟩ : syracuseStep 2410499 = 3615749) B3615749
theorem B1607683 : Blo 1427533 1607683 := bstep (se 1 (by rfl) ⟨1205762, by rfl⟩ : syracuseStep 1607683 = 2411525) B2411525
theorem B2172977 : Blo 1427533 2172977 := bstep (se 2 (by rfl) ⟨814866, by rfl⟩ : syracuseStep 2172977 = 1629733) B1629733
theorem B1427539 : Blo 1427533 1427539 := bstep (se 1 (by rfl) ⟨1070654, by rfl⟩ : syracuseStep 1427539 = 2141309) B2141309
theorem B2173025 : Blo 1427533 2173025 := bstep (se 2 (by rfl) ⟨814884, by rfl⟩ : syracuseStep 2173025 = 1629769) B1629769
theorem B1427555 : Blo 1427533 1427555 := bstep (se 1 (by rfl) ⟨1070666, by rfl⟩ : syracuseStep 1427555 = 2141333) B2141333
theorem B1427571 : Blo 1427533 1427571 := bstep (se 1 (by rfl) ⟨1070678, by rfl⟩ : syracuseStep 1427571 = 2141357) B2141357
theorem B1427587 : Blo 1427533 1427587 := bstep (se 1 (by rfl) ⟨1070690, by rfl⟩ : syracuseStep 1427587 = 2141381) B2141381
theorem B2410627 : Blo 1427533 2410627 := bstep (se 1 (by rfl) ⟨1807970, by rfl⟩ : syracuseStep 2410627 = 3615941) B3615941
theorem B32966797 : Blo 1427533 32966797 := bstep (se 3 (by rfl) ⟨6181274, by rfl⟩ : syracuseStep 32966797 = 12362549) B12362549
theorem B1427603 : Blo 1427533 1427603 := bstep (se 1 (by rfl) ⟨1070702, by rfl⟩ : syracuseStep 1427603 = 2141405) B2141405
theorem B1607827 : Blo 1427533 1607827 := bstep (se 1 (by rfl) ⟨1205870, by rfl⟩ : syracuseStep 1607827 = 2411741) B2411741
theorem B1427619 : Blo 1427533 1427619 := bstep (se 1 (by rfl) ⟨1070714, by rfl⟩ : syracuseStep 1427619 = 2141429) B2141429
theorem B2713763 : Blo 1427533 2713763 := bstep (se 1 (by rfl) ⟨2035322, by rfl⟩ : syracuseStep 2713763 = 4070645) B4070645
theorem B4819121 : Blo 1427533 4819121 := bstep (se 2 (by rfl) ⟨1807170, by rfl⟩ : syracuseStep 4819121 = 3614341) B3614341
theorem B1427635 : Blo 1427533 1427635 := bstep (se 1 (by rfl) ⟨1070726, by rfl⟩ : syracuseStep 1427635 = 2141453) B2141453
theorem B1427651 : Blo 1427533 1427651 := bstep (se 1 (by rfl) ⟨1070738, by rfl⟩ : syracuseStep 1427651 = 2141477) B2141477
theorem B3213521 : Blo 1427533 3213521 := bstep (se 2 (by rfl) ⟨1205070, by rfl⟩ : syracuseStep 3213521 = 2410141) B2410141
theorem B1427667 : Blo 1427533 1427667 := bstep (se 1 (by rfl) ⟨1070750, by rfl⟩ : syracuseStep 1427667 = 2141501) B2141501
theorem B69552341 : Blo 1427533 69552341 := bstep (se 7 (by rfl) ⟨815066, by rfl⟩ : syracuseStep 69552341 = 1630133) B1630133
theorem B2894051 : Blo 1427533 2894051 := bstep (se 1 (by rfl) ⟨2170538, by rfl⟩ : syracuseStep 2894051 = 4341077) B4341077
theorem B1427683 : Blo 1427533 1427683 := bstep (se 1 (by rfl) ⟨1070762, by rfl⟩ : syracuseStep 1427683 = 2141525) B2141525
theorem B3213539 : Blo 1427533 3213539 := bstep (se 1 (by rfl) ⟨2410154, by rfl⟩ : syracuseStep 3213539 = 4820309) B4820309
theorem B2033905 : Blo 1427533 2033905 := bstep (se 2 (by rfl) ⟨762714, by rfl⟩ : syracuseStep 2033905 = 1525429) B1525429
theorem B1427699 : Blo 1427533 1427699 := bstep (se 1 (by rfl) ⟨1070774, by rfl⟩ : syracuseStep 1427699 = 2141549) B2141549
theorem B1427715 : Blo 1427533 1427715 := bstep (se 1 (by rfl) ⟨1070786, by rfl⟩ : syracuseStep 1427715 = 2141573) B2141573
theorem B18303245 : Blo 1427533 18303245 := bstep (se 3 (by rfl) ⟨3431858, by rfl⟩ : syracuseStep 18303245 = 6863717) B6863717
theorem B2410769 : Blo 1427533 2410769 := bstep (se 2 (by rfl) ⟨904038, by rfl⟩ : syracuseStep 2410769 = 1808077) B1808077
theorem B1427731 : Blo 1427533 1427731 := bstep (se 1 (by rfl) ⟨1070798, by rfl⟩ : syracuseStep 1427731 = 2141597) B2141597
theorem B1427747 : Blo 1427533 1427747 := bstep (se 1 (by rfl) ⟨1070810, by rfl⟩ : syracuseStep 1427747 = 2141621) B2141621
theorem B1607971 : Blo 1427533 1607971 := bstep (se 1 (by rfl) ⟨1205978, by rfl⟩ : syracuseStep 1607971 = 2411957) B2411957
theorem B1427763 : Blo 1427533 1427763 := bstep (se 1 (by rfl) ⟨1070822, by rfl⟩ : syracuseStep 1427763 = 2141645) B2141645
theorem B35227957 : Blo 1427533 35227957 := bstep (se 5 (by rfl) ⟨1651310, by rfl⟩ : syracuseStep 35227957 = 3302621) B3302621
theorem B1427779 : Blo 1427533 1427779 := bstep (se 1 (by rfl) ⟨1070834, by rfl⟩ : syracuseStep 1427779 = 2141669) B2141669
theorem B2034001 : Blo 1427533 2034001 := bstep (se 2 (by rfl) ⟨762750, by rfl⟩ : syracuseStep 2034001 = 1525501) B1525501
theorem B1427795 : Blo 1427533 1427795 := bstep (se 1 (by rfl) ⟨1070846, by rfl⟩ : syracuseStep 1427795 = 2141693) B2141693
theorem B1526099 : Blo 1427533 1526099 := bstep (se 1 (by rfl) ⟨1144574, by rfl⟩ : syracuseStep 1526099 = 2289149) B2289149
theorem B1427811 : Blo 1427533 1427811 := bstep (se 1 (by rfl) ⟨1070858, by rfl⟩ : syracuseStep 1427811 = 2141717) B2141717
theorem B1427827 : Blo 1427533 1427827 := bstep (se 1 (by rfl) ⟨1070870, by rfl⟩ : syracuseStep 1427827 = 2141741) B2141741
theorem B1427843 : Blo 1427533 1427843 := bstep (se 1 (by rfl) ⟨1070882, by rfl⟩ : syracuseStep 1427843 = 2141765) B2141765
theorem B9275789 : Blo 1427533 9275789 := bstep (se 3 (by rfl) ⟨1739210, by rfl⟩ : syracuseStep 9275789 = 3478421) B3478421
theorem B2410897 : Blo 1427533 2410897 := bstep (se 2 (by rfl) ⟨904086, by rfl⟩ : syracuseStep 2410897 = 1808173) B1808173
theorem B1427859 : Blo 1427533 1427859 := bstep (se 1 (by rfl) ⟨1070894, by rfl⟩ : syracuseStep 1427859 = 2141789) B2141789
theorem B1427875 : Blo 1427533 1427875 := bstep (se 1 (by rfl) ⟨1070906, by rfl⟩ : syracuseStep 1427875 = 2141813) B2141813
theorem B1427891 : Blo 1427533 1427891 := bstep (se 1 (by rfl) ⟨1070918, by rfl⟩ : syracuseStep 1427891 = 2141837) B2141837
theorem B2410931 : Blo 1427533 2410931 := bstep (se 1 (by rfl) ⟨1808198, by rfl⟩ : syracuseStep 2410931 = 3616397) B3616397
theorem B1608115 : Blo 1427533 1608115 := bstep (se 1 (by rfl) ⟨1206086, by rfl⟩ : syracuseStep 1608115 = 2412173) B2412173
theorem B1427907 : Blo 1427533 1427907 := bstep (se 1 (by rfl) ⟨1070930, by rfl⟩ : syracuseStep 1427907 = 2141861) B2141861
theorem B5425613 : Blo 1427533 5425613 := bstep (se 3 (by rfl) ⟨1017302, by rfl⟩ : syracuseStep 5425613 = 2034605) B2034605
theorem B1427923 : Blo 1427533 1427923 := bstep (se 1 (by rfl) ⟨1070942, by rfl⟩ : syracuseStep 1427923 = 2141885) B2141885
theorem B1427939 : Blo 1427533 1427939 := bstep (se 1 (by rfl) ⟨1070954, by rfl⟩ : syracuseStep 1427939 = 2141909) B2141909
theorem B3049969 : Blo 1427533 3049969 := bstep (se 2 (by rfl) ⟨1143738, by rfl⟩ : syracuseStep 3049969 = 2287477) B2287477
theorem B3213809 : Blo 1427533 3213809 := bstep (se 2 (by rfl) ⟨1205178, by rfl⟩ : syracuseStep 3213809 = 2410357) B2410357
theorem B1427955 : Blo 1427533 1427955 := bstep (se 1 (by rfl) ⟨1070966, by rfl⟩ : syracuseStep 1427955 = 2141933) B2141933
theorem B1427971 : Blo 1427533 1427971 := bstep (se 1 (by rfl) ⟨1070978, by rfl⟩ : syracuseStep 1427971 = 2141957) B2141957
theorem B3213827 : Blo 1427533 3213827 := bstep (se 1 (by rfl) ⟨2410370, by rfl⟩ : syracuseStep 3213827 = 4820741) B4820741
theorem B1427987 : Blo 1427533 1427987 := bstep (se 1 (by rfl) ⟨1070990, by rfl⟩ : syracuseStep 1427987 = 2141981) B2141981
theorem B1428003 : Blo 1427533 1428003 := bstep (se 1 (by rfl) ⟨1071002, by rfl⟩ : syracuseStep 1428003 = 2142005) B2142005
theorem B4885037 : Blo 1427533 4885037 := bstep (se 3 (by rfl) ⟨915944, by rfl⟩ : syracuseStep 4885037 = 1831889) B1831889
theorem B7227953 : Blo 1427533 7227953 := bstep (se 2 (by rfl) ⟨2710482, by rfl⟩ : syracuseStep 7227953 = 5420965) B5420965
theorem B1428019 : Blo 1427533 1428019 := bstep (se 1 (by rfl) ⟨1071014, by rfl⟩ : syracuseStep 1428019 = 2142029) B2142029
theorem B2411059 : Blo 1427533 2411059 := bstep (se 1 (by rfl) ⟨1808294, by rfl⟩ : syracuseStep 2411059 = 3616589) B3616589
theorem B1428035 : Blo 1427533 1428035 := bstep (se 1 (by rfl) ⟨1071026, by rfl⟩ : syracuseStep 1428035 = 2142053) B2142053
theorem B3615313 : Blo 1427533 3615313 := bstep (se 2 (by rfl) ⟨1355742, by rfl⟩ : syracuseStep 3615313 = 2711485) B2711485
theorem B1428051 : Blo 1427533 1428051 := bstep (se 1 (by rfl) ⟨1071038, by rfl⟩ : syracuseStep 1428051 = 2142077) B2142077
theorem B1428067 : Blo 1427533 1428067 := bstep (se 1 (by rfl) ⟨1071050, by rfl⟩ : syracuseStep 1428067 = 2142101) B2142101
theorem B22276721 : Blo 1427533 22276721 := bstep (se 2 (by rfl) ⟨8353770, by rfl⟩ : syracuseStep 22276721 = 16707541) B16707541
theorem B1428083 : Blo 1427533 1428083 := bstep (se 1 (by rfl) ⟨1071062, by rfl⟩ : syracuseStep 1428083 = 2142125) B2142125
theorem B1428099 : Blo 1427533 1428099 := bstep (se 1 (by rfl) ⟨1071074, by rfl⟩ : syracuseStep 1428099 = 2142149) B2142149
theorem B4573837 : Blo 1427533 4573837 := bstep (se 3 (by rfl) ⟨857594, by rfl⟩ : syracuseStep 4573837 = 1715189) B1715189
theorem B1428115 : Blo 1427533 1428115 := bstep (se 1 (by rfl) ⟨1071086, by rfl⟩ : syracuseStep 1428115 = 2142173) B2142173
theorem B1428131 : Blo 1427533 1428131 := bstep (se 1 (by rfl) ⟨1071098, by rfl⟩ : syracuseStep 1428131 = 2142197) B2142197
theorem B1428147 : Blo 1427533 1428147 := bstep (se 1 (by rfl) ⟨1071110, by rfl⟩ : syracuseStep 1428147 = 2142221) B2142221
theorem B1428163 : Blo 1427533 1428163 := bstep (se 1 (by rfl) ⟨1071122, by rfl⟩ : syracuseStep 1428163 = 2142245) B2142245
theorem B2411201 : Blo 1427533 2411201 := bstep (se 2 (by rfl) ⟨904200, by rfl⟩ : syracuseStep 2411201 = 1808401) B1808401
theorem B21146309 : Blo 1427533 21146309 := bstep (se 4 (by rfl) ⟨1982466, by rfl⟩ : syracuseStep 21146309 = 3964933) B3964933
theorem B4819661 : Blo 1427533 4819661 := bstep (se 3 (by rfl) ⟨903686, by rfl⟩ : syracuseStep 4819661 = 1807373) B1807373
theorem B1428179 : Blo 1427533 1428179 := bstep (se 1 (by rfl) ⟨1071134, by rfl⟩ : syracuseStep 1428179 = 2142269) B2142269
theorem B1428195 : Blo 1427533 1428195 := bstep (se 1 (by rfl) ⟨1071146, by rfl⟩ : syracuseStep 1428195 = 2142293) B2142293
theorem B1428211 : Blo 1427533 1428211 := bstep (se 1 (by rfl) ⟨1071158, by rfl⟩ : syracuseStep 1428211 = 2142317) B2142317
theorem B4819715 : Blo 1427533 4819715 := bstep (se 1 (by rfl) ⟨3614786, by rfl⟩ : syracuseStep 4819715 = 7229573) B7229573
theorem B1428227 : Blo 1427533 1428227 := bstep (se 1 (by rfl) ⟨1071170, by rfl⟩ : syracuseStep 1428227 = 2142341) B2142341
theorem B3861251 : Blo 1427533 3861251 := bstep (se 1 (by rfl) ⟨2895938, by rfl⟩ : syracuseStep 3861251 = 5791877) B5791877
theorem B3214097 : Blo 1427533 3214097 := bstep (se 2 (by rfl) ⟨1205286, by rfl⟩ : syracuseStep 3214097 = 2410573) B2410573
theorem B1428243 : Blo 1427533 1428243 := bstep (se 1 (by rfl) ⟨1071182, by rfl⟩ : syracuseStep 1428243 = 2142365) B2142365
theorem B93940501 : Blo 1427533 93940501 := bstep (se 6 (by rfl) ⟨2201730, by rfl⟩ : syracuseStep 93940501 = 4403461) B4403461
theorem B1428259 : Blo 1427533 1428259 := bstep (se 1 (by rfl) ⟨1071194, by rfl⟩ : syracuseStep 1428259 = 2142389) B2142389
theorem B3214115 : Blo 1427533 3214115 := bstep (se 1 (by rfl) ⟨2410586, by rfl⟩ : syracuseStep 3214115 = 4821173) B4821173
theorem B1428275 : Blo 1427533 1428275 := bstep (se 1 (by rfl) ⟨1071206, by rfl⟩ : syracuseStep 1428275 = 2142413) B2142413
theorem B16263989 : Blo 1427533 16263989 := bstep (se 5 (by rfl) ⟨762374, by rfl⟩ : syracuseStep 16263989 = 1524749) B1524749
theorem B2034497 : Blo 1427533 2034497 := bstep (se 2 (by rfl) ⟨762936, by rfl⟩ : syracuseStep 2034497 = 1525873) B1525873
theorem B2411329 : Blo 1427533 2411329 := bstep (se 2 (by rfl) ⟨904248, by rfl⟩ : syracuseStep 2411329 = 1808497) B1808497
theorem B1428291 : Blo 1427533 1428291 := bstep (se 1 (by rfl) ⟨1071218, by rfl⟩ : syracuseStep 1428291 = 2142437) B2142437
theorem B1428307 : Blo 1427533 1428307 := bstep (se 1 (by rfl) ⟨1071230, by rfl⟩ : syracuseStep 1428307 = 2142461) B2142461
theorem B1428323 : Blo 1427533 1428323 := bstep (se 1 (by rfl) ⟨1071242, by rfl⟩ : syracuseStep 1428323 = 2142485) B2142485
theorem B3615587 : Blo 1427533 3615587 := bstep (se 1 (by rfl) ⟨2711690, by rfl⟩ : syracuseStep 3615587 = 5423381) B5423381
theorem B2288483 : Blo 1427533 2288483 := bstep (se 1 (by rfl) ⟨1716362, by rfl⟩ : syracuseStep 2288483 = 3432725) B3432725
theorem B2411363 : Blo 1427533 2411363 := bstep (se 1 (by rfl) ⟨1808522, by rfl⟩ : syracuseStep 2411363 = 3617045) B3617045
theorem B1428339 : Blo 1427533 1428339 := bstep (se 1 (by rfl) ⟨1071254, by rfl⟩ : syracuseStep 1428339 = 2142509) B2142509
theorem B2444161 : Blo 1427533 2444161 := bstep (se 2 (by rfl) ⟨916560, by rfl⟩ : syracuseStep 2444161 = 1833121) B1833121
theorem B1428355 : Blo 1427533 1428355 := bstep (se 1 (by rfl) ⟨1071266, by rfl⟩ : syracuseStep 1428355 = 2142533) B2142533
theorem B1428371 : Blo 1427533 1428371 := bstep (se 1 (by rfl) ⟨1071278, by rfl⟩ : syracuseStep 1428371 = 2142557) B2142557
theorem B1428387 : Blo 1427533 1428387 := bstep (se 1 (by rfl) ⟨1071290, by rfl⟩ : syracuseStep 1428387 = 2142581) B2142581
theorem B1428403 : Blo 1427533 1428403 := bstep (se 1 (by rfl) ⟨1071302, by rfl⟩ : syracuseStep 1428403 = 2142605) B2142605
theorem B1428419 : Blo 1427533 1428419 := bstep (se 1 (by rfl) ⟨1071314, by rfl⟩ : syracuseStep 1428419 = 2142629) B2142629
theorem B1428435 : Blo 1427533 1428435 := bstep (se 1 (by rfl) ⟨1071326, by rfl⟩ : syracuseStep 1428435 = 2142653) B2142653
theorem B1428451 : Blo 1427533 1428451 := bstep (se 1 (by rfl) ⟨1071338, by rfl⟩ : syracuseStep 1428451 = 2142677) B2142677
theorem B2411491 : Blo 1427533 2411491 := bstep (se 1 (by rfl) ⟨1808618, by rfl⟩ : syracuseStep 2411491 = 3617237) B3617237
theorem B1428467 : Blo 1427533 1428467 := bstep (se 1 (by rfl) ⟨1071350, by rfl⟩ : syracuseStep 1428467 = 2142701) B2142701
theorem B1428483 : Blo 1427533 1428483 := bstep (se 1 (by rfl) ⟨1071362, by rfl⟩ : syracuseStep 1428483 = 2142725) B2142725
theorem B4344835 : Blo 1427533 4344835 := bstep (se 1 (by rfl) ⟨3258626, by rfl⟩ : syracuseStep 4344835 = 6517253) B6517253
theorem B4819985 : Blo 1427533 4819985 := bstep (se 2 (by rfl) ⟨1807494, by rfl⟩ : syracuseStep 4819985 = 3614989) B3614989
theorem B1428499 : Blo 1427533 1428499 := bstep (se 1 (by rfl) ⟨1071374, by rfl⟩ : syracuseStep 1428499 = 2142749) B2142749
theorem B3615779 : Blo 1427533 3615779 := bstep (se 1 (by rfl) ⟨2711834, by rfl⟩ : syracuseStep 3615779 = 5423669) B5423669
theorem B1428515 : Blo 1427533 1428515 := bstep (se 1 (by rfl) ⟨1071386, by rfl⟩ : syracuseStep 1428515 = 2142773) B2142773
theorem B2288675 : Blo 1427533 2288675 := bstep (se 1 (by rfl) ⟨1716506, by rfl⟩ : syracuseStep 2288675 = 3433013) B3433013
theorem B3214385 : Blo 1427533 3214385 := bstep (se 2 (by rfl) ⟨1205394, by rfl⟩ : syracuseStep 3214385 = 2410789) B2410789
theorem B1428531 : Blo 1427533 1428531 := bstep (se 1 (by rfl) ⟨1071398, by rfl⟩ : syracuseStep 1428531 = 2142797) B2142797
theorem B1428547 : Blo 1427533 1428547 := bstep (se 1 (by rfl) ⟨1071410, by rfl⟩ : syracuseStep 1428547 = 2142821) B2142821
theorem B3214403 : Blo 1427533 3214403 := bstep (se 1 (by rfl) ⟨2410802, by rfl⟩ : syracuseStep 3214403 = 4821605) B4821605
theorem B19557445 : Blo 1427533 19557445 := bstep (se 4 (by rfl) ⟨1833510, by rfl⟩ : syracuseStep 19557445 = 3667021) B3667021
theorem B1428563 : Blo 1427533 1428563 := bstep (se 1 (by rfl) ⟨1071422, by rfl⟩ : syracuseStep 1428563 = 2142845) B2142845
theorem B1428579 : Blo 1427533 1428579 := bstep (se 1 (by rfl) ⟨1071434, by rfl⟩ : syracuseStep 1428579 = 2142869) B2142869
theorem B10841201 : Blo 1427533 10841201 := bstep (se 2 (by rfl) ⟨4065450, by rfl⟩ : syracuseStep 10841201 = 8130901) B8130901
theorem B2411633 : Blo 1427533 2411633 := bstep (se 2 (by rfl) ⟨904362, by rfl⟩ : syracuseStep 2411633 = 1808725) B1808725
theorem B1428595 : Blo 1427533 1428595 := bstep (se 1 (by rfl) ⟨1071446, by rfl⟩ : syracuseStep 1428595 = 2142893) B2142893
theorem B6106225 : Blo 1427533 6106225 := bstep (se 2 (by rfl) ⟨2289834, by rfl⟩ : syracuseStep 6106225 = 4579669) B4579669
theorem B2141315 : Blo 1427533 2141315 := bstep (se 1 (by rfl) ⟨1605986, by rfl⟩ : syracuseStep 2141315 = 3211973) B3211973
theorem B4574339 : Blo 1427533 4574339 := bstep (se 1 (by rfl) ⟨3430754, by rfl⟩ : syracuseStep 4574339 = 6861509) B6861509
theorem B1428611 : Blo 1427533 1428611 := bstep (se 1 (by rfl) ⟨1071458, by rfl⟩ : syracuseStep 1428611 = 2142917) B2142917
theorem B1428627 : Blo 1427533 1428627 := bstep (se 1 (by rfl) ⟨1071470, by rfl⟩ : syracuseStep 1428627 = 2142941) B2142941
theorem B2141345 : Blo 1427533 2141345 := bstep (se 2 (by rfl) ⟨803004, by rfl⟩ : syracuseStep 2141345 = 1606009) B1606009
theorem B1428643 : Blo 1427533 1428643 := bstep (se 1 (by rfl) ⟨1071482, by rfl⟩ : syracuseStep 1428643 = 2142965) B2142965
theorem B2575523 : Blo 1427533 2575523 := bstep (se 1 (by rfl) ⟨1931642, by rfl⟩ : syracuseStep 2575523 = 3863285) B3863285
theorem B2141363 : Blo 1427533 2141363 := bstep (se 1 (by rfl) ⟨1606022, by rfl⟩ : syracuseStep 2141363 = 3212045) B3212045
theorem B1428659 : Blo 1427533 1428659 := bstep (se 1 (by rfl) ⟨1071494, by rfl⟩ : syracuseStep 1428659 = 2142989) B2142989
theorem B4066499 : Blo 1427533 4066499 := bstep (se 1 (by rfl) ⟨3049874, by rfl⟩ : syracuseStep 4066499 = 6099749) B6099749
theorem B1428675 : Blo 1427533 1428675 := bstep (se 1 (by rfl) ⟨1071506, by rfl⟩ : syracuseStep 1428675 = 2143013) B2143013
theorem B2141393 : Blo 1427533 2141393 := bstep (se 2 (by rfl) ⟨803022, by rfl⟩ : syracuseStep 2141393 = 1606045) B1606045
theorem B1428691 : Blo 1427533 1428691 := bstep (se 1 (by rfl) ⟨1071518, by rfl⟩ : syracuseStep 1428691 = 2143037) B2143037
theorem B2141411 : Blo 1427533 2141411 := bstep (se 1 (by rfl) ⟨1606058, by rfl⟩ : syracuseStep 2141411 = 3212117) B3212117
theorem B2608355 : Blo 1427533 2608355 := bstep (se 1 (by rfl) ⟨1956266, by rfl⟩ : syracuseStep 2608355 = 3912533) B3912533
theorem B1428707 : Blo 1427533 1428707 := bstep (se 1 (by rfl) ⟨1071530, by rfl⟩ : syracuseStep 1428707 = 2143061) B2143061
theorem B2411761 : Blo 1427533 2411761 := bstep (se 2 (by rfl) ⟨904410, by rfl⟩ : syracuseStep 2411761 = 1808821) B1808821
theorem B1428723 : Blo 1427533 1428723 := bstep (se 1 (by rfl) ⟨1071542, by rfl⟩ : syracuseStep 1428723 = 2143085) B2143085
theorem B2141441 : Blo 1427533 2141441 := bstep (se 2 (by rfl) ⟨803040, by rfl⟩ : syracuseStep 2141441 = 1606081) B1606081
theorem B1428739 : Blo 1427533 1428739 := bstep (se 1 (by rfl) ⟨1071554, by rfl⟩ : syracuseStep 1428739 = 2143109) B2143109
theorem B2141459 : Blo 1427533 2141459 := bstep (se 1 (by rfl) ⟨1606094, by rfl⟩ : syracuseStep 2141459 = 3212189) B3212189
theorem B1428755 : Blo 1427533 1428755 := bstep (se 1 (by rfl) ⟨1071566, by rfl⟩ : syracuseStep 1428755 = 2143133) B2143133
theorem B2411795 : Blo 1427533 2411795 := bstep (se 1 (by rfl) ⟨1808846, by rfl⟩ : syracuseStep 2411795 = 3617693) B3617693
theorem B1428771 : Blo 1427533 1428771 := bstep (se 1 (by rfl) ⟨1071578, by rfl⟩ : syracuseStep 1428771 = 2143157) B2143157
theorem B2141489 : Blo 1427533 2141489 := bstep (se 2 (by rfl) ⟨803058, by rfl⟩ : syracuseStep 2141489 = 1606117) B1606117
theorem B2444593 : Blo 1427533 2444593 := bstep (se 2 (by rfl) ⟨916722, by rfl⟩ : syracuseStep 2444593 = 1833445) B1833445
theorem B1428787 : Blo 1427533 1428787 := bstep (se 1 (by rfl) ⟨1071590, by rfl⟩ : syracuseStep 1428787 = 2143181) B2143181
theorem B2141507 : Blo 1427533 2141507 := bstep (se 1 (by rfl) ⟨1606130, by rfl⟩ : syracuseStep 2141507 = 3212261) B3212261
theorem B1428803 : Blo 1427533 1428803 := bstep (se 1 (by rfl) ⟨1071602, by rfl⟩ : syracuseStep 1428803 = 2143205) B2143205
theorem B3214673 : Blo 1427533 3214673 := bstep (se 2 (by rfl) ⟨1205502, by rfl⟩ : syracuseStep 3214673 = 2411005) B2411005
theorem B1428819 : Blo 1427533 1428819 := bstep (se 1 (by rfl) ⟨1071614, by rfl⟩ : syracuseStep 1428819 = 2143229) B2143229
theorem B2141537 : Blo 1427533 2141537 := bstep (se 2 (by rfl) ⟨803076, by rfl⟩ : syracuseStep 2141537 = 1606153) B1606153
theorem B3214691 : Blo 1427533 3214691 := bstep (se 1 (by rfl) ⟨2411018, by rfl⟩ : syracuseStep 3214691 = 4822037) B4822037
theorem B1428835 : Blo 1427533 1428835 := bstep (se 1 (by rfl) ⟨1071626, by rfl⟩ : syracuseStep 1428835 = 2143253) B2143253
theorem B2141555 : Blo 1427533 2141555 := bstep (se 1 (by rfl) ⟨1606166, by rfl⟩ : syracuseStep 2141555 = 3212333) B3212333
theorem B1428851 : Blo 1427533 1428851 := bstep (se 1 (by rfl) ⟨1071638, by rfl⟩ : syracuseStep 1428851 = 2143277) B2143277
theorem B1428867 : Blo 1427533 1428867 := bstep (se 1 (by rfl) ⟨1071650, by rfl⟩ : syracuseStep 1428867 = 2143301) B2143301
theorem B2141585 : Blo 1427533 2141585 := bstep (se 2 (by rfl) ⟨803094, by rfl⟩ : syracuseStep 2141585 = 1606189) B1606189
theorem B1428883 : Blo 1427533 1428883 := bstep (se 1 (by rfl) ⟨1071662, by rfl⟩ : syracuseStep 1428883 = 2143325) B2143325
theorem B2411923 : Blo 1427533 2411923 := bstep (se 1 (by rfl) ⟨1808942, by rfl⟩ : syracuseStep 2411923 = 3617885) B3617885
theorem B2141603 : Blo 1427533 2141603 := bstep (se 1 (by rfl) ⟨1606202, by rfl⟩ : syracuseStep 2141603 = 3212405) B3212405
theorem B1428899 : Blo 1427533 1428899 := bstep (se 1 (by rfl) ⟨1071674, by rfl⟩ : syracuseStep 1428899 = 2143349) B2143349
theorem B1428915 : Blo 1427533 1428915 := bstep (se 1 (by rfl) ⟨1071686, by rfl⟩ : syracuseStep 1428915 = 2143373) B2143373
theorem B2141633 : Blo 1427533 2141633 := bstep (se 2 (by rfl) ⟨803112, by rfl⟩ : syracuseStep 2141633 = 1606225) B1606225
theorem B1428931 : Blo 1427533 1428931 := bstep (se 1 (by rfl) ⟨1071698, by rfl⟩ : syracuseStep 1428931 = 2143397) B2143397
theorem B2141651 : Blo 1427533 2141651 := bstep (se 1 (by rfl) ⟨1606238, by rfl⟩ : syracuseStep 2141651 = 3212477) B3212477
theorem B1428947 : Blo 1427533 1428947 := bstep (se 1 (by rfl) ⟨1071710, by rfl⟩ : syracuseStep 1428947 = 2143421) B2143421
theorem B1428963 : Blo 1427533 1428963 := bstep (se 1 (by rfl) ⟨1071722, by rfl⟩ : syracuseStep 1428963 = 2143445) B2143445
theorem B2141681 : Blo 1427533 2141681 := bstep (se 2 (by rfl) ⟨803130, by rfl⟩ : syracuseStep 2141681 = 1606261) B1606261
theorem B1715699 : Blo 1427533 1715699 := bstep (se 1 (by rfl) ⟨1286774, by rfl⟩ : syracuseStep 1715699 = 2573549) B2573549
theorem B1428979 : Blo 1427533 1428979 := bstep (se 1 (by rfl) ⟨1071734, by rfl⟩ : syracuseStep 1428979 = 2143469) B2143469
theorem B2141699 : Blo 1427533 2141699 := bstep (se 1 (by rfl) ⟨1606274, by rfl⟩ : syracuseStep 2141699 = 3212549) B3212549
theorem B1428995 : Blo 1427533 1428995 := bstep (se 1 (by rfl) ⟨1071746, by rfl⟩ : syracuseStep 1428995 = 2143493) B2143493
theorem B1429011 : Blo 1427533 1429011 := bstep (se 1 (by rfl) ⟨1071758, by rfl⟩ : syracuseStep 1429011 = 2143517) B2143517
theorem B2141729 : Blo 1427533 2141729 := bstep (se 2 (by rfl) ⟨803148, by rfl⟩ : syracuseStep 2141729 = 1606297) B1606297
theorem B2412065 : Blo 1427533 2412065 := bstep (se 2 (by rfl) ⟨904524, by rfl⟩ : syracuseStep 2412065 = 1809049) B1809049
theorem B1715747 : Blo 1427533 1715747 := bstep (se 1 (by rfl) ⟨1286810, by rfl⟩ : syracuseStep 1715747 = 2573621) B2573621
theorem B1429027 : Blo 1427533 1429027 := bstep (se 1 (by rfl) ⟨1071770, by rfl⟩ : syracuseStep 1429027 = 2143541) B2143541
theorem B4820525 : Blo 1427533 4820525 := bstep (se 3 (by rfl) ⟨903848, by rfl⟩ : syracuseStep 4820525 = 1807697) B1807697
theorem B2141747 : Blo 1427533 2141747 := bstep (se 1 (by rfl) ⟨1606310, by rfl⟩ : syracuseStep 2141747 = 3212621) B3212621
theorem B1429043 : Blo 1427533 1429043 := bstep (se 1 (by rfl) ⟨1071782, by rfl⟩ : syracuseStep 1429043 = 2143565) B2143565
theorem B1429059 : Blo 1427533 1429059 := bstep (se 1 (by rfl) ⟨1071794, by rfl⟩ : syracuseStep 1429059 = 2143589) B2143589
theorem B3255889 : Blo 1427533 3255889 := bstep (se 2 (by rfl) ⟨1220958, by rfl⟩ : syracuseStep 3255889 = 2441917) B2441917
theorem B2141777 : Blo 1427533 2141777 := bstep (se 2 (by rfl) ⟨803166, by rfl⟩ : syracuseStep 2141777 = 1606333) B1606333
theorem B1429075 : Blo 1427533 1429075 := bstep (se 1 (by rfl) ⟨1071806, by rfl⟩ : syracuseStep 1429075 = 2143613) B2143613
theorem B2141795 : Blo 1427533 2141795 := bstep (se 1 (by rfl) ⟨1606346, by rfl⟩ : syracuseStep 2141795 = 3212693) B3212693
theorem B4820579 : Blo 1427533 4820579 := bstep (se 1 (by rfl) ⟨3615434, by rfl⟩ : syracuseStep 4820579 = 7230869) B7230869
theorem B1429091 : Blo 1427533 1429091 := bstep (se 1 (by rfl) ⟨1071818, by rfl⟩ : syracuseStep 1429091 = 2143637) B2143637
theorem B31305329 : Blo 1427533 31305329 := bstep (se 2 (by rfl) ⟨11739498, by rfl⟩ : syracuseStep 31305329 = 23478997) B23478997
theorem B3214961 : Blo 1427533 3214961 := bstep (se 2 (by rfl) ⟨1205610, by rfl⟩ : syracuseStep 3214961 = 2411221) B2411221
theorem B1429107 : Blo 1427533 1429107 := bstep (se 1 (by rfl) ⟨1071830, by rfl⟩ : syracuseStep 1429107 = 2143661) B2143661
theorem B2141825 : Blo 1427533 2141825 := bstep (se 2 (by rfl) ⟨803184, by rfl⟩ : syracuseStep 2141825 = 1606369) B1606369
theorem B1715843 : Blo 1427533 1715843 := bstep (se 1 (by rfl) ⟨1286882, by rfl⟩ : syracuseStep 1715843 = 2573765) B2573765
theorem B3214979 : Blo 1427533 3214979 := bstep (se 1 (by rfl) ⟨2411234, by rfl⟩ : syracuseStep 3214979 = 4822469) B4822469
theorem B1429123 : Blo 1427533 1429123 := bstep (se 1 (by rfl) ⟨1071842, by rfl⟩ : syracuseStep 1429123 = 2143685) B2143685
theorem B2141843 : Blo 1427533 2141843 := bstep (se 1 (by rfl) ⟨1606382, by rfl⟩ : syracuseStep 2141843 = 3212765) B3212765
theorem B1429139 : Blo 1427533 1429139 := bstep (se 1 (by rfl) ⟨1071854, by rfl⟩ : syracuseStep 1429139 = 2143709) B2143709
theorem B2412193 : Blo 1427533 2412193 := bstep (se 2 (by rfl) ⟨904572, by rfl⟩ : syracuseStep 2412193 = 1809145) B1809145
theorem B1429155 : Blo 1427533 1429155 := bstep (se 1 (by rfl) ⟨1071866, by rfl⟩ : syracuseStep 1429155 = 2143733) B2143733
theorem B2035363 : Blo 1427533 2035363 := bstep (se 1 (by rfl) ⟨1526522, by rfl⟩ : syracuseStep 2035363 = 3053045) B3053045
theorem B2141873 : Blo 1427533 2141873 := bstep (se 2 (by rfl) ⟨803202, by rfl⟩ : syracuseStep 2141873 = 1606405) B1606405
theorem B1429171 : Blo 1427533 1429171 := bstep (se 1 (by rfl) ⟨1071878, by rfl⟩ : syracuseStep 1429171 = 2143757) B2143757
theorem B2141891 : Blo 1427533 2141891 := bstep (se 1 (by rfl) ⟨1606418, by rfl⟩ : syracuseStep 2141891 = 3212837) B3212837
theorem B1429187 : Blo 1427533 1429187 := bstep (se 1 (by rfl) ⟨1071890, by rfl⟩ : syracuseStep 1429187 = 2143781) B2143781
theorem B2412227 : Blo 1427533 2412227 := bstep (se 1 (by rfl) ⟨1809170, by rfl⟩ : syracuseStep 2412227 = 3618341) B3618341
theorem B3862225 : Blo 1427533 3862225 := bstep (se 2 (by rfl) ⟨1448334, by rfl⟩ : syracuseStep 3862225 = 2896669) B2896669
theorem B1429203 : Blo 1427533 1429203 := bstep (se 1 (by rfl) ⟨1071902, by rfl⟩ : syracuseStep 1429203 = 2143805) B2143805
theorem B2141921 : Blo 1427533 2141921 := bstep (se 2 (by rfl) ⟨803220, by rfl⟩ : syracuseStep 2141921 = 1606441) B1606441
theorem B1429219 : Blo 1427533 1429219 := bstep (se 1 (by rfl) ⟨1071914, by rfl⟩ : syracuseStep 1429219 = 2143829) B2143829
theorem B2141939 : Blo 1427533 2141939 := bstep (se 1 (by rfl) ⟨1606454, by rfl⟩ : syracuseStep 2141939 = 3212909) B3212909
theorem B1429235 : Blo 1427533 1429235 := bstep (se 1 (by rfl) ⟨1071926, by rfl⟩ : syracuseStep 1429235 = 2143853) B2143853
theorem B1429251 : Blo 1427533 1429251 := bstep (se 1 (by rfl) ⟨1071938, by rfl⟩ : syracuseStep 1429251 = 2143877) B2143877
theorem B4345613 : Blo 1427533 4345613 := bstep (se 3 (by rfl) ⟨814802, by rfl⟩ : syracuseStep 4345613 = 1629605) B1629605
theorem B2141969 : Blo 1427533 2141969 := bstep (se 2 (by rfl) ⟨803238, by rfl⟩ : syracuseStep 2141969 = 1606477) B1606477
theorem B1429267 : Blo 1427533 1429267 := bstep (se 1 (by rfl) ⟨1071950, by rfl⟩ : syracuseStep 1429267 = 2143901) B2143901
theorem B6098723 : Blo 1427533 6098723 := bstep (se 1 (by rfl) ⟨4574042, by rfl⟩ : syracuseStep 6098723 = 9148085) B9148085
theorem B2141987 : Blo 1427533 2141987 := bstep (se 1 (by rfl) ⟨1606490, by rfl⟩ : syracuseStep 2141987 = 3212981) B3212981
theorem B5148451 : Blo 1427533 5148451 := bstep (se 1 (by rfl) ⟨3861338, by rfl⟩ : syracuseStep 5148451 = 7722677) B7722677
theorem B1429283 : Blo 1427533 1429283 := bstep (se 1 (by rfl) ⟨1071962, by rfl⟩ : syracuseStep 1429283 = 2143925) B2143925
theorem B1429299 : Blo 1427533 1429299 := bstep (se 1 (by rfl) ⟨1071974, by rfl⟩ : syracuseStep 1429299 = 2143949) B2143949
theorem B2142017 : Blo 1427533 2142017 := bstep (se 2 (by rfl) ⟨803256, by rfl⟩ : syracuseStep 2142017 = 1606513) B1606513
theorem B1429315 : Blo 1427533 1429315 := bstep (se 1 (by rfl) ⟨1071986, by rfl⟩ : syracuseStep 1429315 = 2143973) B2143973
theorem B2142035 : Blo 1427533 2142035 := bstep (se 1 (by rfl) ⟨1606526, by rfl⟩ : syracuseStep 2142035 = 3213053) B3213053
theorem B1429331 : Blo 1427533 1429331 := bstep (se 1 (by rfl) ⟨1071998, by rfl⟩ : syracuseStep 1429331 = 2143997) B2143997
theorem B1429347 : Blo 1427533 1429347 := bstep (se 1 (by rfl) ⟨1072010, by rfl⟩ : syracuseStep 1429347 = 2144021) B2144021
theorem B2142065 : Blo 1427533 2142065 := bstep (se 2 (by rfl) ⟨803274, by rfl⟩ : syracuseStep 2142065 = 1606549) B1606549
theorem B4820849 : Blo 1427533 4820849 := bstep (se 2 (by rfl) ⟨1807818, by rfl⟩ : syracuseStep 4820849 = 3615637) B3615637
theorem B9154417 : Blo 1427533 9154417 := bstep (se 2 (by rfl) ⟨3432906, by rfl⟩ : syracuseStep 9154417 = 6865813) B6865813
theorem B1429363 : Blo 1427533 1429363 := bstep (se 1 (by rfl) ⟨1072022, by rfl⟩ : syracuseStep 1429363 = 2144045) B2144045
theorem B2142083 : Blo 1427533 2142083 := bstep (se 1 (by rfl) ⟨1606562, by rfl⟩ : syracuseStep 2142083 = 3213125) B3213125
theorem B1429379 : Blo 1427533 1429379 := bstep (se 1 (by rfl) ⟨1072034, by rfl⟩ : syracuseStep 1429379 = 2144069) B2144069
theorem B16281485 : Blo 1427533 16281485 := bstep (se 3 (by rfl) ⟨3052778, by rfl⟩ : syracuseStep 16281485 = 6105557) B6105557
theorem B3215249 : Blo 1427533 3215249 := bstep (se 2 (by rfl) ⟨1205718, by rfl⟩ : syracuseStep 3215249 = 2411437) B2411437
theorem B1429395 : Blo 1427533 1429395 := bstep (se 1 (by rfl) ⟨1072046, by rfl⟩ : syracuseStep 1429395 = 2144093) B2144093
theorem B2142113 : Blo 1427533 2142113 := bstep (se 2 (by rfl) ⟨803292, by rfl⟩ : syracuseStep 2142113 = 1606585) B1606585
theorem B3215267 : Blo 1427533 3215267 := bstep (se 1 (by rfl) ⟨2411450, by rfl⟩ : syracuseStep 3215267 = 4822901) B4822901
theorem B1429411 : Blo 1427533 1429411 := bstep (se 1 (by rfl) ⟨1072058, by rfl⟩ : syracuseStep 1429411 = 2144117) B2144117
theorem B2142131 : Blo 1427533 2142131 := bstep (se 1 (by rfl) ⟨1606598, by rfl⟩ : syracuseStep 2142131 = 3213197) B3213197
theorem B1429427 : Blo 1427533 1429427 := bstep (se 1 (by rfl) ⟨1072070, by rfl⟩ : syracuseStep 1429427 = 2144141) B2144141
theorem B1429443 : Blo 1427533 1429443 := bstep (se 1 (by rfl) ⟨1072082, by rfl⟩ : syracuseStep 1429443 = 2144165) B2144165
theorem B2142161 : Blo 1427533 2142161 := bstep (se 2 (by rfl) ⟨803310, by rfl⟩ : syracuseStep 2142161 = 1606621) B1606621
theorem B3616721 : Blo 1427533 3616721 := bstep (se 2 (by rfl) ⟨1356270, by rfl⟩ : syracuseStep 3616721 = 2712541) B2712541
theorem B1429459 : Blo 1427533 1429459 := bstep (se 1 (by rfl) ⟨1072094, by rfl⟩ : syracuseStep 1429459 = 2144189) B2144189
theorem B7229411 : Blo 1427533 7229411 := bstep (se 1 (by rfl) ⟨5422058, by rfl⟩ : syracuseStep 7229411 = 10844117) B10844117
theorem B2142179 : Blo 1427533 2142179 := bstep (se 1 (by rfl) ⟨1606634, by rfl⟩ : syracuseStep 2142179 = 3213269) B3213269
theorem B1429475 : Blo 1427533 1429475 := bstep (se 1 (by rfl) ⟨1072106, by rfl⟩ : syracuseStep 1429475 = 2144213) B2144213
theorem B2289649 : Blo 1427533 2289649 := bstep (se 2 (by rfl) ⟨858618, by rfl⟩ : syracuseStep 2289649 = 1717237) B1717237
theorem B1429491 : Blo 1427533 1429491 := bstep (se 1 (by rfl) ⟨1072118, by rfl⟩ : syracuseStep 1429491 = 2144237) B2144237
theorem B2142209 : Blo 1427533 2142209 := bstep (se 2 (by rfl) ⟨803328, by rfl⟩ : syracuseStep 2142209 = 1606657) B1606657
theorem B3616771 : Blo 1427533 3616771 := bstep (se 1 (by rfl) ⟨2712578, by rfl⟩ : syracuseStep 3616771 = 5425157) B5425157
theorem B1429507 : Blo 1427533 1429507 := bstep (se 1 (by rfl) ⟨1072130, by rfl⟩ : syracuseStep 1429507 = 2144261) B2144261
theorem B2142227 : Blo 1427533 2142227 := bstep (se 1 (by rfl) ⟨1606670, by rfl⟩ : syracuseStep 2142227 = 3213341) B3213341
theorem B1429523 : Blo 1427533 1429523 := bstep (se 1 (by rfl) ⟨1072142, by rfl⟩ : syracuseStep 1429523 = 2144285) B2144285
theorem B2895907 : Blo 1427533 2895907 := bstep (se 1 (by rfl) ⟨2171930, by rfl⟩ : syracuseStep 2895907 = 4343861) B4343861
theorem B2142257 : Blo 1427533 2142257 := bstep (se 2 (by rfl) ⟨803346, by rfl⟩ : syracuseStep 2142257 = 1606693) B1606693
theorem B2142275 : Blo 1427533 2142275 := bstep (se 1 (by rfl) ⟨1606706, by rfl⟩ : syracuseStep 2142275 = 3213413) B3213413
theorem B4124753 : Blo 1427533 4124753 := bstep (se 2 (by rfl) ⟨1546782, by rfl⟩ : syracuseStep 4124753 = 3093565) B3093565
theorem B2142305 : Blo 1427533 2142305 := bstep (se 2 (by rfl) ⟨803364, by rfl⟩ : syracuseStep 2142305 = 1606729) B1606729
theorem B2142323 : Blo 1427533 2142323 := bstep (se 1 (by rfl) ⟨1606742, by rfl⟩ : syracuseStep 2142323 = 3213485) B3213485
theorem B2142353 : Blo 1427533 2142353 := bstep (se 2 (by rfl) ⟨803382, by rfl⟩ : syracuseStep 2142353 = 1606765) B1606765
theorem B3616913 : Blo 1427533 3616913 := bstep (se 2 (by rfl) ⟨1356342, by rfl⟩ : syracuseStep 3616913 = 2712685) B2712685
theorem B2142371 : Blo 1427533 2142371 := bstep (se 1 (by rfl) ⟨1606778, by rfl⟩ : syracuseStep 2142371 = 3213557) B3213557
theorem B3215537 : Blo 1427533 3215537 := bstep (se 2 (by rfl) ⟨1205826, by rfl⟩ : syracuseStep 3215537 = 2411653) B2411653
theorem B2142401 : Blo 1427533 2142401 := bstep (se 2 (by rfl) ⟨803400, by rfl⟩ : syracuseStep 2142401 = 1606801) B1606801
theorem B3862723 : Blo 1427533 3862723 := bstep (se 1 (by rfl) ⟨2897042, by rfl⟩ : syracuseStep 3862723 = 5794085) B5794085
theorem B3215555 : Blo 1427533 3215555 := bstep (se 1 (by rfl) ⟨2411666, by rfl⟩ : syracuseStep 3215555 = 4823333) B4823333
theorem B2142419 : Blo 1427533 2142419 := bstep (se 1 (by rfl) ⟨1606814, by rfl⟩ : syracuseStep 2142419 = 3213629) B3213629
theorem B2142449 : Blo 1427533 2142449 := bstep (se 2 (by rfl) ⟨803418, by rfl⟩ : syracuseStep 2142449 = 1606837) B1606837
theorem B2142467 : Blo 1427533 2142467 := bstep (se 1 (by rfl) ⟨1606850, by rfl⟩ : syracuseStep 2142467 = 3213701) B3213701
theorem B2142497 : Blo 1427533 2142497 := bstep (se 2 (by rfl) ⟨803436, by rfl⟩ : syracuseStep 2142497 = 1606873) B1606873
theorem B2142515 : Blo 1427533 2142515 := bstep (se 1 (by rfl) ⟨1606886, by rfl⟩ : syracuseStep 2142515 = 3213773) B3213773
theorem B2142545 : Blo 1427533 2142545 := bstep (se 2 (by rfl) ⟨803454, by rfl⟩ : syracuseStep 2142545 = 1606909) B1606909
theorem B3051857 : Blo 1427533 3051857 := bstep (se 2 (by rfl) ⟨1144446, by rfl⟩ : syracuseStep 3051857 = 2288893) B2288893
theorem B2142563 : Blo 1427533 2142563 := bstep (se 1 (by rfl) ⟨1606922, by rfl⟩ : syracuseStep 2142563 = 3213845) B3213845
theorem B2142593 : Blo 1427533 2142593 := bstep (se 2 (by rfl) ⟨803472, by rfl⟩ : syracuseStep 2142593 = 1606945) B1606945
theorem B4821389 : Blo 1427533 4821389 := bstep (se 3 (by rfl) ⟨904010, by rfl⟩ : syracuseStep 4821389 = 1808021) B1808021
theorem B8139149 : Blo 1427533 8139149 := bstep (se 3 (by rfl) ⟨1526090, by rfl⟩ : syracuseStep 8139149 = 3052181) B3052181
theorem B4067729 : Blo 1427533 4067729 := bstep (se 2 (by rfl) ⟨1525398, by rfl⟩ : syracuseStep 4067729 = 3050797) B3050797
theorem B2142611 : Blo 1427533 2142611 := bstep (se 1 (by rfl) ⟨1606958, by rfl⟩ : syracuseStep 2142611 = 3213917) B3213917
theorem B2142641 : Blo 1427533 2142641 := bstep (se 2 (by rfl) ⟨803490, by rfl⟩ : syracuseStep 2142641 = 1606981) B1606981
theorem B4575683 : Blo 1427533 4575683 := bstep (se 1 (by rfl) ⟨3431762, by rfl⟩ : syracuseStep 4575683 = 6863525) B6863525
theorem B2142659 : Blo 1427533 2142659 := bstep (se 1 (by rfl) ⟨1606994, by rfl⟩ : syracuseStep 2142659 = 3213989) B3213989
theorem B4821443 : Blo 1427533 4821443 := bstep (se 1 (by rfl) ⟨3616082, by rfl⟩ : syracuseStep 4821443 = 7232165) B7232165
theorem B4641229 : Blo 1427533 4641229 := bstep (se 3 (by rfl) ⟨870230, by rfl⟩ : syracuseStep 4641229 = 1740461) B1740461
theorem B3215825 : Blo 1427533 3215825 := bstep (se 2 (by rfl) ⟨1205934, by rfl⟩ : syracuseStep 3215825 = 2411869) B2411869
theorem B2142689 : Blo 1427533 2142689 := bstep (se 2 (by rfl) ⟨803508, by rfl⟩ : syracuseStep 2142689 = 1607017) B1607017
theorem B3215843 : Blo 1427533 3215843 := bstep (se 1 (by rfl) ⟨2411882, by rfl⟩ : syracuseStep 3215843 = 4823765) B4823765
theorem B2142707 : Blo 1427533 2142707 := bstep (se 1 (by rfl) ⟨1607030, by rfl⟩ : syracuseStep 2142707 = 3214061) B3214061
theorem B3092995 : Blo 1427533 3092995 := bstep (se 1 (by rfl) ⟨2319746, by rfl⟩ : syracuseStep 3092995 = 4639493) B4639493
theorem B2142737 : Blo 1427533 2142737 := bstep (se 2 (by rfl) ⟨803526, by rfl⟩ : syracuseStep 2142737 = 1607053) B1607053
theorem B2142755 : Blo 1427533 2142755 := bstep (se 1 (by rfl) ⟨1607066, by rfl⟩ : syracuseStep 2142755 = 3214133) B3214133
theorem B2142785 : Blo 1427533 2142785 := bstep (se 2 (by rfl) ⟨803544, by rfl⟩ : syracuseStep 2142785 = 1607089) B1607089
theorem B2142803 : Blo 1427533 2142803 := bstep (se 1 (by rfl) ⟨1607102, by rfl⟩ : syracuseStep 2142803 = 3214205) B3214205
theorem B2142833 : Blo 1427533 2142833 := bstep (se 2 (by rfl) ⟨803562, by rfl⟩ : syracuseStep 2142833 = 1607125) B1607125
theorem B2142851 : Blo 1427533 2142851 := bstep (se 1 (by rfl) ⟨1607138, by rfl⟩ : syracuseStep 2142851 = 3214277) B3214277
theorem B8245901 : Blo 1427533 8245901 := bstep (se 3 (by rfl) ⟨1546106, by rfl⟩ : syracuseStep 8245901 = 3092213) B3092213
theorem B2142881 : Blo 1427533 2142881 := bstep (se 2 (by rfl) ⟨803580, by rfl⟩ : syracuseStep 2142881 = 1607161) B1607161
theorem B2142899 : Blo 1427533 2142899 := bstep (se 1 (by rfl) ⟨1607174, by rfl⟩ : syracuseStep 2142899 = 3214349) B3214349
theorem B2142929 : Blo 1427533 2142929 := bstep (se 2 (by rfl) ⟨803598, by rfl⟩ : syracuseStep 2142929 = 1607197) B1607197
theorem B4821713 : Blo 1427533 4821713 := bstep (se 2 (by rfl) ⟨1808142, by rfl⟩ : syracuseStep 4821713 = 3616285) B3616285
theorem B2142947 : Blo 1427533 2142947 := bstep (se 1 (by rfl) ⟨1607210, by rfl⟩ : syracuseStep 2142947 = 3214421) B3214421
theorem B3216113 : Blo 1427533 3216113 := bstep (se 2 (by rfl) ⟨1206042, by rfl⟩ : syracuseStep 3216113 = 2412085) B2412085
theorem B2142977 : Blo 1427533 2142977 := bstep (se 2 (by rfl) ⟨803616, by rfl⟩ : syracuseStep 2142977 = 1607233) B1607233
theorem B3216131 : Blo 1427533 3216131 := bstep (se 1 (by rfl) ⟨2412098, by rfl⟩ : syracuseStep 3216131 = 4824197) B4824197
theorem B7230221 : Blo 1427533 7230221 := bstep (se 3 (by rfl) ⟨1355666, by rfl⟩ : syracuseStep 7230221 = 2711333) B2711333
theorem B2142995 : Blo 1427533 2142995 := bstep (se 1 (by rfl) ⟨1607246, by rfl⟩ : syracuseStep 2142995 = 3214493) B3214493
theorem B2143025 : Blo 1427533 2143025 := bstep (se 2 (by rfl) ⟨803634, by rfl⟩ : syracuseStep 2143025 = 1607269) B1607269
theorem B5149489 : Blo 1427533 5149489 := bstep (se 2 (by rfl) ⟨1931058, by rfl⟩ : syracuseStep 5149489 = 3862117) B3862117
theorem B2143043 : Blo 1427533 2143043 := bstep (se 1 (by rfl) ⟨1607282, by rfl⟩ : syracuseStep 2143043 = 3214565) B3214565
theorem B2143073 : Blo 1427533 2143073 := bstep (se 2 (by rfl) ⟨803652, by rfl⟩ : syracuseStep 2143073 = 1607305) B1607305
theorem B8131427 : Blo 1427533 8131427 := bstep (se 1 (by rfl) ⟨6098570, by rfl⟩ : syracuseStep 8131427 = 12197141) B12197141
theorem B2143091 : Blo 1427533 2143091 := bstep (se 1 (by rfl) ⟨1607318, by rfl⟩ : syracuseStep 2143091 = 3214637) B3214637
theorem B2143121 : Blo 1427533 2143121 := bstep (se 2 (by rfl) ⟨803670, by rfl⟩ : syracuseStep 2143121 = 1607341) B1607341
theorem B1807267 : Blo 1427533 1807267 := bstep (se 1 (by rfl) ⟨1355450, by rfl⟩ : syracuseStep 1807267 = 2710901) B2710901
theorem B2143139 : Blo 1427533 2143139 := bstep (se 1 (by rfl) ⟨1607354, by rfl⟩ : syracuseStep 2143139 = 3214709) B3214709
theorem B2143169 : Blo 1427533 2143169 := bstep (se 2 (by rfl) ⟨803688, by rfl⟩ : syracuseStep 2143169 = 1607377) B1607377
theorem B2143187 : Blo 1427533 2143187 := bstep (se 1 (by rfl) ⟨1607390, by rfl⟩ : syracuseStep 2143187 = 3214781) B3214781
theorem B13726705 : Blo 1427533 13726705 := bstep (se 2 (by rfl) ⟨5147514, by rfl⟩ : syracuseStep 13726705 = 10295029) B10295029
theorem B2143217 : Blo 1427533 2143217 := bstep (se 2 (by rfl) ⟨803706, by rfl⟩ : syracuseStep 2143217 = 1607413) B1607413
theorem B1807363 : Blo 1427533 1807363 := bstep (se 1 (by rfl) ⟨1355522, by rfl⟩ : syracuseStep 1807363 = 2711045) B2711045
theorem B2143235 : Blo 1427533 2143235 := bstep (se 1 (by rfl) ⟨1607426, by rfl⟩ : syracuseStep 2143235 = 3214853) B3214853
theorem B3216401 : Blo 1427533 3216401 := bstep (se 2 (by rfl) ⟨1206150, by rfl⟩ : syracuseStep 3216401 = 2412301) B2412301
theorem B2143265 : Blo 1427533 2143265 := bstep (se 2 (by rfl) ⟨803724, by rfl⟩ : syracuseStep 2143265 = 1607449) B1607449
theorem B3216419 : Blo 1427533 3216419 := bstep (se 1 (by rfl) ⟨2412314, by rfl⟩ : syracuseStep 3216419 = 4824629) B4824629
theorem B2143283 : Blo 1427533 2143283 := bstep (se 1 (by rfl) ⟨1607462, by rfl⟩ : syracuseStep 2143283 = 3214925) B3214925
theorem B2143313 : Blo 1427533 2143313 := bstep (se 2 (by rfl) ⟨803742, by rfl⟩ : syracuseStep 2143313 = 1607485) B1607485
theorem B11580515 : Blo 1427533 11580515 := bstep (se 1 (by rfl) ⟨8685386, by rfl⟩ : syracuseStep 11580515 = 17370773) B17370773
theorem B2143331 : Blo 1427533 2143331 := bstep (se 1 (by rfl) ⟨1607498, by rfl⟩ : syracuseStep 2143331 = 3214997) B3214997
theorem B29717617 : Blo 1427533 29717617 := bstep (se 2 (by rfl) ⟨11144106, by rfl⟩ : syracuseStep 29717617 = 22288213) B22288213
theorem B3617905 : Blo 1427533 3617905 := bstep (se 2 (by rfl) ⟨1356714, by rfl⟩ : syracuseStep 3617905 = 2713429) B2713429
theorem B2143361 : Blo 1427533 2143361 := bstep (se 2 (by rfl) ⟨803760, by rfl⟩ : syracuseStep 2143361 = 1607521) B1607521
theorem B36623501 : Blo 1427533 36623501 := bstep (se 3 (by rfl) ⟨6866906, by rfl⟩ : syracuseStep 36623501 = 13733813) B13733813
theorem B2143379 : Blo 1427533 2143379 := bstep (se 1 (by rfl) ⟨1607534, by rfl⟩ : syracuseStep 2143379 = 3215069) B3215069
theorem B2143409 : Blo 1427533 2143409 := bstep (se 2 (by rfl) ⟨803778, by rfl⟩ : syracuseStep 2143409 = 1607557) B1607557
theorem B2143427 : Blo 1427533 2143427 := bstep (se 1 (by rfl) ⟨1607570, by rfl⟩ : syracuseStep 2143427 = 3215141) B3215141
theorem B27473093 : Blo 1427533 27473093 := bstep (se 4 (by rfl) ⟨2575602, by rfl⟩ : syracuseStep 27473093 = 5151205) B5151205
theorem B2143457 : Blo 1427533 2143457 := bstep (se 2 (by rfl) ⟨803796, by rfl⟩ : syracuseStep 2143457 = 1607593) B1607593
theorem B4822253 : Blo 1427533 4822253 := bstep (se 3 (by rfl) ⟨904172, by rfl⟩ : syracuseStep 4822253 = 1808345) B1808345
theorem B2143475 : Blo 1427533 2143475 := bstep (se 1 (by rfl) ⟨1607606, by rfl⟩ : syracuseStep 2143475 = 3215213) B3215213
theorem B9147653 : Blo 1427533 9147653 := bstep (se 4 (by rfl) ⟨857592, by rfl⟩ : syracuseStep 9147653 = 1715185) B1715185
theorem B2143505 : Blo 1427533 2143505 := bstep (se 2 (by rfl) ⟨803814, by rfl⟩ : syracuseStep 2143505 = 1607629) B1607629
theorem B4822307 : Blo 1427533 4822307 := bstep (se 1 (by rfl) ⟨3616730, by rfl⟩ : syracuseStep 4822307 = 7233461) B7233461
theorem B2143523 : Blo 1427533 2143523 := bstep (se 1 (by rfl) ⟨1607642, by rfl⟩ : syracuseStep 2143523 = 3215285) B3215285
theorem B2143553 : Blo 1427533 2143553 := bstep (se 2 (by rfl) ⟨803832, by rfl⟩ : syracuseStep 2143553 = 1607665) B1607665
theorem B2143571 : Blo 1427533 2143571 := bstep (se 1 (by rfl) ⟨1607678, by rfl⟩ : syracuseStep 2143571 = 3215357) B3215357
theorem B2143601 : Blo 1427533 2143601 := bstep (se 2 (by rfl) ⟨803850, by rfl⟩ : syracuseStep 2143601 = 1607701) B1607701
theorem B2143619 : Blo 1427533 2143619 := bstep (se 1 (by rfl) ⟨1607714, by rfl⟩ : syracuseStep 2143619 = 3215429) B3215429
theorem B3618179 : Blo 1427533 3618179 := bstep (se 1 (by rfl) ⟨2713634, by rfl⟩ : syracuseStep 3618179 = 5427269) B5427269
theorem B4576657 : Blo 1427533 4576657 := bstep (se 2 (by rfl) ⟨1716246, by rfl⟩ : syracuseStep 4576657 = 3432493) B3432493
theorem B2143649 : Blo 1427533 2143649 := bstep (se 2 (by rfl) ⟨803868, by rfl⟩ : syracuseStep 2143649 = 1607737) B1607737
theorem B5420465 : Blo 1427533 5420465 := bstep (se 2 (by rfl) ⟨2032674, by rfl⟩ : syracuseStep 5420465 = 4065349) B4065349
theorem B2143667 : Blo 1427533 2143667 := bstep (se 1 (by rfl) ⟨1607750, by rfl⟩ : syracuseStep 2143667 = 3215501) B3215501
theorem B2143697 : Blo 1427533 2143697 := bstep (se 2 (by rfl) ⟨803886, by rfl⟩ : syracuseStep 2143697 = 1607773) B1607773
theorem B30873059 : Blo 1427533 30873059 := bstep (se 1 (by rfl) ⟨23154794, by rfl⟩ : syracuseStep 30873059 = 46309589) B46309589
theorem B2143715 : Blo 1427533 2143715 := bstep (se 1 (by rfl) ⟨1607786, by rfl⟩ : syracuseStep 2143715 = 3215573) B3215573
theorem B1807859 : Blo 1427533 1807859 := bstep (se 1 (by rfl) ⟨1355894, by rfl⟩ : syracuseStep 1807859 = 2711789) B2711789
theorem B2143745 : Blo 1427533 2143745 := bstep (se 2 (by rfl) ⟨803904, by rfl⟩ : syracuseStep 2143745 = 1607809) B1607809
theorem B1447427 : Blo 1427533 1447427 := bstep (se 1 (by rfl) ⟨1085570, by rfl⟩ : syracuseStep 1447427 = 2171141) B2171141
theorem B2143763 : Blo 1427533 2143763 := bstep (se 1 (by rfl) ⟨1607822, by rfl⟩ : syracuseStep 2143763 = 3215645) B3215645
theorem B4822577 : Blo 1427533 4822577 := bstep (se 2 (by rfl) ⟨1808466, by rfl⟩ : syracuseStep 4822577 = 3616933) B3616933
theorem B2143793 : Blo 1427533 2143793 := bstep (se 2 (by rfl) ⟨803922, by rfl⟩ : syracuseStep 2143793 = 1607845) B1607845
theorem B2143811 : Blo 1427533 2143811 := bstep (se 1 (by rfl) ⟨1607858, by rfl⟩ : syracuseStep 2143811 = 3215717) B3215717
theorem B3618371 : Blo 1427533 3618371 := bstep (se 1 (by rfl) ⟨2713778, by rfl⟩ : syracuseStep 3618371 = 5427557) B5427557
theorem B2143841 : Blo 1427533 2143841 := bstep (se 2 (by rfl) ⟨803940, by rfl⟩ : syracuseStep 2143841 = 1607881) B1607881
theorem B3667555 : Blo 1427533 3667555 := bstep (se 1 (by rfl) ⟨2750666, by rfl⟩ : syracuseStep 3667555 = 5501333) B5501333
theorem B2143859 : Blo 1427533 2143859 := bstep (se 1 (by rfl) ⟨1607894, by rfl⟩ : syracuseStep 2143859 = 3215789) B3215789
theorem B4576913 : Blo 1427533 4576913 := bstep (se 2 (by rfl) ⟨1716342, by rfl⟩ : syracuseStep 4576913 = 3432685) B3432685
theorem B2143889 : Blo 1427533 2143889 := bstep (se 2 (by rfl) ⟨803958, by rfl⟩ : syracuseStep 2143889 = 1607917) B1607917
theorem B2143907 : Blo 1427533 2143907 := bstep (se 1 (by rfl) ⟨1607930, by rfl⟩ : syracuseStep 2143907 = 3215861) B3215861
theorem B2143937 : Blo 1427533 2143937 := bstep (se 2 (by rfl) ⟨803976, by rfl⟩ : syracuseStep 2143937 = 1607953) B1607953
theorem B2143955 : Blo 1427533 2143955 := bstep (se 1 (by rfl) ⟨1607966, by rfl⟩ : syracuseStep 2143955 = 3215933) B3215933
theorem B2143985 : Blo 1427533 2143985 := bstep (se 2 (by rfl) ⟨803994, by rfl⟩ : syracuseStep 2143985 = 1607989) B1607989
theorem B2144003 : Blo 1427533 2144003 := bstep (se 1 (by rfl) ⟨1608002, by rfl⟩ : syracuseStep 2144003 = 3216005) B3216005
theorem B2144033 : Blo 1427533 2144033 := bstep (se 2 (by rfl) ⟨804012, by rfl⟩ : syracuseStep 2144033 = 1608025) B1608025
theorem B2144051 : Blo 1427533 2144051 := bstep (se 1 (by rfl) ⟨1608038, by rfl⟩ : syracuseStep 2144051 = 3216077) B3216077
theorem B4069187 : Blo 1427533 4069187 := bstep (se 1 (by rfl) ⟨3051890, by rfl⟩ : syracuseStep 4069187 = 6103781) B6103781
theorem B2144081 : Blo 1427533 2144081 := bstep (se 2 (by rfl) ⟨804030, by rfl⟩ : syracuseStep 2144081 = 1608061) B1608061
theorem B2144099 : Blo 1427533 2144099 := bstep (se 1 (by rfl) ⟨1608074, by rfl⟩ : syracuseStep 2144099 = 3216149) B3216149
theorem B2144129 : Blo 1427533 2144129 := bstep (se 2 (by rfl) ⟨804048, by rfl⟩ : syracuseStep 2144129 = 1608097) B1608097
theorem B2144147 : Blo 1427533 2144147 := bstep (se 1 (by rfl) ⟨1608110, by rfl⟩ : syracuseStep 2144147 = 3216221) B3216221
theorem B2144177 : Blo 1427533 2144177 := bstep (se 2 (by rfl) ⟨804066, by rfl⟩ : syracuseStep 2144177 = 1608133) B1608133
theorem B2144195 : Blo 1427533 2144195 := bstep (se 1 (by rfl) ⟨1608146, by rfl⟩ : syracuseStep 2144195 = 3216293) B3216293
theorem B1832915 : Blo 1427533 1832915 := bstep (se 1 (by rfl) ⟨1374686, by rfl⟩ : syracuseStep 1832915 = 2749373) B2749373
theorem B2144225 : Blo 1427533 2144225 := bstep (se 2 (by rfl) ⟨804084, by rfl⟩ : syracuseStep 2144225 = 1608169) B1608169
theorem B2144243 : Blo 1427533 2144243 := bstep (se 1 (by rfl) ⟨1608182, by rfl⟩ : syracuseStep 2144243 = 3216365) B3216365
theorem B2144273 : Blo 1427533 2144273 := bstep (se 2 (by rfl) ⟨804102, by rfl⟩ : syracuseStep 2144273 = 1608205) B1608205
theorem B2144291 : Blo 1427533 2144291 := bstep (se 1 (by rfl) ⟨1608218, by rfl⟩ : syracuseStep 2144291 = 3216437) B3216437
theorem B4823117 : Blo 1427533 4823117 := bstep (se 3 (by rfl) ⟨904334, by rfl⟩ : syracuseStep 4823117 = 1808669) B1808669
theorem B4823171 : Blo 1427533 4823171 := bstep (se 1 (by rfl) ⟨3617378, by rfl⟩ : syracuseStep 4823171 = 7234757) B7234757
theorem B1448099 : Blo 1427533 1448099 := bstep (se 1 (by rfl) ⟨1086074, by rfl⟩ : syracuseStep 1448099 = 2172149) B2172149
theorem B1808563 : Blo 1427533 1808563 := bstep (se 1 (by rfl) ⟨1356422, by rfl⟩ : syracuseStep 1808563 = 2712845) B2712845
theorem B16275653 : Blo 1427533 16275653 := bstep (se 4 (by rfl) ⟨1525842, by rfl⟩ : syracuseStep 16275653 = 3051685) B3051685
theorem B2644177 : Blo 1427533 2644177 := bstep (se 2 (by rfl) ⟨991566, by rfl⟩ : syracuseStep 2644177 = 1983133) B1983133
theorem B197941475 : Blo 1427533 197941475 := bstep (se 1 (by rfl) ⟨148456106, by rfl⟩ : syracuseStep 197941475 = 296912213) B296912213
theorem B1808659 : Blo 1427533 1808659 := bstep (se 1 (by rfl) ⟨1356494, by rfl⟩ : syracuseStep 1808659 = 2712989) B2712989
theorem B4823441 : Blo 1427533 4823441 := bstep (se 2 (by rfl) ⟨1808790, by rfl⟩ : syracuseStep 4823441 = 3617581) B3617581
theorem B8141381 : Blo 1427533 8141381 := bstep (se 4 (by rfl) ⟨763254, by rfl⟩ : syracuseStep 8141381 = 1526509) B1526509
theorem B4069997 : Blo 1427533 4069997 := bstep (se 3 (by rfl) ⟨763124, by rfl⟩ : syracuseStep 4069997 = 1526249) B1526249
theorem B24402545 : Blo 1427533 24402545 := bstep (se 2 (by rfl) ⟨9150954, by rfl⟩ : syracuseStep 24402545 = 18301909) B18301909
theorem B1628867 : Blo 1427533 1628867 := bstep (se 1 (by rfl) ⟨1221650, by rfl⟩ : syracuseStep 1628867 = 2443301) B2443301
theorem B8133317 : Blo 1427533 8133317 := bstep (se 4 (by rfl) ⟨762498, by rfl⟩ : syracuseStep 8133317 = 1524997) B1524997
theorem B4578029 : Blo 1427533 4578029 := bstep (se 3 (by rfl) ⟨858380, by rfl⟩ : syracuseStep 4578029 = 1716761) B1716761
theorem B1809155 : Blo 1427533 1809155 := bstep (se 1 (by rfl) ⟨1356866, by rfl⟩ : syracuseStep 1809155 = 2713733) B2713733
theorem B4070189 : Blo 1427533 4070189 := bstep (se 3 (by rfl) ⟨763160, by rfl⟩ : syracuseStep 4070189 = 1526321) B1526321
theorem B5421923 : Blo 1427533 5421923 := bstep (se 1 (by rfl) ⟨4066442, by rfl⟩ : syracuseStep 5421923 = 8132885) B8132885
theorem B5421937 : Blo 1427533 5421937 := bstep (se 2 (by rfl) ⟨2033226, by rfl⟩ : syracuseStep 5421937 = 4066453) B4066453
theorem B4823981 : Blo 1427533 4823981 := bstep (se 3 (by rfl) ⟨904496, by rfl⟩ : syracuseStep 4823981 = 1808993) B1808993
theorem B4824035 : Blo 1427533 4824035 := bstep (se 1 (by rfl) ⟨3618026, by rfl⟩ : syracuseStep 4824035 = 7236053) B7236053
theorem B2710513 : Blo 1427533 2710513 := bstep (se 2 (by rfl) ⟨1016442, by rfl⟩ : syracuseStep 2710513 = 2032885) B2032885
theorem B4824305 : Blo 1427533 4824305 := bstep (se 2 (by rfl) ⟨1809114, by rfl⟩ : syracuseStep 4824305 = 3618229) B3618229
theorem B7331149 : Blo 1427533 7331149 := bstep (se 3 (by rfl) ⟨1374590, by rfl⟩ : syracuseStep 7331149 = 2749181) B2749181
theorem B6102449 : Blo 1427533 6102449 := bstep (se 2 (by rfl) ⟨2288418, by rfl⟩ : syracuseStep 6102449 = 4576837) B4576837
theorem B19553717 : Blo 1427533 19553717 := bstep (se 5 (by rfl) ⟨916580, by rfl⟩ : syracuseStep 19553717 = 1833161) B1833161
theorem B7233137 : Blo 1427533 7233137 := bstep (se 2 (by rfl) ⟨2712426, by rfl⟩ : syracuseStep 7233137 = 5424853) B5424853
theorem B2383489 : Blo 1427533 2383489 := bstep (se 2 (by rfl) ⟨893808, by rfl⟩ : syracuseStep 2383489 = 1787617) B1787617
theorem B1957843 : Blo 1427533 1957843 := bstep (se 1 (by rfl) ⟨1468382, by rfl⟩ : syracuseStep 1957843 = 2936765) B2936765
theorem B6103133 : Blo 1427533 6103133 := bstep (se 3 (by rfl) ⟨1144337, by rfl⟩ : syracuseStep 6103133 = 2288675) B2288675
theorem B2711819 : Blo 1427533 2711819 := bstep (se 1 (by rfl) ⟨2033864, by rfl⟩ : syracuseStep 2711819 = 4067729) B4067729
theorem B2711873 : Blo 1427533 2711873 := bstep (se 2 (by rfl) ⟨1016952, by rfl⟩ : syracuseStep 2711873 = 2033905) B2033905
theorem B1606027 : Blo 1427533 1606027 := bstep (se 1 (by rfl) ⟨1204520, by rfl⟩ : syracuseStep 1606027 = 2409041) B2409041
theorem B5497267 : Blo 1427533 5497267 := bstep (se 1 (by rfl) ⟨4122950, by rfl⟩ : syracuseStep 5497267 = 8245901) B8245901
theorem B5145049 : Blo 1427533 5145049 := bstep (se 2 (by rfl) ⟨1929393, by rfl⟩ : syracuseStep 5145049 = 3858787) B3858787
theorem B1606135 : Blo 1427533 1606135 := bstep (se 1 (by rfl) ⟨1204601, by rfl⟩ : syracuseStep 1606135 = 2409203) B2409203
theorem B1606315 : Blo 1427533 1606315 := bstep (se 1 (by rfl) ⟨1204736, by rfl⟩ : syracuseStep 1606315 = 2409473) B2409473
theorem B3211955 : Blo 1427533 3211955 := bstep (se 1 (by rfl) ⟨2408966, by rfl⟩ : syracuseStep 3211955 = 4817933) B4817933
theorem B3211991 : Blo 1427533 3211991 := bstep (se 1 (by rfl) ⟨2408993, by rfl⟩ : syracuseStep 3211991 = 4817987) B4817987
theorem B1606423 : Blo 1427533 1606423 := bstep (se 1 (by rfl) ⟨1204817, by rfl⟩ : syracuseStep 1606423 = 2409635) B2409635
theorem B1524587 : Blo 1427533 1524587 := bstep (se 1 (by rfl) ⟨1143440, by rfl⟩ : syracuseStep 1524587 = 2286881) B2286881
theorem B3212171 : Blo 1427533 3212171 := bstep (se 1 (by rfl) ⟨2409128, by rfl⟩ : syracuseStep 3212171 = 4818257) B4818257
theorem B3212225 : Blo 1427533 3212225 := bstep (se 2 (by rfl) ⟨1204584, by rfl⟩ : syracuseStep 3212225 = 2409169) B2409169
theorem B3613643 : Blo 1427533 3613643 := bstep (se 1 (by rfl) ⟨2710232, by rfl⟩ : syracuseStep 3613643 = 5420465) B5420465
theorem B2409419 : Blo 1427533 2409419 := bstep (se 1 (by rfl) ⟨1807064, by rfl⟩ : syracuseStep 2409419 = 3614129) B3614129
theorem B1606603 : Blo 1427533 1606603 := bstep (se 1 (by rfl) ⟨1204952, by rfl⟩ : syracuseStep 1606603 = 2409905) B2409905
theorem B1606711 : Blo 1427533 1606711 := bstep (se 1 (by rfl) ⟨1205033, by rfl⟩ : syracuseStep 1606711 = 2410067) B2410067
theorem B6865985 : Blo 1427533 6865985 := bstep (se 2 (by rfl) ⟨2574744, by rfl⟩ : syracuseStep 6865985 = 5149489) B5149489
theorem B2409547 : Blo 1427533 2409547 := bstep (se 1 (by rfl) ⟨1807160, by rfl⟩ : syracuseStep 2409547 = 3614321) B3614321
theorem B6186077 : Blo 1427533 6186077 := bstep (se 3 (by rfl) ⟨1159889, by rfl⟩ : syracuseStep 6186077 = 2319779) B2319779
theorem B3212441 : Blo 1427533 3212441 := bstep (se 2 (by rfl) ⟨1204665, by rfl⟩ : syracuseStep 3212441 = 2409331) B2409331
theorem B2573527 : Blo 1427533 2573527 := bstep (se 1 (by rfl) ⟨1930145, by rfl⟩ : syracuseStep 2573527 = 3860291) B3860291
theorem B2712791 : Blo 1427533 2712791 := bstep (se 1 (by rfl) ⟨2034593, by rfl⟩ : syracuseStep 2712791 = 4069187) B4069187
theorem B2409689 : Blo 1427533 2409689 := bstep (se 2 (by rfl) ⟨903633, by rfl⟩ : syracuseStep 2409689 = 1807267) B1807267
theorem B1606891 : Blo 1427533 1606891 := bstep (se 1 (by rfl) ⟨1205168, by rfl⟩ : syracuseStep 1606891 = 2410337) B2410337
theorem B3212531 : Blo 1427533 3212531 := bstep (se 1 (by rfl) ⟨2409398, by rfl⟩ : syracuseStep 3212531 = 4818797) B4818797
theorem B3212567 : Blo 1427533 3212567 := bstep (se 1 (by rfl) ⟨2409425, by rfl⟩ : syracuseStep 3212567 = 4818851) B4818851
theorem B2573591 : Blo 1427533 2573591 := bstep (se 1 (by rfl) ⟨1930193, by rfl⟩ : syracuseStep 2573591 = 3860387) B3860387
theorem B3614017 : Blo 1427533 3614017 := bstep (se 2 (by rfl) ⟨1355256, by rfl⟩ : syracuseStep 3614017 = 2710513) B2710513
theorem B18302273 : Blo 1427533 18302273 := bstep (se 2 (by rfl) ⟨6863352, by rfl⟩ : syracuseStep 18302273 = 13726705) B13726705
theorem B1606999 : Blo 1427533 1606999 := bstep (se 1 (by rfl) ⟨1205249, by rfl⟩ : syracuseStep 1606999 = 2410499) B2410499
theorem B2409817 : Blo 1427533 2409817 := bstep (se 2 (by rfl) ⟨903681, by rfl⟩ : syracuseStep 2409817 = 1807363) B1807363
theorem B5793113 : Blo 1427533 5793113 := bstep (se 2 (by rfl) ⟨2172417, by rfl⟩ : syracuseStep 5793113 = 4344835) B4344835
theorem B3859805 : Blo 1427533 3859805 := bstep (se 3 (by rfl) ⟨723713, by rfl⟩ : syracuseStep 3859805 = 1447427) B1447427
theorem B26076593 : Blo 1427533 26076593 := bstep (se 2 (by rfl) ⟨9778722, by rfl⟩ : syracuseStep 26076593 = 19557445) B19557445
theorem B3212747 : Blo 1427533 3212747 := bstep (se 1 (by rfl) ⟨2409560, by rfl⟩ : syracuseStep 3212747 = 4819121) B4819121
theorem B2033113 : Blo 1427533 2033113 := bstep (se 2 (by rfl) ⟨762417, by rfl⟩ : syracuseStep 2033113 = 1524835) B1524835
theorem B46368227 : Blo 1427533 46368227 := bstep (se 1 (by rfl) ⟨34776170, by rfl⟩ : syracuseStep 46368227 = 69552341) B69552341
theorem B3212801 : Blo 1427533 3212801 := bstep (se 2 (by rfl) ⟨1204800, by rfl⟩ : syracuseStep 3212801 = 2409601) B2409601
theorem B1607179 : Blo 1427533 1607179 := bstep (se 1 (by rfl) ⟨1205384, by rfl⟩ : syracuseStep 1607179 = 2410769) B2410769
theorem B1607287 : Blo 1427533 1607287 := bstep (se 1 (by rfl) ⟨1205465, by rfl⟩ : syracuseStep 1607287 = 2410931) B2410931
theorem B4818635 : Blo 1427533 4818635 := bstep (se 1 (by rfl) ⟨3613976, by rfl⟩ : syracuseStep 4818635 = 7227953) B7227953
theorem B3213017 : Blo 1427533 3213017 := bstep (se 2 (by rfl) ⟨1204881, by rfl⟩ : syracuseStep 3213017 = 2409763) B2409763
theorem B2713331 : Blo 1427533 2713331 := bstep (se 1 (by rfl) ⟨2034998, by rfl⟩ : syracuseStep 2713331 = 4069997) B4069997
theorem B10848005 : Blo 1427533 10848005 := bstep (se 4 (by rfl) ⟨1017000, by rfl⟩ : syracuseStep 10848005 = 2034001) B2034001
theorem B9774865 : Blo 1427533 9774865 := bstep (se 2 (by rfl) ⟨3665574, by rfl⟩ : syracuseStep 9774865 = 7331149) B7331149
theorem B1607467 : Blo 1427533 1607467 := bstep (se 1 (by rfl) ⟨1205600, by rfl⟩ : syracuseStep 1607467 = 2411201) B2411201
theorem B3213107 : Blo 1427533 3213107 := bstep (se 1 (by rfl) ⟨2409830, by rfl⟩ : syracuseStep 3213107 = 4819661) B4819661
theorem B5146433 : Blo 1427533 5146433 := bstep (se 2 (by rfl) ⟨1929912, by rfl⟩ : syracuseStep 5146433 = 3859825) B3859825
theorem B3213143 : Blo 1427533 3213143 := bstep (se 1 (by rfl) ⟨2409857, by rfl⟩ : syracuseStep 3213143 = 4819715) B4819715
theorem B4343645 : Blo 1427533 4343645 := bstep (se 3 (by rfl) ⟨814433, by rfl⟩ : syracuseStep 4343645 = 1628867) B1628867
theorem B3614615 : Blo 1427533 3614615 := bstep (se 1 (by rfl) ⟨2710961, by rfl⟩ : syracuseStep 3614615 = 5421923) B5421923
theorem B2410391 : Blo 1427533 2410391 := bstep (se 1 (by rfl) ⟨1807793, by rfl⟩ : syracuseStep 2410391 = 3615587) B3615587
theorem B1525655 : Blo 1427533 1525655 := bstep (se 1 (by rfl) ⟨1144241, by rfl⟩ : syracuseStep 1525655 = 2288483) B2288483
theorem B1607575 : Blo 1427533 1607575 := bstep (se 1 (by rfl) ⟨1205681, by rfl⟩ : syracuseStep 1607575 = 2411363) B2411363
theorem B4818905 : Blo 1427533 4818905 := bstep (se 2 (by rfl) ⟨1807089, by rfl⟩ : syracuseStep 4818905 = 3614179) B3614179
theorem B3213323 : Blo 1427533 3213323 := bstep (se 1 (by rfl) ⟨2409992, by rfl⟩ : syracuseStep 3213323 = 4819985) B4819985
theorem B2410519 : Blo 1427533 2410519 := bstep (se 1 (by rfl) ⟨1807889, by rfl⟩ : syracuseStep 2410519 = 3615779) B3615779
theorem B3213377 : Blo 1427533 3213377 := bstep (se 2 (by rfl) ⟨1205016, by rfl⟩ : syracuseStep 3213377 = 2410033) B2410033
theorem B7227467 : Blo 1427533 7227467 := bstep (se 1 (by rfl) ⟨5420600, by rfl⟩ : syracuseStep 7227467 = 10841201) B10841201
theorem B1607755 : Blo 1427533 1607755 := bstep (se 1 (by rfl) ⟨1205816, by rfl⟩ : syracuseStep 1607755 = 2411633) B2411633
theorem B1427543 : Blo 1427533 1427543 := bstep (se 1 (by rfl) ⟨1070657, by rfl⟩ : syracuseStep 1427543 = 2141315) B2141315
theorem B3049559 : Blo 1427533 3049559 := bstep (se 1 (by rfl) ⟨2287169, by rfl⟩ : syracuseStep 3049559 = 4574339) B4574339
theorem B1427563 : Blo 1427533 1427563 := bstep (se 1 (by rfl) ⟨1070672, by rfl⟩ : syracuseStep 1427563 = 2141345) B2141345
theorem B1427575 : Blo 1427533 1427575 := bstep (se 1 (by rfl) ⟨1070681, by rfl⟩ : syracuseStep 1427575 = 2141363) B2141363
theorem B1427595 : Blo 1427533 1427595 := bstep (se 1 (by rfl) ⟨1070696, by rfl⟩ : syracuseStep 1427595 = 2141393) B2141393
theorem B1427607 : Blo 1427533 1427607 := bstep (se 1 (by rfl) ⟨1070705, by rfl⟩ : syracuseStep 1427607 = 2141411) B2141411
theorem B1738903 : Blo 1427533 1738903 := bstep (se 1 (by rfl) ⟨1304177, by rfl⟩ : syracuseStep 1738903 = 2608355) B2608355
theorem B1427627 : Blo 1427533 1427627 := bstep (se 1 (by rfl) ⟨1070720, by rfl⟩ : syracuseStep 1427627 = 2141441) B2141441
theorem B5425325 : Blo 1427533 5425325 := bstep (se 3 (by rfl) ⟨1017248, by rfl⟩ : syracuseStep 5425325 = 2034497) B2034497
theorem B1427639 : Blo 1427533 1427639 := bstep (se 1 (by rfl) ⟨1070729, by rfl⟩ : syracuseStep 1427639 = 2141459) B2141459
theorem B1607863 : Blo 1427533 1607863 := bstep (se 1 (by rfl) ⟨1205897, by rfl⟩ : syracuseStep 1607863 = 2411795) B2411795
theorem B1427659 : Blo 1427533 1427659 := bstep (se 1 (by rfl) ⟨1070744, by rfl⟩ : syracuseStep 1427659 = 2141489) B2141489
theorem B1427671 : Blo 1427533 1427671 := bstep (se 1 (by rfl) ⟨1070753, by rfl⟩ : syracuseStep 1427671 = 2141507) B2141507
theorem B4065497 : Blo 1427533 4065497 := bstep (se 2 (by rfl) ⟨1524561, by rfl⟩ : syracuseStep 4065497 = 3049123) B3049123
theorem B2713817 : Blo 1427533 2713817 := bstep (se 2 (by rfl) ⟨1017681, by rfl⟩ : syracuseStep 2713817 = 2035363) B2035363
theorem B1427691 : Blo 1427533 1427691 := bstep (se 1 (by rfl) ⟨1070768, by rfl⟩ : syracuseStep 1427691 = 2141537) B2141537
theorem B1427703 : Blo 1427533 1427703 := bstep (se 1 (by rfl) ⟨1070777, by rfl⟩ : syracuseStep 1427703 = 2141555) B2141555
theorem B1427723 : Blo 1427533 1427723 := bstep (se 1 (by rfl) ⟨1070792, by rfl⟩ : syracuseStep 1427723 = 2141585) B2141585
theorem B1427735 : Blo 1427533 1427735 := bstep (se 1 (by rfl) ⟨1070801, by rfl⟩ : syracuseStep 1427735 = 2141603) B2141603
theorem B3213593 : Blo 1427533 3213593 := bstep (se 2 (by rfl) ⟨1205097, by rfl⟩ : syracuseStep 3213593 = 2410195) B2410195
theorem B13035811 : Blo 1427533 13035811 := bstep (se 1 (by rfl) ⟨9776858, by rfl⟩ : syracuseStep 13035811 = 19553717) B19553717
theorem B1427755 : Blo 1427533 1427755 := bstep (se 1 (by rfl) ⟨1070816, by rfl⟩ : syracuseStep 1427755 = 2141633) B2141633
theorem B1427767 : Blo 1427533 1427767 := bstep (se 1 (by rfl) ⟨1070825, by rfl⟩ : syracuseStep 1427767 = 2141651) B2141651
theorem B1427787 : Blo 1427533 1427787 := bstep (se 1 (by rfl) ⟨1070840, by rfl⟩ : syracuseStep 1427787 = 2141681) B2141681
theorem B1427799 : Blo 1427533 1427799 := bstep (se 1 (by rfl) ⟨1070849, by rfl⟩ : syracuseStep 1427799 = 2141699) B2141699
theorem B1427819 : Blo 1427533 1427819 := bstep (se 1 (by rfl) ⟨1070864, by rfl⟩ : syracuseStep 1427819 = 2141729) B2141729
theorem B1608043 : Blo 1427533 1608043 := bstep (se 1 (by rfl) ⟨1206032, by rfl⟩ : syracuseStep 1608043 = 2412065) B2412065
theorem B3213683 : Blo 1427533 3213683 := bstep (se 1 (by rfl) ⟨2410262, by rfl⟩ : syracuseStep 3213683 = 4820525) B4820525
theorem B1427831 : Blo 1427533 1427831 := bstep (se 1 (by rfl) ⟨1070873, by rfl⟩ : syracuseStep 1427831 = 2141747) B2141747
theorem B1427851 : Blo 1427533 1427851 := bstep (se 1 (by rfl) ⟨1070888, by rfl⟩ : syracuseStep 1427851 = 2141777) B2141777
theorem B1427863 : Blo 1427533 1427863 := bstep (se 1 (by rfl) ⟨1070897, by rfl⟩ : syracuseStep 1427863 = 2141795) B2141795
theorem B3213719 : Blo 1427533 3213719 := bstep (se 1 (by rfl) ⟨2410289, by rfl⟩ : syracuseStep 3213719 = 4820579) B4820579
theorem B1427883 : Blo 1427533 1427883 := bstep (se 1 (by rfl) ⟨1070912, by rfl⟩ : syracuseStep 1427883 = 2141825) B2141825
theorem B1427895 : Blo 1427533 1427895 := bstep (se 1 (by rfl) ⟨1070921, by rfl⟩ : syracuseStep 1427895 = 2141843) B2141843
theorem B1427915 : Blo 1427533 1427915 := bstep (se 1 (by rfl) ⟨1070936, by rfl⟩ : syracuseStep 1427915 = 2141873) B2141873
theorem B1427927 : Blo 1427533 1427927 := bstep (se 1 (by rfl) ⟨1070945, by rfl⟩ : syracuseStep 1427927 = 2141891) B2141891
theorem B1608151 : Blo 1427533 1608151 := bstep (se 1 (by rfl) ⟨1206113, by rfl⟩ : syracuseStep 1608151 = 2412227) B2412227
theorem B1427947 : Blo 1427533 1427947 := bstep (se 1 (by rfl) ⟨1070960, by rfl⟩ : syracuseStep 1427947 = 2141921) B2141921
theorem B1427959 : Blo 1427533 1427959 := bstep (se 1 (by rfl) ⟨1070969, by rfl⟩ : syracuseStep 1427959 = 2141939) B2141939
theorem B12200453 : Blo 1427533 12200453 := bstep (se 4 (by rfl) ⟨1143792, by rfl⟩ : syracuseStep 12200453 = 2287585) B2287585
theorem B1427979 : Blo 1427533 1427979 := bstep (se 1 (by rfl) ⟨1070984, by rfl⟩ : syracuseStep 1427979 = 2141969) B2141969
theorem B4065815 : Blo 1427533 4065815 := bstep (se 1 (by rfl) ⟨3049361, by rfl⟩ : syracuseStep 4065815 = 6098723) B6098723
theorem B1427991 : Blo 1427533 1427991 := bstep (se 1 (by rfl) ⟨1070993, by rfl⟩ : syracuseStep 1427991 = 2141987) B2141987
theorem B1428011 : Blo 1427533 1428011 := bstep (se 1 (by rfl) ⟨1071008, by rfl⟩ : syracuseStep 1428011 = 2142017) B2142017
theorem B1428023 : Blo 1427533 1428023 := bstep (se 1 (by rfl) ⟨1071017, by rfl⟩ : syracuseStep 1428023 = 2142035) B2142035
theorem B1428043 : Blo 1427533 1428043 := bstep (se 1 (by rfl) ⟨1071032, by rfl⟩ : syracuseStep 1428043 = 2142065) B2142065
theorem B3213899 : Blo 1427533 3213899 := bstep (se 1 (by rfl) ⟨2410424, by rfl⟩ : syracuseStep 3213899 = 4820849) B4820849
theorem B1428055 : Blo 1427533 1428055 := bstep (se 1 (by rfl) ⟨1071041, by rfl⟩ : syracuseStep 1428055 = 2142083) B2142083
theorem B1428075 : Blo 1427533 1428075 := bstep (se 1 (by rfl) ⟨1071056, by rfl⟩ : syracuseStep 1428075 = 2142113) B2142113
theorem B1428087 : Blo 1427533 1428087 := bstep (se 1 (by rfl) ⟨1071065, by rfl⟩ : syracuseStep 1428087 = 2142131) B2142131
theorem B3213953 : Blo 1427533 3213953 := bstep (se 2 (by rfl) ⟨1205232, by rfl⟩ : syracuseStep 3213953 = 2410465) B2410465
theorem B1428107 : Blo 1427533 1428107 := bstep (se 1 (by rfl) ⟨1071080, by rfl⟩ : syracuseStep 1428107 = 2142161) B2142161
theorem B2411147 : Blo 1427533 2411147 := bstep (se 1 (by rfl) ⟨1808360, by rfl⟩ : syracuseStep 2411147 = 3616721) B3616721
theorem B4819607 : Blo 1427533 4819607 := bstep (se 1 (by rfl) ⟨3614705, by rfl⟩ : syracuseStep 4819607 = 7229411) B7229411
theorem B1428119 : Blo 1427533 1428119 := bstep (se 1 (by rfl) ⟨1071089, by rfl⟩ : syracuseStep 1428119 = 2142179) B2142179
theorem B1428139 : Blo 1427533 1428139 := bstep (se 1 (by rfl) ⟨1071104, by rfl⟩ : syracuseStep 1428139 = 2142209) B2142209
theorem B1428151 : Blo 1427533 1428151 := bstep (se 1 (by rfl) ⟨1071113, by rfl⟩ : syracuseStep 1428151 = 2142227) B2142227
theorem B3615425 : Blo 1427533 3615425 := bstep (se 2 (by rfl) ⟨1355784, by rfl⟩ : syracuseStep 3615425 = 2711569) B2711569
theorem B1428171 : Blo 1427533 1428171 := bstep (se 1 (by rfl) ⟨1071128, by rfl⟩ : syracuseStep 1428171 = 2142257) B2142257
theorem B1428183 : Blo 1427533 1428183 := bstep (se 1 (by rfl) ⟨1071137, by rfl⟩ : syracuseStep 1428183 = 2142275) B2142275
theorem B3861209 : Blo 1427533 3861209 := bstep (se 2 (by rfl) ⟨1447953, by rfl⟩ : syracuseStep 3861209 = 2895907) B2895907
theorem B1428203 : Blo 1427533 1428203 := bstep (se 1 (by rfl) ⟨1071152, by rfl⟩ : syracuseStep 1428203 = 2142305) B2142305
theorem B1428215 : Blo 1427533 1428215 := bstep (se 1 (by rfl) ⟨1071161, by rfl⟩ : syracuseStep 1428215 = 2142323) B2142323
theorem B1428235 : Blo 1427533 1428235 := bstep (se 1 (by rfl) ⟨1071176, by rfl⟩ : syracuseStep 1428235 = 2142353) B2142353
theorem B2411275 : Blo 1427533 2411275 := bstep (se 1 (by rfl) ⟨1808456, by rfl⟩ : syracuseStep 2411275 = 3616913) B3616913
theorem B1428247 : Blo 1427533 1428247 := bstep (se 1 (by rfl) ⟨1071185, by rfl⟩ : syracuseStep 1428247 = 2142371) B2142371
theorem B1428267 : Blo 1427533 1428267 := bstep (se 1 (by rfl) ⟨1071200, by rfl⟩ : syracuseStep 1428267 = 2142401) B2142401
theorem B1428279 : Blo 1427533 1428279 := bstep (se 1 (by rfl) ⟨1071209, by rfl⟩ : syracuseStep 1428279 = 2142419) B2142419
theorem B1428299 : Blo 1427533 1428299 := bstep (se 1 (by rfl) ⟨1071224, by rfl⟩ : syracuseStep 1428299 = 2142449) B2142449
theorem B1428311 : Blo 1427533 1428311 := bstep (se 1 (by rfl) ⟨1071233, by rfl⟩ : syracuseStep 1428311 = 2142467) B2142467
theorem B3214169 : Blo 1427533 3214169 := bstep (se 2 (by rfl) ⟨1205313, by rfl⟩ : syracuseStep 3214169 = 2410627) B2410627
theorem B1428331 : Blo 1427533 1428331 := bstep (se 1 (by rfl) ⟨1071248, by rfl⟩ : syracuseStep 1428331 = 2142497) B2142497
theorem B2894707 : Blo 1427533 2894707 := bstep (se 1 (by rfl) ⟨2171030, by rfl⟩ : syracuseStep 2894707 = 4342061) B4342061
theorem B1428343 : Blo 1427533 1428343 := bstep (se 1 (by rfl) ⟨1071257, by rfl⟩ : syracuseStep 1428343 = 2142515) B2142515
theorem B1428363 : Blo 1427533 1428363 := bstep (se 1 (by rfl) ⟨1071272, by rfl⟩ : syracuseStep 1428363 = 2142545) B2142545
theorem B2034571 : Blo 1427533 2034571 := bstep (se 1 (by rfl) ⟨1525928, by rfl⟩ : syracuseStep 2034571 = 3051857) B3051857
theorem B1428375 : Blo 1427533 1428375 := bstep (se 1 (by rfl) ⟨1071281, by rfl⟩ : syracuseStep 1428375 = 2142563) B2142563
theorem B2411417 : Blo 1427533 2411417 := bstep (se 2 (by rfl) ⟨904281, by rfl⟩ : syracuseStep 2411417 = 1808563) B1808563
theorem B1428395 : Blo 1427533 1428395 := bstep (se 1 (by rfl) ⟨1071296, by rfl⟩ : syracuseStep 1428395 = 2142593) B2142593
theorem B5794733 : Blo 1427533 5794733 := bstep (se 3 (by rfl) ⟨1086512, by rfl⟩ : syracuseStep 5794733 = 2173025) B2173025
theorem B2894771 : Blo 1427533 2894771 := bstep (se 1 (by rfl) ⟨2171078, by rfl⟩ : syracuseStep 2894771 = 4342157) B4342157
theorem B3214259 : Blo 1427533 3214259 := bstep (se 1 (by rfl) ⟨2410694, by rfl⟩ : syracuseStep 3214259 = 4821389) B4821389
theorem B5426099 : Blo 1427533 5426099 := bstep (se 1 (by rfl) ⟨4069574, by rfl⟩ : syracuseStep 5426099 = 8139149) B8139149
theorem B1428407 : Blo 1427533 1428407 := bstep (se 1 (by rfl) ⟨1071305, by rfl⟩ : syracuseStep 1428407 = 2142611) B2142611
theorem B3525569 : Blo 1427533 3525569 := bstep (se 2 (by rfl) ⟨1322088, by rfl⟩ : syracuseStep 3525569 = 2644177) B2644177
theorem B1428427 : Blo 1427533 1428427 := bstep (se 1 (by rfl) ⟨1071320, by rfl⟩ : syracuseStep 1428427 = 2142641) B2142641
theorem B3050455 : Blo 1427533 3050455 := bstep (se 1 (by rfl) ⟨2287841, by rfl⟩ : syracuseStep 3050455 = 4575683) B4575683
theorem B1428439 : Blo 1427533 1428439 := bstep (se 1 (by rfl) ⟨1071329, by rfl⟩ : syracuseStep 1428439 = 2142659) B2142659
theorem B3214295 : Blo 1427533 3214295 := bstep (se 1 (by rfl) ⟨2410721, by rfl⟩ : syracuseStep 3214295 = 4821443) B4821443
theorem B1428459 : Blo 1427533 1428459 := bstep (se 1 (by rfl) ⟨1071344, by rfl⟩ : syracuseStep 1428459 = 2142689) B2142689
theorem B1428471 : Blo 1427533 1428471 := bstep (se 1 (by rfl) ⟨1071353, by rfl⟩ : syracuseStep 1428471 = 2142707) B2142707
theorem B11578373 : Blo 1427533 11578373 := bstep (se 4 (by rfl) ⟨1085472, by rfl⟩ : syracuseStep 11578373 = 2170945) B2170945
theorem B1428491 : Blo 1427533 1428491 := bstep (se 1 (by rfl) ⟨1071368, by rfl⟩ : syracuseStep 1428491 = 2142737) B2142737
theorem B1428503 : Blo 1427533 1428503 := bstep (se 1 (by rfl) ⟨1071377, by rfl⟩ : syracuseStep 1428503 = 2142755) B2142755
theorem B2411545 : Blo 1427533 2411545 := bstep (se 2 (by rfl) ⟨904329, by rfl⟩ : syracuseStep 2411545 = 1808659) B1808659
theorem B1428523 : Blo 1427533 1428523 := bstep (se 1 (by rfl) ⟨1071392, by rfl⟩ : syracuseStep 1428523 = 2142785) B2142785
theorem B1428535 : Blo 1427533 1428535 := bstep (se 1 (by rfl) ⟨1071401, by rfl⟩ : syracuseStep 1428535 = 2142803) B2142803
theorem B1428555 : Blo 1427533 1428555 := bstep (se 1 (by rfl) ⟨1071416, by rfl⟩ : syracuseStep 1428555 = 2142833) B2142833
theorem B1428567 : Blo 1427533 1428567 := bstep (se 1 (by rfl) ⟨1071425, by rfl⟩ : syracuseStep 1428567 = 2142851) B2142851
theorem B6868061 : Blo 1427533 6868061 := bstep (se 3 (by rfl) ⟨1287761, by rfl⟩ : syracuseStep 6868061 = 2575523) B2575523
theorem B7236701 : Blo 1427533 7236701 := bstep (se 3 (by rfl) ⟨1356881, by rfl⟩ : syracuseStep 7236701 = 2713763) B2713763
theorem B1428587 : Blo 1427533 1428587 := bstep (se 1 (by rfl) ⟨1071440, by rfl⟩ : syracuseStep 1428587 = 2142881) B2142881
theorem B1428599 : Blo 1427533 1428599 := bstep (se 1 (by rfl) ⟨1071449, by rfl⟩ : syracuseStep 1428599 = 2142899) B2142899
theorem B1428619 : Blo 1427533 1428619 := bstep (se 1 (by rfl) ⟨1071464, by rfl⟩ : syracuseStep 1428619 = 2142929) B2142929
theorem B3214475 : Blo 1427533 3214475 := bstep (se 1 (by rfl) ⟨2410856, by rfl⟩ : syracuseStep 3214475 = 4821713) B4821713
theorem B1428631 : Blo 1427533 1428631 := bstep (se 1 (by rfl) ⟨1071473, by rfl⟩ : syracuseStep 1428631 = 2142947) B2142947
theorem B1428651 : Blo 1427533 1428651 := bstep (se 1 (by rfl) ⟨1071488, by rfl⟩ : syracuseStep 1428651 = 2142977) B2142977
theorem B12201137 : Blo 1427533 12201137 := bstep (se 2 (by rfl) ⟨4575426, by rfl⟩ : syracuseStep 12201137 = 9150853) B9150853
theorem B4820147 : Blo 1427533 4820147 := bstep (se 1 (by rfl) ⟨3615110, by rfl⟩ : syracuseStep 4820147 = 7230221) B7230221
theorem B1428663 : Blo 1427533 1428663 := bstep (se 1 (by rfl) ⟨1071497, by rfl⟩ : syracuseStep 1428663 = 2142995) B2142995
theorem B3214529 : Blo 1427533 3214529 := bstep (se 2 (by rfl) ⟨1205448, by rfl⟩ : syracuseStep 3214529 = 2410897) B2410897
theorem B2141387 : Blo 1427533 2141387 := bstep (se 1 (by rfl) ⟨1606040, by rfl⟩ : syracuseStep 2141387 = 3212081) B3212081
theorem B1428683 : Blo 1427533 1428683 := bstep (se 1 (by rfl) ⟨1071512, by rfl⟩ : syracuseStep 1428683 = 2143025) B2143025
theorem B2141399 : Blo 1427533 2141399 := bstep (se 1 (by rfl) ⟨1606049, by rfl⟩ : syracuseStep 2141399 = 3212099) B3212099
theorem B1428695 : Blo 1427533 1428695 := bstep (se 1 (by rfl) ⟨1071521, by rfl⟩ : syracuseStep 1428695 = 2143043) B2143043
theorem B3615961 : Blo 1427533 3615961 := bstep (se 2 (by rfl) ⟨1355985, by rfl⟩ : syracuseStep 3615961 = 2711971) B2711971
theorem B1428715 : Blo 1427533 1428715 := bstep (se 1 (by rfl) ⟨1071536, by rfl⟩ : syracuseStep 1428715 = 2143073) B2143073
theorem B1428727 : Blo 1427533 1428727 := bstep (se 1 (by rfl) ⟨1071545, by rfl⟩ : syracuseStep 1428727 = 2143091) B2143091
theorem B1428747 : Blo 1427533 1428747 := bstep (se 1 (by rfl) ⟨1071560, by rfl⟩ : syracuseStep 1428747 = 2143121) B2143121
theorem B6188305 : Blo 1427533 6188305 := bstep (se 2 (by rfl) ⟨2320614, by rfl⟩ : syracuseStep 6188305 = 4641229) B4641229
theorem B1428759 : Blo 1427533 1428759 := bstep (se 1 (by rfl) ⟨1071569, by rfl⟩ : syracuseStep 1428759 = 2143139) B2143139
theorem B2141465 : Blo 1427533 2141465 := bstep (se 2 (by rfl) ⟨803049, by rfl⟩ : syracuseStep 2141465 = 1606099) B1606099
theorem B1428779 : Blo 1427533 1428779 := bstep (se 1 (by rfl) ⟨1071584, by rfl⟩ : syracuseStep 1428779 = 2143169) B2143169
theorem B1428791 : Blo 1427533 1428791 := bstep (se 1 (by rfl) ⟨1071593, by rfl⟩ : syracuseStep 1428791 = 2143187) B2143187
theorem B4066625 : Blo 1427533 4066625 := bstep (se 2 (by rfl) ⟨1524984, by rfl⟩ : syracuseStep 4066625 = 3049969) B3049969
theorem B15445313 : Blo 1427533 15445313 := bstep (se 2 (by rfl) ⟨5791992, by rfl⟩ : syracuseStep 15445313 = 11583985) B11583985
theorem B1428811 : Blo 1427533 1428811 := bstep (se 1 (by rfl) ⟨1071608, by rfl⟩ : syracuseStep 1428811 = 2143217) B2143217
theorem B1428823 : Blo 1427533 1428823 := bstep (se 1 (by rfl) ⟨1071617, by rfl⟩ : syracuseStep 1428823 = 2143235) B2143235
theorem B1428843 : Blo 1427533 1428843 := bstep (se 1 (by rfl) ⟨1071632, by rfl⟩ : syracuseStep 1428843 = 2143265) B2143265
theorem B1428855 : Blo 1427533 1428855 := bstep (se 1 (by rfl) ⟨1071641, by rfl⟩ : syracuseStep 1428855 = 2143283) B2143283
theorem B2141579 : Blo 1427533 2141579 := bstep (se 1 (by rfl) ⟨1606184, by rfl⟩ : syracuseStep 2141579 = 3212369) B3212369
theorem B1428875 : Blo 1427533 1428875 := bstep (se 1 (by rfl) ⟨1071656, by rfl⟩ : syracuseStep 1428875 = 2143313) B2143313
theorem B2141591 : Blo 1427533 2141591 := bstep (se 1 (by rfl) ⟨1606193, by rfl⟩ : syracuseStep 2141591 = 3212387) B3212387
theorem B7720343 : Blo 1427533 7720343 := bstep (se 1 (by rfl) ⟨5790257, by rfl⟩ : syracuseStep 7720343 = 11580515) B11580515
theorem B3214745 : Blo 1427533 3214745 := bstep (se 2 (by rfl) ⟨1205529, by rfl⟩ : syracuseStep 3214745 = 2411059) B2411059
theorem B1428887 : Blo 1427533 1428887 := bstep (se 1 (by rfl) ⟨1071665, by rfl⟩ : syracuseStep 1428887 = 2143331) B2143331
theorem B1428907 : Blo 1427533 1428907 := bstep (se 1 (by rfl) ⟨1071680, by rfl⟩ : syracuseStep 1428907 = 2143361) B2143361
theorem B24415667 : Blo 1427533 24415667 := bstep (se 1 (by rfl) ⟨18311750, by rfl⟩ : syracuseStep 24415667 = 36623501) B36623501
theorem B1428919 : Blo 1427533 1428919 := bstep (se 1 (by rfl) ⟨1071689, by rfl⟩ : syracuseStep 1428919 = 2143379) B2143379
theorem B4820417 : Blo 1427533 4820417 := bstep (se 2 (by rfl) ⟨1807656, by rfl⟩ : syracuseStep 4820417 = 3615313) B3615313
theorem B1428939 : Blo 1427533 1428939 := bstep (se 1 (by rfl) ⟨1071704, by rfl⟩ : syracuseStep 1428939 = 2143409) B2143409
theorem B1428951 : Blo 1427533 1428951 := bstep (se 1 (by rfl) ⟨1071713, by rfl⟩ : syracuseStep 1428951 = 2143427) B2143427
theorem B2141657 : Blo 1427533 2141657 := bstep (se 2 (by rfl) ⟨803121, by rfl⟩ : syracuseStep 2141657 = 1606243) B1606243
theorem B1428971 : Blo 1427533 1428971 := bstep (se 1 (by rfl) ⟨1071728, by rfl⟩ : syracuseStep 1428971 = 2143457) B2143457
theorem B3214835 : Blo 1427533 3214835 := bstep (se 1 (by rfl) ⟨2411126, by rfl⟩ : syracuseStep 3214835 = 4822253) B4822253
theorem B1428983 : Blo 1427533 1428983 := bstep (se 1 (by rfl) ⟨1071737, by rfl⟩ : syracuseStep 1428983 = 2143475) B2143475
theorem B6098435 : Blo 1427533 6098435 := bstep (se 1 (by rfl) ⟨4573826, by rfl⟩ : syracuseStep 6098435 = 9147653) B9147653
theorem B1429003 : Blo 1427533 1429003 := bstep (se 1 (by rfl) ⟨1071752, by rfl⟩ : syracuseStep 1429003 = 2143505) B2143505
theorem B3214871 : Blo 1427533 3214871 := bstep (se 1 (by rfl) ⟨2411153, by rfl⟩ : syracuseStep 3214871 = 4822307) B4822307
theorem B1429015 : Blo 1427533 1429015 := bstep (se 1 (by rfl) ⟨1071761, by rfl⟩ : syracuseStep 1429015 = 2143523) B2143523
theorem B1429035 : Blo 1427533 1429035 := bstep (se 1 (by rfl) ⟨1071776, by rfl⟩ : syracuseStep 1429035 = 2143553) B2143553
theorem B1429047 : Blo 1427533 1429047 := bstep (se 1 (by rfl) ⟨1071785, by rfl⟩ : syracuseStep 1429047 = 2143571) B2143571
theorem B2141771 : Blo 1427533 2141771 := bstep (se 1 (by rfl) ⟨1606328, by rfl⟩ : syracuseStep 2141771 = 3212657) B3212657
theorem B1429067 : Blo 1427533 1429067 := bstep (se 1 (by rfl) ⟨1071800, by rfl⟩ : syracuseStep 1429067 = 2143601) B2143601
theorem B2141783 : Blo 1427533 2141783 := bstep (se 1 (by rfl) ⟨1606337, by rfl⟩ : syracuseStep 2141783 = 3212675) B3212675
theorem B1429079 : Blo 1427533 1429079 := bstep (se 1 (by rfl) ⟨1071809, by rfl⟩ : syracuseStep 1429079 = 2143619) B2143619
theorem B2289239 : Blo 1427533 2289239 := bstep (se 1 (by rfl) ⟨1716929, by rfl⟩ : syracuseStep 2289239 = 3433859) B3433859
theorem B2412119 : Blo 1427533 2412119 := bstep (se 1 (by rfl) ⟨1809089, by rfl⟩ : syracuseStep 2412119 = 3618179) B3618179
theorem B1429099 : Blo 1427533 1429099 := bstep (se 1 (by rfl) ⟨1071824, by rfl⟩ : syracuseStep 1429099 = 2143649) B2143649
theorem B1429111 : Blo 1427533 1429111 := bstep (se 1 (by rfl) ⟨1071833, by rfl⟩ : syracuseStep 1429111 = 2143667) B2143667
theorem B1429131 : Blo 1427533 1429131 := bstep (se 1 (by rfl) ⟨1071848, by rfl⟩ : syracuseStep 1429131 = 2143697) B2143697
theorem B20582039 : Blo 1427533 20582039 := bstep (se 1 (by rfl) ⟨15436529, by rfl⟩ : syracuseStep 20582039 = 30873059) B30873059
theorem B1429143 : Blo 1427533 1429143 := bstep (se 1 (by rfl) ⟨1071857, by rfl⟩ : syracuseStep 1429143 = 2143715) B2143715
theorem B2141849 : Blo 1427533 2141849 := bstep (se 2 (by rfl) ⟨803193, by rfl⟩ : syracuseStep 2141849 = 1606387) B1606387
theorem B1429163 : Blo 1427533 1429163 := bstep (se 1 (by rfl) ⟨1071872, by rfl⟩ : syracuseStep 1429163 = 2143745) B2143745
theorem B1429175 : Blo 1427533 1429175 := bstep (se 1 (by rfl) ⟨1071881, by rfl⟩ : syracuseStep 1429175 = 2143763) B2143763
theorem B3215051 : Blo 1427533 3215051 := bstep (se 1 (by rfl) ⟨2411288, by rfl⟩ : syracuseStep 3215051 = 4822577) B4822577
theorem B1429195 : Blo 1427533 1429195 := bstep (se 1 (by rfl) ⟨1071896, by rfl⟩ : syracuseStep 1429195 = 2143793) B2143793
theorem B1429207 : Blo 1427533 1429207 := bstep (se 1 (by rfl) ⟨1071905, by rfl⟩ : syracuseStep 1429207 = 2143811) B2143811
theorem B2412247 : Blo 1427533 2412247 := bstep (se 1 (by rfl) ⟨1809185, by rfl⟩ : syracuseStep 2412247 = 3618371) B3618371
theorem B1429227 : Blo 1427533 1429227 := bstep (se 1 (by rfl) ⟨1071920, by rfl⟩ : syracuseStep 1429227 = 2143841) B2143841
theorem B1429239 : Blo 1427533 1429239 := bstep (se 1 (by rfl) ⟨1071929, by rfl⟩ : syracuseStep 1429239 = 2143859) B2143859
theorem B3215105 : Blo 1427533 3215105 := bstep (se 2 (by rfl) ⟨1205664, by rfl⟩ : syracuseStep 3215105 = 2411329) B2411329
theorem B20598533 : Blo 1427533 20598533 := bstep (se 4 (by rfl) ⟨1931112, by rfl⟩ : syracuseStep 20598533 = 3862225) B3862225
theorem B2141963 : Blo 1427533 2141963 := bstep (se 1 (by rfl) ⟨1606472, by rfl⟩ : syracuseStep 2141963 = 3212945) B3212945
theorem B3051275 : Blo 1427533 3051275 := bstep (se 1 (by rfl) ⟨2288456, by rfl⟩ : syracuseStep 3051275 = 4576913) B4576913
theorem B1429259 : Blo 1427533 1429259 := bstep (se 1 (by rfl) ⟨1071944, by rfl⟩ : syracuseStep 1429259 = 2143889) B2143889
theorem B2141975 : Blo 1427533 2141975 := bstep (se 1 (by rfl) ⟨1606481, by rfl⟩ : syracuseStep 2141975 = 3212963) B3212963
theorem B1429271 : Blo 1427533 1429271 := bstep (se 1 (by rfl) ⟨1071953, by rfl⟩ : syracuseStep 1429271 = 2143907) B2143907
theorem B2289431 : Blo 1427533 2289431 := bstep (se 1 (by rfl) ⟨1717073, by rfl⟩ : syracuseStep 2289431 = 3434147) B3434147
theorem B1429291 : Blo 1427533 1429291 := bstep (se 1 (by rfl) ⟨1071968, by rfl⟩ : syracuseStep 1429291 = 2143937) B2143937
theorem B1429303 : Blo 1427533 1429303 := bstep (se 1 (by rfl) ⟨1071977, by rfl⟩ : syracuseStep 1429303 = 2143955) B2143955
theorem B7229249 : Blo 1427533 7229249 := bstep (se 2 (by rfl) ⟨2710968, by rfl⟩ : syracuseStep 7229249 = 5421937) B5421937
theorem B1429323 : Blo 1427533 1429323 := bstep (se 1 (by rfl) ⟨1071992, by rfl⟩ : syracuseStep 1429323 = 2143985) B2143985
theorem B1429335 : Blo 1427533 1429335 := bstep (se 1 (by rfl) ⟨1072001, by rfl⟩ : syracuseStep 1429335 = 2144003) B2144003
theorem B2142041 : Blo 1427533 2142041 := bstep (se 2 (by rfl) ⟨803265, by rfl⟩ : syracuseStep 2142041 = 1606531) B1606531
theorem B1429355 : Blo 1427533 1429355 := bstep (se 1 (by rfl) ⟨1072016, by rfl⟩ : syracuseStep 1429355 = 2144033) B2144033
theorem B1429367 : Blo 1427533 1429367 := bstep (se 1 (by rfl) ⟨1072025, by rfl⟩ : syracuseStep 1429367 = 2144051) B2144051
theorem B1429387 : Blo 1427533 1429387 := bstep (se 1 (by rfl) ⟨1072040, by rfl⟩ : syracuseStep 1429387 = 2144081) B2144081
theorem B2289559 : Blo 1427533 2289559 := bstep (se 1 (by rfl) ⟨1717169, by rfl⟩ : syracuseStep 2289559 = 3434339) B3434339
theorem B1429399 : Blo 1427533 1429399 := bstep (se 1 (by rfl) ⟨1072049, by rfl⟩ : syracuseStep 1429399 = 2144099) B2144099
theorem B1429419 : Blo 1427533 1429419 := bstep (se 1 (by rfl) ⟨1072064, by rfl⟩ : syracuseStep 1429419 = 2144129) B2144129
theorem B26079155 : Blo 1427533 26079155 := bstep (se 1 (by rfl) ⟨19559366, by rfl⟩ : syracuseStep 26079155 = 39118733) B39118733
theorem B1429431 : Blo 1427533 1429431 := bstep (se 1 (by rfl) ⟨1072073, by rfl⟩ : syracuseStep 1429431 = 2144147) B2144147
theorem B2895809 : Blo 1427533 2895809 := bstep (se 2 (by rfl) ⟨1085928, by rfl⟩ : syracuseStep 2895809 = 2171857) B2171857
theorem B2142155 : Blo 1427533 2142155 := bstep (se 1 (by rfl) ⟨1606616, by rfl⟩ : syracuseStep 2142155 = 3213233) B3213233
theorem B1429451 : Blo 1427533 1429451 := bstep (se 1 (by rfl) ⟨1072088, by rfl⟩ : syracuseStep 1429451 = 2144177) B2144177
theorem B2142167 : Blo 1427533 2142167 := bstep (se 1 (by rfl) ⟨1606625, by rfl⟩ : syracuseStep 2142167 = 3213251) B3213251
theorem B1429463 : Blo 1427533 1429463 := bstep (se 1 (by rfl) ⟨1072097, by rfl⟩ : syracuseStep 1429463 = 2144195) B2144195
theorem B3215321 : Blo 1427533 3215321 := bstep (se 2 (by rfl) ⟨1205745, by rfl⟩ : syracuseStep 3215321 = 2411491) B2411491
theorem B4575197 : Blo 1427533 4575197 := bstep (se 3 (by rfl) ⟨857849, by rfl⟩ : syracuseStep 4575197 = 1715699) B1715699
theorem B4820957 : Blo 1427533 4820957 := bstep (se 3 (by rfl) ⟨903929, by rfl⟩ : syracuseStep 4820957 = 1807859) B1807859
theorem B1429483 : Blo 1427533 1429483 := bstep (se 1 (by rfl) ⟨1072112, by rfl⟩ : syracuseStep 1429483 = 2144225) B2144225
theorem B1429495 : Blo 1427533 1429495 := bstep (se 1 (by rfl) ⟨1072121, by rfl⟩ : syracuseStep 1429495 = 2144243) B2144243
theorem B1429515 : Blo 1427533 1429515 := bstep (se 1 (by rfl) ⟨1072136, by rfl⟩ : syracuseStep 1429515 = 2144273) B2144273
theorem B1429527 : Blo 1427533 1429527 := bstep (se 1 (by rfl) ⟨1072145, by rfl⟩ : syracuseStep 1429527 = 2144291) B2144291
theorem B3256345 : Blo 1427533 3256345 := bstep (se 2 (by rfl) ⟨1221129, by rfl⟩ : syracuseStep 3256345 = 2442259) B2442259
theorem B2142233 : Blo 1427533 2142233 := bstep (se 2 (by rfl) ⟨803337, by rfl⟩ : syracuseStep 2142233 = 1606675) B1606675
theorem B3215411 : Blo 1427533 3215411 := bstep (se 1 (by rfl) ⟨2411558, by rfl⟩ : syracuseStep 3215411 = 4823117) B4823117
theorem B3215447 : Blo 1427533 3215447 := bstep (se 1 (by rfl) ⟨2411585, by rfl⟩ : syracuseStep 3215447 = 4823171) B4823171
theorem B4575325 : Blo 1427533 4575325 := bstep (se 3 (by rfl) ⟨857873, by rfl⟩ : syracuseStep 4575325 = 1715747) B1715747
theorem B10850435 : Blo 1427533 10850435 := bstep (se 1 (by rfl) ⟨8137826, by rfl⟩ : syracuseStep 10850435 = 16275653) B16275653
theorem B2142347 : Blo 1427533 2142347 := bstep (se 1 (by rfl) ⟨1606760, by rfl⟩ : syracuseStep 2142347 = 3213521) B3213521
theorem B1929367 : Blo 1427533 1929367 := bstep (se 1 (by rfl) ⟨1447025, by rfl⟩ : syracuseStep 1929367 = 2894051) B2894051
theorem B2142359 : Blo 1427533 2142359 := bstep (se 1 (by rfl) ⟨1606769, by rfl⟩ : syracuseStep 2142359 = 3213539) B3213539
theorem B131960983 : Blo 1427533 131960983 := bstep (se 1 (by rfl) ⟨98970737, by rfl⟩ : syracuseStep 131960983 = 197941475) B197941475
theorem B12202163 : Blo 1427533 12202163 := bstep (se 1 (by rfl) ⟨9151622, by rfl⟩ : syracuseStep 12202163 = 18303245) B18303245
theorem B2142425 : Blo 1427533 2142425 := bstep (se 2 (by rfl) ⟨803409, by rfl⟩ : syracuseStep 2142425 = 1606819) B1606819
theorem B3215627 : Blo 1427533 3215627 := bstep (se 1 (by rfl) ⟨2411720, by rfl⟩ : syracuseStep 3215627 = 4823441) B4823441
theorem B3617075 : Blo 1427533 3617075 := bstep (se 1 (by rfl) ⟨2712806, by rfl⟩ : syracuseStep 3617075 = 5425613) B5425613
theorem B3215681 : Blo 1427533 3215681 := bstep (se 2 (by rfl) ⟨1205880, by rfl⟩ : syracuseStep 3215681 = 2411761) B2411761
theorem B2142539 : Blo 1427533 2142539 := bstep (se 1 (by rfl) ⟨1606904, by rfl⟩ : syracuseStep 2142539 = 3213809) B3213809
theorem B2142551 : Blo 1427533 2142551 := bstep (se 1 (by rfl) ⟨1606913, by rfl⟩ : syracuseStep 2142551 = 3213827) B3213827
theorem B4575581 : Blo 1427533 4575581 := bstep (se 3 (by rfl) ⟨857921, by rfl⟩ : syracuseStep 4575581 = 1715843) B1715843
theorem B3256691 : Blo 1427533 3256691 := bstep (se 1 (by rfl) ⟨2442518, by rfl⟩ : syracuseStep 3256691 = 4885037) B4885037
theorem B15446389 : Blo 1427533 15446389 := bstep (se 5 (by rfl) ⟨724049, by rfl⟩ : syracuseStep 15446389 = 1448099) B1448099
theorem B5427587 : Blo 1427533 5427587 := bstep (se 1 (by rfl) ⟨4070690, by rfl⟩ : syracuseStep 5427587 = 8141381) B8141381
theorem B2142617 : Blo 1427533 2142617 := bstep (se 2 (by rfl) ⟨803481, by rfl⟩ : syracuseStep 2142617 = 1606963) B1606963
theorem B3052019 : Blo 1427533 3052019 := bstep (se 1 (by rfl) ⟨2289014, by rfl⟩ : syracuseStep 3052019 = 4578029) B4578029
theorem B2142731 : Blo 1427533 2142731 := bstep (se 1 (by rfl) ⟨1607048, by rfl⟩ : syracuseStep 2142731 = 3214097) B3214097
theorem B2142743 : Blo 1427533 2142743 := bstep (se 1 (by rfl) ⟨1607057, by rfl⟩ : syracuseStep 2142743 = 3214115) B3214115
theorem B3215897 : Blo 1427533 3215897 := bstep (se 2 (by rfl) ⟨1205961, by rfl⟩ : syracuseStep 3215897 = 2411923) B2411923
theorem B10842659 : Blo 1427533 10842659 := bstep (se 1 (by rfl) ⟨8131994, by rfl⟩ : syracuseStep 10842659 = 16263989) B16263989
theorem B2142809 : Blo 1427533 2142809 := bstep (se 2 (by rfl) ⟨803553, by rfl⟩ : syracuseStep 2142809 = 1607107) B1607107
theorem B3617369 : Blo 1427533 3617369 := bstep (se 2 (by rfl) ⟨1356513, by rfl⟩ : syracuseStep 3617369 = 2713027) B2713027
theorem B3215987 : Blo 1427533 3215987 := bstep (se 1 (by rfl) ⟨2411990, by rfl⟩ : syracuseStep 3215987 = 4823981) B4823981
theorem B3216023 : Blo 1427533 3216023 := bstep (se 1 (by rfl) ⟨2412017, by rfl⟩ : syracuseStep 3216023 = 4824035) B4824035
theorem B2142923 : Blo 1427533 2142923 := bstep (se 1 (by rfl) ⟨1607192, by rfl⟩ : syracuseStep 2142923 = 3214385) B3214385
theorem B2142935 : Blo 1427533 2142935 := bstep (se 1 (by rfl) ⟨1607201, by rfl⟩ : syracuseStep 2142935 = 3214403) B3214403
theorem B2143001 : Blo 1427533 2143001 := bstep (se 2 (by rfl) ⟨803625, by rfl⟩ : syracuseStep 2143001 = 1607251) B1607251
theorem B3216203 : Blo 1427533 3216203 := bstep (se 1 (by rfl) ⟨2412152, by rfl⟩ : syracuseStep 3216203 = 4824305) B4824305
theorem B3216257 : Blo 1427533 3216257 := bstep (se 2 (by rfl) ⟨1206096, by rfl⟩ : syracuseStep 3216257 = 2412193) B2412193
theorem B2143115 : Blo 1427533 2143115 := bstep (se 1 (by rfl) ⟨1607336, by rfl⟩ : syracuseStep 2143115 = 3214673) B3214673
theorem B2143127 : Blo 1427533 2143127 := bstep (se 1 (by rfl) ⟨1607345, by rfl⟩ : syracuseStep 2143127 = 3214691) B3214691
theorem B4068299 : Blo 1427533 4068299 := bstep (se 1 (by rfl) ⟨3051224, by rfl⟩ : syracuseStep 4068299 = 6102449) B6102449
theorem B2143193 : Blo 1427533 2143193 := bstep (se 2 (by rfl) ⟨803697, by rfl⟩ : syracuseStep 2143193 = 1607395) B1607395
theorem B20870219 : Blo 1427533 20870219 := bstep (se 1 (by rfl) ⟨15652664, by rfl⟩ : syracuseStep 20870219 = 31305329) B31305329
theorem B4822091 : Blo 1427533 4822091 := bstep (se 1 (by rfl) ⟨3616568, by rfl⟩ : syracuseStep 4822091 = 7233137) B7233137
theorem B2143307 : Blo 1427533 2143307 := bstep (se 1 (by rfl) ⟨1607480, by rfl⟩ : syracuseStep 2143307 = 3214961) B3214961
theorem B2143319 : Blo 1427533 2143319 := bstep (se 1 (by rfl) ⟨1607489, by rfl⟩ : syracuseStep 2143319 = 3214979) B3214979
theorem B2143385 : Blo 1427533 2143385 := bstep (se 2 (by rfl) ⟨803769, by rfl⟩ : syracuseStep 2143385 = 1607539) B1607539
theorem B2897075 : Blo 1427533 2897075 := bstep (se 1 (by rfl) ⟨2172806, by rfl⟩ : syracuseStep 2897075 = 4345613) B4345613
theorem B4887773 : Blo 1427533 4887773 := bstep (se 3 (by rfl) ⟨916457, by rfl⟩ : syracuseStep 4887773 = 1832915) B1832915
theorem B2143499 : Blo 1427533 2143499 := bstep (se 1 (by rfl) ⟨1607624, by rfl⟩ : syracuseStep 2143499 = 3215249) B3215249
theorem B2143511 : Blo 1427533 2143511 := bstep (se 1 (by rfl) ⟨1607633, by rfl⟩ : syracuseStep 2143511 = 3215267) B3215267
theorem B2610457 : Blo 1427533 2610457 := bstep (se 2 (by rfl) ⟨978921, by rfl⟩ : syracuseStep 2610457 = 1957843) B1957843
theorem B3052865 : Blo 1427533 3052865 := bstep (se 2 (by rfl) ⟨1144824, by rfl⟩ : syracuseStep 3052865 = 2289649) B2289649
theorem B4822361 : Blo 1427533 4822361 := bstep (se 2 (by rfl) ⟨1808385, by rfl⟩ : syracuseStep 4822361 = 3616771) B3616771
theorem B2143577 : Blo 1427533 2143577 := bstep (se 2 (by rfl) ⟨803841, by rfl⟩ : syracuseStep 2143577 = 1607683) B1607683
theorem B16495973 : Blo 1427533 16495973 := bstep (se 4 (by rfl) ⟨1546497, by rfl⟩ : syracuseStep 16495973 = 3092995) B3092995
theorem B41186677 : Blo 1427533 41186677 := bstep (se 5 (by rfl) ⟨1930625, by rfl⟩ : syracuseStep 41186677 = 3861251) B3861251
theorem B2749835 : Blo 1427533 2749835 := bstep (se 1 (by rfl) ⟨2062376, by rfl⟩ : syracuseStep 2749835 = 4124753) B4124753
theorem B2143691 : Blo 1427533 2143691 := bstep (se 1 (by rfl) ⟨1607768, by rfl⟩ : syracuseStep 2143691 = 3215537) B3215537
theorem B12211661 : Blo 1427533 12211661 := bstep (se 3 (by rfl) ⟨2289686, by rfl⟩ : syracuseStep 12211661 = 4579373) B4579373
theorem B2143703 : Blo 1427533 2143703 := bstep (se 1 (by rfl) ⟨1607777, by rfl⟩ : syracuseStep 2143703 = 3215555) B3215555
theorem B43955729 : Blo 1427533 43955729 := bstep (se 2 (by rfl) ⟨16483398, by rfl⟩ : syracuseStep 43955729 = 32966797) B32966797
theorem B2143769 : Blo 1427533 2143769 := bstep (se 2 (by rfl) ⟨803913, by rfl⟩ : syracuseStep 2143769 = 1607827) B1607827
theorem B5150297 : Blo 1427533 5150297 := bstep (se 2 (by rfl) ⟨1931361, by rfl⟩ : syracuseStep 5150297 = 3862723) B3862723
theorem B1808011 : Blo 1427533 1808011 := bstep (se 1 (by rfl) ⟨1356008, by rfl⟩ : syracuseStep 1808011 = 2712017) B2712017
theorem B2143883 : Blo 1427533 2143883 := bstep (se 1 (by rfl) ⟨1607912, by rfl⟩ : syracuseStep 2143883 = 3215825) B3215825
theorem B2143895 : Blo 1427533 2143895 := bstep (se 1 (by rfl) ⟨1607921, by rfl⟩ : syracuseStep 2143895 = 3215843) B3215843
theorem B7231193 : Blo 1427533 7231193 := bstep (se 2 (by rfl) ⟨2711697, by rfl⟩ : syracuseStep 7231193 = 5423395) B5423395
theorem B2143961 : Blo 1427533 2143961 := bstep (se 2 (by rfl) ⟨803985, by rfl⟩ : syracuseStep 2143961 = 1607971) B1607971
theorem B46970609 : Blo 1427533 46970609 := bstep (se 2 (by rfl) ⟨17613978, by rfl⟩ : syracuseStep 46970609 = 35227957) B35227957
theorem B2144075 : Blo 1427533 2144075 := bstep (se 1 (by rfl) ⟨1608056, by rfl⟩ : syracuseStep 2144075 = 3216113) B3216113
theorem B2144087 : Blo 1427533 2144087 := bstep (se 1 (by rfl) ⟨1608065, by rfl⟩ : syracuseStep 2144087 = 3216131) B3216131
theorem B5420951 : Blo 1427533 5420951 := bstep (se 1 (by rfl) ⟨4065713, by rfl⟩ : syracuseStep 5420951 = 8131427) B8131427
theorem B2144153 : Blo 1427533 2144153 := bstep (se 2 (by rfl) ⟨804057, by rfl⟩ : syracuseStep 2144153 = 1608115) B1608115
theorem B41211827 : Blo 1427533 41211827 := bstep (se 1 (by rfl) ⟨30908870, by rfl⟩ : syracuseStep 41211827 = 61817741) B61817741
theorem B12711941 : Blo 1427533 12711941 := bstep (se 4 (by rfl) ⟨1191744, by rfl⟩ : syracuseStep 12711941 = 2383489) B2383489
theorem B2144267 : Blo 1427533 2144267 := bstep (se 1 (by rfl) ⟨1608200, by rfl⟩ : syracuseStep 2144267 = 3216401) B3216401
theorem B4823063 : Blo 1427533 4823063 := bstep (se 1 (by rfl) ⟨3617297, by rfl⟩ : syracuseStep 4823063 = 7234595) B7234595
theorem B2144279 : Blo 1427533 2144279 := bstep (se 1 (by rfl) ⟨1608209, by rfl⟩ : syracuseStep 2144279 = 3216419) B3216419
theorem B24393797 : Blo 1427533 24393797 := bstep (se 4 (by rfl) ⟨2286918, by rfl⟩ : syracuseStep 24393797 = 4573837) B4573837
theorem B18315395 : Blo 1427533 18315395 := bstep (se 1 (by rfl) ⟨13736546, by rfl⟩ : syracuseStep 18315395 = 27473093) B27473093
theorem B4069597 : Blo 1427533 4069597 := bstep (se 3 (by rfl) ⟨763049, by rfl⟩ : syracuseStep 4069597 = 1526099) B1526099
theorem B125254001 : Blo 1427533 125254001 := bstep (se 2 (by rfl) ⟨46970250, by rfl⟩ : syracuseStep 125254001 = 93940501) B93940501
theorem B3258881 : Blo 1427533 3258881 := bstep (se 2 (by rfl) ⟨1222080, by rfl⟩ : syracuseStep 3258881 = 2444161) B2444161
theorem B4823603 : Blo 1427533 4823603 := bstep (se 1 (by rfl) ⟨3617702, by rfl⟩ : syracuseStep 4823603 = 7235405) B7235405
theorem B4069939 : Blo 1427533 4069939 := bstep (se 1 (by rfl) ⟨3052454, by rfl⟩ : syracuseStep 4069939 = 6104909) B6104909
theorem B1808983 : Blo 1427533 1808983 := bstep (se 1 (by rfl) ⟨1356737, by rfl⟩ : syracuseStep 1808983 = 2713475) B2713475
theorem B1448651 : Blo 1427533 1448651 := bstep (se 1 (by rfl) ⟨1086488, by rfl⟩ : syracuseStep 1448651 = 2172977) B2172977
theorem B39623489 : Blo 1427533 39623489 := bstep (se 2 (by rfl) ⟨14858808, by rfl⟩ : syracuseStep 39623489 = 29717617) B29717617
theorem B4823873 : Blo 1427533 4823873 := bstep (se 2 (by rfl) ⟨1808952, by rfl⟩ : syracuseStep 4823873 = 3617905) B3617905
theorem B8141633 : Blo 1427533 8141633 := bstep (se 2 (by rfl) ⟨3053112, by rfl⟩ : syracuseStep 8141633 = 6106225) B6106225
theorem B2710361 : Blo 1427533 2710361 := bstep (se 2 (by rfl) ⟨1016385, by rfl⟩ : syracuseStep 2710361 = 2032771) B2032771
theorem B6183859 : Blo 1427533 6183859 := bstep (se 1 (by rfl) ⟨4637894, by rfl⟩ : syracuseStep 6183859 = 9275789) B9275789
theorem B3259457 : Blo 1427533 3259457 := bstep (se 2 (by rfl) ⟨1222296, by rfl⟩ : syracuseStep 3259457 = 2444593) B2444593
theorem B14851147 : Blo 1427533 14851147 := bstep (se 1 (by rfl) ⟨11138360, by rfl⟩ : syracuseStep 14851147 = 22276721) B22276721
theorem B16268363 : Blo 1427533 16268363 := bstep (se 1 (by rfl) ⟨12201272, by rfl⟩ : syracuseStep 16268363 = 24402545) B24402545
theorem B14097539 : Blo 1427533 14097539 := bstep (se 1 (by rfl) ⟨10573154, by rfl⟩ : syracuseStep 14097539 = 21146309) B21146309
theorem B5422211 : Blo 1427533 5422211 := bstep (se 1 (by rfl) ⟨4066658, by rfl⟩ : syracuseStep 5422211 = 8133317) B8133317
theorem B6102209 : Blo 1427533 6102209 := bstep (se 2 (by rfl) ⟨2288328, by rfl⟩ : syracuseStep 6102209 = 4576657) B4576657
theorem B7232813 : Blo 1427533 7232813 := bstep (se 3 (by rfl) ⟨1356152, by rfl⟩ : syracuseStep 7232813 = 2712305) B2712305
theorem B4824413 : Blo 1427533 4824413 := bstep (se 3 (by rfl) ⟨904577, by rfl⟩ : syracuseStep 4824413 = 1809155) B1809155
theorem B4341185 : Blo 1427533 4341185 := bstep (se 2 (by rfl) ⟨1627944, by rfl⟩ : syracuseStep 4341185 = 3255889) B3255889
theorem B10853837 : Blo 1427533 10853837 := bstep (se 3 (by rfl) ⟨2035094, by rfl⟩ : syracuseStep 10853837 = 4070189) B4070189
theorem B2710999 : Blo 1427533 2710999 := bstep (se 1 (by rfl) ⟨2033249, by rfl⟩ : syracuseStep 2710999 = 4066499) B4066499
theorem B4890073 : Blo 1427533 4890073 := bstep (se 2 (by rfl) ⟨1833777, by rfl⟩ : syracuseStep 4890073 = 3667555) B3667555
theorem B5791297 : Blo 1427533 5791297 := bstep (se 2 (by rfl) ⟨2171736, by rfl⟩ : syracuseStep 5791297 = 4343473) B4343473
theorem B6864601 : Blo 1427533 6864601 := bstep (se 2 (by rfl) ⟨2574225, by rfl⟩ : syracuseStep 6864601 = 5148451) B5148451
theorem B12205889 : Blo 1427533 12205889 := bstep (se 2 (by rfl) ⟨4577208, by rfl⟩ : syracuseStep 12205889 = 9154417) B9154417
theorem B10854323 : Blo 1427533 10854323 := bstep (se 1 (by rfl) ⟨8140742, by rfl⟩ : syracuseStep 10854323 = 16281485) B16281485
theorem B7233623 : Blo 1427533 7233623 := bstep (se 1 (by rfl) ⟨5425217, by rfl⟩ : syracuseStep 7233623 = 10850435) B10850435
theorem B8134775 : Blo 1427533 8134775 := bstep (se 1 (by rfl) ⟨6101081, by rfl⟩ : syracuseStep 8134775 = 12202163) B12202163
theorem B17367173 : Blo 1427533 17367173 := bstep (se 4 (by rfl) ⟨1628172, by rfl⟩ : syracuseStep 17367173 = 3256345) B3256345
theorem B2572489 : Blo 1427533 2572489 := bstep (se 2 (by rfl) ⟨964683, by rfl⟩ : syracuseStep 2572489 = 1929367) B1929367
theorem B2318537 : Blo 1427533 2318537 := bstep (se 2 (by rfl) ⟨869451, by rfl⟩ : syracuseStep 2318537 = 1738903) B1738903
theorem B175947977 : Blo 1427533 175947977 := bstep (se 2 (by rfl) ⟨65980491, by rfl⟩ : syracuseStep 175947977 = 131960983) B131960983
theorem B20595185 : Blo 1427533 20595185 := bstep (se 2 (by rfl) ⟨7723194, by rfl⟩ : syracuseStep 20595185 = 15446389) B15446389
theorem B7234109 : Blo 1427533 7234109 := bstep (se 3 (by rfl) ⟨1356395, by rfl⟩ : syracuseStep 7234109 = 2712791) B2712791
theorem B2409095 : Blo 1427533 2409095 := bstep (se 1 (by rfl) ⟨1806821, by rfl⟩ : syracuseStep 2409095 = 3613643) B3613643
theorem B1606279 : Blo 1427533 1606279 := bstep (se 1 (by rfl) ⟨1204709, by rfl⟩ : syracuseStep 1606279 = 2409419) B2409419
theorem B2712199 : Blo 1427533 2712199 := bstep (se 1 (by rfl) ⟨2034149, by rfl⟩ : syracuseStep 2712199 = 4068299) B4068299
theorem B1606459 : Blo 1427533 1606459 := bstep (se 1 (by rfl) ⟨1204844, by rfl⟩ : syracuseStep 1606459 = 2409689) B2409689
theorem B2573203 : Blo 1427533 2573203 := bstep (se 1 (by rfl) ⟨1929902, by rfl⟩ : syracuseStep 2573203 = 3859805) B3859805
theorem B17384395 : Blo 1427533 17384395 := bstep (se 1 (by rfl) ⟨13038296, by rfl⟩ : syracuseStep 17384395 = 26076593) B26076593
theorem B8684509 : Blo 1427533 8684509 := bstep (se 3 (by rfl) ⟨1628345, by rfl⟩ : syracuseStep 8684509 = 3256691) B3256691
theorem B29303819 : Blo 1427533 29303819 := bstep (se 1 (by rfl) ⟨21977864, by rfl⟩ : syracuseStep 29303819 = 43955729) B43955729
theorem B7332893 : Blo 1427533 7332893 := bstep (se 3 (by rfl) ⟨1374917, by rfl⟩ : syracuseStep 7332893 = 2749835) B2749835
theorem B3433531 : Blo 1427533 3433531 := bstep (se 1 (by rfl) ⟨2575148, by rfl⟩ : syracuseStep 3433531 = 5150297) B5150297
theorem B3212423 : Blo 1427533 3212423 := bstep (se 1 (by rfl) ⟨2409317, by rfl⟩ : syracuseStep 3212423 = 4818635) B4818635
theorem B3859609 : Blo 1427533 3859609 := bstep (se 2 (by rfl) ⟨1447353, by rfl⟩ : syracuseStep 3859609 = 2894707) B2894707
theorem B2712761 : Blo 1427533 2712761 := bstep (se 2 (by rfl) ⟨1017285, by rfl⟩ : syracuseStep 2712761 = 2034571) B2034571
theorem B3613967 : Blo 1427533 3613967 := bstep (se 1 (by rfl) ⟨2710475, by rfl⟩ : syracuseStep 3613967 = 5420951) B5420951
theorem B2409743 : Blo 1427533 2409743 := bstep (se 1 (by rfl) ⟨1807307, by rfl⟩ : syracuseStep 2409743 = 3614615) B3614615
theorem B1606927 : Blo 1427533 1606927 := bstep (se 1 (by rfl) ⟨1205195, by rfl⟩ : syracuseStep 1606927 = 2410391) B2410391
theorem B3212603 : Blo 1427533 3212603 := bstep (se 1 (by rfl) ⟨2409452, by rfl⟩ : syracuseStep 3212603 = 4818905) B4818905
theorem B16262531 : Blo 1427533 16262531 := bstep (se 1 (by rfl) ⟨12196898, by rfl⟩ : syracuseStep 16262531 = 24393797) B24393797
theorem B4818311 : Blo 1427533 4818311 := bstep (se 1 (by rfl) ⟨3613733, by rfl⟩ : syracuseStep 4818311 = 7227467) B7227467
theorem B2033039 : Blo 1427533 2033039 := bstep (se 1 (by rfl) ⟨1524779, by rfl⟩ : syracuseStep 2033039 = 3049559) B3049559
theorem B19801529 : Blo 1427533 19801529 := bstep (se 2 (by rfl) ⟨7425573, by rfl⟩ : syracuseStep 19801529 = 14851147) B14851147
theorem B3212729 : Blo 1427533 3212729 := bstep (se 2 (by rfl) ⟨1204773, by rfl⟩ : syracuseStep 3212729 = 2409547) B2409547
theorem B83502667 : Blo 1427533 83502667 := bstep (se 1 (by rfl) ⟨62627000, by rfl⟩ : syracuseStep 83502667 = 125254001) B125254001
theorem B2172587 : Blo 1427533 2172587 := bstep (se 1 (by rfl) ⟨1629440, by rfl⟩ : syracuseStep 2172587 = 3258881) B3258881
theorem B8251073 : Blo 1427533 8251073 := bstep (se 2 (by rfl) ⟨3094152, by rfl⟩ : syracuseStep 8251073 = 6188305) B6188305
theorem B4818689 : Blo 1427533 4818689 := bstep (se 2 (by rfl) ⟨1807008, by rfl⟩ : syracuseStep 4818689 = 3614017) B3614017
theorem B1607431 : Blo 1427533 1607431 := bstep (se 1 (by rfl) ⟨1205573, by rfl⟩ : syracuseStep 1607431 = 2411147) B2411147
theorem B3213071 : Blo 1427533 3213071 := bstep (se 1 (by rfl) ⟨2409803, by rfl⟩ : syracuseStep 3213071 = 4819607) B4819607
theorem B3213089 : Blo 1427533 3213089 := bstep (se 2 (by rfl) ⟨1204908, by rfl⟩ : syracuseStep 3213089 = 2409817) B2409817
theorem B2410283 : Blo 1427533 2410283 := bstep (se 1 (by rfl) ⟨1807712, by rfl⟩ : syracuseStep 2410283 = 3615425) B3615425
theorem B1607611 : Blo 1427533 1607611 := bstep (se 1 (by rfl) ⟨1205708, by rfl⟩ : syracuseStep 1607611 = 2411417) B2411417
theorem B3614665 : Blo 1427533 3614665 := bstep (se 2 (by rfl) ⟨1355499, by rfl⟩ : syracuseStep 3614665 = 2710999) B2710999
theorem B7718915 : Blo 1427533 7718915 := bstep (se 1 (by rfl) ⟨5789186, by rfl⟩ : syracuseStep 7718915 = 11578373) B11578373
theorem B8136733 : Blo 1427533 8136733 := bstep (se 3 (by rfl) ⟨1525637, by rfl⟩ : syracuseStep 8136733 = 3051275) B3051275
theorem B2172971 : Blo 1427533 2172971 := bstep (se 1 (by rfl) ⟨1629728, by rfl⟩ : syracuseStep 2172971 = 3259457) B3259457
theorem B9398359 : Blo 1427533 9398359 := bstep (se 1 (by rfl) ⟨7048769, by rfl⟩ : syracuseStep 9398359 = 14097539) B14097539
theorem B3614807 : Blo 1427533 3614807 := bstep (se 1 (by rfl) ⟨2711105, by rfl⟩ : syracuseStep 3614807 = 5422211) B5422211
theorem B3213431 : Blo 1427533 3213431 := bstep (se 1 (by rfl) ⟨2410073, by rfl⟩ : syracuseStep 3213431 = 4820147) B4820147
theorem B1427591 : Blo 1427533 1427591 := bstep (se 1 (by rfl) ⟨1070693, by rfl⟩ : syracuseStep 1427591 = 2141387) B2141387
theorem B1427599 : Blo 1427533 1427599 := bstep (se 1 (by rfl) ⟨1070699, by rfl⟩ : syracuseStep 1427599 = 2141399) B2141399
theorem B2410681 : Blo 1427533 2410681 := bstep (se 2 (by rfl) ⟨904005, by rfl⟩ : syracuseStep 2410681 = 1808011) B1808011
theorem B1427643 : Blo 1427533 1427643 := bstep (se 1 (by rfl) ⟨1070732, by rfl⟩ : syracuseStep 1427643 = 2141465) B2141465
theorem B7227629 : Blo 1427533 7227629 := bstep (se 3 (by rfl) ⟨1355180, by rfl⟩ : syracuseStep 7227629 = 2710361) B2710361
theorem B1427719 : Blo 1427533 1427719 := bstep (se 1 (by rfl) ⟨1070789, by rfl⟩ : syracuseStep 1427719 = 2141579) B2141579
theorem B1427727 : Blo 1427533 1427727 := bstep (se 1 (by rfl) ⟨1070795, by rfl⟩ : syracuseStep 1427727 = 2141591) B2141591
theorem B5146895 : Blo 1427533 5146895 := bstep (se 1 (by rfl) ⟨3860171, by rfl⟩ : syracuseStep 5146895 = 7720343) B7720343
theorem B4065565 : Blo 1427533 4065565 := bstep (se 3 (by rfl) ⟨762293, by rfl⟩ : syracuseStep 4065565 = 1524587) B1524587
theorem B9152801 : Blo 1427533 9152801 := bstep (se 2 (by rfl) ⟨3432300, by rfl⟩ : syracuseStep 9152801 = 6864601) B6864601
theorem B2894123 : Blo 1427533 2894123 := bstep (se 1 (by rfl) ⟨2170592, by rfl⟩ : syracuseStep 2894123 = 4341185) B4341185
theorem B3213611 : Blo 1427533 3213611 := bstep (se 1 (by rfl) ⟨2410208, by rfl⟩ : syracuseStep 3213611 = 4820417) B4820417
theorem B7235891 : Blo 1427533 7235891 := bstep (se 1 (by rfl) ⟨5426918, by rfl⟩ : syracuseStep 7235891 = 10853837) B10853837
theorem B1427771 : Blo 1427533 1427771 := bstep (se 1 (by rfl) ⟨1070828, by rfl⟩ : syracuseStep 1427771 = 2141657) B2141657
theorem B4065623 : Blo 1427533 4065623 := bstep (se 1 (by rfl) ⟨3049217, by rfl⟩ : syracuseStep 4065623 = 6098435) B6098435
theorem B1427847 : Blo 1427533 1427847 := bstep (se 1 (by rfl) ⟨1070885, by rfl⟩ : syracuseStep 1427847 = 2141771) B2141771
theorem B1427855 : Blo 1427533 1427855 := bstep (se 1 (by rfl) ⟨1070891, by rfl⟩ : syracuseStep 1427855 = 2141783) B2141783
theorem B1526159 : Blo 1427533 1526159 := bstep (se 1 (by rfl) ⟨1144619, by rfl⟩ : syracuseStep 1526159 = 2289239) B2289239
theorem B1608079 : Blo 1427533 1608079 := bstep (se 1 (by rfl) ⟨1206059, by rfl⟩ : syracuseStep 1608079 = 2412119) B2412119
theorem B1427899 : Blo 1427533 1427899 := bstep (se 1 (by rfl) ⟨1070924, by rfl⟩ : syracuseStep 1427899 = 2141849) B2141849
theorem B7719389 : Blo 1427533 7719389 := bstep (se 3 (by rfl) ⟨1447385, by rfl⟩ : syracuseStep 7719389 = 2894771) B2894771
theorem B13732355 : Blo 1427533 13732355 := bstep (se 1 (by rfl) ⟨10299266, by rfl⟩ : syracuseStep 13732355 = 20598533) B20598533
theorem B1427975 : Blo 1427533 1427975 := bstep (se 1 (by rfl) ⟨1070981, by rfl⟩ : syracuseStep 1427975 = 2141963) B2141963
theorem B1427983 : Blo 1427533 1427983 := bstep (se 1 (by rfl) ⟨1070987, by rfl⟩ : syracuseStep 1427983 = 2141975) B2141975
theorem B1526287 : Blo 1427533 1526287 := bstep (se 1 (by rfl) ⟨1144715, by rfl⟩ : syracuseStep 1526287 = 2289431) B2289431
theorem B4819499 : Blo 1427533 4819499 := bstep (se 1 (by rfl) ⟨3614624, by rfl⟩ : syracuseStep 4819499 = 7229249) B7229249
theorem B8137259 : Blo 1427533 8137259 := bstep (se 1 (by rfl) ⟨6102944, by rfl⟩ : syracuseStep 8137259 = 12205889) B12205889
theorem B1428027 : Blo 1427533 1428027 := bstep (se 1 (by rfl) ⟨1071020, by rfl⟩ : syracuseStep 1428027 = 2142041) B2142041
theorem B17386103 : Blo 1427533 17386103 := bstep (se 1 (by rfl) ⟨13039577, by rfl⟩ : syracuseStep 17386103 = 26079155) B26079155
theorem B7236215 : Blo 1427533 7236215 := bstep (se 1 (by rfl) ⟨5427161, by rfl⟩ : syracuseStep 7236215 = 10854323) B10854323
theorem B1428103 : Blo 1427533 1428103 := bstep (se 1 (by rfl) ⟨1071077, by rfl⟩ : syracuseStep 1428103 = 2142155) B2142155
theorem B1428111 : Blo 1427533 1428111 := bstep (se 1 (by rfl) ⟨1071083, by rfl⟩ : syracuseStep 1428111 = 2142167) B2142167
theorem B3050131 : Blo 1427533 3050131 := bstep (se 1 (by rfl) ⟨2287598, by rfl⟩ : syracuseStep 3050131 = 4575197) B4575197
theorem B3213971 : Blo 1427533 3213971 := bstep (se 1 (by rfl) ⟨2410478, by rfl⟩ : syracuseStep 3213971 = 4820957) B4820957
theorem B1428155 : Blo 1427533 1428155 := bstep (se 1 (by rfl) ⟨1071116, by rfl⟩ : syracuseStep 1428155 = 2142233) B2142233
theorem B3214025 : Blo 1427533 3214025 := bstep (se 2 (by rfl) ⟨1205259, by rfl⟩ : syracuseStep 3214025 = 2410519) B2410519
theorem B1428231 : Blo 1427533 1428231 := bstep (se 1 (by rfl) ⟨1071173, by rfl⟩ : syracuseStep 1428231 = 2142347) B2142347
theorem B1428239 : Blo 1427533 1428239 := bstep (se 1 (by rfl) ⟨1071179, by rfl⟩ : syracuseStep 1428239 = 2142359) B2142359
theorem B1428283 : Blo 1427533 1428283 := bstep (se 1 (by rfl) ⟨1071212, by rfl⟩ : syracuseStep 1428283 = 2142425) B2142425
theorem B2411383 : Blo 1427533 2411383 := bstep (se 1 (by rfl) ⟨1808537, by rfl⟩ : syracuseStep 2411383 = 3617075) B3617075
theorem B1428359 : Blo 1427533 1428359 := bstep (se 1 (by rfl) ⟨1071269, by rfl⟩ : syracuseStep 1428359 = 2142539) B2142539
theorem B1428367 : Blo 1427533 1428367 := bstep (se 1 (by rfl) ⟨1071275, by rfl⟩ : syracuseStep 1428367 = 2142551) B2142551
theorem B3050387 : Blo 1427533 3050387 := bstep (se 1 (by rfl) ⟨2287790, by rfl⟩ : syracuseStep 3050387 = 4575581) B4575581
theorem B1428411 : Blo 1427533 1428411 := bstep (se 1 (by rfl) ⟨1071308, by rfl⟩ : syracuseStep 1428411 = 2142617) B2142617
theorem B5426129 : Blo 1427533 5426129 := bstep (se 2 (by rfl) ⟨2034798, by rfl⟩ : syracuseStep 5426129 = 4069597) B4069597
theorem B1428487 : Blo 1427533 1428487 := bstep (se 1 (by rfl) ⟨1071365, by rfl⟩ : syracuseStep 1428487 = 2142731) B2142731
theorem B1428495 : Blo 1427533 1428495 := bstep (se 1 (by rfl) ⟨1071371, by rfl⟩ : syracuseStep 1428495 = 2142743) B2142743
theorem B7228439 : Blo 1427533 7228439 := bstep (se 1 (by rfl) ⟨5421329, by rfl⟩ : syracuseStep 7228439 = 10842659) B10842659
theorem B1428539 : Blo 1427533 1428539 := bstep (se 1 (by rfl) ⟨1071404, by rfl⟩ : syracuseStep 1428539 = 2142809) B2142809
theorem B2411579 : Blo 1427533 2411579 := bstep (se 1 (by rfl) ⟨1808684, by rfl⟩ : syracuseStep 2411579 = 3617369) B3617369
theorem B2141303 : Blo 1427533 2141303 := bstep (se 1 (by rfl) ⟨1605977, by rfl⟩ : syracuseStep 2141303 = 3211955) B3211955
theorem B1428615 : Blo 1427533 1428615 := bstep (se 1 (by rfl) ⟨1071461, by rfl⟩ : syracuseStep 1428615 = 2142923) B2142923
theorem B2141327 : Blo 1427533 2141327 := bstep (se 1 (by rfl) ⟨1605995, by rfl⟩ : syracuseStep 2141327 = 3211991) B3211991
theorem B1428623 : Blo 1427533 1428623 := bstep (se 1 (by rfl) ⟨1071467, by rfl⟩ : syracuseStep 1428623 = 2142935) B2142935
theorem B2141369 : Blo 1427533 2141369 := bstep (se 2 (by rfl) ⟨803013, by rfl⟩ : syracuseStep 2141369 = 1606027) B1606027
theorem B1428667 : Blo 1427533 1428667 := bstep (se 1 (by rfl) ⟨1071500, by rfl⟩ : syracuseStep 1428667 = 2143001) B2143001
theorem B2141447 : Blo 1427533 2141447 := bstep (se 1 (by rfl) ⟨1606085, by rfl⟩ : syracuseStep 2141447 = 3212171) B3212171
theorem B1428743 : Blo 1427533 1428743 := bstep (se 1 (by rfl) ⟨1071557, by rfl⟩ : syracuseStep 1428743 = 2143115) B2143115
theorem B1428751 : Blo 1427533 1428751 := bstep (se 1 (by rfl) ⟨1071563, by rfl⟩ : syracuseStep 1428751 = 2143127) B2143127
theorem B6860065 : Blo 1427533 6860065 := bstep (se 2 (by rfl) ⟨2572524, by rfl⟩ : syracuseStep 6860065 = 5145049) B5145049
theorem B2141483 : Blo 1427533 2141483 := bstep (se 1 (by rfl) ⟨1606112, by rfl⟩ : syracuseStep 2141483 = 3212225) B3212225
theorem B1428795 : Blo 1427533 1428795 := bstep (se 1 (by rfl) ⟨1071596, by rfl⟩ : syracuseStep 1428795 = 2143193) B2143193
theorem B2141513 : Blo 1427533 2141513 := bstep (se 2 (by rfl) ⟨803067, by rfl⟩ : syracuseStep 2141513 = 1606135) B1606135
theorem B13913479 : Blo 1427533 13913479 := bstep (se 1 (by rfl) ⟨10435109, by rfl⟩ : syracuseStep 13913479 = 20870219) B20870219
theorem B3214727 : Blo 1427533 3214727 := bstep (se 1 (by rfl) ⟨2411045, by rfl⟩ : syracuseStep 3214727 = 4822091) B4822091
theorem B1428871 : Blo 1427533 1428871 := bstep (se 1 (by rfl) ⟨1071653, by rfl⟩ : syracuseStep 1428871 = 2143307) B2143307
theorem B1428879 : Blo 1427533 1428879 := bstep (se 1 (by rfl) ⟨1071659, by rfl⟩ : syracuseStep 1428879 = 2143319) B2143319
theorem B4124051 : Blo 1427533 4124051 := bstep (se 1 (by rfl) ⟨3093038, by rfl⟩ : syracuseStep 4124051 = 6186077) B6186077
theorem B5426585 : Blo 1427533 5426585 := bstep (se 2 (by rfl) ⟨2034969, by rfl⟩ : syracuseStep 5426585 = 4069939) B4069939
theorem B2141627 : Blo 1427533 2141627 := bstep (se 1 (by rfl) ⟨1606220, by rfl⟩ : syracuseStep 2141627 = 3212441) B3212441
theorem B1428923 : Blo 1427533 1428923 := bstep (se 1 (by rfl) ⟨1071692, by rfl⟩ : syracuseStep 1428923 = 2143385) B2143385
theorem B2411977 : Blo 1427533 2411977 := bstep (se 2 (by rfl) ⟨904491, by rfl⟩ : syracuseStep 2411977 = 1808983) B1808983
theorem B2141687 : Blo 1427533 2141687 := bstep (se 1 (by rfl) ⟨1606265, by rfl⟩ : syracuseStep 2141687 = 3212531) B3212531
theorem B1428999 : Blo 1427533 1428999 := bstep (se 1 (by rfl) ⟨1071749, by rfl⟩ : syracuseStep 1428999 = 2143499) B2143499
theorem B2141711 : Blo 1427533 2141711 := bstep (se 1 (by rfl) ⟨1606283, by rfl⟩ : syracuseStep 2141711 = 3212567) B3212567
theorem B1429007 : Blo 1427533 1429007 := bstep (se 1 (by rfl) ⟨1071755, by rfl⟩ : syracuseStep 1429007 = 2143511) B2143511
theorem B12201515 : Blo 1427533 12201515 := bstep (se 1 (by rfl) ⟨9151136, by rfl⟩ : syracuseStep 12201515 = 18302273) B18302273
theorem B2035243 : Blo 1427533 2035243 := bstep (se 1 (by rfl) ⟨1526432, by rfl⟩ : syracuseStep 2035243 = 3052865) B3052865
theorem B2141753 : Blo 1427533 2141753 := bstep (se 2 (by rfl) ⟨803157, by rfl⟩ : syracuseStep 2141753 = 1606315) B1606315
theorem B3862075 : Blo 1427533 3862075 := bstep (se 1 (by rfl) ⟨2896556, by rfl⟩ : syracuseStep 3862075 = 5793113) B5793113
theorem B3214907 : Blo 1427533 3214907 := bstep (se 1 (by rfl) ⟨2411180, by rfl⟩ : syracuseStep 3214907 = 4822361) B4822361
theorem B1429051 : Blo 1427533 1429051 := bstep (se 1 (by rfl) ⟨1071788, by rfl⟩ : syracuseStep 1429051 = 2143577) B2143577
theorem B10997315 : Blo 1427533 10997315 := bstep (se 1 (by rfl) ⟨8247986, by rfl⟩ : syracuseStep 10997315 = 16495973) B16495973
theorem B2141831 : Blo 1427533 2141831 := bstep (se 1 (by rfl) ⟨1606373, by rfl⟩ : syracuseStep 2141831 = 3212747) B3212747
theorem B1429127 : Blo 1427533 1429127 := bstep (se 1 (by rfl) ⟨1071845, by rfl⟩ : syracuseStep 1429127 = 2143691) B2143691
theorem B1429135 : Blo 1427533 1429135 := bstep (se 1 (by rfl) ⟨1071851, by rfl⟩ : syracuseStep 1429135 = 2143703) B2143703
theorem B2141867 : Blo 1427533 2141867 := bstep (se 1 (by rfl) ⟨1606400, by rfl⟩ : syracuseStep 2141867 = 3212801) B3212801
theorem B3215033 : Blo 1427533 3215033 := bstep (se 2 (by rfl) ⟨1205637, by rfl⟩ : syracuseStep 3215033 = 2411275) B2411275
theorem B1429179 : Blo 1427533 1429179 := bstep (se 1 (by rfl) ⟨1071884, by rfl⟩ : syracuseStep 1429179 = 2143769) B2143769
theorem B2141897 : Blo 1427533 2141897 := bstep (se 2 (by rfl) ⟨803211, by rfl⟩ : syracuseStep 2141897 = 1606423) B1606423
theorem B1429255 : Blo 1427533 1429255 := bstep (se 1 (by rfl) ⟨1071941, by rfl⟩ : syracuseStep 1429255 = 2143883) B2143883
theorem B1429263 : Blo 1427533 1429263 := bstep (se 1 (by rfl) ⟨1071947, by rfl⟩ : syracuseStep 1429263 = 2143895) B2143895
theorem B2142011 : Blo 1427533 2142011 := bstep (se 1 (by rfl) ⟨1606508, by rfl⟩ : syracuseStep 2142011 = 3213017) B3213017
theorem B4820795 : Blo 1427533 4820795 := bstep (se 1 (by rfl) ⟨3615596, by rfl⟩ : syracuseStep 4820795 = 7231193) B7231193
theorem B1429307 : Blo 1427533 1429307 := bstep (se 1 (by rfl) ⟨1071980, by rfl⟩ : syracuseStep 1429307 = 2143961) B2143961
theorem B2142071 : Blo 1427533 2142071 := bstep (se 1 (by rfl) ⟨1606553, by rfl⟩ : syracuseStep 2142071 = 3213107) B3213107
theorem B1429383 : Blo 1427533 1429383 := bstep (se 1 (by rfl) ⟨1072037, by rfl⟩ : syracuseStep 1429383 = 2144075) B2144075
theorem B2142095 : Blo 1427533 2142095 := bstep (se 1 (by rfl) ⟨1606571, by rfl⟩ : syracuseStep 2142095 = 3213143) B3213143
theorem B1429391 : Blo 1427533 1429391 := bstep (se 1 (by rfl) ⟨1072043, by rfl⟩ : syracuseStep 1429391 = 2144087) B2144087
theorem B2895763 : Blo 1427533 2895763 := bstep (se 1 (by rfl) ⟨2171822, by rfl⟩ : syracuseStep 2895763 = 4343645) B4343645
theorem B8245145 : Blo 1427533 8245145 := bstep (se 2 (by rfl) ⟨3091929, by rfl⟩ : syracuseStep 8245145 = 6183859) B6183859
theorem B2142137 : Blo 1427533 2142137 := bstep (se 2 (by rfl) ⟨803301, by rfl⟩ : syracuseStep 2142137 = 1606603) B1606603
theorem B1429435 : Blo 1427533 1429435 := bstep (se 1 (by rfl) ⟨1072076, by rfl⟩ : syracuseStep 1429435 = 2144153) B2144153
theorem B4067273 : Blo 1427533 4067273 := bstep (se 2 (by rfl) ⟨1525227, by rfl⟩ : syracuseStep 4067273 = 3050455) B3050455
theorem B8138717 : Blo 1427533 8138717 := bstep (se 3 (by rfl) ⟨1526009, by rfl⟩ : syracuseStep 8138717 = 3052019) B3052019
theorem B8474627 : Blo 1427533 8474627 := bstep (se 1 (by rfl) ⟨6355970, by rfl⟩ : syracuseStep 8474627 = 12711941) B12711941
theorem B2142215 : Blo 1427533 2142215 := bstep (se 1 (by rfl) ⟨1606661, by rfl⟩ : syracuseStep 2142215 = 3213323) B3213323
theorem B1429511 : Blo 1427533 1429511 := bstep (se 1 (by rfl) ⟨1072133, by rfl⟩ : syracuseStep 1429511 = 2144267) B2144267
theorem B3215375 : Blo 1427533 3215375 := bstep (se 1 (by rfl) ⟨2411531, by rfl⟩ : syracuseStep 3215375 = 4823063) B4823063
theorem B1429519 : Blo 1427533 1429519 := bstep (se 1 (by rfl) ⟨1072139, by rfl⟩ : syracuseStep 1429519 = 2144279) B2144279
theorem B3215393 : Blo 1427533 3215393 := bstep (se 2 (by rfl) ⟨1205772, by rfl⟩ : syracuseStep 3215393 = 2411545) B2411545
theorem B2142251 : Blo 1427533 2142251 := bstep (se 1 (by rfl) ⟨1606688, by rfl⟩ : syracuseStep 2142251 = 3213377) B3213377
theorem B10842173 : Blo 1427533 10842173 := bstep (se 3 (by rfl) ⟨2032907, by rfl⟩ : syracuseStep 10842173 = 4065815) B4065815
theorem B2142281 : Blo 1427533 2142281 := bstep (se 2 (by rfl) ⟨803355, by rfl⟩ : syracuseStep 2142281 = 1606711) B1606711
theorem B12210263 : Blo 1427533 12210263 := bstep (se 1 (by rfl) ⟨9157697, by rfl⟩ : syracuseStep 12210263 = 18315395) B18315395
theorem B3616883 : Blo 1427533 3616883 := bstep (se 1 (by rfl) ⟨2712662, by rfl⟩ : syracuseStep 3616883 = 5425325) B5425325
theorem B13922437 : Blo 1427533 13922437 := bstep (se 4 (by rfl) ⟨1305228, by rfl⟩ : syracuseStep 13922437 = 2610457) B2610457
theorem B2142395 : Blo 1427533 2142395 := bstep (se 1 (by rfl) ⟨1606796, by rfl⟩ : syracuseStep 2142395 = 3213593) B3213593
theorem B2142455 : Blo 1427533 2142455 := bstep (se 1 (by rfl) ⟨1606841, by rfl⟩ : syracuseStep 2142455 = 3213683) B3213683
theorem B2142479 : Blo 1427533 2142479 := bstep (se 1 (by rfl) ⟨1606859, by rfl⟩ : syracuseStep 2142479 = 3213719) B3213719
theorem B4821281 : Blo 1427533 4821281 := bstep (se 2 (by rfl) ⟨1807980, by rfl⟩ : syracuseStep 4821281 = 3615961) B3615961
theorem B2142521 : Blo 1427533 2142521 := bstep (se 2 (by rfl) ⟨803445, by rfl⟩ : syracuseStep 2142521 = 1606891) B1606891
theorem B3215735 : Blo 1427533 3215735 := bstep (se 1 (by rfl) ⟨2411801, by rfl⟩ : syracuseStep 3215735 = 4823603) B4823603
theorem B2142599 : Blo 1427533 2142599 := bstep (se 1 (by rfl) ⟨1606949, by rfl⟩ : syracuseStep 2142599 = 3213899) B3213899
theorem B2142635 : Blo 1427533 2142635 := bstep (se 1 (by rfl) ⟨1606976, by rfl⟩ : syracuseStep 2142635 = 3213953) B3213953
theorem B2142665 : Blo 1427533 2142665 := bstep (se 2 (by rfl) ⟨803499, by rfl⟩ : syracuseStep 2142665 = 1606999) B1606999
theorem B54915569 : Blo 1427533 54915569 := bstep (se 2 (by rfl) ⟨20593338, by rfl⟩ : syracuseStep 54915569 = 41186677) B41186677
theorem B3863069 : Blo 1427533 3863069 := bstep (se 3 (by rfl) ⟨724325, by rfl⟩ : syracuseStep 3863069 = 1448651) B1448651
theorem B26415659 : Blo 1427533 26415659 := bstep (se 1 (by rfl) ⟨19811744, by rfl⟩ : syracuseStep 26415659 = 39623489) B39623489
theorem B3215915 : Blo 1427533 3215915 := bstep (se 1 (by rfl) ⟨2411936, by rfl⟩ : syracuseStep 3215915 = 4823873) B4823873
theorem B5427755 : Blo 1427533 5427755 := bstep (se 1 (by rfl) ⟨4070816, by rfl⟩ : syracuseStep 5427755 = 8141633) B8141633
theorem B2142779 : Blo 1427533 2142779 := bstep (se 1 (by rfl) ⟨1607084, by rfl⟩ : syracuseStep 2142779 = 3214169) B3214169
theorem B3863155 : Blo 1427533 3863155 := bstep (se 1 (by rfl) ⟨2897366, by rfl⟩ : syracuseStep 3863155 = 5794733) B5794733
theorem B2142839 : Blo 1427533 2142839 := bstep (se 1 (by rfl) ⟨1607129, by rfl⟩ : syracuseStep 2142839 = 3214259) B3214259
theorem B3617399 : Blo 1427533 3617399 := bstep (se 1 (by rfl) ⟨2713049, by rfl⟩ : syracuseStep 3617399 = 5426099) B5426099
theorem B2142863 : Blo 1427533 2142863 := bstep (se 1 (by rfl) ⟨1607147, by rfl⟩ : syracuseStep 2142863 = 3214295) B3214295
theorem B37606069 : Blo 1427533 37606069 := bstep (se 5 (by rfl) ⟨1762784, by rfl⟩ : syracuseStep 37606069 = 3525569) B3525569
theorem B2142905 : Blo 1427533 2142905 := bstep (se 2 (by rfl) ⟨803589, by rfl⟩ : syracuseStep 2142905 = 1607179) B1607179
theorem B7721729 : Blo 1427533 7721729 := bstep (se 2 (by rfl) ⟨2895648, by rfl⟩ : syracuseStep 7721729 = 5791297) B5791297
theorem B2142983 : Blo 1427533 2142983 := bstep (se 1 (by rfl) ⟨1607237, by rfl⟩ : syracuseStep 2142983 = 3214475) B3214475
theorem B4068139 : Blo 1427533 4068139 := bstep (se 1 (by rfl) ⟨3051104, by rfl⟩ : syracuseStep 4068139 = 6102209) B6102209
theorem B2143019 : Blo 1427533 2143019 := bstep (se 1 (by rfl) ⟨1607264, by rfl⟩ : syracuseStep 2143019 = 3214529) B3214529
theorem B2143049 : Blo 1427533 2143049 := bstep (se 2 (by rfl) ⟨803643, by rfl⟩ : syracuseStep 2143049 = 1607287) B1607287
theorem B4821875 : Blo 1427533 4821875 := bstep (se 1 (by rfl) ⟨3616406, by rfl⟩ : syracuseStep 4821875 = 7232813) B7232813
theorem B3216275 : Blo 1427533 3216275 := bstep (se 1 (by rfl) ⟨2412206, by rfl⟩ : syracuseStep 3216275 = 4824413) B4824413
theorem B2143163 : Blo 1427533 2143163 := bstep (se 1 (by rfl) ⟨1607372, by rfl⟩ : syracuseStep 2143163 = 3214745) B3214745
theorem B3216329 : Blo 1427533 3216329 := bstep (se 2 (by rfl) ⟨1206123, by rfl⟩ : syracuseStep 3216329 = 2412247) B2412247
theorem B2143223 : Blo 1427533 2143223 := bstep (se 1 (by rfl) ⟨1607417, by rfl⟩ : syracuseStep 2143223 = 3214835) B3214835
theorem B2143247 : Blo 1427533 2143247 := bstep (se 1 (by rfl) ⟨1607435, by rfl⟩ : syracuseStep 2143247 = 3214871) B3214871
theorem B2143289 : Blo 1427533 2143289 := bstep (se 2 (by rfl) ⟨803733, by rfl⟩ : syracuseStep 2143289 = 1607467) B1607467
theorem B4068413 : Blo 1427533 4068413 := bstep (se 3 (by rfl) ⟨762827, by rfl⟩ : syracuseStep 4068413 = 1525655) B1525655
theorem B2143367 : Blo 1427533 2143367 := bstep (se 1 (by rfl) ⟨1607525, by rfl⟩ : syracuseStep 2143367 = 3215051) B3215051
theorem B2143403 : Blo 1427533 2143403 := bstep (se 1 (by rfl) ⟨1607552, by rfl⟩ : syracuseStep 2143403 = 3215105) B3215105
theorem B7722157 : Blo 1427533 7722157 := bstep (se 3 (by rfl) ⟨1447904, by rfl⟩ : syracuseStep 7722157 = 2895809) B2895809
theorem B2143433 : Blo 1427533 2143433 := bstep (se 2 (by rfl) ⟨803787, by rfl⟩ : syracuseStep 2143433 = 1607575) B1607575
theorem B3052745 : Blo 1427533 3052745 := bstep (se 2 (by rfl) ⟨1144779, by rfl⟩ : syracuseStep 3052745 = 2289559) B2289559
theorem B2143547 : Blo 1427533 2143547 := bstep (se 1 (by rfl) ⟨1607660, by rfl⟩ : syracuseStep 2143547 = 3215321) B3215321
theorem B2143607 : Blo 1427533 2143607 := bstep (se 1 (by rfl) ⟨1607705, by rfl⟩ : syracuseStep 2143607 = 3215411) B3215411
theorem B2143631 : Blo 1427533 2143631 := bstep (se 1 (by rfl) ⟨1607723, by rfl⟩ : syracuseStep 2143631 = 3215447) B3215447
theorem B4068755 : Blo 1427533 4068755 := bstep (se 1 (by rfl) ⟨3051566, by rfl⟩ : syracuseStep 4068755 = 6103133) B6103133
theorem B2143673 : Blo 1427533 2143673 := bstep (se 2 (by rfl) ⟨803877, by rfl⟩ : syracuseStep 2143673 = 1607755) B1607755
theorem B6100433 : Blo 1427533 6100433 := bstep (se 2 (by rfl) ⟨2287662, by rfl⟩ : syracuseStep 6100433 = 4575325) B4575325
theorem B2143751 : Blo 1427533 2143751 := bstep (se 1 (by rfl) ⟨1607813, by rfl⟩ : syracuseStep 2143751 = 3215627) B3215627
theorem B1807915 : Blo 1427533 1807915 := bstep (se 1 (by rfl) ⟨1355936, by rfl⟩ : syracuseStep 1807915 = 2711873) B2711873
theorem B2143787 : Blo 1427533 2143787 := bstep (se 1 (by rfl) ⟨1607840, by rfl⟩ : syracuseStep 2143787 = 3215681) B3215681
theorem B2143817 : Blo 1427533 2143817 := bstep (se 2 (by rfl) ⟨803931, by rfl⟩ : syracuseStep 2143817 = 1607863) B1607863
theorem B3618391 : Blo 1427533 3618391 := bstep (se 1 (by rfl) ⟨2713793, by rfl⟩ : syracuseStep 3618391 = 5427587) B5427587
theorem B2143931 : Blo 1427533 2143931 := bstep (se 1 (by rfl) ⟨1607948, by rfl⟩ : syracuseStep 2143931 = 3215897) B3215897
theorem B17381081 : Blo 1427533 17381081 := bstep (se 2 (by rfl) ⟨6517905, by rfl⟩ : syracuseStep 17381081 = 13035811) B13035811
theorem B2143991 : Blo 1427533 2143991 := bstep (se 1 (by rfl) ⟨1607993, by rfl⟩ : syracuseStep 2143991 = 3215987) B3215987
theorem B2144015 : Blo 1427533 2144015 := bstep (se 1 (by rfl) ⟨1608011, by rfl⟩ : syracuseStep 2144015 = 3216023) B3216023
theorem B2144057 : Blo 1427533 2144057 := bstep (se 2 (by rfl) ⟨804021, by rfl⟩ : syracuseStep 2144057 = 1608043) B1608043
theorem B2144135 : Blo 1427533 2144135 := bstep (se 1 (by rfl) ⟨1608101, by rfl⟩ : syracuseStep 2144135 = 3216203) B3216203
theorem B7329689 : Blo 1427533 7329689 := bstep (se 2 (by rfl) ⟨2748633, by rfl⟩ : syracuseStep 7329689 = 5497267) B5497267
theorem B2144171 : Blo 1427533 2144171 := bstep (se 1 (by rfl) ⟨1608128, by rfl⟩ : syracuseStep 2144171 = 3216257) B3216257
theorem B2144201 : Blo 1427533 2144201 := bstep (se 2 (by rfl) ⟨804075, by rfl⟩ : syracuseStep 2144201 = 1608151) B1608151
theorem B7231517 : Blo 1427533 7231517 := bstep (se 3 (by rfl) ⟨1355909, by rfl⟩ : syracuseStep 7231517 = 2711819) B2711819
theorem B4577323 : Blo 1427533 4577323 := bstep (se 1 (by rfl) ⟨3432992, by rfl⟩ : syracuseStep 4577323 = 6865985) B6865985
theorem B6862909 : Blo 1427533 6862909 := bstep (se 3 (by rfl) ⟨1286795, by rfl⟩ : syracuseStep 6862909 = 2573591) B2573591
theorem B1931383 : Blo 1427533 1931383 := bstep (se 1 (by rfl) ⟨1448537, by rfl⟩ : syracuseStep 1931383 = 2897075) B2897075
theorem B3258515 : Blo 1427533 3258515 := bstep (se 1 (by rfl) ⟨2443886, by rfl⟩ : syracuseStep 3258515 = 4887773) B4887773
theorem B8141107 : Blo 1427533 8141107 := bstep (se 1 (by rfl) ⟨6105830, by rfl⟩ : syracuseStep 8141107 = 12211661) B12211661
theorem B1808887 : Blo 1427533 1808887 := bstep (se 1 (by rfl) ⟨1356665, by rfl⟩ : syracuseStep 1808887 = 2713331) B2713331
theorem B7232003 : Blo 1427533 7232003 := bstep (se 1 (by rfl) ⟨5424002, by rfl⟩ : syracuseStep 7232003 = 10848005) B10848005
theorem B3430955 : Blo 1427533 3430955 := bstep (se 1 (by rfl) ⟨2573216, by rfl⟩ : syracuseStep 3430955 = 5146433) B5146433
theorem B123648605 : Blo 1427533 123648605 := bstep (se 3 (by rfl) ⟨23184113, by rfl⟩ : syracuseStep 123648605 = 46368227) B46368227
theorem B27474551 : Blo 1427533 27474551 := bstep (se 1 (by rfl) ⟨20605913, by rfl⟩ : syracuseStep 27474551 = 41211827) B41211827
theorem B2710331 : Blo 1427533 2710331 := bstep (se 1 (by rfl) ⟨2032748, by rfl⟩ : syracuseStep 2710331 = 4065497) B4065497
theorem B1809211 : Blo 1427533 1809211 := bstep (se 1 (by rfl) ⟨1356908, by rfl⟩ : syracuseStep 1809211 = 2713817) B2713817
theorem B3431369 : Blo 1427533 3431369 := bstep (se 2 (by rfl) ⟨1286763, by rfl⟩ : syracuseStep 3431369 = 2573527) B2573527
theorem B8133635 : Blo 1427533 8133635 := bstep (se 1 (by rfl) ⟨6100226, by rfl⟩ : syracuseStep 8133635 = 12200453) B12200453
theorem B10296557 : Blo 1427533 10296557 := bstep (se 3 (by rfl) ⟨1930604, by rfl⟩ : syracuseStep 10296557 = 3861209) B3861209
theorem B2710817 : Blo 1427533 2710817 := bstep (se 2 (by rfl) ⟨1016556, by rfl⟩ : syracuseStep 2710817 = 2033113) B2033113
theorem B6520097 : Blo 1427533 6520097 := bstep (se 2 (by rfl) ⟨2445036, by rfl⟩ : syracuseStep 6520097 = 4890073) B4890073
theorem B125254957 : Blo 1427533 125254957 := bstep (se 3 (by rfl) ⟨23485304, by rfl⟩ : syracuseStep 125254957 = 46970609) B46970609
theorem B10845575 : Blo 1427533 10845575 := bstep (se 1 (by rfl) ⟨8134181, by rfl⟩ : syracuseStep 10845575 = 16268363) B16268363
theorem B4578707 : Blo 1427533 4578707 := bstep (se 1 (by rfl) ⟨3434030, by rfl⟩ : syracuseStep 4578707 = 6868061) B6868061
theorem B4824467 : Blo 1427533 4824467 := bstep (se 1 (by rfl) ⟨3618350, by rfl⟩ : syracuseStep 4824467 = 7236701) B7236701
theorem B8134091 : Blo 1427533 8134091 := bstep (se 1 (by rfl) ⟨6100568, by rfl⟩ : syracuseStep 8134091 = 12201137) B12201137
theorem B2711083 : Blo 1427533 2711083 := bstep (se 1 (by rfl) ⟨2033312, by rfl⟩ : syracuseStep 2711083 = 4066625) B4066625
theorem B10296875 : Blo 1427533 10296875 := bstep (se 1 (by rfl) ⟨7722656, by rfl⟩ : syracuseStep 10296875 = 15445313) B15445313
theorem B16277111 : Blo 1427533 16277111 := bstep (se 1 (by rfl) ⟨12207833, by rfl⟩ : syracuseStep 16277111 = 24415667) B24415667
theorem B13033153 : Blo 1427533 13033153 := bstep (se 2 (by rfl) ⟨4887432, by rfl⟩ : syracuseStep 13033153 = 9774865) B9774865
theorem B13721359 : Blo 1427533 13721359 := bstep (se 1 (by rfl) ⟨10291019, by rfl⟩ : syracuseStep 13721359 = 20582039) B20582039
theorem B6103097 : Blo 1427533 6103097 := bstep (se 2 (by rfl) ⟨2288661, by rfl⟩ : syracuseStep 6103097 = 4577323) B4577323
theorem B5423183 : Blo 1427533 5423183 := bstep (se 1 (by rfl) ⟨4067387, by rfl⟩ : syracuseStep 5423183 = 8134775) B8134775
theorem B9150545 : Blo 1427533 9150545 := bstep (se 2 (by rfl) ⟨3431454, by rfl⟩ : syracuseStep 9150545 = 6862909) B6862909
theorem B18563249 : Blo 1427533 18563249 := bstep (se 2 (by rfl) ⟨6961218, by rfl⟩ : syracuseStep 18563249 = 13922437) B13922437
theorem B36610379 : Blo 1427533 36610379 := bstep (se 1 (by rfl) ⟨27457784, by rfl⟩ : syracuseStep 36610379 = 54915569) B54915569
theorem B13730123 : Blo 1427533 13730123 := bstep (se 1 (by rfl) ⟨10297592, by rfl⟩ : syracuseStep 13730123 = 20595185) B20595185
theorem B10854809 : Blo 1427533 10854809 := bstep (se 2 (by rfl) ⟨4070553, by rfl⟩ : syracuseStep 10854809 = 8141107) B8141107
theorem B1606063 : Blo 1427533 1606063 := bstep (se 1 (by rfl) ⟨1204547, by rfl⟩ : syracuseStep 1606063 = 2409095) B2409095
theorem B2712275 : Blo 1427533 2712275 := bstep (se 1 (by rfl) ⟨2034206, by rfl⟩ : syracuseStep 2712275 = 4068413) B4068413
theorem B2409311 : Blo 1427533 2409311 := bstep (se 1 (by rfl) ⟨1806983, by rfl⟩ : syracuseStep 2409311 = 3613967) B3613967
theorem B1606495 : Blo 1427533 1606495 := bstep (se 1 (by rfl) ⟨1204871, by rfl⟩ : syracuseStep 1606495 = 2409743) B2409743
theorem B3212207 : Blo 1427533 3212207 := bstep (se 1 (by rfl) ⟨2409155, by rfl⟩ : syracuseStep 3212207 = 4818311) B4818311
theorem B2712503 : Blo 1427533 2712503 := bstep (se 1 (by rfl) ⟨2034377, by rfl⟩ : syracuseStep 2712503 = 4068755) B4068755
theorem B5424185 : Blo 1427533 5424185 := bstep (se 2 (by rfl) ⟨2034069, by rfl⟩ : syracuseStep 5424185 = 4068139) B4068139
theorem B3212459 : Blo 1427533 3212459 := bstep (se 1 (by rfl) ⟨2409344, by rfl⟩ : syracuseStep 3212459 = 4818689) B4818689
theorem B1606855 : Blo 1427533 1606855 := bstep (se 1 (by rfl) ⟨1205141, by rfl⟩ : syracuseStep 1606855 = 2410283) B2410283
theorem B5145943 : Blo 1427533 5145943 := bstep (se 1 (by rfl) ⟨3859457, by rfl⟩ : syracuseStep 5145943 = 7718915) B7718915
theorem B2409871 : Blo 1427533 2409871 := bstep (se 1 (by rfl) ⟨1807403, by rfl⟩ : syracuseStep 2409871 = 3614807) B3614807
theorem B4818419 : Blo 1427533 4818419 := bstep (se 1 (by rfl) ⟨3613814, by rfl⟩ : syracuseStep 4818419 = 7227629) B7227629
theorem B5146145 : Blo 1427533 5146145 := bstep (se 2 (by rfl) ⟨1929804, by rfl⟩ : syracuseStep 5146145 = 3859609) B3859609
theorem B5146259 : Blo 1427533 5146259 := bstep (se 1 (by rfl) ⟨3859694, by rfl⟩ : syracuseStep 5146259 = 7719389) B7719389
theorem B3212999 : Blo 1427533 3212999 := bstep (se 1 (by rfl) ⟨2409749, by rfl⟩ : syracuseStep 3212999 = 4819499) B4819499
theorem B5424839 : Blo 1427533 5424839 := bstep (se 1 (by rfl) ⟨4068629, by rfl⟩ : syracuseStep 5424839 = 8137259) B8137259
theorem B5793565 : Blo 1427533 5793565 := bstep (se 3 (by rfl) ⟨1086293, by rfl⟩ : syracuseStep 5793565 = 2172587) B2172587
theorem B2033591 : Blo 1427533 2033591 := bstep (se 1 (by rfl) ⟨1525193, by rfl⟩ : syracuseStep 2033591 = 3050387) B3050387
theorem B4818959 : Blo 1427533 4818959 := bstep (se 1 (by rfl) ⟨3614219, by rfl⟩ : syracuseStep 4818959 = 7228439) B7228439
theorem B1607719 : Blo 1427533 1607719 := bstep (se 1 (by rfl) ⟨1205789, by rfl⟩ : syracuseStep 1607719 = 2411579) B2411579
theorem B3614777 : Blo 1427533 3614777 := bstep (se 2 (by rfl) ⟨1355541, by rfl⟩ : syracuseStep 3614777 = 2711083) B2711083
theorem B2410553 : Blo 1427533 2410553 := bstep (se 2 (by rfl) ⟨903957, by rfl⟩ : syracuseStep 2410553 = 1807915) B1807915
theorem B2713657 : Blo 1427533 2713657 := bstep (se 2 (by rfl) ⟨1017621, by rfl⟩ : syracuseStep 2713657 = 2035243) B2035243
theorem B1427535 : Blo 1427533 1427535 := bstep (se 1 (by rfl) ⟨1070651, by rfl⟩ : syracuseStep 1427535 = 2141303) B2141303
theorem B1427551 : Blo 1427533 1427551 := bstep (se 1 (by rfl) ⟨1070663, by rfl⟩ : syracuseStep 1427551 = 2141327) B2141327
theorem B1427579 : Blo 1427533 1427579 := bstep (se 1 (by rfl) ⟨1070684, by rfl⟩ : syracuseStep 1427579 = 2141369) B2141369
theorem B1427631 : Blo 1427533 1427631 := bstep (se 1 (by rfl) ⟨1070723, by rfl⟩ : syracuseStep 1427631 = 2141447) B2141447
theorem B1427655 : Blo 1427533 1427655 := bstep (se 1 (by rfl) ⟨1070741, by rfl⟩ : syracuseStep 1427655 = 2141483) B2141483
theorem B1427675 : Blo 1427533 1427675 := bstep (se 1 (by rfl) ⟨1070756, by rfl⟩ : syracuseStep 1427675 = 2141513) B2141513
theorem B17377537 : Blo 1427533 17377537 := bstep (se 2 (by rfl) ⟨6516576, by rfl⟩ : syracuseStep 17377537 = 13033153) B13033153
theorem B1427751 : Blo 1427533 1427751 := bstep (se 1 (by rfl) ⟨1070813, by rfl⟩ : syracuseStep 1427751 = 2141627) B2141627
theorem B1427791 : Blo 1427533 1427791 := bstep (se 1 (by rfl) ⟨1070843, by rfl⟩ : syracuseStep 1427791 = 2141687) B2141687
theorem B1427807 : Blo 1427533 1427807 := bstep (se 1 (by rfl) ⟨1070855, by rfl⟩ : syracuseStep 1427807 = 2141711) B2141711
theorem B18295145 : Blo 1427533 18295145 := bstep (se 2 (by rfl) ⟨6860679, by rfl⟩ : syracuseStep 18295145 = 13721359) B13721359
theorem B1427835 : Blo 1427533 1427835 := bstep (se 1 (by rfl) ⟨1070876, by rfl⟩ : syracuseStep 1427835 = 2141753) B2141753
theorem B1427887 : Blo 1427533 1427887 := bstep (se 1 (by rfl) ⟨1070915, by rfl⟩ : syracuseStep 1427887 = 2141831) B2141831
theorem B1427911 : Blo 1427533 1427911 := bstep (se 1 (by rfl) ⟨1070933, by rfl⟩ : syracuseStep 1427911 = 2141867) B2141867
theorem B1427931 : Blo 1427533 1427931 := bstep (se 1 (by rfl) ⟨1070948, by rfl⟩ : syracuseStep 1427931 = 2141897) B2141897
theorem B3861017 : Blo 1427533 3861017 := bstep (se 2 (by rfl) ⟨1447881, by rfl⟩ : syracuseStep 3861017 = 2895763) B2895763
theorem B1428007 : Blo 1427533 1428007 := bstep (se 1 (by rfl) ⟨1071005, by rfl⟩ : syracuseStep 1428007 = 2142011) B2142011
theorem B3213863 : Blo 1427533 3213863 := bstep (se 1 (by rfl) ⟨2410397, by rfl⟩ : syracuseStep 3213863 = 4820795) B4820795
theorem B1428047 : Blo 1427533 1428047 := bstep (se 1 (by rfl) ⟨1071035, by rfl⟩ : syracuseStep 1428047 = 2142071) B2142071
theorem B1428063 : Blo 1427533 1428063 := bstep (se 1 (by rfl) ⟨1071047, by rfl⟩ : syracuseStep 1428063 = 2142095) B2142095
theorem B4819553 : Blo 1427533 4819553 := bstep (se 2 (by rfl) ⟨1807332, by rfl⟩ : syracuseStep 4819553 = 3614665) B3614665
theorem B1428091 : Blo 1427533 1428091 := bstep (se 1 (by rfl) ⟨1071068, by rfl⟩ : syracuseStep 1428091 = 2142137) B2142137
theorem B5425811 : Blo 1427533 5425811 := bstep (se 1 (by rfl) ⟨4069358, by rfl⟩ : syracuseStep 5425811 = 8138717) B8138717
theorem B1428143 : Blo 1427533 1428143 := bstep (se 1 (by rfl) ⟨1071107, by rfl⟩ : syracuseStep 1428143 = 2142215) B2142215
theorem B1428167 : Blo 1427533 1428167 := bstep (se 1 (by rfl) ⟨1071125, by rfl⟩ : syracuseStep 1428167 = 2142251) B2142251
theorem B10848977 : Blo 1427533 10848977 := bstep (se 2 (by rfl) ⟨4068366, by rfl⟩ : syracuseStep 10848977 = 8136733) B8136733
theorem B7228115 : Blo 1427533 7228115 := bstep (se 1 (by rfl) ⟨5421086, by rfl⟩ : syracuseStep 7228115 = 10842173) B10842173
theorem B1428187 : Blo 1427533 1428187 := bstep (se 1 (by rfl) ⟨1071140, by rfl⟩ : syracuseStep 1428187 = 2142281) B2142281
theorem B2411255 : Blo 1427533 2411255 := bstep (se 1 (by rfl) ⟨1808441, by rfl⟩ : syracuseStep 2411255 = 3616883) B3616883
theorem B11578115 : Blo 1427533 11578115 := bstep (se 1 (by rfl) ⟨8683586, by rfl⟩ : syracuseStep 11578115 = 17367173) B17367173
theorem B1428263 : Blo 1427533 1428263 := bstep (se 1 (by rfl) ⟨1071197, by rfl⟩ : syracuseStep 1428263 = 2142395) B2142395
theorem B1428303 : Blo 1427533 1428303 := bstep (se 1 (by rfl) ⟨1071227, by rfl⟩ : syracuseStep 1428303 = 2142455) B2142455
theorem B1428319 : Blo 1427533 1428319 := bstep (se 1 (by rfl) ⟨1071239, by rfl⟩ : syracuseStep 1428319 = 2142479) B2142479
theorem B3214187 : Blo 1427533 3214187 := bstep (se 1 (by rfl) ⟨2410640, by rfl⟩ : syracuseStep 3214187 = 4821281) B4821281
theorem B1428347 : Blo 1427533 1428347 := bstep (se 1 (by rfl) ⟨1071260, by rfl⟩ : syracuseStep 1428347 = 2142521) B2142521
theorem B3214241 : Blo 1427533 3214241 := bstep (se 2 (by rfl) ⟨1205340, by rfl⟩ : syracuseStep 3214241 = 2410681) B2410681
theorem B1428399 : Blo 1427533 1428399 := bstep (se 1 (by rfl) ⟨1071299, by rfl⟩ : syracuseStep 1428399 = 2142599) B2142599
theorem B1428423 : Blo 1427533 1428423 := bstep (se 1 (by rfl) ⟨1071317, by rfl⟩ : syracuseStep 1428423 = 2142635) B2142635
theorem B1428443 : Blo 1427533 1428443 := bstep (se 1 (by rfl) ⟨1071332, by rfl⟩ : syracuseStep 1428443 = 2142665) B2142665
theorem B2575379 : Blo 1427533 2575379 := bstep (se 1 (by rfl) ⟨1931534, by rfl⟩ : syracuseStep 2575379 = 3863069) B3863069
theorem B1428519 : Blo 1427533 1428519 := bstep (se 1 (by rfl) ⟨1071389, by rfl⟩ : syracuseStep 1428519 = 2142779) B2142779
theorem B1428559 : Blo 1427533 1428559 := bstep (se 1 (by rfl) ⟨1071419, by rfl⟩ : syracuseStep 1428559 = 2142839) B2142839
theorem B2411599 : Blo 1427533 2411599 := bstep (se 1 (by rfl) ⟨1808699, by rfl⟩ : syracuseStep 2411599 = 3617399) B3617399
theorem B1428575 : Blo 1427533 1428575 := bstep (se 1 (by rfl) ⟨1071431, by rfl⟩ : syracuseStep 1428575 = 2142863) B2142863
theorem B1428603 : Blo 1427533 1428603 := bstep (se 1 (by rfl) ⟨1071452, by rfl⟩ : syracuseStep 1428603 = 2142905) B2142905
theorem B5147819 : Blo 1427533 5147819 := bstep (se 1 (by rfl) ⟨3860864, by rfl⟩ : syracuseStep 5147819 = 7721729) B7721729
theorem B1428655 : Blo 1427533 1428655 := bstep (se 1 (by rfl) ⟨1071491, by rfl⟩ : syracuseStep 1428655 = 2142983) B2142983
theorem B1428679 : Blo 1427533 1428679 := bstep (se 1 (by rfl) ⟨1071509, by rfl⟩ : syracuseStep 1428679 = 2143019) B2143019
theorem B1428699 : Blo 1427533 1428699 := bstep (se 1 (by rfl) ⟨1071524, by rfl⟩ : syracuseStep 1428699 = 2143049) B2143049
theorem B3214583 : Blo 1427533 3214583 := bstep (se 1 (by rfl) ⟨2410937, by rfl⟩ : syracuseStep 3214583 = 4821875) B4821875
theorem B10300709 : Blo 1427533 10300709 := bstep (se 4 (by rfl) ⟨965691, by rfl⟩ : syracuseStep 10300709 = 1931383) B1931383
theorem B1428775 : Blo 1427533 1428775 := bstep (se 1 (by rfl) ⟨1071581, by rfl⟩ : syracuseStep 1428775 = 2143163) B2143163
theorem B2411849 : Blo 1427533 2411849 := bstep (se 2 (by rfl) ⟨904443, by rfl⟩ : syracuseStep 2411849 = 1808887) B1808887
theorem B1428815 : Blo 1427533 1428815 := bstep (se 1 (by rfl) ⟨1071611, by rfl⟩ : syracuseStep 1428815 = 2143223) B2143223
theorem B1428831 : Blo 1427533 1428831 := bstep (se 1 (by rfl) ⟨1071623, by rfl⟩ : syracuseStep 1428831 = 2143247) B2143247
theorem B2035049 : Blo 1427533 2035049 := bstep (se 2 (by rfl) ⟨763143, by rfl⟩ : syracuseStep 2035049 = 1526287) B1526287
theorem B1428859 : Blo 1427533 1428859 := bstep (se 1 (by rfl) ⟨1071644, by rfl⟩ : syracuseStep 1428859 = 2143289) B2143289
theorem B2141615 : Blo 1427533 2141615 := bstep (se 1 (by rfl) ⟨1606211, by rfl⟩ : syracuseStep 2141615 = 3212423) B3212423
theorem B1428911 : Blo 1427533 1428911 := bstep (se 1 (by rfl) ⟨1071683, by rfl⟩ : syracuseStep 1428911 = 2143367) B2143367
theorem B1428935 : Blo 1427533 1428935 := bstep (se 1 (by rfl) ⟨1071701, by rfl⟩ : syracuseStep 1428935 = 2143403) B2143403
theorem B1428955 : Blo 1427533 1428955 := bstep (se 1 (by rfl) ⟨1071716, by rfl⟩ : syracuseStep 1428955 = 2143433) B2143433
theorem B2035163 : Blo 1427533 2035163 := bstep (se 1 (by rfl) ⟨1526372, by rfl⟩ : syracuseStep 2035163 = 3052745) B3052745
theorem B2141705 : Blo 1427533 2141705 := bstep (se 2 (by rfl) ⟨803139, by rfl⟩ : syracuseStep 2141705 = 1606279) B1606279
theorem B3616265 : Blo 1427533 3616265 := bstep (se 2 (by rfl) ⟨1356099, by rfl⟩ : syracuseStep 3616265 = 2712199) B2712199
theorem B4066841 : Blo 1427533 4066841 := bstep (se 2 (by rfl) ⟨1525065, by rfl⟩ : syracuseStep 4066841 = 3050131) B3050131
theorem B2141735 : Blo 1427533 2141735 := bstep (se 1 (by rfl) ⟨1606301, by rfl⟩ : syracuseStep 2141735 = 3212603) B3212603
theorem B1429031 : Blo 1427533 1429031 := bstep (se 1 (by rfl) ⟨1071773, by rfl⟩ : syracuseStep 1429031 = 2143547) B2143547
theorem B1429071 : Blo 1427533 1429071 := bstep (se 1 (by rfl) ⟨1071803, by rfl⟩ : syracuseStep 1429071 = 2143607) B2143607
theorem B10841687 : Blo 1427533 10841687 := bstep (se 1 (by rfl) ⟨8131265, by rfl⟩ : syracuseStep 10841687 = 16262531) B16262531
theorem B1429087 : Blo 1427533 1429087 := bstep (se 1 (by rfl) ⟨1071815, by rfl⟩ : syracuseStep 1429087 = 2143631) B2143631
theorem B13201019 : Blo 1427533 13201019 := bstep (se 1 (by rfl) ⟨9900764, by rfl⟩ : syracuseStep 13201019 = 19801529) B19801529
theorem B2141819 : Blo 1427533 2141819 := bstep (se 1 (by rfl) ⟨1606364, by rfl⟩ : syracuseStep 2141819 = 3212729) B3212729
theorem B1429115 : Blo 1427533 1429115 := bstep (se 1 (by rfl) ⟨1071836, by rfl⟩ : syracuseStep 1429115 = 2143673) B2143673
theorem B4066955 : Blo 1427533 4066955 := bstep (se 1 (by rfl) ⟨3050216, by rfl⟩ : syracuseStep 4066955 = 6100433) B6100433
theorem B1429167 : Blo 1427533 1429167 := bstep (se 1 (by rfl) ⟨1071875, by rfl⟩ : syracuseStep 1429167 = 2143751) B2143751
theorem B1429191 : Blo 1427533 1429191 := bstep (se 1 (by rfl) ⟨1071893, by rfl⟩ : syracuseStep 1429191 = 2143787) B2143787
theorem B1429211 : Blo 1427533 1429211 := bstep (se 1 (by rfl) ⟨1071908, by rfl⟩ : syracuseStep 1429211 = 2143817) B2143817
theorem B12209885 : Blo 1427533 12209885 := bstep (se 3 (by rfl) ⟨2289353, by rfl⟩ : syracuseStep 12209885 = 4578707) B4578707
theorem B2141945 : Blo 1427533 2141945 := bstep (se 2 (by rfl) ⟨803229, by rfl⟩ : syracuseStep 2141945 = 1606459) B1606459
theorem B2412281 : Blo 1427533 2412281 := bstep (se 2 (by rfl) ⟨904605, by rfl⟩ : syracuseStep 2412281 = 1809211) B1809211
theorem B5500715 : Blo 1427533 5500715 := bstep (se 1 (by rfl) ⟨4125536, by rfl⟩ : syracuseStep 5500715 = 8251073) B8251073
theorem B1429287 : Blo 1427533 1429287 := bstep (se 1 (by rfl) ⟨1071965, by rfl⟩ : syracuseStep 1429287 = 2143931) B2143931
theorem B11587387 : Blo 1427533 11587387 := bstep (se 1 (by rfl) ⟨8690540, by rfl⟩ : syracuseStep 11587387 = 17381081) B17381081
theorem B3215177 : Blo 1427533 3215177 := bstep (se 2 (by rfl) ⟨1205691, by rfl⟩ : syracuseStep 3215177 = 2411383) B2411383
theorem B1429327 : Blo 1427533 1429327 := bstep (se 1 (by rfl) ⟨1071995, by rfl⟩ : syracuseStep 1429327 = 2143991) B2143991
theorem B2142047 : Blo 1427533 2142047 := bstep (se 1 (by rfl) ⟨1606535, by rfl⟩ : syracuseStep 2142047 = 3213071) B3213071
theorem B1429343 : Blo 1427533 1429343 := bstep (se 1 (by rfl) ⟨1072007, by rfl⟩ : syracuseStep 1429343 = 2144015) B2144015
theorem B2142059 : Blo 1427533 2142059 := bstep (se 1 (by rfl) ⟨1606544, by rfl⟩ : syracuseStep 2142059 = 3213089) B3213089
theorem B1429371 : Blo 1427533 1429371 := bstep (se 1 (by rfl) ⟨1072028, by rfl⟩ : syracuseStep 1429371 = 2144057) B2144057
theorem B1429423 : Blo 1427533 1429423 := bstep (se 1 (by rfl) ⟨1072067, by rfl⟩ : syracuseStep 1429423 = 2144135) B2144135
theorem B23179193 : Blo 1427533 23179193 := bstep (se 2 (by rfl) ⟨8692197, by rfl⟩ : syracuseStep 23179193 = 17384395) B17384395
theorem B4886459 : Blo 1427533 4886459 := bstep (se 1 (by rfl) ⟨3664844, by rfl⟩ : syracuseStep 4886459 = 7329689) B7329689
theorem B1429447 : Blo 1427533 1429447 := bstep (se 1 (by rfl) ⟨1072085, by rfl⟩ : syracuseStep 1429447 = 2144171) B2144171
theorem B11579345 : Blo 1427533 11579345 := bstep (se 2 (by rfl) ⟨4342254, by rfl⟩ : syracuseStep 11579345 = 8684509) B8684509
theorem B1429467 : Blo 1427533 1429467 := bstep (se 1 (by rfl) ⟨1072100, by rfl⟩ : syracuseStep 1429467 = 2144201) B2144201
theorem B4821011 : Blo 1427533 4821011 := bstep (se 1 (by rfl) ⟨3615758, by rfl⟩ : syracuseStep 4821011 = 7231517) B7231517
theorem B2142287 : Blo 1427533 2142287 := bstep (se 1 (by rfl) ⟨1606715, by rfl⟩ : syracuseStep 2142287 = 3213431) B3213431
theorem B1929415 : Blo 1427533 1929415 := bstep (se 1 (by rfl) ⟨1447061, by rfl⟩ : syracuseStep 1929415 = 2894123) B2894123
theorem B2142407 : Blo 1427533 2142407 := bstep (se 1 (by rfl) ⟨1606805, by rfl⟩ : syracuseStep 2142407 = 3213611) B3213611
theorem B4821335 : Blo 1427533 4821335 := bstep (se 1 (by rfl) ⟨3616001, by rfl⟩ : syracuseStep 4821335 = 7232003) B7232003
theorem B9154903 : Blo 1427533 9154903 := bstep (se 1 (by rfl) ⟨6866177, by rfl⟩ : syracuseStep 9154903 = 13732355) B13732355
theorem B2142569 : Blo 1427533 2142569 := bstep (se 2 (by rfl) ⟨803463, by rfl⟩ : syracuseStep 2142569 = 1606927) B1606927
theorem B9146753 : Blo 1427533 9146753 := bstep (se 2 (by rfl) ⟨3430032, by rfl⟩ : syracuseStep 9146753 = 6860065) B6860065
theorem B167006609 : Blo 1427533 167006609 := bstep (se 2 (by rfl) ⟨62627478, by rfl⟩ : syracuseStep 167006609 = 125254957) B125254957
theorem B82432403 : Blo 1427533 82432403 := bstep (se 1 (by rfl) ⟨61824302, by rfl⟩ : syracuseStep 82432403 = 123648605) B123648605
theorem B2142647 : Blo 1427533 2142647 := bstep (se 1 (by rfl) ⟨1606985, by rfl⟩ : syracuseStep 2142647 = 3213971) B3213971
theorem B2142683 : Blo 1427533 2142683 := bstep (se 1 (by rfl) ⟨1607012, by rfl⟩ : syracuseStep 2142683 = 3214025) B3214025
theorem B18551305 : Blo 1427533 18551305 := bstep (se 2 (by rfl) ⟨6956739, by rfl⟩ : syracuseStep 18551305 = 13913479) B13913479
theorem B1806887 : Blo 1427533 1806887 := bstep (se 1 (by rfl) ⟨1355165, by rfl⟩ : syracuseStep 1806887 = 2710331) B2710331
theorem B3215969 : Blo 1427533 3215969 := bstep (se 2 (by rfl) ⟨1205988, by rfl⟩ : syracuseStep 3215969 = 2411977) B2411977
theorem B3617419 : Blo 1427533 3617419 := bstep (se 1 (by rfl) ⟨2713064, by rfl⟩ : syracuseStep 3617419 = 5426129) B5426129
theorem B5149433 : Blo 1427533 5149433 := bstep (se 2 (by rfl) ⟨1931037, by rfl⟩ : syracuseStep 5149433 = 3862075) B3862075
theorem B1807211 : Blo 1427533 1807211 := bstep (se 1 (by rfl) ⟨1355408, by rfl⟩ : syracuseStep 1807211 = 2710817) B2710817
theorem B4346731 : Blo 1427533 4346731 := bstep (se 1 (by rfl) ⟨3260048, by rfl⟩ : syracuseStep 4346731 = 6520097) B6520097
theorem B7230383 : Blo 1427533 7230383 := bstep (se 1 (by rfl) ⟨5422787, by rfl⟩ : syracuseStep 7230383 = 10845575) B10845575
theorem B2143151 : Blo 1427533 2143151 := bstep (se 1 (by rfl) ⟨1607363, by rfl⟩ : syracuseStep 2143151 = 3214727) B3214727
theorem B2749367 : Blo 1427533 2749367 := bstep (se 1 (by rfl) ⟨2062025, by rfl⟩ : syracuseStep 2749367 = 4124051) B4124051
theorem B3216311 : Blo 1427533 3216311 := bstep (se 1 (by rfl) ⟨2412233, by rfl⟩ : syracuseStep 3216311 = 4824467) B4824467
theorem B3617723 : Blo 1427533 3617723 := bstep (se 1 (by rfl) ⟨2713292, by rfl⟩ : syracuseStep 3617723 = 5426585) B5426585
theorem B2143241 : Blo 1427533 2143241 := bstep (se 2 (by rfl) ⟨803715, by rfl⟩ : syracuseStep 2143241 = 1607431) B1607431
theorem B2143271 : Blo 1427533 2143271 := bstep (se 1 (by rfl) ⟨1607453, by rfl⟩ : syracuseStep 2143271 = 3214907) B3214907
theorem B10851407 : Blo 1427533 10851407 := bstep (se 1 (by rfl) ⟨8138555, by rfl⟩ : syracuseStep 10851407 = 16277111) B16277111
theorem B2143355 : Blo 1427533 2143355 := bstep (se 1 (by rfl) ⟨1607516, by rfl⟩ : syracuseStep 2143355 = 3215033) B3215033
theorem B2143481 : Blo 1427533 2143481 := bstep (se 2 (by rfl) ⟨803805, by rfl⟩ : syracuseStep 2143481 = 1607611) B1607611
theorem B5649751 : Blo 1427533 5649751 := bstep (se 1 (by rfl) ⟨4237313, by rfl⟩ : syracuseStep 5649751 = 8474627) B8474627
theorem B2143583 : Blo 1427533 2143583 := bstep (se 1 (by rfl) ⟨1607687, by rfl⟩ : syracuseStep 2143583 = 3215375) B3215375
theorem B2143595 : Blo 1427533 2143595 := bstep (se 1 (by rfl) ⟨1607696, by rfl⟩ : syracuseStep 2143595 = 3215393) B3215393
theorem B4822415 : Blo 1427533 4822415 := bstep (se 1 (by rfl) ⟨3616811, by rfl⟩ : syracuseStep 4822415 = 7233623) B7233623
theorem B8140175 : Blo 1427533 8140175 := bstep (se 1 (by rfl) ⟨6105131, by rfl⟩ : syracuseStep 8140175 = 12210263) B12210263
theorem B12531145 : Blo 1427533 12531145 := bstep (se 2 (by rfl) ⟨4699179, by rfl⟩ : syracuseStep 12531145 = 9398359) B9398359
theorem B1545691 : Blo 1427533 1545691 := bstep (se 1 (by rfl) ⟨1159268, by rfl⟩ : syracuseStep 1545691 = 2318537) B2318537
theorem B117298651 : Blo 1427533 117298651 := bstep (se 1 (by rfl) ⟨87973988, by rfl⟩ : syracuseStep 117298651 = 175947977) B175947977
theorem B2143823 : Blo 1427533 2143823 := bstep (se 1 (by rfl) ⟨1607867, by rfl⟩ : syracuseStep 2143823 = 3215735) B3215735
theorem B2143943 : Blo 1427533 2143943 := bstep (se 1 (by rfl) ⟨1607957, by rfl⟩ : syracuseStep 2143943 = 3215915) B3215915
theorem B3618503 : Blo 1427533 3618503 := bstep (se 1 (by rfl) ⟨2713877, by rfl⟩ : syracuseStep 3618503 = 5427755) B5427755
theorem B5420753 : Blo 1427533 5420753 := bstep (se 2 (by rfl) ⟨2032782, by rfl⟩ : syracuseStep 5420753 = 4065565) B4065565
theorem B4822739 : Blo 1427533 4822739 := bstep (se 1 (by rfl) ⟨3617054, by rfl⟩ : syracuseStep 4822739 = 7234109) B7234109
theorem B8689373 : Blo 1427533 8689373 := bstep (se 3 (by rfl) ⟨1629257, by rfl⟩ : syracuseStep 8689373 = 3258515) B3258515
theorem B2144105 : Blo 1427533 2144105 := bstep (se 2 (by rfl) ⟨804039, by rfl⟩ : syracuseStep 2144105 = 1608079) B1608079
theorem B2144183 : Blo 1427533 2144183 := bstep (se 1 (by rfl) ⟨1608137, by rfl⟩ : syracuseStep 2144183 = 3216275) B3216275
theorem B2144219 : Blo 1427533 2144219 := bstep (se 1 (by rfl) ⟨1608164, by rfl⟩ : syracuseStep 2144219 = 3216329) B3216329
theorem B19535879 : Blo 1427533 19535879 := bstep (se 1 (by rfl) ⟨14651909, by rfl⟩ : syracuseStep 19535879 = 29303819) B29303819
theorem B4888595 : Blo 1427533 4888595 := bstep (se 1 (by rfl) ⟨3666446, by rfl⟩ : syracuseStep 4888595 = 7332893) B7332893
theorem B1808507 : Blo 1427533 1808507 := bstep (se 1 (by rfl) ⟨1356380, by rfl⟩ : syracuseStep 1808507 = 2712761) B2712761
theorem B5150873 : Blo 1427533 5150873 := bstep (se 2 (by rfl) ⟨1931577, by rfl⟩ : syracuseStep 5150873 = 3863155) B3863155
theorem B50141425 : Blo 1427533 50141425 := bstep (se 2 (by rfl) ⟨18803034, by rfl⟩ : syracuseStep 50141425 = 37606069) B37606069
theorem B5421437 : Blo 1427533 5421437 := bstep (se 3 (by rfl) ⟨1016519, by rfl⟩ : syracuseStep 5421437 = 2033039) B2033039
theorem B4069757 : Blo 1427533 4069757 := bstep (se 3 (by rfl) ⟨763079, by rfl⟩ : syracuseStep 4069757 = 1526159) B1526159
theorem B13719941 : Blo 1427533 13719941 := bstep (se 4 (by rfl) ⟨1286244, by rfl⟩ : syracuseStep 13719941 = 2572489) B2572489
theorem B3430937 : Blo 1427533 3430937 := bstep (se 2 (by rfl) ⟨1286601, by rfl⟩ : syracuseStep 3430937 = 2573203) B2573203
theorem B1448647 : Blo 1427533 1448647 := bstep (se 1 (by rfl) ⟨1086485, by rfl⟩ : syracuseStep 1448647 = 2172971) B2172971
theorem B4578041 : Blo 1427533 4578041 := bstep (se 2 (by rfl) ⟨1716765, by rfl⟩ : syracuseStep 4578041 = 3433531) B3433531
theorem B9149213 : Blo 1427533 9149213 := bstep (se 3 (by rfl) ⟨1715477, by rfl⟩ : syracuseStep 9149213 = 3430955) B3430955
theorem B70441757 : Blo 1427533 70441757 := bstep (se 3 (by rfl) ⟨13207829, by rfl⟩ : syracuseStep 70441757 = 26415659) B26415659
theorem B3431263 : Blo 1427533 3431263 := bstep (se 1 (by rfl) ⟨2573447, by rfl⟩ : syracuseStep 3431263 = 5146895) B5146895
theorem B6101867 : Blo 1427533 6101867 := bstep (se 1 (by rfl) ⟨4576400, by rfl⟩ : syracuseStep 6101867 = 9152801) B9152801
theorem B4823927 : Blo 1427533 4823927 := bstep (se 1 (by rfl) ⟨3617945, by rfl⟩ : syracuseStep 4823927 = 7235891) B7235891
theorem B2710415 : Blo 1427533 2710415 := bstep (se 1 (by rfl) ⟨2032811, by rfl⟩ : syracuseStep 2710415 = 4065623) B4065623
theorem B10296209 : Blo 1427533 10296209 := bstep (se 2 (by rfl) ⟨3861078, by rfl⟩ : syracuseStep 10296209 = 7722157) B7722157
theorem B11590735 : Blo 1427533 11590735 := bstep (se 1 (by rfl) ⟨8693051, by rfl⟩ : syracuseStep 11590735 = 17386103) B17386103
theorem B18316367 : Blo 1427533 18316367 := bstep (se 1 (by rfl) ⟨13737275, by rfl⟩ : syracuseStep 18316367 = 27474551) B27474551
theorem B4824143 : Blo 1427533 4824143 := bstep (se 1 (by rfl) ⟨3618107, by rfl⟩ : syracuseStep 4824143 = 7236215) B7236215
theorem B5422423 : Blo 1427533 5422423 := bstep (se 1 (by rfl) ⟨4066817, by rfl⟩ : syracuseStep 5422423 = 8133635) B8133635
theorem B111336889 : Blo 1427533 111336889 := bstep (se 2 (by rfl) ⟨41751333, by rfl⟩ : syracuseStep 111336889 = 83502667) B83502667
theorem B4824521 : Blo 1427533 4824521 := bstep (se 2 (by rfl) ⟨1809195, by rfl⟩ : syracuseStep 4824521 = 3618391) B3618391
theorem B6864371 : Blo 1427533 6864371 := bstep (se 1 (by rfl) ⟨5148278, by rfl⟩ : syracuseStep 6864371 = 10296557) B10296557
theorem B5422727 : Blo 1427533 5422727 := bstep (se 1 (by rfl) ⟨4067045, by rfl⟩ : syracuseStep 5422727 = 8134091) B8134091
theorem B8134343 : Blo 1427533 8134343 := bstep (se 1 (by rfl) ⟨6100757, by rfl⟩ : syracuseStep 8134343 = 12201515) B12201515
theorem B6864583 : Blo 1427533 6864583 := bstep (se 1 (by rfl) ⟨5148437, by rfl⟩ : syracuseStep 6864583 = 10296875) B10296875
theorem B7331543 : Blo 1427533 7331543 := bstep (se 1 (by rfl) ⟨5498657, by rfl⟩ : syracuseStep 7331543 = 10997315) B10997315
theorem B9150317 : Blo 1427533 9150317 := bstep (se 3 (by rfl) ⟨1715684, by rfl⟩ : syracuseStep 9150317 = 3431369) B3431369
theorem B10846061 : Blo 1427533 10846061 := bstep (se 3 (by rfl) ⟨2033636, by rfl⟩ : syracuseStep 10846061 = 4067273) B4067273
theorem B5496763 : Blo 1427533 5496763 := bstep (se 1 (by rfl) ⟨4122572, by rfl⟩ : syracuseStep 5496763 = 8245145) B8245145
theorem B2572553 : Blo 1427533 2572553 := bstep (se 2 (by rfl) ⟨964707, by rfl⟩ : syracuseStep 2572553 = 1929415) B1929415
theorem B111337739 : Blo 1427533 111337739 := bstep (se 1 (by rfl) ⟨83503304, by rfl⟩ : syracuseStep 111337739 = 167006609) B167006609
theorem B66855233 : Blo 1427533 66855233 := bstep (se 2 (by rfl) ⟨25070712, by rfl⟩ : syracuseStep 66855233 = 50141425) B50141425
theorem B12206537 : Blo 1427533 12206537 := bstep (se 2 (by rfl) ⟨4577451, by rfl⟩ : syracuseStep 12206537 = 9154903) B9154903
theorem B3432955 : Blo 1427533 3432955 := bstep (se 1 (by rfl) ⟨2574716, by rfl⟩ : syracuseStep 3432955 = 5149433) B5149433
theorem B1606207 : Blo 1427533 1606207 := bstep (se 1 (by rfl) ⟨1204655, by rfl⟩ : syracuseStep 1606207 = 2409311) B2409311
theorem B7234271 : Blo 1427533 7234271 := bstep (se 1 (by rfl) ⟨5425703, by rfl⟩ : syracuseStep 7234271 = 10851407) B10851407
theorem B3212279 : Blo 1427533 3212279 := bstep (se 1 (by rfl) ⟨2409209, by rfl⟩ : syracuseStep 3212279 = 4818419) B4818419
theorem B7726117 : Blo 1427533 7726117 := bstep (se 4 (by rfl) ⟨724323, by rfl⟩ : syracuseStep 7726117 = 1448647) B1448647
theorem B3613835 : Blo 1427533 3613835 := bstep (se 1 (by rfl) ⟨2710376, by rfl⟩ : syracuseStep 3613835 = 5420753) B5420753
theorem B5792915 : Blo 1427533 5792915 := bstep (se 1 (by rfl) ⟨4344686, by rfl⟩ : syracuseStep 5792915 = 8689373) B8689373
theorem B3212639 : Blo 1427533 3212639 := bstep (se 1 (by rfl) ⟨2409479, by rfl⟩ : syracuseStep 3212639 = 4818959) B4818959
theorem B2409851 : Blo 1427533 2409851 := bstep (se 1 (by rfl) ⟨1807388, by rfl⟩ : syracuseStep 2409851 = 3614777) B3614777
theorem B1607035 : Blo 1427533 1607035 := bstep (se 1 (by rfl) ⟨1205276, by rfl⟩ : syracuseStep 1607035 = 2410553) B2410553
theorem B3433915 : Blo 1427533 3433915 := bstep (se 1 (by rfl) ⟨2575436, by rfl⟩ : syracuseStep 3433915 = 5150873) B5150873
theorem B4818365 : Blo 1427533 4818365 := bstep (se 3 (by rfl) ⟨903443, by rfl⟩ : syracuseStep 4818365 = 1806887) B1806887
theorem B3614291 : Blo 1427533 3614291 := bstep (se 1 (by rfl) ⟨2710718, by rfl⟩ : syracuseStep 3614291 = 5421437) B5421437
theorem B2713171 : Blo 1427533 2713171 := bstep (se 1 (by rfl) ⟨2034878, by rfl⟩ : syracuseStep 2713171 = 4069757) B4069757
theorem B2287291 : Blo 1427533 2287291 := bstep (se 1 (by rfl) ⟨1715468, by rfl⟩ : syracuseStep 2287291 = 3430937) B3430937
theorem B2574011 : Blo 1427533 2574011 := bstep (se 1 (by rfl) ⟨1930508, by rfl⟩ : syracuseStep 2574011 = 3861017) B3861017
theorem B13723357 : Blo 1427533 13723357 := bstep (se 3 (by rfl) ⟨2573129, by rfl⟩ : syracuseStep 13723357 = 5146259) B5146259
theorem B3213035 : Blo 1427533 3213035 := bstep (se 1 (by rfl) ⟨2409776, by rfl⟩ : syracuseStep 3213035 = 4819553) B4819553
theorem B4818743 : Blo 1427533 4818743 := bstep (se 1 (by rfl) ⟨3614057, by rfl⟩ : syracuseStep 4818743 = 7228115) B7228115
theorem B1607503 : Blo 1427533 1607503 := bstep (se 1 (by rfl) ⟨1205627, by rfl⟩ : syracuseStep 1607503 = 2411255) B2411255
theorem B7718743 : Blo 1427533 7718743 := bstep (se 1 (by rfl) ⟨5789057, by rfl⟩ : syracuseStep 7718743 = 11578115) B11578115
theorem B3213161 : Blo 1427533 3213161 := bstep (se 2 (by rfl) ⟨1204935, by rfl⟩ : syracuseStep 3213161 = 2409871) B2409871
theorem B148449185 : Blo 1427533 148449185 := bstep (se 2 (by rfl) ⟨55668444, by rfl⟩ : syracuseStep 148449185 = 111336889) B111336889
theorem B6867139 : Blo 1427533 6867139 := bstep (se 1 (by rfl) ⟨5150354, by rfl⟩ : syracuseStep 6867139 = 10300709) B10300709
theorem B1607899 : Blo 1427533 1607899 := bstep (se 1 (by rfl) ⟨1205924, by rfl⟩ : syracuseStep 1607899 = 2411849) B2411849
theorem B9152777 : Blo 1427533 9152777 := bstep (se 2 (by rfl) ⟨3432291, by rfl⟩ : syracuseStep 9152777 = 6864583) B6864583
theorem B4819229 : Blo 1427533 4819229 := bstep (se 3 (by rfl) ⟨903605, by rfl⟩ : syracuseStep 4819229 = 1807211) B1807211
theorem B1427743 : Blo 1427533 1427743 := bstep (se 1 (by rfl) ⟨1070807, by rfl⟩ : syracuseStep 1427743 = 2141615) B2141615
theorem B1427803 : Blo 1427533 1427803 := bstep (se 1 (by rfl) ⟨1070852, by rfl⟩ : syracuseStep 1427803 = 2141705) B2141705
theorem B2410843 : Blo 1427533 2410843 := bstep (se 1 (by rfl) ⟨1808132, by rfl⟩ : syracuseStep 2410843 = 3616265) B3616265
theorem B1427823 : Blo 1427533 1427823 := bstep (se 1 (by rfl) ⟨1070867, by rfl⟩ : syracuseStep 1427823 = 2141735) B2141735
theorem B7227791 : Blo 1427533 7227791 := bstep (se 1 (by rfl) ⟨5420843, by rfl⟩ : syracuseStep 7227791 = 10841687) B10841687
theorem B8800679 : Blo 1427533 8800679 := bstep (se 1 (by rfl) ⟨6600509, by rfl⟩ : syracuseStep 8800679 = 13201019) B13201019
theorem B1427879 : Blo 1427533 1427879 := bstep (se 1 (by rfl) ⟨1070909, by rfl⟩ : syracuseStep 1427879 = 2141819) B2141819
theorem B3615151 : Blo 1427533 3615151 := bstep (se 1 (by rfl) ⟨2711363, by rfl⟩ : syracuseStep 3615151 = 5422727) B5422727
theorem B1427963 : Blo 1427533 1427963 := bstep (se 1 (by rfl) ⟨1070972, by rfl⟩ : syracuseStep 1427963 = 2141945) B2141945
theorem B1608187 : Blo 1427533 1608187 := bstep (se 1 (by rfl) ⟨1206140, by rfl⟩ : syracuseStep 1608187 = 2412281) B2412281
theorem B1428031 : Blo 1427533 1428031 := bstep (se 1 (by rfl) ⟨1071023, by rfl⟩ : syracuseStep 1428031 = 2142047) B2142047
theorem B1428039 : Blo 1427533 1428039 := bstep (se 1 (by rfl) ⟨1071029, by rfl⟩ : syracuseStep 1428039 = 2142059) B2142059
theorem B15452795 : Blo 1427533 15452795 := bstep (se 1 (by rfl) ⟨11589596, by rfl⟩ : syracuseStep 15452795 = 23179193) B23179193
theorem B7719563 : Blo 1427533 7719563 := bstep (se 1 (by rfl) ⟨5789672, by rfl⟩ : syracuseStep 7719563 = 11579345) B11579345
theorem B3214007 : Blo 1427533 3214007 := bstep (se 1 (by rfl) ⟨2410505, by rfl⟩ : syracuseStep 3214007 = 4821011) B4821011
theorem B1428191 : Blo 1427533 1428191 := bstep (se 1 (by rfl) ⟨1071143, by rfl⟩ : syracuseStep 1428191 = 2142287) B2142287
theorem B3615455 : Blo 1427533 3615455 := bstep (se 1 (by rfl) ⟨2711591, by rfl⟩ : syracuseStep 3615455 = 5423183) B5423183
theorem B1428271 : Blo 1427533 1428271 := bstep (se 1 (by rfl) ⟨1071203, by rfl⟩ : syracuseStep 1428271 = 2142407) B2142407
theorem B24406919 : Blo 1427533 24406919 := bstep (se 1 (by rfl) ⟨18305189, by rfl⟩ : syracuseStep 24406919 = 36610379) B36610379
theorem B9153415 : Blo 1427533 9153415 := bstep (se 1 (by rfl) ⟨6865061, by rfl⟩ : syracuseStep 9153415 = 13730123) B13730123
theorem B3214223 : Blo 1427533 3214223 := bstep (se 1 (by rfl) ⟨2410667, by rfl⟩ : syracuseStep 3214223 = 4821335) B4821335
theorem B1428379 : Blo 1427533 1428379 := bstep (se 1 (by rfl) ⟨1071284, by rfl⟩ : syracuseStep 1428379 = 2142569) B2142569
theorem B6097835 : Blo 1427533 6097835 := bstep (se 1 (by rfl) ⟨4573376, by rfl⟩ : syracuseStep 6097835 = 9146753) B9146753
theorem B54954935 : Blo 1427533 54954935 := bstep (se 1 (by rfl) ⟨41216201, by rfl⟩ : syracuseStep 54954935 = 82432403) B82432403
theorem B7236539 : Blo 1427533 7236539 := bstep (se 1 (by rfl) ⟨5427404, by rfl⟩ : syracuseStep 7236539 = 10854809) B10854809
theorem B1428431 : Blo 1427533 1428431 := bstep (se 1 (by rfl) ⟨1071323, by rfl⟩ : syracuseStep 1428431 = 2142647) B2142647
theorem B1428455 : Blo 1427533 1428455 := bstep (se 1 (by rfl) ⟨1071341, by rfl⟩ : syracuseStep 1428455 = 2142683) B2142683
theorem B23170049 : Blo 1427533 23170049 := bstep (se 2 (by rfl) ⟨8688768, by rfl⟩ : syracuseStep 23170049 = 17377537) B17377537
theorem B2141417 : Blo 1427533 2141417 := bstep (se 2 (by rfl) ⟨803031, by rfl⟩ : syracuseStep 2141417 = 1606063) B1606063
theorem B2141471 : Blo 1427533 2141471 := bstep (se 1 (by rfl) ⟨1606103, by rfl⟩ : syracuseStep 2141471 = 3212207) B3212207
theorem B4820255 : Blo 1427533 4820255 := bstep (se 1 (by rfl) ⟨3615191, by rfl⟩ : syracuseStep 4820255 = 7230383) B7230383
theorem B1428767 : Blo 1427533 1428767 := bstep (se 1 (by rfl) ⟨1071575, by rfl⟩ : syracuseStep 1428767 = 2143151) B2143151
theorem B2411815 : Blo 1427533 2411815 := bstep (se 1 (by rfl) ⟨1808861, by rfl⟩ : syracuseStep 2411815 = 3617723) B3617723
theorem B1428827 : Blo 1427533 1428827 := bstep (se 1 (by rfl) ⟨1071620, by rfl⟩ : syracuseStep 1428827 = 2143241) B2143241
theorem B24735073 : Blo 1427533 24735073 := bstep (se 2 (by rfl) ⟨9275652, by rfl⟩ : syracuseStep 24735073 = 18551305) B18551305
theorem B1428847 : Blo 1427533 1428847 := bstep (se 1 (by rfl) ⟨1071635, by rfl⟩ : syracuseStep 1428847 = 2143271) B2143271
theorem B3616123 : Blo 1427533 3616123 := bstep (se 1 (by rfl) ⟨2712092, by rfl⟩ : syracuseStep 3616123 = 5424185) B5424185
theorem B1428903 : Blo 1427533 1428903 := bstep (se 1 (by rfl) ⟨1071677, by rfl⟩ : syracuseStep 1428903 = 2143355) B2143355
theorem B2141639 : Blo 1427533 2141639 := bstep (se 1 (by rfl) ⟨1606229, by rfl⟩ : syracuseStep 2141639 = 3212459) B3212459
theorem B1428987 : Blo 1427533 1428987 := bstep (se 1 (by rfl) ⟨1071740, by rfl⟩ : syracuseStep 1428987 = 2143481) B2143481
theorem B1429055 : Blo 1427533 1429055 := bstep (se 1 (by rfl) ⟨1071791, by rfl⟩ : syracuseStep 1429055 = 2143583) B2143583
theorem B1429063 : Blo 1427533 1429063 := bstep (se 1 (by rfl) ⟨1071797, by rfl⟩ : syracuseStep 1429063 = 2143595) B2143595
theorem B3214943 : Blo 1427533 3214943 := bstep (se 1 (by rfl) ⟨2411207, by rfl⟩ : syracuseStep 3214943 = 4822415) B4822415
theorem B5426783 : Blo 1427533 5426783 := bstep (se 1 (by rfl) ⟨4070087, by rfl⟩ : syracuseStep 5426783 = 8140175) B8140175
theorem B5426797 : Blo 1427533 5426797 := bstep (se 3 (by rfl) ⟨1017524, by rfl⟩ : syracuseStep 5426797 = 2035049) B2035049
theorem B1429215 : Blo 1427533 1429215 := bstep (se 1 (by rfl) ⟨1071911, by rfl⟩ : syracuseStep 1429215 = 2143823) B2143823
theorem B2141993 : Blo 1427533 2141993 := bstep (se 2 (by rfl) ⟨803247, by rfl⟩ : syracuseStep 2141993 = 1606495) B1606495
theorem B4575017 : Blo 1427533 4575017 := bstep (se 2 (by rfl) ⟨1715631, by rfl⟩ : syracuseStep 4575017 = 3431263) B3431263
theorem B2141999 : Blo 1427533 2141999 := bstep (se 1 (by rfl) ⟨1606499, by rfl⟩ : syracuseStep 2141999 = 3212999) B3212999
theorem B3616559 : Blo 1427533 3616559 := bstep (se 1 (by rfl) ⟨2712419, by rfl⟩ : syracuseStep 3616559 = 5424839) B5424839
theorem B1429295 : Blo 1427533 1429295 := bstep (se 1 (by rfl) ⟨1071971, by rfl⟩ : syracuseStep 1429295 = 2143943) B2143943
theorem B2412335 : Blo 1427533 2412335 := bstep (se 1 (by rfl) ⟨1809251, by rfl⟩ : syracuseStep 2412335 = 3618503) B3618503
theorem B3215159 : Blo 1427533 3215159 := bstep (se 1 (by rfl) ⟨2411369, by rfl⟩ : syracuseStep 3215159 = 4822739) B4822739
theorem B5795641 : Blo 1427533 5795641 := bstep (se 2 (by rfl) ⟨2173365, by rfl⟩ : syracuseStep 5795641 = 4346731) B4346731
theorem B1429403 : Blo 1427533 1429403 := bstep (se 1 (by rfl) ⟨1072052, by rfl⟩ : syracuseStep 1429403 = 2144105) B2144105
theorem B5427101 : Blo 1427533 5427101 := bstep (se 3 (by rfl) ⟨1017581, by rfl⟩ : syracuseStep 5427101 = 2035163) B2035163
theorem B1429455 : Blo 1427533 1429455 := bstep (se 1 (by rfl) ⟨1072091, by rfl⟩ : syracuseStep 1429455 = 2144183) B2144183
theorem B1429479 : Blo 1427533 1429479 := bstep (se 1 (by rfl) ⟨1072109, by rfl⟩ : syracuseStep 1429479 = 2144219) B2144219
theorem B3215465 : Blo 1427533 3215465 := bstep (se 2 (by rfl) ⟨1205799, by rfl⟩ : syracuseStep 3215465 = 2411599) B2411599
theorem B15454313 : Blo 1427533 15454313 := bstep (se 2 (by rfl) ⟨5795367, by rfl⟩ : syracuseStep 15454313 = 11590735) B11590735
theorem B9146627 : Blo 1427533 9146627 := bstep (se 1 (by rfl) ⟨6859970, by rfl⟩ : syracuseStep 9146627 = 13719941) B13719941
theorem B2142473 : Blo 1427533 2142473 := bstep (se 2 (by rfl) ⟨803427, by rfl⟩ : syracuseStep 2142473 = 1606855) B1606855
theorem B2142575 : Blo 1427533 2142575 := bstep (se 1 (by rfl) ⟨1606931, by rfl⟩ : syracuseStep 2142575 = 3213863) B3213863
theorem B3617207 : Blo 1427533 3617207 := bstep (se 1 (by rfl) ⟨2712905, by rfl⟩ : syracuseStep 3617207 = 5425811) B5425811
theorem B6861257 : Blo 1427533 6861257 := bstep (se 2 (by rfl) ⟨2572971, by rfl⟩ : syracuseStep 6861257 = 5145943) B5145943
theorem B7229897 : Blo 1427533 7229897 := bstep (se 2 (by rfl) ⟨2711211, by rfl⟩ : syracuseStep 7229897 = 5422423) B5422423
theorem B7533001 : Blo 1427533 7533001 := bstep (se 2 (by rfl) ⟨2824875, by rfl⟩ : syracuseStep 7533001 = 5649751) B5649751
theorem B3052027 : Blo 1427533 3052027 := bstep (se 1 (by rfl) ⟨2289020, by rfl⟩ : syracuseStep 3052027 = 4578041) B4578041
theorem B6099475 : Blo 1427533 6099475 := bstep (se 1 (by rfl) ⟨4574606, by rfl⟩ : syracuseStep 6099475 = 9149213) B9149213
theorem B46961171 : Blo 1427533 46961171 := bstep (se 1 (by rfl) ⟨35220878, by rfl⟩ : syracuseStep 46961171 = 70441757) B70441757
theorem B4067911 : Blo 1427533 4067911 := bstep (se 1 (by rfl) ⟨3050933, by rfl⟩ : syracuseStep 4067911 = 6101867) B6101867
theorem B2142791 : Blo 1427533 2142791 := bstep (se 1 (by rfl) ⟨1607093, by rfl⟩ : syracuseStep 2142791 = 3214187) B3214187
theorem B3215951 : Blo 1427533 3215951 := bstep (se 1 (by rfl) ⟨2411963, by rfl⟩ : syracuseStep 3215951 = 4823927) B4823927
theorem B1806943 : Blo 1427533 1806943 := bstep (se 1 (by rfl) ⟨1355207, by rfl⟩ : syracuseStep 1806943 = 2710415) B2710415
theorem B16708193 : Blo 1427533 16708193 := bstep (se 2 (by rfl) ⟨6265572, by rfl⟩ : syracuseStep 16708193 = 12531145) B12531145
theorem B2142827 : Blo 1427533 2142827 := bstep (se 1 (by rfl) ⟨1607120, by rfl⟩ : syracuseStep 2142827 = 3214241) B3214241
theorem B2060921 : Blo 1427533 2060921 := bstep (se 2 (by rfl) ⟨772845, by rfl⟩ : syracuseStep 2060921 = 1545691) B1545691
theorem B156398201 : Blo 1427533 156398201 := bstep (se 2 (by rfl) ⟨58649325, by rfl⟩ : syracuseStep 156398201 = 117298651) B117298651
theorem B1716919 : Blo 1427533 1716919 := bstep (se 1 (by rfl) ⟨1287689, by rfl⟩ : syracuseStep 1716919 = 2575379) B2575379
theorem B12210911 : Blo 1427533 12210911 := bstep (se 1 (by rfl) ⟨9158183, by rfl⟩ : syracuseStep 12210911 = 18316367) B18316367
theorem B3216095 : Blo 1427533 3216095 := bstep (se 1 (by rfl) ⟨2412071, by rfl⟩ : syracuseStep 3216095 = 4824143) B4824143
theorem B14668573 : Blo 1427533 14668573 := bstep (se 3 (by rfl) ⟨2750357, by rfl⟩ : syracuseStep 14668573 = 5500715) B5500715
theorem B2143055 : Blo 1427533 2143055 := bstep (se 1 (by rfl) ⟨1607291, by rfl⟩ : syracuseStep 2143055 = 3214583) B3214583
theorem B3216347 : Blo 1427533 3216347 := bstep (se 1 (by rfl) ⟨2412260, by rfl⟩ : syracuseStep 3216347 = 4824521) B4824521
theorem B4576247 : Blo 1427533 4576247 := bstep (se 1 (by rfl) ⟨3432185, by rfl⟩ : syracuseStep 4576247 = 6864371) B6864371
theorem B4887695 : Blo 1427533 4887695 := bstep (se 1 (by rfl) ⟨3665771, by rfl⟩ : syracuseStep 4887695 = 7331543) B7331543
theorem B8139923 : Blo 1427533 8139923 := bstep (se 1 (by rfl) ⟨6104942, by rfl⟩ : syracuseStep 8139923 = 12209885) B12209885
theorem B2143451 : Blo 1427533 2143451 := bstep (se 1 (by rfl) ⟨1607588, by rfl⟩ : syracuseStep 2143451 = 3215177) B3215177
theorem B6100211 : Blo 1427533 6100211 := bstep (se 1 (by rfl) ⟨4575158, by rfl⟩ : syracuseStep 6100211 = 9150317) B9150317
theorem B7230707 : Blo 1427533 7230707 := bstep (se 1 (by rfl) ⟨5423030, by rfl⟩ : syracuseStep 7230707 = 10846061) B10846061
theorem B7329017 : Blo 1427533 7329017 := bstep (se 2 (by rfl) ⟨2748381, by rfl⟩ : syracuseStep 7329017 = 5496763) B5496763
theorem B3257639 : Blo 1427533 3257639 := bstep (se 1 (by rfl) ⟨2443229, by rfl⟩ : syracuseStep 3257639 = 4886459) B4886459
theorem B4068731 : Blo 1427533 4068731 := bstep (se 1 (by rfl) ⟨3051548, by rfl⟩ : syracuseStep 4068731 = 6103097) B6103097
theorem B2143625 : Blo 1427533 2143625 := bstep (se 2 (by rfl) ⟨803859, by rfl⟩ : syracuseStep 2143625 = 1607719) B1607719
theorem B6100363 : Blo 1427533 6100363 := bstep (se 1 (by rfl) ⟨4575272, by rfl⟩ : syracuseStep 6100363 = 9150545) B9150545
theorem B3618209 : Blo 1427533 3618209 := bstep (se 2 (by rfl) ⟨1356828, by rfl⟩ : syracuseStep 3618209 = 2713657) B2713657
theorem B12375499 : Blo 1427533 12375499 := bstep (se 1 (by rfl) ⟨9281624, by rfl⟩ : syracuseStep 12375499 = 18563249) B18563249
theorem B4822685 : Blo 1427533 4822685 := bstep (se 3 (by rfl) ⟨904253, by rfl⟩ : syracuseStep 4822685 = 1808507) B1808507
theorem B2143979 : Blo 1427533 2143979 := bstep (se 1 (by rfl) ⟨1607984, by rfl⟩ : syracuseStep 2143979 = 3215969) B3215969
theorem B1808183 : Blo 1427533 1808183 := bstep (se 1 (by rfl) ⟨1356137, by rfl⟩ : syracuseStep 1808183 = 2712275) B2712275
theorem B1832911 : Blo 1427533 1832911 := bstep (se 1 (by rfl) ⟨1374683, by rfl⟩ : syracuseStep 1832911 = 2749367) B2749367
theorem B1808335 : Blo 1427533 1808335 := bstep (se 1 (by rfl) ⟨1356251, by rfl⟩ : syracuseStep 1808335 = 2712503) B2712503
theorem B2144207 : Blo 1427533 2144207 := bstep (se 1 (by rfl) ⟨1608155, by rfl⟩ : syracuseStep 2144207 = 3216311) B3216311
theorem B4823225 : Blo 1427533 4823225 := bstep (se 2 (by rfl) ⟨1808709, by rfl⟩ : syracuseStep 4823225 = 3617419) B3617419
theorem B3430763 : Blo 1427533 3430763 := bstep (se 1 (by rfl) ⟨2573072, by rfl⟩ : syracuseStep 3430763 = 5146145) B5146145
theorem B13023919 : Blo 1427533 13023919 := bstep (se 1 (by rfl) ⟨9767939, by rfl⟩ : syracuseStep 13023919 = 19535879) B19535879
theorem B3259063 : Blo 1427533 3259063 := bstep (se 1 (by rfl) ⟨2444297, by rfl⟩ : syracuseStep 3259063 = 4888595) B4888595
theorem B12196763 : Blo 1427533 12196763 := bstep (se 1 (by rfl) ⟨9147572, by rfl⟩ : syracuseStep 12196763 = 18295145) B18295145
theorem B7232651 : Blo 1427533 7232651 := bstep (se 1 (by rfl) ⟨5424488, by rfl⟩ : syracuseStep 7232651 = 10848977) B10848977
theorem B6864139 : Blo 1427533 6864139 := bstep (se 1 (by rfl) ⟨5148104, by rfl⟩ : syracuseStep 6864139 = 10296209) B10296209
theorem B3431879 : Blo 1427533 3431879 := bstep (se 1 (by rfl) ⟨2573909, by rfl⟩ : syracuseStep 3431879 = 5147819) B5147819
theorem B2711227 : Blo 1427533 2711227 := bstep (se 1 (by rfl) ⟨2033420, by rfl⟩ : syracuseStep 2711227 = 4066841) B4066841
theorem B7724753 : Blo 1427533 7724753 := bstep (se 2 (by rfl) ⟨2896782, by rfl⟩ : syracuseStep 7724753 = 5793565) B5793565
theorem B15449849 : Blo 1427533 15449849 := bstep (se 2 (by rfl) ⟨5793693, by rfl⟩ : syracuseStep 15449849 = 11587387) B11587387
theorem B2711303 : Blo 1427533 2711303 := bstep (se 1 (by rfl) ⟨2033477, by rfl⟩ : syracuseStep 2711303 = 4066955) B4066955
theorem B5422895 : Blo 1427533 5422895 := bstep (se 1 (by rfl) ⟨4067171, by rfl⟩ : syracuseStep 5422895 = 8134343) B8134343
theorem B5422909 : Blo 1427533 5422909 := bstep (se 3 (by rfl) ⟨1016795, by rfl⟩ : syracuseStep 5422909 = 2033591) B2033591
theorem B10044001 : Blo 1427533 10044001 := bstep (se 2 (by rfl) ⟨3766500, by rfl⟩ : syracuseStep 10044001 = 7533001) B7533001
theorem B2409223 : Blo 1427533 2409223 := bstep (se 1 (by rfl) ⟨1806917, by rfl⟩ : syracuseStep 2409223 = 3613835) B3613835
theorem B5423881 : Blo 1427533 5423881 := bstep (se 2 (by rfl) ⟨2033955, by rfl⟩ : syracuseStep 5423881 = 4067911) B4067911
theorem B2409257 : Blo 1427533 2409257 := bstep (se 2 (by rfl) ⟨903471, by rfl⟩ : syracuseStep 2409257 = 1806943) B1806943
theorem B1606567 : Blo 1427533 1606567 := bstep (se 1 (by rfl) ⟨1204925, by rfl⟩ : syracuseStep 1606567 = 2409851) B2409851
theorem B3212243 : Blo 1427533 3212243 := bstep (se 1 (by rfl) ⟨2409182, by rfl⟩ : syracuseStep 3212243 = 4818365) B4818365
theorem B2409527 : Blo 1427533 2409527 := bstep (se 1 (by rfl) ⟨1807145, by rfl⟩ : syracuseStep 2409527 = 3614291) B3614291
theorem B3212495 : Blo 1427533 3212495 := bstep (se 1 (by rfl) ⟨2409371, by rfl⟩ : syracuseStep 3212495 = 4818743) B4818743
theorem B3212819 : Blo 1427533 3212819 := bstep (se 1 (by rfl) ⟨2409614, by rfl⟩ : syracuseStep 3212819 = 4819229) B4819229
theorem B2287175 : Blo 1427533 2287175 := bstep (se 1 (by rfl) ⟨1715381, by rfl⟩ : syracuseStep 2287175 = 3430763) B3430763
theorem B4818527 : Blo 1427533 4818527 := bstep (se 1 (by rfl) ⟨3613895, by rfl⟩ : syracuseStep 4818527 = 7227791) B7227791
theorem B5867119 : Blo 1427533 5867119 := bstep (se 1 (by rfl) ⟨4400339, by rfl⟩ : syracuseStep 5867119 = 8800679) B8800679
theorem B9152185 : Blo 1427533 9152185 := bstep (se 2 (by rfl) ⟨3432069, by rfl⟩ : syracuseStep 9152185 = 6864139) B6864139
theorem B2410303 : Blo 1427533 2410303 := bstep (se 1 (by rfl) ⟨1807727, by rfl⟩ : syracuseStep 2410303 = 3615455) B3615455
theorem B16271279 : Blo 1427533 16271279 := bstep (se 1 (by rfl) ⟨12203459, by rfl⟩ : syracuseStep 16271279 = 24406919) B24406919
theorem B16500665 : Blo 1427533 16500665 := bstep (se 2 (by rfl) ⟨6187749, by rfl⟩ : syracuseStep 16500665 = 12375499) B12375499
theorem B4065223 : Blo 1427533 4065223 := bstep (se 1 (by rfl) ⟨3048917, by rfl⟩ : syracuseStep 4065223 = 6097835) B6097835
theorem B36636623 : Blo 1427533 36636623 := bstep (se 1 (by rfl) ⟨27477467, by rfl⟩ : syracuseStep 36636623 = 54954935) B54954935
theorem B7235729 : Blo 1427533 7235729 := bstep (se 2 (by rfl) ⟨2713398, by rfl⟩ : syracuseStep 7235729 = 5426797) B5426797
theorem B1427611 : Blo 1427533 1427611 := bstep (se 1 (by rfl) ⟨1070708, by rfl⟩ : syracuseStep 1427611 = 2141417) B2141417
theorem B1427647 : Blo 1427533 1427647 := bstep (se 1 (by rfl) ⟨1070735, by rfl⟩ : syracuseStep 1427647 = 2141471) B2141471
theorem B3213503 : Blo 1427533 3213503 := bstep (se 1 (by rfl) ⟨2410127, by rfl⟩ : syracuseStep 3213503 = 4820255) B4820255
theorem B3049721 : Blo 1427533 3049721 := bstep (se 2 (by rfl) ⟨1143645, by rfl⟩ : syracuseStep 3049721 = 2287291) B2287291
theorem B3614969 : Blo 1427533 3614969 := bstep (se 2 (by rfl) ⟨1355613, by rfl⟩ : syracuseStep 3614969 = 2711227) B2711227
theorem B1427759 : Blo 1427533 1427759 := bstep (se 1 (by rfl) ⟨1070819, by rfl⟩ : syracuseStep 1427759 = 2141639) B2141639
theorem B2287919 : Blo 1427533 2287919 := bstep (se 1 (by rfl) ⟨1715939, by rfl⟩ : syracuseStep 2287919 = 3431879) B3431879
theorem B7727521 : Blo 1427533 7727521 := bstep (se 2 (by rfl) ⟨2897820, by rfl⟩ : syracuseStep 7727521 = 5795641) B5795641
theorem B9775525 : Blo 1427533 9775525 := bstep (se 4 (by rfl) ⟨916455, by rfl⟩ : syracuseStep 9775525 = 1832911) B1832911
theorem B10291657 : Blo 1427533 10291657 := bstep (se 2 (by rfl) ⟨3859371, by rfl⟩ : syracuseStep 10291657 = 7718743) B7718743
theorem B10299899 : Blo 1427533 10299899 := bstep (se 1 (by rfl) ⟨7724924, by rfl⟩ : syracuseStep 10299899 = 15449849) B15449849
theorem B1427995 : Blo 1427533 1427995 := bstep (se 1 (by rfl) ⟨1070996, by rfl⟩ : syracuseStep 1427995 = 2141993) B2141993
theorem B3050011 : Blo 1427533 3050011 := bstep (se 1 (by rfl) ⟨2287508, by rfl⟩ : syracuseStep 3050011 = 4575017) B4575017
theorem B1427999 : Blo 1427533 1427999 := bstep (se 1 (by rfl) ⟨1070999, by rfl⟩ : syracuseStep 1427999 = 2141999) B2141999
theorem B3615263 : Blo 1427533 3615263 := bstep (se 1 (by rfl) ⟨2711447, by rfl⟩ : syracuseStep 3615263 = 5422895) B5422895
theorem B2411039 : Blo 1427533 2411039 := bstep (se 1 (by rfl) ⟨1808279, by rfl⟩ : syracuseStep 2411039 = 3616559) B3616559
theorem B1608223 : Blo 1427533 1608223 := bstep (se 1 (by rfl) ⟨1206167, by rfl⟩ : syracuseStep 1608223 = 2412335) B2412335
theorem B2411113 : Blo 1427533 2411113 := bstep (se 2 (by rfl) ⟨904167, by rfl⟩ : syracuseStep 2411113 = 1808335) B1808335
theorem B6097751 : Blo 1427533 6097751 := bstep (se 1 (by rfl) ⟨4573313, by rfl⟩ : syracuseStep 6097751 = 9146627) B9146627
theorem B1428315 : Blo 1427533 1428315 := bstep (se 1 (by rfl) ⟨1071236, by rfl⟩ : syracuseStep 1428315 = 2142473) B2142473
theorem B1428383 : Blo 1427533 1428383 := bstep (se 1 (by rfl) ⟨1071287, by rfl⟩ : syracuseStep 1428383 = 2142575) B2142575
theorem B2411471 : Blo 1427533 2411471 := bstep (se 1 (by rfl) ⟨1808603, by rfl⟩ : syracuseStep 2411471 = 3617207) B3617207
theorem B4574171 : Blo 1427533 4574171 := bstep (se 1 (by rfl) ⟨3430628, by rfl⟩ : syracuseStep 4574171 = 6861257) B6861257
theorem B4819931 : Blo 1427533 4819931 := bstep (se 1 (by rfl) ⟨3614948, by rfl⟩ : syracuseStep 4819931 = 7229897) B7229897
theorem B8137691 : Blo 1427533 8137691 := bstep (se 1 (by rfl) ⟨6103268, by rfl⟩ : syracuseStep 8137691 = 12206537) B12206537
theorem B1428527 : Blo 1427533 1428527 := bstep (se 1 (by rfl) ⟨1071395, by rfl⟩ : syracuseStep 1428527 = 2142791) B2142791
theorem B1428551 : Blo 1427533 1428551 := bstep (se 1 (by rfl) ⟨1071413, by rfl⟩ : syracuseStep 1428551 = 2142827) B2142827
theorem B3214457 : Blo 1427533 3214457 := bstep (se 2 (by rfl) ⟨1205421, by rfl⟩ : syracuseStep 3214457 = 2410843) B2410843
theorem B1428703 : Blo 1427533 1428703 := bstep (se 1 (by rfl) ⟨1071527, by rfl⟩ : syracuseStep 1428703 = 2143055) B2143055
theorem B4820201 : Blo 1427533 4820201 := bstep (se 2 (by rfl) ⟨1807575, by rfl⟩ : syracuseStep 4820201 = 3615151) B3615151
theorem B2141519 : Blo 1427533 2141519 := bstep (se 1 (by rfl) ⟨1606139, by rfl⟩ : syracuseStep 2141519 = 3212279) B3212279
theorem B3050831 : Blo 1427533 3050831 := bstep (se 1 (by rfl) ⟨2288123, by rfl⟩ : syracuseStep 3050831 = 4576247) B4576247
theorem B6860141 : Blo 1427533 6860141 := bstep (se 3 (by rfl) ⟨1286276, by rfl⟩ : syracuseStep 6860141 = 2572553) B2572553
theorem B2141609 : Blo 1427533 2141609 := bstep (se 2 (by rfl) ⟨803103, by rfl⟩ : syracuseStep 2141609 = 1606207) B1606207
theorem B5426615 : Blo 1427533 5426615 := bstep (se 1 (by rfl) ⟨4069961, by rfl⟩ : syracuseStep 5426615 = 8139923) B8139923
theorem B1428967 : Blo 1427533 1428967 := bstep (se 1 (by rfl) ⟨1071725, by rfl⟩ : syracuseStep 1428967 = 2143451) B2143451
theorem B4066807 : Blo 1427533 4066807 := bstep (se 1 (by rfl) ⟨3050105, by rfl⟩ : syracuseStep 4066807 = 6100211) B6100211
theorem B4820471 : Blo 1427533 4820471 := bstep (se 1 (by rfl) ⟨3615353, by rfl⟩ : syracuseStep 4820471 = 7230707) B7230707
theorem B4886011 : Blo 1427533 4886011 := bstep (se 1 (by rfl) ⟨3664508, by rfl⟩ : syracuseStep 4886011 = 7329017) B7329017
theorem B2141759 : Blo 1427533 2141759 := bstep (se 1 (by rfl) ⟨1606319, by rfl⟩ : syracuseStep 2141759 = 3212639) B3212639
theorem B4345417 : Blo 1427533 4345417 := bstep (se 2 (by rfl) ⟨1629531, by rfl⟩ : syracuseStep 4345417 = 3259063) B3259063
theorem B1429083 : Blo 1427533 1429083 := bstep (se 1 (by rfl) ⟨1071812, by rfl⟩ : syracuseStep 1429083 = 2143625) B2143625
theorem B2412139 : Blo 1427533 2412139 := bstep (se 1 (by rfl) ⟨1809104, by rfl⟩ : syracuseStep 2412139 = 3618209) B3618209
theorem B10849949 : Blo 1427533 10849949 := bstep (se 3 (by rfl) ⟨2034365, by rfl⟩ : syracuseStep 10849949 = 4068731) B4068731
theorem B19558097 : Blo 1427533 19558097 := bstep (se 2 (by rfl) ⟨7334286, by rfl⟩ : syracuseStep 19558097 = 14668573) B14668573
theorem B3215123 : Blo 1427533 3215123 := bstep (se 1 (by rfl) ⟨2411342, by rfl⟩ : syracuseStep 3215123 = 4822685) B4822685
theorem B1716007 : Blo 1427533 1716007 := bstep (se 1 (by rfl) ⟨1287005, by rfl⟩ : syracuseStep 1716007 = 2574011) B2574011
theorem B2142023 : Blo 1427533 2142023 := bstep (se 1 (by rfl) ⟨1606517, by rfl⟩ : syracuseStep 2142023 = 3213035) B3213035
theorem B1429319 : Blo 1427533 1429319 := bstep (se 1 (by rfl) ⟨1071989, by rfl⟩ : syracuseStep 1429319 = 2143979) B2143979
theorem B2142107 : Blo 1427533 2142107 := bstep (se 1 (by rfl) ⟨1606580, by rfl⟩ : syracuseStep 2142107 = 3213161) B3213161
theorem B1429471 : Blo 1427533 1429471 := bstep (se 1 (by rfl) ⟨1072103, by rfl⟩ : syracuseStep 1429471 = 2144207) B2144207
theorem B10301489 : Blo 1427533 10301489 := bstep (se 2 (by rfl) ⟨3863058, by rfl⟩ : syracuseStep 10301489 = 7726117) B7726117
theorem B3215483 : Blo 1427533 3215483 := bstep (se 1 (by rfl) ⟨2411612, by rfl⟩ : syracuseStep 3215483 = 4823225) B4823225
theorem B3215753 : Blo 1427533 3215753 := bstep (se 2 (by rfl) ⟨1205907, by rfl⟩ : syracuseStep 3215753 = 2411815) B2411815
theorem B10301863 : Blo 1427533 10301863 := bstep (se 1 (by rfl) ⟨7726397, by rfl⟩ : syracuseStep 10301863 = 15452795) B15452795
theorem B2142671 : Blo 1427533 2142671 := bstep (se 1 (by rfl) ⟨1607003, by rfl⟩ : syracuseStep 2142671 = 3214007) B3214007
theorem B2142713 : Blo 1427533 2142713 := bstep (se 2 (by rfl) ⟨803517, by rfl⟩ : syracuseStep 2142713 = 1607035) B1607035
theorem B4821497 : Blo 1427533 4821497 := bstep (se 2 (by rfl) ⟨1808061, by rfl⟩ : syracuseStep 4821497 = 3616123) B3616123
theorem B2142815 : Blo 1427533 2142815 := bstep (se 1 (by rfl) ⟨1607111, by rfl⟩ : syracuseStep 2142815 = 3214223) B3214223
theorem B8131175 : Blo 1427533 8131175 := bstep (se 1 (by rfl) ⟨6098381, by rfl⟩ : syracuseStep 8131175 = 12196763) B12196763
theorem B15446699 : Blo 1427533 15446699 := bstep (se 1 (by rfl) ⟨11585024, by rfl⟩ : syracuseStep 15446699 = 23170049) B23170049
theorem B4821767 : Blo 1427533 4821767 := bstep (se 1 (by rfl) ⟨3616325, by rfl⟩ : syracuseStep 4821767 = 7232651) B7232651
theorem B3617561 : Blo 1427533 3617561 := bstep (se 2 (by rfl) ⟨1356585, by rfl⟩ : syracuseStep 3617561 = 2713171) B2713171
theorem B4821821 : Blo 1427533 4821821 := bstep (se 3 (by rfl) ⟨904091, by rfl⟩ : syracuseStep 4821821 = 1808183) B1808183
theorem B18297809 : Blo 1427533 18297809 := bstep (se 2 (by rfl) ⟨6861678, by rfl⟩ : syracuseStep 18297809 = 13723357) B13723357
theorem B2143295 : Blo 1427533 2143295 := bstep (se 1 (by rfl) ⟨1607471, by rfl⟩ : syracuseStep 2143295 = 3214943) B3214943
theorem B3617855 : Blo 1427533 3617855 := bstep (se 1 (by rfl) ⟨2713391, by rfl⟩ : syracuseStep 3617855 = 5426783) B5426783
theorem B7230545 : Blo 1427533 7230545 := bstep (se 2 (by rfl) ⟨2711454, by rfl⟩ : syracuseStep 7230545 = 5422909) B5422909
theorem B2143337 : Blo 1427533 2143337 := bstep (se 2 (by rfl) ⟨803751, by rfl⟩ : syracuseStep 2143337 = 1607503) B1607503
theorem B5149835 : Blo 1427533 5149835 := bstep (se 1 (by rfl) ⟨3862376, by rfl⟩ : syracuseStep 5149835 = 7724753) B7724753
theorem B1807535 : Blo 1427533 1807535 := bstep (se 1 (by rfl) ⟨1355651, by rfl⟩ : syracuseStep 1807535 = 2711303) B2711303
theorem B2143439 : Blo 1427533 2143439 := bstep (se 1 (by rfl) ⟨1607579, by rfl⟩ : syracuseStep 2143439 = 3215159) B3215159
theorem B3618067 : Blo 1427533 3618067 := bstep (se 1 (by rfl) ⟨2713550, by rfl⟩ : syracuseStep 3618067 = 5427101) B5427101
theorem B2143643 : Blo 1427533 2143643 := bstep (se 1 (by rfl) ⟨1607732, by rfl⟩ : syracuseStep 2143643 = 3215465) B3215465
theorem B10302875 : Blo 1427533 10302875 := bstep (se 1 (by rfl) ⟨7727156, by rfl⟩ : syracuseStep 10302875 = 15454313) B15454313
theorem B74225159 : Blo 1427533 74225159 := bstep (se 1 (by rfl) ⟨55668869, by rfl⟩ : syracuseStep 74225159 = 111337739) B111337739
theorem B44570155 : Blo 1427533 44570155 := bstep (se 1 (by rfl) ⟨33427616, by rfl⟩ : syracuseStep 44570155 = 66855233) B66855233
theorem B9156185 : Blo 1427533 9156185 := bstep (se 2 (by rfl) ⟨3433569, by rfl⟩ : syracuseStep 9156185 = 6867139) B6867139
theorem B2143865 : Blo 1427533 2143865 := bstep (se 2 (by rfl) ⟨803949, by rfl⟩ : syracuseStep 2143865 = 1607899) B1607899
theorem B31307447 : Blo 1427533 31307447 := bstep (se 1 (by rfl) ⟨23480585, by rfl⟩ : syracuseStep 31307447 = 46961171) B46961171
theorem B15447773 : Blo 1427533 15447773 := bstep (se 3 (by rfl) ⟨2896457, by rfl⟩ : syracuseStep 15447773 = 5792915) B5792915
theorem B2143967 : Blo 1427533 2143967 := bstep (se 1 (by rfl) ⟨1607975, by rfl⟩ : syracuseStep 2143967 = 3215951) B3215951
theorem B11138795 : Blo 1427533 11138795 := bstep (se 1 (by rfl) ⟨8354096, by rfl⟩ : syracuseStep 11138795 = 16708193) B16708193
theorem B34748149 : Blo 1427533 34748149 := bstep (se 5 (by rfl) ⟨1628819, by rfl⟩ : syracuseStep 34748149 = 3257639) B3257639
theorem B104265467 : Blo 1427533 104265467 := bstep (se 1 (by rfl) ⟨78199100, by rfl⟩ : syracuseStep 104265467 = 156398201) B156398201
theorem B4822847 : Blo 1427533 4822847 := bstep (se 1 (by rfl) ⟨3617135, by rfl⟩ : syracuseStep 4822847 = 7234271) B7234271
theorem B8140607 : Blo 1427533 8140607 := bstep (se 1 (by rfl) ⟨6105455, by rfl⟩ : syracuseStep 8140607 = 12210911) B12210911
theorem B2144063 : Blo 1427533 2144063 := bstep (se 1 (by rfl) ⟨1608047, by rfl⟩ : syracuseStep 2144063 = 3216095) B3216095
theorem B2144231 : Blo 1427533 2144231 := bstep (se 1 (by rfl) ⟨1608173, by rfl⟩ : syracuseStep 2144231 = 3216347) B3216347
theorem B4577273 : Blo 1427533 4577273 := bstep (se 2 (by rfl) ⟨1716477, by rfl⟩ : syracuseStep 4577273 = 3432955) B3432955
theorem B4069369 : Blo 1427533 4069369 := bstep (se 2 (by rfl) ⟨1526013, by rfl⟩ : syracuseStep 4069369 = 3052027) B3052027
theorem B2144249 : Blo 1427533 2144249 := bstep (se 2 (by rfl) ⟨804093, by rfl⟩ : syracuseStep 2144249 = 1608187) B1608187
theorem B8132633 : Blo 1427533 8132633 := bstep (se 2 (by rfl) ⟨3049737, by rfl⟩ : syracuseStep 8132633 = 6099475) B6099475
theorem B3258463 : Blo 1427533 3258463 := bstep (se 1 (by rfl) ⟨2443847, by rfl⟩ : syracuseStep 3258463 = 4887695) B4887695
theorem B17365225 : Blo 1427533 17365225 := bstep (se 2 (by rfl) ⟨6511959, by rfl⟩ : syracuseStep 17365225 = 13023919) B13023919
theorem B9156901 : Blo 1427533 9156901 := bstep (se 4 (by rfl) ⟨858459, by rfl⟩ : syracuseStep 9156901 = 1716919) B1716919
theorem B12204553 : Blo 1427533 12204553 := bstep (se 2 (by rfl) ⟨4576707, by rfl⟩ : syracuseStep 12204553 = 9153415) B9153415
theorem B98966123 : Blo 1427533 98966123 := bstep (se 1 (by rfl) ⟨74224592, by rfl⟩ : syracuseStep 98966123 = 148449185) B148449185
theorem B6101851 : Blo 1427533 6101851 := bstep (se 1 (by rfl) ⟨4576388, by rfl⟩ : syracuseStep 6101851 = 9152777) B9152777
theorem B5495789 : Blo 1427533 5495789 := bstep (se 3 (by rfl) ⟨1030460, by rfl⟩ : syracuseStep 5495789 = 2060921) B2060921
theorem B20585501 : Blo 1427533 20585501 := bstep (se 3 (by rfl) ⟨3859781, by rfl⟩ : syracuseStep 20585501 = 7719563) B7719563
theorem B32980097 : Blo 1427533 32980097 := bstep (se 2 (by rfl) ⟨12367536, by rfl⟩ : syracuseStep 32980097 = 24735073) B24735073
theorem B8133817 : Blo 1427533 8133817 := bstep (se 2 (by rfl) ⟨3050181, by rfl⟩ : syracuseStep 8133817 = 6100363) B6100363
theorem B4578553 : Blo 1427533 4578553 := bstep (se 2 (by rfl) ⟨1716957, by rfl⟩ : syracuseStep 4578553 = 3433915) B3433915
theorem B4824359 : Blo 1427533 4824359 := bstep (se 1 (by rfl) ⟨3618269, by rfl⟩ : syracuseStep 4824359 = 7236539) B7236539
theorem B23175557 : Blo 1427533 23175557 := bstep (se 4 (by rfl) ⟨2172708, by rfl⟩ : syracuseStep 23175557 = 4345417) B4345417
theorem B10297799 : Blo 1427533 10297799 := bstep (se 1 (by rfl) ⟨7723349, by rfl⟩ : syracuseStep 10297799 = 15446699) B15446699
theorem B1606171 : Blo 1427533 1606171 := bstep (se 1 (by rfl) ⟨1204628, by rfl⟩ : syracuseStep 1606171 = 2409257) B2409257
theorem B13034033 : Blo 1427533 13034033 := bstep (se 2 (by rfl) ⟨4887762, by rfl⟩ : syracuseStep 13034033 = 9775525) B9775525
theorem B13722209 : Blo 1427533 13722209 := bstep (se 2 (by rfl) ⟨5145828, by rfl⟩ : syracuseStep 13722209 = 10291657) B10291657
theorem B12198539 : Blo 1427533 12198539 := bstep (se 1 (by rfl) ⟨9148904, by rfl⟩ : syracuseStep 12198539 = 18297809) B18297809
theorem B1606351 : Blo 1427533 1606351 := bstep (se 1 (by rfl) ⟨1204763, by rfl⟩ : syracuseStep 1606351 = 2409527) B2409527
theorem B3433223 : Blo 1427533 3433223 := bstep (se 1 (by rfl) ⟨2574917, by rfl⟩ : syracuseStep 3433223 = 5149835) B5149835
theorem B8135549 : Blo 1427533 8135549 := bstep (se 3 (by rfl) ⟨1525415, by rfl⟩ : syracuseStep 8135549 = 3050831) B3050831
theorem B3212297 : Blo 1427533 3212297 := bstep (se 2 (by rfl) ⟨1204611, by rfl⟩ : syracuseStep 3212297 = 2409223) B2409223
theorem B6104123 : Blo 1427533 6104123 := bstep (se 1 (by rfl) ⟨4578092, by rfl⟩ : syracuseStep 6104123 = 9156185) B9156185
theorem B3212351 : Blo 1427533 3212351 := bstep (se 1 (by rfl) ⟨2409263, by rfl⟩ : syracuseStep 3212351 = 4818527) B4818527
theorem B8135801 : Blo 1427533 8135801 := bstep (se 2 (by rfl) ⟨3050925, by rfl⟩ : syracuseStep 8135801 = 6101851) B6101851
theorem B10298515 : Blo 1427533 10298515 := bstep (se 1 (by rfl) ⟨7723886, by rfl⟩ : syracuseStep 10298515 = 15447773) B15447773
theorem B69510311 : Blo 1427533 69510311 := bstep (se 1 (by rfl) ⟨52132733, by rfl⟩ : syracuseStep 69510311 = 104265467) B104265467
theorem B10847519 : Blo 1427533 10847519 := bstep (se 1 (by rfl) ⟨8135639, by rfl⟩ : syracuseStep 10847519 = 16271279) B16271279
theorem B2033147 : Blo 1427533 2033147 := bstep (se 1 (by rfl) ⟨1524860, by rfl⟩ : syracuseStep 2033147 = 3049721) B3049721
theorem B2409979 : Blo 1427533 2409979 := bstep (se 1 (by rfl) ⟨1807484, by rfl⟩ : syracuseStep 2409979 = 3614969) B3614969
theorem B1525279 : Blo 1427533 1525279 := bstep (se 1 (by rfl) ⟨1143959, by rfl⟩ : syracuseStep 1525279 = 2287919) B2287919
theorem B6104737 : Blo 1427533 6104737 := bstep (se 2 (by rfl) ⟨2289276, by rfl⟩ : syracuseStep 6104737 = 4578553) B4578553
theorem B2410175 : Blo 1427533 2410175 := bstep (se 1 (by rfl) ⟨1807631, by rfl⟩ : syracuseStep 2410175 = 3615263) B3615263
theorem B1607359 : Blo 1427533 1607359 := bstep (se 1 (by rfl) ⟨1205519, by rfl⟩ : syracuseStep 1607359 = 2411039) B2411039
theorem B4065167 : Blo 1427533 4065167 := bstep (se 1 (by rfl) ⟨3048875, by rfl⟩ : syracuseStep 4065167 = 6097751) B6097751
theorem B1607647 : Blo 1427533 1607647 := bstep (se 1 (by rfl) ⟨1205735, by rfl⟩ : syracuseStep 1607647 = 2411471) B2411471
theorem B3213287 : Blo 1427533 3213287 := bstep (se 1 (by rfl) ⟨2409965, by rfl⟩ : syracuseStep 3213287 = 4819931) B4819931
theorem B5425127 : Blo 1427533 5425127 := bstep (se 1 (by rfl) ⟨4068845, by rfl⟩ : syracuseStep 5425127 = 8137691) B8137691
theorem B3663859 : Blo 1427533 3663859 := bstep (se 1 (by rfl) ⟨2747894, by rfl⟩ : syracuseStep 3663859 = 5495789) B5495789
theorem B6514681 : Blo 1427533 6514681 := bstep (se 2 (by rfl) ⟨2443005, by rfl⟩ : syracuseStep 6514681 = 4886011) B4886011
theorem B13723667 : Blo 1427533 13723667 := bstep (se 1 (by rfl) ⟨10292750, by rfl⟩ : syracuseStep 13723667 = 20585501) B20585501
theorem B59426873 : Blo 1427533 59426873 := bstep (se 2 (by rfl) ⟨22285077, by rfl⟩ : syracuseStep 59426873 = 44570155) B44570155
theorem B3213467 : Blo 1427533 3213467 := bstep (se 1 (by rfl) ⟨2410100, by rfl⟩ : syracuseStep 3213467 = 4820201) B4820201
theorem B1427679 : Blo 1427533 1427679 := bstep (se 1 (by rfl) ⟨1070759, by rfl⟩ : syracuseStep 1427679 = 2141519) B2141519
theorem B4573427 : Blo 1427533 4573427 := bstep (se 1 (by rfl) ⟨3430070, by rfl⟩ : syracuseStep 4573427 = 6860141) B6860141
theorem B1427739 : Blo 1427533 1427739 := bstep (se 1 (by rfl) ⟨1070804, by rfl⟩ : syracuseStep 1427739 = 2141609) B2141609
theorem B3213647 : Blo 1427533 3213647 := bstep (se 1 (by rfl) ⟨2410235, by rfl⟩ : syracuseStep 3213647 = 4820471) B4820471
theorem B1427839 : Blo 1427533 1427839 := bstep (se 1 (by rfl) ⟨1070879, by rfl⟩ : syracuseStep 1427839 = 2141759) B2141759
theorem B2288009 : Blo 1427533 2288009 := bstep (se 2 (by rfl) ⟨858003, by rfl⟩ : syracuseStep 2288009 = 1716007) B1716007
theorem B3213737 : Blo 1427533 3213737 := bstep (se 2 (by rfl) ⟨1205151, by rfl⟩ : syracuseStep 3213737 = 2410303) B2410303
theorem B1428015 : Blo 1427533 1428015 := bstep (se 1 (by rfl) ⟨1071011, by rfl⟩ : syracuseStep 1428015 = 2142023) B2142023
theorem B1428071 : Blo 1427533 1428071 := bstep (se 1 (by rfl) ⟨1071053, by rfl⟩ : syracuseStep 1428071 = 2142107) B2142107
theorem B5425825 : Blo 1427533 5425825 := bstep (se 2 (by rfl) ⟨2034684, by rfl⟩ : syracuseStep 5425825 = 4069369) B4069369
theorem B6867659 : Blo 1427533 6867659 := bstep (se 1 (by rfl) ⟨5150744, by rfl⟩ : syracuseStep 6867659 = 10301489) B10301489
theorem B4344617 : Blo 1427533 4344617 := bstep (se 2 (by rfl) ⟨1629231, by rfl⟩ : syracuseStep 4344617 = 3258463) B3258463
theorem B1428447 : Blo 1427533 1428447 := bstep (se 1 (by rfl) ⟨1071335, by rfl⟩ : syracuseStep 1428447 = 2142671) B2142671
theorem B23153633 : Blo 1427533 23153633 := bstep (se 2 (by rfl) ⟨8682612, by rfl⟩ : syracuseStep 23153633 = 17365225) B17365225
theorem B1428475 : Blo 1427533 1428475 := bstep (se 1 (by rfl) ⟨1071356, by rfl⟩ : syracuseStep 1428475 = 2142713) B2142713
theorem B3214331 : Blo 1427533 3214331 := bstep (se 1 (by rfl) ⟨2410748, by rfl⟩ : syracuseStep 3214331 = 4821497) B4821497
theorem B12209201 : Blo 1427533 12209201 := bstep (se 2 (by rfl) ⟨4578450, by rfl⟩ : syracuseStep 12209201 = 9156901) B9156901
theorem B1428543 : Blo 1427533 1428543 := bstep (se 1 (by rfl) ⟨1071407, by rfl⟩ : syracuseStep 1428543 = 2142815) B2142815
theorem B4820093 : Blo 1427533 4820093 := bstep (se 3 (by rfl) ⟨903767, by rfl⟩ : syracuseStep 4820093 = 1807535) B1807535
theorem B3214511 : Blo 1427533 3214511 := bstep (se 1 (by rfl) ⟨2410883, by rfl⟩ : syracuseStep 3214511 = 4821767) B4821767
theorem B2411707 : Blo 1427533 2411707 := bstep (se 1 (by rfl) ⟨1808780, by rfl⟩ : syracuseStep 2411707 = 3617561) B3617561
theorem B3214547 : Blo 1427533 3214547 := bstep (se 1 (by rfl) ⟨2410910, by rfl⟩ : syracuseStep 3214547 = 4821821) B4821821
theorem B2141495 : Blo 1427533 2141495 := bstep (se 1 (by rfl) ⟨1606121, by rfl⟩ : syracuseStep 2141495 = 3212243) B3212243
theorem B16272737 : Blo 1427533 16272737 := bstep (se 2 (by rfl) ⟨6102276, by rfl⟩ : syracuseStep 16272737 = 12204553) B12204553
theorem B4066681 : Blo 1427533 4066681 := bstep (se 2 (by rfl) ⟨1525005, by rfl⟩ : syracuseStep 4066681 = 3050011) B3050011
theorem B1428863 : Blo 1427533 1428863 := bstep (se 1 (by rfl) ⟨1071647, by rfl⟩ : syracuseStep 1428863 = 2143295) B2143295
theorem B2411903 : Blo 1427533 2411903 := bstep (se 1 (by rfl) ⟨1808927, by rfl⟩ : syracuseStep 2411903 = 3617855) B3617855
theorem B4820363 : Blo 1427533 4820363 := bstep (se 1 (by rfl) ⟨3615272, by rfl⟩ : syracuseStep 4820363 = 7230545) B7230545
theorem B1428891 : Blo 1427533 1428891 := bstep (se 1 (by rfl) ⟨1071668, by rfl⟩ : syracuseStep 1428891 = 2143337) B2143337
theorem B2141663 : Blo 1427533 2141663 := bstep (se 1 (by rfl) ⟨1606247, by rfl⟩ : syracuseStep 2141663 = 3212495) B3212495
theorem B1428959 : Blo 1427533 1428959 := bstep (se 1 (by rfl) ⟨1071719, by rfl⟩ : syracuseStep 1428959 = 2143439) B2143439
theorem B3214817 : Blo 1427533 3214817 := bstep (se 2 (by rfl) ⟨1205556, by rfl⟩ : syracuseStep 3214817 = 2411113) B2411113
theorem B1429095 : Blo 1427533 1429095 := bstep (se 1 (by rfl) ⟨1071821, by rfl⟩ : syracuseStep 1429095 = 2143643) B2143643
theorem B6868583 : Blo 1427533 6868583 := bstep (se 1 (by rfl) ⟨5151437, by rfl⟩ : syracuseStep 6868583 = 10302875) B10302875
theorem B49483439 : Blo 1427533 49483439 := bstep (se 1 (by rfl) ⟨37112579, by rfl⟩ : syracuseStep 49483439 = 74225159) B74225159
theorem B2141879 : Blo 1427533 2141879 := bstep (se 1 (by rfl) ⟨1606409, by rfl⟩ : syracuseStep 2141879 = 3212819) B3212819
theorem B1429243 : Blo 1427533 1429243 := bstep (se 1 (by rfl) ⟨1071932, by rfl⟩ : syracuseStep 1429243 = 2143865) B2143865
theorem B1429311 : Blo 1427533 1429311 := bstep (se 1 (by rfl) ⟨1071983, by rfl⟩ : syracuseStep 1429311 = 2143967) B2143967
theorem B7425863 : Blo 1427533 7425863 := bstep (se 1 (by rfl) ⟨5569397, by rfl⟩ : syracuseStep 7425863 = 11138795) B11138795
theorem B3215231 : Blo 1427533 3215231 := bstep (se 1 (by rfl) ⟨2411423, by rfl⟩ : syracuseStep 3215231 = 4822847) B4822847
theorem B5427071 : Blo 1427533 5427071 := bstep (se 1 (by rfl) ⟨4070303, by rfl⟩ : syracuseStep 5427071 = 8140607) B8140607
theorem B1429375 : Blo 1427533 1429375 := bstep (se 1 (by rfl) ⟨1072031, by rfl⟩ : syracuseStep 1429375 = 2144063) B2144063
theorem B2142089 : Blo 1427533 2142089 := bstep (se 2 (by rfl) ⟨803283, by rfl⟩ : syracuseStep 2142089 = 1606567) B1606567
theorem B24424415 : Blo 1427533 24424415 := bstep (se 1 (by rfl) ⟨18318311, by rfl⟩ : syracuseStep 24424415 = 36636623) B36636623
theorem B1429487 : Blo 1427533 1429487 := bstep (se 1 (by rfl) ⟨1072115, by rfl⟩ : syracuseStep 1429487 = 2144231) B2144231
theorem B3051515 : Blo 1427533 3051515 := bstep (se 1 (by rfl) ⟨2288636, by rfl⟩ : syracuseStep 3051515 = 4577273) B4577273
theorem B1429499 : Blo 1427533 1429499 := bstep (se 1 (by rfl) ⟨1072124, by rfl⟩ : syracuseStep 1429499 = 2144249) B2144249
theorem B2142335 : Blo 1427533 2142335 := bstep (se 1 (by rfl) ⟨1606751, by rfl⟩ : syracuseStep 2142335 = 3213503) B3213503
theorem B6099133 : Blo 1427533 6099133 := bstep (se 3 (by rfl) ⟨1143587, by rfl⟩ : syracuseStep 6099133 = 2287175) B2287175
theorem B2142971 : Blo 1427533 2142971 := bstep (se 1 (by rfl) ⟨1607228, by rfl⟩ : syracuseStep 2142971 = 3214457) B3214457
theorem B3216185 : Blo 1427533 3216185 := bstep (se 2 (by rfl) ⟨1206069, by rfl⟩ : syracuseStep 3216185 = 2412139) B2412139
theorem B3216239 : Blo 1427533 3216239 := bstep (se 1 (by rfl) ⟨2412179, by rfl⟩ : syracuseStep 3216239 = 4824359) B4824359
theorem B12202913 : Blo 1427533 12202913 := bstep (se 2 (by rfl) ⟨4576092, by rfl⟩ : syracuseStep 12202913 = 9152185) B9152185
theorem B3617743 : Blo 1427533 3617743 := bstep (se 1 (by rfl) ⟨2713307, by rfl⟩ : syracuseStep 3617743 = 5426615) B5426615
theorem B46330865 : Blo 1427533 46330865 := bstep (se 2 (by rfl) ⟨17374074, by rfl⟩ : syracuseStep 46330865 = 34748149) B34748149
theorem B13038731 : Blo 1427533 13038731 := bstep (se 1 (by rfl) ⟨9779048, by rfl⟩ : syracuseStep 13038731 = 19558097) B19558097
theorem B2143415 : Blo 1427533 2143415 := bstep (se 1 (by rfl) ⟨1607561, by rfl⟩ : syracuseStep 2143415 = 3215123) B3215123
theorem B5420297 : Blo 1427533 5420297 := bstep (se 2 (by rfl) ⟨2032611, by rfl⟩ : syracuseStep 5420297 = 4065223) B4065223
theorem B2143655 : Blo 1427533 2143655 := bstep (se 1 (by rfl) ⟨1607741, by rfl⟩ : syracuseStep 2143655 = 3215483) B3215483
theorem B2143835 : Blo 1427533 2143835 := bstep (se 1 (by rfl) ⟨1607876, by rfl⟩ : syracuseStep 2143835 = 3215753) B3215753
theorem B5420783 : Blo 1427533 5420783 := bstep (se 1 (by rfl) ⟨4065587, by rfl⟩ : syracuseStep 5420783 = 8131175) B8131175
theorem B10303361 : Blo 1427533 10303361 := bstep (se 2 (by rfl) ⟨3863760, by rfl⟩ : syracuseStep 10303361 = 7727521) B7727521
theorem B13735817 : Blo 1427533 13735817 := bstep (se 2 (by rfl) ⟨5150931, by rfl⟩ : syracuseStep 13735817 = 10301863) B10301863
theorem B2144297 : Blo 1427533 2144297 := bstep (se 2 (by rfl) ⟨804111, by rfl⟩ : syracuseStep 2144297 = 1608223) B1608223
theorem B13392001 : Blo 1427533 13392001 := bstep (se 2 (by rfl) ⟨5022000, by rfl⟩ : syracuseStep 13392001 = 10044001) B10044001
theorem B7231841 : Blo 1427533 7231841 := bstep (se 2 (by rfl) ⟨2711940, by rfl⟩ : syracuseStep 7231841 = 5423881) B5423881
theorem B20871631 : Blo 1427533 20871631 := bstep (se 1 (by rfl) ⟨15653723, by rfl⟩ : syracuseStep 20871631 = 31307447) B31307447
theorem B11000443 : Blo 1427533 11000443 := bstep (se 1 (by rfl) ⟨8250332, by rfl⟩ : syracuseStep 11000443 = 16500665) B16500665
theorem B27466397 : Blo 1427533 27466397 := bstep (se 3 (by rfl) ⟨5149949, by rfl⟩ : syracuseStep 27466397 = 10299899) B10299899
theorem B5421755 : Blo 1427533 5421755 := bstep (se 1 (by rfl) ⟨4066316, by rfl⟩ : syracuseStep 5421755 = 8132633) B8132633
theorem B4823819 : Blo 1427533 4823819 := bstep (se 1 (by rfl) ⟨3617864, by rfl⟩ : syracuseStep 4823819 = 7235729) B7235729
theorem B10845089 : Blo 1427533 10845089 := bstep (se 2 (by rfl) ⟨4066908, by rfl⟩ : syracuseStep 10845089 = 8133817) B8133817
theorem B4824089 : Blo 1427533 4824089 := bstep (se 2 (by rfl) ⟨1809033, by rfl⟩ : syracuseStep 4824089 = 3618067) B3618067
theorem B65977415 : Blo 1427533 65977415 := bstep (se 1 (by rfl) ⟨49483061, by rfl⟩ : syracuseStep 65977415 = 98966123) B98966123
theorem B5422409 : Blo 1427533 5422409 := bstep (se 2 (by rfl) ⟨2033403, by rfl⟩ : syracuseStep 5422409 = 4066807) B4066807
theorem B21986731 : Blo 1427533 21986731 := bstep (se 1 (by rfl) ⟨16490048, by rfl⟩ : syracuseStep 21986731 = 32980097) B32980097
theorem B7822825 : Blo 1427533 7822825 := bstep (se 2 (by rfl) ⟨2933559, by rfl⟩ : syracuseStep 7822825 = 5867119) B5867119
theorem B7233299 : Blo 1427533 7233299 := bstep (se 1 (by rfl) ⟨5424974, by rfl⟩ : syracuseStep 7233299 = 10849949) B10849949
theorem B12197789 : Blo 1427533 12197789 := bstep (se 3 (by rfl) ⟨2287085, by rfl⟩ : syracuseStep 12197789 = 4574171) B4574171
theorem B15450371 : Blo 1427533 15450371 := bstep (se 1 (by rfl) ⟨11587778, by rfl⟩ : syracuseStep 15450371 = 23175557) B23175557
theorem B6865199 : Blo 1427533 6865199 := bstep (se 1 (by rfl) ⟨5148899, by rfl⟩ : syracuseStep 6865199 = 10297799) B10297799
theorem B5423699 : Blo 1427533 5423699 := bstep (se 1 (by rfl) ⟨4067774, by rfl⟩ : syracuseStep 5423699 = 8135549) B8135549
theorem B27828841 : Blo 1427533 27828841 := bstep (se 2 (by rfl) ⟨10435815, by rfl⟩ : syracuseStep 27828841 = 20871631) B20871631
theorem B8135275 : Blo 1427533 8135275 := bstep (se 1 (by rfl) ⟨6101456, by rfl⟩ : syracuseStep 8135275 = 12202913) B12202913
theorem B5423867 : Blo 1427533 5423867 := bstep (se 1 (by rfl) ⟨4067900, by rfl⟩ : syracuseStep 5423867 = 8135801) B8135801
theorem B8692487 : Blo 1427533 8692487 := bstep (se 1 (by rfl) ⟨6519365, by rfl⟩ : syracuseStep 8692487 = 13038731) B13038731
theorem B3613531 : Blo 1427533 3613531 := bstep (se 1 (by rfl) ⟨2710148, by rfl⟩ : syracuseStep 3613531 = 5420297) B5420297
theorem B7234433 : Blo 1427533 7234433 := bstep (se 2 (by rfl) ⟨2712912, by rfl⟩ : syracuseStep 7234433 = 5425825) B5425825
theorem B1606783 : Blo 1427533 1606783 := bstep (se 1 (by rfl) ⟨1205087, by rfl⟩ : syracuseStep 1606783 = 2410175) B2410175
theorem B3613855 : Blo 1427533 3613855 := bstep (se 1 (by rfl) ⟨2710391, by rfl⟩ : syracuseStep 3613855 = 5420783) B5420783
theorem B39617915 : Blo 1427533 39617915 := bstep (se 1 (by rfl) ⟨29713436, by rfl⟩ : syracuseStep 39617915 = 59426873) B59426873
theorem B13731353 : Blo 1427533 13731353 := bstep (se 2 (by rfl) ⟨5149257, by rfl⟩ : syracuseStep 13731353 = 10298515) B10298515
theorem B1525339 : Blo 1427533 1525339 := bstep (se 1 (by rfl) ⟨1144004, by rfl⟩ : syracuseStep 1525339 = 2288009) B2288009
theorem B18310931 : Blo 1427533 18310931 := bstep (se 1 (by rfl) ⟨13733198, by rfl⟩ : syracuseStep 18310931 = 27466397) B27466397
theorem B3614503 : Blo 1427533 3614503 := bstep (se 1 (by rfl) ⟨2710877, by rfl⟩ : syracuseStep 3614503 = 5421755) B5421755
theorem B15435755 : Blo 1427533 15435755 := bstep (se 1 (by rfl) ⟨11576816, by rfl⟩ : syracuseStep 15435755 = 23153633) B23153633
theorem B3213305 : Blo 1427533 3213305 := bstep (se 2 (by rfl) ⟨1204989, by rfl⟩ : syracuseStep 3213305 = 2409979) B2409979
theorem B2033705 : Blo 1427533 2033705 := bstep (se 2 (by rfl) ⟨762639, by rfl⟩ : syracuseStep 2033705 = 1525279) B1525279
theorem B43984943 : Blo 1427533 43984943 := bstep (se 1 (by rfl) ⟨32988707, by rfl⟩ : syracuseStep 43984943 = 65977415) B65977415
theorem B3213395 : Blo 1427533 3213395 := bstep (se 1 (by rfl) ⟨2410046, by rfl⟩ : syracuseStep 3213395 = 4820093) B4820093
theorem B1427663 : Blo 1427533 1427663 := bstep (se 1 (by rfl) ⟨1070747, by rfl⟩ : syracuseStep 1427663 = 2141495) B2141495
theorem B3614939 : Blo 1427533 3614939 := bstep (se 1 (by rfl) ⟨2711204, by rfl⟩ : syracuseStep 3614939 = 5422409) B5422409
theorem B10848491 : Blo 1427533 10848491 := bstep (se 1 (by rfl) ⟨8136368, by rfl⟩ : syracuseStep 10848491 = 16272737) B16272737
theorem B1607935 : Blo 1427533 1607935 := bstep (se 1 (by rfl) ⟨1205951, by rfl⟩ : syracuseStep 1607935 = 2411903) B2411903
theorem B3213575 : Blo 1427533 3213575 := bstep (se 1 (by rfl) ⟨2410181, by rfl⟩ : syracuseStep 3213575 = 4820363) B4820363
theorem B1427775 : Blo 1427533 1427775 := bstep (se 1 (by rfl) ⟨1070831, by rfl⟩ : syracuseStep 1427775 = 2141663) B2141663
theorem B1427919 : Blo 1427533 1427919 := bstep (se 1 (by rfl) ⟨1070939, by rfl⟩ : syracuseStep 1427919 = 2141879) B2141879
theorem B4950575 : Blo 1427533 4950575 := bstep (se 1 (by rfl) ⟨3712931, by rfl⟩ : syracuseStep 4950575 = 7425863) B7425863
theorem B1428059 : Blo 1427533 1428059 := bstep (se 1 (by rfl) ⟨1071044, by rfl⟩ : syracuseStep 1428059 = 2142089) B2142089
theorem B4885145 : Blo 1427533 4885145 := bstep (se 2 (by rfl) ⟨1831929, by rfl⟩ : syracuseStep 4885145 = 3663859) B3663859
theorem B8686241 : Blo 1427533 8686241 := bstep (se 2 (by rfl) ⟨3257340, by rfl⟩ : syracuseStep 8686241 = 6514681) B6514681
theorem B2034343 : Blo 1427533 2034343 := bstep (se 1 (by rfl) ⟨1525757, by rfl⟩ : syracuseStep 2034343 = 3051515) B3051515
theorem B1428223 : Blo 1427533 1428223 := bstep (se 1 (by rfl) ⟨1071167, by rfl⟩ : syracuseStep 1428223 = 2142335) B2142335
theorem B1428647 : Blo 1427533 1428647 := bstep (se 1 (by rfl) ⟨1071485, by rfl⟩ : syracuseStep 1428647 = 2142971) B2142971
theorem B30887243 : Blo 1427533 30887243 := bstep (se 1 (by rfl) ⟨23165432, by rfl⟩ : syracuseStep 30887243 = 46330865) B46330865
theorem B2141531 : Blo 1427533 2141531 := bstep (se 1 (by rfl) ⟨1606148, by rfl⟩ : syracuseStep 2141531 = 3212297) B3212297
theorem B2141561 : Blo 1427533 2141561 := bstep (se 2 (by rfl) ⟨803085, by rfl⟩ : syracuseStep 2141561 = 1606171) B1606171
theorem B2141567 : Blo 1427533 2141567 := bstep (se 1 (by rfl) ⟨1606175, by rfl⟩ : syracuseStep 2141567 = 3212351) B3212351
theorem B1428943 : Blo 1427533 1428943 := bstep (se 1 (by rfl) ⟨1071707, by rfl⟩ : syracuseStep 1428943 = 2143415) B2143415
theorem B14667257 : Blo 1427533 14667257 := bstep (se 2 (by rfl) ⟨5500221, by rfl⟩ : syracuseStep 14667257 = 11000443) B11000443
theorem B2141801 : Blo 1427533 2141801 := bstep (se 2 (by rfl) ⟨803175, by rfl⟩ : syracuseStep 2141801 = 1606351) B1606351
theorem B1429103 : Blo 1427533 1429103 := bstep (se 1 (by rfl) ⟨1071827, by rfl⟩ : syracuseStep 1429103 = 2143655) B2143655
theorem B1429223 : Blo 1427533 1429223 := bstep (se 1 (by rfl) ⟨1071917, by rfl⟩ : syracuseStep 1429223 = 2143835) B2143835
theorem B6868907 : Blo 1427533 6868907 := bstep (se 1 (by rfl) ⟨5151680, by rfl⟩ : syracuseStep 6868907 = 10303361) B10303361
theorem B2142191 : Blo 1427533 2142191 := bstep (se 1 (by rfl) ⟨1606643, by rfl⟩ : syracuseStep 2142191 = 3213287) B3213287
theorem B3616751 : Blo 1427533 3616751 := bstep (se 1 (by rfl) ⟨2712563, by rfl⟩ : syracuseStep 3616751 = 5425127) B5425127
theorem B1429531 : Blo 1427533 1429531 := bstep (se 1 (by rfl) ⟨1072148, by rfl⟩ : syracuseStep 1429531 = 2144297) B2144297
theorem B2142311 : Blo 1427533 2142311 := bstep (se 1 (by rfl) ⟨1606733, by rfl⟩ : syracuseStep 2142311 = 3213467) B3213467
theorem B2142431 : Blo 1427533 2142431 := bstep (se 1 (by rfl) ⟨1606823, by rfl⟩ : syracuseStep 2142431 = 3213647) B3213647
theorem B4821227 : Blo 1427533 4821227 := bstep (se 1 (by rfl) ⟨3615920, by rfl⟩ : syracuseStep 4821227 = 7231841) B7231841
theorem B3215609 : Blo 1427533 3215609 := bstep (se 2 (by rfl) ⟨1205853, by rfl⟩ : syracuseStep 3215609 = 2411707) B2411707
theorem B2142491 : Blo 1427533 2142491 := bstep (se 1 (by rfl) ⟨1606868, by rfl⟩ : syracuseStep 2142491 = 3213737) B3213737
theorem B3215879 : Blo 1427533 3215879 := bstep (se 1 (by rfl) ⟨2411909, by rfl⟩ : syracuseStep 3215879 = 4823819) B4823819
theorem B2896411 : Blo 1427533 2896411 := bstep (se 1 (by rfl) ⟨2172308, by rfl⟩ : syracuseStep 2896411 = 4344617) B4344617
theorem B29315641 : Blo 1427533 29315641 := bstep (se 2 (by rfl) ⟨10993365, by rfl⟩ : syracuseStep 29315641 = 21986731) B21986731
theorem B7230059 : Blo 1427533 7230059 := bstep (se 1 (by rfl) ⟨5422544, by rfl⟩ : syracuseStep 7230059 = 10845089) B10845089
theorem B2142887 : Blo 1427533 2142887 := bstep (se 1 (by rfl) ⟨1607165, by rfl⟩ : syracuseStep 2142887 = 3214331) B3214331
theorem B3216059 : Blo 1427533 3216059 := bstep (se 1 (by rfl) ⟨2412044, by rfl⟩ : syracuseStep 3216059 = 4824089) B4824089
theorem B9155261 : Blo 1427533 9155261 := bstep (se 3 (by rfl) ⟨1716611, by rfl⟩ : syracuseStep 9155261 = 3433223) B3433223
theorem B8139467 : Blo 1427533 8139467 := bstep (se 1 (by rfl) ⟨6104600, by rfl⟩ : syracuseStep 8139467 = 12209201) B12209201
theorem B2143007 : Blo 1427533 2143007 := bstep (se 1 (by rfl) ⟨1607255, by rfl⟩ : syracuseStep 2143007 = 3214511) B3214511
theorem B2143031 : Blo 1427533 2143031 := bstep (se 1 (by rfl) ⟨1607273, by rfl⟩ : syracuseStep 2143031 = 3214547) B3214547
theorem B8139649 : Blo 1427533 8139649 := bstep (se 2 (by rfl) ⟨3052368, by rfl⟩ : syracuseStep 8139649 = 6104737) B6104737
theorem B2143145 : Blo 1427533 2143145 := bstep (se 2 (by rfl) ⟨803679, by rfl⟩ : syracuseStep 2143145 = 1607359) B1607359
theorem B2143211 : Blo 1427533 2143211 := bstep (se 1 (by rfl) ⟨1607408, by rfl⟩ : syracuseStep 2143211 = 3214817) B3214817
theorem B4822199 : Blo 1427533 4822199 := bstep (se 1 (by rfl) ⟨3616649, by rfl⟩ : syracuseStep 4822199 = 7233299) B7233299
theorem B2143487 : Blo 1427533 2143487 := bstep (se 1 (by rfl) ⟨1607615, by rfl⟩ : syracuseStep 2143487 = 3215231) B3215231
theorem B3618047 : Blo 1427533 3618047 := bstep (se 1 (by rfl) ⟨2713535, by rfl⟩ : syracuseStep 3618047 = 5427071) B5427071
theorem B8131859 : Blo 1427533 8131859 := bstep (se 1 (by rfl) ⟨6098894, by rfl⟩ : syracuseStep 8131859 = 12197789) B12197789
theorem B2143529 : Blo 1427533 2143529 := bstep (se 2 (by rfl) ⟨803823, by rfl⟩ : syracuseStep 2143529 = 1607647) B1607647
theorem B16282943 : Blo 1427533 16282943 := bstep (se 1 (by rfl) ⟨12212207, by rfl⟩ : syracuseStep 16282943 = 24424415) B24424415
theorem B17856001 : Blo 1427533 17856001 := bstep (se 2 (by rfl) ⟨6696000, by rfl⟩ : syracuseStep 17856001 = 13392001) B13392001
theorem B8132177 : Blo 1427533 8132177 := bstep (se 2 (by rfl) ⟨3049566, by rfl⟩ : syracuseStep 8132177 = 6099133) B6099133
theorem B8689355 : Blo 1427533 8689355 := bstep (se 1 (by rfl) ⟨6517016, by rfl⟩ : syracuseStep 8689355 = 13034033) B13034033
theorem B9148139 : Blo 1427533 9148139 := bstep (se 1 (by rfl) ⟨6861104, by rfl⟩ : syracuseStep 9148139 = 13722209) B13722209
theorem B8132359 : Blo 1427533 8132359 := bstep (se 1 (by rfl) ⟨6099269, by rfl⟩ : syracuseStep 8132359 = 12198539) B12198539
theorem B2144123 : Blo 1427533 2144123 := bstep (se 1 (by rfl) ⟨1608092, by rfl⟩ : syracuseStep 2144123 = 3216185) B3216185
theorem B2144159 : Blo 1427533 2144159 := bstep (se 1 (by rfl) ⟨1608119, by rfl⟩ : syracuseStep 2144159 = 3216239) B3216239
theorem B12195805 : Blo 1427533 12195805 := bstep (se 3 (by rfl) ⟨2286713, by rfl⟩ : syracuseStep 12195805 = 4573427) B4573427
theorem B4069415 : Blo 1427533 4069415 := bstep (se 1 (by rfl) ⟨3052061, by rfl⟩ : syracuseStep 4069415 = 6104123) B6104123
theorem B46340207 : Blo 1427533 46340207 := bstep (se 1 (by rfl) ⟨34755155, by rfl⟩ : syracuseStep 46340207 = 69510311) B69510311
theorem B7231679 : Blo 1427533 7231679 := bstep (se 1 (by rfl) ⟨5423759, by rfl⟩ : syracuseStep 7231679 = 10847519) B10847519
theorem B9157211 : Blo 1427533 9157211 := bstep (se 1 (by rfl) ⟨6867908, by rfl⟩ : syracuseStep 9157211 = 13735817) B13735817
theorem B2710111 : Blo 1427533 2710111 := bstep (se 1 (by rfl) ⟨2032583, by rfl⟩ : syracuseStep 2710111 = 4065167) B4065167
theorem B4823657 : Blo 1427533 4823657 := bstep (se 2 (by rfl) ⟨1808871, by rfl⟩ : syracuseStep 4823657 = 3617743) B3617743
theorem B5421725 : Blo 1427533 5421725 := bstep (se 3 (by rfl) ⟨1016573, by rfl⟩ : syracuseStep 5421725 = 2033147) B2033147
theorem B9149111 : Blo 1427533 9149111 := bstep (se 1 (by rfl) ⟨6861833, by rfl⟩ : syracuseStep 9149111 = 13723667) B13723667
theorem B4578439 : Blo 1427533 4578439 := bstep (se 1 (by rfl) ⟨3433829, by rfl⟩ : syracuseStep 4578439 = 6867659) B6867659
theorem B5422241 : Blo 1427533 5422241 := bstep (se 2 (by rfl) ⟨2033340, by rfl⟩ : syracuseStep 5422241 = 4066681) B4066681
theorem B4579055 : Blo 1427533 4579055 := bstep (se 1 (by rfl) ⟨3434291, by rfl⟩ : syracuseStep 4579055 = 6868583) B6868583
theorem B32988959 : Blo 1427533 32988959 := bstep (se 1 (by rfl) ⟨24741719, by rfl⟩ : syracuseStep 32988959 = 49483439) B49483439
theorem B41721733 : Blo 1427533 41721733 := bstep (se 4 (by rfl) ⟨3911412, by rfl⟩ : syracuseStep 41721733 = 7822825) B7822825
theorem B5423213 : Blo 1427533 5423213 := bstep (se 3 (by rfl) ⟨1016852, by rfl⟩ : syracuseStep 5423213 = 2033705) B2033705
theorem B6103507 : Blo 1427533 6103507 := bstep (se 1 (by rfl) ⟨4577630, by rfl⟩ : syracuseStep 6103507 = 9155261) B9155261
theorem B3613481 : Blo 1427533 3613481 := bstep (se 2 (by rfl) ⟨1355055, by rfl⟩ : syracuseStep 3613481 = 2710111) B2710111
theorem B10847033 : Blo 1427533 10847033 := bstep (se 2 (by rfl) ⟨4067637, by rfl⟩ : syracuseStep 10847033 = 8135275) B8135275
theorem B10855295 : Blo 1427533 10855295 := bstep (se 1 (by rfl) ⟨8141471, by rfl⟩ : syracuseStep 10855295 = 16282943) B16282943
theorem B2712457 : Blo 1427533 2712457 := bstep (se 2 (by rfl) ⟨1017171, by rfl⟩ : syracuseStep 2712457 = 2034343) B2034343
theorem B4818041 : Blo 1427533 4818041 := bstep (se 2 (by rfl) ⟨1806765, by rfl⟩ : syracuseStep 4818041 = 3613531) B3613531
theorem B5792903 : Blo 1427533 5792903 := bstep (se 1 (by rfl) ⟨4344677, by rfl⟩ : syracuseStep 5792903 = 8689355) B8689355
theorem B12207287 : Blo 1427533 12207287 := bstep (se 1 (by rfl) ⟨9155465, by rfl⟩ : syracuseStep 12207287 = 18310931) B18310931
theorem B10290503 : Blo 1427533 10290503 := bstep (se 1 (by rfl) ⟨7717877, by rfl⟩ : syracuseStep 10290503 = 15435755) B15435755
theorem B2712943 : Blo 1427533 2712943 := bstep (se 1 (by rfl) ⟨2034707, by rfl⟩ : syracuseStep 2712943 = 4069415) B4069415
theorem B30893471 : Blo 1427533 30893471 := bstep (se 1 (by rfl) ⟨23170103, by rfl⟩ : syracuseStep 30893471 = 46340207) B46340207
theorem B2409959 : Blo 1427533 2409959 := bstep (se 1 (by rfl) ⟨1807469, by rfl⟩ : syracuseStep 2409959 = 3614939) B3614939
theorem B6104585 : Blo 1427533 6104585 := bstep (se 2 (by rfl) ⟨2289219, by rfl⟩ : syracuseStep 6104585 = 4578439) B4578439
theorem B4818473 : Blo 1427533 4818473 := bstep (se 2 (by rfl) ⟨1806927, by rfl⟩ : syracuseStep 4818473 = 3613855) B3613855
theorem B6104807 : Blo 1427533 6104807 := bstep (se 1 (by rfl) ⟨4578605, by rfl⟩ : syracuseStep 6104807 = 9157211) B9157211
theorem B3614483 : Blo 1427533 3614483 := bstep (se 1 (by rfl) ⟨2710862, by rfl⟩ : syracuseStep 3614483 = 5421725) B5421725
theorem B23808001 : Blo 1427533 23808001 := bstep (se 2 (by rfl) ⟨8928000, by rfl⟩ : syracuseStep 23808001 = 17856001) B17856001
theorem B3614827 : Blo 1427533 3614827 := bstep (se 1 (by rfl) ⟨2711120, by rfl⟩ : syracuseStep 3614827 = 5422241) B5422241
theorem B2033785 : Blo 1427533 2033785 := bstep (se 2 (by rfl) ⟨762669, by rfl⟩ : syracuseStep 2033785 = 1525339) B1525339
theorem B1427687 : Blo 1427533 1427687 := bstep (se 1 (by rfl) ⟨1070765, by rfl⟩ : syracuseStep 1427687 = 2141531) B2141531
theorem B1427707 : Blo 1427533 1427707 := bstep (se 1 (by rfl) ⟨1070780, by rfl⟩ : syracuseStep 1427707 = 2141561) B2141561
theorem B1427711 : Blo 1427533 1427711 := bstep (se 1 (by rfl) ⟨1070783, by rfl⟩ : syracuseStep 1427711 = 2141567) B2141567
theorem B4819337 : Blo 1427533 4819337 := bstep (se 2 (by rfl) ⟨1807251, by rfl⟩ : syracuseStep 4819337 = 3614503) B3614503
theorem B1427867 : Blo 1427533 1427867 := bstep (se 1 (by rfl) ⟨1070900, by rfl⟩ : syracuseStep 1427867 = 2141801) B2141801
theorem B1428127 : Blo 1427533 1428127 := bstep (se 1 (by rfl) ⟨1071095, by rfl⟩ : syracuseStep 1428127 = 2142191) B2142191
theorem B2411167 : Blo 1427533 2411167 := bstep (se 1 (by rfl) ⟨1808375, by rfl⟩ : syracuseStep 2411167 = 3616751) B3616751
theorem B1428207 : Blo 1427533 1428207 := bstep (se 1 (by rfl) ⟨1071155, by rfl⟩ : syracuseStep 1428207 = 2142311) B2142311
theorem B1428287 : Blo 1427533 1428287 := bstep (se 1 (by rfl) ⟨1071215, by rfl⟩ : syracuseStep 1428287 = 2142431) B2142431
theorem B3214151 : Blo 1427533 3214151 := bstep (se 1 (by rfl) ⟨2410613, by rfl⟩ : syracuseStep 3214151 = 4821227) B4821227
theorem B10300247 : Blo 1427533 10300247 := bstep (se 1 (by rfl) ⟨7725185, by rfl⟩ : syracuseStep 10300247 = 15450371) B15450371
theorem B1428327 : Blo 1427533 1428327 := bstep (se 1 (by rfl) ⟨1071245, by rfl⟩ : syracuseStep 1428327 = 2142491) B2142491
theorem B3615799 : Blo 1427533 3615799 := bstep (se 1 (by rfl) ⟨2711849, by rfl⟩ : syracuseStep 3615799 = 5423699) B5423699
theorem B4820039 : Blo 1427533 4820039 := bstep (se 1 (by rfl) ⟨3615029, by rfl⟩ : syracuseStep 4820039 = 7230059) B7230059
theorem B1428591 : Blo 1427533 1428591 := bstep (se 1 (by rfl) ⟨1071443, by rfl⟩ : syracuseStep 1428591 = 2142887) B2142887
theorem B5426311 : Blo 1427533 5426311 := bstep (se 1 (by rfl) ⟨4069733, by rfl⟩ : syracuseStep 5426311 = 8139467) B8139467
theorem B3615911 : Blo 1427533 3615911 := bstep (se 1 (by rfl) ⟨2711933, by rfl⟩ : syracuseStep 3615911 = 5423867) B5423867
theorem B5794991 : Blo 1427533 5794991 := bstep (se 1 (by rfl) ⟨4346243, by rfl⟩ : syracuseStep 5794991 = 8692487) B8692487
theorem B1428671 : Blo 1427533 1428671 := bstep (se 1 (by rfl) ⟨1071503, by rfl⟩ : syracuseStep 1428671 = 2143007) B2143007
theorem B1428687 : Blo 1427533 1428687 := bstep (se 1 (by rfl) ⟨1071515, by rfl⟩ : syracuseStep 1428687 = 2143031) B2143031
theorem B1428763 : Blo 1427533 1428763 := bstep (se 1 (by rfl) ⟨1071572, by rfl⟩ : syracuseStep 1428763 = 2143145) B2143145
theorem B1428807 : Blo 1427533 1428807 := bstep (se 1 (by rfl) ⟨1071605, by rfl⟩ : syracuseStep 1428807 = 2143211) B2143211
theorem B3861881 : Blo 1427533 3861881 := bstep (se 2 (by rfl) ⟨1448205, by rfl⟩ : syracuseStep 3861881 = 2896411) B2896411
theorem B39087521 : Blo 1427533 39087521 := bstep (se 2 (by rfl) ⟨14657820, by rfl⟩ : syracuseStep 39087521 = 29315641) B29315641
theorem B3214799 : Blo 1427533 3214799 := bstep (se 1 (by rfl) ⟨2411099, by rfl⟩ : syracuseStep 3214799 = 4822199) B4822199
theorem B37105121 : Blo 1427533 37105121 := bstep (se 2 (by rfl) ⟨13914420, by rfl⟩ : syracuseStep 37105121 = 27828841) B27828841
theorem B1428991 : Blo 1427533 1428991 := bstep (se 1 (by rfl) ⟨1071743, by rfl⟩ : syracuseStep 1428991 = 2143487) B2143487
theorem B2412031 : Blo 1427533 2412031 := bstep (se 1 (by rfl) ⟨1809023, by rfl⟩ : syracuseStep 2412031 = 3618047) B3618047
theorem B1429019 : Blo 1427533 1429019 := bstep (se 1 (by rfl) ⟨1071764, by rfl⟩ : syracuseStep 1429019 = 2143529) B2143529
theorem B9154235 : Blo 1427533 9154235 := bstep (se 1 (by rfl) ⟨6865676, by rfl⟩ : syracuseStep 9154235 = 13731353) B13731353
theorem B6098759 : Blo 1427533 6098759 := bstep (se 1 (by rfl) ⟨4574069, by rfl⟩ : syracuseStep 6098759 = 9148139) B9148139
theorem B1429415 : Blo 1427533 1429415 := bstep (se 1 (by rfl) ⟨1072061, by rfl⟩ : syracuseStep 1429415 = 2144123) B2144123
theorem B1429439 : Blo 1427533 1429439 := bstep (se 1 (by rfl) ⟨1072079, by rfl⟩ : syracuseStep 1429439 = 2144159) B2144159
theorem B39112685 : Blo 1427533 39112685 := bstep (se 3 (by rfl) ⟨7333628, by rfl⟩ : syracuseStep 39112685 = 14667257) B14667257
theorem B2142203 : Blo 1427533 2142203 := bstep (se 1 (by rfl) ⟨1606652, by rfl⟩ : syracuseStep 2142203 = 3213305) B3213305
theorem B29323295 : Blo 1427533 29323295 := bstep (se 1 (by rfl) ⟨21992471, by rfl⟩ : syracuseStep 29323295 = 43984943) B43984943
theorem B2142263 : Blo 1427533 2142263 := bstep (se 1 (by rfl) ⟨1606697, by rfl⟩ : syracuseStep 2142263 = 3213395) B3213395
theorem B4821119 : Blo 1427533 4821119 := bstep (se 1 (by rfl) ⟨3615839, by rfl⟩ : syracuseStep 4821119 = 7231679) B7231679
theorem B2142377 : Blo 1427533 2142377 := bstep (se 2 (by rfl) ⟨803391, by rfl⟩ : syracuseStep 2142377 = 1606783) B1606783
theorem B2142383 : Blo 1427533 2142383 := bstep (se 1 (by rfl) ⟨1606787, by rfl⟩ : syracuseStep 2142383 = 3213575) B3213575
theorem B3215771 : Blo 1427533 3215771 := bstep (se 1 (by rfl) ⟨2411828, by rfl⟩ : syracuseStep 3215771 = 4823657) B4823657
theorem B3256763 : Blo 1427533 3256763 := bstep (se 1 (by rfl) ⟨2442572, by rfl⟩ : syracuseStep 3256763 = 4885145) B4885145
theorem B6099407 : Blo 1427533 6099407 := bstep (se 1 (by rfl) ⟨4574555, by rfl⟩ : syracuseStep 6099407 = 9149111) B9149111
theorem B20591495 : Blo 1427533 20591495 := bstep (se 1 (by rfl) ⟨15443621, by rfl⟩ : syracuseStep 20591495 = 30887243) B30887243
theorem B10843145 : Blo 1427533 10843145 := bstep (se 2 (by rfl) ⟨4066179, by rfl⟩ : syracuseStep 10843145 = 8132359) B8132359
theorem B3052703 : Blo 1427533 3052703 := bstep (se 1 (by rfl) ⟨2289527, by rfl⟩ : syracuseStep 3052703 = 4579055) B4579055
theorem B55628977 : Blo 1427533 55628977 := bstep (se 2 (by rfl) ⟨20860866, by rfl⟩ : syracuseStep 55628977 = 41721733) B41721733
theorem B21992639 : Blo 1427533 21992639 := bstep (se 1 (by rfl) ⟨16494479, by rfl⟩ : syracuseStep 21992639 = 32988959) B32988959
theorem B2143739 : Blo 1427533 2143739 := bstep (se 1 (by rfl) ⟨1607804, by rfl⟩ : syracuseStep 2143739 = 3215609) B3215609
theorem B4576799 : Blo 1427533 4576799 := bstep (se 1 (by rfl) ⟨3432599, by rfl⟩ : syracuseStep 4576799 = 6865199) B6865199
theorem B2143913 : Blo 1427533 2143913 := bstep (se 2 (by rfl) ⟨803967, by rfl⟩ : syracuseStep 2143913 = 1607935) B1607935
theorem B2143919 : Blo 1427533 2143919 := bstep (se 1 (by rfl) ⟨1607939, by rfl⟩ : syracuseStep 2143919 = 3215879) B3215879
theorem B2144039 : Blo 1427533 2144039 := bstep (se 1 (by rfl) ⟨1608029, by rfl⟩ : syracuseStep 2144039 = 3216059) B3216059
theorem B4822955 : Blo 1427533 4822955 := bstep (se 1 (by rfl) ⟨3617216, by rfl⟩ : syracuseStep 4822955 = 7234433) B7234433
theorem B5421239 : Blo 1427533 5421239 := bstep (se 1 (by rfl) ⟨4065929, by rfl⟩ : syracuseStep 5421239 = 8131859) B8131859
theorem B5421451 : Blo 1427533 5421451 := bstep (se 1 (by rfl) ⟨4066088, by rfl⟩ : syracuseStep 5421451 = 8132177) B8132177
theorem B10852865 : Blo 1427533 10852865 := bstep (se 2 (by rfl) ⟨4069824, by rfl⟩ : syracuseStep 10852865 = 8139649) B8139649
theorem B422591093 : Blo 1427533 422591093 := bstep (se 5 (by rfl) ⟨19808957, by rfl⟩ : syracuseStep 422591093 = 39617915) B39617915
theorem B7232327 : Blo 1427533 7232327 := bstep (se 1 (by rfl) ⟨5424245, by rfl⟩ : syracuseStep 7232327 = 10848491) B10848491
theorem B3300383 : Blo 1427533 3300383 := bstep (se 1 (by rfl) ⟨2475287, by rfl⟩ : syracuseStep 3300383 = 4950575) B4950575
theorem B5790827 : Blo 1427533 5790827 := bstep (se 1 (by rfl) ⟨4343120, by rfl⟩ : syracuseStep 5790827 = 8686241) B8686241
theorem B4579271 : Blo 1427533 4579271 := bstep (se 1 (by rfl) ⟨3434453, by rfl⟩ : syracuseStep 4579271 = 6868907) B6868907
theorem B16261073 : Blo 1427533 16261073 := bstep (se 2 (by rfl) ⟨6097902, by rfl⟩ : syracuseStep 16261073 = 12195805) B12195805
theorem B31744001 : Blo 1427533 31744001 := bstep (se 2 (by rfl) ⟨11904000, by rfl⟩ : syracuseStep 31744001 = 23808001) B23808001
theorem B2711713 : Blo 1427533 2711713 := bstep (se 2 (by rfl) ⟨1016892, by rfl⟩ : syracuseStep 2711713 = 2033785) B2033785
theorem B58647037 : Blo 1427533 58647037 := bstep (se 3 (by rfl) ⟨10996319, by rfl⟩ : syracuseStep 58647037 = 21992639) B21992639
theorem B2408987 : Blo 1427533 2408987 := bstep (se 1 (by rfl) ⟨1806740, by rfl⟩ : syracuseStep 2408987 = 3613481) B3613481
theorem B3212027 : Blo 1427533 3212027 := bstep (se 1 (by rfl) ⟨2409020, by rfl⟩ : syracuseStep 3212027 = 4818041) B4818041
theorem B20595647 : Blo 1427533 20595647 := bstep (se 1 (by rfl) ⟨15446735, by rfl⟩ : syracuseStep 20595647 = 30893471) B30893471
theorem B1606639 : Blo 1427533 1606639 := bstep (se 1 (by rfl) ⟨1204979, by rfl⟩ : syracuseStep 1606639 = 2409959) B2409959
theorem B3212315 : Blo 1427533 3212315 := bstep (se 1 (by rfl) ⟨2409236, by rfl⟩ : syracuseStep 3212315 = 4818473) B4818473
theorem B8684701 : Blo 1427533 8684701 := bstep (se 3 (by rfl) ⟨1628381, by rfl⟩ : syracuseStep 8684701 = 3256763) B3256763
theorem B2409655 : Blo 1427533 2409655 := bstep (se 1 (by rfl) ⟨1807241, by rfl⟩ : syracuseStep 2409655 = 3614483) B3614483
theorem B3614159 : Blo 1427533 3614159 := bstep (se 1 (by rfl) ⟨2710619, by rfl⟩ : syracuseStep 3614159 = 5421239) B5421239
theorem B7235081 : Blo 1427533 7235081 := bstep (se 2 (by rfl) ⟨2713155, by rfl⟩ : syracuseStep 7235081 = 5426311) B5426311
theorem B74171969 : Blo 1427533 74171969 := bstep (se 2 (by rfl) ⟨27814488, by rfl⟩ : syracuseStep 74171969 = 55628977) B55628977
theorem B3212891 : Blo 1427533 3212891 := bstep (se 1 (by rfl) ⟨2409668, by rfl⟩ : syracuseStep 3212891 = 4819337) B4819337
theorem B7235243 : Blo 1427533 7235243 := bstep (se 1 (by rfl) ⟨5426432, by rfl⟩ : syracuseStep 7235243 = 10852865) B10852865
theorem B6866831 : Blo 1427533 6866831 := bstep (se 1 (by rfl) ⟨5150123, by rfl⟩ : syracuseStep 6866831 = 10300247) B10300247
theorem B3213359 : Blo 1427533 3213359 := bstep (se 1 (by rfl) ⟨2410019, by rfl⟩ : syracuseStep 3213359 = 4820039) B4820039
theorem B3860551 : Blo 1427533 3860551 := bstep (se 1 (by rfl) ⟨2895413, by rfl⟩ : syracuseStep 3860551 = 5790827) B5790827
theorem B2410607 : Blo 1427533 2410607 := bstep (se 1 (by rfl) ⟨1807955, by rfl⟩ : syracuseStep 2410607 = 3615911) B3615911
theorem B2574587 : Blo 1427533 2574587 := bstep (se 1 (by rfl) ⟨1930940, by rfl⟩ : syracuseStep 2574587 = 3861881) B3861881
theorem B4065839 : Blo 1427533 4065839 := bstep (se 1 (by rfl) ⟨3049379, by rfl⟩ : syracuseStep 4065839 = 6098759) B6098759
theorem B10840715 : Blo 1427533 10840715 := bstep (se 1 (by rfl) ⟨8130536, by rfl⟩ : syracuseStep 10840715 = 16261073) B16261073
theorem B1428135 : Blo 1427533 1428135 := bstep (se 1 (by rfl) ⟨1071101, by rfl⟩ : syracuseStep 1428135 = 2142203) B2142203
theorem B19548863 : Blo 1427533 19548863 := bstep (se 1 (by rfl) ⟨14661647, by rfl⟩ : syracuseStep 19548863 = 29323295) B29323295
theorem B1428175 : Blo 1427533 1428175 := bstep (se 1 (by rfl) ⟨1071131, by rfl⟩ : syracuseStep 1428175 = 2142263) B2142263
theorem B3615475 : Blo 1427533 3615475 := bstep (se 1 (by rfl) ⟨2711606, by rfl⟩ : syracuseStep 3615475 = 5423213) B5423213
theorem B3214079 : Blo 1427533 3214079 := bstep (se 1 (by rfl) ⟨2410559, by rfl⟩ : syracuseStep 3214079 = 4821119) B4821119
theorem B1428251 : Blo 1427533 1428251 := bstep (se 1 (by rfl) ⟨1071188, by rfl⟩ : syracuseStep 1428251 = 2142377) B2142377
theorem B1428255 : Blo 1427533 1428255 := bstep (se 1 (by rfl) ⟨1071191, by rfl⟩ : syracuseStep 1428255 = 2142383) B2142383
theorem B4819769 : Blo 1427533 4819769 := bstep (se 2 (by rfl) ⟨1807413, by rfl⟩ : syracuseStep 4819769 = 3614827) B3614827
theorem B4066271 : Blo 1427533 4066271 := bstep (se 1 (by rfl) ⟨3049703, by rfl⟩ : syracuseStep 4066271 = 6099407) B6099407
theorem B7228601 : Blo 1427533 7228601 := bstep (se 2 (by rfl) ⟨2710725, by rfl⟩ : syracuseStep 7228601 = 5421451) B5421451
theorem B7236863 : Blo 1427533 7236863 := bstep (se 1 (by rfl) ⟨5427647, by rfl⟩ : syracuseStep 7236863 = 10855295) B10855295
theorem B8138009 : Blo 1427533 8138009 := bstep (se 2 (by rfl) ⟨3051753, by rfl⟩ : syracuseStep 8138009 = 6103507) B6103507
theorem B7228763 : Blo 1427533 7228763 := bstep (se 1 (by rfl) ⟨5421572, by rfl⟩ : syracuseStep 7228763 = 10843145) B10843145
theorem B3861935 : Blo 1427533 3861935 := bstep (se 1 (by rfl) ⟨2896451, by rfl⟩ : syracuseStep 3861935 = 5792903) B5792903
theorem B2035135 : Blo 1427533 2035135 := bstep (se 1 (by rfl) ⟨1526351, by rfl⟩ : syracuseStep 2035135 = 3052703) B3052703
theorem B8138191 : Blo 1427533 8138191 := bstep (se 1 (by rfl) ⟨6103643, by rfl⟩ : syracuseStep 8138191 = 12207287) B12207287
theorem B3214889 : Blo 1427533 3214889 := bstep (se 2 (by rfl) ⟨1205583, by rfl⟩ : syracuseStep 3214889 = 2411167) B2411167
theorem B6860335 : Blo 1427533 6860335 := bstep (se 1 (by rfl) ⟨5145251, by rfl⟩ : syracuseStep 6860335 = 10290503) B10290503
theorem B1429159 : Blo 1427533 1429159 := bstep (se 1 (by rfl) ⟨1071869, by rfl⟩ : syracuseStep 1429159 = 2143739) B2143739
theorem B3051199 : Blo 1427533 3051199 := bstep (se 1 (by rfl) ⟨2288399, by rfl⟩ : syracuseStep 3051199 = 4576799) B4576799
theorem B1429275 : Blo 1427533 1429275 := bstep (se 1 (by rfl) ⟨1071956, by rfl⟩ : syracuseStep 1429275 = 2143913) B2143913
theorem B1429279 : Blo 1427533 1429279 := bstep (se 1 (by rfl) ⟨1071959, by rfl⟩ : syracuseStep 1429279 = 2143919) B2143919
theorem B3616609 : Blo 1427533 3616609 := bstep (se 2 (by rfl) ⟨1356228, by rfl⟩ : syracuseStep 3616609 = 2712457) B2712457
theorem B1429359 : Blo 1427533 1429359 := bstep (se 1 (by rfl) ⟨1072019, by rfl⟩ : syracuseStep 1429359 = 2144039) B2144039
theorem B3215303 : Blo 1427533 3215303 := bstep (se 1 (by rfl) ⟨2411477, by rfl⟩ : syracuseStep 3215303 = 4822955) B4822955
theorem B4821065 : Blo 1427533 4821065 := bstep (se 2 (by rfl) ⟨1807899, by rfl⟩ : syracuseStep 4821065 = 3615799) B3615799
theorem B281727395 : Blo 1427533 281727395 := bstep (se 1 (by rfl) ⟨211295546, by rfl⟩ : syracuseStep 281727395 = 422591093) B422591093
theorem B3617257 : Blo 1427533 3617257 := bstep (se 2 (by rfl) ⟨1356471, by rfl⟩ : syracuseStep 3617257 = 2712943) B2712943
theorem B2142767 : Blo 1427533 2142767 := bstep (se 1 (by rfl) ⟨1607075, by rfl⟩ : syracuseStep 2142767 = 3214151) B3214151
theorem B4821551 : Blo 1427533 4821551 := bstep (se 1 (by rfl) ⟨3616163, by rfl⟩ : syracuseStep 4821551 = 7232327) B7232327
theorem B3216041 : Blo 1427533 3216041 := bstep (se 2 (by rfl) ⟨1206015, by rfl⟩ : syracuseStep 3216041 = 2412031) B2412031
theorem B2200255 : Blo 1427533 2200255 := bstep (se 1 (by rfl) ⟨1650191, by rfl⟩ : syracuseStep 2200255 = 3300383) B3300383
theorem B3863327 : Blo 1427533 3863327 := bstep (se 1 (by rfl) ⟨2897495, by rfl⟩ : syracuseStep 3863327 = 5794991) B5794991
theorem B2143199 : Blo 1427533 2143199 := bstep (se 1 (by rfl) ⟨1607399, by rfl⟩ : syracuseStep 2143199 = 3214799) B3214799
theorem B24736747 : Blo 1427533 24736747 := bstep (se 1 (by rfl) ⟨18552560, by rfl⟩ : syracuseStep 24736747 = 37105121) B37105121
theorem B3052847 : Blo 1427533 3052847 := bstep (se 1 (by rfl) ⟨2289635, by rfl⟩ : syracuseStep 3052847 = 4579271) B4579271
theorem B2143847 : Blo 1427533 2143847 := bstep (se 1 (by rfl) ⟨1607885, by rfl⟩ : syracuseStep 2143847 = 3215771) B3215771
theorem B7231355 : Blo 1427533 7231355 := bstep (se 1 (by rfl) ⟨5423516, by rfl⟩ : syracuseStep 7231355 = 10847033) B10847033
theorem B13727663 : Blo 1427533 13727663 := bstep (se 1 (by rfl) ⟨10295747, by rfl⟩ : syracuseStep 13727663 = 20591495) B20591495
theorem B4069723 : Blo 1427533 4069723 := bstep (se 1 (by rfl) ⟨3052292, by rfl⟩ : syracuseStep 4069723 = 6104585) B6104585
theorem B4069871 : Blo 1427533 4069871 := bstep (se 1 (by rfl) ⟨3052403, by rfl⟩ : syracuseStep 4069871 = 6104807) B6104807
theorem B24411293 : Blo 1427533 24411293 := bstep (se 3 (by rfl) ⟨4577117, by rfl⟩ : syracuseStep 24411293 = 9154235) B9154235
theorem B26058347 : Blo 1427533 26058347 := bstep (se 1 (by rfl) ⟨19543760, by rfl⟩ : syracuseStep 26058347 = 39087521) B39087521
theorem B26075123 : Blo 1427533 26075123 := bstep (se 1 (by rfl) ⟨19556342, by rfl⟩ : syracuseStep 26075123 = 39112685) B39112685
theorem B187818263 : Blo 1427533 187818263 := bstep (se 1 (by rfl) ⟨140863697, by rfl⟩ : syracuseStep 187818263 = 281727395) B281727395
theorem B1605991 : Blo 1427533 1605991 := bstep (se 1 (by rfl) ⟨1204493, by rfl⟩ : syracuseStep 1605991 = 2408987) B2408987
theorem B13730431 : Blo 1427533 13730431 := bstep (se 1 (by rfl) ⟨10297823, by rfl⟩ : syracuseStep 13730431 = 20595647) B20595647
theorem B46318405 : Blo 1427533 46318405 := bstep (se 4 (by rfl) ⟨4342350, by rfl⟩ : syracuseStep 46318405 = 8684701) B8684701
theorem B2409439 : Blo 1427533 2409439 := bstep (se 1 (by rfl) ⟨1807079, by rfl⟩ : syracuseStep 2409439 = 3614159) B3614159
theorem B49447979 : Blo 1427533 49447979 := bstep (se 1 (by rfl) ⟨37085984, by rfl⟩ : syracuseStep 49447979 = 74171969) B74171969
theorem B9151775 : Blo 1427533 9151775 := bstep (se 1 (by rfl) ⟨6863831, by rfl⟩ : syracuseStep 9151775 = 13727663) B13727663
theorem B32982329 : Blo 1427533 32982329 := bstep (se 2 (by rfl) ⟨12368373, by rfl⟩ : syracuseStep 32982329 = 24736747) B24736747
theorem B1607071 : Blo 1427533 1607071 := bstep (se 1 (by rfl) ⟨1205303, by rfl⟩ : syracuseStep 1607071 = 2410607) B2410607
theorem B3212873 : Blo 1427533 3212873 := bstep (se 2 (by rfl) ⟨1204827, by rfl⟩ : syracuseStep 3212873 = 2409655) B2409655
theorem B2713247 : Blo 1427533 2713247 := bstep (se 1 (by rfl) ⟨2034935, by rfl⟩ : syracuseStep 2713247 = 4069871) B4069871
theorem B7227143 : Blo 1427533 7227143 := bstep (se 1 (by rfl) ⟨5420357, by rfl⟩ : syracuseStep 7227143 = 10840715) B10840715
theorem B3213179 : Blo 1427533 3213179 := bstep (se 1 (by rfl) ⟨2409884, by rfl⟩ : syracuseStep 3213179 = 4819769) B4819769
theorem B2713513 : Blo 1427533 2713513 := bstep (se 2 (by rfl) ⟨1017567, by rfl⟩ : syracuseStep 2713513 = 2035135) B2035135
theorem B4819067 : Blo 1427533 4819067 := bstep (se 1 (by rfl) ⟨3614300, by rfl⟩ : syracuseStep 4819067 = 7228601) B7228601
theorem B5425339 : Blo 1427533 5425339 := bstep (se 1 (by rfl) ⟨4069004, by rfl⟩ : syracuseStep 5425339 = 8138009) B8138009
theorem B4819175 : Blo 1427533 4819175 := bstep (se 1 (by rfl) ⟨3614381, by rfl⟩ : syracuseStep 4819175 = 7228763) B7228763
theorem B2574623 : Blo 1427533 2574623 := bstep (se 1 (by rfl) ⟨1930967, by rfl⟩ : syracuseStep 2574623 = 3861935) B3861935
theorem B21162667 : Blo 1427533 21162667 := bstep (se 1 (by rfl) ⟨15872000, by rfl⟩ : syracuseStep 21162667 = 31744001) B31744001
theorem B3214043 : Blo 1427533 3214043 := bstep (se 1 (by rfl) ⟨2410532, by rfl⟩ : syracuseStep 3214043 = 4821065) B4821065
theorem B5147401 : Blo 1427533 5147401 := bstep (se 2 (by rfl) ⟨1930275, by rfl⟩ : syracuseStep 5147401 = 3860551) B3860551
theorem B3615617 : Blo 1427533 3615617 := bstep (se 2 (by rfl) ⟨1355856, by rfl⟩ : syracuseStep 3615617 = 2711713) B2711713
theorem B41208821 : Blo 1427533 41208821 := bstep (se 5 (by rfl) ⟨1931663, by rfl⟩ : syracuseStep 41208821 = 3863327) B3863327
theorem B1428511 : Blo 1427533 1428511 := bstep (se 1 (by rfl) ⟨1071383, by rfl⟩ : syracuseStep 1428511 = 2142767) B2142767
theorem B3214367 : Blo 1427533 3214367 := bstep (se 1 (by rfl) ⟨2410775, by rfl⟩ : syracuseStep 3214367 = 4821551) B4821551
theorem B5426297 : Blo 1427533 5426297 := bstep (se 2 (by rfl) ⟨2034861, by rfl⟩ : syracuseStep 5426297 = 4069723) B4069723
theorem B2141351 : Blo 1427533 2141351 := bstep (se 1 (by rfl) ⟨1606013, by rfl⟩ : syracuseStep 2141351 = 3212027) B3212027
theorem B1428799 : Blo 1427533 1428799 := bstep (se 1 (by rfl) ⟨1071599, by rfl⟩ : syracuseStep 1428799 = 2143199) B2143199
theorem B78196049 : Blo 1427533 78196049 := bstep (se 2 (by rfl) ⟨29323518, by rfl⟩ : syracuseStep 78196049 = 58647037) B58647037
theorem B2141543 : Blo 1427533 2141543 := bstep (se 1 (by rfl) ⟨1606157, by rfl⟩ : syracuseStep 2141543 = 3212315) B3212315
theorem B4820633 : Blo 1427533 4820633 := bstep (se 2 (by rfl) ⟨1807737, by rfl⟩ : syracuseStep 4820633 = 3615475) B3615475
theorem B2141927 : Blo 1427533 2141927 := bstep (se 1 (by rfl) ⟨1606445, by rfl⟩ : syracuseStep 2141927 = 3212891) B3212891
theorem B1429231 : Blo 1427533 1429231 := bstep (se 1 (by rfl) ⟨1071923, by rfl⟩ : syracuseStep 1429231 = 2143847) B2143847
theorem B4820903 : Blo 1427533 4820903 := bstep (se 1 (by rfl) ⟨3615677, by rfl⟩ : syracuseStep 4820903 = 7231355) B7231355
theorem B2142185 : Blo 1427533 2142185 := bstep (se 2 (by rfl) ⟨803319, by rfl⟩ : syracuseStep 2142185 = 1606639) B1606639
theorem B2142239 : Blo 1427533 2142239 := bstep (se 1 (by rfl) ⟨1606679, by rfl⟩ : syracuseStep 2142239 = 3213359) B3213359
theorem B1716391 : Blo 1427533 1716391 := bstep (se 1 (by rfl) ⟨1287293, by rfl⟩ : syracuseStep 1716391 = 2574587) B2574587
theorem B2142719 : Blo 1427533 2142719 := bstep (se 1 (by rfl) ⟨1607039, by rfl⟩ : syracuseStep 2142719 = 3214079) B3214079
theorem B10850921 : Blo 1427533 10850921 := bstep (se 2 (by rfl) ⟨4069095, by rfl⟩ : syracuseStep 10850921 = 8138191) B8138191
theorem B9147113 : Blo 1427533 9147113 := bstep (se 2 (by rfl) ⟨3430167, by rfl⟩ : syracuseStep 9147113 = 6860335) B6860335
theorem B16274195 : Blo 1427533 16274195 := bstep (se 1 (by rfl) ⟨12205646, by rfl⟩ : syracuseStep 16274195 = 24411293) B24411293
theorem B4068265 : Blo 1427533 4068265 := bstep (se 2 (by rfl) ⟨1525599, by rfl⟩ : syracuseStep 4068265 = 3051199) B3051199
theorem B2143259 : Blo 1427533 2143259 := bstep (se 1 (by rfl) ⟨1607444, by rfl⟩ : syracuseStep 2143259 = 3214889) B3214889
theorem B17372231 : Blo 1427533 17372231 := bstep (se 1 (by rfl) ⟨13029173, by rfl⟩ : syracuseStep 17372231 = 26058347) B26058347
theorem B4822145 : Blo 1427533 4822145 := bstep (se 2 (by rfl) ⟨1808304, by rfl⟩ : syracuseStep 4822145 = 3616609) B3616609
theorem B2143535 : Blo 1427533 2143535 := bstep (se 1 (by rfl) ⟨1607651, by rfl⟩ : syracuseStep 2143535 = 3215303) B3215303
theorem B2144027 : Blo 1427533 2144027 := bstep (se 1 (by rfl) ⟨1608020, by rfl⟩ : syracuseStep 2144027 = 3216041) B3216041
theorem B4823009 : Blo 1427533 4823009 := bstep (se 2 (by rfl) ⟨1808628, by rfl⟩ : syracuseStep 4823009 = 3617257) B3617257
theorem B8140925 : Blo 1427533 8140925 := bstep (se 3 (by rfl) ⟨1526423, by rfl⟩ : syracuseStep 8140925 = 3052847) B3052847
theorem B4823387 : Blo 1427533 4823387 := bstep (se 1 (by rfl) ⟨3617540, by rfl⟩ : syracuseStep 4823387 = 7235081) B7235081
theorem B4823495 : Blo 1427533 4823495 := bstep (se 1 (by rfl) ⟨3617621, by rfl⟩ : syracuseStep 4823495 = 7235243) B7235243
theorem B4577887 : Blo 1427533 4577887 := bstep (se 1 (by rfl) ⟨3433415, by rfl⟩ : syracuseStep 4577887 = 6866831) B6866831
theorem B46938773 : Blo 1427533 46938773 := bstep (se 6 (by rfl) ⟨1100127, by rfl⟩ : syracuseStep 46938773 = 2200255) B2200255
theorem B2710559 : Blo 1427533 2710559 := bstep (se 1 (by rfl) ⟨2032919, by rfl⟩ : syracuseStep 2710559 = 4065839) B4065839
theorem B13032575 : Blo 1427533 13032575 := bstep (se 1 (by rfl) ⟨9774431, by rfl⟩ : syracuseStep 13032575 = 19548863) B19548863
theorem B2710847 : Blo 1427533 2710847 := bstep (se 1 (by rfl) ⟨2033135, by rfl⟩ : syracuseStep 2710847 = 4066271) B4066271
theorem B4824575 : Blo 1427533 4824575 := bstep (se 1 (by rfl) ⟨3618431, by rfl⟩ : syracuseStep 4824575 = 7236863) B7236863
theorem B17383415 : Blo 1427533 17383415 := bstep (se 1 (by rfl) ⟨13037561, by rfl⟩ : syracuseStep 17383415 = 26075123) B26075123
theorem B7233785 : Blo 1427533 7233785 := bstep (se 2 (by rfl) ⟨2712669, by rfl⟩ : syracuseStep 7233785 = 5425339) B5425339
theorem B7233947 : Blo 1427533 7233947 := bstep (se 1 (by rfl) ⟨5425460, by rfl⟩ : syracuseStep 7233947 = 10850921) B10850921
theorem B32965319 : Blo 1427533 32965319 := bstep (se 1 (by rfl) ⟨24723989, by rfl⟩ : syracuseStep 32965319 = 49447979) B49447979
theorem B6865661 : Blo 1427533 6865661 := bstep (se 3 (by rfl) ⟨1287311, by rfl⟩ : syracuseStep 6865661 = 2574623) B2574623
theorem B6103849 : Blo 1427533 6103849 := bstep (se 2 (by rfl) ⟨2288943, by rfl⟩ : syracuseStep 6103849 = 4577887) B4577887
theorem B21988219 : Blo 1427533 21988219 := bstep (se 1 (by rfl) ⟨16491164, by rfl⟩ : syracuseStep 21988219 = 32982329) B32982329
theorem B4818095 : Blo 1427533 4818095 := bstep (se 1 (by rfl) ⟨3613571, by rfl⟩ : syracuseStep 4818095 = 7227143) B7227143
theorem B5424353 : Blo 1427533 5424353 := bstep (se 2 (by rfl) ⟨2034132, by rfl⟩ : syracuseStep 5424353 = 4068265) B4068265
theorem B3212585 : Blo 1427533 3212585 := bstep (se 2 (by rfl) ⟨1204719, by rfl⟩ : syracuseStep 3212585 = 2409439) B2409439
theorem B3212711 : Blo 1427533 3212711 := bstep (se 1 (by rfl) ⟨2409533, by rfl⟩ : syracuseStep 3212711 = 4819067) B4819067
theorem B3212783 : Blo 1427533 3212783 := bstep (se 1 (by rfl) ⟨2409587, by rfl⟩ : syracuseStep 3212783 = 4819175) B4819175
theorem B2410411 : Blo 1427533 2410411 := bstep (se 1 (by rfl) ⟨1807808, by rfl⟩ : syracuseStep 2410411 = 3615617) B3615617
theorem B1427567 : Blo 1427533 1427567 := bstep (se 1 (by rfl) ⟨1070675, by rfl⟩ : syracuseStep 1427567 = 2141351) B2141351
theorem B1427695 : Blo 1427533 1427695 := bstep (se 1 (by rfl) ⟨1070771, by rfl⟩ : syracuseStep 1427695 = 2141543) B2141543
theorem B3213755 : Blo 1427533 3213755 := bstep (se 1 (by rfl) ⟨2410316, by rfl⟩ : syracuseStep 3213755 = 4820633) B4820633
theorem B1427951 : Blo 1427533 1427951 := bstep (se 1 (by rfl) ⟨1070963, by rfl⟩ : syracuseStep 1427951 = 2141927) B2141927
theorem B3213935 : Blo 1427533 3213935 := bstep (se 1 (by rfl) ⟨2410451, by rfl⟩ : syracuseStep 3213935 = 4820903) B4820903
theorem B1428123 : Blo 1427533 1428123 := bstep (se 1 (by rfl) ⟨1071092, by rfl⟩ : syracuseStep 1428123 = 2142185) B2142185
theorem B1428159 : Blo 1427533 1428159 := bstep (se 1 (by rfl) ⟨1071119, by rfl⟩ : syracuseStep 1428159 = 2142239) B2142239
theorem B2288521 : Blo 1427533 2288521 := bstep (se 2 (by rfl) ⟨858195, by rfl⟩ : syracuseStep 2288521 = 1716391) B1716391
theorem B1428479 : Blo 1427533 1428479 := bstep (se 1 (by rfl) ⟨1071359, by rfl⟩ : syracuseStep 1428479 = 2142719) B2142719
theorem B2141321 : Blo 1427533 2141321 := bstep (se 2 (by rfl) ⟨802995, by rfl⟩ : syracuseStep 2141321 = 1605991) B1605991
theorem B6098075 : Blo 1427533 6098075 := bstep (se 1 (by rfl) ⟨4573556, by rfl⟩ : syracuseStep 6098075 = 9147113) B9147113
theorem B10849463 : Blo 1427533 10849463 := bstep (se 1 (by rfl) ⟨8137097, by rfl⟩ : syracuseStep 10849463 = 16274195) B16274195
theorem B1428839 : Blo 1427533 1428839 := bstep (se 1 (by rfl) ⟨1071629, by rfl⟩ : syracuseStep 1428839 = 2143259) B2143259
theorem B3214763 : Blo 1427533 3214763 := bstep (se 1 (by rfl) ⟨2411072, by rfl⟩ : syracuseStep 3214763 = 4822145) B4822145
theorem B7228925 : Blo 1427533 7228925 := bstep (se 3 (by rfl) ⟨1355423, by rfl⟩ : syracuseStep 7228925 = 2710847) B2710847
theorem B1429023 : Blo 1427533 1429023 := bstep (se 1 (by rfl) ⟨1071767, by rfl⟩ : syracuseStep 1429023 = 2143535) B2143535
theorem B28216889 : Blo 1427533 28216889 := bstep (se 2 (by rfl) ⟨10581333, by rfl⟩ : syracuseStep 28216889 = 21162667) B21162667
theorem B2141915 : Blo 1427533 2141915 := bstep (se 1 (by rfl) ⟨1606436, by rfl⟩ : syracuseStep 2141915 = 3212873) B3212873
theorem B1429351 : Blo 1427533 1429351 := bstep (se 1 (by rfl) ⟨1072013, by rfl⟩ : syracuseStep 1429351 = 2144027) B2144027
theorem B2142119 : Blo 1427533 2142119 := bstep (se 1 (by rfl) ⟨1606589, by rfl⟩ : syracuseStep 2142119 = 3213179) B3213179
theorem B3215339 : Blo 1427533 3215339 := bstep (se 1 (by rfl) ⟨2411504, by rfl⟩ : syracuseStep 3215339 = 4823009) B4823009
theorem B5427283 : Blo 1427533 5427283 := bstep (se 1 (by rfl) ⟨4070462, by rfl⟩ : syracuseStep 5427283 = 8140925) B8140925
theorem B3215591 : Blo 1427533 3215591 := bstep (se 1 (by rfl) ⟨2411693, by rfl⟩ : syracuseStep 3215591 = 4823387) B4823387
theorem B3215663 : Blo 1427533 3215663 := bstep (se 1 (by rfl) ⟨2411747, by rfl⟩ : syracuseStep 3215663 = 4823495) B4823495
theorem B2142695 : Blo 1427533 2142695 := bstep (se 1 (by rfl) ⟨1607021, by rfl⟩ : syracuseStep 2142695 = 3214043) B3214043
theorem B2142761 : Blo 1427533 2142761 := bstep (se 2 (by rfl) ⟨803535, by rfl⟩ : syracuseStep 2142761 = 1607071) B1607071
theorem B27472547 : Blo 1427533 27472547 := bstep (se 1 (by rfl) ⟨20604410, by rfl⟩ : syracuseStep 27472547 = 41208821) B41208821
theorem B1807039 : Blo 1427533 1807039 := bstep (se 1 (by rfl) ⟨1355279, by rfl⟩ : syracuseStep 1807039 = 2710559) B2710559
theorem B2142911 : Blo 1427533 2142911 := bstep (se 1 (by rfl) ⟨1607183, by rfl⟩ : syracuseStep 2142911 = 3214367) B3214367
theorem B3617531 : Blo 1427533 3617531 := bstep (se 1 (by rfl) ⟨2713148, by rfl⟩ : syracuseStep 3617531 = 5426297) B5426297
theorem B8688383 : Blo 1427533 8688383 := bstep (se 1 (by rfl) ⟨6516287, by rfl⟩ : syracuseStep 8688383 = 13032575) B13032575
theorem B52130699 : Blo 1427533 52130699 := bstep (se 1 (by rfl) ⟨39098024, by rfl⟩ : syracuseStep 52130699 = 78196049) B78196049
theorem B3216383 : Blo 1427533 3216383 := bstep (se 1 (by rfl) ⟨2412287, by rfl⟩ : syracuseStep 3216383 = 4824575) B4824575
theorem B3618017 : Blo 1427533 3618017 := bstep (se 2 (by rfl) ⟨1356756, by rfl⟩ : syracuseStep 3618017 = 2713513) B2713513
theorem B46355773 : Blo 1427533 46355773 := bstep (se 3 (by rfl) ⟨8691707, by rfl⟩ : syracuseStep 46355773 = 17383415) B17383415
theorem B125212175 : Blo 1427533 125212175 := bstep (se 1 (by rfl) ⟨93909131, by rfl⟩ : syracuseStep 125212175 = 187818263) B187818263
theorem B11581487 : Blo 1427533 11581487 := bstep (se 1 (by rfl) ⟨8686115, by rfl⟩ : syracuseStep 11581487 = 17372231) B17372231
theorem B18307241 : Blo 1427533 18307241 := bstep (se 2 (by rfl) ⟨6865215, by rfl⟩ : syracuseStep 18307241 = 13730431) B13730431
theorem B6101183 : Blo 1427533 6101183 := bstep (se 1 (by rfl) ⟨4575887, by rfl⟩ : syracuseStep 6101183 = 9151775) B9151775
theorem B6863201 : Blo 1427533 6863201 := bstep (se 2 (by rfl) ⟨2573700, by rfl⟩ : syracuseStep 6863201 = 5147401) B5147401
theorem B61757873 : Blo 1427533 61757873 := bstep (se 2 (by rfl) ⟨23159202, by rfl⟩ : syracuseStep 61757873 = 46318405) B46318405
theorem B1808831 : Blo 1427533 1808831 := bstep (se 1 (by rfl) ⟨1356623, by rfl⟩ : syracuseStep 1808831 = 2713247) B2713247
theorem B31292515 : Blo 1427533 31292515 := bstep (se 1 (by rfl) ⟨23469386, by rfl⟩ : syracuseStep 31292515 = 46938773) B46938773
theorem B16269821 : Blo 1427533 16269821 := bstep (se 3 (by rfl) ⟨3050591, by rfl⟩ : syracuseStep 16269821 = 6101183) B6101183
theorem B5792255 : Blo 1427533 5792255 := bstep (se 1 (by rfl) ⟨4344191, by rfl⟩ : syracuseStep 5792255 = 8688383) B8688383
theorem B3212063 : Blo 1427533 3212063 := bstep (se 1 (by rfl) ⟨2409047, by rfl⟩ : syracuseStep 3212063 = 4818095) B4818095
theorem B2409385 : Blo 1427533 2409385 := bstep (se 2 (by rfl) ⟨903519, by rfl⟩ : syracuseStep 2409385 = 1807039) B1807039
theorem B41723353 : Blo 1427533 41723353 := bstep (se 2 (by rfl) ⟨15646257, by rfl⟩ : syracuseStep 41723353 = 31292515) B31292515
theorem B1427547 : Blo 1427533 1427547 := bstep (se 1 (by rfl) ⟨1070660, by rfl⟩ : syracuseStep 1427547 = 2141321) B2141321
theorem B4065383 : Blo 1427533 4065383 := bstep (se 1 (by rfl) ⟨3049037, by rfl⟩ : syracuseStep 4065383 = 6098075) B6098075
theorem B4819283 : Blo 1427533 4819283 := bstep (se 1 (by rfl) ⟨3614462, by rfl⟩ : syracuseStep 4819283 = 7228925) B7228925
theorem B18811259 : Blo 1427533 18811259 := bstep (se 1 (by rfl) ⟨14108444, by rfl⟩ : syracuseStep 18811259 = 28216889) B28216889
theorem B1427943 : Blo 1427533 1427943 := bstep (se 1 (by rfl) ⟨1070957, by rfl⟩ : syracuseStep 1427943 = 2141915) B2141915
theorem B3213881 : Blo 1427533 3213881 := bstep (se 2 (by rfl) ⟨1205205, by rfl⟩ : syracuseStep 3213881 = 2410411) B2410411
theorem B1428079 : Blo 1427533 1428079 := bstep (se 1 (by rfl) ⟨1071059, by rfl⟩ : syracuseStep 1428079 = 2142119) B2142119
theorem B7236377 : Blo 1427533 7236377 := bstep (se 2 (by rfl) ⟨2713641, by rfl⟩ : syracuseStep 7236377 = 5427283) B5427283
theorem B1428463 : Blo 1427533 1428463 := bstep (se 1 (by rfl) ⟨1071347, by rfl⟩ : syracuseStep 1428463 = 2142695) B2142695
theorem B1428507 : Blo 1427533 1428507 := bstep (se 1 (by rfl) ⟨1071380, by rfl⟩ : syracuseStep 1428507 = 2142761) B2142761
theorem B1428607 : Blo 1427533 1428607 := bstep (se 1 (by rfl) ⟨1071455, by rfl⟩ : syracuseStep 1428607 = 2142911) B2142911
theorem B2411687 : Blo 1427533 2411687 := bstep (se 1 (by rfl) ⟨1808765, by rfl⟩ : syracuseStep 2411687 = 3617531) B3617531
theorem B34753799 : Blo 1427533 34753799 := bstep (se 1 (by rfl) ⟨26065349, by rfl⟩ : syracuseStep 34753799 = 52130699) B52130699
theorem B3616235 : Blo 1427533 3616235 := bstep (se 1 (by rfl) ⟨2712176, by rfl⟩ : syracuseStep 3616235 = 5424353) B5424353
theorem B2412011 : Blo 1427533 2412011 := bstep (se 1 (by rfl) ⟨1809008, by rfl⟩ : syracuseStep 2412011 = 3618017) B3618017
theorem B2141723 : Blo 1427533 2141723 := bstep (se 1 (by rfl) ⟨1606292, by rfl⟩ : syracuseStep 2141723 = 3212585) B3212585
theorem B2141807 : Blo 1427533 2141807 := bstep (se 1 (by rfl) ⟨1606355, by rfl⟩ : syracuseStep 2141807 = 3212711) B3212711
theorem B2141855 : Blo 1427533 2141855 := bstep (se 1 (by rfl) ⟨1606391, by rfl⟩ : syracuseStep 2141855 = 3212783) B3212783
theorem B8138465 : Blo 1427533 8138465 := bstep (se 2 (by rfl) ⟨3051924, by rfl⟩ : syracuseStep 8138465 = 6103849) B6103849
theorem B3051361 : Blo 1427533 3051361 := bstep (se 2 (by rfl) ⟨1144260, by rfl⟩ : syracuseStep 3051361 = 2288521) B2288521
theorem B7720991 : Blo 1427533 7720991 := bstep (se 1 (by rfl) ⟨5790743, by rfl⟩ : syracuseStep 7720991 = 11581487) B11581487
theorem B4575467 : Blo 1427533 4575467 := bstep (se 1 (by rfl) ⟨3431600, by rfl⟩ : syracuseStep 4575467 = 6863201) B6863201
theorem B2142503 : Blo 1427533 2142503 := bstep (se 1 (by rfl) ⟨1606877, by rfl⟩ : syracuseStep 2142503 = 3213755) B3213755
theorem B2142623 : Blo 1427533 2142623 := bstep (se 1 (by rfl) ⟨1606967, by rfl⟩ : syracuseStep 2142623 = 3213935) B3213935
theorem B2143175 : Blo 1427533 2143175 := bstep (se 1 (by rfl) ⟨1607381, by rfl⟩ : syracuseStep 2143175 = 3214763) B3214763
theorem B2143559 : Blo 1427533 2143559 := bstep (se 1 (by rfl) ⟨1607669, by rfl⟩ : syracuseStep 2143559 = 3215339) B3215339
theorem B2143727 : Blo 1427533 2143727 := bstep (se 1 (by rfl) ⟨1607795, by rfl⟩ : syracuseStep 2143727 = 3215591) B3215591
theorem B4822523 : Blo 1427533 4822523 := bstep (se 1 (by rfl) ⟨3616892, by rfl⟩ : syracuseStep 4822523 = 7233785) B7233785
theorem B2143775 : Blo 1427533 2143775 := bstep (se 1 (by rfl) ⟨1607831, by rfl⟩ : syracuseStep 2143775 = 3215663) B3215663
theorem B4822631 : Blo 1427533 4822631 := bstep (se 1 (by rfl) ⟨3616973, by rfl⟩ : syracuseStep 4822631 = 7233947) B7233947
theorem B18315031 : Blo 1427533 18315031 := bstep (se 1 (by rfl) ⟨13736273, by rfl⟩ : syracuseStep 18315031 = 27472547) B27472547
theorem B21976879 : Blo 1427533 21976879 := bstep (se 1 (by rfl) ⟨16482659, by rfl⟩ : syracuseStep 21976879 = 32965319) B32965319
theorem B4577107 : Blo 1427533 4577107 := bstep (se 1 (by rfl) ⟨3432830, by rfl⟩ : syracuseStep 4577107 = 6865661) B6865661
theorem B2144255 : Blo 1427533 2144255 := bstep (se 1 (by rfl) ⟨1608191, by rfl⟩ : syracuseStep 2144255 = 3216383) B3216383
theorem B83474783 : Blo 1427533 83474783 := bstep (se 1 (by rfl) ⟨62606087, by rfl⟩ : syracuseStep 83474783 = 125212175) B125212175
theorem B29317625 : Blo 1427533 29317625 := bstep (se 2 (by rfl) ⟨10994109, by rfl⟩ : syracuseStep 29317625 = 21988219) B21988219
theorem B4823549 : Blo 1427533 4823549 := bstep (se 3 (by rfl) ⟨904415, by rfl⟩ : syracuseStep 4823549 = 1808831) B1808831
theorem B12204827 : Blo 1427533 12204827 := bstep (se 1 (by rfl) ⟨9153620, by rfl⟩ : syracuseStep 12204827 = 18307241) B18307241
theorem B41171915 : Blo 1427533 41171915 := bstep (se 1 (by rfl) ⟨30878936, by rfl⟩ : syracuseStep 41171915 = 61757873) B61757873
theorem B61807697 : Blo 1427533 61807697 := bstep (se 2 (by rfl) ⟨23177886, by rfl⟩ : syracuseStep 61807697 = 46355773) B46355773
theorem B7232975 : Blo 1427533 7232975 := bstep (se 1 (by rfl) ⟨5424731, by rfl⟩ : syracuseStep 7232975 = 10849463) B10849463
theorem B10846547 : Blo 1427533 10846547 := bstep (se 1 (by rfl) ⟨8134910, by rfl⟩ : syracuseStep 10846547 = 16269821) B16269821
theorem B3212513 : Blo 1427533 3212513 := bstep (se 2 (by rfl) ⟨1204692, by rfl⟩ : syracuseStep 3212513 = 2409385) B2409385
theorem B3212855 : Blo 1427533 3212855 := bstep (se 1 (by rfl) ⟨2409641, by rfl⟩ : syracuseStep 3212855 = 4819283) B4819283
theorem B55649855 : Blo 1427533 55649855 := bstep (se 1 (by rfl) ⟨41737391, by rfl⟩ : syracuseStep 55649855 = 83474783) B83474783
theorem B8136551 : Blo 1427533 8136551 := bstep (se 1 (by rfl) ⟨6102413, by rfl⟩ : syracuseStep 8136551 = 12204827) B12204827
theorem B1607791 : Blo 1427533 1607791 := bstep (se 1 (by rfl) ⟨1205843, by rfl⟩ : syracuseStep 1607791 = 2411687) B2411687
theorem B23169199 : Blo 1427533 23169199 := bstep (se 1 (by rfl) ⟨17376899, by rfl⟩ : syracuseStep 23169199 = 34753799) B34753799
theorem B2410823 : Blo 1427533 2410823 := bstep (se 1 (by rfl) ⟨1808117, by rfl⟩ : syracuseStep 2410823 = 3616235) B3616235
theorem B1608007 : Blo 1427533 1608007 := bstep (se 1 (by rfl) ⟨1206005, by rfl⟩ : syracuseStep 1608007 = 2412011) B2412011
theorem B1427815 : Blo 1427533 1427815 := bstep (se 1 (by rfl) ⟨1070861, by rfl⟩ : syracuseStep 1427815 = 2141723) B2141723
theorem B1427871 : Blo 1427533 1427871 := bstep (se 1 (by rfl) ⟨1070903, by rfl⟩ : syracuseStep 1427871 = 2141807) B2141807
theorem B1427903 : Blo 1427533 1427903 := bstep (se 1 (by rfl) ⟨1070927, by rfl⟩ : syracuseStep 1427903 = 2141855) B2141855
theorem B5425643 : Blo 1427533 5425643 := bstep (se 1 (by rfl) ⟨4069232, by rfl⟩ : syracuseStep 5425643 = 8138465) B8138465
theorem B5147327 : Blo 1427533 5147327 := bstep (se 1 (by rfl) ⟨3860495, by rfl⟩ : syracuseStep 5147327 = 7720991) B7720991
theorem B3050311 : Blo 1427533 3050311 := bstep (se 1 (by rfl) ⟨2287733, by rfl⟩ : syracuseStep 3050311 = 4575467) B4575467
theorem B1428335 : Blo 1427533 1428335 := bstep (se 1 (by rfl) ⟨1071251, by rfl⟩ : syracuseStep 1428335 = 2142503) B2142503
theorem B1428415 : Blo 1427533 1428415 := bstep (se 1 (by rfl) ⟨1071311, by rfl⟩ : syracuseStep 1428415 = 2142623) B2142623
theorem B3861503 : Blo 1427533 3861503 := bstep (se 1 (by rfl) ⟨2896127, by rfl⟩ : syracuseStep 3861503 = 5792255) B5792255
theorem B2141375 : Blo 1427533 2141375 := bstep (se 1 (by rfl) ⟨1606031, by rfl⟩ : syracuseStep 2141375 = 3212063) B3212063
theorem B1428783 : Blo 1427533 1428783 := bstep (se 1 (by rfl) ⟨1071587, by rfl⟩ : syracuseStep 1428783 = 2143175) B2143175
theorem B1429039 : Blo 1427533 1429039 := bstep (se 1 (by rfl) ⟨1071779, by rfl⟩ : syracuseStep 1429039 = 2143559) B2143559
theorem B1429151 : Blo 1427533 1429151 := bstep (se 1 (by rfl) ⟨1071863, by rfl⟩ : syracuseStep 1429151 = 2143727) B2143727
theorem B3215015 : Blo 1427533 3215015 := bstep (se 1 (by rfl) ⟨2411261, by rfl⟩ : syracuseStep 3215015 = 4822523) B4822523
theorem B1429183 : Blo 1427533 1429183 := bstep (se 1 (by rfl) ⟨1071887, by rfl⟩ : syracuseStep 1429183 = 2143775) B2143775
theorem B3215087 : Blo 1427533 3215087 := bstep (se 1 (by rfl) ⟨2411315, by rfl⟩ : syracuseStep 3215087 = 4822631) B4822631
theorem B1429503 : Blo 1427533 1429503 := bstep (se 1 (by rfl) ⟨1072127, by rfl⟩ : syracuseStep 1429503 = 2144255) B2144255
theorem B3215699 : Blo 1427533 3215699 := bstep (se 1 (by rfl) ⟨2411774, by rfl⟩ : syracuseStep 3215699 = 4823549) B4823549
theorem B2142587 : Blo 1427533 2142587 := bstep (se 1 (by rfl) ⟨1606940, by rfl⟩ : syracuseStep 2142587 = 3213881) B3213881
theorem B27447943 : Blo 1427533 27447943 := bstep (se 1 (by rfl) ⟨20585957, by rfl⟩ : syracuseStep 27447943 = 41171915) B41171915
theorem B4821983 : Blo 1427533 4821983 := bstep (se 1 (by rfl) ⟨3616487, by rfl⟩ : syracuseStep 4821983 = 7232975) B7232975
theorem B4068481 : Blo 1427533 4068481 := bstep (se 2 (by rfl) ⟨1525680, by rfl⟩ : syracuseStep 4068481 = 3051361) B3051361
theorem B2710255 : Blo 1427533 2710255 := bstep (se 1 (by rfl) ⟨2032691, by rfl⟩ : syracuseStep 2710255 = 4065383) B4065383
theorem B12540839 : Blo 1427533 12540839 := bstep (se 1 (by rfl) ⟨9405629, by rfl⟩ : syracuseStep 12540839 = 18811259) B18811259
theorem B19545083 : Blo 1427533 19545083 := bstep (se 1 (by rfl) ⟨14658812, by rfl⟩ : syracuseStep 19545083 = 29317625) B29317625
theorem B4824251 : Blo 1427533 4824251 := bstep (se 1 (by rfl) ⟨3618188, by rfl⟩ : syracuseStep 4824251 = 7236377) B7236377
theorem B55631137 : Blo 1427533 55631137 := bstep (se 2 (by rfl) ⟨20861676, by rfl⟩ : syracuseStep 55631137 = 41723353) B41723353
theorem B41205131 : Blo 1427533 41205131 := bstep (se 1 (by rfl) ⟨30903848, by rfl⟩ : syracuseStep 41205131 = 61807697) B61807697
theorem B24420041 : Blo 1427533 24420041 := bstep (se 2 (by rfl) ⟨9157515, by rfl⟩ : syracuseStep 24420041 = 18315031) B18315031
theorem B29302505 : Blo 1427533 29302505 := bstep (se 2 (by rfl) ⟨10988439, by rfl⟩ : syracuseStep 29302505 = 21976879) B21976879
theorem B6102809 : Blo 1427533 6102809 := bstep (se 2 (by rfl) ⟨2288553, by rfl⟩ : syracuseStep 6102809 = 4577107) B4577107
theorem B30892265 : Blo 1427533 30892265 := bstep (se 2 (by rfl) ⟨11584599, by rfl⟩ : syracuseStep 30892265 = 23169199) B23169199
theorem B3613673 : Blo 1427533 3613673 := bstep (se 2 (by rfl) ⟨1355127, by rfl⟩ : syracuseStep 3613673 = 2710255) B2710255
theorem B5424367 : Blo 1427533 5424367 := bstep (se 1 (by rfl) ⟨4068275, by rfl⟩ : syracuseStep 5424367 = 8136551) B8136551
theorem B5424641 : Blo 1427533 5424641 := bstep (se 2 (by rfl) ⟨2034240, by rfl⟩ : syracuseStep 5424641 = 4068481) B4068481
theorem B1607215 : Blo 1427533 1607215 := bstep (se 1 (by rfl) ⟨1205411, by rfl⟩ : syracuseStep 1607215 = 2410823) B2410823
theorem B2574335 : Blo 1427533 2574335 := bstep (se 1 (by rfl) ⟨1930751, by rfl⟩ : syracuseStep 2574335 = 3861503) B3861503
theorem B1427583 : Blo 1427533 1427583 := bstep (se 1 (by rfl) ⟨1070687, by rfl⟩ : syracuseStep 1427583 = 2141375) B2141375
theorem B27470087 : Blo 1427533 27470087 := bstep (se 1 (by rfl) ⟨20602565, by rfl⟩ : syracuseStep 27470087 = 41205131) B41205131
theorem B33442237 : Blo 1427533 33442237 := bstep (se 3 (by rfl) ⟨6270419, by rfl⟩ : syracuseStep 33442237 = 12540839) B12540839
theorem B16280027 : Blo 1427533 16280027 := bstep (se 1 (by rfl) ⟨12210020, by rfl⟩ : syracuseStep 16280027 = 24420041) B24420041
theorem B1428391 : Blo 1427533 1428391 := bstep (se 1 (by rfl) ⟨1071293, by rfl⟩ : syracuseStep 1428391 = 2142587) B2142587
theorem B3214655 : Blo 1427533 3214655 := bstep (se 1 (by rfl) ⟨2410991, by rfl⟩ : syracuseStep 3214655 = 4821983) B4821983
theorem B2141675 : Blo 1427533 2141675 := bstep (se 1 (by rfl) ⟨1606256, by rfl⟩ : syracuseStep 2141675 = 3212513) B3212513
theorem B36597257 : Blo 1427533 36597257 := bstep (se 2 (by rfl) ⟨13723971, by rfl⟩ : syracuseStep 36597257 = 27447943) B27447943
theorem B2141903 : Blo 1427533 2141903 := bstep (se 1 (by rfl) ⟨1606427, by rfl⟩ : syracuseStep 2141903 = 3212855) B3212855
theorem B4067081 : Blo 1427533 4067081 := bstep (se 2 (by rfl) ⟨1525155, by rfl⟩ : syracuseStep 4067081 = 3050311) B3050311
theorem B3617095 : Blo 1427533 3617095 := bstep (se 1 (by rfl) ⟨2712821, by rfl⟩ : syracuseStep 3617095 = 5425643) B5425643
theorem B74174849 : Blo 1427533 74174849 := bstep (se 2 (by rfl) ⟨27815568, by rfl⟩ : syracuseStep 74174849 = 55631137) B55631137
theorem B13726205 : Blo 1427533 13726205 := bstep (se 3 (by rfl) ⟨2573663, by rfl⟩ : syracuseStep 13726205 = 5147327) B5147327
theorem B13030055 : Blo 1427533 13030055 := bstep (se 1 (by rfl) ⟨9772541, by rfl⟩ : syracuseStep 13030055 = 19545083) B19545083
theorem B3216167 : Blo 1427533 3216167 := bstep (se 1 (by rfl) ⟨2412125, by rfl⟩ : syracuseStep 3216167 = 4824251) B4824251
theorem B2143343 : Blo 1427533 2143343 := bstep (se 1 (by rfl) ⟨1607507, by rfl⟩ : syracuseStep 2143343 = 3215015) B3215015
theorem B19535003 : Blo 1427533 19535003 := bstep (se 1 (by rfl) ⟨14651252, by rfl⟩ : syracuseStep 19535003 = 29302505) B29302505
theorem B2143391 : Blo 1427533 2143391 := bstep (se 1 (by rfl) ⟨1607543, by rfl⟩ : syracuseStep 2143391 = 3215087) B3215087
theorem B4068539 : Blo 1427533 4068539 := bstep (se 1 (by rfl) ⟨3051404, by rfl⟩ : syracuseStep 4068539 = 6102809) B6102809
theorem B2143721 : Blo 1427533 2143721 := bstep (se 2 (by rfl) ⟨803895, by rfl⟩ : syracuseStep 2143721 = 1607791) B1607791
theorem B7231031 : Blo 1427533 7231031 := bstep (se 1 (by rfl) ⟨5423273, by rfl⟩ : syracuseStep 7231031 = 10846547) B10846547
theorem B2143799 : Blo 1427533 2143799 := bstep (se 1 (by rfl) ⟨1607849, by rfl⟩ : syracuseStep 2143799 = 3215699) B3215699
theorem B2144009 : Blo 1427533 2144009 := bstep (se 2 (by rfl) ⟨804003, by rfl⟩ : syracuseStep 2144009 = 1608007) B1608007
theorem B37099903 : Blo 1427533 37099903 := bstep (se 1 (by rfl) ⟨27824927, by rfl⟩ : syracuseStep 37099903 = 55649855) B55649855
theorem B20594843 : Blo 1427533 20594843 := bstep (se 1 (by rfl) ⟨15446132, by rfl⟩ : syracuseStep 20594843 = 30892265) B30892265
theorem B9150803 : Blo 1427533 9150803 := bstep (se 1 (by rfl) ⟨6863102, by rfl⟩ : syracuseStep 9150803 = 13726205) B13726205
theorem B44589649 : Blo 1427533 44589649 := bstep (se 2 (by rfl) ⟨16721118, by rfl⟩ : syracuseStep 44589649 = 33442237) B33442237
theorem B2409115 : Blo 1427533 2409115 := bstep (se 1 (by rfl) ⟨1806836, by rfl⟩ : syracuseStep 2409115 = 3613673) B3613673
theorem B2712359 : Blo 1427533 2712359 := bstep (se 1 (by rfl) ⟨2034269, by rfl⟩ : syracuseStep 2712359 = 4068539) B4068539
theorem B1427783 : Blo 1427533 1427783 := bstep (se 1 (by rfl) ⟨1070837, by rfl⟩ : syracuseStep 1427783 = 2141675) B2141675
theorem B24398171 : Blo 1427533 24398171 := bstep (se 1 (by rfl) ⟨18298628, by rfl⟩ : syracuseStep 24398171 = 36597257) B36597257
theorem B1427935 : Blo 1427533 1427935 := bstep (se 1 (by rfl) ⟨1070951, by rfl⟩ : syracuseStep 1427935 = 2141903) B2141903
theorem B49449899 : Blo 1427533 49449899 := bstep (se 1 (by rfl) ⟨37087424, by rfl⟩ : syracuseStep 49449899 = 74174849) B74174849
theorem B8686703 : Blo 1427533 8686703 := bstep (se 1 (by rfl) ⟨6515027, by rfl⟩ : syracuseStep 8686703 = 13030055) B13030055
theorem B49466537 : Blo 1427533 49466537 := bstep (se 2 (by rfl) ⟨18549951, by rfl⟩ : syracuseStep 49466537 = 37099903) B37099903
theorem B1428895 : Blo 1427533 1428895 := bstep (se 1 (by rfl) ⟨1071671, by rfl⟩ : syracuseStep 1428895 = 2143343) B2143343
theorem B1428927 : Blo 1427533 1428927 := bstep (se 1 (by rfl) ⟨1071695, by rfl⟩ : syracuseStep 1428927 = 2143391) B2143391
theorem B1429147 : Blo 1427533 1429147 := bstep (se 1 (by rfl) ⟨1071860, by rfl⟩ : syracuseStep 1429147 = 2143721) B2143721
theorem B3616427 : Blo 1427533 3616427 := bstep (se 1 (by rfl) ⟨2712320, by rfl⟩ : syracuseStep 3616427 = 5424641) B5424641
theorem B4820687 : Blo 1427533 4820687 := bstep (se 1 (by rfl) ⟨3615515, by rfl⟩ : syracuseStep 4820687 = 7231031) B7231031
theorem B1429199 : Blo 1427533 1429199 := bstep (se 1 (by rfl) ⟨1071899, by rfl⟩ : syracuseStep 1429199 = 2143799) B2143799
theorem B1429339 : Blo 1427533 1429339 := bstep (se 1 (by rfl) ⟨1072004, by rfl⟩ : syracuseStep 1429339 = 2144009) B2144009
theorem B1716223 : Blo 1427533 1716223 := bstep (se 1 (by rfl) ⟨1287167, by rfl⟩ : syracuseStep 1716223 = 2574335) B2574335
theorem B18313391 : Blo 1427533 18313391 := bstep (se 1 (by rfl) ⟨13735043, by rfl⟩ : syracuseStep 18313391 = 27470087) B27470087
theorem B2142953 : Blo 1427533 2142953 := bstep (se 2 (by rfl) ⟨803607, by rfl⟩ : syracuseStep 2142953 = 1607215) B1607215
theorem B2143103 : Blo 1427533 2143103 := bstep (se 1 (by rfl) ⟨1607327, by rfl⟩ : syracuseStep 2143103 = 3214655) B3214655
theorem B4822793 : Blo 1427533 4822793 := bstep (se 2 (by rfl) ⟨1808547, by rfl⟩ : syracuseStep 4822793 = 3617095) B3617095
theorem B2144111 : Blo 1427533 2144111 := bstep (se 1 (by rfl) ⟨1608083, by rfl⟩ : syracuseStep 2144111 = 3216167) B3216167
theorem B13023335 : Blo 1427533 13023335 := bstep (se 1 (by rfl) ⟨9767501, by rfl⟩ : syracuseStep 13023335 = 19535003) B19535003
theorem B10853351 : Blo 1427533 10853351 := bstep (se 1 (by rfl) ⟨8140013, by rfl⟩ : syracuseStep 10853351 = 16280027) B16280027
theorem B7232489 : Blo 1427533 7232489 := bstep (se 2 (by rfl) ⟨2712183, by rfl⟩ : syracuseStep 7232489 = 5424367) B5424367
theorem B2711387 : Blo 1427533 2711387 := bstep (se 1 (by rfl) ⟨2033540, by rfl⟩ : syracuseStep 2711387 = 4067081) B4067081
theorem B13729895 : Blo 1427533 13729895 := bstep (se 1 (by rfl) ⟨10297421, by rfl⟩ : syracuseStep 13729895 = 20594843) B20594843
theorem B3212153 : Blo 1427533 3212153 := bstep (se 2 (by rfl) ⟨1204557, by rfl⟩ : syracuseStep 3212153 = 2409115) B2409115
theorem B32966599 : Blo 1427533 32966599 := bstep (se 1 (by rfl) ⟨24724949, by rfl⟩ : syracuseStep 32966599 = 49449899) B49449899
theorem B7235567 : Blo 1427533 7235567 := bstep (se 1 (by rfl) ⟨5426675, by rfl⟩ : syracuseStep 7235567 = 10853351) B10853351
theorem B2410951 : Blo 1427533 2410951 := bstep (se 1 (by rfl) ⟨1808213, by rfl⟩ : syracuseStep 2410951 = 3616427) B3616427
theorem B3213791 : Blo 1427533 3213791 := bstep (se 1 (by rfl) ⟨2410343, by rfl⟩ : syracuseStep 3213791 = 4820687) B4820687
theorem B2288297 : Blo 1427533 2288297 := bstep (se 2 (by rfl) ⟨858111, by rfl⟩ : syracuseStep 2288297 = 1716223) B1716223
theorem B12208927 : Blo 1427533 12208927 := bstep (se 1 (by rfl) ⟨9156695, by rfl⟩ : syracuseStep 12208927 = 18313391) B18313391
theorem B1428635 : Blo 1427533 1428635 := bstep (se 1 (by rfl) ⟨1071476, by rfl⟩ : syracuseStep 1428635 = 2142953) B2142953
theorem B1428735 : Blo 1427533 1428735 := bstep (se 1 (by rfl) ⟨1071551, by rfl⟩ : syracuseStep 1428735 = 2143103) B2143103
theorem B59452865 : Blo 1427533 59452865 := bstep (se 2 (by rfl) ⟨22294824, by rfl⟩ : syracuseStep 59452865 = 44589649) B44589649
theorem B3215195 : Blo 1427533 3215195 := bstep (se 1 (by rfl) ⟨2411396, by rfl⟩ : syracuseStep 3215195 = 4822793) B4822793
theorem B1429407 : Blo 1427533 1429407 := bstep (se 1 (by rfl) ⟨1072055, by rfl⟩ : syracuseStep 1429407 = 2144111) B2144111
theorem B16265447 : Blo 1427533 16265447 := bstep (se 1 (by rfl) ⟨12199085, by rfl⟩ : syracuseStep 16265447 = 24398171) B24398171
theorem B4821659 : Blo 1427533 4821659 := bstep (se 1 (by rfl) ⟨3616244, by rfl⟩ : syracuseStep 4821659 = 7232489) B7232489
theorem B32977691 : Blo 1427533 32977691 := bstep (se 1 (by rfl) ⟨24733268, by rfl⟩ : syracuseStep 32977691 = 49466537) B49466537
theorem B1807591 : Blo 1427533 1807591 := bstep (se 1 (by rfl) ⟨1355693, by rfl⟩ : syracuseStep 1807591 = 2711387) B2711387
theorem B6100535 : Blo 1427533 6100535 := bstep (se 1 (by rfl) ⟨4575401, by rfl⟩ : syracuseStep 6100535 = 9150803) B9150803
theorem B1808239 : Blo 1427533 1808239 := bstep (se 1 (by rfl) ⟨1356179, by rfl⟩ : syracuseStep 1808239 = 2712359) B2712359
theorem B8682223 : Blo 1427533 8682223 := bstep (se 1 (by rfl) ⟨6511667, by rfl⟩ : syracuseStep 8682223 = 13023335) B13023335
theorem B5791135 : Blo 1427533 5791135 := bstep (se 1 (by rfl) ⟨4343351, by rfl⟩ : syracuseStep 5791135 = 8686703) B8686703
theorem B11576297 : Blo 1427533 11576297 := bstep (se 2 (by rfl) ⟨4341111, by rfl⟩ : syracuseStep 11576297 = 8682223) B8682223
theorem B16278569 : Blo 1427533 16278569 := bstep (se 2 (by rfl) ⟨6104463, by rfl⟩ : syracuseStep 16278569 = 12208927) B12208927
theorem B2410121 : Blo 1427533 2410121 := bstep (se 2 (by rfl) ⟨903795, by rfl⟩ : syracuseStep 2410121 = 1807591) B1807591
theorem B39635243 : Blo 1427533 39635243 := bstep (se 1 (by rfl) ⟨29726432, by rfl⟩ : syracuseStep 39635243 = 59452865) B59452865
theorem B2410985 : Blo 1427533 2410985 := bstep (se 2 (by rfl) ⟨904119, by rfl⟩ : syracuseStep 2410985 = 1808239) B1808239
theorem B9153263 : Blo 1427533 9153263 := bstep (se 1 (by rfl) ⟨6864947, by rfl⟩ : syracuseStep 9153263 = 13729895) B13729895
theorem B3214439 : Blo 1427533 3214439 := bstep (se 1 (by rfl) ⟨2410829, by rfl⟩ : syracuseStep 3214439 = 4821659) B4821659
theorem B2141435 : Blo 1427533 2141435 := bstep (se 1 (by rfl) ⟨1606076, by rfl⟩ : syracuseStep 2141435 = 3212153) B3212153
theorem B3214601 : Blo 1427533 3214601 := bstep (se 2 (by rfl) ⟨1205475, by rfl⟩ : syracuseStep 3214601 = 2410951) B2410951
theorem B4067023 : Blo 1427533 4067023 := bstep (se 1 (by rfl) ⟨3050267, by rfl⟩ : syracuseStep 4067023 = 6100535) B6100535
theorem B2142527 : Blo 1427533 2142527 := bstep (se 1 (by rfl) ⟨1606895, by rfl⟩ : syracuseStep 2142527 = 3213791) B3213791
theorem B7721513 : Blo 1427533 7721513 := bstep (se 2 (by rfl) ⟨2895567, by rfl⟩ : syracuseStep 7721513 = 5791135) B5791135
theorem B2143463 : Blo 1427533 2143463 := bstep (se 1 (by rfl) ⟨1607597, by rfl⟩ : syracuseStep 2143463 = 3215195) B3215195
theorem B43955465 : Blo 1427533 43955465 := bstep (se 2 (by rfl) ⟨16483299, by rfl⟩ : syracuseStep 43955465 = 32966599) B32966599
theorem B10843631 : Blo 1427533 10843631 := bstep (se 1 (by rfl) ⟨8132723, by rfl⟩ : syracuseStep 10843631 = 16265447) B16265447
theorem B21985127 : Blo 1427533 21985127 := bstep (se 1 (by rfl) ⟨16488845, by rfl⟩ : syracuseStep 21985127 = 32977691) B32977691
theorem B4823711 : Blo 1427533 4823711 := bstep (se 1 (by rfl) ⟨3617783, by rfl⟩ : syracuseStep 4823711 = 7235567) B7235567
theorem B6102125 : Blo 1427533 6102125 := bstep (se 3 (by rfl) ⟨1144148, by rfl⟩ : syracuseStep 6102125 = 2288297) B2288297
theorem B7717531 : Blo 1427533 7717531 := bstep (se 1 (by rfl) ⟨5788148, by rfl⟩ : syracuseStep 7717531 = 11576297) B11576297
theorem B1606747 : Blo 1427533 1606747 := bstep (se 1 (by rfl) ⟨1205060, by rfl⟩ : syracuseStep 1606747 = 2410121) B2410121
theorem B14656751 : Blo 1427533 14656751 := bstep (se 1 (by rfl) ⟨10992563, by rfl⟩ : syracuseStep 14656751 = 21985127) B21985127
theorem B1607323 : Blo 1427533 1607323 := bstep (se 1 (by rfl) ⟨1205492, by rfl⟩ : syracuseStep 1607323 = 2410985) B2410985
theorem B1427623 : Blo 1427533 1427623 := bstep (se 1 (by rfl) ⟨1070717, by rfl⟩ : syracuseStep 1427623 = 2141435) B2141435
theorem B1428351 : Blo 1427533 1428351 := bstep (se 1 (by rfl) ⟨1071263, by rfl⟩ : syracuseStep 1428351 = 2142527) B2142527
theorem B5147675 : Blo 1427533 5147675 := bstep (se 1 (by rfl) ⟨3860756, by rfl⟩ : syracuseStep 5147675 = 7721513) B7721513
theorem B117214573 : Blo 1427533 117214573 := bstep (se 3 (by rfl) ⟨21977732, by rfl⟩ : syracuseStep 117214573 = 43955465) B43955465
theorem B1428975 : Blo 1427533 1428975 := bstep (se 1 (by rfl) ⟨1071731, by rfl⟩ : syracuseStep 1428975 = 2143463) B2143463
theorem B7229087 : Blo 1427533 7229087 := bstep (se 1 (by rfl) ⟨5421815, by rfl⟩ : syracuseStep 7229087 = 10843631) B10843631
theorem B26423495 : Blo 1427533 26423495 := bstep (se 1 (by rfl) ⟨19817621, by rfl⟩ : syracuseStep 26423495 = 39635243) B39635243
theorem B3215807 : Blo 1427533 3215807 := bstep (se 1 (by rfl) ⟨2411855, by rfl⟩ : syracuseStep 3215807 = 4823711) B4823711
theorem B2142959 : Blo 1427533 2142959 := bstep (se 1 (by rfl) ⟨1607219, by rfl⟩ : syracuseStep 2142959 = 3214439) B3214439
theorem B4068083 : Blo 1427533 4068083 := bstep (se 1 (by rfl) ⟨3051062, by rfl⟩ : syracuseStep 4068083 = 6102125) B6102125
theorem B2143067 : Blo 1427533 2143067 := bstep (se 1 (by rfl) ⟨1607300, by rfl⟩ : syracuseStep 2143067 = 3214601) B3214601
theorem B10852379 : Blo 1427533 10852379 := bstep (se 1 (by rfl) ⟨8139284, by rfl⟩ : syracuseStep 10852379 = 16278569) B16278569
theorem B6102175 : Blo 1427533 6102175 := bstep (se 1 (by rfl) ⟨4576631, by rfl⟩ : syracuseStep 6102175 = 9153263) B9153263
theorem B5422697 : Blo 1427533 5422697 := bstep (se 2 (by rfl) ⟨2033511, by rfl⟩ : syracuseStep 5422697 = 4067023) B4067023
theorem B2712055 : Blo 1427533 2712055 := bstep (se 1 (by rfl) ⟨2034041, by rfl⟩ : syracuseStep 2712055 = 4068083) B4068083
theorem B10290041 : Blo 1427533 10290041 := bstep (se 2 (by rfl) ⟨3858765, by rfl⟩ : syracuseStep 10290041 = 7717531) B7717531
theorem B7234919 : Blo 1427533 7234919 := bstep (se 1 (by rfl) ⟨5426189, by rfl⟩ : syracuseStep 7234919 = 10852379) B10852379
theorem B8136233 : Blo 1427533 8136233 := bstep (se 2 (by rfl) ⟨3051087, by rfl⟩ : syracuseStep 8136233 = 6102175) B6102175
theorem B3615131 : Blo 1427533 3615131 := bstep (se 1 (by rfl) ⟨2711348, by rfl⟩ : syracuseStep 3615131 = 5422697) B5422697
theorem B4819391 : Blo 1427533 4819391 := bstep (se 1 (by rfl) ⟨3614543, by rfl⟩ : syracuseStep 4819391 = 7229087) B7229087
theorem B17615663 : Blo 1427533 17615663 := bstep (se 1 (by rfl) ⟨13211747, by rfl⟩ : syracuseStep 17615663 = 26423495) B26423495
theorem B1428639 : Blo 1427533 1428639 := bstep (se 1 (by rfl) ⟨1071479, by rfl⟩ : syracuseStep 1428639 = 2142959) B2142959
theorem B1428711 : Blo 1427533 1428711 := bstep (se 1 (by rfl) ⟨1071533, by rfl⟩ : syracuseStep 1428711 = 2143067) B2143067
theorem B2142329 : Blo 1427533 2142329 := bstep (se 2 (by rfl) ⟨803373, by rfl⟩ : syracuseStep 2142329 = 1606747) B1606747
theorem B2143097 : Blo 1427533 2143097 := bstep (se 2 (by rfl) ⟨803661, by rfl⟩ : syracuseStep 2143097 = 1607323) B1607323
theorem B2143871 : Blo 1427533 2143871 := bstep (se 1 (by rfl) ⟨1607903, by rfl⟩ : syracuseStep 2143871 = 3215807) B3215807
theorem B9771167 : Blo 1427533 9771167 := bstep (se 1 (by rfl) ⟨7328375, by rfl⟩ : syracuseStep 9771167 = 14656751) B14656751
theorem B156286097 : Blo 1427533 156286097 := bstep (se 2 (by rfl) ⟨58607286, by rfl⟩ : syracuseStep 156286097 = 117214573) B117214573
theorem B3431783 : Blo 1427533 3431783 := bstep (se 1 (by rfl) ⟨2573837, by rfl⟩ : syracuseStep 3431783 = 5147675) B5147675
theorem B5424155 : Blo 1427533 5424155 := bstep (se 1 (by rfl) ⟨4068116, by rfl⟩ : syracuseStep 5424155 = 8136233) B8136233
theorem B6514111 : Blo 1427533 6514111 := bstep (se 1 (by rfl) ⟨4885583, by rfl⟩ : syracuseStep 6514111 = 9771167) B9771167
theorem B2410087 : Blo 1427533 2410087 := bstep (se 1 (by rfl) ⟨1807565, by rfl⟩ : syracuseStep 2410087 = 3615131) B3615131
theorem B3212927 : Blo 1427533 3212927 := bstep (se 1 (by rfl) ⟨2409695, by rfl⟩ : syracuseStep 3212927 = 4819391) B4819391
theorem B2287855 : Blo 1427533 2287855 := bstep (se 1 (by rfl) ⟨1715891, by rfl⟩ : syracuseStep 2287855 = 3431783) B3431783
theorem B1428219 : Blo 1427533 1428219 := bstep (se 1 (by rfl) ⟨1071164, by rfl⟩ : syracuseStep 1428219 = 2142329) B2142329
theorem B6860027 : Blo 1427533 6860027 := bstep (se 1 (by rfl) ⟨5145020, by rfl⟩ : syracuseStep 6860027 = 10290041) B10290041
theorem B1428731 : Blo 1427533 1428731 := bstep (se 1 (by rfl) ⟨1071548, by rfl⟩ : syracuseStep 1428731 = 2143097) B2143097
theorem B3616073 : Blo 1427533 3616073 := bstep (se 2 (by rfl) ⟨1356027, by rfl⟩ : syracuseStep 3616073 = 2712055) B2712055
theorem B1429247 : Blo 1427533 1429247 := bstep (se 1 (by rfl) ⟨1071935, by rfl⟩ : syracuseStep 1429247 = 2143871) B2143871
theorem B11743775 : Blo 1427533 11743775 := bstep (se 1 (by rfl) ⟨8807831, by rfl⟩ : syracuseStep 11743775 = 17615663) B17615663
theorem B104190731 : Blo 1427533 104190731 := bstep (se 1 (by rfl) ⟨78143048, by rfl⟩ : syracuseStep 104190731 = 156286097) B156286097
theorem B4823279 : Blo 1427533 4823279 := bstep (se 1 (by rfl) ⟨3617459, by rfl⟩ : syracuseStep 4823279 = 7234919) B7234919
theorem B69460487 : Blo 1427533 69460487 := bstep (se 1 (by rfl) ⟨52095365, by rfl⟩ : syracuseStep 69460487 = 104190731) B104190731
theorem B8685481 : Blo 1427533 8685481 := bstep (se 2 (by rfl) ⟨3257055, by rfl⟩ : syracuseStep 8685481 = 6514111) B6514111
theorem B3213449 : Blo 1427533 3213449 := bstep (se 2 (by rfl) ⟨1205043, by rfl⟩ : syracuseStep 3213449 = 2410087) B2410087
theorem B4573351 : Blo 1427533 4573351 := bstep (se 1 (by rfl) ⟨3430013, by rfl⟩ : syracuseStep 4573351 = 6860027) B6860027
theorem B2410715 : Blo 1427533 2410715 := bstep (se 1 (by rfl) ⟨1808036, by rfl⟩ : syracuseStep 2410715 = 3616073) B3616073
theorem B3050473 : Blo 1427533 3050473 := bstep (se 2 (by rfl) ⟨1143927, by rfl⟩ : syracuseStep 3050473 = 2287855) B2287855
theorem B3616103 : Blo 1427533 3616103 := bstep (se 1 (by rfl) ⟨2712077, by rfl⟩ : syracuseStep 3616103 = 5424155) B5424155
theorem B2141951 : Blo 1427533 2141951 := bstep (se 1 (by rfl) ⟨1606463, by rfl⟩ : syracuseStep 2141951 = 3212927) B3212927
theorem B3215519 : Blo 1427533 3215519 := bstep (se 1 (by rfl) ⟨2411639, by rfl⟩ : syracuseStep 3215519 = 4823279) B4823279
theorem B7829183 : Blo 1427533 7829183 := bstep (se 1 (by rfl) ⟨5871887, by rfl⟩ : syracuseStep 7829183 = 11743775) B11743775
theorem B1607143 : Blo 1427533 1607143 := bstep (se 1 (by rfl) ⟨1205357, by rfl⟩ : syracuseStep 1607143 = 2410715) B2410715
theorem B2410735 : Blo 1427533 2410735 := bstep (se 1 (by rfl) ⟨1808051, by rfl⟩ : syracuseStep 2410735 = 3616103) B3616103
theorem B1427967 : Blo 1427533 1427967 := bstep (se 1 (by rfl) ⟨1070975, by rfl⟩ : syracuseStep 1427967 = 2141951) B2141951
theorem B6097801 : Blo 1427533 6097801 := bstep (se 2 (by rfl) ⟨2286675, by rfl⟩ : syracuseStep 6097801 = 4573351) B4573351
theorem B4067297 : Blo 1427533 4067297 := bstep (se 2 (by rfl) ⟨1525236, by rfl⟩ : syracuseStep 4067297 = 3050473) B3050473
theorem B2142299 : Blo 1427533 2142299 := bstep (se 1 (by rfl) ⟨1606724, by rfl⟩ : syracuseStep 2142299 = 3213449) B3213449
theorem B20877821 : Blo 1427533 20877821 := bstep (se 3 (by rfl) ⟨3914591, by rfl⟩ : syracuseStep 20877821 = 7829183) B7829183
theorem B11580641 : Blo 1427533 11580641 := bstep (se 2 (by rfl) ⟨4342740, by rfl⟩ : syracuseStep 11580641 = 8685481) B8685481
theorem B2143679 : Blo 1427533 2143679 := bstep (se 1 (by rfl) ⟨1607759, by rfl⟩ : syracuseStep 2143679 = 3215519) B3215519
theorem B46306991 : Blo 1427533 46306991 := bstep (se 1 (by rfl) ⟨34730243, by rfl⟩ : syracuseStep 46306991 = 69460487) B69460487
theorem B13918547 : Blo 1427533 13918547 := bstep (se 1 (by rfl) ⟨10438910, by rfl⟩ : syracuseStep 13918547 = 20877821) B20877821
theorem B1428199 : Blo 1427533 1428199 := bstep (se 1 (by rfl) ⟨1071149, by rfl⟩ : syracuseStep 1428199 = 2142299) B2142299
theorem B3214313 : Blo 1427533 3214313 := bstep (se 2 (by rfl) ⟨1205367, by rfl⟩ : syracuseStep 3214313 = 2410735) B2410735
theorem B7720427 : Blo 1427533 7720427 := bstep (se 1 (by rfl) ⟨5790320, by rfl⟩ : syracuseStep 7720427 = 11580641) B11580641
theorem B1429119 : Blo 1427533 1429119 := bstep (se 1 (by rfl) ⟨1071839, by rfl⟩ : syracuseStep 1429119 = 2143679) B2143679
theorem B30871327 : Blo 1427533 30871327 := bstep (se 1 (by rfl) ⟨23153495, by rfl⟩ : syracuseStep 30871327 = 46306991) B46306991
theorem B8130401 : Blo 1427533 8130401 := bstep (se 2 (by rfl) ⟨3048900, by rfl⟩ : syracuseStep 8130401 = 6097801) B6097801
theorem B2142857 : Blo 1427533 2142857 := bstep (se 2 (by rfl) ⟨803571, by rfl⟩ : syracuseStep 2142857 = 1607143) B1607143
theorem B2711531 : Blo 1427533 2711531 := bstep (se 1 (by rfl) ⟨2033648, by rfl⟩ : syracuseStep 2711531 = 4067297) B4067297
theorem B5146951 : Blo 1427533 5146951 := bstep (se 1 (by rfl) ⟨3860213, by rfl⟩ : syracuseStep 5146951 = 7720427) B7720427
theorem B1428571 : Blo 1427533 1428571 := bstep (se 1 (by rfl) ⟨1071428, by rfl⟩ : syracuseStep 1428571 = 2142857) B2142857
theorem B2142875 : Blo 1427533 2142875 := bstep (se 1 (by rfl) ⟨1607156, by rfl⟩ : syracuseStep 2142875 = 3214313) B3214313
theorem B41161769 : Blo 1427533 41161769 := bstep (se 2 (by rfl) ⟨15435663, by rfl⟩ : syracuseStep 41161769 = 30871327) B30871327
theorem B5420267 : Blo 1427533 5420267 := bstep (se 1 (by rfl) ⟨4065200, by rfl⟩ : syracuseStep 5420267 = 8130401) B8130401
theorem B1807687 : Blo 1427533 1807687 := bstep (se 1 (by rfl) ⟨1355765, by rfl⟩ : syracuseStep 1807687 = 2711531) B2711531
theorem B9279031 : Blo 1427533 9279031 := bstep (se 1 (by rfl) ⟨6959273, by rfl⟩ : syracuseStep 9279031 = 13918547) B13918547
theorem B3613511 : Blo 1427533 3613511 := bstep (se 1 (by rfl) ⟨2710133, by rfl⟩ : syracuseStep 3613511 = 5420267) B5420267
theorem B2410249 : Blo 1427533 2410249 := bstep (se 2 (by rfl) ⟨903843, by rfl⟩ : syracuseStep 2410249 = 1807687) B1807687
theorem B12372041 : Blo 1427533 12372041 := bstep (se 2 (by rfl) ⟨4639515, by rfl⟩ : syracuseStep 12372041 = 9279031) B9279031
theorem B1428583 : Blo 1427533 1428583 := bstep (se 1 (by rfl) ⟨1071437, by rfl⟩ : syracuseStep 1428583 = 2142875) B2142875
theorem B6862601 : Blo 1427533 6862601 := bstep (se 2 (by rfl) ⟨2573475, by rfl⟩ : syracuseStep 6862601 = 5146951) B5146951
theorem B27441179 : Blo 1427533 27441179 := bstep (se 1 (by rfl) ⟨20580884, by rfl⟩ : syracuseStep 27441179 = 41161769) B41161769
theorem B2409007 : Blo 1427533 2409007 := bstep (se 1 (by rfl) ⟨1806755, by rfl⟩ : syracuseStep 2409007 = 3613511) B3613511
theorem B18294119 : Blo 1427533 18294119 := bstep (se 1 (by rfl) ⟨13720589, by rfl⟩ : syracuseStep 18294119 = 27441179) B27441179
theorem B3213665 : Blo 1427533 3213665 := bstep (se 2 (by rfl) ⟨1205124, by rfl⟩ : syracuseStep 3213665 = 2410249) B2410249
theorem B8248027 : Blo 1427533 8248027 := bstep (se 1 (by rfl) ⟨6186020, by rfl⟩ : syracuseStep 8248027 = 12372041) B12372041
theorem B18300269 : Blo 1427533 18300269 := bstep (se 3 (by rfl) ⟨3431300, by rfl⟩ : syracuseStep 18300269 = 6862601) B6862601
theorem B3212009 : Blo 1427533 3212009 := bstep (se 2 (by rfl) ⟨1204503, by rfl⟩ : syracuseStep 3212009 = 2409007) B2409007
theorem B12200179 : Blo 1427533 12200179 := bstep (se 1 (by rfl) ⟨9150134, by rfl⟩ : syracuseStep 12200179 = 18300269) B18300269
theorem B10997369 : Blo 1427533 10997369 := bstep (se 2 (by rfl) ⟨4124013, by rfl⟩ : syracuseStep 10997369 = 8248027) B8248027
theorem B2142443 : Blo 1427533 2142443 := bstep (se 1 (by rfl) ⟨1606832, by rfl⟩ : syracuseStep 2142443 = 3213665) B3213665
theorem B12196079 : Blo 1427533 12196079 := bstep (se 1 (by rfl) ⟨9147059, by rfl⟩ : syracuseStep 12196079 = 18294119) B18294119
theorem B1428295 : Blo 1427533 1428295 := bstep (se 1 (by rfl) ⟨1071221, by rfl⟩ : syracuseStep 1428295 = 2142443) B2142443
theorem B2141339 : Blo 1427533 2141339 := bstep (se 1 (by rfl) ⟨1606004, by rfl⟩ : syracuseStep 2141339 = 3212009) B3212009
theorem B8130719 : Blo 1427533 8130719 := bstep (se 1 (by rfl) ⟨6098039, by rfl⟩ : syracuseStep 8130719 = 12196079) B12196079
theorem B16266905 : Blo 1427533 16266905 := bstep (se 2 (by rfl) ⟨6100089, by rfl⟩ : syracuseStep 16266905 = 12200179) B12200179
theorem B7331579 : Blo 1427533 7331579 := bstep (se 1 (by rfl) ⟨5498684, by rfl⟩ : syracuseStep 7331579 = 10997369) B10997369
theorem B1427559 : Blo 1427533 1427559 := bstep (se 1 (by rfl) ⟨1070669, by rfl⟩ : syracuseStep 1427559 = 2141339) B2141339
theorem B4887719 : Blo 1427533 4887719 := bstep (se 1 (by rfl) ⟨3665789, by rfl⟩ : syracuseStep 4887719 = 7331579) B7331579
theorem B5420479 : Blo 1427533 5420479 := bstep (se 1 (by rfl) ⟨4065359, by rfl⟩ : syracuseStep 5420479 = 8130719) B8130719
theorem B10844603 : Blo 1427533 10844603 := bstep (se 1 (by rfl) ⟨8133452, by rfl⟩ : syracuseStep 10844603 = 16266905) B16266905
theorem B7227305 : Blo 1427533 7227305 := bstep (se 2 (by rfl) ⟨2710239, by rfl⟩ : syracuseStep 7227305 = 5420479) B5420479
theorem B7229735 : Blo 1427533 7229735 := bstep (se 1 (by rfl) ⟨5422301, by rfl⟩ : syracuseStep 7229735 = 10844603) B10844603
theorem B3258479 : Blo 1427533 3258479 := bstep (se 1 (by rfl) ⟨2443859, by rfl⟩ : syracuseStep 3258479 = 4887719) B4887719
theorem B4818203 : Blo 1427533 4818203 := bstep (se 1 (by rfl) ⟨3613652, by rfl⟩ : syracuseStep 4818203 = 7227305) B7227305
theorem B2172319 : Blo 1427533 2172319 := bstep (se 1 (by rfl) ⟨1629239, by rfl⟩ : syracuseStep 2172319 = 3258479) B3258479
theorem B4819823 : Blo 1427533 4819823 := bstep (se 1 (by rfl) ⟨3614867, by rfl⟩ : syracuseStep 4819823 = 7229735) B7229735
theorem B3212135 : Blo 1427533 3212135 := bstep (se 1 (by rfl) ⟨2409101, by rfl⟩ : syracuseStep 3212135 = 4818203) B4818203
theorem B3213215 : Blo 1427533 3213215 := bstep (se 1 (by rfl) ⟨2409911, by rfl⟩ : syracuseStep 3213215 = 4819823) B4819823
theorem B11585701 : Blo 1427533 11585701 := bstep (se 4 (by rfl) ⟨1086159, by rfl⟩ : syracuseStep 11585701 = 2172319) B2172319
theorem B2141423 : Blo 1427533 2141423 := bstep (se 1 (by rfl) ⟨1606067, by rfl⟩ : syracuseStep 2141423 = 3212135) B3212135
theorem B2142143 : Blo 1427533 2142143 := bstep (se 1 (by rfl) ⟨1606607, by rfl⟩ : syracuseStep 2142143 = 3213215) B3213215
theorem B15447601 : Blo 1427533 15447601 := bstep (se 2 (by rfl) ⟨5792850, by rfl⟩ : syracuseStep 15447601 = 11585701) B11585701
theorem B20596801 : Blo 1427533 20596801 := bstep (se 2 (by rfl) ⟨7723800, by rfl⟩ : syracuseStep 20596801 = 15447601) B15447601
theorem B1427615 : Blo 1427533 1427615 := bstep (se 1 (by rfl) ⟨1070711, by rfl⟩ : syracuseStep 1427615 = 2141423) B2141423
theorem B1428095 : Blo 1427533 1428095 := bstep (se 1 (by rfl) ⟨1071071, by rfl⟩ : syracuseStep 1428095 = 2142143) B2142143
theorem B27462401 : Blo 1427533 27462401 := bstep (se 2 (by rfl) ⟨10298400, by rfl⟩ : syracuseStep 27462401 = 20596801) B20596801
theorem B18308267 : Blo 1427533 18308267 := bstep (se 1 (by rfl) ⟨13731200, by rfl⟩ : syracuseStep 18308267 = 27462401) B27462401
theorem B12205511 : Blo 1427533 12205511 := bstep (se 1 (by rfl) ⟨9154133, by rfl⟩ : syracuseStep 12205511 = 18308267) B18308267
theorem B8137007 : Blo 1427533 8137007 := bstep (se 1 (by rfl) ⟨6102755, by rfl⟩ : syracuseStep 8137007 = 12205511) B12205511
theorem B5424671 : Blo 1427533 5424671 := bstep (se 1 (by rfl) ⟨4068503, by rfl⟩ : syracuseStep 5424671 = 8137007) B8137007
theorem B3616447 : Blo 1427533 3616447 := bstep (se 1 (by rfl) ⟨2712335, by rfl⟩ : syracuseStep 3616447 = 5424671) B5424671
theorem B4821929 : Blo 1427533 4821929 := bstep (se 2 (by rfl) ⟨1808223, by rfl⟩ : syracuseStep 4821929 = 3616447) B3616447
theorem B3214619 : Blo 1427533 3214619 := bstep (se 1 (by rfl) ⟨2410964, by rfl⟩ : syracuseStep 3214619 = 4821929) B4821929
theorem B2143079 : Blo 1427533 2143079 := bstep (se 1 (by rfl) ⟨1607309, by rfl⟩ : syracuseStep 2143079 = 3214619) B3214619
theorem B1428719 : Blo 1427533 1428719 := bstep (se 1 (by rfl) ⟨1071539, by rfl⟩ : syracuseStep 1428719 = 2143079) B2143079

theorem C0 (j : ℕ) (h1 : 356883 ≤ j) (h2 : j ≤ 357382) : Blo 1427533 (4 * j + 3) := by
  interval_cases j
  · exact B1427535
  · exact B1427539
  · exact B1427543
  · exact B1427547
  · exact B1427551
  · exact B1427555
  · exact B1427559
  · exact B1427563
  · exact B1427567
  · exact B1427571
  · exact B1427575
  · exact B1427579
  · exact B1427583
  · exact B1427587
  · exact B1427591
  · exact B1427595
  · exact B1427599
  · exact B1427603
  · exact B1427607
  · exact B1427611
  · exact B1427615
  · exact B1427619
  · exact B1427623
  · exact B1427627
  · exact B1427631
  · exact B1427635
  · exact B1427639
  · exact B1427643
  · exact B1427647
  · exact B1427651
  · exact B1427655
  · exact B1427659
  · exact B1427663
  · exact B1427667
  · exact B1427671
  · exact B1427675
  · exact B1427679
  · exact B1427683
  · exact B1427687
  · exact B1427691
  · exact B1427695
  · exact B1427699
  · exact B1427703
  · exact B1427707
  · exact B1427711
  · exact B1427715
  · exact B1427719
  · exact B1427723
  · exact B1427727
  · exact B1427731
  · exact B1427735
  · exact B1427739
  · exact B1427743
  · exact B1427747
  · exact B1427751
  · exact B1427755
  · exact B1427759
  · exact B1427763
  · exact B1427767
  · exact B1427771
  · exact B1427775
  · exact B1427779
  · exact B1427783
  · exact B1427787
  · exact B1427791
  · exact B1427795
  · exact B1427799
  · exact B1427803
  · exact B1427807
  · exact B1427811
  · exact B1427815
  · exact B1427819
  · exact B1427823
  · exact B1427827
  · exact B1427831
  · exact B1427835
  · exact B1427839
  · exact B1427843
  · exact B1427847
  · exact B1427851
  · exact B1427855
  · exact B1427859
  · exact B1427863
  · exact B1427867
  · exact B1427871
  · exact B1427875
  · exact B1427879
  · exact B1427883
  · exact B1427887
  · exact B1427891
  · exact B1427895
  · exact B1427899
  · exact B1427903
  · exact B1427907
  · exact B1427911
  · exact B1427915
  · exact B1427919
  · exact B1427923
  · exact B1427927
  · exact B1427931
  · exact B1427935
  · exact B1427939
  · exact B1427943
  · exact B1427947
  · exact B1427951
  · exact B1427955
  · exact B1427959
  · exact B1427963
  · exact B1427967
  · exact B1427971
  · exact B1427975
  · exact B1427979
  · exact B1427983
  · exact B1427987
  · exact B1427991
  · exact B1427995
  · exact B1427999
  · exact B1428003
  · exact B1428007
  · exact B1428011
  · exact B1428015
  · exact B1428019
  · exact B1428023
  · exact B1428027
  · exact B1428031
  · exact B1428035
  · exact B1428039
  · exact B1428043
  · exact B1428047
  · exact B1428051
  · exact B1428055
  · exact B1428059
  · exact B1428063
  · exact B1428067
  · exact B1428071
  · exact B1428075
  · exact B1428079
  · exact B1428083
  · exact B1428087
  · exact B1428091
  · exact B1428095
  · exact B1428099
  · exact B1428103
  · exact B1428107
  · exact B1428111
  · exact B1428115
  · exact B1428119
  · exact B1428123
  · exact B1428127
  · exact B1428131
  · exact B1428135
  · exact B1428139
  · exact B1428143
  · exact B1428147
  · exact B1428151
  · exact B1428155
  · exact B1428159
  · exact B1428163
  · exact B1428167
  · exact B1428171
  · exact B1428175
  · exact B1428179
  · exact B1428183
  · exact B1428187
  · exact B1428191
  · exact B1428195
  · exact B1428199
  · exact B1428203
  · exact B1428207
  · exact B1428211
  · exact B1428215
  · exact B1428219
  · exact B1428223
  · exact B1428227
  · exact B1428231
  · exact B1428235
  · exact B1428239
  · exact B1428243
  · exact B1428247
  · exact B1428251
  · exact B1428255
  · exact B1428259
  · exact B1428263
  · exact B1428267
  · exact B1428271
  · exact B1428275
  · exact B1428279
  · exact B1428283
  · exact B1428287
  · exact B1428291
  · exact B1428295
  · exact B1428299
  · exact B1428303
  · exact B1428307
  · exact B1428311
  · exact B1428315
  · exact B1428319
  · exact B1428323
  · exact B1428327
  · exact B1428331
  · exact B1428335
  · exact B1428339
  · exact B1428343
  · exact B1428347
  · exact B1428351
  · exact B1428355
  · exact B1428359
  · exact B1428363
  · exact B1428367
  · exact B1428371
  · exact B1428375
  · exact B1428379
  · exact B1428383
  · exact B1428387
  · exact B1428391
  · exact B1428395
  · exact B1428399
  · exact B1428403
  · exact B1428407
  · exact B1428411
  · exact B1428415
  · exact B1428419
  · exact B1428423
  · exact B1428427
  · exact B1428431
  · exact B1428435
  · exact B1428439
  · exact B1428443
  · exact B1428447
  · exact B1428451
  · exact B1428455
  · exact B1428459
  · exact B1428463
  · exact B1428467
  · exact B1428471
  · exact B1428475
  · exact B1428479
  · exact B1428483
  · exact B1428487
  · exact B1428491
  · exact B1428495
  · exact B1428499
  · exact B1428503
  · exact B1428507
  · exact B1428511
  · exact B1428515
  · exact B1428519
  · exact B1428523
  · exact B1428527
  · exact B1428531
  · exact B1428535
  · exact B1428539
  · exact B1428543
  · exact B1428547
  · exact B1428551
  · exact B1428555
  · exact B1428559
  · exact B1428563
  · exact B1428567
  · exact B1428571
  · exact B1428575
  · exact B1428579
  · exact B1428583
  · exact B1428587
  · exact B1428591
  · exact B1428595
  · exact B1428599
  · exact B1428603
  · exact B1428607
  · exact B1428611
  · exact B1428615
  · exact B1428619
  · exact B1428623
  · exact B1428627
  · exact B1428631
  · exact B1428635
  · exact B1428639
  · exact B1428643
  · exact B1428647
  · exact B1428651
  · exact B1428655
  · exact B1428659
  · exact B1428663
  · exact B1428667
  · exact B1428671
  · exact B1428675
  · exact B1428679
  · exact B1428683
  · exact B1428687
  · exact B1428691
  · exact B1428695
  · exact B1428699
  · exact B1428703
  · exact B1428707
  · exact B1428711
  · exact B1428715
  · exact B1428719
  · exact B1428723
  · exact B1428727
  · exact B1428731
  · exact B1428735
  · exact B1428739
  · exact B1428743
  · exact B1428747
  · exact B1428751
  · exact B1428755
  · exact B1428759
  · exact B1428763
  · exact B1428767
  · exact B1428771
  · exact B1428775
  · exact B1428779
  · exact B1428783
  · exact B1428787
  · exact B1428791
  · exact B1428795
  · exact B1428799
  · exact B1428803
  · exact B1428807
  · exact B1428811
  · exact B1428815
  · exact B1428819
  · exact B1428823
  · exact B1428827
  · exact B1428831
  · exact B1428835
  · exact B1428839
  · exact B1428843
  · exact B1428847
  · exact B1428851
  · exact B1428855
  · exact B1428859
  · exact B1428863
  · exact B1428867
  · exact B1428871
  · exact B1428875
  · exact B1428879
  · exact B1428883
  · exact B1428887
  · exact B1428891
  · exact B1428895
  · exact B1428899
  · exact B1428903
  · exact B1428907
  · exact B1428911
  · exact B1428915
  · exact B1428919
  · exact B1428923
  · exact B1428927
  · exact B1428931
  · exact B1428935
  · exact B1428939
  · exact B1428943
  · exact B1428947
  · exact B1428951
  · exact B1428955
  · exact B1428959
  · exact B1428963
  · exact B1428967
  · exact B1428971
  · exact B1428975
  · exact B1428979
  · exact B1428983
  · exact B1428987
  · exact B1428991
  · exact B1428995
  · exact B1428999
  · exact B1429003
  · exact B1429007
  · exact B1429011
  · exact B1429015
  · exact B1429019
  · exact B1429023
  · exact B1429027
  · exact B1429031
  · exact B1429035
  · exact B1429039
  · exact B1429043
  · exact B1429047
  · exact B1429051
  · exact B1429055
  · exact B1429059
  · exact B1429063
  · exact B1429067
  · exact B1429071
  · exact B1429075
  · exact B1429079
  · exact B1429083
  · exact B1429087
  · exact B1429091
  · exact B1429095
  · exact B1429099
  · exact B1429103
  · exact B1429107
  · exact B1429111
  · exact B1429115
  · exact B1429119
  · exact B1429123
  · exact B1429127
  · exact B1429131
  · exact B1429135
  · exact B1429139
  · exact B1429143
  · exact B1429147
  · exact B1429151
  · exact B1429155
  · exact B1429159
  · exact B1429163
  · exact B1429167
  · exact B1429171
  · exact B1429175
  · exact B1429179
  · exact B1429183
  · exact B1429187
  · exact B1429191
  · exact B1429195
  · exact B1429199
  · exact B1429203
  · exact B1429207
  · exact B1429211
  · exact B1429215
  · exact B1429219
  · exact B1429223
  · exact B1429227
  · exact B1429231
  · exact B1429235
  · exact B1429239
  · exact B1429243
  · exact B1429247
  · exact B1429251
  · exact B1429255
  · exact B1429259
  · exact B1429263
  · exact B1429267
  · exact B1429271
  · exact B1429275
  · exact B1429279
  · exact B1429283
  · exact B1429287
  · exact B1429291
  · exact B1429295
  · exact B1429299
  · exact B1429303
  · exact B1429307
  · exact B1429311
  · exact B1429315
  · exact B1429319
  · exact B1429323
  · exact B1429327
  · exact B1429331
  · exact B1429335
  · exact B1429339
  · exact B1429343
  · exact B1429347
  · exact B1429351
  · exact B1429355
  · exact B1429359
  · exact B1429363
  · exact B1429367
  · exact B1429371
  · exact B1429375
  · exact B1429379
  · exact B1429383
  · exact B1429387
  · exact B1429391
  · exact B1429395
  · exact B1429399
  · exact B1429403
  · exact B1429407
  · exact B1429411
  · exact B1429415
  · exact B1429419
  · exact B1429423
  · exact B1429427
  · exact B1429431
  · exact B1429435
  · exact B1429439
  · exact B1429443
  · exact B1429447
  · exact B1429451
  · exact B1429455
  · exact B1429459
  · exact B1429463
  · exact B1429467
  · exact B1429471
  · exact B1429475
  · exact B1429479
  · exact B1429483
  · exact B1429487
  · exact B1429491
  · exact B1429495
  · exact B1429499
  · exact B1429503
  · exact B1429507
  · exact B1429511
  · exact B1429515
  · exact B1429519
  · exact B1429523
  · exact B1429527
  · exact B1429531

theorem solution (m : ℕ) (hlo : 1427533 ≤ m) (hhi : m ≤ 1429533) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 356883 ≤ j := by omega
    have hj2 : j ≤ 357382 := by omega
    have hb : Blo 1427533 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
