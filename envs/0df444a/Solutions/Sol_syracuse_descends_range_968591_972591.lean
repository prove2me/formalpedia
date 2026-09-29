-- Prove2me | solution 1 for syracuse_descends_range_968591_972591
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:22:04.440513+00:00
-- url     : https://prove2.me/submissions/a1c953a9-b1bb-4576-a166-172a3d2846cb

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


theorem B983053 : Blo 968591 983053 := bbase (se 3 (by rfl) ⟨184322, by rfl⟩ : syracuseStep 983053 = 368645) (by norm_num)
theorem B2457661 : Blo 968591 2457661 := bbase (se 3 (by rfl) ⟨460811, by rfl⟩ : syracuseStep 2457661 = 921623) (by norm_num)
theorem B1638461 : Blo 968591 1638461 := bbase (se 3 (by rfl) ⟨307211, by rfl⟩ : syracuseStep 1638461 = 614423) (by norm_num)
theorem B3113093 : Blo 968591 3113093 := bbase (se 4 (by rfl) ⟨291852, by rfl⟩ : syracuseStep 3113093 = 583705) (by norm_num)
theorem B2457773 : Blo 968591 2457773 := bbase (se 3 (by rfl) ⟨460832, by rfl⟩ : syracuseStep 2457773 = 921665) (by norm_num)
theorem B1638589 : Blo 968591 1638589 := bbase (se 3 (by rfl) ⟨307235, by rfl⟩ : syracuseStep 1638589 = 614471) (by norm_num)
theorem B1245413 : Blo 968591 1245413 := bbase (se 4 (by rfl) ⟨116757, by rfl⟩ : syracuseStep 1245413 = 233515) (by norm_num)
theorem B1638677 : Blo 968591 1638677 := bbase (se 6 (by rfl) ⟨38406, by rfl⟩ : syracuseStep 1638677 = 76813) (by norm_num)
theorem B2457965 : Blo 968591 2457965 := bbase (se 3 (by rfl) ⟨460868, by rfl⟩ : syracuseStep 2457965 = 921737) (by norm_num)
theorem B1573237 : Blo 968591 1573237 := bbase (se 5 (by rfl) ⟨73745, by rfl⟩ : syracuseStep 1573237 = 147491) (by norm_num)
theorem B3277205 : Blo 968591 3277205 := bbase (se 6 (by rfl) ⟨76809, by rfl⟩ : syracuseStep 3277205 = 153619) (by norm_num)
theorem B1638805 : Blo 968591 1638805 := bbase (se 6 (by rfl) ⟨38409, by rfl⟩ : syracuseStep 1638805 = 76819) (by norm_num)
theorem B1638893 : Blo 968591 1638893 := bbase (se 3 (by rfl) ⟨307292, by rfl⟩ : syracuseStep 1638893 = 614585) (by norm_num)
theorem B1639021 : Blo 968591 1639021 := bbase (se 3 (by rfl) ⟨307316, by rfl⟩ : syracuseStep 1639021 = 614633) (by norm_num)
theorem B983737 : Blo 968591 983737 := bbase (se 2 (by rfl) ⟨368901, by rfl⟩ : syracuseStep 983737 = 737803) (by norm_num)
theorem B2458309 : Blo 968591 2458309 := bbase (se 4 (by rfl) ⟨230466, by rfl⟩ : syracuseStep 2458309 = 460933) (by norm_num)
theorem B1639109 : Blo 968591 1639109 := bbase (se 4 (by rfl) ⟨153666, by rfl⟩ : syracuseStep 1639109 = 307333) (by norm_num)
theorem B2327285 : Blo 968591 2327285 := bbase (se 5 (by rfl) ⟨109091, by rfl⟩ : syracuseStep 2327285 = 218183) (by norm_num)
theorem B2458421 : Blo 968591 2458421 := bbase (se 5 (by rfl) ⟨115238, by rfl⟩ : syracuseStep 2458421 = 230477) (by norm_num)
theorem B3277637 : Blo 968591 3277637 := bbase (se 4 (by rfl) ⟨307278, by rfl⟩ : syracuseStep 3277637 = 614557) (by norm_num)
theorem B1639237 : Blo 968591 1639237 := bbase (se 4 (by rfl) ⟨153678, by rfl⟩ : syracuseStep 1639237 = 307357) (by norm_num)
theorem B1639325 : Blo 968591 1639325 := bbase (se 3 (by rfl) ⟨307373, by rfl⟩ : syracuseStep 1639325 = 614747) (by norm_num)
theorem B1967021 : Blo 968591 1967021 := bbase (se 3 (by rfl) ⟨368816, by rfl⟩ : syracuseStep 1967021 = 737633) (by norm_num)
theorem B1475509 : Blo 968591 1475509 := bbase (se 5 (by rfl) ⟨69164, by rfl⟩ : syracuseStep 1475509 = 138329) (by norm_num)
theorem B1967053 : Blo 968591 1967053 := bbase (se 3 (by rfl) ⟨368822, by rfl⟩ : syracuseStep 1967053 = 737645) (by norm_num)
theorem B4916213 : Blo 968591 4916213 := bbase (se 5 (by rfl) ⟨230447, by rfl⟩ : syracuseStep 4916213 = 460895) (by norm_num)
theorem B2458613 : Blo 968591 2458613 := bbase (se 5 (by rfl) ⟨115247, by rfl⟩ : syracuseStep 2458613 = 230495) (by norm_num)
theorem B9339893 : Blo 968591 9339893 := bbase (se 5 (by rfl) ⟨437807, by rfl⟩ : syracuseStep 9339893 = 875615) (by norm_num)
theorem B1639453 : Blo 968591 1639453 := bbase (se 3 (by rfl) ⟨307397, by rfl⟩ : syracuseStep 1639453 = 614795) (by norm_num)
theorem B1639541 : Blo 968591 1639541 := bbase (se 5 (by rfl) ⟨76853, by rfl⟩ : syracuseStep 1639541 = 153707) (by norm_num)
theorem B1246357 : Blo 968591 1246357 := bbase (se 6 (by rfl) ⟨29211, by rfl⟩ : syracuseStep 1246357 = 58423) (by norm_num)
theorem B3278069 : Blo 968591 3278069 := bbase (se 5 (by rfl) ⟨153659, by rfl⟩ : syracuseStep 3278069 = 307319) (by norm_num)
theorem B1639669 : Blo 968591 1639669 := bbase (se 5 (by rfl) ⟨76859, by rfl⟩ : syracuseStep 1639669 = 153719) (by norm_num)
theorem B2458957 : Blo 968591 2458957 := bbase (se 3 (by rfl) ⟨461054, by rfl⟩ : syracuseStep 2458957 = 922109) (by norm_num)
theorem B1639757 : Blo 968591 1639757 := bbase (se 3 (by rfl) ⟨307454, by rfl⟩ : syracuseStep 1639757 = 614909) (by norm_num)
theorem B1181077 : Blo 968591 1181077 := bbase (se 6 (by rfl) ⟨27681, by rfl⟩ : syracuseStep 1181077 = 55363) (by norm_num)
theorem B2459069 : Blo 968591 2459069 := bbase (se 3 (by rfl) ⟨461075, by rfl⟩ : syracuseStep 2459069 = 922151) (by norm_num)
theorem B1639885 : Blo 968591 1639885 := bbase (se 3 (by rfl) ⟨307478, by rfl⟩ : syracuseStep 1639885 = 614957) (by norm_num)
theorem B13469141 : Blo 968591 13469141 := bbase (se 7 (by rfl) ⟨157841, by rfl⟩ : syracuseStep 13469141 = 315683) (by norm_num)
theorem B984565 : Blo 968591 984565 := bbase (se 5 (by rfl) ⟨46151, by rfl⟩ : syracuseStep 984565 = 92303) (by norm_num)
theorem B1639973 : Blo 968591 1639973 := bbase (se 4 (by rfl) ⟨153747, by rfl⟩ : syracuseStep 1639973 = 307495) (by norm_num)
theorem B2459261 : Blo 968591 2459261 := bbase (se 3 (by rfl) ⟨461111, by rfl⟩ : syracuseStep 2459261 = 922223) (by norm_num)
theorem B3278501 : Blo 968591 3278501 := bbase (se 4 (by rfl) ⟨307359, by rfl⟩ : syracuseStep 3278501 = 614719) (by norm_num)
theorem B1640101 : Blo 968591 1640101 := bbase (se 4 (by rfl) ⟨153759, by rfl⟩ : syracuseStep 1640101 = 307519) (by norm_num)
theorem B1640189 : Blo 968591 1640189 := bbase (se 3 (by rfl) ⟨307535, by rfl⟩ : syracuseStep 1640189 = 615071) (by norm_num)
theorem B5605141 : Blo 968591 5605141 := bbase (se 6 (by rfl) ⟨131370, by rfl⟩ : syracuseStep 5605141 = 262741) (by norm_num)
theorem B1050397 : Blo 968591 1050397 := bbase (se 3 (by rfl) ⟨196949, by rfl⟩ : syracuseStep 1050397 = 393899) (by norm_num)
theorem B1640317 : Blo 968591 1640317 := bbase (se 3 (by rfl) ⟨307559, by rfl⟩ : syracuseStep 1640317 = 615119) (by norm_num)
theorem B2459605 : Blo 968591 2459605 := bbase (se 7 (by rfl) ⟨28823, by rfl⟩ : syracuseStep 2459605 = 57647) (by norm_num)
theorem B1640405 : Blo 968591 1640405 := bbase (se 7 (by rfl) ⟨19223, by rfl⟩ : syracuseStep 1640405 = 38447) (by norm_num)
theorem B2459717 : Blo 968591 2459717 := bbase (se 4 (by rfl) ⟨230598, by rfl⟩ : syracuseStep 2459717 = 461197) (by norm_num)
theorem B3278933 : Blo 968591 3278933 := bbase (se 8 (by rfl) ⟨19212, by rfl⟩ : syracuseStep 3278933 = 38425) (by norm_num)
theorem B1640533 : Blo 968591 1640533 := bbase (se 8 (by rfl) ⟨9612, by rfl⟩ : syracuseStep 1640533 = 19225) (by norm_num)
theorem B1968221 : Blo 968591 1968221 := bbase (se 3 (by rfl) ⟨369041, by rfl⟩ : syracuseStep 1968221 = 738083) (by norm_num)
theorem B1476725 : Blo 968591 1476725 := bbase (se 5 (by rfl) ⟨69221, by rfl⟩ : syracuseStep 1476725 = 138443) (by norm_num)
theorem B2492549 : Blo 968591 2492549 := bbase (se 4 (by rfl) ⟨233676, by rfl⟩ : syracuseStep 2492549 = 467353) (by norm_num)
theorem B1640621 : Blo 968591 1640621 := bbase (se 3 (by rfl) ⟨307616, by rfl⟩ : syracuseStep 1640621 = 615233) (by norm_num)
theorem B4917509 : Blo 968591 4917509 := bbase (se 4 (by rfl) ⟨461016, by rfl⟩ : syracuseStep 4917509 = 922033) (by norm_num)
theorem B2459909 : Blo 968591 2459909 := bbase (se 4 (by rfl) ⟨230616, by rfl⟩ : syracuseStep 2459909 = 461233) (by norm_num)
theorem B1640749 : Blo 968591 1640749 := bbase (se 3 (by rfl) ⟨307640, by rfl⟩ : syracuseStep 1640749 = 615281) (by norm_num)
theorem B4983125 : Blo 968591 4983125 := bbase (se 10 (by rfl) ⟨7299, by rfl⟩ : syracuseStep 4983125 = 14599) (by norm_num)
theorem B1640837 : Blo 968591 1640837 := bbase (se 4 (by rfl) ⟨153828, by rfl⟩ : syracuseStep 1640837 = 307657) (by norm_num)
theorem B3279365 : Blo 968591 3279365 := bbase (se 4 (by rfl) ⟨307440, by rfl⟩ : syracuseStep 3279365 = 614881) (by norm_num)
theorem B1640965 : Blo 968591 1640965 := bbase (se 4 (by rfl) ⟨153840, by rfl⟩ : syracuseStep 1640965 = 307681) (by norm_num)
theorem B2460253 : Blo 968591 2460253 := bbase (se 3 (by rfl) ⟨461297, by rfl⟩ : syracuseStep 2460253 = 922595) (by norm_num)
theorem B1641053 : Blo 968591 1641053 := bbase (se 3 (by rfl) ⟨307697, by rfl⟩ : syracuseStep 1641053 = 615395) (by norm_num)
theorem B985765 : Blo 968591 985765 := bbase (se 4 (by rfl) ⟨92415, by rfl⟩ : syracuseStep 985765 = 184831) (by norm_num)
theorem B985789 : Blo 968591 985789 := bbase (se 3 (by rfl) ⟨184835, by rfl⟩ : syracuseStep 985789 = 369671) (by norm_num)
theorem B2460365 : Blo 968591 2460365 := bbase (se 3 (by rfl) ⟨461318, by rfl⟩ : syracuseStep 2460365 = 922637) (by norm_num)
theorem B1641181 : Blo 968591 1641181 := bbase (se 3 (by rfl) ⟨307721, by rfl⟩ : syracuseStep 1641181 = 615443) (by norm_num)
theorem B2460557 : Blo 968591 2460557 := bbase (se 3 (by rfl) ⟨461354, by rfl⟩ : syracuseStep 2460557 = 922709) (by norm_num)
theorem B1182637 : Blo 968591 1182637 := bbase (se 3 (by rfl) ⟨221744, by rfl⟩ : syracuseStep 1182637 = 443489) (by norm_num)
theorem B3279797 : Blo 968591 3279797 := bbase (se 5 (by rfl) ⟨153740, by rfl⟩ : syracuseStep 3279797 = 307481) (by norm_num)
theorem B1477693 : Blo 968591 1477693 := bbase (se 3 (by rfl) ⟨277067, by rfl⟩ : syracuseStep 1477693 = 554135) (by norm_num)
theorem B7376021 : Blo 968591 7376021 := bbase (se 6 (by rfl) ⟨172875, by rfl⟩ : syracuseStep 7376021 = 345751) (by norm_num)
theorem B2100421 : Blo 968591 2100421 := bbase (se 4 (by rfl) ⟨196914, by rfl⟩ : syracuseStep 2100421 = 393829) (by norm_num)
theorem B1969373 : Blo 968591 1969373 := bbase (se 3 (by rfl) ⟨369257, by rfl⟩ : syracuseStep 1969373 = 738515) (by norm_num)
theorem B2460901 : Blo 968591 2460901 := bbase (se 4 (by rfl) ⟨230709, by rfl⟩ : syracuseStep 2460901 = 461419) (by norm_num)
theorem B2461013 : Blo 968591 2461013 := bbase (se 11 (by rfl) ⟨1802, by rfl⟩ : syracuseStep 2461013 = 3605) (by norm_num)
theorem B3280229 : Blo 968591 3280229 := bbase (se 4 (by rfl) ⟨307521, by rfl⟩ : syracuseStep 3280229 = 615043) (by norm_num)
theorem B1379701 : Blo 968591 1379701 := bbase (se 5 (by rfl) ⟨64673, by rfl⟩ : syracuseStep 1379701 = 129347) (by norm_num)
theorem B1052029 : Blo 968591 1052029 := bbase (se 3 (by rfl) ⟨197255, by rfl⟩ : syracuseStep 1052029 = 394511) (by norm_num)
theorem B4918805 : Blo 968591 4918805 := bbase (se 6 (by rfl) ⟨115284, by rfl⟩ : syracuseStep 4918805 = 230569) (by norm_num)
theorem B2461205 : Blo 968591 2461205 := bbase (se 6 (by rfl) ⟨57684, by rfl⟩ : syracuseStep 2461205 = 115369) (by norm_num)
theorem B9473557 : Blo 968591 9473557 := bbase (se 6 (by rfl) ⟨222036, by rfl⟩ : syracuseStep 9473557 = 444073) (by norm_num)
theorem B2428453 : Blo 968591 2428453 := bbase (se 4 (by rfl) ⟨227667, by rfl⟩ : syracuseStep 2428453 = 455335) (by norm_num)
theorem B2330245 : Blo 968591 2330245 := bbase (se 4 (by rfl) ⟨218460, by rfl⟩ : syracuseStep 2330245 = 436921) (by norm_num)
theorem B3280661 : Blo 968591 3280661 := bbase (se 6 (by rfl) ⟨76890, by rfl⟩ : syracuseStep 3280661 = 153781) (by norm_num)
theorem B8294197 : Blo 968591 8294197 := bbase (se 5 (by rfl) ⟨388790, by rfl⟩ : syracuseStep 8294197 = 777581) (by norm_num)
theorem B2330437 : Blo 968591 2330437 := bbase (se 4 (by rfl) ⟨218478, by rfl⟩ : syracuseStep 2330437 = 436957) (by norm_num)
theorem B1052497 : Blo 968591 1052497 := bbase (se 2 (by rfl) ⟨394686, by rfl⟩ : syracuseStep 1052497 = 789373) (by norm_num)
theorem B1838933 : Blo 968591 1838933 := bbase (se 9 (by rfl) ⟨5387, by rfl⟩ : syracuseStep 1838933 = 10775) (by norm_num)
theorem B2330477 : Blo 968591 2330477 := bbase (se 3 (by rfl) ⟨436964, by rfl⟩ : syracuseStep 2330477 = 873929) (by norm_num)
theorem B2461549 : Blo 968591 2461549 := bbase (se 3 (by rfl) ⟨461540, by rfl⟩ : syracuseStep 2461549 = 923081) (by norm_num)
theorem B4657013 : Blo 968591 4657013 := bbase (se 5 (by rfl) ⟨218297, by rfl⟩ : syracuseStep 4657013 = 436595) (by norm_num)
theorem B2461661 : Blo 968591 2461661 := bbase (se 3 (by rfl) ⟨461561, by rfl⟩ : syracuseStep 2461661 = 923123) (by norm_num)
theorem B3313685 : Blo 968591 3313685 := bbase (se 6 (by rfl) ⟨77664, by rfl⟩ : syracuseStep 3313685 = 155329) (by norm_num)
theorem B1183777 : Blo 968591 1183777 := bbase (se 2 (by rfl) ⟨443916, by rfl⟩ : syracuseStep 1183777 = 887833) (by norm_num)
theorem B12423253 : Blo 968591 12423253 := bbase (se 8 (by rfl) ⟨72792, by rfl⟩ : syracuseStep 12423253 = 145585) (by norm_num)
theorem B1380493 : Blo 968591 1380493 := bbase (se 3 (by rfl) ⟨258842, by rfl⟩ : syracuseStep 1380493 = 517685) (by norm_num)
theorem B2330765 : Blo 968591 2330765 := bbase (se 3 (by rfl) ⟨437018, by rfl⟩ : syracuseStep 2330765 = 874037) (by norm_num)
theorem B2461853 : Blo 968591 2461853 := bbase (se 3 (by rfl) ⟨461597, by rfl⟩ : syracuseStep 2461853 = 923195) (by norm_num)
theorem B3281093 : Blo 968591 3281093 := bbase (se 4 (by rfl) ⟨307602, by rfl⟩ : syracuseStep 3281093 = 615205) (by norm_num)
theorem B8392949 : Blo 968591 8392949 := bbase (se 5 (by rfl) ⟨393419, by rfl⟩ : syracuseStep 8392949 = 786839) (by norm_num)
theorem B2363717 : Blo 968591 2363717 := bbase (se 4 (by rfl) ⟨221598, by rfl⟩ : syracuseStep 2363717 = 443197) (by norm_num)
theorem B1380829 : Blo 968591 1380829 := bbase (se 3 (by rfl) ⟨258905, by rfl⟩ : syracuseStep 1380829 = 517811) (by norm_num)
theorem B3740165 : Blo 968591 3740165 := bbase (se 4 (by rfl) ⟨350640, by rfl⟩ : syracuseStep 3740165 = 701281) (by norm_num)
theorem B2069005 : Blo 968591 2069005 := bbase (se 3 (by rfl) ⟨387938, by rfl⟩ : syracuseStep 2069005 = 775877) (by norm_num)
theorem B1839685 : Blo 968591 1839685 := bbase (se 4 (by rfl) ⟨172470, by rfl⟩ : syracuseStep 1839685 = 344941) (by norm_num)
theorem B2953829 : Blo 968591 2953829 := bbase (se 4 (by rfl) ⟨276921, by rfl⟩ : syracuseStep 2953829 = 553843) (by norm_num)
theorem B3281525 : Blo 968591 3281525 := bbase (se 5 (by rfl) ⟨153821, by rfl⟩ : syracuseStep 3281525 = 307643) (by norm_num)
theorem B1381045 : Blo 968591 1381045 := bbase (se 5 (by rfl) ⟨64736, by rfl⟩ : syracuseStep 1381045 = 129473) (by norm_num)
theorem B1839829 : Blo 968591 1839829 := bbase (se 7 (by rfl) ⟨21560, by rfl⟩ : syracuseStep 1839829 = 43121) (by norm_num)
theorem B4920101 : Blo 968591 4920101 := bbase (se 4 (by rfl) ⟨461259, by rfl⟩ : syracuseStep 4920101 = 922519) (by norm_num)
theorem B1839989 : Blo 968591 1839989 := bbase (se 5 (by rfl) ⟨86249, by rfl⟩ : syracuseStep 1839989 = 172499) (by norm_num)
theorem B2069381 : Blo 968591 2069381 := bbase (se 4 (by rfl) ⟨194004, by rfl⟩ : syracuseStep 2069381 = 388009) (by norm_num)
theorem B1840133 : Blo 968591 1840133 := bbase (se 4 (by rfl) ⟨172512, by rfl⟩ : syracuseStep 1840133 = 345025) (by norm_num)
theorem B3281957 : Blo 968591 3281957 := bbase (se 4 (by rfl) ⟨307683, by rfl⟩ : syracuseStep 3281957 = 615367) (by norm_num)
theorem B1381421 : Blo 968591 1381421 := bbase (se 3 (by rfl) ⟨259016, by rfl⟩ : syracuseStep 1381421 = 518033) (by norm_num)
theorem B1316125 : Blo 968591 1316125 := bbase (se 3 (by rfl) ⟨246773, by rfl⟩ : syracuseStep 1316125 = 493547) (by norm_num)
theorem B1840421 : Blo 968591 1840421 := bbase (se 4 (by rfl) ⟨172539, by rfl⟩ : syracuseStep 1840421 = 345079) (by norm_num)
theorem B1840573 : Blo 968591 1840573 := bbase (se 3 (by rfl) ⟨345107, by rfl⟩ : syracuseStep 1840573 = 690215) (by norm_num)
theorem B3282389 : Blo 968591 3282389 := bbase (se 7 (by rfl) ⟨38465, by rfl⟩ : syracuseStep 3282389 = 76931) (by norm_num)
theorem B1119853 : Blo 968591 1119853 := bbase (se 3 (by rfl) ⟨209972, by rfl⟩ : syracuseStep 1119853 = 419945) (by norm_num)
theorem B1840877 : Blo 968591 1840877 := bbase (se 3 (by rfl) ⟨345164, by rfl⟩ : syracuseStep 1840877 = 690329) (by norm_num)
theorem B8296181 : Blo 968591 8296181 := bbase (se 5 (by rfl) ⟨388883, by rfl⟩ : syracuseStep 8296181 = 777767) (by norm_num)
theorem B4659029 : Blo 968591 4659029 := bbase (se 9 (by rfl) ⟨13649, by rfl⟩ : syracuseStep 4659029 = 27299) (by norm_num)
theorem B4659221 : Blo 968591 4659221 := bbase (se 6 (by rfl) ⟨109200, by rfl⟩ : syracuseStep 4659221 = 218401) (by norm_num)
theorem B4921397 : Blo 968591 4921397 := bbase (se 5 (by rfl) ⟨230690, by rfl⟩ : syracuseStep 4921397 = 461381) (by norm_num)
theorem B2627797 : Blo 968591 2627797 := bbase (se 7 (by rfl) ⟨30794, by rfl⟩ : syracuseStep 2627797 = 61589) (by norm_num)
theorem B2758981 : Blo 968591 2758981 := bbase (se 4 (by rfl) ⟨258654, by rfl⟩ : syracuseStep 2758981 = 517309) (by norm_num)
theorem B1382845 : Blo 968591 1382845 := bbase (se 3 (by rfl) ⟨259283, by rfl⟩ : syracuseStep 1382845 = 518567) (by norm_num)
theorem B1841629 : Blo 968591 1841629 := bbase (se 3 (by rfl) ⟨345305, by rfl⟩ : syracuseStep 1841629 = 690611) (by norm_num)
theorem B2071021 : Blo 968591 2071021 := bbase (se 3 (by rfl) ⟨388316, by rfl⟩ : syracuseStep 2071021 = 776633) (by norm_num)
theorem B1841773 : Blo 968591 1841773 := bbase (se 3 (by rfl) ⟨345332, by rfl⟩ : syracuseStep 1841773 = 690665) (by norm_num)
theorem B9837173 : Blo 968591 9837173 := bbase (se 5 (by rfl) ⟨461117, by rfl⟩ : syracuseStep 9837173 = 922235) (by norm_num)
theorem B1841933 : Blo 968591 1841933 := bbase (se 3 (by rfl) ⟨345362, by rfl⟩ : syracuseStep 1841933 = 690725) (by norm_num)
theorem B1842077 : Blo 968591 1842077 := bbase (se 3 (by rfl) ⟨345389, by rfl⟩ : syracuseStep 1842077 = 690779) (by norm_num)
theorem B2104301 : Blo 968591 2104301 := bbase (se 3 (by rfl) ⟨394556, by rfl⟩ : syracuseStep 2104301 = 789113) (by norm_num)
theorem B1776629 : Blo 968591 1776629 := bbase (se 5 (by rfl) ⟨83279, by rfl⟩ : syracuseStep 1776629 = 166559) (by norm_num)
theorem B1383437 : Blo 968591 1383437 := bbase (se 3 (by rfl) ⟨259394, by rfl⟩ : syracuseStep 1383437 = 518789) (by norm_num)
theorem B2104397 : Blo 968591 2104397 := bbase (se 3 (by rfl) ⟨394574, by rfl⟩ : syracuseStep 2104397 = 789149) (by norm_num)
theorem B1383517 : Blo 968591 1383517 := bbase (se 3 (by rfl) ⟨259409, by rfl⟩ : syracuseStep 1383517 = 518819) (by norm_num)
theorem B3153077 : Blo 968591 3153077 := bbase (se 5 (by rfl) ⟨147800, by rfl⟩ : syracuseStep 3153077 = 295601) (by norm_num)
theorem B1842365 : Blo 968591 1842365 := bbase (se 3 (by rfl) ⟨345443, by rfl⟩ : syracuseStep 1842365 = 690887) (by norm_num)
theorem B1383637 : Blo 968591 1383637 := bbase (se 7 (by rfl) ⟨16214, by rfl⟩ : syracuseStep 1383637 = 32429) (by norm_num)
theorem B2956517 : Blo 968591 2956517 := bbase (se 4 (by rfl) ⟨277173, by rfl⟩ : syracuseStep 2956517 = 554347) (by norm_num)
theorem B1383733 : Blo 968591 1383733 := bbase (se 5 (by rfl) ⟨64862, by rfl⟩ : syracuseStep 1383733 = 129725) (by norm_num)
theorem B4922693 : Blo 968591 4922693 := bbase (se 4 (by rfl) ⟨461502, by rfl⟩ : syracuseStep 4922693 = 923005) (by norm_num)
theorem B2694485 : Blo 968591 2694485 := bbase (se 11 (by rfl) ⟨1973, by rfl⟩ : syracuseStep 2694485 = 3947) (by norm_num)
theorem B1842517 : Blo 968591 1842517 := bbase (se 11 (by rfl) ⟨1349, by rfl⟩ : syracuseStep 1842517 = 2699) (by norm_num)
theorem B2071909 : Blo 968591 2071909 := bbase (se 4 (by rfl) ⟨194241, by rfl⟩ : syracuseStep 2071909 = 388483) (by norm_num)
theorem B2760085 : Blo 968591 2760085 := bbase (se 6 (by rfl) ⟨64689, by rfl⟩ : syracuseStep 2760085 = 129379) (by norm_num)
theorem B3677669 : Blo 968591 3677669 := bbase (se 4 (by rfl) ⟨344781, by rfl⟩ : syracuseStep 3677669 = 689563) (by norm_num)
theorem B2367029 : Blo 968591 2367029 := bbase (se 5 (by rfl) ⟨110954, by rfl⟩ : syracuseStep 2367029 = 221909) (by norm_num)
theorem B1842821 : Blo 968591 1842821 := bbase (se 4 (by rfl) ⟨172764, by rfl⟩ : syracuseStep 1842821 = 345529) (by norm_num)
theorem B2334349 : Blo 968591 2334349 := bbase (se 3 (by rfl) ⟨437690, by rfl⟩ : syracuseStep 2334349 = 875381) (by norm_num)
theorem B1121989 : Blo 968591 1121989 := bbase (se 4 (by rfl) ⟨105186, by rfl⟩ : syracuseStep 1121989 = 210373) (by norm_num)
theorem B5119685 : Blo 968591 5119685 := bbase (se 4 (by rfl) ⟨479970, by rfl⟩ : syracuseStep 5119685 = 959941) (by norm_num)
theorem B3677957 : Blo 968591 3677957 := bbase (se 4 (by rfl) ⟨344808, by rfl⟩ : syracuseStep 3677957 = 689617) (by norm_num)
theorem B1384229 : Blo 968591 1384229 := bbase (se 4 (by rfl) ⟨129771, by rfl⟩ : syracuseStep 1384229 = 259543) (by norm_num)
theorem B2072405 : Blo 968591 2072405 := bbase (se 9 (by rfl) ⟨6071, by rfl⟩ : syracuseStep 2072405 = 12143) (by norm_num)
theorem B4661317 : Blo 968591 4661317 := bbase (se 4 (by rfl) ⟨436998, by rfl⟩ : syracuseStep 4661317 = 873997) (by norm_num)
theorem B1089697 : Blo 968591 1089697 := bbase (se 2 (by rfl) ⟨408636, by rfl⟩ : syracuseStep 1089697 = 817273) (by norm_num)
theorem B1089733 : Blo 968591 1089733 := bbase (se 4 (by rfl) ⟨102162, by rfl⟩ : syracuseStep 1089733 = 204325) (by norm_num)
theorem B2957525 : Blo 968591 2957525 := bbase (se 7 (by rfl) ⟨34658, by rfl⟩ : syracuseStep 2957525 = 69317) (by norm_num)
theorem B1089769 : Blo 968591 1089769 := bbase (se 2 (by rfl) ⟨408663, by rfl⟩ : syracuseStep 1089769 = 817327) (by norm_num)
theorem B1089805 : Blo 968591 1089805 := bbase (se 3 (by rfl) ⟨204338, by rfl⟩ : syracuseStep 1089805 = 408677) (by norm_num)
theorem B2335013 : Blo 968591 2335013 := bbase (se 4 (by rfl) ⟨218907, by rfl⟩ : syracuseStep 2335013 = 437815) (by norm_num)
theorem B1089841 : Blo 968591 1089841 := bbase (se 2 (by rfl) ⟨408690, by rfl⟩ : syracuseStep 1089841 = 817381) (by norm_num)
theorem B1384781 : Blo 968591 1384781 := bbase (se 3 (by rfl) ⟨259646, by rfl⟩ : syracuseStep 1384781 = 519293) (by norm_num)
theorem B1089877 : Blo 968591 1089877 := bbase (se 10 (by rfl) ⟨1596, by rfl⟩ : syracuseStep 1089877 = 3193) (by norm_num)
theorem B1122665 : Blo 968591 1122665 := bbase (se 2 (by rfl) ⟨420999, by rfl⟩ : syracuseStep 1122665 = 841999) (by norm_num)
theorem B1843573 : Blo 968591 1843573 := bbase (se 5 (by rfl) ⟨86417, by rfl⟩ : syracuseStep 1843573 = 172835) (by norm_num)
theorem B1089913 : Blo 968591 1089913 := bbase (se 2 (by rfl) ⟨408717, by rfl⟩ : syracuseStep 1089913 = 817435) (by norm_num)
theorem B1089949 : Blo 968591 1089949 := bbase (se 3 (by rfl) ⟨204365, by rfl⟩ : syracuseStep 1089949 = 408731) (by norm_num)
theorem B1089985 : Blo 968591 1089985 := bbase (se 2 (by rfl) ⟨408744, by rfl⟩ : syracuseStep 1089985 = 817489) (by norm_num)
theorem B1090021 : Blo 968591 1090021 := bbase (se 4 (by rfl) ⟨102189, by rfl⟩ : syracuseStep 1090021 = 204379) (by norm_num)
theorem B1843717 : Blo 968591 1843717 := bbase (se 4 (by rfl) ⟨172848, by rfl⟩ : syracuseStep 1843717 = 345697) (by norm_num)
theorem B1090057 : Blo 968591 1090057 := bbase (se 2 (by rfl) ⟨408771, by rfl⟩ : syracuseStep 1090057 = 817543) (by norm_num)
theorem B1090093 : Blo 968591 1090093 := bbase (se 3 (by rfl) ⟨204392, by rfl⟩ : syracuseStep 1090093 = 408785) (by norm_num)
theorem B2335301 : Blo 968591 2335301 := bbase (se 4 (by rfl) ⟨218934, by rfl⟩ : syracuseStep 2335301 = 437869) (by norm_num)
theorem B1090129 : Blo 968591 1090129 := bbase (se 2 (by rfl) ⟨408798, by rfl⟩ : syracuseStep 1090129 = 817597) (by norm_num)
theorem B1090165 : Blo 968591 1090165 := bbase (se 5 (by rfl) ⟨51101, by rfl⟩ : syracuseStep 1090165 = 102203) (by norm_num)
theorem B1090201 : Blo 968591 1090201 := bbase (se 2 (by rfl) ⟨408825, by rfl⟩ : syracuseStep 1090201 = 817651) (by norm_num)
theorem B1843877 : Blo 968591 1843877 := bbase (se 4 (by rfl) ⟨172863, by rfl⟩ : syracuseStep 1843877 = 345727) (by norm_num)
theorem B2073269 : Blo 968591 2073269 := bbase (se 5 (by rfl) ⟨97184, by rfl⟩ : syracuseStep 2073269 = 194369) (by norm_num)
theorem B1090237 : Blo 968591 1090237 := bbase (se 3 (by rfl) ⟨204419, by rfl⟩ : syracuseStep 1090237 = 408839) (by norm_num)
theorem B1090273 : Blo 968591 1090273 := bbase (se 2 (by rfl) ⟨408852, by rfl⟩ : syracuseStep 1090273 = 817705) (by norm_num)
theorem B1090309 : Blo 968591 1090309 := bbase (se 4 (by rfl) ⟨102216, by rfl⟩ : syracuseStep 1090309 = 204433) (by norm_num)
theorem B1090345 : Blo 968591 1090345 := bbase (se 2 (by rfl) ⟨408879, by rfl⟩ : syracuseStep 1090345 = 817759) (by norm_num)
theorem B1844021 : Blo 968591 1844021 := bbase (se 5 (by rfl) ⟨86438, by rfl⟩ : syracuseStep 1844021 = 172877) (by norm_num)
theorem B2073413 : Blo 968591 2073413 := bbase (se 4 (by rfl) ⟨194382, by rfl⟩ : syracuseStep 2073413 = 388765) (by norm_num)
theorem B1090381 : Blo 968591 1090381 := bbase (se 3 (by rfl) ⟨204446, by rfl⟩ : syracuseStep 1090381 = 408893) (by norm_num)
theorem B1090417 : Blo 968591 1090417 := bbase (se 2 (by rfl) ⟨408906, by rfl⟩ : syracuseStep 1090417 = 817813) (by norm_num)
theorem B2761589 : Blo 968591 2761589 := bbase (se 5 (by rfl) ⟨129449, by rfl⟩ : syracuseStep 2761589 = 258899) (by norm_num)
theorem B1090453 : Blo 968591 1090453 := bbase (se 6 (by rfl) ⟨25557, by rfl⟩ : syracuseStep 1090453 = 51115) (by norm_num)
theorem B3679141 : Blo 968591 3679141 := bbase (se 4 (by rfl) ⟨344919, by rfl⟩ : syracuseStep 3679141 = 689839) (by norm_num)
theorem B1090489 : Blo 968591 1090489 := bbase (se 2 (by rfl) ⟨408933, by rfl⟩ : syracuseStep 1090489 = 817867) (by norm_num)
theorem B4137925 : Blo 968591 4137925 := bbase (se 4 (by rfl) ⟨387930, by rfl⟩ : syracuseStep 4137925 = 775861) (by norm_num)
theorem B4137941 : Blo 968591 4137941 := bbase (se 7 (by rfl) ⟨48491, by rfl⟩ : syracuseStep 4137941 = 96983) (by norm_num)
theorem B1090525 : Blo 968591 1090525 := bbase (se 3 (by rfl) ⟨204473, by rfl⟩ : syracuseStep 1090525 = 408947) (by norm_num)
theorem B1090561 : Blo 968591 1090561 := bbase (se 2 (by rfl) ⟨408960, by rfl⟩ : syracuseStep 1090561 = 817921) (by norm_num)
theorem B1090597 : Blo 968591 1090597 := bbase (se 4 (by rfl) ⟨102243, by rfl⟩ : syracuseStep 1090597 = 204487) (by norm_num)
theorem B6628405 : Blo 968591 6628405 := bbase (se 5 (by rfl) ⟨310706, by rfl⟩ : syracuseStep 6628405 = 621413) (by norm_num)
theorem B1090633 : Blo 968591 1090633 := bbase (se 2 (by rfl) ⟨408987, by rfl⟩ : syracuseStep 1090633 = 817975) (by norm_num)
theorem B1844309 : Blo 968591 1844309 := bbase (se 8 (by rfl) ⟨10806, by rfl⟩ : syracuseStep 1844309 = 21613) (by norm_num)
theorem B1090669 : Blo 968591 1090669 := bbase (se 3 (by rfl) ⟨204500, by rfl⟩ : syracuseStep 1090669 = 409001) (by norm_num)
theorem B1090705 : Blo 968591 1090705 := bbase (se 2 (by rfl) ⟨409014, by rfl⟩ : syracuseStep 1090705 = 818029) (by norm_num)
theorem B1090741 : Blo 968591 1090741 := bbase (se 5 (by rfl) ⟨51128, by rfl⟩ : syracuseStep 1090741 = 102257) (by norm_num)
theorem B3679445 : Blo 968591 3679445 := bbase (se 7 (by rfl) ⟨43118, by rfl⟩ : syracuseStep 3679445 = 86237) (by norm_num)
theorem B5252309 : Blo 968591 5252309 := bbase (se 7 (by rfl) ⟨61550, by rfl⟩ : syracuseStep 5252309 = 123101) (by norm_num)
theorem B1090777 : Blo 968591 1090777 := bbase (se 2 (by rfl) ⟨409041, by rfl⟩ : syracuseStep 1090777 = 818083) (by norm_num)
theorem B1844461 : Blo 968591 1844461 := bbase (se 3 (by rfl) ⟨345836, by rfl⟩ : syracuseStep 1844461 = 691673) (by norm_num)
theorem B1090813 : Blo 968591 1090813 := bbase (se 3 (by rfl) ⟨204527, by rfl⟩ : syracuseStep 1090813 = 409055) (by norm_num)
theorem B1090849 : Blo 968591 1090849 := bbase (se 2 (by rfl) ⟨409068, by rfl⟩ : syracuseStep 1090849 = 818137) (by norm_num)
theorem B1090885 : Blo 968591 1090885 := bbase (se 4 (by rfl) ⟨102270, by rfl⟩ : syracuseStep 1090885 = 204541) (by norm_num)
theorem B1090921 : Blo 968591 1090921 := bbase (se 2 (by rfl) ⟨409095, by rfl⟩ : syracuseStep 1090921 = 818191) (by norm_num)
theorem B1090957 : Blo 968591 1090957 := bbase (se 3 (by rfl) ⟨204554, by rfl⟩ : syracuseStep 1090957 = 409109) (by norm_num)
theorem B1090993 : Blo 968591 1090993 := bbase (se 2 (by rfl) ⟨409122, by rfl⟩ : syracuseStep 1090993 = 818245) (by norm_num)
theorem B1091029 : Blo 968591 1091029 := bbase (se 7 (by rfl) ⟨12785, by rfl⟩ : syracuseStep 1091029 = 25571) (by norm_num)
theorem B1091065 : Blo 968591 1091065 := bbase (se 2 (by rfl) ⟨409149, by rfl⟩ : syracuseStep 1091065 = 818299) (by norm_num)
theorem B1091101 : Blo 968591 1091101 := bbase (se 3 (by rfl) ⟨204581, by rfl⟩ : syracuseStep 1091101 = 409163) (by norm_num)
theorem B1844765 : Blo 968591 1844765 := bbase (se 3 (by rfl) ⟨345893, by rfl⟩ : syracuseStep 1844765 = 691787) (by norm_num)
theorem B2074157 : Blo 968591 2074157 := bbase (se 3 (by rfl) ⟨388904, by rfl⟩ : syracuseStep 2074157 = 777809) (by norm_num)
theorem B1091137 : Blo 968591 1091137 := bbase (se 2 (by rfl) ⟨409176, by rfl⟩ : syracuseStep 1091137 = 818353) (by norm_num)
theorem B1746517 : Blo 968591 1746517 := bbase (se 8 (by rfl) ⟨10233, by rfl⟩ : syracuseStep 1746517 = 20467) (by norm_num)
theorem B1091173 : Blo 968591 1091173 := bbase (se 4 (by rfl) ⟨102297, by rfl⟩ : syracuseStep 1091173 = 204595) (by norm_num)
theorem B1091209 : Blo 968591 1091209 := bbase (se 2 (by rfl) ⟨409203, by rfl⟩ : syracuseStep 1091209 = 818407) (by norm_num)
theorem B2107037 : Blo 968591 2107037 := bbase (se 3 (by rfl) ⟨395069, by rfl⟩ : syracuseStep 2107037 = 790139) (by norm_num)
theorem B1091245 : Blo 968591 1091245 := bbase (se 3 (by rfl) ⟨204608, by rfl⟩ : syracuseStep 1091245 = 409217) (by norm_num)
theorem B1091281 : Blo 968591 1091281 := bbase (se 2 (by rfl) ⟨409230, by rfl⟩ : syracuseStep 1091281 = 818461) (by norm_num)
theorem B1091317 : Blo 968591 1091317 := bbase (se 5 (by rfl) ⟨51155, by rfl⟩ : syracuseStep 1091317 = 102311) (by norm_num)
theorem B1091353 : Blo 968591 1091353 := bbase (se 2 (by rfl) ⟨409257, by rfl⟩ : syracuseStep 1091353 = 818515) (by norm_num)
theorem B4433717 : Blo 968591 4433717 := bbase (se 5 (by rfl) ⟨207830, by rfl⟩ : syracuseStep 4433717 = 415661) (by norm_num)
theorem B1091389 : Blo 968591 1091389 := bbase (se 3 (by rfl) ⟨204635, by rfl⟩ : syracuseStep 1091389 = 409271) (by norm_num)
theorem B1091425 : Blo 968591 1091425 := bbase (se 2 (by rfl) ⟨409284, by rfl⟩ : syracuseStep 1091425 = 818569) (by norm_num)
theorem B1091461 : Blo 968591 1091461 := bbase (se 4 (by rfl) ⟨102324, by rfl⟩ : syracuseStep 1091461 = 204649) (by norm_num)
theorem B8398741 : Blo 968591 8398741 := bbase (se 6 (by rfl) ⟨196845, by rfl⟩ : syracuseStep 8398741 = 393691) (by norm_num)
theorem B1091497 : Blo 968591 1091497 := bbase (se 2 (by rfl) ⟨409311, by rfl⟩ : syracuseStep 1091497 = 818623) (by norm_num)
theorem B1091533 : Blo 968591 1091533 := bbase (se 3 (by rfl) ⟨204662, by rfl⟩ : syracuseStep 1091533 = 409325) (by norm_num)
theorem B1091569 : Blo 968591 1091569 := bbase (se 2 (by rfl) ⟨409338, by rfl⟩ : syracuseStep 1091569 = 818677) (by norm_num)
theorem B6989813 : Blo 968591 6989813 := bbase (se 5 (by rfl) ⟨327647, by rfl⟩ : syracuseStep 6989813 = 655295) (by norm_num)
theorem B1091605 : Blo 968591 1091605 := bbase (se 6 (by rfl) ⟨25584, by rfl⟩ : syracuseStep 1091605 = 51169) (by norm_num)
theorem B1091641 : Blo 968591 1091641 := bbase (se 2 (by rfl) ⟨409365, by rfl⟩ : syracuseStep 1091641 = 818731) (by norm_num)
theorem B1091677 : Blo 968591 1091677 := bbase (se 3 (by rfl) ⟨204689, by rfl⟩ : syracuseStep 1091677 = 409379) (by norm_num)
theorem B1091713 : Blo 968591 1091713 := bbase (se 2 (by rfl) ⟨409392, by rfl⟩ : syracuseStep 1091713 = 818785) (by norm_num)
theorem B1091749 : Blo 968591 1091749 := bbase (se 4 (by rfl) ⟨102351, by rfl⟩ : syracuseStep 1091749 = 204703) (by norm_num)
theorem B1091785 : Blo 968591 1091785 := bbase (se 2 (by rfl) ⟨409419, by rfl⟩ : syracuseStep 1091785 = 818839) (by norm_num)
theorem B1091821 : Blo 968591 1091821 := bbase (se 3 (by rfl) ⟨204716, by rfl⟩ : syracuseStep 1091821 = 409433) (by norm_num)
theorem B1845517 : Blo 968591 1845517 := bbase (se 3 (by rfl) ⟨346034, by rfl⟩ : syracuseStep 1845517 = 692069) (by norm_num)
theorem B1091857 : Blo 968591 1091857 := bbase (se 2 (by rfl) ⟨409446, by rfl⟩ : syracuseStep 1091857 = 818893) (by norm_num)
theorem B2074909 : Blo 968591 2074909 := bbase (se 3 (by rfl) ⟨389045, by rfl⟩ : syracuseStep 2074909 = 778091) (by norm_num)
theorem B1091893 : Blo 968591 1091893 := bbase (se 5 (by rfl) ⟨51182, by rfl⟩ : syracuseStep 1091893 = 102365) (by norm_num)
theorem B1091929 : Blo 968591 1091929 := bbase (se 2 (by rfl) ⟨409473, by rfl⟩ : syracuseStep 1091929 = 818947) (by norm_num)
theorem B1747325 : Blo 968591 1747325 := bbase (se 3 (by rfl) ⟨327623, by rfl⟩ : syracuseStep 1747325 = 655247) (by norm_num)
theorem B1091965 : Blo 968591 1091965 := bbase (se 3 (by rfl) ⟨204743, by rfl⟩ : syracuseStep 1091965 = 409487) (by norm_num)
theorem B1845661 : Blo 968591 1845661 := bbase (se 3 (by rfl) ⟨346061, by rfl⟩ : syracuseStep 1845661 = 692123) (by norm_num)
theorem B1092001 : Blo 968591 1092001 := bbase (se 2 (by rfl) ⟨409500, by rfl⟩ : syracuseStep 1092001 = 819001) (by norm_num)
theorem B2763173 : Blo 968591 2763173 := bbase (se 4 (by rfl) ⟨259047, by rfl⟩ : syracuseStep 2763173 = 518095) (by norm_num)
theorem B2075053 : Blo 968591 2075053 := bbase (se 3 (by rfl) ⟨389072, by rfl⟩ : syracuseStep 2075053 = 778145) (by norm_num)
theorem B1092037 : Blo 968591 1092037 := bbase (se 4 (by rfl) ⟨102378, by rfl⟩ : syracuseStep 1092037 = 204757) (by norm_num)
theorem B1092073 : Blo 968591 1092073 := bbase (se 2 (by rfl) ⟨409527, by rfl⟩ : syracuseStep 1092073 = 819055) (by norm_num)
theorem B1092109 : Blo 968591 1092109 := bbase (se 3 (by rfl) ⟨204770, by rfl⟩ : syracuseStep 1092109 = 409541) (by norm_num)
theorem B1092145 : Blo 968591 1092145 := bbase (se 2 (by rfl) ⟨409554, by rfl⟩ : syracuseStep 1092145 = 819109) (by norm_num)
theorem B1845821 : Blo 968591 1845821 := bbase (se 3 (by rfl) ⟨346091, by rfl⟩ : syracuseStep 1845821 = 692183) (by norm_num)
theorem B1092181 : Blo 968591 1092181 := bbase (se 8 (by rfl) ⟨6399, by rfl⟩ : syracuseStep 1092181 = 12799) (by norm_num)
theorem B1092217 : Blo 968591 1092217 := bbase (se 2 (by rfl) ⟨409581, by rfl⟩ : syracuseStep 1092217 = 819163) (by norm_num)
theorem B1092253 : Blo 968591 1092253 := bbase (se 3 (by rfl) ⟨204797, by rfl⟩ : syracuseStep 1092253 = 409595) (by norm_num)
theorem B1092289 : Blo 968591 1092289 := bbase (se 2 (by rfl) ⟨409608, by rfl⟩ : syracuseStep 1092289 = 819217) (by norm_num)
theorem B1845965 : Blo 968591 1845965 := bbase (se 3 (by rfl) ⟨346118, by rfl⟩ : syracuseStep 1845965 = 692237) (by norm_num)
theorem B1092325 : Blo 968591 1092325 := bbase (se 4 (by rfl) ⟨102405, by rfl⟩ : syracuseStep 1092325 = 204811) (by norm_num)
theorem B7383797 : Blo 968591 7383797 := bbase (se 5 (by rfl) ⟨346115, by rfl⟩ : syracuseStep 7383797 = 692231) (by norm_num)
theorem B1092361 : Blo 968591 1092361 := bbase (se 2 (by rfl) ⟨409635, by rfl⟩ : syracuseStep 1092361 = 819271) (by norm_num)
theorem B2075429 : Blo 968591 2075429 := bbase (se 4 (by rfl) ⟨194571, by rfl⟩ : syracuseStep 2075429 = 389143) (by norm_num)
theorem B1092397 : Blo 968591 1092397 := bbase (se 3 (by rfl) ⟨204824, by rfl⟩ : syracuseStep 1092397 = 409649) (by norm_num)
theorem B1092433 : Blo 968591 1092433 := bbase (se 2 (by rfl) ⟨409662, by rfl⟩ : syracuseStep 1092433 = 819325) (by norm_num)
theorem B1452893 : Blo 968591 1452893 := bbase (se 3 (by rfl) ⟨272417, by rfl⟩ : syracuseStep 1452893 = 544835) (by norm_num)
theorem B1452917 : Blo 968591 1452917 := bbase (se 5 (by rfl) ⟨68105, by rfl⟩ : syracuseStep 1452917 = 136211) (by norm_num)
theorem B1092469 : Blo 968591 1092469 := bbase (se 5 (by rfl) ⟨51209, by rfl⟩ : syracuseStep 1092469 = 102419) (by norm_num)
theorem B1452941 : Blo 968591 1452941 := bbase (se 3 (by rfl) ⟨272426, by rfl⟩ : syracuseStep 1452941 = 544853) (by norm_num)
theorem B17935253 : Blo 968591 17935253 := bbase (se 6 (by rfl) ⟨420357, by rfl⟩ : syracuseStep 17935253 = 840715) (by norm_num)
theorem B1092505 : Blo 968591 1092505 := bbase (se 2 (by rfl) ⟨409689, by rfl⟩ : syracuseStep 1092505 = 819379) (by norm_num)
theorem B1452965 : Blo 968591 1452965 := bbase (se 4 (by rfl) ⟨136215, by rfl⟩ : syracuseStep 1452965 = 272431) (by norm_num)
theorem B5909429 : Blo 968591 5909429 := bbase (se 5 (by rfl) ⟨277004, by rfl⟩ : syracuseStep 5909429 = 554009) (by norm_num)
theorem B1452989 : Blo 968591 1452989 := bbase (se 3 (by rfl) ⟨272435, by rfl⟩ : syracuseStep 1452989 = 544871) (by norm_num)
theorem B1747901 : Blo 968591 1747901 := bbase (se 3 (by rfl) ⟨327731, by rfl⟩ : syracuseStep 1747901 = 655463) (by norm_num)
theorem B1092541 : Blo 968591 1092541 := bbase (se 3 (by rfl) ⟨204851, by rfl⟩ : syracuseStep 1092541 = 409703) (by norm_num)
theorem B1453013 : Blo 968591 1453013 := bbase (se 7 (by rfl) ⟨17027, by rfl⟩ : syracuseStep 1453013 = 34055) (by norm_num)
theorem B1092577 : Blo 968591 1092577 := bbase (se 2 (by rfl) ⟨409716, by rfl⟩ : syracuseStep 1092577 = 819433) (by norm_num)
theorem B1453037 : Blo 968591 1453037 := bbase (se 3 (by rfl) ⟨272444, by rfl⟩ : syracuseStep 1453037 = 544889) (by norm_num)
theorem B1846253 : Blo 968591 1846253 := bbase (se 3 (by rfl) ⟨346172, by rfl⟩ : syracuseStep 1846253 = 692345) (by norm_num)
theorem B1453061 : Blo 968591 1453061 := bbase (se 4 (by rfl) ⟨136224, by rfl⟩ : syracuseStep 1453061 = 272449) (by norm_num)
theorem B1092613 : Blo 968591 1092613 := bbase (se 4 (by rfl) ⟨102432, by rfl⟩ : syracuseStep 1092613 = 204865) (by norm_num)
theorem B1453085 : Blo 968591 1453085 := bbase (se 3 (by rfl) ⟨272453, by rfl⟩ : syracuseStep 1453085 = 544907) (by norm_num)
theorem B1092649 : Blo 968591 1092649 := bbase (se 2 (by rfl) ⟨409743, by rfl⟩ : syracuseStep 1092649 = 819487) (by norm_num)
theorem B1453109 : Blo 968591 1453109 := bbase (se 5 (by rfl) ⟨68114, by rfl⟩ : syracuseStep 1453109 = 136229) (by norm_num)
theorem B2763845 : Blo 968591 2763845 := bbase (se 4 (by rfl) ⟨259110, by rfl⟩ : syracuseStep 2763845 = 518221) (by norm_num)
theorem B1453133 : Blo 968591 1453133 := bbase (se 3 (by rfl) ⟨272462, by rfl⟩ : syracuseStep 1453133 = 544925) (by norm_num)
theorem B1092685 : Blo 968591 1092685 := bbase (se 3 (by rfl) ⟨204878, by rfl⟩ : syracuseStep 1092685 = 409757) (by norm_num)
theorem B1453157 : Blo 968591 1453157 := bbase (se 4 (by rfl) ⟨136233, by rfl⟩ : syracuseStep 1453157 = 272467) (by norm_num)
theorem B1092721 : Blo 968591 1092721 := bbase (se 2 (by rfl) ⟨409770, by rfl⟩ : syracuseStep 1092721 = 819541) (by norm_num)
theorem B1453181 : Blo 968591 1453181 := bbase (se 3 (by rfl) ⟨272471, by rfl⟩ : syracuseStep 1453181 = 544943) (by norm_num)
theorem B1846405 : Blo 968591 1846405 := bbase (se 4 (by rfl) ⟨173100, by rfl⟩ : syracuseStep 1846405 = 346201) (by norm_num)
theorem B1453205 : Blo 968591 1453205 := bbase (se 6 (by rfl) ⟨34059, by rfl⟩ : syracuseStep 1453205 = 68119) (by norm_num)
theorem B1092757 : Blo 968591 1092757 := bbase (se 6 (by rfl) ⟨25611, by rfl⟩ : syracuseStep 1092757 = 51223) (by norm_num)
theorem B2075797 : Blo 968591 2075797 := bbase (se 6 (by rfl) ⟨48651, by rfl⟩ : syracuseStep 2075797 = 97303) (by norm_num)
theorem B4140197 : Blo 968591 4140197 := bbase (se 4 (by rfl) ⟨388143, by rfl⟩ : syracuseStep 4140197 = 776287) (by norm_num)
theorem B1453229 : Blo 968591 1453229 := bbase (se 3 (by rfl) ⟨272480, by rfl⟩ : syracuseStep 1453229 = 544961) (by norm_num)
theorem B1092793 : Blo 968591 1092793 := bbase (se 2 (by rfl) ⟨409797, by rfl⟩ : syracuseStep 1092793 = 819595) (by norm_num)
theorem B1453253 : Blo 968591 1453253 := bbase (se 4 (by rfl) ⟨136242, by rfl⟩ : syracuseStep 1453253 = 272485) (by norm_num)
theorem B1453277 : Blo 968591 1453277 := bbase (se 3 (by rfl) ⟨272489, by rfl⟩ : syracuseStep 1453277 = 544979) (by norm_num)
theorem B1092829 : Blo 968591 1092829 := bbase (se 3 (by rfl) ⟨204905, by rfl⟩ : syracuseStep 1092829 = 409811) (by norm_num)
theorem B1453301 : Blo 968591 1453301 := bbase (se 5 (by rfl) ⟨68123, by rfl⟩ : syracuseStep 1453301 = 136247) (by norm_num)
theorem B1092865 : Blo 968591 1092865 := bbase (se 2 (by rfl) ⟨409824, by rfl⟩ : syracuseStep 1092865 = 819649) (by norm_num)
theorem B1453325 : Blo 968591 1453325 := bbase (se 3 (by rfl) ⟨272498, by rfl⟩ : syracuseStep 1453325 = 544997) (by norm_num)
theorem B3681557 : Blo 968591 3681557 := bbase (se 6 (by rfl) ⟨86286, by rfl⟩ : syracuseStep 3681557 = 172573) (by norm_num)
theorem B1453349 : Blo 968591 1453349 := bbase (se 4 (by rfl) ⟨136251, by rfl⟩ : syracuseStep 1453349 = 272503) (by norm_num)
theorem B1092901 : Blo 968591 1092901 := bbase (se 4 (by rfl) ⟨102459, by rfl⟩ : syracuseStep 1092901 = 204919) (by norm_num)
theorem B1453373 : Blo 968591 1453373 := bbase (se 3 (by rfl) ⟨272507, by rfl⟩ : syracuseStep 1453373 = 545015) (by norm_num)
theorem B1092937 : Blo 968591 1092937 := bbase (se 2 (by rfl) ⟨409851, by rfl⟩ : syracuseStep 1092937 = 819703) (by norm_num)
theorem B1453397 : Blo 968591 1453397 := bbase (se 11 (by rfl) ⟨1064, by rfl⟩ : syracuseStep 1453397 = 2129) (by norm_num)
theorem B1453421 : Blo 968591 1453421 := bbase (se 3 (by rfl) ⟨272516, by rfl⟩ : syracuseStep 1453421 = 545033) (by norm_num)
theorem B1092973 : Blo 968591 1092973 := bbase (se 3 (by rfl) ⟨204932, by rfl⟩ : syracuseStep 1092973 = 409865) (by norm_num)
theorem B1453445 : Blo 968591 1453445 := bbase (se 4 (by rfl) ⟨136260, by rfl⟩ : syracuseStep 1453445 = 272521) (by norm_num)
theorem B1093009 : Blo 968591 1093009 := bbase (se 2 (by rfl) ⟨409878, by rfl⟩ : syracuseStep 1093009 = 819757) (by norm_num)
theorem B1453469 : Blo 968591 1453469 := bbase (se 3 (by rfl) ⟨272525, by rfl⟩ : syracuseStep 1453469 = 545051) (by norm_num)
theorem B1453493 : Blo 968591 1453493 := bbase (se 5 (by rfl) ⟨68132, by rfl⟩ : syracuseStep 1453493 = 136265) (by norm_num)
theorem B1093045 : Blo 968591 1093045 := bbase (se 5 (by rfl) ⟨51236, by rfl⟩ : syracuseStep 1093045 = 102473) (by norm_num)
theorem B1453517 : Blo 968591 1453517 := bbase (se 3 (by rfl) ⟨272534, by rfl⟩ : syracuseStep 1453517 = 545069) (by norm_num)
theorem B5385685 : Blo 968591 5385685 := bbase (se 7 (by rfl) ⟨63113, by rfl⟩ : syracuseStep 5385685 = 126227) (by norm_num)
theorem B1093081 : Blo 968591 1093081 := bbase (se 2 (by rfl) ⟨409905, by rfl⟩ : syracuseStep 1093081 = 819811) (by norm_num)
theorem B1453541 : Blo 968591 1453541 := bbase (se 4 (by rfl) ⟨136269, by rfl⟩ : syracuseStep 1453541 = 272539) (by norm_num)
theorem B2764277 : Blo 968591 2764277 := bbase (se 5 (by rfl) ⟨129575, by rfl⟩ : syracuseStep 2764277 = 259151) (by norm_num)
theorem B1453565 : Blo 968591 1453565 := bbase (se 3 (by rfl) ⟨272543, by rfl⟩ : syracuseStep 1453565 = 545087) (by norm_num)
theorem B1093117 : Blo 968591 1093117 := bbase (se 3 (by rfl) ⟨204959, by rfl⟩ : syracuseStep 1093117 = 409919) (by norm_num)
theorem B1453589 : Blo 968591 1453589 := bbase (se 6 (by rfl) ⟨34068, by rfl⟩ : syracuseStep 1453589 = 68137) (by norm_num)
theorem B1093153 : Blo 968591 1093153 := bbase (se 2 (by rfl) ⟨409932, by rfl⟩ : syracuseStep 1093153 = 819865) (by norm_num)
theorem B1453613 : Blo 968591 1453613 := bbase (se 3 (by rfl) ⟨272552, by rfl⟩ : syracuseStep 1453613 = 545105) (by norm_num)
theorem B3681845 : Blo 968591 3681845 := bbase (se 5 (by rfl) ⟨172586, by rfl⟩ : syracuseStep 3681845 = 345173) (by norm_num)
theorem B1453637 : Blo 968591 1453637 := bbase (se 4 (by rfl) ⟨136278, by rfl⟩ : syracuseStep 1453637 = 272557) (by norm_num)
theorem B1093189 : Blo 968591 1093189 := bbase (se 4 (by rfl) ⟨102486, by rfl⟩ : syracuseStep 1093189 = 204973) (by norm_num)
theorem B1453661 : Blo 968591 1453661 := bbase (se 3 (by rfl) ⟨272561, by rfl⟩ : syracuseStep 1453661 = 545123) (by norm_num)
theorem B1093225 : Blo 968591 1093225 := bbase (se 2 (by rfl) ⟨409959, by rfl⟩ : syracuseStep 1093225 = 819919) (by norm_num)
theorem B1453685 : Blo 968591 1453685 := bbase (se 5 (by rfl) ⟨68141, by rfl⟩ : syracuseStep 1453685 = 136283) (by norm_num)
theorem B1453709 : Blo 968591 1453709 := bbase (se 3 (by rfl) ⟨272570, by rfl⟩ : syracuseStep 1453709 = 545141) (by norm_num)
theorem B1093261 : Blo 968591 1093261 := bbase (se 3 (by rfl) ⟨204986, by rfl⟩ : syracuseStep 1093261 = 409973) (by norm_num)
theorem B1453733 : Blo 968591 1453733 := bbase (se 4 (by rfl) ⟨136287, by rfl⟩ : syracuseStep 1453733 = 272575) (by norm_num)
theorem B1093297 : Blo 968591 1093297 := bbase (se 2 (by rfl) ⟨409986, by rfl⟩ : syracuseStep 1093297 = 819973) (by norm_num)
theorem B5516981 : Blo 968591 5516981 := bbase (se 5 (by rfl) ⟨258608, by rfl⟩ : syracuseStep 5516981 = 517217) (by norm_num)
theorem B1453757 : Blo 968591 1453757 := bbase (se 3 (by rfl) ⟨272579, by rfl⟩ : syracuseStep 1453757 = 545159) (by norm_num)
theorem B1683149 : Blo 968591 1683149 := bbase (se 3 (by rfl) ⟨315590, by rfl⟩ : syracuseStep 1683149 = 631181) (by norm_num)
theorem B1453781 : Blo 968591 1453781 := bbase (se 7 (by rfl) ⟨17036, by rfl⟩ : syracuseStep 1453781 = 34073) (by norm_num)
theorem B1748693 : Blo 968591 1748693 := bbase (se 7 (by rfl) ⟨20492, by rfl⟩ : syracuseStep 1748693 = 40985) (by norm_num)
theorem B1093333 : Blo 968591 1093333 := bbase (se 7 (by rfl) ⟨12812, by rfl⟩ : syracuseStep 1093333 = 25625) (by norm_num)
theorem B1453805 : Blo 968591 1453805 := bbase (se 3 (by rfl) ⟨272588, by rfl⟩ : syracuseStep 1453805 = 545177) (by norm_num)
theorem B5254901 : Blo 968591 5254901 := bbase (se 5 (by rfl) ⟨246323, by rfl⟩ : syracuseStep 5254901 = 492647) (by norm_num)
theorem B1093369 : Blo 968591 1093369 := bbase (se 2 (by rfl) ⟨410013, by rfl⟩ : syracuseStep 1093369 = 820027) (by norm_num)
theorem B1453829 : Blo 968591 1453829 := bbase (se 4 (by rfl) ⟨136296, by rfl⟩ : syracuseStep 1453829 = 272593) (by norm_num)
theorem B1453853 : Blo 968591 1453853 := bbase (se 3 (by rfl) ⟨272597, by rfl⟩ : syracuseStep 1453853 = 545195) (by norm_num)
theorem B1093405 : Blo 968591 1093405 := bbase (se 3 (by rfl) ⟨205013, by rfl⟩ : syracuseStep 1093405 = 410027) (by norm_num)
theorem B1453877 : Blo 968591 1453877 := bbase (se 5 (by rfl) ⟨68150, by rfl⟩ : syracuseStep 1453877 = 136301) (by norm_num)
theorem B1093441 : Blo 968591 1093441 := bbase (se 2 (by rfl) ⟨410040, by rfl⟩ : syracuseStep 1093441 = 820081) (by norm_num)
theorem B1453901 : Blo 968591 1453901 := bbase (se 3 (by rfl) ⟨272606, by rfl⟩ : syracuseStep 1453901 = 545213) (by norm_num)
theorem B1453925 : Blo 968591 1453925 := bbase (se 4 (by rfl) ⟨136305, by rfl⟩ : syracuseStep 1453925 = 272611) (by norm_num)
theorem B1748837 : Blo 968591 1748837 := bbase (se 4 (by rfl) ⟨163953, by rfl⟩ : syracuseStep 1748837 = 327907) (by norm_num)
theorem B1093477 : Blo 968591 1093477 := bbase (se 4 (by rfl) ⟨102513, by rfl⟩ : syracuseStep 1093477 = 205027) (by norm_num)
theorem B1453949 : Blo 968591 1453949 := bbase (se 3 (by rfl) ⟨272615, by rfl⟩ : syracuseStep 1453949 = 545231) (by norm_num)
theorem B4665221 : Blo 968591 4665221 := bbase (se 4 (by rfl) ⟨437364, by rfl⟩ : syracuseStep 4665221 = 874729) (by norm_num)
theorem B1093513 : Blo 968591 1093513 := bbase (se 2 (by rfl) ⟨410067, by rfl⟩ : syracuseStep 1093513 = 820135) (by norm_num)
theorem B1453973 : Blo 968591 1453973 := bbase (se 6 (by rfl) ⟨34077, by rfl⟩ : syracuseStep 1453973 = 68155) (by norm_num)
theorem B1453997 : Blo 968591 1453997 := bbase (se 3 (by rfl) ⟨272624, by rfl⟩ : syracuseStep 1453997 = 545249) (by norm_num)
theorem B1093549 : Blo 968591 1093549 := bbase (se 3 (by rfl) ⟨205040, by rfl⟩ : syracuseStep 1093549 = 410081) (by norm_num)
theorem B1454021 : Blo 968591 1454021 := bbase (se 4 (by rfl) ⟨136314, by rfl⟩ : syracuseStep 1454021 = 272629) (by norm_num)
theorem B1093585 : Blo 968591 1093585 := bbase (se 2 (by rfl) ⟨410094, by rfl⟩ : syracuseStep 1093585 = 820189) (by norm_num)
theorem B1454045 : Blo 968591 1454045 := bbase (se 3 (by rfl) ⟨272633, by rfl⟩ : syracuseStep 1454045 = 545267) (by norm_num)
theorem B1454069 : Blo 968591 1454069 := bbase (se 5 (by rfl) ⟨68159, by rfl⟩ : syracuseStep 1454069 = 136319) (by norm_num)
theorem B1093621 : Blo 968591 1093621 := bbase (se 5 (by rfl) ⟨51263, by rfl⟩ : syracuseStep 1093621 = 102527) (by norm_num)
theorem B1454093 : Blo 968591 1454093 := bbase (se 3 (by rfl) ⟨272642, by rfl⟩ : syracuseStep 1454093 = 545285) (by norm_num)
theorem B1093657 : Blo 968591 1093657 := bbase (se 2 (by rfl) ⟨410121, by rfl⟩ : syracuseStep 1093657 = 820243) (by norm_num)
theorem B1552421 : Blo 968591 1552421 := bbase (se 4 (by rfl) ⟨145539, by rfl⟩ : syracuseStep 1552421 = 291079) (by norm_num)
theorem B1454117 : Blo 968591 1454117 := bbase (se 4 (by rfl) ⟨136323, by rfl⟩ : syracuseStep 1454117 = 272647) (by norm_num)
theorem B1454141 : Blo 968591 1454141 := bbase (se 3 (by rfl) ⟨272651, by rfl⟩ : syracuseStep 1454141 = 545303) (by norm_num)
theorem B1093693 : Blo 968591 1093693 := bbase (se 3 (by rfl) ⟨205067, by rfl⟩ : syracuseStep 1093693 = 410135) (by norm_num)
theorem B1454165 : Blo 968591 1454165 := bbase (se 8 (by rfl) ⟨8520, by rfl⟩ : syracuseStep 1454165 = 17041) (by norm_num)
theorem B1093729 : Blo 968591 1093729 := bbase (se 2 (by rfl) ⟨410148, by rfl⟩ : syracuseStep 1093729 = 820297) (by norm_num)
theorem B1454189 : Blo 968591 1454189 := bbase (se 3 (by rfl) ⟨272660, by rfl⟩ : syracuseStep 1454189 = 545321) (by norm_num)
theorem B1454213 : Blo 968591 1454213 := bbase (se 4 (by rfl) ⟨136332, by rfl⟩ : syracuseStep 1454213 = 272665) (by norm_num)
theorem B1093765 : Blo 968591 1093765 := bbase (se 4 (by rfl) ⟨102540, by rfl⟩ : syracuseStep 1093765 = 205081) (by norm_num)
theorem B3158165 : Blo 968591 3158165 := bbase (se 6 (by rfl) ⟨74019, by rfl⟩ : syracuseStep 3158165 = 148039) (by norm_num)
theorem B1454237 : Blo 968591 1454237 := bbase (se 3 (by rfl) ⟨272669, by rfl⟩ : syracuseStep 1454237 = 545339) (by norm_num)
theorem B1093801 : Blo 968591 1093801 := bbase (se 2 (by rfl) ⟨410175, by rfl⟩ : syracuseStep 1093801 = 820351) (by norm_num)
theorem B1454261 : Blo 968591 1454261 := bbase (se 5 (by rfl) ⟨68168, by rfl⟩ : syracuseStep 1454261 = 136337) (by norm_num)
theorem B1454285 : Blo 968591 1454285 := bbase (se 3 (by rfl) ⟨272678, by rfl⟩ : syracuseStep 1454285 = 545357) (by norm_num)
theorem B1093837 : Blo 968591 1093837 := bbase (se 3 (by rfl) ⟨205094, by rfl⟩ : syracuseStep 1093837 = 410189) (by norm_num)
theorem B1454309 : Blo 968591 1454309 := bbase (se 4 (by rfl) ⟨136341, by rfl⟩ : syracuseStep 1454309 = 272683) (by norm_num)
theorem B2765029 : Blo 968591 2765029 := bbase (se 4 (by rfl) ⟨259221, by rfl⟩ : syracuseStep 2765029 = 518443) (by norm_num)
theorem B1093873 : Blo 968591 1093873 := bbase (se 2 (by rfl) ⟨410202, by rfl⟩ : syracuseStep 1093873 = 820405) (by norm_num)
theorem B1454333 : Blo 968591 1454333 := bbase (se 3 (by rfl) ⟨272687, by rfl⟩ : syracuseStep 1454333 = 545375) (by norm_num)
theorem B1552645 : Blo 968591 1552645 := bbase (se 4 (by rfl) ⟨145560, by rfl⟩ : syracuseStep 1552645 = 291121) (by norm_num)
theorem B1454357 : Blo 968591 1454357 := bbase (se 6 (by rfl) ⟨34086, by rfl⟩ : syracuseStep 1454357 = 68173) (by norm_num)
theorem B1093909 : Blo 968591 1093909 := bbase (se 6 (by rfl) ⟨25638, by rfl⟩ : syracuseStep 1093909 = 51277) (by norm_num)
theorem B1454381 : Blo 968591 1454381 := bbase (se 3 (by rfl) ⟨272696, by rfl⟩ : syracuseStep 1454381 = 545393) (by norm_num)
theorem B1093945 : Blo 968591 1093945 := bbase (se 2 (by rfl) ⟨410229, by rfl⟩ : syracuseStep 1093945 = 820459) (by norm_num)
theorem B1454405 : Blo 968591 1454405 := bbase (se 4 (by rfl) ⟨136350, by rfl⟩ : syracuseStep 1454405 = 272701) (by norm_num)
theorem B1454429 : Blo 968591 1454429 := bbase (se 3 (by rfl) ⟨272705, by rfl⟩ : syracuseStep 1454429 = 545411) (by norm_num)
theorem B1093981 : Blo 968591 1093981 := bbase (se 3 (by rfl) ⟨205121, by rfl⟩ : syracuseStep 1093981 = 410243) (by norm_num)
theorem B995689 : Blo 968591 995689 := bbase (se 2 (by rfl) ⟨373383, by rfl⟩ : syracuseStep 995689 = 746767) (by norm_num)
theorem B1454453 : Blo 968591 1454453 := bbase (se 5 (by rfl) ⟨68177, by rfl⟩ : syracuseStep 1454453 = 136355) (by norm_num)
theorem B1094017 : Blo 968591 1094017 := bbase (se 2 (by rfl) ⟨410256, by rfl⟩ : syracuseStep 1094017 = 820513) (by norm_num)
theorem B1454477 : Blo 968591 1454477 := bbase (se 3 (by rfl) ⟨272714, by rfl⟩ : syracuseStep 1454477 = 545429) (by norm_num)
theorem B1454501 : Blo 968591 1454501 := bbase (se 4 (by rfl) ⟨136359, by rfl⟩ : syracuseStep 1454501 = 272719) (by norm_num)
theorem B1094053 : Blo 968591 1094053 := bbase (se 4 (by rfl) ⟨102567, by rfl⟩ : syracuseStep 1094053 = 205135) (by norm_num)
theorem B1454525 : Blo 968591 1454525 := bbase (se 3 (by rfl) ⟨272723, by rfl⟩ : syracuseStep 1454525 = 545447) (by norm_num)
theorem B1094089 : Blo 968591 1094089 := bbase (se 2 (by rfl) ⟨410283, by rfl⟩ : syracuseStep 1094089 = 820567) (by norm_num)
theorem B1454549 : Blo 968591 1454549 := bbase (se 7 (by rfl) ⟨17045, by rfl⟩ : syracuseStep 1454549 = 34091) (by norm_num)
theorem B1454573 : Blo 968591 1454573 := bbase (se 3 (by rfl) ⟨272732, by rfl⟩ : syracuseStep 1454573 = 545465) (by norm_num)
theorem B1094125 : Blo 968591 1094125 := bbase (se 3 (by rfl) ⟨205148, by rfl⟩ : syracuseStep 1094125 = 410297) (by norm_num)
theorem B1454597 : Blo 968591 1454597 := bbase (se 4 (by rfl) ⟨136368, by rfl⟩ : syracuseStep 1454597 = 272737) (by norm_num)
theorem B1094161 : Blo 968591 1094161 := bbase (se 2 (by rfl) ⟨410310, by rfl⟩ : syracuseStep 1094161 = 820621) (by norm_num)
theorem B1454621 : Blo 968591 1454621 := bbase (se 3 (by rfl) ⟨272741, by rfl⟩ : syracuseStep 1454621 = 545483) (by norm_num)
theorem B1454645 : Blo 968591 1454645 := bbase (se 5 (by rfl) ⟨68186, by rfl⟩ : syracuseStep 1454645 = 136373) (by norm_num)
theorem B1454669 : Blo 968591 1454669 := bbase (se 3 (by rfl) ⟨272750, by rfl⟩ : syracuseStep 1454669 = 545501) (by norm_num)
theorem B1454693 : Blo 968591 1454693 := bbase (se 4 (by rfl) ⟨136377, by rfl⟩ : syracuseStep 1454693 = 272755) (by norm_num)
theorem B1454717 : Blo 968591 1454717 := bbase (se 3 (by rfl) ⟨272759, by rfl⟩ : syracuseStep 1454717 = 545519) (by norm_num)
theorem B1454741 : Blo 968591 1454741 := bbase (se 6 (by rfl) ⟨34095, by rfl⟩ : syracuseStep 1454741 = 68191) (by norm_num)
theorem B1454765 : Blo 968591 1454765 := bbase (se 3 (by rfl) ⟨272768, by rfl⟩ : syracuseStep 1454765 = 545537) (by norm_num)
theorem B1454789 : Blo 968591 1454789 := bbase (se 4 (by rfl) ⟨136386, by rfl⟩ : syracuseStep 1454789 = 272773) (by norm_num)
theorem B3683029 : Blo 968591 3683029 := bbase (se 7 (by rfl) ⟨43160, by rfl⟩ : syracuseStep 3683029 = 86321) (by norm_num)
theorem B1454813 : Blo 968591 1454813 := bbase (se 3 (by rfl) ⟨272777, by rfl⟩ : syracuseStep 1454813 = 545555) (by norm_num)
theorem B1454837 : Blo 968591 1454837 := bbase (se 5 (by rfl) ⟨68195, by rfl⟩ : syracuseStep 1454837 = 136391) (by norm_num)
theorem B1454861 : Blo 968591 1454861 := bbase (se 3 (by rfl) ⟨272786, by rfl⟩ : syracuseStep 1454861 = 545573) (by norm_num)
theorem B1454885 : Blo 968591 1454885 := bbase (se 4 (by rfl) ⟨136395, by rfl⟩ : syracuseStep 1454885 = 272791) (by norm_num)
theorem B1454909 : Blo 968591 1454909 := bbase (se 3 (by rfl) ⟨272795, by rfl⟩ : syracuseStep 1454909 = 545591) (by norm_num)
theorem B5518165 : Blo 968591 5518165 := bbase (se 9 (by rfl) ⟨16166, by rfl⟩ : syracuseStep 5518165 = 32333) (by norm_num)
theorem B1454933 : Blo 968591 1454933 := bbase (se 9 (by rfl) ⟨4262, by rfl⟩ : syracuseStep 1454933 = 8525) (by norm_num)
theorem B1684309 : Blo 968591 1684309 := bbase (se 9 (by rfl) ⟨4934, by rfl⟩ : syracuseStep 1684309 = 9869) (by norm_num)
theorem B1454957 : Blo 968591 1454957 := bbase (se 3 (by rfl) ⟨272804, by rfl⟩ : syracuseStep 1454957 = 545609) (by norm_num)
theorem B3322741 : Blo 968591 3322741 := bbase (se 5 (by rfl) ⟨155753, by rfl⟩ : syracuseStep 3322741 = 311507) (by norm_num)
theorem B1454981 : Blo 968591 1454981 := bbase (se 4 (by rfl) ⟨136404, by rfl⟩ : syracuseStep 1454981 = 272809) (by norm_num)
theorem B1455005 : Blo 968591 1455005 := bbase (se 3 (by rfl) ⟨272813, by rfl⟩ : syracuseStep 1455005 = 545627) (by norm_num)
theorem B1455029 : Blo 968591 1455029 := bbase (se 5 (by rfl) ⟨68204, by rfl⟩ : syracuseStep 1455029 = 136409) (by norm_num)
theorem B1455053 : Blo 968591 1455053 := bbase (se 3 (by rfl) ⟨272822, by rfl⟩ : syracuseStep 1455053 = 545645) (by norm_num)
theorem B996305 : Blo 968591 996305 := bbase (se 2 (by rfl) ⟨373614, by rfl⟩ : syracuseStep 996305 = 747229) (by norm_num)
theorem B1455077 : Blo 968591 1455077 := bbase (se 4 (by rfl) ⟨136413, by rfl⟩ : syracuseStep 1455077 = 272827) (by norm_num)
theorem B1455101 : Blo 968591 1455101 := bbase (se 3 (by rfl) ⟨272831, by rfl⟩ : syracuseStep 1455101 = 545663) (by norm_num)
theorem B3683333 : Blo 968591 3683333 := bbase (se 4 (by rfl) ⟨345312, by rfl⟩ : syracuseStep 3683333 = 690625) (by norm_num)
theorem B1455125 : Blo 968591 1455125 := bbase (se 6 (by rfl) ⟨34104, by rfl⟩ : syracuseStep 1455125 = 68209) (by norm_num)
theorem B1455149 : Blo 968591 1455149 := bbase (se 3 (by rfl) ⟨272840, by rfl⟩ : syracuseStep 1455149 = 545681) (by norm_num)
theorem B1455173 : Blo 968591 1455173 := bbase (se 4 (by rfl) ⟨136422, by rfl⟩ : syracuseStep 1455173 = 272845) (by norm_num)
theorem B1455197 : Blo 968591 1455197 := bbase (se 3 (by rfl) ⟨272849, by rfl⟩ : syracuseStep 1455197 = 545699) (by norm_num)
theorem B1455221 : Blo 968591 1455221 := bbase (se 5 (by rfl) ⟨68213, by rfl⟩ : syracuseStep 1455221 = 136427) (by norm_num)
theorem B1455245 : Blo 968591 1455245 := bbase (se 3 (by rfl) ⟨272858, by rfl⟩ : syracuseStep 1455245 = 545717) (by norm_num)
theorem B1455269 : Blo 968591 1455269 := bbase (se 4 (by rfl) ⟨136431, by rfl⟩ : syracuseStep 1455269 = 272863) (by norm_num)
theorem B1455293 : Blo 968591 1455293 := bbase (se 3 (by rfl) ⟨272867, by rfl⟩ : syracuseStep 1455293 = 545735) (by norm_num)
theorem B1455317 : Blo 968591 1455317 := bbase (se 7 (by rfl) ⟨17054, by rfl⟩ : syracuseStep 1455317 = 34109) (by norm_num)
theorem B1225945 : Blo 968591 1225945 := bbase (se 2 (by rfl) ⟨459729, by rfl⟩ : syracuseStep 1225945 = 919459) (by norm_num)
theorem B1455341 : Blo 968591 1455341 := bbase (se 3 (by rfl) ⟨272876, by rfl⟩ : syracuseStep 1455341 = 545753) (by norm_num)
theorem B1455365 : Blo 968591 1455365 := bbase (se 4 (by rfl) ⟨136440, by rfl⟩ : syracuseStep 1455365 = 272881) (by norm_num)
theorem B2733317 : Blo 968591 2733317 := bbase (se 4 (by rfl) ⟨256248, by rfl⟩ : syracuseStep 2733317 = 512497) (by norm_num)
theorem B1455389 : Blo 968591 1455389 := bbase (se 3 (by rfl) ⟨272885, by rfl⟩ : syracuseStep 1455389 = 545771) (by norm_num)
theorem B1455413 : Blo 968591 1455413 := bbase (se 5 (by rfl) ⟨68222, by rfl⟩ : syracuseStep 1455413 = 136445) (by norm_num)
theorem B1455437 : Blo 968591 1455437 := bbase (se 3 (by rfl) ⟨272894, by rfl⟩ : syracuseStep 1455437 = 545789) (by norm_num)
theorem B1455461 : Blo 968591 1455461 := bbase (se 4 (by rfl) ⟨136449, by rfl⟩ : syracuseStep 1455461 = 272899) (by norm_num)
theorem B1455485 : Blo 968591 1455485 := bbase (se 3 (by rfl) ⟨272903, by rfl⟩ : syracuseStep 1455485 = 545807) (by norm_num)
theorem B1226117 : Blo 968591 1226117 := bbase (se 4 (by rfl) ⟨114948, by rfl⟩ : syracuseStep 1226117 = 229897) (by norm_num)
theorem B1455509 : Blo 968591 1455509 := bbase (se 6 (by rfl) ⟨34113, by rfl⟩ : syracuseStep 1455509 = 68227) (by norm_num)
theorem B1455533 : Blo 968591 1455533 := bbase (se 3 (by rfl) ⟨272912, by rfl⟩ : syracuseStep 1455533 = 545825) (by norm_num)
theorem B1226173 : Blo 968591 1226173 := bbase (se 3 (by rfl) ⟨229907, by rfl⟩ : syracuseStep 1226173 = 459815) (by norm_num)
theorem B1455557 : Blo 968591 1455557 := bbase (se 4 (by rfl) ⟨136458, by rfl⟩ : syracuseStep 1455557 = 272917) (by norm_num)
theorem B1455581 : Blo 968591 1455581 := bbase (se 3 (by rfl) ⟨272921, by rfl⟩ : syracuseStep 1455581 = 545843) (by norm_num)
theorem B1455605 : Blo 968591 1455605 := bbase (se 5 (by rfl) ⟨68231, by rfl⟩ : syracuseStep 1455605 = 136463) (by norm_num)
theorem B1455629 : Blo 968591 1455629 := bbase (se 3 (by rfl) ⟨272930, by rfl⟩ : syracuseStep 1455629 = 545861) (by norm_num)
theorem B1226269 : Blo 968591 1226269 := bbase (se 3 (by rfl) ⟨229925, by rfl⟩ : syracuseStep 1226269 = 459851) (by norm_num)
theorem B1455653 : Blo 968591 1455653 := bbase (se 4 (by rfl) ⟨136467, by rfl⟩ : syracuseStep 1455653 = 272935) (by norm_num)
theorem B1455677 : Blo 968591 1455677 := bbase (se 3 (by rfl) ⟨272939, by rfl⟩ : syracuseStep 1455677 = 545879) (by norm_num)
theorem B1455701 : Blo 968591 1455701 := bbase (se 8 (by rfl) ⟨8529, by rfl⟩ : syracuseStep 1455701 = 17059) (by norm_num)
theorem B1455725 : Blo 968591 1455725 := bbase (se 3 (by rfl) ⟨272948, by rfl⟩ : syracuseStep 1455725 = 545897) (by norm_num)
theorem B1455749 : Blo 968591 1455749 := bbase (se 4 (by rfl) ⟨136476, by rfl⟩ : syracuseStep 1455749 = 272953) (by norm_num)
theorem B1554061 : Blo 968591 1554061 := bbase (se 3 (by rfl) ⟨291386, by rfl⟩ : syracuseStep 1554061 = 582773) (by norm_num)
theorem B1455773 : Blo 968591 1455773 := bbase (se 3 (by rfl) ⟨272957, by rfl⟩ : syracuseStep 1455773 = 545915) (by norm_num)
theorem B1455797 : Blo 968591 1455797 := bbase (se 5 (by rfl) ⟨68240, by rfl⟩ : syracuseStep 1455797 = 136481) (by norm_num)
theorem B4732613 : Blo 968591 4732613 := bbase (se 4 (by rfl) ⟨443682, by rfl⟩ : syracuseStep 4732613 = 887365) (by norm_num)
theorem B1226441 : Blo 968591 1226441 := bbase (se 2 (by rfl) ⟨459915, by rfl⟩ : syracuseStep 1226441 = 919831) (by norm_num)
theorem B1455821 : Blo 968591 1455821 := bbase (se 3 (by rfl) ⟨272966, by rfl⟩ : syracuseStep 1455821 = 545933) (by norm_num)
theorem B1455845 : Blo 968591 1455845 := bbase (se 4 (by rfl) ⟨136485, by rfl⟩ : syracuseStep 1455845 = 272971) (by norm_num)
theorem B1455869 : Blo 968591 1455869 := bbase (se 3 (by rfl) ⟨272975, by rfl⟩ : syracuseStep 1455869 = 545951) (by norm_num)
theorem B1226497 : Blo 968591 1226497 := bbase (se 2 (by rfl) ⟨459936, by rfl⟩ : syracuseStep 1226497 = 919873) (by norm_num)
theorem B1685261 : Blo 968591 1685261 := bbase (se 3 (by rfl) ⟨315986, by rfl⟩ : syracuseStep 1685261 = 631973) (by norm_num)
theorem B1455893 : Blo 968591 1455893 := bbase (se 6 (by rfl) ⟨34122, by rfl⟩ : syracuseStep 1455893 = 68245) (by norm_num)
theorem B1455917 : Blo 968591 1455917 := bbase (se 3 (by rfl) ⟨272984, by rfl⟩ : syracuseStep 1455917 = 545969) (by norm_num)
theorem B1455941 : Blo 968591 1455941 := bbase (se 4 (by rfl) ⟨136494, by rfl⟩ : syracuseStep 1455941 = 272989) (by norm_num)
theorem B1455965 : Blo 968591 1455965 := bbase (se 3 (by rfl) ⟨272993, by rfl⟩ : syracuseStep 1455965 = 545987) (by norm_num)
theorem B1226593 : Blo 968591 1226593 := bbase (se 2 (by rfl) ⟨459972, by rfl⟩ : syracuseStep 1226593 = 919945) (by norm_num)
theorem B1455989 : Blo 968591 1455989 := bbase (se 5 (by rfl) ⟨68249, by rfl⟩ : syracuseStep 1455989 = 136499) (by norm_num)
theorem B1554317 : Blo 968591 1554317 := bbase (se 3 (by rfl) ⟨291434, by rfl⟩ : syracuseStep 1554317 = 582869) (by norm_num)
theorem B1456013 : Blo 968591 1456013 := bbase (se 3 (by rfl) ⟨273002, by rfl⟩ : syracuseStep 1456013 = 546005) (by norm_num)
theorem B1456037 : Blo 968591 1456037 := bbase (se 4 (by rfl) ⟨136503, by rfl⟩ : syracuseStep 1456037 = 273007) (by norm_num)
theorem B1456061 : Blo 968591 1456061 := bbase (se 3 (by rfl) ⟨273011, by rfl⟩ : syracuseStep 1456061 = 546023) (by norm_num)
theorem B1456085 : Blo 968591 1456085 := bbase (se 7 (by rfl) ⟨17063, by rfl⟩ : syracuseStep 1456085 = 34127) (by norm_num)
theorem B1456109 : Blo 968591 1456109 := bbase (se 3 (by rfl) ⟨273020, by rfl⟩ : syracuseStep 1456109 = 546041) (by norm_num)
theorem B1456133 : Blo 968591 1456133 := bbase (se 4 (by rfl) ⟨136512, by rfl⟩ : syracuseStep 1456133 = 273025) (by norm_num)
theorem B1226765 : Blo 968591 1226765 := bbase (se 3 (by rfl) ⟨230018, by rfl⟩ : syracuseStep 1226765 = 460037) (by norm_num)
theorem B1456157 : Blo 968591 1456157 := bbase (se 3 (by rfl) ⟨273029, by rfl⟩ : syracuseStep 1456157 = 546059) (by norm_num)
theorem B1456181 : Blo 968591 1456181 := bbase (se 5 (by rfl) ⟨68258, by rfl⟩ : syracuseStep 1456181 = 136517) (by norm_num)
theorem B1226821 : Blo 968591 1226821 := bbase (se 4 (by rfl) ⟨115014, by rfl⟩ : syracuseStep 1226821 = 230029) (by norm_num)
theorem B1554509 : Blo 968591 1554509 := bbase (se 3 (by rfl) ⟨291470, by rfl⟩ : syracuseStep 1554509 = 582941) (by norm_num)
theorem B1456205 : Blo 968591 1456205 := bbase (se 3 (by rfl) ⟨273038, by rfl⟩ : syracuseStep 1456205 = 546077) (by norm_num)
theorem B1456229 : Blo 968591 1456229 := bbase (se 4 (by rfl) ⟨136521, by rfl⟩ : syracuseStep 1456229 = 273043) (by norm_num)
theorem B1456253 : Blo 968591 1456253 := bbase (se 3 (by rfl) ⟨273047, by rfl⟩ : syracuseStep 1456253 = 546095) (by norm_num)
theorem B1456277 : Blo 968591 1456277 := bbase (se 6 (by rfl) ⟨34131, by rfl⟩ : syracuseStep 1456277 = 68263) (by norm_num)
theorem B1226917 : Blo 968591 1226917 := bbase (se 4 (by rfl) ⟨115023, by rfl⟩ : syracuseStep 1226917 = 230047) (by norm_num)
theorem B1456301 : Blo 968591 1456301 := bbase (se 3 (by rfl) ⟨273056, by rfl⟩ : syracuseStep 1456301 = 546113) (by norm_num)
theorem B1456325 : Blo 968591 1456325 := bbase (se 4 (by rfl) ⟨136530, by rfl⟩ : syracuseStep 1456325 = 273061) (by norm_num)
theorem B1456349 : Blo 968591 1456349 := bbase (se 3 (by rfl) ⟨273065, by rfl⟩ : syracuseStep 1456349 = 546131) (by norm_num)
theorem B1456373 : Blo 968591 1456373 := bbase (se 5 (by rfl) ⟨68267, by rfl⟩ : syracuseStep 1456373 = 136535) (by norm_num)
theorem B1456397 : Blo 968591 1456397 := bbase (se 3 (by rfl) ⟨273074, by rfl⟩ : syracuseStep 1456397 = 546149) (by norm_num)
theorem B1456421 : Blo 968591 1456421 := bbase (se 4 (by rfl) ⟨136539, by rfl⟩ : syracuseStep 1456421 = 273079) (by norm_num)
theorem B1456445 : Blo 968591 1456445 := bbase (se 3 (by rfl) ⟨273083, by rfl⟩ : syracuseStep 1456445 = 546167) (by norm_num)
theorem B1227089 : Blo 968591 1227089 := bbase (se 2 (by rfl) ⟨460158, by rfl⟩ : syracuseStep 1227089 = 920317) (by norm_num)
theorem B1456469 : Blo 968591 1456469 := bbase (se 10 (by rfl) ⟨2133, by rfl⟩ : syracuseStep 1456469 = 4267) (by norm_num)
theorem B1456493 : Blo 968591 1456493 := bbase (se 3 (by rfl) ⟨273092, by rfl⟩ : syracuseStep 1456493 = 546185) (by norm_num)
theorem B1456517 : Blo 968591 1456517 := bbase (se 4 (by rfl) ⟨136548, by rfl⟩ : syracuseStep 1456517 = 273097) (by norm_num)
theorem B1227145 : Blo 968591 1227145 := bbase (se 2 (by rfl) ⟨460179, by rfl⟩ : syracuseStep 1227145 = 920359) (by norm_num)
theorem B1456541 : Blo 968591 1456541 := bbase (se 3 (by rfl) ⟨273101, by rfl⟩ : syracuseStep 1456541 = 546203) (by norm_num)
theorem B1456565 : Blo 968591 1456565 := bbase (se 5 (by rfl) ⟨68276, by rfl⟩ : syracuseStep 1456565 = 136553) (by norm_num)
theorem B1456589 : Blo 968591 1456589 := bbase (se 3 (by rfl) ⟨273110, by rfl⟩ : syracuseStep 1456589 = 546221) (by norm_num)
theorem B1456613 : Blo 968591 1456613 := bbase (se 4 (by rfl) ⟨136557, by rfl⟩ : syracuseStep 1456613 = 273115) (by norm_num)
theorem B1227241 : Blo 968591 1227241 := bbase (se 2 (by rfl) ⟨460215, by rfl⟩ : syracuseStep 1227241 = 920431) (by norm_num)
theorem B1456637 : Blo 968591 1456637 := bbase (se 3 (by rfl) ⟨273119, by rfl⟩ : syracuseStep 1456637 = 546239) (by norm_num)
theorem B1456661 : Blo 968591 1456661 := bbase (se 6 (by rfl) ⟨34140, by rfl⟩ : syracuseStep 1456661 = 68281) (by norm_num)
theorem B1456685 : Blo 968591 1456685 := bbase (se 3 (by rfl) ⟨273128, by rfl⟩ : syracuseStep 1456685 = 546257) (by norm_num)
theorem B1456709 : Blo 968591 1456709 := bbase (se 4 (by rfl) ⟨136566, by rfl⟩ : syracuseStep 1456709 = 273133) (by norm_num)
theorem B1456733 : Blo 968591 1456733 := bbase (se 3 (by rfl) ⟨273137, by rfl⟩ : syracuseStep 1456733 = 546275) (by norm_num)
theorem B1456757 : Blo 968591 1456757 := bbase (se 5 (by rfl) ⟨68285, by rfl⟩ : syracuseStep 1456757 = 136571) (by norm_num)
theorem B1456781 : Blo 968591 1456781 := bbase (se 3 (by rfl) ⟨273146, by rfl⟩ : syracuseStep 1456781 = 546293) (by norm_num)
theorem B1227413 : Blo 968591 1227413 := bbase (se 6 (by rfl) ⟨28767, by rfl⟩ : syracuseStep 1227413 = 57535) (by norm_num)
theorem B1456805 : Blo 968591 1456805 := bbase (se 4 (by rfl) ⟨136575, by rfl⟩ : syracuseStep 1456805 = 273151) (by norm_num)
theorem B1456829 : Blo 968591 1456829 := bbase (se 3 (by rfl) ⟨273155, by rfl⟩ : syracuseStep 1456829 = 546311) (by norm_num)
theorem B4668101 : Blo 968591 4668101 := bbase (se 4 (by rfl) ⟨437634, by rfl⟩ : syracuseStep 4668101 = 875269) (by norm_num)
theorem B1227469 : Blo 968591 1227469 := bbase (se 3 (by rfl) ⟨230150, by rfl⟩ : syracuseStep 1227469 = 460301) (by norm_num)
theorem B1456853 : Blo 968591 1456853 := bbase (se 7 (by rfl) ⟨17072, by rfl⟩ : syracuseStep 1456853 = 34145) (by norm_num)
theorem B1456877 : Blo 968591 1456877 := bbase (se 3 (by rfl) ⟨273164, by rfl⟩ : syracuseStep 1456877 = 546329) (by norm_num)
theorem B1456901 : Blo 968591 1456901 := bbase (se 4 (by rfl) ⟨136584, by rfl⟩ : syracuseStep 1456901 = 273169) (by norm_num)
theorem B5520149 : Blo 968591 5520149 := bbase (se 6 (by rfl) ⟨129378, by rfl⟩ : syracuseStep 5520149 = 258757) (by norm_num)
theorem B1456925 : Blo 968591 1456925 := bbase (se 3 (by rfl) ⟨273173, by rfl⟩ : syracuseStep 1456925 = 546347) (by norm_num)
theorem B1227565 : Blo 968591 1227565 := bbase (se 3 (by rfl) ⟨230168, by rfl⟩ : syracuseStep 1227565 = 460337) (by norm_num)
theorem B1456949 : Blo 968591 1456949 := bbase (se 5 (by rfl) ⟨68294, by rfl⟩ : syracuseStep 1456949 = 136589) (by norm_num)
theorem B1456973 : Blo 968591 1456973 := bbase (se 3 (by rfl) ⟨273182, by rfl⟩ : syracuseStep 1456973 = 546365) (by norm_num)
theorem B1456997 : Blo 968591 1456997 := bbase (se 4 (by rfl) ⟨136593, by rfl⟩ : syracuseStep 1456997 = 273187) (by norm_num)
theorem B1457021 : Blo 968591 1457021 := bbase (se 3 (by rfl) ⟨273191, by rfl⟩ : syracuseStep 1457021 = 546383) (by norm_num)
theorem B1457045 : Blo 968591 1457045 := bbase (se 6 (by rfl) ⟨34149, by rfl⟩ : syracuseStep 1457045 = 68299) (by norm_num)
theorem B1457069 : Blo 968591 1457069 := bbase (se 3 (by rfl) ⟨273200, by rfl⟩ : syracuseStep 1457069 = 546401) (by norm_num)
theorem B1457093 : Blo 968591 1457093 := bbase (se 4 (by rfl) ⟨136602, by rfl⟩ : syracuseStep 1457093 = 273205) (by norm_num)
theorem B18889685 : Blo 968591 18889685 := bbase (se 7 (by rfl) ⟨221363, by rfl⟩ : syracuseStep 18889685 = 442727) (by norm_num)
theorem B1227737 : Blo 968591 1227737 := bbase (se 2 (by rfl) ⟨460401, by rfl⟩ : syracuseStep 1227737 = 920803) (by norm_num)
theorem B1457117 : Blo 968591 1457117 := bbase (se 3 (by rfl) ⟨273209, by rfl⟩ : syracuseStep 1457117 = 546419) (by norm_num)
theorem B1555445 : Blo 968591 1555445 := bbase (se 5 (by rfl) ⟨72911, by rfl⟩ : syracuseStep 1555445 = 145823) (by norm_num)
theorem B1457141 : Blo 968591 1457141 := bbase (se 5 (by rfl) ⟨68303, by rfl⟩ : syracuseStep 1457141 = 136607) (by norm_num)
theorem B2767877 : Blo 968591 2767877 := bbase (se 4 (by rfl) ⟨259488, by rfl⟩ : syracuseStep 2767877 = 518977) (by norm_num)
theorem B1457165 : Blo 968591 1457165 := bbase (se 3 (by rfl) ⟨273218, by rfl⟩ : syracuseStep 1457165 = 546437) (by norm_num)
theorem B1227793 : Blo 968591 1227793 := bbase (se 2 (by rfl) ⟨460422, by rfl⟩ : syracuseStep 1227793 = 920845) (by norm_num)
theorem B1457189 : Blo 968591 1457189 := bbase (se 4 (by rfl) ⟨136611, by rfl⟩ : syracuseStep 1457189 = 273223) (by norm_num)
theorem B1457213 : Blo 968591 1457213 := bbase (se 3 (by rfl) ⟨273227, by rfl⟩ : syracuseStep 1457213 = 546455) (by norm_num)
theorem B3685445 : Blo 968591 3685445 := bbase (se 4 (by rfl) ⟨345510, by rfl⟩ : syracuseStep 3685445 = 691021) (by norm_num)
theorem B1457237 : Blo 968591 1457237 := bbase (se 8 (by rfl) ⟨8538, by rfl⟩ : syracuseStep 1457237 = 17077) (by norm_num)
theorem B4144229 : Blo 968591 4144229 := bbase (se 4 (by rfl) ⟨388521, by rfl⟩ : syracuseStep 4144229 = 777043) (by norm_num)
theorem B1457261 : Blo 968591 1457261 := bbase (se 3 (by rfl) ⟨273236, by rfl⟩ : syracuseStep 1457261 = 546473) (by norm_num)
theorem B1227889 : Blo 968591 1227889 := bbase (se 2 (by rfl) ⟨460458, by rfl⟩ : syracuseStep 1227889 = 920917) (by norm_num)
theorem B1457285 : Blo 968591 1457285 := bbase (se 4 (by rfl) ⟨136620, by rfl⟩ : syracuseStep 1457285 = 273241) (by norm_num)
theorem B1457309 : Blo 968591 1457309 := bbase (se 3 (by rfl) ⟨273245, by rfl⟩ : syracuseStep 1457309 = 546491) (by norm_num)
theorem B1457333 : Blo 968591 1457333 := bbase (se 5 (by rfl) ⟨68312, by rfl⟩ : syracuseStep 1457333 = 136625) (by norm_num)
theorem B1457357 : Blo 968591 1457357 := bbase (se 3 (by rfl) ⟨273254, by rfl⟩ : syracuseStep 1457357 = 546509) (by norm_num)
theorem B1457381 : Blo 968591 1457381 := bbase (se 4 (by rfl) ⟨136629, by rfl⟩ : syracuseStep 1457381 = 273259) (by norm_num)
theorem B6208757 : Blo 968591 6208757 := bbase (se 5 (by rfl) ⟨291035, by rfl⟩ : syracuseStep 6208757 = 582071) (by norm_num)
theorem B1457405 : Blo 968591 1457405 := bbase (se 3 (by rfl) ⟨273263, by rfl⟩ : syracuseStep 1457405 = 546527) (by norm_num)
theorem B1457429 : Blo 968591 1457429 := bbase (se 6 (by rfl) ⟨34158, by rfl⟩ : syracuseStep 1457429 = 68317) (by norm_num)
theorem B1228061 : Blo 968591 1228061 := bbase (se 3 (by rfl) ⟨230261, by rfl⟩ : syracuseStep 1228061 = 460523) (by norm_num)
theorem B1457453 : Blo 968591 1457453 := bbase (se 3 (by rfl) ⟨273272, by rfl⟩ : syracuseStep 1457453 = 546545) (by norm_num)
theorem B1457477 : Blo 968591 1457477 := bbase (se 4 (by rfl) ⟨136638, by rfl⟩ : syracuseStep 1457477 = 273277) (by norm_num)
theorem B1228117 : Blo 968591 1228117 := bbase (se 11 (by rfl) ⟨899, by rfl⟩ : syracuseStep 1228117 = 1799) (by norm_num)
theorem B1457501 : Blo 968591 1457501 := bbase (se 3 (by rfl) ⟨273281, by rfl⟩ : syracuseStep 1457501 = 546563) (by norm_num)
theorem B3685733 : Blo 968591 3685733 := bbase (se 4 (by rfl) ⟨345537, by rfl⟩ : syracuseStep 3685733 = 691075) (by norm_num)
theorem B1555829 : Blo 968591 1555829 := bbase (se 5 (by rfl) ⟨72929, by rfl⟩ : syracuseStep 1555829 = 145859) (by norm_num)
theorem B1457525 : Blo 968591 1457525 := bbase (se 5 (by rfl) ⟨68321, by rfl⟩ : syracuseStep 1457525 = 136643) (by norm_num)
theorem B1457549 : Blo 968591 1457549 := bbase (se 3 (by rfl) ⟨273290, by rfl⟩ : syracuseStep 1457549 = 546581) (by norm_num)
theorem B1457573 : Blo 968591 1457573 := bbase (se 4 (by rfl) ⟨136647, by rfl⟩ : syracuseStep 1457573 = 273295) (by norm_num)
theorem B1228213 : Blo 968591 1228213 := bbase (se 5 (by rfl) ⟨57572, by rfl⟩ : syracuseStep 1228213 = 115145) (by norm_num)
theorem B1457597 : Blo 968591 1457597 := bbase (se 3 (by rfl) ⟨273299, by rfl⟩ : syracuseStep 1457597 = 546599) (by norm_num)
theorem B1457621 : Blo 968591 1457621 := bbase (se 7 (by rfl) ⟨17081, by rfl⟩ : syracuseStep 1457621 = 34163) (by norm_num)
theorem B1457645 : Blo 968591 1457645 := bbase (se 3 (by rfl) ⟨273308, by rfl⟩ : syracuseStep 1457645 = 546617) (by norm_num)
theorem B1555957 : Blo 968591 1555957 := bbase (se 5 (by rfl) ⟨72935, by rfl⟩ : syracuseStep 1555957 = 145871) (by norm_num)
theorem B1457669 : Blo 968591 1457669 := bbase (se 4 (by rfl) ⟨136656, by rfl⟩ : syracuseStep 1457669 = 273313) (by norm_num)
theorem B1457693 : Blo 968591 1457693 := bbase (se 3 (by rfl) ⟨273317, by rfl⟩ : syracuseStep 1457693 = 546635) (by norm_num)
theorem B2211365 : Blo 968591 2211365 := bbase (se 4 (by rfl) ⟨207315, by rfl⟩ : syracuseStep 2211365 = 414631) (by norm_num)
theorem B1457717 : Blo 968591 1457717 := bbase (se 5 (by rfl) ⟨68330, by rfl⟩ : syracuseStep 1457717 = 136661) (by norm_num)
theorem B1457741 : Blo 968591 1457741 := bbase (se 3 (by rfl) ⟨273326, by rfl⟩ : syracuseStep 1457741 = 546653) (by norm_num)
theorem B999001 : Blo 968591 999001 := bbase (se 2 (by rfl) ⟨374625, by rfl⟩ : syracuseStep 999001 = 749251) (by norm_num)
theorem B1228385 : Blo 968591 1228385 := bbase (se 2 (by rfl) ⟨460644, by rfl⟩ : syracuseStep 1228385 = 921289) (by norm_num)
theorem B1457765 : Blo 968591 1457765 := bbase (se 4 (by rfl) ⟨136665, by rfl⟩ : syracuseStep 1457765 = 273331) (by norm_num)
theorem B1457789 : Blo 968591 1457789 := bbase (se 3 (by rfl) ⟨273335, by rfl⟩ : syracuseStep 1457789 = 546671) (by norm_num)
theorem B1457813 : Blo 968591 1457813 := bbase (se 6 (by rfl) ⟨34167, by rfl⟩ : syracuseStep 1457813 = 68335) (by norm_num)
theorem B1228441 : Blo 968591 1228441 := bbase (se 2 (by rfl) ⟨460665, by rfl⟩ : syracuseStep 1228441 = 921331) (by norm_num)
theorem B1457837 : Blo 968591 1457837 := bbase (se 3 (by rfl) ⟨273344, by rfl⟩ : syracuseStep 1457837 = 546689) (by norm_num)
theorem B1457861 : Blo 968591 1457861 := bbase (se 4 (by rfl) ⟨136674, by rfl⟩ : syracuseStep 1457861 = 273349) (by norm_num)
theorem B1457885 : Blo 968591 1457885 := bbase (se 3 (by rfl) ⟨273353, by rfl⟩ : syracuseStep 1457885 = 546707) (by norm_num)
theorem B1457909 : Blo 968591 1457909 := bbase (se 5 (by rfl) ⟨68339, by rfl⟩ : syracuseStep 1457909 = 136679) (by norm_num)
theorem B1228537 : Blo 968591 1228537 := bbase (se 2 (by rfl) ⟨460701, by rfl⟩ : syracuseStep 1228537 = 921403) (by norm_num)
theorem B1457933 : Blo 968591 1457933 := bbase (se 3 (by rfl) ⟨273362, by rfl⟩ : syracuseStep 1457933 = 546725) (by norm_num)
theorem B2801429 : Blo 968591 2801429 := bbase (se 6 (by rfl) ⟨65658, by rfl⟩ : syracuseStep 2801429 = 131317) (by norm_num)
theorem B1457957 : Blo 968591 1457957 := bbase (se 4 (by rfl) ⟨136683, by rfl⟩ : syracuseStep 1457957 = 273367) (by norm_num)
theorem B1457981 : Blo 968591 1457981 := bbase (se 3 (by rfl) ⟨273371, by rfl⟩ : syracuseStep 1457981 = 546743) (by norm_num)
theorem B1458005 : Blo 968591 1458005 := bbase (se 9 (by rfl) ⟨4271, by rfl⟩ : syracuseStep 1458005 = 8543) (by norm_num)
theorem B1458029 : Blo 968591 1458029 := bbase (se 3 (by rfl) ⟨273380, by rfl⟩ : syracuseStep 1458029 = 546761) (by norm_num)
theorem B1458053 : Blo 968591 1458053 := bbase (se 4 (by rfl) ⟨136692, by rfl⟩ : syracuseStep 1458053 = 273385) (by norm_num)
theorem B1458077 : Blo 968591 1458077 := bbase (se 3 (by rfl) ⟨273389, by rfl⟩ : syracuseStep 1458077 = 546779) (by norm_num)
theorem B1228709 : Blo 968591 1228709 := bbase (se 4 (by rfl) ⟨115191, by rfl⟩ : syracuseStep 1228709 = 230383) (by norm_num)
theorem B1458101 : Blo 968591 1458101 := bbase (se 5 (by rfl) ⟨68348, by rfl⟩ : syracuseStep 1458101 = 136697) (by norm_num)
theorem B1458125 : Blo 968591 1458125 := bbase (se 3 (by rfl) ⟨273398, by rfl⟩ : syracuseStep 1458125 = 546797) (by norm_num)
theorem B1228765 : Blo 968591 1228765 := bbase (se 3 (by rfl) ⟨230393, by rfl⟩ : syracuseStep 1228765 = 460787) (by norm_num)
theorem B1458149 : Blo 968591 1458149 := bbase (se 4 (by rfl) ⟨136701, by rfl⟩ : syracuseStep 1458149 = 273403) (by norm_num)
theorem B1458173 : Blo 968591 1458173 := bbase (se 3 (by rfl) ⟨273407, by rfl⟩ : syracuseStep 1458173 = 546815) (by norm_num)
theorem B1458197 : Blo 968591 1458197 := bbase (se 6 (by rfl) ⟨34176, by rfl⟩ : syracuseStep 1458197 = 68353) (by norm_num)
theorem B1458221 : Blo 968591 1458221 := bbase (se 3 (by rfl) ⟨273416, by rfl⟩ : syracuseStep 1458221 = 546833) (by norm_num)
theorem B1228861 : Blo 968591 1228861 := bbase (se 3 (by rfl) ⟨230411, by rfl⟩ : syracuseStep 1228861 = 460823) (by norm_num)
theorem B1458245 : Blo 968591 1458245 := bbase (se 4 (by rfl) ⟨136710, by rfl⟩ : syracuseStep 1458245 = 273421) (by norm_num)
theorem B1458269 : Blo 968591 1458269 := bbase (se 3 (by rfl) ⟨273425, by rfl⟩ : syracuseStep 1458269 = 546851) (by norm_num)
theorem B1458293 : Blo 968591 1458293 := bbase (se 5 (by rfl) ⟨68357, by rfl⟩ : syracuseStep 1458293 = 136715) (by norm_num)
theorem B1458317 : Blo 968591 1458317 := bbase (se 3 (by rfl) ⟨273434, by rfl⟩ : syracuseStep 1458317 = 546869) (by norm_num)
theorem B1458341 : Blo 968591 1458341 := bbase (se 4 (by rfl) ⟨136719, by rfl⟩ : syracuseStep 1458341 = 273439) (by norm_num)
theorem B2769061 : Blo 968591 2769061 := bbase (se 4 (by rfl) ⟨259599, by rfl⟩ : syracuseStep 2769061 = 519199) (by norm_num)
theorem B1458365 : Blo 968591 1458365 := bbase (se 3 (by rfl) ⟨273443, by rfl⟩ : syracuseStep 1458365 = 546887) (by norm_num)
theorem B1458389 : Blo 968591 1458389 := bbase (se 7 (by rfl) ⟨17090, by rfl⟩ : syracuseStep 1458389 = 34181) (by norm_num)
theorem B1229033 : Blo 968591 1229033 := bbase (se 2 (by rfl) ⟨460887, by rfl⟩ : syracuseStep 1229033 = 921775) (by norm_num)
theorem B1458413 : Blo 968591 1458413 := bbase (se 3 (by rfl) ⟨273452, by rfl⟩ : syracuseStep 1458413 = 546905) (by norm_num)
theorem B1458437 : Blo 968591 1458437 := bbase (se 4 (by rfl) ⟨136728, by rfl⟩ : syracuseStep 1458437 = 273457) (by norm_num)
theorem B2179349 : Blo 968591 2179349 := bbase (se 6 (by rfl) ⟨51078, by rfl⟩ : syracuseStep 2179349 = 102157) (by norm_num)
theorem B1458461 : Blo 968591 1458461 := bbase (se 3 (by rfl) ⟨273461, by rfl⟩ : syracuseStep 1458461 = 546923) (by norm_num)
theorem B1229089 : Blo 968591 1229089 := bbase (se 2 (by rfl) ⟨460908, by rfl⟩ : syracuseStep 1229089 = 921817) (by norm_num)
theorem B1458485 : Blo 968591 1458485 := bbase (se 5 (by rfl) ⟨68366, by rfl⟩ : syracuseStep 1458485 = 136733) (by norm_num)
theorem B2769221 : Blo 968591 2769221 := bbase (se 4 (by rfl) ⟨259614, by rfl⟩ : syracuseStep 2769221 = 519229) (by norm_num)
theorem B1458509 : Blo 968591 1458509 := bbase (se 3 (by rfl) ⟨273470, by rfl⟩ : syracuseStep 1458509 = 546941) (by norm_num)
theorem B2179421 : Blo 968591 2179421 := bbase (se 3 (by rfl) ⟨408641, by rfl⟩ : syracuseStep 2179421 = 817283) (by norm_num)
theorem B1458533 : Blo 968591 1458533 := bbase (se 4 (by rfl) ⟨136737, by rfl⟩ : syracuseStep 1458533 = 273475) (by norm_num)
theorem B1458557 : Blo 968591 1458557 := bbase (se 3 (by rfl) ⟨273479, by rfl⟩ : syracuseStep 1458557 = 546959) (by norm_num)
theorem B1229185 : Blo 968591 1229185 := bbase (se 2 (by rfl) ⟨460944, by rfl⟩ : syracuseStep 1229185 = 921889) (by norm_num)
theorem B1458581 : Blo 968591 1458581 := bbase (se 6 (by rfl) ⟨34185, by rfl⟩ : syracuseStep 1458581 = 68371) (by norm_num)
theorem B2179493 : Blo 968591 2179493 := bbase (se 4 (by rfl) ⟨204327, by rfl⟩ : syracuseStep 2179493 = 408655) (by norm_num)
theorem B1458605 : Blo 968591 1458605 := bbase (se 3 (by rfl) ⟨273488, by rfl⟩ : syracuseStep 1458605 = 546977) (by norm_num)
theorem B1458629 : Blo 968591 1458629 := bbase (se 4 (by rfl) ⟨136746, by rfl⟩ : syracuseStep 1458629 = 273493) (by norm_num)
theorem B1556957 : Blo 968591 1556957 := bbase (se 3 (by rfl) ⟨291929, by rfl⟩ : syracuseStep 1556957 = 583859) (by norm_num)
theorem B1458653 : Blo 968591 1458653 := bbase (se 3 (by rfl) ⟨273497, by rfl⟩ : syracuseStep 1458653 = 546995) (by norm_num)
theorem B2179565 : Blo 968591 2179565 := bbase (se 3 (by rfl) ⟨408668, by rfl⟩ : syracuseStep 2179565 = 817337) (by norm_num)
theorem B1458677 : Blo 968591 1458677 := bbase (se 5 (by rfl) ⟨68375, by rfl⟩ : syracuseStep 1458677 = 136751) (by norm_num)
theorem B3686917 : Blo 968591 3686917 := bbase (se 4 (by rfl) ⟨345648, by rfl⟩ : syracuseStep 3686917 = 691297) (by norm_num)
theorem B1458701 : Blo 968591 1458701 := bbase (se 3 (by rfl) ⟨273506, by rfl⟩ : syracuseStep 1458701 = 547013) (by norm_num)
theorem B1458725 : Blo 968591 1458725 := bbase (se 4 (by rfl) ⟨136755, by rfl⟩ : syracuseStep 1458725 = 273511) (by norm_num)
theorem B1229357 : Blo 968591 1229357 := bbase (se 3 (by rfl) ⟨230504, by rfl⟩ : syracuseStep 1229357 = 461009) (by norm_num)
theorem B2179637 : Blo 968591 2179637 := bbase (se 5 (by rfl) ⟨102170, by rfl⟩ : syracuseStep 2179637 = 204341) (by norm_num)
theorem B2769461 : Blo 968591 2769461 := bbase (se 5 (by rfl) ⟨129818, by rfl⟩ : syracuseStep 2769461 = 259637) (by norm_num)
theorem B1458749 : Blo 968591 1458749 := bbase (se 3 (by rfl) ⟨273515, by rfl⟩ : syracuseStep 1458749 = 547031) (by norm_num)
theorem B1163845 : Blo 968591 1163845 := bbase (se 4 (by rfl) ⟨109110, by rfl⟩ : syracuseStep 1163845 = 218221) (by norm_num)
theorem B1458773 : Blo 968591 1458773 := bbase (se 8 (by rfl) ⟨8547, by rfl⟩ : syracuseStep 1458773 = 17095) (by norm_num)
theorem B1557085 : Blo 968591 1557085 := bbase (se 3 (by rfl) ⟨291953, by rfl⟩ : syracuseStep 1557085 = 583907) (by norm_num)
theorem B1229413 : Blo 968591 1229413 := bbase (se 4 (by rfl) ⟨115257, by rfl⟩ : syracuseStep 1229413 = 230515) (by norm_num)
theorem B1458797 : Blo 968591 1458797 := bbase (se 3 (by rfl) ⟨273524, by rfl⟩ : syracuseStep 1458797 = 547049) (by norm_num)
theorem B2179709 : Blo 968591 2179709 := bbase (se 3 (by rfl) ⟨408695, by rfl⟩ : syracuseStep 2179709 = 817391) (by norm_num)
theorem B1458821 : Blo 968591 1458821 := bbase (se 4 (by rfl) ⟨136764, by rfl⟩ : syracuseStep 1458821 = 273529) (by norm_num)
theorem B1458845 : Blo 968591 1458845 := bbase (se 3 (by rfl) ⟨273533, by rfl⟩ : syracuseStep 1458845 = 547067) (by norm_num)
theorem B1458869 : Blo 968591 1458869 := bbase (se 5 (by rfl) ⟨68384, by rfl⟩ : syracuseStep 1458869 = 136769) (by norm_num)
theorem B2179781 : Blo 968591 2179781 := bbase (se 4 (by rfl) ⟨204354, by rfl⟩ : syracuseStep 2179781 = 408709) (by norm_num)
theorem B1229509 : Blo 968591 1229509 := bbase (se 4 (by rfl) ⟨115266, by rfl⟩ : syracuseStep 1229509 = 230533) (by norm_num)
theorem B1164037 : Blo 968591 1164037 := bbase (se 4 (by rfl) ⟨109128, by rfl⟩ : syracuseStep 1164037 = 218257) (by norm_num)
theorem B2179853 : Blo 968591 2179853 := bbase (se 3 (by rfl) ⟨408722, by rfl⟩ : syracuseStep 2179853 = 817445) (by norm_num)
theorem B1164061 : Blo 968591 1164061 := bbase (se 3 (by rfl) ⟨218261, by rfl⟩ : syracuseStep 1164061 = 436523) (by norm_num)
theorem B1164065 : Blo 968591 1164065 := bbase (se 2 (by rfl) ⟨436524, by rfl⟩ : syracuseStep 1164065 = 873049) (by norm_num)
theorem B3687221 : Blo 968591 3687221 := bbase (se 5 (by rfl) ⟨172838, by rfl⟩ : syracuseStep 3687221 = 345677) (by norm_num)
theorem B2179925 : Blo 968591 2179925 := bbase (se 9 (by rfl) ⟨6386, by rfl⟩ : syracuseStep 2179925 = 12773) (by norm_num)
theorem B4146005 : Blo 968591 4146005 := bbase (se 9 (by rfl) ⟨12146, by rfl⟩ : syracuseStep 4146005 = 24293) (by norm_num)
theorem B4670293 : Blo 968591 4670293 := bbase (se 9 (by rfl) ⟨13682, by rfl⟩ : syracuseStep 4670293 = 27365) (by norm_num)
theorem B1229681 : Blo 968591 1229681 := bbase (se 2 (by rfl) ⟨461130, by rfl⟩ : syracuseStep 1229681 = 922261) (by norm_num)
theorem B2179997 : Blo 968591 2179997 := bbase (se 3 (by rfl) ⟨408749, by rfl⟩ : syracuseStep 2179997 = 817499) (by norm_num)
theorem B1229737 : Blo 968591 1229737 := bbase (se 2 (by rfl) ⟨461151, by rfl⟩ : syracuseStep 1229737 = 922303) (by norm_num)
theorem B5522357 : Blo 968591 5522357 := bbase (se 5 (by rfl) ⟨258860, by rfl⟩ : syracuseStep 5522357 = 517721) (by norm_num)
theorem B1557469 : Blo 968591 1557469 := bbase (se 3 (by rfl) ⟨292025, by rfl⟩ : syracuseStep 1557469 = 584051) (by norm_num)
theorem B2180069 : Blo 968591 2180069 := bbase (se 4 (by rfl) ⟨204381, by rfl⟩ : syracuseStep 2180069 = 408763) (by norm_num)
theorem B1229833 : Blo 968591 1229833 := bbase (se 2 (by rfl) ⟨461187, by rfl⟩ : syracuseStep 1229833 = 922375) (by norm_num)
theorem B2180141 : Blo 968591 2180141 := bbase (se 3 (by rfl) ⟨408776, by rfl⟩ : syracuseStep 2180141 = 817553) (by norm_num)
theorem B8275061 : Blo 968591 8275061 := bbase (se 5 (by rfl) ⟨387893, by rfl⟩ : syracuseStep 8275061 = 775787) (by norm_num)
theorem B2180213 : Blo 968591 2180213 := bbase (se 5 (by rfl) ⟨102197, by rfl⟩ : syracuseStep 2180213 = 204395) (by norm_num)
theorem B1230005 : Blo 968591 1230005 := bbase (se 5 (by rfl) ⟨57656, by rfl⟩ : syracuseStep 1230005 = 115313) (by norm_num)
theorem B2180285 : Blo 968591 2180285 := bbase (se 3 (by rfl) ⟨408803, by rfl⟩ : syracuseStep 2180285 = 817607) (by norm_num)
theorem B1557725 : Blo 968591 1557725 := bbase (se 3 (by rfl) ⟨292073, by rfl⟩ : syracuseStep 1557725 = 584147) (by norm_num)
theorem B1230061 : Blo 968591 1230061 := bbase (se 3 (by rfl) ⟨230636, by rfl⟩ : syracuseStep 1230061 = 461273) (by norm_num)
theorem B2180357 : Blo 968591 2180357 := bbase (se 4 (by rfl) ⟨204408, by rfl⟩ : syracuseStep 2180357 = 408817) (by norm_num)
theorem B1164565 : Blo 968591 1164565 := bbase (se 6 (by rfl) ⟨27294, by rfl⟩ : syracuseStep 1164565 = 54589) (by norm_num)
theorem B2180429 : Blo 968591 2180429 := bbase (se 3 (by rfl) ⟨408830, by rfl⟩ : syracuseStep 2180429 = 817661) (by norm_num)
theorem B1230157 : Blo 968591 1230157 := bbase (se 3 (by rfl) ⟨230654, by rfl⟩ : syracuseStep 1230157 = 461309) (by norm_num)
theorem B1164661 : Blo 968591 1164661 := bbase (se 5 (by rfl) ⟨54593, by rfl⟩ : syracuseStep 1164661 = 109187) (by norm_num)
theorem B2180501 : Blo 968591 2180501 := bbase (se 6 (by rfl) ⟨51105, by rfl⟩ : syracuseStep 2180501 = 102211) (by norm_num)
theorem B2180573 : Blo 968591 2180573 := bbase (se 3 (by rfl) ⟨408857, by rfl⟩ : syracuseStep 2180573 = 817715) (by norm_num)
theorem B1230329 : Blo 968591 1230329 := bbase (se 2 (by rfl) ⟨461373, by rfl⟩ : syracuseStep 1230329 = 922747) (by norm_num)
theorem B2180645 : Blo 968591 2180645 := bbase (se 4 (by rfl) ⟨204435, by rfl⟩ : syracuseStep 2180645 = 408871) (by norm_num)
theorem B1230385 : Blo 968591 1230385 := bbase (se 2 (by rfl) ⟨461394, by rfl⟩ : syracuseStep 1230385 = 922789) (by norm_num)
theorem B8308277 : Blo 968591 8308277 := bbase (se 5 (by rfl) ⟨389450, by rfl⟩ : syracuseStep 8308277 = 778901) (by norm_num)
theorem B2180717 : Blo 968591 2180717 := bbase (se 3 (by rfl) ⟨408884, by rfl⟩ : syracuseStep 2180717 = 817769) (by norm_num)
theorem B1230481 : Blo 968591 1230481 := bbase (se 2 (by rfl) ⟨461430, by rfl⟩ : syracuseStep 1230481 = 922861) (by norm_num)
theorem B2180789 : Blo 968591 2180789 := bbase (se 5 (by rfl) ⟨102224, by rfl⟩ : syracuseStep 2180789 = 204449) (by norm_num)
theorem B2213621 : Blo 968591 2213621 := bbase (se 5 (by rfl) ⟨103763, by rfl⟩ : syracuseStep 2213621 = 207527) (by norm_num)
theorem B2180861 : Blo 968591 2180861 := bbase (se 3 (by rfl) ⟨408911, by rfl⟩ : syracuseStep 2180861 = 817823) (by norm_num)
theorem B4146997 : Blo 968591 4146997 := bbase (se 5 (by rfl) ⟨194390, by rfl⟩ : syracuseStep 4146997 = 388781) (by norm_num)
theorem B1230653 : Blo 968591 1230653 := bbase (se 3 (by rfl) ⟨230747, by rfl⟩ : syracuseStep 1230653 = 461495) (by norm_num)
theorem B2180933 : Blo 968591 2180933 := bbase (se 4 (by rfl) ⟨204462, by rfl⟩ : syracuseStep 2180933 = 408925) (by norm_num)
theorem B1230709 : Blo 968591 1230709 := bbase (se 5 (by rfl) ⟨57689, by rfl⟩ : syracuseStep 1230709 = 115379) (by norm_num)
theorem B2181005 : Blo 968591 2181005 := bbase (se 3 (by rfl) ⟨408938, by rfl⟩ : syracuseStep 2181005 = 817877) (by norm_num)
theorem B2181077 : Blo 968591 2181077 := bbase (se 7 (by rfl) ⟨25559, by rfl⟩ : syracuseStep 2181077 = 51119) (by norm_num)
theorem B1230805 : Blo 968591 1230805 := bbase (se 7 (by rfl) ⟨14423, by rfl⟩ : syracuseStep 1230805 = 28847) (by norm_num)
theorem B2181149 : Blo 968591 2181149 := bbase (se 3 (by rfl) ⟨408965, by rfl⟩ : syracuseStep 2181149 = 817931) (by norm_num)
theorem B2181221 : Blo 968591 2181221 := bbase (se 4 (by rfl) ⟨204489, by rfl⟩ : syracuseStep 2181221 = 408979) (by norm_num)
theorem B12601493 : Blo 968591 12601493 := bbase (se 6 (by rfl) ⟨295347, by rfl⟩ : syracuseStep 12601493 = 590695) (by norm_num)
theorem B2181293 : Blo 968591 2181293 := bbase (se 3 (by rfl) ⟨408992, by rfl⟩ : syracuseStep 2181293 = 817985) (by norm_num)
theorem B1034417 : Blo 968591 1034417 := bbase (se 2 (by rfl) ⟨387906, by rfl⟩ : syracuseStep 1034417 = 775813) (by norm_num)
theorem B2181365 : Blo 968591 2181365 := bbase (se 5 (by rfl) ⟨102251, by rfl⟩ : syracuseStep 2181365 = 204503) (by norm_num)
theorem B9324821 : Blo 968591 9324821 := bbase (se 6 (by rfl) ⟨218550, by rfl⟩ : syracuseStep 9324821 = 437101) (by norm_num)
theorem B2181437 : Blo 968591 2181437 := bbase (se 3 (by rfl) ⟨409019, by rfl⟩ : syracuseStep 2181437 = 818039) (by norm_num)
theorem B1165637 : Blo 968591 1165637 := bbase (se 4 (by rfl) ⟨109278, by rfl⟩ : syracuseStep 1165637 = 218557) (by norm_num)
theorem B2181509 : Blo 968591 2181509 := bbase (se 4 (by rfl) ⟨204516, by rfl⟩ : syracuseStep 2181509 = 409033) (by norm_num)
theorem B2181581 : Blo 968591 2181581 := bbase (se 3 (by rfl) ⟨409046, by rfl⟩ : syracuseStep 2181581 = 818093) (by norm_num)
theorem B2181653 : Blo 968591 2181653 := bbase (se 6 (by rfl) ⟨51132, by rfl⟩ : syracuseStep 2181653 = 102265) (by norm_num)
theorem B2214469 : Blo 968591 2214469 := bbase (se 4 (by rfl) ⟨207606, by rfl⟩ : syracuseStep 2214469 = 415213) (by norm_num)
theorem B11061845 : Blo 968591 11061845 := bbase (se 8 (by rfl) ⟨64815, by rfl⟩ : syracuseStep 11061845 = 129631) (by norm_num)
theorem B2181725 : Blo 968591 2181725 := bbase (se 3 (by rfl) ⟨409073, by rfl⟩ : syracuseStep 2181725 = 818147) (by norm_num)
theorem B1034861 : Blo 968591 1034861 := bbase (se 3 (by rfl) ⟨194036, by rfl⟩ : syracuseStep 1034861 = 388073) (by norm_num)
theorem B2181797 : Blo 968591 2181797 := bbase (se 4 (by rfl) ⟨204543, by rfl⟩ : syracuseStep 2181797 = 409087) (by norm_num)
theorem B2181869 : Blo 968591 2181869 := bbase (se 3 (by rfl) ⟨409100, by rfl⟩ : syracuseStep 2181869 = 818201) (by norm_num)
theorem B1166113 : Blo 968591 1166113 := bbase (se 2 (by rfl) ⟨437292, by rfl⟩ : syracuseStep 1166113 = 874585) (by norm_num)
theorem B2181941 : Blo 968591 2181941 := bbase (se 5 (by rfl) ⟨102278, by rfl⟩ : syracuseStep 2181941 = 204557) (by norm_num)
theorem B1166141 : Blo 968591 1166141 := bbase (se 3 (by rfl) ⟨218651, by rfl⟩ : syracuseStep 1166141 = 437303) (by norm_num)
theorem B1035109 : Blo 968591 1035109 := bbase (se 4 (by rfl) ⟨97041, by rfl⟩ : syracuseStep 1035109 = 194083) (by norm_num)
theorem B3689333 : Blo 968591 3689333 := bbase (se 5 (by rfl) ⟨172937, by rfl⟩ : syracuseStep 3689333 = 345875) (by norm_num)
theorem B2182013 : Blo 968591 2182013 := bbase (se 3 (by rfl) ⟨409127, by rfl⟩ : syracuseStep 2182013 = 818255) (by norm_num)
theorem B3492773 : Blo 968591 3492773 := bbase (se 4 (by rfl) ⟨327447, by rfl⟩ : syracuseStep 3492773 = 654895) (by norm_num)
theorem B2182085 : Blo 968591 2182085 := bbase (se 4 (by rfl) ⟨204570, by rfl⟩ : syracuseStep 2182085 = 409141) (by norm_num)
theorem B1657813 : Blo 968591 1657813 := bbase (se 7 (by rfl) ⟨19427, by rfl⟩ : syracuseStep 1657813 = 38855) (by norm_num)
theorem B1166329 : Blo 968591 1166329 := bbase (se 2 (by rfl) ⟨437373, by rfl⟩ : syracuseStep 1166329 = 874747) (by norm_num)
theorem B2182157 : Blo 968591 2182157 := bbase (se 3 (by rfl) ⟨409154, by rfl⟩ : syracuseStep 2182157 = 818309) (by norm_num)
theorem B2182229 : Blo 968591 2182229 := bbase (se 8 (by rfl) ⟨12786, by rfl⟩ : syracuseStep 2182229 = 25573) (by norm_num)
theorem B1166449 : Blo 968591 1166449 := bbase (se 2 (by rfl) ⟨437418, by rfl⟩ : syracuseStep 1166449 = 874837) (by norm_num)
theorem B3689621 : Blo 968591 3689621 := bbase (se 6 (by rfl) ⟨86475, by rfl⟩ : syracuseStep 3689621 = 172951) (by norm_num)
theorem B2182301 : Blo 968591 2182301 := bbase (se 3 (by rfl) ⟨409181, by rfl⟩ : syracuseStep 2182301 = 818363) (by norm_num)
theorem B3493061 : Blo 968591 3493061 := bbase (se 4 (by rfl) ⟨327474, by rfl⟩ : syracuseStep 3493061 = 654949) (by norm_num)
theorem B2182373 : Blo 968591 2182373 := bbase (se 4 (by rfl) ⟨204597, by rfl⟩ : syracuseStep 2182373 = 409195) (by norm_num)
theorem B1035541 : Blo 968591 1035541 := bbase (se 6 (by rfl) ⟨24270, by rfl⟩ : syracuseStep 1035541 = 48541) (by norm_num)
theorem B2182445 : Blo 968591 2182445 := bbase (se 3 (by rfl) ⟨409208, by rfl⟩ : syracuseStep 2182445 = 818417) (by norm_num)
theorem B1035613 : Blo 968591 1035613 := bbase (se 3 (by rfl) ⟨194177, by rfl⟩ : syracuseStep 1035613 = 388355) (by norm_num)
theorem B2182517 : Blo 968591 2182517 := bbase (se 5 (by rfl) ⟨102305, by rfl⟩ : syracuseStep 2182517 = 204611) (by norm_num)
theorem B2182589 : Blo 968591 2182589 := bbase (se 3 (by rfl) ⟨409235, by rfl⟩ : syracuseStep 2182589 = 818471) (by norm_num)
theorem B2182661 : Blo 968591 2182661 := bbase (se 4 (by rfl) ⟨204624, by rfl⟩ : syracuseStep 2182661 = 409249) (by norm_num)
theorem B2182733 : Blo 968591 2182733 := bbase (se 3 (by rfl) ⟨409262, by rfl⟩ : syracuseStep 2182733 = 818525) (by norm_num)
theorem B2182805 : Blo 968591 2182805 := bbase (se 6 (by rfl) ⟨51159, by rfl⟩ : syracuseStep 2182805 = 102319) (by norm_num)
theorem B1035985 : Blo 968591 1035985 := bbase (se 2 (by rfl) ⟨388494, by rfl⟩ : syracuseStep 1035985 = 776989) (by norm_num)
theorem B2215637 : Blo 968591 2215637 := bbase (se 7 (by rfl) ⟨25964, by rfl⟩ : syracuseStep 2215637 = 51929) (by norm_num)
theorem B2182877 : Blo 968591 2182877 := bbase (se 3 (by rfl) ⟨409289, by rfl⟩ : syracuseStep 2182877 = 818579) (by norm_num)
theorem B2182949 : Blo 968591 2182949 := bbase (se 4 (by rfl) ⟨204651, by rfl⟩ : syracuseStep 2182949 = 409303) (by norm_num)
theorem B2183021 : Blo 968591 2183021 := bbase (se 3 (by rfl) ⟨409316, by rfl⟩ : syracuseStep 2183021 = 818633) (by norm_num)
theorem B2183093 : Blo 968591 2183093 := bbase (se 5 (by rfl) ⟨102332, by rfl⟩ : syracuseStep 2183093 = 204665) (by norm_num)
theorem B7360469 : Blo 968591 7360469 := bbase (se 7 (by rfl) ⟨86255, by rfl⟩ : syracuseStep 7360469 = 172511) (by norm_num)
theorem B970729 : Blo 968591 970729 := bbase (se 2 (by rfl) ⟨364023, by rfl⟩ : syracuseStep 970729 = 728047) (by norm_num)
theorem B2183165 : Blo 968591 2183165 := bbase (se 3 (by rfl) ⟨409343, by rfl⟩ : syracuseStep 2183165 = 818687) (by norm_num)
theorem B8278037 : Blo 968591 8278037 := bbase (se 6 (by rfl) ⟨194016, by rfl⟩ : syracuseStep 8278037 = 388033) (by norm_num)
theorem B2183237 : Blo 968591 2183237 := bbase (se 4 (by rfl) ⟨204678, by rfl⟩ : syracuseStep 2183237 = 409357) (by norm_num)
theorem B1036361 : Blo 968591 1036361 := bbase (se 2 (by rfl) ⟨388635, by rfl⟩ : syracuseStep 1036361 = 777271) (by norm_num)
theorem B2183309 : Blo 968591 2183309 := bbase (se 3 (by rfl) ⟨409370, by rfl⟩ : syracuseStep 2183309 = 818741) (by norm_num)
theorem B1036433 : Blo 968591 1036433 := bbase (se 2 (by rfl) ⟨388662, by rfl⟩ : syracuseStep 1036433 = 777325) (by norm_num)
theorem B2183381 : Blo 968591 2183381 := bbase (se 7 (by rfl) ⟨25586, by rfl⟩ : syracuseStep 2183381 = 51173) (by norm_num)
theorem B2183453 : Blo 968591 2183453 := bbase (se 3 (by rfl) ⟨409397, by rfl⟩ : syracuseStep 2183453 = 818795) (by norm_num)
theorem B3690805 : Blo 968591 3690805 := bbase (se 5 (by rfl) ⟨173006, by rfl⟩ : syracuseStep 3690805 = 346013) (by norm_num)
theorem B1036621 : Blo 968591 1036621 := bbase (se 3 (by rfl) ⟨194366, by rfl⟩ : syracuseStep 1036621 = 388733) (by norm_num)
theorem B2183525 : Blo 968591 2183525 := bbase (se 4 (by rfl) ⟨204705, by rfl⟩ : syracuseStep 2183525 = 409411) (by norm_num)
theorem B2183597 : Blo 968591 2183597 := bbase (se 3 (by rfl) ⟨409424, by rfl⟩ : syracuseStep 2183597 = 818849) (by norm_num)
theorem B2183669 : Blo 968591 2183669 := bbase (se 5 (by rfl) ⟨102359, by rfl⟩ : syracuseStep 2183669 = 204719) (by norm_num)
theorem B1036805 : Blo 968591 1036805 := bbase (se 4 (by rfl) ⟨97200, by rfl⟩ : syracuseStep 1036805 = 194401) (by norm_num)
theorem B2183741 : Blo 968591 2183741 := bbase (se 3 (by rfl) ⟨409451, by rfl⟩ : syracuseStep 2183741 = 818903) (by norm_num)
theorem B3691109 : Blo 968591 3691109 := bbase (se 4 (by rfl) ⟨346041, by rfl⟩ : syracuseStep 3691109 = 692083) (by norm_num)
theorem B2183813 : Blo 968591 2183813 := bbase (se 4 (by rfl) ⟨204732, by rfl⟩ : syracuseStep 2183813 = 409465) (by norm_num)
theorem B1168025 : Blo 968591 1168025 := bbase (se 2 (by rfl) ⟨438009, by rfl⟩ : syracuseStep 1168025 = 876019) (by norm_num)
theorem B2183885 : Blo 968591 2183885 := bbase (se 3 (by rfl) ⟨409478, by rfl⟩ : syracuseStep 2183885 = 818957) (by norm_num)
theorem B2216693 : Blo 968591 2216693 := bbase (se 5 (by rfl) ⟨103907, by rfl⟩ : syracuseStep 2216693 = 207815) (by norm_num)
theorem B2183957 : Blo 968591 2183957 := bbase (se 6 (by rfl) ⟨51186, by rfl⟩ : syracuseStep 2183957 = 102373) (by norm_num)
theorem B2184029 : Blo 968591 2184029 := bbase (se 3 (by rfl) ⟨409505, by rfl⟩ : syracuseStep 2184029 = 819011) (by norm_num)
theorem B2184101 : Blo 968591 2184101 := bbase (se 4 (by rfl) ⟨204759, by rfl⟩ : syracuseStep 2184101 = 409519) (by norm_num)
theorem B2184173 : Blo 968591 2184173 := bbase (se 3 (by rfl) ⟨409532, by rfl⟩ : syracuseStep 2184173 = 819065) (by norm_num)
theorem B2184245 : Blo 968591 2184245 := bbase (se 5 (by rfl) ⟨102386, by rfl⟩ : syracuseStep 2184245 = 204773) (by norm_num)
theorem B2184317 : Blo 968591 2184317 := bbase (se 3 (by rfl) ⟨409559, by rfl⟩ : syracuseStep 2184317 = 819119) (by norm_num)
theorem B2184389 : Blo 968591 2184389 := bbase (se 4 (by rfl) ⟨204786, by rfl⟩ : syracuseStep 2184389 = 409573) (by norm_num)
theorem B1037557 : Blo 968591 1037557 := bbase (se 5 (by rfl) ⟨48635, by rfl⟩ : syracuseStep 1037557 = 97271) (by norm_num)
theorem B2184461 : Blo 968591 2184461 := bbase (se 3 (by rfl) ⟨409586, by rfl⟩ : syracuseStep 2184461 = 819173) (by norm_num)
theorem B1037629 : Blo 968591 1037629 := bbase (se 3 (by rfl) ⟨194555, by rfl⟩ : syracuseStep 1037629 = 389111) (by norm_num)
theorem B2184533 : Blo 968591 2184533 := bbase (se 18 (by rfl) ⟨12, by rfl⟩ : syracuseStep 2184533 = 25) (by norm_num)
theorem B2184605 : Blo 968591 2184605 := bbase (se 3 (by rfl) ⟨409613, by rfl⟩ : syracuseStep 2184605 = 819227) (by norm_num)
theorem B2184677 : Blo 968591 2184677 := bbase (se 4 (by rfl) ⟨204813, by rfl⟩ : syracuseStep 2184677 = 409627) (by norm_num)
theorem B1037809 : Blo 968591 1037809 := bbase (se 2 (by rfl) ⟨389178, by rfl⟩ : syracuseStep 1037809 = 778357) (by norm_num)
theorem B2184749 : Blo 968591 2184749 := bbase (se 3 (by rfl) ⟨409640, by rfl⟩ : syracuseStep 2184749 = 819281) (by norm_num)
theorem B4904549 : Blo 968591 4904549 := bbase (se 4 (by rfl) ⟨459801, by rfl⟩ : syracuseStep 4904549 = 919603) (by norm_num)
theorem B2184821 : Blo 968591 2184821 := bbase (se 5 (by rfl) ⟨102413, by rfl⟩ : syracuseStep 2184821 = 204827) (by norm_num)
theorem B2184893 : Blo 968591 2184893 := bbase (se 3 (by rfl) ⟨409667, by rfl⟩ : syracuseStep 2184893 = 819335) (by norm_num)
theorem B2184965 : Blo 968591 2184965 := bbase (se 4 (by rfl) ⟨204840, by rfl⟩ : syracuseStep 2184965 = 409681) (by norm_num)
theorem B2185037 : Blo 968591 2185037 := bbase (se 3 (by rfl) ⟨409694, by rfl⟩ : syracuseStep 2185037 = 819389) (by norm_num)
theorem B2185109 : Blo 968591 2185109 := bbase (se 6 (by rfl) ⟨51213, by rfl⟩ : syracuseStep 2185109 = 102427) (by norm_num)
theorem B1038253 : Blo 968591 1038253 := bbase (se 3 (by rfl) ⟨194672, by rfl⟩ : syracuseStep 1038253 = 389345) (by norm_num)
theorem B2185181 : Blo 968591 2185181 := bbase (se 3 (by rfl) ⟨409721, by rfl⟩ : syracuseStep 2185181 = 819443) (by norm_num)
theorem B1660933 : Blo 968591 1660933 := bbase (se 4 (by rfl) ⟨155712, by rfl⟩ : syracuseStep 1660933 = 311425) (by norm_num)
theorem B2185253 : Blo 968591 2185253 := bbase (se 4 (by rfl) ⟨204867, by rfl⟩ : syracuseStep 2185253 = 409735) (by norm_num)
theorem B1038377 : Blo 968591 1038377 := bbase (se 2 (by rfl) ⟨389391, by rfl⟩ : syracuseStep 1038377 = 778783) (by norm_num)
theorem B2185325 : Blo 968591 2185325 := bbase (se 3 (by rfl) ⟨409748, by rfl⟩ : syracuseStep 2185325 = 819497) (by norm_num)
theorem B3496117 : Blo 968591 3496117 := bbase (se 5 (by rfl) ⟨163880, by rfl⟩ : syracuseStep 3496117 = 327761) (by norm_num)
theorem B2185397 : Blo 968591 2185397 := bbase (se 5 (by rfl) ⟨102440, by rfl⟩ : syracuseStep 2185397 = 204881) (by norm_num)
theorem B2185469 : Blo 968591 2185469 := bbase (se 3 (by rfl) ⟨409775, by rfl⟩ : syracuseStep 2185469 = 819551) (by norm_num)
theorem B2185541 : Blo 968591 2185541 := bbase (se 4 (by rfl) ⟨204894, by rfl⟩ : syracuseStep 2185541 = 409789) (by norm_num)
theorem B2185613 : Blo 968591 2185613 := bbase (se 3 (by rfl) ⟨409802, by rfl⟩ : syracuseStep 2185613 = 819605) (by norm_num)
theorem B7985557 : Blo 968591 7985557 := bbase (se 6 (by rfl) ⟨187161, by rfl⟩ : syracuseStep 7985557 = 374323) (by norm_num)
theorem B2185685 : Blo 968591 2185685 := bbase (se 7 (by rfl) ⟨25613, by rfl⟩ : syracuseStep 2185685 = 51227) (by norm_num)
theorem B2185757 : Blo 968591 2185757 := bbase (se 3 (by rfl) ⟨409829, by rfl⟩ : syracuseStep 2185757 = 819659) (by norm_num)
theorem B2185829 : Blo 968591 2185829 := bbase (se 4 (by rfl) ⟨204921, by rfl⟩ : syracuseStep 2185829 = 409843) (by norm_num)
theorem B2185901 : Blo 968591 2185901 := bbase (se 3 (by rfl) ⟨409856, by rfl⟩ : syracuseStep 2185901 = 819713) (by norm_num)
theorem B4152005 : Blo 968591 4152005 := bbase (se 4 (by rfl) ⟨389250, by rfl⟩ : syracuseStep 4152005 = 778501) (by norm_num)
theorem B2185973 : Blo 968591 2185973 := bbase (se 5 (by rfl) ⟨102467, by rfl⟩ : syracuseStep 2185973 = 204935) (by norm_num)
theorem B2186045 : Blo 968591 2186045 := bbase (se 3 (by rfl) ⟨409883, by rfl⟩ : syracuseStep 2186045 = 819767) (by norm_num)
theorem B4905845 : Blo 968591 4905845 := bbase (se 5 (by rfl) ⟨229961, by rfl⟩ : syracuseStep 4905845 = 459923) (by norm_num)
theorem B2186117 : Blo 968591 2186117 := bbase (se 4 (by rfl) ⟨204948, by rfl⟩ : syracuseStep 2186117 = 409897) (by norm_num)
theorem B2186189 : Blo 968591 2186189 := bbase (se 3 (by rfl) ⟨409910, by rfl⟩ : syracuseStep 2186189 = 819821) (by norm_num)
theorem B4152293 : Blo 968591 4152293 := bbase (se 4 (by rfl) ⟨389277, by rfl⟩ : syracuseStep 4152293 = 778555) (by norm_num)
theorem B2186261 : Blo 968591 2186261 := bbase (se 6 (by rfl) ⟨51240, by rfl⟩ : syracuseStep 2186261 = 102481) (by norm_num)
theorem B2186333 : Blo 968591 2186333 := bbase (se 3 (by rfl) ⟨409937, by rfl⟩ : syracuseStep 2186333 = 819875) (by norm_num)
theorem B2186405 : Blo 968591 2186405 := bbase (se 4 (by rfl) ⟨204975, by rfl⟩ : syracuseStep 2186405 = 409951) (by norm_num)
theorem B1400005 : Blo 968591 1400005 := bbase (se 4 (by rfl) ⟨131250, by rfl⟩ : syracuseStep 1400005 = 262501) (by norm_num)
theorem B2186477 : Blo 968591 2186477 := bbase (se 3 (by rfl) ⟨409964, by rfl⟩ : syracuseStep 2186477 = 819929) (by norm_num)
theorem B3104021 : Blo 968591 3104021 := bbase (se 6 (by rfl) ⟨72750, by rfl⟩ : syracuseStep 3104021 = 145501) (by norm_num)
theorem B2186549 : Blo 968591 2186549 := bbase (se 5 (by rfl) ⟨102494, by rfl⟩ : syracuseStep 2186549 = 204989) (by norm_num)
theorem B2186621 : Blo 968591 2186621 := bbase (se 3 (by rfl) ⟨409991, by rfl⟩ : syracuseStep 2186621 = 819983) (by norm_num)
theorem B2186693 : Blo 968591 2186693 := bbase (se 4 (by rfl) ⟨205002, by rfl⟩ : syracuseStep 2186693 = 410005) (by norm_num)
theorem B1105373 : Blo 968591 1105373 := bbase (se 3 (by rfl) ⟨207257, by rfl⟩ : syracuseStep 1105373 = 414515) (by norm_num)
theorem B2186765 : Blo 968591 2186765 := bbase (se 3 (by rfl) ⟨410018, by rfl⟩ : syracuseStep 2186765 = 820037) (by norm_num)
theorem B2186837 : Blo 968591 2186837 := bbase (se 8 (by rfl) ⟨12813, by rfl⟩ : syracuseStep 2186837 = 25627) (by norm_num)
theorem B2186909 : Blo 968591 2186909 := bbase (se 3 (by rfl) ⟨410045, by rfl⟩ : syracuseStep 2186909 = 820091) (by norm_num)
theorem B4153045 : Blo 968591 4153045 := bbase (se 7 (by rfl) ⟨48668, by rfl⟩ : syracuseStep 4153045 = 97337) (by norm_num)
theorem B2186981 : Blo 968591 2186981 := bbase (se 4 (by rfl) ⟨205029, by rfl⟩ : syracuseStep 2186981 = 410059) (by norm_num)
theorem B2187053 : Blo 968591 2187053 := bbase (se 3 (by rfl) ⟨410072, by rfl⟩ : syracuseStep 2187053 = 820145) (by norm_num)
theorem B2187125 : Blo 968591 2187125 := bbase (se 5 (by rfl) ⟨102521, by rfl⟩ : syracuseStep 2187125 = 205043) (by norm_num)
theorem B2187197 : Blo 968591 2187197 := bbase (se 3 (by rfl) ⟨410099, by rfl⟩ : syracuseStep 2187197 = 820199) (by norm_num)
theorem B1105861 : Blo 968591 1105861 := bbase (se 4 (by rfl) ⟨103674, by rfl⟩ : syracuseStep 1105861 = 207349) (by norm_num)
theorem B2187269 : Blo 968591 2187269 := bbase (se 4 (by rfl) ⟨205056, by rfl⟩ : syracuseStep 2187269 = 410113) (by norm_num)
theorem B1663013 : Blo 968591 1663013 := bbase (se 4 (by rfl) ⟨155907, by rfl⟩ : syracuseStep 1663013 = 311815) (by norm_num)
theorem B2187341 : Blo 968591 2187341 := bbase (se 3 (by rfl) ⟨410126, by rfl⟩ : syracuseStep 2187341 = 820253) (by norm_num)
theorem B4972661 : Blo 968591 4972661 := bbase (se 5 (by rfl) ⟨233093, by rfl⟩ : syracuseStep 4972661 = 466187) (by norm_num)
theorem B4907141 : Blo 968591 4907141 := bbase (se 4 (by rfl) ⟨460044, by rfl⟩ : syracuseStep 4907141 = 920089) (by norm_num)
theorem B2187413 : Blo 968591 2187413 := bbase (se 6 (by rfl) ⟨51267, by rfl⟩ : syracuseStep 2187413 = 102535) (by norm_num)
theorem B2187485 : Blo 968591 2187485 := bbase (se 3 (by rfl) ⟨410153, by rfl⟩ : syracuseStep 2187485 = 820307) (by norm_num)
theorem B9953525 : Blo 968591 9953525 := bbase (se 5 (by rfl) ⟨466571, by rfl⟩ : syracuseStep 9953525 = 933143) (by norm_num)
theorem B2187557 : Blo 968591 2187557 := bbase (se 4 (by rfl) ⟨205083, by rfl⟩ : syracuseStep 2187557 = 410167) (by norm_num)
theorem B1663301 : Blo 968591 1663301 := bbase (se 4 (by rfl) ⟨155934, by rfl⟩ : syracuseStep 1663301 = 311869) (by norm_num)
theorem B2187629 : Blo 968591 2187629 := bbase (se 3 (by rfl) ⟨410180, by rfl⟩ : syracuseStep 2187629 = 820361) (by norm_num)
theorem B3268997 : Blo 968591 3268997 := bbase (se 4 (by rfl) ⟨306468, by rfl⟩ : syracuseStep 3268997 = 612937) (by norm_num)
theorem B2187701 : Blo 968591 2187701 := bbase (se 5 (by rfl) ⟨102548, by rfl⟩ : syracuseStep 2187701 = 205097) (by norm_num)
theorem B4153781 : Blo 968591 4153781 := bbase (se 5 (by rfl) ⟨194708, by rfl⟩ : syracuseStep 4153781 = 389417) (by norm_num)
theorem B2187773 : Blo 968591 2187773 := bbase (se 3 (by rfl) ⟨410207, by rfl⟩ : syracuseStep 2187773 = 820415) (by norm_num)
theorem B2187845 : Blo 968591 2187845 := bbase (se 4 (by rfl) ⟨205110, by rfl⟩ : syracuseStep 2187845 = 410221) (by norm_num)
theorem B2187917 : Blo 968591 2187917 := bbase (se 3 (by rfl) ⟨410234, by rfl⟩ : syracuseStep 2187917 = 820469) (by norm_num)
theorem B1106605 : Blo 968591 1106605 := bbase (se 3 (by rfl) ⟨207488, by rfl⟩ : syracuseStep 1106605 = 414977) (by norm_num)
theorem B1401517 : Blo 968591 1401517 := bbase (se 3 (by rfl) ⟨262784, by rfl⟩ : syracuseStep 1401517 = 525569) (by norm_num)
theorem B2187989 : Blo 968591 2187989 := bbase (se 7 (by rfl) ⟨25640, by rfl⟩ : syracuseStep 2187989 = 51281) (by norm_num)
theorem B2188061 : Blo 968591 2188061 := bbase (se 3 (by rfl) ⟨410261, by rfl⟩ : syracuseStep 2188061 = 820523) (by norm_num)
theorem B3269429 : Blo 968591 3269429 := bbase (se 5 (by rfl) ⟨153254, by rfl⟩ : syracuseStep 3269429 = 306509) (by norm_num)
theorem B2188133 : Blo 968591 2188133 := bbase (se 4 (by rfl) ⟨205137, by rfl⟩ : syracuseStep 2188133 = 410275) (by norm_num)
theorem B1106833 : Blo 968591 1106833 := bbase (se 2 (by rfl) ⟨415062, by rfl⟩ : syracuseStep 1106833 = 830125) (by norm_num)
theorem B2188205 : Blo 968591 2188205 := bbase (se 3 (by rfl) ⟨410288, by rfl⟩ : syracuseStep 2188205 = 820577) (by norm_num)
theorem B2188277 : Blo 968591 2188277 := bbase (se 5 (by rfl) ⟨102575, by rfl⟩ : syracuseStep 2188277 = 205151) (by norm_num)
theorem B3269861 : Blo 968591 3269861 := bbase (se 4 (by rfl) ⟨306549, by rfl⟩ : syracuseStep 3269861 = 613099) (by norm_num)
theorem B13985045 : Blo 968591 13985045 := bbase (se 6 (by rfl) ⟨327774, by rfl⟩ : syracuseStep 13985045 = 655549) (by norm_num)
theorem B4908437 : Blo 968591 4908437 := bbase (se 6 (by rfl) ⟨115041, by rfl⟩ : syracuseStep 4908437 = 230083) (by norm_num)
theorem B1402429 : Blo 968591 1402429 := bbase (se 3 (by rfl) ⟨262955, by rfl⟩ : syracuseStep 1402429 = 525911) (by norm_num)
theorem B1894013 : Blo 968591 1894013 := bbase (se 3 (by rfl) ⟨355127, by rfl⟩ : syracuseStep 1894013 = 710255) (by norm_num)
theorem B3270293 : Blo 968591 3270293 := bbase (se 6 (by rfl) ⟨76647, by rfl⟩ : syracuseStep 3270293 = 153295) (by norm_num)
theorem B1107613 : Blo 968591 1107613 := bbase (se 3 (by rfl) ⟨207677, by rfl⟩ : syracuseStep 1107613 = 415355) (by norm_num)
theorem B12445397 : Blo 968591 12445397 := bbase (se 7 (by rfl) ⟨145844, by rfl⟩ : syracuseStep 12445397 = 291689) (by norm_num)
theorem B3270725 : Blo 968591 3270725 := bbase (se 4 (by rfl) ⟨306630, by rfl⟩ : syracuseStep 3270725 = 613261) (by norm_num)
theorem B3107173 : Blo 968591 3107173 := bbase (se 4 (by rfl) ⟨291297, by rfl⟩ : syracuseStep 3107173 = 582595) (by norm_num)
theorem B2451829 : Blo 968591 2451829 := bbase (se 5 (by rfl) ⟨114929, by rfl⟩ : syracuseStep 2451829 = 229859) (by norm_num)
theorem B2451941 : Blo 968591 2451941 := bbase (se 4 (by rfl) ⟨229869, by rfl⟩ : syracuseStep 2451941 = 459739) (by norm_num)
theorem B3271157 : Blo 968591 3271157 := bbase (se 5 (by rfl) ⟨153335, by rfl⟩ : syracuseStep 3271157 = 306671) (by norm_num)
theorem B5532245 : Blo 968591 5532245 := bbase (se 8 (by rfl) ⟨32415, by rfl⟩ : syracuseStep 5532245 = 64831) (by norm_num)
theorem B2452133 : Blo 968591 2452133 := bbase (se 4 (by rfl) ⟨229887, by rfl⟩ : syracuseStep 2452133 = 459775) (by norm_num)
theorem B4909733 : Blo 968591 4909733 := bbase (se 4 (by rfl) ⟨460287, by rfl⟩ : syracuseStep 4909733 = 920575) (by norm_num)
theorem B7858997 : Blo 968591 7858997 := bbase (se 5 (by rfl) ⟨368390, by rfl⟩ : syracuseStep 7858997 = 736781) (by norm_num)
theorem B3271589 : Blo 968591 3271589 := bbase (se 4 (by rfl) ⟨306711, by rfl⟩ : syracuseStep 3271589 = 613423) (by norm_num)
theorem B2452477 : Blo 968591 2452477 := bbase (se 3 (by rfl) ⟨459839, by rfl⟩ : syracuseStep 2452477 = 919679) (by norm_num)
theorem B7007285 : Blo 968591 7007285 := bbase (se 5 (by rfl) ⟨328466, by rfl⟩ : syracuseStep 7007285 = 656933) (by norm_num)
theorem B2452589 : Blo 968591 2452589 := bbase (se 3 (by rfl) ⟨459860, by rfl⟩ : syracuseStep 2452589 = 919721) (by norm_num)
theorem B2452781 : Blo 968591 2452781 := bbase (se 3 (by rfl) ⟨459896, by rfl⟩ : syracuseStep 2452781 = 919793) (by norm_num)
theorem B3272021 : Blo 968591 3272021 := bbase (se 11 (by rfl) ⟨2396, by rfl⟩ : syracuseStep 3272021 = 4793) (by norm_num)
theorem B7368245 : Blo 968591 7368245 := bbase (se 5 (by rfl) ⟨345386, by rfl⟩ : syracuseStep 7368245 = 690773) (by norm_num)
theorem B2453125 : Blo 968591 2453125 := bbase (se 4 (by rfl) ⟨229980, by rfl⟩ : syracuseStep 2453125 = 459961) (by norm_num)
theorem B3501797 : Blo 968591 3501797 := bbase (se 4 (by rfl) ⟨328293, by rfl⟩ : syracuseStep 3501797 = 656587) (by norm_num)
theorem B2453237 : Blo 968591 2453237 := bbase (se 5 (by rfl) ⟨114995, by rfl⟩ : syracuseStep 2453237 = 229991) (by norm_num)
theorem B3272453 : Blo 968591 3272453 := bbase (se 4 (by rfl) ⟨306792, by rfl⟩ : syracuseStep 3272453 = 613585) (by norm_num)
theorem B2453429 : Blo 968591 2453429 := bbase (se 5 (by rfl) ⟨115004, by rfl⟩ : syracuseStep 2453429 = 230009) (by norm_num)
theorem B4911029 : Blo 968591 4911029 := bbase (se 5 (by rfl) ⟨230204, by rfl⟩ : syracuseStep 4911029 = 460409) (by norm_num)
theorem B3272885 : Blo 968591 3272885 := bbase (se 5 (by rfl) ⟨153416, by rfl⟩ : syracuseStep 3272885 = 306833) (by norm_num)
theorem B4976885 : Blo 968591 4976885 := bbase (se 5 (by rfl) ⟨233291, by rfl⟩ : syracuseStep 4976885 = 466583) (by norm_num)
theorem B1634573 : Blo 968591 1634573 := bbase (se 3 (by rfl) ⟨306482, by rfl⟩ : syracuseStep 1634573 = 612965) (by norm_num)
theorem B2453773 : Blo 968591 2453773 := bbase (se 3 (by rfl) ⟨460082, by rfl⟩ : syracuseStep 2453773 = 920165) (by norm_num)
theorem B2453885 : Blo 968591 2453885 := bbase (se 3 (by rfl) ⟨460103, by rfl⟩ : syracuseStep 2453885 = 920207) (by norm_num)
theorem B1634701 : Blo 968591 1634701 := bbase (se 3 (by rfl) ⟨306506, by rfl⟩ : syracuseStep 1634701 = 613013) (by norm_num)
theorem B1634789 : Blo 968591 1634789 := bbase (se 4 (by rfl) ⟨153261, by rfl⟩ : syracuseStep 1634789 = 306523) (by norm_num)
theorem B2454077 : Blo 968591 2454077 := bbase (se 3 (by rfl) ⟨460139, by rfl⟩ : syracuseStep 2454077 = 920279) (by norm_num)
theorem B1634917 : Blo 968591 1634917 := bbase (se 4 (by rfl) ⟨153273, by rfl⟩ : syracuseStep 1634917 = 306547) (by norm_num)
theorem B3273317 : Blo 968591 3273317 := bbase (se 4 (by rfl) ⟨306873, by rfl⟩ : syracuseStep 3273317 = 613747) (by norm_num)
theorem B1635005 : Blo 968591 1635005 := bbase (se 3 (by rfl) ⟨306563, by rfl⟩ : syracuseStep 1635005 = 613127) (by norm_num)
theorem B2519813 : Blo 968591 2519813 := bbase (se 4 (by rfl) ⟨236232, by rfl⟩ : syracuseStep 2519813 = 472465) (by norm_num)
theorem B2519837 : Blo 968591 2519837 := bbase (se 3 (by rfl) ⟨472469, by rfl⟩ : syracuseStep 2519837 = 944939) (by norm_num)
theorem B1635133 : Blo 968591 1635133 := bbase (se 3 (by rfl) ⟨306587, by rfl⟩ : syracuseStep 1635133 = 613175) (by norm_num)
theorem B4977541 : Blo 968591 4977541 := bbase (se 4 (by rfl) ⟨466644, by rfl⟩ : syracuseStep 4977541 = 933289) (by norm_num)
theorem B1635221 : Blo 968591 1635221 := bbase (se 6 (by rfl) ⟨38325, by rfl⟩ : syracuseStep 1635221 = 76651) (by norm_num)
theorem B2454421 : Blo 968591 2454421 := bbase (se 6 (by rfl) ⟨57525, by rfl⟩ : syracuseStep 2454421 = 115051) (by norm_num)
theorem B2454533 : Blo 968591 2454533 := bbase (se 4 (by rfl) ⟨230112, by rfl⟩ : syracuseStep 2454533 = 460225) (by norm_num)
theorem B1635349 : Blo 968591 1635349 := bbase (se 6 (by rfl) ⟨38328, by rfl⟩ : syracuseStep 1635349 = 76657) (by norm_num)
theorem B3273749 : Blo 968591 3273749 := bbase (se 6 (by rfl) ⟨76728, by rfl⟩ : syracuseStep 3273749 = 153457) (by norm_num)
theorem B7009301 : Blo 968591 7009301 := bbase (se 6 (by rfl) ⟨164280, by rfl⟩ : syracuseStep 7009301 = 328561) (by norm_num)
theorem B9335893 : Blo 968591 9335893 := bbase (se 8 (by rfl) ⟨54702, by rfl⟩ : syracuseStep 9335893 = 109405) (by norm_num)
theorem B1635437 : Blo 968591 1635437 := bbase (se 3 (by rfl) ⟨306644, by rfl⟩ : syracuseStep 1635437 = 613289) (by norm_num)
theorem B3110005 : Blo 968591 3110005 := bbase (se 5 (by rfl) ⟨145781, by rfl⟩ : syracuseStep 3110005 = 291563) (by norm_num)
theorem B3110069 : Blo 968591 3110069 := bbase (se 5 (by rfl) ⟨145784, by rfl⟩ : syracuseStep 3110069 = 291569) (by norm_num)
theorem B2454725 : Blo 968591 2454725 := bbase (se 4 (by rfl) ⟨230130, by rfl⟩ : syracuseStep 2454725 = 460261) (by norm_num)
theorem B4912325 : Blo 968591 4912325 := bbase (se 4 (by rfl) ⟨460530, by rfl⟩ : syracuseStep 4912325 = 921061) (by norm_num)
theorem B1635565 : Blo 968591 1635565 := bbase (se 3 (by rfl) ⟨306668, by rfl⟩ : syracuseStep 1635565 = 613337) (by norm_num)
theorem B1635653 : Blo 968591 1635653 := bbase (se 4 (by rfl) ⟨153342, by rfl⟩ : syracuseStep 1635653 = 306685) (by norm_num)
theorem B1635781 : Blo 968591 1635781 := bbase (se 4 (by rfl) ⟨153354, by rfl⟩ : syracuseStep 1635781 = 306709) (by norm_num)
theorem B3274181 : Blo 968591 3274181 := bbase (se 4 (by rfl) ⟨306954, by rfl⟩ : syracuseStep 3274181 = 613909) (by norm_num)
theorem B1635869 : Blo 968591 1635869 := bbase (se 3 (by rfl) ⟨306725, by rfl⟩ : syracuseStep 1635869 = 613451) (by norm_num)
theorem B2455069 : Blo 968591 2455069 := bbase (se 3 (by rfl) ⟨460325, by rfl⟩ : syracuseStep 2455069 = 920651) (by norm_num)
theorem B2455181 : Blo 968591 2455181 := bbase (se 3 (by rfl) ⟨460346, by rfl⟩ : syracuseStep 2455181 = 920693) (by norm_num)
theorem B1635997 : Blo 968591 1635997 := bbase (se 3 (by rfl) ⟨306749, by rfl⟩ : syracuseStep 1635997 = 613499) (by norm_num)
theorem B1636085 : Blo 968591 1636085 := bbase (se 5 (by rfl) ⟨76691, by rfl⟩ : syracuseStep 1636085 = 153383) (by norm_num)
theorem B2455373 : Blo 968591 2455373 := bbase (se 3 (by rfl) ⟨460382, by rfl⟩ : syracuseStep 2455373 = 920765) (by norm_num)
theorem B1636213 : Blo 968591 1636213 := bbase (se 5 (by rfl) ⟨76697, by rfl⟩ : syracuseStep 1636213 = 153395) (by norm_num)
theorem B3274613 : Blo 968591 3274613 := bbase (se 5 (by rfl) ⟨153497, by rfl⟩ : syracuseStep 3274613 = 306995) (by norm_num)
theorem B1636301 : Blo 968591 1636301 := bbase (se 3 (by rfl) ⟨306806, by rfl⟩ : syracuseStep 1636301 = 613613) (by norm_num)
theorem B1964029 : Blo 968591 1964029 := bbase (se 3 (by rfl) ⟨368255, by rfl⟩ : syracuseStep 1964029 = 736511) (by norm_num)
theorem B1964069 : Blo 968591 1964069 := bbase (se 4 (by rfl) ⟨184131, by rfl⟩ : syracuseStep 1964069 = 368263) (by norm_num)
theorem B1964101 : Blo 968591 1964101 := bbase (se 4 (by rfl) ⟨184134, by rfl⟩ : syracuseStep 1964101 = 368269) (by norm_num)
theorem B1636429 : Blo 968591 1636429 := bbase (se 3 (by rfl) ⟨306830, by rfl⟩ : syracuseStep 1636429 = 613661) (by norm_num)
theorem B4421749 : Blo 968591 4421749 := bbase (se 5 (by rfl) ⟨207269, by rfl⟩ : syracuseStep 4421749 = 414539) (by norm_num)
theorem B3930277 : Blo 968591 3930277 := bbase (se 4 (by rfl) ⟨368463, by rfl⟩ : syracuseStep 3930277 = 736927) (by norm_num)
theorem B1636517 : Blo 968591 1636517 := bbase (se 4 (by rfl) ⟨153423, by rfl⟩ : syracuseStep 1636517 = 306847) (by norm_num)
theorem B2455717 : Blo 968591 2455717 := bbase (se 4 (by rfl) ⟨230223, by rfl⟩ : syracuseStep 2455717 = 460447) (by norm_num)
theorem B3504293 : Blo 968591 3504293 := bbase (se 4 (by rfl) ⟨328527, by rfl⟩ : syracuseStep 3504293 = 657055) (by norm_num)
theorem B2455829 : Blo 968591 2455829 := bbase (se 6 (by rfl) ⟨57558, by rfl⟩ : syracuseStep 2455829 = 115117) (by norm_num)
theorem B1636645 : Blo 968591 1636645 := bbase (se 4 (by rfl) ⟨153435, by rfl⟩ : syracuseStep 1636645 = 306871) (by norm_num)
theorem B3275045 : Blo 968591 3275045 := bbase (se 4 (by rfl) ⟨307035, by rfl⟩ : syracuseStep 3275045 = 614071) (by norm_num)
theorem B1636733 : Blo 968591 1636733 := bbase (se 3 (by rfl) ⟨306887, by rfl⟩ : syracuseStep 1636733 = 613775) (by norm_num)
theorem B2488765 : Blo 968591 2488765 := bbase (se 3 (by rfl) ⟨466643, by rfl⟩ : syracuseStep 2488765 = 933287) (by norm_num)
theorem B2456021 : Blo 968591 2456021 := bbase (se 7 (by rfl) ⟨28781, by rfl⟩ : syracuseStep 2456021 = 57563) (by norm_num)
theorem B4913621 : Blo 968591 4913621 := bbase (se 7 (by rfl) ⟨57581, by rfl⟩ : syracuseStep 4913621 = 115163) (by norm_num)
theorem B1636861 : Blo 968591 1636861 := bbase (se 3 (by rfl) ⟨306911, by rfl⟩ : syracuseStep 1636861 = 613823) (by norm_num)
theorem B1243669 : Blo 968591 1243669 := bbase (se 6 (by rfl) ⟨29148, by rfl⟩ : syracuseStep 1243669 = 58297) (by norm_num)
theorem B1636949 : Blo 968591 1636949 := bbase (se 8 (by rfl) ⟨9591, by rfl⟩ : syracuseStep 1636949 = 19183) (by norm_num)
theorem B1637077 : Blo 968591 1637077 := bbase (se 7 (by rfl) ⟨19184, by rfl⟩ : syracuseStep 1637077 = 38369) (by norm_num)
theorem B3275477 : Blo 968591 3275477 := bbase (se 7 (by rfl) ⟨38384, by rfl⟩ : syracuseStep 3275477 = 76769) (by norm_num)
theorem B6224597 : Blo 968591 6224597 := bbase (se 7 (by rfl) ⟨72944, by rfl⟩ : syracuseStep 6224597 = 145889) (by norm_num)
theorem B1637165 : Blo 968591 1637165 := bbase (se 3 (by rfl) ⟨306968, by rfl⟩ : syracuseStep 1637165 = 613937) (by norm_num)
theorem B2456365 : Blo 968591 2456365 := bbase (se 3 (by rfl) ⟨460568, by rfl⟩ : syracuseStep 2456365 = 921137) (by norm_num)
theorem B2456477 : Blo 968591 2456477 := bbase (se 3 (by rfl) ⟨460589, by rfl⟩ : syracuseStep 2456477 = 921179) (by norm_num)
theorem B1637293 : Blo 968591 1637293 := bbase (se 3 (by rfl) ⟨306992, by rfl⟩ : syracuseStep 1637293 = 613985) (by norm_num)
theorem B1637381 : Blo 968591 1637381 := bbase (se 4 (by rfl) ⟨153504, by rfl⟩ : syracuseStep 1637381 = 307009) (by norm_num)
theorem B2456669 : Blo 968591 2456669 := bbase (se 3 (by rfl) ⟨460625, by rfl⟩ : syracuseStep 2456669 = 921251) (by norm_num)
theorem B2948197 : Blo 968591 2948197 := bbase (se 4 (by rfl) ⟨276393, by rfl⟩ : syracuseStep 2948197 = 552787) (by norm_num)
theorem B1637509 : Blo 968591 1637509 := bbase (se 4 (by rfl) ⟨153516, by rfl⟩ : syracuseStep 1637509 = 307033) (by norm_num)
theorem B3275909 : Blo 968591 3275909 := bbase (se 4 (by rfl) ⟨307116, by rfl⟩ : syracuseStep 3275909 = 614233) (by norm_num)
theorem B1965197 : Blo 968591 1965197 := bbase (se 3 (by rfl) ⟨368474, by rfl⟩ : syracuseStep 1965197 = 736949) (by norm_num)
theorem B1244365 : Blo 968591 1244365 := bbase (se 3 (by rfl) ⟨233318, by rfl⟩ : syracuseStep 1244365 = 466637) (by norm_num)
theorem B1965269 : Blo 968591 1965269 := bbase (se 7 (by rfl) ⟨23030, by rfl⟩ : syracuseStep 1965269 = 46061) (by norm_num)
theorem B1637597 : Blo 968591 1637597 := bbase (se 3 (by rfl) ⟨307049, by rfl⟩ : syracuseStep 1637597 = 614099) (by norm_num)
theorem B1637725 : Blo 968591 1637725 := bbase (se 3 (by rfl) ⟨307073, by rfl⟩ : syracuseStep 1637725 = 614147) (by norm_num)
theorem B1637813 : Blo 968591 1637813 := bbase (se 5 (by rfl) ⟨76772, by rfl⟩ : syracuseStep 1637813 = 153545) (by norm_num)
theorem B2457013 : Blo 968591 2457013 := bbase (se 5 (by rfl) ⟨115172, by rfl⟩ : syracuseStep 2457013 = 230345) (by norm_num)
theorem B18906581 : Blo 968591 18906581 := bbase (se 7 (by rfl) ⟨221561, by rfl⟩ : syracuseStep 18906581 = 443123) (by norm_num)
theorem B1474013 : Blo 968591 1474013 := bbase (se 3 (by rfl) ⟨276377, by rfl⟩ : syracuseStep 1474013 = 552755) (by norm_num)
theorem B2457125 : Blo 968591 2457125 := bbase (se 4 (by rfl) ⟨230355, by rfl⟩ : syracuseStep 2457125 = 460711) (by norm_num)
theorem B1310261 : Blo 968591 1310261 := bbase (se 5 (by rfl) ⟨61418, by rfl⟩ : syracuseStep 1310261 = 122837) (by norm_num)
theorem B1637941 : Blo 968591 1637941 := bbase (se 5 (by rfl) ⟨76778, by rfl⟩ : syracuseStep 1637941 = 153557) (by norm_num)
theorem B3276341 : Blo 968591 3276341 := bbase (se 5 (by rfl) ⟨153578, by rfl⟩ : syracuseStep 3276341 = 307157) (by norm_num)
theorem B1638029 : Blo 968591 1638029 := bbase (se 3 (by rfl) ⟨307130, by rfl⟩ : syracuseStep 1638029 = 614261) (by norm_num)
theorem B2457317 : Blo 968591 2457317 := bbase (se 4 (by rfl) ⟨230373, by rfl⟩ : syracuseStep 2457317 = 460747) (by norm_num)
theorem B4914917 : Blo 968591 4914917 := bbase (se 4 (by rfl) ⟨460773, by rfl⟩ : syracuseStep 4914917 = 921547) (by norm_num)
theorem B1638157 : Blo 968591 1638157 := bbase (se 3 (by rfl) ⟨307154, by rfl⟩ : syracuseStep 1638157 = 614309) (by norm_num)
theorem B1965917 : Blo 968591 1965917 := bbase (se 3 (by rfl) ⟨368609, by rfl⟩ : syracuseStep 1965917 = 737219) (by norm_num)
theorem B1638245 : Blo 968591 1638245 := bbase (se 4 (by rfl) ⟨153585, by rfl⟩ : syracuseStep 1638245 = 307171) (by norm_num)
theorem B6651829 : Blo 968591 6651829 := bbase (se 5 (by rfl) ⟨311804, by rfl⟩ : syracuseStep 6651829 = 623609) (by norm_num)
theorem B1638373 : Blo 968591 1638373 := bbase (se 4 (by rfl) ⟨153597, by rfl⟩ : syracuseStep 1638373 = 307195) (by norm_num)
theorem B3276773 : Blo 968591 3276773 := bbase (se 4 (by rfl) ⟨307197, by rfl⟩ : syracuseStep 3276773 = 614395) (by norm_num)
theorem B1769453 : Blo 968591 1769453 := bbase (se 3 (by rfl) ⟨331772, by rfl⟩ : syracuseStep 1769453 = 663545) (by norm_num)
theorem B1310737 : Blo 968591 1310737 := bstep (se 2 (by rfl) ⟨491526, by rfl⟩ : syracuseStep 1310737 = 983053) B983053
theorem B3276881 : Blo 968591 3276881 := bstep (se 2 (by rfl) ⟨1228830, by rfl⟩ : syracuseStep 3276881 = 2457661) B2457661
theorem B1638481 : Blo 968591 1638481 := bstep (se 2 (by rfl) ⟨614430, by rfl⟩ : syracuseStep 1638481 = 1228861) B1228861
theorem B1638515 : Blo 968591 1638515 := bstep (se 1 (by rfl) ⟨1228886, by rfl⟩ : syracuseStep 1638515 = 2457773) B2457773
theorem B1638643 : Blo 968591 1638643 := bstep (se 1 (by rfl) ⟨1228982, by rfl⟩ : syracuseStep 1638643 = 2457965) B2457965
theorem B1638785 : Blo 968591 1638785 := bstep (se 2 (by rfl) ⟨614544, by rfl⟩ : syracuseStep 1638785 = 1229089) B1229089
theorem B2097649 : Blo 968591 2097649 := bstep (se 2 (by rfl) ⟨786618, by rfl⟩ : syracuseStep 2097649 = 1573237) B1573237
theorem B2458097 : Blo 968591 2458097 := bstep (se 2 (by rfl) ⟨921786, by rfl⟩ : syracuseStep 2458097 = 1843573) B1843573
theorem B1638913 : Blo 968591 1638913 := bstep (se 2 (by rfl) ⟨614592, by rfl⟩ : syracuseStep 1638913 = 1229185) B1229185
theorem B2458147 : Blo 968591 2458147 := bstep (se 1 (by rfl) ⟨1843610, by rfl⟩ : syracuseStep 2458147 = 3687221) B3687221
theorem B1638947 : Blo 968591 1638947 := bstep (se 1 (by rfl) ⟨1229210, by rfl⟩ : syracuseStep 1638947 = 2458421) B2458421
theorem B3277421 : Blo 968591 3277421 := bstep (se 3 (by rfl) ⟨614516, by rfl⟩ : syracuseStep 3277421 = 1229033) B1229033
theorem B1311347 : Blo 968591 1311347 := bstep (se 1 (by rfl) ⟨983510, by rfl⟩ : syracuseStep 1311347 = 1967021) B1967021
theorem B3277475 : Blo 968591 3277475 := bstep (se 1 (by rfl) ⟨2458106, by rfl⟩ : syracuseStep 3277475 = 4916213) B4916213
theorem B1639075 : Blo 968591 1639075 := bstep (se 1 (by rfl) ⟨1229306, by rfl⟩ : syracuseStep 1639075 = 2458613) B2458613
theorem B6226595 : Blo 968591 6226595 := bstep (se 1 (by rfl) ⟨4669946, by rfl⟩ : syracuseStep 6226595 = 9339893) B9339893
theorem B4915889 : Blo 968591 4915889 := bstep (se 2 (by rfl) ⟨1843458, by rfl⟩ : syracuseStep 4915889 = 3686917) B3686917
theorem B2458289 : Blo 968591 2458289 := bstep (se 2 (by rfl) ⟨921858, by rfl⟩ : syracuseStep 2458289 = 1843717) B1843717
theorem B1639217 : Blo 968591 1639217 := bstep (se 2 (by rfl) ⟨614706, by rfl⟩ : syracuseStep 1639217 = 1229413) B1229413
theorem B1868689 : Blo 968591 1868689 := bstep (se 2 (by rfl) ⟨700758, by rfl⟩ : syracuseStep 1868689 = 1401517) B1401517
theorem B1311649 : Blo 968591 1311649 := bstep (se 2 (by rfl) ⟨491868, by rfl⟩ : syracuseStep 1311649 = 983737) B983737
theorem B3277745 : Blo 968591 3277745 := bstep (se 2 (by rfl) ⟨1229154, by rfl⟩ : syracuseStep 3277745 = 2458309) B2458309
theorem B1639345 : Blo 968591 1639345 := bstep (se 2 (by rfl) ⟨614754, by rfl⟩ : syracuseStep 1639345 = 1229509) B1229509
theorem B1639379 : Blo 968591 1639379 := bstep (se 1 (by rfl) ⟨1229534, by rfl⟩ : syracuseStep 1639379 = 2459069) B2459069
theorem B8979427 : Blo 968591 8979427 := bstep (se 1 (by rfl) ⟨6734570, by rfl⟩ : syracuseStep 8979427 = 13469141) B13469141
theorem B5538851 : Blo 968591 5538851 := bstep (se 1 (by rfl) ⟨4154138, by rfl⟩ : syracuseStep 5538851 = 8308277) B8308277
theorem B1639507 : Blo 968591 1639507 := bstep (se 1 (by rfl) ⟨1229630, by rfl⟩ : syracuseStep 1639507 = 2459261) B2459261
theorem B6227057 : Blo 968591 6227057 := bstep (se 2 (by rfl) ⟨2335146, by rfl⟩ : syracuseStep 6227057 = 4670293) B4670293
theorem B1475747 : Blo 968591 1475747 := bstep (se 1 (by rfl) ⟨1106810, by rfl⟩ : syracuseStep 1475747 = 2213621) B2213621
theorem B1475777 : Blo 968591 1475777 := bstep (se 2 (by rfl) ⟨553416, by rfl⟩ : syracuseStep 1475777 = 1106833) B1106833
theorem B1639649 : Blo 968591 1639649 := bstep (se 2 (by rfl) ⟨614868, by rfl⟩ : syracuseStep 1639649 = 1229737) B1229737
theorem B1967345 : Blo 968591 1967345 := bstep (se 2 (by rfl) ⟨737754, by rfl⟩ : syracuseStep 1967345 = 1475509) B1475509
theorem B2622737 : Blo 968591 2622737 := bstep (se 2 (by rfl) ⟨983526, by rfl⟩ : syracuseStep 2622737 = 1967053) B1967053
theorem B1639777 : Blo 968591 1639777 := bstep (se 2 (by rfl) ⟨614916, by rfl⟩ : syracuseStep 1639777 = 1229833) B1229833
theorem B1639811 : Blo 968591 1639811 := bstep (se 1 (by rfl) ⟨1229858, by rfl⟩ : syracuseStep 1639811 = 2459717) B2459717
theorem B1312147 : Blo 968591 1312147 := bstep (se 1 (by rfl) ⟨984110, by rfl⟩ : syracuseStep 1312147 = 1968221) B1968221
theorem B3278285 : Blo 968591 3278285 := bstep (se 3 (by rfl) ⟨614678, by rfl⟩ : syracuseStep 3278285 = 1229357) B1229357
theorem B3278339 : Blo 968591 3278339 := bstep (se 1 (by rfl) ⟨2458754, by rfl⟩ : syracuseStep 3278339 = 4917509) B4917509
theorem B1639939 : Blo 968591 1639939 := bstep (se 1 (by rfl) ⟨1229954, by rfl⟩ : syracuseStep 1639939 = 2459909) B2459909
theorem B2459281 : Blo 968591 2459281 := bstep (se 2 (by rfl) ⟨922230, by rfl⟩ : syracuseStep 2459281 = 1844461) B1844461
theorem B1640081 : Blo 968591 1640081 := bstep (se 2 (by rfl) ⟨615030, by rfl⟩ : syracuseStep 1640081 = 1230061) B1230061
theorem B7374563 : Blo 968591 7374563 := bstep (se 1 (by rfl) ⟨5530922, by rfl⟩ : syracuseStep 7374563 = 11061845) B11061845
theorem B3114733 : Blo 968591 3114733 := bstep (se 3 (by rfl) ⟨584012, by rfl⟩ : syracuseStep 3114733 = 1168025) B1168025
theorem B3278609 : Blo 968591 3278609 := bstep (se 2 (by rfl) ⟨1229478, by rfl⟩ : syracuseStep 3278609 = 2458957) B2458957
theorem B1640209 : Blo 968591 1640209 := bstep (se 2 (by rfl) ⟨615078, by rfl⟩ : syracuseStep 1640209 = 1230157) B1230157
theorem B1640243 : Blo 968591 1640243 := bstep (se 1 (by rfl) ⟨1230182, by rfl⟩ : syracuseStep 1640243 = 2460365) B2460365
theorem B2459555 : Blo 968591 2459555 := bstep (se 1 (by rfl) ⟨1844666, by rfl⟩ : syracuseStep 2459555 = 3689333) B3689333
theorem B1640371 : Blo 968591 1640371 := bstep (se 1 (by rfl) ⟨1230278, by rfl⟩ : syracuseStep 1640371 = 2460557) B2460557
theorem B2328515 : Blo 968591 2328515 := bstep (se 1 (by rfl) ⟨1746386, by rfl⟩ : syracuseStep 2328515 = 3492773) B3492773
theorem B1312753 : Blo 968591 1312753 := bstep (se 2 (by rfl) ⟨492282, by rfl⟩ : syracuseStep 1312753 = 984565) B984565
theorem B6719501 : Blo 968591 6719501 := bstep (se 3 (by rfl) ⟨1259906, by rfl⟩ : syracuseStep 6719501 = 2519813) B2519813
theorem B1640513 : Blo 968591 1640513 := bstep (se 2 (by rfl) ⟨615192, by rfl⟩ : syracuseStep 1640513 = 1230385) B1230385
theorem B1869905 : Blo 968591 1869905 := bstep (se 2 (by rfl) ⟨701214, by rfl⟩ : syracuseStep 1869905 = 1402429) B1402429
theorem B4917347 : Blo 968591 4917347 := bstep (se 1 (by rfl) ⟨3688010, by rfl⟩ : syracuseStep 4917347 = 7376021) B7376021
theorem B2459747 : Blo 968591 2459747 := bstep (se 1 (by rfl) ⟨1844810, by rfl⟩ : syracuseStep 2459747 = 3689621) B3689621
theorem B2328689 : Blo 968591 2328689 := bstep (se 2 (by rfl) ⟨873258, by rfl⟩ : syracuseStep 2328689 = 1746517) B1746517
theorem B2328707 : Blo 968591 2328707 := bstep (se 1 (by rfl) ⟨1746530, by rfl⟩ : syracuseStep 2328707 = 3493061) B3493061
theorem B1640641 : Blo 968591 1640641 := bstep (se 2 (by rfl) ⟨615240, by rfl⟩ : syracuseStep 1640641 = 1230481) B1230481
theorem B1640675 : Blo 968591 1640675 := bstep (se 1 (by rfl) ⟨1230506, by rfl⟩ : syracuseStep 1640675 = 2461013) B2461013
theorem B3279149 : Blo 968591 3279149 := bstep (se 3 (by rfl) ⟨614840, by rfl⟩ : syracuseStep 3279149 = 1229681) B1229681
theorem B3279203 : Blo 968591 3279203 := bstep (se 1 (by rfl) ⟨2459402, by rfl⟩ : syracuseStep 3279203 = 4918805) B4918805
theorem B1640803 : Blo 968591 1640803 := bstep (se 1 (by rfl) ⟨1230602, by rfl⟩ : syracuseStep 1640803 = 2461205) B2461205
theorem B7473521 : Blo 968591 7473521 := bstep (se 2 (by rfl) ⟨2802570, by rfl⟩ : syracuseStep 7473521 = 5605141) B5605141
theorem B1477091 : Blo 968591 1477091 := bstep (se 1 (by rfl) ⟨1107818, by rfl⟩ : syracuseStep 1477091 = 2215637) B2215637
theorem B1640945 : Blo 968591 1640945 := bstep (se 2 (by rfl) ⟨615354, by rfl⟩ : syracuseStep 1640945 = 1230709) B1230709
theorem B2656813 : Blo 968591 2656813 := bstep (se 3 (by rfl) ⟨498152, by rfl⟩ : syracuseStep 2656813 = 996305) B996305
theorem B3279473 : Blo 968591 3279473 := bstep (se 2 (by rfl) ⟨1229802, by rfl⟩ : syracuseStep 3279473 = 2459605) B2459605
theorem B1641073 : Blo 968591 1641073 := bstep (se 2 (by rfl) ⟨615402, by rfl⟩ : syracuseStep 1641073 = 1230805) B1230805
theorem B1641107 : Blo 968591 1641107 := bstep (se 1 (by rfl) ⟨1230830, by rfl⟩ : syracuseStep 1641107 = 2461661) B2461661
theorem B1641235 : Blo 968591 1641235 := bstep (se 1 (by rfl) ⟨1230926, by rfl⟩ : syracuseStep 1641235 = 2461853) B2461853
theorem B1575811 : Blo 968591 1575811 := bstep (se 1 (by rfl) ⟨1181858, by rfl⟩ : syracuseStep 1575811 = 2363717) B2363717
theorem B4918157 : Blo 968591 4918157 := bstep (se 3 (by rfl) ⟨922154, by rfl⟩ : syracuseStep 4918157 = 1844309) B1844309
theorem B2493443 : Blo 968591 2493443 := bstep (se 1 (by rfl) ⟨1870082, by rfl⟩ : syracuseStep 2493443 = 3740165) B3740165
theorem B2460689 : Blo 968591 2460689 := bstep (se 2 (by rfl) ⟨922758, by rfl⟩ : syracuseStep 2460689 = 1845517) B1845517
theorem B1969219 : Blo 968591 1969219 := bstep (se 1 (by rfl) ⟨1476914, by rfl⟩ : syracuseStep 1969219 = 2953829) B2953829
theorem B2460739 : Blo 968591 2460739 := bstep (se 1 (by rfl) ⟨1845554, by rfl⟩ : syracuseStep 2460739 = 3691109) B3691109
theorem B3280013 : Blo 968591 3280013 := bstep (se 3 (by rfl) ⟨615002, by rfl⟩ : syracuseStep 3280013 = 1230005) B1230005
theorem B3280067 : Blo 968591 3280067 := bstep (se 1 (by rfl) ⟨2460050, by rfl⟩ : syracuseStep 3280067 = 4920101) B4920101
theorem B2460881 : Blo 968591 2460881 := bstep (se 2 (by rfl) ⟨922830, by rfl⟩ : syracuseStep 2460881 = 1845661) B1845661
theorem B1379587 : Blo 968591 1379587 := bstep (se 1 (by rfl) ⟨1034690, by rfl⟩ : syracuseStep 1379587 = 2069381) B2069381
theorem B2952625 : Blo 968591 2952625 := bstep (se 2 (by rfl) ⟨1107234, by rfl⟩ : syracuseStep 2952625 = 2214469) B2214469
theorem B3280337 : Blo 968591 3280337 := bstep (se 2 (by rfl) ⟨1230126, by rfl⟩ : syracuseStep 3280337 = 2460253) B2460253
theorem B1314353 : Blo 968591 1314353 := bstep (se 2 (by rfl) ⟨492882, by rfl⟩ : syracuseStep 1314353 = 985765) B985765
theorem B5901893 : Blo 968591 5901893 := bstep (se 4 (by rfl) ⟨553302, by rfl⟩ : syracuseStep 5901893 = 1106605) B1106605
theorem B1576849 : Blo 968591 1576849 := bstep (se 2 (by rfl) ⟨591318, by rfl⟩ : syracuseStep 1576849 = 1182637) B1182637
theorem B3280877 : Blo 968591 3280877 := bstep (se 3 (by rfl) ⟨615164, by rfl⟩ : syracuseStep 3280877 = 1230329) B1230329
theorem B3280931 : Blo 968591 3280931 := bstep (se 1 (by rfl) ⟨2460698, by rfl⟩ : syracuseStep 3280931 = 4921397) B4921397
theorem B1970257 : Blo 968591 1970257 := bstep (se 2 (by rfl) ⟨738846, by rfl⟩ : syracuseStep 1970257 = 1477693) B1477693
theorem B2461873 : Blo 968591 2461873 := bstep (se 2 (by rfl) ⟨923202, by rfl⟩ : syracuseStep 2461873 = 1846405) B1846405
theorem B3281201 : Blo 968591 3281201 := bstep (se 2 (by rfl) ⟨1230450, by rfl⟩ : syracuseStep 3281201 = 2460901) B2460901
theorem B1380721 : Blo 968591 1380721 := bstep (se 2 (by rfl) ⟨517770, by rfl⟩ : syracuseStep 1380721 = 1035541) B1035541
theorem B6558115 : Blo 968591 6558115 := bstep (se 1 (by rfl) ⟨4918586, by rfl⟩ : syracuseStep 6558115 = 9837173) B9837173
theorem B1380817 : Blo 968591 1380817 := bstep (se 2 (by rfl) ⟨517806, by rfl⟩ : syracuseStep 1380817 = 1035613) B1035613
theorem B1839601 : Blo 968591 1839601 := bstep (se 2 (by rfl) ⟨689850, by rfl⟩ : syracuseStep 1839601 = 1379701) B1379701
theorem B7180913 : Blo 968591 7180913 := bstep (se 2 (by rfl) ⟨2692842, by rfl⟩ : syracuseStep 7180913 = 5385685) B5385685
theorem B1184419 : Blo 968591 1184419 := bstep (se 1 (by rfl) ⟨888314, by rfl⟩ : syracuseStep 1184419 = 1776629) B1776629
theorem B26546885 : Blo 968591 26546885 := bstep (se 4 (by rfl) ⟨2488770, by rfl⟩ : syracuseStep 26546885 = 4977541) B4977541
theorem B2102051 : Blo 968591 2102051 := bstep (se 1 (by rfl) ⟨1576538, by rfl⟩ : syracuseStep 2102051 = 3153077) B3153077
theorem B1971011 : Blo 968591 1971011 := bstep (se 1 (by rfl) ⟨1478258, by rfl⟩ : syracuseStep 1971011 = 2956517) B2956517
theorem B3281741 : Blo 968591 3281741 := bstep (se 3 (by rfl) ⟨615326, by rfl⟩ : syracuseStep 3281741 = 1230653) B1230653
theorem B2069347 : Blo 968591 2069347 := bstep (se 1 (by rfl) ⟨1552010, by rfl⟩ : syracuseStep 2069347 = 3104021) B3104021
theorem B3281795 : Blo 968591 3281795 := bstep (se 1 (by rfl) ⟨2461346, by rfl⟩ : syracuseStep 3281795 = 4922693) B4922693
theorem B1381313 : Blo 968591 1381313 := bstep (se 2 (by rfl) ⟨517992, by rfl⟩ : syracuseStep 1381313 = 1035985) B1035985
theorem B3413123 : Blo 968591 3413123 := bstep (se 1 (by rfl) ⟨2559842, by rfl⟩ : syracuseStep 3413123 = 5119685) B5119685
theorem B3282065 : Blo 968591 3282065 := bstep (se 2 (by rfl) ⟨1230774, by rfl⟩ : syracuseStep 3282065 = 2461549) B2461549
theorem B12424589 : Blo 968591 12424589 := bstep (se 3 (by rfl) ⟨2329610, by rfl⟩ : syracuseStep 12424589 = 4659221) B4659221
theorem B3315107 : Blo 968591 3315107 := bstep (se 1 (by rfl) ⟨2486330, by rfl⟩ : syracuseStep 3315107 = 4972661) B4972661
theorem B1971683 : Blo 968591 1971683 := bstep (se 1 (by rfl) ⟨1478762, by rfl⟩ : syracuseStep 1971683 = 2957525) B2957525
theorem B1840657 : Blo 968591 1840657 := bstep (se 2 (by rfl) ⟨690246, by rfl⟩ : syracuseStep 1840657 = 1380493) B1380493
theorem B3937933 : Blo 968591 3937933 := bstep (se 3 (by rfl) ⟨738362, by rfl⟩ : syracuseStep 3937933 = 1476725) B1476725
theorem B2070193 : Blo 968591 2070193 := bstep (se 2 (by rfl) ⟨776322, by rfl⟩ : syracuseStep 2070193 = 1552645) B1552645
theorem B4921073 : Blo 968591 4921073 := bstep (se 2 (by rfl) ⟨1845402, by rfl⟩ : syracuseStep 4921073 = 3690805) B3690805
theorem B1382179 : Blo 968591 1382179 := bstep (se 1 (by rfl) ⟨1036634, by rfl⟩ : syracuseStep 1382179 = 2073269) B2073269
theorem B2758445 : Blo 968591 2758445 := bstep (se 3 (by rfl) ⟨517208, by rfl⟩ : syracuseStep 2758445 = 1034417) B1034417
theorem B1382275 : Blo 968591 1382275 := bstep (se 1 (by rfl) ⟨1036706, by rfl⟩ : syracuseStep 1382275 = 2073413) B2073413
theorem B1841059 : Blo 968591 1841059 := bstep (se 1 (by rfl) ⟨1380794, by rfl⟩ : syracuseStep 1841059 = 2761589) B2761589
theorem B1841105 : Blo 968591 1841105 := bstep (se 2 (by rfl) ⟨690414, by rfl⟩ : syracuseStep 1841105 = 1380829) B1380829
theorem B2758627 : Blo 968591 2758627 := bstep (se 1 (by rfl) ⟨2068970, by rfl⟩ : syracuseStep 2758627 = 4137941) B4137941
theorem B2758673 : Blo 968591 2758673 := bstep (se 2 (by rfl) ⟨1034502, by rfl⟩ : syracuseStep 2758673 = 2069005) B2069005
theorem B1841393 : Blo 968591 1841393 := bstep (se 2 (by rfl) ⟨690522, by rfl⟩ : syracuseStep 1841393 = 1381045) B1381045
theorem B1382771 : Blo 968591 1382771 := bstep (se 1 (by rfl) ⟨1037078, by rfl⟩ : syracuseStep 1382771 = 2074157) B2074157
theorem B8296931 : Blo 968591 8296931 := bstep (se 1 (by rfl) ⟨6222698, by rfl⟩ : syracuseStep 8296931 = 12445397) B12445397
theorem B4430321 : Blo 968591 4430321 := bstep (se 2 (by rfl) ⟨1661370, by rfl⟩ : syracuseStep 4430321 = 3322741) B3322741
theorem B2955811 : Blo 968591 2955811 := bstep (se 1 (by rfl) ⟨2216858, by rfl⟩ : syracuseStep 2955811 = 4433717) B4433717
theorem B4659875 : Blo 968591 4659875 := bstep (se 1 (by rfl) ⟨3494906, by rfl⟩ : syracuseStep 4659875 = 6989813) B6989813
theorem B1842115 : Blo 968591 1842115 := bstep (se 1 (by rfl) ⟨1381586, by rfl⟩ : syracuseStep 1842115 = 2763173) B2763173
theorem B7379909 : Blo 968591 7379909 := bstep (se 4 (by rfl) ⟨691866, by rfl⟩ : syracuseStep 7379909 = 1383733) B1383733
theorem B1383409 : Blo 968591 1383409 := bstep (se 2 (by rfl) ⟨518778, by rfl⟩ : syracuseStep 1383409 = 1037557) B1037557
theorem B4922531 : Blo 968591 4922531 := bstep (se 1 (by rfl) ⟨3691898, by rfl⟩ : syracuseStep 4922531 = 7383797) B7383797
theorem B11050181 : Blo 968591 11050181 := bstep (se 4 (by rfl) ⟨1035954, by rfl⟩ : syracuseStep 11050181 = 2071909) B2071909
theorem B3939619 : Blo 968591 3939619 := bstep (se 1 (by rfl) ⟨2954714, by rfl⟩ : syracuseStep 3939619 = 5909429) B5909429
theorem B1383745 : Blo 968591 1383745 := bstep (se 2 (by rfl) ⟨518904, by rfl⟩ : syracuseStep 1383745 = 1037809) B1037809
theorem B1842563 : Blo 968591 1842563 := bstep (se 1 (by rfl) ⟨1381922, by rfl⟩ : syracuseStep 1842563 = 2763845) B2763845
theorem B2760131 : Blo 968591 2760131 := bstep (se 1 (by rfl) ⟨2070098, by rfl⟩ : syracuseStep 2760131 = 4140197) B4140197
theorem B2072081 : Blo 968591 2072081 := bstep (se 2 (by rfl) ⟨777030, by rfl⟩ : syracuseStep 2072081 = 1554061) B1554061
theorem B1842851 : Blo 968591 1842851 := bstep (se 1 (by rfl) ⟨1382138, by rfl⟩ : syracuseStep 1842851 = 2764277) B2764277
theorem B3677987 : Blo 968591 3677987 := bstep (se 1 (by rfl) ⟨2758490, by rfl⟩ : syracuseStep 3677987 = 5516981) B5516981
theorem B1384337 : Blo 968591 1384337 := bstep (se 2 (by rfl) ⟨519126, by rfl⟩ : syracuseStep 1384337 = 1038253) B1038253
theorem B4923341 : Blo 968591 4923341 := bstep (se 3 (by rfl) ⟨923126, by rfl⟩ : syracuseStep 4923341 = 1846253) B1846253
theorem B2105443 : Blo 968591 2105443 := bstep (se 1 (by rfl) ⟨1579082, by rfl⟩ : syracuseStep 2105443 = 3158165) B3158165
theorem B3317923 : Blo 968591 3317923 := bstep (se 1 (by rfl) ⟨2488442, by rfl⟩ : syracuseStep 3317923 = 4976885) B4976885
theorem B1089715 : Blo 968591 1089715 := bstep (se 1 (by rfl) ⟨817286, by rfl⟩ : syracuseStep 1089715 = 1634573) B1634573
theorem B4661489 : Blo 968591 4661489 := bstep (se 2 (by rfl) ⟨1748058, by rfl⟩ : syracuseStep 4661489 = 3496117) B3496117
theorem B1089859 : Blo 968591 1089859 := bstep (se 1 (by rfl) ⟨817394, by rfl⟩ : syracuseStep 1089859 = 1634789) B1634789
theorem B3678641 : Blo 968591 3678641 := bstep (se 2 (by rfl) ⟨1379490, by rfl⟩ : syracuseStep 3678641 = 2758981) B2758981
theorem B1090003 : Blo 968591 1090003 := bstep (se 1 (by rfl) ⟨817502, by rfl⟩ : syracuseStep 1090003 = 1635005) B1635005
theorem B1679891 : Blo 968591 1679891 := bstep (se 1 (by rfl) ⟨1259918, by rfl⟩ : syracuseStep 1679891 = 2519837) B2519837
theorem B5972549 : Blo 968591 5972549 := bstep (se 4 (by rfl) ⟨559926, by rfl⟩ : syracuseStep 5972549 = 1119853) B1119853
theorem B5251661 : Blo 968591 5251661 := bstep (se 3 (by rfl) ⟨984686, by rfl⟩ : syracuseStep 5251661 = 1969373) B1969373
theorem B3318353 : Blo 968591 3318353 := bstep (se 2 (by rfl) ⟨1244382, by rfl⟩ : syracuseStep 3318353 = 2488765) B2488765
theorem B1843793 : Blo 968591 1843793 := bstep (se 2 (by rfl) ⟨691422, by rfl⟩ : syracuseStep 1843793 = 1382845) B1382845
theorem B1090147 : Blo 968591 1090147 := bstep (se 1 (by rfl) ⟨817610, by rfl⟩ : syracuseStep 1090147 = 1635221) B1635221
theorem B2761361 : Blo 968591 2761361 := bstep (se 2 (by rfl) ⟨1035510, by rfl⟩ : syracuseStep 2761361 = 2071021) B2071021
theorem B1090291 : Blo 968591 1090291 := bstep (se 1 (by rfl) ⟨817718, by rfl⟩ : syracuseStep 1090291 = 1635437) B1635437
theorem B2073379 : Blo 968591 2073379 := bstep (se 1 (by rfl) ⟨1555034, by rfl⟩ : syracuseStep 2073379 = 3110069) B3110069
theorem B5907269 : Blo 968591 5907269 := bstep (se 4 (by rfl) ⟨553806, by rfl⟩ : syracuseStep 5907269 = 1107613) B1107613
theorem B1090435 : Blo 968591 1090435 := bstep (se 1 (by rfl) ⟨817826, by rfl⟩ : syracuseStep 1090435 = 1635653) B1635653
theorem B1090579 : Blo 968591 1090579 := bstep (se 1 (by rfl) ⟨817934, by rfl⟩ : syracuseStep 1090579 = 1635869) B1635869
theorem B3155075 : Blo 968591 3155075 := bstep (se 1 (by rfl) ⟨2366306, by rfl⟩ : syracuseStep 3155075 = 4732613) B4732613
theorem B1090723 : Blo 968591 1090723 := bstep (se 1 (by rfl) ⟨818042, by rfl⟩ : syracuseStep 1090723 = 1636085) B1636085
theorem B1123507 : Blo 968591 1123507 := bstep (se 1 (by rfl) ⟨842630, by rfl⟩ : syracuseStep 1123507 = 1685261) B1685261
theorem B1090867 : Blo 968591 1090867 := bstep (se 1 (by rfl) ⟨818150, by rfl⟩ : syracuseStep 1090867 = 1636301) B1636301
theorem B1091011 : Blo 968591 1091011 := bstep (se 1 (by rfl) ⟨818258, by rfl⟩ : syracuseStep 1091011 = 1636517) B1636517
theorem B2336195 : Blo 968591 2336195 := bstep (se 1 (by rfl) ⟨1752146, by rfl⟩ : syracuseStep 2336195 = 3504293) B3504293
theorem B1844689 : Blo 968591 1844689 := bstep (se 2 (by rfl) ⟨691758, by rfl⟩ : syracuseStep 1844689 = 1383517) B1383517
theorem B1091155 : Blo 968591 1091155 := bstep (se 1 (by rfl) ⟨818366, by rfl⟩ : syracuseStep 1091155 = 1636733) B1636733
theorem B1844849 : Blo 968591 1844849 := bstep (se 2 (by rfl) ⟨691818, by rfl⟩ : syracuseStep 1844849 = 1383637) B1383637
theorem B1091299 : Blo 968591 1091299 := bstep (se 1 (by rfl) ⟨818474, by rfl⟩ : syracuseStep 1091299 = 1636949) B1636949
theorem B3680099 : Blo 968591 3680099 := bstep (se 1 (by rfl) ⟨2760074, by rfl⟩ : syracuseStep 3680099 = 5520149) B5520149
theorem B3680113 : Blo 968591 3680113 := bstep (se 2 (by rfl) ⟨1380042, by rfl⟩ : syracuseStep 3680113 = 2760085) B2760085
theorem B1091443 : Blo 968591 1091443 := bstep (se 1 (by rfl) ⟨818582, by rfl⟩ : syracuseStep 1091443 = 1637165) B1637165
theorem B12593123 : Blo 968591 12593123 := bstep (se 1 (by rfl) ⟨9444842, by rfl⟩ : syracuseStep 12593123 = 18889685) B18889685
theorem B2074609 : Blo 968591 2074609 := bstep (se 2 (by rfl) ⟨777978, by rfl⟩ : syracuseStep 2074609 = 1555957) B1555957
theorem B1091587 : Blo 968591 1091587 := bstep (se 1 (by rfl) ⟨818690, by rfl⟩ : syracuseStep 1091587 = 1637381) B1637381
theorem B1845251 : Blo 968591 1845251 := bstep (se 1 (by rfl) ⟨1383938, by rfl⟩ : syracuseStep 1845251 = 2767877) B2767877
theorem B2762819 : Blo 968591 2762819 := bstep (se 1 (by rfl) ⟨2072114, by rfl⟩ : syracuseStep 2762819 = 4144229) B4144229
theorem B1091731 : Blo 968591 1091731 := bstep (se 1 (by rfl) ⟨818798, by rfl⟩ : syracuseStep 1091731 = 1637597) B1637597
theorem B4139171 : Blo 968591 4139171 := bstep (se 1 (by rfl) ⟨3104378, by rfl⟩ : syracuseStep 4139171 = 6208757) B6208757
theorem B4663565 : Blo 968591 4663565 := bstep (se 3 (by rfl) ⟨874418, by rfl⟩ : syracuseStep 4663565 = 1748837) B1748837
theorem B1091875 : Blo 968591 1091875 := bstep (se 1 (by rfl) ⟨818906, by rfl⟩ : syracuseStep 1091875 = 1637813) B1637813
theorem B1092019 : Blo 968591 1092019 := bstep (se 1 (by rfl) ⟨819014, by rfl⟩ : syracuseStep 1092019 = 1638029) B1638029
theorem B1092163 : Blo 968591 1092163 := bstep (se 1 (by rfl) ⟨819122, by rfl⟩ : syracuseStep 1092163 = 1638245) B1638245
theorem B1092307 : Blo 968591 1092307 := bstep (se 1 (by rfl) ⟨819230, by rfl⟩ : syracuseStep 1092307 = 1638461) B1638461
theorem B2075395 : Blo 968591 2075395 := bstep (se 1 (by rfl) ⟨1556546, by rfl⟩ : syracuseStep 2075395 = 3113093) B3113093
theorem B1452899 : Blo 968591 1452899 := bstep (se 1 (by rfl) ⟨1089674, by rfl⟩ : syracuseStep 1452899 = 2179349) B2179349
theorem B1092451 : Blo 968591 1092451 := bstep (se 1 (by rfl) ⟨819338, by rfl⟩ : syracuseStep 1092451 = 1638677) B1638677
theorem B2763629 : Blo 968591 2763629 := bstep (se 3 (by rfl) ⟨518180, by rfl⟩ : syracuseStep 2763629 = 1036361) B1036361
theorem B1452929 : Blo 968591 1452929 := bstep (se 2 (by rfl) ⟨544848, by rfl⟩ : syracuseStep 1452929 = 1089697) B1089697
theorem B1846147 : Blo 968591 1846147 := bstep (se 1 (by rfl) ⟨1384610, by rfl⟩ : syracuseStep 1846147 = 2769221) B2769221
theorem B1452947 : Blo 968591 1452947 := bstep (se 1 (by rfl) ⟨1089710, by rfl⟩ : syracuseStep 1452947 = 2179421) B2179421
theorem B1452977 : Blo 968591 1452977 := bstep (se 2 (by rfl) ⟨544866, by rfl⟩ : syracuseStep 1452977 = 1089733) B1089733
theorem B1452995 : Blo 968591 1452995 := bstep (se 1 (by rfl) ⟨1089746, by rfl⟩ : syracuseStep 1452995 = 2179493) B2179493
theorem B1453025 : Blo 968591 1453025 := bstep (se 2 (by rfl) ⟨544884, by rfl⟩ : syracuseStep 1453025 = 1089769) B1089769
theorem B1453043 : Blo 968591 1453043 := bstep (se 1 (by rfl) ⟨1089782, by rfl⟩ : syracuseStep 1453043 = 2179565) B2179565
theorem B1092595 : Blo 968591 1092595 := bstep (se 1 (by rfl) ⟨819446, by rfl⟩ : syracuseStep 1092595 = 1638893) B1638893
theorem B1453073 : Blo 968591 1453073 := bstep (se 2 (by rfl) ⟨544902, by rfl⟩ : syracuseStep 1453073 = 1089805) B1089805
theorem B1453091 : Blo 968591 1453091 := bstep (se 1 (by rfl) ⟨1089818, by rfl⟩ : syracuseStep 1453091 = 2179637) B2179637
theorem B1846307 : Blo 968591 1846307 := bstep (se 1 (by rfl) ⟨1384730, by rfl⟩ : syracuseStep 1846307 = 2769461) B2769461
theorem B2763821 : Blo 968591 2763821 := bstep (se 3 (by rfl) ⟨518216, by rfl⟩ : syracuseStep 2763821 = 1036433) B1036433
theorem B1453121 : Blo 968591 1453121 := bstep (se 2 (by rfl) ⟨544920, by rfl⟩ : syracuseStep 1453121 = 1089841) B1089841
theorem B1453139 : Blo 968591 1453139 := bstep (se 1 (by rfl) ⟨1089854, by rfl⟩ : syracuseStep 1453139 = 2179709) B2179709
theorem B1453169 : Blo 968591 1453169 := bstep (se 2 (by rfl) ⟨544938, by rfl⟩ : syracuseStep 1453169 = 1089877) B1089877
theorem B1453187 : Blo 968591 1453187 := bstep (se 1 (by rfl) ⟨1089890, by rfl⟩ : syracuseStep 1453187 = 2179781) B2179781
theorem B1092739 : Blo 968591 1092739 := bstep (se 1 (by rfl) ⟨819554, by rfl⟩ : syracuseStep 1092739 = 1639109) B1639109
theorem B1453217 : Blo 968591 1453217 := bstep (se 2 (by rfl) ⟨544956, by rfl⟩ : syracuseStep 1453217 = 1089913) B1089913
theorem B1551523 : Blo 968591 1551523 := bstep (se 1 (by rfl) ⟨1163642, by rfl⟩ : syracuseStep 1551523 = 2327285) B2327285
theorem B1453235 : Blo 968591 1453235 := bstep (se 1 (by rfl) ⟨1089926, by rfl⟩ : syracuseStep 1453235 = 2179853) B2179853
theorem B1453265 : Blo 968591 1453265 := bstep (se 2 (by rfl) ⟨544974, by rfl⟩ : syracuseStep 1453265 = 1089949) B1089949
theorem B1453283 : Blo 968591 1453283 := bstep (se 1 (by rfl) ⟨1089962, by rfl⟩ : syracuseStep 1453283 = 2179925) B2179925
theorem B1453313 : Blo 968591 1453313 := bstep (se 2 (by rfl) ⟨544992, by rfl⟩ : syracuseStep 1453313 = 1089985) B1089985
theorem B3321101 : Blo 968591 3321101 := bstep (se 3 (by rfl) ⟨622706, by rfl⟩ : syracuseStep 3321101 = 1245413) B1245413
theorem B1453331 : Blo 968591 1453331 := bstep (se 1 (by rfl) ⟨1089998, by rfl⟩ : syracuseStep 1453331 = 2179997) B2179997
theorem B1092883 : Blo 968591 1092883 := bstep (se 1 (by rfl) ⟨819662, by rfl⟩ : syracuseStep 1092883 = 1639325) B1639325
theorem B3681571 : Blo 968591 3681571 := bstep (se 1 (by rfl) ⟨2761178, by rfl⟩ : syracuseStep 3681571 = 5522357) B5522357
theorem B1453361 : Blo 968591 1453361 := bstep (se 2 (by rfl) ⟨545010, by rfl⟩ : syracuseStep 1453361 = 1090021) B1090021
theorem B1453379 : Blo 968591 1453379 := bstep (se 1 (by rfl) ⟨1090034, by rfl⟩ : syracuseStep 1453379 = 2180069) B2180069
theorem B1453409 : Blo 968591 1453409 := bstep (se 2 (by rfl) ⟨545028, by rfl⟩ : syracuseStep 1453409 = 1090057) B1090057
theorem B1453427 : Blo 968591 1453427 := bstep (se 1 (by rfl) ⟨1090070, by rfl⟩ : syracuseStep 1453427 = 2180141) B2180141
theorem B1453457 : Blo 968591 1453457 := bstep (se 2 (by rfl) ⟨545046, by rfl⟩ : syracuseStep 1453457 = 1090093) B1090093
theorem B5516707 : Blo 968591 5516707 := bstep (se 1 (by rfl) ⟨4137530, by rfl⟩ : syracuseStep 5516707 = 8275061) B8275061
theorem B1453475 : Blo 968591 1453475 := bstep (se 1 (by rfl) ⟨1090106, by rfl⟩ : syracuseStep 1453475 = 2180213) B2180213
theorem B1093027 : Blo 968591 1093027 := bstep (se 1 (by rfl) ⟨819770, by rfl⟩ : syracuseStep 1093027 = 1639541) B1639541
theorem B1551793 : Blo 968591 1551793 := bstep (se 2 (by rfl) ⟨581922, by rfl⟩ : syracuseStep 1551793 = 1163845) B1163845
theorem B1453505 : Blo 968591 1453505 := bstep (se 2 (by rfl) ⟨545064, by rfl⟩ : syracuseStep 1453505 = 1090129) B1090129
theorem B2076113 : Blo 968591 2076113 := bstep (se 2 (by rfl) ⟨778542, by rfl⟩ : syracuseStep 2076113 = 1557085) B1557085
theorem B1453523 : Blo 968591 1453523 := bstep (se 1 (by rfl) ⟨1090142, by rfl⟩ : syracuseStep 1453523 = 2180285) B2180285
theorem B1453553 : Blo 968591 1453553 := bstep (se 2 (by rfl) ⟨545082, by rfl⟩ : syracuseStep 1453553 = 1090165) B1090165
theorem B1453571 : Blo 968591 1453571 := bstep (se 1 (by rfl) ⟨1090178, by rfl⟩ : syracuseStep 1453571 = 2180357) B2180357
theorem B4435469 : Blo 968591 4435469 := bstep (se 3 (by rfl) ⟨831650, by rfl⟩ : syracuseStep 4435469 = 1663301) B1663301
theorem B1453601 : Blo 968591 1453601 := bstep (se 2 (by rfl) ⟨545100, by rfl⟩ : syracuseStep 1453601 = 1090201) B1090201
theorem B1453619 : Blo 968591 1453619 := bstep (se 1 (by rfl) ⟨1090214, by rfl⟩ : syracuseStep 1453619 = 2180429) B2180429
theorem B1093171 : Blo 968591 1093171 := bstep (se 1 (by rfl) ⟨819878, by rfl⟩ : syracuseStep 1093171 = 1639757) B1639757
theorem B1453649 : Blo 968591 1453649 := bstep (se 2 (by rfl) ⟨545118, by rfl⟩ : syracuseStep 1453649 = 1090237) B1090237
theorem B1453667 : Blo 968591 1453667 := bstep (se 1 (by rfl) ⟨1090250, by rfl⟩ : syracuseStep 1453667 = 2180501) B2180501
theorem B2993773 : Blo 968591 2993773 := bstep (se 3 (by rfl) ⟨561332, by rfl⟩ : syracuseStep 2993773 = 1122665) B1122665
theorem B1453697 : Blo 968591 1453697 := bstep (se 2 (by rfl) ⟨545136, by rfl⟩ : syracuseStep 1453697 = 1090273) B1090273
theorem B1453715 : Blo 968591 1453715 := bstep (se 1 (by rfl) ⟨1090286, by rfl⟩ : syracuseStep 1453715 = 2180573) B2180573
theorem B1552049 : Blo 968591 1552049 := bstep (se 2 (by rfl) ⟨582018, by rfl⟩ : syracuseStep 1552049 = 1164037) B1164037
theorem B1453745 : Blo 968591 1453745 := bstep (se 2 (by rfl) ⟨545154, by rfl⟩ : syracuseStep 1453745 = 1090309) B1090309
theorem B1453763 : Blo 968591 1453763 := bstep (se 1 (by rfl) ⟨1090322, by rfl⟩ : syracuseStep 1453763 = 2180645) B2180645
theorem B1093315 : Blo 968591 1093315 := bstep (se 1 (by rfl) ⟨819986, by rfl⟩ : syracuseStep 1093315 = 1639973) B1639973
theorem B1453793 : Blo 968591 1453793 := bstep (se 2 (by rfl) ⟨545172, by rfl⟩ : syracuseStep 1453793 = 1090345) B1090345
theorem B1453811 : Blo 968591 1453811 := bstep (se 1 (by rfl) ⟨1090358, by rfl⟩ : syracuseStep 1453811 = 2180717) B2180717
theorem B1453841 : Blo 968591 1453841 := bstep (se 2 (by rfl) ⟨545190, by rfl⟩ : syracuseStep 1453841 = 1090381) B1090381
theorem B1453859 : Blo 968591 1453859 := bstep (se 1 (by rfl) ⟨1090394, by rfl⟩ : syracuseStep 1453859 = 2180789) B2180789
theorem B1453889 : Blo 968591 1453889 := bstep (se 2 (by rfl) ⟨545208, by rfl⟩ : syracuseStep 1453889 = 1090417) B1090417
theorem B1453907 : Blo 968591 1453907 := bstep (se 1 (by rfl) ⟨1090430, by rfl⟩ : syracuseStep 1453907 = 2180861) B2180861
theorem B1093459 : Blo 968591 1093459 := bstep (se 1 (by rfl) ⟨820094, by rfl⟩ : syracuseStep 1093459 = 1640189) B1640189
theorem B1453937 : Blo 968591 1453937 := bstep (se 2 (by rfl) ⟨545226, by rfl⟩ : syracuseStep 1453937 = 1090453) B1090453
theorem B1453955 : Blo 968591 1453955 := bstep (se 1 (by rfl) ⟨1090466, by rfl⟩ : syracuseStep 1453955 = 2180933) B2180933
theorem B1453985 : Blo 968591 1453985 := bstep (se 2 (by rfl) ⟨545244, by rfl⟩ : syracuseStep 1453985 = 1090489) B1090489
theorem B5517233 : Blo 968591 5517233 := bstep (se 2 (by rfl) ⟨2068962, by rfl⟩ : syracuseStep 5517233 = 4137925) B4137925
theorem B1454003 : Blo 968591 1454003 := bstep (se 1 (by rfl) ⟨1090502, by rfl⟩ : syracuseStep 1454003 = 2181005) B2181005
theorem B1454033 : Blo 968591 1454033 := bstep (se 2 (by rfl) ⟨545262, by rfl⟩ : syracuseStep 1454033 = 1090525) B1090525
theorem B2076625 : Blo 968591 2076625 := bstep (se 2 (by rfl) ⟨778734, by rfl⟩ : syracuseStep 2076625 = 1557469) B1557469
theorem B1454051 : Blo 968591 1454051 := bstep (se 1 (by rfl) ⟨1090538, by rfl⟩ : syracuseStep 1454051 = 2181077) B2181077
theorem B1093603 : Blo 968591 1093603 := bstep (se 1 (by rfl) ⟨820202, by rfl⟩ : syracuseStep 1093603 = 1640405) B1640405
theorem B1454081 : Blo 968591 1454081 := bstep (se 2 (by rfl) ⟨545280, by rfl⟩ : syracuseStep 1454081 = 1090561) B1090561
theorem B2764813 : Blo 968591 2764813 := bstep (se 3 (by rfl) ⟨518402, by rfl⟩ : syracuseStep 2764813 = 1036805) B1036805
theorem B1454099 : Blo 968591 1454099 := bstep (se 1 (by rfl) ⟨1090574, by rfl⟩ : syracuseStep 1454099 = 2181149) B2181149
theorem B1454129 : Blo 968591 1454129 := bstep (se 2 (by rfl) ⟨545298, by rfl⟩ : syracuseStep 1454129 = 1090597) B1090597
theorem B1454147 : Blo 968591 1454147 := bstep (se 1 (by rfl) ⟨1090610, by rfl⟩ : syracuseStep 1454147 = 2181221) B2181221
theorem B1454177 : Blo 968591 1454177 := bstep (se 2 (by rfl) ⟨545316, by rfl⟩ : syracuseStep 1454177 = 1090633) B1090633
theorem B8400995 : Blo 968591 8400995 := bstep (se 1 (by rfl) ⟨6300746, by rfl⟩ : syracuseStep 8400995 = 12601493) B12601493
theorem B1454195 : Blo 968591 1454195 := bstep (se 1 (by rfl) ⟨1090646, by rfl⟩ : syracuseStep 1454195 = 2181293) B2181293
theorem B1093747 : Blo 968591 1093747 := bstep (se 1 (by rfl) ⟨820310, by rfl⟩ : syracuseStep 1093747 = 1640621) B1640621
theorem B1454225 : Blo 968591 1454225 := bstep (se 2 (by rfl) ⟨545334, by rfl⟩ : syracuseStep 1454225 = 1090669) B1090669
theorem B1454243 : Blo 968591 1454243 := bstep (se 1 (by rfl) ⟨1090682, by rfl⟩ : syracuseStep 1454243 = 2181365) B2181365
theorem B1454273 : Blo 968591 1454273 := bstep (se 2 (by rfl) ⟨545352, by rfl⟩ : syracuseStep 1454273 = 1090705) B1090705
theorem B1454291 : Blo 968591 1454291 := bstep (se 1 (by rfl) ⟨1090718, by rfl⟩ : syracuseStep 1454291 = 2181437) B2181437
theorem B1454321 : Blo 968591 1454321 := bstep (se 2 (by rfl) ⟨545370, by rfl⟩ : syracuseStep 1454321 = 1090741) B1090741
theorem B1454339 : Blo 968591 1454339 := bstep (se 1 (by rfl) ⟨1090754, by rfl⟩ : syracuseStep 1454339 = 2181509) B2181509
theorem B1093891 : Blo 968591 1093891 := bstep (se 1 (by rfl) ⟨820418, by rfl⟩ : syracuseStep 1093891 = 1640837) B1640837
theorem B1454369 : Blo 968591 1454369 := bstep (se 2 (by rfl) ⟨545388, by rfl⟩ : syracuseStep 1454369 = 1090777) B1090777
theorem B1454387 : Blo 968591 1454387 := bstep (se 1 (by rfl) ⟨1090790, by rfl⟩ : syracuseStep 1454387 = 2181581) B2181581
theorem B1454417 : Blo 968591 1454417 := bstep (se 2 (by rfl) ⟨545406, by rfl⟩ : syracuseStep 1454417 = 1090813) B1090813
theorem B1454435 : Blo 968591 1454435 := bstep (se 1 (by rfl) ⟨1090826, by rfl⟩ : syracuseStep 1454435 = 2181653) B2181653
theorem B1552753 : Blo 968591 1552753 := bstep (se 2 (by rfl) ⟨582282, by rfl⟩ : syracuseStep 1552753 = 1164565) B1164565
theorem B1454465 : Blo 968591 1454465 := bstep (se 2 (by rfl) ⟨545424, by rfl⟩ : syracuseStep 1454465 = 1090849) B1090849
theorem B1454483 : Blo 968591 1454483 := bstep (se 1 (by rfl) ⟨1090862, by rfl⟩ : syracuseStep 1454483 = 2181725) B2181725
theorem B1094035 : Blo 968591 1094035 := bstep (se 1 (by rfl) ⟨820526, by rfl⟩ : syracuseStep 1094035 = 1641053) B1641053
theorem B1454513 : Blo 968591 1454513 := bstep (se 2 (by rfl) ⟨545442, by rfl⟩ : syracuseStep 1454513 = 1090885) B1090885
theorem B1454531 : Blo 968591 1454531 := bstep (se 1 (by rfl) ⟨1090898, by rfl⟩ : syracuseStep 1454531 = 2181797) B2181797
theorem B1454561 : Blo 968591 1454561 := bstep (se 2 (by rfl) ⟨545460, by rfl⟩ : syracuseStep 1454561 = 1090921) B1090921
theorem B1454579 : Blo 968591 1454579 := bstep (se 1 (by rfl) ⟨1090934, by rfl⟩ : syracuseStep 1454579 = 2181869) B2181869
theorem B1454609 : Blo 968591 1454609 := bstep (se 2 (by rfl) ⟨545478, by rfl⟩ : syracuseStep 1454609 = 1090957) B1090957
theorem B1454627 : Blo 968591 1454627 := bstep (se 1 (by rfl) ⟨1090970, by rfl⟩ : syracuseStep 1454627 = 2181941) B2181941
theorem B1454657 : Blo 968591 1454657 := bstep (se 2 (by rfl) ⟨545496, by rfl⟩ : syracuseStep 1454657 = 1090993) B1090993
theorem B1454675 : Blo 968591 1454675 := bstep (se 1 (by rfl) ⟨1091006, by rfl⟩ : syracuseStep 1454675 = 2182013) B2182013
theorem B1454705 : Blo 968591 1454705 := bstep (se 2 (by rfl) ⟨545514, by rfl⟩ : syracuseStep 1454705 = 1091029) B1091029
theorem B1454723 : Blo 968591 1454723 := bstep (se 1 (by rfl) ⟨1091042, by rfl⟩ : syracuseStep 1454723 = 2182085) B2182085
theorem B5911181 : Blo 968591 5911181 := bstep (se 3 (by rfl) ⟨1108346, by rfl⟩ : syracuseStep 5911181 = 2216693) B2216693
theorem B1454753 : Blo 968591 1454753 := bstep (se 2 (by rfl) ⟨545532, by rfl⟩ : syracuseStep 1454753 = 1091065) B1091065
theorem B1454771 : Blo 968591 1454771 := bstep (se 1 (by rfl) ⟨1091078, by rfl⟩ : syracuseStep 1454771 = 2182157) B2182157
theorem B1454801 : Blo 968591 1454801 := bstep (se 2 (by rfl) ⟨545550, by rfl⟩ : syracuseStep 1454801 = 1091101) B1091101
theorem B1454819 : Blo 968591 1454819 := bstep (se 1 (by rfl) ⟨1091114, by rfl⟩ : syracuseStep 1454819 = 2182229) B2182229
theorem B1454849 : Blo 968591 1454849 := bstep (se 2 (by rfl) ⟨545568, by rfl⟩ : syracuseStep 1454849 = 1091137) B1091137
theorem B1454867 : Blo 968591 1454867 := bstep (se 1 (by rfl) ⟨1091150, by rfl⟩ : syracuseStep 1454867 = 2182301) B2182301
theorem B1454897 : Blo 968591 1454897 := bstep (se 2 (by rfl) ⟨545586, by rfl⟩ : syracuseStep 1454897 = 1091173) B1091173
theorem B1454915 : Blo 968591 1454915 := bstep (se 1 (by rfl) ⟨1091186, by rfl⟩ : syracuseStep 1454915 = 2182373) B2182373
theorem B1454945 : Blo 968591 1454945 := bstep (se 2 (by rfl) ⟨545604, by rfl⟩ : syracuseStep 1454945 = 1091209) B1091209
theorem B1454963 : Blo 968591 1454963 := bstep (se 1 (by rfl) ⟨1091222, by rfl⟩ : syracuseStep 1454963 = 2182445) B2182445
theorem B11056013 : Blo 968591 11056013 := bstep (se 3 (by rfl) ⟨2073002, by rfl⟩ : syracuseStep 11056013 = 4146005) B4146005
theorem B1454993 : Blo 968591 1454993 := bstep (se 2 (by rfl) ⟨545622, by rfl⟩ : syracuseStep 1454993 = 1091245) B1091245
theorem B1455011 : Blo 968591 1455011 := bstep (se 1 (by rfl) ⟨1091258, by rfl⟩ : syracuseStep 1455011 = 2182517) B2182517
theorem B1455041 : Blo 968591 1455041 := bstep (se 2 (by rfl) ⟨545640, by rfl⟩ : syracuseStep 1455041 = 1091281) B1091281
theorem B1455059 : Blo 968591 1455059 := bstep (se 1 (by rfl) ⟨1091294, by rfl⟩ : syracuseStep 1455059 = 2182589) B2182589
theorem B1455089 : Blo 968591 1455089 := bstep (se 2 (by rfl) ⟨545658, by rfl⟩ : syracuseStep 1455089 = 1091317) B1091317
theorem B1455107 : Blo 968591 1455107 := bstep (se 1 (by rfl) ⟨1091330, by rfl⟩ : syracuseStep 1455107 = 2182661) B2182661
theorem B1455137 : Blo 968591 1455137 := bstep (se 2 (by rfl) ⟨545676, by rfl⟩ : syracuseStep 1455137 = 1091353) B1091353
theorem B1455155 : Blo 968591 1455155 := bstep (se 1 (by rfl) ⟨1091366, by rfl⟩ : syracuseStep 1455155 = 2182733) B2182733
theorem B1455185 : Blo 968591 1455185 := bstep (se 2 (by rfl) ⟨545694, by rfl⟩ : syracuseStep 1455185 = 1091389) B1091389
theorem B1455203 : Blo 968591 1455203 := bstep (se 1 (by rfl) ⟨1091402, by rfl⟩ : syracuseStep 1455203 = 2182805) B2182805
theorem B1455233 : Blo 968591 1455233 := bstep (se 2 (by rfl) ⟨545712, by rfl⟩ : syracuseStep 1455233 = 1091425) B1091425
theorem B1455251 : Blo 968591 1455251 := bstep (se 1 (by rfl) ⟨1091438, by rfl⟩ : syracuseStep 1455251 = 2182877) B2182877
theorem B1455281 : Blo 968591 1455281 := bstep (se 2 (by rfl) ⟨545730, by rfl⟩ : syracuseStep 1455281 = 1091461) B1091461
theorem B1455299 : Blo 968591 1455299 := bstep (se 1 (by rfl) ⟨1091474, by rfl⟩ : syracuseStep 1455299 = 2182949) B2182949
theorem B1455329 : Blo 968591 1455329 := bstep (se 2 (by rfl) ⟨545748, by rfl⟩ : syracuseStep 1455329 = 1091497) B1091497
theorem B1225955 : Blo 968591 1225955 := bstep (se 1 (by rfl) ⟨919466, by rfl⟩ : syracuseStep 1225955 = 1838933) B1838933
theorem B1553651 : Blo 968591 1553651 := bstep (se 1 (by rfl) ⟨1165238, by rfl⟩ : syracuseStep 1553651 = 2330477) B2330477
theorem B1455347 : Blo 968591 1455347 := bstep (se 1 (by rfl) ⟨1091510, by rfl⟩ : syracuseStep 1455347 = 2183021) B2183021
theorem B1455377 : Blo 968591 1455377 := bstep (se 2 (by rfl) ⟨545766, by rfl⟩ : syracuseStep 1455377 = 1091533) B1091533
theorem B1455395 : Blo 968591 1455395 := bstep (se 1 (by rfl) ⟨1091546, by rfl⟩ : syracuseStep 1455395 = 2183093) B2183093
theorem B1455425 : Blo 968591 1455425 := bstep (se 2 (by rfl) ⟨545784, by rfl⟩ : syracuseStep 1455425 = 1091569) B1091569
theorem B1455443 : Blo 968591 1455443 := bstep (se 1 (by rfl) ⟨1091582, by rfl⟩ : syracuseStep 1455443 = 2183165) B2183165
theorem B2209123 : Blo 968591 2209123 := bstep (se 1 (by rfl) ⟨1656842, by rfl⟩ : syracuseStep 2209123 = 3313685) B3313685
theorem B5518691 : Blo 968591 5518691 := bstep (se 1 (by rfl) ⟨4139018, by rfl⟩ : syracuseStep 5518691 = 8278037) B8278037
theorem B1455473 : Blo 968591 1455473 := bstep (se 2 (by rfl) ⟨545802, by rfl⟩ : syracuseStep 1455473 = 1091605) B1091605
theorem B1455491 : Blo 968591 1455491 := bstep (se 1 (by rfl) ⟨1091618, by rfl⟩ : syracuseStep 1455491 = 2183237) B2183237
theorem B18691469 : Blo 968591 18691469 := bstep (se 3 (by rfl) ⟨3504650, by rfl⟩ : syracuseStep 18691469 = 7009301) B7009301
theorem B1455521 : Blo 968591 1455521 := bstep (se 2 (by rfl) ⟨545820, by rfl⟩ : syracuseStep 1455521 = 1091641) B1091641
theorem B1553843 : Blo 968591 1553843 := bstep (se 1 (by rfl) ⟨1165382, by rfl⟩ : syracuseStep 1553843 = 2330765) B2330765
theorem B1455539 : Blo 968591 1455539 := bstep (se 1 (by rfl) ⟨1091654, by rfl⟩ : syracuseStep 1455539 = 2183309) B2183309
theorem B3683789 : Blo 968591 3683789 := bstep (se 3 (by rfl) ⟨690710, by rfl⟩ : syracuseStep 3683789 = 1381421) B1381421
theorem B1455569 : Blo 968591 1455569 := bstep (se 2 (by rfl) ⟨545838, by rfl⟩ : syracuseStep 1455569 = 1091677) B1091677
theorem B1455587 : Blo 968591 1455587 := bstep (se 1 (by rfl) ⟨1091690, by rfl⟩ : syracuseStep 1455587 = 2183381) B2183381
theorem B1455617 : Blo 968591 1455617 := bstep (se 2 (by rfl) ⟨545856, by rfl⟩ : syracuseStep 1455617 = 1091713) B1091713
theorem B1455635 : Blo 968591 1455635 := bstep (se 1 (by rfl) ⟨1091726, by rfl⟩ : syracuseStep 1455635 = 2183453) B2183453
theorem B1455665 : Blo 968591 1455665 := bstep (se 2 (by rfl) ⟨545874, by rfl⟩ : syracuseStep 1455665 = 1091749) B1091749
theorem B1455683 : Blo 968591 1455683 := bstep (se 1 (by rfl) ⟨1091762, by rfl⟩ : syracuseStep 1455683 = 2183525) B2183525
theorem B1455713 : Blo 968591 1455713 := bstep (se 2 (by rfl) ⟨545892, by rfl⟩ : syracuseStep 1455713 = 1091785) B1091785
theorem B1455731 : Blo 968591 1455731 := bstep (se 1 (by rfl) ⟨1091798, by rfl⟩ : syracuseStep 1455731 = 2183597) B2183597
theorem B1455761 : Blo 968591 1455761 := bstep (se 2 (by rfl) ⟨545910, by rfl⟩ : syracuseStep 1455761 = 1091821) B1091821
theorem B1455779 : Blo 968591 1455779 := bstep (se 1 (by rfl) ⟨1091834, by rfl⟩ : syracuseStep 1455779 = 2183669) B2183669
theorem B1455809 : Blo 968591 1455809 := bstep (se 2 (by rfl) ⟨545928, by rfl⟩ : syracuseStep 1455809 = 1091857) B1091857
theorem B2766545 : Blo 968591 2766545 := bstep (se 2 (by rfl) ⟨1037454, by rfl⟩ : syracuseStep 2766545 = 2074909) B2074909
theorem B1455827 : Blo 968591 1455827 := bstep (se 1 (by rfl) ⟨1091870, by rfl⟩ : syracuseStep 1455827 = 2183741) B2183741
theorem B1455857 : Blo 968591 1455857 := bstep (se 2 (by rfl) ⟨545946, by rfl⟩ : syracuseStep 1455857 = 1091893) B1091893
theorem B1455875 : Blo 968591 1455875 := bstep (se 1 (by rfl) ⟨1091906, by rfl⟩ : syracuseStep 1455875 = 2183813) B2183813
theorem B1455905 : Blo 968591 1455905 := bstep (se 2 (by rfl) ⟨545964, by rfl⟩ : syracuseStep 1455905 = 1091929) B1091929
theorem B4142897 : Blo 968591 4142897 := bstep (se 2 (by rfl) ⟨1553586, by rfl⟩ : syracuseStep 4142897 = 3107173) B3107173
theorem B1455923 : Blo 968591 1455923 := bstep (se 1 (by rfl) ⟨1091942, by rfl⟩ : syracuseStep 1455923 = 2183885) B2183885
theorem B1455953 : Blo 968591 1455953 := bstep (se 2 (by rfl) ⟨545982, by rfl⟩ : syracuseStep 1455953 = 1091965) B1091965
theorem B1455971 : Blo 968591 1455971 := bstep (se 1 (by rfl) ⟨1091978, by rfl⟩ : syracuseStep 1455971 = 2183957) B2183957
theorem B1456001 : Blo 968591 1456001 := bstep (se 2 (by rfl) ⟨546000, by rfl⟩ : syracuseStep 1456001 = 1092001) B1092001
theorem B2766737 : Blo 968591 2766737 := bstep (se 2 (by rfl) ⟨1037526, by rfl⟩ : syracuseStep 2766737 = 2075053) B2075053
theorem B1456019 : Blo 968591 1456019 := bstep (se 1 (by rfl) ⟨1092014, by rfl⟩ : syracuseStep 1456019 = 2184029) B2184029
theorem B1226659 : Blo 968591 1226659 := bstep (se 1 (by rfl) ⟨919994, by rfl⟩ : syracuseStep 1226659 = 1839989) B1839989
theorem B1456049 : Blo 968591 1456049 := bstep (se 2 (by rfl) ⟨546018, by rfl⟩ : syracuseStep 1456049 = 1092037) B1092037
theorem B1456067 : Blo 968591 1456067 := bstep (se 1 (by rfl) ⟨1092050, by rfl⟩ : syracuseStep 1456067 = 2184101) B2184101
theorem B1456097 : Blo 968591 1456097 := bstep (se 2 (by rfl) ⟨546036, by rfl⟩ : syracuseStep 1456097 = 1092073) B1092073
theorem B1456115 : Blo 968591 1456115 := bstep (se 1 (by rfl) ⟨1092086, by rfl⟩ : syracuseStep 1456115 = 2184173) B2184173
theorem B1226755 : Blo 968591 1226755 := bstep (se 1 (by rfl) ⟨920066, by rfl⟩ : syracuseStep 1226755 = 1840133) B1840133
theorem B1456145 : Blo 968591 1456145 := bstep (se 2 (by rfl) ⟨546054, by rfl⟩ : syracuseStep 1456145 = 1092109) B1092109
theorem B1456163 : Blo 968591 1456163 := bstep (se 1 (by rfl) ⟨1092122, by rfl⟩ : syracuseStep 1456163 = 2184245) B2184245
theorem B1456193 : Blo 968591 1456193 := bstep (se 2 (by rfl) ⟨546072, by rfl⟩ : syracuseStep 1456193 = 1092145) B1092145
theorem B1456211 : Blo 968591 1456211 := bstep (se 1 (by rfl) ⟨1092158, by rfl⟩ : syracuseStep 1456211 = 2184317) B2184317
theorem B1456241 : Blo 968591 1456241 := bstep (se 2 (by rfl) ⟨546090, by rfl⟩ : syracuseStep 1456241 = 1092181) B1092181
theorem B1456259 : Blo 968591 1456259 := bstep (se 1 (by rfl) ⟨1092194, by rfl⟩ : syracuseStep 1456259 = 2184389) B2184389
theorem B1456289 : Blo 968591 1456289 := bstep (se 2 (by rfl) ⟨546108, by rfl⟩ : syracuseStep 1456289 = 1092217) B1092217
theorem B1456307 : Blo 968591 1456307 := bstep (se 1 (by rfl) ⟨1092230, by rfl⟩ : syracuseStep 1456307 = 2184461) B2184461
theorem B1456337 : Blo 968591 1456337 := bstep (se 2 (by rfl) ⟨546126, by rfl⟩ : syracuseStep 1456337 = 1092253) B1092253
theorem B1456355 : Blo 968591 1456355 := bstep (se 1 (by rfl) ⟨1092266, by rfl⟩ : syracuseStep 1456355 = 2184533) B2184533
theorem B1456385 : Blo 968591 1456385 := bstep (se 2 (by rfl) ⟨546144, by rfl⟩ : syracuseStep 1456385 = 1092289) B1092289
theorem B1456403 : Blo 968591 1456403 := bstep (se 1 (by rfl) ⟨1092302, by rfl⟩ : syracuseStep 1456403 = 2184605) B2184605
theorem B1456433 : Blo 968591 1456433 := bstep (se 2 (by rfl) ⟨546162, by rfl⟩ : syracuseStep 1456433 = 1092325) B1092325
theorem B1456451 : Blo 968591 1456451 := bstep (se 1 (by rfl) ⟨1092338, by rfl⟩ : syracuseStep 1456451 = 2184677) B2184677
theorem B5257541 : Blo 968591 5257541 := bstep (se 4 (by rfl) ⟨492894, by rfl⟩ : syracuseStep 5257541 = 985789) B985789
theorem B1456481 : Blo 968591 1456481 := bstep (se 2 (by rfl) ⟨546180, by rfl⟩ : syracuseStep 1456481 = 1092361) B1092361
theorem B1456499 : Blo 968591 1456499 := bstep (se 1 (by rfl) ⟨1092374, by rfl⟩ : syracuseStep 1456499 = 2184749) B2184749
theorem B1554817 : Blo 968591 1554817 := bstep (se 2 (by rfl) ⟨583056, by rfl⟩ : syracuseStep 1554817 = 1166113) B1166113
theorem B1456529 : Blo 968591 1456529 := bstep (se 2 (by rfl) ⟨546198, by rfl⟩ : syracuseStep 1456529 = 1092397) B1092397
theorem B1456547 : Blo 968591 1456547 := bstep (se 1 (by rfl) ⟨1092410, by rfl⟩ : syracuseStep 1456547 = 2184821) B2184821
theorem B1456577 : Blo 968591 1456577 := bstep (se 2 (by rfl) ⟨546216, by rfl⟩ : syracuseStep 1456577 = 1092433) B1092433
theorem B1456595 : Blo 968591 1456595 := bstep (se 1 (by rfl) ⟨1092446, by rfl⟩ : syracuseStep 1456595 = 2184893) B2184893
theorem B1456625 : Blo 968591 1456625 := bstep (se 2 (by rfl) ⟨546234, by rfl⟩ : syracuseStep 1456625 = 1092469) B1092469
theorem B1227251 : Blo 968591 1227251 := bstep (se 1 (by rfl) ⟨920438, by rfl⟩ : syracuseStep 1227251 = 1840877) B1840877
theorem B1456643 : Blo 968591 1456643 := bstep (se 1 (by rfl) ⟨1092482, by rfl⟩ : syracuseStep 1456643 = 2184965) B2184965
theorem B1456673 : Blo 968591 1456673 := bstep (se 2 (by rfl) ⟨546252, by rfl⟩ : syracuseStep 1456673 = 1092505) B1092505
theorem B1456691 : Blo 968591 1456691 := bstep (se 1 (by rfl) ⟨1092518, by rfl⟩ : syracuseStep 1456691 = 2185037) B2185037
theorem B1456721 : Blo 968591 1456721 := bstep (se 2 (by rfl) ⟨546270, by rfl⟩ : syracuseStep 1456721 = 1092541) B1092541
theorem B1456739 : Blo 968591 1456739 := bstep (se 1 (by rfl) ⟨1092554, by rfl⟩ : syracuseStep 1456739 = 2185109) B2185109
theorem B2210417 : Blo 968591 2210417 := bstep (se 2 (by rfl) ⟨828906, by rfl⟩ : syracuseStep 2210417 = 1657813) B1657813
theorem B1456769 : Blo 968591 1456769 := bstep (se 2 (by rfl) ⟨546288, by rfl⟩ : syracuseStep 1456769 = 1092577) B1092577
theorem B1456787 : Blo 968591 1456787 := bstep (se 1 (by rfl) ⟨1092590, by rfl⟩ : syracuseStep 1456787 = 2185181) B2185181
theorem B1456817 : Blo 968591 1456817 := bstep (se 2 (by rfl) ⟨546306, by rfl⟩ : syracuseStep 1456817 = 1092613) B1092613
theorem B1456835 : Blo 968591 1456835 := bstep (se 1 (by rfl) ⟨1092626, by rfl⟩ : syracuseStep 1456835 = 2185253) B2185253
theorem B1456865 : Blo 968591 1456865 := bstep (se 2 (by rfl) ⟨546324, by rfl⟩ : syracuseStep 1456865 = 1092649) B1092649
theorem B1456883 : Blo 968591 1456883 := bstep (se 1 (by rfl) ⟨1092662, by rfl⟩ : syracuseStep 1456883 = 2185325) B2185325
theorem B1456913 : Blo 968591 1456913 := bstep (se 2 (by rfl) ⟨546342, by rfl⟩ : syracuseStep 1456913 = 1092685) B1092685
theorem B1456931 : Blo 968591 1456931 := bstep (se 1 (by rfl) ⟨1092698, by rfl⟩ : syracuseStep 1456931 = 2185397) B2185397
theorem B1555265 : Blo 968591 1555265 := bstep (se 2 (by rfl) ⟨583224, by rfl⟩ : syracuseStep 1555265 = 1166449) B1166449
theorem B1456961 : Blo 968591 1456961 := bstep (se 2 (by rfl) ⟨546360, by rfl⟩ : syracuseStep 1456961 = 1092721) B1092721
theorem B6208325 : Blo 968591 6208325 := bstep (se 4 (by rfl) ⟨582030, by rfl⟩ : syracuseStep 6208325 = 1164061) B1164061
theorem B1456979 : Blo 968591 1456979 := bstep (se 1 (by rfl) ⟨1092734, by rfl⟩ : syracuseStep 1456979 = 2185469) B2185469
theorem B1457009 : Blo 968591 1457009 := bstep (se 2 (by rfl) ⟨546378, by rfl⟩ : syracuseStep 1457009 = 1092757) B1092757
theorem B2767729 : Blo 968591 2767729 := bstep (se 2 (by rfl) ⟨1037898, by rfl⟩ : syracuseStep 2767729 = 2075797) B2075797
theorem B1457027 : Blo 968591 1457027 := bstep (se 1 (by rfl) ⟨1092770, by rfl⟩ : syracuseStep 1457027 = 2185541) B2185541
theorem B1457057 : Blo 968591 1457057 := bstep (se 2 (by rfl) ⟨546396, by rfl⟩ : syracuseStep 1457057 = 1092793) B1092793
theorem B2800561 : Blo 968591 2800561 := bstep (se 2 (by rfl) ⟨1050210, by rfl⟩ : syracuseStep 2800561 = 2100421) B2100421
theorem B1457075 : Blo 968591 1457075 := bstep (se 1 (by rfl) ⟨1092806, by rfl⟩ : syracuseStep 1457075 = 2185613) B2185613
theorem B1457105 : Blo 968591 1457105 := bstep (se 2 (by rfl) ⟨546414, by rfl⟩ : syracuseStep 1457105 = 1092829) B1092829
theorem B1457123 : Blo 968591 1457123 := bstep (se 1 (by rfl) ⟨1092842, by rfl⟩ : syracuseStep 1457123 = 2185685) B2185685
theorem B1457153 : Blo 968591 1457153 := bstep (se 2 (by rfl) ⟨546432, by rfl⟩ : syracuseStep 1457153 = 1092865) B1092865
theorem B1457171 : Blo 968591 1457171 := bstep (se 1 (by rfl) ⟨1092878, by rfl⟩ : syracuseStep 1457171 = 2185757) B2185757
theorem B1457201 : Blo 968591 1457201 := bstep (se 2 (by rfl) ⟨546450, by rfl⟩ : syracuseStep 1457201 = 1092901) B1092901
theorem B1457219 : Blo 968591 1457219 := bstep (se 1 (by rfl) ⟨1092914, by rfl⟩ : syracuseStep 1457219 = 2185829) B2185829
theorem B1457249 : Blo 968591 1457249 := bstep (se 2 (by rfl) ⟨546468, by rfl⟩ : syracuseStep 1457249 = 1092937) B1092937
theorem B1457267 : Blo 968591 1457267 := bstep (se 1 (by rfl) ⟨1092950, by rfl⟩ : syracuseStep 1457267 = 2185901) B2185901
theorem B2768003 : Blo 968591 2768003 := bstep (se 1 (by rfl) ⟨2076002, by rfl⟩ : syracuseStep 2768003 = 4152005) B4152005
theorem B1457297 : Blo 968591 1457297 := bstep (se 2 (by rfl) ⟨546486, by rfl⟩ : syracuseStep 1457297 = 1092973) B1092973
theorem B1457315 : Blo 968591 1457315 := bstep (se 1 (by rfl) ⟨1092986, by rfl⟩ : syracuseStep 1457315 = 2185973) B2185973
theorem B1227955 : Blo 968591 1227955 := bstep (se 1 (by rfl) ⟨920966, by rfl⟩ : syracuseStep 1227955 = 1841933) B1841933
theorem B1457345 : Blo 968591 1457345 := bstep (se 2 (by rfl) ⟨546504, by rfl⟩ : syracuseStep 1457345 = 1093009) B1093009
theorem B5520581 : Blo 968591 5520581 := bstep (se 4 (by rfl) ⟨517554, by rfl⟩ : syracuseStep 5520581 = 1035109) B1035109
theorem B1457363 : Blo 968591 1457363 := bstep (se 1 (by rfl) ⟨1093022, by rfl⟩ : syracuseStep 1457363 = 2186045) B2186045
theorem B1457393 : Blo 968591 1457393 := bstep (se 2 (by rfl) ⟨546522, by rfl⟩ : syracuseStep 1457393 = 1093045) B1093045
theorem B1457411 : Blo 968591 1457411 := bstep (se 1 (by rfl) ⟨1093058, by rfl⟩ : syracuseStep 1457411 = 2186117) B2186117
theorem B1228051 : Blo 968591 1228051 := bstep (se 1 (by rfl) ⟨921038, by rfl⟩ : syracuseStep 1228051 = 1842077) B1842077
theorem B1457441 : Blo 968591 1457441 := bstep (se 2 (by rfl) ⟨546540, by rfl⟩ : syracuseStep 1457441 = 1093081) B1093081
theorem B1457459 : Blo 968591 1457459 := bstep (se 1 (by rfl) ⟨1093094, by rfl⟩ : syracuseStep 1457459 = 2186189) B2186189
theorem B2768195 : Blo 968591 2768195 := bstep (se 1 (by rfl) ⟨2076146, by rfl⟩ : syracuseStep 2768195 = 4152293) B4152293
theorem B1457489 : Blo 968591 1457489 := bstep (se 2 (by rfl) ⟨546558, by rfl⟩ : syracuseStep 1457489 = 1093117) B1093117
theorem B1457507 : Blo 968591 1457507 := bstep (se 1 (by rfl) ⟨1093130, by rfl⟩ : syracuseStep 1457507 = 2186261) B2186261
theorem B12631409 : Blo 968591 12631409 := bstep (se 2 (by rfl) ⟨4736778, by rfl⟩ : syracuseStep 12631409 = 9473557) B9473557
theorem B1457537 : Blo 968591 1457537 := bstep (se 2 (by rfl) ⟨546576, by rfl⟩ : syracuseStep 1457537 = 1093153) B1093153
theorem B1457555 : Blo 968591 1457555 := bstep (se 1 (by rfl) ⟨1093166, by rfl⟩ : syracuseStep 1457555 = 2186333) B2186333
theorem B1457585 : Blo 968591 1457585 := bstep (se 2 (by rfl) ⟨546594, by rfl⟩ : syracuseStep 1457585 = 1093189) B1093189
theorem B1457603 : Blo 968591 1457603 := bstep (se 1 (by rfl) ⟨1093202, by rfl⟩ : syracuseStep 1457603 = 2186405) B2186405
theorem B1457633 : Blo 968591 1457633 := bstep (se 2 (by rfl) ⟨546612, by rfl⟩ : syracuseStep 1457633 = 1093225) B1093225
theorem B1457651 : Blo 968591 1457651 := bstep (se 1 (by rfl) ⟨1093238, by rfl⟩ : syracuseStep 1457651 = 2186477) B2186477
theorem B1457681 : Blo 968591 1457681 := bstep (se 2 (by rfl) ⟨546630, by rfl⟩ : syracuseStep 1457681 = 1093261) B1093261
theorem B1457699 : Blo 968591 1457699 := bstep (se 1 (by rfl) ⟨1093274, by rfl⟩ : syracuseStep 1457699 = 2186549) B2186549
theorem B1457729 : Blo 968591 1457729 := bstep (se 2 (by rfl) ⟨546648, by rfl⟩ : syracuseStep 1457729 = 1093297) B1093297
theorem B1457747 : Blo 968591 1457747 := bstep (se 1 (by rfl) ⟨1093310, by rfl⟩ : syracuseStep 1457747 = 2186621) B2186621
theorem B1457777 : Blo 968591 1457777 := bstep (se 2 (by rfl) ⟨546666, by rfl⟩ : syracuseStep 1457777 = 1093333) B1093333
theorem B1457795 : Blo 968591 1457795 := bstep (se 1 (by rfl) ⟨1093346, by rfl⟩ : syracuseStep 1457795 = 2186693) B2186693
theorem B1457825 : Blo 968591 1457825 := bstep (se 2 (by rfl) ⟨546684, by rfl⟩ : syracuseStep 1457825 = 1093369) B1093369
theorem B1457843 : Blo 968591 1457843 := bstep (se 1 (by rfl) ⟨1093382, by rfl⟩ : syracuseStep 1457843 = 2186765) B2186765
theorem B1457873 : Blo 968591 1457873 := bstep (se 2 (by rfl) ⟨546702, by rfl⟩ : syracuseStep 1457873 = 1093405) B1093405
theorem B1457891 : Blo 968591 1457891 := bstep (se 1 (by rfl) ⟨1093418, by rfl⟩ : syracuseStep 1457891 = 2186837) B2186837
theorem B11058929 : Blo 968591 11058929 := bstep (se 2 (by rfl) ⟨4147098, by rfl⟩ : syracuseStep 11058929 = 8294197) B8294197
theorem B1457921 : Blo 968591 1457921 := bstep (se 2 (by rfl) ⟨546720, by rfl⟩ : syracuseStep 1457921 = 1093441) B1093441
theorem B1228547 : Blo 968591 1228547 := bstep (se 1 (by rfl) ⟨921410, by rfl⟩ : syracuseStep 1228547 = 1842821) B1842821
theorem B1457939 : Blo 968591 1457939 := bstep (se 1 (by rfl) ⟨1093454, by rfl⟩ : syracuseStep 1457939 = 2186909) B2186909
theorem B1457969 : Blo 968591 1457969 := bstep (se 2 (by rfl) ⟨546738, by rfl⟩ : syracuseStep 1457969 = 1093477) B1093477
theorem B1457987 : Blo 968591 1457987 := bstep (se 1 (by rfl) ⟨1093490, by rfl⟩ : syracuseStep 1457987 = 2186981) B2186981
theorem B1458017 : Blo 968591 1458017 := bstep (se 2 (by rfl) ⟨546756, by rfl⟩ : syracuseStep 1458017 = 1093513) B1093513
theorem B1458035 : Blo 968591 1458035 := bstep (se 1 (by rfl) ⟨1093526, by rfl⟩ : syracuseStep 1458035 = 2187053) B2187053
theorem B1458065 : Blo 968591 1458065 := bstep (se 2 (by rfl) ⟨546774, by rfl⟩ : syracuseStep 1458065 = 1093549) B1093549
theorem B1458083 : Blo 968591 1458083 := bstep (se 1 (by rfl) ⟨1093562, by rfl⟩ : syracuseStep 1458083 = 2187125) B2187125
theorem B1458113 : Blo 968591 1458113 := bstep (se 2 (by rfl) ⟨546792, by rfl⟩ : syracuseStep 1458113 = 1093585) B1093585
theorem B1458131 : Blo 968591 1458131 := bstep (se 1 (by rfl) ⟨1093598, by rfl⟩ : syracuseStep 1458131 = 2187197) B2187197
theorem B1458161 : Blo 968591 1458161 := bstep (se 2 (by rfl) ⟨546810, by rfl⟩ : syracuseStep 1458161 = 1093621) B1093621
theorem B1458179 : Blo 968591 1458179 := bstep (se 1 (by rfl) ⟨1093634, by rfl⟩ : syracuseStep 1458179 = 2187269) B2187269
theorem B1458209 : Blo 968591 1458209 := bstep (se 2 (by rfl) ⟨546828, by rfl⟩ : syracuseStep 1458209 = 1093657) B1093657
theorem B1458227 : Blo 968591 1458227 := bstep (se 1 (by rfl) ⟨1093670, by rfl⟩ : syracuseStep 1458227 = 2187341) B2187341
theorem B1458257 : Blo 968591 1458257 := bstep (se 2 (by rfl) ⟨546846, by rfl⟩ : syracuseStep 1458257 = 1093693) B1093693
theorem B1458275 : Blo 968591 1458275 := bstep (se 1 (by rfl) ⟨1093706, by rfl⟩ : syracuseStep 1458275 = 2187413) B2187413
theorem B2769005 : Blo 968591 2769005 := bstep (se 3 (by rfl) ⟨519188, by rfl⟩ : syracuseStep 2769005 = 1038377) B1038377
theorem B16564337 : Blo 968591 16564337 := bstep (se 2 (by rfl) ⟨6211626, by rfl⟩ : syracuseStep 16564337 = 12423253) B12423253
theorem B1458305 : Blo 968591 1458305 := bstep (se 2 (by rfl) ⟨546864, by rfl⟩ : syracuseStep 1458305 = 1093729) B1093729
theorem B1458323 : Blo 968591 1458323 := bstep (se 1 (by rfl) ⟨1093742, by rfl⟩ : syracuseStep 1458323 = 2187485) B2187485
theorem B6635683 : Blo 968591 6635683 := bstep (se 1 (by rfl) ⟨4976762, by rfl⟩ : syracuseStep 6635683 = 9953525) B9953525
theorem B1458353 : Blo 968591 1458353 := bstep (se 2 (by rfl) ⟨546882, by rfl⟩ : syracuseStep 1458353 = 1093765) B1093765
theorem B1556675 : Blo 968591 1556675 := bstep (se 1 (by rfl) ⟨1167506, by rfl⟩ : syracuseStep 1556675 = 2335013) B2335013
theorem B1458371 : Blo 968591 1458371 := bstep (se 1 (by rfl) ⟨1093778, by rfl⟩ : syracuseStep 1458371 = 2187557) B2187557
theorem B4145357 : Blo 968591 4145357 := bstep (se 3 (by rfl) ⟨777254, by rfl⟩ : syracuseStep 4145357 = 1554509) B1554509
theorem B1458401 : Blo 968591 1458401 := bstep (se 2 (by rfl) ⟨546900, by rfl⟩ : syracuseStep 1458401 = 1093801) B1093801
theorem B1458419 : Blo 968591 1458419 := bstep (se 1 (by rfl) ⟨1093814, by rfl⟩ : syracuseStep 1458419 = 2187629) B2187629
theorem B2179331 : Blo 968591 2179331 := bstep (se 1 (by rfl) ⟨1634498, by rfl⟩ : syracuseStep 2179331 = 3268997) B3268997
theorem B1458449 : Blo 968591 1458449 := bstep (se 2 (by rfl) ⟨546918, by rfl⟩ : syracuseStep 1458449 = 1093837) B1093837
theorem B1458467 : Blo 968591 1458467 := bstep (se 1 (by rfl) ⟨1093850, by rfl⟩ : syracuseStep 1458467 = 2187701) B2187701
theorem B2769187 : Blo 968591 2769187 := bstep (se 1 (by rfl) ⟨2076890, by rfl⟩ : syracuseStep 2769187 = 4153781) B4153781
theorem B3686705 : Blo 968591 3686705 := bstep (se 2 (by rfl) ⟨1382514, by rfl⟩ : syracuseStep 3686705 = 2765029) B2765029
theorem B1458497 : Blo 968591 1458497 := bstep (se 2 (by rfl) ⟨546936, by rfl⟩ : syracuseStep 1458497 = 1093873) B1093873
theorem B1458515 : Blo 968591 1458515 := bstep (se 1 (by rfl) ⟨1093886, by rfl⟩ : syracuseStep 1458515 = 2187773) B2187773
theorem B1458545 : Blo 968591 1458545 := bstep (se 2 (by rfl) ⟨546954, by rfl⟩ : syracuseStep 1458545 = 1093909) B1093909
theorem B1556867 : Blo 968591 1556867 := bstep (se 1 (by rfl) ⟨1167650, by rfl⟩ : syracuseStep 1556867 = 2335301) B2335301
theorem B1458563 : Blo 968591 1458563 := bstep (se 1 (by rfl) ⟨1093922, by rfl⟩ : syracuseStep 1458563 = 2187845) B2187845
theorem B1458593 : Blo 968591 1458593 := bstep (se 2 (by rfl) ⟨546972, by rfl⟩ : syracuseStep 1458593 = 1093945) B1093945
theorem B1458611 : Blo 968591 1458611 := bstep (se 1 (by rfl) ⟨1093958, by rfl⟩ : syracuseStep 1458611 = 2187917) B2187917
theorem B1229251 : Blo 968591 1229251 := bstep (se 1 (by rfl) ⟨921938, by rfl⟩ : syracuseStep 1229251 = 1843877) B1843877
theorem B1458641 : Blo 968591 1458641 := bstep (se 2 (by rfl) ⟨546990, by rfl⟩ : syracuseStep 1458641 = 1093981) B1093981
theorem B1327585 : Blo 968591 1327585 := bstep (se 2 (by rfl) ⟨497844, by rfl⟩ : syracuseStep 1327585 = 995689) B995689
theorem B1458659 : Blo 968591 1458659 := bstep (se 1 (by rfl) ⟨1093994, by rfl⟩ : syracuseStep 1458659 = 2187989) B2187989
theorem B1458689 : Blo 968591 1458689 := bstep (se 2 (by rfl) ⟨547008, by rfl⟩ : syracuseStep 1458689 = 1094017) B1094017
theorem B2179601 : Blo 968591 2179601 := bstep (se 2 (by rfl) ⟨817350, by rfl⟩ : syracuseStep 2179601 = 1634701) B1634701
theorem B1458707 : Blo 968591 1458707 := bstep (se 1 (by rfl) ⟨1094030, by rfl⟩ : syracuseStep 1458707 = 2188061) B2188061
theorem B2179619 : Blo 968591 2179619 := bstep (se 1 (by rfl) ⟨1634714, by rfl⟩ : syracuseStep 2179619 = 3269429) B3269429
theorem B1229347 : Blo 968591 1229347 := bstep (se 1 (by rfl) ⟨922010, by rfl⟩ : syracuseStep 1229347 = 1844021) B1844021
theorem B1458737 : Blo 968591 1458737 := bstep (se 2 (by rfl) ⟨547026, by rfl⟩ : syracuseStep 1458737 = 1094053) B1094053
theorem B1458755 : Blo 968591 1458755 := bstep (se 1 (by rfl) ⟨1094066, by rfl⟩ : syracuseStep 1458755 = 2188133) B2188133
theorem B1458785 : Blo 968591 1458785 := bstep (se 2 (by rfl) ⟨547044, by rfl⟩ : syracuseStep 1458785 = 1094089) B1094089
theorem B1458803 : Blo 968591 1458803 := bstep (se 1 (by rfl) ⟨1094102, by rfl⟩ : syracuseStep 1458803 = 2188205) B2188205
theorem B1458833 : Blo 968591 1458833 := bstep (se 2 (by rfl) ⟨547062, by rfl⟩ : syracuseStep 1458833 = 1094125) B1094125
theorem B1458851 : Blo 968591 1458851 := bstep (se 1 (by rfl) ⟨1094138, by rfl⟩ : syracuseStep 1458851 = 2188277) B2188277
theorem B1458881 : Blo 968591 1458881 := bstep (se 2 (by rfl) ⟨547080, by rfl⟩ : syracuseStep 1458881 = 1094161) B1094161
theorem B2179889 : Blo 968591 2179889 := bstep (se 2 (by rfl) ⟨817458, by rfl⟩ : syracuseStep 2179889 = 1634917) B1634917
theorem B2179907 : Blo 968591 2179907 := bstep (se 1 (by rfl) ⟨1634930, by rfl⟩ : syracuseStep 2179907 = 3269861) B3269861
theorem B9323363 : Blo 968591 9323363 := bstep (se 1 (by rfl) ⟨6992522, by rfl⟩ : syracuseStep 9323363 = 13985045) B13985045
theorem B13288333 : Blo 968591 13288333 := bstep (se 3 (by rfl) ⟨2491562, by rfl⟩ : syracuseStep 13288333 = 4983125) B4983125
theorem B1229843 : Blo 968591 1229843 := bstep (se 1 (by rfl) ⟨922382, by rfl⟩ : syracuseStep 1229843 = 1844765) B1844765
theorem B6636613 : Blo 968591 6636613 := bstep (se 4 (by rfl) ⟨622182, by rfl⟩ : syracuseStep 6636613 = 1244365) B1244365
theorem B2180177 : Blo 968591 2180177 := bstep (se 2 (by rfl) ⟨817566, by rfl⟩ : syracuseStep 2180177 = 1635133) B1635133
theorem B1262675 : Blo 968591 1262675 := bstep (se 1 (by rfl) ⟨947006, by rfl⟩ : syracuseStep 1262675 = 1894013) B1894013
theorem B2180195 : Blo 968591 2180195 := bstep (se 1 (by rfl) ⟨1635146, by rfl⟩ : syracuseStep 2180195 = 3270293) B3270293
theorem B7357553 : Blo 968591 7357553 := bstep (se 2 (by rfl) ⟨2759082, by rfl⟩ : syracuseStep 7357553 = 5518165) B5518165
theorem B2245745 : Blo 968591 2245745 := bstep (se 2 (by rfl) ⟨842154, by rfl⟩ : syracuseStep 2245745 = 1684309) B1684309
theorem B2180465 : Blo 968591 2180465 := bstep (se 2 (by rfl) ⟨817674, by rfl⟩ : syracuseStep 2180465 = 1635349) B1635349
theorem B2180483 : Blo 968591 2180483 := bstep (se 1 (by rfl) ⟨1635362, by rfl⟩ : syracuseStep 2180483 = 3270725) B3270725
theorem B4146673 : Blo 968591 4146673 := bstep (se 2 (by rfl) ⟨1555002, by rfl⟩ : syracuseStep 4146673 = 3110005) B3110005
theorem B1164883 : Blo 968591 1164883 := bstep (se 1 (by rfl) ⟨873662, by rfl⟩ : syracuseStep 1164883 = 1747325) B1747325
theorem B2180753 : Blo 968591 2180753 := bstep (se 2 (by rfl) ⟨817782, by rfl⟩ : syracuseStep 2180753 = 1635565) B1635565
theorem B2180771 : Blo 968591 2180771 := bstep (se 1 (by rfl) ⟨1635578, by rfl⟩ : syracuseStep 2180771 = 3271157) B3271157
theorem B1754833 : Blo 968591 1754833 := bstep (se 2 (by rfl) ⟨658062, by rfl⟩ : syracuseStep 1754833 = 1316125) B1316125
theorem B1230547 : Blo 968591 1230547 := bstep (se 1 (by rfl) ⟨922910, by rfl⟩ : syracuseStep 1230547 = 1845821) B1845821
theorem B3688163 : Blo 968591 3688163 := bstep (se 1 (by rfl) ⟨2766122, by rfl⟩ : syracuseStep 3688163 = 5532245) B5532245
theorem B1230643 : Blo 968591 1230643 := bstep (se 1 (by rfl) ⟨922982, by rfl⟩ : syracuseStep 1230643 = 1845965) B1845965
theorem B968595 : Blo 968591 968595 := bstep (se 1 (by rfl) ⟨726446, by rfl⟩ : syracuseStep 968595 = 1452893) B1452893
theorem B968611 : Blo 968591 968611 := bstep (se 1 (by rfl) ⟨726458, by rfl⟩ : syracuseStep 968611 = 1452917) B1452917
theorem B2181041 : Blo 968591 2181041 := bstep (se 2 (by rfl) ⟨817890, by rfl⟩ : syracuseStep 2181041 = 1635781) B1635781
theorem B968627 : Blo 968591 968627 := bstep (se 1 (by rfl) ⟨726470, by rfl⟩ : syracuseStep 968627 = 1452941) B1452941
theorem B968643 : Blo 968591 968643 := bstep (se 1 (by rfl) ⟨726482, by rfl⟩ : syracuseStep 968643 = 1452965) B1452965
theorem B2181059 : Blo 968591 2181059 := bstep (se 1 (by rfl) ⟨1635794, by rfl⟩ : syracuseStep 2181059 = 3271589) B3271589
theorem B6211525 : Blo 968591 6211525 := bstep (se 4 (by rfl) ⟨582330, by rfl⟩ : syracuseStep 6211525 = 1164661) B1164661
theorem B968659 : Blo 968591 968659 := bstep (se 1 (by rfl) ⟨726494, by rfl⟩ : syracuseStep 968659 = 1452989) B1452989
theorem B1165267 : Blo 968591 1165267 := bstep (se 1 (by rfl) ⟨873950, by rfl⟩ : syracuseStep 1165267 = 1747901) B1747901
theorem B968675 : Blo 968591 968675 := bstep (se 1 (by rfl) ⟨726506, by rfl⟩ : syracuseStep 968675 = 1453013) B1453013
theorem B968691 : Blo 968591 968691 := bstep (se 1 (by rfl) ⟨726518, by rfl⟩ : syracuseStep 968691 = 1453037) B1453037
theorem B968707 : Blo 968591 968707 := bstep (se 1 (by rfl) ⟨726530, by rfl⟩ : syracuseStep 968707 = 1453061) B1453061
theorem B968723 : Blo 968591 968723 := bstep (se 1 (by rfl) ⟨726542, by rfl⟩ : syracuseStep 968723 = 1453085) B1453085
theorem B968739 : Blo 968591 968739 := bstep (se 1 (by rfl) ⟨726554, by rfl⟩ : syracuseStep 968739 = 1453109) B1453109
theorem B4671523 : Blo 968591 4671523 := bstep (se 1 (by rfl) ⟨3503642, by rfl⟩ : syracuseStep 4671523 = 7007285) B7007285
theorem B968755 : Blo 968591 968755 := bstep (se 1 (by rfl) ⟨726566, by rfl⟩ : syracuseStep 968755 = 1453133) B1453133
theorem B968771 : Blo 968591 968771 := bstep (se 1 (by rfl) ⟨726578, by rfl⟩ : syracuseStep 968771 = 1453157) B1453157
theorem B968787 : Blo 968591 968787 := bstep (se 1 (by rfl) ⟨726590, by rfl⟩ : syracuseStep 968787 = 1453181) B1453181
theorem B968803 : Blo 968591 968803 := bstep (se 1 (by rfl) ⟨726602, by rfl⟩ : syracuseStep 968803 = 1453205) B1453205
theorem B968819 : Blo 968591 968819 := bstep (se 1 (by rfl) ⟨726614, by rfl⟩ : syracuseStep 968819 = 1453229) B1453229
theorem B968835 : Blo 968591 968835 := bstep (se 1 (by rfl) ⟨726626, by rfl⟩ : syracuseStep 968835 = 1453253) B1453253
theorem B968851 : Blo 968591 968851 := bstep (se 1 (by rfl) ⟨726638, by rfl⟩ : syracuseStep 968851 = 1453277) B1453277
theorem B968867 : Blo 968591 968867 := bstep (se 1 (by rfl) ⟨726650, by rfl⟩ : syracuseStep 968867 = 1453301) B1453301
theorem B968883 : Blo 968591 968883 := bstep (se 1 (by rfl) ⟨726662, by rfl⟩ : syracuseStep 968883 = 1453325) B1453325
theorem B968899 : Blo 968591 968899 := bstep (se 1 (by rfl) ⟨726674, by rfl⟩ : syracuseStep 968899 = 1453349) B1453349
theorem B2181329 : Blo 968591 2181329 := bstep (se 2 (by rfl) ⟨817998, by rfl⟩ : syracuseStep 2181329 = 1635997) B1635997
theorem B968915 : Blo 968591 968915 := bstep (se 1 (by rfl) ⟨726686, by rfl⟩ : syracuseStep 968915 = 1453373) B1453373
theorem B968931 : Blo 968591 968931 := bstep (se 1 (by rfl) ⟨726698, by rfl⟩ : syracuseStep 968931 = 1453397) B1453397
theorem B2181347 : Blo 968591 2181347 := bstep (se 1 (by rfl) ⟨1636010, by rfl⟩ : syracuseStep 2181347 = 3272021) B3272021
theorem B968947 : Blo 968591 968947 := bstep (se 1 (by rfl) ⟨726710, by rfl⟩ : syracuseStep 968947 = 1453421) B1453421
theorem B968963 : Blo 968591 968963 := bstep (se 1 (by rfl) ⟨726722, by rfl⟩ : syracuseStep 968963 = 1453445) B1453445
theorem B968979 : Blo 968591 968979 := bstep (se 1 (by rfl) ⟨726734, by rfl⟩ : syracuseStep 968979 = 1453469) B1453469
theorem B968995 : Blo 968591 968995 := bstep (se 1 (by rfl) ⟨726746, by rfl⟩ : syracuseStep 968995 = 1453493) B1453493
theorem B969011 : Blo 968591 969011 := bstep (se 1 (by rfl) ⟨726758, by rfl⟩ : syracuseStep 969011 = 1453517) B1453517
theorem B969027 : Blo 968591 969027 := bstep (se 1 (by rfl) ⟨726770, by rfl⟩ : syracuseStep 969027 = 1453541) B1453541
theorem B969043 : Blo 968591 969043 := bstep (se 1 (by rfl) ⟨726782, by rfl⟩ : syracuseStep 969043 = 1453565) B1453565
theorem B969059 : Blo 968591 969059 := bstep (se 1 (by rfl) ⟨726794, by rfl⟩ : syracuseStep 969059 = 1453589) B1453589
theorem B969075 : Blo 968591 969075 := bstep (se 1 (by rfl) ⟨726806, by rfl⟩ : syracuseStep 969075 = 1453613) B1453613
theorem B969091 : Blo 968591 969091 := bstep (se 1 (by rfl) ⟨726818, by rfl⟩ : syracuseStep 969091 = 1453637) B1453637
theorem B969107 : Blo 968591 969107 := bstep (se 1 (by rfl) ⟨726830, by rfl⟩ : syracuseStep 969107 = 1453661) B1453661
theorem B969123 : Blo 968591 969123 := bstep (se 1 (by rfl) ⟨726842, by rfl⟩ : syracuseStep 969123 = 1453685) B1453685
theorem B969139 : Blo 968591 969139 := bstep (se 1 (by rfl) ⟨726854, by rfl⟩ : syracuseStep 969139 = 1453709) B1453709
theorem B969155 : Blo 968591 969155 := bstep (se 1 (by rfl) ⟨726866, by rfl⟩ : syracuseStep 969155 = 1453733) B1453733
theorem B969171 : Blo 968591 969171 := bstep (se 1 (by rfl) ⟨726878, by rfl⟩ : syracuseStep 969171 = 1453757) B1453757
theorem B969187 : Blo 968591 969187 := bstep (se 1 (by rfl) ⟨726890, by rfl⟩ : syracuseStep 969187 = 1453781) B1453781
theorem B1165795 : Blo 968591 1165795 := bstep (se 1 (by rfl) ⟨874346, by rfl⟩ : syracuseStep 1165795 = 1748693) B1748693
theorem B2181617 : Blo 968591 2181617 := bstep (se 2 (by rfl) ⟨818106, by rfl⟩ : syracuseStep 2181617 = 1636213) B1636213
theorem B969203 : Blo 968591 969203 := bstep (se 1 (by rfl) ⟨726902, by rfl⟩ : syracuseStep 969203 = 1453805) B1453805
theorem B969219 : Blo 968591 969219 := bstep (se 1 (by rfl) ⟨726914, by rfl⟩ : syracuseStep 969219 = 1453829) B1453829
theorem B2181635 : Blo 968591 2181635 := bstep (se 1 (by rfl) ⟨1636226, by rfl⟩ : syracuseStep 2181635 = 3272453) B3272453
theorem B969235 : Blo 968591 969235 := bstep (se 1 (by rfl) ⟨726926, by rfl⟩ : syracuseStep 969235 = 1453853) B1453853
theorem B969251 : Blo 968591 969251 := bstep (se 1 (by rfl) ⟨726938, by rfl⟩ : syracuseStep 969251 = 1453877) B1453877
theorem B969267 : Blo 968591 969267 := bstep (se 1 (by rfl) ⟨726950, by rfl⟩ : syracuseStep 969267 = 1453901) B1453901
theorem B969283 : Blo 968591 969283 := bstep (se 1 (by rfl) ⟨726962, by rfl⟩ : syracuseStep 969283 = 1453925) B1453925
theorem B969299 : Blo 968591 969299 := bstep (se 1 (by rfl) ⟨726974, by rfl⟩ : syracuseStep 969299 = 1453949) B1453949
theorem B969315 : Blo 968591 969315 := bstep (se 1 (by rfl) ⟨726986, by rfl⟩ : syracuseStep 969315 = 1453973) B1453973
theorem B969331 : Blo 968591 969331 := bstep (se 1 (by rfl) ⟨726998, by rfl⟩ : syracuseStep 969331 = 1453997) B1453997
theorem B969347 : Blo 968591 969347 := bstep (se 1 (by rfl) ⟨727010, by rfl⟩ : syracuseStep 969347 = 1454021) B1454021
theorem B969363 : Blo 968591 969363 := bstep (se 1 (by rfl) ⟨727022, by rfl⟩ : syracuseStep 969363 = 1454045) B1454045
theorem B969379 : Blo 968591 969379 := bstep (se 1 (by rfl) ⟨727034, by rfl⟩ : syracuseStep 969379 = 1454069) B1454069
theorem B2214577 : Blo 968591 2214577 := bstep (se 2 (by rfl) ⟨830466, by rfl⟩ : syracuseStep 2214577 = 1660933) B1660933
theorem B969395 : Blo 968591 969395 := bstep (se 1 (by rfl) ⟨727046, by rfl⟩ : syracuseStep 969395 = 1454093) B1454093
theorem B1034947 : Blo 968591 1034947 := bstep (se 1 (by rfl) ⟨776210, by rfl⟩ : syracuseStep 1034947 = 1552421) B1552421
theorem B969411 : Blo 968591 969411 := bstep (se 1 (by rfl) ⟨727058, by rfl⟩ : syracuseStep 969411 = 1454117) B1454117
theorem B3689165 : Blo 968591 3689165 := bstep (se 3 (by rfl) ⟨691718, by rfl⟩ : syracuseStep 3689165 = 1383437) B1383437
theorem B969427 : Blo 968591 969427 := bstep (se 1 (by rfl) ⟨727070, by rfl⟩ : syracuseStep 969427 = 1454141) B1454141
theorem B969443 : Blo 968591 969443 := bstep (se 1 (by rfl) ⟨727082, by rfl⟩ : syracuseStep 969443 = 1454165) B1454165
theorem B969459 : Blo 968591 969459 := bstep (se 1 (by rfl) ⟨727094, by rfl⟩ : syracuseStep 969459 = 1454189) B1454189
theorem B969475 : Blo 968591 969475 := bstep (se 1 (by rfl) ⟨727106, by rfl⟩ : syracuseStep 969475 = 1454213) B1454213
theorem B2181905 : Blo 968591 2181905 := bstep (se 2 (by rfl) ⟨818214, by rfl⟩ : syracuseStep 2181905 = 1636429) B1636429
theorem B969491 : Blo 968591 969491 := bstep (se 1 (by rfl) ⟨727118, by rfl⟩ : syracuseStep 969491 = 1454237) B1454237
theorem B969507 : Blo 968591 969507 := bstep (se 1 (by rfl) ⟨727130, by rfl⟩ : syracuseStep 969507 = 1454261) B1454261
theorem B2181923 : Blo 968591 2181923 := bstep (se 1 (by rfl) ⟨1636442, by rfl⟩ : syracuseStep 2181923 = 3272885) B3272885
theorem B969523 : Blo 968591 969523 := bstep (se 1 (by rfl) ⟨727142, by rfl⟩ : syracuseStep 969523 = 1454285) B1454285
theorem B969539 : Blo 968591 969539 := bstep (se 1 (by rfl) ⟨727154, by rfl⟩ : syracuseStep 969539 = 1454309) B1454309
theorem B969555 : Blo 968591 969555 := bstep (se 1 (by rfl) ⟨727166, by rfl⟩ : syracuseStep 969555 = 1454333) B1454333
theorem B969571 : Blo 968591 969571 := bstep (se 1 (by rfl) ⟨727178, by rfl⟩ : syracuseStep 969571 = 1454357) B1454357
theorem B969587 : Blo 968591 969587 := bstep (se 1 (by rfl) ⟨727190, by rfl⟩ : syracuseStep 969587 = 1454381) B1454381
theorem B969603 : Blo 968591 969603 := bstep (se 1 (by rfl) ⟨727202, by rfl⟩ : syracuseStep 969603 = 1454405) B1454405
theorem B969619 : Blo 968591 969619 := bstep (se 1 (by rfl) ⟨727214, by rfl⟩ : syracuseStep 969619 = 1454429) B1454429
theorem B969635 : Blo 968591 969635 := bstep (se 1 (by rfl) ⟨727226, by rfl⟩ : syracuseStep 969635 = 1454453) B1454453
theorem B969651 : Blo 968591 969651 := bstep (se 1 (by rfl) ⟨727238, by rfl⟩ : syracuseStep 969651 = 1454477) B1454477
theorem B969667 : Blo 968591 969667 := bstep (se 1 (by rfl) ⟨727250, by rfl⟩ : syracuseStep 969667 = 1454501) B1454501
theorem B969683 : Blo 968591 969683 := bstep (se 1 (by rfl) ⟨727262, by rfl⟩ : syracuseStep 969683 = 1454525) B1454525
theorem B969699 : Blo 968591 969699 := bstep (se 1 (by rfl) ⟨727274, by rfl⟩ : syracuseStep 969699 = 1454549) B1454549
theorem B969715 : Blo 968591 969715 := bstep (se 1 (by rfl) ⟨727286, by rfl⟩ : syracuseStep 969715 = 1454573) B1454573
theorem B969731 : Blo 968591 969731 := bstep (se 1 (by rfl) ⟨727298, by rfl⟩ : syracuseStep 969731 = 1454597) B1454597
theorem B969747 : Blo 968591 969747 := bstep (se 1 (by rfl) ⟨727310, by rfl⟩ : syracuseStep 969747 = 1454621) B1454621
theorem B969763 : Blo 968591 969763 := bstep (se 1 (by rfl) ⟨727322, by rfl⟩ : syracuseStep 969763 = 1454645) B1454645
theorem B2182193 : Blo 968591 2182193 := bstep (se 2 (by rfl) ⟨818322, by rfl⟩ : syracuseStep 2182193 = 1636645) B1636645
theorem B969779 : Blo 968591 969779 := bstep (se 1 (by rfl) ⟨727334, by rfl⟩ : syracuseStep 969779 = 1454669) B1454669
theorem B969795 : Blo 968591 969795 := bstep (se 1 (by rfl) ⟨727346, by rfl⟩ : syracuseStep 969795 = 1454693) B1454693
theorem B2182211 : Blo 968591 2182211 := bstep (se 1 (by rfl) ⟨1636658, by rfl⟩ : syracuseStep 2182211 = 3273317) B3273317
theorem B969811 : Blo 968591 969811 := bstep (se 1 (by rfl) ⟨727358, by rfl⟩ : syracuseStep 969811 = 1454717) B1454717
theorem B969827 : Blo 968591 969827 := bstep (se 1 (by rfl) ⟨727370, by rfl⟩ : syracuseStep 969827 = 1454741) B1454741
theorem B969843 : Blo 968591 969843 := bstep (se 1 (by rfl) ⟨727382, by rfl⟩ : syracuseStep 969843 = 1454765) B1454765
theorem B969859 : Blo 968591 969859 := bstep (se 1 (by rfl) ⟨727394, by rfl⟩ : syracuseStep 969859 = 1454789) B1454789
theorem B969875 : Blo 968591 969875 := bstep (se 1 (by rfl) ⟨727406, by rfl⟩ : syracuseStep 969875 = 1454813) B1454813
theorem B969891 : Blo 968591 969891 := bstep (se 1 (by rfl) ⟨727418, by rfl⟩ : syracuseStep 969891 = 1454837) B1454837
theorem B969907 : Blo 968591 969907 := bstep (se 1 (by rfl) ⟨727430, by rfl⟩ : syracuseStep 969907 = 1454861) B1454861
theorem B969923 : Blo 968591 969923 := bstep (se 1 (by rfl) ⟨727442, by rfl⟩ : syracuseStep 969923 = 1454885) B1454885
theorem B969939 : Blo 968591 969939 := bstep (se 1 (by rfl) ⟨727454, by rfl⟩ : syracuseStep 969939 = 1454909) B1454909
theorem B969955 : Blo 968591 969955 := bstep (se 1 (by rfl) ⟨727466, by rfl⟩ : syracuseStep 969955 = 1454933) B1454933
theorem B969971 : Blo 968591 969971 := bstep (se 1 (by rfl) ⟨727478, by rfl⟩ : syracuseStep 969971 = 1454957) B1454957
theorem B969987 : Blo 968591 969987 := bstep (se 1 (by rfl) ⟨727490, by rfl⟩ : syracuseStep 969987 = 1454981) B1454981
theorem B970003 : Blo 968591 970003 := bstep (se 1 (by rfl) ⟨727502, by rfl⟩ : syracuseStep 970003 = 1455005) B1455005
theorem B970019 : Blo 968591 970019 := bstep (se 1 (by rfl) ⟨727514, by rfl⟩ : syracuseStep 970019 = 1455029) B1455029
theorem B970035 : Blo 968591 970035 := bstep (se 1 (by rfl) ⟨727526, by rfl⟩ : syracuseStep 970035 = 1455053) B1455053
theorem B970051 : Blo 968591 970051 := bstep (se 1 (by rfl) ⟨727538, by rfl⟩ : syracuseStep 970051 = 1455077) B1455077
theorem B2182481 : Blo 968591 2182481 := bstep (se 2 (by rfl) ⟨818430, by rfl⟩ : syracuseStep 2182481 = 1636861) B1636861
theorem B970067 : Blo 968591 970067 := bstep (se 1 (by rfl) ⟨727550, by rfl⟩ : syracuseStep 970067 = 1455101) B1455101
theorem B2182499 : Blo 968591 2182499 := bstep (se 1 (by rfl) ⟨1636874, by rfl⟩ : syracuseStep 2182499 = 3273749) B3273749
theorem B970083 : Blo 968591 970083 := bstep (se 1 (by rfl) ⟨727562, by rfl⟩ : syracuseStep 970083 = 1455125) B1455125
theorem B1658225 : Blo 968591 1658225 := bstep (se 2 (by rfl) ⟨621834, by rfl⟩ : syracuseStep 1658225 = 1243669) B1243669
theorem B970099 : Blo 968591 970099 := bstep (se 1 (by rfl) ⟨727574, by rfl⟩ : syracuseStep 970099 = 1455149) B1455149
theorem B970115 : Blo 968591 970115 := bstep (se 1 (by rfl) ⟨727586, by rfl⟩ : syracuseStep 970115 = 1455173) B1455173
theorem B970131 : Blo 968591 970131 := bstep (se 1 (by rfl) ⟨727598, by rfl⟩ : syracuseStep 970131 = 1455197) B1455197
theorem B970147 : Blo 968591 970147 := bstep (se 1 (by rfl) ⟨727610, by rfl⟩ : syracuseStep 970147 = 1455221) B1455221
theorem B970163 : Blo 968591 970163 := bstep (se 1 (by rfl) ⟨727622, by rfl⟩ : syracuseStep 970163 = 1455245) B1455245
theorem B970179 : Blo 968591 970179 := bstep (se 1 (by rfl) ⟨727634, by rfl⟩ : syracuseStep 970179 = 1455269) B1455269
theorem B970195 : Blo 968591 970195 := bstep (se 1 (by rfl) ⟨727646, by rfl⟩ : syracuseStep 970195 = 1455293) B1455293
theorem B970211 : Blo 968591 970211 := bstep (se 1 (by rfl) ⟨727658, by rfl⟩ : syracuseStep 970211 = 1455317) B1455317
theorem B970227 : Blo 968591 970227 := bstep (se 1 (by rfl) ⟨727670, by rfl⟩ : syracuseStep 970227 = 1455341) B1455341
theorem B970243 : Blo 968591 970243 := bstep (se 1 (by rfl) ⟨727682, by rfl⟩ : syracuseStep 970243 = 1455365) B1455365
theorem B1822211 : Blo 968591 1822211 := bstep (se 1 (by rfl) ⟨1366658, by rfl⟩ : syracuseStep 1822211 = 2733317) B2733317
theorem B970259 : Blo 968591 970259 := bstep (se 1 (by rfl) ⟨727694, by rfl⟩ : syracuseStep 970259 = 1455389) B1455389
theorem B970275 : Blo 968591 970275 := bstep (se 1 (by rfl) ⟨727706, by rfl⟩ : syracuseStep 970275 = 1455413) B1455413
theorem B970291 : Blo 968591 970291 := bstep (se 1 (by rfl) ⟨727718, by rfl⟩ : syracuseStep 970291 = 1455437) B1455437
theorem B970307 : Blo 968591 970307 := bstep (se 1 (by rfl) ⟨727730, by rfl⟩ : syracuseStep 970307 = 1455461) B1455461
theorem B970323 : Blo 968591 970323 := bstep (se 1 (by rfl) ⟨727742, by rfl⟩ : syracuseStep 970323 = 1455485) B1455485
theorem B970339 : Blo 968591 970339 := bstep (se 1 (by rfl) ⟨727754, by rfl⟩ : syracuseStep 970339 = 1455509) B1455509
theorem B2182769 : Blo 968591 2182769 := bstep (se 2 (by rfl) ⟨818538, by rfl⟩ : syracuseStep 2182769 = 1637077) B1637077
theorem B970355 : Blo 968591 970355 := bstep (se 1 (by rfl) ⟨727766, by rfl⟩ : syracuseStep 970355 = 1455533) B1455533
theorem B2182787 : Blo 968591 2182787 := bstep (se 1 (by rfl) ⟨1637090, by rfl⟩ : syracuseStep 2182787 = 3274181) B3274181
theorem B970371 : Blo 968591 970371 := bstep (se 1 (by rfl) ⟨727778, by rfl⟩ : syracuseStep 970371 = 1455557) B1455557
theorem B970387 : Blo 968591 970387 := bstep (se 1 (by rfl) ⟨727790, by rfl⟩ : syracuseStep 970387 = 1455581) B1455581
theorem B970403 : Blo 968591 970403 := bstep (se 1 (by rfl) ⟨727802, by rfl⟩ : syracuseStep 970403 = 1455605) B1455605
theorem B970419 : Blo 968591 970419 := bstep (se 1 (by rfl) ⟨727814, by rfl⟩ : syracuseStep 970419 = 1455629) B1455629
theorem B970435 : Blo 968591 970435 := bstep (se 1 (by rfl) ⟨727826, by rfl⟩ : syracuseStep 970435 = 1455653) B1455653
theorem B970451 : Blo 968591 970451 := bstep (se 1 (by rfl) ⟨727838, by rfl⟩ : syracuseStep 970451 = 1455677) B1455677
theorem B970467 : Blo 968591 970467 := bstep (se 1 (by rfl) ⟨727850, by rfl⟩ : syracuseStep 970467 = 1455701) B1455701
theorem B970483 : Blo 968591 970483 := bstep (se 1 (by rfl) ⟨727862, by rfl⟩ : syracuseStep 970483 = 1455725) B1455725
theorem B970499 : Blo 968591 970499 := bstep (se 1 (by rfl) ⟨727874, by rfl⟩ : syracuseStep 970499 = 1455749) B1455749
theorem B970515 : Blo 968591 970515 := bstep (se 1 (by rfl) ⟨727886, by rfl⟩ : syracuseStep 970515 = 1455773) B1455773
theorem B970531 : Blo 968591 970531 := bstep (se 1 (by rfl) ⟨727898, by rfl⟩ : syracuseStep 970531 = 1455797) B1455797
theorem B970547 : Blo 968591 970547 := bstep (se 1 (by rfl) ⟨727910, by rfl⟩ : syracuseStep 970547 = 1455821) B1455821
theorem B970563 : Blo 968591 970563 := bstep (se 1 (by rfl) ⟨727922, by rfl⟩ : syracuseStep 970563 = 1455845) B1455845
theorem B970579 : Blo 968591 970579 := bstep (se 1 (by rfl) ⟨727934, by rfl⟩ : syracuseStep 970579 = 1455869) B1455869
theorem B970595 : Blo 968591 970595 := bstep (se 1 (by rfl) ⟨727946, by rfl⟩ : syracuseStep 970595 = 1455893) B1455893
theorem B970611 : Blo 968591 970611 := bstep (se 1 (by rfl) ⟨727958, by rfl⟩ : syracuseStep 970611 = 1455917) B1455917
theorem B970627 : Blo 968591 970627 := bstep (se 1 (by rfl) ⟨727970, by rfl⟩ : syracuseStep 970627 = 1455941) B1455941
theorem B50417549 : Blo 968591 50417549 := bstep (se 3 (by rfl) ⟨9453290, by rfl⟩ : syracuseStep 50417549 = 18906581) B18906581
theorem B2183057 : Blo 968591 2183057 := bstep (se 2 (by rfl) ⟨818646, by rfl⟩ : syracuseStep 2183057 = 1637293) B1637293
theorem B970643 : Blo 968591 970643 := bstep (se 1 (by rfl) ⟨727982, by rfl⟩ : syracuseStep 970643 = 1455965) B1455965
theorem B2183075 : Blo 968591 2183075 := bstep (se 1 (by rfl) ⟨1637306, by rfl⟩ : syracuseStep 2183075 = 3274613) B3274613
theorem B970659 : Blo 968591 970659 := bstep (se 1 (by rfl) ⟨727994, by rfl⟩ : syracuseStep 970659 = 1455989) B1455989
theorem B1036211 : Blo 968591 1036211 := bstep (se 1 (by rfl) ⟨777158, by rfl⟩ : syracuseStep 1036211 = 1554317) B1554317
theorem B970675 : Blo 968591 970675 := bstep (se 1 (by rfl) ⟨728006, by rfl⟩ : syracuseStep 970675 = 1456013) B1456013
theorem B970691 : Blo 968591 970691 := bstep (se 1 (by rfl) ⟨728018, by rfl⟩ : syracuseStep 970691 = 1456037) B1456037
theorem B970707 : Blo 968591 970707 := bstep (se 1 (by rfl) ⟨728030, by rfl⟩ : syracuseStep 970707 = 1456061) B1456061
theorem B970723 : Blo 968591 970723 := bstep (se 1 (by rfl) ⟨728042, by rfl⟩ : syracuseStep 970723 = 1456085) B1456085
theorem B970739 : Blo 968591 970739 := bstep (se 1 (by rfl) ⟨728054, by rfl⟩ : syracuseStep 970739 = 1456109) B1456109
theorem B970755 : Blo 968591 970755 := bstep (se 1 (by rfl) ⟨728066, by rfl⟩ : syracuseStep 970755 = 1456133) B1456133
theorem B970771 : Blo 968591 970771 := bstep (se 1 (by rfl) ⟨728078, by rfl⟩ : syracuseStep 970771 = 1456157) B1456157
theorem B970787 : Blo 968591 970787 := bstep (se 1 (by rfl) ⟨728090, by rfl⟩ : syracuseStep 970787 = 1456181) B1456181
theorem B970803 : Blo 968591 970803 := bstep (se 1 (by rfl) ⟨728102, by rfl⟩ : syracuseStep 970803 = 1456205) B1456205
theorem B970819 : Blo 968591 970819 := bstep (se 1 (by rfl) ⟨728114, by rfl⟩ : syracuseStep 970819 = 1456229) B1456229
theorem B970835 : Blo 968591 970835 := bstep (se 1 (by rfl) ⟨728126, by rfl⟩ : syracuseStep 970835 = 1456253) B1456253
theorem B970851 : Blo 968591 970851 := bstep (se 1 (by rfl) ⟨728138, by rfl⟩ : syracuseStep 970851 = 1456277) B1456277
theorem B970867 : Blo 968591 970867 := bstep (se 1 (by rfl) ⟨728150, by rfl⟩ : syracuseStep 970867 = 1456301) B1456301
theorem B970883 : Blo 968591 970883 := bstep (se 1 (by rfl) ⟨728162, by rfl⟩ : syracuseStep 970883 = 1456325) B1456325
theorem B3494029 : Blo 968591 3494029 := bstep (se 3 (by rfl) ⟨655130, by rfl⟩ : syracuseStep 3494029 = 1310261) B1310261
theorem B6312077 : Blo 968591 6312077 := bstep (se 3 (by rfl) ⟨1183514, by rfl⟩ : syracuseStep 6312077 = 2367029) B2367029
theorem B970899 : Blo 968591 970899 := bstep (se 1 (by rfl) ⟨728174, by rfl⟩ : syracuseStep 970899 = 1456349) B1456349
theorem B970915 : Blo 968591 970915 := bstep (se 1 (by rfl) ⟨728186, by rfl⟩ : syracuseStep 970915 = 1456373) B1456373
theorem B2183345 : Blo 968591 2183345 := bstep (se 2 (by rfl) ⟨818754, by rfl⟩ : syracuseStep 2183345 = 1637509) B1637509
theorem B970931 : Blo 968591 970931 := bstep (se 1 (by rfl) ⟨728198, by rfl⟩ : syracuseStep 970931 = 1456397) B1456397
theorem B2183363 : Blo 968591 2183363 := bstep (se 1 (by rfl) ⟨1637522, by rfl⟩ : syracuseStep 2183363 = 3275045) B3275045
theorem B970947 : Blo 968591 970947 := bstep (se 1 (by rfl) ⟨728210, by rfl⟩ : syracuseStep 970947 = 1456421) B1456421
theorem B970963 : Blo 968591 970963 := bstep (se 1 (by rfl) ⟨728222, by rfl⟩ : syracuseStep 970963 = 1456445) B1456445
theorem B970979 : Blo 968591 970979 := bstep (se 1 (by rfl) ⟨728234, by rfl⟩ : syracuseStep 970979 = 1456469) B1456469
theorem B970995 : Blo 968591 970995 := bstep (se 1 (by rfl) ⟨728246, by rfl⟩ : syracuseStep 970995 = 1456493) B1456493
theorem B971011 : Blo 968591 971011 := bstep (se 1 (by rfl) ⟨728258, by rfl⟩ : syracuseStep 971011 = 1456517) B1456517
theorem B971027 : Blo 968591 971027 := bstep (se 1 (by rfl) ⟨728270, by rfl⟩ : syracuseStep 971027 = 1456541) B1456541
theorem B971043 : Blo 968591 971043 := bstep (se 1 (by rfl) ⟨728282, by rfl⟩ : syracuseStep 971043 = 1456565) B1456565
theorem B971059 : Blo 968591 971059 := bstep (se 1 (by rfl) ⟨728294, by rfl⟩ : syracuseStep 971059 = 1456589) B1456589
theorem B971075 : Blo 968591 971075 := bstep (se 1 (by rfl) ⟨728306, by rfl⟩ : syracuseStep 971075 = 1456613) B1456613
theorem B971091 : Blo 968591 971091 := bstep (se 1 (by rfl) ⟨728318, by rfl⟩ : syracuseStep 971091 = 1456637) B1456637
theorem B971107 : Blo 968591 971107 := bstep (se 1 (by rfl) ⟨728330, by rfl⟩ : syracuseStep 971107 = 1456661) B1456661
theorem B971123 : Blo 968591 971123 := bstep (se 1 (by rfl) ⟨728342, by rfl⟩ : syracuseStep 971123 = 1456685) B1456685
theorem B971139 : Blo 968591 971139 := bstep (se 1 (by rfl) ⟨728354, by rfl⟩ : syracuseStep 971139 = 1456709) B1456709
theorem B971155 : Blo 968591 971155 := bstep (se 1 (by rfl) ⟨728366, by rfl⟩ : syracuseStep 971155 = 1456733) B1456733
theorem B971171 : Blo 968591 971171 := bstep (se 1 (by rfl) ⟨728378, by rfl⟩ : syracuseStep 971171 = 1456757) B1456757
theorem B971187 : Blo 968591 971187 := bstep (se 1 (by rfl) ⟨728390, by rfl⟩ : syracuseStep 971187 = 1456781) B1456781
theorem B971203 : Blo 968591 971203 := bstep (se 1 (by rfl) ⟨728402, by rfl⟩ : syracuseStep 971203 = 1456805) B1456805
theorem B2183633 : Blo 968591 2183633 := bstep (se 2 (by rfl) ⟨818862, by rfl⟩ : syracuseStep 2183633 = 1637725) B1637725
theorem B971219 : Blo 968591 971219 := bstep (se 1 (by rfl) ⟨728414, by rfl⟩ : syracuseStep 971219 = 1456829) B1456829
theorem B2183651 : Blo 968591 2183651 := bstep (se 1 (by rfl) ⟨1637738, by rfl⟩ : syracuseStep 2183651 = 3275477) B3275477
theorem B971235 : Blo 968591 971235 := bstep (se 1 (by rfl) ⟨728426, by rfl⟩ : syracuseStep 971235 = 1456853) B1456853
theorem B4149731 : Blo 968591 4149731 := bstep (se 1 (by rfl) ⟨3112298, by rfl⟩ : syracuseStep 4149731 = 6224597) B6224597
theorem B971251 : Blo 968591 971251 := bstep (se 1 (by rfl) ⟨728438, by rfl⟩ : syracuseStep 971251 = 1456877) B1456877
theorem B971267 : Blo 968591 971267 := bstep (se 1 (by rfl) ⟨728450, by rfl⟩ : syracuseStep 971267 = 1456901) B1456901
theorem B971283 : Blo 968591 971283 := bstep (se 1 (by rfl) ⟨728462, by rfl⟩ : syracuseStep 971283 = 1456925) B1456925
theorem B971299 : Blo 968591 971299 := bstep (se 1 (by rfl) ⟨728474, by rfl⟩ : syracuseStep 971299 = 1456949) B1456949
theorem B971315 : Blo 968591 971315 := bstep (se 1 (by rfl) ⟨728486, by rfl⟩ : syracuseStep 971315 = 1456973) B1456973
theorem B971331 : Blo 968591 971331 := bstep (se 1 (by rfl) ⟨728498, by rfl⟩ : syracuseStep 971331 = 1456997) B1456997
theorem B971347 : Blo 968591 971347 := bstep (se 1 (by rfl) ⟨728510, by rfl⟩ : syracuseStep 971347 = 1457021) B1457021
theorem B971363 : Blo 968591 971363 := bstep (se 1 (by rfl) ⟨728522, by rfl⟩ : syracuseStep 971363 = 1457045) B1457045
theorem B971379 : Blo 968591 971379 := bstep (se 1 (by rfl) ⟨728534, by rfl⟩ : syracuseStep 971379 = 1457069) B1457069
theorem B971395 : Blo 968591 971395 := bstep (se 1 (by rfl) ⟨728546, by rfl⟩ : syracuseStep 971395 = 1457093) B1457093
theorem B971411 : Blo 968591 971411 := bstep (se 1 (by rfl) ⟨728558, by rfl⟩ : syracuseStep 971411 = 1457117) B1457117
theorem B1036963 : Blo 968591 1036963 := bstep (se 1 (by rfl) ⟨777722, by rfl⟩ : syracuseStep 1036963 = 1555445) B1555445
theorem B971427 : Blo 968591 971427 := bstep (se 1 (by rfl) ⟨728570, by rfl⟩ : syracuseStep 971427 = 1457141) B1457141
theorem B971443 : Blo 968591 971443 := bstep (se 1 (by rfl) ⟨728582, by rfl⟩ : syracuseStep 971443 = 1457165) B1457165
theorem B971459 : Blo 968591 971459 := bstep (se 1 (by rfl) ⟨728594, by rfl⟩ : syracuseStep 971459 = 1457189) B1457189
theorem B971475 : Blo 968591 971475 := bstep (se 1 (by rfl) ⟨728606, by rfl⟩ : syracuseStep 971475 = 1457213) B1457213
theorem B971491 : Blo 968591 971491 := bstep (se 1 (by rfl) ⟨728618, by rfl⟩ : syracuseStep 971491 = 1457237) B1457237
theorem B2183921 : Blo 968591 2183921 := bstep (se 2 (by rfl) ⟨818970, by rfl⟩ : syracuseStep 2183921 = 1637941) B1637941
theorem B971507 : Blo 968591 971507 := bstep (se 1 (by rfl) ⟨728630, by rfl⟩ : syracuseStep 971507 = 1457261) B1457261
theorem B2183939 : Blo 968591 2183939 := bstep (se 1 (by rfl) ⟨1637954, by rfl⟩ : syracuseStep 2183939 = 3275909) B3275909
theorem B971523 : Blo 968591 971523 := bstep (se 1 (by rfl) ⟨728642, by rfl⟩ : syracuseStep 971523 = 1457285) B1457285
theorem B3691277 : Blo 968591 3691277 := bstep (se 3 (by rfl) ⟨692114, by rfl⟩ : syracuseStep 3691277 = 1384229) B1384229
theorem B971539 : Blo 968591 971539 := bstep (se 1 (by rfl) ⟨728654, by rfl⟩ : syracuseStep 971539 = 1457309) B1457309
theorem B1332001 : Blo 968591 1332001 := bstep (se 2 (by rfl) ⟨499500, by rfl⟩ : syracuseStep 1332001 = 999001) B999001
theorem B971555 : Blo 968591 971555 := bstep (se 1 (by rfl) ⟨728666, by rfl⟩ : syracuseStep 971555 = 1457333) B1457333
theorem B971571 : Blo 968591 971571 := bstep (se 1 (by rfl) ⟨728678, by rfl⟩ : syracuseStep 971571 = 1457357) B1457357
theorem B971587 : Blo 968591 971587 := bstep (se 1 (by rfl) ⟨728690, by rfl⟩ : syracuseStep 971587 = 1457381) B1457381
theorem B971603 : Blo 968591 971603 := bstep (se 1 (by rfl) ⟨728702, by rfl⟩ : syracuseStep 971603 = 1457405) B1457405
theorem B971619 : Blo 968591 971619 := bstep (se 1 (by rfl) ⟨728714, by rfl⟩ : syracuseStep 971619 = 1457429) B1457429
theorem B971635 : Blo 968591 971635 := bstep (se 1 (by rfl) ⟨728726, by rfl⟩ : syracuseStep 971635 = 1457453) B1457453
theorem B971651 : Blo 968591 971651 := bstep (se 1 (by rfl) ⟨728738, by rfl⟩ : syracuseStep 971651 = 1457477) B1457477
theorem B5526413 : Blo 968591 5526413 := bstep (se 3 (by rfl) ⟨1036202, by rfl⟩ : syracuseStep 5526413 = 2072405) B2072405
theorem B971667 : Blo 968591 971667 := bstep (se 1 (by rfl) ⟨728750, by rfl⟩ : syracuseStep 971667 = 1457501) B1457501
theorem B1037219 : Blo 968591 1037219 := bstep (se 1 (by rfl) ⟨777914, by rfl⟩ : syracuseStep 1037219 = 1555829) B1555829
theorem B971683 : Blo 968591 971683 := bstep (se 1 (by rfl) ⟨728762, by rfl⟩ : syracuseStep 971683 = 1457525) B1457525
theorem B1495985 : Blo 968591 1495985 := bstep (se 2 (by rfl) ⟨560994, by rfl⟩ : syracuseStep 1495985 = 1121989) B1121989
theorem B971699 : Blo 968591 971699 := bstep (se 1 (by rfl) ⟨728774, by rfl⟩ : syracuseStep 971699 = 1457549) B1457549
theorem B971715 : Blo 968591 971715 := bstep (se 1 (by rfl) ⟨728786, by rfl⟩ : syracuseStep 971715 = 1457573) B1457573
theorem B971731 : Blo 968591 971731 := bstep (se 1 (by rfl) ⟨728798, by rfl⟩ : syracuseStep 971731 = 1457597) B1457597
theorem B971747 : Blo 968591 971747 := bstep (se 1 (by rfl) ⟨728810, by rfl⟩ : syracuseStep 971747 = 1457621) B1457621
theorem B971763 : Blo 968591 971763 := bstep (se 1 (by rfl) ⟨728822, by rfl⟩ : syracuseStep 971763 = 1457645) B1457645
theorem B971779 : Blo 968591 971779 := bstep (se 1 (by rfl) ⟨728834, by rfl⟩ : syracuseStep 971779 = 1457669) B1457669
theorem B2184209 : Blo 968591 2184209 := bstep (se 2 (by rfl) ⟨819078, by rfl⟩ : syracuseStep 2184209 = 1638157) B1638157
theorem B971795 : Blo 968591 971795 := bstep (se 1 (by rfl) ⟨728846, by rfl⟩ : syracuseStep 971795 = 1457693) B1457693
theorem B2184227 : Blo 968591 2184227 := bstep (se 1 (by rfl) ⟨1638170, by rfl⟩ : syracuseStep 2184227 = 3276341) B3276341
theorem B971811 : Blo 968591 971811 := bstep (se 1 (by rfl) ⟨728858, by rfl⟩ : syracuseStep 971811 = 1457717) B1457717
theorem B971827 : Blo 968591 971827 := bstep (se 1 (by rfl) ⟨728870, by rfl⟩ : syracuseStep 971827 = 1457741) B1457741
theorem B971843 : Blo 968591 971843 := bstep (se 1 (by rfl) ⟨728882, by rfl⟩ : syracuseStep 971843 = 1457765) B1457765
theorem B971859 : Blo 968591 971859 := bstep (se 1 (by rfl) ⟨728894, by rfl⟩ : syracuseStep 971859 = 1457789) B1457789
theorem B971875 : Blo 968591 971875 := bstep (se 1 (by rfl) ⟨728906, by rfl⟩ : syracuseStep 971875 = 1457813) B1457813
theorem B971891 : Blo 968591 971891 := bstep (se 1 (by rfl) ⟨728918, by rfl⟩ : syracuseStep 971891 = 1457837) B1457837
theorem B971907 : Blo 968591 971907 := bstep (se 1 (by rfl) ⟨728930, by rfl⟩ : syracuseStep 971907 = 1457861) B1457861
theorem B971923 : Blo 968591 971923 := bstep (se 1 (by rfl) ⟨728942, by rfl⟩ : syracuseStep 971923 = 1457885) B1457885
theorem B971939 : Blo 968591 971939 := bstep (se 1 (by rfl) ⟨728954, by rfl⟩ : syracuseStep 971939 = 1457909) B1457909
theorem B971955 : Blo 968591 971955 := bstep (se 1 (by rfl) ⟨728966, by rfl⟩ : syracuseStep 971955 = 1457933) B1457933
theorem B971971 : Blo 968591 971971 := bstep (se 1 (by rfl) ⟨728978, by rfl⟩ : syracuseStep 971971 = 1457957) B1457957
theorem B971987 : Blo 968591 971987 := bstep (se 1 (by rfl) ⟨728990, by rfl⟩ : syracuseStep 971987 = 1457981) B1457981
theorem B972003 : Blo 968591 972003 := bstep (se 1 (by rfl) ⟨729002, by rfl⟩ : syracuseStep 972003 = 1458005) B1458005
theorem B8869105 : Blo 968591 8869105 := bstep (se 2 (by rfl) ⟨3325914, by rfl⟩ : syracuseStep 8869105 = 6651829) B6651829
theorem B972019 : Blo 968591 972019 := bstep (se 1 (by rfl) ⟨729014, by rfl⟩ : syracuseStep 972019 = 1458029) B1458029
theorem B972035 : Blo 968591 972035 := bstep (se 1 (by rfl) ⟨729026, by rfl⟩ : syracuseStep 972035 = 1458053) B1458053
theorem B972051 : Blo 968591 972051 := bstep (se 1 (by rfl) ⟨729038, by rfl⟩ : syracuseStep 972051 = 1458077) B1458077
theorem B972067 : Blo 968591 972067 := bstep (se 1 (by rfl) ⟨729050, by rfl⟩ : syracuseStep 972067 = 1458101) B1458101
theorem B2184497 : Blo 968591 2184497 := bstep (se 2 (by rfl) ⟨819186, by rfl⟩ : syracuseStep 2184497 = 1638373) B1638373
theorem B972083 : Blo 968591 972083 := bstep (se 1 (by rfl) ⟨729062, by rfl⟩ : syracuseStep 972083 = 1458125) B1458125
theorem B2184515 : Blo 968591 2184515 := bstep (se 1 (by rfl) ⟨1638386, by rfl⟩ : syracuseStep 2184515 = 3276773) B3276773
theorem B972099 : Blo 968591 972099 := bstep (se 1 (by rfl) ⟨729074, by rfl⟩ : syracuseStep 972099 = 1458149) B1458149
theorem B972115 : Blo 968591 972115 := bstep (se 1 (by rfl) ⟨729086, by rfl⟩ : syracuseStep 972115 = 1458173) B1458173
theorem B972131 : Blo 968591 972131 := bstep (se 1 (by rfl) ⟨729098, by rfl⟩ : syracuseStep 972131 = 1458197) B1458197
theorem B972147 : Blo 968591 972147 := bstep (se 1 (by rfl) ⟨729110, by rfl⟩ : syracuseStep 972147 = 1458221) B1458221
theorem B972163 : Blo 968591 972163 := bstep (se 1 (by rfl) ⟨729122, by rfl⟩ : syracuseStep 972163 = 1458245) B1458245
theorem B972179 : Blo 968591 972179 := bstep (se 1 (by rfl) ⟨729134, by rfl⟩ : syracuseStep 972179 = 1458269) B1458269
theorem B972195 : Blo 968591 972195 := bstep (se 1 (by rfl) ⟨729146, by rfl⟩ : syracuseStep 972195 = 1458293) B1458293
theorem B6215089 : Blo 968591 6215089 := bstep (se 2 (by rfl) ⟨2330658, by rfl⟩ : syracuseStep 6215089 = 4661317) B4661317
theorem B972211 : Blo 968591 972211 := bstep (se 1 (by rfl) ⟨729158, by rfl⟩ : syracuseStep 972211 = 1458317) B1458317
theorem B972227 : Blo 968591 972227 := bstep (se 1 (by rfl) ⟨729170, by rfl⟩ : syracuseStep 972227 = 1458341) B1458341
theorem B972243 : Blo 968591 972243 := bstep (se 1 (by rfl) ⟨729182, by rfl⟩ : syracuseStep 972243 = 1458365) B1458365
theorem B972259 : Blo 968591 972259 := bstep (se 1 (by rfl) ⟨729194, by rfl⟩ : syracuseStep 972259 = 1458389) B1458389
theorem B972275 : Blo 968591 972275 := bstep (se 1 (by rfl) ⟨729206, by rfl⟩ : syracuseStep 972275 = 1458413) B1458413
theorem B972291 : Blo 968591 972291 := bstep (se 1 (by rfl) ⟨729218, by rfl⟩ : syracuseStep 972291 = 1458437) B1458437
theorem B6313477 : Blo 968591 6313477 := bstep (se 4 (by rfl) ⟨591888, by rfl⟩ : syracuseStep 6313477 = 1183777) B1183777
theorem B972307 : Blo 968591 972307 := bstep (se 1 (by rfl) ⟨729230, by rfl⟩ : syracuseStep 972307 = 1458461) B1458461
theorem B972323 : Blo 968591 972323 := bstep (se 1 (by rfl) ⟨729242, by rfl⟩ : syracuseStep 972323 = 1458485) B1458485
theorem B3692081 : Blo 968591 3692081 := bstep (se 2 (by rfl) ⟨1384530, by rfl⟩ : syracuseStep 3692081 = 2769061) B2769061
theorem B972339 : Blo 968591 972339 := bstep (se 1 (by rfl) ⟨729254, by rfl⟩ : syracuseStep 972339 = 1458509) B1458509
theorem B972355 : Blo 968591 972355 := bstep (se 1 (by rfl) ⟨729266, by rfl⟩ : syracuseStep 972355 = 1458533) B1458533
theorem B2184785 : Blo 968591 2184785 := bstep (se 2 (by rfl) ⟨819294, by rfl⟩ : syracuseStep 2184785 = 1638589) B1638589
theorem B972371 : Blo 968591 972371 := bstep (se 1 (by rfl) ⟨729278, by rfl⟩ : syracuseStep 972371 = 1458557) B1458557
theorem B2184803 : Blo 968591 2184803 := bstep (se 1 (by rfl) ⟨1638602, by rfl⟩ : syracuseStep 2184803 = 3277205) B3277205
theorem B972387 : Blo 968591 972387 := bstep (se 1 (by rfl) ⟨729290, by rfl⟩ : syracuseStep 972387 = 1458581) B1458581
theorem B972403 : Blo 968591 972403 := bstep (se 1 (by rfl) ⟨729302, by rfl⟩ : syracuseStep 972403 = 1458605) B1458605
theorem B972419 : Blo 968591 972419 := bstep (se 1 (by rfl) ⟨729314, by rfl⟩ : syracuseStep 972419 = 1458629) B1458629
theorem B1037971 : Blo 968591 1037971 := bstep (se 1 (by rfl) ⟨778478, by rfl⟩ : syracuseStep 1037971 = 1556957) B1556957
theorem B972435 : Blo 968591 972435 := bstep (se 1 (by rfl) ⟨729326, by rfl⟩ : syracuseStep 972435 = 1458653) B1458653
theorem B972451 : Blo 968591 972451 := bstep (se 1 (by rfl) ⟨729338, by rfl⟩ : syracuseStep 972451 = 1458677) B1458677
theorem B972467 : Blo 968591 972467 := bstep (se 1 (by rfl) ⟨729350, by rfl⟩ : syracuseStep 972467 = 1458701) B1458701
theorem B972483 : Blo 968591 972483 := bstep (se 1 (by rfl) ⟨729362, by rfl⟩ : syracuseStep 972483 = 1458725) B1458725
theorem B972499 : Blo 968591 972499 := bstep (se 1 (by rfl) ⟨729374, by rfl⟩ : syracuseStep 972499 = 1458749) B1458749
theorem B972515 : Blo 968591 972515 := bstep (se 1 (by rfl) ⟨729386, by rfl⟩ : syracuseStep 972515 = 1458773) B1458773
theorem B972531 : Blo 968591 972531 := bstep (se 1 (by rfl) ⟨729398, by rfl⟩ : syracuseStep 972531 = 1458797) B1458797
theorem B972547 : Blo 968591 972547 := bstep (se 1 (by rfl) ⟨729410, by rfl⟩ : syracuseStep 972547 = 1458821) B1458821
theorem B972563 : Blo 968591 972563 := bstep (se 1 (by rfl) ⟨729422, by rfl⟩ : syracuseStep 972563 = 1458845) B1458845
theorem B972579 : Blo 968591 972579 := bstep (se 1 (by rfl) ⟨729434, by rfl⟩ : syracuseStep 972579 = 1458869) B1458869
theorem B2185073 : Blo 968591 2185073 := bstep (se 2 (by rfl) ⟨819402, by rfl⟩ : syracuseStep 2185073 = 1638805) B1638805
theorem B2185091 : Blo 968591 2185091 := bstep (se 1 (by rfl) ⟨1638818, by rfl⟩ : syracuseStep 2185091 = 3277637) B3277637
theorem B2185361 : Blo 968591 2185361 := bstep (se 2 (by rfl) ⟨819510, by rfl⟩ : syracuseStep 2185361 = 1639021) B1639021
theorem B2185379 : Blo 968591 2185379 := bstep (se 1 (by rfl) ⟨1639034, by rfl⟩ : syracuseStep 2185379 = 3278069) B3278069
theorem B3692749 : Blo 968591 3692749 := bstep (se 3 (by rfl) ⟨692390, by rfl⟩ : syracuseStep 3692749 = 1384781) B1384781
theorem B2185649 : Blo 968591 2185649 := bstep (se 2 (by rfl) ⟨819618, by rfl⟩ : syracuseStep 2185649 = 1639237) B1639237
theorem B2185667 : Blo 968591 2185667 := bstep (se 1 (by rfl) ⟨1639250, by rfl⟩ : syracuseStep 2185667 = 3278501) B3278501
theorem B4905521 : Blo 968591 4905521 := bstep (se 2 (by rfl) ⟨1839570, by rfl⟩ : syracuseStep 4905521 = 3679141) B3679141
theorem B2185937 : Blo 968591 2185937 := bstep (se 2 (by rfl) ⟨819726, by rfl⟩ : syracuseStep 2185937 = 1639453) B1639453
theorem B2185955 : Blo 968591 2185955 := bstep (se 1 (by rfl) ⟨1639466, by rfl⟩ : syracuseStep 2185955 = 3278933) B3278933
theorem B8837873 : Blo 968591 8837873 := bstep (se 2 (by rfl) ⟨3314202, by rfl⟩ : syracuseStep 8837873 = 6628405) B6628405
theorem B1661699 : Blo 968591 1661699 := bstep (se 1 (by rfl) ⟨1246274, by rfl⟩ : syracuseStep 1661699 = 2492549) B2492549
theorem B1661809 : Blo 968591 1661809 := bstep (se 2 (by rfl) ⟨623178, by rfl⟩ : syracuseStep 1661809 = 1246357) B1246357
theorem B2186225 : Blo 968591 2186225 := bstep (se 2 (by rfl) ⟨819834, by rfl⟩ : syracuseStep 2186225 = 1639669) B1639669
theorem B2186243 : Blo 968591 2186243 := bstep (se 1 (by rfl) ⟨1639682, by rfl⟩ : syracuseStep 2186243 = 3279365) B3279365
theorem B5528645 : Blo 968591 5528645 := bstep (se 4 (by rfl) ⟨518310, by rfl⟩ : syracuseStep 5528645 = 1036621) B1036621
theorem B2186513 : Blo 968591 2186513 := bstep (se 2 (by rfl) ⟨819942, by rfl⟩ : syracuseStep 2186513 = 1639885) B1639885
theorem B2186531 : Blo 968591 2186531 := bstep (se 1 (by rfl) ⟨1639898, by rfl⟩ : syracuseStep 2186531 = 3279797) B3279797
theorem B3104173 : Blo 968591 3104173 := bstep (se 3 (by rfl) ⟨582032, by rfl⟩ : syracuseStep 3104173 = 1164065) B1164065
theorem B42589637 : Blo 968591 42589637 := bstep (se 4 (by rfl) ⟨3992778, by rfl⟩ : syracuseStep 42589637 = 7985557) B7985557
theorem B2186801 : Blo 968591 2186801 := bstep (se 2 (by rfl) ⟨820050, by rfl⟩ : syracuseStep 2186801 = 1640101) B1640101
theorem B2186819 : Blo 968591 2186819 := bstep (se 1 (by rfl) ⟨1640114, by rfl⟩ : syracuseStep 2186819 = 3280229) B3280229
theorem B5529329 : Blo 968591 5529329 := bstep (se 2 (by rfl) ⟨2073498, by rfl⟩ : syracuseStep 5529329 = 4146997) B4146997
theorem B2187089 : Blo 968591 2187089 := bstep (se 2 (by rfl) ⟨820158, by rfl⟩ : syracuseStep 2187089 = 1640317) B1640317
theorem B2187107 : Blo 968591 2187107 := bstep (se 1 (by rfl) ⟨1640330, by rfl⟩ : syracuseStep 2187107 = 3280661) B3280661
theorem B11198321 : Blo 968591 11198321 := bstep (se 2 (by rfl) ⟨4199370, by rfl⟩ : syracuseStep 11198321 = 8398741) B8398741
theorem B3104675 : Blo 968591 3104675 := bstep (se 1 (by rfl) ⟨2328506, by rfl⟩ : syracuseStep 3104675 = 4657013) B4657013
theorem B4906979 : Blo 968591 4906979 := bstep (se 1 (by rfl) ⟨3680234, by rfl⟩ : syracuseStep 4906979 = 7360469) B7360469
theorem B2187377 : Blo 968591 2187377 := bstep (se 2 (by rfl) ⟨820266, by rfl⟩ : syracuseStep 2187377 = 1640533) B1640533
theorem B2187395 : Blo 968591 2187395 := bstep (se 1 (by rfl) ⟨1640546, by rfl⟩ : syracuseStep 2187395 = 3281093) B3281093
theorem B5595299 : Blo 968591 5595299 := bstep (se 1 (by rfl) ⟨4196474, by rfl⟩ : syracuseStep 5595299 = 8392949) B8392949
theorem B2187665 : Blo 968591 2187665 := bstep (se 2 (by rfl) ⟨820374, by rfl⟩ : syracuseStep 2187665 = 1640749) B1640749
theorem B2187683 : Blo 968591 2187683 := bstep (se 1 (by rfl) ⟨1640762, by rfl⟩ : syracuseStep 2187683 = 3281525) B3281525
theorem B3269105 : Blo 968591 3269105 := bstep (se 2 (by rfl) ⟨1225914, by rfl⟩ : syracuseStep 3269105 = 2451829) B2451829
theorem B4153933 : Blo 968591 4153933 := bstep (se 3 (by rfl) ⟨778862, by rfl⟩ : syracuseStep 4153933 = 1557725) B1557725
theorem B2187953 : Blo 968591 2187953 := bstep (se 2 (by rfl) ⟨820482, by rfl⟩ : syracuseStep 2187953 = 1640965) B1640965
theorem B2187971 : Blo 968591 2187971 := bstep (se 1 (by rfl) ⟨1640978, by rfl⟩ : syracuseStep 2187971 = 3281957) B3281957
theorem B4907789 : Blo 968591 4907789 := bstep (se 3 (by rfl) ⟨920210, by rfl⟩ : syracuseStep 4907789 = 1840421) B1840421
theorem B2188241 : Blo 968591 2188241 := bstep (se 2 (by rfl) ⟨820590, by rfl⟩ : syracuseStep 2188241 = 1641181) B1641181
theorem B2188259 : Blo 968591 2188259 := bstep (se 1 (by rfl) ⟨1641194, by rfl⟩ : syracuseStep 2188259 = 3282389) B3282389
theorem B3269645 : Blo 968591 3269645 := bstep (se 3 (by rfl) ⟨613058, by rfl⟩ : syracuseStep 3269645 = 1226117) B1226117
theorem B3269699 : Blo 968591 3269699 := bstep (se 1 (by rfl) ⟨2452274, by rfl⟩ : syracuseStep 3269699 = 4904549) B4904549
theorem B5530787 : Blo 968591 5530787 := bstep (se 1 (by rfl) ⟨4148090, by rfl⟩ : syracuseStep 5530787 = 8296181) B8296181
theorem B3106019 : Blo 968591 3106019 := bstep (se 1 (by rfl) ⟨2329514, by rfl⟩ : syracuseStep 3106019 = 4659029) B4659029
theorem B3269969 : Blo 968591 3269969 := bstep (se 2 (by rfl) ⟨1226238, by rfl⟩ : syracuseStep 3269969 = 2452477) B2452477
theorem B1402705 : Blo 968591 1402705 := bstep (se 2 (by rfl) ⟨526014, by rfl⟩ : syracuseStep 1402705 = 1052029) B1052029
theorem B3270509 : Blo 968591 3270509 := bstep (se 3 (by rfl) ⟨613220, by rfl⟩ : syracuseStep 3270509 = 1226441) B1226441
theorem B3270563 : Blo 968591 3270563 := bstep (se 1 (by rfl) ⟨2452922, by rfl⟩ : syracuseStep 3270563 = 4905845) B4905845
theorem B1402867 : Blo 968591 1402867 := bstep (se 1 (by rfl) ⟨1052150, by rfl⟩ : syracuseStep 1402867 = 2104301) B2104301
theorem B3237937 : Blo 968591 3237937 := bstep (se 2 (by rfl) ⟨1214226, by rfl⟩ : syracuseStep 3237937 = 2428453) B2428453
theorem B1402931 : Blo 968591 1402931 := bstep (se 1 (by rfl) ⟨1052198, by rfl⟩ : syracuseStep 1402931 = 2104397) B2104397
theorem B3270833 : Blo 968591 3270833 := bstep (se 2 (by rfl) ⟨1226562, by rfl⟩ : syracuseStep 3270833 = 2453125) B2453125
theorem B3106993 : Blo 968591 3106993 := bstep (se 2 (by rfl) ⟨1165122, by rfl⟩ : syracuseStep 3106993 = 2330245) B2330245
theorem B1796323 : Blo 968591 1796323 := bstep (se 1 (by rfl) ⟨1347242, by rfl⟩ : syracuseStep 1796323 = 2694485) B2694485
theorem B2451779 : Blo 968591 2451779 := bstep (se 1 (by rfl) ⟨1838834, by rfl⟩ : syracuseStep 2451779 = 3677669) B3677669
theorem B3107249 : Blo 968591 3107249 := bstep (se 2 (by rfl) ⟨1165218, by rfl⟩ : syracuseStep 3107249 = 2330437) B2330437
theorem B1403329 : Blo 968591 1403329 := bstep (se 2 (by rfl) ⟨526248, by rfl⟩ : syracuseStep 1403329 = 1052497) B1052497
theorem B2451971 : Blo 968591 2451971 := bstep (se 1 (by rfl) ⟨1838978, by rfl⟩ : syracuseStep 2451971 = 3677957) B3677957
theorem B6220421 : Blo 968591 6220421 := bstep (se 4 (by rfl) ⟨583164, by rfl⟩ : syracuseStep 6220421 = 1166329) B1166329
theorem B1108675 : Blo 968591 1108675 := bstep (se 1 (by rfl) ⟨831506, by rfl⟩ : syracuseStep 1108675 = 1663013) B1663013
theorem B3271373 : Blo 968591 3271373 := bstep (se 3 (by rfl) ⟨613382, by rfl⟩ : syracuseStep 3271373 = 1226765) B1226765
theorem B3271427 : Blo 968591 3271427 := bstep (se 1 (by rfl) ⟨2453570, by rfl⟩ : syracuseStep 3271427 = 4907141) B4907141
theorem B3271697 : Blo 968591 3271697 := bstep (se 2 (by rfl) ⟨1226886, by rfl⟩ : syracuseStep 3271697 = 2453773) B2453773
theorem B24866189 : Blo 968591 24866189 := bstep (se 3 (by rfl) ⟨4662410, by rfl⟩ : syracuseStep 24866189 = 9324821) B9324821
theorem B2452913 : Blo 968591 2452913 := bstep (se 2 (by rfl) ⟨919842, by rfl⟩ : syracuseStep 2452913 = 1839685) B1839685
theorem B2452963 : Blo 968591 2452963 := bstep (se 1 (by rfl) ⟨1839722, by rfl⟩ : syracuseStep 2452963 = 3679445) B3679445
theorem B3501539 : Blo 968591 3501539 := bstep (se 1 (by rfl) ⟨2626154, by rfl⟩ : syracuseStep 3501539 = 5252309) B5252309
theorem B3108365 : Blo 968591 3108365 := bstep (se 3 (by rfl) ⟨582818, by rfl⟩ : syracuseStep 3108365 = 1165637) B1165637
theorem B3272237 : Blo 968591 3272237 := bstep (se 3 (by rfl) ⟨613544, by rfl⟩ : syracuseStep 3272237 = 1227089) B1227089
theorem B3272291 : Blo 968591 3272291 := bstep (se 1 (by rfl) ⟨2454218, by rfl⟩ : syracuseStep 3272291 = 4908437) B4908437
theorem B2453105 : Blo 968591 2453105 := bstep (se 2 (by rfl) ⟨919914, by rfl⟩ : syracuseStep 2453105 = 1839829) B1839829
theorem B4910705 : Blo 968591 4910705 := bstep (se 2 (by rfl) ⟨1841514, by rfl⟩ : syracuseStep 4910705 = 3683029) B3683029
theorem B1404691 : Blo 968591 1404691 := bstep (se 1 (by rfl) ⟨1053518, by rfl⟩ : syracuseStep 1404691 = 2107037) B2107037
theorem B11038517 : Blo 968591 11038517 := bstep (se 5 (by rfl) ⟨517430, by rfl⟩ : syracuseStep 11038517 = 1034861) B1034861
theorem B3272561 : Blo 968591 3272561 := bstep (se 2 (by rfl) ⟨1227210, by rfl⟩ : syracuseStep 3272561 = 2454421) B2454421
theorem B12447857 : Blo 968591 12447857 := bstep (se 2 (by rfl) ⟨4667946, by rfl⟩ : syracuseStep 12447857 = 9335893) B9335893
theorem B1634593 : Blo 968591 1634593 := bstep (se 2 (by rfl) ⟨612972, by rfl⟩ : syracuseStep 1634593 = 1225945) B1225945
theorem B1634627 : Blo 968591 1634627 := bstep (se 1 (by rfl) ⟨1225970, by rfl⟩ : syracuseStep 1634627 = 2451941) B2451941
theorem B5534021 : Blo 968591 5534021 := bstep (se 4 (by rfl) ⟨518814, by rfl⟩ : syracuseStep 5534021 = 1037629) B1037629
theorem B3273101 : Blo 968591 3273101 := bstep (se 3 (by rfl) ⟨613706, by rfl⟩ : syracuseStep 3273101 = 1227413) B1227413
theorem B1634755 : Blo 968591 1634755 := bstep (se 1 (by rfl) ⟨1226066, by rfl⟩ : syracuseStep 1634755 = 2452133) B2452133
theorem B3273155 : Blo 968591 3273155 := bstep (se 1 (by rfl) ⟨2454866, by rfl⟩ : syracuseStep 3273155 = 4909733) B4909733
theorem B5239331 : Blo 968591 5239331 := bstep (se 1 (by rfl) ⟨3929498, by rfl⟩ : syracuseStep 5239331 = 7858997) B7858997
theorem B1634897 : Blo 968591 1634897 := bstep (se 2 (by rfl) ⟨613086, by rfl⟩ : syracuseStep 1634897 = 1226173) B1226173
theorem B2454097 : Blo 968591 2454097 := bstep (se 2 (by rfl) ⟨920286, by rfl⟩ : syracuseStep 2454097 = 1840573) B1840573
theorem B11956835 : Blo 968591 11956835 := bstep (se 1 (by rfl) ⟨8967626, by rfl⟩ : syracuseStep 11956835 = 17935253) B17935253
theorem B1635025 : Blo 968591 1635025 := bstep (se 2 (by rfl) ⟨613134, by rfl⟩ : syracuseStep 1635025 = 1226269) B1226269
theorem B3273425 : Blo 968591 3273425 := bstep (se 2 (by rfl) ⟨1227534, by rfl⟩ : syracuseStep 3273425 = 2455069) B2455069
theorem B1635059 : Blo 968591 1635059 := bstep (se 1 (by rfl) ⟨1226294, by rfl⟩ : syracuseStep 1635059 = 2452589) B2452589
theorem B5534477 : Blo 968591 5534477 := bstep (se 3 (by rfl) ⟨1037714, by rfl⟩ : syracuseStep 5534477 = 2075429) B2075429
theorem B17953589 : Blo 968591 17953589 := bstep (se 5 (by rfl) ⟨841574, by rfl⟩ : syracuseStep 17953589 = 1683149) B1683149
theorem B3109709 : Blo 968591 3109709 := bstep (se 3 (by rfl) ⟨583070, by rfl⟩ : syracuseStep 3109709 = 1166141) B1166141
theorem B2454371 : Blo 968591 2454371 := bstep (se 1 (by rfl) ⟨1840778, by rfl⟩ : syracuseStep 2454371 = 3681557) B3681557
theorem B1635187 : Blo 968591 1635187 := bstep (se 1 (by rfl) ⟨1226390, by rfl⟩ : syracuseStep 1635187 = 2452781) B2452781
theorem B1635329 : Blo 968591 1635329 := bstep (se 2 (by rfl) ⟨613248, by rfl⟩ : syracuseStep 1635329 = 1226497) B1226497
theorem B2454563 : Blo 968591 2454563 := bstep (se 1 (by rfl) ⟨1840922, by rfl⟩ : syracuseStep 2454563 = 3681845) B3681845
theorem B4912163 : Blo 968591 4912163 := bstep (se 1 (by rfl) ⟨3684122, by rfl⟩ : syracuseStep 4912163 = 7368245) B7368245
theorem B1635457 : Blo 968591 1635457 := bstep (se 2 (by rfl) ⟨613296, by rfl⟩ : syracuseStep 1635457 = 1226593) B1226593
theorem B1635491 : Blo 968591 1635491 := bstep (se 1 (by rfl) ⟨1226618, by rfl⟩ : syracuseStep 1635491 = 2453237) B2453237
theorem B3503267 : Blo 968591 3503267 := bstep (se 1 (by rfl) ⟨2627450, by rfl⟩ : syracuseStep 3503267 = 5254901) B5254901
theorem B3273965 : Blo 968591 3273965 := bstep (se 3 (by rfl) ⟨613868, by rfl⟩ : syracuseStep 3273965 = 1227737) B1227737
theorem B3110147 : Blo 968591 3110147 := bstep (se 1 (by rfl) ⟨2332610, by rfl⟩ : syracuseStep 3110147 = 4665221) B4665221
theorem B1635619 : Blo 968591 1635619 := bstep (se 1 (by rfl) ⟨1226714, by rfl⟩ : syracuseStep 1635619 = 2453429) B2453429
theorem B3274019 : Blo 968591 3274019 := bstep (se 1 (by rfl) ⟨2455514, by rfl⟩ : syracuseStep 3274019 = 4911029) B4911029
theorem B2618705 : Blo 968591 2618705 := bstep (se 2 (by rfl) ⟨982014, by rfl⟩ : syracuseStep 2618705 = 1964029) B1964029
theorem B2618801 : Blo 968591 2618801 := bstep (se 2 (by rfl) ⟨982050, by rfl⟩ : syracuseStep 2618801 = 1964101) B1964101
theorem B1635761 : Blo 968591 1635761 := bstep (se 2 (by rfl) ⟨613410, by rfl⟩ : syracuseStep 1635761 = 1226821) B1226821
theorem B5895665 : Blo 968591 5895665 := bstep (se 2 (by rfl) ⟨2210874, by rfl⟩ : syracuseStep 5895665 = 4421749) B4421749
theorem B5240369 : Blo 968591 5240369 := bstep (se 2 (by rfl) ⟨1965138, by rfl⟩ : syracuseStep 5240369 = 3930277) B3930277
theorem B1635889 : Blo 968591 1635889 := bstep (se 2 (by rfl) ⟨613458, by rfl⟩ : syracuseStep 1635889 = 1226917) B1226917
theorem B3274289 : Blo 968591 3274289 := bstep (se 2 (by rfl) ⟨1227858, by rfl⟩ : syracuseStep 3274289 = 2455717) B2455717
theorem B1635923 : Blo 968591 1635923 := bstep (se 1 (by rfl) ⟨1226942, by rfl⟩ : syracuseStep 1635923 = 2453885) B2453885
theorem B3503729 : Blo 968591 3503729 := bstep (se 2 (by rfl) ⟨1313898, by rfl⟩ : syracuseStep 3503729 = 2627797) B2627797
theorem B1636051 : Blo 968591 1636051 := bstep (se 1 (by rfl) ⟨1227038, by rfl⟩ : syracuseStep 1636051 = 2454077) B2454077
theorem B25196309 : Blo 968591 25196309 := bstep (se 6 (by rfl) ⟨590538, by rfl⟩ : syracuseStep 25196309 = 1181077) B1181077
theorem B4912973 : Blo 968591 4912973 := bstep (se 3 (by rfl) ⟨921182, by rfl⟩ : syracuseStep 4912973 = 1842365) B1842365
theorem B1636193 : Blo 968591 1636193 := bstep (se 2 (by rfl) ⟨613572, by rfl⟩ : syracuseStep 1636193 = 1227145) B1227145
theorem B2455505 : Blo 968591 2455505 := bstep (se 2 (by rfl) ⟨920814, by rfl⟩ : syracuseStep 2455505 = 1841629) B1841629
theorem B1636321 : Blo 968591 1636321 := bstep (se 2 (by rfl) ⟨613620, by rfl⟩ : syracuseStep 1636321 = 1227241) B1227241
theorem B1636355 : Blo 968591 1636355 := bstep (se 1 (by rfl) ⟨1227266, by rfl⟩ : syracuseStep 1636355 = 2454533) B2454533
theorem B2455555 : Blo 968591 2455555 := bstep (se 1 (by rfl) ⟨1841666, by rfl⟩ : syracuseStep 2455555 = 3683333) B3683333
theorem B12449861 : Blo 968591 12449861 := bstep (se 4 (by rfl) ⟨1167174, by rfl⟩ : syracuseStep 12449861 = 2334349) B2334349
theorem B3274829 : Blo 968591 3274829 := bstep (se 3 (by rfl) ⟨614030, by rfl⟩ : syracuseStep 3274829 = 1228061) B1228061
theorem B1636483 : Blo 968591 1636483 := bstep (se 1 (by rfl) ⟨1227362, by rfl⟩ : syracuseStep 1636483 = 2454725) B2454725
theorem B3274883 : Blo 968591 3274883 := bstep (se 1 (by rfl) ⟨2456162, by rfl⟩ : syracuseStep 3274883 = 4912325) B4912325
theorem B2455697 : Blo 968591 2455697 := bstep (se 2 (by rfl) ⟨920886, by rfl⟩ : syracuseStep 2455697 = 1841773) B1841773
theorem B1636625 : Blo 968591 1636625 := bstep (se 2 (by rfl) ⟨613734, by rfl⟩ : syracuseStep 1636625 = 1227469) B1227469
theorem B1636753 : Blo 968591 1636753 := bstep (se 2 (by rfl) ⟨613782, by rfl⟩ : syracuseStep 1636753 = 1227565) B1227565
theorem B3275153 : Blo 968591 3275153 := bstep (se 2 (by rfl) ⟨1228182, by rfl⟩ : syracuseStep 3275153 = 2456365) B2456365
theorem B1636787 : Blo 968591 1636787 := bstep (se 1 (by rfl) ⟨1227590, by rfl⟩ : syracuseStep 1636787 = 2455181) B2455181
theorem B1636915 : Blo 968591 1636915 := bstep (se 1 (by rfl) ⟨1227686, by rfl⟩ : syracuseStep 1636915 = 2455373) B2455373
theorem B2947661 : Blo 968591 2947661 := bstep (se 3 (by rfl) ⟨552686, by rfl⟩ : syracuseStep 2947661 = 1105373) B1105373
theorem B1637057 : Blo 968591 1637057 := bstep (se 2 (by rfl) ⟨613896, by rfl⟩ : syracuseStep 1637057 = 1227793) B1227793
theorem B1309379 : Blo 968591 1309379 := bstep (se 1 (by rfl) ⟨982034, by rfl⟩ : syracuseStep 1309379 = 1964069) B1964069
theorem B3930929 : Blo 968591 3930929 := bstep (se 2 (by rfl) ⟨1474098, by rfl⟩ : syracuseStep 3930929 = 2948197) B2948197
theorem B1637185 : Blo 968591 1637185 := bstep (se 2 (by rfl) ⟨613944, by rfl⟩ : syracuseStep 1637185 = 1227889) B1227889
theorem B5602117 : Blo 968591 5602117 := bstep (se 4 (by rfl) ⟨525198, by rfl⟩ : syracuseStep 5602117 = 1050397) B1050397
theorem B1637219 : Blo 968591 1637219 := bstep (se 1 (by rfl) ⟨1227914, by rfl⟩ : syracuseStep 1637219 = 2455829) B2455829
theorem B3275693 : Blo 968591 3275693 := bstep (se 3 (by rfl) ⟨614192, by rfl⟩ : syracuseStep 3275693 = 1228385) B1228385
theorem B1866673 : Blo 968591 1866673 := bstep (se 2 (by rfl) ⟨700002, by rfl⟩ : syracuseStep 1866673 = 1400005) B1400005
theorem B1637347 : Blo 968591 1637347 := bstep (se 1 (by rfl) ⟨1228010, by rfl⟩ : syracuseStep 1637347 = 2456021) B2456021
theorem B3275747 : Blo 968591 3275747 := bstep (se 1 (by rfl) ⟨2456810, by rfl⟩ : syracuseStep 3275747 = 4913621) B4913621
theorem B1637489 : Blo 968591 1637489 := bstep (se 2 (by rfl) ⟨614058, by rfl⟩ : syracuseStep 1637489 = 1228117) B1228117
theorem B2456689 : Blo 968591 2456689 := bstep (se 2 (by rfl) ⟨921258, by rfl⟩ : syracuseStep 2456689 = 1842517) B1842517
theorem B3112067 : Blo 968591 3112067 := bstep (se 1 (by rfl) ⟨2334050, by rfl⟩ : syracuseStep 3112067 = 4668101) B4668101
theorem B1637617 : Blo 968591 1637617 := bstep (se 2 (by rfl) ⟨614106, by rfl⟩ : syracuseStep 1637617 = 1228213) B1228213
theorem B3276017 : Blo 968591 3276017 := bstep (se 2 (by rfl) ⟨1228506, by rfl⟩ : syracuseStep 3276017 = 2457013) B2457013
theorem B9338125 : Blo 968591 9338125 := bstep (se 3 (by rfl) ⟨1750898, by rfl⟩ : syracuseStep 9338125 = 3501797) B3501797
theorem B1637651 : Blo 968591 1637651 := bstep (se 1 (by rfl) ⟨1228238, by rfl⟩ : syracuseStep 1637651 = 2456477) B2456477
theorem B2456963 : Blo 968591 2456963 := bstep (se 1 (by rfl) ⟨1842722, by rfl⟩ : syracuseStep 2456963 = 3685445) B3685445
theorem B1637779 : Blo 968591 1637779 := bstep (se 1 (by rfl) ⟨1228334, by rfl⟩ : syracuseStep 1637779 = 2456669) B2456669
theorem B1310131 : Blo 968591 1310131 := bstep (se 1 (by rfl) ⟨982598, by rfl⟩ : syracuseStep 1310131 = 1965197) B1965197
theorem B1310179 : Blo 968591 1310179 := bstep (se 1 (by rfl) ⟨982634, by rfl⟩ : syracuseStep 1310179 = 1965269) B1965269
theorem B20708885 : Blo 968591 20708885 := bstep (se 6 (by rfl) ⟨485364, by rfl⟩ : syracuseStep 20708885 = 970729) B970729
theorem B1637921 : Blo 968591 1637921 := bstep (se 2 (by rfl) ⟨614220, by rfl⟩ : syracuseStep 1637921 = 1228441) B1228441
theorem B2457155 : Blo 968591 2457155 := bstep (se 1 (by rfl) ⟨1842866, by rfl⟩ : syracuseStep 2457155 = 3685733) B3685733
theorem B5537393 : Blo 968591 5537393 := bstep (se 2 (by rfl) ⟨2076522, by rfl⟩ : syracuseStep 5537393 = 4153045) B4153045
theorem B982675 : Blo 968591 982675 := bstep (se 1 (by rfl) ⟨737006, by rfl⟩ : syracuseStep 982675 = 1474013) B1474013
theorem B1638049 : Blo 968591 1638049 := bstep (se 2 (by rfl) ⟨614268, by rfl⟩ : syracuseStep 1638049 = 1228537) B1228537
theorem B1474243 : Blo 968591 1474243 := bstep (se 1 (by rfl) ⟨1105682, by rfl⟩ : syracuseStep 1474243 = 2211365) B2211365
theorem B1638083 : Blo 968591 1638083 := bstep (se 1 (by rfl) ⟨1228562, by rfl⟩ : syracuseStep 1638083 = 2457125) B2457125
theorem B3276557 : Blo 968591 3276557 := bstep (se 3 (by rfl) ⟨614354, by rfl⟩ : syracuseStep 3276557 = 1228709) B1228709
theorem B1638211 : Blo 968591 1638211 := bstep (se 1 (by rfl) ⟨1228658, by rfl⟩ : syracuseStep 1638211 = 2457317) B2457317
theorem B3276611 : Blo 968591 3276611 := bstep (se 1 (by rfl) ⟨2457458, by rfl⟩ : syracuseStep 3276611 = 4914917) B4914917
theorem B1867619 : Blo 968591 1867619 := bstep (se 1 (by rfl) ⟨1400714, by rfl⟩ : syracuseStep 1867619 = 2801429) B2801429
theorem B1310611 : Blo 968591 1310611 := bstep (se 1 (by rfl) ⟨982958, by rfl⟩ : syracuseStep 1310611 = 1965917) B1965917
theorem B1474481 : Blo 968591 1474481 := bstep (se 2 (by rfl) ⟨552930, by rfl⟩ : syracuseStep 1474481 = 1105861) B1105861
theorem B1638353 : Blo 968591 1638353 := bstep (se 2 (by rfl) ⟨614382, by rfl⟩ : syracuseStep 1638353 = 1228765) B1228765
theorem B1179635 : Blo 968591 1179635 := bstep (se 1 (by rfl) ⟨884726, by rfl⟩ : syracuseStep 1179635 = 1769453) B1769453
theorem B11042891 : Blo 968591 11042891 := bstep (se 1 (by rfl) ⟨8282168, by rfl⟩ : syracuseStep 11042891 = 16564337) B16564337
theorem B2457803 : Blo 968591 2457803 := bstep (se 1 (by rfl) ⟨1843352, by rfl⟩ : syracuseStep 2457803 = 3686705) B3686705
theorem B8847577 : Blo 968591 8847577 := bstep (se 2 (by rfl) ⟨3317841, by rfl⟩ : syracuseStep 8847577 = 6635683) B6635683
theorem B4423897 : Blo 968591 4423897 := bstep (se 2 (by rfl) ⟨1658961, by rfl⟩ : syracuseStep 4423897 = 3317923) B3317923
theorem B17268997 : Blo 968591 17268997 := bstep (se 4 (by rfl) ⟨1618968, by rfl⟩ : syracuseStep 17268997 = 3237937) B3237937
theorem B1638731 : Blo 968591 1638731 := bstep (se 1 (by rfl) ⟨1229048, by rfl⟩ : syracuseStep 1638731 = 2458097) B2458097
theorem B3277259 : Blo 968591 3277259 := bstep (se 1 (by rfl) ⟨2457944, by rfl⟩ : syracuseStep 3277259 = 4915889) B4915889
theorem B1638859 : Blo 968591 1638859 := bstep (se 1 (by rfl) ⟨1229144, by rfl⟩ : syracuseStep 1638859 = 2458289) B2458289
theorem B1639001 : Blo 968591 1639001 := bstep (se 2 (by rfl) ⟨614625, by rfl⟩ : syracuseStep 1639001 = 1229251) B1229251
theorem B1770113 : Blo 968591 1770113 := bstep (se 2 (by rfl) ⟨663792, by rfl⟩ : syracuseStep 1770113 = 1327585) B1327585
theorem B3277529 : Blo 968591 3277529 := bstep (se 2 (by rfl) ⟨1229073, by rfl⟩ : syracuseStep 3277529 = 2458147) B2458147
theorem B1639129 : Blo 968591 1639129 := bstep (se 2 (by rfl) ⟨614673, by rfl⟩ : syracuseStep 1639129 = 1229347) B1229347
theorem B5538577 : Blo 968591 5538577 := bstep (se 2 (by rfl) ⟨2076966, by rfl⟩ : syracuseStep 5538577 = 4153933) B4153933
theorem B983831 : Blo 968591 983831 := bstep (se 1 (by rfl) ⟨737873, by rfl⟩ : syracuseStep 983831 = 1475747) B1475747
theorem B1311563 : Blo 968591 1311563 := bstep (se 1 (by rfl) ⟨983672, by rfl⟩ : syracuseStep 1311563 = 1967345) B1967345
theorem B4916375 : Blo 968591 4916375 := bstep (se 1 (by rfl) ⟨3687281, by rfl⟩ : syracuseStep 4916375 = 7374563) B7374563
theorem B2458775 : Blo 968591 2458775 := bstep (se 1 (by rfl) ⟨1844081, by rfl⟩ : syracuseStep 2458775 = 3688163) B3688163
theorem B1639703 : Blo 968591 1639703 := bstep (se 1 (by rfl) ⟨1229777, by rfl⟩ : syracuseStep 1639703 = 2459555) B2459555
theorem B1246603 : Blo 968591 1246603 := bstep (se 1 (by rfl) ⟨934952, by rfl⟩ : syracuseStep 1246603 = 1869905) B1869905
theorem B3278231 : Blo 968591 3278231 := bstep (se 1 (by rfl) ⟨2458673, by rfl⟩ : syracuseStep 3278231 = 4917347) B4917347
theorem B1639831 : Blo 968591 1639831 := bstep (se 1 (by rfl) ⟨1229873, by rfl⟩ : syracuseStep 1639831 = 2459747) B2459747
theorem B8848817 : Blo 968591 8848817 := bstep (se 2 (by rfl) ⟨3318306, by rfl⟩ : syracuseStep 8848817 = 6636613) B6636613
theorem B15926797 : Blo 968591 15926797 := bstep (se 3 (by rfl) ⟨2986274, by rfl⟩ : syracuseStep 15926797 = 5972549) B5972549
theorem B4982347 : Blo 968591 4982347 := bstep (se 1 (by rfl) ⟨3736760, by rfl⟩ : syracuseStep 4982347 = 7473521) B7473521
theorem B984727 : Blo 968591 984727 := bstep (se 1 (by rfl) ⟨738545, by rfl⟩ : syracuseStep 984727 = 1477091) B1477091
theorem B2459443 : Blo 968591 2459443 := bstep (se 1 (by rfl) ⟨1844582, by rfl⟩ : syracuseStep 2459443 = 3689165) B3689165
theorem B3278771 : Blo 968591 3278771 := bstep (se 1 (by rfl) ⟨2459078, by rfl⟩ : syracuseStep 3278771 = 4918157) B4918157
theorem B2459585 : Blo 968591 2459585 := bstep (se 2 (by rfl) ⟨922344, by rfl⟩ : syracuseStep 2459585 = 1844689) B1844689
theorem B1640459 : Blo 968591 1640459 := bstep (se 1 (by rfl) ⟨1230344, by rfl⟩ : syracuseStep 1640459 = 2460689) B2460689
theorem B1640587 : Blo 968591 1640587 := bstep (se 1 (by rfl) ⟨1230440, by rfl⟩ : syracuseStep 1640587 = 2460881) B2460881
theorem B3279041 : Blo 968591 3279041 := bstep (se 2 (by rfl) ⟨1229640, by rfl⟩ : syracuseStep 3279041 = 2459281) B2459281
theorem B8292557 : Blo 968591 8292557 := bstep (se 3 (by rfl) ⟨1554854, by rfl⟩ : syracuseStep 8292557 = 3109709) B3109709
theorem B1640729 : Blo 968591 1640729 := bstep (se 2 (by rfl) ⟨615273, by rfl⟩ : syracuseStep 1640729 = 1230547) B1230547
theorem B1214807 : Blo 968591 1214807 := bstep (se 1 (by rfl) ⟨911105, by rfl⟩ : syracuseStep 1214807 = 1822211) B1822211
theorem B3934595 : Blo 968591 3934595 := bstep (se 1 (by rfl) ⟨2950946, by rfl⟩ : syracuseStep 3934595 = 5901893) B5901893
theorem B1640857 : Blo 968591 1640857 := bstep (se 2 (by rfl) ⟨615321, by rfl⟩ : syracuseStep 1640857 = 1230643) B1230643
theorem B1870273 : Blo 968591 1870273 := bstep (se 2 (by rfl) ⟨701352, by rfl⟩ : syracuseStep 1870273 = 1402705) B1402705
theorem B1870489 : Blo 968591 1870489 := bstep (se 2 (by rfl) ⟨701433, by rfl⟩ : syracuseStep 1870489 = 1402867) B1402867
theorem B6228697 : Blo 968591 6228697 := bstep (se 2 (by rfl) ⟨2335761, by rfl⟩ : syracuseStep 6228697 = 4671523) B4671523
theorem B3279581 : Blo 968591 3279581 := bstep (se 3 (by rfl) ⟨614921, by rfl⟩ : syracuseStep 3279581 = 1229843) B1229843
theorem B2395097 : Blo 968591 2395097 := bstep (se 2 (by rfl) ⟨898161, by rfl⟩ : syracuseStep 2395097 = 1796323) B1796323
theorem B4787275 : Blo 968591 4787275 := bstep (se 1 (by rfl) ⟨3590456, by rfl⟩ : syracuseStep 4787275 = 7180913) B7180913
theorem B17697923 : Blo 968591 17697923 := bstep (se 1 (by rfl) ⟨13273442, by rfl⟩ : syracuseStep 17697923 = 26546885) B26546885
theorem B3935405 : Blo 968591 3935405 := bstep (se 3 (by rfl) ⟨737888, by rfl⟩ : syracuseStep 3935405 = 1475777) B1475777
theorem B2460851 : Blo 968591 2460851 := bstep (se 1 (by rfl) ⟨1845638, by rfl⟩ : syracuseStep 2460851 = 3691277) B3691277
theorem B1871105 : Blo 968591 1871105 := bstep (se 2 (by rfl) ⟨701664, by rfl⟩ : syracuseStep 1871105 = 1403329) B1403329
theorem B3542417 : Blo 968591 3542417 := bstep (se 2 (by rfl) ⟨1328406, by rfl⟩ : syracuseStep 3542417 = 2656813) B2656813
theorem B2952769 : Blo 968591 2952769 := bstep (se 2 (by rfl) ⟨1107288, by rfl⟩ : syracuseStep 2952769 = 2214577) B2214577
theorem B1379929 : Blo 968591 1379929 := bstep (se 2 (by rfl) ⟨517473, by rfl⟩ : syracuseStep 1379929 = 1034947) B1034947
theorem B1478233 : Blo 968591 1478233 := bstep (se 2 (by rfl) ⟨554337, by rfl⟩ : syracuseStep 1478233 = 1108675) B1108675
theorem B2461387 : Blo 968591 2461387 := bstep (se 1 (by rfl) ⟨1846040, by rfl⟩ : syracuseStep 2461387 = 3692081) B3692081
theorem B3280715 : Blo 968591 3280715 := bstep (se 1 (by rfl) ⟨2460536, by rfl⟩ : syracuseStep 3280715 = 4921073) B4921073
theorem B2101081 : Blo 968591 2101081 := bstep (se 2 (by rfl) ⟨787905, by rfl⟩ : syracuseStep 2101081 = 1575811) B1575811
theorem B2461529 : Blo 968591 2461529 := bstep (se 2 (by rfl) ⟨923073, by rfl⟩ : syracuseStep 2461529 = 1846147) B1846147
theorem B1838963 : Blo 968591 1838963 := bstep (se 1 (by rfl) ⟨1379222, by rfl⟩ : syracuseStep 1838963 = 2758445) B2758445
theorem B1839115 : Blo 968591 1839115 := bstep (se 1 (by rfl) ⟨1379336, by rfl⟩ : syracuseStep 1839115 = 2758673) B2758673
theorem B2625625 : Blo 968591 2625625 := bstep (se 2 (by rfl) ⟨984609, by rfl⟩ : syracuseStep 2625625 = 1969219) B1969219
theorem B3280985 : Blo 968591 3280985 := bstep (se 2 (by rfl) ⟨1230369, by rfl⟩ : syracuseStep 3280985 = 2460739) B2460739
theorem B2068697 : Blo 968591 2068697 := bstep (se 2 (by rfl) ⟨775761, by rfl⟩ : syracuseStep 2068697 = 1551523) B1551523
theorem B2953547 : Blo 968591 2953547 := bstep (se 1 (by rfl) ⟨2215160, by rfl⟩ : syracuseStep 2953547 = 4430321) B4430321
theorem B1839449 : Blo 968591 1839449 := bstep (se 2 (by rfl) ⟨689793, by rfl⟩ : syracuseStep 1839449 = 1379587) B1379587
theorem B2069057 : Blo 968591 2069057 := bstep (se 2 (by rfl) ⟨775896, by rfl⟩ : syracuseStep 2069057 = 1551793) B1551793
theorem B3936833 : Blo 968591 3936833 := bstep (se 2 (by rfl) ⟨1476312, by rfl⟩ : syracuseStep 3936833 = 2952625) B2952625
theorem B4919939 : Blo 968591 4919939 := bstep (se 1 (by rfl) ⟨3689954, by rfl⟩ : syracuseStep 4919939 = 7379909) B7379909
theorem B9966341 : Blo 968591 9966341 := bstep (se 4 (by rfl) ⟨934344, by rfl⟩ : syracuseStep 9966341 = 1868689) B1868689
theorem B3281687 : Blo 968591 3281687 := bstep (se 1 (by rfl) ⟨2461265, by rfl⟩ : syracuseStep 3281687 = 4922531) B4922531
theorem B1840087 : Blo 968591 1840087 := bstep (se 1 (by rfl) ⟨1380065, by rfl⟩ : syracuseStep 1840087 = 2760131) B2760131
theorem B1381387 : Blo 968591 1381387 := bstep (se 1 (by rfl) ⟨1036040, by rfl⟩ : syracuseStep 1381387 = 2072081) B2072081
theorem B7377965 : Blo 968591 7377965 := bstep (se 3 (by rfl) ⟨1383368, by rfl⟩ : syracuseStep 7377965 = 2766737) B2766737
theorem B2102465 : Blo 968591 2102465 := bstep (se 2 (by rfl) ⟨788424, by rfl⟩ : syracuseStep 2102465 = 1576849) B1576849
theorem B2069783 : Blo 968591 2069783 := bstep (se 1 (by rfl) ⟨1552337, by rfl⟩ : syracuseStep 2069783 = 3104675) B3104675
theorem B3282227 : Blo 968591 3282227 := bstep (se 1 (by rfl) ⟨2461670, by rfl⟩ : syracuseStep 3282227 = 4923341) B4923341
theorem B2627009 : Blo 968591 2627009 := bstep (se 2 (by rfl) ⟨985128, by rfl⟩ : syracuseStep 2627009 = 1970257) B1970257
theorem B3741149 : Blo 968591 3741149 := bstep (se 3 (by rfl) ⟨701465, by rfl⟩ : syracuseStep 3741149 = 1402931) B1402931
theorem B4658705 : Blo 968591 4658705 := bstep (se 2 (by rfl) ⟨1747014, by rfl⟩ : syracuseStep 4658705 = 3494029) B3494029
theorem B3282497 : Blo 968591 3282497 := bstep (se 2 (by rfl) ⟨1230936, by rfl⟩ : syracuseStep 3282497 = 2461873) B2461873
theorem B1840907 : Blo 968591 1840907 := bstep (se 1 (by rfl) ⟨1380680, by rfl⟩ : syracuseStep 1840907 = 2761361) B2761361
theorem B1840961 : Blo 968591 1840961 := bstep (se 2 (by rfl) ⟨690360, by rfl⟩ : syracuseStep 1840961 = 1380721) B1380721
theorem B3938179 : Blo 968591 3938179 := bstep (se 1 (by rfl) ⟨2953634, by rfl⟩ : syracuseStep 3938179 = 5907269) B5907269
theorem B2103383 : Blo 968591 2103383 := bstep (se 1 (by rfl) ⟨1577537, by rfl⟩ : syracuseStep 2103383 = 3155075) B3155075
theorem B2070679 : Blo 968591 2070679 := bstep (se 1 (by rfl) ⟨1553009, by rfl⟩ : syracuseStep 2070679 = 3106019) B3106019
theorem B1579225 : Blo 968591 1579225 := bstep (se 2 (by rfl) ⟨592209, by rfl⟩ : syracuseStep 1579225 = 1184419) B1184419
theorem B1382617 : Blo 968591 1382617 := bstep (se 2 (by rfl) ⟨518481, by rfl⟩ : syracuseStep 1382617 = 1036963) B1036963
theorem B1776001 : Blo 968591 1776001 := bstep (se 2 (by rfl) ⟨666000, by rfl⟩ : syracuseStep 1776001 = 1332001) B1332001
theorem B2759129 : Blo 968591 2759129 := bstep (se 2 (by rfl) ⟨1034673, by rfl⟩ : syracuseStep 2759129 = 2069347) B2069347
theorem B8395415 : Blo 968591 8395415 := bstep (se 1 (by rfl) ⟨6296561, by rfl⟩ : syracuseStep 8395415 = 12593123) B12593123
theorem B1841879 : Blo 968591 1841879 := bstep (se 1 (by rfl) ⟨1381409, by rfl⟩ : syracuseStep 1841879 = 2762819) B2762819
theorem B2759447 : Blo 968591 2759447 := bstep (se 1 (by rfl) ⟨2069585, by rfl⟩ : syracuseStep 2759447 = 4139171) B4139171
theorem B2071499 : Blo 968591 2071499 := bstep (se 1 (by rfl) ⟨1553624, by rfl⟩ : syracuseStep 2071499 = 3107249) B3107249
theorem B1842419 : Blo 968591 1842419 := bstep (se 1 (by rfl) ⟨1381814, by rfl⟩ : syracuseStep 1842419 = 2763629) B2763629
theorem B5250577 : Blo 968591 5250577 := bstep (se 2 (by rfl) ⟨1968966, by rfl⟩ : syracuseStep 5250577 = 3937933) B3937933
theorem B1383961 : Blo 968591 1383961 := bstep (se 2 (by rfl) ⟨518985, by rfl⟩ : syracuseStep 1383961 = 1037971) B1037971
theorem B2760257 : Blo 968591 2760257 := bstep (se 2 (by rfl) ⟨1035096, by rfl⟩ : syracuseStep 2760257 = 2070193) B2070193
theorem B16555589 : Blo 968591 16555589 := bstep (se 4 (by rfl) ⟨1552086, by rfl⟩ : syracuseStep 16555589 = 3104173) B3104173
theorem B1384075 : Blo 968591 1384075 := bstep (se 1 (by rfl) ⟨1038056, by rfl⟩ : syracuseStep 1384075 = 2076113) B2076113
theorem B2334359 : Blo 968591 2334359 := bstep (se 1 (by rfl) ⟨1750769, by rfl⟩ : syracuseStep 2334359 = 3501539) B3501539
theorem B2072243 : Blo 968591 2072243 := bstep (se 1 (by rfl) ⟨1554182, by rfl⟩ : syracuseStep 2072243 = 3108365) B3108365
theorem B2956979 : Blo 968591 2956979 := bstep (se 1 (by rfl) ⟨2217734, by rfl⟩ : syracuseStep 2956979 = 4435469) B4435469
theorem B1842905 : Blo 968591 1842905 := bstep (se 2 (by rfl) ⟨691089, by rfl⟩ : syracuseStep 1842905 = 1382179) B1382179
theorem B3678155 : Blo 968591 3678155 := bstep (se 1 (by rfl) ⟨2758616, by rfl⟩ : syracuseStep 3678155 = 5517233) B5517233
theorem B3678169 : Blo 968591 3678169 := bstep (se 2 (by rfl) ⟨1379313, by rfl⟩ : syracuseStep 3678169 = 2758627) B2758627
theorem B8298571 : Blo 968591 8298571 := bstep (se 1 (by rfl) ⟨6223928, by rfl⟩ : syracuseStep 8298571 = 12447857) B12447857
theorem B1089751 : Blo 968591 1089751 := bstep (se 1 (by rfl) ⟨817313, by rfl⟩ : syracuseStep 1089751 = 1634627) B1634627
theorem B4923665 : Blo 968591 4923665 := bstep (se 2 (by rfl) ⟨1846374, by rfl⟩ : syracuseStep 4923665 = 3692749) B3692749
theorem B8298845 : Blo 968591 8298845 := bstep (se 3 (by rfl) ⟨1556033, by rfl⟩ : syracuseStep 8298845 = 3112067) B3112067
theorem B1089931 : Blo 968591 1089931 := bstep (se 1 (by rfl) ⟨817448, by rfl⟩ : syracuseStep 1089931 = 1634897) B1634897
theorem B27959701 : Blo 968591 27959701 := bstep (se 6 (by rfl) ⟨655305, by rfl⟩ : syracuseStep 27959701 = 1310611) B1310611
theorem B7971223 : Blo 968591 7971223 := bstep (se 1 (by rfl) ⟨5978417, by rfl⟩ : syracuseStep 7971223 = 11956835) B11956835
theorem B3940787 : Blo 968591 3940787 := bstep (se 1 (by rfl) ⟨2955590, by rfl⟩ : syracuseStep 3940787 = 5911181) B5911181
theorem B1090039 : Blo 968591 1090039 := bstep (se 1 (by rfl) ⟨817529, by rfl⟩ : syracuseStep 1090039 = 1635059) B1635059
theorem B2073089 : Blo 968591 2073089 := bstep (se 2 (by rfl) ⟨777408, by rfl⟩ : syracuseStep 2073089 = 1554817) B1554817
theorem B11969059 : Blo 968591 11969059 := bstep (se 1 (by rfl) ⟨8976794, by rfl⟩ : syracuseStep 11969059 = 17953589) B17953589
theorem B1090219 : Blo 968591 1090219 := bstep (se 1 (by rfl) ⟨817664, by rfl⟩ : syracuseStep 1090219 = 1635329) B1635329
theorem B3941081 : Blo 968591 3941081 := bstep (se 2 (by rfl) ⟨1477905, by rfl⟩ : syracuseStep 3941081 = 2955811) B2955811
theorem B1090327 : Blo 968591 1090327 := bstep (se 1 (by rfl) ⟨817745, by rfl⟩ : syracuseStep 1090327 = 1635491) B1635491
theorem B2335511 : Blo 968591 2335511 := bstep (se 1 (by rfl) ⟨1751633, by rfl⟩ : syracuseStep 2335511 = 3503267) B3503267
theorem B2073431 : Blo 968591 2073431 := bstep (se 1 (by rfl) ⟨1555073, by rfl⟩ : syracuseStep 2073431 = 3110147) B3110147
theorem B7381853 : Blo 968591 7381853 := bstep (se 3 (by rfl) ⟨1384097, by rfl⟩ : syracuseStep 7381853 = 2768195) B2768195
theorem B1745803 : Blo 968591 1745803 := bstep (se 1 (by rfl) ⟨1309352, by rfl⟩ : syracuseStep 1745803 = 2618705) B2618705
theorem B3679127 : Blo 968591 3679127 := bstep (se 1 (by rfl) ⟨2759345, by rfl⟩ : syracuseStep 3679127 = 5518691) B5518691
theorem B12460979 : Blo 968591 12460979 := bstep (se 1 (by rfl) ⟨9345734, by rfl⟩ : syracuseStep 12460979 = 18691469) B18691469
theorem B1745867 : Blo 968591 1745867 := bstep (se 1 (by rfl) ⟨1309400, by rfl⟩ : syracuseStep 1745867 = 2618801) B2618801
theorem B1090507 : Blo 968591 1090507 := bstep (se 1 (by rfl) ⟨817880, by rfl⟩ : syracuseStep 1090507 = 1635761) B1635761
theorem B1090615 : Blo 968591 1090615 := bstep (se 1 (by rfl) ⟨817961, by rfl⟩ : syracuseStep 1090615 = 1635923) B1635923
theorem B2335819 : Blo 968591 2335819 := bstep (se 1 (by rfl) ⟨1751864, by rfl⟩ : syracuseStep 2335819 = 3503729) B3503729
theorem B1844363 : Blo 968591 1844363 := bstep (se 1 (by rfl) ⟨1383272, by rfl⟩ : syracuseStep 1844363 = 2766545) B2766545
theorem B2761931 : Blo 968591 2761931 := bstep (se 1 (by rfl) ⟨2071448, by rfl⟩ : syracuseStep 2761931 = 4142897) B4142897
theorem B1090795 : Blo 968591 1090795 := bstep (se 1 (by rfl) ⟨818096, by rfl⟩ : syracuseStep 1090795 = 1636193) B1636193
theorem B1844545 : Blo 968591 1844545 := bstep (se 2 (by rfl) ⟨691704, by rfl⟩ : syracuseStep 1844545 = 1383409) B1383409
theorem B1090903 : Blo 968591 1090903 := bstep (se 1 (by rfl) ⟨818177, by rfl⟩ : syracuseStep 1090903 = 1636355) B1636355
theorem B8299907 : Blo 968591 8299907 := bstep (se 1 (by rfl) ⟨6224930, by rfl⟩ : syracuseStep 8299907 = 12449861) B12449861
theorem B1091083 : Blo 968591 1091083 := bstep (se 1 (by rfl) ⟨818312, by rfl⟩ : syracuseStep 1091083 = 1636625) B1636625
theorem B1091191 : Blo 968591 1091191 := bstep (se 1 (by rfl) ⟨818393, by rfl⟩ : syracuseStep 1091191 = 1636787) B1636787
theorem B5252825 : Blo 968591 5252825 := bstep (se 2 (by rfl) ⟨1969809, by rfl⟩ : syracuseStep 5252825 = 3939619) B3939619
theorem B1844993 : Blo 968591 1844993 := bstep (se 2 (by rfl) ⟨691872, by rfl⟩ : syracuseStep 1844993 = 1383745) B1383745
theorem B1091371 : Blo 968591 1091371 := bstep (se 1 (by rfl) ⟨818528, by rfl⟩ : syracuseStep 1091371 = 1637057) B1637057
theorem B4138883 : Blo 968591 4138883 := bstep (se 1 (by rfl) ⟨3104162, by rfl⟩ : syracuseStep 4138883 = 6208325) B6208325
theorem B1091479 : Blo 968591 1091479 := bstep (se 1 (by rfl) ⟨818609, by rfl⟩ : syracuseStep 1091479 = 1637219) B1637219
theorem B1746841 : Blo 968591 1746841 := bstep (se 2 (by rfl) ⟨655065, by rfl⟩ : syracuseStep 1746841 = 1310131) B1310131
theorem B1746905 : Blo 968591 1746905 := bstep (se 2 (by rfl) ⟨655089, by rfl⟩ : syracuseStep 1746905 = 1310179) B1310179
theorem B1091659 : Blo 968591 1091659 := bstep (se 1 (by rfl) ⟨818744, by rfl⟩ : syracuseStep 1091659 = 1637489) B1637489
theorem B1845335 : Blo 968591 1845335 := bstep (se 1 (by rfl) ⟨1384001, by rfl⟩ : syracuseStep 1845335 = 2768003) B2768003
theorem B3680387 : Blo 968591 3680387 := bstep (se 1 (by rfl) ⟨2760290, by rfl⟩ : syracuseStep 3680387 = 5520581) B5520581
theorem B1091767 : Blo 968591 1091767 := bstep (se 1 (by rfl) ⟨818825, by rfl⟩ : syracuseStep 1091767 = 1637651) B1637651
theorem B13805923 : Blo 968591 13805923 := bstep (se 1 (by rfl) ⟨10354442, by rfl⟩ : syracuseStep 13805923 = 20708885) B20708885
theorem B1091947 : Blo 968591 1091947 := bstep (se 1 (by rfl) ⟨818960, by rfl⟩ : syracuseStep 1091947 = 1637921) B1637921
theorem B1092055 : Blo 968591 1092055 := bstep (se 1 (by rfl) ⟨819041, by rfl⟩ : syracuseStep 1092055 = 1638083) B1638083
theorem B2763229 : Blo 968591 2763229 := bstep (se 3 (by rfl) ⟨518105, by rfl⟩ : syracuseStep 2763229 = 1036211) B1036211
theorem B1092235 : Blo 968591 1092235 := bstep (se 1 (by rfl) ⟨819176, by rfl⟩ : syracuseStep 1092235 = 1638353) B1638353
theorem B1747649 : Blo 968591 1747649 := bstep (se 2 (by rfl) ⟨655368, by rfl⟩ : syracuseStep 1747649 = 1310737) B1310737
theorem B1846003 : Blo 968591 1846003 := bstep (se 1 (by rfl) ⟨1384502, by rfl⟩ : syracuseStep 1846003 = 2769005) B2769005
theorem B1092343 : Blo 968591 1092343 := bstep (se 1 (by rfl) ⟨819257, by rfl⟩ : syracuseStep 1092343 = 1638515) B1638515
theorem B2763571 : Blo 968591 2763571 := bstep (se 1 (by rfl) ⟨2072678, by rfl⟩ : syracuseStep 2763571 = 4145357) B4145357
theorem B1452887 : Blo 968591 1452887 := bstep (se 1 (by rfl) ⟨1089665, by rfl⟩ : syracuseStep 1452887 = 2179331) B2179331
theorem B1452953 : Blo 968591 1452953 := bstep (se 2 (by rfl) ⟨544857, by rfl⟩ : syracuseStep 1452953 = 1089715) B1089715
theorem B1092523 : Blo 968591 1092523 := bstep (se 1 (by rfl) ⟨819392, by rfl⟩ : syracuseStep 1092523 = 1638785) B1638785
theorem B1453067 : Blo 968591 1453067 := bstep (se 1 (by rfl) ⟨1089800, by rfl⟩ : syracuseStep 1453067 = 2179601) B2179601
theorem B1453079 : Blo 968591 1453079 := bstep (se 1 (by rfl) ⟨1089809, by rfl⟩ : syracuseStep 1453079 = 2179619) B2179619
theorem B1092631 : Blo 968591 1092631 := bstep (se 1 (by rfl) ⟨819473, by rfl⟩ : syracuseStep 1092631 = 1638947) B1638947
theorem B1453145 : Blo 968591 1453145 := bstep (se 2 (by rfl) ⟨544929, by rfl⟩ : syracuseStep 1453145 = 1089859) B1089859
theorem B1453259 : Blo 968591 1453259 := bstep (se 1 (by rfl) ⟨1089944, by rfl⟩ : syracuseStep 1453259 = 2179889) B2179889
theorem B1092811 : Blo 968591 1092811 := bstep (se 1 (by rfl) ⟨819608, by rfl⟩ : syracuseStep 1092811 = 1639217) B1639217
theorem B1453271 : Blo 968591 1453271 := bstep (se 1 (by rfl) ⟨1089953, by rfl⟩ : syracuseStep 1453271 = 2179907) B2179907
theorem B1453337 : Blo 968591 1453337 := bstep (se 2 (by rfl) ⟨545001, by rfl⟩ : syracuseStep 1453337 = 1090003) B1090003
theorem B1092919 : Blo 968591 1092919 := bstep (se 1 (by rfl) ⟨819689, by rfl⟩ : syracuseStep 1092919 = 1639379) B1639379
theorem B2796865 : Blo 968591 2796865 := bstep (se 2 (by rfl) ⟨1048824, by rfl⟩ : syracuseStep 2796865 = 2097649) B2097649
theorem B1453451 : Blo 968591 1453451 := bstep (se 1 (by rfl) ⟨1090088, by rfl⟩ : syracuseStep 1453451 = 2180177) B2180177
theorem B1453463 : Blo 968591 1453463 := bstep (se 1 (by rfl) ⟨1090097, by rfl⟩ : syracuseStep 1453463 = 2180195) B2180195
theorem B1453529 : Blo 968591 1453529 := bstep (se 2 (by rfl) ⟨545073, by rfl⟩ : syracuseStep 1453529 = 1090147) B1090147
theorem B1093099 : Blo 968591 1093099 := bstep (se 1 (by rfl) ⟨819824, by rfl⟩ : syracuseStep 1093099 = 1639649) B1639649
theorem B1453643 : Blo 968591 1453643 := bstep (se 1 (by rfl) ⟨1090232, by rfl⟩ : syracuseStep 1453643 = 2180465) B2180465
theorem B1453655 : Blo 968591 1453655 := bstep (se 1 (by rfl) ⟨1090241, by rfl⟩ : syracuseStep 1453655 = 2180483) B2180483
theorem B1093207 : Blo 968591 1093207 := bstep (se 1 (by rfl) ⟨819905, by rfl⟩ : syracuseStep 1093207 = 1639811) B1639811
theorem B1453721 : Blo 968591 1453721 := bstep (se 2 (by rfl) ⟨545145, by rfl⟩ : syracuseStep 1453721 = 1090291) B1090291
theorem B2764505 : Blo 968591 2764505 := bstep (se 2 (by rfl) ⟨1036689, by rfl⟩ : syracuseStep 2764505 = 2073379) B2073379
theorem B1453835 : Blo 968591 1453835 := bstep (se 1 (by rfl) ⟨1090376, by rfl⟩ : syracuseStep 1453835 = 2180753) B2180753
theorem B1093387 : Blo 968591 1093387 := bstep (se 1 (by rfl) ⟨820040, by rfl⟩ : syracuseStep 1093387 = 1640081) B1640081
theorem B1453847 : Blo 968591 1453847 := bstep (se 1 (by rfl) ⟨1090385, by rfl⟩ : syracuseStep 1453847 = 2180771) B2180771
theorem B1453913 : Blo 968591 1453913 := bstep (se 2 (by rfl) ⟨545217, by rfl⟩ : syracuseStep 1453913 = 1090435) B1090435
theorem B1093495 : Blo 968591 1093495 := bstep (se 1 (by rfl) ⟨820121, by rfl⟩ : syracuseStep 1093495 = 1640243) B1640243
theorem B1454027 : Blo 968591 1454027 := bstep (se 1 (by rfl) ⟨1090520, by rfl⟩ : syracuseStep 1454027 = 2181041) B2181041
theorem B1552343 : Blo 968591 1552343 := bstep (se 1 (by rfl) ⟨1164257, by rfl⟩ : syracuseStep 1552343 = 2328515) B2328515
theorem B1454039 : Blo 968591 1454039 := bstep (se 1 (by rfl) ⟨1090529, by rfl⟩ : syracuseStep 1454039 = 2181059) B2181059
theorem B11972569 : Blo 968591 11972569 := bstep (se 2 (by rfl) ⟨4489713, by rfl⟩ : syracuseStep 11972569 = 8979427) B8979427
theorem B1454105 : Blo 968591 1454105 := bstep (se 2 (by rfl) ⟨545289, by rfl⟩ : syracuseStep 1454105 = 1090579) B1090579
theorem B1093675 : Blo 968591 1093675 := bstep (se 1 (by rfl) ⟨820256, by rfl⟩ : syracuseStep 1093675 = 1640513) B1640513
theorem B1552459 : Blo 968591 1552459 := bstep (se 1 (by rfl) ⟨1164344, by rfl⟩ : syracuseStep 1552459 = 2328689) B2328689
theorem B1454219 : Blo 968591 1454219 := bstep (se 1 (by rfl) ⟨1090664, by rfl⟩ : syracuseStep 1454219 = 2181329) B2181329
theorem B1454231 : Blo 968591 1454231 := bstep (se 1 (by rfl) ⟨1090673, by rfl⟩ : syracuseStep 1454231 = 2181347) B2181347
theorem B1093783 : Blo 968591 1093783 := bstep (se 1 (by rfl) ⟨820337, by rfl⟩ : syracuseStep 1093783 = 1640675) B1640675
theorem B1454297 : Blo 968591 1454297 := bstep (se 2 (by rfl) ⟨545361, by rfl⟩ : syracuseStep 1454297 = 1090723) B1090723
theorem B1454411 : Blo 968591 1454411 := bstep (se 1 (by rfl) ⟨1090808, by rfl⟩ : syracuseStep 1454411 = 2181617) B2181617
theorem B1093963 : Blo 968591 1093963 := bstep (se 1 (by rfl) ⟨820472, by rfl⟩ : syracuseStep 1093963 = 1640945) B1640945
theorem B1454423 : Blo 968591 1454423 := bstep (se 1 (by rfl) ⟨1090817, by rfl⟩ : syracuseStep 1454423 = 2181635) B2181635
theorem B59683189 : Blo 968591 59683189 := bstep (se 5 (by rfl) ⟨2797649, by rfl⟩ : syracuseStep 59683189 = 5595299) B5595299
theorem B1454489 : Blo 968591 1454489 := bstep (se 2 (by rfl) ⟨545433, by rfl⟩ : syracuseStep 1454489 = 1090867) B1090867
theorem B1094071 : Blo 968591 1094071 := bstep (se 1 (by rfl) ⟨820553, by rfl⟩ : syracuseStep 1094071 = 1641107) B1641107
theorem B1454603 : Blo 968591 1454603 := bstep (se 1 (by rfl) ⟨1090952, by rfl⟩ : syracuseStep 1454603 = 2181905) B2181905
theorem B1454615 : Blo 968591 1454615 := bstep (se 1 (by rfl) ⟨1090961, by rfl⟩ : syracuseStep 1454615 = 2181923) B2181923
theorem B1749529 : Blo 968591 1749529 := bstep (se 2 (by rfl) ⟨656073, by rfl⟩ : syracuseStep 1749529 = 1312147) B1312147
theorem B1454681 : Blo 968591 1454681 := bstep (se 2 (by rfl) ⟨545505, by rfl⟩ : syracuseStep 1454681 = 1091011) B1091011
theorem B1454795 : Blo 968591 1454795 := bstep (se 1 (by rfl) ⟨1091096, by rfl⟩ : syracuseStep 1454795 = 2182193) B2182193
theorem B1454807 : Blo 968591 1454807 := bstep (se 1 (by rfl) ⟨1091105, by rfl⟩ : syracuseStep 1454807 = 2182211) B2182211
theorem B1553177 : Blo 968591 1553177 := bstep (se 2 (by rfl) ⟨582441, by rfl⟩ : syracuseStep 1553177 = 1164883) B1164883
theorem B1454873 : Blo 968591 1454873 := bstep (se 2 (by rfl) ⟨545577, by rfl⟩ : syracuseStep 1454873 = 1091155) B1091155
theorem B5256029 : Blo 968591 5256029 := bstep (se 3 (by rfl) ⟨985505, by rfl⟩ : syracuseStep 5256029 = 1971011) B1971011
theorem B1454987 : Blo 968591 1454987 := bstep (se 1 (by rfl) ⟨1091240, by rfl⟩ : syracuseStep 1454987 = 2182481) B2182481
theorem B1454999 : Blo 968591 1454999 := bstep (se 1 (by rfl) ⟨1091249, by rfl⟩ : syracuseStep 1454999 = 2182499) B2182499
theorem B2339777 : Blo 968591 2339777 := bstep (se 2 (by rfl) ⟨877416, by rfl⟩ : syracuseStep 2339777 = 1754833) B1754833
theorem B1455065 : Blo 968591 1455065 := bstep (se 2 (by rfl) ⟨545649, by rfl⟩ : syracuseStep 1455065 = 1091299) B1091299
theorem B1455179 : Blo 968591 1455179 := bstep (se 1 (by rfl) ⟨1091384, by rfl⟩ : syracuseStep 1455179 = 2182769) B2182769
theorem B1455191 : Blo 968591 1455191 := bstep (se 1 (by rfl) ⟨1091393, by rfl⟩ : syracuseStep 1455191 = 2182787) B2182787
theorem B2765917 : Blo 968591 2765917 := bstep (se 3 (by rfl) ⟨518609, by rfl⟩ : syracuseStep 2765917 = 1037219) B1037219
theorem B1455257 : Blo 968591 1455257 := bstep (se 2 (by rfl) ⟨545721, by rfl⟩ : syracuseStep 1455257 = 1091443) B1091443
theorem B3683501 : Blo 968591 3683501 := bstep (se 3 (by rfl) ⟨690656, by rfl⟩ : syracuseStep 3683501 = 1381313) B1381313
theorem B1455371 : Blo 968591 1455371 := bstep (se 1 (by rfl) ⟨1091528, by rfl⟩ : syracuseStep 1455371 = 2183057) B2183057
theorem B1455383 : Blo 968591 1455383 := bstep (se 1 (by rfl) ⟨1091537, by rfl⟩ : syracuseStep 1455383 = 2183075) B2183075
theorem B1553689 : Blo 968591 1553689 := bstep (se 2 (by rfl) ⟨582633, by rfl⟩ : syracuseStep 1553689 = 1165267) B1165267
theorem B1750337 : Blo 968591 1750337 := bstep (se 2 (by rfl) ⟨656376, by rfl⟩ : syracuseStep 1750337 = 1312753) B1312753
theorem B2766145 : Blo 968591 2766145 := bstep (se 2 (by rfl) ⟨1037304, by rfl⟩ : syracuseStep 2766145 = 2074609) B2074609
theorem B1455449 : Blo 968591 1455449 := bstep (se 2 (by rfl) ⟨545793, by rfl⟩ : syracuseStep 1455449 = 1091587) B1091587
theorem B4208051 : Blo 968591 4208051 := bstep (se 1 (by rfl) ⟨3156038, by rfl⟩ : syracuseStep 4208051 = 6312077) B6312077
theorem B1455563 : Blo 968591 1455563 := bstep (se 1 (by rfl) ⟨1091672, by rfl⟩ : syracuseStep 1455563 = 2183345) B2183345
theorem B1455575 : Blo 968591 1455575 := bstep (se 1 (by rfl) ⟨1091681, by rfl⟩ : syracuseStep 1455575 = 2183363) B2183363
theorem B1455641 : Blo 968591 1455641 := bstep (se 2 (by rfl) ⟨545865, by rfl⟩ : syracuseStep 1455641 = 1091731) B1091731
theorem B4142657 : Blo 968591 4142657 := bstep (se 2 (by rfl) ⟨1553496, by rfl⟩ : syracuseStep 4142657 = 3106993) B3106993
theorem B1455755 : Blo 968591 1455755 := bstep (se 1 (by rfl) ⟨1091816, by rfl⟩ : syracuseStep 1455755 = 2183633) B2183633
theorem B1455767 : Blo 968591 1455767 := bstep (se 1 (by rfl) ⟨1091825, by rfl⟩ : syracuseStep 1455767 = 2183651) B2183651
theorem B2766487 : Blo 968591 2766487 := bstep (se 1 (by rfl) ⟨2074865, by rfl⟩ : syracuseStep 2766487 = 4149731) B4149731
theorem B1455833 : Blo 968591 1455833 := bstep (se 2 (by rfl) ⟨545937, by rfl⟩ : syracuseStep 1455833 = 1091875) B1091875
theorem B1455947 : Blo 968591 1455947 := bstep (se 1 (by rfl) ⟨1091960, by rfl⟩ : syracuseStep 1455947 = 2183921) B2183921
theorem B1455959 : Blo 968591 1455959 := bstep (se 1 (by rfl) ⟨1091969, by rfl⟩ : syracuseStep 1455959 = 2183939) B2183939
theorem B1456025 : Blo 968591 1456025 := bstep (se 2 (by rfl) ⟨546009, by rfl⟩ : syracuseStep 1456025 = 1092019) B1092019
theorem B3684275 : Blo 968591 3684275 := bstep (se 1 (by rfl) ⟨2763206, by rfl⟩ : syracuseStep 3684275 = 5526413) B5526413
theorem B1456139 : Blo 968591 1456139 := bstep (se 1 (by rfl) ⟨1092104, by rfl⟩ : syracuseStep 1456139 = 2184209) B2184209
theorem B1456151 : Blo 968591 1456151 := bstep (se 1 (by rfl) ⟨1092113, by rfl⟩ : syracuseStep 1456151 = 2184227) B2184227
theorem B6993965 : Blo 968591 6993965 := bstep (se 3 (by rfl) ⟨1311368, by rfl⟩ : syracuseStep 6993965 = 2622737) B2622737
theorem B2275415 : Blo 968591 2275415 := bstep (se 1 (by rfl) ⟨1706561, by rfl⟩ : syracuseStep 2275415 = 3413123) B3413123
theorem B1456217 : Blo 968591 1456217 := bstep (se 2 (by rfl) ⟨546081, by rfl⟩ : syracuseStep 1456217 = 1092163) B1092163
theorem B1456331 : Blo 968591 1456331 := bstep (se 1 (by rfl) ⟨1092248, by rfl⟩ : syracuseStep 1456331 = 2184497) B2184497
theorem B1456343 : Blo 968591 1456343 := bstep (se 1 (by rfl) ⟨1092257, by rfl⟩ : syracuseStep 1456343 = 2184515) B2184515
theorem B2210071 : Blo 968591 2210071 := bstep (se 1 (by rfl) ⟨1657553, by rfl⟩ : syracuseStep 2210071 = 3315107) B3315107
theorem B1456409 : Blo 968591 1456409 := bstep (se 2 (by rfl) ⟨546153, by rfl⟩ : syracuseStep 1456409 = 1092307) B1092307
theorem B2767193 : Blo 968591 2767193 := bstep (se 2 (by rfl) ⟨1037697, by rfl⟩ : syracuseStep 2767193 = 2075395) B2075395
theorem B1456523 : Blo 968591 1456523 := bstep (se 1 (by rfl) ⟨1092392, by rfl⟩ : syracuseStep 1456523 = 2184785) B2184785
theorem B1456535 : Blo 968591 1456535 := bstep (se 1 (by rfl) ⟨1092401, by rfl⟩ : syracuseStep 1456535 = 2184803) B2184803
theorem B1456601 : Blo 968591 1456601 := bstep (se 2 (by rfl) ⟨546225, by rfl⟩ : syracuseStep 1456601 = 1092451) B1092451
theorem B4143581 : Blo 968591 4143581 := bstep (se 3 (by rfl) ⟨776921, by rfl⟩ : syracuseStep 4143581 = 1553843) B1553843
theorem B1456715 : Blo 968591 1456715 := bstep (se 1 (by rfl) ⟨1092536, by rfl⟩ : syracuseStep 1456715 = 2185073) B2185073
theorem B1456727 : Blo 968591 1456727 := bstep (se 1 (by rfl) ⟨1092545, by rfl⟩ : syracuseStep 1456727 = 2185091) B2185091
theorem B1227403 : Blo 968591 1227403 := bstep (se 1 (by rfl) ⟨920552, by rfl⟩ : syracuseStep 1227403 = 1841105) B1841105
theorem B1456793 : Blo 968591 1456793 := bstep (se 2 (by rfl) ⟨546297, by rfl⟩ : syracuseStep 1456793 = 1092595) B1092595
theorem B1456907 : Blo 968591 1456907 := bstep (se 1 (by rfl) ⟨1092680, by rfl⟩ : syracuseStep 1456907 = 2185361) B2185361
theorem B1456919 : Blo 968591 1456919 := bstep (se 1 (by rfl) ⟨1092689, by rfl⟩ : syracuseStep 1456919 = 2185379) B2185379
theorem B1456985 : Blo 968591 1456985 := bstep (se 2 (by rfl) ⟨546369, by rfl⟩ : syracuseStep 1456985 = 1092739) B1092739
theorem B1457099 : Blo 968591 1457099 := bstep (se 1 (by rfl) ⟨1092824, by rfl⟩ : syracuseStep 1457099 = 2185649) B2185649
theorem B1457111 : Blo 968591 1457111 := bstep (se 1 (by rfl) ⟨1092833, by rfl⟩ : syracuseStep 1457111 = 2185667) B2185667
theorem B1457177 : Blo 968591 1457177 := bstep (se 2 (by rfl) ⟨546441, by rfl⟩ : syracuseStep 1457177 = 1092883) B1092883
theorem B1457291 : Blo 968591 1457291 := bstep (se 1 (by rfl) ⟨1092968, by rfl⟩ : syracuseStep 1457291 = 2185937) B2185937
theorem B1457303 : Blo 968591 1457303 := bstep (se 1 (by rfl) ⟨1092977, by rfl⟩ : syracuseStep 1457303 = 2185955) B2185955
theorem B7355609 : Blo 968591 7355609 := bstep (se 2 (by rfl) ⟨2758353, by rfl⟩ : syracuseStep 7355609 = 5516707) B5516707
theorem B1457369 : Blo 968591 1457369 := bstep (se 2 (by rfl) ⟨546513, by rfl⟩ : syracuseStep 1457369 = 1093027) B1093027
theorem B1457483 : Blo 968591 1457483 := bstep (se 1 (by rfl) ⟨1093112, by rfl⟩ : syracuseStep 1457483 = 2186225) B2186225
theorem B1457495 : Blo 968591 1457495 := bstep (se 1 (by rfl) ⟨1093121, by rfl⟩ : syracuseStep 1457495 = 2186243) B2186243
theorem B3685763 : Blo 968591 3685763 := bstep (se 1 (by rfl) ⟨2764322, by rfl⟩ : syracuseStep 3685763 = 5528645) B5528645
theorem B1457561 : Blo 968591 1457561 := bstep (se 2 (by rfl) ⟨546585, by rfl⟩ : syracuseStep 1457561 = 1093171) B1093171
theorem B1457675 : Blo 968591 1457675 := bstep (se 1 (by rfl) ⟨1093256, by rfl⟩ : syracuseStep 1457675 = 2186513) B2186513
theorem B1457687 : Blo 968591 1457687 := bstep (se 1 (by rfl) ⟨1093265, by rfl⟩ : syracuseStep 1457687 = 2186531) B2186531
theorem B1228375 : Blo 968591 1228375 := bstep (se 1 (by rfl) ⟨921281, by rfl⟩ : syracuseStep 1228375 = 1842563) B1842563
theorem B1457753 : Blo 968591 1457753 := bstep (se 2 (by rfl) ⟨546657, by rfl⟩ : syracuseStep 1457753 = 1093315) B1093315
theorem B28393091 : Blo 968591 28393091 := bstep (se 1 (by rfl) ⟨21294818, by rfl⟩ : syracuseStep 28393091 = 42589637) B42589637
theorem B1457867 : Blo 968591 1457867 := bstep (se 1 (by rfl) ⟨1093400, by rfl⟩ : syracuseStep 1457867 = 2186801) B2186801
theorem B1457879 : Blo 968591 1457879 := bstep (se 1 (by rfl) ⟨1093409, by rfl⟩ : syracuseStep 1457879 = 2186819) B2186819
theorem B1457945 : Blo 968591 1457945 := bstep (se 2 (by rfl) ⟨546729, by rfl⟩ : syracuseStep 1457945 = 1093459) B1093459
theorem B3686219 : Blo 968591 3686219 := bstep (se 1 (by rfl) ⟨2764664, by rfl⟩ : syracuseStep 3686219 = 5529329) B5529329
theorem B1458059 : Blo 968591 1458059 := bstep (se 1 (by rfl) ⟨1093544, by rfl⟩ : syracuseStep 1458059 = 2187089) B2187089
theorem B1458071 : Blo 968591 1458071 := bstep (se 1 (by rfl) ⟨1093553, by rfl⟩ : syracuseStep 1458071 = 2187107) B2187107
theorem B2768833 : Blo 968591 2768833 := bstep (se 2 (by rfl) ⟨1038312, by rfl⟩ : syracuseStep 2768833 = 2076625) B2076625
theorem B1458137 : Blo 968591 1458137 := bstep (se 2 (by rfl) ⟨546801, by rfl⟩ : syracuseStep 1458137 = 1093603) B1093603
theorem B3686417 : Blo 968591 3686417 := bstep (se 2 (by rfl) ⟨1382406, by rfl⟩ : syracuseStep 3686417 = 2764813) B2764813
theorem B1458251 : Blo 968591 1458251 := bstep (se 1 (by rfl) ⟨1093688, by rfl⟩ : syracuseStep 1458251 = 2187377) B2187377
theorem B1458263 : Blo 968591 1458263 := bstep (se 1 (by rfl) ⟨1093697, by rfl⟩ : syracuseStep 1458263 = 2187395) B2187395
theorem B1458329 : Blo 968591 1458329 := bstep (se 2 (by rfl) ⟨546873, by rfl⟩ : syracuseStep 1458329 = 1093747) B1093747
theorem B1458443 : Blo 968591 1458443 := bstep (se 1 (by rfl) ⟨1093832, by rfl⟩ : syracuseStep 1458443 = 2187665) B2187665
theorem B1458455 : Blo 968591 1458455 := bstep (se 1 (by rfl) ⟨1093841, by rfl⟩ : syracuseStep 1458455 = 2187683) B2187683
theorem B2179403 : Blo 968591 2179403 := bstep (se 1 (by rfl) ⟨1634552, by rfl⟩ : syracuseStep 2179403 = 3269105) B3269105
theorem B1458521 : Blo 968591 1458521 := bstep (se 2 (by rfl) ⟨546945, by rfl⟩ : syracuseStep 1458521 = 1093891) B1093891
theorem B6209885 : Blo 968591 6209885 := bstep (se 3 (by rfl) ⟨1164353, by rfl⟩ : syracuseStep 6209885 = 2328707) B2328707
theorem B2179457 : Blo 968591 2179457 := bstep (se 2 (by rfl) ⟨817296, by rfl⟩ : syracuseStep 2179457 = 1634593) B1634593
theorem B2212235 : Blo 968591 2212235 := bstep (se 1 (by rfl) ⟨1659176, by rfl⟩ : syracuseStep 2212235 = 3318353) B3318353
theorem B1229195 : Blo 968591 1229195 := bstep (se 1 (by rfl) ⟨921896, by rfl⟩ : syracuseStep 1229195 = 1843793) B1843793
theorem B1458635 : Blo 968591 1458635 := bstep (se 1 (by rfl) ⟨1093976, by rfl⟩ : syracuseStep 1458635 = 2187953) B2187953
theorem B1458647 : Blo 968591 1458647 := bstep (se 1 (by rfl) ⟨1093985, by rfl⟩ : syracuseStep 1458647 = 2187971) B2187971
theorem B1458713 : Blo 968591 1458713 := bstep (se 2 (by rfl) ⟨547017, by rfl⟩ : syracuseStep 1458713 = 1094035) B1094035
theorem B2179673 : Blo 968591 2179673 := bstep (se 2 (by rfl) ⟨817377, by rfl⟩ : syracuseStep 2179673 = 1634755) B1634755
theorem B1458827 : Blo 968591 1458827 := bstep (se 1 (by rfl) ⟨1094120, by rfl⟩ : syracuseStep 1458827 = 2188241) B2188241
theorem B1458839 : Blo 968591 1458839 := bstep (se 1 (by rfl) ⟨1094129, by rfl⟩ : syracuseStep 1458839 = 2188259) B2188259
theorem B2179763 : Blo 968591 2179763 := bstep (se 1 (by rfl) ⟨1634822, by rfl⟩ : syracuseStep 2179763 = 3269645) B3269645
theorem B2179799 : Blo 968591 2179799 := bstep (se 1 (by rfl) ⟨1634849, by rfl⟩ : syracuseStep 2179799 = 3269699) B3269699
theorem B3687191 : Blo 968591 3687191 := bstep (se 1 (by rfl) ⟨2765393, by rfl⟩ : syracuseStep 3687191 = 5530787) B5530787
theorem B2179979 : Blo 968591 2179979 := bstep (se 1 (by rfl) ⟨1634984, by rfl⟩ : syracuseStep 2179979 = 3269969) B3269969
theorem B2180033 : Blo 968591 2180033 := bstep (se 2 (by rfl) ⟨817512, by rfl⟩ : syracuseStep 2180033 = 1635025) B1635025
theorem B1557463 : Blo 968591 1557463 := bstep (se 1 (by rfl) ⟨1168097, by rfl⟩ : syracuseStep 1557463 = 2336195) B2336195
theorem B3687389 : Blo 968591 3687389 := bstep (se 3 (by rfl) ⟨691385, by rfl⟩ : syracuseStep 3687389 = 1382771) B1382771
theorem B1229899 : Blo 968591 1229899 := bstep (se 1 (by rfl) ⟨922424, by rfl⟩ : syracuseStep 1229899 = 1844849) B1844849
theorem B2180249 : Blo 968591 2180249 := bstep (se 2 (by rfl) ⟨817593, by rfl⟩ : syracuseStep 2180249 = 1635187) B1635187
theorem B2180339 : Blo 968591 2180339 := bstep (se 1 (by rfl) ⟨1635254, by rfl⟩ : syracuseStep 2180339 = 3270509) B3270509
theorem B47301893 : Blo 968591 47301893 := bstep (se 4 (by rfl) ⟨4434552, by rfl⟩ : syracuseStep 47301893 = 8869105) B8869105
theorem B2180375 : Blo 968591 2180375 := bstep (se 1 (by rfl) ⟨1635281, by rfl⟩ : syracuseStep 2180375 = 3270563) B3270563
theorem B1230167 : Blo 968591 1230167 := bstep (se 1 (by rfl) ⟨922625, by rfl⟩ : syracuseStep 1230167 = 1845251) B1845251
theorem B2180555 : Blo 968591 2180555 := bstep (se 1 (by rfl) ⟨1635416, by rfl⟩ : syracuseStep 2180555 = 3270833) B3270833
theorem B2180609 : Blo 968591 2180609 := bstep (se 2 (by rfl) ⟨817728, by rfl⟩ : syracuseStep 2180609 = 1635457) B1635457
theorem B2180825 : Blo 968591 2180825 := bstep (se 2 (by rfl) ⟨817809, by rfl⟩ : syracuseStep 2180825 = 1635619) B1635619
theorem B4146947 : Blo 968591 4146947 := bstep (se 1 (by rfl) ⟨3110210, by rfl⟩ : syracuseStep 4146947 = 6220421) B6220421
theorem B2180915 : Blo 968591 2180915 := bstep (se 1 (by rfl) ⟨1635686, by rfl⟩ : syracuseStep 2180915 = 3271373) B3271373
theorem B2180951 : Blo 968591 2180951 := bstep (se 1 (by rfl) ⟨1635713, by rfl⟩ : syracuseStep 2180951 = 3271427) B3271427
theorem B3491677 : Blo 968591 3491677 := bstep (se 3 (by rfl) ⟨654689, by rfl⟩ : syracuseStep 3491677 = 1309379) B1309379
theorem B968599 : Blo 968591 968599 := bstep (se 1 (by rfl) ⟨726449, by rfl⟩ : syracuseStep 968599 = 1452899) B1452899
theorem B968619 : Blo 968591 968619 := bstep (se 1 (by rfl) ⟨726464, by rfl⟩ : syracuseStep 968619 = 1452929) B1452929
theorem B968631 : Blo 968591 968631 := bstep (se 1 (by rfl) ⟨726473, by rfl⟩ : syracuseStep 968631 = 1452947) B1452947
theorem B968651 : Blo 968591 968651 := bstep (se 1 (by rfl) ⟨726488, by rfl⟩ : syracuseStep 968651 = 1452977) B1452977
theorem B968663 : Blo 968591 968663 := bstep (se 1 (by rfl) ⟨726497, by rfl⟩ : syracuseStep 968663 = 1452995) B1452995
theorem B968683 : Blo 968591 968683 := bstep (se 1 (by rfl) ⟨726512, by rfl⟩ : syracuseStep 968683 = 1453025) B1453025
theorem B968695 : Blo 968591 968695 := bstep (se 1 (by rfl) ⟨726521, by rfl⟩ : syracuseStep 968695 = 1453043) B1453043
theorem B968715 : Blo 968591 968715 := bstep (se 1 (by rfl) ⟨726536, by rfl⟩ : syracuseStep 968715 = 1453073) B1453073
theorem B2181131 : Blo 968591 2181131 := bstep (se 1 (by rfl) ⟨1635848, by rfl⟩ : syracuseStep 2181131 = 3271697) B3271697
theorem B968727 : Blo 968591 968727 := bstep (se 1 (by rfl) ⟨726545, by rfl⟩ : syracuseStep 968727 = 1453091) B1453091
theorem B1230871 : Blo 968591 1230871 := bstep (se 1 (by rfl) ⟨923153, by rfl⟩ : syracuseStep 1230871 = 1846307) B1846307
theorem B968747 : Blo 968591 968747 := bstep (se 1 (by rfl) ⟨726560, by rfl⟩ : syracuseStep 968747 = 1453121) B1453121
theorem B968759 : Blo 968591 968759 := bstep (se 1 (by rfl) ⟨726569, by rfl⟩ : syracuseStep 968759 = 1453139) B1453139
theorem B2181185 : Blo 968591 2181185 := bstep (se 2 (by rfl) ⟨817944, by rfl⟩ : syracuseStep 2181185 = 1635889) B1635889
theorem B968779 : Blo 968591 968779 := bstep (se 1 (by rfl) ⟨726584, by rfl⟩ : syracuseStep 968779 = 1453169) B1453169
theorem B968791 : Blo 968591 968791 := bstep (se 1 (by rfl) ⟨726593, by rfl⟩ : syracuseStep 968791 = 1453187) B1453187
theorem B968811 : Blo 968591 968811 := bstep (se 1 (by rfl) ⟨726608, by rfl⟩ : syracuseStep 968811 = 1453217) B1453217
theorem B968823 : Blo 968591 968823 := bstep (se 1 (by rfl) ⟨726617, by rfl⟩ : syracuseStep 968823 = 1453235) B1453235
theorem B968843 : Blo 968591 968843 := bstep (se 1 (by rfl) ⟨726632, by rfl⟩ : syracuseStep 968843 = 1453265) B1453265
theorem B968855 : Blo 968591 968855 := bstep (se 1 (by rfl) ⟨726641, by rfl⟩ : syracuseStep 968855 = 1453283) B1453283
theorem B968875 : Blo 968591 968875 := bstep (se 1 (by rfl) ⟨726656, by rfl⟩ : syracuseStep 968875 = 1453313) B1453313
theorem B2214067 : Blo 968591 2214067 := bstep (se 1 (by rfl) ⟨1660550, by rfl⟩ : syracuseStep 2214067 = 3321101) B3321101
theorem B968887 : Blo 968591 968887 := bstep (se 1 (by rfl) ⟨726665, by rfl⟩ : syracuseStep 968887 = 1453331) B1453331
theorem B968907 : Blo 968591 968907 := bstep (se 1 (by rfl) ⟨726680, by rfl⟩ : syracuseStep 968907 = 1453361) B1453361
theorem B968919 : Blo 968591 968919 := bstep (se 1 (by rfl) ⟨726689, by rfl⟩ : syracuseStep 968919 = 1453379) B1453379
theorem B968939 : Blo 968591 968939 := bstep (se 1 (by rfl) ⟨726704, by rfl⟩ : syracuseStep 968939 = 1453409) B1453409
theorem B968951 : Blo 968591 968951 := bstep (se 1 (by rfl) ⟨726713, by rfl⟩ : syracuseStep 968951 = 1453427) B1453427
theorem B968971 : Blo 968591 968971 := bstep (se 1 (by rfl) ⟨726728, by rfl⟩ : syracuseStep 968971 = 1453457) B1453457
theorem B968983 : Blo 968591 968983 := bstep (se 1 (by rfl) ⟨726737, by rfl⟩ : syracuseStep 968983 = 1453475) B1453475
theorem B2181401 : Blo 968591 2181401 := bstep (se 2 (by rfl) ⟨818025, by rfl⟩ : syracuseStep 2181401 = 1636051) B1636051
theorem B969003 : Blo 968591 969003 := bstep (se 1 (by rfl) ⟨726752, by rfl⟩ : syracuseStep 969003 = 1453505) B1453505
theorem B969015 : Blo 968591 969015 := bstep (se 1 (by rfl) ⟨726761, by rfl⟩ : syracuseStep 969015 = 1453523) B1453523
theorem B969035 : Blo 968591 969035 := bstep (se 1 (by rfl) ⟨726776, by rfl⟩ : syracuseStep 969035 = 1453553) B1453553
theorem B969047 : Blo 968591 969047 := bstep (se 1 (by rfl) ⟨726785, by rfl⟩ : syracuseStep 969047 = 1453571) B1453571
theorem B969067 : Blo 968591 969067 := bstep (se 1 (by rfl) ⟨726800, by rfl⟩ : syracuseStep 969067 = 1453601) B1453601
theorem B2181491 : Blo 968591 2181491 := bstep (se 1 (by rfl) ⟨1636118, by rfl⟩ : syracuseStep 2181491 = 3272237) B3272237
theorem B969079 : Blo 968591 969079 := bstep (se 1 (by rfl) ⟨726809, by rfl⟩ : syracuseStep 969079 = 1453619) B1453619
theorem B969099 : Blo 968591 969099 := bstep (se 1 (by rfl) ⟨726824, by rfl⟩ : syracuseStep 969099 = 1453649) B1453649
theorem B969111 : Blo 968591 969111 := bstep (se 1 (by rfl) ⟨726833, by rfl⟩ : syracuseStep 969111 = 1453667) B1453667
theorem B2181527 : Blo 968591 2181527 := bstep (se 1 (by rfl) ⟨1636145, by rfl⟩ : syracuseStep 2181527 = 3272291) B3272291
theorem B969131 : Blo 968591 969131 := bstep (se 1 (by rfl) ⟨726848, by rfl⟩ : syracuseStep 969131 = 1453697) B1453697
theorem B969143 : Blo 968591 969143 := bstep (se 1 (by rfl) ⟨726857, by rfl⟩ : syracuseStep 969143 = 1453715) B1453715
theorem B1034699 : Blo 968591 1034699 := bstep (se 1 (by rfl) ⟨776024, by rfl⟩ : syracuseStep 1034699 = 1552049) B1552049
theorem B969163 : Blo 968591 969163 := bstep (se 1 (by rfl) ⟨726872, by rfl⟩ : syracuseStep 969163 = 1453745) B1453745
theorem B969175 : Blo 968591 969175 := bstep (se 1 (by rfl) ⟨726881, by rfl⟩ : syracuseStep 969175 = 1453763) B1453763
theorem B969195 : Blo 968591 969195 := bstep (se 1 (by rfl) ⟨726896, by rfl⟩ : syracuseStep 969195 = 1453793) B1453793
theorem B969207 : Blo 968591 969207 := bstep (se 1 (by rfl) ⟨726905, by rfl⟩ : syracuseStep 969207 = 1453811) B1453811
theorem B969227 : Blo 968591 969227 := bstep (se 1 (by rfl) ⟨726920, by rfl⟩ : syracuseStep 969227 = 1453841) B1453841
theorem B969239 : Blo 968591 969239 := bstep (se 1 (by rfl) ⟨726929, by rfl⟩ : syracuseStep 969239 = 1453859) B1453859
theorem B7359011 : Blo 968591 7359011 := bstep (se 1 (by rfl) ⟨5519258, by rfl⟩ : syracuseStep 7359011 = 11038517) B11038517
theorem B969259 : Blo 968591 969259 := bstep (se 1 (by rfl) ⟨726944, by rfl⟩ : syracuseStep 969259 = 1453889) B1453889
theorem B969271 : Blo 968591 969271 := bstep (se 1 (by rfl) ⟨726953, by rfl⟩ : syracuseStep 969271 = 1453907) B1453907
theorem B969291 : Blo 968591 969291 := bstep (se 1 (by rfl) ⟨726968, by rfl⟩ : syracuseStep 969291 = 1453937) B1453937
theorem B2181707 : Blo 968591 2181707 := bstep (se 1 (by rfl) ⟨1636280, by rfl⟩ : syracuseStep 2181707 = 3272561) B3272561
theorem B969303 : Blo 968591 969303 := bstep (se 1 (by rfl) ⟨726977, by rfl⟩ : syracuseStep 969303 = 1453955) B1453955
theorem B969323 : Blo 968591 969323 := bstep (se 1 (by rfl) ⟨726992, by rfl⟩ : syracuseStep 969323 = 1453985) B1453985
theorem B969335 : Blo 968591 969335 := bstep (se 1 (by rfl) ⟨727001, by rfl⟩ : syracuseStep 969335 = 1454003) B1454003
theorem B2181761 : Blo 968591 2181761 := bstep (se 2 (by rfl) ⟨818160, by rfl⟩ : syracuseStep 2181761 = 1636321) B1636321
theorem B969355 : Blo 968591 969355 := bstep (se 1 (by rfl) ⟨727016, by rfl⟩ : syracuseStep 969355 = 1454033) B1454033
theorem B969367 : Blo 968591 969367 := bstep (se 1 (by rfl) ⟨727025, by rfl⟩ : syracuseStep 969367 = 1454051) B1454051
theorem B969387 : Blo 968591 969387 := bstep (se 1 (by rfl) ⟨727040, by rfl⟩ : syracuseStep 969387 = 1454081) B1454081
theorem B969399 : Blo 968591 969399 := bstep (se 1 (by rfl) ⟨727049, by rfl⟩ : syracuseStep 969399 = 1454099) B1454099
theorem B969419 : Blo 968591 969419 := bstep (se 1 (by rfl) ⟨727064, by rfl⟩ : syracuseStep 969419 = 1454129) B1454129
theorem B969431 : Blo 968591 969431 := bstep (se 1 (by rfl) ⟨727073, by rfl⟩ : syracuseStep 969431 = 1454147) B1454147
theorem B969451 : Blo 968591 969451 := bstep (se 1 (by rfl) ⟨727088, by rfl⟩ : syracuseStep 969451 = 1454177) B1454177
theorem B969463 : Blo 968591 969463 := bstep (se 1 (by rfl) ⟨727097, by rfl⟩ : syracuseStep 969463 = 1454195) B1454195
theorem B969483 : Blo 968591 969483 := bstep (se 1 (by rfl) ⟨727112, by rfl⟩ : syracuseStep 969483 = 1454225) B1454225
theorem B969495 : Blo 968591 969495 := bstep (se 1 (by rfl) ⟨727121, by rfl⟩ : syracuseStep 969495 = 1454243) B1454243
theorem B969515 : Blo 968591 969515 := bstep (se 1 (by rfl) ⟨727136, by rfl⟩ : syracuseStep 969515 = 1454273) B1454273
theorem B969527 : Blo 968591 969527 := bstep (se 1 (by rfl) ⟨727145, by rfl⟩ : syracuseStep 969527 = 1454291) B1454291
theorem B969547 : Blo 968591 969547 := bstep (se 1 (by rfl) ⟨727160, by rfl⟩ : syracuseStep 969547 = 1454321) B1454321
theorem B969559 : Blo 968591 969559 := bstep (se 1 (by rfl) ⟨727169, by rfl⟩ : syracuseStep 969559 = 1454339) B1454339
theorem B2181977 : Blo 968591 2181977 := bstep (se 2 (by rfl) ⟨818241, by rfl⟩ : syracuseStep 2181977 = 1636483) B1636483
theorem B969579 : Blo 968591 969579 := bstep (se 1 (by rfl) ⟨727184, by rfl⟩ : syracuseStep 969579 = 1454369) B1454369
theorem B969591 : Blo 968591 969591 := bstep (se 1 (by rfl) ⟨727193, by rfl⟩ : syracuseStep 969591 = 1454387) B1454387
theorem B3689347 : Blo 968591 3689347 := bstep (se 1 (by rfl) ⟨2767010, by rfl⟩ : syracuseStep 3689347 = 5534021) B5534021
theorem B969611 : Blo 968591 969611 := bstep (se 1 (by rfl) ⟨727208, by rfl⟩ : syracuseStep 969611 = 1454417) B1454417
theorem B969623 : Blo 968591 969623 := bstep (se 1 (by rfl) ⟨727217, by rfl⟩ : syracuseStep 969623 = 1454435) B1454435
theorem B969643 : Blo 968591 969643 := bstep (se 1 (by rfl) ⟨727232, by rfl⟩ : syracuseStep 969643 = 1454465) B1454465
theorem B2182067 : Blo 968591 2182067 := bstep (se 1 (by rfl) ⟨1636550, by rfl⟩ : syracuseStep 2182067 = 3273101) B3273101
theorem B969655 : Blo 968591 969655 := bstep (se 1 (by rfl) ⟨727241, by rfl⟩ : syracuseStep 969655 = 1454483) B1454483
theorem B969675 : Blo 968591 969675 := bstep (se 1 (by rfl) ⟨727256, by rfl⟩ : syracuseStep 969675 = 1454513) B1454513
theorem B969687 : Blo 968591 969687 := bstep (se 1 (by rfl) ⟨727265, by rfl⟩ : syracuseStep 969687 = 1454531) B1454531
theorem B2182103 : Blo 968591 2182103 := bstep (se 1 (by rfl) ⟨1636577, by rfl⟩ : syracuseStep 2182103 = 3273155) B3273155
theorem B969707 : Blo 968591 969707 := bstep (se 1 (by rfl) ⟨727280, by rfl⟩ : syracuseStep 969707 = 1454561) B1454561
theorem B969719 : Blo 968591 969719 := bstep (se 1 (by rfl) ⟨727289, by rfl⟩ : syracuseStep 969719 = 1454579) B1454579
theorem B969739 : Blo 968591 969739 := bstep (se 1 (by rfl) ⟨727304, by rfl⟩ : syracuseStep 969739 = 1454609) B1454609
theorem B3492887 : Blo 968591 3492887 := bstep (se 1 (by rfl) ⟨2619665, by rfl⟩ : syracuseStep 3492887 = 5239331) B5239331
theorem B969751 : Blo 968591 969751 := bstep (se 1 (by rfl) ⟨727313, by rfl⟩ : syracuseStep 969751 = 1454627) B1454627
theorem B969771 : Blo 968591 969771 := bstep (se 1 (by rfl) ⟨727328, by rfl⟩ : syracuseStep 969771 = 1454657) B1454657
theorem B969783 : Blo 968591 969783 := bstep (se 1 (by rfl) ⟨727337, by rfl⟩ : syracuseStep 969783 = 1454675) B1454675
theorem B969803 : Blo 968591 969803 := bstep (se 1 (by rfl) ⟨727352, by rfl⟩ : syracuseStep 969803 = 1454705) B1454705
theorem B969815 : Blo 968591 969815 := bstep (se 1 (by rfl) ⟨727361, by rfl⟩ : syracuseStep 969815 = 1454723) B1454723
theorem B969835 : Blo 968591 969835 := bstep (se 1 (by rfl) ⟨727376, by rfl⟩ : syracuseStep 969835 = 1454753) B1454753
theorem B969847 : Blo 968591 969847 := bstep (se 1 (by rfl) ⟨727385, by rfl⟩ : syracuseStep 969847 = 1454771) B1454771
theorem B969867 : Blo 968591 969867 := bstep (se 1 (by rfl) ⟨727400, by rfl⟩ : syracuseStep 969867 = 1454801) B1454801
theorem B2182283 : Blo 968591 2182283 := bstep (se 1 (by rfl) ⟨1636712, by rfl⟩ : syracuseStep 2182283 = 3273425) B3273425
theorem B969879 : Blo 968591 969879 := bstep (se 1 (by rfl) ⟨727409, by rfl⟩ : syracuseStep 969879 = 1454819) B1454819
theorem B969899 : Blo 968591 969899 := bstep (se 1 (by rfl) ⟨727424, by rfl⟩ : syracuseStep 969899 = 1454849) B1454849
theorem B3689651 : Blo 968591 3689651 := bstep (se 1 (by rfl) ⟨2767238, by rfl⟩ : syracuseStep 3689651 = 5534477) B5534477
theorem B969911 : Blo 968591 969911 := bstep (se 1 (by rfl) ⟨727433, by rfl⟩ : syracuseStep 969911 = 1454867) B1454867
theorem B2182337 : Blo 968591 2182337 := bstep (se 2 (by rfl) ⟨818376, by rfl⟩ : syracuseStep 2182337 = 1636753) B1636753
theorem B969931 : Blo 968591 969931 := bstep (se 1 (by rfl) ⟨727448, by rfl⟩ : syracuseStep 969931 = 1454897) B1454897
theorem B969943 : Blo 968591 969943 := bstep (se 1 (by rfl) ⟨727457, by rfl⟩ : syracuseStep 969943 = 1454915) B1454915
theorem B969963 : Blo 968591 969963 := bstep (se 1 (by rfl) ⟨727472, by rfl⟩ : syracuseStep 969963 = 1454945) B1454945
theorem B969975 : Blo 968591 969975 := bstep (se 1 (by rfl) ⟨727481, by rfl⟩ : syracuseStep 969975 = 1454963) B1454963
theorem B969995 : Blo 968591 969995 := bstep (se 1 (by rfl) ⟨727496, by rfl⟩ : syracuseStep 969995 = 1454993) B1454993
theorem B970007 : Blo 968591 970007 := bstep (se 1 (by rfl) ⟨727505, by rfl⟩ : syracuseStep 970007 = 1455011) B1455011
theorem B970027 : Blo 968591 970027 := bstep (se 1 (by rfl) ⟨727520, by rfl⟩ : syracuseStep 970027 = 1455041) B1455041
theorem B970039 : Blo 968591 970039 := bstep (se 1 (by rfl) ⟨727529, by rfl⟩ : syracuseStep 970039 = 1455059) B1455059
theorem B970059 : Blo 968591 970059 := bstep (se 1 (by rfl) ⟨727544, by rfl⟩ : syracuseStep 970059 = 1455089) B1455089
theorem B970071 : Blo 968591 970071 := bstep (se 1 (by rfl) ⟨727553, by rfl⟩ : syracuseStep 970071 = 1455107) B1455107
theorem B970091 : Blo 968591 970091 := bstep (se 1 (by rfl) ⟨727568, by rfl⟩ : syracuseStep 970091 = 1455137) B1455137
theorem B970103 : Blo 968591 970103 := bstep (se 1 (by rfl) ⟨727577, by rfl⟩ : syracuseStep 970103 = 1455155) B1455155
theorem B970123 : Blo 968591 970123 := bstep (se 1 (by rfl) ⟨727592, by rfl⟩ : syracuseStep 970123 = 1455185) B1455185
theorem B970135 : Blo 968591 970135 := bstep (se 1 (by rfl) ⟨727601, by rfl⟩ : syracuseStep 970135 = 1455203) B1455203
theorem B2182553 : Blo 968591 2182553 := bstep (se 2 (by rfl) ⟨818457, by rfl⟩ : syracuseStep 2182553 = 1636915) B1636915
theorem B970155 : Blo 968591 970155 := bstep (se 1 (by rfl) ⟨727616, by rfl⟩ : syracuseStep 970155 = 1455233) B1455233
theorem B970167 : Blo 968591 970167 := bstep (se 1 (by rfl) ⟨727625, by rfl⟩ : syracuseStep 970167 = 1455251) B1455251
theorem B970187 : Blo 968591 970187 := bstep (se 1 (by rfl) ⟨727640, by rfl⟩ : syracuseStep 970187 = 1455281) B1455281
theorem B970199 : Blo 968591 970199 := bstep (se 1 (by rfl) ⟨727649, by rfl⟩ : syracuseStep 970199 = 1455299) B1455299
theorem B970219 : Blo 968591 970219 := bstep (se 1 (by rfl) ⟨727664, by rfl⟩ : syracuseStep 970219 = 1455329) B1455329
theorem B2182643 : Blo 968591 2182643 := bstep (se 1 (by rfl) ⟨1636982, by rfl⟩ : syracuseStep 2182643 = 3273965) B3273965
theorem B1035767 : Blo 968591 1035767 := bstep (se 1 (by rfl) ⟨776825, by rfl⟩ : syracuseStep 1035767 = 1553651) B1553651
theorem B970231 : Blo 968591 970231 := bstep (se 1 (by rfl) ⟨727673, by rfl⟩ : syracuseStep 970231 = 1455347) B1455347
theorem B970251 : Blo 968591 970251 := bstep (se 1 (by rfl) ⟨727688, by rfl⟩ : syracuseStep 970251 = 1455377) B1455377
theorem B2182679 : Blo 968591 2182679 := bstep (se 1 (by rfl) ⟨1637009, by rfl⟩ : syracuseStep 2182679 = 3274019) B3274019
theorem B970263 : Blo 968591 970263 := bstep (se 1 (by rfl) ⟨727697, by rfl⟩ : syracuseStep 970263 = 1455395) B1455395
theorem B970283 : Blo 968591 970283 := bstep (se 1 (by rfl) ⟨727712, by rfl⟩ : syracuseStep 970283 = 1455425) B1455425
theorem B970295 : Blo 968591 970295 := bstep (se 1 (by rfl) ⟨727721, by rfl⟩ : syracuseStep 970295 = 1455443) B1455443
theorem B970315 : Blo 968591 970315 := bstep (se 1 (by rfl) ⟨727736, by rfl⟩ : syracuseStep 970315 = 1455473) B1455473
theorem B970327 : Blo 968591 970327 := bstep (se 1 (by rfl) ⟨727745, by rfl⟩ : syracuseStep 970327 = 1455491) B1455491
theorem B970347 : Blo 968591 970347 := bstep (se 1 (by rfl) ⟨727760, by rfl⟩ : syracuseStep 970347 = 1455521) B1455521
theorem B970359 : Blo 968591 970359 := bstep (se 1 (by rfl) ⟨727769, by rfl⟩ : syracuseStep 970359 = 1455539) B1455539
theorem B970379 : Blo 968591 970379 := bstep (se 1 (by rfl) ⟨727784, by rfl⟩ : syracuseStep 970379 = 1455569) B1455569
theorem B970391 : Blo 968591 970391 := bstep (se 1 (by rfl) ⟨727793, by rfl⟩ : syracuseStep 970391 = 1455587) B1455587
theorem B970411 : Blo 968591 970411 := bstep (se 1 (by rfl) ⟨727808, by rfl⟩ : syracuseStep 970411 = 1455617) B1455617
theorem B970423 : Blo 968591 970423 := bstep (se 1 (by rfl) ⟨727817, by rfl⟩ : syracuseStep 970423 = 1455635) B1455635
theorem B3493579 : Blo 968591 3493579 := bstep (se 1 (by rfl) ⟨2620184, by rfl⟩ : syracuseStep 3493579 = 5240369) B5240369
theorem B2182859 : Blo 968591 2182859 := bstep (se 1 (by rfl) ⟨1637144, by rfl⟩ : syracuseStep 2182859 = 3274289) B3274289
theorem B970443 : Blo 968591 970443 := bstep (se 1 (by rfl) ⟨727832, by rfl⟩ : syracuseStep 970443 = 1455665) B1455665
theorem B970455 : Blo 968591 970455 := bstep (se 1 (by rfl) ⟨727841, by rfl⟩ : syracuseStep 970455 = 1455683) B1455683
theorem B970475 : Blo 968591 970475 := bstep (se 1 (by rfl) ⟨727856, by rfl⟩ : syracuseStep 970475 = 1455713) B1455713
theorem B970487 : Blo 968591 970487 := bstep (se 1 (by rfl) ⟨727865, by rfl⟩ : syracuseStep 970487 = 1455731) B1455731
theorem B2182913 : Blo 968591 2182913 := bstep (se 2 (by rfl) ⟨818592, by rfl⟩ : syracuseStep 2182913 = 1637185) B1637185
theorem B970507 : Blo 968591 970507 := bstep (se 1 (by rfl) ⟨727880, by rfl⟩ : syracuseStep 970507 = 1455761) B1455761
theorem B970519 : Blo 968591 970519 := bstep (se 1 (by rfl) ⟨727889, by rfl⟩ : syracuseStep 970519 = 1455779) B1455779
theorem B970539 : Blo 968591 970539 := bstep (se 1 (by rfl) ⟨727904, by rfl⟩ : syracuseStep 970539 = 1455809) B1455809
theorem B970551 : Blo 968591 970551 := bstep (se 1 (by rfl) ⟨727913, by rfl⟩ : syracuseStep 970551 = 1455827) B1455827
theorem B2215745 : Blo 968591 2215745 := bstep (se 2 (by rfl) ⟨830904, by rfl⟩ : syracuseStep 2215745 = 1661809) B1661809
theorem B3690305 : Blo 968591 3690305 := bstep (se 2 (by rfl) ⟨1383864, by rfl⟩ : syracuseStep 3690305 = 2767729) B2767729
theorem B970571 : Blo 968591 970571 := bstep (se 1 (by rfl) ⟨727928, by rfl⟩ : syracuseStep 970571 = 1455857) B1455857
theorem B970583 : Blo 968591 970583 := bstep (se 1 (by rfl) ⟨727937, by rfl⟩ : syracuseStep 970583 = 1455875) B1455875
theorem B16797539 : Blo 968591 16797539 := bstep (se 1 (by rfl) ⟨12598154, by rfl⟩ : syracuseStep 16797539 = 25196309) B25196309
theorem B970603 : Blo 968591 970603 := bstep (se 1 (by rfl) ⟨727952, by rfl⟩ : syracuseStep 970603 = 1455905) B1455905
theorem B970615 : Blo 968591 970615 := bstep (se 1 (by rfl) ⟨727961, by rfl⟩ : syracuseStep 970615 = 1455923) B1455923
theorem B970635 : Blo 968591 970635 := bstep (se 1 (by rfl) ⟨727976, by rfl⟩ : syracuseStep 970635 = 1455953) B1455953
theorem B970647 : Blo 968591 970647 := bstep (se 1 (by rfl) ⟨727985, by rfl⟩ : syracuseStep 970647 = 1455971) B1455971
theorem B970667 : Blo 968591 970667 := bstep (se 1 (by rfl) ⟨728000, by rfl⟩ : syracuseStep 970667 = 1456001) B1456001
theorem B970679 : Blo 968591 970679 := bstep (se 1 (by rfl) ⟨728009, by rfl⟩ : syracuseStep 970679 = 1456019) B1456019
theorem B970699 : Blo 968591 970699 := bstep (se 1 (by rfl) ⟨728024, by rfl⟩ : syracuseStep 970699 = 1456049) B1456049
theorem B970711 : Blo 968591 970711 := bstep (se 1 (by rfl) ⟨728033, by rfl⟩ : syracuseStep 970711 = 1456067) B1456067
theorem B2183129 : Blo 968591 2183129 := bstep (se 2 (by rfl) ⟨818673, by rfl⟩ : syracuseStep 2183129 = 1637347) B1637347
theorem B970731 : Blo 968591 970731 := bstep (se 1 (by rfl) ⟨728048, by rfl⟩ : syracuseStep 970731 = 1456097) B1456097
theorem B970743 : Blo 968591 970743 := bstep (se 1 (by rfl) ⟨728057, by rfl⟩ : syracuseStep 970743 = 1456115) B1456115
theorem B970763 : Blo 968591 970763 := bstep (se 1 (by rfl) ⟨728072, by rfl⟩ : syracuseStep 970763 = 1456145) B1456145
theorem B970775 : Blo 968591 970775 := bstep (se 1 (by rfl) ⟨728081, by rfl⟩ : syracuseStep 970775 = 1456163) B1456163
theorem B970795 : Blo 968591 970795 := bstep (se 1 (by rfl) ⟨728096, by rfl⟩ : syracuseStep 970795 = 1456193) B1456193
theorem B2183219 : Blo 968591 2183219 := bstep (se 1 (by rfl) ⟨1637414, by rfl⟩ : syracuseStep 2183219 = 3274829) B3274829
theorem B970807 : Blo 968591 970807 := bstep (se 1 (by rfl) ⟨728105, by rfl⟩ : syracuseStep 970807 = 1456211) B1456211
theorem B970827 : Blo 968591 970827 := bstep (se 1 (by rfl) ⟨728120, by rfl⟩ : syracuseStep 970827 = 1456241) B1456241
theorem B2183255 : Blo 968591 2183255 := bstep (se 1 (by rfl) ⟨1637441, by rfl⟩ : syracuseStep 2183255 = 3274883) B3274883
theorem B970839 : Blo 968591 970839 := bstep (se 1 (by rfl) ⟨728129, by rfl⟩ : syracuseStep 970839 = 1456259) B1456259
theorem B7491685 : Blo 968591 7491685 := bstep (se 4 (by rfl) ⟨702345, by rfl⟩ : syracuseStep 7491685 = 1404691) B1404691
theorem B970859 : Blo 968591 970859 := bstep (se 1 (by rfl) ⟨728144, by rfl⟩ : syracuseStep 970859 = 1456289) B1456289
theorem B970871 : Blo 968591 970871 := bstep (se 1 (by rfl) ⟨728153, by rfl⟩ : syracuseStep 970871 = 1456307) B1456307
theorem B970891 : Blo 968591 970891 := bstep (se 1 (by rfl) ⟨728168, by rfl⟩ : syracuseStep 970891 = 1456337) B1456337
theorem B970903 : Blo 968591 970903 := bstep (se 1 (by rfl) ⟨728177, by rfl⟩ : syracuseStep 970903 = 1456355) B1456355
theorem B970923 : Blo 968591 970923 := bstep (se 1 (by rfl) ⟨728192, by rfl⟩ : syracuseStep 970923 = 1456385) B1456385
theorem B970935 : Blo 968591 970935 := bstep (se 1 (by rfl) ⟨728201, by rfl⟩ : syracuseStep 970935 = 1456403) B1456403
theorem B970955 : Blo 968591 970955 := bstep (se 1 (by rfl) ⟨728216, by rfl⟩ : syracuseStep 970955 = 1456433) B1456433
theorem B970967 : Blo 968591 970967 := bstep (se 1 (by rfl) ⟨728225, by rfl⟩ : syracuseStep 970967 = 1456451) B1456451
theorem B970987 : Blo 968591 970987 := bstep (se 1 (by rfl) ⟨728240, by rfl⟩ : syracuseStep 970987 = 1456481) B1456481
theorem B970999 : Blo 968591 970999 := bstep (se 1 (by rfl) ⟨728249, by rfl⟩ : syracuseStep 970999 = 1456499) B1456499
theorem B2183435 : Blo 968591 2183435 := bstep (se 1 (by rfl) ⟨1637576, by rfl⟩ : syracuseStep 2183435 = 3275153) B3275153
theorem B971019 : Blo 968591 971019 := bstep (se 1 (by rfl) ⟨728264, by rfl⟩ : syracuseStep 971019 = 1456529) B1456529
theorem B971031 : Blo 968591 971031 := bstep (se 1 (by rfl) ⟨728273, by rfl⟩ : syracuseStep 971031 = 1456547) B1456547
theorem B971051 : Blo 968591 971051 := bstep (se 1 (by rfl) ⟨728288, by rfl⟩ : syracuseStep 971051 = 1456577) B1456577
theorem B971063 : Blo 968591 971063 := bstep (se 1 (by rfl) ⟨728297, by rfl⟩ : syracuseStep 971063 = 1456595) B1456595
theorem B2183489 : Blo 968591 2183489 := bstep (se 2 (by rfl) ⟨818808, by rfl⟩ : syracuseStep 2183489 = 1637617) B1637617
theorem B971083 : Blo 968591 971083 := bstep (se 1 (by rfl) ⟨728312, by rfl⟩ : syracuseStep 971083 = 1456625) B1456625
theorem B971095 : Blo 968591 971095 := bstep (se 1 (by rfl) ⟨728321, by rfl⟩ : syracuseStep 971095 = 1456643) B1456643
theorem B971115 : Blo 968591 971115 := bstep (se 1 (by rfl) ⟨728336, by rfl⟩ : syracuseStep 971115 = 1456673) B1456673
theorem B971127 : Blo 968591 971127 := bstep (se 1 (by rfl) ⟨728345, by rfl⟩ : syracuseStep 971127 = 1456691) B1456691
theorem B971147 : Blo 968591 971147 := bstep (se 1 (by rfl) ⟨728360, by rfl⟩ : syracuseStep 971147 = 1456721) B1456721
theorem B971159 : Blo 968591 971159 := bstep (se 1 (by rfl) ⟨728369, by rfl⟩ : syracuseStep 971159 = 1456739) B1456739
theorem B971179 : Blo 968591 971179 := bstep (se 1 (by rfl) ⟨728384, by rfl⟩ : syracuseStep 971179 = 1456769) B1456769
theorem B971191 : Blo 968591 971191 := bstep (se 1 (by rfl) ⟨728393, by rfl⟩ : syracuseStep 971191 = 1456787) B1456787
theorem B971211 : Blo 968591 971211 := bstep (se 1 (by rfl) ⟨728408, by rfl⟩ : syracuseStep 971211 = 1456817) B1456817
theorem B971223 : Blo 968591 971223 := bstep (se 1 (by rfl) ⟨728417, by rfl⟩ : syracuseStep 971223 = 1456835) B1456835
theorem B971243 : Blo 968591 971243 := bstep (se 1 (by rfl) ⟨728432, by rfl⟩ : syracuseStep 971243 = 1456865) B1456865
theorem B971255 : Blo 968591 971255 := bstep (se 1 (by rfl) ⟨728441, by rfl⟩ : syracuseStep 971255 = 1456883) B1456883
theorem B971275 : Blo 968591 971275 := bstep (se 1 (by rfl) ⟨728456, by rfl⟩ : syracuseStep 971275 = 1456913) B1456913
theorem B971287 : Blo 968591 971287 := bstep (se 1 (by rfl) ⟨728465, by rfl⟩ : syracuseStep 971287 = 1456931) B1456931
theorem B2183705 : Blo 968591 2183705 := bstep (se 2 (by rfl) ⟨818889, by rfl⟩ : syracuseStep 2183705 = 1637779) B1637779
theorem B1036843 : Blo 968591 1036843 := bstep (se 1 (by rfl) ⟨777632, by rfl⟩ : syracuseStep 1036843 = 1555265) B1555265
theorem B971307 : Blo 968591 971307 := bstep (se 1 (by rfl) ⟨728480, by rfl⟩ : syracuseStep 971307 = 1456961) B1456961
theorem B971319 : Blo 968591 971319 := bstep (se 1 (by rfl) ⟨728489, by rfl⟩ : syracuseStep 971319 = 1456979) B1456979
theorem B971339 : Blo 968591 971339 := bstep (se 1 (by rfl) ⟨728504, by rfl⟩ : syracuseStep 971339 = 1457009) B1457009
theorem B971351 : Blo 968591 971351 := bstep (se 1 (by rfl) ⟨728513, by rfl⟩ : syracuseStep 971351 = 1457027) B1457027
theorem B971371 : Blo 968591 971371 := bstep (se 1 (by rfl) ⟨728528, by rfl⟩ : syracuseStep 971371 = 1457057) B1457057
theorem B2183795 : Blo 968591 2183795 := bstep (se 1 (by rfl) ⟨1637846, by rfl⟩ : syracuseStep 2183795 = 3275693) B3275693
theorem B971383 : Blo 968591 971383 := bstep (se 1 (by rfl) ⟨728537, by rfl⟩ : syracuseStep 971383 = 1457075) B1457075
theorem B971403 : Blo 968591 971403 := bstep (se 1 (by rfl) ⟨728552, by rfl⟩ : syracuseStep 971403 = 1457105) B1457105
theorem B2183831 : Blo 968591 2183831 := bstep (se 1 (by rfl) ⟨1637873, by rfl⟩ : syracuseStep 2183831 = 3275747) B3275747
theorem B971415 : Blo 968591 971415 := bstep (se 1 (by rfl) ⟨728561, by rfl⟩ : syracuseStep 971415 = 1457123) B1457123
theorem B971435 : Blo 968591 971435 := bstep (se 1 (by rfl) ⟨728576, by rfl⟩ : syracuseStep 971435 = 1457153) B1457153
theorem B971447 : Blo 968591 971447 := bstep (se 1 (by rfl) ⟨728585, by rfl⟩ : syracuseStep 971447 = 1457171) B1457171
theorem B971467 : Blo 968591 971467 := bstep (se 1 (by rfl) ⟨728600, by rfl⟩ : syracuseStep 971467 = 1457201) B1457201
theorem B971479 : Blo 968591 971479 := bstep (se 1 (by rfl) ⟨728609, by rfl⟩ : syracuseStep 971479 = 1457219) B1457219
theorem B971499 : Blo 968591 971499 := bstep (se 1 (by rfl) ⟨728624, by rfl⟩ : syracuseStep 971499 = 1457249) B1457249
theorem B971511 : Blo 968591 971511 := bstep (se 1 (by rfl) ⟨728633, by rfl⟩ : syracuseStep 971511 = 1457267) B1457267
theorem B971531 : Blo 968591 971531 := bstep (se 1 (by rfl) ⟨728648, by rfl⟩ : syracuseStep 971531 = 1457297) B1457297
theorem B971543 : Blo 968591 971543 := bstep (se 1 (by rfl) ⟨728657, by rfl⟩ : syracuseStep 971543 = 1457315) B1457315
theorem B971563 : Blo 968591 971563 := bstep (se 1 (by rfl) ⟨728672, by rfl⟩ : syracuseStep 971563 = 1457345) B1457345
theorem B971575 : Blo 968591 971575 := bstep (se 1 (by rfl) ⟨728681, by rfl⟩ : syracuseStep 971575 = 1457363) B1457363
theorem B2184011 : Blo 968591 2184011 := bstep (se 1 (by rfl) ⟨1638008, by rfl⟩ : syracuseStep 2184011 = 3276017) B3276017
theorem B971595 : Blo 968591 971595 := bstep (se 1 (by rfl) ⟨728696, by rfl⟩ : syracuseStep 971595 = 1457393) B1457393
theorem B971607 : Blo 968591 971607 := bstep (se 1 (by rfl) ⟨728705, by rfl⟩ : syracuseStep 971607 = 1457411) B1457411
theorem B971627 : Blo 968591 971627 := bstep (se 1 (by rfl) ⟨728720, by rfl⟩ : syracuseStep 971627 = 1457441) B1457441
theorem B971639 : Blo 968591 971639 := bstep (se 1 (by rfl) ⟨728729, by rfl⟩ : syracuseStep 971639 = 1457459) B1457459
theorem B2184065 : Blo 968591 2184065 := bstep (se 2 (by rfl) ⟨819024, by rfl⟩ : syracuseStep 2184065 = 1638049) B1638049
theorem B971659 : Blo 968591 971659 := bstep (se 1 (by rfl) ⟨728744, by rfl⟩ : syracuseStep 971659 = 1457489) B1457489
theorem B971671 : Blo 968591 971671 := bstep (se 1 (by rfl) ⟨728753, by rfl⟩ : syracuseStep 971671 = 1457507) B1457507
theorem B971691 : Blo 968591 971691 := bstep (se 1 (by rfl) ⟨728768, by rfl⟩ : syracuseStep 971691 = 1457537) B1457537
theorem B971703 : Blo 968591 971703 := bstep (se 1 (by rfl) ⟨728777, by rfl⟩ : syracuseStep 971703 = 1457555) B1457555
theorem B971723 : Blo 968591 971723 := bstep (se 1 (by rfl) ⟨728792, by rfl⟩ : syracuseStep 971723 = 1457585) B1457585
theorem B971735 : Blo 968591 971735 := bstep (se 1 (by rfl) ⟨728801, by rfl⟩ : syracuseStep 971735 = 1457603) B1457603
theorem B971755 : Blo 968591 971755 := bstep (se 1 (by rfl) ⟨728816, by rfl⟩ : syracuseStep 971755 = 1457633) B1457633
theorem B971767 : Blo 968591 971767 := bstep (se 1 (by rfl) ⟨728825, by rfl⟩ : syracuseStep 971767 = 1457651) B1457651
theorem B971787 : Blo 968591 971787 := bstep (se 1 (by rfl) ⟨728840, by rfl⟩ : syracuseStep 971787 = 1457681) B1457681
theorem B971799 : Blo 968591 971799 := bstep (se 1 (by rfl) ⟨728849, by rfl⟩ : syracuseStep 971799 = 1457699) B1457699
theorem B971819 : Blo 968591 971819 := bstep (se 1 (by rfl) ⟨728864, by rfl⟩ : syracuseStep 971819 = 1457729) B1457729
theorem B3691565 : Blo 968591 3691565 := bstep (se 3 (by rfl) ⟨692168, by rfl⟩ : syracuseStep 3691565 = 1384337) B1384337
theorem B971831 : Blo 968591 971831 := bstep (se 1 (by rfl) ⟨728873, by rfl⟩ : syracuseStep 971831 = 1457747) B1457747
theorem B971851 : Blo 968591 971851 := bstep (se 1 (by rfl) ⟨728888, by rfl⟩ : syracuseStep 971851 = 1457777) B1457777
theorem B3691595 : Blo 968591 3691595 := bstep (se 1 (by rfl) ⟨2768696, by rfl⟩ : syracuseStep 3691595 = 5537393) B5537393
theorem B971863 : Blo 968591 971863 := bstep (se 1 (by rfl) ⟨728897, by rfl⟩ : syracuseStep 971863 = 1457795) B1457795
theorem B2184281 : Blo 968591 2184281 := bstep (se 2 (by rfl) ⟨819105, by rfl⟩ : syracuseStep 2184281 = 1638211) B1638211
theorem B971883 : Blo 968591 971883 := bstep (se 1 (by rfl) ⟨728912, by rfl⟩ : syracuseStep 971883 = 1457825) B1457825
theorem B971895 : Blo 968591 971895 := bstep (se 1 (by rfl) ⟨728921, by rfl⟩ : syracuseStep 971895 = 1457843) B1457843
theorem B971915 : Blo 968591 971915 := bstep (se 1 (by rfl) ⟨728936, by rfl⟩ : syracuseStep 971915 = 1457873) B1457873
theorem B971927 : Blo 968591 971927 := bstep (se 1 (by rfl) ⟨728945, by rfl⟩ : syracuseStep 971927 = 1457891) B1457891
theorem B971947 : Blo 968591 971947 := bstep (se 1 (by rfl) ⟨728960, by rfl⟩ : syracuseStep 971947 = 1457921) B1457921
theorem B2184371 : Blo 968591 2184371 := bstep (se 1 (by rfl) ⟨1638278, by rfl⟩ : syracuseStep 2184371 = 3276557) B3276557
theorem B971959 : Blo 968591 971959 := bstep (se 1 (by rfl) ⟨728969, by rfl⟩ : syracuseStep 971959 = 1457939) B1457939
theorem B971979 : Blo 968591 971979 := bstep (se 1 (by rfl) ⟨728984, by rfl⟩ : syracuseStep 971979 = 1457969) B1457969
theorem B2184407 : Blo 968591 2184407 := bstep (se 1 (by rfl) ⟨1638305, by rfl⟩ : syracuseStep 2184407 = 3276611) B3276611
theorem B971991 : Blo 968591 971991 := bstep (se 1 (by rfl) ⟨728993, by rfl⟩ : syracuseStep 971991 = 1457987) B1457987
theorem B972011 : Blo 968591 972011 := bstep (se 1 (by rfl) ⟨729008, by rfl⟩ : syracuseStep 972011 = 1458017) B1458017
theorem B972023 : Blo 968591 972023 := bstep (se 1 (by rfl) ⟨729017, by rfl⟩ : syracuseStep 972023 = 1458035) B1458035
theorem B972043 : Blo 968591 972043 := bstep (se 1 (by rfl) ⟨729032, by rfl⟩ : syracuseStep 972043 = 1458065) B1458065
theorem B972055 : Blo 968591 972055 := bstep (se 1 (by rfl) ⟨729041, by rfl⟩ : syracuseStep 972055 = 1458083) B1458083
theorem B972075 : Blo 968591 972075 := bstep (se 1 (by rfl) ⟨729056, by rfl⟩ : syracuseStep 972075 = 1458113) B1458113
theorem B972087 : Blo 968591 972087 := bstep (se 1 (by rfl) ⟨729065, by rfl⟩ : syracuseStep 972087 = 1458131) B1458131
theorem B972107 : Blo 968591 972107 := bstep (se 1 (by rfl) ⟨729080, by rfl⟩ : syracuseStep 972107 = 1458161) B1458161
theorem B972119 : Blo 968591 972119 := bstep (se 1 (by rfl) ⟨729089, by rfl⟩ : syracuseStep 972119 = 1458179) B1458179
theorem B972139 : Blo 968591 972139 := bstep (se 1 (by rfl) ⟨729104, by rfl⟩ : syracuseStep 972139 = 1458209) B1458209
theorem B972151 : Blo 968591 972151 := bstep (se 1 (by rfl) ⟨729113, by rfl⟩ : syracuseStep 972151 = 1458227) B1458227
theorem B2184587 : Blo 968591 2184587 := bstep (se 1 (by rfl) ⟨1638440, by rfl⟩ : syracuseStep 2184587 = 3276881) B3276881
theorem B972171 : Blo 968591 972171 := bstep (se 1 (by rfl) ⟨729128, by rfl⟩ : syracuseStep 972171 = 1458257) B1458257
theorem B972183 : Blo 968591 972183 := bstep (se 1 (by rfl) ⟨729137, by rfl⟩ : syracuseStep 972183 = 1458275) B1458275
theorem B972203 : Blo 968591 972203 := bstep (se 1 (by rfl) ⟨729152, by rfl⟩ : syracuseStep 972203 = 1458305) B1458305
theorem B972215 : Blo 968591 972215 := bstep (se 1 (by rfl) ⟨729161, by rfl⟩ : syracuseStep 972215 = 1458323) B1458323
theorem B2184641 : Blo 968591 2184641 := bstep (se 2 (by rfl) ⟨819240, by rfl⟩ : syracuseStep 2184641 = 1638481) B1638481
theorem B972235 : Blo 968591 972235 := bstep (se 1 (by rfl) ⟨729176, by rfl⟩ : syracuseStep 972235 = 1458353) B1458353
theorem B1037783 : Blo 968591 1037783 := bstep (se 1 (by rfl) ⟨778337, by rfl⟩ : syracuseStep 1037783 = 1556675) B1556675
theorem B972247 : Blo 968591 972247 := bstep (se 1 (by rfl) ⟨729185, by rfl⟩ : syracuseStep 972247 = 1458371) B1458371
theorem B2807257 : Blo 968591 2807257 := bstep (se 2 (by rfl) ⟨1052721, by rfl⟩ : syracuseStep 2807257 = 2105443) B2105443
theorem B972267 : Blo 968591 972267 := bstep (se 1 (by rfl) ⟨729200, by rfl⟩ : syracuseStep 972267 = 1458401) B1458401
theorem B972279 : Blo 968591 972279 := bstep (se 1 (by rfl) ⟨729209, by rfl⟩ : syracuseStep 972279 = 1458419) B1458419
theorem B972299 : Blo 968591 972299 := bstep (se 1 (by rfl) ⟨729224, by rfl⟩ : syracuseStep 972299 = 1458449) B1458449
theorem B972311 : Blo 968591 972311 := bstep (se 1 (by rfl) ⟨729233, by rfl⟩ : syracuseStep 972311 = 1458467) B1458467
theorem B972331 : Blo 968591 972331 := bstep (se 1 (by rfl) ⟨729248, by rfl⟩ : syracuseStep 972331 = 1458497) B1458497
theorem B972343 : Blo 968591 972343 := bstep (se 1 (by rfl) ⟨729257, by rfl⟩ : syracuseStep 972343 = 1458515) B1458515
theorem B972363 : Blo 968591 972363 := bstep (se 1 (by rfl) ⟨729272, by rfl⟩ : syracuseStep 972363 = 1458545) B1458545
theorem B972375 : Blo 968591 972375 := bstep (se 1 (by rfl) ⟨729281, by rfl⟩ : syracuseStep 972375 = 1458563) B1458563
theorem B972395 : Blo 968591 972395 := bstep (se 1 (by rfl) ⟨729296, by rfl⟩ : syracuseStep 972395 = 1458593) B1458593
theorem B972407 : Blo 968591 972407 := bstep (se 1 (by rfl) ⟨729305, by rfl⟩ : syracuseStep 972407 = 1458611) B1458611
theorem B972427 : Blo 968591 972427 := bstep (se 1 (by rfl) ⟨729320, by rfl⟩ : syracuseStep 972427 = 1458641) B1458641
theorem B972439 : Blo 968591 972439 := bstep (se 1 (by rfl) ⟨729329, by rfl⟩ : syracuseStep 972439 = 1458659) B1458659
theorem B2184857 : Blo 968591 2184857 := bstep (se 2 (by rfl) ⟨819321, by rfl⟩ : syracuseStep 2184857 = 1638643) B1638643
theorem B972459 : Blo 968591 972459 := bstep (se 1 (by rfl) ⟨729344, by rfl⟩ : syracuseStep 972459 = 1458689) B1458689
theorem B972471 : Blo 968591 972471 := bstep (se 1 (by rfl) ⟨729353, by rfl⟩ : syracuseStep 972471 = 1458707) B1458707
theorem B972491 : Blo 968591 972491 := bstep (se 1 (by rfl) ⟨729368, by rfl⟩ : syracuseStep 972491 = 1458737) B1458737
theorem B972503 : Blo 968591 972503 := bstep (se 1 (by rfl) ⟨729377, by rfl⟩ : syracuseStep 972503 = 1458755) B1458755
theorem B3692249 : Blo 968591 3692249 := bstep (se 2 (by rfl) ⟨1384593, by rfl⟩ : syracuseStep 3692249 = 2769187) B2769187
theorem B972523 : Blo 968591 972523 := bstep (se 1 (by rfl) ⟨729392, by rfl⟩ : syracuseStep 972523 = 1458785) B1458785
theorem B2184947 : Blo 968591 2184947 := bstep (se 1 (by rfl) ⟨1638710, by rfl⟩ : syracuseStep 2184947 = 3277421) B3277421
theorem B972535 : Blo 968591 972535 := bstep (se 1 (by rfl) ⟨729401, by rfl⟩ : syracuseStep 972535 = 1458803) B1458803
theorem B972555 : Blo 968591 972555 := bstep (se 1 (by rfl) ⟨729416, by rfl⟩ : syracuseStep 972555 = 1458833) B1458833
theorem B2184983 : Blo 968591 2184983 := bstep (se 1 (by rfl) ⟨1638737, by rfl⟩ : syracuseStep 2184983 = 3277475) B3277475
theorem B4151063 : Blo 968591 4151063 := bstep (se 1 (by rfl) ⟨3113297, by rfl⟩ : syracuseStep 4151063 = 6226595) B6226595
theorem B972567 : Blo 968591 972567 := bstep (se 1 (by rfl) ⟨729425, by rfl⟩ : syracuseStep 972567 = 1458851) B1458851
theorem B972587 : Blo 968591 972587 := bstep (se 1 (by rfl) ⟨729440, by rfl⟩ : syracuseStep 972587 = 1458881) B1458881
theorem B6215575 : Blo 968591 6215575 := bstep (se 1 (by rfl) ⟨4661681, by rfl⟩ : syracuseStep 6215575 = 9323363) B9323363
theorem B2185163 : Blo 968591 2185163 := bstep (se 1 (by rfl) ⟨1638872, by rfl⟩ : syracuseStep 2185163 = 3277745) B3277745
theorem B2185217 : Blo 968591 2185217 := bstep (se 2 (by rfl) ⟨819456, by rfl⟩ : syracuseStep 2185217 = 1638913) B1638913
theorem B3692567 : Blo 968591 3692567 := bstep (se 1 (by rfl) ⟨2769425, by rfl⟩ : syracuseStep 3692567 = 5538851) B5538851
theorem B4905035 : Blo 968591 4905035 := bstep (se 1 (by rfl) ⟨3678776, by rfl⟩ : syracuseStep 4905035 = 7357553) B7357553
theorem B1497163 : Blo 968591 1497163 := bstep (se 1 (by rfl) ⟨1122872, by rfl⟩ : syracuseStep 1497163 = 2245745) B2245745
theorem B4151371 : Blo 968591 4151371 := bstep (se 1 (by rfl) ⟨3113528, by rfl⟩ : syracuseStep 4151371 = 6227057) B6227057
theorem B2185433 : Blo 968591 2185433 := bstep (se 2 (by rfl) ⟨819537, by rfl⟩ : syracuseStep 2185433 = 1639075) B1639075
theorem B2185523 : Blo 968591 2185523 := bstep (se 1 (by rfl) ⟨1639142, by rfl⟩ : syracuseStep 2185523 = 3278285) B3278285
theorem B2185559 : Blo 968591 2185559 := bstep (se 1 (by rfl) ⟨1639169, by rfl⟩ : syracuseStep 2185559 = 3278339) B3278339
theorem B4151645 : Blo 968591 4151645 := bstep (se 3 (by rfl) ⟨778433, by rfl⟩ : syracuseStep 4151645 = 1556867) B1556867
theorem B2185739 : Blo 968591 2185739 := bstep (se 1 (by rfl) ⟨1639304, by rfl⟩ : syracuseStep 2185739 = 3278609) B3278609
theorem B17717777 : Blo 968591 17717777 := bstep (se 2 (by rfl) ⟨6644166, by rfl⟩ : syracuseStep 17717777 = 13288333) B13288333
theorem B2185793 : Blo 968591 2185793 := bstep (se 2 (by rfl) ⟨819672, by rfl⟩ : syracuseStep 2185793 = 1639345) B1639345
theorem B4479667 : Blo 968591 4479667 := bstep (se 1 (by rfl) ⟨3359750, by rfl⟩ : syracuseStep 4479667 = 6719501) B6719501
theorem B4479709 : Blo 968591 4479709 := bstep (se 3 (by rfl) ⟨839945, by rfl⟩ : syracuseStep 4479709 = 1679891) B1679891
theorem B2186009 : Blo 968591 2186009 := bstep (se 2 (by rfl) ⟨819753, by rfl⟩ : syracuseStep 2186009 = 1639507) B1639507
theorem B2186099 : Blo 968591 2186099 := bstep (se 1 (by rfl) ⟨1639574, by rfl⟩ : syracuseStep 2186099 = 3279149) B3279149
theorem B2186135 : Blo 968591 2186135 := bstep (se 1 (by rfl) ⟨1639601, by rfl⟩ : syracuseStep 2186135 = 3279203) B3279203
theorem B1498009 : Blo 968591 1498009 := bstep (se 2 (by rfl) ⟨561753, by rfl⟩ : syracuseStep 1498009 = 1123507) B1123507
theorem B3496925 : Blo 968591 3496925 := bstep (se 3 (by rfl) ⟨655673, by rfl⟩ : syracuseStep 3496925 = 1311347) B1311347
theorem B2186315 : Blo 968591 2186315 := bstep (se 1 (by rfl) ⟨1639736, by rfl⟩ : syracuseStep 2186315 = 3279473) B3279473
theorem B2186369 : Blo 968591 2186369 := bstep (se 2 (by rfl) ⟨819888, by rfl⟩ : syracuseStep 2186369 = 1639777) B1639777
theorem B8281349 : Blo 968591 8281349 := bstep (se 4 (by rfl) ⟨776376, by rfl⟩ : syracuseStep 8281349 = 1552753) B1552753
theorem B5528897 : Blo 968591 5528897 := bstep (se 2 (by rfl) ⟨2073336, by rfl⟩ : syracuseStep 5528897 = 4146673) B4146673
theorem B1662295 : Blo 968591 1662295 := bstep (se 1 (by rfl) ⟨1246721, by rfl⟩ : syracuseStep 1662295 = 2493443) B2493443
theorem B2186585 : Blo 968591 2186585 := bstep (se 2 (by rfl) ⟨819969, by rfl⟩ : syracuseStep 2186585 = 1639939) B1639939
theorem B2186675 : Blo 968591 2186675 := bstep (se 1 (by rfl) ⟨1640006, by rfl⟩ : syracuseStep 2186675 = 3280013) B3280013
theorem B2186711 : Blo 968591 2186711 := bstep (se 1 (by rfl) ⟨1640033, by rfl⟩ : syracuseStep 2186711 = 3280067) B3280067
theorem B1105483 : Blo 968591 1105483 := bstep (se 1 (by rfl) ⟨829112, by rfl⟩ : syracuseStep 1105483 = 1658225) B1658225
theorem B2186891 : Blo 968591 2186891 := bstep (se 1 (by rfl) ⟨1640168, by rfl⟩ : syracuseStep 2186891 = 3280337) B3280337
theorem B4152977 : Blo 968591 4152977 := bstep (se 2 (by rfl) ⟨1557366, by rfl⟩ : syracuseStep 4152977 = 3114733) B3114733
theorem B2186945 : Blo 968591 2186945 := bstep (se 2 (by rfl) ⟨820104, by rfl⟩ : syracuseStep 2186945 = 1640209) B1640209
theorem B7364357 : Blo 968591 7364357 := bstep (se 4 (by rfl) ⟨690408, by rfl⟩ : syracuseStep 7364357 = 1380817) B1380817
theorem B3989293 : Blo 968591 3989293 := bstep (se 3 (by rfl) ⟨747992, by rfl⟩ : syracuseStep 3989293 = 1495985) B1495985
theorem B4906817 : Blo 968591 4906817 := bstep (se 2 (by rfl) ⟨1840056, by rfl⟩ : syracuseStep 4906817 = 3680113) B3680113
theorem B6217573 : Blo 968591 6217573 := bstep (se 4 (by rfl) ⟨582897, by rfl⟩ : syracuseStep 6217573 = 1165795) B1165795
theorem B2187161 : Blo 968591 2187161 := bstep (se 2 (by rfl) ⟨820185, by rfl⟩ : syracuseStep 2187161 = 1640371) B1640371
theorem B8282033 : Blo 968591 8282033 := bstep (se 2 (by rfl) ⟨3105762, by rfl⟩ : syracuseStep 8282033 = 6211525) B6211525
theorem B33611699 : Blo 968591 33611699 := bstep (se 1 (by rfl) ⟨25208774, by rfl⟩ : syracuseStep 33611699 = 50417549) B50417549
theorem B2187251 : Blo 968591 2187251 := bstep (se 1 (by rfl) ⟨1640438, by rfl⟩ : syracuseStep 2187251 = 3280877) B3280877
theorem B2187287 : Blo 968591 2187287 := bstep (se 1 (by rfl) ⟨1640465, by rfl⟩ : syracuseStep 2187287 = 3280931) B3280931
theorem B2187467 : Blo 968591 2187467 := bstep (se 1 (by rfl) ⟨1640600, by rfl⟩ : syracuseStep 2187467 = 3281201) B3281201
theorem B3367133 : Blo 968591 3367133 := bstep (se 3 (by rfl) ⟨631337, by rfl⟩ : syracuseStep 3367133 = 1262675) B1262675
theorem B2187521 : Blo 968591 2187521 := bstep (se 2 (by rfl) ⟨820320, by rfl⟩ : syracuseStep 2187521 = 1640641) B1640641
theorem B2187737 : Blo 968591 2187737 := bstep (se 2 (by rfl) ⟨820401, by rfl⟩ : syracuseStep 2187737 = 1640803) B1640803
theorem B1401367 : Blo 968591 1401367 := bstep (se 1 (by rfl) ⟨1051025, by rfl⟩ : syracuseStep 1401367 = 2102051) B2102051
theorem B2187827 : Blo 968591 2187827 := bstep (se 1 (by rfl) ⟨1640870, by rfl⟩ : syracuseStep 2187827 = 3281741) B3281741
theorem B2187863 : Blo 968591 2187863 := bstep (se 1 (by rfl) ⟨1640897, by rfl⟩ : syracuseStep 2187863 = 3281795) B3281795
theorem B3269213 : Blo 968591 3269213 := bstep (se 3 (by rfl) ⟨612977, by rfl⟩ : syracuseStep 3269213 = 1225955) B1225955
theorem B2188043 : Blo 968591 2188043 := bstep (se 1 (by rfl) ⟨1641032, by rfl⟩ : syracuseStep 2188043 = 3282065) B3282065
theorem B2188097 : Blo 968591 2188097 := bstep (se 2 (by rfl) ⟨820536, by rfl⟩ : syracuseStep 2188097 = 1641073) B1641073
theorem B8283059 : Blo 968591 8283059 := bstep (se 1 (by rfl) ⟨6212294, by rfl⟩ : syracuseStep 8283059 = 12424589) B12424589
theorem B2188313 : Blo 968591 2188313 := bstep (se 2 (by rfl) ⟨820617, by rfl⟩ : syracuseStep 2188313 = 1641235) B1641235
theorem B31450517 : Blo 968591 31450517 := bstep (se 6 (by rfl) ⟨737121, by rfl⟩ : syracuseStep 31450517 = 1474243) B1474243
theorem B5531287 : Blo 968591 5531287 := bstep (se 1 (by rfl) ⟨4148465, by rfl⟩ : syracuseStep 5531287 = 8296931) B8296931
theorem B3270347 : Blo 968591 3270347 := bstep (se 1 (by rfl) ⟨2452760, by rfl⟩ : syracuseStep 3270347 = 4905521) B4905521
theorem B4908761 : Blo 968591 4908761 := bstep (se 2 (by rfl) ⟨1840785, by rfl⟩ : syracuseStep 4908761 = 3681571) B3681571
theorem B3106583 : Blo 968591 3106583 := bstep (se 1 (by rfl) ⟨2329937, by rfl⟩ : syracuseStep 3106583 = 4659875) B4659875
theorem B5891915 : Blo 968591 5891915 := bstep (se 1 (by rfl) ⟨4418936, by rfl⟩ : syracuseStep 5891915 = 8837873) B8837873
theorem B1107799 : Blo 968591 1107799 := bstep (se 1 (by rfl) ⟨830849, by rfl⟩ : syracuseStep 1107799 = 1661699) B1661699
theorem B3270617 : Blo 968591 3270617 := bstep (se 2 (by rfl) ⟨1226481, by rfl⟩ : syracuseStep 3270617 = 2452963) B2452963
theorem B7366787 : Blo 968591 7366787 := bstep (se 1 (by rfl) ⟨5525090, by rfl⟩ : syracuseStep 7366787 = 11050181) B11050181
theorem B3991697 : Blo 968591 3991697 := bstep (se 2 (by rfl) ⟨1496886, by rfl⟩ : syracuseStep 3991697 = 2993773) B2993773
theorem B21031285 : Blo 968591 21031285 := bstep (se 5 (by rfl) ⟨985841, by rfl⟩ : syracuseStep 21031285 = 1971683) B1971683
theorem B2451991 : Blo 968591 2451991 := bstep (se 1 (by rfl) ⟨1838993, by rfl⟩ : syracuseStep 2451991 = 3677987) B3677987
theorem B7465547 : Blo 968591 7465547 := bstep (se 1 (by rfl) ⟨5599160, by rfl⟩ : syracuseStep 7465547 = 11198321) B11198321
theorem B3271319 : Blo 968591 3271319 := bstep (se 1 (by rfl) ⟨2453489, by rfl⟩ : syracuseStep 3271319 = 4906979) B4906979
theorem B3107659 : Blo 968591 3107659 := bstep (se 1 (by rfl) ⟨2330744, by rfl⟩ : syracuseStep 3107659 = 4661489) B4661489
theorem B2452427 : Blo 968591 2452427 := bstep (se 1 (by rfl) ⟨1839320, by rfl⟩ : syracuseStep 2452427 = 3678641) B3678641
theorem B3501107 : Blo 968591 3501107 := bstep (se 1 (by rfl) ⟨2625830, by rfl⟩ : syracuseStep 3501107 = 5251661) B5251661
theorem B3271859 : Blo 968591 3271859 := bstep (se 1 (by rfl) ⟨2453894, by rfl⟩ : syracuseStep 3271859 = 4907789) B4907789
theorem B8744153 : Blo 968591 8744153 := bstep (se 2 (by rfl) ⟨3279057, by rfl⟩ : syracuseStep 8744153 = 6558115) B6558115
theorem B4910381 : Blo 968591 4910381 := bstep (se 3 (by rfl) ⟨920696, by rfl⟩ : syracuseStep 4910381 = 1841393) B1841393
theorem B2452801 : Blo 968591 2452801 := bstep (se 2 (by rfl) ⟨919800, by rfl⟩ : syracuseStep 2452801 = 1839601) B1839601
theorem B3272129 : Blo 968591 3272129 := bstep (se 2 (by rfl) ⟨1227048, by rfl⟩ : syracuseStep 3272129 = 2454097) B2454097
theorem B2453399 : Blo 968591 2453399 := bstep (se 1 (by rfl) ⟨1840049, by rfl⟩ : syracuseStep 2453399 = 3680099) B3680099
theorem B3272669 : Blo 968591 3272669 := bstep (se 3 (by rfl) ⟨613625, by rfl⟩ : syracuseStep 3272669 = 1227251) B1227251
theorem B3109043 : Blo 968591 3109043 := bstep (se 1 (by rfl) ⟨2331782, by rfl⟩ : syracuseStep 3109043 = 4663565) B4663565
theorem B1634519 : Blo 968591 1634519 := bstep (se 1 (by rfl) ⟨1225889, by rfl⟩ : syracuseStep 1634519 = 2451779) B2451779
theorem B1634647 : Blo 968591 1634647 := bstep (se 1 (by rfl) ⟨1225985, by rfl⟩ : syracuseStep 1634647 = 2451971) B2451971
theorem B2945497 : Blo 968591 2945497 := bstep (se 2 (by rfl) ⟨1104561, by rfl⟩ : syracuseStep 2945497 = 2209123) B2209123
theorem B8286785 : Blo 968591 8286785 := bstep (se 2 (by rfl) ⟨3107544, by rfl⟩ : syracuseStep 8286785 = 6215089) B6215089
theorem B8417969 : Blo 968591 8417969 := bstep (se 2 (by rfl) ⟨3156738, by rfl⟩ : syracuseStep 8417969 = 6313477) B6313477
theorem B2454209 : Blo 968591 2454209 := bstep (se 2 (by rfl) ⟨920328, by rfl⟩ : syracuseStep 2454209 = 1840657) B1840657
theorem B16577459 : Blo 968591 16577459 := bstep (se 1 (by rfl) ⟨12433094, by rfl⟩ : syracuseStep 16577459 = 24866189) B24866189
theorem B1635275 : Blo 968591 1635275 := bstep (se 1 (by rfl) ⟨1226456, by rfl⟩ : syracuseStep 1635275 = 2452913) B2452913
theorem B1635403 : Blo 968591 1635403 := bstep (se 1 (by rfl) ⟨1226552, by rfl⟩ : syracuseStep 1635403 = 2453105) B2453105
theorem B3273803 : Blo 968591 3273803 := bstep (se 1 (by rfl) ⟨2455352, by rfl⟩ : syracuseStep 3273803 = 4910705) B4910705
theorem B1635545 : Blo 968591 1635545 := bstep (se 2 (by rfl) ⟨613329, by rfl⟩ : syracuseStep 1635545 = 1226659) B1226659
theorem B2454745 : Blo 968591 2454745 := bstep (se 2 (by rfl) ⟨920529, by rfl⟩ : syracuseStep 2454745 = 1841059) B1841059
theorem B1635673 : Blo 968591 1635673 := bstep (se 2 (by rfl) ⟨613377, by rfl⟩ : syracuseStep 1635673 = 1226755) B1226755
theorem B3274073 : Blo 968591 3274073 := bstep (se 2 (by rfl) ⟨1227777, by rfl⟩ : syracuseStep 3274073 = 2455555) B2455555
theorem B5600663 : Blo 968591 5600663 := bstep (se 1 (by rfl) ⟨4200497, by rfl⟩ : syracuseStep 5600663 = 8400995) B8400995
theorem B7370189 : Blo 968591 7370189 := bstep (se 3 (by rfl) ⟨1381910, by rfl⟩ : syracuseStep 7370189 = 2763821) B2763821
theorem B1636247 : Blo 968591 1636247 := bstep (se 1 (by rfl) ⟨1227185, by rfl⟩ : syracuseStep 1636247 = 2454371) B2454371
theorem B7370675 : Blo 968591 7370675 := bstep (se 1 (by rfl) ⟨5528006, by rfl⟩ : syracuseStep 7370675 = 11056013) B11056013
theorem B27981845 : Blo 968591 27981845 := bstep (se 6 (by rfl) ⟨655824, by rfl⟩ : syracuseStep 27981845 = 1311649) B1311649
theorem B1636375 : Blo 968591 1636375 := bstep (se 1 (by rfl) ⟨1227281, by rfl⟩ : syracuseStep 1636375 = 2454563) B2454563
theorem B3274775 : Blo 968591 3274775 := bstep (se 1 (by rfl) ⟨2456081, by rfl⟩ : syracuseStep 3274775 = 4912163) B4912163
theorem B5240933 : Blo 968591 5240933 := bstep (se 4 (by rfl) ⟨491337, by rfl⟩ : syracuseStep 5240933 = 982675) B982675
theorem B2455859 : Blo 968591 2455859 := bstep (se 1 (by rfl) ⟨1841894, by rfl⟩ : syracuseStep 2455859 = 3683789) B3683789
theorem B3930443 : Blo 968591 3930443 := bstep (se 1 (by rfl) ⟨2947832, by rfl⟩ : syracuseStep 3930443 = 5895665) B5895665
theorem B7469489 : Blo 968591 7469489 := bstep (se 2 (by rfl) ⟨2801058, by rfl⟩ : syracuseStep 7469489 = 5602117) B5602117
theorem B3275315 : Blo 968591 3275315 := bstep (se 1 (by rfl) ⟨2456486, by rfl⟩ : syracuseStep 3275315 = 4912973) B4912973
theorem B2488897 : Blo 968591 2488897 := bstep (se 2 (by rfl) ⟨933336, by rfl⟩ : syracuseStep 2488897 = 1866673) B1866673
theorem B3734081 : Blo 968591 3734081 := bstep (se 2 (by rfl) ⟨1400280, by rfl⟩ : syracuseStep 3734081 = 2800561) B2800561
theorem B2456153 : Blo 968591 2456153 := bstep (se 2 (by rfl) ⟨921057, by rfl⟩ : syracuseStep 2456153 = 1842115) B1842115
theorem B1637003 : Blo 968591 1637003 := bstep (se 1 (by rfl) ⟨1227752, by rfl⟩ : syracuseStep 1637003 = 2455505) B2455505
theorem B1637131 : Blo 968591 1637131 := bstep (se 1 (by rfl) ⟨1227848, by rfl⟩ : syracuseStep 1637131 = 2455697) B2455697
theorem B3504941 : Blo 968591 3504941 := bstep (se 3 (by rfl) ⟨657176, by rfl⟩ : syracuseStep 3504941 = 1314353) B1314353
theorem B3275585 : Blo 968591 3275585 := bstep (se 2 (by rfl) ⟨1228344, by rfl⟩ : syracuseStep 3275585 = 2456689) B2456689
theorem B3505027 : Blo 968591 3505027 := bstep (se 1 (by rfl) ⟨2628770, by rfl⟩ : syracuseStep 3505027 = 5257541) B5257541
theorem B1637273 : Blo 968591 1637273 := bstep (se 2 (by rfl) ⟨613977, by rfl⟩ : syracuseStep 1637273 = 1227955) B1227955
theorem B12450833 : Blo 968591 12450833 := bstep (se 2 (by rfl) ⟨4669062, by rfl⟩ : syracuseStep 12450833 = 9338125) B9338125
theorem B1637401 : Blo 968591 1637401 := bstep (se 2 (by rfl) ⟨614025, by rfl⟩ : syracuseStep 1637401 = 1228051) B1228051
theorem B1965107 : Blo 968591 1965107 := bstep (se 1 (by rfl) ⟨1473830, by rfl⟩ : syracuseStep 1965107 = 2947661) B2947661
theorem B1473611 : Blo 968591 1473611 := bstep (se 1 (by rfl) ⟨1105208, by rfl⟩ : syracuseStep 1473611 = 2210417) B2210417
theorem B4914269 : Blo 968591 4914269 := bstep (se 3 (by rfl) ⟨921425, by rfl⟩ : syracuseStep 4914269 = 1842851) B1842851
theorem B2620619 : Blo 968591 2620619 := bstep (se 1 (by rfl) ⟨1965464, by rfl⟩ : syracuseStep 2620619 = 3930929) B3930929
theorem B3276125 : Blo 968591 3276125 := bstep (se 3 (by rfl) ⟨614273, by rfl⟩ : syracuseStep 3276125 = 1228547) B1228547
theorem B7372133 : Blo 968591 7372133 := bstep (se 4 (by rfl) ⟨691137, by rfl⟩ : syracuseStep 7372133 = 1382275) B1382275
theorem B8420939 : Blo 968591 8420939 := bstep (se 1 (by rfl) ⟨6315704, by rfl⟩ : syracuseStep 8420939 = 12631409) B12631409
theorem B1637975 : Blo 968591 1637975 := bstep (se 1 (by rfl) ⟨1228481, by rfl⟩ : syracuseStep 1637975 = 2456963) B2456963
theorem B1638103 : Blo 968591 1638103 := bstep (se 1 (by rfl) ⟨1228577, by rfl⟩ : syracuseStep 1638103 = 2457155) B2457155
theorem B3931949 : Blo 968591 3931949 := bstep (se 3 (by rfl) ⟨737240, by rfl⟩ : syracuseStep 3931949 = 1474481) B1474481
theorem B7372619 : Blo 968591 7372619 := bstep (se 1 (by rfl) ⟨5529464, by rfl⟩ : syracuseStep 7372619 = 11058929) B11058929
theorem B12582773 : Blo 968591 12582773 := bstep (se 5 (by rfl) ⟨589817, by rfl⟩ : syracuseStep 12582773 = 1179635) B1179635
theorem B1245079 : Blo 968591 1245079 := bstep (se 1 (by rfl) ⟨933809, by rfl⟩ : syracuseStep 1245079 = 1867619) B1867619
theorem B2457611 : Blo 968591 2457611 := bstep (se 1 (by rfl) ⟨1843208, by rfl⟩ : syracuseStep 2457611 = 3686417) B3686417
theorem B1638535 : Blo 968591 1638535 := bstep (se 1 (by rfl) ⟨1228901, by rfl⟩ : syracuseStep 1638535 = 2457803) B2457803
theorem B1474823 : Blo 968591 1474823 := bstep (se 1 (by rfl) ⟨1106117, by rfl⟩ : syracuseStep 1474823 = 2212235) B2212235
theorem B11796769 : Blo 968591 11796769 := bstep (se 2 (by rfl) ⟨4423788, by rfl⟩ : syracuseStep 11796769 = 8847577) B8847577
theorem B5898529 : Blo 968591 5898529 := bstep (se 2 (by rfl) ⟨2211948, by rfl⟩ : syracuseStep 5898529 = 4423897) B4423897
theorem B1180075 : Blo 968591 1180075 := bstep (se 1 (by rfl) ⟨885056, by rfl⟩ : syracuseStep 1180075 = 1770113) B1770113
theorem B8290781 : Blo 968591 8290781 := bstep (se 3 (by rfl) ⟨1554521, by rfl⟩ : syracuseStep 8290781 = 3109043) B3109043
theorem B2458127 : Blo 968591 2458127 := bstep (se 1 (by rfl) ⟨1843595, by rfl⟩ : syracuseStep 2458127 = 3687191) B3687191
theorem B2458259 : Blo 968591 2458259 := bstep (se 1 (by rfl) ⟨1843694, by rfl⟩ : syracuseStep 2458259 = 3687389) B3687389
theorem B1868489 : Blo 968591 1868489 := bstep (se 2 (by rfl) ⟨700683, by rfl⟩ : syracuseStep 1868489 = 1401367) B1401367
theorem B15958745 : Blo 968591 15958745 := bstep (se 2 (by rfl) ⟨5984529, by rfl⟩ : syracuseStep 15958745 = 11969059) B11969059
theorem B3277583 : Blo 968591 3277583 := bstep (se 1 (by rfl) ⟨2458187, by rfl⟩ : syracuseStep 3277583 = 4916375) B4916375
theorem B1639183 : Blo 968591 1639183 := bstep (se 1 (by rfl) ⟨1229387, by rfl⟩ : syracuseStep 1639183 = 2458775) B2458775
theorem B5899211 : Blo 968591 5899211 := bstep (se 1 (by rfl) ⟨4424408, by rfl⟩ : syracuseStep 5899211 = 8848817) B8848817
theorem B3277853 : Blo 968591 3277853 := bstep (se 3 (by rfl) ⟨614597, by rfl⟩ : syracuseStep 3277853 = 1229195) B1229195
theorem B1639723 : Blo 968591 1639723 := bstep (se 1 (by rfl) ⟨1229792, by rfl⟩ : syracuseStep 1639723 = 2459585) B2459585
theorem B1639865 : Blo 968591 1639865 := bstep (se 2 (by rfl) ⟨614949, by rfl⟩ : syracuseStep 1639865 = 1229899) B1229899
theorem B3114425 : Blo 968591 3114425 := bstep (se 2 (by rfl) ⟨1167909, by rfl⟩ : syracuseStep 3114425 = 2335819) B2335819
theorem B2623063 : Blo 968591 2623063 := bstep (se 1 (by rfl) ⟨1967297, by rfl⟩ : syracuseStep 2623063 = 3934595) B3934595
theorem B2459393 : Blo 968591 2459393 := bstep (se 2 (by rfl) ⟨922272, by rfl⟩ : syracuseStep 2459393 = 1844545) B1844545
theorem B21235729 : Blo 968591 21235729 := bstep (se 2 (by rfl) ⟨7963398, by rfl⟩ : syracuseStep 21235729 = 15926797) B15926797
theorem B6228029 : Blo 968591 6228029 := bstep (se 3 (by rfl) ⟨1167755, by rfl⟩ : syracuseStep 6228029 = 2335511) B2335511
theorem B11798615 : Blo 968591 11798615 := bstep (se 1 (by rfl) ⟨8848961, by rfl⟩ : syracuseStep 11798615 = 17697923) B17697923
theorem B2623603 : Blo 968591 2623603 := bstep (se 1 (by rfl) ⟨1967702, by rfl⟩ : syracuseStep 2623603 = 3935405) B3935405
theorem B2459767 : Blo 968591 2459767 := bstep (se 1 (by rfl) ⟨1844825, by rfl⟩ : syracuseStep 2459767 = 3689651) B3689651
theorem B1640567 : Blo 968591 1640567 := bstep (se 1 (by rfl) ⟨1230425, by rfl⟩ : syracuseStep 1640567 = 2460851) B2460851
theorem B7375049 : Blo 968591 7375049 := bstep (se 2 (by rfl) ⟨2765643, by rfl⟩ : syracuseStep 7375049 = 5531287) B5531287
theorem B2361611 : Blo 968591 2361611 := bstep (se 1 (by rfl) ⟨1771208, by rfl⟩ : syracuseStep 2361611 = 3542417) B3542417
theorem B3279257 : Blo 968591 3279257 := bstep (se 2 (by rfl) ⟨1229721, by rfl⟩ : syracuseStep 3279257 = 2459443) B2459443
theorem B4655569 : Blo 968591 4655569 := bstep (se 2 (by rfl) ⟨1745838, by rfl⟩ : syracuseStep 4655569 = 3491677) B3491677
theorem B4655645 : Blo 968591 4655645 := bstep (se 3 (by rfl) ⟨872933, by rfl⟩ : syracuseStep 4655645 = 1745867) B1745867
theorem B2329121 : Blo 968591 2329121 := bstep (se 2 (by rfl) ⟨873420, by rfl⟩ : syracuseStep 2329121 = 1746841) B1746841
theorem B1477163 : Blo 968591 1477163 := bstep (se 1 (by rfl) ⟨1107872, by rfl⟩ : syracuseStep 1477163 = 2215745) B2215745
theorem B2460203 : Blo 968591 2460203 := bstep (se 1 (by rfl) ⟨1845152, by rfl⟩ : syracuseStep 2460203 = 3690305) B3690305
theorem B1641019 : Blo 968591 1641019 := bstep (se 1 (by rfl) ⟨1230764, by rfl⟩ : syracuseStep 1641019 = 2461529) B2461529
theorem B1641161 : Blo 968591 1641161 := bstep (se 2 (by rfl) ⟨615435, by rfl⟩ : syracuseStep 1641161 = 1230871) B1230871
theorem B1969031 : Blo 968591 1969031 := bstep (se 1 (by rfl) ⟨1476773, by rfl⟩ : syracuseStep 1969031 = 2953547) B2953547
theorem B2952089 : Blo 968591 2952089 := bstep (se 2 (by rfl) ⟨1107033, by rfl⟩ : syracuseStep 2952089 = 2214067) B2214067
theorem B1379371 : Blo 968591 1379371 := bstep (se 1 (by rfl) ⟨1034528, by rfl⟩ : syracuseStep 1379371 = 2069057) B2069057
theorem B2624555 : Blo 968591 2624555 := bstep (se 1 (by rfl) ⟨1968416, by rfl⟩ : syracuseStep 2624555 = 3936833) B3936833
theorem B3279959 : Blo 968591 3279959 := bstep (se 1 (by rfl) ⟨2459969, by rfl⟩ : syracuseStep 3279959 = 4919939) B4919939
theorem B4918643 : Blo 968591 4918643 := bstep (se 1 (by rfl) ⟨3688982, by rfl⟩ : syracuseStep 4918643 = 7377965) B7377965
theorem B2461043 : Blo 968591 2461043 := bstep (se 1 (by rfl) ⟨1845782, by rfl⟩ : syracuseStep 2461043 = 3691565) B3691565
theorem B2461063 : Blo 968591 2461063 := bstep (se 1 (by rfl) ⟨1845797, by rfl⟩ : syracuseStep 2461063 = 3691595) B3691595
theorem B1379855 : Blo 968591 1379855 := bstep (se 1 (by rfl) ⟨1034891, by rfl⟩ : syracuseStep 1379855 = 2069783) B2069783
theorem B2493985 : Blo 968591 2493985 := bstep (se 2 (by rfl) ⟨935244, by rfl⟩ : syracuseStep 2493985 = 1870489) B1870489
theorem B3280445 : Blo 968591 3280445 := bstep (se 3 (by rfl) ⟨615083, by rfl⟩ : syracuseStep 3280445 = 1230167) B1230167
theorem B2494099 : Blo 968591 2494099 := bstep (se 1 (by rfl) ⟨1870574, by rfl⟩ : syracuseStep 2494099 = 3741149) B3741149
theorem B2461337 : Blo 968591 2461337 := bstep (se 2 (by rfl) ⟨923001, by rfl⟩ : syracuseStep 2461337 = 1846003) B1846003
theorem B2461499 : Blo 968591 2461499 := bstep (se 1 (by rfl) ⟨1846124, by rfl⟩ : syracuseStep 2461499 = 3692249) B3692249
theorem B4919129 : Blo 968591 4919129 := bstep (se 2 (by rfl) ⟨1844673, by rfl⟩ : syracuseStep 4919129 = 3689347) B3689347
theorem B2461711 : Blo 968591 2461711 := bstep (se 1 (by rfl) ⟨1846283, by rfl⟩ : syracuseStep 2461711 = 3692567) B3692567
theorem B1839419 : Blo 968591 1839419 := bstep (se 1 (by rfl) ⟨1379564, by rfl⟩ : syracuseStep 1839419 = 2759129) B2759129
theorem B2331283 : Blo 968591 2331283 := bstep (se 1 (by rfl) ⟨1748462, by rfl⟩ : syracuseStep 2331283 = 3496925) B3496925
theorem B9310949 : Blo 968591 9310949 := bstep (se 4 (by rfl) ⟨872901, by rfl⟩ : syracuseStep 9310949 = 1745803) B1745803
theorem B3937025 : Blo 968591 3937025 := bstep (se 2 (by rfl) ⟨1476384, by rfl⟩ : syracuseStep 3937025 = 2952769) B2952769
theorem B1839905 : Blo 968591 1839905 := bstep (se 2 (by rfl) ⟨689964, by rfl⟩ : syracuseStep 1839905 = 1379929) B1379929
theorem B1970977 : Blo 968591 1970977 := bstep (se 2 (by rfl) ⟨739116, by rfl⟩ : syracuseStep 1970977 = 1478233) B1478233
theorem B4658105 : Blo 968591 4658105 := bstep (se 2 (by rfl) ⟨1746789, by rfl⟩ : syracuseStep 4658105 = 3493579) B3493579
theorem B3281849 : Blo 968591 3281849 := bstep (se 2 (by rfl) ⟨1230693, by rfl⟩ : syracuseStep 3281849 = 2461387) B2461387
theorem B1840171 : Blo 968591 1840171 := bstep (se 1 (by rfl) ⟨1380128, by rfl⟩ : syracuseStep 1840171 = 2760257) B2760257
theorem B1971319 : Blo 968591 1971319 := bstep (se 1 (by rfl) ⟨1478489, by rfl⟩ : syracuseStep 1971319 = 2956979) B2956979
theorem B4658413 : Blo 968591 4658413 := bstep (se 3 (by rfl) ⟨873452, by rfl⟩ : syracuseStep 4658413 = 1746905) B1746905
theorem B15963425 : Blo 968591 15963425 := bstep (se 2 (by rfl) ⟨5986284, by rfl⟩ : syracuseStep 15963425 = 11972569) B11972569
theorem B2069945 : Blo 968591 2069945 := bstep (se 2 (by rfl) ⟨776229, by rfl⟩ : syracuseStep 2069945 = 1552459) B1552459
theorem B3282443 : Blo 968591 3282443 := bstep (se 1 (by rfl) ⟨2461832, by rfl⟩ : syracuseStep 3282443 = 4923665) B4923665
theorem B5609021 : Blo 968591 5609021 := bstep (se 3 (by rfl) ⟨1051691, by rfl⟩ : syracuseStep 5609021 = 2103383) B2103383
theorem B2627191 : Blo 968591 2627191 := bstep (se 1 (by rfl) ⟨1970393, by rfl⟩ : syracuseStep 2627191 = 3940787) B3940787
theorem B1382059 : Blo 968591 1382059 := bstep (se 1 (by rfl) ⟨1036544, by rfl⟩ : syracuseStep 1382059 = 2073089) B2073089
theorem B2627387 : Blo 968591 2627387 := bstep (se 1 (by rfl) ⟨1970540, by rfl⟩ : syracuseStep 2627387 = 3941081) B3941081
theorem B1382287 : Blo 968591 1382287 := bstep (se 1 (by rfl) ⟨1036715, by rfl⟩ : syracuseStep 1382287 = 2073431) B2073431
theorem B4921235 : Blo 968591 4921235 := bstep (se 1 (by rfl) ⟨3690926, by rfl⟩ : syracuseStep 4921235 = 7381853) B7381853
theorem B1841287 : Blo 968591 1841287 := bstep (se 1 (by rfl) ⟨1380965, by rfl⟩ : syracuseStep 1841287 = 2761931) B2761931
theorem B85104917 : Blo 968591 85104917 := bstep (se 6 (by rfl) ⟨1994646, by rfl⟩ : syracuseStep 85104917 = 3989293) B3989293
theorem B2071055 : Blo 968591 2071055 := bstep (se 1 (by rfl) ⟨1553291, by rfl⟩ : syracuseStep 2071055 = 3106583) B3106583
theorem B2759197 : Blo 968591 2759197 := bstep (se 3 (by rfl) ⟨517349, by rfl⟩ : syracuseStep 2759197 = 1034699) B1034699
theorem B2759255 : Blo 968591 2759255 := bstep (se 1 (by rfl) ⟨2069441, by rfl⟩ : syracuseStep 2759255 = 4138883) B4138883
theorem B1841849 : Blo 968591 1841849 := bstep (se 2 (by rfl) ⟨690693, by rfl⟩ : syracuseStep 1841849 = 1381387) B1381387
theorem B2661131 : Blo 968591 2661131 := bstep (se 1 (by rfl) ⟨1995848, by rfl⟩ : syracuseStep 2661131 = 3991697) B3991697
theorem B2071585 : Blo 968591 2071585 := bstep (se 2 (by rfl) ⟨776844, by rfl⟩ : syracuseStep 2071585 = 1553689) B1553689
theorem B3743009 : Blo 968591 3743009 := bstep (se 2 (by rfl) ⟨1403628, by rfl⟩ : syracuseStep 3743009 = 2807257) B2807257
theorem B2334071 : Blo 968591 2334071 := bstep (se 1 (by rfl) ⟨1750553, by rfl⟩ : syracuseStep 2334071 = 3501107) B3501107
theorem B1843003 : Blo 968591 1843003 := bstep (se 1 (by rfl) ⟨1382252, by rfl⟩ : syracuseStep 1843003 = 2764505) B2764505
theorem B5250905 : Blo 968591 5250905 := bstep (se 2 (by rfl) ⟨1969089, by rfl⟩ : syracuseStep 5250905 = 3938179) B3938179
theorem B9314365 : Blo 968591 9314365 := bstep (se 3 (by rfl) ⟨1746443, by rfl⟩ : syracuseStep 9314365 = 3492887) B3492887
theorem B1089679 : Blo 968591 1089679 := bstep (se 1 (by rfl) ⟨817259, by rfl⟩ : syracuseStep 1089679 = 1634519) B1634519
theorem B2760905 : Blo 968591 2760905 := bstep (se 2 (by rfl) ⟨1035339, by rfl⟩ : syracuseStep 2760905 = 2070679) B2070679
theorem B10494197 : Blo 968591 10494197 := bstep (se 5 (by rfl) ⟨491915, by rfl⟩ : syracuseStep 10494197 = 983831) B983831
theorem B2105633 : Blo 968591 2105633 := bstep (se 2 (by rfl) ⟨789612, by rfl⟩ : syracuseStep 2105633 = 1579225) B1579225
theorem B1843489 : Blo 968591 1843489 := bstep (se 2 (by rfl) ⟨691308, by rfl⟩ : syracuseStep 1843489 = 1382617) B1382617
theorem B5611979 : Blo 968591 5611979 := bstep (se 1 (by rfl) ⟨4208984, by rfl⟩ : syracuseStep 5611979 = 8417969) B8417969
theorem B2368001 : Blo 968591 2368001 := bstep (se 2 (by rfl) ⟨888000, by rfl⟩ : syracuseStep 2368001 = 1776001) B1776001
theorem B11051639 : Blo 968591 11051639 := bstep (se 1 (by rfl) ⟨8288729, by rfl⟩ : syracuseStep 11051639 = 16577459) B16577459
theorem B1090183 : Blo 968591 1090183 := bstep (se 1 (by rfl) ⟨817637, by rfl⟩ : syracuseStep 1090183 = 1635275) B1635275
theorem B4989613 : Blo 968591 4989613 := bstep (se 3 (by rfl) ⟨935552, by rfl⟩ : syracuseStep 4989613 = 1871105) B1871105
theorem B3318529 : Blo 968591 3318529 := bstep (se 2 (by rfl) ⟨1244448, by rfl⟩ : syracuseStep 3318529 = 2488897) B2488897
theorem B5251877 : Blo 968591 5251877 := bstep (se 4 (by rfl) ⟨492363, by rfl⟩ : syracuseStep 5251877 = 984727) B984727
theorem B1090363 : Blo 968591 1090363 := bstep (se 1 (by rfl) ⟨817772, by rfl⟩ : syracuseStep 1090363 = 1635545) B1635545
theorem B5972945 : Blo 968591 5972945 := bstep (se 2 (by rfl) ⟨2239854, by rfl⟩ : syracuseStep 5972945 = 4479709) B4479709
theorem B2761771 : Blo 968591 2761771 := bstep (se 1 (by rfl) ⟨2071328, by rfl⟩ : syracuseStep 2761771 = 4142657) B4142657
theorem B1090831 : Blo 968591 1090831 := bstep (se 1 (by rfl) ⟨818123, by rfl⟩ : syracuseStep 1090831 = 1636247) B1636247
theorem B2762045 : Blo 968591 2762045 := bstep (se 3 (by rfl) ⟨517883, by rfl⟩ : syracuseStep 2762045 = 1035767) B1035767
theorem B18654563 : Blo 968591 18654563 := bstep (se 1 (by rfl) ⟨13990922, by rfl⟩ : syracuseStep 18654563 = 27981845) B27981845
theorem B4662643 : Blo 968591 4662643 := bstep (se 1 (by rfl) ⟨3496982, by rfl⟩ : syracuseStep 4662643 = 6993965) B6993965
theorem B1516943 : Blo 968591 1516943 := bstep (se 1 (by rfl) ⟨1137707, by rfl⟩ : syracuseStep 1516943 = 2275415) B2275415
theorem B1844795 : Blo 968591 1844795 := bstep (se 1 (by rfl) ⟨1383596, by rfl⟩ : syracuseStep 1844795 = 2767193) B2767193
theorem B2762387 : Blo 968591 2762387 := bstep (se 1 (by rfl) ⟨2071790, by rfl⟩ : syracuseStep 2762387 = 4143581) B4143581
theorem B1091335 : Blo 968591 1091335 := bstep (se 1 (by rfl) ⟨818501, by rfl⟩ : syracuseStep 1091335 = 1637003) B1637003
theorem B5908261 : Blo 968591 5908261 := bstep (se 4 (by rfl) ⟨553899, by rfl⟩ : syracuseStep 5908261 = 1107799) B1107799
theorem B2336627 : Blo 968591 2336627 := bstep (se 1 (by rfl) ⟨1752470, by rfl⟩ : syracuseStep 2336627 = 3504941) B3504941
theorem B1091515 : Blo 968591 1091515 := bstep (se 1 (by rfl) ⟨818636, by rfl⟩ : syracuseStep 1091515 = 1637273) B1637273
theorem B8300555 : Blo 968591 8300555 := bstep (se 1 (by rfl) ⟨6225416, by rfl⟩ : syracuseStep 8300555 = 12450833) B12450833
theorem B1845281 : Blo 968591 1845281 := bstep (se 2 (by rfl) ⟨691980, by rfl⟩ : syracuseStep 1845281 = 1383961) B1383961
theorem B1747079 : Blo 968591 1747079 := bstep (se 1 (by rfl) ⟨1310309, by rfl⟩ : syracuseStep 1747079 = 2620619) B2620619
theorem B1845433 : Blo 968591 1845433 := bstep (se 2 (by rfl) ⟨692037, by rfl⟩ : syracuseStep 1845433 = 1384075) B1384075
theorem B5613959 : Blo 968591 5613959 := bstep (se 1 (by rfl) ⟨4210469, by rfl⟩ : syracuseStep 5613959 = 8420939) B8420939
theorem B1091983 : Blo 968591 1091983 := bstep (se 1 (by rfl) ⟨818987, by rfl⟩ : syracuseStep 1091983 = 1637975) B1637975
theorem B89631197 : Blo 968591 89631197 := bstep (se 3 (by rfl) ⟨16805849, by rfl⟩ : syracuseStep 89631197 = 33611699) B33611699
theorem B4139581 : Blo 968591 4139581 := bstep (se 3 (by rfl) ⟨776171, by rfl⟩ : syracuseStep 4139581 = 1552343) B1552343
theorem B1452935 : Blo 968591 1452935 := bstep (se 1 (by rfl) ⟨1089701, by rfl⟩ : syracuseStep 1452935 = 2179403) B2179403
theorem B1092487 : Blo 968591 1092487 := bstep (se 1 (by rfl) ⟨819365, by rfl⟩ : syracuseStep 1092487 = 1638731) B1638731
theorem B4139923 : Blo 968591 4139923 := bstep (se 1 (by rfl) ⟨3104942, by rfl⟩ : syracuseStep 4139923 = 6209885) B6209885
theorem B1452971 : Blo 968591 1452971 := bstep (se 1 (by rfl) ⟨1089728, by rfl⟩ : syracuseStep 1452971 = 2179457) B2179457
theorem B1453001 : Blo 968591 1453001 := bstep (se 2 (by rfl) ⟨544875, by rfl⟩ : syracuseStep 1453001 = 1089751) B1089751
theorem B1453115 : Blo 968591 1453115 := bstep (se 1 (by rfl) ⟨1089836, by rfl⟩ : syracuseStep 1453115 = 2179673) B2179673
theorem B1092667 : Blo 968591 1092667 := bstep (se 1 (by rfl) ⟨819500, by rfl⟩ : syracuseStep 1092667 = 1639001) B1639001
theorem B1453175 : Blo 968591 1453175 := bstep (se 1 (by rfl) ⟨1089881, by rfl⟩ : syracuseStep 1453175 = 2179763) B2179763
theorem B1453199 : Blo 968591 1453199 := bstep (se 1 (by rfl) ⟨1089899, by rfl⟩ : syracuseStep 1453199 = 2179799) B2179799
theorem B1453241 : Blo 968591 1453241 := bstep (se 2 (by rfl) ⟨544965, by rfl⟩ : syracuseStep 1453241 = 1089931) B1089931
theorem B10628297 : Blo 968591 10628297 := bstep (se 2 (by rfl) ⟨3985611, by rfl⟩ : syracuseStep 10628297 = 7971223) B7971223
theorem B5516525 : Blo 968591 5516525 := bstep (se 3 (by rfl) ⟨1034348, by rfl⟩ : syracuseStep 5516525 = 2068697) B2068697
theorem B1453319 : Blo 968591 1453319 := bstep (se 1 (by rfl) ⟨1089989, by rfl⟩ : syracuseStep 1453319 = 2179979) B2179979
theorem B1453355 : Blo 968591 1453355 := bstep (se 1 (by rfl) ⟨1090016, by rfl⟩ : syracuseStep 1453355 = 2180033) B2180033
theorem B1453385 : Blo 968591 1453385 := bstep (se 2 (by rfl) ⟨545019, by rfl⟩ : syracuseStep 1453385 = 1090039) B1090039
theorem B1453499 : Blo 968591 1453499 := bstep (se 1 (by rfl) ⟨1090124, by rfl⟩ : syracuseStep 1453499 = 2180249) B2180249
theorem B1453559 : Blo 968591 1453559 := bstep (se 1 (by rfl) ⟨1090169, by rfl⟩ : syracuseStep 1453559 = 2180339) B2180339
theorem B31534595 : Blo 968591 31534595 := bstep (se 1 (by rfl) ⟨23650946, by rfl⟩ : syracuseStep 31534595 = 47301893) B47301893
theorem B1453583 : Blo 968591 1453583 := bstep (se 1 (by rfl) ⟨1090187, by rfl⟩ : syracuseStep 1453583 = 2180375) B2180375
theorem B1093135 : Blo 968591 1093135 := bstep (se 1 (by rfl) ⟨819851, by rfl⟩ : syracuseStep 1093135 = 1639703) B1639703
theorem B1453625 : Blo 968591 1453625 := bstep (se 2 (by rfl) ⟨545109, by rfl⟩ : syracuseStep 1453625 = 1090219) B1090219
theorem B1453703 : Blo 968591 1453703 := bstep (se 1 (by rfl) ⟨1090277, by rfl⟩ : syracuseStep 1453703 = 2180555) B2180555
theorem B1453739 : Blo 968591 1453739 := bstep (se 1 (by rfl) ⟨1090304, by rfl⟩ : syracuseStep 1453739 = 2180609) B2180609
theorem B7384769 : Blo 968591 7384769 := bstep (se 2 (by rfl) ⟨2769288, by rfl⟩ : syracuseStep 7384769 = 5538577) B5538577
theorem B1453769 : Blo 968591 1453769 := bstep (se 2 (by rfl) ⟨545163, by rfl⟩ : syracuseStep 1453769 = 1090327) B1090327
theorem B1453883 : Blo 968591 1453883 := bstep (se 1 (by rfl) ⟨1090412, by rfl⟩ : syracuseStep 1453883 = 2180825) B2180825
theorem B2764631 : Blo 968591 2764631 := bstep (se 1 (by rfl) ⟨2073473, by rfl⟩ : syracuseStep 2764631 = 4146947) B4146947
theorem B1453943 : Blo 968591 1453943 := bstep (se 1 (by rfl) ⟨1090457, by rfl⟩ : syracuseStep 1453943 = 2180915) B2180915
theorem B1453967 : Blo 968591 1453967 := bstep (se 1 (by rfl) ⟨1090475, by rfl⟩ : syracuseStep 1453967 = 2180951) B2180951
theorem B1454009 : Blo 968591 1454009 := bstep (se 2 (by rfl) ⟨545253, by rfl⟩ : syracuseStep 1454009 = 1090507) B1090507
theorem B2076617 : Blo 968591 2076617 := bstep (se 2 (by rfl) ⟨778731, by rfl⟩ : syracuseStep 2076617 = 1557463) B1557463
theorem B1454087 : Blo 968591 1454087 := bstep (se 1 (by rfl) ⟨1090565, by rfl⟩ : syracuseStep 1454087 = 2181131) B2181131
theorem B1093639 : Blo 968591 1093639 := bstep (se 1 (by rfl) ⟨820229, by rfl⟩ : syracuseStep 1093639 = 1640459) B1640459
theorem B1454123 : Blo 968591 1454123 := bstep (se 1 (by rfl) ⟨1090592, by rfl⟩ : syracuseStep 1454123 = 2181185) B2181185
theorem B1454153 : Blo 968591 1454153 := bstep (se 2 (by rfl) ⟨545307, by rfl⟩ : syracuseStep 1454153 = 1090615) B1090615
theorem B1454267 : Blo 968591 1454267 := bstep (se 1 (by rfl) ⟨1090700, by rfl⟩ : syracuseStep 1454267 = 2181401) B2181401
theorem B1093819 : Blo 968591 1093819 := bstep (se 1 (by rfl) ⟨820364, by rfl⟩ : syracuseStep 1093819 = 1640729) B1640729
theorem B1454327 : Blo 968591 1454327 := bstep (se 1 (by rfl) ⟨1090745, by rfl⟩ : syracuseStep 1454327 = 2181491) B2181491
theorem B1454351 : Blo 968591 1454351 := bstep (se 1 (by rfl) ⟨1090763, by rfl⟩ : syracuseStep 1454351 = 2181527) B2181527
theorem B1454393 : Blo 968591 1454393 := bstep (se 2 (by rfl) ⟨545397, by rfl⟩ : syracuseStep 1454393 = 1090795) B1090795
theorem B1454471 : Blo 968591 1454471 := bstep (se 1 (by rfl) ⟨1090853, by rfl⟩ : syracuseStep 1454471 = 2181707) B2181707
theorem B1454507 : Blo 968591 1454507 := bstep (se 1 (by rfl) ⟨1090880, by rfl⟩ : syracuseStep 1454507 = 2181761) B2181761
theorem B1454537 : Blo 968591 1454537 := bstep (se 2 (by rfl) ⟨545451, by rfl⟩ : syracuseStep 1454537 = 1090903) B1090903
theorem B1454651 : Blo 968591 1454651 := bstep (se 1 (by rfl) ⟨1090988, by rfl⟩ : syracuseStep 1454651 = 2181977) B2181977
theorem B1454711 : Blo 968591 1454711 := bstep (se 1 (by rfl) ⟨1091033, by rfl⟩ : syracuseStep 1454711 = 2182067) B2182067
theorem B1454735 : Blo 968591 1454735 := bstep (se 1 (by rfl) ⟨1091051, by rfl⟩ : syracuseStep 1454735 = 2182103) B2182103
theorem B1454777 : Blo 968591 1454777 := bstep (se 2 (by rfl) ⟨545541, by rfl⟩ : syracuseStep 1454777 = 1091083) B1091083
theorem B1454855 : Blo 968591 1454855 := bstep (se 1 (by rfl) ⟨1091141, by rfl⟩ : syracuseStep 1454855 = 2182283) B2182283
theorem B1454891 : Blo 968591 1454891 := bstep (se 1 (by rfl) ⟨1091168, by rfl⟩ : syracuseStep 1454891 = 2182337) B2182337
theorem B1454921 : Blo 968591 1454921 := bstep (se 2 (by rfl) ⟨545595, by rfl⟩ : syracuseStep 1454921 = 1091191) B1091191
theorem B1455035 : Blo 968591 1455035 := bstep (se 1 (by rfl) ⟨1091276, by rfl⟩ : syracuseStep 1455035 = 2182553) B2182553
theorem B1455095 : Blo 968591 1455095 := bstep (se 1 (by rfl) ⟨1091321, by rfl⟩ : syracuseStep 1455095 = 2182643) B2182643
theorem B9974789 : Blo 968591 9974789 := bstep (se 4 (by rfl) ⟨935136, by rfl⟩ : syracuseStep 9974789 = 1870273) B1870273
theorem B1455119 : Blo 968591 1455119 := bstep (se 1 (by rfl) ⟨1091339, by rfl⟩ : syracuseStep 1455119 = 2182679) B2182679
theorem B1455161 : Blo 968591 1455161 := bstep (se 2 (by rfl) ⟨545685, by rfl⟩ : syracuseStep 1455161 = 1091371) B1091371
theorem B1455239 : Blo 968591 1455239 := bstep (se 1 (by rfl) ⟨1091429, by rfl⟩ : syracuseStep 1455239 = 2182859) B2182859
theorem B1455275 : Blo 968591 1455275 := bstep (se 1 (by rfl) ⟨1091456, by rfl⟩ : syracuseStep 1455275 = 2182913) B2182913
theorem B1455305 : Blo 968591 1455305 := bstep (se 2 (by rfl) ⟨545739, by rfl⟩ : syracuseStep 1455305 = 1091479) B1091479
theorem B1455419 : Blo 968591 1455419 := bstep (se 1 (by rfl) ⟨1091564, by rfl⟩ : syracuseStep 1455419 = 2183129) B2183129
theorem B1455479 : Blo 968591 1455479 := bstep (se 1 (by rfl) ⟨1091609, by rfl⟩ : syracuseStep 1455479 = 2183219) B2183219
theorem B1455503 : Blo 968591 1455503 := bstep (se 1 (by rfl) ⟨1091627, by rfl⟩ : syracuseStep 1455503 = 2183255) B2183255
theorem B1455545 : Blo 968591 1455545 := bstep (se 2 (by rfl) ⟨545829, by rfl⟩ : syracuseStep 1455545 = 1091659) B1091659
theorem B1455623 : Blo 968591 1455623 := bstep (se 1 (by rfl) ⟨1091717, by rfl⟩ : syracuseStep 1455623 = 2183435) B2183435
theorem B1455659 : Blo 968591 1455659 := bstep (se 1 (by rfl) ⟨1091744, by rfl⟩ : syracuseStep 1455659 = 2183489) B2183489
theorem B1455689 : Blo 968591 1455689 := bstep (se 2 (by rfl) ⟨545883, by rfl⟩ : syracuseStep 1455689 = 1091767) B1091767
theorem B1455803 : Blo 968591 1455803 := bstep (se 1 (by rfl) ⟨1091852, by rfl⟩ : syracuseStep 1455803 = 2183705) B2183705
theorem B1455863 : Blo 968591 1455863 := bstep (se 1 (by rfl) ⟨1091897, by rfl⟩ : syracuseStep 1455863 = 2183795) B2183795
theorem B1455887 : Blo 968591 1455887 := bstep (se 1 (by rfl) ⟨1091915, by rfl⟩ : syracuseStep 1455887 = 2183831) B2183831
theorem B1455929 : Blo 968591 1455929 := bstep (se 2 (by rfl) ⟨545973, by rfl⟩ : syracuseStep 1455929 = 1091947) B1091947
theorem B1456007 : Blo 968591 1456007 := bstep (se 1 (by rfl) ⟨1092005, by rfl⟩ : syracuseStep 1456007 = 2184011) B2184011
theorem B1456043 : Blo 968591 1456043 := bstep (se 1 (by rfl) ⟨1092032, by rfl⟩ : syracuseStep 1456043 = 2184065) B2184065
theorem B1456073 : Blo 968591 1456073 := bstep (se 2 (by rfl) ⟨546027, by rfl⟩ : syracuseStep 1456073 = 1092055) B1092055
theorem B3684305 : Blo 968591 3684305 := bstep (se 2 (by rfl) ⟨1381614, by rfl⟩ : syracuseStep 3684305 = 2763229) B2763229
theorem B1456187 : Blo 968591 1456187 := bstep (se 1 (by rfl) ⟨1092140, by rfl⟩ : syracuseStep 1456187 = 2184281) B2184281
theorem B1456247 : Blo 968591 1456247 := bstep (se 1 (by rfl) ⟨1092185, by rfl⟩ : syracuseStep 1456247 = 2184371) B2184371
theorem B1456271 : Blo 968591 1456271 := bstep (se 1 (by rfl) ⟨1092203, by rfl⟩ : syracuseStep 1456271 = 2184407) B2184407
theorem B1456313 : Blo 968591 1456313 := bstep (se 2 (by rfl) ⟨546117, by rfl⟩ : syracuseStep 1456313 = 1092235) B1092235
theorem B12957941 : Blo 968591 12957941 := bstep (se 5 (by rfl) ⟨607403, by rfl⟩ : syracuseStep 12957941 = 1214807) B1214807
theorem B1456391 : Blo 968591 1456391 := bstep (se 1 (by rfl) ⟨1092293, by rfl⟩ : syracuseStep 1456391 = 2184587) B2184587
theorem B8304929 : Blo 968591 8304929 := bstep (se 2 (by rfl) ⟨3114348, by rfl⟩ : syracuseStep 8304929 = 6228697) B6228697
theorem B1456427 : Blo 968591 1456427 := bstep (se 1 (by rfl) ⟨1092320, by rfl⟩ : syracuseStep 1456427 = 2184641) B2184641
theorem B1751339 : Blo 968591 1751339 := bstep (se 1 (by rfl) ⟨1313504, by rfl⟩ : syracuseStep 1751339 = 2627009) B2627009
theorem B1456457 : Blo 968591 1456457 := bstep (se 2 (by rfl) ⟨546171, by rfl⟩ : syracuseStep 1456457 = 1092343) B1092343
theorem B95566229 : Blo 968591 95566229 := bstep (se 6 (by rfl) ⟨2239833, by rfl⟩ : syracuseStep 95566229 = 4479667) B4479667
theorem B3684761 : Blo 968591 3684761 := bstep (se 2 (by rfl) ⟨1381785, by rfl⟩ : syracuseStep 3684761 = 2763571) B2763571
theorem B4143545 : Blo 968591 4143545 := bstep (se 2 (by rfl) ⟨1553829, by rfl⟩ : syracuseStep 4143545 = 3107659) B3107659
theorem B1456571 : Blo 968591 1456571 := bstep (se 1 (by rfl) ⟨1092428, by rfl⟩ : syracuseStep 1456571 = 2184857) B2184857
theorem B1456631 : Blo 968591 1456631 := bstep (se 1 (by rfl) ⟨1092473, by rfl⟩ : syracuseStep 1456631 = 2184947) B2184947
theorem B1456655 : Blo 968591 1456655 := bstep (se 1 (by rfl) ⟨1092491, by rfl⟩ : syracuseStep 1456655 = 2184983) B2184983
theorem B2767375 : Blo 968591 2767375 := bstep (se 1 (by rfl) ⟨2075531, by rfl⟩ : syracuseStep 2767375 = 4151063) B4151063
theorem B1227307 : Blo 968591 1227307 := bstep (se 1 (by rfl) ⟨920480, by rfl⟩ : syracuseStep 1227307 = 1840961) B1840961
theorem B1456697 : Blo 968591 1456697 := bstep (se 2 (by rfl) ⟨546261, by rfl⟩ : syracuseStep 1456697 = 1092523) B1092523
theorem B2767421 : Blo 968591 2767421 := bstep (se 3 (by rfl) ⟨518891, by rfl⟩ : syracuseStep 2767421 = 1037783) B1037783
theorem B1456775 : Blo 968591 1456775 := bstep (se 1 (by rfl) ⟨1092581, by rfl⟩ : syracuseStep 1456775 = 2185163) B2185163
theorem B1456811 : Blo 968591 1456811 := bstep (se 1 (by rfl) ⟨1092608, by rfl⟩ : syracuseStep 1456811 = 2185217) B2185217
theorem B1456841 : Blo 968591 1456841 := bstep (se 2 (by rfl) ⟨546315, by rfl⟩ : syracuseStep 1456841 = 1092631) B1092631
theorem B1456955 : Blo 968591 1456955 := bstep (se 1 (by rfl) ⟨1092716, by rfl⟩ : syracuseStep 1456955 = 2185433) B2185433
theorem B1457015 : Blo 968591 1457015 := bstep (se 1 (by rfl) ⟨1092761, by rfl⟩ : syracuseStep 1457015 = 2185523) B2185523
theorem B1457039 : Blo 968591 1457039 := bstep (se 1 (by rfl) ⟨1092779, by rfl⟩ : syracuseStep 1457039 = 2185559) B2185559
theorem B2767763 : Blo 968591 2767763 := bstep (se 1 (by rfl) ⟨2075822, by rfl⟩ : syracuseStep 2767763 = 4151645) B4151645
theorem B1457081 : Blo 968591 1457081 := bstep (se 2 (by rfl) ⟨546405, by rfl⟩ : syracuseStep 1457081 = 1092811) B1092811
theorem B1457159 : Blo 968591 1457159 := bstep (se 1 (by rfl) ⟨1092869, by rfl⟩ : syracuseStep 1457159 = 2185739) B2185739
theorem B11811851 : Blo 968591 11811851 := bstep (se 1 (by rfl) ⟨8858888, by rfl⟩ : syracuseStep 11811851 = 17717777) B17717777
theorem B1457195 : Blo 968591 1457195 := bstep (se 1 (by rfl) ⟨1092896, by rfl⟩ : syracuseStep 1457195 = 2185793) B2185793
theorem B1457225 : Blo 968591 1457225 := bstep (se 2 (by rfl) ⟨546459, by rfl⟩ : syracuseStep 1457225 = 1092919) B1092919
theorem B1457339 : Blo 968591 1457339 := bstep (se 1 (by rfl) ⟨1093004, by rfl⟩ : syracuseStep 1457339 = 2186009) B2186009
theorem B1457399 : Blo 968591 1457399 := bstep (se 1 (by rfl) ⟨1093049, by rfl⟩ : syracuseStep 1457399 = 2186099) B2186099
theorem B1457423 : Blo 968591 1457423 := bstep (se 1 (by rfl) ⟨1093067, by rfl⟩ : syracuseStep 1457423 = 2186135) B2186135
theorem B1457465 : Blo 968591 1457465 := bstep (se 2 (by rfl) ⟨546549, by rfl⟩ : syracuseStep 1457465 = 1093099) B1093099
theorem B1457543 : Blo 968591 1457543 := bstep (se 1 (by rfl) ⟨1093157, by rfl⟩ : syracuseStep 1457543 = 2186315) B2186315
theorem B1457579 : Blo 968591 1457579 := bstep (se 1 (by rfl) ⟨1093184, by rfl⟩ : syracuseStep 1457579 = 2186369) B2186369
theorem B1457609 : Blo 968591 1457609 := bstep (se 2 (by rfl) ⟨546603, by rfl⟩ : syracuseStep 1457609 = 1093207) B1093207
theorem B1228279 : Blo 968591 1228279 := bstep (se 1 (by rfl) ⟨921209, by rfl⟩ : syracuseStep 1228279 = 1842419) B1842419
theorem B5520899 : Blo 968591 5520899 := bstep (se 1 (by rfl) ⟨4140674, by rfl⟩ : syracuseStep 5520899 = 8281349) B8281349
theorem B3685931 : Blo 968591 3685931 := bstep (se 1 (by rfl) ⟨2764448, by rfl⟩ : syracuseStep 3685931 = 5528897) B5528897
theorem B1457723 : Blo 968591 1457723 := bstep (se 1 (by rfl) ⟨1093292, by rfl⟩ : syracuseStep 1457723 = 2186585) B2186585
theorem B1457783 : Blo 968591 1457783 := bstep (se 1 (by rfl) ⟨1093337, by rfl⟩ : syracuseStep 1457783 = 2186675) B2186675
theorem B1457807 : Blo 968591 1457807 := bstep (se 1 (by rfl) ⟨1093355, by rfl⟩ : syracuseStep 1457807 = 2186711) B2186711
theorem B1457849 : Blo 968591 1457849 := bstep (se 2 (by rfl) ⟨546693, by rfl⟩ : syracuseStep 1457849 = 1093387) B1093387
theorem B1457927 : Blo 968591 1457927 := bstep (se 1 (by rfl) ⟨1093445, by rfl⟩ : syracuseStep 1457927 = 2186891) B2186891
theorem B2768651 : Blo 968591 2768651 := bstep (se 1 (by rfl) ⟨2076488, by rfl⟩ : syracuseStep 2768651 = 4152977) B4152977
theorem B1556239 : Blo 968591 1556239 := bstep (se 1 (by rfl) ⟨1167179, by rfl⟩ : syracuseStep 1556239 = 2334359) B2334359
theorem B2801441 : Blo 968591 2801441 := bstep (se 2 (by rfl) ⟨1050540, by rfl⟩ : syracuseStep 2801441 = 2101081) B2101081
theorem B1457963 : Blo 968591 1457963 := bstep (se 1 (by rfl) ⟨1093472, by rfl⟩ : syracuseStep 1457963 = 2186945) B2186945
theorem B1228603 : Blo 968591 1228603 := bstep (se 1 (by rfl) ⟨921452, by rfl⟩ : syracuseStep 1228603 = 1842905) B1842905
theorem B1457993 : Blo 968591 1457993 := bstep (se 2 (by rfl) ⟨546747, by rfl⟩ : syracuseStep 1457993 = 1093495) B1093495
theorem B1458107 : Blo 968591 1458107 := bstep (se 1 (by rfl) ⟨1093580, by rfl⟩ : syracuseStep 1458107 = 2187161) B2187161
theorem B5521355 : Blo 968591 5521355 := bstep (se 1 (by rfl) ⟨4141016, by rfl⟩ : syracuseStep 5521355 = 8282033) B8282033
theorem B1458167 : Blo 968591 1458167 := bstep (se 1 (by rfl) ⟨1093625, by rfl⟩ : syracuseStep 1458167 = 2187251) B2187251
theorem B1458191 : Blo 968591 1458191 := bstep (se 1 (by rfl) ⟨1093643, by rfl⟩ : syracuseStep 1458191 = 2187287) B2187287
theorem B1458233 : Blo 968591 1458233 := bstep (se 2 (by rfl) ⟨546837, by rfl⟩ : syracuseStep 1458233 = 1093675) B1093675
theorem B1458311 : Blo 968591 1458311 := bstep (se 1 (by rfl) ⟨1093733, by rfl⟩ : syracuseStep 1458311 = 2187467) B2187467
theorem B2244755 : Blo 968591 2244755 := bstep (se 1 (by rfl) ⟨1683566, by rfl⟩ : syracuseStep 2244755 = 3367133) B3367133
theorem B1458347 : Blo 968591 1458347 := bstep (se 1 (by rfl) ⟨1093760, by rfl⟩ : syracuseStep 1458347 = 2187521) B2187521
theorem B1458377 : Blo 968591 1458377 := bstep (se 2 (by rfl) ⟨546891, by rfl⟩ : syracuseStep 1458377 = 1093783) B1093783
theorem B1458491 : Blo 968591 1458491 := bstep (se 1 (by rfl) ⟨1093868, by rfl⟩ : syracuseStep 1458491 = 2187737) B2187737
theorem B1458551 : Blo 968591 1458551 := bstep (se 1 (by rfl) ⟨1093913, by rfl⟩ : syracuseStep 1458551 = 2187827) B2187827
theorem B1458575 : Blo 968591 1458575 := bstep (se 1 (by rfl) ⟨1093931, by rfl⟩ : syracuseStep 1458575 = 2187863) B2187863
theorem B2179475 : Blo 968591 2179475 := bstep (se 1 (by rfl) ⟨1634606, by rfl⟩ : syracuseStep 2179475 = 3269213) B3269213
theorem B1458617 : Blo 968591 1458617 := bstep (se 2 (by rfl) ⟨546981, by rfl⟩ : syracuseStep 1458617 = 1093963) B1093963
theorem B2179529 : Blo 968591 2179529 := bstep (se 2 (by rfl) ⟨817323, by rfl⟩ : syracuseStep 2179529 = 1634647) B1634647
theorem B79577585 : Blo 968591 79577585 := bstep (se 2 (by rfl) ⟨29841594, by rfl⟩ : syracuseStep 79577585 = 59683189) B59683189
theorem B1458695 : Blo 968591 1458695 := bstep (se 1 (by rfl) ⟨1094021, by rfl⟩ : syracuseStep 1458695 = 2188043) B2188043
theorem B1458731 : Blo 968591 1458731 := bstep (se 1 (by rfl) ⟨1094048, by rfl⟩ : syracuseStep 1458731 = 2188097) B2188097
theorem B1458761 : Blo 968591 1458761 := bstep (se 2 (by rfl) ⟨547035, by rfl⟩ : syracuseStep 1458761 = 1094071) B1094071
theorem B5522039 : Blo 968591 5522039 := bstep (se 1 (by rfl) ⟨4141529, by rfl⟩ : syracuseStep 5522039 = 8283059) B8283059
theorem B8307319 : Blo 968591 8307319 := bstep (se 1 (by rfl) ⟨6230489, by rfl⟩ : syracuseStep 8307319 = 12460979) B12460979
theorem B1458875 : Blo 968591 1458875 := bstep (se 1 (by rfl) ⟨1094156, by rfl⟩ : syracuseStep 1458875 = 2188313) B2188313
theorem B1229575 : Blo 968591 1229575 := bstep (se 1 (by rfl) ⟨922181, by rfl⟩ : syracuseStep 1229575 = 1844363) B1844363
theorem B2180231 : Blo 968591 2180231 := bstep (se 1 (by rfl) ⟨1635173, by rfl⟩ : syracuseStep 2180231 = 3270347) B3270347
theorem B1229995 : Blo 968591 1229995 := bstep (se 1 (by rfl) ⟨922496, by rfl⟩ : syracuseStep 1229995 = 1844993) B1844993
theorem B2180411 : Blo 968591 2180411 := bstep (se 1 (by rfl) ⟨1635308, by rfl⟩ : syracuseStep 2180411 = 3270617) B3270617
theorem B1230223 : Blo 968591 1230223 := bstep (se 1 (by rfl) ⟨922667, by rfl⟩ : syracuseStep 1230223 = 1845335) B1845335
theorem B2180537 : Blo 968591 2180537 := bstep (se 2 (by rfl) ⟨817701, by rfl⟩ : syracuseStep 2180537 = 1635403) B1635403
theorem B3687889 : Blo 968591 3687889 := bstep (se 2 (by rfl) ⟨1382958, by rfl⟩ : syracuseStep 3687889 = 2765917) B2765917
theorem B19908125 : Blo 968591 19908125 := bstep (se 3 (by rfl) ⟨3732773, by rfl⟩ : syracuseStep 19908125 = 7465547) B7465547
theorem B3688193 : Blo 968591 3688193 := bstep (se 2 (by rfl) ⟨1383072, by rfl⟩ : syracuseStep 3688193 = 2766145) B2766145
theorem B2180879 : Blo 968591 2180879 := bstep (se 1 (by rfl) ⟨1635659, by rfl⟩ : syracuseStep 2180879 = 3271319) B3271319
theorem B2180897 : Blo 968591 2180897 := bstep (se 2 (by rfl) ⟨817836, by rfl⟩ : syracuseStep 2180897 = 1635673) B1635673
theorem B1165099 : Blo 968591 1165099 := bstep (se 1 (by rfl) ⟨873824, by rfl⟩ : syracuseStep 1165099 = 1747649) B1747649
theorem B968591 : Blo 968591 968591 := bstep (se 1 (by rfl) ⟨726443, by rfl⟩ : syracuseStep 968591 = 1452887) B1452887
theorem B968635 : Blo 968591 968635 := bstep (se 1 (by rfl) ⟨726476, by rfl⟩ : syracuseStep 968635 = 1452953) B1452953
theorem B968711 : Blo 968591 968711 := bstep (se 1 (by rfl) ⟨726533, by rfl⟩ : syracuseStep 968711 = 1453067) B1453067
theorem B968719 : Blo 968591 968719 := bstep (se 1 (by rfl) ⟨726539, by rfl⟩ : syracuseStep 968719 = 1453079) B1453079
theorem B968763 : Blo 968591 968763 := bstep (se 1 (by rfl) ⟨726572, by rfl⟩ : syracuseStep 968763 = 1453145) B1453145
theorem B7358525 : Blo 968591 7358525 := bstep (se 3 (by rfl) ⟨1379723, by rfl⟩ : syracuseStep 7358525 = 2759447) B2759447
theorem B2181239 : Blo 968591 2181239 := bstep (se 1 (by rfl) ⟨1635929, by rfl⟩ : syracuseStep 2181239 = 3271859) B3271859
theorem B968839 : Blo 968591 968839 := bstep (se 1 (by rfl) ⟨726629, by rfl⟩ : syracuseStep 968839 = 1453259) B1453259
theorem B968847 : Blo 968591 968847 := bstep (se 1 (by rfl) ⟨726635, by rfl⟩ : syracuseStep 968847 = 1453271) B1453271
theorem B968891 : Blo 968591 968891 := bstep (se 1 (by rfl) ⟨726668, by rfl⟩ : syracuseStep 968891 = 1453337) B1453337
theorem B3688649 : Blo 968591 3688649 := bstep (se 2 (by rfl) ⟨1383243, by rfl⟩ : syracuseStep 3688649 = 2766487) B2766487
theorem B968967 : Blo 968591 968967 := bstep (se 1 (by rfl) ⟨726725, by rfl⟩ : syracuseStep 968967 = 1453451) B1453451
theorem B968975 : Blo 968591 968975 := bstep (se 1 (by rfl) ⟨726731, by rfl⟩ : syracuseStep 968975 = 1453463) B1453463
theorem B2181419 : Blo 968591 2181419 := bstep (se 1 (by rfl) ⟨1636064, by rfl⟩ : syracuseStep 2181419 = 3272129) B3272129
theorem B969019 : Blo 968591 969019 := bstep (se 1 (by rfl) ⟨726764, by rfl⟩ : syracuseStep 969019 = 1453529) B1453529
theorem B969095 : Blo 968591 969095 := bstep (se 1 (by rfl) ⟨726821, by rfl⟩ : syracuseStep 969095 = 1453643) B1453643
theorem B969103 : Blo 968591 969103 := bstep (se 1 (by rfl) ⟨726827, by rfl⟩ : syracuseStep 969103 = 1453655) B1453655
theorem B969147 : Blo 968591 969147 := bstep (se 1 (by rfl) ⟨726860, by rfl⟩ : syracuseStep 969147 = 1453721) B1453721
theorem B969223 : Blo 968591 969223 := bstep (se 1 (by rfl) ⟨726917, by rfl⟩ : syracuseStep 969223 = 1453835) B1453835
theorem B969231 : Blo 968591 969231 := bstep (se 1 (by rfl) ⟨726923, by rfl⟩ : syracuseStep 969231 = 1453847) B1453847
theorem B5523997 : Blo 968591 5523997 := bstep (se 3 (by rfl) ⟨1035749, by rfl⟩ : syracuseStep 5523997 = 2071499) B2071499
theorem B969275 : Blo 968591 969275 := bstep (se 1 (by rfl) ⟨726956, by rfl⟩ : syracuseStep 969275 = 1453913) B1453913
theorem B969351 : Blo 968591 969351 := bstep (se 1 (by rfl) ⟨727013, by rfl⟩ : syracuseStep 969351 = 1454027) B1454027
theorem B969359 : Blo 968591 969359 := bstep (se 1 (by rfl) ⟨727019, by rfl⟩ : syracuseStep 969359 = 1454039) B1454039
theorem B2181779 : Blo 968591 2181779 := bstep (se 1 (by rfl) ⟨1636334, by rfl⟩ : syracuseStep 2181779 = 3272669) B3272669
theorem B969403 : Blo 968591 969403 := bstep (se 1 (by rfl) ⟨727052, by rfl⟩ : syracuseStep 969403 = 1454105) B1454105
theorem B2181833 : Blo 968591 2181833 := bstep (se 2 (by rfl) ⟨818187, by rfl⟩ : syracuseStep 2181833 = 1636375) B1636375
theorem B99830485 : Blo 968591 99830485 := bstep (se 7 (by rfl) ⟨1169888, by rfl⟩ : syracuseStep 99830485 = 2339777) B2339777
theorem B969479 : Blo 968591 969479 := bstep (se 1 (by rfl) ⟨727109, by rfl⟩ : syracuseStep 969479 = 1454219) B1454219
theorem B969487 : Blo 968591 969487 := bstep (se 1 (by rfl) ⟨727115, by rfl⟩ : syracuseStep 969487 = 1454231) B1454231
theorem B969531 : Blo 968591 969531 := bstep (se 1 (by rfl) ⟨727148, by rfl⟩ : syracuseStep 969531 = 1454297) B1454297
theorem B969607 : Blo 968591 969607 := bstep (se 1 (by rfl) ⟨727205, by rfl⟩ : syracuseStep 969607 = 1454411) B1454411
theorem B969615 : Blo 968591 969615 := bstep (se 1 (by rfl) ⟨727211, by rfl⟩ : syracuseStep 969615 = 1454423) B1454423
theorem B969659 : Blo 968591 969659 := bstep (se 1 (by rfl) ⟨727244, by rfl⟩ : syracuseStep 969659 = 1454489) B1454489
theorem B969735 : Blo 968591 969735 := bstep (se 1 (by rfl) ⟨727301, by rfl⟩ : syracuseStep 969735 = 1454603) B1454603
theorem B969743 : Blo 968591 969743 := bstep (se 1 (by rfl) ⟨727307, by rfl⟩ : syracuseStep 969743 = 1454615) B1454615
theorem B5524523 : Blo 968591 5524523 := bstep (se 1 (by rfl) ⟨4143392, by rfl⟩ : syracuseStep 5524523 = 8286785) B8286785
theorem B969787 : Blo 968591 969787 := bstep (se 1 (by rfl) ⟨727340, by rfl⟩ : syracuseStep 969787 = 1454681) B1454681
theorem B969863 : Blo 968591 969863 := bstep (se 1 (by rfl) ⟨727397, by rfl⟩ : syracuseStep 969863 = 1454795) B1454795
theorem B969871 : Blo 968591 969871 := bstep (se 1 (by rfl) ⟨727403, by rfl⟩ : syracuseStep 969871 = 1454807) B1454807
theorem B1035451 : Blo 968591 1035451 := bstep (se 1 (by rfl) ⟨776588, by rfl⟩ : syracuseStep 1035451 = 1553177) B1553177
theorem B969915 : Blo 968591 969915 := bstep (se 1 (by rfl) ⟨727436, by rfl⟩ : syracuseStep 969915 = 1454873) B1454873
theorem B23317741 : Blo 968591 23317741 := bstep (se 3 (by rfl) ⟨4372076, by rfl⟩ : syracuseStep 23317741 = 8744153) B8744153
theorem B969991 : Blo 968591 969991 := bstep (se 1 (by rfl) ⟨727493, by rfl⟩ : syracuseStep 969991 = 1454987) B1454987
theorem B969999 : Blo 968591 969999 := bstep (se 1 (by rfl) ⟨727499, by rfl⟩ : syracuseStep 969999 = 1454999) B1454999
theorem B970043 : Blo 968591 970043 := bstep (se 1 (by rfl) ⟨727532, by rfl⟩ : syracuseStep 970043 = 1455065) B1455065
theorem B2182535 : Blo 968591 2182535 := bstep (se 1 (by rfl) ⟨1636901, by rfl⟩ : syracuseStep 2182535 = 3273803) B3273803
theorem B970119 : Blo 968591 970119 := bstep (se 1 (by rfl) ⟨727589, by rfl⟩ : syracuseStep 970119 = 1455179) B1455179
theorem B970127 : Blo 968591 970127 := bstep (se 1 (by rfl) ⟨727595, by rfl⟩ : syracuseStep 970127 = 1455191) B1455191
theorem B970171 : Blo 968591 970171 := bstep (se 1 (by rfl) ⟨727628, by rfl⟩ : syracuseStep 970171 = 1455257) B1455257
theorem B970247 : Blo 968591 970247 := bstep (se 1 (by rfl) ⟨727685, by rfl⟩ : syracuseStep 970247 = 1455371) B1455371
theorem B970255 : Blo 968591 970255 := bstep (se 1 (by rfl) ⟨727691, by rfl⟩ : syracuseStep 970255 = 1455383) B1455383
theorem B1166891 : Blo 968591 1166891 := bstep (se 1 (by rfl) ⟨875168, by rfl⟩ : syracuseStep 1166891 = 1750337) B1750337
theorem B2182715 : Blo 968591 2182715 := bstep (se 1 (by rfl) ⟨1637036, by rfl⟩ : syracuseStep 2182715 = 3274073) B3274073
theorem B970299 : Blo 968591 970299 := bstep (se 1 (by rfl) ⟨727724, by rfl⟩ : syracuseStep 970299 = 1455449) B1455449
theorem B2805367 : Blo 968591 2805367 := bstep (se 1 (by rfl) ⟨2104025, by rfl⟩ : syracuseStep 2805367 = 4208051) B4208051
theorem B970375 : Blo 968591 970375 := bstep (se 1 (by rfl) ⟨727781, by rfl⟩ : syracuseStep 970375 = 1455563) B1455563
theorem B970383 : Blo 968591 970383 := bstep (se 1 (by rfl) ⟨727787, by rfl⟩ : syracuseStep 970383 = 1455575) B1455575
theorem B2182841 : Blo 968591 2182841 := bstep (se 2 (by rfl) ⟨818565, by rfl⟩ : syracuseStep 2182841 = 1637131) B1637131
theorem B970427 : Blo 968591 970427 := bstep (se 1 (by rfl) ⟨727820, by rfl⟩ : syracuseStep 970427 = 1455641) B1455641
theorem B970503 : Blo 968591 970503 := bstep (se 1 (by rfl) ⟨727877, by rfl⟩ : syracuseStep 970503 = 1455755) B1455755
theorem B970511 : Blo 968591 970511 := bstep (se 1 (by rfl) ⟨727883, by rfl⟩ : syracuseStep 970511 = 1455767) B1455767
theorem B970555 : Blo 968591 970555 := bstep (se 1 (by rfl) ⟨727916, by rfl⟩ : syracuseStep 970555 = 1455833) B1455833
theorem B4673369 : Blo 968591 4673369 := bstep (se 2 (by rfl) ⟨1752513, by rfl⟩ : syracuseStep 4673369 = 3505027) B3505027
theorem B970631 : Blo 968591 970631 := bstep (se 1 (by rfl) ⟨727973, by rfl⟩ : syracuseStep 970631 = 1455947) B1455947
theorem B970639 : Blo 968591 970639 := bstep (se 1 (by rfl) ⟨727979, by rfl⟩ : syracuseStep 970639 = 1455959) B1455959
theorem B970683 : Blo 968591 970683 := bstep (se 1 (by rfl) ⟨728012, by rfl⟩ : syracuseStep 970683 = 1456025) B1456025
theorem B970759 : Blo 968591 970759 := bstep (se 1 (by rfl) ⟨728069, by rfl⟩ : syracuseStep 970759 = 1456139) B1456139
theorem B2183183 : Blo 968591 2183183 := bstep (se 1 (by rfl) ⟨1637387, by rfl⟩ : syracuseStep 2183183 = 3274775) B3274775
theorem B970767 : Blo 968591 970767 := bstep (se 1 (by rfl) ⟨728075, by rfl⟩ : syracuseStep 970767 = 1456151) B1456151
theorem B2183201 : Blo 968591 2183201 := bstep (se 2 (by rfl) ⟨818700, by rfl⟩ : syracuseStep 2183201 = 1637401) B1637401
theorem B970811 : Blo 968591 970811 := bstep (se 1 (by rfl) ⟨728108, by rfl⟩ : syracuseStep 970811 = 1456217) B1456217
theorem B3493955 : Blo 968591 3493955 := bstep (se 1 (by rfl) ⟨2620466, by rfl⟩ : syracuseStep 3493955 = 5240933) B5240933
theorem B970887 : Blo 968591 970887 := bstep (se 1 (by rfl) ⟨728165, by rfl⟩ : syracuseStep 970887 = 1456331) B1456331
theorem B970895 : Blo 968591 970895 := bstep (se 1 (by rfl) ⟨728171, by rfl⟩ : syracuseStep 970895 = 1456343) B1456343
theorem B970939 : Blo 968591 970939 := bstep (se 1 (by rfl) ⟨728204, by rfl⟩ : syracuseStep 970939 = 1456409) B1456409
theorem B971015 : Blo 968591 971015 := bstep (se 1 (by rfl) ⟨728261, by rfl⟩ : syracuseStep 971015 = 1456523) B1456523
theorem B971023 : Blo 968591 971023 := bstep (se 1 (by rfl) ⟨728267, by rfl⟩ : syracuseStep 971023 = 1456535) B1456535
theorem B971067 : Blo 968591 971067 := bstep (se 1 (by rfl) ⟨728300, by rfl⟩ : syracuseStep 971067 = 1456601) B1456601
theorem B2183543 : Blo 968591 2183543 := bstep (se 1 (by rfl) ⟨1637657, by rfl⟩ : syracuseStep 2183543 = 3275315) B3275315
theorem B971143 : Blo 968591 971143 := bstep (se 1 (by rfl) ⟨728357, by rfl⟩ : syracuseStep 971143 = 1456715) B1456715
theorem B971151 : Blo 968591 971151 := bstep (se 1 (by rfl) ⟨728363, by rfl⟩ : syracuseStep 971151 = 1456727) B1456727
theorem B971195 : Blo 968591 971195 := bstep (se 1 (by rfl) ⟨728396, by rfl⟩ : syracuseStep 971195 = 1456793) B1456793
theorem B2216393 : Blo 968591 2216393 := bstep (se 2 (by rfl) ⟨831147, by rfl⟩ : syracuseStep 2216393 = 1662295) B1662295
theorem B5525981 : Blo 968591 5525981 := bstep (se 3 (by rfl) ⟨1036121, by rfl⟩ : syracuseStep 5525981 = 2072243) B2072243
theorem B971271 : Blo 968591 971271 := bstep (se 1 (by rfl) ⟨728453, by rfl⟩ : syracuseStep 971271 = 1456907) B1456907
theorem B971279 : Blo 968591 971279 := bstep (se 1 (by rfl) ⟨728459, by rfl⟩ : syracuseStep 971279 = 1456919) B1456919
theorem B2183723 : Blo 968591 2183723 := bstep (se 1 (by rfl) ⟨1637792, by rfl⟩ : syracuseStep 2183723 = 3275585) B3275585
theorem B971323 : Blo 968591 971323 := bstep (se 1 (by rfl) ⟨728492, by rfl⟩ : syracuseStep 971323 = 1456985) B1456985
theorem B971399 : Blo 968591 971399 := bstep (se 1 (by rfl) ⟨728549, by rfl⟩ : syracuseStep 971399 = 1457099) B1457099
theorem B971407 : Blo 968591 971407 := bstep (se 1 (by rfl) ⟨728555, by rfl⟩ : syracuseStep 971407 = 1457111) B1457111
theorem B971451 : Blo 968591 971451 := bstep (se 1 (by rfl) ⟨728588, by rfl⟩ : syracuseStep 971451 = 1457177) B1457177
theorem B7000769 : Blo 968591 7000769 := bstep (se 2 (by rfl) ⟨2625288, by rfl⟩ : syracuseStep 7000769 = 5250577) B5250577
theorem B971527 : Blo 968591 971527 := bstep (se 1 (by rfl) ⟨728645, by rfl⟩ : syracuseStep 971527 = 1457291) B1457291
theorem B971535 : Blo 968591 971535 := bstep (se 1 (by rfl) ⟨728651, by rfl⟩ : syracuseStep 971535 = 1457303) B1457303
theorem B4903739 : Blo 968591 4903739 := bstep (se 1 (by rfl) ⟨3677804, by rfl⟩ : syracuseStep 4903739 = 7355609) B7355609
theorem B971579 : Blo 968591 971579 := bstep (se 1 (by rfl) ⟨728684, by rfl⟩ : syracuseStep 971579 = 1457369) B1457369
theorem B971655 : Blo 968591 971655 := bstep (se 1 (by rfl) ⟨728741, by rfl⟩ : syracuseStep 971655 = 1457483) B1457483
theorem B971663 : Blo 968591 971663 := bstep (se 1 (by rfl) ⟨728747, by rfl⟩ : syracuseStep 971663 = 1457495) B1457495
theorem B2184083 : Blo 968591 2184083 := bstep (se 1 (by rfl) ⟨1638062, by rfl⟩ : syracuseStep 2184083 = 3276125) B3276125
theorem B971707 : Blo 968591 971707 := bstep (se 1 (by rfl) ⟨728780, by rfl⟩ : syracuseStep 971707 = 1457561) B1457561
theorem B2184137 : Blo 968591 2184137 := bstep (se 2 (by rfl) ⟨819051, by rfl⟩ : syracuseStep 2184137 = 1638103) B1638103
theorem B4903901 : Blo 968591 4903901 := bstep (se 3 (by rfl) ⟨919481, by rfl⟩ : syracuseStep 4903901 = 1838963) B1838963
theorem B971783 : Blo 968591 971783 := bstep (se 1 (by rfl) ⟨728837, by rfl⟩ : syracuseStep 971783 = 1457675) B1457675
theorem B971791 : Blo 968591 971791 := bstep (se 1 (by rfl) ⟨728843, by rfl⟩ : syracuseStep 971791 = 1457687) B1457687
theorem B971835 : Blo 968591 971835 := bstep (se 1 (by rfl) ⟨728876, by rfl⟩ : syracuseStep 971835 = 1457753) B1457753
theorem B18928727 : Blo 968591 18928727 := bstep (se 1 (by rfl) ⟨14196545, by rfl⟩ : syracuseStep 18928727 = 28393091) B28393091
theorem B971911 : Blo 968591 971911 := bstep (se 1 (by rfl) ⟨728933, by rfl⟩ : syracuseStep 971911 = 1457867) B1457867
theorem B971919 : Blo 968591 971919 := bstep (se 1 (by rfl) ⟨728939, by rfl⟩ : syracuseStep 971919 = 1457879) B1457879
theorem B971963 : Blo 968591 971963 := bstep (se 1 (by rfl) ⟨728972, by rfl⟩ : syracuseStep 971963 = 1457945) B1457945
theorem B1660105 : Blo 968591 1660105 := bstep (se 2 (by rfl) ⟨622539, by rfl⟩ : syracuseStep 1660105 = 1245079) B1245079
theorem B3691777 : Blo 968591 3691777 := bstep (se 2 (by rfl) ⟨1384416, by rfl⟩ : syracuseStep 3691777 = 2768833) B2768833
theorem B972039 : Blo 968591 972039 := bstep (se 1 (by rfl) ⟨729029, by rfl⟩ : syracuseStep 972039 = 1458059) B1458059
theorem B972047 : Blo 968591 972047 := bstep (se 1 (by rfl) ⟨729035, by rfl⟩ : syracuseStep 972047 = 1458071) B1458071
theorem B4904225 : Blo 968591 4904225 := bstep (se 2 (by rfl) ⟨1839084, by rfl⟩ : syracuseStep 4904225 = 3678169) B3678169
theorem B972091 : Blo 968591 972091 := bstep (se 1 (by rfl) ⟨729068, by rfl⟩ : syracuseStep 972091 = 1458137) B1458137
theorem B7361927 : Blo 968591 7361927 := bstep (se 1 (by rfl) ⟨5521445, by rfl⟩ : syracuseStep 7361927 = 11042891) B11042891
theorem B972167 : Blo 968591 972167 := bstep (se 1 (by rfl) ⟨729125, by rfl⟩ : syracuseStep 972167 = 1458251) B1458251
theorem B972175 : Blo 968591 972175 := bstep (se 1 (by rfl) ⟨729131, by rfl⟩ : syracuseStep 972175 = 1458263) B1458263
theorem B11064761 : Blo 968591 11064761 := bstep (se 2 (by rfl) ⟨4149285, by rfl⟩ : syracuseStep 11064761 = 8298571) B8298571
theorem B972219 : Blo 968591 972219 := bstep (se 1 (by rfl) ⟨729164, by rfl⟩ : syracuseStep 972219 = 1458329) B1458329
theorem B972295 : Blo 968591 972295 := bstep (se 1 (by rfl) ⟨729221, by rfl⟩ : syracuseStep 972295 = 1458443) B1458443
theorem B972303 : Blo 968591 972303 := bstep (se 1 (by rfl) ⟨729227, by rfl⟩ : syracuseStep 972303 = 1458455) B1458455
theorem B972347 : Blo 968591 972347 := bstep (se 1 (by rfl) ⟨729260, by rfl⟩ : syracuseStep 972347 = 1458521) B1458521
theorem B2184839 : Blo 968591 2184839 := bstep (se 1 (by rfl) ⟨1638629, by rfl⟩ : syracuseStep 2184839 = 3277259) B3277259
theorem B972423 : Blo 968591 972423 := bstep (se 1 (by rfl) ⟨729317, by rfl⟩ : syracuseStep 972423 = 1458635) B1458635
theorem B972431 : Blo 968591 972431 := bstep (se 1 (by rfl) ⟨729323, by rfl⟩ : syracuseStep 972431 = 1458647) B1458647
theorem B23025329 : Blo 968591 23025329 := bstep (se 2 (by rfl) ⟨8634498, by rfl⟩ : syracuseStep 23025329 = 17268997) B17268997
theorem B972475 : Blo 968591 972475 := bstep (se 1 (by rfl) ⟨729356, by rfl⟩ : syracuseStep 972475 = 1458713) B1458713
theorem B972551 : Blo 968591 972551 := bstep (se 1 (by rfl) ⟨729413, by rfl⟩ : syracuseStep 972551 = 1458827) B1458827
theorem B972559 : Blo 968591 972559 := bstep (se 1 (by rfl) ⟨729419, by rfl⟩ : syracuseStep 972559 = 1458839) B1458839
theorem B2185019 : Blo 968591 2185019 := bstep (se 1 (by rfl) ⟨1638764, by rfl⟩ : syracuseStep 2185019 = 3277529) B3277529
theorem B37279601 : Blo 968591 37279601 := bstep (se 2 (by rfl) ⟨13979850, by rfl⟩ : syracuseStep 37279601 = 27959701) B27959701
theorem B2185145 : Blo 968591 2185145 := bstep (se 2 (by rfl) ⟨819429, by rfl⟩ : syracuseStep 2185145 = 1638859) B1638859
theorem B4905197 : Blo 968591 4905197 := bstep (se 3 (by rfl) ⟨919724, by rfl⟩ : syracuseStep 4905197 = 1839449) B1839449
theorem B2185487 : Blo 968591 2185487 := bstep (se 1 (by rfl) ⟨1639115, by rfl⟩ : syracuseStep 2185487 = 3278231) B3278231
theorem B2185505 : Blo 968591 2185505 := bstep (se 2 (by rfl) ⟨819564, by rfl⟩ : syracuseStep 2185505 = 1639129) B1639129
theorem B2185847 : Blo 968591 2185847 := bstep (se 1 (by rfl) ⟨1639385, by rfl⟩ : syracuseStep 2185847 = 3278771) B3278771
theorem B2186027 : Blo 968591 2186027 := bstep (se 1 (by rfl) ⟨1639520, by rfl⟩ : syracuseStep 2186027 = 3279041) B3279041
theorem B5528371 : Blo 968591 5528371 := bstep (se 1 (by rfl) ⟨4146278, by rfl⟩ : syracuseStep 5528371 = 8292557) B8292557
theorem B4906007 : Blo 968591 4906007 := bstep (se 1 (by rfl) ⟨3679505, by rfl⟩ : syracuseStep 4906007 = 7359011) B7359011
theorem B2186387 : Blo 968591 2186387 := bstep (se 1 (by rfl) ⟨1639790, by rfl⟩ : syracuseStep 2186387 = 3279581) B3279581
theorem B1662137 : Blo 968591 1662137 := bstep (se 2 (by rfl) ⟨623301, by rfl⟩ : syracuseStep 1662137 = 1246603) B1246603
theorem B2186441 : Blo 968591 2186441 := bstep (se 2 (by rfl) ⟨819915, by rfl⟩ : syracuseStep 2186441 = 1639831) B1639831
theorem B1596731 : Blo 968591 1596731 := bstep (se 1 (by rfl) ⟨1197548, by rfl⟩ : syracuseStep 1596731 = 2395097) B2395097
theorem B6643129 : Blo 968591 6643129 := bstep (se 2 (by rfl) ⟨2491173, by rfl⟩ : syracuseStep 6643129 = 4982347) B4982347
theorem B3497501 : Blo 968591 3497501 := bstep (se 3 (by rfl) ⟨655781, by rfl⟩ : syracuseStep 3497501 = 1311563) B1311563
theorem B2187143 : Blo 968591 2187143 := bstep (se 1 (by rfl) ⟨1640357, by rfl⟩ : syracuseStep 2187143 = 3280715) B3280715
theorem B11198359 : Blo 968591 11198359 := bstep (se 1 (by rfl) ⟨8398769, by rfl⟩ : syracuseStep 11198359 = 16797539) B16797539
theorem B2187323 : Blo 968591 2187323 := bstep (se 1 (by rfl) ⟨1640492, by rfl⟩ : syracuseStep 2187323 = 3280985) B3280985
theorem B9330821 : Blo 968591 9330821 := bstep (se 4 (by rfl) ⟨874764, by rfl⟩ : syracuseStep 9330821 = 1749529) B1749529
theorem B2187449 : Blo 968591 2187449 := bstep (se 2 (by rfl) ⟨820293, by rfl⟩ : syracuseStep 2187449 = 1640587) B1640587
theorem B5529829 : Blo 968591 5529829 := bstep (se 4 (by rfl) ⟨518421, by rfl⟩ : syracuseStep 5529829 = 1036843) B1036843
theorem B18407897 : Blo 968591 18407897 := bstep (se 2 (by rfl) ⟨6902961, by rfl⟩ : syracuseStep 18407897 = 13805923) B13805923
theorem B28041713 : Blo 968591 28041713 := bstep (se 2 (by rfl) ⟨10515642, by rfl⟩ : syracuseStep 28041713 = 21031285) B21031285
theorem B6644227 : Blo 968591 6644227 := bstep (se 1 (by rfl) ⟨4983170, by rfl⟩ : syracuseStep 6644227 = 9966341) B9966341
theorem B2187791 : Blo 968591 2187791 := bstep (se 1 (by rfl) ⟨1640843, by rfl⟩ : syracuseStep 2187791 = 3281687) B3281687
theorem B2187809 : Blo 968591 2187809 := bstep (se 2 (by rfl) ⟨820428, by rfl⟩ : syracuseStep 2187809 = 1640857) B1640857
theorem B3269321 : Blo 968591 3269321 := bstep (se 2 (by rfl) ⟨1225995, by rfl⟩ : syracuseStep 3269321 = 2451991) B2451991
theorem B1401643 : Blo 968591 1401643 := bstep (se 1 (by rfl) ⟨1051232, by rfl⟩ : syracuseStep 1401643 = 2102465) B2102465
theorem B2188151 : Blo 968591 2188151 := bstep (se 1 (by rfl) ⟨1641113, by rfl⟩ : syracuseStep 2188151 = 3282227) B3282227
theorem B3105803 : Blo 968591 3105803 := bstep (se 1 (by rfl) ⟨2329352, by rfl⟩ : syracuseStep 3105803 = 4658705) B4658705
theorem B2188331 : Blo 968591 2188331 := bstep (se 1 (by rfl) ⟨1641248, by rfl⟩ : syracuseStep 2188331 = 3282497) B3282497
theorem B3270023 : Blo 968591 3270023 := bstep (se 1 (by rfl) ⟨2452517, by rfl⟩ : syracuseStep 3270023 = 4905035) B4905035
theorem B6383033 : Blo 968591 6383033 := bstep (se 2 (by rfl) ⟨2393637, by rfl⟩ : syracuseStep 6383033 = 4787275) B4787275
theorem B3270401 : Blo 968591 3270401 := bstep (se 2 (by rfl) ⟨1226400, by rfl⟩ : syracuseStep 3270401 = 2452801) B2452801
theorem B5596943 : Blo 968591 5596943 := bstep (se 1 (by rfl) ⟨4197707, by rfl⟩ : syracuseStep 5596943 = 8395415) B8395415
theorem B4909085 : Blo 968591 4909085 := bstep (se 3 (by rfl) ⟨920453, by rfl⟩ : syracuseStep 4909085 = 1840907) B1840907
theorem B11037059 : Blo 968591 11037059 := bstep (se 1 (by rfl) ⟨8277794, by rfl⟩ : syracuseStep 11037059 = 16555589) B16555589
theorem B4909571 : Blo 968591 4909571 := bstep (se 1 (by rfl) ⟨3682178, by rfl⟩ : syracuseStep 4909571 = 7364357) B7364357
theorem B3271211 : Blo 968591 3271211 := bstep (se 1 (by rfl) ⟨2453408, by rfl⟩ : syracuseStep 3271211 = 4906817) B4906817
theorem B2452103 : Blo 968591 2452103 := bstep (se 1 (by rfl) ⟨1839077, by rfl⟩ : syracuseStep 2452103 = 3678155) B3678155
theorem B2452153 : Blo 968591 2452153 := bstep (se 2 (by rfl) ⟨919557, by rfl⟩ : syracuseStep 2452153 = 1839115) B1839115
theorem B3500833 : Blo 968591 3500833 := bstep (se 2 (by rfl) ⟨1312812, by rfl⟩ : syracuseStep 3500833 = 2625625) B2625625
theorem B9988913 : Blo 968591 9988913 := bstep (se 2 (by rfl) ⟨3745842, by rfl⟩ : syracuseStep 9988913 = 7491685) B7491685
theorem B5532563 : Blo 968591 5532563 := bstep (se 1 (by rfl) ⟨4149422, by rfl⟩ : syracuseStep 5532563 = 8298845) B8298845
theorem B2452751 : Blo 968591 2452751 := bstep (se 1 (by rfl) ⟨1839563, by rfl⟩ : syracuseStep 2452751 = 3679127) B3679127
theorem B3927329 : Blo 968591 3927329 := bstep (se 2 (by rfl) ⟨1472748, by rfl⟩ : syracuseStep 3927329 = 2945497) B2945497
theorem B5533271 : Blo 968591 5533271 := bstep (se 1 (by rfl) ⟨4149953, by rfl⟩ : syracuseStep 5533271 = 8299907) B8299907
theorem B20967011 : Blo 968591 20967011 := bstep (se 1 (by rfl) ⟨15725258, by rfl⟩ : syracuseStep 20967011 = 31450517) B31450517
theorem B3272507 : Blo 968591 3272507 := bstep (se 1 (by rfl) ⟨2454380, by rfl⟩ : syracuseStep 3272507 = 4908761) B4908761
theorem B3501883 : Blo 968591 3501883 := bstep (se 1 (by rfl) ⟨2626412, by rfl⟩ : syracuseStep 3501883 = 5252825) B5252825
theorem B3927943 : Blo 968591 3927943 := bstep (se 1 (by rfl) ⟨2945957, by rfl⟩ : syracuseStep 3927943 = 5891915) B5891915
theorem B2453449 : Blo 968591 2453449 := bstep (se 2 (by rfl) ⟨920043, by rfl⟩ : syracuseStep 2453449 = 1840087) B1840087
theorem B59666453 : Blo 968591 59666453 := bstep (se 6 (by rfl) ⟨1398432, by rfl⟩ : syracuseStep 59666453 = 2796865) B2796865
theorem B2453591 : Blo 968591 2453591 := bstep (se 1 (by rfl) ⟨1840193, by rfl⟩ : syracuseStep 2453591 = 3680387) B3680387
theorem B4911191 : Blo 968591 4911191 := bstep (se 1 (by rfl) ⟨3683393, by rfl⟩ : syracuseStep 4911191 = 7366787) B7366787
theorem B3272993 : Blo 968591 3272993 := bstep (se 2 (by rfl) ⟨1227372, by rfl⟩ : syracuseStep 3272993 = 2454745) B2454745
theorem B4911677 : Blo 968591 4911677 := bstep (se 3 (by rfl) ⟨920939, by rfl⟩ : syracuseStep 4911677 = 1841879) B1841879
theorem B1634951 : Blo 968591 1634951 := bstep (se 1 (by rfl) ⟨1226213, by rfl⟩ : syracuseStep 1634951 = 2452427) B2452427
theorem B3273587 : Blo 968591 3273587 := bstep (se 1 (by rfl) ⟨2455190, by rfl⟩ : syracuseStep 3273587 = 4910381) B4910381
theorem B8287433 : Blo 968591 8287433 := bstep (se 2 (by rfl) ⟨3107787, by rfl⟩ : syracuseStep 8287433 = 6215575) B6215575
theorem B1635599 : Blo 968591 1635599 := bstep (se 1 (by rfl) ⟨1226699, by rfl⟩ : syracuseStep 1635599 = 2453399) B2453399
theorem B1996217 : Blo 968591 1996217 := bstep (se 2 (by rfl) ⟨748581, by rfl⟩ : syracuseStep 1996217 = 1497163) B1497163
theorem B5535161 : Blo 968591 5535161 := bstep (se 2 (by rfl) ⟨2075685, by rfl⟩ : syracuseStep 5535161 = 4151371) B4151371
theorem B5240285 : Blo 968591 5240285 := bstep (se 3 (by rfl) ⟨982553, by rfl⟩ : syracuseStep 5240285 = 1965107) B1965107
theorem B3929629 : Blo 968591 3929629 := bstep (se 3 (by rfl) ⟨736805, by rfl⟩ : syracuseStep 3929629 = 1473611) B1473611
theorem B2946761 : Blo 968591 2946761 := bstep (se 2 (by rfl) ⟨1105035, by rfl⟩ : syracuseStep 2946761 = 2210071) B2210071
theorem B1636139 : Blo 968591 1636139 := bstep (se 1 (by rfl) ⟨1227104, by rfl⟩ : syracuseStep 1636139 = 2454209) B2454209
theorem B3504019 : Blo 968591 3504019 := bstep (se 1 (by rfl) ⟨2628014, by rfl⟩ : syracuseStep 3504019 = 5256029) B5256029
theorem B2455667 : Blo 968591 2455667 := bstep (se 1 (by rfl) ⟨1841750, by rfl⟩ : syracuseStep 2455667 = 3683501) B3683501
theorem B1636537 : Blo 968591 1636537 := bstep (se 2 (by rfl) ⟨613701, by rfl⟩ : syracuseStep 1636537 = 1227403) B1227403
theorem B3733775 : Blo 968591 3733775 := bstep (se 1 (by rfl) ⟨2800331, by rfl⟩ : syracuseStep 3733775 = 5600663) B5600663
theorem B4913459 : Blo 968591 4913459 := bstep (se 1 (by rfl) ⟨3685094, by rfl⟩ : syracuseStep 4913459 = 7370189) B7370189
theorem B1997345 : Blo 968591 1997345 := bstep (se 2 (by rfl) ⟨749004, by rfl⟩ : syracuseStep 1997345 = 1498009) B1498009
theorem B2456183 : Blo 968591 2456183 := bstep (se 1 (by rfl) ⟨1842137, by rfl⟩ : syracuseStep 2456183 = 3684275) B3684275
theorem B4913783 : Blo 968591 4913783 := bstep (se 1 (by rfl) ⟨3685337, by rfl⟩ : syracuseStep 4913783 = 7370675) B7370675
theorem B1637239 : Blo 968591 1637239 := bstep (se 1 (by rfl) ⟨1227929, by rfl⟩ : syracuseStep 1637239 = 2455859) B2455859
theorem B2620295 : Blo 968591 2620295 := bstep (se 1 (by rfl) ⟨1965221, by rfl⟩ : syracuseStep 2620295 = 3930443) B3930443
theorem B4979659 : Blo 968591 4979659 := bstep (se 1 (by rfl) ⟨3734744, by rfl⟩ : syracuseStep 4979659 = 7469489) B7469489
theorem B2489387 : Blo 968591 2489387 := bstep (se 1 (by rfl) ⟨1867040, by rfl⟩ : syracuseStep 2489387 = 3734081) B3734081
theorem B1637435 : Blo 968591 1637435 := bstep (se 1 (by rfl) ⟨1228076, by rfl⟩ : syracuseStep 1637435 = 2456153) B2456153
theorem B3276179 : Blo 968591 3276179 := bstep (se 1 (by rfl) ⟨2457134, by rfl⟩ : syracuseStep 3276179 = 4914269) B4914269
theorem B1473977 : Blo 968591 1473977 := bstep (se 2 (by rfl) ⟨552741, by rfl⟩ : syracuseStep 1473977 = 1105483) B1105483
theorem B1637833 : Blo 968591 1637833 := bstep (se 2 (by rfl) ⟨614187, by rfl⟩ : syracuseStep 1637833 = 1228375) B1228375
theorem B10485197 : Blo 968591 10485197 := bstep (se 3 (by rfl) ⟨1965974, by rfl⟩ : syracuseStep 10485197 = 3931949) B3931949
theorem B4914755 : Blo 968591 4914755 := bstep (se 1 (by rfl) ⟨3686066, by rfl⟩ : syracuseStep 4914755 = 7372133) B7372133
theorem B2457175 : Blo 968591 2457175 := bstep (se 1 (by rfl) ⟨1842881, by rfl⟩ : syracuseStep 2457175 = 3685763) B3685763
theorem B8290097 : Blo 968591 8290097 := bstep (se 2 (by rfl) ⟨3108786, by rfl⟩ : syracuseStep 8290097 = 6217573) B6217573
theorem B2457479 : Blo 968591 2457479 := bstep (se 1 (by rfl) ⟨1843109, by rfl⟩ : syracuseStep 2457479 = 3686219) B3686219
theorem B4915079 : Blo 968591 4915079 := bstep (se 1 (by rfl) ⟨3686309, by rfl⟩ : syracuseStep 4915079 = 7372619) B7372619
theorem B8388515 : Blo 968591 8388515 := bstep (se 1 (by rfl) ⟨6291386, by rfl⟩ : syracuseStep 8388515 = 12582773) B12582773
theorem B1638407 : Blo 968591 1638407 := bstep (se 1 (by rfl) ⟨1228805, by rfl⟩ : syracuseStep 1638407 = 2457611) B2457611
theorem B12419153 : Blo 968591 12419153 := bstep (se 2 (by rfl) ⟨4657182, by rfl⟩ : syracuseStep 12419153 = 9314365) B9314365
theorem B983215 : Blo 968591 983215 := bstep (se 1 (by rfl) ⟨737411, by rfl⟩ : syracuseStep 983215 = 1474823) B1474823
theorem B7373105 : Blo 968591 7373105 := bstep (se 2 (by rfl) ⟨2764914, by rfl⟩ : syracuseStep 7373105 = 5529829) B5529829
theorem B53051723 : Blo 968591 53051723 := bstep (se 1 (by rfl) ⟨39788792, by rfl⟩ : syracuseStep 53051723 = 79577585) B79577585
theorem B1638751 : Blo 968591 1638751 := bstep (se 1 (by rfl) ⟨1229063, by rfl⟩ : syracuseStep 1638751 = 2458127) B2458127
theorem B15729025 : Blo 968591 15729025 := bstep (se 2 (by rfl) ⟨5898384, by rfl⟩ : syracuseStep 15729025 = 11796769) B11796769
theorem B7864705 : Blo 968591 7864705 := bstep (se 2 (by rfl) ⟨2949264, by rfl⟩ : syracuseStep 7864705 = 5898529) B5898529
theorem B2457985 : Blo 968591 2457985 := bstep (se 2 (by rfl) ⟨921744, by rfl⟩ : syracuseStep 2457985 = 1843489) B1843489
theorem B1638839 : Blo 968591 1638839 := bstep (se 1 (by rfl) ⟨1229129, by rfl⟩ : syracuseStep 1638839 = 2458259) B2458259
theorem B1245659 : Blo 968591 1245659 := bstep (se 1 (by rfl) ⟨934244, by rfl⟩ : syracuseStep 1245659 = 1868489) B1868489
theorem B1573433 : Blo 968591 1573433 := bstep (se 2 (by rfl) ⟨590037, by rfl⟩ : syracuseStep 1573433 = 1180075) B1180075
theorem B3932807 : Blo 968591 3932807 := bstep (se 1 (by rfl) ⟨2949605, by rfl⟩ : syracuseStep 3932807 = 5899211) B5899211
theorem B11076425 : Blo 968591 11076425 := bstep (se 2 (by rfl) ⟨4153659, by rfl⟩ : syracuseStep 11076425 = 8307319) B8307319
theorem B6652817 : Blo 968591 6652817 := bstep (se 2 (by rfl) ⟨2494806, by rfl⟩ : syracuseStep 6652817 = 4989613) B4989613
theorem B4424705 : Blo 968591 4424705 := bstep (se 2 (by rfl) ⟨1659264, by rfl⟩ : syracuseStep 4424705 = 3318529) B3318529
theorem B1639433 : Blo 968591 1639433 := bstep (se 2 (by rfl) ⟨614787, by rfl⟩ : syracuseStep 1639433 = 1229575) B1229575
theorem B13272083 : Blo 968591 13272083 := bstep (se 1 (by rfl) ⟨9954062, by rfl⟩ : syracuseStep 13272083 = 19908125) B19908125
theorem B2458795 : Blo 968591 2458795 := bstep (se 1 (by rfl) ⟨1844096, by rfl⟩ : syracuseStep 2458795 = 3688193) B3688193
theorem B1639595 : Blo 968591 1639595 := bstep (se 1 (by rfl) ⟨1229696, by rfl⟩ : syracuseStep 1639595 = 2459393) B2459393
theorem B7865743 : Blo 968591 7865743 := bstep (se 1 (by rfl) ⟨5899307, by rfl⟩ : syracuseStep 7865743 = 11798615) B11798615
theorem B4916699 : Blo 968591 4916699 := bstep (se 1 (by rfl) ⟨3687524, by rfl⟩ : syracuseStep 4916699 = 7375049) B7375049
theorem B2459099 : Blo 968591 2459099 := bstep (se 1 (by rfl) ⟨1844324, by rfl⟩ : syracuseStep 2459099 = 3688649) B3688649
theorem B1574407 : Blo 968591 1574407 := bstep (se 1 (by rfl) ⟨1180805, by rfl⟩ : syracuseStep 1574407 = 2361611) B2361611
theorem B1639993 : Blo 968591 1639993 := bstep (se 2 (by rfl) ⟨614997, by rfl⟩ : syracuseStep 1639993 = 1229995) B1229995
theorem B984775 : Blo 968591 984775 := bstep (se 1 (by rfl) ⟨738581, by rfl⟩ : syracuseStep 984775 = 1477163) B1477163
theorem B1640135 : Blo 968591 1640135 := bstep (se 1 (by rfl) ⟨1230101, by rfl⟩ : syracuseStep 1640135 = 2460203) B2460203
theorem B1640297 : Blo 968591 1640297 := bstep (se 2 (by rfl) ⟨615111, by rfl⟩ : syracuseStep 1640297 = 1230223) B1230223
theorem B1312687 : Blo 968591 1312687 := bstep (se 1 (by rfl) ⟨984515, by rfl⟩ : syracuseStep 1312687 = 1969031) B1969031
theorem B1968059 : Blo 968591 1968059 := bstep (se 1 (by rfl) ⟨1476044, by rfl⟩ : syracuseStep 1968059 = 2952089) B2952089
theorem B4917185 : Blo 968591 4917185 := bstep (se 2 (by rfl) ⟨1843944, by rfl⟩ : syracuseStep 4917185 = 3687889) B3687889
theorem B3279095 : Blo 968591 3279095 := bstep (se 1 (by rfl) ⟨2459321, by rfl⟩ : syracuseStep 3279095 = 4918643) B4918643
theorem B1640695 : Blo 968591 1640695 := bstep (se 1 (by rfl) ⟨1230521, by rfl⟩ : syracuseStep 1640695 = 2461043) B2461043
theorem B1640891 : Blo 968591 1640891 := bstep (se 1 (by rfl) ⟨1230668, by rfl⟩ : syracuseStep 1640891 = 2461337) B2461337
theorem B12421613 : Blo 968591 12421613 := bstep (se 3 (by rfl) ⟨2329052, by rfl⟩ : syracuseStep 12421613 = 4658105) B4658105
theorem B1640999 : Blo 968591 1640999 := bstep (se 1 (by rfl) ⟨1230749, by rfl⟩ : syracuseStep 1640999 = 2461499) B2461499
theorem B15927853 : Blo 968591 15927853 := bstep (se 3 (by rfl) ⟨2986472, by rfl⟩ : syracuseStep 15927853 = 5972945) B5972945
theorem B3279419 : Blo 968591 3279419 := bstep (se 1 (by rfl) ⟨2459564, by rfl⟩ : syracuseStep 3279419 = 4919129) B4919129
theorem B3115579 : Blo 968591 3115579 := bstep (se 1 (by rfl) ⟨2336684, by rfl⟩ : syracuseStep 3115579 = 4673369) B4673369
theorem B28314305 : Blo 968591 28314305 := bstep (se 2 (by rfl) ⟨10617864, by rfl⟩ : syracuseStep 28314305 = 21235729) B21235729
theorem B3279689 : Blo 968591 3279689 := bstep (se 2 (by rfl) ⟨1229883, by rfl⟩ : syracuseStep 3279689 = 2459767) B2459767
theorem B2460577 : Blo 968591 2460577 := bstep (se 2 (by rfl) ⟨922716, by rfl⟩ : syracuseStep 2460577 = 1845433) B1845433
theorem B1477595 : Blo 968591 1477595 := bstep (se 1 (by rfl) ⟨1108196, by rfl⟩ : syracuseStep 1477595 = 2216393) B2216393
theorem B2624683 : Blo 968591 2624683 := bstep (se 1 (by rfl) ⟨1968512, by rfl⟩ : syracuseStep 2624683 = 3937025) B3937025
theorem B12619151 : Blo 968591 12619151 := bstep (se 1 (by rfl) ⟨9464363, by rfl⟩ : syracuseStep 12619151 = 18928727) B18928727
theorem B133107313 : Blo 968591 133107313 := bstep (se 2 (by rfl) ⟨49915242, by rfl⟩ : syracuseStep 133107313 = 99830485) B99830485
theorem B1379963 : Blo 968591 1379963 := bstep (se 1 (by rfl) ⟨1034972, by rfl⟩ : syracuseStep 1379963 = 2069945) B2069945
theorem B7376507 : Blo 968591 7376507 := bstep (se 1 (by rfl) ⟨5532380, by rfl⟩ : syracuseStep 7376507 = 11064761) B11064761
theorem B3280823 : Blo 968591 3280823 := bstep (se 1 (by rfl) ⟨2460617, by rfl⟩ : syracuseStep 3280823 = 4921235) B4921235
theorem B1839161 : Blo 968591 1839161 := bstep (se 2 (by rfl) ⟨689685, by rfl⟩ : syracuseStep 1839161 = 1379371) B1379371
theorem B4919453 : Blo 968591 4919453 := bstep (se 3 (by rfl) ⟨922397, by rfl⟩ : syracuseStep 4919453 = 1844795) B1844795
theorem B7475429 : Blo 968591 7475429 := bstep (se 4 (by rfl) ⟨700821, by rfl⟩ : syracuseStep 7475429 = 1401643) B1401643
theorem B1380601 : Blo 968591 1380601 := bstep (se 2 (by rfl) ⟨517725, by rfl⟩ : syracuseStep 1380601 = 1035451) B1035451
theorem B1839503 : Blo 968591 1839503 := bstep (se 1 (by rfl) ⟨1379627, by rfl⟩ : syracuseStep 1839503 = 2759255) B2759255
theorem B3281417 : Blo 968591 3281417 := bstep (se 2 (by rfl) ⟨1230531, by rfl⟩ : syracuseStep 3281417 = 2461063) B2461063
theorem B3740489 : Blo 968591 3740489 := bstep (se 2 (by rfl) ⟨1402683, by rfl⟩ : syracuseStep 3740489 = 2805367) B2805367
theorem B2495339 : Blo 968591 2495339 := bstep (se 1 (by rfl) ⟨1871504, by rfl⟩ : syracuseStep 2495339 = 3743009) B3743009
theorem B6231005 : Blo 968591 6231005 := bstep (se 3 (by rfl) ⟨1168313, by rfl⟩ : syracuseStep 6231005 = 2336627) B2336627
theorem B2331667 : Blo 968591 2331667 := bstep (se 1 (by rfl) ⟨1748750, by rfl⟩ : syracuseStep 2331667 = 3497501) B3497501
theorem B3282281 : Blo 968591 3282281 := bstep (se 2 (by rfl) ⟨1230855, by rfl⟩ : syracuseStep 3282281 = 2461711) B2461711
theorem B4920749 : Blo 968591 4920749 := bstep (se 3 (by rfl) ⟨922640, by rfl⟩ : syracuseStep 4920749 = 1845281) B1845281
theorem B3741319 : Blo 968591 3741319 := bstep (se 1 (by rfl) ⟨2805989, by rfl⟩ : syracuseStep 3741319 = 5611979) B5611979
theorem B2070535 : Blo 968591 2070535 := bstep (se 1 (by rfl) ⟨1552901, by rfl⟩ : syracuseStep 2070535 = 3105803) B3105803
theorem B1841363 : Blo 968591 1841363 := bstep (se 1 (by rfl) ⟨1381022, by rfl⟩ : syracuseStep 1841363 = 2762045) B2762045
theorem B2627969 : Blo 968591 2627969 := bstep (se 2 (by rfl) ⟨985488, by rfl⟩ : syracuseStep 2627969 = 1970977) B1970977
theorem B8853893 : Blo 968591 8853893 := bstep (se 4 (by rfl) ⟨830052, by rfl⟩ : syracuseStep 8853893 = 1660105) B1660105
theorem B1841591 : Blo 968591 1841591 := bstep (se 1 (by rfl) ⟨1381193, by rfl⟩ : syracuseStep 1841591 = 2762387) B2762387
theorem B2628425 : Blo 968591 2628425 := bstep (se 2 (by rfl) ⟨985659, by rfl⟩ : syracuseStep 2628425 = 1971319) B1971319
theorem B4922369 : Blo 968591 4922369 := bstep (se 2 (by rfl) ⟨1845888, by rfl⟩ : syracuseStep 4922369 = 3691777) B3691777
theorem B6659275 : Blo 968591 6659275 := bstep (se 1 (by rfl) ⟨4994456, by rfl⟩ : syracuseStep 6659275 = 9988913) B9988913
theorem B7085531 : Blo 968591 7085531 := bstep (se 1 (by rfl) ⟨5314148, by rfl⟩ : syracuseStep 7085531 = 10628297) B10628297
theorem B3677683 : Blo 968591 3677683 := bstep (se 1 (by rfl) ⟨2758262, by rfl⟩ : syracuseStep 3677683 = 5516525) B5516525
theorem B1842745 : Blo 968591 1842745 := bstep (se 2 (by rfl) ⟨691029, by rfl⟩ : syracuseStep 1842745 = 1382059) B1382059
theorem B4923179 : Blo 968591 4923179 := bstep (se 1 (by rfl) ⟨3692384, by rfl⟩ : syracuseStep 4923179 = 7384769) B7384769
theorem B1843049 : Blo 968591 1843049 := bstep (se 2 (by rfl) ⟨691143, by rfl⟩ : syracuseStep 1843049 = 1382287) B1382287
theorem B1843087 : Blo 968591 1843087 := bstep (se 1 (by rfl) ⟨1382315, by rfl⟩ : syracuseStep 1843087 = 2764631) B2764631
theorem B1089967 : Blo 968591 1089967 := bstep (se 1 (by rfl) ⟨817475, by rfl⟩ : syracuseStep 1089967 = 1634951) B1634951
theorem B3678929 : Blo 968591 3678929 := bstep (se 2 (by rfl) ⟨1379598, by rfl⟩ : syracuseStep 3678929 = 2759197) B2759197
theorem B1090399 : Blo 968591 1090399 := bstep (se 1 (by rfl) ⟨817799, by rfl⟩ : syracuseStep 1090399 = 1635599) B1635599
theorem B1090759 : Blo 968591 1090759 := bstep (se 1 (by rfl) ⟨818069, by rfl⟩ : syracuseStep 1090759 = 1636139) B1636139
theorem B3679613 : Blo 968591 3679613 := bstep (se 3 (by rfl) ⟨689927, by rfl⟩ : syracuseStep 3679613 = 1379855) B1379855
theorem B2762113 : Blo 968591 2762113 := bstep (se 2 (by rfl) ⟨1035792, by rfl⟩ : syracuseStep 2762113 = 2071585) B2071585
theorem B63710819 : Blo 968591 63710819 := bstep (se 1 (by rfl) ⟨47783114, by rfl⟩ : syracuseStep 63710819 = 95566229) B95566229
theorem B2762363 : Blo 968591 2762363 := bstep (se 1 (by rfl) ⟨2071772, by rfl⟩ : syracuseStep 2762363 = 4143545) B4143545
theorem B1844947 : Blo 968591 1844947 := bstep (se 1 (by rfl) ⟨1383710, by rfl⟩ : syracuseStep 1844947 = 2767421) B2767421
theorem B8857505 : Blo 968591 8857505 := bstep (se 2 (by rfl) ⟨3321564, by rfl⟩ : syracuseStep 8857505 = 6643129) B6643129
theorem B1746863 : Blo 968591 1746863 := bstep (se 1 (by rfl) ⟨1310147, by rfl⟩ : syracuseStep 1746863 = 2620295) B2620295
theorem B1845175 : Blo 968591 1845175 := bstep (se 1 (by rfl) ⟨1383881, by rfl⟩ : syracuseStep 1845175 = 2767763) B2767763
theorem B7874567 : Blo 968591 7874567 := bstep (se 1 (by rfl) ⟨5905925, by rfl⟩ : syracuseStep 7874567 = 11811851) B11811851
theorem B1091623 : Blo 968591 1091623 := bstep (se 1 (by rfl) ⟨818717, by rfl⟩ : syracuseStep 1091623 = 1637435) B1637435
theorem B6990131 : Blo 968591 6990131 := bstep (se 1 (by rfl) ⟨5242598, by rfl⟩ : syracuseStep 6990131 = 10485197) B10485197
theorem B3680599 : Blo 968591 3680599 := bstep (se 1 (by rfl) ⟨2760449, by rfl⟩ : syracuseStep 3680599 = 5520899) B5520899
theorem B2074985 : Blo 968591 2074985 := bstep (se 2 (by rfl) ⟨778119, by rfl⟩ : syracuseStep 2074985 = 1556239) B1556239
theorem B1845767 : Blo 968591 1845767 := bstep (se 1 (by rfl) ⟨1384325, by rfl⟩ : syracuseStep 1845767 = 2768651) B2768651
theorem B3680903 : Blo 968591 3680903 := bstep (se 1 (by rfl) ⟨2760677, by rfl⟩ : syracuseStep 3680903 = 5521355) B5521355
theorem B9317213 : Blo 968591 9317213 := bstep (se 3 (by rfl) ⟨1746977, by rfl⟩ : syracuseStep 9317213 = 3493955) B3493955
theorem B1452905 : Blo 968591 1452905 := bstep (se 2 (by rfl) ⟨544839, by rfl⟩ : syracuseStep 1452905 = 1089679) B1089679
theorem B1452983 : Blo 968591 1452983 := bstep (se 1 (by rfl) ⟨1089737, by rfl⟩ : syracuseStep 1452983 = 2179475) B2179475
theorem B1453019 : Blo 968591 1453019 := bstep (se 1 (by rfl) ⟨1089764, by rfl⟩ : syracuseStep 1453019 = 2179529) B2179529
theorem B3681359 : Blo 968591 3681359 := bstep (se 1 (by rfl) ⟨2761019, by rfl⟩ : syracuseStep 3681359 = 5522039) B5522039
theorem B8858969 : Blo 968591 8858969 := bstep (se 2 (by rfl) ⟨3322113, by rfl⟩ : syracuseStep 8858969 = 6644227) B6644227
theorem B5615021 : Blo 968591 5615021 := bstep (se 3 (by rfl) ⟨1052816, by rfl⟩ : syracuseStep 5615021 = 2105633) B2105633
theorem B1453487 : Blo 968591 1453487 := bstep (se 1 (by rfl) ⟨1090115, by rfl⟩ : syracuseStep 1453487 = 2180231) B2180231
theorem B1453577 : Blo 968591 1453577 := bstep (se 2 (by rfl) ⟨545091, by rfl⟩ : syracuseStep 1453577 = 1090183) B1090183
theorem B1453607 : Blo 968591 1453607 := bstep (se 1 (by rfl) ⟨1090205, by rfl⟩ : syracuseStep 1453607 = 2180411) B2180411
theorem B1093243 : Blo 968591 1093243 := bstep (se 1 (by rfl) ⟨819932, by rfl⟩ : syracuseStep 1093243 = 1639865) B1639865
theorem B1453691 : Blo 968591 1453691 := bstep (se 1 (by rfl) ⟨1090268, by rfl⟩ : syracuseStep 1453691 = 2180537) B2180537
theorem B2076283 : Blo 968591 2076283 := bstep (se 1 (by rfl) ⟨1557212, by rfl⟩ : syracuseStep 2076283 = 3114425) B3114425
theorem B1453817 : Blo 968591 1453817 := bstep (se 2 (by rfl) ⟨545181, by rfl⟩ : syracuseStep 1453817 = 1090363) B1090363
theorem B1453919 : Blo 968591 1453919 := bstep (se 1 (by rfl) ⟨1090439, by rfl⟩ : syracuseStep 1453919 = 2180879) B2180879
theorem B1453931 : Blo 968591 1453931 := bstep (se 1 (by rfl) ⟨1090448, by rfl⟩ : syracuseStep 1453931 = 2180897) B2180897
theorem B3682361 : Blo 968591 3682361 := bstep (se 2 (by rfl) ⟨1380885, by rfl⟩ : syracuseStep 3682361 = 2761771) B2761771
theorem B1454159 : Blo 968591 1454159 := bstep (se 1 (by rfl) ⟨1090619, by rfl⟩ : syracuseStep 1454159 = 2181239) B2181239
theorem B1093711 : Blo 968591 1093711 := bstep (se 1 (by rfl) ⟨820283, by rfl⟩ : syracuseStep 1093711 = 1640567) B1640567
theorem B1454279 : Blo 968591 1454279 := bstep (se 1 (by rfl) ⟨1090709, by rfl⟩ : syracuseStep 1454279 = 2181419) B2181419
theorem B1454441 : Blo 968591 1454441 := bstep (se 2 (by rfl) ⟨545415, by rfl⟩ : syracuseStep 1454441 = 1090831) B1090831
theorem B1454519 : Blo 968591 1454519 := bstep (se 1 (by rfl) ⟨1090889, by rfl⟩ : syracuseStep 1454519 = 2181779) B2181779
theorem B1454555 : Blo 968591 1454555 := bstep (se 1 (by rfl) ⟨1090916, by rfl⟩ : syracuseStep 1454555 = 2181833) B2181833
theorem B1094107 : Blo 968591 1094107 := bstep (se 1 (by rfl) ⟨820580, by rfl⟩ : syracuseStep 1094107 = 1641161) B1641161
theorem B3683015 : Blo 968591 3683015 := bstep (se 1 (by rfl) ⟨2762261, by rfl⟩ : syracuseStep 3683015 = 5524523) B5524523
theorem B1749703 : Blo 968591 1749703 := bstep (se 1 (by rfl) ⟨1312277, by rfl⟩ : syracuseStep 1749703 = 2624555) B2624555
theorem B1455023 : Blo 968591 1455023 := bstep (se 1 (by rfl) ⟨1091267, by rfl⟩ : syracuseStep 1455023 = 2182535) B2182535
theorem B1455113 : Blo 968591 1455113 := bstep (se 2 (by rfl) ⟨545667, by rfl⟩ : syracuseStep 1455113 = 1091335) B1091335
theorem B1455143 : Blo 968591 1455143 := bstep (se 1 (by rfl) ⟨1091357, by rfl⟩ : syracuseStep 1455143 = 2182715) B2182715
theorem B7877681 : Blo 968591 7877681 := bstep (se 2 (by rfl) ⟨2954130, by rfl⟩ : syracuseStep 7877681 = 5908261) B5908261
theorem B1553465 : Blo 968591 1553465 := bstep (se 2 (by rfl) ⟨582549, by rfl⟩ : syracuseStep 1553465 = 1165099) B1165099
theorem B1455227 : Blo 968591 1455227 := bstep (se 1 (by rfl) ⟨1091420, by rfl⟩ : syracuseStep 1455227 = 2182841) B2182841
theorem B1455353 : Blo 968591 1455353 := bstep (se 2 (by rfl) ⟨545757, by rfl⟩ : syracuseStep 1455353 = 1091515) B1091515
theorem B1455455 : Blo 968591 1455455 := bstep (se 1 (by rfl) ⟨1091591, by rfl⟩ : syracuseStep 1455455 = 2183183) B2183183
theorem B1455467 : Blo 968591 1455467 := bstep (se 1 (by rfl) ⟨1091600, by rfl⟩ : syracuseStep 1455467 = 2183201) B2183201
theorem B1226279 : Blo 968591 1226279 := bstep (se 1 (by rfl) ⟨919709, by rfl⟩ : syracuseStep 1226279 = 1839419) B1839419
theorem B1455695 : Blo 968591 1455695 := bstep (se 1 (by rfl) ⟨1091771, by rfl⟩ : syracuseStep 1455695 = 2183543) B2183543
theorem B3683987 : Blo 968591 3683987 := bstep (se 1 (by rfl) ⟨2762990, by rfl⟩ : syracuseStep 3683987 = 5525981) B5525981
theorem B1455815 : Blo 968591 1455815 := bstep (se 1 (by rfl) ⟨1091861, by rfl⟩ : syracuseStep 1455815 = 2183723) B2183723
theorem B4667179 : Blo 968591 4667179 := bstep (se 1 (by rfl) ⟨3500384, by rfl⟩ : syracuseStep 4667179 = 7000769) B7000769
theorem B6207299 : Blo 968591 6207299 := bstep (se 1 (by rfl) ⟨4655474, by rfl⟩ : syracuseStep 6207299 = 9310949) B9310949
theorem B1455977 : Blo 968591 1455977 := bstep (se 2 (by rfl) ⟨545991, by rfl⟩ : syracuseStep 1455977 = 1091983) B1091983
theorem B1226603 : Blo 968591 1226603 := bstep (se 1 (by rfl) ⟨919952, by rfl⟩ : syracuseStep 1226603 = 1839905) B1839905
theorem B1456055 : Blo 968591 1456055 := bstep (se 1 (by rfl) ⟨1092041, by rfl⟩ : syracuseStep 1456055 = 2184083) B2184083
theorem B6207425 : Blo 968591 6207425 := bstep (se 2 (by rfl) ⟨2327784, by rfl⟩ : syracuseStep 6207425 = 4655569) B4655569
theorem B1456091 : Blo 968591 1456091 := bstep (se 1 (by rfl) ⟨1092068, by rfl⟩ : syracuseStep 1456091 = 2184137) B2184137
theorem B5519441 : Blo 968591 5519441 := bstep (se 2 (by rfl) ⟨2069790, by rfl⟩ : syracuseStep 5519441 = 4139581) B4139581
theorem B4667777 : Blo 968591 4667777 := bstep (se 2 (by rfl) ⟨1750416, by rfl⟩ : syracuseStep 4667777 = 3500833) B3500833
theorem B1456559 : Blo 968591 1456559 := bstep (se 1 (by rfl) ⟨1092419, by rfl⟩ : syracuseStep 1456559 = 2184839) B2184839
theorem B15350219 : Blo 968591 15350219 := bstep (se 1 (by rfl) ⟨11512664, by rfl⟩ : syracuseStep 15350219 = 23025329) B23025329
theorem B1456649 : Blo 968591 1456649 := bstep (se 2 (by rfl) ⟨546243, by rfl⟩ : syracuseStep 1456649 = 1092487) B1092487
theorem B5519897 : Blo 968591 5519897 := bstep (se 2 (by rfl) ⟨2069961, by rfl⟩ : syracuseStep 5519897 = 4139923) B4139923
theorem B1456679 : Blo 968591 1456679 := bstep (se 1 (by rfl) ⟨1092509, by rfl⟩ : syracuseStep 1456679 = 2185019) B2185019
theorem B1751591 : Blo 968591 1751591 := bstep (se 1 (by rfl) ⟨1313693, by rfl⟩ : syracuseStep 1751591 = 2627387) B2627387
theorem B24853067 : Blo 968591 24853067 := bstep (se 1 (by rfl) ⟨18639800, by rfl⟩ : syracuseStep 24853067 = 37279601) B37279601
theorem B1456763 : Blo 968591 1456763 := bstep (se 1 (by rfl) ⟨1092572, by rfl⟩ : syracuseStep 1456763 = 2185145) B2185145
theorem B1456889 : Blo 968591 1456889 := bstep (se 2 (by rfl) ⟨546333, by rfl⟩ : syracuseStep 1456889 = 1092667) B1092667
theorem B14957389 : Blo 968591 14957389 := bstep (se 3 (by rfl) ⟨2804510, by rfl⟩ : syracuseStep 14957389 = 5609021) B5609021
theorem B1456991 : Blo 968591 1456991 := bstep (se 1 (by rfl) ⟨1092743, by rfl⟩ : syracuseStep 1456991 = 2185487) B2185487
theorem B56736611 : Blo 968591 56736611 := bstep (se 1 (by rfl) ⟨42552458, by rfl⟩ : syracuseStep 56736611 = 85104917) B85104917
theorem B1457003 : Blo 968591 1457003 := bstep (se 1 (by rfl) ⟨1092752, by rfl⟩ : syracuseStep 1457003 = 2185505) B2185505
theorem B1457231 : Blo 968591 1457231 := bstep (se 1 (by rfl) ⟨1092923, by rfl⟩ : syracuseStep 1457231 = 2185847) B2185847
theorem B1227899 : Blo 968591 1227899 := bstep (se 1 (by rfl) ⟨920924, by rfl⟩ : syracuseStep 1227899 = 1841849) B1841849
theorem B1457351 : Blo 968591 1457351 := bstep (se 1 (by rfl) ⟨1093013, by rfl⟩ : syracuseStep 1457351 = 2186027) B2186027
theorem B1457513 : Blo 968591 1457513 := bstep (se 2 (by rfl) ⟨546567, by rfl⟩ : syracuseStep 1457513 = 1093135) B1093135
theorem B14925181 : Blo 968591 14925181 := bstep (se 3 (by rfl) ⟨2798471, by rfl⟩ : syracuseStep 14925181 = 5596943) B5596943
theorem B3325313 : Blo 968591 3325313 := bstep (se 2 (by rfl) ⟨1246992, by rfl⟩ : syracuseStep 3325313 = 2493985) B2493985
theorem B1457591 : Blo 968591 1457591 := bstep (se 1 (by rfl) ⟨1093193, by rfl⟩ : syracuseStep 1457591 = 2186387) B2186387
theorem B1457627 : Blo 968591 1457627 := bstep (se 1 (by rfl) ⟨1093220, by rfl⟩ : syracuseStep 1457627 = 2186441) B2186441
theorem B3325465 : Blo 968591 3325465 := bstep (se 2 (by rfl) ⟨1247049, by rfl⟩ : syracuseStep 3325465 = 2494099) B2494099
theorem B1556047 : Blo 968591 1556047 := bstep (se 1 (by rfl) ⟨1167035, by rfl⟩ : syracuseStep 1556047 = 2334071) B2334071
theorem B4669177 : Blo 968591 4669177 := bstep (se 2 (by rfl) ⟨1750941, by rfl⟩ : syracuseStep 4669177 = 3501883) B3501883
theorem B1458095 : Blo 968591 1458095 := bstep (se 1 (by rfl) ⟨1093571, by rfl⟩ : syracuseStep 1458095 = 2187143) B2187143
theorem B1458185 : Blo 968591 1458185 := bstep (se 2 (by rfl) ⟨546819, by rfl⟩ : syracuseStep 1458185 = 1093639) B1093639
theorem B1458215 : Blo 968591 1458215 := bstep (se 1 (by rfl) ⟨1093661, by rfl⟩ : syracuseStep 1458215 = 2187323) B2187323
theorem B1458299 : Blo 968591 1458299 := bstep (se 1 (by rfl) ⟨1093724, by rfl⟩ : syracuseStep 1458299 = 2187449) B2187449
theorem B6996131 : Blo 968591 6996131 := bstep (se 1 (by rfl) ⟨5247098, by rfl⟩ : syracuseStep 6996131 = 10494197) B10494197
theorem B1458425 : Blo 968591 1458425 := bstep (se 2 (by rfl) ⟨546909, by rfl⟩ : syracuseStep 1458425 = 1093819) B1093819
theorem B12271931 : Blo 968591 12271931 := bstep (se 1 (by rfl) ⟨9203948, by rfl⟩ : syracuseStep 12271931 = 18407897) B18407897
theorem B18694475 : Blo 968591 18694475 := bstep (se 1 (by rfl) ⟨14020856, by rfl⟩ : syracuseStep 18694475 = 28041713) B28041713
theorem B1458527 : Blo 968591 1458527 := bstep (se 1 (by rfl) ⟨1093895, by rfl⟩ : syracuseStep 1458527 = 2187791) B2187791
theorem B1458539 : Blo 968591 1458539 := bstep (se 1 (by rfl) ⟨1093904, by rfl⟩ : syracuseStep 1458539 = 2187809) B2187809
theorem B2179547 : Blo 968591 2179547 := bstep (se 1 (by rfl) ⟨1634660, by rfl⟩ : syracuseStep 2179547 = 3269321) B3269321
theorem B1458767 : Blo 968591 1458767 := bstep (se 1 (by rfl) ⟨1094075, by rfl⟩ : syracuseStep 1458767 = 2188151) B2188151
theorem B34554509 : Blo 968591 34554509 := bstep (se 3 (by rfl) ⟨6478970, by rfl⟩ : syracuseStep 34554509 = 12957941) B12957941
theorem B1458887 : Blo 968591 1458887 := bstep (se 1 (by rfl) ⟨1094165, by rfl⟩ : syracuseStep 1458887 = 2188331) B2188331
theorem B4670237 : Blo 968591 4670237 := bstep (se 3 (by rfl) ⟨875669, by rfl⟩ : syracuseStep 4670237 = 1751339) B1751339
theorem B12436375 : Blo 968591 12436375 := bstep (se 1 (by rfl) ⟨9327281, by rfl⟩ : syracuseStep 12436375 = 18654563) B18654563
theorem B2180015 : Blo 968591 2180015 := bstep (se 1 (by rfl) ⟨1635011, by rfl⟩ : syracuseStep 2180015 = 3270023) B3270023
theorem B2180267 : Blo 968591 2180267 := bstep (se 1 (by rfl) ⟨1635200, by rfl⟩ : syracuseStep 2180267 = 3270401) B3270401
theorem B5522813 : Blo 968591 5522813 := bstep (se 3 (by rfl) ⟨1035527, by rfl⟩ : syracuseStep 5522813 = 2071055) B2071055
theorem B6210989 : Blo 968591 6210989 := bstep (se 3 (by rfl) ⟨1164560, by rfl⟩ : syracuseStep 6210989 = 2329121) B2329121
theorem B1164719 : Blo 968591 1164719 := bstep (se 1 (by rfl) ⟨873539, by rfl⟩ : syracuseStep 1164719 = 1747079) B1747079
theorem B7358039 : Blo 968591 7358039 := bstep (se 1 (by rfl) ⟨5518529, by rfl⟩ : syracuseStep 7358039 = 11037059) B11037059
theorem B6211217 : Blo 968591 6211217 := bstep (se 2 (by rfl) ⟨2329206, by rfl⟩ : syracuseStep 6211217 = 4658413) B4658413
theorem B59754131 : Blo 968591 59754131 := bstep (se 1 (by rfl) ⟨44815598, by rfl⟩ : syracuseStep 59754131 = 89631197) B89631197
theorem B2180807 : Blo 968591 2180807 := bstep (se 1 (by rfl) ⟨1635605, by rfl⟩ : syracuseStep 2180807 = 3271211) B3271211
theorem B968623 : Blo 968591 968623 := bstep (se 1 (by rfl) ⟨726467, by rfl⟩ : syracuseStep 968623 = 1452935) B1452935
theorem B3688375 : Blo 968591 3688375 := bstep (se 1 (by rfl) ⟨2766281, by rfl⟩ : syracuseStep 3688375 = 5532563) B5532563
theorem B968647 : Blo 968591 968647 := bstep (se 1 (by rfl) ⟨726485, by rfl⟩ : syracuseStep 968647 = 1452971) B1452971
theorem B968667 : Blo 968591 968667 := bstep (se 1 (by rfl) ⟨726500, by rfl⟩ : syracuseStep 968667 = 1453001) B1453001
theorem B7096349 : Blo 968591 7096349 := bstep (se 3 (by rfl) ⟨1330565, by rfl⟩ : syracuseStep 7096349 = 2661131) B2661131
theorem B968743 : Blo 968591 968743 := bstep (se 1 (by rfl) ⟨726557, by rfl⟩ : syracuseStep 968743 = 1453115) B1453115
theorem B968783 : Blo 968591 968783 := bstep (se 1 (by rfl) ⟨726587, by rfl⟩ : syracuseStep 968783 = 1453175) B1453175
theorem B968799 : Blo 968591 968799 := bstep (se 1 (by rfl) ⟨726599, by rfl⟩ : syracuseStep 968799 = 1453199) B1453199
theorem B968827 : Blo 968591 968827 := bstep (se 1 (by rfl) ⟨726620, by rfl⟩ : syracuseStep 968827 = 1453241) B1453241
theorem B968879 : Blo 968591 968879 := bstep (se 1 (by rfl) ⟨726659, by rfl⟩ : syracuseStep 968879 = 1453319) B1453319
theorem B968903 : Blo 968591 968903 := bstep (se 1 (by rfl) ⟨726677, by rfl⟩ : syracuseStep 968903 = 1453355) B1453355
theorem B968923 : Blo 968591 968923 := bstep (se 1 (by rfl) ⟨726692, by rfl⟩ : syracuseStep 968923 = 1453385) B1453385
theorem B968999 : Blo 968591 968999 := bstep (se 1 (by rfl) ⟨726749, by rfl⟩ : syracuseStep 968999 = 1453499) B1453499
theorem B969039 : Blo 968591 969039 := bstep (se 1 (by rfl) ⟨726779, by rfl⟩ : syracuseStep 969039 = 1453559) B1453559
theorem B21023063 : Blo 968591 21023063 := bstep (se 1 (by rfl) ⟨15767297, by rfl⟩ : syracuseStep 21023063 = 31534595) B31534595
theorem B969055 : Blo 968591 969055 := bstep (se 1 (by rfl) ⟨726791, by rfl⟩ : syracuseStep 969055 = 1453583) B1453583
theorem B969083 : Blo 968591 969083 := bstep (se 1 (by rfl) ⟨726812, by rfl⟩ : syracuseStep 969083 = 1453625) B1453625
theorem B3688847 : Blo 968591 3688847 := bstep (se 1 (by rfl) ⟨2766635, by rfl⟩ : syracuseStep 3688847 = 5533271) B5533271
theorem B13978007 : Blo 968591 13978007 := bstep (se 1 (by rfl) ⟨10483505, by rfl⟩ : syracuseStep 13978007 = 20967011) B20967011
theorem B969135 : Blo 968591 969135 := bstep (se 1 (by rfl) ⟨726851, by rfl⟩ : syracuseStep 969135 = 1453703) B1453703
theorem B969159 : Blo 968591 969159 := bstep (se 1 (by rfl) ⟨726869, by rfl⟩ : syracuseStep 969159 = 1453739) B1453739
theorem B969179 : Blo 968591 969179 := bstep (se 1 (by rfl) ⟨726884, by rfl⟩ : syracuseStep 969179 = 1453769) B1453769
theorem B4672025 : Blo 968591 4672025 := bstep (se 2 (by rfl) ⟨1752009, by rfl⟩ : syracuseStep 4672025 = 3504019) B3504019
theorem B969255 : Blo 968591 969255 := bstep (se 1 (by rfl) ⟨726941, by rfl⟩ : syracuseStep 969255 = 1453883) B1453883
theorem B2181671 : Blo 968591 2181671 := bstep (se 1 (by rfl) ⟨1636253, by rfl⟩ : syracuseStep 2181671 = 3272507) B3272507
theorem B969295 : Blo 968591 969295 := bstep (se 1 (by rfl) ⟨726971, by rfl⟩ : syracuseStep 969295 = 1453943) B1453943
theorem B969311 : Blo 968591 969311 := bstep (se 1 (by rfl) ⟨726983, by rfl⟩ : syracuseStep 969311 = 1453967) B1453967
theorem B969339 : Blo 968591 969339 := bstep (se 1 (by rfl) ⟨727004, by rfl⟩ : syracuseStep 969339 = 1454009) B1454009
theorem B969391 : Blo 968591 969391 := bstep (se 1 (by rfl) ⟨727043, by rfl⟩ : syracuseStep 969391 = 1454087) B1454087
theorem B969415 : Blo 968591 969415 := bstep (se 1 (by rfl) ⟨727061, by rfl⟩ : syracuseStep 969415 = 1454123) B1454123
theorem B969435 : Blo 968591 969435 := bstep (se 1 (by rfl) ⟨727076, by rfl⟩ : syracuseStep 969435 = 1454153) B1454153
theorem B6638365 : Blo 968591 6638365 := bstep (se 3 (by rfl) ⟨1244693, by rfl⟩ : syracuseStep 6638365 = 2489387) B2489387
theorem B969511 : Blo 968591 969511 := bstep (se 1 (by rfl) ⟨727133, by rfl⟩ : syracuseStep 969511 = 1454267) B1454267
theorem B969551 : Blo 968591 969551 := bstep (se 1 (by rfl) ⟨727163, by rfl⟩ : syracuseStep 969551 = 1454327) B1454327
theorem B969567 : Blo 968591 969567 := bstep (se 1 (by rfl) ⟨727175, by rfl⟩ : syracuseStep 969567 = 1454351) B1454351
theorem B2181995 : Blo 968591 2181995 := bstep (se 1 (by rfl) ⟨1636496, by rfl⟩ : syracuseStep 2181995 = 3272993) B3272993
theorem B969595 : Blo 968591 969595 := bstep (se 1 (by rfl) ⟨727196, by rfl⟩ : syracuseStep 969595 = 1454393) B1454393
theorem B2182049 : Blo 968591 2182049 := bstep (se 2 (by rfl) ⟨818268, by rfl⟩ : syracuseStep 2182049 = 1636537) B1636537
theorem B969647 : Blo 968591 969647 := bstep (se 1 (by rfl) ⟨727235, by rfl⟩ : syracuseStep 969647 = 1454471) B1454471
theorem B969671 : Blo 968591 969671 := bstep (se 1 (by rfl) ⟨727253, by rfl⟩ : syracuseStep 969671 = 1454507) B1454507
theorem B969691 : Blo 968591 969691 := bstep (se 1 (by rfl) ⟨727268, by rfl⟩ : syracuseStep 969691 = 1454537) B1454537
theorem B969767 : Blo 968591 969767 := bstep (se 1 (by rfl) ⟨727325, by rfl⟩ : syracuseStep 969767 = 1454651) B1454651
theorem B969807 : Blo 968591 969807 := bstep (se 1 (by rfl) ⟨727355, by rfl⟩ : syracuseStep 969807 = 1454711) B1454711
theorem B969823 : Blo 968591 969823 := bstep (se 1 (by rfl) ⟨727367, by rfl⟩ : syracuseStep 969823 = 1454735) B1454735
theorem B969851 : Blo 968591 969851 := bstep (se 1 (by rfl) ⟨727388, by rfl⟩ : syracuseStep 969851 = 1454777) B1454777
theorem B969903 : Blo 968591 969903 := bstep (se 1 (by rfl) ⟨727427, by rfl⟩ : syracuseStep 969903 = 1454855) B1454855
theorem B969927 : Blo 968591 969927 := bstep (se 1 (by rfl) ⟨727445, by rfl⟩ : syracuseStep 969927 = 1454891) B1454891
theorem B969947 : Blo 968591 969947 := bstep (se 1 (by rfl) ⟨727460, by rfl⟩ : syracuseStep 969947 = 1454921) B1454921
theorem B2182391 : Blo 968591 2182391 := bstep (se 1 (by rfl) ⟨1636793, by rfl⟩ : syracuseStep 2182391 = 3273587) B3273587
theorem B970023 : Blo 968591 970023 := bstep (se 1 (by rfl) ⟨727517, by rfl⟩ : syracuseStep 970023 = 1455035) B1455035
theorem B970063 : Blo 968591 970063 := bstep (se 1 (by rfl) ⟨727547, by rfl⟩ : syracuseStep 970063 = 1455095) B1455095
theorem B970079 : Blo 968591 970079 := bstep (se 1 (by rfl) ⟨727559, by rfl⟩ : syracuseStep 970079 = 1455119) B1455119
theorem B3689833 : Blo 968591 3689833 := bstep (se 2 (by rfl) ⟨1383687, by rfl⟩ : syracuseStep 3689833 = 2767375) B2767375
theorem B970107 : Blo 968591 970107 := bstep (se 1 (by rfl) ⟨727580, by rfl⟩ : syracuseStep 970107 = 1455161) B1455161
theorem B970159 : Blo 968591 970159 := bstep (se 1 (by rfl) ⟨727619, by rfl⟩ : syracuseStep 970159 = 1455239) B1455239
theorem B970183 : Blo 968591 970183 := bstep (se 1 (by rfl) ⟨727637, by rfl⟩ : syracuseStep 970183 = 1455275) B1455275
theorem B5524955 : Blo 968591 5524955 := bstep (se 1 (by rfl) ⟨4143716, by rfl⟩ : syracuseStep 5524955 = 8287433) B8287433
theorem B970203 : Blo 968591 970203 := bstep (se 1 (by rfl) ⟨727652, by rfl⟩ : syracuseStep 970203 = 1455305) B1455305
theorem B970279 : Blo 968591 970279 := bstep (se 1 (by rfl) ⟨727709, by rfl⟩ : syracuseStep 970279 = 1455419) B1455419
theorem B970319 : Blo 968591 970319 := bstep (se 1 (by rfl) ⟨727739, by rfl⟩ : syracuseStep 970319 = 1455479) B1455479
theorem B970335 : Blo 968591 970335 := bstep (se 1 (by rfl) ⟨727751, by rfl⟩ : syracuseStep 970335 = 1455503) B1455503
theorem B970363 : Blo 968591 970363 := bstep (se 1 (by rfl) ⟨727772, by rfl⟩ : syracuseStep 970363 = 1455545) B1455545
theorem B1330811 : Blo 968591 1330811 := bstep (se 1 (by rfl) ⟨998108, by rfl⟩ : syracuseStep 1330811 = 1996217) B1996217
theorem B3690107 : Blo 968591 3690107 := bstep (se 1 (by rfl) ⟨2767580, by rfl⟩ : syracuseStep 3690107 = 5535161) B5535161
theorem B3493523 : Blo 968591 3493523 := bstep (se 1 (by rfl) ⟨2620142, by rfl⟩ : syracuseStep 3493523 = 5240285) B5240285
theorem B970415 : Blo 968591 970415 := bstep (se 1 (by rfl) ⟨727811, by rfl⟩ : syracuseStep 970415 = 1455623) B1455623
theorem B970439 : Blo 968591 970439 := bstep (se 1 (by rfl) ⟨727829, by rfl⟩ : syracuseStep 970439 = 1455659) B1455659
theorem B970459 : Blo 968591 970459 := bstep (se 1 (by rfl) ⟨727844, by rfl⟩ : syracuseStep 970459 = 1455689) B1455689
theorem B970535 : Blo 968591 970535 := bstep (se 1 (by rfl) ⟨727901, by rfl⟩ : syracuseStep 970535 = 1455803) B1455803
theorem B2182985 : Blo 968591 2182985 := bstep (se 2 (by rfl) ⟨818619, by rfl⟩ : syracuseStep 2182985 = 1637239) B1637239
theorem B970575 : Blo 968591 970575 := bstep (se 1 (by rfl) ⟨727931, by rfl⟩ : syracuseStep 970575 = 1455863) B1455863
theorem B970591 : Blo 968591 970591 := bstep (se 1 (by rfl) ⟨727943, by rfl⟩ : syracuseStep 970591 = 1455887) B1455887
theorem B970619 : Blo 968591 970619 := bstep (se 1 (by rfl) ⟨727964, by rfl⟩ : syracuseStep 970619 = 1455929) B1455929
theorem B970671 : Blo 968591 970671 := bstep (se 1 (by rfl) ⟨728003, by rfl⟩ : syracuseStep 970671 = 1456007) B1456007
theorem B6639545 : Blo 968591 6639545 := bstep (se 2 (by rfl) ⟨2489829, by rfl⟩ : syracuseStep 6639545 = 4979659) B4979659
theorem B970695 : Blo 968591 970695 := bstep (se 1 (by rfl) ⟨728021, by rfl⟩ : syracuseStep 970695 = 1456043) B1456043
theorem B970715 : Blo 968591 970715 := bstep (se 1 (by rfl) ⟨728036, by rfl⟩ : syracuseStep 970715 = 1456073) B1456073
theorem B970791 : Blo 968591 970791 := bstep (se 1 (by rfl) ⟨728093, by rfl⟩ : syracuseStep 970791 = 1456187) B1456187
theorem B970831 : Blo 968591 970831 := bstep (se 1 (by rfl) ⟨728123, by rfl⟩ : syracuseStep 970831 = 1456247) B1456247
theorem B970847 : Blo 968591 970847 := bstep (se 1 (by rfl) ⟨728135, by rfl⟩ : syracuseStep 970847 = 1456271) B1456271
theorem B970875 : Blo 968591 970875 := bstep (se 1 (by rfl) ⟨728156, by rfl⟩ : syracuseStep 970875 = 1456313) B1456313
theorem B970927 : Blo 968591 970927 := bstep (se 1 (by rfl) ⟨728195, by rfl⟩ : syracuseStep 970927 = 1456391) B1456391
theorem B970951 : Blo 968591 970951 := bstep (se 1 (by rfl) ⟨728213, by rfl⟩ : syracuseStep 970951 = 1456427) B1456427
theorem B970971 : Blo 968591 970971 := bstep (se 1 (by rfl) ⟨728228, by rfl⟩ : syracuseStep 970971 = 1456457) B1456457
theorem B971047 : Blo 968591 971047 := bstep (se 1 (by rfl) ⟨728285, by rfl⟩ : syracuseStep 971047 = 1456571) B1456571
theorem B971087 : Blo 968591 971087 := bstep (se 1 (by rfl) ⟨728315, by rfl⟩ : syracuseStep 971087 = 1456631) B1456631
theorem B971103 : Blo 968591 971103 := bstep (se 1 (by rfl) ⟨728327, by rfl⟩ : syracuseStep 971103 = 1456655) B1456655
theorem B1331563 : Blo 968591 1331563 := bstep (se 1 (by rfl) ⟨998672, by rfl⟩ : syracuseStep 1331563 = 1997345) B1997345
theorem B971131 : Blo 968591 971131 := bstep (se 1 (by rfl) ⟨728348, by rfl⟩ : syracuseStep 971131 = 1456697) B1456697
theorem B971183 : Blo 968591 971183 := bstep (se 1 (by rfl) ⟨728387, by rfl⟩ : syracuseStep 971183 = 1456775) B1456775
theorem B971207 : Blo 968591 971207 := bstep (se 1 (by rfl) ⟨728405, by rfl⟩ : syracuseStep 971207 = 1456811) B1456811
theorem B971227 : Blo 968591 971227 := bstep (se 1 (by rfl) ⟨728420, by rfl⟩ : syracuseStep 971227 = 1456841) B1456841
theorem B971303 : Blo 968591 971303 := bstep (se 1 (by rfl) ⟨728477, by rfl⟩ : syracuseStep 971303 = 1456955) B1456955
theorem B971343 : Blo 968591 971343 := bstep (se 1 (by rfl) ⟨728507, by rfl⟩ : syracuseStep 971343 = 1457015) B1457015
theorem B971359 : Blo 968591 971359 := bstep (se 1 (by rfl) ⟨728519, by rfl⟩ : syracuseStep 971359 = 1457039) B1457039
theorem B2183777 : Blo 968591 2183777 := bstep (se 2 (by rfl) ⟨818916, by rfl⟩ : syracuseStep 2183777 = 1637833) B1637833
theorem B971387 : Blo 968591 971387 := bstep (se 1 (by rfl) ⟨728540, by rfl⟩ : syracuseStep 971387 = 1457081) B1457081
theorem B971439 : Blo 968591 971439 := bstep (se 1 (by rfl) ⟨728579, by rfl⟩ : syracuseStep 971439 = 1457159) B1457159
theorem B971463 : Blo 968591 971463 := bstep (se 1 (by rfl) ⟨728597, by rfl⟩ : syracuseStep 971463 = 1457195) B1457195
theorem B971483 : Blo 968591 971483 := bstep (se 1 (by rfl) ⟨728612, by rfl⟩ : syracuseStep 971483 = 1457225) B1457225
theorem B971559 : Blo 968591 971559 := bstep (se 1 (by rfl) ⟨728669, by rfl⟩ : syracuseStep 971559 = 1457339) B1457339
theorem B971599 : Blo 968591 971599 := bstep (se 1 (by rfl) ⟨728699, by rfl⟩ : syracuseStep 971599 = 1457399) B1457399
theorem B971615 : Blo 968591 971615 := bstep (se 1 (by rfl) ⟨728711, by rfl⟩ : syracuseStep 971615 = 1457423) B1457423
theorem B971643 : Blo 968591 971643 := bstep (se 1 (by rfl) ⟨728732, by rfl⟩ : syracuseStep 971643 = 1457465) B1457465
theorem B971695 : Blo 968591 971695 := bstep (se 1 (by rfl) ⟨728771, by rfl⟩ : syracuseStep 971695 = 1457543) B1457543
theorem B2184119 : Blo 968591 2184119 := bstep (se 1 (by rfl) ⟨1638089, by rfl⟩ : syracuseStep 2184119 = 3276179) B3276179
theorem B971719 : Blo 968591 971719 := bstep (se 1 (by rfl) ⟨728789, by rfl⟩ : syracuseStep 971719 = 1457579) B1457579
theorem B971739 : Blo 968591 971739 := bstep (se 1 (by rfl) ⟨728804, by rfl⟩ : syracuseStep 971739 = 1457609) B1457609
theorem B971815 : Blo 968591 971815 := bstep (se 1 (by rfl) ⟨728861, by rfl⟩ : syracuseStep 971815 = 1457723) B1457723
theorem B971855 : Blo 968591 971855 := bstep (se 1 (by rfl) ⟨728891, by rfl⟩ : syracuseStep 971855 = 1457783) B1457783
theorem B22369373 : Blo 968591 22369373 := bstep (se 3 (by rfl) ⟨4194257, by rfl⟩ : syracuseStep 22369373 = 8388515) B8388515
theorem B971871 : Blo 968591 971871 := bstep (se 1 (by rfl) ⟨728903, by rfl⟩ : syracuseStep 971871 = 1457807) B1457807
theorem B971899 : Blo 968591 971899 := bstep (se 1 (by rfl) ⟨728924, by rfl⟩ : syracuseStep 971899 = 1457849) B1457849
theorem B971951 : Blo 968591 971951 := bstep (se 1 (by rfl) ⟨728963, by rfl⟩ : syracuseStep 971951 = 1457927) B1457927
theorem B971975 : Blo 968591 971975 := bstep (se 1 (by rfl) ⟨728981, by rfl⟩ : syracuseStep 971975 = 1457963) B1457963
theorem B14931145 : Blo 968591 14931145 := bstep (se 2 (by rfl) ⟨5599179, by rfl⟩ : syracuseStep 14931145 = 11198359) B11198359
theorem B5526731 : Blo 968591 5526731 := bstep (se 1 (by rfl) ⟨4145048, by rfl⟩ : syracuseStep 5526731 = 8290097) B8290097
theorem B971995 : Blo 968591 971995 := bstep (se 1 (by rfl) ⟨728996, by rfl⟩ : syracuseStep 971995 = 1457993) B1457993
theorem B972071 : Blo 968591 972071 := bstep (se 1 (by rfl) ⟨729053, by rfl⟩ : syracuseStep 972071 = 1458107) B1458107
theorem B972111 : Blo 968591 972111 := bstep (se 1 (by rfl) ⟨729083, by rfl⟩ : syracuseStep 972111 = 1458167) B1458167
theorem B972127 : Blo 968591 972127 := bstep (se 1 (by rfl) ⟨729095, by rfl⟩ : syracuseStep 972127 = 1458191) B1458191
theorem B972155 : Blo 968591 972155 := bstep (se 1 (by rfl) ⟨729116, by rfl⟩ : syracuseStep 972155 = 1458233) B1458233
theorem B972207 : Blo 968591 972207 := bstep (se 1 (by rfl) ⟨729155, by rfl⟩ : syracuseStep 972207 = 1458311) B1458311
theorem B1496503 : Blo 968591 1496503 := bstep (se 1 (by rfl) ⟨1122377, by rfl⟩ : syracuseStep 1496503 = 2244755) B2244755
theorem B972231 : Blo 968591 972231 := bstep (se 1 (by rfl) ⟨729173, by rfl⟩ : syracuseStep 972231 = 1458347) B1458347
theorem B972251 : Blo 968591 972251 := bstep (se 1 (by rfl) ⟨729188, by rfl⟩ : syracuseStep 972251 = 1458377) B1458377
theorem B2184713 : Blo 968591 2184713 := bstep (se 2 (by rfl) ⟨819267, by rfl⟩ : syracuseStep 2184713 = 1638535) B1638535
theorem B972327 : Blo 968591 972327 := bstep (se 1 (by rfl) ⟨729245, by rfl⟩ : syracuseStep 972327 = 1458491) B1458491
theorem B972367 : Blo 968591 972367 := bstep (se 1 (by rfl) ⟨729275, by rfl⟩ : syracuseStep 972367 = 1458551) B1458551
theorem B972383 : Blo 968591 972383 := bstep (se 1 (by rfl) ⟨729287, by rfl⟩ : syracuseStep 972383 = 1458575) B1458575
theorem B972411 : Blo 968591 972411 := bstep (se 1 (by rfl) ⟨729308, by rfl⟩ : syracuseStep 972411 = 1458617) B1458617
theorem B5527187 : Blo 968591 5527187 := bstep (se 1 (by rfl) ⟨4145390, by rfl⟩ : syracuseStep 5527187 = 8290781) B8290781
theorem B972463 : Blo 968591 972463 := bstep (se 1 (by rfl) ⟨729347, by rfl⟩ : syracuseStep 972463 = 1458695) B1458695
theorem B972487 : Blo 968591 972487 := bstep (se 1 (by rfl) ⟨729365, by rfl⟩ : syracuseStep 972487 = 1458731) B1458731
theorem B972507 : Blo 968591 972507 := bstep (se 1 (by rfl) ⟨729380, by rfl⟩ : syracuseStep 972507 = 1458761) B1458761
theorem B972583 : Blo 968591 972583 := bstep (se 1 (by rfl) ⟨729437, by rfl⟩ : syracuseStep 972583 = 1458875) B1458875
theorem B10639163 : Blo 968591 10639163 := bstep (se 1 (by rfl) ⟨7979372, by rfl⟩ : syracuseStep 10639163 = 15958745) B15958745
theorem B2185055 : Blo 968591 2185055 := bstep (se 1 (by rfl) ⟨1638791, by rfl⟩ : syracuseStep 2185055 = 3277583) B3277583
theorem B7362413 : Blo 968591 7362413 := bstep (se 3 (by rfl) ⟨1380452, by rfl⟩ : syracuseStep 7362413 = 2760905) B2760905
theorem B2185235 : Blo 968591 2185235 := bstep (se 1 (by rfl) ⟨1638926, by rfl⟩ : syracuseStep 2185235 = 3277853) B3277853
theorem B2185577 : Blo 968591 2185577 := bstep (se 2 (by rfl) ⟨819591, by rfl⟩ : syracuseStep 2185577 = 1639183) B1639183
theorem B6314669 : Blo 968591 6314669 := bstep (se 3 (by rfl) ⟨1184000, by rfl⟩ : syracuseStep 6314669 = 2368001) B2368001
theorem B4905683 : Blo 968591 4905683 := bstep (se 1 (by rfl) ⟨3679262, by rfl⟩ : syracuseStep 4905683 = 7358525) B7358525
theorem B2186171 : Blo 968591 2186171 := bstep (se 1 (by rfl) ⟨1639628, by rfl⟩ : syracuseStep 2186171 = 3279257) B3279257
theorem B3103763 : Blo 968591 3103763 := bstep (se 1 (by rfl) ⟨2327822, by rfl⟩ : syracuseStep 3103763 = 4655645) B4655645
theorem B2186297 : Blo 968591 2186297 := bstep (se 2 (by rfl) ⟨819861, by rfl⟩ : syracuseStep 2186297 = 1639723) B1639723
theorem B6216857 : Blo 968591 6216857 := bstep (se 2 (by rfl) ⟨2331321, by rfl⟩ : syracuseStep 6216857 = 4662643) B4662643
theorem B2186639 : Blo 968591 2186639 := bstep (se 1 (by rfl) ⟨1639979, by rfl⟩ : syracuseStep 2186639 = 3279959) B3279959
theorem B3497417 : Blo 968591 3497417 := bstep (se 2 (by rfl) ⟨1311531, by rfl⟩ : syracuseStep 3497417 = 2623063) B2623063
theorem B2186963 : Blo 968591 2186963 := bstep (se 1 (by rfl) ⟨1640222, by rfl⟩ : syracuseStep 2186963 = 3280445) B3280445
theorem B3498137 : Blo 968591 3498137 := bstep (se 2 (by rfl) ⟨1311801, by rfl⟩ : syracuseStep 3498137 = 2623603) B2623603
theorem B3269159 : Blo 968591 3269159 := bstep (se 1 (by rfl) ⟨2451869, by rfl⟩ : syracuseStep 3269159 = 4903739) B4903739
theorem B2187899 : Blo 968591 2187899 := bstep (se 1 (by rfl) ⟨1640924, by rfl⟩ : syracuseStep 2187899 = 3281849) B3281849
theorem B3269267 : Blo 968591 3269267 := bstep (se 1 (by rfl) ⟨2451950, by rfl⟩ : syracuseStep 3269267 = 4903901) B4903901
theorem B7365329 : Blo 968591 7365329 := bstep (se 2 (by rfl) ⟨2761998, by rfl⟩ : syracuseStep 7365329 = 5523997) B5523997
theorem B2188025 : Blo 968591 2188025 := bstep (se 2 (by rfl) ⟨820509, by rfl⟩ : syracuseStep 2188025 = 1641019) B1641019
theorem B3269483 : Blo 968591 3269483 := bstep (se 1 (by rfl) ⟨2452112, by rfl⟩ : syracuseStep 3269483 = 4904225) B4904225
theorem B10642283 : Blo 968591 10642283 := bstep (se 1 (by rfl) ⟨7981712, by rfl⟩ : syracuseStep 10642283 = 15963425) B15963425
theorem B3269537 : Blo 968591 3269537 := bstep (se 2 (by rfl) ⟨1226076, by rfl⟩ : syracuseStep 3269537 = 2452153) B2452153
theorem B4907951 : Blo 968591 4907951 := bstep (se 1 (by rfl) ⟨3680963, by rfl⟩ : syracuseStep 4907951 = 7361927) B7361927
theorem B2188295 : Blo 968591 2188295 := bstep (se 1 (by rfl) ⟨1641221, by rfl⟩ : syracuseStep 2188295 = 3282443) B3282443
theorem B3270131 : Blo 968591 3270131 := bstep (se 1 (by rfl) ⟨2452598, by rfl⟩ : syracuseStep 3270131 = 4905197) B4905197
theorem B31090321 : Blo 968591 31090321 := bstep (se 2 (by rfl) ⟨11658870, by rfl⟩ : syracuseStep 31090321 = 23317741) B23317741
theorem B3270671 : Blo 968591 3270671 := bstep (se 1 (by rfl) ⟨2453003, by rfl⟩ : syracuseStep 3270671 = 4906007) B4906007
theorem B1108091 : Blo 968591 1108091 := bstep (se 1 (by rfl) ⟨831068, by rfl⟩ : syracuseStep 1108091 = 1662137) B1662137
theorem B5237257 : Blo 968591 5237257 := bstep (se 2 (by rfl) ⟨1963971, by rfl⟩ : syracuseStep 5237257 = 3927943) B3927943
theorem B3500603 : Blo 968591 3500603 := bstep (se 1 (by rfl) ⟨2625452, by rfl⟩ : syracuseStep 3500603 = 5250905) B5250905
theorem B3271265 : Blo 968591 3271265 := bstep (se 2 (by rfl) ⟨1226724, by rfl⟩ : syracuseStep 3271265 = 2453449) B2453449
theorem B6220547 : Blo 968591 6220547 := bstep (se 1 (by rfl) ⟨4665410, by rfl⟩ : syracuseStep 6220547 = 9330821) B9330821
theorem B16608077 : Blo 968591 16608077 := bstep (se 3 (by rfl) ⟨3114014, by rfl⟩ : syracuseStep 16608077 = 6228029) B6228029
theorem B7367759 : Blo 968591 7367759 := bstep (se 1 (by rfl) ⟨5525819, by rfl⟩ : syracuseStep 7367759 = 11051639) B11051639
theorem B3501251 : Blo 968591 3501251 := bstep (se 1 (by rfl) ⟨2625938, by rfl⟩ : syracuseStep 3501251 = 5251877) B5251877
theorem B3108377 : Blo 968591 3108377 := bstep (se 2 (by rfl) ⟨1165641, by rfl⟩ : syracuseStep 3108377 = 2331283) B2331283
theorem B1011295 : Blo 968591 1011295 := bstep (se 1 (by rfl) ⟨758471, by rfl⟩ : syracuseStep 1011295 = 1516943) B1516943
theorem B4255355 : Blo 968591 4255355 := bstep (se 1 (by rfl) ⟨3191516, by rfl⟩ : syracuseStep 4255355 = 6383033) B6383033
theorem B14970557 : Blo 968591 14970557 := bstep (se 3 (by rfl) ⟨2806979, by rfl⟩ : syracuseStep 14970557 = 5613959) B5613959
theorem B5533703 : Blo 968591 5533703 := bstep (se 1 (by rfl) ⟨4150277, by rfl⟩ : syracuseStep 5533703 = 8300555) B8300555
theorem B3272723 : Blo 968591 3272723 := bstep (se 1 (by rfl) ⟨2454542, by rfl⟩ : syracuseStep 3272723 = 4909085) B4909085
theorem B2453561 : Blo 968591 2453561 := bstep (se 2 (by rfl) ⟨920085, by rfl⟩ : syracuseStep 2453561 = 1840171) B1840171
theorem B3273047 : Blo 968591 3273047 := bstep (se 1 (by rfl) ⟨2454785, by rfl⟩ : syracuseStep 3273047 = 4909571) B4909571
theorem B1634735 : Blo 968591 1634735 := bstep (se 1 (by rfl) ⟨1226051, by rfl⟩ : syracuseStep 1634735 = 2452103) B2452103
theorem B5239505 : Blo 968591 5239505 := bstep (se 2 (by rfl) ⟨1964814, by rfl⟩ : syracuseStep 5239505 = 3929629) B3929629
theorem B3502921 : Blo 968591 3502921 := bstep (se 2 (by rfl) ⟨1313595, by rfl⟩ : syracuseStep 3502921 = 2627191) B2627191
theorem B1635167 : Blo 968591 1635167 := bstep (se 1 (by rfl) ⟨1226375, by rfl⟩ : syracuseStep 1635167 = 2452751) B2452751
theorem B2618219 : Blo 968591 2618219 := bstep (se 1 (by rfl) ⟨1963664, by rfl⟩ : syracuseStep 2618219 = 3927329) B3927329
theorem B39777635 : Blo 968591 39777635 := bstep (se 1 (by rfl) ⟨29833226, by rfl⟩ : syracuseStep 39777635 = 59666453) B59666453
theorem B1635727 : Blo 968591 1635727 := bstep (se 1 (by rfl) ⟨1226795, by rfl⟩ : syracuseStep 1635727 = 2453591) B2453591
theorem B3274127 : Blo 968591 3274127 := bstep (se 1 (by rfl) ⟨2455595, by rfl⟩ : syracuseStep 3274127 = 4911191) B4911191
theorem B2455049 : Blo 968591 2455049 := bstep (se 2 (by rfl) ⟨920643, by rfl⟩ : syracuseStep 2455049 = 1841287) B1841287
theorem B3274451 : Blo 968591 3274451 := bstep (se 1 (by rfl) ⟨2455838, by rfl⟩ : syracuseStep 3274451 = 4911677) B4911677
theorem B6649859 : Blo 968591 6649859 := bstep (se 1 (by rfl) ⟨4987394, by rfl⟩ : syracuseStep 6649859 = 9974789) B9974789
theorem B1636409 : Blo 968591 1636409 := bstep (se 2 (by rfl) ⟨613653, by rfl⟩ : syracuseStep 1636409 = 1227307) B1227307
theorem B4257949 : Blo 968591 4257949 := bstep (se 3 (by rfl) ⟨798365, by rfl⟩ : syracuseStep 4257949 = 1596731) B1596731
theorem B7371161 : Blo 968591 7371161 := bstep (se 2 (by rfl) ⟨2764185, by rfl⟩ : syracuseStep 7371161 = 5528371) B5528371
theorem B1964507 : Blo 968591 1964507 := bstep (se 1 (by rfl) ⟨1473380, by rfl⟩ : syracuseStep 1964507 = 2946761) B2946761
theorem B3930605 : Blo 968591 3930605 := bstep (se 3 (by rfl) ⟨736988, by rfl⟩ : syracuseStep 3930605 = 1473977) B1473977
theorem B2456203 : Blo 968591 2456203 := bstep (se 1 (by rfl) ⟨1842152, by rfl⟩ : syracuseStep 2456203 = 3684305) B3684305
theorem B1637111 : Blo 968591 1637111 := bstep (se 1 (by rfl) ⟨1227833, by rfl⟩ : syracuseStep 1637111 = 2455667) B2455667
theorem B3111709 : Blo 968591 3111709 := bstep (se 3 (by rfl) ⟨583445, by rfl⟩ : syracuseStep 3111709 = 1166891) B1166891
theorem B2489183 : Blo 968591 2489183 := bstep (se 1 (by rfl) ⟨1866887, by rfl⟩ : syracuseStep 2489183 = 3733775) B3733775
theorem B5536619 : Blo 968591 5536619 := bstep (se 1 (by rfl) ⟨4152464, by rfl⟩ : syracuseStep 5536619 = 8304929) B8304929
theorem B3275639 : Blo 968591 3275639 := bstep (se 1 (by rfl) ⟨2456729, by rfl⟩ : syracuseStep 3275639 = 4913459) B4913459
theorem B2456507 : Blo 968591 2456507 := bstep (se 1 (by rfl) ⟨1842380, by rfl⟩ : syracuseStep 2456507 = 3684761) B3684761
theorem B1637455 : Blo 968591 1637455 := bstep (se 1 (by rfl) ⟨1228091, by rfl⟩ : syracuseStep 1637455 = 2456183) B2456183
theorem B3275855 : Blo 968591 3275855 := bstep (se 1 (by rfl) ⟨2456891, by rfl⟩ : syracuseStep 3275855 = 4913783) B4913783
theorem B1637705 : Blo 968591 1637705 := bstep (se 2 (by rfl) ⟨614139, by rfl⟩ : syracuseStep 1637705 = 1228279) B1228279
theorem B3276233 : Blo 968591 3276233 := bstep (se 2 (by rfl) ⟨1228587, by rfl⟩ : syracuseStep 3276233 = 2457175) B2457175
theorem B2457287 : Blo 968591 2457287 := bstep (se 1 (by rfl) ⟨1842965, by rfl⟩ : syracuseStep 2457287 = 3685931) B3685931
theorem B3276503 : Blo 968591 3276503 := bstep (se 1 (by rfl) ⟨2457377, by rfl⟩ : syracuseStep 3276503 = 4914755) B4914755
theorem B1638137 : Blo 968591 1638137 := bstep (se 2 (by rfl) ⟨614301, by rfl⟩ : syracuseStep 1638137 = 1228603) B1228603
theorem B2457337 : Blo 968591 2457337 := bstep (se 2 (by rfl) ⟨921501, by rfl⟩ : syracuseStep 2457337 = 1843003) B1843003
theorem B1867627 : Blo 968591 1867627 := bstep (se 1 (by rfl) ⟨1400720, by rfl⟩ : syracuseStep 1867627 = 2801441) B2801441
theorem B5537645 : Blo 968591 5537645 := bstep (se 3 (by rfl) ⟨1038308, by rfl⟩ : syracuseStep 5537645 = 2076617) B2076617
theorem B1638319 : Blo 968591 1638319 := bstep (se 1 (by rfl) ⟨1228739, by rfl⟩ : syracuseStep 1638319 = 2457479) B2457479
theorem B3276719 : Blo 968591 3276719 := bstep (se 1 (by rfl) ⟨2457539, by rfl⟩ : syracuseStep 3276719 = 4915079) B4915079
theorem B4915403 : Blo 968591 4915403 := bstep (se 1 (by rfl) ⟨3686552, by rfl⟩ : syracuseStep 4915403 = 7373105) B7373105
theorem B1310953 : Blo 968591 1310953 := bstep (se 2 (by rfl) ⟨491607, by rfl⟩ : syracuseStep 1310953 = 983215) B983215
theorem B1048955 : Blo 968591 1048955 := bstep (se 1 (by rfl) ⟨786716, by rfl⟩ : syracuseStep 1048955 = 1573433) B1573433
theorem B23036339 : Blo 968591 23036339 := bstep (se 1 (by rfl) ⟨17277254, by rfl⟩ : syracuseStep 23036339 = 34554509) B34554509
theorem B20972033 : Blo 968591 20972033 := bstep (se 2 (by rfl) ⟨7864512, by rfl⟩ : syracuseStep 20972033 = 15729025) B15729025
theorem B10486273 : Blo 968591 10486273 := bstep (se 2 (by rfl) ⟨3932352, by rfl⟩ : syracuseStep 10486273 = 7864705) B7864705
theorem B3277313 : Blo 968591 3277313 := bstep (se 2 (by rfl) ⟨1228992, by rfl⟩ : syracuseStep 3277313 = 2457985) B2457985
theorem B3113491 : Blo 968591 3113491 := bstep (se 1 (by rfl) ⟨2335118, by rfl⟩ : syracuseStep 3113491 = 4670237) B4670237
theorem B2949803 : Blo 968591 2949803 := bstep (se 1 (by rfl) ⟨2212352, by rfl⟩ : syracuseStep 2949803 = 4424705) B4424705
theorem B8848055 : Blo 968591 8848055 := bstep (se 1 (by rfl) ⟨6636041, by rfl⟩ : syracuseStep 8848055 = 13272083) B13272083
theorem B3277799 : Blo 968591 3277799 := bstep (se 1 (by rfl) ⟨2458349, by rfl⟩ : syracuseStep 3277799 = 4916699) B4916699
theorem B1639399 : Blo 968591 1639399 := bstep (se 1 (by rfl) ⟨1229549, by rfl⟩ : syracuseStep 1639399 = 2459099) B2459099
theorem B16581833 : Blo 968591 16581833 := bstep (se 2 (by rfl) ⟨6218187, by rfl⟩ : syracuseStep 16581833 = 12436375) B12436375
theorem B1312039 : Blo 968591 1312039 := bstep (se 1 (by rfl) ⟨984029, by rfl⟩ : syracuseStep 1312039 = 1968059) B1968059
theorem B3278123 : Blo 968591 3278123 := bstep (se 1 (by rfl) ⟨2458592, by rfl⟩ : syracuseStep 3278123 = 4917185) B4917185
theorem B3278393 : Blo 968591 3278393 := bstep (se 2 (by rfl) ⟨1229397, by rfl⟩ : syracuseStep 3278393 = 2458795) B2458795
theorem B2459231 : Blo 968591 2459231 := bstep (se 1 (by rfl) ⟨1844423, by rfl⟩ : syracuseStep 2459231 = 3688847) B3688847
theorem B3114683 : Blo 968591 3114683 := bstep (se 1 (by rfl) ⟨2336012, by rfl⟩ : syracuseStep 3114683 = 4672025) B4672025
theorem B10487485 : Blo 968591 10487485 := bstep (se 3 (by rfl) ⟨1966403, by rfl⟩ : syracuseStep 10487485 = 3932807) B3932807
theorem B18876203 : Blo 968591 18876203 := bstep (se 1 (by rfl) ⟨14157152, by rfl⟩ : syracuseStep 18876203 = 28314305) B28314305
theorem B10487657 : Blo 968591 10487657 := bstep (se 2 (by rfl) ⟨3932871, by rfl⟩ : syracuseStep 10487657 = 7865743) B7865743
theorem B2099209 : Blo 968591 2099209 := bstep (se 2 (by rfl) ⟨787203, by rfl⟩ : syracuseStep 2099209 = 1574407) B1574407
theorem B1313033 : Blo 968591 1313033 := bstep (se 2 (by rfl) ⟨492387, by rfl⟩ : syracuseStep 1313033 = 984775) B984775
theorem B2459929 : Blo 968591 2459929 := bstep (se 2 (by rfl) ⟨922473, by rfl⟩ : syracuseStep 2459929 = 1844947) B1844947
theorem B4917671 : Blo 968591 4917671 := bstep (se 1 (by rfl) ⟨3688253, by rfl⟩ : syracuseStep 4917671 = 7376507) B7376507
theorem B2460071 : Blo 968591 2460071 := bstep (se 1 (by rfl) ⟨1845053, by rfl⟩ : syracuseStep 2460071 = 3690107) B3690107
theorem B2329015 : Blo 968591 2329015 := bstep (se 1 (by rfl) ⟨1746761, by rfl⟩ : syracuseStep 2329015 = 3493523) B3493523
theorem B4917833 : Blo 968591 4917833 := bstep (se 2 (by rfl) ⟨1844187, by rfl⟩ : syracuseStep 4917833 = 3688375) B3688375
theorem B2460233 : Blo 968591 2460233 := bstep (se 2 (by rfl) ⟨922587, by rfl⟩ : syracuseStep 2460233 = 1845175) B1845175
theorem B4426363 : Blo 968591 4426363 := bstep (se 1 (by rfl) ⟨3319772, by rfl⟩ : syracuseStep 4426363 = 6639545) B6639545
theorem B3279635 : Blo 968591 3279635 := bstep (se 1 (by rfl) ⟨2459726, by rfl⟩ : syracuseStep 3279635 = 4919453) B4919453
theorem B4983619 : Blo 968591 4983619 := bstep (se 1 (by rfl) ⟨3737714, by rfl⟩ : syracuseStep 4983619 = 7475429) B7475429
theorem B2493659 : Blo 968591 2493659 := bstep (se 1 (by rfl) ⟨1870244, by rfl⟩ : syracuseStep 2493659 = 3740489) B3740489
theorem B6983009 : Blo 968591 6983009 := bstep (se 2 (by rfl) ⟨2618628, by rfl⟩ : syracuseStep 6983009 = 5237257) B5237257
theorem B21237137 : Blo 968591 21237137 := bstep (se 2 (by rfl) ⟨7963926, by rfl⟩ : syracuseStep 21237137 = 15927853) B15927853
theorem B14912915 : Blo 968591 14912915 := bstep (se 1 (by rfl) ⟨11184686, by rfl⟩ : syracuseStep 14912915 = 22369373) B22369373
theorem B3280499 : Blo 968591 3280499 := bstep (se 1 (by rfl) ⟨2460374, by rfl⟩ : syracuseStep 3280499 = 4920749) B4920749
theorem B3280769 : Blo 968591 3280769 := bstep (se 2 (by rfl) ⟨1230288, by rfl⟩ : syracuseStep 3280769 = 2460577) B2460577
theorem B5902595 : Blo 968591 5902595 := bstep (se 1 (by rfl) ⟨4426946, by rfl⟩ : syracuseStep 5902595 = 8853893) B8853893
theorem B4919777 : Blo 968591 4919777 := bstep (se 2 (by rfl) ⟨1844916, by rfl⟩ : syracuseStep 4919777 = 3689833) B3689833
theorem B3281579 : Blo 968591 3281579 := bstep (se 1 (by rfl) ⟨2461184, by rfl⟩ : syracuseStep 3281579 = 4922369) B4922369
theorem B1348393 : Blo 968591 1348393 := bstep (se 2 (by rfl) ⟨505647, by rfl⟩ : syracuseStep 1348393 = 1011295) B1011295
theorem B177476417 : Blo 968591 177476417 := bstep (se 2 (by rfl) ⟨66553656, by rfl⟩ : syracuseStep 177476417 = 133107313) B133107313
theorem B2331611 : Blo 968591 2331611 := bstep (se 1 (by rfl) ⟨1748708, by rfl⟩ : syracuseStep 2331611 = 3497417) B3497417
theorem B4723687 : Blo 968591 4723687 := bstep (se 1 (by rfl) ⟨3542765, by rfl⟩ : syracuseStep 4723687 = 7085531) B7085531
theorem B3282119 : Blo 968591 3282119 := bstep (se 1 (by rfl) ⟨2461589, by rfl⟩ : syracuseStep 3282119 = 4923179) B4923179
theorem B2332091 : Blo 968591 2332091 := bstep (se 1 (by rfl) ⟨1749068, by rfl⟩ : syracuseStep 2332091 = 3498137) B3498137
theorem B2954909 : Blo 968591 2954909 := bstep (se 3 (by rfl) ⟨554045, by rfl⟩ : syracuseStep 2954909 = 1108091) B1108091
theorem B1840801 : Blo 968591 1840801 := bstep (se 2 (by rfl) ⟨690300, by rfl⟩ : syracuseStep 1840801 = 1380601) B1380601
theorem B1775417 : Blo 968591 1775417 := bstep (se 2 (by rfl) ⟨665781, by rfl⟩ : syracuseStep 1775417 = 1331563) B1331563
theorem B2332937 : Blo 968591 2332937 := bstep (se 2 (by rfl) ⟨874851, by rfl⟩ : syracuseStep 2332937 = 1749703) B1749703
theorem B42473879 : Blo 968591 42473879 := bstep (se 1 (by rfl) ⟨31855409, by rfl⟩ : syracuseStep 42473879 = 63710819) B63710819
theorem B5905003 : Blo 968591 5905003 := bstep (se 1 (by rfl) ⟨4428752, by rfl⟩ : syracuseStep 5905003 = 8857505) B8857505
theorem B14195317 : Blo 968591 14195317 := bstep (se 5 (by rfl) ⟨665405, by rfl⟩ : syracuseStep 14195317 = 1330811) B1330811
theorem B5249711 : Blo 968591 5249711 := bstep (se 1 (by rfl) ⟨3937283, by rfl⟩ : syracuseStep 5249711 = 7874567) B7874567
theorem B4922045 : Blo 968591 4922045 := bstep (se 3 (by rfl) ⟨922883, by rfl⟩ : syracuseStep 4922045 = 1845767) B1845767
theorem B4660087 : Blo 968591 4660087 := bstep (se 1 (by rfl) ⟨3495065, by rfl⟩ : syracuseStep 4660087 = 6990131) B6990131
theorem B1383323 : Blo 968591 1383323 := bstep (se 1 (by rfl) ⟨1037492, by rfl⟩ : syracuseStep 1383323 = 2074985) B2074985
theorem B2333735 : Blo 968591 2333735 := bstep (se 1 (by rfl) ⟨1750301, by rfl⟩ : syracuseStep 2333735 = 3500603) B3500603
theorem B2334167 : Blo 968591 2334167 := bstep (se 1 (by rfl) ⟨1750625, by rfl⟩ : syracuseStep 2334167 = 3501251) B3501251
theorem B4988425 : Blo 968591 4988425 := bstep (se 2 (by rfl) ⟨1870659, by rfl⟩ : syracuseStep 4988425 = 3741319) B3741319
theorem B5905979 : Blo 968591 5905979 := bstep (se 1 (by rfl) ⟨4429484, by rfl⟩ : syracuseStep 5905979 = 8858969) B8858969
theorem B3743347 : Blo 968591 3743347 := bstep (se 1 (by rfl) ⟨2807510, by rfl⟩ : syracuseStep 3743347 = 5615021) B5615021
theorem B2072251 : Blo 968591 2072251 := bstep (se 1 (by rfl) ⟨1554188, by rfl⟩ : syracuseStep 2072251 = 3108377) B3108377
theorem B3940253 : Blo 968591 3940253 := bstep (se 3 (by rfl) ⟨738797, by rfl⟩ : syracuseStep 3940253 = 1477595) B1477595
theorem B2760713 : Blo 968591 2760713 := bstep (se 2 (by rfl) ⟨1035267, by rfl⟩ : syracuseStep 2760713 = 2070535) B2070535
theorem B5677265 : Blo 968591 5677265 := bstep (se 2 (by rfl) ⟨2128974, by rfl⟩ : syracuseStep 5677265 = 4257949) B4257949
theorem B1089823 : Blo 968591 1089823 := bstep (se 1 (by rfl) ⟨817367, by rfl⟩ : syracuseStep 1089823 = 1634735) B1634735
theorem B1090111 : Blo 968591 1090111 := bstep (se 1 (by rfl) ⟨817583, by rfl⟩ : syracuseStep 1090111 = 1635167) B1635167
theorem B1745479 : Blo 968591 1745479 := bstep (se 1 (by rfl) ⟨1309109, by rfl⟩ : syracuseStep 1745479 = 2618219) B2618219
theorem B5251787 : Blo 968591 5251787 := bstep (se 1 (by rfl) ⟨3938840, by rfl⟩ : syracuseStep 5251787 = 7877681) B7877681
theorem B165815045 : Blo 968591 165815045 := bstep (se 4 (by rfl) ⟨15545160, by rfl⟩ : syracuseStep 165815045 = 31090321) B31090321
theorem B26518423 : Blo 968591 26518423 := bstep (se 1 (by rfl) ⟨19888817, by rfl⟩ : syracuseStep 26518423 = 39777635) B39777635
theorem B4138199 : Blo 968591 4138199 := bstep (se 1 (by rfl) ⟨3103649, by rfl⟩ : syracuseStep 4138199 = 6207299) B6207299
theorem B4138283 : Blo 968591 4138283 := bstep (se 1 (by rfl) ⟨3103712, by rfl⟩ : syracuseStep 4138283 = 6207425) B6207425
theorem B4433239 : Blo 968591 4433239 := bstep (se 1 (by rfl) ⟨3324929, by rfl⟩ : syracuseStep 4433239 = 6649859) B6649859
theorem B1090939 : Blo 968591 1090939 := bstep (se 1 (by rfl) ⟨818204, by rfl⟩ : syracuseStep 1090939 = 1636409) B1636409
theorem B3679627 : Blo 968591 3679627 := bstep (se 1 (by rfl) ⟨2759720, by rfl⟩ : syracuseStep 3679627 = 5519441) B5519441
theorem B10233479 : Blo 968591 10233479 := bstep (se 1 (by rfl) ⟨7675109, by rfl⟩ : syracuseStep 10233479 = 15350219) B15350219
theorem B3679901 : Blo 968591 3679901 := bstep (se 3 (by rfl) ⟨689981, by rfl⟩ : syracuseStep 3679901 = 1379963) B1379963
theorem B11347613 : Blo 968591 11347613 := bstep (se 3 (by rfl) ⟨2127677, by rfl⟩ : syracuseStep 11347613 = 4255355) B4255355
theorem B3679931 : Blo 968591 3679931 := bstep (se 1 (by rfl) ⟨2759948, by rfl⟩ : syracuseStep 3679931 = 5519897) B5519897
theorem B1091407 : Blo 968591 1091407 := bstep (se 1 (by rfl) ⟨818555, by rfl⟩ : syracuseStep 1091407 = 1637111) B1637111
theorem B19900241 : Blo 968591 19900241 := bstep (se 2 (by rfl) ⟨7462590, by rfl⟩ : syracuseStep 19900241 = 14925181) B14925181
theorem B37824407 : Blo 968591 37824407 := bstep (se 1 (by rfl) ⟨28368305, by rfl⟩ : syracuseStep 37824407 = 56736611) B56736611
theorem B4433953 : Blo 968591 4433953 := bstep (se 2 (by rfl) ⟨1662732, by rfl⟩ : syracuseStep 4433953 = 3325465) B3325465
theorem B2074729 : Blo 968591 2074729 := bstep (se 2 (by rfl) ⟨778023, by rfl⟩ : syracuseStep 2074729 = 1556047) B1556047
theorem B1091803 : Blo 968591 1091803 := bstep (se 1 (by rfl) ⟨818852, by rfl⟩ : syracuseStep 1091803 = 1637705) B1637705
theorem B1092091 : Blo 968591 1092091 := bstep (se 1 (by rfl) ⟨819068, by rfl⟩ : syracuseStep 1092091 = 1638137) B1638137
theorem B1092271 : Blo 968591 1092271 := bstep (se 1 (by rfl) ⟨819203, by rfl⟩ : syracuseStep 1092271 = 1638407) B1638407
theorem B4664087 : Blo 968591 4664087 := bstep (se 1 (by rfl) ⟨3498065, by rfl⟩ : syracuseStep 4664087 = 6996131) B6996131
theorem B35367815 : Blo 968591 35367815 := bstep (se 1 (by rfl) ⟨26525861, by rfl⟩ : syracuseStep 35367815 = 53051723) B53051723
theorem B12462983 : Blo 968591 12462983 := bstep (se 1 (by rfl) ⟨9347237, by rfl⟩ : syracuseStep 12462983 = 18694475) B18694475
theorem B1092559 : Blo 968591 1092559 := bstep (se 1 (by rfl) ⟨819419, by rfl⟩ : syracuseStep 1092559 = 1638839) B1638839
theorem B1453031 : Blo 968591 1453031 := bstep (se 1 (by rfl) ⟨1089773, by rfl⟩ : syracuseStep 1453031 = 2179547) B2179547
theorem B7384283 : Blo 968591 7384283 := bstep (se 1 (by rfl) ⟨5538212, by rfl⟩ : syracuseStep 7384283 = 11076425) B11076425
theorem B1453289 : Blo 968591 1453289 := bstep (se 2 (by rfl) ⟨544983, by rfl⟩ : syracuseStep 1453289 = 1089967) B1089967
theorem B4435211 : Blo 968591 4435211 := bstep (se 1 (by rfl) ⟨3326408, by rfl⟩ : syracuseStep 4435211 = 6652817) B6652817
theorem B1453343 : Blo 968591 1453343 := bstep (se 1 (by rfl) ⟨1090007, by rfl⟩ : syracuseStep 1453343 = 2180015) B2180015
theorem B1092955 : Blo 968591 1092955 := bstep (se 1 (by rfl) ⟨819716, by rfl⟩ : syracuseStep 1092955 = 1639433) B1639433
theorem B1453511 : Blo 968591 1453511 := bstep (se 1 (by rfl) ⟨1090133, by rfl⟩ : syracuseStep 1453511 = 2180267) B2180267
theorem B1093063 : Blo 968591 1093063 := bstep (se 1 (by rfl) ⟨819797, by rfl⟩ : syracuseStep 1093063 = 1639595) B1639595
theorem B3681875 : Blo 968591 3681875 := bstep (se 1 (by rfl) ⟨2761406, by rfl⟩ : syracuseStep 3681875 = 5522813) B5522813
theorem B4140659 : Blo 968591 4140659 := bstep (se 1 (by rfl) ⟨3105494, by rfl⟩ : syracuseStep 4140659 = 6210989) B6210989
theorem B4140811 : Blo 968591 4140811 := bstep (se 1 (by rfl) ⟨3105608, by rfl⟩ : syracuseStep 4140811 = 6211217) B6211217
theorem B1453865 : Blo 968591 1453865 := bstep (se 2 (by rfl) ⟨545199, by rfl⟩ : syracuseStep 1453865 = 1090399) B1090399
theorem B1453871 : Blo 968591 1453871 := bstep (se 1 (by rfl) ⟨1090403, by rfl⟩ : syracuseStep 1453871 = 2180807) B2180807
theorem B1093423 : Blo 968591 1093423 := bstep (se 1 (by rfl) ⟨820067, by rfl⟩ : syracuseStep 1093423 = 1640135) B1640135
theorem B3321757 : Blo 968591 3321757 := bstep (se 3 (by rfl) ⟨622829, by rfl⟩ : syracuseStep 3321757 = 1245659) B1245659
theorem B1093531 : Blo 968591 1093531 := bstep (se 1 (by rfl) ⟨820148, by rfl⟩ : syracuseStep 1093531 = 1640297) B1640297
theorem B4730899 : Blo 968591 4730899 := bstep (se 1 (by rfl) ⟨3548174, by rfl⟩ : syracuseStep 4730899 = 7096349) B7096349
theorem B1454345 : Blo 968591 1454345 := bstep (se 2 (by rfl) ⟨545379, by rfl⟩ : syracuseStep 1454345 = 1090759) B1090759
theorem B9318671 : Blo 968591 9318671 := bstep (se 1 (by rfl) ⟨6989003, by rfl⟩ : syracuseStep 9318671 = 13978007) B13978007
theorem B1093927 : Blo 968591 1093927 := bstep (se 1 (by rfl) ⟨820445, by rfl⟩ : syracuseStep 1093927 = 1640891) B1640891
theorem B1454447 : Blo 968591 1454447 := bstep (se 1 (by rfl) ⟨1090835, by rfl⟩ : syracuseStep 1454447 = 2181671) B2181671
theorem B1093999 : Blo 968591 1093999 := bstep (se 1 (by rfl) ⟨820499, by rfl⟩ : syracuseStep 1093999 = 1640999) B1640999
theorem B3682817 : Blo 968591 3682817 := bstep (se 2 (by rfl) ⟨1381056, by rfl⟩ : syracuseStep 3682817 = 2762113) B2762113
theorem B13972013 : Blo 968591 13972013 := bstep (se 3 (by rfl) ⟨2619752, by rfl⟩ : syracuseStep 13972013 = 5239505) B5239505
theorem B1454663 : Blo 968591 1454663 := bstep (se 1 (by rfl) ⟨1090997, by rfl⟩ : syracuseStep 1454663 = 2181995) B2181995
theorem B1454699 : Blo 968591 1454699 := bstep (se 1 (by rfl) ⟨1091024, by rfl⟩ : syracuseStep 1454699 = 2182049) B2182049
theorem B1454927 : Blo 968591 1454927 := bstep (se 1 (by rfl) ⟨1091195, by rfl⟩ : syracuseStep 1454927 = 2182391) B2182391
theorem B3683303 : Blo 968591 3683303 := bstep (se 1 (by rfl) ⟨2762477, by rfl⟩ : syracuseStep 3683303 = 5524955) B5524955
theorem B1455323 : Blo 968591 1455323 := bstep (se 1 (by rfl) ⟨1091492, by rfl⟩ : syracuseStep 1455323 = 2182985) B2182985
theorem B1226107 : Blo 968591 1226107 := bstep (se 1 (by rfl) ⟨919580, by rfl⟩ : syracuseStep 1226107 = 1839161) B1839161
theorem B1455497 : Blo 968591 1455497 := bstep (se 2 (by rfl) ⟨545811, by rfl⟩ : syracuseStep 1455497 = 1091623) B1091623
theorem B4142573 : Blo 968591 4142573 := bstep (se 3 (by rfl) ⟨776732, by rfl⟩ : syracuseStep 4142573 = 1553465) B1553465
theorem B1226335 : Blo 968591 1226335 := bstep (se 1 (by rfl) ⟨919751, by rfl⟩ : syracuseStep 1226335 = 1839503) B1839503
theorem B1455851 : Blo 968591 1455851 := bstep (se 1 (by rfl) ⟨1091888, by rfl⟩ : syracuseStep 1455851 = 2183777) B2183777
theorem B1456079 : Blo 968591 1456079 := bstep (se 1 (by rfl) ⟨1092059, by rfl⟩ : syracuseStep 1456079 = 2184119) B2184119
theorem B3684487 : Blo 968591 3684487 := bstep (se 1 (by rfl) ⟨2763365, by rfl⟩ : syracuseStep 3684487 = 5526731) B5526731
theorem B1456475 : Blo 968591 1456475 := bstep (se 1 (by rfl) ⟨1092356, by rfl⟩ : syracuseStep 1456475 = 2184713) B2184713
theorem B3684791 : Blo 968591 3684791 := bstep (se 1 (by rfl) ⟨2763593, by rfl⟩ : syracuseStep 3684791 = 5527187) B5527187
theorem B7092775 : Blo 968591 7092775 := bstep (se 1 (by rfl) ⟨5319581, by rfl⟩ : syracuseStep 7092775 = 10639163) B10639163
theorem B1456703 : Blo 968591 1456703 := bstep (se 1 (by rfl) ⟨1092527, by rfl⟩ : syracuseStep 1456703 = 2185055) B2185055
theorem B28031669 : Blo 968591 28031669 := bstep (se 5 (by rfl) ⟨1313984, by rfl⟩ : syracuseStep 28031669 = 2627969) B2627969
theorem B1456823 : Blo 968591 1456823 := bstep (se 1 (by rfl) ⟨1092617, by rfl⟩ : syracuseStep 1456823 = 2185235) B2185235
theorem B1227575 : Blo 968591 1227575 := bstep (se 1 (by rfl) ⟨920681, by rfl⟩ : syracuseStep 1227575 = 1841363) B1841363
theorem B35404613 : Blo 968591 35404613 := bstep (se 4 (by rfl) ⟨3319182, by rfl⟩ : syracuseStep 35404613 = 6638365) B6638365
theorem B1457051 : Blo 968591 1457051 := bstep (se 1 (by rfl) ⟨1092788, by rfl⟩ : syracuseStep 1457051 = 2185577) B2185577
theorem B1227727 : Blo 968591 1227727 := bstep (se 1 (by rfl) ⟨920795, by rfl⟩ : syracuseStep 1227727 = 1841591) B1841591
theorem B4209779 : Blo 968591 4209779 := bstep (se 1 (by rfl) ⟨3157334, by rfl⟩ : syracuseStep 4209779 = 6314669) B6314669
theorem B1752283 : Blo 968591 1752283 := bstep (se 1 (by rfl) ⟨1314212, by rfl⟩ : syracuseStep 1752283 = 2628425) B2628425
theorem B1457447 : Blo 968591 1457447 := bstep (se 1 (by rfl) ⟨1093085, by rfl⟩ : syracuseStep 1457447 = 2186171) B2186171
theorem B1457531 : Blo 968591 1457531 := bstep (se 1 (by rfl) ⟨1093148, by rfl⟩ : syracuseStep 1457531 = 2186297) B2186297
theorem B4144571 : Blo 968591 4144571 := bstep (se 1 (by rfl) ⟨3108428, by rfl⟩ : syracuseStep 4144571 = 6216857) B6216857
theorem B1457657 : Blo 968591 1457657 := bstep (se 2 (by rfl) ⟨546621, by rfl⟩ : syracuseStep 1457657 = 1093243) B1093243
theorem B1457759 : Blo 968591 1457759 := bstep (se 1 (by rfl) ⟨1093319, by rfl⟩ : syracuseStep 1457759 = 2186639) B2186639
theorem B1457975 : Blo 968591 1457975 := bstep (se 1 (by rfl) ⟨1093481, by rfl⟩ : syracuseStep 1457975 = 2186963) B2186963
theorem B1228699 : Blo 968591 1228699 := bstep (se 1 (by rfl) ⟨921524, by rfl⟩ : syracuseStep 1228699 = 1843049) B1843049
theorem B1458281 : Blo 968591 1458281 := bstep (se 2 (by rfl) ⟨546855, by rfl⟩ : syracuseStep 1458281 = 1093711) B1093711
theorem B2179439 : Blo 968591 2179439 := bstep (se 1 (by rfl) ⟨1634579, by rfl⟩ : syracuseStep 2179439 = 3269159) B3269159
theorem B1458599 : Blo 968591 1458599 := bstep (se 1 (by rfl) ⟨1093949, by rfl⟩ : syracuseStep 1458599 = 2187899) B2187899
theorem B2179511 : Blo 968591 2179511 := bstep (se 1 (by rfl) ⟨1634633, by rfl⟩ : syracuseStep 2179511 = 3269267) B3269267
theorem B1458683 : Blo 968591 1458683 := bstep (se 1 (by rfl) ⟨1094012, by rfl⟩ : syracuseStep 1458683 = 2188025) B2188025
theorem B2179655 : Blo 968591 2179655 := bstep (se 1 (by rfl) ⟨1634741, by rfl⟩ : syracuseStep 2179655 = 3269483) B3269483
theorem B7094855 : Blo 968591 7094855 := bstep (se 1 (by rfl) ⟨5321141, by rfl⟩ : syracuseStep 7094855 = 10642283) B10642283
theorem B2179691 : Blo 968591 2179691 := bstep (se 1 (by rfl) ⟨1634768, by rfl⟩ : syracuseStep 2179691 = 3269537) B3269537
theorem B1458809 : Blo 968591 1458809 := bstep (se 2 (by rfl) ⟨547053, by rfl⟩ : syracuseStep 1458809 = 1094107) B1094107
theorem B1458863 : Blo 968591 1458863 := bstep (se 1 (by rfl) ⟨1094147, by rfl⟩ : syracuseStep 1458863 = 2188295) B2188295
theorem B2180087 : Blo 968591 2180087 := bstep (se 1 (by rfl) ⟨1635065, by rfl⟩ : syracuseStep 2180087 = 3270131) B3270131
theorem B4670561 : Blo 968591 4670561 := bstep (se 2 (by rfl) ⟨1751460, by rfl⟩ : syracuseStep 4670561 = 3502921) B3502921
theorem B1164575 : Blo 968591 1164575 := bstep (se 1 (by rfl) ⟨873431, by rfl⟩ : syracuseStep 1164575 = 1746863) B1746863
theorem B2180447 : Blo 968591 2180447 := bstep (se 1 (by rfl) ⟨1635335, by rfl⟩ : syracuseStep 2180447 = 3270671) B3270671
theorem B4670909 : Blo 968591 4670909 := bstep (se 3 (by rfl) ⟨875795, by rfl⟩ : syracuseStep 4670909 = 1751591) B1751591
theorem B19908193 : Blo 968591 19908193 := bstep (se 2 (by rfl) ⟨7465572, by rfl⟩ : syracuseStep 19908193 = 14931145) B14931145
theorem B2180843 : Blo 968591 2180843 := bstep (se 1 (by rfl) ⟨1635632, by rfl⟩ : syracuseStep 2180843 = 3271265) B3271265
theorem B4147031 : Blo 968591 4147031 := bstep (se 1 (by rfl) ⟨3110273, by rfl⟩ : syracuseStep 4147031 = 6220547) B6220547
theorem B2180969 : Blo 968591 2180969 := bstep (se 2 (by rfl) ⟨817863, by rfl⟩ : syracuseStep 2180969 = 1635727) B1635727
theorem B6211475 : Blo 968591 6211475 := bstep (se 1 (by rfl) ⟨4658606, by rfl⟩ : syracuseStep 6211475 = 9317213) B9317213
theorem B968603 : Blo 968591 968603 := bstep (se 1 (by rfl) ⟨726452, by rfl⟩ : syracuseStep 968603 = 1452905) B1452905
theorem B968655 : Blo 968591 968655 := bstep (se 1 (by rfl) ⟨726491, by rfl⟩ : syracuseStep 968655 = 1452983) B1452983
theorem B968679 : Blo 968591 968679 := bstep (se 1 (by rfl) ⟨726509, by rfl⟩ : syracuseStep 968679 = 1453019) B1453019
theorem B968991 : Blo 968591 968991 := bstep (se 1 (by rfl) ⟨726743, by rfl⟩ : syracuseStep 968991 = 1453487) B1453487
theorem B969051 : Blo 968591 969051 := bstep (se 1 (by rfl) ⟨726788, by rfl⟩ : syracuseStep 969051 = 1453577) B1453577
theorem B969071 : Blo 968591 969071 := bstep (se 1 (by rfl) ⟨726803, by rfl⟩ : syracuseStep 969071 = 1453607) B1453607
theorem B969127 : Blo 968591 969127 := bstep (se 1 (by rfl) ⟨726845, by rfl⟩ : syracuseStep 969127 = 1453691) B1453691
theorem B9980371 : Blo 968591 9980371 := bstep (se 1 (by rfl) ⟨7485278, by rfl⟩ : syracuseStep 9980371 = 14970557) B14970557
theorem B969211 : Blo 968591 969211 := bstep (se 1 (by rfl) ⟨726908, by rfl⟩ : syracuseStep 969211 = 1453817) B1453817
theorem B969279 : Blo 968591 969279 := bstep (se 1 (by rfl) ⟨726959, by rfl⟩ : syracuseStep 969279 = 1453919) B1453919
theorem B969287 : Blo 968591 969287 := bstep (se 1 (by rfl) ⟨726965, by rfl⟩ : syracuseStep 969287 = 1453931) B1453931
theorem B3689135 : Blo 968591 3689135 := bstep (se 1 (by rfl) ⟨2766851, by rfl⟩ : syracuseStep 3689135 = 5533703) B5533703
theorem B2181815 : Blo 968591 2181815 := bstep (se 1 (by rfl) ⟨1636361, by rfl⟩ : syracuseStep 2181815 = 3272723) B3272723
theorem B8276701 : Blo 968591 8276701 := bstep (se 3 (by rfl) ⟨1551881, by rfl⟩ : syracuseStep 8276701 = 3103763) B3103763
theorem B969439 : Blo 968591 969439 := bstep (se 1 (by rfl) ⟨727079, by rfl⟩ : syracuseStep 969439 = 1454159) B1454159
theorem B969519 : Blo 968591 969519 := bstep (se 1 (by rfl) ⟨727139, by rfl⟩ : syracuseStep 969519 = 1454279) B1454279
theorem B2182031 : Blo 968591 2182031 := bstep (se 1 (by rfl) ⟨1636523, by rfl⟩ : syracuseStep 2182031 = 3273047) B3273047
theorem B969627 : Blo 968591 969627 := bstep (se 1 (by rfl) ⟨727220, by rfl⟩ : syracuseStep 969627 = 1454441) B1454441
theorem B969679 : Blo 968591 969679 := bstep (se 1 (by rfl) ⟨727259, by rfl⟩ : syracuseStep 969679 = 1454519) B1454519
theorem B969703 : Blo 968591 969703 := bstep (se 1 (by rfl) ⟨727277, by rfl⟩ : syracuseStep 969703 = 1454555) B1454555
theorem B970015 : Blo 968591 970015 := bstep (se 1 (by rfl) ⟨727511, by rfl⟩ : syracuseStep 970015 = 1455023) B1455023
theorem B970075 : Blo 968591 970075 := bstep (se 1 (by rfl) ⟨727556, by rfl⟩ : syracuseStep 970075 = 1455113) B1455113
theorem B970095 : Blo 968591 970095 := bstep (se 1 (by rfl) ⟨727571, by rfl⟩ : syracuseStep 970095 = 1455143) B1455143
theorem B970151 : Blo 968591 970151 := bstep (se 1 (by rfl) ⟨727613, by rfl⟩ : syracuseStep 970151 = 1455227) B1455227
theorem B970235 : Blo 968591 970235 := bstep (se 1 (by rfl) ⟨727676, by rfl⟩ : syracuseStep 970235 = 1455353) B1455353
theorem B970303 : Blo 968591 970303 := bstep (se 1 (by rfl) ⟨727727, by rfl⟩ : syracuseStep 970303 = 1455455) B1455455
theorem B970311 : Blo 968591 970311 := bstep (se 1 (by rfl) ⟨727733, by rfl⟩ : syracuseStep 970311 = 1455467) B1455467
theorem B2182751 : Blo 968591 2182751 := bstep (se 1 (by rfl) ⟨1637063, by rfl⟩ : syracuseStep 2182751 = 3274127) B3274127
theorem B4148945 : Blo 968591 4148945 := bstep (se 2 (by rfl) ⟨1555854, by rfl⟩ : syracuseStep 4148945 = 3111709) B3111709
theorem B970463 : Blo 968591 970463 := bstep (se 1 (by rfl) ⟨727847, by rfl⟩ : syracuseStep 970463 = 1455695) B1455695
theorem B19943185 : Blo 968591 19943185 := bstep (se 2 (by rfl) ⟨7478694, by rfl⟩ : syracuseStep 19943185 = 14957389) B14957389
theorem B970543 : Blo 968591 970543 := bstep (se 1 (by rfl) ⟨727907, by rfl⟩ : syracuseStep 970543 = 1455815) B1455815
theorem B2182967 : Blo 968591 2182967 := bstep (se 1 (by rfl) ⟨1637225, by rfl⟩ : syracuseStep 2182967 = 3274451) B3274451
theorem B970651 : Blo 968591 970651 := bstep (se 1 (by rfl) ⟨727988, by rfl⟩ : syracuseStep 970651 = 1455977) B1455977
theorem B970703 : Blo 968591 970703 := bstep (se 1 (by rfl) ⟨728027, by rfl⟩ : syracuseStep 970703 = 1456055) B1456055
theorem B970727 : Blo 968591 970727 := bstep (se 1 (by rfl) ⟨728045, by rfl⟩ : syracuseStep 970727 = 1456091) B1456091
theorem B2183273 : Blo 968591 2183273 := bstep (se 2 (by rfl) ⟨818727, by rfl⟩ : syracuseStep 2183273 = 1637455) B1637455
theorem B971039 : Blo 968591 971039 := bstep (se 1 (by rfl) ⟨728279, by rfl⟩ : syracuseStep 971039 = 1456559) B1456559
theorem B971099 : Blo 968591 971099 := bstep (se 1 (by rfl) ⟨728324, by rfl⟩ : syracuseStep 971099 = 1456649) B1456649
theorem B971119 : Blo 968591 971119 := bstep (se 1 (by rfl) ⟨728339, by rfl⟩ : syracuseStep 971119 = 1456679) B1456679
theorem B16568711 : Blo 968591 16568711 := bstep (se 1 (by rfl) ⟨12426533, by rfl⟩ : syracuseStep 16568711 = 24853067) B24853067
theorem B971175 : Blo 968591 971175 := bstep (se 1 (by rfl) ⟨728381, by rfl⟩ : syracuseStep 971175 = 1456763) B1456763
theorem B971259 : Blo 968591 971259 := bstep (se 1 (by rfl) ⟨728444, by rfl⟩ : syracuseStep 971259 = 1456889) B1456889
theorem B1659455 : Blo 968591 1659455 := bstep (se 1 (by rfl) ⟨1244591, by rfl⟩ : syracuseStep 1659455 = 2489183) B2489183
theorem B971327 : Blo 968591 971327 := bstep (se 1 (by rfl) ⟨728495, by rfl⟩ : syracuseStep 971327 = 1456991) B1456991
theorem B971335 : Blo 968591 971335 := bstep (se 1 (by rfl) ⟨728501, by rfl⟩ : syracuseStep 971335 = 1457003) B1457003
theorem B3691079 : Blo 968591 3691079 := bstep (se 1 (by rfl) ⟨2768309, by rfl⟩ : syracuseStep 3691079 = 5536619) B5536619
theorem B2183759 : Blo 968591 2183759 := bstep (se 1 (by rfl) ⟨1637819, by rfl⟩ : syracuseStep 2183759 = 3275639) B3275639
theorem B4903577 : Blo 968591 4903577 := bstep (se 2 (by rfl) ⟨1838841, by rfl⟩ : syracuseStep 4903577 = 3677683) B3677683
theorem B2183903 : Blo 968591 2183903 := bstep (se 1 (by rfl) ⟨1637927, by rfl⟩ : syracuseStep 2183903 = 3275855) B3275855
theorem B971487 : Blo 968591 971487 := bstep (se 1 (by rfl) ⟨728615, by rfl⟩ : syracuseStep 971487 = 1457231) B1457231
theorem B971567 : Blo 968591 971567 := bstep (se 1 (by rfl) ⟨728675, by rfl⟩ : syracuseStep 971567 = 1457351) B1457351
theorem B971675 : Blo 968591 971675 := bstep (se 1 (by rfl) ⟨728756, by rfl⟩ : syracuseStep 971675 = 1457513) B1457513
theorem B7000997 : Blo 968591 7000997 := bstep (se 4 (by rfl) ⟨656343, by rfl⟩ : syracuseStep 7000997 = 1312687) B1312687
theorem B2216875 : Blo 968591 2216875 := bstep (se 1 (by rfl) ⟨1662656, by rfl⟩ : syracuseStep 2216875 = 3325313) B3325313
theorem B971727 : Blo 968591 971727 := bstep (se 1 (by rfl) ⟨728795, by rfl⟩ : syracuseStep 971727 = 1457591) B1457591
theorem B2184155 : Blo 968591 2184155 := bstep (se 1 (by rfl) ⟨1638116, by rfl⟩ : syracuseStep 2184155 = 3276233) B3276233
theorem B971751 : Blo 968591 971751 := bstep (se 1 (by rfl) ⟨728813, by rfl⟩ : syracuseStep 971751 = 1457627) B1457627
theorem B2184335 : Blo 968591 2184335 := bstep (se 1 (by rfl) ⟨1638251, by rfl⟩ : syracuseStep 2184335 = 3276503) B3276503
theorem B2184425 : Blo 968591 2184425 := bstep (se 2 (by rfl) ⟨819159, by rfl⟩ : syracuseStep 2184425 = 1638319) B1638319
theorem B3691763 : Blo 968591 3691763 := bstep (se 1 (by rfl) ⟨2768822, by rfl⟩ : syracuseStep 3691763 = 5537645) B5537645
theorem B2184479 : Blo 968591 2184479 := bstep (se 1 (by rfl) ⟨1638359, by rfl⟩ : syracuseStep 2184479 = 3276719) B3276719
theorem B972063 : Blo 968591 972063 := bstep (se 1 (by rfl) ⟨729047, by rfl⟩ : syracuseStep 972063 = 1458095) B1458095
theorem B972123 : Blo 968591 972123 := bstep (se 1 (by rfl) ⟨729092, by rfl⟩ : syracuseStep 972123 = 1458185) B1458185
theorem B972143 : Blo 968591 972143 := bstep (se 1 (by rfl) ⟨729107, by rfl⟩ : syracuseStep 972143 = 1458215) B1458215
theorem B8279435 : Blo 968591 8279435 := bstep (se 1 (by rfl) ⟨6209576, by rfl⟩ : syracuseStep 8279435 = 12419153) B12419153
theorem B972199 : Blo 968591 972199 := bstep (se 1 (by rfl) ⟨729149, by rfl⟩ : syracuseStep 972199 = 1458299) B1458299
theorem B972283 : Blo 968591 972283 := bstep (se 1 (by rfl) ⟨729212, by rfl⟩ : syracuseStep 972283 = 1458425) B1458425
theorem B8181287 : Blo 968591 8181287 := bstep (se 1 (by rfl) ⟨6135965, by rfl⟩ : syracuseStep 8181287 = 12271931) B12271931
theorem B972351 : Blo 968591 972351 := bstep (se 1 (by rfl) ⟨729263, by rfl⟩ : syracuseStep 972351 = 1458527) B1458527
theorem B972359 : Blo 968591 972359 := bstep (se 1 (by rfl) ⟨729269, by rfl⟩ : syracuseStep 972359 = 1458539) B1458539
theorem B972511 : Blo 968591 972511 := bstep (se 1 (by rfl) ⟨729383, by rfl⟩ : syracuseStep 972511 = 1458767) B1458767
theorem B2185001 : Blo 968591 2185001 := bstep (se 2 (by rfl) ⟨819375, by rfl⟩ : syracuseStep 2185001 = 1638751) B1638751
theorem B972591 : Blo 968591 972591 := bstep (se 1 (by rfl) ⟨729443, by rfl⟩ : syracuseStep 972591 = 1458887) B1458887
theorem B4905359 : Blo 968591 4905359 := bstep (se 1 (by rfl) ⟨3679019, by rfl⟩ : syracuseStep 4905359 = 7358039) B7358039
theorem B39836087 : Blo 968591 39836087 := bstep (se 1 (by rfl) ⟨29877065, by rfl⟩ : syracuseStep 39836087 = 59754131) B59754131
theorem B2186063 : Blo 968591 2186063 := bstep (se 1 (by rfl) ⟨1639547, by rfl⟩ : syracuseStep 2186063 = 3279095) B3279095
theorem B14015375 : Blo 968591 14015375 := bstep (se 1 (by rfl) ⟨10511531, by rfl⟩ : syracuseStep 14015375 = 21023063) B21023063
theorem B8281075 : Blo 968591 8281075 := bstep (se 1 (by rfl) ⟨6210806, by rfl⟩ : syracuseStep 8281075 = 12421613) B12421613
theorem B2186279 : Blo 968591 2186279 := bstep (se 1 (by rfl) ⟨1639709, by rfl⟩ : syracuseStep 2186279 = 3279419) B3279419
theorem B2186459 : Blo 968591 2186459 := bstep (se 1 (by rfl) ⟨1639844, by rfl⟩ : syracuseStep 2186459 = 3279689) B3279689
theorem B2186657 : Blo 968591 2186657 := bstep (se 2 (by rfl) ⟨819996, by rfl⟩ : syracuseStep 2186657 = 1639993) B1639993
theorem B8412767 : Blo 968591 8412767 := bstep (se 1 (by rfl) ⟨6309575, by rfl⟩ : syracuseStep 8412767 = 12619151) B12619151
theorem B2187215 : Blo 968591 2187215 := bstep (se 1 (by rfl) ⟨1640411, by rfl⟩ : syracuseStep 2187215 = 3280823) B3280823
theorem B2187593 : Blo 968591 2187593 := bstep (se 2 (by rfl) ⟨820347, by rfl⟩ : syracuseStep 2187593 = 1640695) B1640695
theorem B2187611 : Blo 968591 2187611 := bstep (se 1 (by rfl) ⟨1640708, by rfl⟩ : syracuseStep 2187611 = 3281417) B3281417
theorem B4907465 : Blo 968591 4907465 := bstep (se 2 (by rfl) ⟨1840299, by rfl⟩ : syracuseStep 4907465 = 3680599) B3680599
theorem B1663559 : Blo 968591 1663559 := bstep (se 1 (by rfl) ⟨1247669, by rfl⟩ : syracuseStep 1663559 = 2495339) B2495339
theorem B4154003 : Blo 968591 4154003 := bstep (se 1 (by rfl) ⟨3115502, by rfl⟩ : syracuseStep 4154003 = 6231005) B6231005
theorem B4154105 : Blo 968591 4154105 := bstep (se 2 (by rfl) ⟨1557789, by rfl⟩ : syracuseStep 4154105 = 3115579) B3115579
theorem B2188187 : Blo 968591 2188187 := bstep (se 1 (by rfl) ⟨1641140, by rfl⟩ : syracuseStep 2188187 = 3282281) B3282281
theorem B3105917 : Blo 968591 3105917 := bstep (se 3 (by rfl) ⟨582359, by rfl⟩ : syracuseStep 3105917 = 1164719) B1164719
theorem B4908275 : Blo 968591 4908275 := bstep (se 1 (by rfl) ⟨3681206, by rfl⟩ : syracuseStep 4908275 = 7362413) B7362413
theorem B3270077 : Blo 968591 3270077 := bstep (se 3 (by rfl) ⟨613139, by rfl⟩ : syracuseStep 3270077 = 1226279) B1226279
theorem B3499577 : Blo 968591 3499577 := bstep (se 2 (by rfl) ⟨1312341, by rfl⟩ : syracuseStep 3499577 = 2624683) B2624683
theorem B7366301 : Blo 968591 7366301 := bstep (se 3 (by rfl) ⟨1381181, by rfl⟩ : syracuseStep 7366301 = 2762363) B2762363
theorem B3270455 : Blo 968591 3270455 := bstep (se 1 (by rfl) ⟨2452841, by rfl⟩ : syracuseStep 3270455 = 4905683) B4905683
theorem B3270941 : Blo 968591 3270941 := bstep (se 3 (by rfl) ⟨613301, by rfl⟩ : syracuseStep 3270941 = 1226603) B1226603
theorem B2452619 : Blo 968591 2452619 := bstep (se 1 (by rfl) ⟨1839464, by rfl⟩ : syracuseStep 2452619 = 3678929) B3678929
theorem B4910219 : Blo 968591 4910219 := bstep (se 1 (by rfl) ⟨3682664, by rfl⟩ : syracuseStep 4910219 = 7365329) B7365329
theorem B3271967 : Blo 968591 3271967 := bstep (se 1 (by rfl) ⟨2453975, by rfl⟩ : syracuseStep 3271967 = 4907951) B4907951
theorem B2453075 : Blo 968591 2453075 := bstep (se 1 (by rfl) ⟨1839806, by rfl⟩ : syracuseStep 2453075 = 3679613) B3679613
theorem B5238685 : Blo 968591 5238685 := bstep (se 3 (by rfl) ⟨982253, by rfl⟩ : syracuseStep 5238685 = 1964507) B1964507
theorem B3108889 : Blo 968591 3108889 := bstep (se 2 (by rfl) ⟨1165833, by rfl⟩ : syracuseStep 3108889 = 2331667) B2331667
theorem B2453935 : Blo 968591 2453935 := bstep (se 1 (by rfl) ⟨1840451, by rfl⟩ : syracuseStep 2453935 = 3680903) B3680903
theorem B11072051 : Blo 968591 11072051 := bstep (se 1 (by rfl) ⟨8304038, by rfl⟩ : syracuseStep 11072051 = 16608077) B16608077
theorem B1995337 : Blo 968591 1995337 := bstep (se 2 (by rfl) ⟨748251, by rfl⟩ : syracuseStep 1995337 = 1496503) B1496503
theorem B2454239 : Blo 968591 2454239 := bstep (se 1 (by rfl) ⟨1840679, by rfl⟩ : syracuseStep 2454239 = 3681359) B3681359
theorem B4911839 : Blo 968591 4911839 := bstep (se 1 (by rfl) ⟨3683879, by rfl⟩ : syracuseStep 4911839 = 7367759) B7367759
theorem B6222905 : Blo 968591 6222905 := bstep (se 2 (by rfl) ⟨2333589, by rfl⟩ : syracuseStep 6222905 = 4667179) B4667179
theorem B1635707 : Blo 968591 1635707 := bstep (se 1 (by rfl) ⟨1226780, by rfl⟩ : syracuseStep 1635707 = 2453561) B2453561
theorem B2454907 : Blo 968591 2454907 := bstep (se 1 (by rfl) ⟨1841180, by rfl⟩ : syracuseStep 2454907 = 3682361) B3682361
theorem B3274397 : Blo 968591 3274397 := bstep (se 3 (by rfl) ⟨613949, by rfl⟩ : syracuseStep 3274397 = 1227899) B1227899
theorem B2455343 : Blo 968591 2455343 := bstep (se 1 (by rfl) ⟨1841507, by rfl⟩ : syracuseStep 2455343 = 3683015) B3683015
theorem B11073509 : Blo 968591 11073509 := bstep (se 4 (by rfl) ⟨1038141, by rfl⟩ : syracuseStep 11073509 = 2076283) B2076283
theorem B3274937 : Blo 968591 3274937 := bstep (se 2 (by rfl) ⟨1228101, by rfl⟩ : syracuseStep 3274937 = 2456203) B2456203
theorem B1636699 : Blo 968591 1636699 := bstep (se 1 (by rfl) ⟨1227524, by rfl⟩ : syracuseStep 1636699 = 2455049) B2455049
theorem B2455991 : Blo 968591 2455991 := bstep (se 1 (by rfl) ⟨1841993, by rfl⟩ : syracuseStep 2455991 = 3683987) B3683987
theorem B3111851 : Blo 968591 3111851 := bstep (se 1 (by rfl) ⟨2333888, by rfl⟩ : syracuseStep 3111851 = 4667777) B4667777
theorem B8879033 : Blo 968591 8879033 := bstep (se 2 (by rfl) ⟨3329637, by rfl⟩ : syracuseStep 8879033 = 6659275) B6659275
theorem B4914107 : Blo 968591 4914107 := bstep (se 1 (by rfl) ⟨3685580, by rfl⟩ : syracuseStep 4914107 = 7371161) B7371161
theorem B2620403 : Blo 968591 2620403 := bstep (se 1 (by rfl) ⟨1965302, by rfl⟩ : syracuseStep 2620403 = 3930605) B3930605
theorem B9960677 : Blo 968591 9960677 := bstep (se 4 (by rfl) ⟨933813, by rfl⟩ : syracuseStep 9960677 = 1867627) B1867627
theorem B1637671 : Blo 968591 1637671 := bstep (se 1 (by rfl) ⟨1228253, by rfl⟩ : syracuseStep 1637671 = 2456507) B2456507
theorem B2456993 : Blo 968591 2456993 := bstep (se 2 (by rfl) ⟨921372, by rfl⟩ : syracuseStep 2456993 = 1842745) B1842745
theorem B3276449 : Blo 968591 3276449 := bstep (se 2 (by rfl) ⟨1228668, by rfl⟩ : syracuseStep 3276449 = 2457337) B2457337
theorem B6225569 : Blo 968591 6225569 := bstep (se 2 (by rfl) ⟨2334588, by rfl⟩ : syracuseStep 6225569 = 4669177) B4669177
theorem B1638191 : Blo 968591 1638191 := bstep (se 1 (by rfl) ⟨1228643, by rfl⟩ : syracuseStep 1638191 = 2457287) B2457287
theorem B2457449 : Blo 968591 2457449 := bstep (se 2 (by rfl) ⟨921543, by rfl⟩ : syracuseStep 2457449 = 1843087) B1843087
theorem B3276935 : Blo 968591 3276935 := bstep (se 1 (by rfl) ⟨2457701, by rfl⟩ : syracuseStep 3276935 = 4915403) B4915403
theorem B1966535 : Blo 968591 1966535 := bstep (se 1 (by rfl) ⟨1474901, by rfl⟩ : syracuseStep 1966535 = 2949803) B2949803
theorem B2327305 : Blo 968591 2327305 := bstep (se 2 (by rfl) ⟨872739, by rfl⟩ : syracuseStep 2327305 = 1745479) B1745479
theorem B3113939 : Blo 968591 3113939 := bstep (se 1 (by rfl) ⟨2335454, by rfl⟩ : syracuseStep 3113939 = 4670909) B4670909
theorem B1639487 : Blo 968591 1639487 := bstep (se 1 (by rfl) ⟨1229615, by rfl⟩ : syracuseStep 1639487 = 2459231) B2459231
theorem B12584135 : Blo 968591 12584135 := bstep (se 1 (by rfl) ⟨9438101, by rfl⟩ : syracuseStep 12584135 = 18876203) B18876203
theorem B35357897 : Blo 968591 35357897 := bstep (se 2 (by rfl) ⟨13259211, by rfl⟩ : syracuseStep 35357897 = 26518423) B26518423
theorem B3278447 : Blo 968591 3278447 := bstep (se 1 (by rfl) ⟨2458835, by rfl⟩ : syracuseStep 3278447 = 4917671) B4917671
theorem B1640047 : Blo 968591 1640047 := bstep (se 1 (by rfl) ⟨1230035, by rfl⟩ : syracuseStep 1640047 = 2460071) B2460071
theorem B3278555 : Blo 968591 3278555 := bstep (se 1 (by rfl) ⟨2458916, by rfl⟩ : syracuseStep 3278555 = 4917833) B4917833
theorem B1640155 : Blo 968591 1640155 := bstep (se 1 (by rfl) ⟨1230116, by rfl⟩ : syracuseStep 1640155 = 2460233) B2460233
theorem B2459423 : Blo 968591 2459423 := bstep (se 1 (by rfl) ⟨1844567, by rfl⟩ : syracuseStep 2459423 = 3689135) B3689135
theorem B23594813 : Blo 968591 23594813 := bstep (se 3 (by rfl) ⟨4424027, by rfl⟩ : syracuseStep 23594813 = 8848055) B8848055
theorem B26544257 : Blo 968591 26544257 := bstep (se 2 (by rfl) ⟨9954096, by rfl⟩ : syracuseStep 26544257 = 19908193) B19908193
theorem B4655339 : Blo 968591 4655339 := bstep (se 1 (by rfl) ⟨3491504, by rfl⟩ : syracuseStep 4655339 = 6983009) B6983009
theorem B14158091 : Blo 968591 14158091 := bstep (se 1 (by rfl) ⟨10618568, by rfl⟩ : syracuseStep 14158091 = 21237137) B21237137
theorem B3935063 : Blo 968591 3935063 := bstep (se 1 (by rfl) ⟨2951297, by rfl⟩ : syracuseStep 3935063 = 5902595) B5902595
theorem B12454829 : Blo 968591 12454829 := bstep (se 3 (by rfl) ⟨2335280, by rfl⟩ : syracuseStep 12454829 = 4670561) B4670561
theorem B11045807 : Blo 968591 11045807 := bstep (se 1 (by rfl) ⟨8284355, by rfl⟩ : syracuseStep 11045807 = 16568711) B16568711
theorem B70978517 : Blo 968591 70978517 := bstep (se 7 (by rfl) ⟨831779, by rfl⟩ : syracuseStep 70978517 = 1663559) B1663559
theorem B3279851 : Blo 968591 3279851 := bstep (se 1 (by rfl) ⟨2459888, by rfl⟩ : syracuseStep 3279851 = 4919777) B4919777
theorem B3279905 : Blo 968591 3279905 := bstep (se 2 (by rfl) ⟨1229964, by rfl⟩ : syracuseStep 3279905 = 2459929) B2459929
theorem B2460719 : Blo 968591 2460719 := bstep (se 1 (by rfl) ⟨1845539, by rfl⟩ : syracuseStep 2460719 = 3691079) B3691079
theorem B13307161 : Blo 968591 13307161 := bstep (se 2 (by rfl) ⟨4990185, by rfl⟩ : syracuseStep 13307161 = 9980371) B9980371
theorem B2461175 : Blo 968591 2461175 := bstep (se 1 (by rfl) ⟨1845881, by rfl⟩ : syracuseStep 2461175 = 3691763) B3691763
theorem B5901817 : Blo 968591 5901817 := bstep (se 2 (by rfl) ⟨2213181, by rfl⟩ : syracuseStep 5901817 = 4426363) B4426363
theorem B1969939 : Blo 968591 1969939 := bstep (se 1 (by rfl) ⟨1477454, by rfl⟩ : syracuseStep 1969939 = 2954909) B2954909
theorem B28315919 : Blo 968591 28315919 := bstep (se 1 (by rfl) ⟨21236939, by rfl⟩ : syracuseStep 28315919 = 42473879) B42473879
theorem B3281363 : Blo 968591 3281363 := bstep (se 1 (by rfl) ⟨2461022, by rfl⟩ : syracuseStep 3281363 = 4922045) B4922045
theorem B9343583 : Blo 968591 9343583 := bstep (se 1 (by rfl) ⟨7007687, by rfl⟩ : syracuseStep 9343583 = 14015375) B14015375
theorem B3937319 : Blo 968591 3937319 := bstep (se 1 (by rfl) ⟨2952989, by rfl⟩ : syracuseStep 3937319 = 5905979) B5905979
theorem B5608511 : Blo 968591 5608511 := bstep (se 1 (by rfl) ⟨4206383, by rfl⟩ : syracuseStep 5608511 = 8412767) B8412767
theorem B6984913 : Blo 968591 6984913 := bstep (se 2 (by rfl) ⟨2619342, by rfl⟩ : syracuseStep 6984913 = 5238685) B5238685
theorem B4429009 : Blo 968591 4429009 := bstep (se 2 (by rfl) ⟨1660878, by rfl⟩ : syracuseStep 4429009 = 3321757) B3321757
theorem B2626835 : Blo 968591 2626835 := bstep (se 1 (by rfl) ⟨1970126, by rfl⟩ : syracuseStep 2626835 = 3940253) B3940253
theorem B1840475 : Blo 968591 1840475 := bstep (se 1 (by rfl) ⟨1380356, by rfl⟩ : syracuseStep 1840475 = 2760713) B2760713
theorem B2070611 : Blo 968591 2070611 := bstep (se 1 (by rfl) ⟨1552958, by rfl⟩ : syracuseStep 2070611 = 3105917) B3105917
theorem B2660449 : Blo 968591 2660449 := bstep (se 2 (by rfl) ⟨997668, by rfl⟩ : syracuseStep 2660449 = 1995337) B1995337
theorem B2758799 : Blo 968591 2758799 := bstep (se 1 (by rfl) ⟨2069099, by rfl⟩ : syracuseStep 2758799 = 4138199) B4138199
theorem B2758855 : Blo 968591 2758855 := bstep (se 1 (by rfl) ⟨2069141, by rfl⟩ : syracuseStep 2758855 = 4138283) B4138283
theorem B2333051 : Blo 968591 2333051 := bstep (se 1 (by rfl) ⟨1749788, by rfl⟩ : syracuseStep 2333051 = 3499577) B3499577
theorem B6822319 : Blo 968591 6822319 := bstep (se 1 (by rfl) ⟨5116739, by rfl⟩ : syracuseStep 6822319 = 10233479) B10233479
theorem B2955833 : Blo 968591 2955833 := bstep (se 2 (by rfl) ⟨1108437, by rfl⟩ : syracuseStep 2955833 = 2216875) B2216875
theorem B6298249 : Blo 968591 6298249 := bstep (se 2 (by rfl) ⟨2361843, by rfl⟩ : syracuseStep 6298249 = 4723687) B4723687
theorem B13999229 : Blo 968591 13999229 := bstep (se 3 (by rfl) ⟨2624855, by rfl⟩ : syracuseStep 13999229 = 5249711) B5249711
theorem B4922855 : Blo 968591 4922855 := bstep (se 1 (by rfl) ⟨3692141, by rfl⟩ : syracuseStep 4922855 = 7384283) B7384283
theorem B2956807 : Blo 968591 2956807 := bstep (se 1 (by rfl) ⟨2217605, by rfl⟩ : syracuseStep 2956807 = 4435211) B4435211
theorem B2760439 : Blo 968591 2760439 := bstep (se 1 (by rfl) ⟨2070329, by rfl⟩ : syracuseStep 2760439 = 4140659) B4140659
theorem B9314675 : Blo 968591 9314675 := bstep (se 1 (by rfl) ⟨6986006, by rfl⟩ : syracuseStep 9314675 = 13972013) B13972013
theorem B7381367 : Blo 968591 7381367 := bstep (se 1 (by rfl) ⟨5536025, by rfl⟩ : syracuseStep 7381367 = 11072051) B11072051
theorem B7873337 : Blo 968591 7873337 := bstep (se 2 (by rfl) ⟨2952501, by rfl⟩ : syracuseStep 7873337 = 5905003) B5905003
theorem B1090471 : Blo 968591 1090471 := bstep (se 1 (by rfl) ⟨817853, by rfl⟩ : syracuseStep 1090471 = 1635707) B1635707
theorem B2761715 : Blo 968591 2761715 := bstep (se 1 (by rfl) ⟨2071286, by rfl⟩ : syracuseStep 2761715 = 4142573) B4142573
theorem B7382339 : Blo 968591 7382339 := bstep (se 1 (by rfl) ⟨5536754, by rfl⟩ : syracuseStep 7382339 = 11073509) B11073509
theorem B2336377 : Blo 968591 2336377 := bstep (se 2 (by rfl) ⟨876141, by rfl⟩ : syracuseStep 2336377 = 1752283) B1752283
theorem B18687779 : Blo 968591 18687779 := bstep (se 1 (by rfl) ⟨14015834, by rfl⟩ : syracuseStep 18687779 = 28031669) B28031669
theorem B23603075 : Blo 968591 23603075 := bstep (se 1 (by rfl) ⟨17702306, by rfl⟩ : syracuseStep 23603075 = 35404613) B35404613
theorem B2074567 : Blo 968591 2074567 := bstep (se 1 (by rfl) ⟨1555925, by rfl⟩ : syracuseStep 2074567 = 3111851) B3111851
theorem B1746935 : Blo 968591 1746935 := bstep (se 1 (by rfl) ⟨1310201, by rfl⟩ : syracuseStep 1746935 = 2620403) B2620403
theorem B4991129 : Blo 968591 4991129 := bstep (se 2 (by rfl) ⟨1871673, by rfl⟩ : syracuseStep 4991129 = 3743347) B3743347
theorem B2763001 : Blo 968591 2763001 := bstep (se 2 (by rfl) ⟨1036125, by rfl⟩ : syracuseStep 2763001 = 2072251) B2072251
theorem B2763047 : Blo 968591 2763047 := bstep (se 1 (by rfl) ⟨2072285, by rfl⟩ : syracuseStep 2763047 = 4144571) B4144571
theorem B1092127 : Blo 968591 1092127 := bstep (se 1 (by rfl) ⟨819095, by rfl⟩ : syracuseStep 1092127 = 1638191) B1638191
theorem B1452959 : Blo 968591 1452959 := bstep (se 1 (by rfl) ⟨1089719, by rfl⟩ : syracuseStep 1452959 = 2179439) B2179439
theorem B1453007 : Blo 968591 1453007 := bstep (se 1 (by rfl) ⟨1089755, by rfl⟩ : syracuseStep 1453007 = 2179511) B2179511
theorem B1747937 : Blo 968591 1747937 := bstep (se 2 (by rfl) ⟨655476, by rfl⟩ : syracuseStep 1747937 = 1310953) B1310953
theorem B1453097 : Blo 968591 1453097 := bstep (se 2 (by rfl) ⟨544911, by rfl⟩ : syracuseStep 1453097 = 1089823) B1089823
theorem B1453103 : Blo 968591 1453103 := bstep (se 1 (by rfl) ⟨1089827, by rfl⟩ : syracuseStep 1453103 = 2179655) B2179655
theorem B4729903 : Blo 968591 4729903 := bstep (se 1 (by rfl) ⟨3547427, by rfl⟩ : syracuseStep 4729903 = 7094855) B7094855
theorem B1453127 : Blo 968591 1453127 := bstep (se 1 (by rfl) ⟨1089845, by rfl⟩ : syracuseStep 1453127 = 2179691) B2179691
theorem B1453391 : Blo 968591 1453391 := bstep (se 1 (by rfl) ⟨1090043, by rfl⟩ : syracuseStep 1453391 = 2180087) B2180087
theorem B1453481 : Blo 968591 1453481 := bstep (se 2 (by rfl) ⟨545055, by rfl⟩ : syracuseStep 1453481 = 1090111) B1090111
theorem B11054555 : Blo 968591 11054555 := bstep (se 1 (by rfl) ⟨8290916, by rfl⟩ : syracuseStep 11054555 = 16581833) B16581833
theorem B1453631 : Blo 968591 1453631 := bstep (se 1 (by rfl) ⟨1090223, by rfl⟩ : syracuseStep 1453631 = 2180447) B2180447
theorem B2076455 : Blo 968591 2076455 := bstep (se 1 (by rfl) ⟨1557341, by rfl⟩ : syracuseStep 2076455 = 3114683) B3114683
theorem B1453895 : Blo 968591 1453895 := bstep (se 1 (by rfl) ⟨1090421, by rfl⟩ : syracuseStep 1453895 = 2180843) B2180843
theorem B2764687 : Blo 968591 2764687 := bstep (se 1 (by rfl) ⟨2073515, by rfl⟩ : syracuseStep 2764687 = 4147031) B4147031
theorem B1453979 : Blo 968591 1453979 := bstep (se 1 (by rfl) ⟨1090484, by rfl⟩ : syracuseStep 1453979 = 2180969) B2180969
theorem B6991771 : Blo 968591 6991771 := bstep (se 1 (by rfl) ⟨5243828, by rfl⟩ : syracuseStep 6991771 = 10487657) B10487657
theorem B4140983 : Blo 968591 4140983 := bstep (se 1 (by rfl) ⟨3105737, by rfl⟩ : syracuseStep 4140983 = 6211475) B6211475
theorem B1749385 : Blo 968591 1749385 := bstep (se 2 (by rfl) ⟨656019, by rfl⟩ : syracuseStep 1749385 = 1312039) B1312039
theorem B5910985 : Blo 968591 5910985 := bstep (se 2 (by rfl) ⟨2216619, by rfl⟩ : syracuseStep 5910985 = 4433239) B4433239
theorem B1454543 : Blo 968591 1454543 := bstep (se 1 (by rfl) ⟨1090907, by rfl⟩ : syracuseStep 1454543 = 2181815) B2181815
theorem B1454585 : Blo 968591 1454585 := bstep (se 2 (by rfl) ⟨545469, by rfl⟩ : syracuseStep 1454585 = 1090939) B1090939
theorem B1454687 : Blo 968591 1454687 := bstep (se 1 (by rfl) ⟨1091015, by rfl⟩ : syracuseStep 1454687 = 2182031) B2182031
theorem B1455167 : Blo 968591 1455167 := bstep (se 1 (by rfl) ⟨1091375, by rfl⟩ : syracuseStep 1455167 = 2182751) B2182751
theorem B1455209 : Blo 968591 1455209 := bstep (se 2 (by rfl) ⟨545703, by rfl⟩ : syracuseStep 1455209 = 1091407) B1091407
theorem B2765963 : Blo 968591 2765963 := bstep (se 1 (by rfl) ⟨2074472, by rfl⟩ : syracuseStep 2765963 = 4148945) B4148945
theorem B1455311 : Blo 968591 1455311 := bstep (se 1 (by rfl) ⟨1091483, by rfl⟩ : syracuseStep 1455311 = 2182967) B2182967
theorem B2798945 : Blo 968591 2798945 := bstep (se 2 (by rfl) ⟨1049604, by rfl⟩ : syracuseStep 2798945 = 2099209) B2099209
theorem B5911937 : Blo 968591 5911937 := bstep (se 2 (by rfl) ⟨2216976, by rfl⟩ : syracuseStep 5911937 = 4433953) B4433953
theorem B1455515 : Blo 968591 1455515 := bstep (se 1 (by rfl) ⟨1091636, by rfl⟩ : syracuseStep 1455515 = 2183273) B2183273
theorem B14005685 : Blo 968591 14005685 := bstep (se 5 (by rfl) ⟨656516, by rfl⟩ : syracuseStep 14005685 = 1313033) B1313033
theorem B2766305 : Blo 968591 2766305 := bstep (se 2 (by rfl) ⟨1037364, by rfl⟩ : syracuseStep 2766305 = 2074729) B2074729
theorem B1455737 : Blo 968591 1455737 := bstep (se 2 (by rfl) ⟨545901, by rfl⟩ : syracuseStep 1455737 = 1091803) B1091803
theorem B1455839 : Blo 968591 1455839 := bstep (se 1 (by rfl) ⟨1091879, by rfl⟩ : syracuseStep 1455839 = 2183759) B2183759
theorem B1455935 : Blo 968591 1455935 := bstep (se 1 (by rfl) ⟨1091951, by rfl⟩ : syracuseStep 1455935 = 2183903) B2183903
theorem B1554407 : Blo 968591 1554407 := bstep (se 1 (by rfl) ⟨1165805, by rfl⟩ : syracuseStep 1554407 = 2331611) B2331611
theorem B1456103 : Blo 968591 1456103 := bstep (se 1 (by rfl) ⟨1092077, by rfl⟩ : syracuseStep 1456103 = 2184155) B2184155
theorem B1456121 : Blo 968591 1456121 := bstep (se 2 (by rfl) ⟨546045, by rfl⟩ : syracuseStep 1456121 = 1092091) B1092091
theorem B1456223 : Blo 968591 1456223 := bstep (se 1 (by rfl) ⟨1092167, by rfl⟩ : syracuseStep 1456223 = 2184335) B2184335
theorem B1456283 : Blo 968591 1456283 := bstep (se 1 (by rfl) ⟨1092212, by rfl⟩ : syracuseStep 1456283 = 2184425) B2184425
theorem B1456319 : Blo 968591 1456319 := bstep (se 1 (by rfl) ⟨1092239, by rfl⟩ : syracuseStep 1456319 = 2184479) B2184479
theorem B1456361 : Blo 968591 1456361 := bstep (se 2 (by rfl) ⟨546135, by rfl⟩ : syracuseStep 1456361 = 1092271) B1092271
theorem B5519623 : Blo 968591 5519623 := bstep (se 1 (by rfl) ⟨4139717, by rfl⟩ : syracuseStep 5519623 = 8279435) B8279435
theorem B1554727 : Blo 968591 1554727 := bstep (se 1 (by rfl) ⟨1166045, by rfl⟩ : syracuseStep 1554727 = 2332091) B2332091
theorem B5454191 : Blo 968591 5454191 := bstep (se 1 (by rfl) ⟨4090643, by rfl⟩ : syracuseStep 5454191 = 8181287) B8181287
theorem B1456667 : Blo 968591 1456667 := bstep (se 1 (by rfl) ⟨1092500, by rfl⟩ : syracuseStep 1456667 = 2185001) B2185001
theorem B1456745 : Blo 968591 1456745 := bstep (se 2 (by rfl) ⟨546279, by rfl⟩ : syracuseStep 1456745 = 1092559) B1092559
theorem B11188853 : Blo 968591 11188853 := bstep (se 5 (by rfl) ⟨524477, by rfl⟩ : syracuseStep 11188853 = 1048955) B1048955
theorem B1555291 : Blo 968591 1555291 := bstep (se 1 (by rfl) ⟨1166468, by rfl⟩ : syracuseStep 1555291 = 2332937) B2332937
theorem B26557391 : Blo 968591 26557391 := bstep (se 1 (by rfl) ⟨19918043, by rfl⟩ : syracuseStep 26557391 = 39836087) B39836087
theorem B1457273 : Blo 968591 1457273 := bstep (se 2 (by rfl) ⟨546477, by rfl⟩ : syracuseStep 1457273 = 1092955) B1092955
theorem B1457375 : Blo 968591 1457375 := bstep (se 1 (by rfl) ⟨1093031, by rfl⟩ : syracuseStep 1457375 = 2186063) B2186063
theorem B1457417 : Blo 968591 1457417 := bstep (se 2 (by rfl) ⟨546531, by rfl⟩ : syracuseStep 1457417 = 1093063) B1093063
theorem B1555823 : Blo 968591 1555823 := bstep (se 1 (by rfl) ⟨1166867, by rfl⟩ : syracuseStep 1555823 = 2333735) B2333735
theorem B1457519 : Blo 968591 1457519 := bstep (se 1 (by rfl) ⟨1093139, by rfl⟩ : syracuseStep 1457519 = 2186279) B2186279
theorem B1457639 : Blo 968591 1457639 := bstep (se 1 (by rfl) ⟨1093229, by rfl⟩ : syracuseStep 1457639 = 2186459) B2186459
theorem B4734445 : Blo 968591 4734445 := bstep (se 3 (by rfl) ⟨887708, by rfl⟩ : syracuseStep 4734445 = 1775417) B1775417
theorem B1457771 : Blo 968591 1457771 := bstep (se 1 (by rfl) ⟨1093328, by rfl⟩ : syracuseStep 1457771 = 2186657) B2186657
theorem B1556111 : Blo 968591 1556111 := bstep (se 1 (by rfl) ⟨1167083, by rfl⟩ : syracuseStep 1556111 = 2334167) B2334167
theorem B5521081 : Blo 968591 5521081 := bstep (se 2 (by rfl) ⟨2070405, by rfl⟩ : syracuseStep 5521081 = 4140811) B4140811
theorem B26590913 : Blo 968591 26590913 := bstep (se 2 (by rfl) ⟨9971592, by rfl⟩ : syracuseStep 26590913 = 19943185) B19943185
theorem B1457897 : Blo 968591 1457897 := bstep (se 2 (by rfl) ⟨546711, by rfl⟩ : syracuseStep 1457897 = 1093423) B1093423
theorem B1458041 : Blo 968591 1458041 := bstep (se 2 (by rfl) ⟨546765, by rfl⟩ : syracuseStep 1458041 = 1093531) B1093531
theorem B1458143 : Blo 968591 1458143 := bstep (se 1 (by rfl) ⟨1093607, by rfl⟩ : syracuseStep 1458143 = 2187215) B2187215
theorem B6307865 : Blo 968591 6307865 := bstep (se 2 (by rfl) ⟨2365449, by rfl⟩ : syracuseStep 6307865 = 4730899) B4730899
theorem B4145185 : Blo 968591 4145185 := bstep (se 2 (by rfl) ⟨1554444, by rfl⟩ : syracuseStep 4145185 = 3108889) B3108889
theorem B3784843 : Blo 968591 3784843 := bstep (se 1 (by rfl) ⟨2838632, by rfl⟩ : syracuseStep 3784843 = 5677265) B5677265
theorem B1458395 : Blo 968591 1458395 := bstep (se 1 (by rfl) ⟨1093796, by rfl⟩ : syracuseStep 1458395 = 2187593) B2187593
theorem B1458407 : Blo 968591 1458407 := bstep (se 1 (by rfl) ⟨1093805, by rfl⟩ : syracuseStep 1458407 = 2187611) B2187611
theorem B1458569 : Blo 968591 1458569 := bstep (se 2 (by rfl) ⟨546963, by rfl⟩ : syracuseStep 1458569 = 1093927) B1093927
theorem B2769335 : Blo 968591 2769335 := bstep (se 1 (by rfl) ⟨2077001, by rfl⟩ : syracuseStep 2769335 = 4154003) B4154003
theorem B1458665 : Blo 968591 1458665 := bstep (se 2 (by rfl) ⟨546999, by rfl⟩ : syracuseStep 1458665 = 1093999) B1093999
theorem B2769403 : Blo 968591 2769403 := bstep (se 1 (by rfl) ⟨2077052, by rfl⟩ : syracuseStep 2769403 = 4154105) B4154105
theorem B110543363 : Blo 968591 110543363 := bstep (se 1 (by rfl) ⟨82907522, by rfl⟩ : syracuseStep 110543363 = 165815045) B165815045
theorem B1458791 : Blo 968591 1458791 := bstep (se 1 (by rfl) ⟨1094093, by rfl⟩ : syracuseStep 1458791 = 2188187) B2188187
theorem B2180051 : Blo 968591 2180051 := bstep (se 1 (by rfl) ⟨1635038, by rfl⟩ : syracuseStep 2180051 = 3270077) B3270077
theorem B2180303 : Blo 968591 2180303 := bstep (se 1 (by rfl) ⟨1635227, by rfl⟩ : syracuseStep 2180303 = 3270455) B3270455
theorem B25216271 : Blo 968591 25216271 := bstep (se 1 (by rfl) ⟨18912203, by rfl⟩ : syracuseStep 25216271 = 37824407) B37824407
theorem B2180627 : Blo 968591 2180627 := bstep (se 1 (by rfl) ⟨1635470, by rfl⟩ : syracuseStep 2180627 = 3270941) B3270941
theorem B23578543 : Blo 968591 23578543 := bstep (se 1 (by rfl) ⟨17683907, by rfl⟩ : syracuseStep 23578543 = 35367815) B35367815
theorem B8308655 : Blo 968591 8308655 := bstep (se 1 (by rfl) ⟨6231491, by rfl⟩ : syracuseStep 8308655 = 12462983) B12462983
theorem B968687 : Blo 968591 968687 := bstep (se 1 (by rfl) ⟨726515, by rfl⟩ : syracuseStep 968687 = 1453031) B1453031
theorem B968859 : Blo 968591 968859 := bstep (se 1 (by rfl) ⟨726644, by rfl⟩ : syracuseStep 968859 = 1453289) B1453289
theorem B968895 : Blo 968591 968895 := bstep (se 1 (by rfl) ⟨726671, by rfl⟩ : syracuseStep 968895 = 1453343) B1453343
theorem B2181311 : Blo 968591 2181311 := bstep (se 1 (by rfl) ⟨1635983, by rfl⟩ : syracuseStep 2181311 = 3271967) B3271967
theorem B969007 : Blo 968591 969007 := bstep (se 1 (by rfl) ⟨726755, by rfl⟩ : syracuseStep 969007 = 1453511) B1453511
theorem B3688861 : Blo 968591 3688861 := bstep (se 3 (by rfl) ⟨691661, by rfl⟩ : syracuseStep 3688861 = 1383323) B1383323
theorem B969243 : Blo 968591 969243 := bstep (se 1 (by rfl) ⟨726932, by rfl⟩ : syracuseStep 969243 = 1453865) B1453865
theorem B969247 : Blo 968591 969247 := bstep (se 1 (by rfl) ⟨726935, by rfl⟩ : syracuseStep 969247 = 1453871) B1453871
theorem B969563 : Blo 968591 969563 := bstep (se 1 (by rfl) ⟨727172, by rfl⟩ : syracuseStep 969563 = 1454345) B1454345
theorem B6212447 : Blo 968591 6212447 := bstep (se 1 (by rfl) ⟨4659335, by rfl⟩ : syracuseStep 6212447 = 9318671) B9318671
theorem B969631 : Blo 968591 969631 := bstep (se 1 (by rfl) ⟨727223, by rfl⟩ : syracuseStep 969631 = 1454447) B1454447
theorem B11226077 : Blo 968591 11226077 := bstep (se 3 (by rfl) ⟨2104889, by rfl⟩ : syracuseStep 11226077 = 4209779) B4209779
theorem B969775 : Blo 968591 969775 := bstep (se 1 (by rfl) ⟨727331, by rfl⟩ : syracuseStep 969775 = 1454663) B1454663
theorem B969799 : Blo 968591 969799 := bstep (se 1 (by rfl) ⟨727349, by rfl⟩ : syracuseStep 969799 = 1454699) B1454699
theorem B2182265 : Blo 968591 2182265 := bstep (se 2 (by rfl) ⟨818349, by rfl⟩ : syracuseStep 2182265 = 1636699) B1636699
theorem B969951 : Blo 968591 969951 := bstep (se 1 (by rfl) ⟨727463, by rfl⟩ : syracuseStep 969951 = 1454927) B1454927
theorem B4148603 : Blo 968591 4148603 := bstep (se 1 (by rfl) ⟨3111452, by rfl⟩ : syracuseStep 4148603 = 6222905) B6222905
theorem B9457033 : Blo 968591 9457033 := bstep (se 2 (by rfl) ⟨3546387, by rfl⟩ : syracuseStep 9457033 = 7092775) B7092775
theorem B970215 : Blo 968591 970215 := bstep (se 1 (by rfl) ⟨727661, by rfl⟩ : syracuseStep 970215 = 1455323) B1455323
theorem B18927089 : Blo 968591 18927089 := bstep (se 2 (by rfl) ⟨7097658, by rfl⟩ : syracuseStep 18927089 = 14195317) B14195317
theorem B970331 : Blo 968591 970331 := bstep (se 1 (by rfl) ⟨727748, by rfl⟩ : syracuseStep 970331 = 1455497) B1455497
theorem B39767773 : Blo 968591 39767773 := bstep (se 3 (by rfl) ⟨7456457, by rfl⟩ : syracuseStep 39767773 = 14912915) B14912915
theorem B2182931 : Blo 968591 2182931 := bstep (se 1 (by rfl) ⟨1637198, by rfl⟩ : syracuseStep 2182931 = 3274397) B3274397
theorem B970567 : Blo 968591 970567 := bstep (se 1 (by rfl) ⟨727925, by rfl⟩ : syracuseStep 970567 = 1455851) B1455851
theorem B6213449 : Blo 968591 6213449 := bstep (se 2 (by rfl) ⟨2330043, by rfl⟩ : syracuseStep 6213449 = 4660087) B4660087
theorem B970719 : Blo 968591 970719 := bstep (se 1 (by rfl) ⟨728039, by rfl⟩ : syracuseStep 970719 = 1456079) B1456079
theorem B2183291 : Blo 968591 2183291 := bstep (se 1 (by rfl) ⟨1637468, by rfl⟩ : syracuseStep 2183291 = 3274937) B3274937
theorem B970983 : Blo 968591 970983 := bstep (se 1 (by rfl) ⟨728237, by rfl⟩ : syracuseStep 970983 = 1456475) B1456475
theorem B971135 : Blo 968591 971135 := bstep (se 1 (by rfl) ⟨728351, by rfl⟩ : syracuseStep 971135 = 1456703) B1456703
theorem B2183561 : Blo 968591 2183561 := bstep (se 2 (by rfl) ⟨818835, by rfl⟩ : syracuseStep 2183561 = 1637671) B1637671
theorem B971215 : Blo 968591 971215 := bstep (se 1 (by rfl) ⟨728411, by rfl⟩ : syracuseStep 971215 = 1456823) B1456823
theorem B971367 : Blo 968591 971367 := bstep (se 1 (by rfl) ⟨728525, by rfl⟩ : syracuseStep 971367 = 1457051) B1457051
theorem B5919355 : Blo 968591 5919355 := bstep (se 1 (by rfl) ⟨4439516, by rfl⟩ : syracuseStep 5919355 = 8879033) B8879033
theorem B6640451 : Blo 968591 6640451 := bstep (se 1 (by rfl) ⟨4980338, by rfl⟩ : syracuseStep 6640451 = 9960677) B9960677
theorem B971631 : Blo 968591 971631 := bstep (se 1 (by rfl) ⟨728723, by rfl⟩ : syracuseStep 971631 = 1457447) B1457447
theorem B971687 : Blo 968591 971687 := bstep (se 1 (by rfl) ⟨728765, by rfl⟩ : syracuseStep 971687 = 1457531) B1457531
theorem B971771 : Blo 968591 971771 := bstep (se 1 (by rfl) ⟨728828, by rfl⟩ : syracuseStep 971771 = 1457657) B1457657
theorem B971839 : Blo 968591 971839 := bstep (se 1 (by rfl) ⟨728879, by rfl⟩ : syracuseStep 971839 = 1457759) B1457759
theorem B2184299 : Blo 968591 2184299 := bstep (se 1 (by rfl) ⟨1638224, by rfl⟩ : syracuseStep 2184299 = 3276449) B3276449
theorem B4150379 : Blo 968591 4150379 := bstep (se 1 (by rfl) ⟨3112784, by rfl⟩ : syracuseStep 4150379 = 6225569) B6225569
theorem B971983 : Blo 968591 971983 := bstep (se 1 (by rfl) ⟨728987, by rfl⟩ : syracuseStep 971983 = 1457975) B1457975
theorem B972187 : Blo 968591 972187 := bstep (se 1 (by rfl) ⟨729140, by rfl⟩ : syracuseStep 972187 = 1458281) B1458281
theorem B972399 : Blo 968591 972399 := bstep (se 1 (by rfl) ⟨729299, by rfl⟩ : syracuseStep 972399 = 1458599) B1458599
theorem B15357559 : Blo 968591 15357559 := bstep (se 1 (by rfl) ⟨11518169, by rfl⟩ : syracuseStep 15357559 = 23036339) B23036339
theorem B972455 : Blo 968591 972455 := bstep (se 1 (by rfl) ⟨729341, by rfl⟩ : syracuseStep 972455 = 1458683) B1458683
theorem B13981355 : Blo 968591 13981355 := bstep (se 1 (by rfl) ⟨10486016, by rfl⟩ : syracuseStep 13981355 = 20972033) B20972033
theorem B2184875 : Blo 968591 2184875 := bstep (se 1 (by rfl) ⟨1638656, by rfl⟩ : syracuseStep 2184875 = 3277313) B3277313
theorem B972539 : Blo 968591 972539 := bstep (se 1 (by rfl) ⟨729404, by rfl⟩ : syracuseStep 972539 = 1458809) B1458809
theorem B972575 : Blo 968591 972575 := bstep (se 1 (by rfl) ⟨729431, by rfl⟩ : syracuseStep 972575 = 1458863) B1458863
theorem B2185199 : Blo 968591 2185199 := bstep (se 1 (by rfl) ⟨1638899, by rfl⟩ : syracuseStep 2185199 = 3277799) B3277799
theorem B13981697 : Blo 968591 13981697 := bstep (se 2 (by rfl) ⟨5243136, by rfl⟩ : syracuseStep 13981697 = 10486273) B10486273
theorem B4151321 : Blo 968591 4151321 := bstep (se 2 (by rfl) ⟨1556745, by rfl⟩ : syracuseStep 4151321 = 3113491) B3113491
theorem B2185415 : Blo 968591 2185415 := bstep (se 1 (by rfl) ⟨1639061, by rfl⟩ : syracuseStep 2185415 = 3278123) B3278123
theorem B2185595 : Blo 968591 2185595 := bstep (se 1 (by rfl) ⟨1639196, by rfl⟩ : syracuseStep 2185595 = 3278393) B3278393
theorem B2185865 : Blo 968591 2185865 := bstep (se 2 (by rfl) ⟨819699, by rfl⟩ : syracuseStep 2185865 = 1639399) B1639399
theorem B2186423 : Blo 968591 2186423 := bstep (se 1 (by rfl) ⟨1639817, by rfl⟩ : syracuseStep 2186423 = 3279635) B3279635
theorem B4906169 : Blo 968591 4906169 := bstep (se 2 (by rfl) ⟨1839813, by rfl⟩ : syracuseStep 4906169 = 3679627) B3679627
theorem B1662439 : Blo 968591 1662439 := bstep (se 1 (by rfl) ⟨1246829, by rfl⟩ : syracuseStep 1662439 = 2493659) B2493659
theorem B13983313 : Blo 968591 13983313 := bstep (se 2 (by rfl) ⟨5243742, by rfl⟩ : syracuseStep 13983313 = 10487485) B10487485
theorem B2186999 : Blo 968591 2186999 := bstep (se 1 (by rfl) ⟨1640249, by rfl⟩ : syracuseStep 2186999 = 3280499) B3280499
theorem B18669325 : Blo 968591 18669325 := bstep (se 3 (by rfl) ⟨3500498, by rfl⟩ : syracuseStep 18669325 = 7000997) B7000997
theorem B2187179 : Blo 968591 2187179 := bstep (se 1 (by rfl) ⟨1640384, by rfl⟩ : syracuseStep 2187179 = 3280769) B3280769
theorem B1106303 : Blo 968591 1106303 := bstep (se 1 (by rfl) ⟨829727, by rfl⟩ : syracuseStep 1106303 = 1659455) B1659455
theorem B3269051 : Blo 968591 3269051 := bstep (se 1 (by rfl) ⟨2451788, by rfl⟩ : syracuseStep 3269051 = 4903577) B4903577
theorem B2187719 : Blo 968591 2187719 := bstep (se 1 (by rfl) ⟨1640789, by rfl⟩ : syracuseStep 2187719 = 3281579) B3281579
theorem B118317611 : Blo 968591 118317611 := bstep (se 1 (by rfl) ⟨88738208, by rfl⟩ : syracuseStep 118317611 = 177476417) B177476417
theorem B3105353 : Blo 968591 3105353 := bstep (se 2 (by rfl) ⟨1164507, by rfl⟩ : syracuseStep 3105353 = 2329015) B2329015
theorem B3105533 : Blo 968591 3105533 := bstep (se 3 (by rfl) ⟨582287, by rfl⟩ : syracuseStep 3105533 = 1164575) B1164575
theorem B2188079 : Blo 968591 2188079 := bstep (se 1 (by rfl) ⟨1641059, by rfl⟩ : syracuseStep 2188079 = 3282119) B3282119
theorem B11035601 : Blo 968591 11035601 := bstep (se 2 (by rfl) ⟨4138350, by rfl⟩ : syracuseStep 11035601 = 8276701) B8276701
theorem B6644825 : Blo 968591 6644825 := bstep (se 2 (by rfl) ⟨2491809, by rfl⟩ : syracuseStep 6644825 = 4983619) B4983619
theorem B3270239 : Blo 968591 3270239 := bstep (se 1 (by rfl) ⟨2452679, by rfl⟩ : syracuseStep 3270239 = 4905359) B4905359
theorem B3271643 : Blo 968591 3271643 := bstep (se 1 (by rfl) ⟨2453732, by rfl⟩ : syracuseStep 3271643 = 4907465) B4907465
theorem B3501191 : Blo 968591 3501191 := bstep (se 1 (by rfl) ⟨2625893, by rfl⟩ : syracuseStep 3501191 = 5251787) B5251787
theorem B3271913 : Blo 968591 3271913 := bstep (se 2 (by rfl) ⟨1226967, by rfl⟩ : syracuseStep 3271913 = 2453935) B2453935
theorem B3272183 : Blo 968591 3272183 := bstep (se 1 (by rfl) ⟨2454137, by rfl⟩ : syracuseStep 3272183 = 4908275) B4908275
theorem B1797857 : Blo 968591 1797857 := bstep (se 2 (by rfl) ⟨674196, by rfl⟩ : syracuseStep 1797857 = 1348393) B1348393
theorem B2453267 : Blo 968591 2453267 := bstep (se 1 (by rfl) ⟨1839950, by rfl⟩ : syracuseStep 2453267 = 3679901) B3679901
theorem B7565075 : Blo 968591 7565075 := bstep (se 1 (by rfl) ⟨5673806, by rfl⟩ : syracuseStep 7565075 = 11347613) B11347613
theorem B4910867 : Blo 968591 4910867 := bstep (se 1 (by rfl) ⟨3683150, by rfl⟩ : syracuseStep 4910867 = 7366301) B7366301
theorem B2453287 : Blo 968591 2453287 := bstep (se 1 (by rfl) ⟨1839965, by rfl⟩ : syracuseStep 2453287 = 3679931) B3679931
theorem B13266827 : Blo 968591 13266827 := bstep (se 1 (by rfl) ⟨9950120, by rfl⟩ : syracuseStep 13266827 = 19900241) B19900241
theorem B1634809 : Blo 968591 1634809 := bstep (se 2 (by rfl) ⟨613053, by rfl⟩ : syracuseStep 1634809 = 1226107) B1226107
theorem B3273209 : Blo 968591 3273209 := bstep (se 2 (by rfl) ⟨1227453, by rfl⟩ : syracuseStep 3273209 = 2454907) B2454907
theorem B3109391 : Blo 968591 3109391 := bstep (se 1 (by rfl) ⟨2332043, by rfl⟩ : syracuseStep 3109391 = 4664087) B4664087
theorem B1635079 : Blo 968591 1635079 := bstep (se 1 (by rfl) ⟨1226309, by rfl⟩ : syracuseStep 1635079 = 2452619) B2452619
theorem B3273479 : Blo 968591 3273479 := bstep (se 1 (by rfl) ⟨2455109, by rfl⟩ : syracuseStep 3273479 = 4910219) B4910219
theorem B1635113 : Blo 968591 1635113 := bstep (se 2 (by rfl) ⟨613167, by rfl⟩ : syracuseStep 1635113 = 1226335) B1226335
theorem B3273533 : Blo 968591 3273533 := bstep (se 3 (by rfl) ⟨613787, by rfl⟩ : syracuseStep 3273533 = 1227575) B1227575
theorem B2454401 : Blo 968591 2454401 := bstep (se 2 (by rfl) ⟨920400, by rfl⟩ : syracuseStep 2454401 = 1840801) B1840801
theorem B1635383 : Blo 968591 1635383 := bstep (se 1 (by rfl) ⟨1226537, by rfl⟩ : syracuseStep 1635383 = 2453075) B2453075
theorem B2454583 : Blo 968591 2454583 := bstep (se 1 (by rfl) ⟨1840937, by rfl⟩ : syracuseStep 2454583 = 3681875) B3681875
theorem B4912649 : Blo 968591 4912649 := bstep (se 2 (by rfl) ⟨1842243, by rfl⟩ : syracuseStep 4912649 = 3684487) B3684487
theorem B2455211 : Blo 968591 2455211 := bstep (se 1 (by rfl) ⟨1841408, by rfl⟩ : syracuseStep 2455211 = 3682817) B3682817
theorem B1636159 : Blo 968591 1636159 := bstep (se 1 (by rfl) ⟨1227119, by rfl⟩ : syracuseStep 1636159 = 2454239) B2454239
theorem B3274559 : Blo 968591 3274559 := bstep (se 1 (by rfl) ⟨2455919, by rfl⟩ : syracuseStep 3274559 = 4911839) B4911839
theorem B2455535 : Blo 968591 2455535 := bstep (se 1 (by rfl) ⟨1841651, by rfl⟩ : syracuseStep 2455535 = 3683303) B3683303
theorem B1636895 : Blo 968591 1636895 := bstep (se 1 (by rfl) ⟨1227671, by rfl⟩ : syracuseStep 1636895 = 2455343) B2455343
theorem B1636969 : Blo 968591 1636969 := bstep (se 2 (by rfl) ⟨613863, by rfl⟩ : syracuseStep 1636969 = 1227727) B1227727
theorem B11041433 : Blo 968591 11041433 := bstep (se 2 (by rfl) ⟨4140537, by rfl⟩ : syracuseStep 11041433 = 8281075) B8281075
theorem B1637327 : Blo 968591 1637327 := bstep (se 1 (by rfl) ⟨1227995, by rfl⟩ : syracuseStep 1637327 = 2455991) B2455991
theorem B2456527 : Blo 968591 2456527 := bstep (se 1 (by rfl) ⟨1842395, by rfl⟩ : syracuseStep 2456527 = 3684791) B3684791
theorem B3276071 : Blo 968591 3276071 := bstep (se 1 (by rfl) ⟨2457053, by rfl⟩ : syracuseStep 3276071 = 4914107) B4914107
theorem B6651233 : Blo 968591 6651233 := bstep (se 2 (by rfl) ⟨2494212, by rfl⟩ : syracuseStep 6651233 = 4988425) B4988425
theorem B1637995 : Blo 968591 1637995 := bstep (se 1 (by rfl) ⟨1228496, by rfl⟩ : syracuseStep 1637995 = 2456993) B2456993
theorem B1638265 : Blo 968591 1638265 := bstep (se 2 (by rfl) ⟨614349, by rfl⟩ : syracuseStep 1638265 = 1228699) B1228699
theorem B1638299 : Blo 968591 1638299 := bstep (se 1 (by rfl) ⟨1228724, by rfl⟩ : syracuseStep 1638299 = 2457449) B2457449
theorem B5046457 : Blo 968591 5046457 := bstep (se 2 (by rfl) ⟨1892421, by rfl⟩ : syracuseStep 5046457 = 3784843) B3784843
theorem B1311023 : Blo 968591 1311023 := bstep (se 1 (by rfl) ⟨983267, by rfl⟩ : syracuseStep 1311023 = 1966535) B1966535
theorem B73695575 : Blo 968591 73695575 := bstep (se 1 (by rfl) ⟨55271681, by rfl⟩ : syracuseStep 73695575 = 110543363) B110543363
theorem B8389423 : Blo 968591 8389423 := bstep (se 1 (by rfl) ⟨6292067, by rfl⟩ : syracuseStep 8389423 = 12584135) B12584135
theorem B16810847 : Blo 968591 16810847 := bstep (se 1 (by rfl) ⟨12608135, by rfl⟩ : syracuseStep 16810847 = 25216271) B25216271
theorem B1639615 : Blo 968591 1639615 := bstep (se 1 (by rfl) ⟨1229711, by rfl⟩ : syracuseStep 1639615 = 2459423) B2459423
theorem B15729875 : Blo 968591 15729875 := bstep (se 1 (by rfl) ⟨11797406, by rfl⟩ : syracuseStep 15729875 = 23594813) B23594813
theorem B5539103 : Blo 968591 5539103 := bstep (se 1 (by rfl) ⟨4154327, by rfl⟩ : syracuseStep 5539103 = 8308655) B8308655
theorem B17696171 : Blo 968591 17696171 := bstep (se 1 (by rfl) ⟨13272128, by rfl⟩ : syracuseStep 17696171 = 26544257) B26544257
theorem B9438727 : Blo 968591 9438727 := bstep (se 1 (by rfl) ⟨7079045, by rfl⟩ : syracuseStep 9438727 = 14158091) B14158091
theorem B2623375 : Blo 968591 2623375 := bstep (se 1 (by rfl) ⟨1967531, by rfl⟩ : syracuseStep 2623375 = 3935063) B3935063
theorem B47319011 : Blo 968591 47319011 := bstep (se 1 (by rfl) ⟨35489258, by rfl⟩ : syracuseStep 47319011 = 70978517) B70978517
theorem B1640479 : Blo 968591 1640479 := bstep (se 1 (by rfl) ⟨1230359, by rfl⟩ : syracuseStep 1640479 = 2460719) B2460719
theorem B3115169 : Blo 968591 3115169 := bstep (se 2 (by rfl) ⟨1168188, by rfl⟩ : syracuseStep 3115169 = 2336377) B2336377
theorem B12618059 : Blo 968591 12618059 := bstep (se 1 (by rfl) ⟨9463544, by rfl⟩ : syracuseStep 12618059 = 18927089) B18927089
theorem B1640783 : Blo 968591 1640783 := bstep (se 1 (by rfl) ⟨1230587, by rfl⟩ : syracuseStep 1640783 = 2461175) B2461175
theorem B18877279 : Blo 968591 18877279 := bstep (se 1 (by rfl) ⟨14157959, by rfl⟩ : syracuseStep 18877279 = 28315919) B28315919
theorem B6229055 : Blo 968591 6229055 := bstep (se 1 (by rfl) ⟨4671791, by rfl⟩ : syracuseStep 6229055 = 9343583) B9343583
theorem B4918481 : Blo 968591 4918481 := bstep (se 2 (by rfl) ⟨1844430, by rfl⟩ : syracuseStep 4918481 = 3688861) B3688861
theorem B4426967 : Blo 968591 4426967 := bstep (se 1 (by rfl) ⟨3320225, by rfl⟩ : syracuseStep 4426967 = 6640451) B6640451
theorem B2624879 : Blo 968591 2624879 := bstep (se 1 (by rfl) ⟨1968659, by rfl⟩ : syracuseStep 2624879 = 3937319) B3937319
theorem B3739007 : Blo 968591 3739007 := bstep (se 1 (by rfl) ⟨2804255, by rfl⟩ : syracuseStep 3739007 = 5608511) B5608511
theorem B11800565 : Blo 968591 11800565 := bstep (se 5 (by rfl) ⟨553151, by rfl⟩ : syracuseStep 11800565 = 1106303) B1106303
theorem B1380407 : Blo 968591 1380407 := bstep (se 1 (by rfl) ⟨1035305, by rfl⟩ : syracuseStep 1380407 = 2070611) B2070611
theorem B1839199 : Blo 968591 1839199 := bstep (se 1 (by rfl) ⟨1379399, by rfl⟩ : syracuseStep 1839199 = 2758799) B2758799
theorem B7869089 : Blo 968591 7869089 := bstep (se 2 (by rfl) ⟨2950908, by rfl⟩ : syracuseStep 7869089 = 5901817) B5901817
theorem B53023697 : Blo 968591 53023697 := bstep (se 2 (by rfl) ⟨19883886, by rfl⟩ : syracuseStep 53023697 = 39767773) B39767773
theorem B3281903 : Blo 968591 3281903 := bstep (se 1 (by rfl) ⟨2461427, by rfl⟩ : syracuseStep 3281903 = 4922855) B4922855
theorem B4920911 : Blo 968591 4920911 := bstep (se 1 (by rfl) ⟨3690683, by rfl⟩ : syracuseStep 4920911 = 7381367) B7381367
theorem B78878407 : Blo 968591 78878407 := bstep (se 1 (by rfl) ⟨59158805, by rfl⟩ : syracuseStep 78878407 = 118317611) B118317611
theorem B2070235 : Blo 968591 2070235 := bstep (se 1 (by rfl) ⟨1552676, by rfl⟩ : syracuseStep 2070235 = 3105353) B3105353
theorem B2070355 : Blo 968591 2070355 := bstep (se 1 (by rfl) ⟨1552766, by rfl⟩ : syracuseStep 2070355 = 3105533) B3105533
theorem B2332513 : Blo 968591 2332513 := bstep (se 2 (by rfl) ⟨874692, by rfl⟩ : syracuseStep 2332513 = 1749385) B1749385
theorem B5248891 : Blo 968591 5248891 := bstep (se 1 (by rfl) ⟨3936668, by rfl⟩ : syracuseStep 5248891 = 7873337) B7873337
theorem B31528885 : Blo 968591 31528885 := bstep (se 5 (by rfl) ⟨1477916, by rfl⟩ : syracuseStep 31528885 = 2955833) B2955833
theorem B1841143 : Blo 968591 1841143 := bstep (se 1 (by rfl) ⟨1380857, by rfl⟩ : syracuseStep 1841143 = 2761715) B2761715
theorem B4429883 : Blo 968591 4429883 := bstep (se 1 (by rfl) ⟨3322412, by rfl⟩ : syracuseStep 4429883 = 6644825) B6644825
theorem B4921559 : Blo 968591 4921559 := bstep (se 1 (by rfl) ⟨3691169, by rfl⟩ : syracuseStep 4921559 = 7382339) B7382339
theorem B12458519 : Blo 968591 12458519 := bstep (se 1 (by rfl) ⟨9343889, by rfl⟩ : syracuseStep 12458519 = 18687779) B18687779
theorem B15735383 : Blo 968591 15735383 := bstep (se 1 (by rfl) ⟨11801537, by rfl⟩ : syracuseStep 15735383 = 23603075) B23603075
theorem B1842031 : Blo 968591 1842031 := bstep (se 1 (by rfl) ⟨1381523, by rfl⟩ : syracuseStep 1842031 = 2763047) B2763047
theorem B9313217 : Blo 968591 9313217 := bstep (se 2 (by rfl) ⟨3492456, by rfl⟩ : syracuseStep 9313217 = 6984913) B6984913
theorem B5905345 : Blo 968591 5905345 := bstep (se 2 (by rfl) ⟨2214504, by rfl⟩ : syracuseStep 5905345 = 4429009) B4429009
theorem B1384303 : Blo 968591 1384303 := bstep (se 1 (by rfl) ⟨1038227, by rfl⟩ : syracuseStep 1384303 = 2076455) B2076455
theorem B4661165 : Blo 968591 4661165 := bstep (se 3 (by rfl) ⟨873968, by rfl⟩ : syracuseStep 4661165 = 1747937) B1747937
theorem B2760655 : Blo 968591 2760655 := bstep (se 1 (by rfl) ⟨2070491, by rfl⟩ : syracuseStep 2760655 = 4140983) B4140983
theorem B15769637 : Blo 968591 15769637 := bstep (se 4 (by rfl) ⟨1478403, by rfl⟩ : syracuseStep 15769637 = 2956807) B2956807
theorem B3547265 : Blo 968591 3547265 := bstep (se 2 (by rfl) ⟨1330224, by rfl⟩ : syracuseStep 3547265 = 2660449) B2660449
theorem B3678473 : Blo 968591 3678473 := bstep (se 2 (by rfl) ⟨1379427, by rfl⟩ : syracuseStep 3678473 = 2758855) B2758855
theorem B2072927 : Blo 968591 2072927 := bstep (se 1 (by rfl) ⟨1554695, by rfl⟩ : syracuseStep 2072927 = 3109391) B3109391
theorem B2072969 : Blo 968591 2072969 := bstep (se 2 (by rfl) ⟨777363, by rfl⟩ : syracuseStep 2072969 = 1554727) B1554727
theorem B1090075 : Blo 968591 1090075 := bstep (se 1 (by rfl) ⟨817556, by rfl⟩ : syracuseStep 1090075 = 1635113) B1635113
theorem B1090255 : Blo 968591 1090255 := bstep (se 1 (by rfl) ⟨817691, by rfl⟩ : syracuseStep 1090255 = 1635383) B1635383
theorem B1843975 : Blo 968591 1843975 := bstep (se 1 (by rfl) ⟨1382981, by rfl⟩ : syracuseStep 1843975 = 2765963) B2765963
theorem B8397665 : Blo 968591 8397665 := bstep (se 2 (by rfl) ⟨3149124, by rfl⟩ : syracuseStep 8397665 = 6298249) B6298249
theorem B3941291 : Blo 968591 3941291 := bstep (se 1 (by rfl) ⟨2955968, by rfl⟩ : syracuseStep 3941291 = 5911937) B5911937
theorem B1844203 : Blo 968591 1844203 := bstep (se 1 (by rfl) ⟨1383152, by rfl⟩ : syracuseStep 1844203 = 2766305) B2766305
theorem B2073721 : Blo 968591 2073721 := bstep (se 2 (by rfl) ⟨777645, by rfl⟩ : syracuseStep 2073721 = 1555291) B1555291
theorem B1091263 : Blo 968591 1091263 := bstep (se 1 (by rfl) ⟨818447, by rfl⟩ : syracuseStep 1091263 = 1636895) B1636895
theorem B1091551 : Blo 968591 1091551 := bstep (se 1 (by rfl) ⟨818663, by rfl⟩ : syracuseStep 1091551 = 1637327) B1637327
theorem B17704927 : Blo 968591 17704927 := bstep (se 1 (by rfl) ⟨13278695, by rfl⟩ : syracuseStep 17704927 = 26557391) B26557391
theorem B4434155 : Blo 968591 4434155 := bstep (se 1 (by rfl) ⟨3325616, by rfl⟩ : syracuseStep 4434155 = 6651233) B6651233
theorem B3680585 : Blo 968591 3680585 := bstep (se 2 (by rfl) ⟨1380219, by rfl⟩ : syracuseStep 3680585 = 2760439) B2760439
theorem B1092199 : Blo 968591 1092199 := bstep (se 1 (by rfl) ⟨819149, by rfl⟩ : syracuseStep 1092199 = 1638299) B1638299
theorem B4205243 : Blo 968591 4205243 := bstep (se 1 (by rfl) ⟨3153932, by rfl⟩ : syracuseStep 4205243 = 6307865) B6307865
theorem B1846223 : Blo 968591 1846223 := bstep (se 1 (by rfl) ⟨1384667, by rfl⟩ : syracuseStep 1846223 = 2769335) B2769335
theorem B1453367 : Blo 968591 1453367 := bstep (se 1 (by rfl) ⟨1090025, by rfl⟩ : syracuseStep 1453367 = 2180051) B2180051
theorem B2075959 : Blo 968591 2075959 := bstep (se 1 (by rfl) ⟨1556969, by rfl⟩ : syracuseStep 2075959 = 3113939) B3113939
theorem B1092991 : Blo 968591 1092991 := bstep (se 1 (by rfl) ⟨819743, by rfl⟩ : syracuseStep 1092991 = 1639487) B1639487
theorem B23571931 : Blo 968591 23571931 := bstep (se 1 (by rfl) ⟨17678948, by rfl⟩ : syracuseStep 23571931 = 35357897) B35357897
theorem B1453535 : Blo 968591 1453535 := bstep (se 1 (by rfl) ⟨1090151, by rfl⟩ : syracuseStep 1453535 = 2180303) B2180303
theorem B1453751 : Blo 968591 1453751 := bstep (se 1 (by rfl) ⟨1090313, by rfl⟩ : syracuseStep 1453751 = 2180627) B2180627
theorem B1453961 : Blo 968591 1453961 := bstep (se 2 (by rfl) ⟨545235, by rfl⟩ : syracuseStep 1453961 = 1090471) B1090471
theorem B1454207 : Blo 968591 1454207 := bstep (se 1 (by rfl) ⟨1090655, by rfl⟩ : syracuseStep 1454207 = 2181311) B2181311
theorem B4141631 : Blo 968591 4141631 := bstep (se 1 (by rfl) ⟨3106223, by rfl⟩ : syracuseStep 4141631 = 6212447) B6212447
theorem B8303219 : Blo 968591 8303219 := bstep (se 1 (by rfl) ⟨6227414, by rfl⟩ : syracuseStep 8303219 = 12454829) B12454829
theorem B7484051 : Blo 968591 7484051 := bstep (se 1 (by rfl) ⟨5613038, by rfl⟩ : syracuseStep 7484051 = 11226077) B11226077
theorem B1454843 : Blo 968591 1454843 := bstep (se 1 (by rfl) ⟨1091132, by rfl⟩ : syracuseStep 1454843 = 2182265) B2182265
theorem B2765735 : Blo 968591 2765735 := bstep (se 1 (by rfl) ⟨2074301, by rfl⟩ : syracuseStep 2765735 = 4148603) B4148603
theorem B1455287 : Blo 968591 1455287 := bstep (se 1 (by rfl) ⟨1091465, by rfl⟩ : syracuseStep 1455287 = 2182931) B2182931
theorem B4142299 : Blo 968591 4142299 := bstep (se 1 (by rfl) ⟨3106724, by rfl⟩ : syracuseStep 4142299 = 6213449) B6213449
theorem B31438057 : Blo 968591 31438057 := bstep (se 2 (by rfl) ⟨11789271, by rfl⟩ : syracuseStep 31438057 = 23578543) B23578543
theorem B2766089 : Blo 968591 2766089 := bstep (se 2 (by rfl) ⟨1037283, by rfl⟩ : syracuseStep 2766089 = 2074567) B2074567
theorem B1455527 : Blo 968591 1455527 := bstep (se 1 (by rfl) ⟨1091645, by rfl⟩ : syracuseStep 1455527 = 2183291) B2183291
theorem B1455707 : Blo 968591 1455707 := bstep (se 1 (by rfl) ⟨1091780, by rfl⟩ : syracuseStep 1455707 = 2183561) B2183561
theorem B3684001 : Blo 968591 3684001 := bstep (se 2 (by rfl) ⟨1381500, by rfl⟩ : syracuseStep 3684001 = 2763001) B2763001
theorem B1456169 : Blo 968591 1456169 := bstep (se 2 (by rfl) ⟨546063, by rfl⟩ : syracuseStep 1456169 = 1092127) B1092127
theorem B1456199 : Blo 968591 1456199 := bstep (se 1 (by rfl) ⟨1092149, by rfl⟩ : syracuseStep 1456199 = 2184299) B2184299
theorem B1226983 : Blo 968591 1226983 := bstep (se 1 (by rfl) ⟨920237, by rfl⟩ : syracuseStep 1226983 = 1840475) B1840475
theorem B9320903 : Blo 968591 9320903 := bstep (se 1 (by rfl) ⟨6990677, by rfl⟩ : syracuseStep 9320903 = 13981355) B13981355
theorem B1456583 : Blo 968591 1456583 := bstep (se 1 (by rfl) ⟨1092437, by rfl⟩ : syracuseStep 1456583 = 2184875) B2184875
theorem B1456799 : Blo 968591 1456799 := bstep (se 1 (by rfl) ⟨1092599, by rfl⟩ : syracuseStep 1456799 = 2185199) B2185199
theorem B9321131 : Blo 968591 9321131 := bstep (se 1 (by rfl) ⟨6990848, by rfl⟩ : syracuseStep 9321131 = 13981697) B13981697
theorem B2767547 : Blo 968591 2767547 := bstep (se 1 (by rfl) ⟨2075660, by rfl⟩ : syracuseStep 2767547 = 4151321) B4151321
theorem B1456943 : Blo 968591 1456943 := bstep (se 1 (by rfl) ⟨1092707, by rfl⟩ : syracuseStep 1456943 = 2185415) B2185415
theorem B1555367 : Blo 968591 1555367 := bstep (se 1 (by rfl) ⟨1166525, by rfl⟩ : syracuseStep 1555367 = 2333051) B2333051
theorem B1457063 : Blo 968591 1457063 := bstep (se 1 (by rfl) ⟨1092797, by rfl⟩ : syracuseStep 1457063 = 2185595) B2185595
theorem B17742881 : Blo 968591 17742881 := bstep (se 2 (by rfl) ⟨6653580, by rfl⟩ : syracuseStep 17742881 = 13307161) B13307161
theorem B1457243 : Blo 968591 1457243 := bstep (se 1 (by rfl) ⟨1092932, by rfl⟩ : syracuseStep 1457243 = 2185865) B2185865
theorem B1457615 : Blo 968591 1457615 := bstep (se 1 (by rfl) ⟨1093211, by rfl⟩ : syracuseStep 1457615 = 2186423) B2186423
theorem B1457999 : Blo 968591 1457999 := bstep (se 1 (by rfl) ⟨1093499, by rfl⟩ : syracuseStep 1457999 = 2186999) B2186999
theorem B3686249 : Blo 968591 3686249 := bstep (se 2 (by rfl) ⟨1382343, by rfl⟩ : syracuseStep 3686249 = 2764687) B2764687
theorem B9322361 : Blo 968591 9322361 := bstep (se 2 (by rfl) ⟨3495885, by rfl⟩ : syracuseStep 9322361 = 6991771) B6991771
theorem B1458119 : Blo 968591 1458119 := bstep (se 1 (by rfl) ⟨1093589, by rfl⟩ : syracuseStep 1458119 = 2187179) B2187179
theorem B6209783 : Blo 968591 6209783 := bstep (se 1 (by rfl) ⟨4657337, by rfl⟩ : syracuseStep 6209783 = 9314675) B9314675
theorem B2179367 : Blo 968591 2179367 := bstep (se 1 (by rfl) ⟨1634525, by rfl⟩ : syracuseStep 2179367 = 3269051) B3269051
theorem B1458479 : Blo 968591 1458479 := bstep (se 1 (by rfl) ⟨1093859, by rfl⟩ : syracuseStep 1458479 = 2187719) B2187719
theorem B1458719 : Blo 968591 1458719 := bstep (se 1 (by rfl) ⟨1094039, by rfl⟩ : syracuseStep 1458719 = 2188079) B2188079
theorem B7881313 : Blo 968591 7881313 := bstep (se 2 (by rfl) ⟨2955492, by rfl⟩ : syracuseStep 7881313 = 5910985) B5910985
theorem B7357067 : Blo 968591 7357067 := bstep (se 1 (by rfl) ⟨5517800, by rfl⟩ : syracuseStep 7357067 = 11035601) B11035601
theorem B2179745 : Blo 968591 2179745 := bstep (se 2 (by rfl) ⟨817404, by rfl⟩ : syracuseStep 2179745 = 1634809) B1634809
theorem B2180105 : Blo 968591 2180105 := bstep (se 2 (by rfl) ⟨817539, by rfl⟩ : syracuseStep 2180105 = 1635079) B1635079
theorem B2180159 : Blo 968591 2180159 := bstep (se 1 (by rfl) ⟨1635119, by rfl⟩ : syracuseStep 2180159 = 3270239) B3270239
theorem B1164623 : Blo 968591 1164623 := bstep (se 1 (by rfl) ⟨873467, by rfl⟩ : syracuseStep 1164623 = 1746935) B1746935
theorem B3327419 : Blo 968591 3327419 := bstep (se 1 (by rfl) ⟨2495564, by rfl⟩ : syracuseStep 3327419 = 4991129) B4991129
theorem B968639 : Blo 968591 968639 := bstep (se 1 (by rfl) ⟨726479, by rfl⟩ : syracuseStep 968639 = 1452959) B1452959
theorem B968671 : Blo 968591 968671 := bstep (se 1 (by rfl) ⟨726503, by rfl⟩ : syracuseStep 968671 = 1453007) B1453007
theorem B2181095 : Blo 968591 2181095 := bstep (se 1 (by rfl) ⟨1635821, by rfl⟩ : syracuseStep 2181095 = 3271643) B3271643
theorem B968731 : Blo 968591 968731 := bstep (se 1 (by rfl) ⟨726548, by rfl⟩ : syracuseStep 968731 = 1453097) B1453097
theorem B968735 : Blo 968591 968735 := bstep (se 1 (by rfl) ⟨726551, by rfl⟩ : syracuseStep 968735 = 1453103) B1453103
theorem B968751 : Blo 968591 968751 := bstep (se 1 (by rfl) ⟨726563, by rfl⟩ : syracuseStep 968751 = 1453127) B1453127
theorem B2181275 : Blo 968591 2181275 := bstep (se 1 (by rfl) ⟨1635956, by rfl⟩ : syracuseStep 2181275 = 3271913) B3271913
theorem B968927 : Blo 968591 968927 := bstep (se 1 (by rfl) ⟨726695, by rfl⟩ : syracuseStep 968927 = 1453391) B1453391
theorem B968987 : Blo 968591 968987 := bstep (se 1 (by rfl) ⟨726740, by rfl⟩ : syracuseStep 968987 = 1453481) B1453481
theorem B2181455 : Blo 968591 2181455 := bstep (se 1 (by rfl) ⟨1636091, by rfl⟩ : syracuseStep 2181455 = 3272183) B3272183
theorem B969087 : Blo 968591 969087 := bstep (se 1 (by rfl) ⟨726815, by rfl⟩ : syracuseStep 969087 = 1453631) B1453631
theorem B2181545 : Blo 968591 2181545 := bstep (se 2 (by rfl) ⟨818079, by rfl⟩ : syracuseStep 2181545 = 1636159) B1636159
theorem B1198571 : Blo 968591 1198571 := bstep (se 1 (by rfl) ⟨898928, by rfl⟩ : syracuseStep 1198571 = 1797857) B1797857
theorem B969263 : Blo 968591 969263 := bstep (se 1 (by rfl) ⟨726947, by rfl⟩ : syracuseStep 969263 = 1453895) B1453895
theorem B969319 : Blo 968591 969319 := bstep (se 1 (by rfl) ⟨726989, by rfl⟩ : syracuseStep 969319 = 1453979) B1453979
theorem B969695 : Blo 968591 969695 := bstep (se 1 (by rfl) ⟨727271, by rfl⟩ : syracuseStep 969695 = 1454543) B1454543
theorem B969723 : Blo 968591 969723 := bstep (se 1 (by rfl) ⟨727292, by rfl⟩ : syracuseStep 969723 = 1454585) B1454585
theorem B2182139 : Blo 968591 2182139 := bstep (se 1 (by rfl) ⟨1636604, by rfl⟩ : syracuseStep 2182139 = 3273209) B3273209
theorem B7359497 : Blo 968591 7359497 := bstep (se 2 (by rfl) ⟨2759811, by rfl⟩ : syracuseStep 7359497 = 5519623) B5519623
theorem B969791 : Blo 968591 969791 := bstep (se 1 (by rfl) ⟨727343, by rfl⟩ : syracuseStep 969791 = 1454687) B1454687
theorem B2182319 : Blo 968591 2182319 := bstep (se 1 (by rfl) ⟨1636739, by rfl⟩ : syracuseStep 2182319 = 3273479) B3273479
theorem B2182355 : Blo 968591 2182355 := bstep (se 1 (by rfl) ⟨1636766, by rfl⟩ : syracuseStep 2182355 = 3273533) B3273533
theorem B9096425 : Blo 968591 9096425 := bstep (se 2 (by rfl) ⟨3411159, by rfl⟩ : syracuseStep 9096425 = 6822319) B6822319
theorem B970111 : Blo 968591 970111 := bstep (se 1 (by rfl) ⟨727583, by rfl⟩ : syracuseStep 970111 = 1455167) B1455167
theorem B970139 : Blo 968591 970139 := bstep (se 1 (by rfl) ⟨727604, by rfl⟩ : syracuseStep 970139 = 1455209) B1455209
theorem B970207 : Blo 968591 970207 := bstep (se 1 (by rfl) ⟨727655, by rfl⟩ : syracuseStep 970207 = 1455311) B1455311
theorem B2182625 : Blo 968591 2182625 := bstep (se 2 (by rfl) ⟨818484, by rfl⟩ : syracuseStep 2182625 = 1636969) B1636969
theorem B970343 : Blo 968591 970343 := bstep (se 1 (by rfl) ⟨727757, by rfl⟩ : syracuseStep 970343 = 1455515) B1455515
theorem B970491 : Blo 968591 970491 := bstep (se 1 (by rfl) ⟨727868, by rfl⟩ : syracuseStep 970491 = 1455737) B1455737
theorem B970559 : Blo 968591 970559 := bstep (se 1 (by rfl) ⟨727919, by rfl⟩ : syracuseStep 970559 = 1455839) B1455839
theorem B2183039 : Blo 968591 2183039 := bstep (se 1 (by rfl) ⟨1637279, by rfl⟩ : syracuseStep 2183039 = 3274559) B3274559
theorem B970623 : Blo 968591 970623 := bstep (se 1 (by rfl) ⟨727967, by rfl⟩ : syracuseStep 970623 = 1455935) B1455935
theorem B1036271 : Blo 968591 1036271 := bstep (se 1 (by rfl) ⟨777203, by rfl⟩ : syracuseStep 1036271 = 1554407) B1554407
theorem B970735 : Blo 968591 970735 := bstep (se 1 (by rfl) ⟨728051, by rfl⟩ : syracuseStep 970735 = 1456103) B1456103
theorem B970747 : Blo 968591 970747 := bstep (se 1 (by rfl) ⟨728060, by rfl⟩ : syracuseStep 970747 = 1456121) B1456121
theorem B970815 : Blo 968591 970815 := bstep (se 1 (by rfl) ⟨728111, by rfl⟩ : syracuseStep 970815 = 1456223) B1456223
theorem B10506341 : Blo 968591 10506341 := bstep (se 4 (by rfl) ⟨984969, by rfl⟩ : syracuseStep 10506341 = 1969939) B1969939
theorem B970855 : Blo 968591 970855 := bstep (se 1 (by rfl) ⟨728141, by rfl⟩ : syracuseStep 970855 = 1456283) B1456283
theorem B970879 : Blo 968591 970879 := bstep (se 1 (by rfl) ⟨728159, by rfl⟩ : syracuseStep 970879 = 1456319) B1456319
theorem B970907 : Blo 968591 970907 := bstep (se 1 (by rfl) ⟨728180, by rfl⟩ : syracuseStep 970907 = 1456361) B1456361
theorem B971111 : Blo 968591 971111 := bstep (se 1 (by rfl) ⟨728333, by rfl⟩ : syracuseStep 971111 = 1456667) B1456667
theorem B4149629 : Blo 968591 4149629 := bstep (se 3 (by rfl) ⟨778055, by rfl⟩ : syracuseStep 4149629 = 1556111) B1556111
theorem B971163 : Blo 968591 971163 := bstep (se 1 (by rfl) ⟨728372, by rfl⟩ : syracuseStep 971163 = 1456745) B1456745
theorem B7459235 : Blo 968591 7459235 := bstep (se 1 (by rfl) ⟨5594426, by rfl⟩ : syracuseStep 7459235 = 11188853) B11188853
theorem B7360955 : Blo 968591 7360955 := bstep (se 1 (by rfl) ⟨5520716, by rfl⟩ : syracuseStep 7360955 = 11041433) B11041433
theorem B2216585 : Blo 968591 2216585 := bstep (se 2 (by rfl) ⟨831219, by rfl⟩ : syracuseStep 2216585 = 1662439) B1662439
theorem B6312593 : Blo 968591 6312593 := bstep (se 2 (by rfl) ⟨2367222, by rfl⟩ : syracuseStep 6312593 = 4734445) B4734445
theorem B971515 : Blo 968591 971515 := bstep (se 1 (by rfl) ⟨728636, by rfl⟩ : syracuseStep 971515 = 1457273) B1457273
theorem B2183993 : Blo 968591 2183993 := bstep (se 2 (by rfl) ⟨818997, by rfl⟩ : syracuseStep 2183993 = 1637995) B1637995
theorem B971583 : Blo 968591 971583 := bstep (se 1 (by rfl) ⟨728687, by rfl⟩ : syracuseStep 971583 = 1457375) B1457375
theorem B971611 : Blo 968591 971611 := bstep (se 1 (by rfl) ⟨728708, by rfl⟩ : syracuseStep 971611 = 1457417) B1457417
theorem B2184047 : Blo 968591 2184047 := bstep (se 1 (by rfl) ⟨1638035, by rfl⟩ : syracuseStep 2184047 = 3276071) B3276071
theorem B1037215 : Blo 968591 1037215 := bstep (se 1 (by rfl) ⟨777911, by rfl⟩ : syracuseStep 1037215 = 1555823) B1555823
theorem B971679 : Blo 968591 971679 := bstep (se 1 (by rfl) ⟨728759, by rfl⟩ : syracuseStep 971679 = 1457519) B1457519
theorem B7361441 : Blo 968591 7361441 := bstep (se 2 (by rfl) ⟨2760540, by rfl⟩ : syracuseStep 7361441 = 5521081) B5521081
theorem B971759 : Blo 968591 971759 := bstep (se 1 (by rfl) ⟨728819, by rfl⟩ : syracuseStep 971759 = 1457639) B1457639
theorem B24892433 : Blo 968591 24892433 := bstep (se 2 (by rfl) ⟨9334662, by rfl⟩ : syracuseStep 24892433 = 18669325) B18669325
theorem B971847 : Blo 968591 971847 := bstep (se 1 (by rfl) ⟨728885, by rfl⟩ : syracuseStep 971847 = 1457771) B1457771
theorem B971931 : Blo 968591 971931 := bstep (se 1 (by rfl) ⟨728948, by rfl⟩ : syracuseStep 971931 = 1457897) B1457897
theorem B2184353 : Blo 968591 2184353 := bstep (se 2 (by rfl) ⟨819132, by rfl⟩ : syracuseStep 2184353 = 1638265) B1638265
theorem B972027 : Blo 968591 972027 := bstep (se 1 (by rfl) ⟨729020, by rfl⟩ : syracuseStep 972027 = 1458041) B1458041
theorem B972095 : Blo 968591 972095 := bstep (se 1 (by rfl) ⟨729071, by rfl⟩ : syracuseStep 972095 = 1458143) B1458143
theorem B5526913 : Blo 968591 5526913 := bstep (se 2 (by rfl) ⟨2072592, by rfl⟩ : syracuseStep 5526913 = 4145185) B4145185
theorem B2184623 : Blo 968591 2184623 := bstep (se 1 (by rfl) ⟨1638467, by rfl⟩ : syracuseStep 2184623 = 3276935) B3276935
theorem B972263 : Blo 968591 972263 := bstep (se 1 (by rfl) ⟨729197, by rfl⟩ : syracuseStep 972263 = 1458395) B1458395
theorem B972271 : Blo 968591 972271 := bstep (se 1 (by rfl) ⟨729203, by rfl⟩ : syracuseStep 972271 = 1458407) B1458407
theorem B972379 : Blo 968591 972379 := bstep (se 1 (by rfl) ⟨729284, by rfl⟩ : syracuseStep 972379 = 1458569) B1458569
theorem B972443 : Blo 968591 972443 := bstep (se 1 (by rfl) ⟨729332, by rfl⟩ : syracuseStep 972443 = 1458665) B1458665
theorem B972527 : Blo 968591 972527 := bstep (se 1 (by rfl) ⟨729395, by rfl⟩ : syracuseStep 972527 = 1458791) B1458791
theorem B3692537 : Blo 968591 3692537 := bstep (se 2 (by rfl) ⟨1384701, by rfl⟩ : syracuseStep 3692537 = 2769403) B2769403
theorem B3103073 : Blo 968591 3103073 := bstep (se 2 (by rfl) ⟨1163652, by rfl⟩ : syracuseStep 3103073 = 2327305) B2327305
theorem B2185631 : Blo 968591 2185631 := bstep (se 1 (by rfl) ⟨1639223, by rfl⟩ : syracuseStep 2185631 = 3278447) B3278447
theorem B2185703 : Blo 968591 2185703 := bstep (se 1 (by rfl) ⟨1639277, by rfl⟩ : syracuseStep 2185703 = 3278555) B3278555
theorem B3103559 : Blo 968591 3103559 := bstep (se 1 (by rfl) ⟨2327669, by rfl⟩ : syracuseStep 3103559 = 4655339) B4655339
theorem B7363871 : Blo 968591 7363871 := bstep (se 1 (by rfl) ⟨5522903, by rfl⟩ : syracuseStep 7363871 = 11045807) B11045807
theorem B2186567 : Blo 968591 2186567 := bstep (se 1 (by rfl) ⟨1639925, by rfl⟩ : syracuseStep 2186567 = 3279851) B3279851
theorem B2186603 : Blo 968591 2186603 := bstep (se 1 (by rfl) ⟨1639952, by rfl⟩ : syracuseStep 2186603 = 3279905) B3279905
theorem B2186729 : Blo 968591 2186729 := bstep (se 2 (by rfl) ⟨820023, by rfl⟩ : syracuseStep 2186729 = 1640047) B1640047
theorem B2186873 : Blo 968591 2186873 := bstep (se 2 (by rfl) ⟨820077, by rfl⟩ : syracuseStep 2186873 = 1640155) B1640155
theorem B11067677 : Blo 968591 11067677 := bstep (se 3 (by rfl) ⟨2075189, by rfl⟩ : syracuseStep 11067677 = 4150379) B4150379
theorem B2187575 : Blo 968591 2187575 := bstep (se 1 (by rfl) ⟨1640681, by rfl⟩ : syracuseStep 2187575 = 3281363) B3281363
theorem B7004893 : Blo 968591 7004893 := bstep (se 3 (by rfl) ⟨1313417, by rfl⟩ : syracuseStep 7004893 = 2626835) B2626835
theorem B12609377 : Blo 968591 12609377 := bstep (se 2 (by rfl) ⟨4728516, by rfl⟩ : syracuseStep 12609377 = 9457033) B9457033
theorem B9332819 : Blo 968591 9332819 := bstep (se 1 (by rfl) ⟨6999614, by rfl⟩ : syracuseStep 9332819 = 13999229) B13999229
theorem B3270779 : Blo 968591 3270779 := bstep (se 1 (by rfl) ⟨2453084, by rfl⟩ : syracuseStep 3270779 = 4906169) B4906169
theorem B3271049 : Blo 968591 3271049 := bstep (se 2 (by rfl) ⟨1226643, by rfl⟩ : syracuseStep 3271049 = 2453287) B2453287
theorem B25226149 : Blo 968591 25226149 := bstep (se 4 (by rfl) ⟨2364951, by rfl⟩ : syracuseStep 25226149 = 4729903) B4729903
theorem B7892473 : Blo 968591 7892473 := bstep (se 2 (by rfl) ⟨2959677, by rfl⟩ : syracuseStep 7892473 = 5919355) B5919355
theorem B3272777 : Blo 968591 3272777 := bstep (se 2 (by rfl) ⟨1227291, by rfl⟩ : syracuseStep 3272777 = 2454583) B2454583
theorem B20476745 : Blo 968591 20476745 := bstep (se 2 (by rfl) ⟨7678779, by rfl⟩ : syracuseStep 20476745 = 15357559) B15357559
theorem B7369703 : Blo 968591 7369703 := bstep (se 1 (by rfl) ⟨5527277, by rfl⟩ : syracuseStep 7369703 = 11054555) B11054555
theorem B1635511 : Blo 968591 1635511 := bstep (se 1 (by rfl) ⟨1226633, by rfl⟩ : syracuseStep 1635511 = 2453267) B2453267
theorem B5043383 : Blo 968591 5043383 := bstep (se 1 (by rfl) ⟨3782537, by rfl⟩ : syracuseStep 5043383 = 7565075) B7565075
theorem B3273911 : Blo 968591 3273911 := bstep (se 1 (by rfl) ⟨2455433, by rfl⟩ : syracuseStep 3273911 = 4910867) B4910867
theorem B8844551 : Blo 968591 8844551 := bstep (se 1 (by rfl) ⟨6633413, by rfl⟩ : syracuseStep 8844551 = 13266827) B13266827
theorem B9336509 : Blo 968591 9336509 := bstep (se 3 (by rfl) ⟨1750595, by rfl⟩ : syracuseStep 9336509 = 3501191) B3501191
theorem B1636267 : Blo 968591 1636267 := bstep (se 1 (by rfl) ⟨1227200, by rfl⟩ : syracuseStep 1636267 = 2454401) B2454401
theorem B1865963 : Blo 968591 1865963 := bstep (se 1 (by rfl) ⟨1399472, by rfl⟩ : syracuseStep 1865963 = 2798945) B2798945
theorem B9337123 : Blo 968591 9337123 := bstep (se 1 (by rfl) ⟨7002842, by rfl⟩ : syracuseStep 9337123 = 14005685) B14005685
theorem B3275099 : Blo 968591 3275099 := bstep (se 1 (by rfl) ⟨2456324, by rfl⟩ : syracuseStep 3275099 = 4912649) B4912649
theorem B1636807 : Blo 968591 1636807 := bstep (se 1 (by rfl) ⟨1227605, by rfl⟩ : syracuseStep 1636807 = 2455211) B2455211
theorem B3275369 : Blo 968591 3275369 := bstep (se 2 (by rfl) ⟨1228263, by rfl⟩ : syracuseStep 3275369 = 2456527) B2456527
theorem B1637023 : Blo 968591 1637023 := bstep (se 1 (by rfl) ⟨1227767, by rfl⟩ : syracuseStep 1637023 = 2455535) B2455535
theorem B3636127 : Blo 968591 3636127 := bstep (se 1 (by rfl) ⟨2727095, by rfl⟩ : syracuseStep 3636127 = 5454191) B5454191
theorem B18644417 : Blo 968591 18644417 := bstep (se 2 (by rfl) ⟨6991656, by rfl⟩ : syracuseStep 18644417 = 13983313) B13983313
theorem B17727275 : Blo 968591 17727275 := bstep (se 1 (by rfl) ⟨13295456, by rfl⟩ : syracuseStep 17727275 = 26590913) B26590913
theorem B11207231 : Blo 968591 11207231 := bstep (se 1 (by rfl) ⟨8405423, by rfl⟩ : syracuseStep 11207231 = 16810847) B16810847
theorem B10486583 : Blo 968591 10486583 := bstep (se 1 (by rfl) ⟨7864937, by rfl⟩ : syracuseStep 10486583 = 15729875) B15729875
theorem B9339857 : Blo 968591 9339857 := bstep (se 2 (by rfl) ⟨3502446, by rfl⟩ : syracuseStep 9339857 = 7004893) B7004893
theorem B2458633 : Blo 968591 2458633 := bstep (se 2 (by rfl) ⟨921987, by rfl⟩ : syracuseStep 2458633 = 1843975) B1843975
theorem B2458937 : Blo 968591 2458937 := bstep (se 2 (by rfl) ⟨922101, by rfl⟩ : syracuseStep 2458937 = 1844203) B1844203
theorem B11044349 : Blo 968591 11044349 := bstep (se 3 (by rfl) ⟨2070815, by rfl⟩ : syracuseStep 11044349 = 4141631) B4141631
theorem B12584969 : Blo 968591 12584969 := bstep (se 2 (by rfl) ⟨4719363, by rfl⟩ : syracuseStep 12584969 = 9438727) B9438727
theorem B3278987 : Blo 968591 3278987 := bstep (se 1 (by rfl) ⟨2459240, by rfl⟩ : syracuseStep 3278987 = 4918481) B4918481
theorem B2951311 : Blo 968591 2951311 := bstep (se 1 (by rfl) ⟨2213483, by rfl⟩ : syracuseStep 2951311 = 4426967) B4426967
theorem B6064283 : Blo 968591 6064283 := bstep (se 1 (by rfl) ⟨4548212, by rfl⟩ : syracuseStep 6064283 = 9096425) B9096425
theorem B7867043 : Blo 968591 7867043 := bstep (se 1 (by rfl) ⟨5900282, by rfl⟩ : syracuseStep 7867043 = 11800565) B11800565
theorem B5246059 : Blo 968591 5246059 := bstep (se 1 (by rfl) ⟨3934544, by rfl⟩ : syracuseStep 5246059 = 7869089) B7869089
theorem B3280607 : Blo 968591 3280607 := bstep (se 1 (by rfl) ⟨2460455, by rfl⟩ : syracuseStep 3280607 = 4920911) B4920911
theorem B47189789 : Blo 968591 47189789 := bstep (se 3 (by rfl) ⟨8848085, by rfl⟩ : syracuseStep 47189789 = 17696171) B17696171
theorem B25169705 : Blo 968591 25169705 := bstep (se 2 (by rfl) ⟨9438639, by rfl⟩ : syracuseStep 25169705 = 18877279) B18877279
theorem B2461691 : Blo 968591 2461691 := bstep (se 1 (by rfl) ⟨1846268, by rfl⟩ : syracuseStep 2461691 = 3692537) B3692537
theorem B2953255 : Blo 968591 2953255 := bstep (se 1 (by rfl) ⟨2214941, by rfl⟩ : syracuseStep 2953255 = 4429883) B4429883
theorem B3281039 : Blo 968591 3281039 := bstep (se 1 (by rfl) ⟨2460779, by rfl⟩ : syracuseStep 3281039 = 4921559) B4921559
theorem B2068715 : Blo 968591 2068715 := bstep (se 1 (by rfl) ⟨1551536, by rfl⟩ : syracuseStep 2068715 = 3103073) B3103073
theorem B10490255 : Blo 968591 10490255 := bstep (se 1 (by rfl) ⟨7867691, by rfl⟩ : syracuseStep 10490255 = 15735383) B15735383
theorem B2069039 : Blo 968591 2069039 := bstep (se 1 (by rfl) ⟨1551779, by rfl⟩ : syracuseStep 2069039 = 3103559) B3103559
theorem B31429241 : Blo 968591 31429241 := bstep (se 2 (by rfl) ⟨11785965, by rfl⟩ : syracuseStep 31429241 = 23571931) B23571931
theorem B10523297 : Blo 968591 10523297 := bstep (se 2 (by rfl) ⟨3946236, by rfl⟩ : syracuseStep 10523297 = 7892473) B7892473
theorem B7378451 : Blo 968591 7378451 := bstep (se 1 (by rfl) ⟨5533838, by rfl⟩ : syracuseStep 7378451 = 11067677) B11067677
theorem B1381951 : Blo 968591 1381951 := bstep (se 1 (by rfl) ⟨1036463, by rfl⟩ : syracuseStep 1381951 = 2072927) B2072927
theorem B1381979 : Blo 968591 1381979 := bstep (se 1 (by rfl) ⟨1036484, by rfl⟩ : syracuseStep 1381979 = 2072969) B2072969
theorem B2627527 : Blo 968591 2627527 := bstep (se 1 (by rfl) ⟨1970645, by rfl⟩ : syracuseStep 2627527 = 3941291) B3941291
theorem B2956103 : Blo 968591 2956103 := bstep (se 1 (by rfl) ⟨2217077, by rfl⟩ : syracuseStep 2956103 = 4434155) B4434155
theorem B41917409 : Blo 968591 41917409 := bstep (se 2 (by rfl) ⟨15719028, by rfl⟩ : syracuseStep 41917409 = 31438057) B31438057
theorem B2760313 : Blo 968591 2760313 := bstep (se 2 (by rfl) ⟨1035117, by rfl⟩ : syracuseStep 2760313 = 2070235) B2070235
theorem B2760473 : Blo 968591 2760473 := bstep (se 2 (by rfl) ⟨1035177, by rfl⟩ : syracuseStep 2760473 = 2070355) B2070355
theorem B4989367 : Blo 968591 4989367 := bstep (se 1 (by rfl) ⟨3742025, by rfl⟩ : syracuseStep 4989367 = 7484051) B7484051
theorem B1843823 : Blo 968591 1843823 := bstep (se 1 (by rfl) ⟨1382867, by rfl⟩ : syracuseStep 1843823 = 2765735) B2765735
theorem B1844059 : Blo 968591 1844059 := bstep (se 1 (by rfl) ⟨1383044, by rfl⟩ : syracuseStep 1844059 = 2766089) B2766089
theorem B9970685 : Blo 968591 9970685 := bstep (se 3 (by rfl) ⟨1869503, by rfl⟩ : syracuseStep 9970685 = 3739007) B3739007
theorem B7873793 : Blo 968591 7873793 := bstep (se 2 (by rfl) ⟨2952672, by rfl⟩ : syracuseStep 7873793 = 5905345) B5905345
theorem B16590581 : Blo 968591 16590581 := bstep (se 5 (by rfl) ⟨777683, by rfl⟩ : syracuseStep 16590581 = 1555367) B1555367
theorem B1845031 : Blo 968591 1845031 := bstep (se 1 (by rfl) ⟨1383773, by rfl⟩ : syracuseStep 1845031 = 2767547) B2767547
theorem B12429611 : Blo 968591 12429611 := bstep (se 1 (by rfl) ⟨9322208, by rfl⟩ : syracuseStep 12429611 = 18644417) B18644417
theorem B1845737 : Blo 968591 1845737 := bstep (se 2 (by rfl) ⟨692151, by rfl⟩ : syracuseStep 1845737 = 1384303) B1384303
theorem B3680873 : Blo 968591 3680873 := bstep (se 2 (by rfl) ⟨1380327, by rfl⟩ : syracuseStep 3680873 = 2760655) B2760655
theorem B2763389 : Blo 968591 2763389 := bstep (se 3 (by rfl) ⟨518135, by rfl⟩ : syracuseStep 2763389 = 1036271) B1036271
theorem B3681085 : Blo 968591 3681085 := bstep (se 3 (by rfl) ⟨690203, by rfl⟩ : syracuseStep 3681085 = 1380407) B1380407
theorem B4139855 : Blo 968591 4139855 := bstep (se 1 (by rfl) ⟨3104891, by rfl⟩ : syracuseStep 4139855 = 6209783) B6209783
theorem B1452911 : Blo 968591 1452911 := bstep (se 1 (by rfl) ⟨1089683, by rfl⟩ : syracuseStep 1452911 = 2179367) B2179367
theorem B49130383 : Blo 968591 49130383 := bstep (se 1 (by rfl) ⟨36847787, by rfl⟩ : syracuseStep 49130383 = 73695575) B73695575
theorem B6728609 : Blo 968591 6728609 := bstep (se 2 (by rfl) ⟨2523228, by rfl⟩ : syracuseStep 6728609 = 5046457) B5046457
theorem B1453163 : Blo 968591 1453163 := bstep (se 1 (by rfl) ⟨1089872, by rfl⟩ : syracuseStep 1453163 = 2179745) B2179745
theorem B1453403 : Blo 968591 1453403 := bstep (se 1 (by rfl) ⟨1090052, by rfl⟩ : syracuseStep 1453403 = 2180105) B2180105
theorem B1453433 : Blo 968591 1453433 := bstep (se 2 (by rfl) ⟨545037, by rfl⟩ : syracuseStep 1453433 = 1090075) B1090075
theorem B1453439 : Blo 968591 1453439 := bstep (se 1 (by rfl) ⟨1090079, by rfl⟩ : syracuseStep 1453439 = 2180159) B2180159
theorem B1453673 : Blo 968591 1453673 := bstep (se 2 (by rfl) ⟨545127, by rfl⟩ : syracuseStep 1453673 = 1090255) B1090255
theorem B11185897 : Blo 968591 11185897 := bstep (se 2 (by rfl) ⟨4194711, by rfl⟩ : syracuseStep 11185897 = 8389423) B8389423
theorem B1454063 : Blo 968591 1454063 := bstep (se 1 (by rfl) ⟨1090547, by rfl⟩ : syracuseStep 1454063 = 2181095) B2181095
theorem B1454183 : Blo 968591 1454183 := bstep (se 1 (by rfl) ⟨1090637, by rfl⟩ : syracuseStep 1454183 = 2181275) B2181275
theorem B2076779 : Blo 968591 2076779 := bstep (se 1 (by rfl) ⟨1557584, by rfl⟩ : syracuseStep 2076779 = 3115169) B3115169
theorem B2764961 : Blo 968591 2764961 := bstep (se 2 (by rfl) ⟨1036860, by rfl⟩ : syracuseStep 2764961 = 2073721) B2073721
theorem B1454303 : Blo 968591 1454303 := bstep (se 1 (by rfl) ⟨1090727, by rfl⟩ : syracuseStep 1454303 = 2181455) B2181455
theorem B1093855 : Blo 968591 1093855 := bstep (se 1 (by rfl) ⟨820391, by rfl⟩ : syracuseStep 1093855 = 1640783) B1640783
theorem B1454363 : Blo 968591 1454363 := bstep (se 1 (by rfl) ⟨1090772, by rfl⟩ : syracuseStep 1454363 = 2181545) B2181545
theorem B5910893 : Blo 968591 5910893 := bstep (se 3 (by rfl) ⟨1108292, by rfl⟩ : syracuseStep 5910893 = 2216585) B2216585
theorem B1454759 : Blo 968591 1454759 := bstep (se 1 (by rfl) ⟨1091069, by rfl⟩ : syracuseStep 1454759 = 2182139) B2182139
theorem B1454879 : Blo 968591 1454879 := bstep (se 1 (by rfl) ⟨1091159, by rfl⟩ : syracuseStep 1454879 = 2182319) B2182319
theorem B1454903 : Blo 968591 1454903 := bstep (se 1 (by rfl) ⟨1091177, by rfl⟩ : syracuseStep 1454903 = 2182355) B2182355
theorem B1749919 : Blo 968591 1749919 := bstep (se 1 (by rfl) ⟨1312439, by rfl⟩ : syracuseStep 1749919 = 2624879) B2624879
theorem B1455017 : Blo 968591 1455017 := bstep (se 2 (by rfl) ⟨545631, by rfl⟩ : syracuseStep 1455017 = 1091263) B1091263
theorem B1455083 : Blo 968591 1455083 := bstep (se 1 (by rfl) ⟨1091312, by rfl⟩ : syracuseStep 1455083 = 2182625) B2182625
theorem B1455359 : Blo 968591 1455359 := bstep (se 1 (by rfl) ⟨1091519, by rfl⟩ : syracuseStep 1455359 = 2183039) B2183039
theorem B1455401 : Blo 968591 1455401 := bstep (se 2 (by rfl) ⟨545775, by rfl⟩ : syracuseStep 1455401 = 1091551) B1091551
theorem B23606569 : Blo 968591 23606569 := bstep (se 2 (by rfl) ⟨8852463, by rfl⟩ : syracuseStep 23606569 = 17704927) B17704927
theorem B2766419 : Blo 968591 2766419 := bstep (se 1 (by rfl) ⟨2074814, by rfl⟩ : syracuseStep 2766419 = 4149629) B4149629
theorem B1455995 : Blo 968591 1455995 := bstep (se 1 (by rfl) ⟨1091996, by rfl⟩ : syracuseStep 1455995 = 2183993) B2183993
theorem B1456031 : Blo 968591 1456031 := bstep (se 1 (by rfl) ⟨1092023, by rfl⟩ : syracuseStep 1456031 = 2184047) B2184047
theorem B16594955 : Blo 968591 16594955 := bstep (se 1 (by rfl) ⟨12446216, by rfl⟩ : syracuseStep 16594955 = 24892433) B24892433
theorem B1456235 : Blo 968591 1456235 := bstep (se 1 (by rfl) ⟨1092176, by rfl⟩ : syracuseStep 1456235 = 2184353) B2184353
theorem B1456265 : Blo 968591 1456265 := bstep (se 2 (by rfl) ⟨546099, by rfl⟩ : syracuseStep 1456265 = 1092199) B1092199
theorem B1456415 : Blo 968591 1456415 := bstep (se 1 (by rfl) ⟨1092311, by rfl⟩ : syracuseStep 1456415 = 2184623) B2184623
theorem B33634865 : Blo 968591 33634865 := bstep (se 2 (by rfl) ⟨12613074, by rfl⟩ : syracuseStep 33634865 = 25226149) B25226149
theorem B1457087 : Blo 968591 1457087 := bstep (se 1 (by rfl) ⟨1092815, by rfl⟩ : syracuseStep 1457087 = 2185631) B2185631
theorem B1457135 : Blo 968591 1457135 := bstep (se 1 (by rfl) ⟨1092851, by rfl⟩ : syracuseStep 1457135 = 2185703) B2185703
theorem B8305679 : Blo 968591 8305679 := bstep (se 1 (by rfl) ⟨6229259, by rfl⟩ : syracuseStep 8305679 = 12458519) B12458519
theorem B2767945 : Blo 968591 2767945 := bstep (se 2 (by rfl) ⟨1037979, by rfl⟩ : syracuseStep 2767945 = 2075959) B2075959
theorem B1457321 : Blo 968591 1457321 := bstep (se 2 (by rfl) ⟨546495, by rfl⟩ : syracuseStep 1457321 = 1092991) B1092991
theorem B6208811 : Blo 968591 6208811 := bstep (se 1 (by rfl) ⟨4656608, by rfl⟩ : syracuseStep 6208811 = 9313217) B9313217
theorem B1457711 : Blo 968591 1457711 := bstep (se 1 (by rfl) ⟨1093283, by rfl⟩ : syracuseStep 1457711 = 2186567) B2186567
theorem B1457735 : Blo 968591 1457735 := bstep (se 1 (by rfl) ⟨1093301, by rfl⟩ : syracuseStep 1457735 = 2186603) B2186603
theorem B1457819 : Blo 968591 1457819 := bstep (se 1 (by rfl) ⟨1093364, by rfl⟩ : syracuseStep 1457819 = 2186729) B2186729
theorem B1457915 : Blo 968591 1457915 := bstep (se 1 (by rfl) ⟨1093436, by rfl⟩ : syracuseStep 1457915 = 2186873) B2186873
theorem B1458383 : Blo 968591 1458383 := bstep (se 1 (by rfl) ⟨1093787, by rfl⟩ : syracuseStep 1458383 = 2187575) B2187575
theorem B8406251 : Blo 968591 8406251 := bstep (se 1 (by rfl) ⟨6304688, by rfl⟩ : syracuseStep 8406251 = 12609377) B12609377
theorem B3196189 : Blo 968591 3196189 := bstep (se 3 (by rfl) ⟨599285, by rfl⟩ : syracuseStep 3196189 = 1198571) B1198571
theorem B2180519 : Blo 968591 2180519 := bstep (se 1 (by rfl) ⟨1635389, by rfl⟩ : syracuseStep 2180519 = 3270779) B3270779
theorem B2180681 : Blo 968591 2180681 := bstep (se 2 (by rfl) ⟨817755, by rfl⟩ : syracuseStep 2180681 = 1635511) B1635511
theorem B2180699 : Blo 968591 2180699 := bstep (se 1 (by rfl) ⟨1635524, by rfl⟩ : syracuseStep 2180699 = 3271049) B3271049
theorem B5523065 : Blo 968591 5523065 := bstep (se 2 (by rfl) ⟨2071149, by rfl⟩ : syracuseStep 5523065 = 4142299) B4142299
theorem B2803495 : Blo 968591 2803495 := bstep (se 1 (by rfl) ⟨2102621, by rfl⟩ : syracuseStep 2803495 = 4205243) B4205243
theorem B1230815 : Blo 968591 1230815 := bstep (se 1 (by rfl) ⟨923111, by rfl⟩ : syracuseStep 1230815 = 1846223) B1846223
theorem B968911 : Blo 968591 968911 := bstep (se 1 (by rfl) ⟨726683, by rfl⟩ : syracuseStep 968911 = 1453367) B1453367
theorem B105171209 : Blo 968591 105171209 := bstep (se 2 (by rfl) ⟨39439203, by rfl⟩ : syracuseStep 105171209 = 78878407) B78878407
theorem B969023 : Blo 968591 969023 := bstep (se 1 (by rfl) ⟨726767, by rfl⟩ : syracuseStep 969023 = 1453535) B1453535
theorem B969167 : Blo 968591 969167 := bstep (se 1 (by rfl) ⟨726875, by rfl⟩ : syracuseStep 969167 = 1453751) B1453751
theorem B6998521 : Blo 968591 6998521 := bstep (se 2 (by rfl) ⟨2624445, by rfl⟩ : syracuseStep 6998521 = 5248891) B5248891
theorem B2181689 : Blo 968591 2181689 := bstep (se 2 (by rfl) ⟨818133, by rfl⟩ : syracuseStep 2181689 = 1636267) B1636267
theorem B969307 : Blo 968591 969307 := bstep (se 1 (by rfl) ⟨726980, by rfl⟩ : syracuseStep 969307 = 1453961) B1453961
theorem B2181851 : Blo 968591 2181851 := bstep (se 1 (by rfl) ⟨1636388, by rfl⟩ : syracuseStep 2181851 = 3272777) B3272777
theorem B969471 : Blo 968591 969471 := bstep (se 1 (by rfl) ⟨727103, by rfl⟩ : syracuseStep 969471 = 1454207) B1454207
theorem B969895 : Blo 968591 969895 := bstep (se 1 (by rfl) ⟨727421, by rfl⟩ : syracuseStep 969895 = 1454843) B1454843
theorem B13651163 : Blo 968591 13651163 := bstep (se 1 (by rfl) ⟨10238372, by rfl⟩ : syracuseStep 13651163 = 20476745) B20476745
theorem B2182409 : Blo 968591 2182409 := bstep (se 2 (by rfl) ⟨818403, by rfl⟩ : syracuseStep 2182409 = 1636807) B1636807
theorem B3362255 : Blo 968591 3362255 := bstep (se 1 (by rfl) ⟨2521691, by rfl⟩ : syracuseStep 3362255 = 5043383) B5043383
theorem B2182607 : Blo 968591 2182607 := bstep (se 1 (by rfl) ⟨1636955, by rfl⟩ : syracuseStep 2182607 = 3273911) B3273911
theorem B970191 : Blo 968591 970191 := bstep (se 1 (by rfl) ⟨727643, by rfl⟩ : syracuseStep 970191 = 1455287) B1455287
theorem B2182697 : Blo 968591 2182697 := bstep (se 2 (by rfl) ⟨818511, by rfl⟩ : syracuseStep 2182697 = 1637023) B1637023
theorem B970351 : Blo 968591 970351 := bstep (se 1 (by rfl) ⟨727763, by rfl⟩ : syracuseStep 970351 = 1455527) B1455527
theorem B970471 : Blo 968591 970471 := bstep (se 1 (by rfl) ⟨727853, by rfl⟩ : syracuseStep 970471 = 1455707) B1455707
theorem B970779 : Blo 968591 970779 := bstep (se 1 (by rfl) ⟨728084, by rfl⟩ : syracuseStep 970779 = 1456169) B1456169
theorem B970799 : Blo 968591 970799 := bstep (se 1 (by rfl) ⟨728099, by rfl⟩ : syracuseStep 970799 = 1456199) B1456199
theorem B2183399 : Blo 968591 2183399 := bstep (se 1 (by rfl) ⟨1637549, by rfl⟩ : syracuseStep 2183399 = 3275099) B3275099
theorem B6213935 : Blo 968591 6213935 := bstep (se 1 (by rfl) ⟨4660451, by rfl⟩ : syracuseStep 6213935 = 9320903) B9320903
theorem B971055 : Blo 968591 971055 := bstep (se 1 (by rfl) ⟨728291, by rfl⟩ : syracuseStep 971055 = 1456583) B1456583
theorem B2183579 : Blo 968591 2183579 := bstep (se 1 (by rfl) ⟨1637684, by rfl⟩ : syracuseStep 2183579 = 3275369) B3275369
theorem B971199 : Blo 968591 971199 := bstep (se 1 (by rfl) ⟨728399, by rfl⟩ : syracuseStep 971199 = 1456799) B1456799
theorem B6214087 : Blo 968591 6214087 := bstep (se 1 (by rfl) ⟨4660565, by rfl⟩ : syracuseStep 6214087 = 9321131) B9321131
theorem B971295 : Blo 968591 971295 := bstep (se 1 (by rfl) ⟨728471, by rfl⟩ : syracuseStep 971295 = 1456943) B1456943
theorem B971375 : Blo 968591 971375 := bstep (se 1 (by rfl) ⟨728531, by rfl⟩ : syracuseStep 971375 = 1457063) B1457063
theorem B971495 : Blo 968591 971495 := bstep (se 1 (by rfl) ⟨728621, by rfl⟩ : syracuseStep 971495 = 1457243) B1457243
theorem B971743 : Blo 968591 971743 := bstep (se 1 (by rfl) ⟨728807, by rfl⟩ : syracuseStep 971743 = 1457615) B1457615
theorem B11818183 : Blo 968591 11818183 := bstep (se 1 (by rfl) ⟨8863637, by rfl⟩ : syracuseStep 11818183 = 17727275) B17727275
theorem B971999 : Blo 968591 971999 := bstep (se 1 (by rfl) ⟨728999, by rfl⟩ : syracuseStep 971999 = 1457999) B1457999
theorem B6214907 : Blo 968591 6214907 := bstep (se 1 (by rfl) ⟨4661180, by rfl⟩ : syracuseStep 6214907 = 9322361) B9322361
theorem B972079 : Blo 968591 972079 := bstep (se 1 (by rfl) ⟨729059, by rfl⟩ : syracuseStep 972079 = 1458119) B1458119
theorem B972319 : Blo 968591 972319 := bstep (se 1 (by rfl) ⟨729239, by rfl⟩ : syracuseStep 972319 = 1458479) B1458479
theorem B972479 : Blo 968591 972479 := bstep (se 1 (by rfl) ⟨729359, by rfl⟩ : syracuseStep 972479 = 1458719) B1458719
theorem B4904711 : Blo 968591 4904711 := bstep (se 1 (by rfl) ⟨3678533, by rfl⟩ : syracuseStep 4904711 = 7357067) B7357067
theorem B3496061 : Blo 968591 3496061 := bstep (se 3 (by rfl) ⟨655511, by rfl⟩ : syracuseStep 3496061 = 1311023) B1311023
theorem B10508417 : Blo 968591 10508417 := bstep (se 2 (by rfl) ⟨3940656, by rfl⟩ : syracuseStep 10508417 = 7881313) B7881313
theorem B3692735 : Blo 968591 3692735 := bstep (se 1 (by rfl) ⟨2769551, by rfl⟩ : syracuseStep 3692735 = 5539103) B5539103
theorem B2218279 : Blo 968591 2218279 := bstep (se 1 (by rfl) ⟨1663709, by rfl⟩ : syracuseStep 2218279 = 3327419) B3327419
theorem B31546007 : Blo 968591 31546007 := bstep (se 1 (by rfl) ⟨23659505, by rfl⟩ : syracuseStep 31546007 = 47319011) B47319011
theorem B37837493 : Blo 968591 37837493 := bstep (se 5 (by rfl) ⟨1773632, by rfl⟩ : syracuseStep 37837493 = 3547265) B3547265
theorem B2186153 : Blo 968591 2186153 := bstep (se 2 (by rfl) ⟨819807, by rfl⟩ : syracuseStep 2186153 = 1639615) B1639615
theorem B16833581 : Blo 968591 16833581 := bstep (se 3 (by rfl) ⟨3156296, by rfl⟩ : syracuseStep 16833581 = 6312593) B6312593
theorem B4906331 : Blo 968591 4906331 := bstep (se 1 (by rfl) ⟨3679748, by rfl⟩ : syracuseStep 4906331 = 7359497) B7359497
theorem B4152703 : Blo 968591 4152703 := bstep (se 1 (by rfl) ⟨3114527, by rfl⟩ : syracuseStep 4152703 = 6229055) B6229055
theorem B3497833 : Blo 968591 3497833 := bstep (se 2 (by rfl) ⟨1311687, by rfl⟩ : syracuseStep 3497833 = 2623375) B2623375
theorem B2187305 : Blo 968591 2187305 := bstep (se 2 (by rfl) ⟨820239, by rfl⟩ : syracuseStep 2187305 = 1640479) B1640479
theorem B7004227 : Blo 968591 7004227 := bstep (se 1 (by rfl) ⟨5253170, by rfl⟩ : syracuseStep 7004227 = 10506341) B10506341
theorem B4972823 : Blo 968591 4972823 := bstep (se 1 (by rfl) ⟨3729617, by rfl⟩ : syracuseStep 4972823 = 7459235) B7459235
theorem B4907303 : Blo 968591 4907303 := bstep (se 1 (by rfl) ⟨3680477, by rfl⟩ : syracuseStep 4907303 = 7360955) B7360955
theorem B4907627 : Blo 968591 4907627 := bstep (se 1 (by rfl) ⟨3680720, by rfl⟩ : syracuseStep 4907627 = 7361441) B7361441
theorem B35349131 : Blo 968591 35349131 := bstep (se 1 (by rfl) ⟨26511848, by rfl⟩ : syracuseStep 35349131 = 53023697) B53023697
theorem B2187935 : Blo 968591 2187935 := bstep (se 1 (by rfl) ⟨1640951, by rfl⟩ : syracuseStep 2187935 = 3281903) B3281903
theorem B3105661 : Blo 968591 3105661 := bstep (se 3 (by rfl) ⟨582311, by rfl⟩ : syracuseStep 3105661 = 1164623) B1164623
theorem B5531813 : Blo 968591 5531813 := bstep (se 4 (by rfl) ⟨518607, by rfl⟩ : syracuseStep 5531813 = 1037215) B1037215
theorem B4909247 : Blo 968591 4909247 := bstep (se 1 (by rfl) ⟨3681935, by rfl⟩ : syracuseStep 4909247 = 7363871) B7363871
theorem B3107443 : Blo 968591 3107443 := bstep (se 1 (by rfl) ⟨2330582, by rfl⟩ : syracuseStep 3107443 = 4661165) B4661165
theorem B10513091 : Blo 968591 10513091 := bstep (se 1 (by rfl) ⟨7884818, by rfl⟩ : syracuseStep 10513091 = 15769637) B15769637
theorem B2452265 : Blo 968591 2452265 := bstep (se 2 (by rfl) ⟨919599, by rfl⟩ : syracuseStep 2452265 = 1839199) B1839199
theorem B2452315 : Blo 968591 2452315 := bstep (se 1 (by rfl) ⟨1839236, by rfl⟩ : syracuseStep 2452315 = 3678473) B3678473
theorem B5598443 : Blo 968591 5598443 := bstep (se 1 (by rfl) ⟨4198832, by rfl⟩ : syracuseStep 5598443 = 8397665) B8397665
theorem B4975901 : Blo 968591 4975901 := bstep (se 3 (by rfl) ⟨932981, by rfl⟩ : syracuseStep 4975901 = 1865963) B1865963
theorem B33648157 : Blo 968591 33648157 := bstep (se 3 (by rfl) ⟨6309029, by rfl⟩ : syracuseStep 33648157 = 12618059) B12618059
theorem B6221879 : Blo 968591 6221879 := bstep (se 1 (by rfl) ⟨4666409, by rfl⟩ : syracuseStep 6221879 = 9332819) B9332819
theorem B2453723 : Blo 968591 2453723 := bstep (se 1 (by rfl) ⟨1840292, by rfl⟩ : syracuseStep 2453723 = 3680585) B3680585
theorem B7369217 : Blo 968591 7369217 := bstep (se 2 (by rfl) ⟨2763456, by rfl⟩ : syracuseStep 7369217 = 5526913) B5526913
theorem B4912001 : Blo 968591 4912001 := bstep (se 2 (by rfl) ⟨1842000, by rfl⟩ : syracuseStep 4912001 = 3684001) B3684001
theorem B3110017 : Blo 968591 3110017 := bstep (se 2 (by rfl) ⟨1166256, by rfl⟩ : syracuseStep 3110017 = 2332513) B2332513
theorem B42038513 : Blo 968591 42038513 := bstep (se 2 (by rfl) ⟨15764442, by rfl⟩ : syracuseStep 42038513 = 31528885) B31528885
theorem B2454857 : Blo 968591 2454857 := bstep (se 2 (by rfl) ⟨920571, by rfl⟩ : syracuseStep 2454857 = 1841143) B1841143
theorem B1635977 : Blo 968591 1635977 := bstep (se 2 (by rfl) ⟨613491, by rfl⟩ : syracuseStep 1635977 = 1226983) B1226983
theorem B12449497 : Blo 968591 12449497 := bstep (se 2 (by rfl) ⟨4668561, by rfl⟩ : syracuseStep 12449497 = 9337123) B9337123
theorem B5535479 : Blo 968591 5535479 := bstep (se 1 (by rfl) ⟨4151609, by rfl⟩ : syracuseStep 5535479 = 8303219) B8303219
theorem B4913135 : Blo 968591 4913135 := bstep (se 1 (by rfl) ⟨3684851, by rfl⟩ : syracuseStep 4913135 = 7369703) B7369703
theorem B5896367 : Blo 968591 5896367 := bstep (se 1 (by rfl) ⟨4422275, by rfl⟩ : syracuseStep 5896367 = 8844551) B8844551
theorem B6224339 : Blo 968591 6224339 := bstep (se 1 (by rfl) ⟨4668254, by rfl⟩ : syracuseStep 6224339 = 9336509) B9336509
theorem B2456041 : Blo 968591 2456041 := bstep (se 2 (by rfl) ⟨921015, by rfl⟩ : syracuseStep 2456041 = 1842031) B1842031
theorem B4848169 : Blo 968591 4848169 := bstep (se 2 (by rfl) ⟨1818063, by rfl⟩ : syracuseStep 4848169 = 3636127) B3636127
theorem B11828587 : Blo 968591 11828587 := bstep (se 1 (by rfl) ⟨8871440, by rfl⟩ : syracuseStep 11828587 = 17742881) B17742881
theorem B2457499 : Blo 968591 2457499 := bstep (se 1 (by rfl) ⟨1843124, by rfl⟩ : syracuseStep 2457499 = 3686249) B3686249
theorem B9338969 : Blo 968591 9338969 := bstep (se 2 (by rfl) ⟨3502113, by rfl⟩ : syracuseStep 9338969 = 7004227) B7004227
theorem B5538077 : Blo 968591 5538077 := bstep (se 3 (by rfl) ⟨1038389, by rfl⟩ : syracuseStep 5538077 = 2076779) B2076779
theorem B7471487 : Blo 968591 7471487 := bstep (se 1 (by rfl) ⟨5603615, by rfl⟩ : syracuseStep 7471487 = 11207231) B11207231
theorem B6652489 : Blo 968591 6652489 := bstep (se 2 (by rfl) ⟨2494683, by rfl⟩ : syracuseStep 6652489 = 4989367) B4989367
theorem B6226571 : Blo 968591 6226571 := bstep (se 1 (by rfl) ⟨4669928, by rfl⟩ : syracuseStep 6226571 = 9339857) B9339857
theorem B5604167 : Blo 968591 5604167 := bstep (se 1 (by rfl) ⟨4203125, by rfl⟩ : syracuseStep 5604167 = 8406251) B8406251
theorem B1639291 : Blo 968591 1639291 := bstep (se 1 (by rfl) ⟨1229468, by rfl⟩ : syracuseStep 1639291 = 2458937) B2458937
theorem B2458745 : Blo 968591 2458745 := bstep (se 2 (by rfl) ⟨922029, by rfl⟩ : syracuseStep 2458745 = 1844059) B1844059
theorem B8389979 : Blo 968591 8389979 := bstep (se 1 (by rfl) ⟨6292484, by rfl⟩ : syracuseStep 8389979 = 12584969) B12584969
theorem B3278177 : Blo 968591 3278177 := bstep (se 2 (by rfl) ⟨1229316, by rfl⟩ : syracuseStep 3278177 = 2458633) B2458633
theorem B4916861 : Blo 968591 4916861 := bstep (se 3 (by rfl) ⟨921911, by rfl⟩ : syracuseStep 4916861 = 1843823) B1843823
theorem B4261585 : Blo 968591 4261585 := bstep (se 2 (by rfl) ⟨1598094, by rfl⟩ : syracuseStep 4261585 = 3196189) B3196189
theorem B5244695 : Blo 968591 5244695 := bstep (se 1 (by rfl) ⟨3933521, by rfl⟩ : syracuseStep 5244695 = 7867043) B7867043
theorem B3737993 : Blo 968591 3737993 := bstep (se 2 (by rfl) ⟨1401747, by rfl⟩ : syracuseStep 3737993 = 2803495) B2803495
theorem B2460041 : Blo 968591 2460041 := bstep (se 2 (by rfl) ⟨922515, by rfl⟩ : syracuseStep 2460041 = 1845031) B1845031
theorem B31459859 : Blo 968591 31459859 := bstep (se 1 (by rfl) ⟨23594894, by rfl⟩ : syracuseStep 31459859 = 47189789) B47189789
theorem B16779803 : Blo 968591 16779803 := bstep (se 1 (by rfl) ⟨12584852, by rfl⟩ : syracuseStep 16779803 = 25169705) B25169705
theorem B1641127 : Blo 968591 1641127 := bstep (se 1 (by rfl) ⟨1230845, by rfl⟩ : syracuseStep 1641127 = 2461691) B2461691
theorem B1379143 : Blo 968591 1379143 := bstep (se 1 (by rfl) ⟨1034357, by rfl⟩ : syracuseStep 1379143 = 2068715) B2068715
theorem B3935081 : Blo 968591 3935081 := bstep (se 2 (by rfl) ⟨1475655, by rfl⟩ : syracuseStep 3935081 = 2951311) B2951311
theorem B1379359 : Blo 968591 1379359 := bstep (se 1 (by rfl) ⟨1034519, by rfl⟩ : syracuseStep 1379359 = 2069039) B2069039
theorem B4918967 : Blo 968591 4918967 := bstep (se 1 (by rfl) ⟨3689225, by rfl⟩ : syracuseStep 4918967 = 7378451) B7378451
theorem B65507177 : Blo 968591 65507177 := bstep (se 2 (by rfl) ⟨24565191, by rfl⟩ : syracuseStep 65507177 = 49130383) B49130383
theorem B2330707 : Blo 968591 2330707 := bstep (se 1 (by rfl) ⟨1748030, by rfl⟩ : syracuseStep 2330707 = 3496061) B3496061
theorem B2461823 : Blo 968591 2461823 := bstep (se 1 (by rfl) ⟨1846367, by rfl⟩ : syracuseStep 2461823 = 3692735) B3692735
theorem B1970735 : Blo 968591 1970735 := bstep (se 1 (by rfl) ⟨1478051, by rfl⟩ : syracuseStep 1970735 = 2956103) B2956103
theorem B44864209 : Blo 968591 44864209 := bstep (se 2 (by rfl) ⟨16824078, by rfl⟩ : syracuseStep 44864209 = 33648157) B33648157
theorem B14914529 : Blo 968591 14914529 := bstep (se 2 (by rfl) ⟨5592948, by rfl⟩ : syracuseStep 14914529 = 11185897) B11185897
theorem B1840315 : Blo 968591 1840315 := bstep (se 1 (by rfl) ⟨1380236, by rfl⟩ : syracuseStep 1840315 = 2760473) B2760473
theorem B3282173 : Blo 968591 3282173 := bstep (se 3 (by rfl) ⟨615407, by rfl⟩ : syracuseStep 3282173 = 1230815) B1230815
theorem B3937673 : Blo 968591 3937673 := bstep (se 2 (by rfl) ⟨1476627, by rfl⟩ : syracuseStep 3937673 = 2953255) B2953255
theorem B3315215 : Blo 968591 3315215 := bstep (se 1 (by rfl) ⟨2486411, by rfl⟩ : syracuseStep 3315215 = 4972823) B4972823
theorem B23566087 : Blo 968591 23566087 := bstep (se 1 (by rfl) ⟨17674565, by rfl⟩ : syracuseStep 23566087 = 35349131) B35349131
theorem B5249195 : Blo 968591 5249195 := bstep (se 1 (by rfl) ⟨3936896, by rfl⟩ : syracuseStep 5249195 = 7873793) B7873793
theorem B2333225 : Blo 968591 2333225 := bstep (se 2 (by rfl) ⟨874959, by rfl⟩ : syracuseStep 2333225 = 1749919) B1749919
theorem B1842259 : Blo 968591 1842259 := bstep (se 1 (by rfl) ⟨1381694, by rfl⟩ : syracuseStep 1842259 = 2763389) B2763389
theorem B2759903 : Blo 968591 2759903 := bstep (se 1 (by rfl) ⟨2069927, by rfl⟩ : syracuseStep 2759903 = 4139855) B4139855
theorem B1842601 : Blo 968591 1842601 := bstep (se 2 (by rfl) ⟨690975, by rfl⟩ : syracuseStep 1842601 = 1381951) B1381951
theorem B3317267 : Blo 968591 3317267 := bstep (se 1 (by rfl) ⟨2487950, by rfl⟩ : syracuseStep 3317267 = 4975901) B4975901
theorem B1843307 : Blo 968591 1843307 := bstep (se 1 (by rfl) ⟨1382480, by rfl⟩ : syracuseStep 1843307 = 2764961) B2764961
theorem B3940595 : Blo 968591 3940595 := bstep (se 1 (by rfl) ⟨2955446, by rfl⟩ : syracuseStep 3940595 = 5910893) B5910893
theorem B2957705 : Blo 968591 2957705 := bstep (se 2 (by rfl) ⟨1109139, by rfl⟩ : syracuseStep 2957705 = 2218279) B2218279
theorem B6464225 : Blo 968591 6464225 := bstep (se 2 (by rfl) ⟨2424084, by rfl⟩ : syracuseStep 6464225 = 4848169) B4848169
theorem B28025675 : Blo 968591 28025675 := bstep (se 1 (by rfl) ⟨21019256, by rfl⟩ : syracuseStep 28025675 = 42038513) B42038513
theorem B1844279 : Blo 968591 1844279 := bstep (se 1 (by rfl) ⟨1383209, by rfl⟩ : syracuseStep 1844279 = 2766419) B2766419
theorem B1090651 : Blo 968591 1090651 := bstep (se 1 (by rfl) ⟨817988, by rfl⟩ : syracuseStep 1090651 = 1635977) B1635977
theorem B22423243 : Blo 968591 22423243 := bstep (se 1 (by rfl) ⟨16817432, by rfl⟩ : syracuseStep 22423243 = 33634865) B33634865
theorem B15771449 : Blo 968591 15771449 := bstep (se 2 (by rfl) ⟨5914293, by rfl⟩ : syracuseStep 15771449 = 11828587) B11828587
theorem B18655109 : Blo 968591 18655109 := bstep (se 4 (by rfl) ⟨1748916, by rfl⟩ : syracuseStep 18655109 = 3497833) B3497833
theorem B3680417 : Blo 968591 3680417 := bstep (se 2 (by rfl) ⟨1380156, by rfl⟩ : syracuseStep 3680417 = 2760313) B2760313
theorem B4139207 : Blo 968591 4139207 := bstep (se 1 (by rfl) ⟨3104405, by rfl⟩ : syracuseStep 4139207 = 6208811) B6208811
theorem B6991055 : Blo 968591 6991055 := bstep (se 1 (by rfl) ⟨5243291, by rfl⟩ : syracuseStep 6991055 = 10486583) B10486583
theorem B1453679 : Blo 968591 1453679 := bstep (se 1 (by rfl) ⟨1090259, by rfl⟩ : syracuseStep 1453679 = 2180519) B2180519
theorem B1453787 : Blo 968591 1453787 := bstep (se 1 (by rfl) ⟨1090340, by rfl⟩ : syracuseStep 1453787 = 2180681) B2180681
theorem B1453799 : Blo 968591 1453799 := bstep (se 1 (by rfl) ⟨1090349, by rfl⟩ : syracuseStep 1453799 = 2180699) B2180699
theorem B3682043 : Blo 968591 3682043 := bstep (se 1 (by rfl) ⟨2761532, by rfl⟩ : syracuseStep 3682043 = 5523065) B5523065
theorem B4140881 : Blo 968591 4140881 := bstep (se 2 (by rfl) ⟨1552830, by rfl⟩ : syracuseStep 4140881 = 3105661) B3105661
theorem B4042855 : Blo 968591 4042855 := bstep (se 1 (by rfl) ⟨3032141, by rfl⟩ : syracuseStep 4042855 = 6064283) B6064283
theorem B1454459 : Blo 968591 1454459 := bstep (se 1 (by rfl) ⟨1090844, by rfl⟩ : syracuseStep 1454459 = 2181689) B2181689
theorem B28062125 : Blo 968591 28062125 := bstep (se 3 (by rfl) ⟨5261648, by rfl⟩ : syracuseStep 28062125 = 10523297) B10523297
theorem B1454567 : Blo 968591 1454567 := bstep (se 1 (by rfl) ⟨1090925, by rfl⟩ : syracuseStep 1454567 = 2181851) B2181851
theorem B1454939 : Blo 968591 1454939 := bstep (se 1 (by rfl) ⟨1091204, by rfl⟩ : syracuseStep 1454939 = 2182409) B2182409
theorem B2241503 : Blo 968591 2241503 := bstep (se 1 (by rfl) ⟨1681127, by rfl⟩ : syracuseStep 2241503 = 3362255) B3362255
theorem B1455071 : Blo 968591 1455071 := bstep (se 1 (by rfl) ⟨1091303, by rfl⟩ : syracuseStep 1455071 = 2182607) B2182607
theorem B1455131 : Blo 968591 1455131 := bstep (se 1 (by rfl) ⟨1091348, by rfl⟩ : syracuseStep 1455131 = 2182697) B2182697
theorem B1455599 : Blo 968591 1455599 := bstep (se 1 (by rfl) ⟨1091699, by rfl⟩ : syracuseStep 1455599 = 2183399) B2183399
theorem B4142623 : Blo 968591 4142623 := bstep (se 1 (by rfl) ⟨3106967, by rfl⟩ : syracuseStep 4142623 = 6213935) B6213935
theorem B6993503 : Blo 968591 6993503 := bstep (se 1 (by rfl) ⟨5245127, by rfl⟩ : syracuseStep 6993503 = 10490255) B10490255
theorem B1455719 : Blo 968591 1455719 := bstep (se 1 (by rfl) ⟨1091789, by rfl⟩ : syracuseStep 1455719 = 2183579) B2183579
theorem B20952827 : Blo 968591 20952827 := bstep (se 1 (by rfl) ⟨15714620, by rfl⟩ : syracuseStep 20952827 = 31429241) B31429241
theorem B4143257 : Blo 968591 4143257 := bstep (se 2 (by rfl) ⟨1553721, by rfl⟩ : syracuseStep 4143257 = 3107443) B3107443
theorem B6994745 : Blo 968591 6994745 := bstep (se 2 (by rfl) ⟨2623029, by rfl⟩ : syracuseStep 6994745 = 5246059) B5246059
theorem B3685277 : Blo 968591 3685277 := bstep (se 3 (by rfl) ⟨690989, by rfl⟩ : syracuseStep 3685277 = 1381979) B1381979
theorem B1457435 : Blo 968591 1457435 := bstep (se 1 (by rfl) ⟨1093076, by rfl⟩ : syracuseStep 1457435 = 2186153) B2186153
theorem B11222387 : Blo 968591 11222387 := bstep (se 1 (by rfl) ⟨8416790, by rfl⟩ : syracuseStep 11222387 = 16833581) B16833581
theorem B1458203 : Blo 968591 1458203 := bstep (se 1 (by rfl) ⟨1093652, by rfl⟩ : syracuseStep 1458203 = 2187305) B2187305
theorem B1458473 : Blo 968591 1458473 := bstep (se 2 (by rfl) ⟨546927, by rfl⟩ : syracuseStep 1458473 = 1093855) B1093855
theorem B1458623 : Blo 968591 1458623 := bstep (se 1 (by rfl) ⟨1093967, by rfl⟩ : syracuseStep 1458623 = 2187935) B2187935
theorem B11060387 : Blo 968591 11060387 := bstep (se 1 (by rfl) ⟨8295290, by rfl⟩ : syracuseStep 11060387 = 16590581) B16590581
theorem B3687875 : Blo 968591 3687875 := bstep (se 1 (by rfl) ⟨2765906, by rfl⟩ : syracuseStep 3687875 = 5531813) B5531813
theorem B4146689 : Blo 968591 4146689 := bstep (se 2 (by rfl) ⟨1555008, by rfl⟩ : syracuseStep 4146689 = 3110017) B3110017
theorem B1230491 : Blo 968591 1230491 := bstep (se 1 (by rfl) ⟨922868, by rfl⟩ : syracuseStep 1230491 = 1845737) B1845737
theorem B31475425 : Blo 968591 31475425 := bstep (se 2 (by rfl) ⟨11803284, by rfl⟩ : syracuseStep 31475425 = 23606569) B23606569
theorem B968607 : Blo 968591 968607 := bstep (se 1 (by rfl) ⟨726455, by rfl⟩ : syracuseStep 968607 = 1452911) B1452911
theorem B968775 : Blo 968591 968775 := bstep (se 1 (by rfl) ⟨726581, by rfl⟩ : syracuseStep 968775 = 1453163) B1453163
theorem B968935 : Blo 968591 968935 := bstep (se 1 (by rfl) ⟨726701, by rfl⟩ : syracuseStep 968935 = 1453403) B1453403
theorem B968955 : Blo 968591 968955 := bstep (se 1 (by rfl) ⟨726716, by rfl⟩ : syracuseStep 968955 = 1453433) B1453433
theorem B968959 : Blo 968591 968959 := bstep (se 1 (by rfl) ⟨726719, by rfl⟩ : syracuseStep 968959 = 1453439) B1453439
theorem B16599329 : Blo 968591 16599329 := bstep (se 2 (by rfl) ⟨6224748, by rfl⟩ : syracuseStep 16599329 = 12449497) B12449497
theorem B969115 : Blo 968591 969115 := bstep (se 1 (by rfl) ⟨726836, by rfl⟩ : syracuseStep 969115 = 1453673) B1453673
theorem B969375 : Blo 968591 969375 := bstep (se 1 (by rfl) ⟨727031, by rfl⟩ : syracuseStep 969375 = 1454063) B1454063
theorem B4147919 : Blo 968591 4147919 := bstep (se 1 (by rfl) ⟨3110939, by rfl⟩ : syracuseStep 4147919 = 6221879) B6221879
theorem B969455 : Blo 968591 969455 := bstep (se 1 (by rfl) ⟨727091, by rfl⟩ : syracuseStep 969455 = 1454183) B1454183
theorem B969535 : Blo 968591 969535 := bstep (se 1 (by rfl) ⟨727151, by rfl⟩ : syracuseStep 969535 = 1454303) B1454303
theorem B969575 : Blo 968591 969575 := bstep (se 1 (by rfl) ⟨727181, by rfl⟩ : syracuseStep 969575 = 1454363) B1454363
theorem B969839 : Blo 968591 969839 := bstep (se 1 (by rfl) ⟨727379, by rfl⟩ : syracuseStep 969839 = 1454759) B1454759
theorem B969919 : Blo 968591 969919 := bstep (se 1 (by rfl) ⟨727439, by rfl⟩ : syracuseStep 969919 = 1454879) B1454879
theorem B969935 : Blo 968591 969935 := bstep (se 1 (by rfl) ⟨727451, by rfl⟩ : syracuseStep 969935 = 1454903) B1454903
theorem B970011 : Blo 968591 970011 := bstep (se 1 (by rfl) ⟨727508, by rfl⟩ : syracuseStep 970011 = 1455017) B1455017
theorem B14929181 : Blo 968591 14929181 := bstep (se 3 (by rfl) ⟨2799221, by rfl⟩ : syracuseStep 14929181 = 5598443) B5598443
theorem B970055 : Blo 968591 970055 := bstep (se 1 (by rfl) ⟨727541, by rfl⟩ : syracuseStep 970055 = 1455083) B1455083
theorem B970239 : Blo 968591 970239 := bstep (se 1 (by rfl) ⟨727679, by rfl⟩ : syracuseStep 970239 = 1455359) B1455359
theorem B970267 : Blo 968591 970267 := bstep (se 1 (by rfl) ⟨727700, by rfl⟩ : syracuseStep 970267 = 1455401) B1455401
theorem B3690319 : Blo 968591 3690319 := bstep (se 1 (by rfl) ⟨2767739, by rfl⟩ : syracuseStep 3690319 = 5535479) B5535479
theorem B970663 : Blo 968591 970663 := bstep (se 1 (by rfl) ⟨727997, by rfl⟩ : syracuseStep 970663 = 1455995) B1455995
theorem B970687 : Blo 968591 970687 := bstep (se 1 (by rfl) ⟨728015, by rfl⟩ : syracuseStep 970687 = 1456031) B1456031
theorem B11063303 : Blo 968591 11063303 := bstep (se 1 (by rfl) ⟨8297477, by rfl⟩ : syracuseStep 11063303 = 16594955) B16594955
theorem B970823 : Blo 968591 970823 := bstep (se 1 (by rfl) ⟨728117, by rfl⟩ : syracuseStep 970823 = 1456235) B1456235
theorem B970843 : Blo 968591 970843 := bstep (se 1 (by rfl) ⟨728132, by rfl⟩ : syracuseStep 970843 = 1456265) B1456265
theorem B3690593 : Blo 968591 3690593 := bstep (se 2 (by rfl) ⟨1383972, by rfl⟩ : syracuseStep 3690593 = 2767945) B2767945
theorem B970943 : Blo 968591 970943 := bstep (se 1 (by rfl) ⟨728207, by rfl⟩ : syracuseStep 970943 = 1456415) B1456415
theorem B4149559 : Blo 968591 4149559 := bstep (se 1 (by rfl) ⟨3112169, by rfl⟩ : syracuseStep 4149559 = 6224339) B6224339
theorem B971391 : Blo 968591 971391 := bstep (se 1 (by rfl) ⟨728543, by rfl⟩ : syracuseStep 971391 = 1457087) B1457087
theorem B971423 : Blo 968591 971423 := bstep (se 1 (by rfl) ⟨728567, by rfl⟩ : syracuseStep 971423 = 1457135) B1457135
theorem B971547 : Blo 968591 971547 := bstep (se 1 (by rfl) ⟨728660, by rfl⟩ : syracuseStep 971547 = 1457321) B1457321
theorem B971807 : Blo 968591 971807 := bstep (se 1 (by rfl) ⟨728855, by rfl⟩ : syracuseStep 971807 = 1457711) B1457711
theorem B971823 : Blo 968591 971823 := bstep (se 1 (by rfl) ⟨728867, by rfl⟩ : syracuseStep 971823 = 1457735) B1457735
theorem B971879 : Blo 968591 971879 := bstep (se 1 (by rfl) ⟨728909, by rfl⟩ : syracuseStep 971879 = 1457819) B1457819
theorem B971943 : Blo 968591 971943 := bstep (se 1 (by rfl) ⟨728957, by rfl⟩ : syracuseStep 971943 = 1457915) B1457915
theorem B972255 : Blo 968591 972255 := bstep (se 1 (by rfl) ⟨729191, by rfl⟩ : syracuseStep 972255 = 1458383) B1458383
theorem B7362899 : Blo 968591 7362899 := bstep (se 1 (by rfl) ⟨5522174, by rfl⟩ : syracuseStep 7362899 = 11044349) B11044349
theorem B2185991 : Blo 968591 2185991 := bstep (se 1 (by rfl) ⟨1639493, by rfl⟩ : syracuseStep 2185991 = 3278987) B3278987
theorem B70114139 : Blo 968591 70114139 := bstep (se 1 (by rfl) ⟨52585604, by rfl⟩ : syracuseStep 70114139 = 105171209) B105171209
theorem B9100775 : Blo 968591 9100775 := bstep (se 1 (by rfl) ⟨6825581, by rfl⟩ : syracuseStep 9100775 = 13651163) B13651163
theorem B2187071 : Blo 968591 2187071 := bstep (se 1 (by rfl) ⟨1640303, by rfl⟩ : syracuseStep 2187071 = 3280607) B3280607
theorem B2187359 : Blo 968591 2187359 := bstep (se 1 (by rfl) ⟨1640519, by rfl⟩ : syracuseStep 2187359 = 3281039) B3281039
theorem B16573085 : Blo 968591 16573085 := bstep (se 3 (by rfl) ⟨3107453, by rfl⟩ : syracuseStep 16573085 = 6214907) B6214907
theorem B9331361 : Blo 968591 9331361 := bstep (se 2 (by rfl) ⟨3499260, by rfl⟩ : syracuseStep 9331361 = 6998521) B6998521
theorem B4908113 : Blo 968591 4908113 := bstep (se 2 (by rfl) ⟨1840542, by rfl⟩ : syracuseStep 4908113 = 3681085) B3681085
theorem B3269753 : Blo 968591 3269753 := bstep (se 2 (by rfl) ⟨1226157, by rfl⟩ : syracuseStep 3269753 = 2452315) B2452315
theorem B3269807 : Blo 968591 3269807 := bstep (se 1 (by rfl) ⟨2452355, by rfl⟩ : syracuseStep 3269807 = 4904711) B4904711
theorem B7005611 : Blo 968591 7005611 := bstep (se 1 (by rfl) ⟨5254208, by rfl⟩ : syracuseStep 7005611 = 10508417) B10508417
theorem B21030671 : Blo 968591 21030671 := bstep (se 1 (by rfl) ⟨15773003, by rfl⟩ : syracuseStep 21030671 = 31546007) B31546007
theorem B25224995 : Blo 968591 25224995 := bstep (se 1 (by rfl) ⟨18918746, by rfl⟩ : syracuseStep 25224995 = 37837493) B37837493
theorem B27944939 : Blo 968591 27944939 := bstep (se 1 (by rfl) ⟨20958704, by rfl⟩ : syracuseStep 27944939 = 41917409) B41917409
theorem B3270887 : Blo 968591 3270887 := bstep (se 1 (by rfl) ⟨2453165, by rfl⟩ : syracuseStep 3270887 = 4906331) B4906331
theorem B3271535 : Blo 968591 3271535 := bstep (se 1 (by rfl) ⟨2453651, by rfl⟩ : syracuseStep 3271535 = 4907303) B4907303
theorem B3271751 : Blo 968591 3271751 := bstep (se 1 (by rfl) ⟨2453813, by rfl⟩ : syracuseStep 3271751 = 4907627) B4907627
theorem B8285449 : Blo 968591 8285449 := bstep (se 2 (by rfl) ⟨3107043, by rfl⟩ : syracuseStep 8285449 = 6214087) B6214087
theorem B6647123 : Blo 968591 6647123 := bstep (se 1 (by rfl) ⟨4985342, by rfl⟩ : syracuseStep 6647123 = 9970685) B9970685
theorem B3272831 : Blo 968591 3272831 := bstep (se 1 (by rfl) ⟨2454623, by rfl⟩ : syracuseStep 3272831 = 4909247) B4909247
theorem B8286407 : Blo 968591 8286407 := bstep (se 1 (by rfl) ⟨6214805, by rfl⟩ : syracuseStep 8286407 = 12429611) B12429611
theorem B15757577 : Blo 968591 15757577 := bstep (se 2 (by rfl) ⟨5909091, by rfl⟩ : syracuseStep 15757577 = 11818183) B11818183
theorem B2453915 : Blo 968591 2453915 := bstep (se 1 (by rfl) ⟨1840436, by rfl⟩ : syracuseStep 2453915 = 3680873) B3680873
theorem B7008727 : Blo 968591 7008727 := bstep (se 1 (by rfl) ⟨5256545, by rfl⟩ : syracuseStep 7008727 = 10513091) B10513091
theorem B1634843 : Blo 968591 1634843 := bstep (se 1 (by rfl) ⟨1226132, by rfl⟩ : syracuseStep 1634843 = 2452265) B2452265
theorem B4485739 : Blo 968591 4485739 := bstep (se 1 (by rfl) ⟨3364304, by rfl⟩ : syracuseStep 4485739 = 6728609) B6728609
theorem B3503369 : Blo 968591 3503369 := bstep (se 2 (by rfl) ⟨1313763, by rfl⟩ : syracuseStep 3503369 = 2627527) B2627527
theorem B1635815 : Blo 968591 1635815 := bstep (se 1 (by rfl) ⟨1226861, by rfl⟩ : syracuseStep 1635815 = 2453723) B2453723
theorem B4912811 : Blo 968591 4912811 := bstep (se 1 (by rfl) ⟨3684608, by rfl⟩ : syracuseStep 4912811 = 7369217) B7369217
theorem B3274667 : Blo 968591 3274667 := bstep (se 1 (by rfl) ⟨2456000, by rfl⟩ : syracuseStep 3274667 = 4912001) B4912001
theorem B3274721 : Blo 968591 3274721 := bstep (se 2 (by rfl) ⟨1228020, by rfl⟩ : syracuseStep 3274721 = 2456041) B2456041
theorem B1636571 : Blo 968591 1636571 := bstep (se 1 (by rfl) ⟨1227428, by rfl⟩ : syracuseStep 1636571 = 2454857) B2454857
theorem B3275423 : Blo 968591 3275423 := bstep (se 1 (by rfl) ⟨2456567, by rfl⟩ : syracuseStep 3275423 = 4913135) B4913135
theorem B3930911 : Blo 968591 3930911 := bstep (se 1 (by rfl) ⟨2948183, by rfl⟩ : syracuseStep 3930911 = 5896367) B5896367
theorem B5536937 : Blo 968591 5536937 := bstep (se 2 (by rfl) ⟨2076351, by rfl⟩ : syracuseStep 5536937 = 4152703) B4152703
theorem B5537119 : Blo 968591 5537119 := bstep (se 1 (by rfl) ⟨4152839, by rfl⟩ : syracuseStep 5537119 = 8305679) B8305679
theorem B3276665 : Blo 968591 3276665 := bstep (se 2 (by rfl) ⟨1228749, by rfl⟩ : syracuseStep 3276665 = 2457499) B2457499
theorem B6225979 : Blo 968591 6225979 := bstep (se 1 (by rfl) ⟨4669484, by rfl⟩ : syracuseStep 6225979 = 9338969) B9338969
theorem B3736111 : Blo 968591 3736111 := bstep (se 1 (by rfl) ⟨2802083, by rfl⟩ : syracuseStep 3736111 = 5604167) B5604167
theorem B1639163 : Blo 968591 1639163 := bstep (se 1 (by rfl) ⟨1229372, by rfl⟩ : syracuseStep 1639163 = 2458745) B2458745
theorem B7373591 : Blo 968591 7373591 := bstep (se 1 (by rfl) ⟨5530193, by rfl⟩ : syracuseStep 7373591 = 11060387) B11060387
theorem B2458583 : Blo 968591 2458583 := bstep (se 1 (by rfl) ⟨1843937, by rfl⟩ : syracuseStep 2458583 = 3687875) B3687875
theorem B19923965 : Blo 968591 19923965 := bstep (se 3 (by rfl) ⟨3735743, by rfl⟩ : syracuseStep 19923965 = 7471487) B7471487
theorem B3277907 : Blo 968591 3277907 := bstep (se 1 (by rfl) ⟨2458430, by rfl⟩ : syracuseStep 3277907 = 4916861) B4916861
theorem B1640027 : Blo 968591 1640027 := bstep (se 1 (by rfl) ⟨1230020, by rfl⟩ : syracuseStep 1640027 = 2460041) B2460041
theorem B20973239 : Blo 968591 20973239 := bstep (se 1 (by rfl) ⟨15729929, by rfl⟩ : syracuseStep 20973239 = 31459859) B31459859
theorem B2623387 : Blo 968591 2623387 := bstep (se 1 (by rfl) ⟨1967540, by rfl⟩ : syracuseStep 2623387 = 3935081) B3935081
theorem B17237933 : Blo 968591 17237933 := bstep (se 3 (by rfl) ⟨3232112, by rfl⟩ : syracuseStep 17237933 = 6464225) B6464225
theorem B3279311 : Blo 968591 3279311 := bstep (se 1 (by rfl) ⟨2459483, by rfl⟩ : syracuseStep 3279311 = 4918967) B4918967
theorem B7375535 : Blo 968591 7375535 := bstep (se 1 (by rfl) ⟨5531651, by rfl⟩ : syracuseStep 7375535 = 11063303) B11063303
theorem B2460395 : Blo 968591 2460395 := bstep (se 1 (by rfl) ⟨1845296, by rfl⟩ : syracuseStep 2460395 = 3690593) B3690593
theorem B1641215 : Blo 968591 1641215 := bstep (se 1 (by rfl) ⟨1230911, by rfl⟩ : syracuseStep 1641215 = 2461823) B2461823
theorem B9342317 : Blo 968591 9342317 := bstep (se 3 (by rfl) ⟨1751684, by rfl⟩ : syracuseStep 9342317 = 3503369) B3503369
theorem B1838857 : Blo 968591 1838857 := bstep (se 2 (by rfl) ⟨689571, by rfl⟩ : syracuseStep 1838857 = 1379143) B1379143
theorem B11047265 : Blo 968591 11047265 := bstep (se 2 (by rfl) ⟨4142724, by rfl⟩ : syracuseStep 11047265 = 8285449) B8285449
theorem B3281309 : Blo 968591 3281309 := bstep (se 3 (by rfl) ⟨615245, by rfl⟩ : syracuseStep 3281309 = 1230491) B1230491
theorem B1839935 : Blo 968591 1839935 := bstep (se 1 (by rfl) ⟨1379951, by rfl⟩ : syracuseStep 1839935 = 2759903) B2759903
theorem B6067183 : Blo 968591 6067183 := bstep (se 1 (by rfl) ⟨4550387, by rfl⟩ : syracuseStep 6067183 = 9100775) B9100775
theorem B4920425 : Blo 968591 4920425 := bstep (se 2 (by rfl) ⟨1845159, by rfl⟩ : syracuseStep 4920425 = 3690319) B3690319
theorem B2627063 : Blo 968591 2627063 := bstep (se 1 (by rfl) ⟨1970297, by rfl⟩ : syracuseStep 2627063 = 3940595) B3940595
theorem B1971803 : Blo 968591 1971803 := bstep (se 1 (by rfl) ⟨1478852, by rfl⟩ : syracuseStep 1971803 = 2957705) B2957705
theorem B11048723 : Blo 968591 11048723 := bstep (se 1 (by rfl) ⟨8286542, by rfl⟩ : syracuseStep 11048723 = 16573085) B16573085
theorem B18683783 : Blo 968591 18683783 := bstep (se 1 (by rfl) ⟨14012837, by rfl⟩ : syracuseStep 18683783 = 28025675) B28025675
theorem B9344969 : Blo 968591 9344969 := bstep (se 2 (by rfl) ⟨3504363, by rfl⟩ : syracuseStep 9344969 = 7008727) B7008727
theorem B9967981 : Blo 968591 9967981 := bstep (se 3 (by rfl) ⟨1868996, by rfl⟩ : syracuseStep 9967981 = 3737993) B3737993
theorem B16816663 : Blo 968591 16816663 := bstep (se 1 (by rfl) ⟨12612497, by rfl⟩ : syracuseStep 16816663 = 25224995) B25224995
theorem B2759471 : Blo 968591 2759471 := bstep (se 1 (by rfl) ⟨2069603, by rfl⟩ : syracuseStep 2759471 = 4139207) B4139207
theorem B4660703 : Blo 968591 4660703 := bstep (se 1 (by rfl) ⟨3495527, by rfl⟩ : syracuseStep 4660703 = 6991055) B6991055
theorem B4431415 : Blo 968591 4431415 := bstep (se 1 (by rfl) ⟨3323561, by rfl⟩ : syracuseStep 4431415 = 6647123) B6647123
theorem B2760587 : Blo 968591 2760587 := bstep (se 1 (by rfl) ⟨2070440, by rfl⟩ : syracuseStep 2760587 = 4140881) B4140881
theorem B1089895 : Blo 968591 1089895 := bstep (se 1 (by rfl) ⟨817421, by rfl⟩ : syracuseStep 1089895 = 1634843) B1634843
theorem B1090543 : Blo 968591 1090543 := bstep (se 1 (by rfl) ⟨817907, by rfl⟩ : syracuseStep 1090543 = 1635815) B1635815
theorem B4662335 : Blo 968591 4662335 := bstep (se 1 (by rfl) ⟨3496751, by rfl⟩ : syracuseStep 4662335 = 6993503) B6993503
theorem B13968551 : Blo 968591 13968551 := bstep (se 1 (by rfl) ⟨10476413, by rfl⟩ : syracuseStep 13968551 = 20952827) B20952827
theorem B2762171 : Blo 968591 2762171 := bstep (se 1 (by rfl) ⟨2071628, by rfl⟩ : syracuseStep 2762171 = 4143257) B4143257
theorem B1091047 : Blo 968591 1091047 := bstep (se 1 (by rfl) ⟨818285, by rfl⟩ : syracuseStep 1091047 = 1636571) B1636571
theorem B7382825 : Blo 968591 7382825 := bstep (se 2 (by rfl) ⟨2768559, by rfl⟩ : syracuseStep 7382825 = 5537119) B5537119
theorem B4663163 : Blo 968591 4663163 := bstep (se 1 (by rfl) ⟨3497372, by rfl⟩ : syracuseStep 4663163 = 6994745) B6994745
theorem B7481591 : Blo 968591 7481591 := bstep (se 1 (by rfl) ⟨5611193, by rfl⟩ : syracuseStep 7481591 = 11222387) B11222387
theorem B2764459 : Blo 968591 2764459 := bstep (se 1 (by rfl) ⟨2073344, by rfl⟩ : syracuseStep 2764459 = 4146689) B4146689
theorem B1454201 : Blo 968591 1454201 := bstep (se 2 (by rfl) ⟨545325, by rfl⟩ : syracuseStep 1454201 = 1090651) B1090651
theorem B5255293 : Blo 968591 5255293 := bstep (se 3 (by rfl) ⟨985367, by rfl⟩ : syracuseStep 5255293 = 1970735) B1970735
theorem B2765279 : Blo 968591 2765279 := bstep (se 1 (by rfl) ⟨2073959, by rfl⟩ : syracuseStep 2765279 = 4147919) B4147919
theorem B29897657 : Blo 968591 29897657 := bstep (se 2 (by rfl) ⟨11211621, by rfl⟩ : syracuseStep 29897657 = 22423243) B22423243
theorem B5682113 : Blo 968591 5682113 := bstep (se 2 (by rfl) ⟨2130792, by rfl⟩ : syracuseStep 5682113 = 4261585) B4261585
theorem B9943019 : Blo 968591 9943019 := bstep (se 1 (by rfl) ⟨7457264, by rfl⟩ : syracuseStep 9943019 = 14914529) B14914529
theorem B10500461 : Blo 968591 10500461 := bstep (se 3 (by rfl) ⟨1968836, by rfl⟩ : syracuseStep 10500461 = 3937673) B3937673
theorem B1457327 : Blo 968591 1457327 := bstep (se 1 (by rfl) ⟨1092995, by rfl⟩ : syracuseStep 1457327 = 2185991) B2185991
theorem B46742759 : Blo 968591 46742759 := bstep (se 1 (by rfl) ⟨35057069, by rfl⟩ : syracuseStep 46742759 = 70114139) B70114139
theorem B2211511 : Blo 968591 2211511 := bstep (se 1 (by rfl) ⟨1658633, by rfl⟩ : syracuseStep 2211511 = 3317267) B3317267
theorem B1458047 : Blo 968591 1458047 := bstep (se 1 (by rfl) ⟨1093535, by rfl⟩ : syracuseStep 1458047 = 2187071) B2187071
theorem B1458239 : Blo 968591 1458239 := bstep (se 1 (by rfl) ⟨1093679, by rfl⟩ : syracuseStep 1458239 = 2187359) B2187359
theorem B1228871 : Blo 968591 1228871 := bstep (se 1 (by rfl) ⟨921653, by rfl⟩ : syracuseStep 1228871 = 1843307) B1843307
theorem B5390473 : Blo 968591 5390473 := bstep (se 2 (by rfl) ⟨2021427, by rfl⟩ : syracuseStep 5390473 = 4042855) B4042855
theorem B7356581 : Blo 968591 7356581 := bstep (se 4 (by rfl) ⟨689679, by rfl⟩ : syracuseStep 7356581 = 1379359) B1379359
theorem B1229519 : Blo 968591 1229519 := bstep (se 1 (by rfl) ⟨922139, by rfl⟩ : syracuseStep 1229519 = 1844279) B1844279
theorem B2179835 : Blo 968591 2179835 := bstep (se 1 (by rfl) ⟨1634876, by rfl⟩ : syracuseStep 2179835 = 3269753) B3269753
theorem B2179871 : Blo 968591 2179871 := bstep (se 1 (by rfl) ⟨1634903, by rfl⟩ : syracuseStep 2179871 = 3269807) B3269807
theorem B5980985 : Blo 968591 5980985 := bstep (se 2 (by rfl) ⟨2242869, by rfl⟩ : syracuseStep 5980985 = 4485739) B4485739
theorem B59818945 : Blo 968591 59818945 := bstep (se 2 (by rfl) ⟨22432104, by rfl⟩ : syracuseStep 59818945 = 44864209) B44864209
theorem B4670407 : Blo 968591 4670407 := bstep (se 1 (by rfl) ⟨3502805, by rfl⟩ : syracuseStep 4670407 = 7005611) B7005611
theorem B12436739 : Blo 968591 12436739 := bstep (se 1 (by rfl) ⟨9327554, by rfl⟩ : syracuseStep 12436739 = 18655109) B18655109
theorem B18629959 : Blo 968591 18629959 := bstep (se 1 (by rfl) ⟨13972469, by rfl⟩ : syracuseStep 18629959 = 27944939) B27944939
theorem B44746141 : Blo 968591 44746141 := bstep (se 3 (by rfl) ⟨8389901, by rfl⟩ : syracuseStep 44746141 = 16779803) B16779803
theorem B2180591 : Blo 968591 2180591 := bstep (se 1 (by rfl) ⟨1635443, by rfl⟩ : syracuseStep 2180591 = 3270887) B3270887
theorem B2181023 : Blo 968591 2181023 := bstep (se 1 (by rfl) ⟨1635767, by rfl⟩ : syracuseStep 2181023 = 3271535) B3271535
theorem B5523497 : Blo 968591 5523497 := bstep (se 2 (by rfl) ⟨2071311, by rfl⟩ : syracuseStep 5523497 = 4142623) B4142623
theorem B2181167 : Blo 968591 2181167 := bstep (se 1 (by rfl) ⟨1635875, by rfl⟩ : syracuseStep 2181167 = 3271751) B3271751
theorem B969119 : Blo 968591 969119 := bstep (se 1 (by rfl) ⟨726839, by rfl⟩ : syracuseStep 969119 = 1453679) B1453679
theorem B969191 : Blo 968591 969191 := bstep (se 1 (by rfl) ⟨726893, by rfl⟩ : syracuseStep 969191 = 1453787) B1453787
theorem B969199 : Blo 968591 969199 := bstep (se 1 (by rfl) ⟨726899, by rfl⟩ : syracuseStep 969199 = 1453799) B1453799
theorem B2181887 : Blo 968591 2181887 := bstep (se 1 (by rfl) ⟨1636415, by rfl⟩ : syracuseStep 2181887 = 3272831) B3272831
theorem B5524271 : Blo 968591 5524271 := bstep (se 1 (by rfl) ⟨4143203, by rfl⟩ : syracuseStep 5524271 = 8286407) B8286407
theorem B10505051 : Blo 968591 10505051 := bstep (se 1 (by rfl) ⟨7878788, by rfl⟩ : syracuseStep 10505051 = 15757577) B15757577
theorem B969639 : Blo 968591 969639 := bstep (se 1 (by rfl) ⟨727229, by rfl⟩ : syracuseStep 969639 = 1454459) B1454459
theorem B969711 : Blo 968591 969711 := bstep (se 1 (by rfl) ⟨727283, by rfl⟩ : syracuseStep 969711 = 1454567) B1454567
theorem B969959 : Blo 968591 969959 := bstep (se 1 (by rfl) ⟨727469, by rfl⟩ : syracuseStep 969959 = 1454939) B1454939
theorem B1494335 : Blo 968591 1494335 := bstep (se 1 (by rfl) ⟨1120751, by rfl⟩ : syracuseStep 1494335 = 2241503) B2241503
theorem B970047 : Blo 968591 970047 := bstep (se 1 (by rfl) ⟨727535, by rfl⟩ : syracuseStep 970047 = 1455071) B1455071
theorem B970087 : Blo 968591 970087 := bstep (se 1 (by rfl) ⟨727565, by rfl⟩ : syracuseStep 970087 = 1455131) B1455131
theorem B970399 : Blo 968591 970399 := bstep (se 1 (by rfl) ⟨727799, by rfl⟩ : syracuseStep 970399 = 1455599) B1455599
theorem B970479 : Blo 968591 970479 := bstep (se 1 (by rfl) ⟨727859, by rfl⟩ : syracuseStep 970479 = 1455719) B1455719
theorem B2183111 : Blo 968591 2183111 := bstep (se 1 (by rfl) ⟨1637333, by rfl⟩ : syracuseStep 2183111 = 3274667) B3274667
theorem B2183147 : Blo 968591 2183147 := bstep (se 1 (by rfl) ⟨1637360, by rfl⟩ : syracuseStep 2183147 = 3274721) B3274721
theorem B2183615 : Blo 968591 2183615 := bstep (se 1 (by rfl) ⟨1637711, by rfl⟩ : syracuseStep 2183615 = 3275423) B3275423
theorem B3691291 : Blo 968591 3691291 := bstep (se 1 (by rfl) ⟨2768468, by rfl⟩ : syracuseStep 3691291 = 5536937) B5536937
theorem B971623 : Blo 968591 971623 := bstep (se 1 (by rfl) ⟨728717, by rfl⟩ : syracuseStep 971623 = 1457435) B1457435
theorem B2184443 : Blo 968591 2184443 := bstep (se 1 (by rfl) ⟨1638332, by rfl⟩ : syracuseStep 2184443 = 3276665) B3276665
theorem B972135 : Blo 968591 972135 := bstep (se 1 (by rfl) ⟨729101, by rfl⟩ : syracuseStep 972135 = 1458203) B1458203
theorem B3692051 : Blo 968591 3692051 := bstep (se 1 (by rfl) ⟨2769038, by rfl⟩ : syracuseStep 3692051 = 5538077) B5538077
theorem B972315 : Blo 968591 972315 := bstep (se 1 (by rfl) ⟨729236, by rfl⟩ : syracuseStep 972315 = 1458473) B1458473
theorem B972415 : Blo 968591 972415 := bstep (se 1 (by rfl) ⟨729311, by rfl⟩ : syracuseStep 972415 = 1458623) B1458623
theorem B4151047 : Blo 968591 4151047 := bstep (se 1 (by rfl) ⟨3113285, by rfl⟩ : syracuseStep 4151047 = 6226571) B6226571
theorem B8869985 : Blo 968591 8869985 := bstep (se 2 (by rfl) ⟨3326244, by rfl⟩ : syracuseStep 8869985 = 6652489) B6652489
theorem B5593319 : Blo 968591 5593319 := bstep (se 1 (by rfl) ⟨4194989, by rfl⟩ : syracuseStep 5593319 = 8389979) B8389979
theorem B2185451 : Blo 968591 2185451 := bstep (se 1 (by rfl) ⟨1639088, by rfl⟩ : syracuseStep 2185451 = 3278177) B3278177
theorem B2185721 : Blo 968591 2185721 := bstep (se 2 (by rfl) ⟨819645, by rfl⟩ : syracuseStep 2185721 = 1639291) B1639291
theorem B3496463 : Blo 968591 3496463 := bstep (se 1 (by rfl) ⟨2622347, by rfl⟩ : syracuseStep 3496463 = 5244695) B5244695
theorem B11066219 : Blo 968591 11066219 := bstep (se 1 (by rfl) ⟨8299664, by rfl⟩ : syracuseStep 11066219 = 16599329) B16599329
theorem B9952787 : Blo 968591 9952787 := bstep (se 1 (by rfl) ⟨7464590, by rfl⟩ : syracuseStep 9952787 = 14929181) B14929181
theorem B41967233 : Blo 968591 41967233 := bstep (se 2 (by rfl) ⟨15737712, by rfl⟩ : syracuseStep 41967233 = 31475425) B31475425
theorem B2188115 : Blo 968591 2188115 := bstep (se 1 (by rfl) ⟨1641086, by rfl⟩ : syracuseStep 2188115 = 3282173) B3282173
theorem B2188169 : Blo 968591 2188169 := bstep (se 2 (by rfl) ⟨820563, by rfl⟩ : syracuseStep 2188169 = 1641127) B1641127
theorem B8840573 : Blo 968591 8840573 := bstep (se 3 (by rfl) ⟨1657607, by rfl⟩ : syracuseStep 8840573 = 3315215) B3315215
theorem B3499463 : Blo 968591 3499463 := bstep (se 1 (by rfl) ⟨2624597, by rfl⟩ : syracuseStep 3499463 = 5249195) B5249195
theorem B4908599 : Blo 968591 4908599 := bstep (se 1 (by rfl) ⟨3681449, by rfl⟩ : syracuseStep 4908599 = 7362899) B7362899
theorem B3107609 : Blo 968591 3107609 := bstep (se 2 (by rfl) ⟨1165353, by rfl⟩ : syracuseStep 3107609 = 2330707) B2330707
theorem B5532745 : Blo 968591 5532745 := bstep (se 2 (by rfl) ⟨2074779, by rfl⟩ : syracuseStep 5532745 = 4149559) B4149559
theorem B6220907 : Blo 968591 6220907 := bstep (se 1 (by rfl) ⟨4665680, by rfl⟩ : syracuseStep 6220907 = 9331361) B9331361
theorem B3272075 : Blo 968591 3272075 := bstep (se 1 (by rfl) ⟨2454056, by rfl⟩ : syracuseStep 3272075 = 4908113) B4908113
theorem B14020447 : Blo 968591 14020447 := bstep (se 1 (by rfl) ⟨10515335, by rfl⟩ : syracuseStep 14020447 = 21030671) B21030671
theorem B10514299 : Blo 968591 10514299 := bstep (se 1 (by rfl) ⟨7885724, by rfl⟩ : syracuseStep 10514299 = 15771449) B15771449
theorem B2453611 : Blo 968591 2453611 := bstep (se 1 (by rfl) ⟨1840208, by rfl⟩ : syracuseStep 2453611 = 3680417) B3680417
theorem B6221933 : Blo 968591 6221933 := bstep (se 3 (by rfl) ⟨1166612, by rfl⟩ : syracuseStep 6221933 = 2333225) B2333225
theorem B2453753 : Blo 968591 2453753 := bstep (se 2 (by rfl) ⟨920157, by rfl⟩ : syracuseStep 2453753 = 1840315) B1840315
theorem B31421449 : Blo 968591 31421449 := bstep (se 2 (by rfl) ⟨11783043, by rfl⟩ : syracuseStep 31421449 = 23566087) B23566087
theorem B2454695 : Blo 968591 2454695 := bstep (se 1 (by rfl) ⟨1841021, by rfl⟩ : syracuseStep 2454695 = 3682043) B3682043
theorem B1635943 : Blo 968591 1635943 := bstep (se 1 (by rfl) ⟨1226957, by rfl⟩ : syracuseStep 1635943 = 2453915) B2453915
theorem B18708083 : Blo 968591 18708083 := bstep (se 1 (by rfl) ⟨14031062, by rfl⟩ : syracuseStep 18708083 = 28062125) B28062125
theorem B3275207 : Blo 968591 3275207 := bstep (se 1 (by rfl) ⟨2456405, by rfl⟩ : syracuseStep 3275207 = 4912811) B4912811
theorem B2456345 : Blo 968591 2456345 := bstep (se 2 (by rfl) ⟨921129, by rfl⟩ : syracuseStep 2456345 = 1842259) B1842259
theorem B2620607 : Blo 968591 2620607 := bstep (se 1 (by rfl) ⟨1965455, by rfl⟩ : syracuseStep 2620607 = 3930911) B3930911
theorem B2456801 : Blo 968591 2456801 := bstep (se 2 (by rfl) ⟨921300, by rfl⟩ : syracuseStep 2456801 = 1842601) B1842601
theorem B2456851 : Blo 968591 2456851 := bstep (se 1 (by rfl) ⟨1842638, by rfl⟩ : syracuseStep 2456851 = 3685277) B3685277
theorem B174685805 : Blo 968591 174685805 := bstep (se 3 (by rfl) ⟨32753588, by rfl⟩ : syracuseStep 174685805 = 65507177) B65507177
theorem B3276989 : Blo 968591 3276989 := bstep (se 3 (by rfl) ⟨614435, by rfl⟩ : syracuseStep 3276989 = 1228871) B1228871
theorem B4915727 : Blo 968591 4915727 := bstep (se 1 (by rfl) ⟨3686795, by rfl⟩ : syracuseStep 4915727 = 7373591) B7373591
theorem B1639055 : Blo 968591 1639055 := bstep (se 1 (by rfl) ⟨1229291, by rfl⟩ : syracuseStep 1639055 = 2458583) B2458583
theorem B4981481 : Blo 968591 4981481 := bstep (se 2 (by rfl) ⟨1868055, by rfl⟩ : syracuseStep 4981481 = 3736111) B3736111
theorem B8291159 : Blo 968591 8291159 := bstep (se 1 (by rfl) ⟨6218369, by rfl⟩ : syracuseStep 8291159 = 12436739) B12436739
theorem B7374077 : Blo 968591 7374077 := bstep (se 3 (by rfl) ⟨1382639, by rfl⟩ : syracuseStep 7374077 = 2765279) B2765279
theorem B79758593 : Blo 968591 79758593 := bstep (se 2 (by rfl) ⟨29909472, by rfl⟩ : syracuseStep 79758593 = 59818945) B59818945
theorem B6227209 : Blo 968591 6227209 := bstep (se 2 (by rfl) ⟨2335203, by rfl⟩ : syracuseStep 6227209 = 4670407) B4670407
theorem B24839945 : Blo 968591 24839945 := bstep (se 2 (by rfl) ⟨9314979, by rfl⟩ : syracuseStep 24839945 = 18629959) B18629959
theorem B4917023 : Blo 968591 4917023 := bstep (se 1 (by rfl) ⟨3687767, by rfl⟩ : syracuseStep 4917023 = 7375535) B7375535
theorem B1640263 : Blo 968591 1640263 := bstep (se 1 (by rfl) ⟨1230197, by rfl⟩ : syracuseStep 1640263 = 2460395) B2460395
theorem B3278717 : Blo 968591 3278717 := bstep (se 3 (by rfl) ⟨614759, by rfl⟩ : syracuseStep 3278717 = 1229519) B1229519
theorem B6228211 : Blo 968591 6228211 := bstep (se 1 (by rfl) ⟨4671158, by rfl⟩ : syracuseStep 6228211 = 9342317) B9342317
theorem B89688869 : Blo 968591 89688869 := bstep (se 4 (by rfl) ⟨8408331, by rfl⟩ : syracuseStep 89688869 = 16816663) B16816663
theorem B3280283 : Blo 968591 3280283 := bstep (se 1 (by rfl) ⟨2460212, by rfl⟩ : syracuseStep 3280283 = 4920425) B4920425
theorem B2461367 : Blo 968591 2461367 := bstep (se 1 (by rfl) ⟨1846025, by rfl⟩ : syracuseStep 2461367 = 3692051) B3692051
theorem B12455855 : Blo 968591 12455855 := bstep (se 1 (by rfl) ⟨9341891, by rfl⟩ : syracuseStep 12455855 = 18683783) B18683783
theorem B6229979 : Blo 968591 6229979 := bstep (se 1 (by rfl) ⟨4672484, by rfl⟩ : syracuseStep 6229979 = 9344969) B9344969
theorem B7376993 : Blo 968591 7376993 := bstep (se 2 (by rfl) ⟨2766372, by rfl⟩ : syracuseStep 7376993 = 5532745) B5532745
theorem B2330975 : Blo 968591 2330975 := bstep (se 1 (by rfl) ⟨1748231, by rfl⟩ : syracuseStep 2330975 = 3496463) B3496463
theorem B1839647 : Blo 968591 1839647 := bstep (se 1 (by rfl) ⟨1379735, by rfl⟩ : syracuseStep 1839647 = 2759471) B2759471
theorem B7377479 : Blo 968591 7377479 := bstep (se 1 (by rfl) ⟨5533109, by rfl⟩ : syracuseStep 7377479 = 11066219) B11066219
theorem B1840391 : Blo 968591 1840391 := bstep (se 1 (by rfl) ⟨1380293, by rfl⟩ : syracuseStep 1840391 = 2760587) B2760587
theorem B9312367 : Blo 968591 9312367 := bstep (se 1 (by rfl) ⟨6984275, by rfl⟩ : syracuseStep 9312367 = 13968551) B13968551
theorem B1841447 : Blo 968591 1841447 := bstep (se 1 (by rfl) ⟨1381085, by rfl⟩ : syracuseStep 1841447 = 2762171) B2762171
theorem B2332975 : Blo 968591 2332975 := bstep (se 1 (by rfl) ⟨1749731, by rfl⟩ : syracuseStep 2332975 = 3499463) B3499463
theorem B4921721 : Blo 968591 4921721 := bstep (se 2 (by rfl) ⟨1845645, by rfl⟩ : syracuseStep 4921721 = 3691291) B3691291
theorem B4921883 : Blo 968591 4921883 := bstep (se 1 (by rfl) ⟨3691412, by rfl⟩ : syracuseStep 4921883 = 7382825) B7382825
theorem B4987727 : Blo 968591 4987727 := bstep (se 1 (by rfl) ⟨3740795, by rfl⟩ : syracuseStep 4987727 = 7481591) B7481591
theorem B2071739 : Blo 968591 2071739 := bstep (se 1 (by rfl) ⟨1553804, by rfl⟩ : syracuseStep 2071739 = 3107609) B3107609
theorem B6988285 : Blo 968591 6988285 := bstep (se 3 (by rfl) ⟨1310303, by rfl⟩ : syracuseStep 6988285 = 2620607) B2620607
theorem B19931771 : Blo 968591 19931771 := bstep (se 1 (by rfl) ⟨14948828, by rfl⟩ : syracuseStep 19931771 = 29897657) B29897657
theorem B6628679 : Blo 968591 6628679 := bstep (se 1 (by rfl) ⟨4971509, by rfl⟩ : syracuseStep 6628679 = 9943019) B9943019
theorem B5908553 : Blo 968591 5908553 := bstep (se 2 (by rfl) ⟨2215707, by rfl⟩ : syracuseStep 5908553 = 4431415) B4431415
theorem B8301305 : Blo 968591 8301305 := bstep (se 2 (by rfl) ⟨3112989, by rfl⟩ : syracuseStep 8301305 = 6225979) B6225979
theorem B7187297 : Blo 968591 7187297 := bstep (se 2 (by rfl) ⟨2695236, by rfl⟩ : syracuseStep 7187297 = 5390473) B5390473
theorem B1453193 : Blo 968591 1453193 := bstep (se 2 (by rfl) ⟨544947, by rfl⟩ : syracuseStep 1453193 = 1089895) B1089895
theorem B1453223 : Blo 968591 1453223 := bstep (se 1 (by rfl) ⟨1089917, by rfl⟩ : syracuseStep 1453223 = 2179835) B2179835
theorem B1092775 : Blo 968591 1092775 := bstep (se 1 (by rfl) ⟨819581, by rfl⟩ : syracuseStep 1092775 = 1639163) B1639163
theorem B1453247 : Blo 968591 1453247 := bstep (se 1 (by rfl) ⟨1089935, by rfl⟩ : syracuseStep 1453247 = 2179871) B2179871
theorem B13282643 : Blo 968591 13282643 := bstep (se 1 (by rfl) ⟨9961982, by rfl⟩ : syracuseStep 13282643 = 19923965) B19923965
theorem B1453727 : Blo 968591 1453727 := bstep (se 1 (by rfl) ⟨1090295, by rfl⟩ : syracuseStep 1453727 = 2180591) B2180591
theorem B1093351 : Blo 968591 1093351 := bstep (se 1 (by rfl) ⟨820013, by rfl⟩ : syracuseStep 1093351 = 1640027) B1640027
theorem B1454015 : Blo 968591 1454015 := bstep (se 1 (by rfl) ⟨1090511, by rfl⟩ : syracuseStep 1454015 = 2181023) B2181023
theorem B1454057 : Blo 968591 1454057 := bstep (se 2 (by rfl) ⟨545271, by rfl⟩ : syracuseStep 1454057 = 1090543) B1090543
theorem B3682331 : Blo 968591 3682331 := bstep (se 1 (by rfl) ⟨2761748, by rfl⟩ : syracuseStep 3682331 = 5523497) B5523497
theorem B1454111 : Blo 968591 1454111 := bstep (se 1 (by rfl) ⟨1090583, by rfl⟩ : syracuseStep 1454111 = 2181167) B2181167
theorem B1454591 : Blo 968591 1454591 := bstep (se 1 (by rfl) ⟨1090943, by rfl⟩ : syracuseStep 1454591 = 2181887) B2181887
theorem B1094143 : Blo 968591 1094143 := bstep (se 1 (by rfl) ⟨820607, by rfl⟩ : syracuseStep 1094143 = 1641215) B1641215
theorem B3682847 : Blo 968591 3682847 := bstep (se 1 (by rfl) ⟨2762135, by rfl⟩ : syracuseStep 3682847 = 5524271) B5524271
theorem B1454729 : Blo 968591 1454729 := bstep (se 2 (by rfl) ⟨545523, by rfl⟩ : syracuseStep 1454729 = 1091047) B1091047
theorem B996223 : Blo 968591 996223 := bstep (se 1 (by rfl) ⟨747167, by rfl⟩ : syracuseStep 996223 = 1494335) B1494335
theorem B1455407 : Blo 968591 1455407 := bstep (se 1 (by rfl) ⟨1091555, by rfl⟩ : syracuseStep 1455407 = 2183111) B2183111
theorem B1455431 : Blo 968591 1455431 := bstep (se 1 (by rfl) ⟨1091573, by rfl⟩ : syracuseStep 1455431 = 2183147) B2183147
theorem B1455743 : Blo 968591 1455743 := bstep (se 1 (by rfl) ⟨1091807, by rfl⟩ : syracuseStep 1455743 = 2183615) B2183615
theorem B1456295 : Blo 968591 1456295 := bstep (se 1 (by rfl) ⟨1092221, by rfl⟩ : syracuseStep 1456295 = 2184443) B2184443
theorem B1751375 : Blo 968591 1751375 := bstep (se 1 (by rfl) ⟨1313531, by rfl⟩ : syracuseStep 1751375 = 2627063) B2627063
theorem B5913323 : Blo 968591 5913323 := bstep (se 1 (by rfl) ⟨4434992, by rfl⟩ : syracuseStep 5913323 = 8869985) B8869985
theorem B1456967 : Blo 968591 1456967 := bstep (se 1 (by rfl) ⟨1092725, by rfl⟩ : syracuseStep 1456967 = 2185451) B2185451
theorem B5258141 : Blo 968591 5258141 := bstep (se 3 (by rfl) ⟨985901, by rfl⟩ : syracuseStep 5258141 = 1971803) B1971803
theorem B1457147 : Blo 968591 1457147 := bstep (se 1 (by rfl) ⟨1092860, by rfl⟩ : syracuseStep 1457147 = 2185721) B2185721
theorem B3685945 : Blo 968591 3685945 := bstep (se 2 (by rfl) ⟨1382229, by rfl⟩ : syracuseStep 3685945 = 2764459) B2764459
theorem B6635191 : Blo 968591 6635191 := bstep (se 1 (by rfl) ⟨4976393, by rfl⟩ : syracuseStep 6635191 = 9952787) B9952787
theorem B18693929 : Blo 968591 18693929 := bstep (se 2 (by rfl) ⟨7010223, by rfl⟩ : syracuseStep 18693929 = 14020447) B14020447
theorem B1458743 : Blo 968591 1458743 := bstep (se 1 (by rfl) ⟨1094057, by rfl⟩ : syracuseStep 1458743 = 2188115) B2188115
theorem B1458779 : Blo 968591 1458779 := bstep (se 1 (by rfl) ⟨1094084, by rfl⟩ : syracuseStep 1458779 = 2188169) B2188169
theorem B41895265 : Blo 968591 41895265 := bstep (se 2 (by rfl) ⟨15710724, by rfl⟩ : syracuseStep 41895265 = 31421449) B31421449
theorem B4147271 : Blo 968591 4147271 := bstep (se 1 (by rfl) ⟨3110453, by rfl⟩ : syracuseStep 4147271 = 6220907) B6220907
theorem B2181257 : Blo 968591 2181257 := bstep (se 2 (by rfl) ⟨817971, by rfl⟩ : syracuseStep 2181257 = 1635943) B1635943
theorem B2181383 : Blo 968591 2181383 := bstep (se 1 (by rfl) ⟨1636037, by rfl⟩ : syracuseStep 2181383 = 3272075) B3272075
theorem B4147955 : Blo 968591 4147955 := bstep (se 1 (by rfl) ⟨3110966, by rfl⟩ : syracuseStep 4147955 = 6221933) B6221933
theorem B969467 : Blo 968591 969467 := bstep (se 1 (by rfl) ⟨727100, by rfl⟩ : syracuseStep 969467 = 1454201) B1454201
theorem B13290641 : Blo 968591 13290641 := bstep (se 2 (by rfl) ⟨4983990, by rfl⟩ : syracuseStep 13290641 = 9967981) B9967981
theorem B3788075 : Blo 968591 3788075 := bstep (se 1 (by rfl) ⟨2841056, by rfl⟩ : syracuseStep 3788075 = 5682113) B5682113
theorem B12472055 : Blo 968591 12472055 := bstep (se 1 (by rfl) ⟨9354041, by rfl⟩ : syracuseStep 12472055 = 18708083) B18708083
theorem B7000307 : Blo 968591 7000307 := bstep (se 1 (by rfl) ⟨5250230, by rfl⟩ : syracuseStep 7000307 = 10500461) B10500461
theorem B2183471 : Blo 968591 2183471 := bstep (se 1 (by rfl) ⟨1637603, by rfl⟩ : syracuseStep 2183471 = 3275207) B3275207
theorem B971551 : Blo 968591 971551 := bstep (se 1 (by rfl) ⟨728663, by rfl⟩ : syracuseStep 971551 = 1457327) B1457327
theorem B972031 : Blo 968591 972031 := bstep (se 1 (by rfl) ⟨729023, by rfl⟩ : syracuseStep 972031 = 1458047) B1458047
theorem B972159 : Blo 968591 972159 := bstep (se 1 (by rfl) ⟨729119, by rfl⟩ : syracuseStep 972159 = 1458239) B1458239
theorem B4904387 : Blo 968591 4904387 := bstep (se 1 (by rfl) ⟨3678290, by rfl⟩ : syracuseStep 4904387 = 7356581) B7356581
theorem B3987323 : Blo 968591 3987323 := bstep (se 1 (by rfl) ⟨2990492, by rfl⟩ : syracuseStep 3987323 = 5980985) B5980985
theorem B2185271 : Blo 968591 2185271 := bstep (se 1 (by rfl) ⟨1638953, by rfl⟩ : syracuseStep 2185271 = 3277907) B3277907
theorem B13982159 : Blo 968591 13982159 := bstep (se 1 (by rfl) ⟨10486619, by rfl⟩ : syracuseStep 13982159 = 20973239) B20973239
theorem B11491955 : Blo 968591 11491955 := bstep (se 1 (by rfl) ⟨8618966, by rfl⟩ : syracuseStep 11491955 = 17237933) B17237933
theorem B2186207 : Blo 968591 2186207 := bstep (se 1 (by rfl) ⟨1639655, by rfl⟩ : syracuseStep 2186207 = 3279311) B3279311
theorem B59661521 : Blo 968591 59661521 := bstep (se 2 (by rfl) ⟨22373070, by rfl⟩ : syracuseStep 59661521 = 44746141) B44746141
theorem B7003367 : Blo 968591 7003367 := bstep (se 1 (by rfl) ⟨5252525, by rfl⟩ : syracuseStep 7003367 = 10505051) B10505051
theorem B4906493 : Blo 968591 4906493 := bstep (se 3 (by rfl) ⟨919967, by rfl⟩ : syracuseStep 4906493 = 1839935) B1839935
theorem B3497849 : Blo 968591 3497849 := bstep (se 2 (by rfl) ⟨1311693, by rfl⟩ : syracuseStep 3497849 = 2623387) B2623387
theorem B7364843 : Blo 968591 7364843 := bstep (se 1 (by rfl) ⟨5523632, by rfl⟩ : syracuseStep 7364843 = 11047265) B11047265
theorem B2187539 : Blo 968591 2187539 := bstep (se 1 (by rfl) ⟨1640654, by rfl⟩ : syracuseStep 2187539 = 3281309) B3281309
theorem B7365815 : Blo 968591 7365815 := bstep (se 1 (by rfl) ⟨5524361, by rfl⟩ : syracuseStep 7365815 = 11048723) B11048723
theorem B3728879 : Blo 968591 3728879 := bstep (se 1 (by rfl) ⟨2796659, by rfl⟩ : syracuseStep 3728879 = 5593319) B5593319
theorem B3107135 : Blo 968591 3107135 := bstep (se 1 (by rfl) ⟨2330351, by rfl⟩ : syracuseStep 3107135 = 4660703) B4660703
theorem B2451809 : Blo 968591 2451809 := bstep (se 2 (by rfl) ⟨919428, by rfl⟩ : syracuseStep 2451809 = 1838857) B1838857
theorem B27978155 : Blo 968591 27978155 := bstep (se 1 (by rfl) ⟨20983616, by rfl⟩ : syracuseStep 27978155 = 41967233) B41967233
theorem B14019065 : Blo 968591 14019065 := bstep (se 2 (by rfl) ⟨5257149, by rfl⟩ : syracuseStep 14019065 = 10514299) B10514299
theorem B3271481 : Blo 968591 3271481 := bstep (se 2 (by rfl) ⟨1226805, by rfl⟩ : syracuseStep 3271481 = 2453611) B2453611
theorem B7007057 : Blo 968591 7007057 := bstep (se 2 (by rfl) ⟨2627646, by rfl⟩ : syracuseStep 7007057 = 5255293) B5255293
theorem B3108223 : Blo 968591 3108223 := bstep (se 1 (by rfl) ⟨2331167, by rfl⟩ : syracuseStep 3108223 = 4662335) B4662335
theorem B5893715 : Blo 968591 5893715 := bstep (se 1 (by rfl) ⟨4420286, by rfl⟩ : syracuseStep 5893715 = 8840573) B8840573
theorem B3272399 : Blo 968591 3272399 := bstep (se 1 (by rfl) ⟨2454299, by rfl⟩ : syracuseStep 3272399 = 4908599) B4908599
theorem B3108775 : Blo 968591 3108775 := bstep (se 1 (by rfl) ⟨2331581, by rfl⟩ : syracuseStep 3108775 = 4663163) B4663163
theorem B8089577 : Blo 968591 8089577 := bstep (se 2 (by rfl) ⟨3033591, by rfl⟩ : syracuseStep 8089577 = 6067183) B6067183
theorem B5534729 : Blo 968591 5534729 := bstep (se 2 (by rfl) ⟨2075523, by rfl⟩ : syracuseStep 5534729 = 4151047) B4151047
theorem B1635835 : Blo 968591 1635835 := bstep (se 1 (by rfl) ⟨1226876, by rfl⟩ : syracuseStep 1635835 = 2453753) B2453753
theorem B1636463 : Blo 968591 1636463 := bstep (se 1 (by rfl) ⟨1227347, by rfl⟩ : syracuseStep 1636463 = 2454695) B2454695
theorem B3275801 : Blo 968591 3275801 := bstep (se 2 (by rfl) ⟨1228425, by rfl⟩ : syracuseStep 3275801 = 2456851) B2456851
theorem B1637563 : Blo 968591 1637563 := bstep (se 1 (by rfl) ⟨1228172, by rfl⟩ : syracuseStep 1637563 = 2456345) B2456345
theorem B1637867 : Blo 968591 1637867 := bstep (se 1 (by rfl) ⟨1228400, by rfl⟩ : syracuseStep 1637867 = 2456801) B2456801
theorem B31161839 : Blo 968591 31161839 := bstep (se 1 (by rfl) ⟨23371379, by rfl⟩ : syracuseStep 31161839 = 46742759) B46742759
theorem B2948681 : Blo 968591 2948681 := bstep (se 2 (by rfl) ⟨1105755, by rfl⟩ : syracuseStep 2948681 = 2211511) B2211511
theorem B116457203 : Blo 968591 116457203 := bstep (se 1 (by rfl) ⟨87342902, by rfl⟩ : syracuseStep 116457203 = 174685805) B174685805
theorem B3277151 : Blo 968591 3277151 := bstep (se 1 (by rfl) ⟨2457863, by rfl⟩ : syracuseStep 3277151 = 4915727) B4915727
theorem B4916051 : Blo 968591 4916051 := bstep (se 1 (by rfl) ⟨3687038, by rfl⟩ : syracuseStep 4916051 = 7374077) B7374077
theorem B3278015 : Blo 968591 3278015 := bstep (se 1 (by rfl) ⟨2458511, by rfl⟩ : syracuseStep 3278015 = 4917023) B4917023
theorem B2525383 : Blo 968591 2525383 := bstep (se 1 (by rfl) ⟨1894037, by rfl⟩ : syracuseStep 2525383 = 3788075) B3788075
theorem B1640911 : Blo 968591 1640911 := bstep (se 1 (by rfl) ⟨1230683, by rfl⟩ : syracuseStep 1640911 = 2461367) B2461367
theorem B4917995 : Blo 968591 4917995 := bstep (se 1 (by rfl) ⟨3688496, by rfl⟩ : syracuseStep 4917995 = 7376993) B7376993
theorem B4918319 : Blo 968591 4918319 := bstep (se 1 (by rfl) ⟨3688739, by rfl⟩ : syracuseStep 4918319 = 7377479) B7377479
theorem B2658215 : Blo 968591 2658215 := bstep (se 1 (by rfl) ⟨1993661, by rfl⟩ : syracuseStep 2658215 = 3987323) B3987323
theorem B3281147 : Blo 968591 3281147 := bstep (se 1 (by rfl) ⟨2460860, by rfl⟩ : syracuseStep 3281147 = 4921721) B4921721
theorem B3281255 : Blo 968591 3281255 := bstep (se 1 (by rfl) ⟨2460941, by rfl⟩ : syracuseStep 3281255 = 4921883) B4921883
theorem B1381159 : Blo 968591 1381159 := bstep (se 1 (by rfl) ⟨1035869, by rfl⟩ : syracuseStep 1381159 = 2071739) B2071739
theorem B2331899 : Blo 968591 2331899 := bstep (se 1 (by rfl) ⟨1748924, by rfl⟩ : syracuseStep 2331899 = 3497849) B3497849
theorem B3939035 : Blo 968591 3939035 := bstep (se 1 (by rfl) ⟨2954276, by rfl⟩ : syracuseStep 3939035 = 5908553) B5908553
theorem B2071423 : Blo 968591 2071423 := bstep (se 1 (by rfl) ⟨1553567, by rfl⟩ : syracuseStep 2071423 = 3107135) B3107135
theorem B18652103 : Blo 968591 18652103 := bstep (se 1 (by rfl) ⟨13989077, by rfl⟩ : syracuseStep 18652103 = 27978155) B27978155
theorem B9346043 : Blo 968591 9346043 := bstep (se 1 (by rfl) ⟨7009532, by rfl⟩ : syracuseStep 9346043 = 14019065) B14019065
theorem B8855095 : Blo 968591 8855095 := bstep (se 1 (by rfl) ⟨6641321, by rfl⟩ : syracuseStep 8855095 = 13282643) B13282643
theorem B1090975 : Blo 968591 1090975 := bstep (se 1 (by rfl) ⟨818231, by rfl⟩ : syracuseStep 1090975 = 1636463) B1636463
theorem B3942215 : Blo 968591 3942215 := bstep (se 1 (by rfl) ⟨2956661, by rfl⟩ : syracuseStep 3942215 = 5913323) B5913323
theorem B1091911 : Blo 968591 1091911 := bstep (se 1 (by rfl) ⟨818933, by rfl⟩ : syracuseStep 1091911 = 1637867) B1637867
theorem B77638135 : Blo 968591 77638135 := bstep (se 1 (by rfl) ⟨58228601, by rfl⟩ : syracuseStep 77638135 = 116457203) B116457203
theorem B12462619 : Blo 968591 12462619 := bstep (se 1 (by rfl) ⟨9346964, by rfl⟩ : syracuseStep 12462619 = 18693929) B18693929
theorem B1092703 : Blo 968591 1092703 := bstep (se 1 (by rfl) ⟨819527, by rfl⟩ : syracuseStep 1092703 = 1639055) B1639055
theorem B9317713 : Blo 968591 9317713 := bstep (se 2 (by rfl) ⟨3494142, by rfl⟩ : syracuseStep 9317713 = 6988285) B6988285
theorem B16559963 : Blo 968591 16559963 := bstep (se 1 (by rfl) ⟨12419972, by rfl⟩ : syracuseStep 16559963 = 24839945) B24839945
theorem B2764847 : Blo 968591 2764847 := bstep (se 1 (by rfl) ⟨2073635, by rfl⟩ : syracuseStep 2764847 = 4147271) B4147271
theorem B1454171 : Blo 968591 1454171 := bstep (se 1 (by rfl) ⟨1090628, by rfl⟩ : syracuseStep 1454171 = 2181257) B2181257
theorem B1454255 : Blo 968591 1454255 := bstep (se 1 (by rfl) ⟨1090691, by rfl⟩ : syracuseStep 1454255 = 2181383) B2181383
theorem B8302945 : Blo 968591 8302945 := bstep (se 2 (by rfl) ⟨3113604, by rfl⟩ : syracuseStep 8302945 = 6227209) B6227209
theorem B2765303 : Blo 968591 2765303 := bstep (se 1 (by rfl) ⟨2073977, by rfl⟩ : syracuseStep 2765303 = 4147955) B4147955
theorem B8860427 : Blo 968591 8860427 := bstep (se 1 (by rfl) ⟨6645320, by rfl⟩ : syracuseStep 8860427 = 13290641) B13290641
theorem B8303903 : Blo 968591 8303903 := bstep (se 1 (by rfl) ⟨6227927, by rfl⟩ : syracuseStep 8303903 = 12455855) B12455855
theorem B4666871 : Blo 968591 4666871 := bstep (se 1 (by rfl) ⟨3500153, by rfl⟩ : syracuseStep 4666871 = 7000307) B7000307
theorem B1455647 : Blo 968591 1455647 := bstep (se 1 (by rfl) ⟨1091735, by rfl⟩ : syracuseStep 1455647 = 2183471) B2183471
theorem B8304281 : Blo 968591 8304281 := bstep (se 2 (by rfl) ⟨3114105, by rfl⟩ : syracuseStep 8304281 = 6228211) B6228211
theorem B1226431 : Blo 968591 1226431 := bstep (se 1 (by rfl) ⟨919823, by rfl⟩ : syracuseStep 1226431 = 1839647) B1839647
theorem B1226927 : Blo 968591 1226927 := bstep (se 1 (by rfl) ⟨920195, by rfl⟩ : syracuseStep 1226927 = 1840391) B1840391
theorem B1456847 : Blo 968591 1456847 := bstep (se 1 (by rfl) ⟨1092635, by rfl⟩ : syracuseStep 1456847 = 2185271) B2185271
theorem B1227631 : Blo 968591 1227631 := bstep (se 1 (by rfl) ⟨920723, by rfl⟩ : syracuseStep 1227631 = 1841447) B1841447
theorem B1457033 : Blo 968591 1457033 := bstep (se 2 (by rfl) ⟨546387, by rfl⟩ : syracuseStep 1457033 = 1092775) B1092775
theorem B9321439 : Blo 968591 9321439 := bstep (se 1 (by rfl) ⟨6991079, by rfl⟩ : syracuseStep 9321439 = 13982159) B13982159
theorem B4144297 : Blo 968591 4144297 := bstep (se 2 (by rfl) ⟨1554111, by rfl⟩ : syracuseStep 4144297 = 3108223) B3108223
theorem B3325151 : Blo 968591 3325151 := bstep (se 1 (by rfl) ⟨2493863, by rfl⟩ : syracuseStep 3325151 = 4987727) B4987727
theorem B1457471 : Blo 968591 1457471 := bstep (se 1 (by rfl) ⟨1093103, by rfl⟩ : syracuseStep 1457471 = 2186207) B2186207
theorem B4668911 : Blo 968591 4668911 := bstep (se 1 (by rfl) ⟨3501683, by rfl⟩ : syracuseStep 4668911 = 7003367) B7003367
theorem B1457801 : Blo 968591 1457801 := bstep (se 2 (by rfl) ⟨546675, by rfl⟩ : syracuseStep 1457801 = 1093351) B1093351
theorem B4145033 : Blo 968591 4145033 := bstep (se 2 (by rfl) ⟨1554387, by rfl⟩ : syracuseStep 4145033 = 3108775) B3108775
theorem B1458359 : Blo 968591 1458359 := bstep (se 1 (by rfl) ⟨1093769, by rfl⟩ : syracuseStep 1458359 = 2187539) B2187539
theorem B13287847 : Blo 968591 13287847 := bstep (se 1 (by rfl) ⟨9965885, by rfl⟩ : syracuseStep 13287847 = 19931771) B19931771
theorem B1458857 : Blo 968591 1458857 := bstep (se 2 (by rfl) ⟨547071, by rfl⟩ : syracuseStep 1458857 = 1094143) B1094143
theorem B1328297 : Blo 968591 1328297 := bstep (se 2 (by rfl) ⟨498111, by rfl⟩ : syracuseStep 1328297 = 996223) B996223
theorem B2180987 : Blo 968591 2180987 := bstep (se 1 (by rfl) ⟨1635740, by rfl⟩ : syracuseStep 2180987 = 3271481) B3271481
theorem B4671371 : Blo 968591 4671371 := bstep (se 1 (by rfl) ⟨3503528, by rfl⟩ : syracuseStep 4671371 = 7007057) B7007057
theorem B2181113 : Blo 968591 2181113 := bstep (se 2 (by rfl) ⟨817917, by rfl⟩ : syracuseStep 2181113 = 1635835) B1635835
theorem B968795 : Blo 968591 968795 := bstep (se 1 (by rfl) ⟨726596, by rfl⟩ : syracuseStep 968795 = 1453193) B1453193
theorem B968815 : Blo 968591 968815 := bstep (se 1 (by rfl) ⟨726611, by rfl⟩ : syracuseStep 968815 = 1453223) B1453223
theorem B968831 : Blo 968591 968831 := bstep (se 1 (by rfl) ⟨726623, by rfl⟩ : syracuseStep 968831 = 1453247) B1453247
theorem B53135797 : Blo 968591 53135797 := bstep (se 5 (by rfl) ⟨2490740, by rfl⟩ : syracuseStep 53135797 = 4981481) B4981481
theorem B969151 : Blo 968591 969151 := bstep (se 1 (by rfl) ⟨726863, by rfl⟩ : syracuseStep 969151 = 1453727) B1453727
theorem B2181599 : Blo 968591 2181599 := bstep (se 1 (by rfl) ⟨1636199, by rfl⟩ : syracuseStep 2181599 = 3272399) B3272399
theorem B969343 : Blo 968591 969343 := bstep (se 1 (by rfl) ⟨727007, by rfl⟩ : syracuseStep 969343 = 1454015) B1454015
theorem B969371 : Blo 968591 969371 := bstep (se 1 (by rfl) ⟨727028, by rfl⟩ : syracuseStep 969371 = 1454057) B1454057
theorem B5393051 : Blo 968591 5393051 := bstep (se 1 (by rfl) ⟨4044788, by rfl⟩ : syracuseStep 5393051 = 8089577) B8089577
theorem B969407 : Blo 968591 969407 := bstep (se 1 (by rfl) ⟨727055, by rfl⟩ : syracuseStep 969407 = 1454111) B1454111
theorem B969727 : Blo 968591 969727 := bstep (se 1 (by rfl) ⟨727295, by rfl⟩ : syracuseStep 969727 = 1454591) B1454591
theorem B969819 : Blo 968591 969819 := bstep (se 1 (by rfl) ⟨727364, by rfl⟩ : syracuseStep 969819 = 1454729) B1454729
theorem B3689819 : Blo 968591 3689819 := bstep (se 1 (by rfl) ⟨2767364, by rfl⟩ : syracuseStep 3689819 = 5534729) B5534729
theorem B970271 : Blo 968591 970271 := bstep (se 1 (by rfl) ⟨727703, by rfl⟩ : syracuseStep 970271 = 1455407) B1455407
theorem B970287 : Blo 968591 970287 := bstep (se 1 (by rfl) ⟨727715, by rfl⟩ : syracuseStep 970287 = 1455431) B1455431
theorem B76664501 : Blo 968591 76664501 := bstep (se 5 (by rfl) ⟨3593648, by rfl⟩ : syracuseStep 76664501 = 7187297) B7187297
theorem B970495 : Blo 968591 970495 := bstep (se 1 (by rfl) ⟨727871, by rfl⟩ : syracuseStep 970495 = 1455743) B1455743
theorem B970863 : Blo 968591 970863 := bstep (se 1 (by rfl) ⟨728147, by rfl⟩ : syracuseStep 970863 = 1456295) B1456295
theorem B1167583 : Blo 968591 1167583 := bstep (se 1 (by rfl) ⟨875687, by rfl⟩ : syracuseStep 1167583 = 1751375) B1751375
theorem B2183417 : Blo 968591 2183417 := bstep (se 2 (by rfl) ⟨818781, by rfl⟩ : syracuseStep 2183417 = 1637563) B1637563
theorem B971311 : Blo 968591 971311 := bstep (se 1 (by rfl) ⟨728483, by rfl⟩ : syracuseStep 971311 = 1456967) B1456967
theorem B971431 : Blo 968591 971431 := bstep (se 1 (by rfl) ⟨728573, by rfl⟩ : syracuseStep 971431 = 1457147) B1457147
theorem B2183867 : Blo 968591 2183867 := bstep (se 1 (by rfl) ⟨1637900, by rfl⟩ : syracuseStep 2183867 = 3275801) B3275801
theorem B2184659 : Blo 968591 2184659 := bstep (se 1 (by rfl) ⟨1638494, by rfl⟩ : syracuseStep 2184659 = 3276989) B3276989
theorem B972495 : Blo 968591 972495 := bstep (se 1 (by rfl) ⟨729371, by rfl⟩ : syracuseStep 972495 = 1458743) B1458743
theorem B972519 : Blo 968591 972519 := bstep (se 1 (by rfl) ⟨729389, by rfl⟩ : syracuseStep 972519 = 1458779) B1458779
theorem B5527439 : Blo 968591 5527439 := bstep (se 1 (by rfl) ⟨4145579, by rfl⟩ : syracuseStep 5527439 = 8291159) B8291159
theorem B53172395 : Blo 968591 53172395 := bstep (se 1 (by rfl) ⟨39879296, by rfl⟩ : syracuseStep 53172395 = 79758593) B79758593
theorem B6215933 : Blo 968591 6215933 := bstep (se 3 (by rfl) ⟨1165487, by rfl⟩ : syracuseStep 6215933 = 2330975) B2330975
theorem B2185811 : Blo 968591 2185811 := bstep (se 1 (by rfl) ⟨1639358, by rfl⟩ : syracuseStep 2185811 = 3278717) B3278717
theorem B55860353 : Blo 968591 55860353 := bstep (se 2 (by rfl) ⟨20947632, by rfl⟩ : syracuseStep 55860353 = 41895265) B41895265
theorem B59792579 : Blo 968591 59792579 := bstep (se 1 (by rfl) ⟨44844434, by rfl⟩ : syracuseStep 59792579 = 89688869) B89688869
theorem B2186855 : Blo 968591 2186855 := bstep (se 1 (by rfl) ⟨1640141, by rfl⟩ : syracuseStep 2186855 = 3280283) B3280283
theorem B2187017 : Blo 968591 2187017 := bstep (se 2 (by rfl) ⟨820131, by rfl⟩ : syracuseStep 2187017 = 1640263) B1640263
theorem B8314703 : Blo 968591 8314703 := bstep (se 1 (by rfl) ⟨6236027, by rfl⟩ : syracuseStep 8314703 = 12472055) B12472055
theorem B4153319 : Blo 968591 4153319 := bstep (se 1 (by rfl) ⟨3114989, by rfl⟩ : syracuseStep 4153319 = 6229979) B6229979
theorem B3269591 : Blo 968591 3269591 := bstep (se 1 (by rfl) ⟨2452193, by rfl⟩ : syracuseStep 3269591 = 4904387) B4904387
theorem B7661303 : Blo 968591 7661303 := bstep (se 1 (by rfl) ⟨5745977, by rfl⟩ : syracuseStep 7661303 = 11491955) B11491955
theorem B39774347 : Blo 968591 39774347 := bstep (se 1 (by rfl) ⟨29830760, by rfl⟩ : syracuseStep 39774347 = 59661521) B59661521
theorem B3270995 : Blo 968591 3270995 := bstep (se 1 (by rfl) ⟨2453246, by rfl⟩ : syracuseStep 3270995 = 4906493) B4906493
theorem B4909895 : Blo 968591 4909895 := bstep (se 1 (by rfl) ⟨3682421, by rfl⟩ : syracuseStep 4909895 = 7364843) B7364843
theorem B4910543 : Blo 968591 4910543 := bstep (se 1 (by rfl) ⟨3682907, by rfl⟩ : syracuseStep 4910543 = 7365815) B7365815
theorem B4419119 : Blo 968591 4419119 := bstep (se 1 (by rfl) ⟨3314339, by rfl⟩ : syracuseStep 4419119 = 6628679) B6628679
theorem B2485919 : Blo 968591 2485919 := bstep (se 1 (by rfl) ⟨1864439, by rfl⟩ : syracuseStep 2485919 = 3728879) B3728879
theorem B1634539 : Blo 968591 1634539 := bstep (se 1 (by rfl) ⟨1225904, by rfl⟩ : syracuseStep 1634539 = 2451809) B2451809
theorem B5534203 : Blo 968591 5534203 := bstep (se 1 (by rfl) ⟨4150652, by rfl⟩ : syracuseStep 5534203 = 8301305) B8301305
theorem B3929143 : Blo 968591 3929143 := bstep (se 1 (by rfl) ⟨2946857, by rfl⟩ : syracuseStep 3929143 = 5893715) B5893715
theorem B2454887 : Blo 968591 2454887 := bstep (se 1 (by rfl) ⟨1841165, by rfl⟩ : syracuseStep 2454887 = 3682331) B3682331
theorem B12416489 : Blo 968591 12416489 := bstep (se 2 (by rfl) ⟨4656183, by rfl⟩ : syracuseStep 12416489 = 9312367) B9312367
theorem B2455231 : Blo 968591 2455231 := bstep (se 1 (by rfl) ⟨1841423, by rfl⟩ : syracuseStep 2455231 = 3682847) B3682847
theorem B3110633 : Blo 968591 3110633 := bstep (se 2 (by rfl) ⟨1166487, by rfl⟩ : syracuseStep 3110633 = 2332975) B2332975
theorem B83098237 : Blo 968591 83098237 := bstep (se 3 (by rfl) ⟨15580919, by rfl⟩ : syracuseStep 83098237 = 31161839) B31161839
theorem B7863149 : Blo 968591 7863149 := bstep (se 3 (by rfl) ⟨1474340, by rfl⟩ : syracuseStep 7863149 = 2948681) B2948681
theorem B3505427 : Blo 968591 3505427 := bstep (se 1 (by rfl) ⟨2629070, by rfl⟩ : syracuseStep 3505427 = 5258141) B5258141
theorem B4914593 : Blo 968591 4914593 := bstep (se 2 (by rfl) ⟨1842972, by rfl⟩ : syracuseStep 4914593 = 3685945) B3685945
theorem B8846921 : Blo 968591 8846921 := bstep (se 2 (by rfl) ⟨3317595, by rfl⟩ : syracuseStep 8846921 = 6635191) B6635191
theorem B3277367 : Blo 968591 3277367 := bstep (se 1 (by rfl) ⟨2458025, by rfl⟩ : syracuseStep 3277367 = 4916051) B4916051
theorem B3114247 : Blo 968591 3114247 := bstep (se 1 (by rfl) ⟨2335685, by rfl⟩ : syracuseStep 3114247 = 4671371) B4671371
theorem B3278663 : Blo 968591 3278663 := bstep (se 1 (by rfl) ⟨2458997, by rfl⟩ : syracuseStep 3278663 = 4917995) B4917995
theorem B3278879 : Blo 968591 3278879 := bstep (se 1 (by rfl) ⟨2459159, by rfl⟩ : syracuseStep 3278879 = 4918319) B4918319
theorem B2459879 : Blo 968591 2459879 := bstep (se 1 (by rfl) ⟨1844909, by rfl⟩ : syracuseStep 2459879 = 3689819) B3689819
theorem B3542125 : Blo 968591 3542125 := bstep (se 3 (by rfl) ⟨664148, by rfl⟩ : syracuseStep 3542125 = 1328297) B1328297
theorem B70847729 : Blo 968591 70847729 := bstep (se 2 (by rfl) ⟨26567898, by rfl⟩ : syracuseStep 70847729 = 53135797) B53135797
theorem B103517513 : Blo 968591 103517513 := bstep (se 2 (by rfl) ⟨38819067, by rfl⟩ : syracuseStep 103517513 = 77638135) B77638135
theorem B16616825 : Blo 968591 16616825 := bstep (se 2 (by rfl) ⟨6231309, by rfl⟩ : syracuseStep 16616825 = 12462619) B12462619
theorem B12423617 : Blo 968591 12423617 := bstep (se 2 (by rfl) ⟨4658856, by rfl⟩ : syracuseStep 12423617 = 9317713) B9317713
theorem B6230695 : Blo 968591 6230695 := bstep (se 1 (by rfl) ⟨4673021, by rfl⟩ : syracuseStep 6230695 = 9346043) B9346043
theorem B5543135 : Blo 968591 5543135 := bstep (se 1 (by rfl) ⟨4157351, by rfl⟩ : syracuseStep 5543135 = 8314703) B8314703
theorem B7378937 : Blo 968591 7378937 := bstep (se 2 (by rfl) ⟨2767101, by rfl⟩ : syracuseStep 7378937 = 5534203) B5534203
theorem B1841545 : Blo 968591 1841545 := bstep (se 2 (by rfl) ⟨690579, by rfl⟩ : syracuseStep 1841545 = 1381159) B1381159
theorem B2628143 : Blo 968591 2628143 := bstep (se 1 (by rfl) ⟨1971107, by rfl⟩ : syracuseStep 2628143 = 3942215) B3942215
theorem B26516231 : Blo 968591 26516231 := bstep (se 1 (by rfl) ⟨19887173, by rfl⟩ : syracuseStep 26516231 = 39774347) B39774347
theorem B1843231 : Blo 968591 1843231 := bstep (se 1 (by rfl) ⟨1382423, by rfl⟩ : syracuseStep 1843231 = 2764847) B2764847
theorem B1843535 : Blo 968591 1843535 := bstep (se 1 (by rfl) ⟨1382651, by rfl⟩ : syracuseStep 1843535 = 2765303) B2765303
theorem B5906951 : Blo 968591 5906951 := bstep (se 1 (by rfl) ⟨4430213, by rfl⟩ : syracuseStep 5906951 = 8860427) B8860427
theorem B110797649 : Blo 968591 110797649 := bstep (se 2 (by rfl) ⟨41549118, by rfl⟩ : syracuseStep 110797649 = 83098237) B83098237
theorem B2073755 : Blo 968591 2073755 := bstep (se 1 (by rfl) ⟨1555316, by rfl⟩ : syracuseStep 2073755 = 3110633) B3110633
theorem B2761897 : Blo 968591 2761897 := bstep (se 2 (by rfl) ⟨1035711, by rfl⟩ : syracuseStep 2761897 = 2071423) B2071423
theorem B12428585 : Blo 968591 12428585 := bstep (se 2 (by rfl) ⟨4660719, by rfl⟩ : syracuseStep 12428585 = 9321439) B9321439
theorem B11806793 : Blo 968591 11806793 := bstep (se 2 (by rfl) ⟨4427547, by rfl⟩ : syracuseStep 11806793 = 8855095) B8855095
theorem B2336951 : Blo 968591 2336951 := bstep (se 1 (by rfl) ⟨1752713, by rfl⟩ : syracuseStep 2336951 = 3505427) B3505427
theorem B7088573 : Blo 968591 7088573 := bstep (se 3 (by rfl) ⟨1329107, by rfl⟩ : syracuseStep 7088573 = 2658215) B2658215
theorem B2763355 : Blo 968591 2763355 := bstep (se 1 (by rfl) ⟨2072516, by rfl⟩ : syracuseStep 2763355 = 4145033) B4145033
theorem B1453991 : Blo 968591 1453991 := bstep (se 1 (by rfl) ⟨1090493, by rfl⟩ : syracuseStep 1453991 = 2180987) B2180987
theorem B1454075 : Blo 968591 1454075 := bstep (se 1 (by rfl) ⟨1090556, by rfl⟩ : syracuseStep 1454075 = 2181113) B2181113
theorem B1454399 : Blo 968591 1454399 := bstep (se 1 (by rfl) ⟨1090799, by rfl⟩ : syracuseStep 1454399 = 2181599) B2181599
theorem B1454633 : Blo 968591 1454633 := bstep (se 2 (by rfl) ⟨545487, by rfl⟩ : syracuseStep 1454633 = 1090975) B1090975
theorem B1455611 : Blo 968591 1455611 := bstep (se 1 (by rfl) ⟨1091708, by rfl⟩ : syracuseStep 1455611 = 2183417) B2183417
theorem B1455881 : Blo 968591 1455881 := bstep (se 2 (by rfl) ⟨545955, by rfl⟩ : syracuseStep 1455881 = 1091911) B1091911
theorem B1455911 : Blo 968591 1455911 := bstep (se 1 (by rfl) ⟨1091933, by rfl⟩ : syracuseStep 1455911 = 2183867) B2183867
theorem B1554599 : Blo 968591 1554599 := bstep (se 1 (by rfl) ⟨1165949, by rfl⟩ : syracuseStep 1554599 = 2331899) B2331899
theorem B1456439 : Blo 968591 1456439 := bstep (se 1 (by rfl) ⟨1092329, by rfl⟩ : syracuseStep 1456439 = 2184659) B2184659
theorem B3684959 : Blo 968591 3684959 := bstep (se 1 (by rfl) ⟨2763719, by rfl⟩ : syracuseStep 3684959 = 5527439) B5527439
theorem B1456937 : Blo 968591 1456937 := bstep (se 2 (by rfl) ⟨546351, by rfl⟩ : syracuseStep 1456937 = 1092703) B1092703
theorem B4143955 : Blo 968591 4143955 := bstep (se 1 (by rfl) ⟨3107966, by rfl⟩ : syracuseStep 4143955 = 6215933) B6215933
theorem B1457207 : Blo 968591 1457207 := bstep (se 1 (by rfl) ⟨1092905, by rfl⟩ : syracuseStep 1457207 = 2185811) B2185811
theorem B12434735 : Blo 968591 12434735 := bstep (se 1 (by rfl) ⟨9326051, by rfl⟩ : syracuseStep 12434735 = 18652103) B18652103
theorem B37240235 : Blo 968591 37240235 := bstep (se 1 (by rfl) ⟨27930176, by rfl⟩ : syracuseStep 37240235 = 55860353) B55860353
theorem B39861719 : Blo 968591 39861719 := bstep (se 1 (by rfl) ⟨29896289, by rfl⟩ : syracuseStep 39861719 = 59792579) B59792579
theorem B1457903 : Blo 968591 1457903 := bstep (se 1 (by rfl) ⟨1093427, by rfl⟩ : syracuseStep 1457903 = 2186855) B2186855
theorem B1458011 : Blo 968591 1458011 := bstep (se 1 (by rfl) ⟨1093508, by rfl⟩ : syracuseStep 1458011 = 2187017) B2187017
theorem B2768879 : Blo 968591 2768879 := bstep (se 1 (by rfl) ⟨2076659, by rfl⟩ : syracuseStep 2768879 = 4153319) B4153319
theorem B1556777 : Blo 968591 1556777 := bstep (se 2 (by rfl) ⟨583791, by rfl⟩ : syracuseStep 1556777 = 1167583) B1167583
theorem B2179385 : Blo 968591 2179385 := bstep (se 2 (by rfl) ⟨817269, by rfl⟩ : syracuseStep 2179385 = 1634539) B1634539
theorem B2179727 : Blo 968591 2179727 := bstep (se 1 (by rfl) ⟨1634795, by rfl⟩ : syracuseStep 2179727 = 3269591) B3269591
theorem B2180663 : Blo 968591 2180663 := bstep (se 1 (by rfl) ⟨1635497, by rfl⟩ : syracuseStep 2180663 = 3270995) B3270995
theorem B10504093 : Blo 968591 10504093 := bstep (se 3 (by rfl) ⟨1969517, by rfl⟩ : syracuseStep 10504093 = 3939035) B3939035
theorem B1657279 : Blo 968591 1657279 := bstep (se 1 (by rfl) ⟨1242959, by rfl⟩ : syracuseStep 1657279 = 2485919) B2485919
theorem B969447 : Blo 968591 969447 := bstep (se 1 (by rfl) ⟨727085, by rfl⟩ : syracuseStep 969447 = 1454171) B1454171
theorem B969503 : Blo 968591 969503 := bstep (se 1 (by rfl) ⟨727127, by rfl⟩ : syracuseStep 969503 = 1454255) B1454255
theorem B8867069 : Blo 968591 8867069 := bstep (se 3 (by rfl) ⟨1662575, by rfl⟩ : syracuseStep 8867069 = 3325151) B3325151
theorem B8277659 : Blo 968591 8277659 := bstep (se 1 (by rfl) ⟨6208244, by rfl⟩ : syracuseStep 8277659 = 12416489) B12416489
theorem B970431 : Blo 968591 970431 := bstep (se 1 (by rfl) ⟨727823, by rfl⟩ : syracuseStep 970431 = 1455647) B1455647
theorem B5525729 : Blo 968591 5525729 := bstep (se 2 (by rfl) ⟨2072148, by rfl⟩ : syracuseStep 5525729 = 4144297) B4144297
theorem B971231 : Blo 968591 971231 := bstep (se 1 (by rfl) ⟨728423, by rfl⟩ : syracuseStep 971231 = 1456847) B1456847
theorem B971355 : Blo 968591 971355 := bstep (se 1 (by rfl) ⟨728516, by rfl⟩ : syracuseStep 971355 = 1457033) B1457033
theorem B971647 : Blo 968591 971647 := bstep (se 1 (by rfl) ⟨728735, by rfl⟩ : syracuseStep 971647 = 1457471) B1457471
theorem B971867 : Blo 968591 971867 := bstep (se 1 (by rfl) ⟨728900, by rfl⟩ : syracuseStep 971867 = 1457801) B1457801
theorem B972239 : Blo 968591 972239 := bstep (se 1 (by rfl) ⟨729179, by rfl⟩ : syracuseStep 972239 = 1458359) B1458359
theorem B2184767 : Blo 968591 2184767 := bstep (se 1 (by rfl) ⟨1638575, by rfl⟩ : syracuseStep 2184767 = 3277151) B3277151
theorem B972571 : Blo 968591 972571 := bstep (se 1 (by rfl) ⟨729428, by rfl⟩ : syracuseStep 972571 = 1458857) B1458857
theorem B17717129 : Blo 968591 17717129 := bstep (se 2 (by rfl) ⟨6643923, by rfl⟩ : syracuseStep 17717129 = 13287847) B13287847
theorem B2185343 : Blo 968591 2185343 := bstep (se 1 (by rfl) ⟨1639007, by rfl⟩ : syracuseStep 2185343 = 3278015) B3278015
theorem B3595367 : Blo 968591 3595367 := bstep (se 1 (by rfl) ⟨2696525, by rfl⟩ : syracuseStep 3595367 = 5393051) B5393051
theorem B51109667 : Blo 968591 51109667 := bstep (se 1 (by rfl) ⟨38332250, by rfl⟩ : syracuseStep 51109667 = 76664501) B76664501
theorem B2187431 : Blo 968591 2187431 := bstep (se 1 (by rfl) ⟨1640573, by rfl⟩ : syracuseStep 2187431 = 3281147) B3281147
theorem B2187503 : Blo 968591 2187503 := bstep (se 1 (by rfl) ⟨1640627, by rfl⟩ : syracuseStep 2187503 = 3281255) B3281255
theorem B3367177 : Blo 968591 3367177 := bstep (se 2 (by rfl) ⟨1262691, by rfl⟩ : syracuseStep 3367177 = 2525383) B2525383
theorem B2187881 : Blo 968591 2187881 := bstep (se 2 (by rfl) ⟨820455, by rfl⟩ : syracuseStep 2187881 = 1640911) B1640911
theorem B35448263 : Blo 968591 35448263 := bstep (se 1 (by rfl) ⟨26586197, by rfl⟩ : syracuseStep 35448263 = 53172395) B53172395
theorem B3271805 : Blo 968591 3271805 := bstep (se 3 (by rfl) ⟨613463, by rfl⟩ : syracuseStep 3271805 = 1226927) B1226927
theorem B11070593 : Blo 968591 11070593 := bstep (se 2 (by rfl) ⟨4151472, by rfl⟩ : syracuseStep 11070593 = 8302945) B8302945
theorem B5107535 : Blo 968591 5107535 := bstep (se 1 (by rfl) ⟨3830651, by rfl⟩ : syracuseStep 5107535 = 7661303) B7661303
theorem B5238857 : Blo 968591 5238857 := bstep (se 2 (by rfl) ⟨1964571, by rfl⟩ : syracuseStep 5238857 = 3929143) B3929143
theorem B3273263 : Blo 968591 3273263 := bstep (se 1 (by rfl) ⟨2454947, by rfl⟩ : syracuseStep 3273263 = 4909895) B4909895
theorem B1635241 : Blo 968591 1635241 := bstep (se 2 (by rfl) ⟨613215, by rfl⟩ : syracuseStep 1635241 = 1226431) B1226431
theorem B3273641 : Blo 968591 3273641 := bstep (se 2 (by rfl) ⟨1227615, by rfl⟩ : syracuseStep 3273641 = 2455231) B2455231
theorem B3273695 : Blo 968591 3273695 := bstep (se 1 (by rfl) ⟨2455271, by rfl⟩ : syracuseStep 3273695 = 4910543) B4910543
theorem B2946079 : Blo 968591 2946079 := bstep (se 1 (by rfl) ⟨2209559, by rfl⟩ : syracuseStep 2946079 = 4419119) B4419119
theorem B11039975 : Blo 968591 11039975 := bstep (se 1 (by rfl) ⟨8279981, by rfl⟩ : syracuseStep 11039975 = 16559963) B16559963
theorem B5535935 : Blo 968591 5535935 := bstep (se 1 (by rfl) ⟨4151951, by rfl⟩ : syracuseStep 5535935 = 8303903) B8303903
theorem B1636591 : Blo 968591 1636591 := bstep (se 1 (by rfl) ⟨1227443, by rfl⟩ : syracuseStep 1636591 = 2454887) B2454887
theorem B3111247 : Blo 968591 3111247 := bstep (se 1 (by rfl) ⟨2333435, by rfl⟩ : syracuseStep 3111247 = 4666871) B4666871
theorem B5536187 : Blo 968591 5536187 := bstep (se 1 (by rfl) ⟨4152140, by rfl⟩ : syracuseStep 5536187 = 8304281) B8304281
theorem B1636841 : Blo 968591 1636841 := bstep (se 2 (by rfl) ⟨613815, by rfl⟩ : syracuseStep 1636841 = 1227631) B1227631
theorem B5242099 : Blo 968591 5242099 := bstep (se 1 (by rfl) ⟨3931574, by rfl⟩ : syracuseStep 5242099 = 7863149) B7863149
theorem B3276395 : Blo 968591 3276395 := bstep (se 1 (by rfl) ⟨2457296, by rfl⟩ : syracuseStep 3276395 = 4914593) B4914593
theorem B3112607 : Blo 968591 3112607 := bstep (se 1 (by rfl) ⟨2334455, by rfl⟩ : syracuseStep 3112607 = 4668911) B4668911
theorem B5897947 : Blo 968591 5897947 := bstep (se 1 (by rfl) ⟨4423460, by rfl⟩ : syracuseStep 5897947 = 8846921) B8846921
theorem B2457641 : Blo 968591 2457641 := bstep (se 2 (by rfl) ⟨921615, by rfl⟩ : syracuseStep 2457641 = 1843231) B1843231
theorem B17958277 : Blo 968591 17958277 := bstep (se 4 (by rfl) ⟨1683588, by rfl⟩ : syracuseStep 17958277 = 3367177) B3367177
theorem B1639919 : Blo 968591 1639919 := bstep (se 1 (by rfl) ⟨1229939, by rfl⟩ : syracuseStep 1639919 = 2459879) B2459879
theorem B69011675 : Blo 968591 69011675 := bstep (se 1 (by rfl) ⟨51758756, by rfl⟩ : syracuseStep 69011675 = 103517513) B103517513
theorem B11077883 : Blo 968591 11077883 := bstep (se 1 (by rfl) ⟨8308412, by rfl⟩ : syracuseStep 11077883 = 16616825) B16616825
theorem B4919291 : Blo 968591 4919291 := bstep (se 1 (by rfl) ⟨3689468, by rfl⟩ : syracuseStep 4919291 = 7378937) B7378937
theorem B4722833 : Blo 968591 4722833 := bstep (se 2 (by rfl) ⟨1771062, by rfl⟩ : syracuseStep 4722833 = 3542125) B3542125
theorem B2396911 : Blo 968591 2396911 := bstep (se 1 (by rfl) ⟨1797683, by rfl⟩ : syracuseStep 2396911 = 3595367) B3595367
theorem B3937967 : Blo 968591 3937967 := bstep (se 1 (by rfl) ⟨2953475, by rfl⟩ : syracuseStep 3937967 = 5906951) B5906951
theorem B6231869 : Blo 968591 6231869 := bstep (se 3 (by rfl) ⟨1168475, by rfl⟩ : syracuseStep 6231869 = 2336951) B2336951
theorem B73865099 : Blo 968591 73865099 := bstep (se 1 (by rfl) ⟨55398824, by rfl⟩ : syracuseStep 73865099 = 110797649) B110797649
theorem B1382503 : Blo 968591 1382503 := bstep (se 1 (by rfl) ⟨1036877, by rfl⟩ : syracuseStep 1382503 = 2073755) B2073755
theorem B23632175 : Blo 968591 23632175 := bstep (se 1 (by rfl) ⟨17724131, by rfl⟩ : syracuseStep 23632175 = 35448263) B35448263
theorem B7871195 : Blo 968591 7871195 := bstep (se 1 (by rfl) ⟨5903396, by rfl⟩ : syracuseStep 7871195 = 11806793) B11806793
theorem B4725715 : Blo 968591 4725715 := bstep (se 1 (by rfl) ⟨3544286, by rfl⟩ : syracuseStep 4725715 = 7088573) B7088573
theorem B7380395 : Blo 968591 7380395 := bstep (se 1 (by rfl) ⟨5535296, by rfl⟩ : syracuseStep 7380395 = 11070593) B11070593
theorem B6989465 : Blo 968591 6989465 := bstep (se 2 (by rfl) ⟨2621049, by rfl⟩ : syracuseStep 6989465 = 5242099) B5242099
theorem B1091227 : Blo 968591 1091227 := bstep (se 1 (by rfl) ⟨818420, by rfl⟩ : syracuseStep 1091227 = 1636841) B1636841
theorem B2075071 : Blo 968591 2075071 := bstep (se 1 (by rfl) ⟨1556303, by rfl⟩ : syracuseStep 2075071 = 3112607) B3112607
theorem B1845919 : Blo 968591 1845919 := bstep (se 1 (by rfl) ⟨1384439, by rfl⟩ : syracuseStep 1845919 = 2768879) B2768879
theorem B1452923 : Blo 968591 1452923 := bstep (se 1 (by rfl) ⟨1089692, by rfl⟩ : syracuseStep 1452923 = 2179385) B2179385
theorem B1453151 : Blo 968591 1453151 := bstep (se 1 (by rfl) ⟨1089863, by rfl⟩ : syracuseStep 1453151 = 2179727) B2179727
theorem B1453775 : Blo 968591 1453775 := bstep (se 1 (by rfl) ⟨1090331, by rfl⟩ : syracuseStep 1453775 = 2180663) B2180663
theorem B3682529 : Blo 968591 3682529 := bstep (se 2 (by rfl) ⟨1380948, by rfl⟩ : syracuseStep 3682529 = 2761897) B2761897
theorem B47231819 : Blo 968591 47231819 := bstep (se 1 (by rfl) ⟨35423864, by rfl⟩ : syracuseStep 47231819 = 70847729) B70847729
theorem B5911379 : Blo 968591 5911379 := bstep (se 1 (by rfl) ⟨4433534, by rfl⟩ : syracuseStep 5911379 = 8867069) B8867069
theorem B5518439 : Blo 968591 5518439 := bstep (se 1 (by rfl) ⟨4138829, by rfl⟩ : syracuseStep 5518439 = 8277659) B8277659
theorem B14005457 : Blo 968591 14005457 := bstep (se 2 (by rfl) ⟨5252046, by rfl⟩ : syracuseStep 14005457 = 10504093) B10504093
theorem B3683819 : Blo 968591 3683819 := bstep (se 1 (by rfl) ⟨2762864, by rfl⟩ : syracuseStep 3683819 = 5525729) B5525729
theorem B3684473 : Blo 968591 3684473 := bstep (se 2 (by rfl) ⟨1381677, by rfl⟩ : syracuseStep 3684473 = 2763355) B2763355
theorem B1456511 : Blo 968591 1456511 := bstep (se 1 (by rfl) ⟨1092383, by rfl⟩ : syracuseStep 1456511 = 2184767) B2184767
theorem B11811419 : Blo 968591 11811419 := bstep (se 1 (by rfl) ⟨8858564, by rfl⟩ : syracuseStep 11811419 = 17717129) B17717129
theorem B1456895 : Blo 968591 1456895 := bstep (se 1 (by rfl) ⟨1092671, by rfl⟩ : syracuseStep 1456895 = 2185343) B2185343
theorem B1752095 : Blo 968591 1752095 := bstep (se 1 (by rfl) ⟨1314071, by rfl⟩ : syracuseStep 1752095 = 2628143) B2628143
theorem B17677487 : Blo 968591 17677487 := bstep (se 1 (by rfl) ⟨13258115, by rfl⟩ : syracuseStep 17677487 = 26516231) B26516231
theorem B1458287 : Blo 968591 1458287 := bstep (se 1 (by rfl) ⟨1093715, by rfl⟩ : syracuseStep 1458287 = 2187431) B2187431
theorem B1458335 : Blo 968591 1458335 := bstep (se 1 (by rfl) ⟨1093751, by rfl⟩ : syracuseStep 1458335 = 2187503) B2187503
theorem B1229023 : Blo 968591 1229023 := bstep (se 1 (by rfl) ⟨921767, by rfl⟩ : syracuseStep 1229023 = 1843535) B1843535
theorem B1458587 : Blo 968591 1458587 := bstep (se 1 (by rfl) ⟨1093940, by rfl⟩ : syracuseStep 1458587 = 2187881) B2187881
theorem B8307593 : Blo 968591 8307593 := bstep (se 2 (by rfl) ⟨3115347, by rfl⟩ : syracuseStep 8307593 = 6230695) B6230695
theorem B2180321 : Blo 968591 2180321 := bstep (se 2 (by rfl) ⟨817620, by rfl⟩ : syracuseStep 2180321 = 1635241) B1635241
theorem B2181203 : Blo 968591 2181203 := bstep (se 1 (by rfl) ⟨1635902, by rfl⟩ : syracuseStep 2181203 = 3271805) B3271805
theorem B969327 : Blo 968591 969327 := bstep (se 1 (by rfl) ⟨726995, by rfl⟩ : syracuseStep 969327 = 1453991) B1453991
theorem B969383 : Blo 968591 969383 := bstep (se 1 (by rfl) ⟨727037, by rfl⟩ : syracuseStep 969383 = 1454075) B1454075
theorem B3492571 : Blo 968591 3492571 := bstep (se 1 (by rfl) ⟨2619428, by rfl⟩ : syracuseStep 3492571 = 5238857) B5238857
theorem B969599 : Blo 968591 969599 := bstep (se 1 (by rfl) ⟨727199, by rfl⟩ : syracuseStep 969599 = 1454399) B1454399
theorem B2182121 : Blo 968591 2182121 := bstep (se 2 (by rfl) ⟨818295, by rfl⟩ : syracuseStep 2182121 = 1636591) B1636591
theorem B969755 : Blo 968591 969755 := bstep (se 1 (by rfl) ⟨727316, by rfl⟩ : syracuseStep 969755 = 1454633) B1454633
theorem B2182175 : Blo 968591 2182175 := bstep (se 1 (by rfl) ⟨1636631, by rfl⟩ : syracuseStep 2182175 = 3273263) B3273263
theorem B4148329 : Blo 968591 4148329 := bstep (se 2 (by rfl) ⟨1555623, by rfl⟩ : syracuseStep 4148329 = 3111247) B3111247
theorem B2182427 : Blo 968591 2182427 := bstep (se 1 (by rfl) ⟨1636820, by rfl⟩ : syracuseStep 2182427 = 3273641) B3273641
theorem B2182463 : Blo 968591 2182463 := bstep (se 1 (by rfl) ⟨1636847, by rfl⟩ : syracuseStep 2182463 = 3273695) B3273695
theorem B7359983 : Blo 968591 7359983 := bstep (se 1 (by rfl) ⟨5519987, by rfl⟩ : syracuseStep 7359983 = 11039975) B11039975
theorem B970407 : Blo 968591 970407 := bstep (se 1 (by rfl) ⟨727805, by rfl⟩ : syracuseStep 970407 = 1455611) B1455611
theorem B5525273 : Blo 968591 5525273 := bstep (se 2 (by rfl) ⟨2071977, by rfl⟩ : syracuseStep 5525273 = 4143955) B4143955
theorem B970587 : Blo 968591 970587 := bstep (se 1 (by rfl) ⟨727940, by rfl⟩ : syracuseStep 970587 = 1455881) B1455881
theorem B970607 : Blo 968591 970607 := bstep (se 1 (by rfl) ⟨727955, by rfl⟩ : syracuseStep 970607 = 1455911) B1455911
theorem B1036399 : Blo 968591 1036399 := bstep (se 1 (by rfl) ⟨777299, by rfl⟩ : syracuseStep 1036399 = 1554599) B1554599
theorem B3690623 : Blo 968591 3690623 := bstep (se 1 (by rfl) ⟨2767967, by rfl⟩ : syracuseStep 3690623 = 5535935) B5535935
theorem B970959 : Blo 968591 970959 := bstep (se 1 (by rfl) ⟨728219, by rfl⟩ : syracuseStep 970959 = 1456439) B1456439
theorem B3690791 : Blo 968591 3690791 := bstep (se 1 (by rfl) ⟨2768093, by rfl⟩ : syracuseStep 3690791 = 5536187) B5536187
theorem B971291 : Blo 968591 971291 := bstep (se 1 (by rfl) ⟨728468, by rfl⟩ : syracuseStep 971291 = 1456937) B1456937
theorem B971471 : Blo 968591 971471 := bstep (se 1 (by rfl) ⟨728603, by rfl⟩ : syracuseStep 971471 = 1457207) B1457207
theorem B24826823 : Blo 968591 24826823 := bstep (se 1 (by rfl) ⟨18620117, by rfl⟩ : syracuseStep 24826823 = 37240235) B37240235
theorem B2184263 : Blo 968591 2184263 := bstep (se 1 (by rfl) ⟨1638197, by rfl⟩ : syracuseStep 2184263 = 3276395) B3276395
theorem B971935 : Blo 968591 971935 := bstep (se 1 (by rfl) ⟨728951, by rfl⟩ : syracuseStep 971935 = 1457903) B1457903
theorem B972007 : Blo 968591 972007 := bstep (se 1 (by rfl) ⟨729005, by rfl⟩ : syracuseStep 972007 = 1458011) B1458011
theorem B2184911 : Blo 968591 2184911 := bstep (se 1 (by rfl) ⟨1638683, by rfl⟩ : syracuseStep 2184911 = 3277367) B3277367
theorem B4151405 : Blo 968591 4151405 := bstep (se 3 (by rfl) ⟨778388, by rfl⟩ : syracuseStep 4151405 = 1556777) B1556777
theorem B2185775 : Blo 968591 2185775 := bstep (se 1 (by rfl) ⟨1639331, by rfl⟩ : syracuseStep 2185775 = 3278663) B3278663
theorem B2185919 : Blo 968591 2185919 := bstep (se 1 (by rfl) ⟨1639439, by rfl⟩ : syracuseStep 2185919 = 3278879) B3278879
theorem B4152329 : Blo 968591 4152329 := bstep (se 2 (by rfl) ⟨1557123, by rfl⟩ : syracuseStep 4152329 = 3114247) B3114247
theorem B8838821 : Blo 968591 8838821 := bstep (se 4 (by rfl) ⟨828639, by rfl⟩ : syracuseStep 8838821 = 1657279) B1657279
theorem B8282411 : Blo 968591 8282411 := bstep (se 1 (by rfl) ⟨6211808, by rfl⟩ : syracuseStep 8282411 = 12423617) B12423617
theorem B3695423 : Blo 968591 3695423 := bstep (se 1 (by rfl) ⟨2771567, by rfl⟩ : syracuseStep 3695423 = 5543135) B5543135
theorem B34073111 : Blo 968591 34073111 := bstep (se 1 (by rfl) ⟨25554833, by rfl⟩ : syracuseStep 34073111 = 51109667) B51109667
theorem B8285723 : Blo 968591 8285723 := bstep (se 1 (by rfl) ⟨6214292, by rfl⟩ : syracuseStep 8285723 = 12428585) B12428585
theorem B3928105 : Blo 968591 3928105 := bstep (se 2 (by rfl) ⟨1473039, by rfl⟩ : syracuseStep 3928105 = 2946079) B2946079
theorem B3405023 : Blo 968591 3405023 := bstep (se 1 (by rfl) ⟨2553767, by rfl⟩ : syracuseStep 3405023 = 5107535) B5107535
theorem B2455393 : Blo 968591 2455393 := bstep (se 2 (by rfl) ⟨920772, by rfl⟩ : syracuseStep 2455393 = 1841545) B1841545
theorem B2456639 : Blo 968591 2456639 := bstep (se 1 (by rfl) ⟨1842479, by rfl⟩ : syracuseStep 2456639 = 3684959) B3684959
theorem B8289823 : Blo 968591 8289823 := bstep (se 1 (by rfl) ⟨6217367, by rfl⟩ : syracuseStep 8289823 = 12434735) B12434735
theorem B7863929 : Blo 968591 7863929 := bstep (se 2 (by rfl) ⟨2948973, by rfl⟩ : syracuseStep 7863929 = 5897947) B5897947
theorem B26574479 : Blo 968591 26574479 := bstep (se 1 (by rfl) ⟨19930859, by rfl⟩ : syracuseStep 26574479 = 39861719) B39861719
theorem B1638427 : Blo 968591 1638427 := bstep (se 1 (by rfl) ⟨1228820, by rfl⟩ : syracuseStep 1638427 = 2457641) B2457641
theorem B1638697 : Blo 968591 1638697 := bstep (se 2 (by rfl) ⟨614511, by rfl⟩ : syracuseStep 1638697 = 1229023) B1229023
theorem B5538395 : Blo 968591 5538395 := bstep (se 1 (by rfl) ⟨4153796, by rfl⟩ : syracuseStep 5538395 = 8307593) B8307593
theorem B46007783 : Blo 968591 46007783 := bstep (se 1 (by rfl) ⟨34505837, by rfl⟩ : syracuseStep 46007783 = 69011675) B69011675
theorem B3279527 : Blo 968591 3279527 := bstep (se 1 (by rfl) ⟨2459645, by rfl⟩ : syracuseStep 3279527 = 4919291) B4919291
theorem B2460415 : Blo 968591 2460415 := bstep (se 1 (by rfl) ⟨1845311, by rfl⟩ : syracuseStep 2460415 = 3690623) B3690623
theorem B3148555 : Blo 968591 3148555 := bstep (se 1 (by rfl) ⟨2361416, by rfl⟩ : syracuseStep 3148555 = 4722833) B4722833
theorem B2460527 : Blo 968591 2460527 := bstep (se 1 (by rfl) ⟨1845395, by rfl⟩ : syracuseStep 2460527 = 3690791) B3690791
theorem B16551215 : Blo 968591 16551215 := bstep (se 1 (by rfl) ⟨12413411, by rfl⟩ : syracuseStep 16551215 = 24826823) B24826823
theorem B2461225 : Blo 968591 2461225 := bstep (se 2 (by rfl) ⟨922959, by rfl⟩ : syracuseStep 2461225 = 1845919) B1845919
theorem B4656761 : Blo 968591 4656761 := bstep (se 2 (by rfl) ⟨1746285, by rfl⟩ : syracuseStep 4656761 = 3492571) B3492571
theorem B2625311 : Blo 968591 2625311 := bstep (se 1 (by rfl) ⟨1968983, by rfl⟩ : syracuseStep 2625311 = 3937967) B3937967
theorem B5247463 : Blo 968591 5247463 := bstep (se 1 (by rfl) ⟨3935597, by rfl⟩ : syracuseStep 5247463 = 7871195) B7871195
theorem B4920263 : Blo 968591 4920263 := bstep (se 1 (by rfl) ⟨3690197, by rfl⟩ : syracuseStep 4920263 = 7380395) B7380395
theorem B1381865 : Blo 968591 1381865 := bstep (se 2 (by rfl) ⟨518199, by rfl⟩ : syracuseStep 1381865 = 1036399) B1036399
theorem B4659643 : Blo 968591 4659643 := bstep (se 1 (by rfl) ⟨3494732, by rfl⟩ : syracuseStep 4659643 = 6989465) B6989465
theorem B22715407 : Blo 968591 22715407 := bstep (se 1 (by rfl) ⟨17036555, by rfl⟩ : syracuseStep 22715407 = 34073111) B34073111
theorem B1843337 : Blo 968591 1843337 := bstep (se 2 (by rfl) ⟨691251, by rfl⟩ : syracuseStep 1843337 = 1382503) B1382503
theorem B3940919 : Blo 968591 3940919 := bstep (se 1 (by rfl) ⟨2955689, by rfl⟩ : syracuseStep 3940919 = 5911379) B5911379
theorem B3678959 : Blo 968591 3678959 := bstep (se 1 (by rfl) ⟨2759219, by rfl⟩ : syracuseStep 3678959 = 5518439) B5518439
theorem B2270015 : Blo 968591 2270015 := bstep (se 1 (by rfl) ⟨1702511, by rfl⟩ : syracuseStep 2270015 = 3405023) B3405023
theorem B6300953 : Blo 968591 6300953 := bstep (se 2 (by rfl) ⟨2362857, by rfl⟩ : syracuseStep 6300953 = 4725715) B4725715
theorem B7874279 : Blo 968591 7874279 := bstep (se 1 (by rfl) ⟨5905709, by rfl⟩ : syracuseStep 7874279 = 11811419) B11811419
theorem B23570189 : Blo 968591 23570189 := bstep (se 3 (by rfl) ⟨4419410, by rfl⟩ : syracuseStep 23570189 = 8838821) B8838821
theorem B11053097 : Blo 968591 11053097 := bstep (se 2 (by rfl) ⟨4144911, by rfl⟩ : syracuseStep 11053097 = 8289823) B8289823
theorem B1453547 : Blo 968591 1453547 := bstep (se 1 (by rfl) ⟨1090160, by rfl⟩ : syracuseStep 1453547 = 2180321) B2180321
theorem B1093279 : Blo 968591 1093279 := bstep (se 1 (by rfl) ⟨819959, by rfl⟩ : syracuseStep 1093279 = 1639919) B1639919
theorem B1454135 : Blo 968591 1454135 := bstep (se 1 (by rfl) ⟨1090601, by rfl⟩ : syracuseStep 1454135 = 2181203) B2181203
theorem B7385255 : Blo 968591 7385255 := bstep (se 1 (by rfl) ⟨5538941, by rfl⟩ : syracuseStep 7385255 = 11077883) B11077883
theorem B1454747 : Blo 968591 1454747 := bstep (se 1 (by rfl) ⟨1091060, by rfl⟩ : syracuseStep 1454747 = 2182121) B2182121
theorem B1454783 : Blo 968591 1454783 := bstep (se 1 (by rfl) ⟨1091087, by rfl⟩ : syracuseStep 1454783 = 2182175) B2182175
theorem B1454951 : Blo 968591 1454951 := bstep (se 1 (by rfl) ⟨1091213, by rfl⟩ : syracuseStep 1454951 = 2182427) B2182427
theorem B1454969 : Blo 968591 1454969 := bstep (se 2 (by rfl) ⟨545613, by rfl⟩ : syracuseStep 1454969 = 1091227) B1091227
theorem B1454975 : Blo 968591 1454975 := bstep (se 1 (by rfl) ⟨1091231, by rfl⟩ : syracuseStep 1454975 = 2182463) B2182463
theorem B3683515 : Blo 968591 3683515 := bstep (se 1 (by rfl) ⟨2762636, by rfl⟩ : syracuseStep 3683515 = 5525273) B5525273
theorem B2766761 : Blo 968591 2766761 := bstep (se 2 (by rfl) ⟨1037535, by rfl⟩ : syracuseStep 2766761 = 2075071) B2075071
theorem B1456175 : Blo 968591 1456175 := bstep (se 1 (by rfl) ⟨1092131, by rfl⟩ : syracuseStep 1456175 = 2184263) B2184263
theorem B1456607 : Blo 968591 1456607 := bstep (se 1 (by rfl) ⟨1092455, by rfl⟩ : syracuseStep 1456607 = 2184911) B2184911
theorem B2767603 : Blo 968591 2767603 := bstep (se 1 (by rfl) ⟨2075702, by rfl⟩ : syracuseStep 2767603 = 4151405) B4151405
theorem B1457183 : Blo 968591 1457183 := bstep (se 1 (by rfl) ⟨1092887, by rfl⟩ : syracuseStep 1457183 = 2185775) B2185775
theorem B1457279 : Blo 968591 1457279 := bstep (se 1 (by rfl) ⟨1092959, by rfl⟩ : syracuseStep 1457279 = 2185919) B2185919
theorem B2768219 : Blo 968591 2768219 := bstep (se 1 (by rfl) ⟨2076164, by rfl⟩ : syracuseStep 2768219 = 4152329) B4152329
theorem B5521607 : Blo 968591 5521607 := bstep (se 1 (by rfl) ⟨4141205, by rfl⟩ : syracuseStep 5521607 = 8282411) B8282411
theorem B3195881 : Blo 968591 3195881 := bstep (se 2 (by rfl) ⟨1198455, by rfl⟩ : syracuseStep 3195881 = 2396911) B2396911
theorem B968615 : Blo 968591 968615 := bstep (se 1 (by rfl) ⟨726461, by rfl⟩ : syracuseStep 968615 = 1452923) B1452923
theorem B968767 : Blo 968591 968767 := bstep (se 1 (by rfl) ⟨726575, by rfl⟩ : syracuseStep 968767 = 1453151) B1453151
theorem B5523815 : Blo 968591 5523815 := bstep (se 1 (by rfl) ⟨4142861, by rfl⟩ : syracuseStep 5523815 = 8285723) B8285723
theorem B969183 : Blo 968591 969183 := bstep (se 1 (by rfl) ⟨726887, by rfl⟩ : syracuseStep 969183 = 1453775) B1453775
theorem B47139965 : Blo 968591 47139965 := bstep (se 3 (by rfl) ⟨8838743, by rfl⟩ : syracuseStep 47139965 = 17677487) B17677487
theorem B971007 : Blo 968591 971007 := bstep (se 1 (by rfl) ⟨728255, by rfl⟩ : syracuseStep 971007 = 1456511) B1456511
theorem B971263 : Blo 968591 971263 := bstep (se 1 (by rfl) ⟨728447, by rfl⟩ : syracuseStep 971263 = 1456895) B1456895
theorem B1168063 : Blo 968591 1168063 := bstep (se 1 (by rfl) ⟨876047, by rfl⟩ : syracuseStep 1168063 = 1752095) B1752095
theorem B17716319 : Blo 968591 17716319 := bstep (se 1 (by rfl) ⟨13287239, by rfl⟩ : syracuseStep 17716319 = 26574479) B26574479
theorem B972191 : Blo 968591 972191 := bstep (se 1 (by rfl) ⟨729143, by rfl⟩ : syracuseStep 972191 = 1458287) B1458287
theorem B972223 : Blo 968591 972223 := bstep (se 1 (by rfl) ⟨729167, by rfl⟩ : syracuseStep 972223 = 1458335) B1458335
theorem B972391 : Blo 968591 972391 := bstep (se 1 (by rfl) ⟨729293, by rfl⟩ : syracuseStep 972391 = 1458587) B1458587
theorem B9854461 : Blo 968591 9854461 := bstep (se 3 (by rfl) ⟨1847711, by rfl⟩ : syracuseStep 9854461 = 3695423) B3695423
theorem B4906655 : Blo 968591 4906655 := bstep (se 1 (by rfl) ⟨3679991, by rfl⟩ : syracuseStep 4906655 = 7359983) B7359983
theorem B4154579 : Blo 968591 4154579 := bstep (se 1 (by rfl) ⟨3115934, by rfl⟩ : syracuseStep 4154579 = 6231869) B6231869
theorem B49243399 : Blo 968591 49243399 := bstep (se 1 (by rfl) ⟨36932549, by rfl⟩ : syracuseStep 49243399 = 73865099) B73865099
theorem B5531105 : Blo 968591 5531105 := bstep (se 2 (by rfl) ⟨2074164, by rfl⟩ : syracuseStep 5531105 = 4148329) B4148329
theorem B15754783 : Blo 968591 15754783 := bstep (se 1 (by rfl) ⟨11816087, by rfl⟩ : syracuseStep 15754783 = 23632175) B23632175
theorem B5237473 : Blo 968591 5237473 := bstep (se 2 (by rfl) ⟨1964052, by rfl⟩ : syracuseStep 5237473 = 3928105) B3928105
theorem B95777477 : Blo 968591 95777477 := bstep (se 4 (by rfl) ⟨8979138, by rfl⟩ : syracuseStep 95777477 = 17958277) B17958277
theorem B3273857 : Blo 968591 3273857 := bstep (se 2 (by rfl) ⟨1227696, by rfl⟩ : syracuseStep 3273857 = 2455393) B2455393
theorem B2455019 : Blo 968591 2455019 := bstep (se 1 (by rfl) ⟨1841264, by rfl⟩ : syracuseStep 2455019 = 3682529) B3682529
theorem B31487879 : Blo 968591 31487879 := bstep (se 1 (by rfl) ⟨23615909, by rfl⟩ : syracuseStep 31487879 = 47231819) B47231819
theorem B9336971 : Blo 968591 9336971 := bstep (se 1 (by rfl) ⟨7002728, by rfl⟩ : syracuseStep 9336971 = 14005457) B14005457
theorem B2455879 : Blo 968591 2455879 := bstep (se 1 (by rfl) ⟨1841909, by rfl⟩ : syracuseStep 2455879 = 3683819) B3683819
theorem B2456315 : Blo 968591 2456315 := bstep (se 1 (by rfl) ⟨1842236, by rfl⟩ : syracuseStep 2456315 = 3684473) B3684473
theorem B1637759 : Blo 968591 1637759 := bstep (se 1 (by rfl) ⟨1228319, by rfl⟩ : syracuseStep 1637759 = 2456639) B2456639
theorem B5242619 : Blo 968591 5242619 := bstep (se 1 (by rfl) ⟨3931964, by rfl⟩ : syracuseStep 5242619 = 7863929) B7863929
theorem B4915565 : Blo 968591 4915565 := bstep (se 3 (by rfl) ⟨921668, by rfl⟩ : syracuseStep 4915565 = 1843337) B1843337
theorem B2130587 : Blo 968591 2130587 := bstep (se 1 (by rfl) ⟨1597940, by rfl⟩ : syracuseStep 2130587 = 3195881) B3195881
theorem B30671855 : Blo 968591 30671855 := bstep (se 1 (by rfl) ⟨23003891, by rfl⟩ : syracuseStep 30671855 = 46007783) B46007783
theorem B1640351 : Blo 968591 1640351 := bstep (se 1 (by rfl) ⟨1230263, by rfl⟩ : syracuseStep 1640351 = 2460527) B2460527
theorem B21006377 : Blo 968591 21006377 := bstep (se 2 (by rfl) ⟨7877391, by rfl⟩ : syracuseStep 21006377 = 15754783) B15754783
theorem B31426643 : Blo 968591 31426643 := bstep (se 1 (by rfl) ⟨23569982, by rfl⟩ : syracuseStep 31426643 = 47139965) B47139965
theorem B3280175 : Blo 968591 3280175 := bstep (se 1 (by rfl) ⟨2460131, by rfl⟩ : syracuseStep 3280175 = 4920263) B4920263
theorem B6983297 : Blo 968591 6983297 := bstep (se 2 (by rfl) ⟨2618736, by rfl⟩ : syracuseStep 6983297 = 5237473) B5237473
theorem B3280553 : Blo 968591 3280553 := bstep (se 2 (by rfl) ⟨1230207, by rfl⟩ : syracuseStep 3280553 = 2460415) B2460415
theorem B4198073 : Blo 968591 4198073 := bstep (se 2 (by rfl) ⟨1574277, by rfl⟩ : syracuseStep 4198073 = 3148555) B3148555
theorem B3281633 : Blo 968591 3281633 := bstep (se 2 (by rfl) ⟨1230612, by rfl⟩ : syracuseStep 3281633 = 2461225) B2461225
theorem B2627279 : Blo 968591 2627279 := bstep (se 1 (by rfl) ⟨1970459, by rfl⟩ : syracuseStep 2627279 = 3940919) B3940919
theorem B1513343 : Blo 968591 1513343 := bstep (se 1 (by rfl) ⟨1135007, by rfl⟩ : syracuseStep 1513343 = 2270015) B2270015
theorem B4200635 : Blo 968591 4200635 := bstep (se 1 (by rfl) ⟨3150476, by rfl⟩ : syracuseStep 4200635 = 6300953) B6300953
theorem B5249519 : Blo 968591 5249519 := bstep (se 1 (by rfl) ⟨3937139, by rfl⟩ : syracuseStep 5249519 = 7874279) B7874279
theorem B4923503 : Blo 968591 4923503 := bstep (se 1 (by rfl) ⟨3692627, by rfl⟩ : syracuseStep 4923503 = 7385255) B7385255
theorem B1844507 : Blo 968591 1844507 := bstep (se 1 (by rfl) ⟨1383380, by rfl⟩ : syracuseStep 1844507 = 2766761) B2766761
theorem B30287209 : Blo 968591 30287209 := bstep (se 2 (by rfl) ⟨11357703, by rfl⟩ : syracuseStep 30287209 = 22715407) B22715407
theorem B1845479 : Blo 968591 1845479 := bstep (se 1 (by rfl) ⟨1384109, by rfl⟩ : syracuseStep 1845479 = 2768219) B2768219
theorem B1091839 : Blo 968591 1091839 := bstep (se 1 (by rfl) ⟨818879, by rfl⟩ : syracuseStep 1091839 = 1637759) B1637759
theorem B3681071 : Blo 968591 3681071 := bstep (se 1 (by rfl) ⟨2760803, by rfl⟩ : syracuseStep 3681071 = 5521607) B5521607
theorem B3682543 : Blo 968591 3682543 := bstep (se 1 (by rfl) ⟨2761907, by rfl⟩ : syracuseStep 3682543 = 5523815) B5523815
theorem B11810879 : Blo 968591 11810879 := bstep (se 1 (by rfl) ⟨8858159, by rfl⟩ : syracuseStep 11810879 = 17716319) B17716319
theorem B3684973 : Blo 968591 3684973 := bstep (se 3 (by rfl) ⟨690932, by rfl⟩ : syracuseStep 3684973 = 1381865) B1381865
theorem B24918677 : Blo 968591 24918677 := bstep (se 6 (by rfl) ⟨584031, by rfl⟩ : syracuseStep 24918677 = 1168063) B1168063
theorem B1457705 : Blo 968591 1457705 := bstep (se 2 (by rfl) ⟨546639, by rfl⟩ : syracuseStep 1457705 = 1093279) B1093279
theorem B83967677 : Blo 968591 83967677 := bstep (se 3 (by rfl) ⟨15743939, by rfl⟩ : syracuseStep 83967677 = 31487879) B31487879
theorem B1050525845 : Blo 968591 1050525845 := bstep (se 6 (by rfl) ⟨24621699, by rfl⟩ : syracuseStep 1050525845 = 49243399) B49243399
theorem B6996617 : Blo 968591 6996617 := bstep (se 2 (by rfl) ⟨2623731, by rfl⟩ : syracuseStep 6996617 = 5247463) B5247463
theorem B2769719 : Blo 968591 2769719 := bstep (se 1 (by rfl) ⟨2077289, by rfl⟩ : syracuseStep 2769719 = 4154579) B4154579
theorem B3687403 : Blo 968591 3687403 := bstep (se 1 (by rfl) ⟨2765552, by rfl⟩ : syracuseStep 3687403 = 5531105) B5531105
theorem B15713459 : Blo 968591 15713459 := bstep (se 1 (by rfl) ⟨11785094, by rfl⟩ : syracuseStep 15713459 = 23570189) B23570189
theorem B969031 : Blo 968591 969031 := bstep (se 1 (by rfl) ⟨726773, by rfl⟩ : syracuseStep 969031 = 1453547) B1453547
theorem B969423 : Blo 968591 969423 := bstep (se 1 (by rfl) ⟨727067, by rfl⟩ : syracuseStep 969423 = 1454135) B1454135
theorem B969831 : Blo 968591 969831 := bstep (se 1 (by rfl) ⟨727373, by rfl⟩ : syracuseStep 969831 = 1454747) B1454747
theorem B969855 : Blo 968591 969855 := bstep (se 1 (by rfl) ⟨727391, by rfl⟩ : syracuseStep 969855 = 1454783) B1454783
theorem B63851651 : Blo 968591 63851651 := bstep (se 1 (by rfl) ⟨47888738, by rfl⟩ : syracuseStep 63851651 = 95777477) B95777477
theorem B969967 : Blo 968591 969967 := bstep (se 1 (by rfl) ⟨727475, by rfl⟩ : syracuseStep 969967 = 1454951) B1454951
theorem B6212857 : Blo 968591 6212857 := bstep (se 2 (by rfl) ⟨2329821, by rfl⟩ : syracuseStep 6212857 = 4659643) B4659643
theorem B969979 : Blo 968591 969979 := bstep (se 1 (by rfl) ⟨727484, by rfl⟩ : syracuseStep 969979 = 1454969) B1454969
theorem B969983 : Blo 968591 969983 := bstep (se 1 (by rfl) ⟨727487, by rfl⟩ : syracuseStep 969983 = 1454975) B1454975
theorem B2182571 : Blo 968591 2182571 := bstep (se 1 (by rfl) ⟨1636928, by rfl⟩ : syracuseStep 2182571 = 3273857) B3273857
theorem B3690137 : Blo 968591 3690137 := bstep (se 2 (by rfl) ⟨1383801, by rfl⟩ : syracuseStep 3690137 = 2767603) B2767603
theorem B970783 : Blo 968591 970783 := bstep (se 1 (by rfl) ⟨728087, by rfl⟩ : syracuseStep 970783 = 1456175) B1456175
theorem B971071 : Blo 968591 971071 := bstep (se 1 (by rfl) ⟨728303, by rfl⟩ : syracuseStep 971071 = 1456607) B1456607
theorem B971455 : Blo 968591 971455 := bstep (se 1 (by rfl) ⟨728591, by rfl⟩ : syracuseStep 971455 = 1457183) B1457183
theorem B7000829 : Blo 968591 7000829 := bstep (se 3 (by rfl) ⟨1312655, by rfl⟩ : syracuseStep 7000829 = 2625311) B2625311
theorem B971519 : Blo 968591 971519 := bstep (se 1 (by rfl) ⟨728639, by rfl⟩ : syracuseStep 971519 = 1457279) B1457279
theorem B3495079 : Blo 968591 3495079 := bstep (se 1 (by rfl) ⟨2621309, by rfl⟩ : syracuseStep 3495079 = 5242619) B5242619
theorem B2184569 : Blo 968591 2184569 := bstep (se 2 (by rfl) ⟨819213, by rfl⟩ : syracuseStep 2184569 = 1638427) B1638427
theorem B2184929 : Blo 968591 2184929 := bstep (se 2 (by rfl) ⟨819348, by rfl⟩ : syracuseStep 2184929 = 1638697) B1638697
theorem B3692263 : Blo 968591 3692263 := bstep (se 1 (by rfl) ⟨2769197, by rfl⟩ : syracuseStep 3692263 = 5538395) B5538395
theorem B2186351 : Blo 968591 2186351 := bstep (se 1 (by rfl) ⟨1639763, by rfl⟩ : syracuseStep 2186351 = 3279527) B3279527
theorem B11034143 : Blo 968591 11034143 := bstep (se 1 (by rfl) ⟨8275607, by rfl⟩ : syracuseStep 11034143 = 16551215) B16551215
theorem B3104507 : Blo 968591 3104507 := bstep (se 1 (by rfl) ⟨2328380, by rfl⟩ : syracuseStep 3104507 = 4656761) B4656761
theorem B3271103 : Blo 968591 3271103 := bstep (se 1 (by rfl) ⟨2453327, by rfl⟩ : syracuseStep 3271103 = 4906655) B4906655
theorem B2452639 : Blo 968591 2452639 := bstep (se 1 (by rfl) ⟨1839479, by rfl⟩ : syracuseStep 2452639 = 3678959) B3678959
theorem B7368731 : Blo 968591 7368731 := bstep (se 1 (by rfl) ⟨5526548, by rfl⟩ : syracuseStep 7368731 = 11053097) B11053097
theorem B4911353 : Blo 968591 4911353 := bstep (se 2 (by rfl) ⟨1841757, by rfl⟩ : syracuseStep 4911353 = 3683515) B3683515
theorem B3274505 : Blo 968591 3274505 := bstep (se 2 (by rfl) ⟨1227939, by rfl⟩ : syracuseStep 3274505 = 2455879) B2455879
theorem B1636679 : Blo 968591 1636679 := bstep (se 1 (by rfl) ⟨1227509, by rfl⟩ : syracuseStep 1636679 = 2455019) B2455019
theorem B6224647 : Blo 968591 6224647 := bstep (se 1 (by rfl) ⟨4668485, by rfl⟩ : syracuseStep 6224647 = 9336971) B9336971
theorem B1637543 : Blo 968591 1637543 := bstep (se 1 (by rfl) ⟨1228157, by rfl⟩ : syracuseStep 1637543 = 2456315) B2456315
theorem B13139281 : Blo 968591 13139281 := bstep (se 2 (by rfl) ⟨4927230, by rfl⟩ : syracuseStep 13139281 = 9854461) B9854461
theorem B700350563 : Blo 968591 700350563 := bstep (se 1 (by rfl) ⟨525262922, by rfl⟩ : syracuseStep 700350563 = 1050525845) B1050525845
theorem B3277043 : Blo 968591 3277043 := bstep (se 1 (by rfl) ⟨2457782, by rfl⟩ : syracuseStep 3277043 = 4915565) B4915565
theorem B20447903 : Blo 968591 20447903 := bstep (se 1 (by rfl) ⟨15335927, by rfl⟩ : syracuseStep 20447903 = 30671855) B30671855
theorem B4916537 : Blo 968591 4916537 := bstep (se 2 (by rfl) ⟨1843701, by rfl⟩ : syracuseStep 4916537 = 3687403) B3687403
theorem B42567767 : Blo 968591 42567767 := bstep (se 1 (by rfl) ⟨31925825, by rfl⟩ : syracuseStep 42567767 = 63851651) B63851651
theorem B4655531 : Blo 968591 4655531 := bstep (se 1 (by rfl) ⟨3491648, by rfl⟩ : syracuseStep 4655531 = 6983297) B6983297
theorem B2460091 : Blo 968591 2460091 := bstep (se 1 (by rfl) ⟨1845068, by rfl⟩ : syracuseStep 2460091 = 3690137) B3690137
theorem B4035581 : Blo 968591 4035581 := bstep (se 3 (by rfl) ⟨756671, by rfl⟩ : syracuseStep 4035581 = 1513343) B1513343
theorem B3282335 : Blo 968591 3282335 := bstep (se 1 (by rfl) ⟨2461751, by rfl⟩ : syracuseStep 3282335 = 4923503) B4923503
theorem B4660105 : Blo 968591 4660105 := bstep (se 2 (by rfl) ⟨1747539, by rfl⟩ : syracuseStep 4660105 = 3495079) B3495079
theorem B4923017 : Blo 968591 4923017 := bstep (se 2 (by rfl) ⟨1846131, by rfl⟩ : syracuseStep 4923017 = 3692263) B3692263
theorem B8299529 : Blo 968591 8299529 := bstep (se 2 (by rfl) ⟨3112323, by rfl⟩ : syracuseStep 8299529 = 6224647) B6224647
theorem B7873919 : Blo 968591 7873919 := bstep (se 1 (by rfl) ⟨5905439, by rfl⟩ : syracuseStep 7873919 = 11810879) B11810879
theorem B1091119 : Blo 968591 1091119 := bstep (se 1 (by rfl) ⟨818339, by rfl⟩ : syracuseStep 1091119 = 1636679) B1636679
theorem B1091695 : Blo 968591 1091695 := bstep (se 1 (by rfl) ⟨818771, by rfl⟩ : syracuseStep 1091695 = 1637543) B1637543
theorem B55978451 : Blo 968591 55978451 := bstep (se 1 (by rfl) ⟨41983838, by rfl⟩ : syracuseStep 55978451 = 83967677) B83967677
theorem B4664411 : Blo 968591 4664411 := bstep (se 1 (by rfl) ⟨3498308, by rfl⟩ : syracuseStep 4664411 = 6996617) B6996617
theorem B1420391 : Blo 968591 1420391 := bstep (se 1 (by rfl) ⟨1065293, by rfl⟩ : syracuseStep 1420391 = 2130587) B2130587
theorem B1093567 : Blo 968591 1093567 := bstep (se 1 (by rfl) ⟨820175, by rfl⟩ : syracuseStep 1093567 = 1640351) B1640351
theorem B14004251 : Blo 968591 14004251 := bstep (se 1 (by rfl) ⟨10503188, by rfl⟩ : syracuseStep 14004251 = 21006377) B21006377
theorem B20951095 : Blo 968591 20951095 := bstep (se 1 (by rfl) ⟨15713321, by rfl⟩ : syracuseStep 20951095 = 31426643) B31426643
theorem B40382945 : Blo 968591 40382945 := bstep (se 2 (by rfl) ⟨15143604, by rfl⟩ : syracuseStep 40382945 = 30287209) B30287209
theorem B7385917 : Blo 968591 7385917 := bstep (se 3 (by rfl) ⟨1384859, by rfl⟩ : syracuseStep 7385917 = 2769719) B2769719
theorem B1455047 : Blo 968591 1455047 := bstep (se 1 (by rfl) ⟨1091285, by rfl⟩ : syracuseStep 1455047 = 2182571) B2182571
theorem B1455785 : Blo 968591 1455785 := bstep (se 2 (by rfl) ⟨545919, by rfl⟩ : syracuseStep 1455785 = 1091839) B1091839
theorem B4667219 : Blo 968591 4667219 := bstep (se 1 (by rfl) ⟨3500414, by rfl⟩ : syracuseStep 4667219 = 7000829) B7000829
theorem B1456379 : Blo 968591 1456379 := bstep (se 1 (by rfl) ⟨1092284, by rfl⟩ : syracuseStep 1456379 = 2184569) B2184569
theorem B1751519 : Blo 968591 1751519 := bstep (se 1 (by rfl) ⟨1313639, by rfl⟩ : syracuseStep 1751519 = 2627279) B2627279
theorem B1456619 : Blo 968591 1456619 := bstep (se 1 (by rfl) ⟨1092464, by rfl⟩ : syracuseStep 1456619 = 2184929) B2184929
theorem B2800423 : Blo 968591 2800423 := bstep (se 1 (by rfl) ⟨2100317, by rfl⟩ : syracuseStep 2800423 = 4200635) B4200635
theorem B1457567 : Blo 968591 1457567 := bstep (se 1 (by rfl) ⟨1093175, by rfl⟩ : syracuseStep 1457567 = 2186351) B2186351
theorem B7356095 : Blo 968591 7356095 := bstep (se 1 (by rfl) ⟨5517071, by rfl⟩ : syracuseStep 7356095 = 11034143) B11034143
theorem B1229671 : Blo 968591 1229671 := bstep (se 1 (by rfl) ⟨922253, by rfl⟩ : syracuseStep 1229671 = 1844507) B1844507
theorem B1230319 : Blo 968591 1230319 := bstep (se 1 (by rfl) ⟨922739, by rfl⟩ : syracuseStep 1230319 = 1845479) B1845479
theorem B2180735 : Blo 968591 2180735 := bstep (se 1 (by rfl) ⟨1635551, by rfl⟩ : syracuseStep 2180735 = 3271103) B3271103
theorem B2183003 : Blo 968591 2183003 := bstep (se 1 (by rfl) ⟨1637252, by rfl⟩ : syracuseStep 2183003 = 3274505) B3274505
theorem B17519041 : Blo 968591 17519041 := bstep (se 2 (by rfl) ⟨6569640, by rfl⟩ : syracuseStep 17519041 = 13139281) B13139281
theorem B11194861 : Blo 968591 11194861 := bstep (se 3 (by rfl) ⟨2099036, by rfl⟩ : syracuseStep 11194861 = 4198073) B4198073
theorem B8278685 : Blo 968591 8278685 := bstep (se 3 (by rfl) ⟨1552253, by rfl⟩ : syracuseStep 8278685 = 3104507) B3104507
theorem B971803 : Blo 968591 971803 := bstep (se 1 (by rfl) ⟨728852, by rfl⟩ : syracuseStep 971803 = 1457705) B1457705
theorem B10475639 : Blo 968591 10475639 := bstep (se 1 (by rfl) ⟨7856729, by rfl⟩ : syracuseStep 10475639 = 15713459) B15713459
theorem B2186783 : Blo 968591 2186783 := bstep (se 1 (by rfl) ⟨1640087, by rfl⟩ : syracuseStep 2186783 = 3280175) B3280175
theorem B2187035 : Blo 968591 2187035 := bstep (se 1 (by rfl) ⟨1640276, by rfl⟩ : syracuseStep 2187035 = 3280553) B3280553
theorem B2187755 : Blo 968591 2187755 := bstep (se 1 (by rfl) ⟨1640816, by rfl⟩ : syracuseStep 2187755 = 3281633) B3281633
theorem B3270185 : Blo 968591 3270185 := bstep (se 2 (by rfl) ⟨1226319, by rfl⟩ : syracuseStep 3270185 = 2452639) B2452639
theorem B3499679 : Blo 968591 3499679 := bstep (se 1 (by rfl) ⟨2624759, by rfl⟩ : syracuseStep 3499679 = 5249519) B5249519
theorem B8283809 : Blo 968591 8283809 := bstep (se 2 (by rfl) ⟨3106428, by rfl⟩ : syracuseStep 8283809 = 6212857) B6212857
theorem B4910057 : Blo 968591 4910057 := bstep (se 2 (by rfl) ⟨1841271, by rfl⟩ : syracuseStep 4910057 = 3682543) B3682543
theorem B2454047 : Blo 968591 2454047 := bstep (se 1 (by rfl) ⟨1840535, by rfl⟩ : syracuseStep 2454047 = 3681071) B3681071
theorem B4912487 : Blo 968591 4912487 := bstep (se 1 (by rfl) ⟨3684365, by rfl⟩ : syracuseStep 4912487 = 7368731) B7368731
theorem B3274235 : Blo 968591 3274235 := bstep (se 1 (by rfl) ⟨2455676, by rfl⟩ : syracuseStep 3274235 = 4911353) B4911353
theorem B4913297 : Blo 968591 4913297 := bstep (se 2 (by rfl) ⟨1842486, by rfl⟩ : syracuseStep 4913297 = 3684973) B3684973
theorem B16612451 : Blo 968591 16612451 := bstep (se 1 (by rfl) ⟨12459338, by rfl⟩ : syracuseStep 16612451 = 24918677) B24918677
theorem B13631935 : Blo 968591 13631935 := bstep (se 1 (by rfl) ⟨10223951, by rfl⟩ : syracuseStep 13631935 = 20447903) B20447903
theorem B3277691 : Blo 968591 3277691 := bstep (se 1 (by rfl) ⟨2458268, by rfl⟩ : syracuseStep 3277691 = 4916537) B4916537
theorem B1639561 : Blo 968591 1639561 := bstep (se 2 (by rfl) ⟨614835, by rfl⟩ : syracuseStep 1639561 = 1229671) B1229671
theorem B28378511 : Blo 968591 28378511 := bstep (se 1 (by rfl) ⟨21283883, by rfl⟩ : syracuseStep 28378511 = 42567767) B42567767
theorem B1640425 : Blo 968591 1640425 := bstep (se 2 (by rfl) ⟨615159, by rfl⟩ : syracuseStep 1640425 = 1230319) B1230319
theorem B3280121 : Blo 968591 3280121 := bstep (se 2 (by rfl) ⟨1230045, by rfl⟩ : syracuseStep 3280121 = 2460091) B2460091
theorem B2690387 : Blo 968591 2690387 := bstep (se 1 (by rfl) ⟨2017790, by rfl⟩ : syracuseStep 2690387 = 4035581) B4035581
theorem B6983759 : Blo 968591 6983759 := bstep (se 1 (by rfl) ⟨5237819, by rfl⟩ : syracuseStep 6983759 = 10475639) B10475639
theorem B3282011 : Blo 968591 3282011 := bstep (se 1 (by rfl) ⟨2461508, by rfl⟩ : syracuseStep 3282011 = 4923017) B4923017
theorem B5249279 : Blo 968591 5249279 := bstep (se 1 (by rfl) ⟨3936959, by rfl⟩ : syracuseStep 5249279 = 7873919) B7873919
theorem B2333119 : Blo 968591 2333119 := bstep (se 1 (by rfl) ⟨1749839, by rfl⟩ : syracuseStep 2333119 = 3499679) B3499679
theorem B1453823 : Blo 968591 1453823 := bstep (se 1 (by rfl) ⟨1090367, by rfl⟩ : syracuseStep 1453823 = 2180735) B2180735
theorem B1454825 : Blo 968591 1454825 := bstep (se 2 (by rfl) ⟨545559, by rfl⟩ : syracuseStep 1454825 = 1091119) B1091119
theorem B1455335 : Blo 968591 1455335 := bstep (se 1 (by rfl) ⟨1091501, by rfl⟩ : syracuseStep 1455335 = 2183003) B2183003
theorem B1455593 : Blo 968591 1455593 := bstep (se 2 (by rfl) ⟨545847, by rfl⟩ : syracuseStep 1455593 = 1091695) B1091695
theorem B5519123 : Blo 968591 5519123 := bstep (se 1 (by rfl) ⟨4139342, by rfl⟩ : syracuseStep 5519123 = 8278685) B8278685
theorem B1457855 : Blo 968591 1457855 := bstep (se 1 (by rfl) ⟨1093391, by rfl⟩ : syracuseStep 1457855 = 2186783) B2186783
theorem B1458023 : Blo 968591 1458023 := bstep (se 1 (by rfl) ⟨1093517, by rfl⟩ : syracuseStep 1458023 = 2187035) B2187035
theorem B1458089 : Blo 968591 1458089 := bstep (se 2 (by rfl) ⟨546783, by rfl⟩ : syracuseStep 1458089 = 1093567) B1093567
theorem B27934793 : Blo 968591 27934793 := bstep (se 2 (by rfl) ⟨10475547, by rfl⟩ : syracuseStep 27934793 = 20951095) B20951095
theorem B1458503 : Blo 968591 1458503 := bstep (se 1 (by rfl) ⟨1093877, by rfl⟩ : syracuseStep 1458503 = 2187755) B2187755
theorem B14926481 : Blo 968591 14926481 := bstep (se 2 (by rfl) ⟨5597430, by rfl⟩ : syracuseStep 14926481 = 11194861) B11194861
theorem B2180123 : Blo 968591 2180123 := bstep (se 1 (by rfl) ⟨1635092, by rfl⟩ : syracuseStep 2180123 = 3270185) B3270185
theorem B9847889 : Blo 968591 9847889 := bstep (se 2 (by rfl) ⟨3692958, by rfl⟩ : syracuseStep 9847889 = 7385917) B7385917
theorem B5522539 : Blo 968591 5522539 := bstep (se 1 (by rfl) ⟨4141904, by rfl⟩ : syracuseStep 5522539 = 8283809) B8283809
theorem B3787709 : Blo 968591 3787709 := bstep (se 3 (by rfl) ⟨710195, by rfl⟩ : syracuseStep 3787709 = 1420391) B1420391
theorem B26921963 : Blo 968591 26921963 := bstep (se 1 (by rfl) ⟨20191472, by rfl⟩ : syracuseStep 26921963 = 40382945) B40382945
theorem B970031 : Blo 968591 970031 := bstep (se 1 (by rfl) ⟨727523, by rfl⟩ : syracuseStep 970031 = 1455047) B1455047
theorem B2182823 : Blo 968591 2182823 := bstep (se 1 (by rfl) ⟨1637117, by rfl⟩ : syracuseStep 2182823 = 3274235) B3274235
theorem B970523 : Blo 968591 970523 := bstep (se 1 (by rfl) ⟨727892, by rfl⟩ : syracuseStep 970523 = 1455785) B1455785
theorem B6213473 : Blo 968591 6213473 := bstep (se 2 (by rfl) ⟨2330052, by rfl⟩ : syracuseStep 6213473 = 4660105) B4660105
theorem B970919 : Blo 968591 970919 := bstep (se 1 (by rfl) ⟨728189, by rfl⟩ : syracuseStep 970919 = 1456379) B1456379
theorem B1167679 : Blo 968591 1167679 := bstep (se 1 (by rfl) ⟨875759, by rfl⟩ : syracuseStep 1167679 = 1751519) B1751519
theorem B971079 : Blo 968591 971079 := bstep (se 1 (by rfl) ⟨728309, by rfl⟩ : syracuseStep 971079 = 1456619) B1456619
theorem B971711 : Blo 968591 971711 := bstep (se 1 (by rfl) ⟨728783, by rfl⟩ : syracuseStep 971711 = 1457567) B1457567
theorem B4904063 : Blo 968591 4904063 := bstep (se 1 (by rfl) ⟨3678047, by rfl⟩ : syracuseStep 4904063 = 7356095) B7356095
theorem B466900375 : Blo 968591 466900375 := bstep (se 1 (by rfl) ⟨350175281, by rfl⟩ : syracuseStep 466900375 = 700350563) B700350563
theorem B2184695 : Blo 968591 2184695 := bstep (se 1 (by rfl) ⟨1638521, by rfl⟩ : syracuseStep 2184695 = 3277043) B3277043
theorem B3103687 : Blo 968591 3103687 := bstep (se 1 (by rfl) ⟨2327765, by rfl⟩ : syracuseStep 3103687 = 4655531) B4655531
theorem B2188223 : Blo 968591 2188223 := bstep (se 1 (by rfl) ⟨1641167, by rfl⟩ : syracuseStep 2188223 = 3282335) B3282335
theorem B23358721 : Blo 968591 23358721 := bstep (se 2 (by rfl) ⟨8759520, by rfl⟩ : syracuseStep 23358721 = 17519041) B17519041
theorem B5533019 : Blo 968591 5533019 := bstep (se 1 (by rfl) ⟨4149764, by rfl⟩ : syracuseStep 5533019 = 8299529) B8299529
theorem B37318967 : Blo 968591 37318967 := bstep (se 1 (by rfl) ⟨27989225, by rfl⟩ : syracuseStep 37318967 = 55978451) B55978451
theorem B3273371 : Blo 968591 3273371 := bstep (se 1 (by rfl) ⟨2455028, by rfl⟩ : syracuseStep 3273371 = 4910057) B4910057
theorem B3109607 : Blo 968591 3109607 := bstep (se 1 (by rfl) ⟨2332205, by rfl⟩ : syracuseStep 3109607 = 4664411) B4664411
theorem B9336167 : Blo 968591 9336167 := bstep (se 1 (by rfl) ⟨7002125, by rfl⟩ : syracuseStep 9336167 = 14004251) B14004251
theorem B1636031 : Blo 968591 1636031 := bstep (se 1 (by rfl) ⟨1227023, by rfl⟩ : syracuseStep 1636031 = 2454047) B2454047
theorem B3274991 : Blo 968591 3274991 := bstep (se 1 (by rfl) ⟨2456243, by rfl⟩ : syracuseStep 3274991 = 4912487) B4912487
theorem B3733897 : Blo 968591 3733897 := bstep (se 2 (by rfl) ⟨1400211, by rfl⟩ : syracuseStep 3733897 = 2800423) B2800423
theorem B3111479 : Blo 968591 3111479 := bstep (se 1 (by rfl) ⟨2333609, by rfl⟩ : syracuseStep 3111479 = 4667219) B4667219
theorem B3275531 : Blo 968591 3275531 := bstep (se 1 (by rfl) ⟨2456648, by rfl⟩ : syracuseStep 3275531 = 4913297) B4913297
theorem B11074967 : Blo 968591 11074967 := bstep (se 1 (by rfl) ⟨8306225, by rfl⟩ : syracuseStep 11074967 = 16612451) B16612451
theorem B4655839 : Blo 968591 4655839 := bstep (se 1 (by rfl) ⟨3491879, by rfl⟩ : syracuseStep 4655839 = 6983759) B6983759
theorem B622533833 : Blo 968591 622533833 := bstep (se 2 (by rfl) ⟨233450187, by rfl⟩ : syracuseStep 622533833 = 466900375) B466900375
theorem B10100557 : Blo 968591 10100557 := bstep (se 3 (by rfl) ⟨1893854, by rfl⟩ : syracuseStep 10100557 = 3787709) B3787709
theorem B24879311 : Blo 968591 24879311 := bstep (se 1 (by rfl) ⟨18659483, by rfl⟩ : syracuseStep 24879311 = 37318967) B37318967
theorem B2073071 : Blo 968591 2073071 := bstep (se 1 (by rfl) ⟨1554803, by rfl⟩ : syracuseStep 2073071 = 3109607) B3109607
theorem B1090687 : Blo 968591 1090687 := bstep (se 1 (by rfl) ⟨818015, by rfl⟩ : syracuseStep 1090687 = 1636031) B1636031
theorem B3679415 : Blo 968591 3679415 := bstep (se 1 (by rfl) ⟨2759561, by rfl⟩ : syracuseStep 3679415 = 5519123) B5519123
theorem B4138249 : Blo 968591 4138249 := bstep (se 2 (by rfl) ⟨1551843, by rfl⟩ : syracuseStep 4138249 = 3103687) B3103687
theorem B2074319 : Blo 968591 2074319 := bstep (se 1 (by rfl) ⟨1555739, by rfl⟩ : syracuseStep 2074319 = 3111479) B3111479
theorem B7383311 : Blo 968591 7383311 := bstep (se 1 (by rfl) ⟨5537483, by rfl⟩ : syracuseStep 7383311 = 11074967) B11074967
theorem B18623195 : Blo 968591 18623195 := bstep (se 1 (by rfl) ⟨13967396, by rfl⟩ : syracuseStep 18623195 = 27934793) B27934793
theorem B1453415 : Blo 968591 1453415 := bstep (se 1 (by rfl) ⟨1090061, by rfl⟩ : syracuseStep 1453415 = 2180123) B2180123
theorem B6565259 : Blo 968591 6565259 := bstep (se 1 (by rfl) ⟨4923944, by rfl⟩ : syracuseStep 6565259 = 9847889) B9847889
theorem B18919007 : Blo 968591 18919007 := bstep (se 1 (by rfl) ⟨14189255, by rfl⟩ : syracuseStep 18919007 = 28378511) B28378511
theorem B1455215 : Blo 968591 1455215 := bstep (se 1 (by rfl) ⟨1091411, by rfl⟩ : syracuseStep 1455215 = 2182823) B2182823
theorem B4142315 : Blo 968591 4142315 := bstep (se 1 (by rfl) ⟨3106736, by rfl⟩ : syracuseStep 4142315 = 6213473) B6213473
theorem B1456463 : Blo 968591 1456463 := bstep (se 1 (by rfl) ⟨1092347, by rfl⟩ : syracuseStep 1456463 = 2184695) B2184695
theorem B31144961 : Blo 968591 31144961 := bstep (se 2 (by rfl) ⟨11679360, by rfl⟩ : syracuseStep 31144961 = 23358721) B23358721
theorem B1556905 : Blo 968591 1556905 := bstep (se 2 (by rfl) ⟨583839, by rfl⟩ : syracuseStep 1556905 = 1167679) B1167679
theorem B1458815 : Blo 968591 1458815 := bstep (se 1 (by rfl) ⟨1094111, by rfl⟩ : syracuseStep 1458815 = 2188223) B2188223
theorem B3688679 : Blo 968591 3688679 := bstep (se 1 (by rfl) ⟨2766509, by rfl⟩ : syracuseStep 3688679 = 5533019) B5533019
theorem B969215 : Blo 968591 969215 := bstep (se 1 (by rfl) ⟨726911, by rfl⟩ : syracuseStep 969215 = 1453823) B1453823
theorem B2182247 : Blo 968591 2182247 := bstep (se 1 (by rfl) ⟨1636685, by rfl⟩ : syracuseStep 2182247 = 3273371) B3273371
theorem B969883 : Blo 968591 969883 := bstep (se 1 (by rfl) ⟨727412, by rfl⟩ : syracuseStep 969883 = 1454825) B1454825
theorem B970223 : Blo 968591 970223 := bstep (se 1 (by rfl) ⟨727667, by rfl⟩ : syracuseStep 970223 = 1455335) B1455335
theorem B970395 : Blo 968591 970395 := bstep (se 1 (by rfl) ⟨727796, by rfl⟩ : syracuseStep 970395 = 1455593) B1455593
theorem B2183327 : Blo 968591 2183327 := bstep (se 1 (by rfl) ⟨1637495, by rfl⟩ : syracuseStep 2183327 = 3274991) B3274991
theorem B2183687 : Blo 968591 2183687 := bstep (se 1 (by rfl) ⟨1637765, by rfl⟩ : syracuseStep 2183687 = 3275531) B3275531
theorem B971903 : Blo 968591 971903 := bstep (se 1 (by rfl) ⟨728927, by rfl⟩ : syracuseStep 971903 = 1457855) B1457855
theorem B972015 : Blo 968591 972015 := bstep (se 1 (by rfl) ⟨729011, by rfl⟩ : syracuseStep 972015 = 1458023) B1458023
theorem B972059 : Blo 968591 972059 := bstep (se 1 (by rfl) ⟨729044, by rfl⟩ : syracuseStep 972059 = 1458089) B1458089
theorem B972335 : Blo 968591 972335 := bstep (se 1 (by rfl) ⟨729251, by rfl⟩ : syracuseStep 972335 = 1458503) B1458503
theorem B9950987 : Blo 968591 9950987 := bstep (se 1 (by rfl) ⟨7463240, by rfl⟩ : syracuseStep 9950987 = 14926481) B14926481
theorem B2185127 : Blo 968591 2185127 := bstep (se 1 (by rfl) ⟨1638845, by rfl⟩ : syracuseStep 2185127 = 3277691) B3277691
theorem B18175913 : Blo 968591 18175913 := bstep (se 2 (by rfl) ⟨6815967, by rfl⟩ : syracuseStep 18175913 = 13631935) B13631935
theorem B7363385 : Blo 968591 7363385 := bstep (se 2 (by rfl) ⟨2761269, by rfl⟩ : syracuseStep 7363385 = 5522539) B5522539
theorem B2186081 : Blo 968591 2186081 := bstep (se 2 (by rfl) ⟨819780, by rfl⟩ : syracuseStep 2186081 = 1639561) B1639561
theorem B17947975 : Blo 968591 17947975 := bstep (se 1 (by rfl) ⟨13460981, by rfl⟩ : syracuseStep 17947975 = 26921963) B26921963
theorem B2186747 : Blo 968591 2186747 := bstep (se 1 (by rfl) ⟨1640060, by rfl⟩ : syracuseStep 2186747 = 3280121) B3280121
theorem B1793591 : Blo 968591 1793591 := bstep (se 1 (by rfl) ⟨1345193, by rfl⟩ : syracuseStep 1793591 = 2690387) B2690387
theorem B2187233 : Blo 968591 2187233 := bstep (se 2 (by rfl) ⟨820212, by rfl⟩ : syracuseStep 2187233 = 1640425) B1640425
theorem B2188007 : Blo 968591 2188007 := bstep (se 1 (by rfl) ⟨1641005, by rfl⟩ : syracuseStep 2188007 = 3282011) B3282011
theorem B3269375 : Blo 968591 3269375 := bstep (se 1 (by rfl) ⟨2452031, by rfl⟩ : syracuseStep 3269375 = 4904063) B4904063
theorem B3499519 : Blo 968591 3499519 := bstep (se 1 (by rfl) ⟨2624639, by rfl⟩ : syracuseStep 3499519 = 5249279) B5249279
theorem B4978529 : Blo 968591 4978529 := bstep (se 2 (by rfl) ⟨1866948, by rfl⟩ : syracuseStep 4978529 = 3733897) B3733897
theorem B3110825 : Blo 968591 3110825 := bstep (se 2 (by rfl) ⟨1166559, by rfl⟩ : syracuseStep 3110825 = 2333119) B2333119
theorem B6224111 : Blo 968591 6224111 := bstep (se 1 (by rfl) ⟨4668083, by rfl⟩ : syracuseStep 6224111 = 9336167) B9336167
theorem B2459119 : Blo 968591 2459119 := bstep (se 1 (by rfl) ⟨1844339, by rfl⟩ : syracuseStep 2459119 = 3688679) B3688679
theorem B8295533 : Blo 968591 8295533 := bstep (se 3 (by rfl) ⟨1555412, by rfl⟩ : syracuseStep 8295533 = 3110825) B3110825
theorem B16586207 : Blo 968591 16586207 := bstep (se 1 (by rfl) ⟨12439655, by rfl⟩ : syracuseStep 16586207 = 24879311) B24879311
theorem B1382879 : Blo 968591 1382879 := bstep (se 1 (by rfl) ⟨1037159, by rfl⟩ : syracuseStep 1382879 = 2074319) B2074319
theorem B4922207 : Blo 968591 4922207 := bstep (se 1 (by rfl) ⟨3691655, by rfl⟩ : syracuseStep 4922207 = 7383311) B7383311
theorem B2761543 : Blo 968591 2761543 := bstep (se 1 (by rfl) ⟨2071157, by rfl⟩ : syracuseStep 2761543 = 4142315) B4142315
theorem B17507357 : Blo 968591 17507357 := bstep (se 3 (by rfl) ⟨3282629, by rfl⟩ : syracuseStep 17507357 = 6565259) B6565259
theorem B3319019 : Blo 968591 3319019 := bstep (se 1 (by rfl) ⟨2489264, by rfl⟩ : syracuseStep 3319019 = 4978529) B4978529
theorem B23930633 : Blo 968591 23930633 := bstep (se 2 (by rfl) ⟨8973987, by rfl⟩ : syracuseStep 23930633 = 17947975) B17947975
theorem B2075873 : Blo 968591 2075873 := bstep (se 2 (by rfl) ⟨778452, by rfl⟩ : syracuseStep 2075873 = 1556905) B1556905
theorem B1454249 : Blo 968591 1454249 := bstep (se 2 (by rfl) ⟨545343, by rfl⟩ : syracuseStep 1454249 = 1090687) B1090687
theorem B5517665 : Blo 968591 5517665 := bstep (se 2 (by rfl) ⟨2069124, by rfl⟩ : syracuseStep 5517665 = 4138249) B4138249
theorem B4666025 : Blo 968591 4666025 := bstep (se 2 (by rfl) ⟨1749759, by rfl⟩ : syracuseStep 4666025 = 3499519) B3499519
theorem B1454831 : Blo 968591 1454831 := bstep (se 1 (by rfl) ⟨1091123, by rfl⟩ : syracuseStep 1454831 = 2182247) B2182247
theorem B1455551 : Blo 968591 1455551 := bstep (se 1 (by rfl) ⟨1091663, by rfl⟩ : syracuseStep 1455551 = 2183327) B2183327
theorem B1455791 : Blo 968591 1455791 := bstep (se 1 (by rfl) ⟨1091843, by rfl⟩ : syracuseStep 1455791 = 2183687) B2183687
theorem B6207785 : Blo 968591 6207785 := bstep (se 2 (by rfl) ⟨2327919, by rfl⟩ : syracuseStep 6207785 = 4655839) B4655839
theorem B6633991 : Blo 968591 6633991 := bstep (se 1 (by rfl) ⟨4975493, by rfl⟩ : syracuseStep 6633991 = 9950987) B9950987
theorem B1456751 : Blo 968591 1456751 := bstep (se 1 (by rfl) ⟨1092563, by rfl⟩ : syracuseStep 1456751 = 2185127) B2185127
theorem B1457387 : Blo 968591 1457387 := bstep (se 1 (by rfl) ⟨1093040, by rfl⟩ : syracuseStep 1457387 = 2186081) B2186081
theorem B415022555 : Blo 968591 415022555 := bstep (se 1 (by rfl) ⟨311266916, by rfl⟩ : syracuseStep 415022555 = 622533833) B622533833
theorem B1457831 : Blo 968591 1457831 := bstep (se 1 (by rfl) ⟨1093373, by rfl⟩ : syracuseStep 1457831 = 2186747) B2186747
theorem B1195727 : Blo 968591 1195727 := bstep (se 1 (by rfl) ⟨896795, by rfl⟩ : syracuseStep 1195727 = 1793591) B1793591
theorem B1458155 : Blo 968591 1458155 := bstep (se 1 (by rfl) ⟨1093616, by rfl⟩ : syracuseStep 1458155 = 2187233) B2187233
theorem B1458671 : Blo 968591 1458671 := bstep (se 1 (by rfl) ⟨1094003, by rfl⟩ : syracuseStep 1458671 = 2188007) B2188007
theorem B2179583 : Blo 968591 2179583 := bstep (se 1 (by rfl) ⟨1634687, by rfl⟩ : syracuseStep 2179583 = 3269375) B3269375
theorem B968943 : Blo 968591 968943 := bstep (se 1 (by rfl) ⟨726707, by rfl⟩ : syracuseStep 968943 = 1453415) B1453415
theorem B970143 : Blo 968591 970143 := bstep (se 1 (by rfl) ⟨727607, by rfl⟩ : syracuseStep 970143 = 1455215) B1455215
theorem B4149407 : Blo 968591 4149407 := bstep (se 1 (by rfl) ⟨3112055, by rfl⟩ : syracuseStep 4149407 = 6224111) B6224111
theorem B970975 : Blo 968591 970975 := bstep (se 1 (by rfl) ⟨728231, by rfl⟩ : syracuseStep 970975 = 1456463) B1456463
theorem B20763307 : Blo 968591 20763307 := bstep (se 1 (by rfl) ⟨15572480, by rfl⟩ : syracuseStep 20763307 = 31144961) B31144961
theorem B972543 : Blo 968591 972543 := bstep (se 1 (by rfl) ⟨729407, by rfl⟩ : syracuseStep 972543 = 1458815) B1458815
theorem B5528189 : Blo 968591 5528189 := bstep (se 3 (by rfl) ⟨1036535, by rfl⟩ : syracuseStep 5528189 = 2073071) B2073071
theorem B12117275 : Blo 968591 12117275 := bstep (se 1 (by rfl) ⟨9087956, by rfl⟩ : syracuseStep 12117275 = 18175913) B18175913
theorem B4908923 : Blo 968591 4908923 := bstep (se 1 (by rfl) ⟨3681692, by rfl⟩ : syracuseStep 4908923 = 7363385) B7363385
theorem B2452943 : Blo 968591 2452943 := bstep (se 1 (by rfl) ⟨1839707, by rfl⟩ : syracuseStep 2452943 = 3679415) B3679415
theorem B12415463 : Blo 968591 12415463 := bstep (se 1 (by rfl) ⟨9311597, by rfl⟩ : syracuseStep 12415463 = 18623195) B18623195
theorem B12612671 : Blo 968591 12612671 := bstep (se 1 (by rfl) ⟨9459503, by rfl⟩ : syracuseStep 12612671 = 18919007) B18919007
theorem B53869637 : Blo 968591 53869637 := bstep (se 4 (by rfl) ⟨5050278, by rfl⟩ : syracuseStep 53869637 = 10100557) B10100557
theorem B3278825 : Blo 968591 3278825 := bstep (se 2 (by rfl) ⟨1229559, by rfl⟩ : syracuseStep 3278825 = 2459119) B2459119
theorem B3281471 : Blo 968591 3281471 := bstep (se 1 (by rfl) ⟨2461103, by rfl⟩ : syracuseStep 3281471 = 4922207) B4922207
theorem B11671571 : Blo 968591 11671571 := bstep (se 1 (by rfl) ⟨8753678, by rfl⟩ : syracuseStep 11671571 = 17507357) B17507357
theorem B3678443 : Blo 968591 3678443 := bstep (se 1 (by rfl) ⟨2758832, by rfl⟩ : syracuseStep 3678443 = 5517665) B5517665
theorem B4138523 : Blo 968591 4138523 := bstep (se 1 (by rfl) ⟨3103892, by rfl⟩ : syracuseStep 4138523 = 6207785) B6207785
theorem B3188605 : Blo 968591 3188605 := bstep (se 3 (by rfl) ⟨597863, by rfl⟩ : syracuseStep 3188605 = 1195727) B1195727
theorem B1453055 : Blo 968591 1453055 := bstep (se 1 (by rfl) ⟨1089791, by rfl⟩ : syracuseStep 1453055 = 2179583) B2179583
theorem B3682057 : Blo 968591 3682057 := bstep (se 2 (by rfl) ⟨1380771, by rfl⟩ : syracuseStep 3682057 = 2761543) B2761543
theorem B2766271 : Blo 968591 2766271 := bstep (se 1 (by rfl) ⟨2074703, by rfl⟩ : syracuseStep 2766271 = 4149407) B4149407
theorem B110737637 : Blo 968591 110737637 := bstep (se 4 (by rfl) ⟨10381653, by rfl⟩ : syracuseStep 110737637 = 20763307) B20763307
theorem B11057471 : Blo 968591 11057471 := bstep (se 1 (by rfl) ⟨8293103, by rfl⟩ : syracuseStep 11057471 = 16586207) B16586207
theorem B3685459 : Blo 968591 3685459 := bstep (se 1 (by rfl) ⟨2764094, by rfl⟩ : syracuseStep 3685459 = 5528189) B5528189
theorem B2212679 : Blo 968591 2212679 := bstep (se 1 (by rfl) ⟨1659509, by rfl⟩ : syracuseStep 2212679 = 3319019) B3319019
theorem B8078183 : Blo 968591 8078183 := bstep (se 1 (by rfl) ⟨6058637, by rfl⟩ : syracuseStep 8078183 = 12117275) B12117275
theorem B3687677 : Blo 968591 3687677 := bstep (se 3 (by rfl) ⟨691439, by rfl⟩ : syracuseStep 3687677 = 1382879) B1382879
theorem B969499 : Blo 968591 969499 := bstep (se 1 (by rfl) ⟨727124, by rfl⟩ : syracuseStep 969499 = 1454249) B1454249
theorem B8276975 : Blo 968591 8276975 := bstep (se 1 (by rfl) ⟨6207731, by rfl⟩ : syracuseStep 8276975 = 12415463) B12415463
theorem B969887 : Blo 968591 969887 := bstep (se 1 (by rfl) ⟨727415, by rfl⟩ : syracuseStep 969887 = 1454831) B1454831
theorem B8408447 : Blo 968591 8408447 := bstep (se 1 (by rfl) ⟨6306335, by rfl⟩ : syracuseStep 8408447 = 12612671) B12612671
theorem B970367 : Blo 968591 970367 := bstep (se 1 (by rfl) ⟨727775, by rfl⟩ : syracuseStep 970367 = 1455551) B1455551
theorem B970527 : Blo 968591 970527 := bstep (se 1 (by rfl) ⟨727895, by rfl⟩ : syracuseStep 970527 = 1455791) B1455791
theorem B971167 : Blo 968591 971167 := bstep (se 1 (by rfl) ⟨728375, by rfl⟩ : syracuseStep 971167 = 1456751) B1456751
theorem B971591 : Blo 968591 971591 := bstep (se 1 (by rfl) ⟨728693, by rfl⟩ : syracuseStep 971591 = 1457387) B1457387
theorem B276681703 : Blo 968591 276681703 := bstep (se 1 (by rfl) ⟨207511277, by rfl⟩ : syracuseStep 276681703 = 415022555) B415022555
theorem B971887 : Blo 968591 971887 := bstep (se 1 (by rfl) ⟨728915, by rfl⟩ : syracuseStep 971887 = 1457831) B1457831
theorem B972103 : Blo 968591 972103 := bstep (se 1 (by rfl) ⟨729077, by rfl⟩ : syracuseStep 972103 = 1458155) B1458155
theorem B972447 : Blo 968591 972447 := bstep (se 1 (by rfl) ⟨729335, by rfl⟩ : syracuseStep 972447 = 1458671) B1458671
theorem B12442733 : Blo 968591 12442733 := bstep (se 3 (by rfl) ⟨2333012, by rfl⟩ : syracuseStep 12442733 = 4666025) B4666025
theorem B5530355 : Blo 968591 5530355 := bstep (se 1 (by rfl) ⟨4147766, by rfl⟩ : syracuseStep 5530355 = 8295533) B8295533
theorem B15953755 : Blo 968591 15953755 := bstep (se 1 (by rfl) ⟨11965316, by rfl⟩ : syracuseStep 15953755 = 23930633) B23930633
theorem B3272615 : Blo 968591 3272615 := bstep (se 1 (by rfl) ⟨2454461, by rfl⟩ : syracuseStep 3272615 = 4908923) B4908923
theorem B1635295 : Blo 968591 1635295 := bstep (se 1 (by rfl) ⟨1226471, by rfl⟩ : syracuseStep 1635295 = 2452943) B2452943
theorem B143652365 : Blo 968591 143652365 := bstep (se 3 (by rfl) ⟨26934818, by rfl⟩ : syracuseStep 143652365 = 53869637) B53869637
theorem B5535661 : Blo 968591 5535661 := bstep (se 3 (by rfl) ⟨1037936, by rfl⟩ : syracuseStep 5535661 = 2075873) B2075873
theorem B8845321 : Blo 968591 8845321 := bstep (se 2 (by rfl) ⟨3316995, by rfl⟩ : syracuseStep 8845321 = 6633991) B6633991
theorem B1475119 : Blo 968591 1475119 := bstep (se 1 (by rfl) ⟨1106339, by rfl⟩ : syracuseStep 1475119 = 2212679) B2212679
theorem B2458451 : Blo 968591 2458451 := bstep (se 1 (by rfl) ⟨1843838, by rfl⟩ : syracuseStep 2458451 = 3687677) B3687677
theorem B5605631 : Blo 968591 5605631 := bstep (se 1 (by rfl) ⟨4204223, by rfl⟩ : syracuseStep 5605631 = 8408447) B8408447
theorem B8295155 : Blo 968591 8295155 := bstep (se 1 (by rfl) ⟨6221366, by rfl⟩ : syracuseStep 8295155 = 12442733) B12442733
theorem B21271673 : Blo 968591 21271673 := bstep (se 2 (by rfl) ⟨7976877, by rfl⟩ : syracuseStep 21271673 = 15953755) B15953755
theorem B2759015 : Blo 968591 2759015 := bstep (se 1 (by rfl) ⟨2069261, by rfl⟩ : syracuseStep 2759015 = 4138523) B4138523
theorem B368908937 : Blo 968591 368908937 := bstep (se 2 (by rfl) ⟨138340851, by rfl⟩ : syracuseStep 368908937 = 276681703) B276681703
theorem B7380881 : Blo 968591 7380881 := bstep (se 2 (by rfl) ⟨2767830, by rfl⟩ : syracuseStep 7380881 = 5535661) B5535661
theorem B5385455 : Blo 968591 5385455 := bstep (se 1 (by rfl) ⟨4039091, by rfl⟩ : syracuseStep 5385455 = 8078183) B8078183
theorem B5517983 : Blo 968591 5517983 := bstep (se 1 (by rfl) ⟨4138487, by rfl⟩ : syracuseStep 5517983 = 8276975) B8276975
theorem B3686903 : Blo 968591 3686903 := bstep (se 1 (by rfl) ⟨2765177, by rfl⟩ : syracuseStep 3686903 = 5530355) B5530355
theorem B2180393 : Blo 968591 2180393 := bstep (se 2 (by rfl) ⟨817647, by rfl⟩ : syracuseStep 2180393 = 1635295) B1635295
theorem B3688361 : Blo 968591 3688361 := bstep (se 2 (by rfl) ⟨1383135, by rfl⟩ : syracuseStep 3688361 = 2766271) B2766271
theorem B968703 : Blo 968591 968703 := bstep (se 1 (by rfl) ⟨726527, by rfl⟩ : syracuseStep 968703 = 1453055) B1453055
theorem B2181743 : Blo 968591 2181743 := bstep (se 1 (by rfl) ⟨1636307, by rfl⟩ : syracuseStep 2181743 = 3272615) B3272615
theorem B95768243 : Blo 968591 95768243 := bstep (se 1 (by rfl) ⟨71826182, by rfl⟩ : syracuseStep 95768243 = 143652365) B143652365
theorem B2185883 : Blo 968591 2185883 := bstep (se 1 (by rfl) ⟨1639412, by rfl⟩ : syracuseStep 2185883 = 3278825) B3278825
theorem B4251473 : Blo 968591 4251473 := bstep (se 2 (by rfl) ⟨1594302, by rfl⟩ : syracuseStep 4251473 = 3188605) B3188605
theorem B2187647 : Blo 968591 2187647 := bstep (se 1 (by rfl) ⟨1640735, by rfl⟩ : syracuseStep 2187647 = 3281471) B3281471
theorem B4909409 : Blo 968591 4909409 := bstep (se 2 (by rfl) ⟨1841028, by rfl⟩ : syracuseStep 4909409 = 3682057) B3682057
theorem B31124189 : Blo 968591 31124189 := bstep (se 3 (by rfl) ⟨5835785, by rfl⟩ : syracuseStep 31124189 = 11671571) B11671571
theorem B2452295 : Blo 968591 2452295 := bstep (se 1 (by rfl) ⟨1839221, by rfl⟩ : syracuseStep 2452295 = 3678443) B3678443
theorem B11793761 : Blo 968591 11793761 := bstep (se 2 (by rfl) ⟨4422660, by rfl⟩ : syracuseStep 11793761 = 8845321) B8845321
theorem B4913945 : Blo 968591 4913945 := bstep (se 2 (by rfl) ⟨1842729, by rfl⟩ : syracuseStep 4913945 = 3685459) B3685459
theorem B73825091 : Blo 968591 73825091 := bstep (se 1 (by rfl) ⟨55368818, by rfl⟩ : syracuseStep 73825091 = 110737637) B110737637
theorem B7371647 : Blo 968591 7371647 := bstep (se 1 (by rfl) ⟨5528735, by rfl⟩ : syracuseStep 7371647 = 11057471) B11057471
theorem B2457935 : Blo 968591 2457935 := bstep (se 1 (by rfl) ⟨1843451, by rfl⟩ : syracuseStep 2457935 = 3686903) B3686903
theorem B1638967 : Blo 968591 1638967 := bstep (se 1 (by rfl) ⟨1229225, by rfl⟩ : syracuseStep 1638967 = 2458451) B2458451
theorem B1966825 : Blo 968591 1966825 := bstep (se 2 (by rfl) ⟨737559, by rfl⟩ : syracuseStep 1966825 = 1475119) B1475119
theorem B2458907 : Blo 968591 2458907 := bstep (se 1 (by rfl) ⟨1844180, by rfl⟩ : syracuseStep 2458907 = 3688361) B3688361
theorem B3737087 : Blo 968591 3737087 := bstep (se 1 (by rfl) ⟨2802815, by rfl⟩ : syracuseStep 3737087 = 5605631) B5605631
theorem B56724461 : Blo 968591 56724461 := bstep (se 3 (by rfl) ⟨10635836, by rfl⟩ : syracuseStep 56724461 = 21271673) B21271673
theorem B1839343 : Blo 968591 1839343 := bstep (se 1 (by rfl) ⟨1379507, by rfl⟩ : syracuseStep 1839343 = 2759015) B2759015
theorem B4920587 : Blo 968591 4920587 := bstep (se 1 (by rfl) ⟨3690440, by rfl⟩ : syracuseStep 4920587 = 7380881) B7380881
theorem B20749459 : Blo 968591 20749459 := bstep (se 1 (by rfl) ⟨15562094, by rfl⟩ : syracuseStep 20749459 = 31124189) B31124189
theorem B3678655 : Blo 968591 3678655 := bstep (se 1 (by rfl) ⟨2758991, by rfl⟩ : syracuseStep 3678655 = 5517983) B5517983
theorem B1453595 : Blo 968591 1453595 := bstep (se 1 (by rfl) ⟨1090196, by rfl⟩ : syracuseStep 1453595 = 2180393) B2180393
theorem B1454495 : Blo 968591 1454495 := bstep (se 1 (by rfl) ⟨1090871, by rfl⟩ : syracuseStep 1454495 = 2181743) B2181743
theorem B63845495 : Blo 968591 63845495 := bstep (se 1 (by rfl) ⟨47884121, by rfl⟩ : syracuseStep 63845495 = 95768243) B95768243
theorem B245939291 : Blo 968591 245939291 := bstep (se 1 (by rfl) ⟨184454468, by rfl⟩ : syracuseStep 245939291 = 368908937) B368908937
theorem B1457255 : Blo 968591 1457255 := bstep (se 1 (by rfl) ⟨1092941, by rfl⟩ : syracuseStep 1457255 = 2185883) B2185883
theorem B2834315 : Blo 968591 2834315 := bstep (se 1 (by rfl) ⟨2125736, by rfl⟩ : syracuseStep 2834315 = 4251473) B4251473
theorem B1458431 : Blo 968591 1458431 := bstep (se 1 (by rfl) ⟨1093823, by rfl⟩ : syracuseStep 1458431 = 2187647) B2187647
theorem B3590303 : Blo 968591 3590303 := bstep (se 1 (by rfl) ⟨2692727, by rfl⟩ : syracuseStep 3590303 = 5385455) B5385455
theorem B5530103 : Blo 968591 5530103 := bstep (se 1 (by rfl) ⟨4147577, by rfl⟩ : syracuseStep 5530103 = 8295155) B8295155
theorem B3272939 : Blo 968591 3272939 := bstep (se 1 (by rfl) ⟨2454704, by rfl⟩ : syracuseStep 3272939 = 4909409) B4909409
theorem B1634863 : Blo 968591 1634863 := bstep (se 1 (by rfl) ⟨1226147, by rfl⟩ : syracuseStep 1634863 = 2452295) B2452295
theorem B7862507 : Blo 968591 7862507 := bstep (se 1 (by rfl) ⟨5896880, by rfl⟩ : syracuseStep 7862507 = 11793761) B11793761
theorem B3275963 : Blo 968591 3275963 := bstep (se 1 (by rfl) ⟨2456972, by rfl⟩ : syracuseStep 3275963 = 4913945) B4913945
theorem B49216727 : Blo 968591 49216727 := bstep (se 1 (by rfl) ⟨36912545, by rfl⟩ : syracuseStep 49216727 = 73825091) B73825091
theorem B4914431 : Blo 968591 4914431 := bstep (se 1 (by rfl) ⟨3685823, by rfl⟩ : syracuseStep 4914431 = 7371647) B7371647
theorem B1638623 : Blo 968591 1638623 := bstep (se 1 (by rfl) ⟨1228967, by rfl⟩ : syracuseStep 1638623 = 2457935) B2457935
theorem B1639271 : Blo 968591 1639271 := bstep (se 1 (by rfl) ⟨1229453, by rfl⟩ : syracuseStep 1639271 = 2458907) B2458907
theorem B2491391 : Blo 968591 2491391 := bstep (se 1 (by rfl) ⟨1868543, by rfl⟩ : syracuseStep 2491391 = 3737087) B3737087
theorem B37816307 : Blo 968591 37816307 := bstep (se 1 (by rfl) ⟨28362230, by rfl⟩ : syracuseStep 37816307 = 56724461) B56724461
theorem B3280391 : Blo 968591 3280391 := bstep (se 1 (by rfl) ⟨2460293, by rfl⟩ : syracuseStep 3280391 = 4920587) B4920587
theorem B10489733 : Blo 968591 10489733 := bstep (se 4 (by rfl) ⟨983412, by rfl⟩ : syracuseStep 10489733 = 1966825) B1966825
theorem B9574141 : Blo 968591 9574141 := bstep (se 3 (by rfl) ⟨1795151, by rfl⟩ : syracuseStep 9574141 = 3590303) B3590303
theorem B27665945 : Blo 968591 27665945 := bstep (se 2 (by rfl) ⟨10374729, by rfl⟩ : syracuseStep 27665945 = 20749459) B20749459
theorem B32811151 : Blo 968591 32811151 := bstep (se 1 (by rfl) ⟨24608363, by rfl⟩ : syracuseStep 32811151 = 49216727) B49216727
theorem B3686735 : Blo 968591 3686735 := bstep (se 1 (by rfl) ⟨2765051, by rfl⟩ : syracuseStep 3686735 = 5530103) B5530103
theorem B2179817 : Blo 968591 2179817 := bstep (se 2 (by rfl) ⟨817431, by rfl⟩ : syracuseStep 2179817 = 1634863) B1634863
theorem B969063 : Blo 968591 969063 := bstep (se 1 (by rfl) ⟨726797, by rfl⟩ : syracuseStep 969063 = 1453595) B1453595
theorem B2181959 : Blo 968591 2181959 := bstep (se 1 (by rfl) ⟨1636469, by rfl⟩ : syracuseStep 2181959 = 3272939) B3272939
theorem B969663 : Blo 968591 969663 := bstep (se 1 (by rfl) ⟨727247, by rfl⟩ : syracuseStep 969663 = 1454495) B1454495
theorem B163959527 : Blo 968591 163959527 := bstep (se 1 (by rfl) ⟨122969645, by rfl⟩ : syracuseStep 163959527 = 245939291) B245939291
theorem B971503 : Blo 968591 971503 := bstep (se 1 (by rfl) ⟨728627, by rfl⟩ : syracuseStep 971503 = 1457255) B1457255
theorem B2183975 : Blo 968591 2183975 := bstep (se 1 (by rfl) ⟨1637981, by rfl⟩ : syracuseStep 2183975 = 3275963) B3275963
theorem B1889543 : Blo 968591 1889543 := bstep (se 1 (by rfl) ⟨1417157, by rfl⟩ : syracuseStep 1889543 = 2834315) B2834315
theorem B972287 : Blo 968591 972287 := bstep (se 1 (by rfl) ⟨729215, by rfl⟩ : syracuseStep 972287 = 1458431) B1458431
theorem B4904873 : Blo 968591 4904873 := bstep (se 2 (by rfl) ⟨1839327, by rfl⟩ : syracuseStep 4904873 = 3678655) B3678655
theorem B2185289 : Blo 968591 2185289 := bstep (se 2 (by rfl) ⟨819483, by rfl⟩ : syracuseStep 2185289 = 1638967) B1638967
theorem B2452457 : Blo 968591 2452457 := bstep (se 2 (by rfl) ⟨919671, by rfl⟩ : syracuseStep 2452457 = 1839343) B1839343
theorem B42563663 : Blo 968591 42563663 := bstep (se 1 (by rfl) ⟨31922747, by rfl⟩ : syracuseStep 42563663 = 63845495) B63845495
theorem B5241671 : Blo 968591 5241671 := bstep (se 1 (by rfl) ⟨3931253, by rfl⟩ : syracuseStep 5241671 = 7862507) B7862507
theorem B3276287 : Blo 968591 3276287 := bstep (se 1 (by rfl) ⟨2457215, by rfl⟩ : syracuseStep 3276287 = 4914431) B4914431
theorem B2457823 : Blo 968591 2457823 := bstep (se 1 (by rfl) ⟨1843367, by rfl⟩ : syracuseStep 2457823 = 3686735) B3686735
theorem B43748201 : Blo 968591 43748201 := bstep (se 2 (by rfl) ⟨16405575, by rfl⟩ : syracuseStep 43748201 = 32811151) B32811151
theorem B1092415 : Blo 968591 1092415 := bstep (se 1 (by rfl) ⟨819311, by rfl⟩ : syracuseStep 1092415 = 1638623) B1638623
theorem B1453211 : Blo 968591 1453211 := bstep (se 1 (by rfl) ⟨1089908, by rfl⟩ : syracuseStep 1453211 = 2179817) B2179817
theorem B1092847 : Blo 968591 1092847 := bstep (se 1 (by rfl) ⟨819635, by rfl⟩ : syracuseStep 1092847 = 1639271) B1639271
theorem B25210871 : Blo 968591 25210871 := bstep (se 1 (by rfl) ⟨18908153, by rfl⟩ : syracuseStep 25210871 = 37816307) B37816307
theorem B1454639 : Blo 968591 1454639 := bstep (se 1 (by rfl) ⟨1090979, by rfl⟩ : syracuseStep 1454639 = 2181959) B2181959
theorem B6993155 : Blo 968591 6993155 := bstep (se 1 (by rfl) ⟨5244866, by rfl⟩ : syracuseStep 6993155 = 10489733) B10489733
theorem B1455983 : Blo 968591 1455983 := bstep (se 1 (by rfl) ⟨1091987, by rfl⟩ : syracuseStep 1455983 = 2183975) B2183975
theorem B1259695 : Blo 968591 1259695 := bstep (se 1 (by rfl) ⟨944771, by rfl⟩ : syracuseStep 1259695 = 1889543) B1889543
theorem B1456859 : Blo 968591 1456859 := bstep (se 1 (by rfl) ⟨1092644, by rfl⟩ : syracuseStep 1456859 = 2185289) B2185289
theorem B12765521 : Blo 968591 12765521 := bstep (se 2 (by rfl) ⟨4787070, by rfl⟩ : syracuseStep 12765521 = 9574141) B9574141
theorem B3494447 : Blo 968591 3494447 := bstep (se 1 (by rfl) ⟨2620835, by rfl⟩ : syracuseStep 3494447 = 5241671) B5241671
theorem B2184191 : Blo 968591 2184191 := bstep (se 1 (by rfl) ⟨1638143, by rfl⟩ : syracuseStep 2184191 = 3276287) B3276287
theorem B1660927 : Blo 968591 1660927 := bstep (se 1 (by rfl) ⟨1245695, by rfl⟩ : syracuseStep 1660927 = 2491391) B2491391
theorem B2186927 : Blo 968591 2186927 := bstep (se 1 (by rfl) ⟨1640195, by rfl⟩ : syracuseStep 2186927 = 3280391) B3280391
theorem B109306351 : Blo 968591 109306351 := bstep (se 1 (by rfl) ⟨81979763, by rfl⟩ : syracuseStep 109306351 = 163959527) B163959527
theorem B3269915 : Blo 968591 3269915 := bstep (se 1 (by rfl) ⟨2452436, by rfl⟩ : syracuseStep 3269915 = 4904873) B4904873
theorem B18443963 : Blo 968591 18443963 := bstep (se 1 (by rfl) ⟨13832972, by rfl⟩ : syracuseStep 18443963 = 27665945) B27665945
theorem B1634971 : Blo 968591 1634971 := bstep (se 1 (by rfl) ⟨1226228, by rfl⟩ : syracuseStep 1634971 = 2452457) B2452457
theorem B28375775 : Blo 968591 28375775 := bstep (se 1 (by rfl) ⟨21281831, by rfl⟩ : syracuseStep 28375775 = 42563663) B42563663
theorem B3277097 : Blo 968591 3277097 := bstep (se 2 (by rfl) ⟨1228911, by rfl⟩ : syracuseStep 3277097 = 2457823) B2457823
theorem B6718373 : Blo 968591 6718373 := bstep (se 4 (by rfl) ⟨629847, by rfl⟩ : syracuseStep 6718373 = 1259695) B1259695
theorem B29165467 : Blo 968591 29165467 := bstep (se 1 (by rfl) ⟨21874100, by rfl⟩ : syracuseStep 29165467 = 43748201) B43748201
theorem B2329631 : Blo 968591 2329631 := bstep (se 1 (by rfl) ⟨1747223, by rfl⟩ : syracuseStep 2329631 = 3494447) B3494447
theorem B18648413 : Blo 968591 18648413 := bstep (se 3 (by rfl) ⟨3496577, by rfl⟩ : syracuseStep 18648413 = 6993155) B6993155
theorem B12295975 : Blo 968591 12295975 := bstep (se 1 (by rfl) ⟨9221981, by rfl⟩ : syracuseStep 12295975 = 18443963) B18443963
theorem B18917183 : Blo 968591 18917183 := bstep (se 1 (by rfl) ⟨14187887, by rfl⟩ : syracuseStep 18917183 = 28375775) B28375775
theorem B1456127 : Blo 968591 1456127 := bstep (se 1 (by rfl) ⟨1092095, by rfl⟩ : syracuseStep 1456127 = 2184191) B2184191
theorem B1456553 : Blo 968591 1456553 := bstep (se 2 (by rfl) ⟨546207, by rfl⟩ : syracuseStep 1456553 = 1092415) B1092415
theorem B1457129 : Blo 968591 1457129 := bstep (se 2 (by rfl) ⟨546423, by rfl⟩ : syracuseStep 1457129 = 1092847) B1092847
theorem B1457951 : Blo 968591 1457951 := bstep (se 1 (by rfl) ⟨1093463, by rfl⟩ : syracuseStep 1457951 = 2186927) B2186927
theorem B2179943 : Blo 968591 2179943 := bstep (se 1 (by rfl) ⟨1634957, by rfl⟩ : syracuseStep 2179943 = 3269915) B3269915
theorem B2179961 : Blo 968591 2179961 := bstep (se 2 (by rfl) ⟨817485, by rfl⟩ : syracuseStep 2179961 = 1634971) B1634971
theorem B968807 : Blo 968591 968807 := bstep (se 1 (by rfl) ⟨726605, by rfl⟩ : syracuseStep 968807 = 1453211) B1453211
theorem B2214569 : Blo 968591 2214569 := bstep (se 2 (by rfl) ⟨830463, by rfl⟩ : syracuseStep 2214569 = 1660927) B1660927
theorem B969759 : Blo 968591 969759 := bstep (se 1 (by rfl) ⟨727319, by rfl⟩ : syracuseStep 969759 = 1454639) B1454639
theorem B970655 : Blo 968591 970655 := bstep (se 1 (by rfl) ⟨727991, by rfl⟩ : syracuseStep 970655 = 1455983) B1455983
theorem B971239 : Blo 968591 971239 := bstep (se 1 (by rfl) ⟨728429, by rfl⟩ : syracuseStep 971239 = 1456859) B1456859
theorem B145741801 : Blo 968591 145741801 := bstep (se 2 (by rfl) ⟨54653175, by rfl⟩ : syracuseStep 145741801 = 109306351) B109306351
theorem B8510347 : Blo 968591 8510347 := bstep (se 1 (by rfl) ⟨6382760, by rfl⟩ : syracuseStep 8510347 = 12765521) B12765521
theorem B16807247 : Blo 968591 16807247 := bstep (se 1 (by rfl) ⟨12605435, by rfl⟩ : syracuseStep 16807247 = 25210871) B25210871
theorem B1476379 : Blo 968591 1476379 := bstep (se 1 (by rfl) ⟨1107284, by rfl⟩ : syracuseStep 1476379 = 2214569) B2214569
theorem B194322401 : Blo 968591 194322401 := bstep (se 2 (by rfl) ⟨72870900, by rfl⟩ : syracuseStep 194322401 = 145741801) B145741801
theorem B11347129 : Blo 968591 11347129 := bstep (se 2 (by rfl) ⟨4255173, by rfl⟩ : syracuseStep 11347129 = 8510347) B8510347
theorem B16394633 : Blo 968591 16394633 := bstep (se 2 (by rfl) ⟨6147987, by rfl⟩ : syracuseStep 16394633 = 12295975) B12295975
theorem B1453295 : Blo 968591 1453295 := bstep (se 1 (by rfl) ⟨1089971, by rfl⟩ : syracuseStep 1453295 = 2179943) B2179943
theorem B1453307 : Blo 968591 1453307 := bstep (se 1 (by rfl) ⟨1089980, by rfl⟩ : syracuseStep 1453307 = 2179961) B2179961
theorem B1553087 : Blo 968591 1553087 := bstep (se 1 (by rfl) ⟨1164815, by rfl⟩ : syracuseStep 1553087 = 2329631) B2329631
theorem B12432275 : Blo 968591 12432275 := bstep (se 1 (by rfl) ⟨9324206, by rfl⟩ : syracuseStep 12432275 = 18648413) B18648413
theorem B50445821 : Blo 968591 50445821 := bstep (se 3 (by rfl) ⟨9458591, by rfl⟩ : syracuseStep 50445821 = 18917183) B18917183
theorem B970751 : Blo 968591 970751 := bstep (se 1 (by rfl) ⟨728063, by rfl⟩ : syracuseStep 970751 = 1456127) B1456127
theorem B971035 : Blo 968591 971035 := bstep (se 1 (by rfl) ⟨728276, by rfl⟩ : syracuseStep 971035 = 1456553) B1456553
theorem B971419 : Blo 968591 971419 := bstep (se 1 (by rfl) ⟨728564, by rfl⟩ : syracuseStep 971419 = 1457129) B1457129
theorem B971967 : Blo 968591 971967 := bstep (se 1 (by rfl) ⟨728975, by rfl⟩ : syracuseStep 971967 = 1457951) B1457951
theorem B2184731 : Blo 968591 2184731 := bstep (se 1 (by rfl) ⟨1638548, by rfl⟩ : syracuseStep 2184731 = 3277097) B3277097
theorem B4478915 : Blo 968591 4478915 := bstep (se 1 (by rfl) ⟨3359186, by rfl⟩ : syracuseStep 4478915 = 6718373) B6718373
theorem B38887289 : Blo 968591 38887289 := bstep (se 2 (by rfl) ⟨14582733, by rfl⟩ : syracuseStep 38887289 = 29165467) B29165467
theorem B11204831 : Blo 968591 11204831 := bstep (se 1 (by rfl) ⟨8403623, by rfl⟩ : syracuseStep 11204831 = 16807247) B16807247
theorem B1968505 : Blo 968591 1968505 := bstep (se 2 (by rfl) ⟨738189, by rfl⟩ : syracuseStep 1968505 = 1476379) B1476379
theorem B25924859 : Blo 968591 25924859 := bstep (se 1 (by rfl) ⟨19443644, by rfl⟩ : syracuseStep 25924859 = 38887289) B38887289
theorem B33630547 : Blo 968591 33630547 := bstep (se 1 (by rfl) ⟨25222910, by rfl⟩ : syracuseStep 33630547 = 50445821) B50445821
theorem B1456487 : Blo 968591 1456487 := bstep (se 1 (by rfl) ⟨1092365, by rfl⟩ : syracuseStep 1456487 = 2184731) B2184731
theorem B11943773 : Blo 968591 11943773 := bstep (se 3 (by rfl) ⟨2239457, by rfl⟩ : syracuseStep 11943773 = 4478915) B4478915
theorem B129548267 : Blo 968591 129548267 := bstep (se 1 (by rfl) ⟨97161200, by rfl⟩ : syracuseStep 129548267 = 194322401) B194322401
theorem B10929755 : Blo 968591 10929755 := bstep (se 1 (by rfl) ⟨8197316, by rfl⟩ : syracuseStep 10929755 = 16394633) B16394633
theorem B968863 : Blo 968591 968863 := bstep (se 1 (by rfl) ⟨726647, by rfl⟩ : syracuseStep 968863 = 1453295) B1453295
theorem B968871 : Blo 968591 968871 := bstep (se 1 (by rfl) ⟨726653, by rfl⟩ : syracuseStep 968871 = 1453307) B1453307
theorem B1035391 : Blo 968591 1035391 := bstep (se 1 (by rfl) ⟨776543, by rfl⟩ : syracuseStep 1035391 = 1553087) B1553087
theorem B15129505 : Blo 968591 15129505 := bstep (se 2 (by rfl) ⟨5673564, by rfl⟩ : syracuseStep 15129505 = 11347129) B11347129
theorem B8288183 : Blo 968591 8288183 := bstep (se 1 (by rfl) ⟨6216137, by rfl⟩ : syracuseStep 8288183 = 12432275) B12432275
theorem B7469887 : Blo 968591 7469887 := bstep (se 1 (by rfl) ⟨5602415, by rfl⟩ : syracuseStep 7469887 = 11204831) B11204831
theorem B1380521 : Blo 968591 1380521 := bstep (se 2 (by rfl) ⟨517695, by rfl⟩ : syracuseStep 1380521 = 1035391) B1035391
theorem B10498693 : Blo 968591 10498693 := bstep (se 4 (by rfl) ⟨984252, by rfl⟩ : syracuseStep 10498693 = 1968505) B1968505
theorem B44840729 : Blo 968591 44840729 := bstep (se 2 (by rfl) ⟨16815273, by rfl⟩ : syracuseStep 44840729 = 33630547) B33630547
theorem B17283239 : Blo 968591 17283239 := bstep (se 1 (by rfl) ⟨12962429, by rfl⟩ : syracuseStep 17283239 = 25924859) B25924859
theorem B29146013 : Blo 968591 29146013 := bstep (se 3 (by rfl) ⟨5464877, by rfl⟩ : syracuseStep 29146013 = 10929755) B10929755
theorem B20172673 : Blo 968591 20172673 := bstep (se 2 (by rfl) ⟨7564752, by rfl⟩ : syracuseStep 20172673 = 15129505) B15129505
theorem B5525455 : Blo 968591 5525455 := bstep (se 1 (by rfl) ⟨4144091, by rfl⟩ : syracuseStep 5525455 = 8288183) B8288183
theorem B970991 : Blo 968591 970991 := bstep (se 1 (by rfl) ⟨728243, by rfl⟩ : syracuseStep 970991 = 1456487) B1456487
theorem B86365511 : Blo 968591 86365511 := bstep (se 1 (by rfl) ⟨64774133, by rfl⟩ : syracuseStep 86365511 = 129548267) B129548267
theorem B9959849 : Blo 968591 9959849 := bstep (se 2 (by rfl) ⟨3734943, by rfl⟩ : syracuseStep 9959849 = 7469887) B7469887
theorem B7962515 : Blo 968591 7962515 := bstep (se 1 (by rfl) ⟨5971886, by rfl⟩ : syracuseStep 7962515 = 11943773) B11943773
theorem B57577007 : Blo 968591 57577007 := bstep (se 1 (by rfl) ⟨43182755, by rfl⟩ : syracuseStep 57577007 = 86365511) B86365511
theorem B13998257 : Blo 968591 13998257 := bstep (se 2 (by rfl) ⟨5249346, by rfl⟩ : syracuseStep 13998257 = 10498693) B10498693
theorem B29893819 : Blo 968591 29893819 := bstep (se 1 (by rfl) ⟨22420364, by rfl⟩ : syracuseStep 29893819 = 44840729) B44840729
theorem B3681389 : Blo 968591 3681389 := bstep (se 3 (by rfl) ⟨690260, by rfl⟩ : syracuseStep 3681389 = 1380521) B1380521
theorem B11522159 : Blo 968591 11522159 := bstep (se 1 (by rfl) ⟨8641619, by rfl⟩ : syracuseStep 11522159 = 17283239) B17283239
theorem B6639899 : Blo 968591 6639899 := bstep (se 1 (by rfl) ⟨4979924, by rfl⟩ : syracuseStep 6639899 = 9959849) B9959849
theorem B26896897 : Blo 968591 26896897 := bstep (se 2 (by rfl) ⟨10086336, by rfl⟩ : syracuseStep 26896897 = 20172673) B20172673
theorem B7367273 : Blo 968591 7367273 := bstep (se 2 (by rfl) ⟨2762727, by rfl⟩ : syracuseStep 7367273 = 5525455) B5525455
theorem B19430675 : Blo 968591 19430675 := bstep (se 1 (by rfl) ⟨14573006, by rfl⟩ : syracuseStep 19430675 = 29146013) B29146013
theorem B5308343 : Blo 968591 5308343 := bstep (se 1 (by rfl) ⟨3981257, by rfl⟩ : syracuseStep 5308343 = 7962515) B7962515
theorem B12953783 : Blo 968591 12953783 := bstep (se 1 (by rfl) ⟨9715337, by rfl⟩ : syracuseStep 12953783 = 19430675) B19430675
theorem B17706397 : Blo 968591 17706397 := bstep (se 3 (by rfl) ⟨3319949, by rfl⟩ : syracuseStep 17706397 = 6639899) B6639899
theorem B39858425 : Blo 968591 39858425 := bstep (se 2 (by rfl) ⟨14946909, by rfl⟩ : syracuseStep 39858425 = 29893819) B29893819
theorem B38384671 : Blo 968591 38384671 := bstep (se 1 (by rfl) ⟨28788503, by rfl⟩ : syracuseStep 38384671 = 57577007) B57577007
theorem B7681439 : Blo 968591 7681439 := bstep (se 1 (by rfl) ⟨5761079, by rfl⟩ : syracuseStep 7681439 = 11522159) B11522159
theorem B35862529 : Blo 968591 35862529 := bstep (se 2 (by rfl) ⟨13448448, by rfl⟩ : syracuseStep 35862529 = 26896897) B26896897
theorem B9332171 : Blo 968591 9332171 := bstep (se 1 (by rfl) ⟨6999128, by rfl⟩ : syracuseStep 9332171 = 13998257) B13998257
theorem B4911515 : Blo 968591 4911515 := bstep (se 1 (by rfl) ⟨3683636, by rfl⟩ : syracuseStep 4911515 = 7367273) B7367273
theorem B2454259 : Blo 968591 2454259 := bstep (se 1 (by rfl) ⟨1840694, by rfl⟩ : syracuseStep 2454259 = 3681389) B3681389
theorem B3538895 : Blo 968591 3538895 := bstep (se 1 (by rfl) ⟨2654171, by rfl⟩ : syracuseStep 3538895 = 5308343) B5308343
theorem B20483837 : Blo 968591 20483837 := bstep (se 3 (by rfl) ⟨3840719, by rfl⟩ : syracuseStep 20483837 = 7681439) B7681439
theorem B47816705 : Blo 968591 47816705 := bstep (se 2 (by rfl) ⟨17931264, by rfl⟩ : syracuseStep 47816705 = 35862529) B35862529
theorem B23608529 : Blo 968591 23608529 := bstep (se 2 (by rfl) ⟨8853198, by rfl⟩ : syracuseStep 23608529 = 17706397) B17706397
theorem B8635855 : Blo 968591 8635855 := bstep (se 1 (by rfl) ⟨6476891, by rfl⟩ : syracuseStep 8635855 = 12953783) B12953783
theorem B6221447 : Blo 968591 6221447 := bstep (se 1 (by rfl) ⟨4666085, by rfl⟩ : syracuseStep 6221447 = 9332171) B9332171
theorem B3272345 : Blo 968591 3272345 := bstep (se 2 (by rfl) ⟨1227129, by rfl⟩ : syracuseStep 3272345 = 2454259) B2454259
theorem B51179561 : Blo 968591 51179561 := bstep (se 2 (by rfl) ⟨19192335, by rfl⟩ : syracuseStep 51179561 = 38384671) B38384671
theorem B26572283 : Blo 968591 26572283 := bstep (se 1 (by rfl) ⟨19929212, by rfl⟩ : syracuseStep 26572283 = 39858425) B39858425
theorem B3274343 : Blo 968591 3274343 := bstep (se 1 (by rfl) ⟨2455757, by rfl⟩ : syracuseStep 3274343 = 4911515) B4911515
theorem B37748213 : Blo 968591 37748213 := bstep (se 5 (by rfl) ⟨1769447, by rfl⟩ : syracuseStep 37748213 = 3538895) B3538895
theorem B34119707 : Blo 968591 34119707 := bstep (se 1 (by rfl) ⟨25589780, by rfl⟩ : syracuseStep 34119707 = 51179561) B51179561
theorem B15739019 : Blo 968591 15739019 := bstep (se 1 (by rfl) ⟨11804264, by rfl⟩ : syracuseStep 15739019 = 23608529) B23608529
theorem B11514473 : Blo 968591 11514473 := bstep (se 2 (by rfl) ⟨4317927, by rfl⟩ : syracuseStep 11514473 = 8635855) B8635855
theorem B4147631 : Blo 968591 4147631 := bstep (se 1 (by rfl) ⟨3110723, by rfl⟩ : syracuseStep 4147631 = 6221447) B6221447
theorem B2181563 : Blo 968591 2181563 := bstep (se 1 (by rfl) ⟨1636172, by rfl⟩ : syracuseStep 2181563 = 3272345) B3272345
theorem B17714855 : Blo 968591 17714855 := bstep (se 1 (by rfl) ⟨13286141, by rfl⟩ : syracuseStep 17714855 = 26572283) B26572283
theorem B2182895 : Blo 968591 2182895 := bstep (se 1 (by rfl) ⟨1637171, by rfl⟩ : syracuseStep 2182895 = 3274343) B3274343
theorem B13655891 : Blo 968591 13655891 := bstep (se 1 (by rfl) ⟨10241918, by rfl⟩ : syracuseStep 13655891 = 20483837) B20483837
theorem B31877803 : Blo 968591 31877803 := bstep (se 1 (by rfl) ⟨23908352, by rfl⟩ : syracuseStep 31877803 = 47816705) B47816705
theorem B25165475 : Blo 968591 25165475 := bstep (se 1 (by rfl) ⟨18874106, by rfl⟩ : syracuseStep 25165475 = 37748213) B37748213
theorem B42503737 : Blo 968591 42503737 := bstep (se 2 (by rfl) ⟨15938901, by rfl⟩ : syracuseStep 42503737 = 31877803) B31877803
theorem B10492679 : Blo 968591 10492679 := bstep (se 1 (by rfl) ⟨7869509, by rfl⟩ : syracuseStep 10492679 = 15739019) B15739019
theorem B7676315 : Blo 968591 7676315 := bstep (se 1 (by rfl) ⟨5757236, by rfl⟩ : syracuseStep 7676315 = 11514473) B11514473
theorem B2765087 : Blo 968591 2765087 := bstep (se 1 (by rfl) ⟨2073815, by rfl⟩ : syracuseStep 2765087 = 4147631) B4147631
theorem B1454375 : Blo 968591 1454375 := bstep (se 1 (by rfl) ⟨1090781, by rfl⟩ : syracuseStep 1454375 = 2181563) B2181563
theorem B11809903 : Blo 968591 11809903 := bstep (se 1 (by rfl) ⟨8857427, by rfl⟩ : syracuseStep 11809903 = 17714855) B17714855
theorem B1455263 : Blo 968591 1455263 := bstep (se 1 (by rfl) ⟨1091447, by rfl⟩ : syracuseStep 1455263 = 2182895) B2182895
theorem B90985885 : Blo 968591 90985885 := bstep (se 3 (by rfl) ⟨17059853, by rfl⟩ : syracuseStep 90985885 = 34119707) B34119707
theorem B9103927 : Blo 968591 9103927 := bstep (se 1 (by rfl) ⟨6827945, by rfl⟩ : syracuseStep 9103927 = 13655891) B13655891
theorem B16776983 : Blo 968591 16776983 := bstep (se 1 (by rfl) ⟨12582737, by rfl⟩ : syracuseStep 16776983 = 25165475) B25165475
theorem B5117543 : Blo 968591 5117543 := bstep (se 1 (by rfl) ⟨3838157, by rfl⟩ : syracuseStep 5117543 = 7676315) B7676315
theorem B1843391 : Blo 968591 1843391 := bstep (se 1 (by rfl) ⟨1382543, by rfl⟩ : syracuseStep 1843391 = 2765087) B2765087
theorem B11184655 : Blo 968591 11184655 := bstep (se 1 (by rfl) ⟨8388491, by rfl⟩ : syracuseStep 11184655 = 16776983) B16776983
theorem B12138569 : Blo 968591 12138569 := bstep (se 2 (by rfl) ⟨4551963, by rfl⟩ : syracuseStep 12138569 = 9103927) B9103927
theorem B6995119 : Blo 968591 6995119 := bstep (se 1 (by rfl) ⟨5246339, by rfl⟩ : syracuseStep 6995119 = 10492679) B10492679
theorem B56671649 : Blo 968591 56671649 := bstep (se 2 (by rfl) ⟨21251868, by rfl⟩ : syracuseStep 56671649 = 42503737) B42503737
theorem B15746537 : Blo 968591 15746537 := bstep (se 2 (by rfl) ⟨5904951, by rfl⟩ : syracuseStep 15746537 = 11809903) B11809903
theorem B969583 : Blo 968591 969583 := bstep (se 1 (by rfl) ⟨727187, by rfl⟩ : syracuseStep 969583 = 1454375) B1454375
theorem B970175 : Blo 968591 970175 := bstep (se 1 (by rfl) ⟨727631, by rfl⟩ : syracuseStep 970175 = 1455263) B1455263
theorem B485258053 : Blo 968591 485258053 := bstep (se 4 (by rfl) ⟨45492942, by rfl⟩ : syracuseStep 485258053 = 90985885) B90985885
theorem B14912873 : Blo 968591 14912873 := bstep (se 2 (by rfl) ⟨5592327, by rfl⟩ : syracuseStep 14912873 = 11184655) B11184655
theorem B3411695 : Blo 968591 3411695 := bstep (se 1 (by rfl) ⟨2558771, by rfl⟩ : syracuseStep 3411695 = 5117543) B5117543
theorem B647010737 : Blo 968591 647010737 := bstep (se 2 (by rfl) ⟨242629026, by rfl⟩ : syracuseStep 647010737 = 485258053) B485258053
theorem B10497691 : Blo 968591 10497691 := bstep (se 1 (by rfl) ⟨7873268, by rfl⟩ : syracuseStep 10497691 = 15746537) B15746537
theorem B1228927 : Blo 968591 1228927 := bstep (se 1 (by rfl) ⟨921695, by rfl⟩ : syracuseStep 1228927 = 1843391) B1843391
theorem B9326825 : Blo 968591 9326825 := bstep (se 2 (by rfl) ⟨3497559, by rfl⟩ : syracuseStep 9326825 = 6995119) B6995119
theorem B8092379 : Blo 968591 8092379 := bstep (se 1 (by rfl) ⟨6069284, by rfl⟩ : syracuseStep 8092379 = 12138569) B12138569
theorem B37781099 : Blo 968591 37781099 := bstep (se 1 (by rfl) ⟨28335824, by rfl⟩ : syracuseStep 37781099 = 56671649) B56671649
theorem B1638569 : Blo 968591 1638569 := bstep (se 2 (by rfl) ⟨614463, by rfl⟩ : syracuseStep 1638569 = 1228927) B1228927
theorem B13996921 : Blo 968591 13996921 := bstep (se 2 (by rfl) ⟨5248845, by rfl⟩ : syracuseStep 13996921 = 10497691) B10497691
theorem B9941915 : Blo 968591 9941915 := bstep (se 1 (by rfl) ⟨7456436, by rfl⟩ : syracuseStep 9941915 = 14912873) B14912873
theorem B2274463 : Blo 968591 2274463 := bstep (se 1 (by rfl) ⟨1705847, by rfl⟩ : syracuseStep 2274463 = 3411695) B3411695
theorem B431340491 : Blo 968591 431340491 := bstep (se 1 (by rfl) ⟨323505368, by rfl⟩ : syracuseStep 431340491 = 647010737) B647010737
theorem B5394919 : Blo 968591 5394919 := bstep (se 1 (by rfl) ⟨4046189, by rfl⟩ : syracuseStep 5394919 = 8092379) B8092379
theorem B25187399 : Blo 968591 25187399 := bstep (se 1 (by rfl) ⟨18890549, by rfl⟩ : syracuseStep 25187399 = 37781099) B37781099
theorem B6217883 : Blo 968591 6217883 := bstep (se 1 (by rfl) ⟨4663412, by rfl⟩ : syracuseStep 6217883 = 9326825) B9326825
theorem B12130469 : Blo 968591 12130469 := bstep (se 4 (by rfl) ⟨1137231, by rfl⟩ : syracuseStep 12130469 = 2274463) B2274463
theorem B6627943 : Blo 968591 6627943 := bstep (se 1 (by rfl) ⟨4970957, by rfl⟩ : syracuseStep 6627943 = 9941915) B9941915
theorem B1092379 : Blo 968591 1092379 := bstep (se 1 (by rfl) ⟨819284, by rfl⟩ : syracuseStep 1092379 = 1638569) B1638569
theorem B16791599 : Blo 968591 16791599 := bstep (se 1 (by rfl) ⟨12593699, by rfl⟩ : syracuseStep 16791599 = 25187399) B25187399
theorem B4145255 : Blo 968591 4145255 := bstep (se 1 (by rfl) ⟨3108941, by rfl⟩ : syracuseStep 4145255 = 6217883) B6217883
theorem B7193225 : Blo 968591 7193225 := bstep (se 2 (by rfl) ⟨2697459, by rfl⟩ : syracuseStep 7193225 = 5394919) B5394919
theorem B18662561 : Blo 968591 18662561 := bstep (se 2 (by rfl) ⟨6998460, by rfl⟩ : syracuseStep 18662561 = 13996921) B13996921
theorem B287560327 : Blo 968591 287560327 := bstep (se 1 (by rfl) ⟨215670245, by rfl⟩ : syracuseStep 287560327 = 431340491) B431340491
theorem B2763503 : Blo 968591 2763503 := bstep (se 1 (by rfl) ⟨2072627, by rfl⟩ : syracuseStep 2763503 = 4145255) B4145255
theorem B4795483 : Blo 968591 4795483 := bstep (se 1 (by rfl) ⟨3596612, by rfl⟩ : syracuseStep 4795483 = 7193225) B7193225
theorem B1456505 : Blo 968591 1456505 := bstep (se 2 (by rfl) ⟨546189, by rfl⟩ : syracuseStep 1456505 = 1092379) B1092379
theorem B11194399 : Blo 968591 11194399 := bstep (se 1 (by rfl) ⟨8395799, by rfl⟩ : syracuseStep 11194399 = 16791599) B16791599
theorem B12441707 : Blo 968591 12441707 := bstep (se 1 (by rfl) ⟨9331280, by rfl⟩ : syracuseStep 12441707 = 18662561) B18662561
theorem B8837257 : Blo 968591 8837257 := bstep (se 2 (by rfl) ⟨3313971, by rfl⟩ : syracuseStep 8837257 = 6627943) B6627943
theorem B8086979 : Blo 968591 8086979 := bstep (se 1 (by rfl) ⟨6065234, by rfl⟩ : syracuseStep 8086979 = 12130469) B12130469
theorem B383413769 : Blo 968591 383413769 := bstep (se 2 (by rfl) ⟨143780163, by rfl⟩ : syracuseStep 383413769 = 287560327) B287560327
theorem B21565277 : Blo 968591 21565277 := bstep (se 3 (by rfl) ⟨4043489, by rfl⟩ : syracuseStep 21565277 = 8086979) B8086979
theorem B8294471 : Blo 968591 8294471 := bstep (se 1 (by rfl) ⟨6220853, by rfl⟩ : syracuseStep 8294471 = 12441707) B12441707
theorem B6393977 : Blo 968591 6393977 := bstep (se 2 (by rfl) ⟨2397741, by rfl⟩ : syracuseStep 6393977 = 4795483) B4795483
theorem B1842335 : Blo 968591 1842335 := bstep (se 1 (by rfl) ⟨1381751, by rfl⟩ : syracuseStep 1842335 = 2763503) B2763503
theorem B14925865 : Blo 968591 14925865 := bstep (se 2 (by rfl) ⟨5597199, by rfl⟩ : syracuseStep 14925865 = 11194399) B11194399
theorem B255609179 : Blo 968591 255609179 := bstep (se 1 (by rfl) ⟨191706884, by rfl⟩ : syracuseStep 255609179 = 383413769) B383413769
theorem B11783009 : Blo 968591 11783009 := bstep (se 2 (by rfl) ⟨4418628, by rfl⟩ : syracuseStep 11783009 = 8837257) B8837257
theorem B971003 : Blo 968591 971003 := bstep (se 1 (by rfl) ⟨728252, by rfl⟩ : syracuseStep 971003 = 1456505) B1456505
theorem B4262651 : Blo 968591 4262651 := bstep (se 1 (by rfl) ⟨3196988, by rfl⟩ : syracuseStep 4262651 = 6393977) B6393977
theorem B19901153 : Blo 968591 19901153 := bstep (se 2 (by rfl) ⟨7462932, by rfl⟩ : syracuseStep 19901153 = 14925865) B14925865
theorem B170406119 : Blo 968591 170406119 := bstep (se 1 (by rfl) ⟨127804589, by rfl⟩ : syracuseStep 170406119 = 255609179) B255609179
theorem B1228223 : Blo 968591 1228223 := bstep (se 1 (by rfl) ⟨921167, by rfl⟩ : syracuseStep 1228223 = 1842335) B1842335
theorem B7855339 : Blo 968591 7855339 := bstep (se 1 (by rfl) ⟨5891504, by rfl⟩ : syracuseStep 7855339 = 11783009) B11783009
theorem B14376851 : Blo 968591 14376851 := bstep (se 1 (by rfl) ⟨10782638, by rfl⟩ : syracuseStep 14376851 = 21565277) B21565277
theorem B5529647 : Blo 968591 5529647 := bstep (se 1 (by rfl) ⟨4147235, by rfl⟩ : syracuseStep 5529647 = 8294471) B8294471
theorem B9584567 : Blo 968591 9584567 := bstep (se 1 (by rfl) ⟨7188425, by rfl⟩ : syracuseStep 9584567 = 14376851) B14376851
theorem B3686431 : Blo 968591 3686431 := bstep (se 1 (by rfl) ⟨2764823, by rfl⟩ : syracuseStep 3686431 = 5529647) B5529647
theorem B10473785 : Blo 968591 10473785 := bstep (se 2 (by rfl) ⟨3927669, by rfl⟩ : syracuseStep 10473785 = 7855339) B7855339
theorem B454416317 : Blo 968591 454416317 := bstep (se 3 (by rfl) ⟨85203059, by rfl⟩ : syracuseStep 454416317 = 170406119) B170406119
theorem B2841767 : Blo 968591 2841767 := bstep (se 1 (by rfl) ⟨2131325, by rfl⟩ : syracuseStep 2841767 = 4262651) B4262651
theorem B13267435 : Blo 968591 13267435 := bstep (se 1 (by rfl) ⟨9950576, by rfl⟩ : syracuseStep 13267435 = 19901153) B19901153
theorem B3275261 : Blo 968591 3275261 := bstep (se 3 (by rfl) ⟨614111, by rfl⟩ : syracuseStep 3275261 = 1228223) B1228223
theorem B4915241 : Blo 968591 4915241 := bstep (se 2 (by rfl) ⟨1843215, by rfl⟩ : syracuseStep 4915241 = 3686431) B3686431
theorem B6982523 : Blo 968591 6982523 := bstep (se 1 (by rfl) ⟨5236892, by rfl⟩ : syracuseStep 6982523 = 10473785) B10473785
theorem B302944211 : Blo 968591 302944211 := bstep (se 1 (by rfl) ⟨227208158, by rfl⟩ : syracuseStep 302944211 = 454416317) B454416317
theorem B2183507 : Blo 968591 2183507 := bstep (se 1 (by rfl) ⟨1637630, by rfl⟩ : syracuseStep 2183507 = 3275261) B3275261
theorem B1894511 : Blo 968591 1894511 := bstep (se 1 (by rfl) ⟨1420883, by rfl⟩ : syracuseStep 1894511 = 2841767) B2841767
theorem B17689913 : Blo 968591 17689913 := bstep (se 2 (by rfl) ⟨6633717, by rfl⟩ : syracuseStep 17689913 = 13267435) B13267435
theorem B6389711 : Blo 968591 6389711 := bstep (se 1 (by rfl) ⟨4792283, by rfl⟩ : syracuseStep 6389711 = 9584567) B9584567
theorem B3276827 : Blo 968591 3276827 := bstep (se 1 (by rfl) ⟨2457620, by rfl⟩ : syracuseStep 3276827 = 4915241) B4915241
theorem B4655015 : Blo 968591 4655015 := bstep (se 1 (by rfl) ⟨3491261, by rfl⟩ : syracuseStep 4655015 = 6982523) B6982523
theorem B201962807 : Blo 968591 201962807 := bstep (se 1 (by rfl) ⟨151472105, by rfl⟩ : syracuseStep 201962807 = 302944211) B302944211
theorem B1455671 : Blo 968591 1455671 := bstep (se 1 (by rfl) ⟨1091753, by rfl⟩ : syracuseStep 1455671 = 2183507) B2183507
theorem B1263007 : Blo 968591 1263007 := bstep (se 1 (by rfl) ⟨947255, by rfl⟩ : syracuseStep 1263007 = 1894511) B1894511
theorem B11793275 : Blo 968591 11793275 := bstep (se 1 (by rfl) ⟨8844956, by rfl⟩ : syracuseStep 11793275 = 17689913) B17689913
theorem B4259807 : Blo 968591 4259807 := bstep (se 1 (by rfl) ⟨3194855, by rfl⟩ : syracuseStep 4259807 = 6389711) B6389711
theorem B1684009 : Blo 968591 1684009 := bstep (se 2 (by rfl) ⟨631503, by rfl⟩ : syracuseStep 1684009 = 1263007) B1263007
theorem B970447 : Blo 968591 970447 := bstep (se 1 (by rfl) ⟨727835, by rfl⟩ : syracuseStep 970447 = 1455671) B1455671
theorem B2839871 : Blo 968591 2839871 := bstep (se 1 (by rfl) ⟨2129903, by rfl⟩ : syracuseStep 2839871 = 4259807) B4259807
theorem B2184551 : Blo 968591 2184551 := bstep (se 1 (by rfl) ⟨1638413, by rfl⟩ : syracuseStep 2184551 = 3276827) B3276827
theorem B3103343 : Blo 968591 3103343 := bstep (se 1 (by rfl) ⟨2327507, by rfl⟩ : syracuseStep 3103343 = 4655015) B4655015
theorem B7862183 : Blo 968591 7862183 := bstep (se 1 (by rfl) ⟨5896637, by rfl⟩ : syracuseStep 7862183 = 11793275) B11793275
theorem B134641871 : Blo 968591 134641871 := bstep (se 1 (by rfl) ⟨100981403, by rfl⟩ : syracuseStep 134641871 = 201962807) B201962807
theorem B8981381 : Blo 968591 8981381 := bstep (se 4 (by rfl) ⟨842004, by rfl⟩ : syracuseStep 8981381 = 1684009) B1684009
theorem B7572989 : Blo 968591 7572989 := bstep (se 3 (by rfl) ⟨1419935, by rfl⟩ : syracuseStep 7572989 = 2839871) B2839871
theorem B2068895 : Blo 968591 2068895 := bstep (se 1 (by rfl) ⟨1551671, by rfl⟩ : syracuseStep 2068895 = 3103343) B3103343
theorem B89761247 : Blo 968591 89761247 := bstep (se 1 (by rfl) ⟨67320935, by rfl⟩ : syracuseStep 89761247 = 134641871) B134641871
theorem B1456367 : Blo 968591 1456367 := bstep (se 1 (by rfl) ⟨1092275, by rfl⟩ : syracuseStep 1456367 = 2184551) B2184551
theorem B5241455 : Blo 968591 5241455 := bstep (se 1 (by rfl) ⟨3931091, by rfl⟩ : syracuseStep 5241455 = 7862183) B7862183
theorem B5048659 : Blo 968591 5048659 := bstep (se 1 (by rfl) ⟨3786494, by rfl⟩ : syracuseStep 5048659 = 7572989) B7572989
theorem B1379263 : Blo 968591 1379263 := bstep (se 1 (by rfl) ⟨1034447, by rfl⟩ : syracuseStep 1379263 = 2068895) B2068895
theorem B59840831 : Blo 968591 59840831 := bstep (se 1 (by rfl) ⟨44880623, by rfl⟩ : syracuseStep 59840831 = 89761247) B89761247
theorem B970911 : Blo 968591 970911 := bstep (se 1 (by rfl) ⟨728183, by rfl⟩ : syracuseStep 970911 = 1456367) B1456367
theorem B3494303 : Blo 968591 3494303 := bstep (se 1 (by rfl) ⟨2620727, by rfl⟩ : syracuseStep 3494303 = 5241455) B5241455
theorem B23950349 : Blo 968591 23950349 := bstep (se 3 (by rfl) ⟨4490690, by rfl⟩ : syracuseStep 23950349 = 8981381) B8981381
theorem B2329535 : Blo 968591 2329535 := bstep (se 1 (by rfl) ⟨1747151, by rfl⟩ : syracuseStep 2329535 = 3494303) B3494303
theorem B1839017 : Blo 968591 1839017 := bstep (se 2 (by rfl) ⟨689631, by rfl⟩ : syracuseStep 1839017 = 1379263) B1379263
theorem B15966899 : Blo 968591 15966899 := bstep (se 1 (by rfl) ⟨11975174, by rfl⟩ : syracuseStep 15966899 = 23950349) B23950349
theorem B6731545 : Blo 968591 6731545 := bstep (se 2 (by rfl) ⟨2524329, by rfl⟩ : syracuseStep 6731545 = 5048659) B5048659
theorem B39893887 : Blo 968591 39893887 := bstep (se 1 (by rfl) ⟨29920415, by rfl⟩ : syracuseStep 39893887 = 59840831) B59840831
theorem B53191849 : Blo 968591 53191849 := bstep (se 2 (by rfl) ⟨19946943, by rfl⟩ : syracuseStep 53191849 = 39893887) B39893887
theorem B1553023 : Blo 968591 1553023 := bstep (se 1 (by rfl) ⟨1164767, by rfl⟩ : syracuseStep 1553023 = 2329535) B2329535
theorem B1226011 : Blo 968591 1226011 := bstep (se 1 (by rfl) ⟨919508, by rfl⟩ : syracuseStep 1226011 = 1839017) B1839017
theorem B10644599 : Blo 968591 10644599 := bstep (se 1 (by rfl) ⟨7983449, by rfl⟩ : syracuseStep 10644599 = 15966899) B15966899
theorem B8975393 : Blo 968591 8975393 := bstep (se 2 (by rfl) ⟨3365772, by rfl⟩ : syracuseStep 8975393 = 6731545) B6731545
theorem B2070697 : Blo 968591 2070697 := bstep (se 2 (by rfl) ⟨776511, by rfl⟩ : syracuseStep 2070697 = 1553023) B1553023
theorem B28385597 : Blo 968591 28385597 := bstep (se 3 (by rfl) ⟨5322299, by rfl⟩ : syracuseStep 28385597 = 10644599) B10644599
theorem B70922465 : Blo 968591 70922465 := bstep (se 2 (by rfl) ⟨26595924, by rfl⟩ : syracuseStep 70922465 = 53191849) B53191849
theorem B5983595 : Blo 968591 5983595 := bstep (se 1 (by rfl) ⟨4487696, by rfl⟩ : syracuseStep 5983595 = 8975393) B8975393
theorem B1634681 : Blo 968591 1634681 := bstep (se 2 (by rfl) ⟨613005, by rfl⟩ : syracuseStep 1634681 = 1226011) B1226011
theorem B75694925 : Blo 968591 75694925 := bstep (se 3 (by rfl) ⟨14192798, by rfl⟩ : syracuseStep 75694925 = 28385597) B28385597
theorem B2760929 : Blo 968591 2760929 := bstep (se 2 (by rfl) ⟨1035348, by rfl⟩ : syracuseStep 2760929 = 2070697) B2070697
theorem B1089787 : Blo 968591 1089787 := bstep (se 1 (by rfl) ⟨817340, by rfl⟩ : syracuseStep 1089787 = 1634681) B1634681
theorem B3989063 : Blo 968591 3989063 := bstep (se 1 (by rfl) ⟨2991797, by rfl⟩ : syracuseStep 3989063 = 5983595) B5983595
theorem B47281643 : Blo 968591 47281643 := bstep (se 1 (by rfl) ⟨35461232, by rfl⟩ : syracuseStep 47281643 = 70922465) B70922465
theorem B50463283 : Blo 968591 50463283 := bstep (se 1 (by rfl) ⟨37847462, by rfl⟩ : syracuseStep 50463283 = 75694925) B75694925
theorem B2659375 : Blo 968591 2659375 := bstep (se 1 (by rfl) ⟨1994531, by rfl⟩ : syracuseStep 2659375 = 3989063) B3989063
theorem B1840619 : Blo 968591 1840619 := bstep (se 1 (by rfl) ⟨1380464, by rfl⟩ : syracuseStep 1840619 = 2760929) B2760929
theorem B1453049 : Blo 968591 1453049 := bstep (se 2 (by rfl) ⟨544893, by rfl⟩ : syracuseStep 1453049 = 1089787) B1089787
theorem B31521095 : Blo 968591 31521095 := bstep (se 1 (by rfl) ⟨23640821, by rfl⟩ : syracuseStep 31521095 = 47281643) B47281643
theorem B21014063 : Blo 968591 21014063 := bstep (se 1 (by rfl) ⟨15760547, by rfl⟩ : syracuseStep 21014063 = 31521095) B31521095
theorem B67284377 : Blo 968591 67284377 := bstep (se 2 (by rfl) ⟨25231641, by rfl⟩ : syracuseStep 67284377 = 50463283) B50463283
theorem B1227079 : Blo 968591 1227079 := bstep (se 1 (by rfl) ⟨920309, by rfl⟩ : syracuseStep 1227079 = 1840619) B1840619
theorem B968699 : Blo 968591 968699 := bstep (se 1 (by rfl) ⟨726524, by rfl⟩ : syracuseStep 968699 = 1453049) B1453049
theorem B14183333 : Blo 968591 14183333 := bstep (se 4 (by rfl) ⟨1329687, by rfl⟩ : syracuseStep 14183333 = 2659375) B2659375
theorem B14009375 : Blo 968591 14009375 := bstep (se 1 (by rfl) ⟨10507031, by rfl⟩ : syracuseStep 14009375 = 21014063) B21014063
theorem B9455555 : Blo 968591 9455555 := bstep (se 1 (by rfl) ⟨7091666, by rfl⟩ : syracuseStep 9455555 = 14183333) B14183333
theorem B44856251 : Blo 968591 44856251 := bstep (se 1 (by rfl) ⟨33642188, by rfl⟩ : syracuseStep 44856251 = 67284377) B67284377
theorem B1636105 : Blo 968591 1636105 := bstep (se 2 (by rfl) ⟨613539, by rfl⟩ : syracuseStep 1636105 = 1227079) B1227079
theorem B37358333 : Blo 968591 37358333 := bstep (se 3 (by rfl) ⟨7004687, by rfl⟩ : syracuseStep 37358333 = 14009375) B14009375
theorem B6303703 : Blo 968591 6303703 := bstep (se 1 (by rfl) ⟨4727777, by rfl⟩ : syracuseStep 6303703 = 9455555) B9455555
theorem B2181473 : Blo 968591 2181473 := bstep (se 2 (by rfl) ⟨818052, by rfl⟩ : syracuseStep 2181473 = 1636105) B1636105
theorem B29904167 : Blo 968591 29904167 := bstep (se 1 (by rfl) ⟨22428125, by rfl⟩ : syracuseStep 29904167 = 44856251) B44856251
theorem B24905555 : Blo 968591 24905555 := bstep (se 1 (by rfl) ⟨18679166, by rfl⟩ : syracuseStep 24905555 = 37358333) B37358333
theorem B1454315 : Blo 968591 1454315 := bstep (se 1 (by rfl) ⟨1090736, by rfl⟩ : syracuseStep 1454315 = 2181473) B2181473
theorem B8404937 : Blo 968591 8404937 := bstep (se 2 (by rfl) ⟨3151851, by rfl⟩ : syracuseStep 8404937 = 6303703) B6303703
theorem B79744445 : Blo 968591 79744445 := bstep (se 3 (by rfl) ⟨14952083, by rfl⟩ : syracuseStep 79744445 = 29904167) B29904167
theorem B53162963 : Blo 968591 53162963 := bstep (se 1 (by rfl) ⟨39872222, by rfl⟩ : syracuseStep 53162963 = 79744445) B79744445
theorem B969543 : Blo 968591 969543 := bstep (se 1 (by rfl) ⟨727157, by rfl⟩ : syracuseStep 969543 = 1454315) B1454315
theorem B16603703 : Blo 968591 16603703 := bstep (se 1 (by rfl) ⟨12452777, by rfl⟩ : syracuseStep 16603703 = 24905555) B24905555
theorem B5603291 : Blo 968591 5603291 := bstep (se 1 (by rfl) ⟨4202468, by rfl⟩ : syracuseStep 5603291 = 8404937) B8404937
theorem B35441975 : Blo 968591 35441975 := bstep (se 1 (by rfl) ⟨26581481, by rfl⟩ : syracuseStep 35441975 = 53162963) B53162963
theorem B11069135 : Blo 968591 11069135 := bstep (se 1 (by rfl) ⟨8301851, by rfl⟩ : syracuseStep 11069135 = 16603703) B16603703
theorem B3735527 : Blo 968591 3735527 := bstep (se 1 (by rfl) ⟨2801645, by rfl⟩ : syracuseStep 3735527 = 5603291) B5603291
theorem B23627983 : Blo 968591 23627983 := bstep (se 1 (by rfl) ⟨17720987, by rfl⟩ : syracuseStep 23627983 = 35441975) B35441975
theorem B7379423 : Blo 968591 7379423 := bstep (se 1 (by rfl) ⟨5534567, by rfl⟩ : syracuseStep 7379423 = 11069135) B11069135
theorem B39845621 : Blo 968591 39845621 := bstep (se 5 (by rfl) ⟨1867763, by rfl⟩ : syracuseStep 39845621 = 3735527) B3735527
theorem B4919615 : Blo 968591 4919615 := bstep (se 1 (by rfl) ⟨3689711, by rfl⟩ : syracuseStep 4919615 = 7379423) B7379423
theorem B31503977 : Blo 968591 31503977 := bstep (se 2 (by rfl) ⟨11813991, by rfl⟩ : syracuseStep 31503977 = 23627983) B23627983
theorem B26563747 : Blo 968591 26563747 := bstep (se 1 (by rfl) ⟨19922810, by rfl⟩ : syracuseStep 26563747 = 39845621) B39845621
theorem B3279743 : Blo 968591 3279743 := bstep (se 1 (by rfl) ⟨2459807, by rfl⟩ : syracuseStep 3279743 = 4919615) B4919615
theorem B35418329 : Blo 968591 35418329 := bstep (se 2 (by rfl) ⟨13281873, by rfl⟩ : syracuseStep 35418329 = 26563747) B26563747
theorem B21002651 : Blo 968591 21002651 := bstep (se 1 (by rfl) ⟨15751988, by rfl⟩ : syracuseStep 21002651 = 31503977) B31503977
theorem B14001767 : Blo 968591 14001767 := bstep (se 1 (by rfl) ⟨10501325, by rfl⟩ : syracuseStep 14001767 = 21002651) B21002651
theorem B23612219 : Blo 968591 23612219 := bstep (se 1 (by rfl) ⟨17709164, by rfl⟩ : syracuseStep 23612219 = 35418329) B35418329
theorem B2186495 : Blo 968591 2186495 := bstep (se 1 (by rfl) ⟨1639871, by rfl⟩ : syracuseStep 2186495 = 3279743) B3279743
theorem B15741479 : Blo 968591 15741479 := bstep (se 1 (by rfl) ⟨11806109, by rfl⟩ : syracuseStep 15741479 = 23612219) B23612219
theorem B1457663 : Blo 968591 1457663 := bstep (se 1 (by rfl) ⟨1093247, by rfl⟩ : syracuseStep 1457663 = 2186495) B2186495
theorem B9334511 : Blo 968591 9334511 := bstep (se 1 (by rfl) ⟨7000883, by rfl⟩ : syracuseStep 9334511 = 14001767) B14001767
theorem B41977277 : Blo 968591 41977277 := bstep (se 3 (by rfl) ⟨7870739, by rfl⟩ : syracuseStep 41977277 = 15741479) B15741479
theorem B971775 : Blo 968591 971775 := bstep (se 1 (by rfl) ⟨728831, by rfl⟩ : syracuseStep 971775 = 1457663) B1457663
theorem B6223007 : Blo 968591 6223007 := bstep (se 1 (by rfl) ⟨4667255, by rfl⟩ : syracuseStep 6223007 = 9334511) B9334511
theorem B27984851 : Blo 968591 27984851 := bstep (se 1 (by rfl) ⟨20988638, by rfl⟩ : syracuseStep 27984851 = 41977277) B41977277
theorem B4148671 : Blo 968591 4148671 := bstep (se 1 (by rfl) ⟨3111503, by rfl⟩ : syracuseStep 4148671 = 6223007) B6223007
theorem B18656567 : Blo 968591 18656567 := bstep (se 1 (by rfl) ⟨13992425, by rfl⟩ : syracuseStep 18656567 = 27984851) B27984851
theorem B5531561 : Blo 968591 5531561 := bstep (se 2 (by rfl) ⟨2074335, by rfl⟩ : syracuseStep 5531561 = 4148671) B4148671
theorem B3687707 : Blo 968591 3687707 := bstep (se 1 (by rfl) ⟨2765780, by rfl⟩ : syracuseStep 3687707 = 5531561) B5531561
theorem B12437711 : Blo 968591 12437711 := bstep (se 1 (by rfl) ⟨9328283, by rfl⟩ : syracuseStep 12437711 = 18656567) B18656567
theorem B2458471 : Blo 968591 2458471 := bstep (se 1 (by rfl) ⟨1843853, by rfl⟩ : syracuseStep 2458471 = 3687707) B3687707
theorem B8291807 : Blo 968591 8291807 := bstep (se 1 (by rfl) ⟨6218855, by rfl⟩ : syracuseStep 8291807 = 12437711) B12437711
theorem B3277961 : Blo 968591 3277961 := bstep (se 2 (by rfl) ⟨1229235, by rfl⟩ : syracuseStep 3277961 = 2458471) B2458471
theorem B5527871 : Blo 968591 5527871 := bstep (se 1 (by rfl) ⟨4145903, by rfl⟩ : syracuseStep 5527871 = 8291807) B8291807
theorem B3685247 : Blo 968591 3685247 := bstep (se 1 (by rfl) ⟨2763935, by rfl⟩ : syracuseStep 3685247 = 5527871) B5527871
theorem B2185307 : Blo 968591 2185307 := bstep (se 1 (by rfl) ⟨1638980, by rfl⟩ : syracuseStep 2185307 = 3277961) B3277961
theorem B1456871 : Blo 968591 1456871 := bstep (se 1 (by rfl) ⟨1092653, by rfl⟩ : syracuseStep 1456871 = 2185307) B2185307
theorem B2456831 : Blo 968591 2456831 := bstep (se 1 (by rfl) ⟨1842623, by rfl⟩ : syracuseStep 2456831 = 3685247) B3685247
theorem B971247 : Blo 968591 971247 := bstep (se 1 (by rfl) ⟨728435, by rfl⟩ : syracuseStep 971247 = 1456871) B1456871
theorem B1637887 : Blo 968591 1637887 := bstep (se 1 (by rfl) ⟨1228415, by rfl⟩ : syracuseStep 1637887 = 2456831) B2456831
theorem B2183849 : Blo 968591 2183849 := bstep (se 2 (by rfl) ⟨818943, by rfl⟩ : syracuseStep 2183849 = 1637887) B1637887
theorem B1455899 : Blo 968591 1455899 := bstep (se 1 (by rfl) ⟨1091924, by rfl⟩ : syracuseStep 1455899 = 2183849) B2183849
theorem B970599 : Blo 968591 970599 := bstep (se 1 (by rfl) ⟨727949, by rfl⟩ : syracuseStep 970599 = 1455899) B1455899

theorem C0 (j : ℕ) (h1 : 242147 ≤ j) (h2 : j ≤ 242846) : Blo 968591 (4 * j + 3) := by
  interval_cases j
  · exact B968591
  · exact B968595
  · exact B968599
  · exact B968603
  · exact B968607
  · exact B968611
  · exact B968615
  · exact B968619
  · exact B968623
  · exact B968627
  · exact B968631
  · exact B968635
  · exact B968639
  · exact B968643
  · exact B968647
  · exact B968651
  · exact B968655
  · exact B968659
  · exact B968663
  · exact B968667
  · exact B968671
  · exact B968675
  · exact B968679
  · exact B968683
  · exact B968687
  · exact B968691
  · exact B968695
  · exact B968699
  · exact B968703
  · exact B968707
  · exact B968711
  · exact B968715
  · exact B968719
  · exact B968723
  · exact B968727
  · exact B968731
  · exact B968735
  · exact B968739
  · exact B968743
  · exact B968747
  · exact B968751
  · exact B968755
  · exact B968759
  · exact B968763
  · exact B968767
  · exact B968771
  · exact B968775
  · exact B968779
  · exact B968783
  · exact B968787
  · exact B968791
  · exact B968795
  · exact B968799
  · exact B968803
  · exact B968807
  · exact B968811
  · exact B968815
  · exact B968819
  · exact B968823
  · exact B968827
  · exact B968831
  · exact B968835
  · exact B968839
  · exact B968843
  · exact B968847
  · exact B968851
  · exact B968855
  · exact B968859
  · exact B968863
  · exact B968867
  · exact B968871
  · exact B968875
  · exact B968879
  · exact B968883
  · exact B968887
  · exact B968891
  · exact B968895
  · exact B968899
  · exact B968903
  · exact B968907
  · exact B968911
  · exact B968915
  · exact B968919
  · exact B968923
  · exact B968927
  · exact B968931
  · exact B968935
  · exact B968939
  · exact B968943
  · exact B968947
  · exact B968951
  · exact B968955
  · exact B968959
  · exact B968963
  · exact B968967
  · exact B968971
  · exact B968975
  · exact B968979
  · exact B968983
  · exact B968987
  · exact B968991
  · exact B968995
  · exact B968999
  · exact B969003
  · exact B969007
  · exact B969011
  · exact B969015
  · exact B969019
  · exact B969023
  · exact B969027
  · exact B969031
  · exact B969035
  · exact B969039
  · exact B969043
  · exact B969047
  · exact B969051
  · exact B969055
  · exact B969059
  · exact B969063
  · exact B969067
  · exact B969071
  · exact B969075
  · exact B969079
  · exact B969083
  · exact B969087
  · exact B969091
  · exact B969095
  · exact B969099
  · exact B969103
  · exact B969107
  · exact B969111
  · exact B969115
  · exact B969119
  · exact B969123
  · exact B969127
  · exact B969131
  · exact B969135
  · exact B969139
  · exact B969143
  · exact B969147
  · exact B969151
  · exact B969155
  · exact B969159
  · exact B969163
  · exact B969167
  · exact B969171
  · exact B969175
  · exact B969179
  · exact B969183
  · exact B969187
  · exact B969191
  · exact B969195
  · exact B969199
  · exact B969203
  · exact B969207
  · exact B969211
  · exact B969215
  · exact B969219
  · exact B969223
  · exact B969227
  · exact B969231
  · exact B969235
  · exact B969239
  · exact B969243
  · exact B969247
  · exact B969251
  · exact B969255
  · exact B969259
  · exact B969263
  · exact B969267
  · exact B969271
  · exact B969275
  · exact B969279
  · exact B969283
  · exact B969287
  · exact B969291
  · exact B969295
  · exact B969299
  · exact B969303
  · exact B969307
  · exact B969311
  · exact B969315
  · exact B969319
  · exact B969323
  · exact B969327
  · exact B969331
  · exact B969335
  · exact B969339
  · exact B969343
  · exact B969347
  · exact B969351
  · exact B969355
  · exact B969359
  · exact B969363
  · exact B969367
  · exact B969371
  · exact B969375
  · exact B969379
  · exact B969383
  · exact B969387
  · exact B969391
  · exact B969395
  · exact B969399
  · exact B969403
  · exact B969407
  · exact B969411
  · exact B969415
  · exact B969419
  · exact B969423
  · exact B969427
  · exact B969431
  · exact B969435
  · exact B969439
  · exact B969443
  · exact B969447
  · exact B969451
  · exact B969455
  · exact B969459
  · exact B969463
  · exact B969467
  · exact B969471
  · exact B969475
  · exact B969479
  · exact B969483
  · exact B969487
  · exact B969491
  · exact B969495
  · exact B969499
  · exact B969503
  · exact B969507
  · exact B969511
  · exact B969515
  · exact B969519
  · exact B969523
  · exact B969527
  · exact B969531
  · exact B969535
  · exact B969539
  · exact B969543
  · exact B969547
  · exact B969551
  · exact B969555
  · exact B969559
  · exact B969563
  · exact B969567
  · exact B969571
  · exact B969575
  · exact B969579
  · exact B969583
  · exact B969587
  · exact B969591
  · exact B969595
  · exact B969599
  · exact B969603
  · exact B969607
  · exact B969611
  · exact B969615
  · exact B969619
  · exact B969623
  · exact B969627
  · exact B969631
  · exact B969635
  · exact B969639
  · exact B969643
  · exact B969647
  · exact B969651
  · exact B969655
  · exact B969659
  · exact B969663
  · exact B969667
  · exact B969671
  · exact B969675
  · exact B969679
  · exact B969683
  · exact B969687
  · exact B969691
  · exact B969695
  · exact B969699
  · exact B969703
  · exact B969707
  · exact B969711
  · exact B969715
  · exact B969719
  · exact B969723
  · exact B969727
  · exact B969731
  · exact B969735
  · exact B969739
  · exact B969743
  · exact B969747
  · exact B969751
  · exact B969755
  · exact B969759
  · exact B969763
  · exact B969767
  · exact B969771
  · exact B969775
  · exact B969779
  · exact B969783
  · exact B969787
  · exact B969791
  · exact B969795
  · exact B969799
  · exact B969803
  · exact B969807
  · exact B969811
  · exact B969815
  · exact B969819
  · exact B969823
  · exact B969827
  · exact B969831
  · exact B969835
  · exact B969839
  · exact B969843
  · exact B969847
  · exact B969851
  · exact B969855
  · exact B969859
  · exact B969863
  · exact B969867
  · exact B969871
  · exact B969875
  · exact B969879
  · exact B969883
  · exact B969887
  · exact B969891
  · exact B969895
  · exact B969899
  · exact B969903
  · exact B969907
  · exact B969911
  · exact B969915
  · exact B969919
  · exact B969923
  · exact B969927
  · exact B969931
  · exact B969935
  · exact B969939
  · exact B969943
  · exact B969947
  · exact B969951
  · exact B969955
  · exact B969959
  · exact B969963
  · exact B969967
  · exact B969971
  · exact B969975
  · exact B969979
  · exact B969983
  · exact B969987
  · exact B969991
  · exact B969995
  · exact B969999
  · exact B970003
  · exact B970007
  · exact B970011
  · exact B970015
  · exact B970019
  · exact B970023
  · exact B970027
  · exact B970031
  · exact B970035
  · exact B970039
  · exact B970043
  · exact B970047
  · exact B970051
  · exact B970055
  · exact B970059
  · exact B970063
  · exact B970067
  · exact B970071
  · exact B970075
  · exact B970079
  · exact B970083
  · exact B970087
  · exact B970091
  · exact B970095
  · exact B970099
  · exact B970103
  · exact B970107
  · exact B970111
  · exact B970115
  · exact B970119
  · exact B970123
  · exact B970127
  · exact B970131
  · exact B970135
  · exact B970139
  · exact B970143
  · exact B970147
  · exact B970151
  · exact B970155
  · exact B970159
  · exact B970163
  · exact B970167
  · exact B970171
  · exact B970175
  · exact B970179
  · exact B970183
  · exact B970187
  · exact B970191
  · exact B970195
  · exact B970199
  · exact B970203
  · exact B970207
  · exact B970211
  · exact B970215
  · exact B970219
  · exact B970223
  · exact B970227
  · exact B970231
  · exact B970235
  · exact B970239
  · exact B970243
  · exact B970247
  · exact B970251
  · exact B970255
  · exact B970259
  · exact B970263
  · exact B970267
  · exact B970271
  · exact B970275
  · exact B970279
  · exact B970283
  · exact B970287
  · exact B970291
  · exact B970295
  · exact B970299
  · exact B970303
  · exact B970307
  · exact B970311
  · exact B970315
  · exact B970319
  · exact B970323
  · exact B970327
  · exact B970331
  · exact B970335
  · exact B970339
  · exact B970343
  · exact B970347
  · exact B970351
  · exact B970355
  · exact B970359
  · exact B970363
  · exact B970367
  · exact B970371
  · exact B970375
  · exact B970379
  · exact B970383
  · exact B970387
  · exact B970391
  · exact B970395
  · exact B970399
  · exact B970403
  · exact B970407
  · exact B970411
  · exact B970415
  · exact B970419
  · exact B970423
  · exact B970427
  · exact B970431
  · exact B970435
  · exact B970439
  · exact B970443
  · exact B970447
  · exact B970451
  · exact B970455
  · exact B970459
  · exact B970463
  · exact B970467
  · exact B970471
  · exact B970475
  · exact B970479
  · exact B970483
  · exact B970487
  · exact B970491
  · exact B970495
  · exact B970499
  · exact B970503
  · exact B970507
  · exact B970511
  · exact B970515
  · exact B970519
  · exact B970523
  · exact B970527
  · exact B970531
  · exact B970535
  · exact B970539
  · exact B970543
  · exact B970547
  · exact B970551
  · exact B970555
  · exact B970559
  · exact B970563
  · exact B970567
  · exact B970571
  · exact B970575
  · exact B970579
  · exact B970583
  · exact B970587
  · exact B970591
  · exact B970595
  · exact B970599
  · exact B970603
  · exact B970607
  · exact B970611
  · exact B970615
  · exact B970619
  · exact B970623
  · exact B970627
  · exact B970631
  · exact B970635
  · exact B970639
  · exact B970643
  · exact B970647
  · exact B970651
  · exact B970655
  · exact B970659
  · exact B970663
  · exact B970667
  · exact B970671
  · exact B970675
  · exact B970679
  · exact B970683
  · exact B970687
  · exact B970691
  · exact B970695
  · exact B970699
  · exact B970703
  · exact B970707
  · exact B970711
  · exact B970715
  · exact B970719
  · exact B970723
  · exact B970727
  · exact B970731
  · exact B970735
  · exact B970739
  · exact B970743
  · exact B970747
  · exact B970751
  · exact B970755
  · exact B970759
  · exact B970763
  · exact B970767
  · exact B970771
  · exact B970775
  · exact B970779
  · exact B970783
  · exact B970787
  · exact B970791
  · exact B970795
  · exact B970799
  · exact B970803
  · exact B970807
  · exact B970811
  · exact B970815
  · exact B970819
  · exact B970823
  · exact B970827
  · exact B970831
  · exact B970835
  · exact B970839
  · exact B970843
  · exact B970847
  · exact B970851
  · exact B970855
  · exact B970859
  · exact B970863
  · exact B970867
  · exact B970871
  · exact B970875
  · exact B970879
  · exact B970883
  · exact B970887
  · exact B970891
  · exact B970895
  · exact B970899
  · exact B970903
  · exact B970907
  · exact B970911
  · exact B970915
  · exact B970919
  · exact B970923
  · exact B970927
  · exact B970931
  · exact B970935
  · exact B970939
  · exact B970943
  · exact B970947
  · exact B970951
  · exact B970955
  · exact B970959
  · exact B970963
  · exact B970967
  · exact B970971
  · exact B970975
  · exact B970979
  · exact B970983
  · exact B970987
  · exact B970991
  · exact B970995
  · exact B970999
  · exact B971003
  · exact B971007
  · exact B971011
  · exact B971015
  · exact B971019
  · exact B971023
  · exact B971027
  · exact B971031
  · exact B971035
  · exact B971039
  · exact B971043
  · exact B971047
  · exact B971051
  · exact B971055
  · exact B971059
  · exact B971063
  · exact B971067
  · exact B971071
  · exact B971075
  · exact B971079
  · exact B971083
  · exact B971087
  · exact B971091
  · exact B971095
  · exact B971099
  · exact B971103
  · exact B971107
  · exact B971111
  · exact B971115
  · exact B971119
  · exact B971123
  · exact B971127
  · exact B971131
  · exact B971135
  · exact B971139
  · exact B971143
  · exact B971147
  · exact B971151
  · exact B971155
  · exact B971159
  · exact B971163
  · exact B971167
  · exact B971171
  · exact B971175
  · exact B971179
  · exact B971183
  · exact B971187
  · exact B971191
  · exact B971195
  · exact B971199
  · exact B971203
  · exact B971207
  · exact B971211
  · exact B971215
  · exact B971219
  · exact B971223
  · exact B971227
  · exact B971231
  · exact B971235
  · exact B971239
  · exact B971243
  · exact B971247
  · exact B971251
  · exact B971255
  · exact B971259
  · exact B971263
  · exact B971267
  · exact B971271
  · exact B971275
  · exact B971279
  · exact B971283
  · exact B971287
  · exact B971291
  · exact B971295
  · exact B971299
  · exact B971303
  · exact B971307
  · exact B971311
  · exact B971315
  · exact B971319
  · exact B971323
  · exact B971327
  · exact B971331
  · exact B971335
  · exact B971339
  · exact B971343
  · exact B971347
  · exact B971351
  · exact B971355
  · exact B971359
  · exact B971363
  · exact B971367
  · exact B971371
  · exact B971375
  · exact B971379
  · exact B971383
  · exact B971387

theorem C1 (j : ℕ) (h1 : 242847 ≤ j) (h2 : j ≤ 243147) : Blo 968591 (4 * j + 3) := by
  interval_cases j
  · exact B971391
  · exact B971395
  · exact B971399
  · exact B971403
  · exact B971407
  · exact B971411
  · exact B971415
  · exact B971419
  · exact B971423
  · exact B971427
  · exact B971431
  · exact B971435
  · exact B971439
  · exact B971443
  · exact B971447
  · exact B971451
  · exact B971455
  · exact B971459
  · exact B971463
  · exact B971467
  · exact B971471
  · exact B971475
  · exact B971479
  · exact B971483
  · exact B971487
  · exact B971491
  · exact B971495
  · exact B971499
  · exact B971503
  · exact B971507
  · exact B971511
  · exact B971515
  · exact B971519
  · exact B971523
  · exact B971527
  · exact B971531
  · exact B971535
  · exact B971539
  · exact B971543
  · exact B971547
  · exact B971551
  · exact B971555
  · exact B971559
  · exact B971563
  · exact B971567
  · exact B971571
  · exact B971575
  · exact B971579
  · exact B971583
  · exact B971587
  · exact B971591
  · exact B971595
  · exact B971599
  · exact B971603
  · exact B971607
  · exact B971611
  · exact B971615
  · exact B971619
  · exact B971623
  · exact B971627
  · exact B971631
  · exact B971635
  · exact B971639
  · exact B971643
  · exact B971647
  · exact B971651
  · exact B971655
  · exact B971659
  · exact B971663
  · exact B971667
  · exact B971671
  · exact B971675
  · exact B971679
  · exact B971683
  · exact B971687
  · exact B971691
  · exact B971695
  · exact B971699
  · exact B971703
  · exact B971707
  · exact B971711
  · exact B971715
  · exact B971719
  · exact B971723
  · exact B971727
  · exact B971731
  · exact B971735
  · exact B971739
  · exact B971743
  · exact B971747
  · exact B971751
  · exact B971755
  · exact B971759
  · exact B971763
  · exact B971767
  · exact B971771
  · exact B971775
  · exact B971779
  · exact B971783
  · exact B971787
  · exact B971791
  · exact B971795
  · exact B971799
  · exact B971803
  · exact B971807
  · exact B971811
  · exact B971815
  · exact B971819
  · exact B971823
  · exact B971827
  · exact B971831
  · exact B971835
  · exact B971839
  · exact B971843
  · exact B971847
  · exact B971851
  · exact B971855
  · exact B971859
  · exact B971863
  · exact B971867
  · exact B971871
  · exact B971875
  · exact B971879
  · exact B971883
  · exact B971887
  · exact B971891
  · exact B971895
  · exact B971899
  · exact B971903
  · exact B971907
  · exact B971911
  · exact B971915
  · exact B971919
  · exact B971923
  · exact B971927
  · exact B971931
  · exact B971935
  · exact B971939
  · exact B971943
  · exact B971947
  · exact B971951
  · exact B971955
  · exact B971959
  · exact B971963
  · exact B971967
  · exact B971971
  · exact B971975
  · exact B971979
  · exact B971983
  · exact B971987
  · exact B971991
  · exact B971995
  · exact B971999
  · exact B972003
  · exact B972007
  · exact B972011
  · exact B972015
  · exact B972019
  · exact B972023
  · exact B972027
  · exact B972031
  · exact B972035
  · exact B972039
  · exact B972043
  · exact B972047
  · exact B972051
  · exact B972055
  · exact B972059
  · exact B972063
  · exact B972067
  · exact B972071
  · exact B972075
  · exact B972079
  · exact B972083
  · exact B972087
  · exact B972091
  · exact B972095
  · exact B972099
  · exact B972103
  · exact B972107
  · exact B972111
  · exact B972115
  · exact B972119
  · exact B972123
  · exact B972127
  · exact B972131
  · exact B972135
  · exact B972139
  · exact B972143
  · exact B972147
  · exact B972151
  · exact B972155
  · exact B972159
  · exact B972163
  · exact B972167
  · exact B972171
  · exact B972175
  · exact B972179
  · exact B972183
  · exact B972187
  · exact B972191
  · exact B972195
  · exact B972199
  · exact B972203
  · exact B972207
  · exact B972211
  · exact B972215
  · exact B972219
  · exact B972223
  · exact B972227
  · exact B972231
  · exact B972235
  · exact B972239
  · exact B972243
  · exact B972247
  · exact B972251
  · exact B972255
  · exact B972259
  · exact B972263
  · exact B972267
  · exact B972271
  · exact B972275
  · exact B972279
  · exact B972283
  · exact B972287
  · exact B972291
  · exact B972295
  · exact B972299
  · exact B972303
  · exact B972307
  · exact B972311
  · exact B972315
  · exact B972319
  · exact B972323
  · exact B972327
  · exact B972331
  · exact B972335
  · exact B972339
  · exact B972343
  · exact B972347
  · exact B972351
  · exact B972355
  · exact B972359
  · exact B972363
  · exact B972367
  · exact B972371
  · exact B972375
  · exact B972379
  · exact B972383
  · exact B972387
  · exact B972391
  · exact B972395
  · exact B972399
  · exact B972403
  · exact B972407
  · exact B972411
  · exact B972415
  · exact B972419
  · exact B972423
  · exact B972427
  · exact B972431
  · exact B972435
  · exact B972439
  · exact B972443
  · exact B972447
  · exact B972451
  · exact B972455
  · exact B972459
  · exact B972463
  · exact B972467
  · exact B972471
  · exact B972475
  · exact B972479
  · exact B972483
  · exact B972487
  · exact B972491
  · exact B972495
  · exact B972499
  · exact B972503
  · exact B972507
  · exact B972511
  · exact B972515
  · exact B972519
  · exact B972523
  · exact B972527
  · exact B972531
  · exact B972535
  · exact B972539
  · exact B972543
  · exact B972547
  · exact B972551
  · exact B972555
  · exact B972559
  · exact B972563
  · exact B972567
  · exact B972571
  · exact B972575
  · exact B972579
  · exact B972583
  · exact B972587
  · exact B972591

theorem solution (m : ℕ) (hlo : 968591 ≤ m) (hhi : m ≤ 972591) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 242147 ≤ j := by omega
    have hj2 : j ≤ 243147 := by omega
    have hb : Blo 968591 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 242847 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
