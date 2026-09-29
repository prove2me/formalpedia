-- Prove2me | solution 1 for syracuse_descends_range_1166400_1168400
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:10:18.603026+00:00
-- url     : https://prove2.me/submissions/5d7fa0d4-43c0-471e-9417-3715c3b1d527

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


theorem B4431941 : Blo 1166400 4431941 := bbase (se 4 (by rfl) ⟨415494, by rfl⟩ : syracuseStep 4431941 = 830989) (by norm_num)
theorem B2957381 : Blo 1166400 2957381 := bbase (se 4 (by rfl) ⟨277254, by rfl⟩ : syracuseStep 2957381 = 554509) (by norm_num)
theorem B6651989 : Blo 1166400 6651989 := bbase (se 8 (by rfl) ⟨38976, by rfl⟩ : syracuseStep 6651989 = 77953) (by norm_num)
theorem B4432229 : Blo 1166400 4432229 := bbase (se 4 (by rfl) ⟨415521, by rfl⟩ : syracuseStep 4432229 = 831043) (by norm_num)
theorem B3547525 : Blo 1166400 3547525 := bbase (se 4 (by rfl) ⟨332580, by rfl⟩ : syracuseStep 3547525 = 665161) (by norm_num)
theorem B1663373 : Blo 1166400 1663373 := bbase (se 3 (by rfl) ⟨311882, by rfl⟩ : syracuseStep 1663373 = 623765) (by norm_num)
theorem B2245013 : Blo 1166400 2245013 := bbase (se 6 (by rfl) ⟨52617, by rfl⟩ : syracuseStep 2245013 = 105235) (by norm_num)
theorem B3940757 : Blo 1166400 3940757 := bbase (se 6 (by rfl) ⟨92361, by rfl⟩ : syracuseStep 3940757 = 184723) (by norm_num)
theorem B1663453 : Blo 1166400 1663453 := bbase (se 3 (by rfl) ⟨311897, by rfl⟩ : syracuseStep 1663453 = 623795) (by norm_num)
theorem B1663573 : Blo 1166400 1663573 := bbase (se 8 (by rfl) ⟨9747, by rfl⟩ : syracuseStep 1663573 = 19495) (by norm_num)
theorem B2663045 : Blo 1166400 2663045 := bbase (se 4 (by rfl) ⟨249660, by rfl⟩ : syracuseStep 2663045 = 499321) (by norm_num)
theorem B1245937 : Blo 1166400 1245937 := bbase (se 2 (by rfl) ⟨467226, by rfl⟩ : syracuseStep 1245937 = 934453) (by norm_num)
theorem B3941189 : Blo 1166400 3941189 := bbase (se 4 (by rfl) ⟨369486, by rfl⟩ : syracuseStep 3941189 = 738973) (by norm_num)
theorem B2802637 : Blo 1166400 2802637 := bbase (se 3 (by rfl) ⟨525494, by rfl⟩ : syracuseStep 2802637 = 1050989) (by norm_num)
theorem B1401833 : Blo 1166400 1401833 := bbase (se 2 (by rfl) ⟨525687, by rfl⟩ : syracuseStep 1401833 = 1051375) (by norm_num)
theorem B1246313 : Blo 1166400 1246313 := bbase (se 2 (by rfl) ⟨467367, by rfl⟩ : syracuseStep 1246313 = 934735) (by norm_num)
theorem B4801669 : Blo 1166400 4801669 := bbase (se 4 (by rfl) ⟨450156, by rfl⟩ : syracuseStep 4801669 = 900313) (by norm_num)
theorem B2802829 : Blo 1166400 2802829 := bbase (se 3 (by rfl) ⟨525530, by rfl⟩ : syracuseStep 2802829 = 1051061) (by norm_num)
theorem B1246385 : Blo 1166400 1246385 := bbase (se 2 (by rfl) ⟨467394, by rfl⟩ : syracuseStep 1246385 = 934789) (by norm_num)
theorem B2802869 : Blo 1166400 2802869 := bbase (se 5 (by rfl) ⟨131384, by rfl⟩ : syracuseStep 2802869 = 262769) (by norm_num)
theorem B1868989 : Blo 1166400 1868989 := bbase (se 3 (by rfl) ⟨350435, by rfl⟩ : syracuseStep 1868989 = 700871) (by norm_num)
theorem B5907653 : Blo 1166400 5907653 := bbase (se 4 (by rfl) ⟨553842, by rfl⟩ : syracuseStep 5907653 = 1107685) (by norm_num)
theorem B1262837 : Blo 1166400 1262837 := bbase (se 5 (by rfl) ⟨59195, by rfl⟩ : syracuseStep 1262837 = 118391) (by norm_num)
theorem B3941621 : Blo 1166400 3941621 := bbase (se 5 (by rfl) ⟨184763, by rfl⟩ : syracuseStep 3941621 = 369527) (by norm_num)
theorem B4736261 : Blo 1166400 4736261 := bbase (se 4 (by rfl) ⟨444024, by rfl⟩ : syracuseStep 4736261 = 888049) (by norm_num)
theorem B3368213 : Blo 1166400 3368213 := bbase (se 6 (by rfl) ⟨78942, by rfl⟩ : syracuseStep 3368213 = 157885) (by norm_num)
theorem B5612885 : Blo 1166400 5612885 := bbase (se 12 (by rfl) ⟨2055, by rfl⟩ : syracuseStep 5612885 = 4111) (by norm_num)
theorem B1246573 : Blo 1166400 1246573 := bbase (se 3 (by rfl) ⟨233732, by rfl⟩ : syracuseStep 1246573 = 467465) (by norm_num)
theorem B2491813 : Blo 1166400 2491813 := bbase (se 4 (by rfl) ⟨233607, by rfl⟩ : syracuseStep 2491813 = 467215) (by norm_num)
theorem B1869245 : Blo 1166400 1869245 := bbase (se 3 (by rfl) ⟨350483, by rfl⟩ : syracuseStep 1869245 = 700967) (by norm_num)
theorem B3737029 : Blo 1166400 3737029 := bbase (se 4 (by rfl) ⟨350346, by rfl⟩ : syracuseStep 3737029 = 700693) (by norm_num)
theorem B1402309 : Blo 1166400 1402309 := bbase (se 4 (by rfl) ⟨131466, by rfl⟩ : syracuseStep 1402309 = 262933) (by norm_num)
theorem B1312213 : Blo 1166400 1312213 := bbase (se 7 (by rfl) ⟨15377, by rfl⟩ : syracuseStep 1312213 = 30755) (by norm_num)
theorem B2803157 : Blo 1166400 2803157 := bbase (se 7 (by rfl) ⟨32849, by rfl⟩ : syracuseStep 2803157 = 65699) (by norm_num)
theorem B1402337 : Blo 1166400 1402337 := bbase (se 2 (by rfl) ⟨525876, by rfl⟩ : syracuseStep 1402337 = 1051753) (by norm_num)
theorem B5400037 : Blo 1166400 5400037 := bbase (se 4 (by rfl) ⟨506253, by rfl⟩ : syracuseStep 5400037 = 1012507) (by norm_num)
theorem B1312249 : Blo 1166400 1312249 := bbase (se 2 (by rfl) ⟨492093, by rfl⟩ : syracuseStep 1312249 = 984187) (by norm_num)
theorem B4433413 : Blo 1166400 4433413 := bbase (se 4 (by rfl) ⟨415632, by rfl⟩ : syracuseStep 4433413 = 831265) (by norm_num)
theorem B1312285 : Blo 1166400 1312285 := bbase (se 3 (by rfl) ⟨246053, by rfl⟩ : syracuseStep 1312285 = 492107) (by norm_num)
theorem B1246757 : Blo 1166400 1246757 := bbase (se 4 (by rfl) ⟨116883, by rfl⟩ : syracuseStep 1246757 = 233767) (by norm_num)
theorem B1312321 : Blo 1166400 1312321 := bbase (se 2 (by rfl) ⟨492120, by rfl⟩ : syracuseStep 1312321 = 984241) (by norm_num)
theorem B2246213 : Blo 1166400 2246213 := bbase (se 4 (by rfl) ⟨210582, by rfl⟩ : syracuseStep 2246213 = 421165) (by norm_num)
theorem B1312357 : Blo 1166400 1312357 := bbase (se 4 (by rfl) ⟨123033, by rfl⟩ : syracuseStep 1312357 = 246067) (by norm_num)
theorem B1893989 : Blo 1166400 1893989 := bbase (se 4 (by rfl) ⟨177561, by rfl⟩ : syracuseStep 1893989 = 355123) (by norm_num)
theorem B1869437 : Blo 1166400 1869437 := bbase (se 3 (by rfl) ⟨350519, by rfl⟩ : syracuseStep 1869437 = 701039) (by norm_num)
theorem B1312393 : Blo 1166400 1312393 := bbase (se 2 (by rfl) ⟨492147, by rfl⟩ : syracuseStep 1312393 = 984295) (by norm_num)
theorem B1476245 : Blo 1166400 1476245 := bbase (se 6 (by rfl) ⟨34599, by rfl⟩ : syracuseStep 1476245 = 69199) (by norm_num)
theorem B1402525 : Blo 1166400 1402525 := bbase (se 3 (by rfl) ⟨262973, by rfl⟩ : syracuseStep 1402525 = 525947) (by norm_num)
theorem B3942053 : Blo 1166400 3942053 := bbase (se 4 (by rfl) ⟨369567, by rfl⟩ : syracuseStep 3942053 = 739135) (by norm_num)
theorem B1312429 : Blo 1166400 1312429 := bbase (se 3 (by rfl) ⟨246080, by rfl⟩ : syracuseStep 1312429 = 492161) (by norm_num)
theorem B1476301 : Blo 1166400 1476301 := bbase (se 3 (by rfl) ⟨276806, by rfl⟩ : syracuseStep 1476301 = 553613) (by norm_num)
theorem B1312465 : Blo 1166400 1312465 := bbase (se 2 (by rfl) ⟨492174, by rfl⟩ : syracuseStep 1312465 = 984349) (by norm_num)
theorem B1312501 : Blo 1166400 1312501 := bbase (se 5 (by rfl) ⟨61523, by rfl⟩ : syracuseStep 1312501 = 123047) (by norm_num)
theorem B1402645 : Blo 1166400 1402645 := bbase (se 6 (by rfl) ⟨32874, by rfl⟩ : syracuseStep 1402645 = 65749) (by norm_num)
theorem B1312537 : Blo 1166400 1312537 := bbase (se 2 (by rfl) ⟨492201, by rfl⟩ : syracuseStep 1312537 = 984403) (by norm_num)
theorem B1476397 : Blo 1166400 1476397 := bbase (se 3 (by rfl) ⟨276824, by rfl⟩ : syracuseStep 1476397 = 553649) (by norm_num)
theorem B4433717 : Blo 1166400 4433717 := bbase (se 5 (by rfl) ⟨207830, by rfl⟩ : syracuseStep 4433717 = 415661) (by norm_num)
theorem B1312573 : Blo 1166400 1312573 := bbase (se 3 (by rfl) ⟨246107, by rfl⟩ : syracuseStep 1312573 = 492215) (by norm_num)
theorem B1312609 : Blo 1166400 1312609 := bbase (se 2 (by rfl) ⟨492228, by rfl⟩ : syracuseStep 1312609 = 984457) (by norm_num)
theorem B1312645 : Blo 1166400 1312645 := bbase (se 4 (by rfl) ⟨123060, by rfl⟩ : syracuseStep 1312645 = 246121) (by norm_num)
theorem B2492309 : Blo 1166400 2492309 := bbase (se 6 (by rfl) ⟨58413, by rfl⟩ : syracuseStep 2492309 = 116827) (by norm_num)
theorem B1312681 : Blo 1166400 1312681 := bbase (se 2 (by rfl) ⟨492255, by rfl⟩ : syracuseStep 1312681 = 984511) (by norm_num)
theorem B1312717 : Blo 1166400 1312717 := bbase (se 3 (by rfl) ⟨246134, by rfl⟩ : syracuseStep 1312717 = 492269) (by norm_num)
theorem B1476569 : Blo 1166400 1476569 := bbase (se 2 (by rfl) ⟨553713, by rfl⟩ : syracuseStep 1476569 = 1107427) (by norm_num)
theorem B1312753 : Blo 1166400 1312753 := bbase (se 2 (by rfl) ⟨492282, by rfl⟩ : syracuseStep 1312753 = 984565) (by norm_num)
theorem B1476625 : Blo 1166400 1476625 := bbase (se 2 (by rfl) ⟨553734, by rfl⟩ : syracuseStep 1476625 = 1107469) (by norm_num)
theorem B1312789 : Blo 1166400 1312789 := bbase (se 6 (by rfl) ⟨30768, by rfl⟩ : syracuseStep 1312789 = 61537) (by norm_num)
theorem B1312825 : Blo 1166400 1312825 := bbase (se 2 (by rfl) ⟨492309, by rfl⟩ : syracuseStep 1312825 = 984619) (by norm_num)
theorem B3942485 : Blo 1166400 3942485 := bbase (se 8 (by rfl) ⟨23100, by rfl⟩ : syracuseStep 3942485 = 46201) (by norm_num)
theorem B1312861 : Blo 1166400 1312861 := bbase (se 3 (by rfl) ⟨246161, by rfl⟩ : syracuseStep 1312861 = 492323) (by norm_num)
theorem B1476721 : Blo 1166400 1476721 := bbase (se 2 (by rfl) ⟨553770, by rfl⟩ : syracuseStep 1476721 = 1107541) (by norm_num)
theorem B1312897 : Blo 1166400 1312897 := bbase (se 2 (by rfl) ⟨492336, by rfl⟩ : syracuseStep 1312897 = 984673) (by norm_num)
theorem B1312933 : Blo 1166400 1312933 := bbase (se 4 (by rfl) ⟨123087, by rfl⟩ : syracuseStep 1312933 = 246175) (by norm_num)
theorem B1312969 : Blo 1166400 1312969 := bbase (se 2 (by rfl) ⟨492363, by rfl⟩ : syracuseStep 1312969 = 984727) (by norm_num)
theorem B1313005 : Blo 1166400 1313005 := bbase (se 3 (by rfl) ⟨246188, by rfl⟩ : syracuseStep 1313005 = 492377) (by norm_num)
theorem B1313041 : Blo 1166400 1313041 := bbase (se 2 (by rfl) ⟨492390, by rfl⟩ : syracuseStep 1313041 = 984781) (by norm_num)
theorem B1247509 : Blo 1166400 1247509 := bbase (se 6 (by rfl) ⟨29238, by rfl⟩ : syracuseStep 1247509 = 58477) (by norm_num)
theorem B1476893 : Blo 1166400 1476893 := bbase (se 3 (by rfl) ⟨276917, by rfl⟩ : syracuseStep 1476893 = 553835) (by norm_num)
theorem B1968421 : Blo 1166400 1968421 := bbase (se 4 (by rfl) ⟨184539, by rfl⟩ : syracuseStep 1968421 = 369079) (by norm_num)
theorem B1313077 : Blo 1166400 1313077 := bbase (se 5 (by rfl) ⟨61550, by rfl⟩ : syracuseStep 1313077 = 123101) (by norm_num)
theorem B1476949 : Blo 1166400 1476949 := bbase (se 10 (by rfl) ⟨2163, by rfl⟩ : syracuseStep 1476949 = 4327) (by norm_num)
theorem B1313113 : Blo 1166400 1313113 := bbase (se 2 (by rfl) ⟨492417, by rfl⟩ : syracuseStep 1313113 = 984835) (by norm_num)
theorem B1247581 : Blo 1166400 1247581 := bbase (se 3 (by rfl) ⟨233921, by rfl⟩ : syracuseStep 1247581 = 467843) (by norm_num)
theorem B11225461 : Blo 1166400 11225461 := bbase (se 5 (by rfl) ⟨526193, by rfl⟩ : syracuseStep 11225461 = 1052387) (by norm_num)
theorem B1968509 : Blo 1166400 1968509 := bbase (se 3 (by rfl) ⟨369095, by rfl⟩ : syracuseStep 1968509 = 738191) (by norm_num)
theorem B1313149 : Blo 1166400 1313149 := bbase (se 3 (by rfl) ⟨246215, by rfl⟩ : syracuseStep 1313149 = 492431) (by norm_num)
theorem B1313185 : Blo 1166400 1313185 := bbase (se 2 (by rfl) ⟨492444, by rfl⟩ : syracuseStep 1313185 = 984889) (by norm_num)
theorem B1477045 : Blo 1166400 1477045 := bbase (se 5 (by rfl) ⟨69236, by rfl⟩ : syracuseStep 1477045 = 138473) (by norm_num)
theorem B1313221 : Blo 1166400 1313221 := bbase (se 4 (by rfl) ⟨123114, by rfl⟩ : syracuseStep 1313221 = 246229) (by norm_num)
theorem B5908949 : Blo 1166400 5908949 := bbase (se 7 (by rfl) ⟨69245, by rfl⟩ : syracuseStep 5908949 = 138491) (by norm_num)
theorem B4491749 : Blo 1166400 4491749 := bbase (se 4 (by rfl) ⟨421101, by rfl⟩ : syracuseStep 4491749 = 842203) (by norm_num)
theorem B1313257 : Blo 1166400 1313257 := bbase (se 2 (by rfl) ⟨492471, by rfl⟩ : syracuseStep 1313257 = 984943) (by norm_num)
theorem B1968637 : Blo 1166400 1968637 := bbase (se 3 (by rfl) ⟨369119, by rfl⟩ : syracuseStep 1968637 = 738239) (by norm_num)
theorem B3942917 : Blo 1166400 3942917 := bbase (se 4 (by rfl) ⟨369648, by rfl⟩ : syracuseStep 3942917 = 739297) (by norm_num)
theorem B1313293 : Blo 1166400 1313293 := bbase (se 3 (by rfl) ⟨246242, by rfl⟩ : syracuseStep 1313293 = 492485) (by norm_num)
theorem B1870373 : Blo 1166400 1870373 := bbase (se 4 (by rfl) ⟨175347, by rfl⟩ : syracuseStep 1870373 = 350695) (by norm_num)
theorem B1313329 : Blo 1166400 1313329 := bbase (se 2 (by rfl) ⟨492498, by rfl⟩ : syracuseStep 1313329 = 984997) (by norm_num)
theorem B1968725 : Blo 1166400 1968725 := bbase (se 8 (by rfl) ⟨11535, by rfl⟩ : syracuseStep 1968725 = 23071) (by norm_num)
theorem B1313365 : Blo 1166400 1313365 := bbase (se 8 (by rfl) ⟨7695, by rfl⟩ : syracuseStep 1313365 = 15391) (by norm_num)
theorem B1477217 : Blo 1166400 1477217 := bbase (se 2 (by rfl) ⟨553956, by rfl⟩ : syracuseStep 1477217 = 1107913) (by norm_num)
theorem B1313401 : Blo 1166400 1313401 := bbase (se 2 (by rfl) ⟨492525, by rfl⟩ : syracuseStep 1313401 = 985051) (by norm_num)
theorem B1477273 : Blo 1166400 1477273 := bbase (se 2 (by rfl) ⟨553977, by rfl⟩ : syracuseStep 1477273 = 1107955) (by norm_num)
theorem B1313437 : Blo 1166400 1313437 := bbase (se 3 (by rfl) ⟨246269, by rfl⟩ : syracuseStep 1313437 = 492539) (by norm_num)
theorem B1313473 : Blo 1166400 1313473 := bbase (se 2 (by rfl) ⟨492552, by rfl⟩ : syracuseStep 1313473 = 985105) (by norm_num)
theorem B5606101 : Blo 1166400 5606101 := bbase (se 7 (by rfl) ⟨65696, by rfl⟩ : syracuseStep 5606101 = 131393) (by norm_num)
theorem B1968853 : Blo 1166400 1968853 := bbase (se 7 (by rfl) ⟨23072, by rfl⟩ : syracuseStep 1968853 = 46145) (by norm_num)
theorem B1313509 : Blo 1166400 1313509 := bbase (se 4 (by rfl) ⟨123141, by rfl⟩ : syracuseStep 1313509 = 246283) (by norm_num)
theorem B2493173 : Blo 1166400 2493173 := bbase (se 5 (by rfl) ⟨116867, by rfl⟩ : syracuseStep 2493173 = 233735) (by norm_num)
theorem B1477369 : Blo 1166400 1477369 := bbase (se 2 (by rfl) ⟨554013, by rfl⟩ : syracuseStep 1477369 = 1108027) (by norm_num)
theorem B1313545 : Blo 1166400 1313545 := bbase (se 2 (by rfl) ⟨492579, by rfl⟩ : syracuseStep 1313545 = 985159) (by norm_num)
theorem B1182485 : Blo 1166400 1182485 := bbase (se 6 (by rfl) ⟨27714, by rfl⟩ : syracuseStep 1182485 = 55429) (by norm_num)
theorem B1968941 : Blo 1166400 1968941 := bbase (se 3 (by rfl) ⟨369176, by rfl⟩ : syracuseStep 1968941 = 738353) (by norm_num)
theorem B1313581 : Blo 1166400 1313581 := bbase (se 3 (by rfl) ⟨246296, by rfl⟩ : syracuseStep 1313581 = 492593) (by norm_num)
theorem B1313617 : Blo 1166400 1313617 := bbase (se 2 (by rfl) ⟨492606, by rfl⟩ : syracuseStep 1313617 = 985213) (by norm_num)
theorem B1264465 : Blo 1166400 1264465 := bbase (se 2 (by rfl) ⟨474174, by rfl⟩ : syracuseStep 1264465 = 948349) (by norm_num)
theorem B1313653 : Blo 1166400 1313653 := bbase (se 5 (by rfl) ⟨61577, by rfl⟩ : syracuseStep 1313653 = 123155) (by norm_num)
theorem B4492165 : Blo 1166400 4492165 := bbase (se 4 (by rfl) ⟨421140, by rfl⟩ : syracuseStep 4492165 = 842281) (by norm_num)
theorem B2493317 : Blo 1166400 2493317 := bbase (se 4 (by rfl) ⟨233748, by rfl⟩ : syracuseStep 2493317 = 467497) (by norm_num)
theorem B2845589 : Blo 1166400 2845589 := bbase (se 6 (by rfl) ⟨66693, by rfl⟩ : syracuseStep 2845589 = 133387) (by norm_num)
theorem B1313689 : Blo 1166400 1313689 := bbase (se 2 (by rfl) ⟨492633, by rfl⟩ : syracuseStep 1313689 = 985267) (by norm_num)
theorem B1477541 : Blo 1166400 1477541 := bbase (se 4 (by rfl) ⟨138519, by rfl⟩ : syracuseStep 1477541 = 277039) (by norm_num)
theorem B1870757 : Blo 1166400 1870757 := bbase (se 4 (by rfl) ⟨175383, by rfl⟩ : syracuseStep 1870757 = 350767) (by norm_num)
theorem B1969069 : Blo 1166400 1969069 := bbase (se 3 (by rfl) ⟨369200, by rfl⟩ : syracuseStep 1969069 = 738401) (by norm_num)
theorem B3943349 : Blo 1166400 3943349 := bbase (se 5 (by rfl) ⟨184844, by rfl⟩ : syracuseStep 3943349 = 369689) (by norm_num)
theorem B1313725 : Blo 1166400 1313725 := bbase (se 3 (by rfl) ⟨246323, by rfl⟩ : syracuseStep 1313725 = 492647) (by norm_num)
theorem B2624453 : Blo 1166400 2624453 := bbase (se 4 (by rfl) ⟨246042, by rfl⟩ : syracuseStep 2624453 = 492085) (by norm_num)
theorem B2214877 : Blo 1166400 2214877 := bbase (se 3 (by rfl) ⟨415289, by rfl⟩ : syracuseStep 2214877 = 830579) (by norm_num)
theorem B1477597 : Blo 1166400 1477597 := bbase (se 3 (by rfl) ⟨277049, by rfl⟩ : syracuseStep 1477597 = 554099) (by norm_num)
theorem B1313761 : Blo 1166400 1313761 := bbase (se 2 (by rfl) ⟨492660, by rfl⟩ : syracuseStep 1313761 = 985321) (by norm_num)
theorem B1969157 : Blo 1166400 1969157 := bbase (se 4 (by rfl) ⟨184608, by rfl⟩ : syracuseStep 1969157 = 369217) (by norm_num)
theorem B1313797 : Blo 1166400 1313797 := bbase (se 4 (by rfl) ⟨123168, by rfl⟩ : syracuseStep 1313797 = 246337) (by norm_num)
theorem B2624525 : Blo 1166400 2624525 := bbase (se 3 (by rfl) ⟨492098, by rfl⟩ : syracuseStep 2624525 = 984197) (by norm_num)
theorem B1870885 : Blo 1166400 1870885 := bbase (se 4 (by rfl) ⟨175395, by rfl⟩ : syracuseStep 1870885 = 350791) (by norm_num)
theorem B1313833 : Blo 1166400 1313833 := bbase (se 2 (by rfl) ⟨492687, by rfl⟩ : syracuseStep 1313833 = 985375) (by norm_num)
theorem B1477693 : Blo 1166400 1477693 := bbase (se 3 (by rfl) ⟨277067, by rfl⟩ : syracuseStep 1477693 = 554135) (by norm_num)
theorem B1313869 : Blo 1166400 1313869 := bbase (se 3 (by rfl) ⟨246350, by rfl⟩ : syracuseStep 1313869 = 492701) (by norm_num)
theorem B2624597 : Blo 1166400 2624597 := bbase (se 8 (by rfl) ⟨15378, by rfl⟩ : syracuseStep 2624597 = 30757) (by norm_num)
theorem B1182817 : Blo 1166400 1182817 := bbase (se 2 (by rfl) ⟨443556, by rfl⟩ : syracuseStep 1182817 = 887113) (by norm_num)
theorem B2215021 : Blo 1166400 2215021 := bbase (se 3 (by rfl) ⟨415316, by rfl⟩ : syracuseStep 2215021 = 830633) (by norm_num)
theorem B1313905 : Blo 1166400 1313905 := bbase (se 2 (by rfl) ⟨492714, by rfl⟩ : syracuseStep 1313905 = 985429) (by norm_num)
theorem B1969285 : Blo 1166400 1969285 := bbase (se 4 (by rfl) ⟨184620, by rfl⟩ : syracuseStep 1969285 = 369241) (by norm_num)
theorem B1313941 : Blo 1166400 1313941 := bbase (se 6 (by rfl) ⟨30795, by rfl⟩ : syracuseStep 1313941 = 61591) (by norm_num)
theorem B2624669 : Blo 1166400 2624669 := bbase (se 3 (by rfl) ⟨492125, by rfl⟩ : syracuseStep 2624669 = 984251) (by norm_num)
theorem B2526365 : Blo 1166400 2526365 := bbase (se 3 (by rfl) ⟨473693, by rfl⟩ : syracuseStep 2526365 = 947387) (by norm_num)
theorem B4730021 : Blo 1166400 4730021 := bbase (se 4 (by rfl) ⟨443439, by rfl⟩ : syracuseStep 4730021 = 886879) (by norm_num)
theorem B3550373 : Blo 1166400 3550373 := bbase (se 4 (by rfl) ⟨332847, by rfl⟩ : syracuseStep 3550373 = 665695) (by norm_num)
theorem B1313977 : Blo 1166400 1313977 := bbase (se 2 (by rfl) ⟨492741, by rfl⟩ : syracuseStep 1313977 = 985483) (by norm_num)
theorem B1969373 : Blo 1166400 1969373 := bbase (se 3 (by rfl) ⟨369257, by rfl⟩ : syracuseStep 1969373 = 738515) (by norm_num)
theorem B1314013 : Blo 1166400 1314013 := bbase (se 3 (by rfl) ⟨246377, by rfl⟩ : syracuseStep 1314013 = 492755) (by norm_num)
theorem B2624741 : Blo 1166400 2624741 := bbase (se 4 (by rfl) ⟨246069, by rfl⟩ : syracuseStep 2624741 = 492139) (by norm_num)
theorem B4984037 : Blo 1166400 4984037 := bbase (se 4 (by rfl) ⟨467253, by rfl⟩ : syracuseStep 4984037 = 934507) (by norm_num)
theorem B1477865 : Blo 1166400 1477865 := bbase (se 2 (by rfl) ⟨554199, by rfl⟩ : syracuseStep 1477865 = 1108399) (by norm_num)
theorem B1314049 : Blo 1166400 1314049 := bbase (se 2 (by rfl) ⟨492768, by rfl⟩ : syracuseStep 1314049 = 985537) (by norm_num)
theorem B2215181 : Blo 1166400 2215181 := bbase (se 3 (by rfl) ⟨415346, by rfl⟩ : syracuseStep 2215181 = 830693) (by norm_num)
theorem B1477921 : Blo 1166400 1477921 := bbase (se 2 (by rfl) ⟨554220, by rfl⟩ : syracuseStep 1477921 = 1108441) (by norm_num)
theorem B1314085 : Blo 1166400 1314085 := bbase (se 4 (by rfl) ⟨123195, by rfl⟩ : syracuseStep 1314085 = 246391) (by norm_num)
theorem B2624813 : Blo 1166400 2624813 := bbase (se 3 (by rfl) ⟨492152, by rfl⟩ : syracuseStep 2624813 = 984305) (by norm_num)
theorem B1314121 : Blo 1166400 1314121 := bbase (se 2 (by rfl) ⟨492795, by rfl⟩ : syracuseStep 1314121 = 985591) (by norm_num)
theorem B1969501 : Blo 1166400 1969501 := bbase (se 3 (by rfl) ⟨369281, by rfl⟩ : syracuseStep 1969501 = 738563) (by norm_num)
theorem B1314157 : Blo 1166400 1314157 := bbase (se 3 (by rfl) ⟨246404, by rfl⟩ : syracuseStep 1314157 = 492809) (by norm_num)
theorem B2624885 : Blo 1166400 2624885 := bbase (se 5 (by rfl) ⟨123041, by rfl⟩ : syracuseStep 2624885 = 246083) (by norm_num)
theorem B1478017 : Blo 1166400 1478017 := bbase (se 2 (by rfl) ⟨554256, by rfl⟩ : syracuseStep 1478017 = 1108513) (by norm_num)
theorem B1314193 : Blo 1166400 1314193 := bbase (se 2 (by rfl) ⟨492822, by rfl⟩ : syracuseStep 1314193 = 985645) (by norm_num)
theorem B2215325 : Blo 1166400 2215325 := bbase (se 3 (by rfl) ⟨415373, by rfl⟩ : syracuseStep 2215325 = 830747) (by norm_num)
theorem B1969589 : Blo 1166400 1969589 := bbase (se 5 (by rfl) ⟨92324, by rfl⟩ : syracuseStep 1969589 = 184649) (by norm_num)
theorem B4206005 : Blo 1166400 4206005 := bbase (se 5 (by rfl) ⟨197156, by rfl⟩ : syracuseStep 4206005 = 394313) (by norm_num)
theorem B1314229 : Blo 1166400 1314229 := bbase (se 5 (by rfl) ⟨61604, by rfl⟩ : syracuseStep 1314229 = 123209) (by norm_num)
theorem B2624957 : Blo 1166400 2624957 := bbase (se 3 (by rfl) ⟨492179, by rfl⟩ : syracuseStep 2624957 = 984359) (by norm_num)
theorem B1314265 : Blo 1166400 1314265 := bbase (se 2 (by rfl) ⟨492849, by rfl⟩ : syracuseStep 1314265 = 985699) (by norm_num)
theorem B1314301 : Blo 1166400 1314301 := bbase (se 3 (by rfl) ⟨246431, by rfl⟩ : syracuseStep 1314301 = 492863) (by norm_num)
theorem B2625029 : Blo 1166400 2625029 := bbase (se 4 (by rfl) ⟨246096, by rfl⟩ : syracuseStep 2625029 = 492193) (by norm_num)
theorem B2952733 : Blo 1166400 2952733 := bbase (se 3 (by rfl) ⟨553637, by rfl⟩ : syracuseStep 2952733 = 1107275) (by norm_num)
theorem B1314337 : Blo 1166400 1314337 := bbase (se 2 (by rfl) ⟨492876, by rfl⟩ : syracuseStep 1314337 = 985753) (by norm_num)
theorem B1478189 : Blo 1166400 1478189 := bbase (se 3 (by rfl) ⟨277160, by rfl⟩ : syracuseStep 1478189 = 554321) (by norm_num)
theorem B2993717 : Blo 1166400 2993717 := bbase (se 5 (by rfl) ⟨140330, by rfl⟩ : syracuseStep 2993717 = 280661) (by norm_num)
theorem B1969717 : Blo 1166400 1969717 := bbase (se 5 (by rfl) ⟨92330, by rfl⟩ : syracuseStep 1969717 = 184661) (by norm_num)
theorem B1314373 : Blo 1166400 1314373 := bbase (se 4 (by rfl) ⟨123222, by rfl⟩ : syracuseStep 1314373 = 246445) (by norm_num)
theorem B2625101 : Blo 1166400 2625101 := bbase (se 3 (by rfl) ⟨492206, by rfl⟩ : syracuseStep 2625101 = 984413) (by norm_num)
theorem B1478245 : Blo 1166400 1478245 := bbase (se 4 (by rfl) ⟨138585, by rfl⟩ : syracuseStep 1478245 = 277171) (by norm_num)
theorem B1314409 : Blo 1166400 1314409 := bbase (se 2 (by rfl) ⟨492903, by rfl⟩ : syracuseStep 1314409 = 985807) (by norm_num)
theorem B2494061 : Blo 1166400 2494061 := bbase (se 3 (by rfl) ⟨467636, by rfl⟩ : syracuseStep 2494061 = 935273) (by norm_num)
theorem B2952845 : Blo 1166400 2952845 := bbase (se 3 (by rfl) ⟨553658, by rfl⟩ : syracuseStep 2952845 = 1107317) (by norm_num)
theorem B1969805 : Blo 1166400 1969805 := bbase (se 3 (by rfl) ⟨369338, by rfl⟩ : syracuseStep 1969805 = 738677) (by norm_num)
theorem B1314445 : Blo 1166400 1314445 := bbase (se 3 (by rfl) ⟨246458, by rfl⟩ : syracuseStep 1314445 = 492917) (by norm_num)
theorem B2625173 : Blo 1166400 2625173 := bbase (se 6 (by rfl) ⟨61527, by rfl⟩ : syracuseStep 2625173 = 123055) (by norm_num)
theorem B2526869 : Blo 1166400 2526869 := bbase (se 6 (by rfl) ⟨59223, by rfl⟩ : syracuseStep 2526869 = 118447) (by norm_num)
theorem B2215613 : Blo 1166400 2215613 := bbase (se 3 (by rfl) ⟨415427, by rfl⟩ : syracuseStep 2215613 = 830855) (by norm_num)
theorem B1478341 : Blo 1166400 1478341 := bbase (se 4 (by rfl) ⟨138594, by rfl⟩ : syracuseStep 1478341 = 277189) (by norm_num)
theorem B2625245 : Blo 1166400 2625245 := bbase (se 3 (by rfl) ⟨492233, by rfl⟩ : syracuseStep 2625245 = 984467) (by norm_num)
theorem B5910245 : Blo 1166400 5910245 := bbase (se 4 (by rfl) ⟨554085, by rfl⟩ : syracuseStep 5910245 = 1108171) (by norm_num)
theorem B1969933 : Blo 1166400 1969933 := bbase (se 3 (by rfl) ⟨369362, by rfl⟩ : syracuseStep 1969933 = 738725) (by norm_num)
theorem B2625317 : Blo 1166400 2625317 := bbase (se 4 (by rfl) ⟨246123, by rfl⟩ : syracuseStep 2625317 = 492247) (by norm_num)
theorem B2953037 : Blo 1166400 2953037 := bbase (se 3 (by rfl) ⟨553694, by rfl⟩ : syracuseStep 2953037 = 1107389) (by norm_num)
theorem B4206421 : Blo 1166400 4206421 := bbase (se 9 (by rfl) ⟨12323, by rfl⟩ : syracuseStep 4206421 = 24647) (by norm_num)
theorem B2215765 : Blo 1166400 2215765 := bbase (se 9 (by rfl) ⟨6491, by rfl⟩ : syracuseStep 2215765 = 12983) (by norm_num)
theorem B4206437 : Blo 1166400 4206437 := bbase (se 4 (by rfl) ⟨394353, by rfl⟩ : syracuseStep 4206437 = 788707) (by norm_num)
theorem B1970021 : Blo 1166400 1970021 := bbase (se 4 (by rfl) ⟨184689, by rfl⟩ : syracuseStep 1970021 = 369379) (by norm_num)
theorem B2625389 : Blo 1166400 2625389 := bbase (se 3 (by rfl) ⟨492260, by rfl⟩ : syracuseStep 2625389 = 984521) (by norm_num)
theorem B1478513 : Blo 1166400 1478513 := bbase (se 2 (by rfl) ⟨554442, by rfl⟩ : syracuseStep 1478513 = 1108885) (by norm_num)
theorem B4435829 : Blo 1166400 4435829 := bbase (se 5 (by rfl) ⟨207929, by rfl⟩ : syracuseStep 4435829 = 415859) (by norm_num)
theorem B1478569 : Blo 1166400 1478569 := bbase (se 2 (by rfl) ⟨554463, by rfl⟩ : syracuseStep 1478569 = 1108927) (by norm_num)
theorem B7983029 : Blo 1166400 7983029 := bbase (se 5 (by rfl) ⟨374204, by rfl⟩ : syracuseStep 7983029 = 748409) (by norm_num)
theorem B2625461 : Blo 1166400 2625461 := bbase (se 5 (by rfl) ⟨123068, by rfl⟩ : syracuseStep 2625461 = 246137) (by norm_num)
theorem B1970149 : Blo 1166400 1970149 := bbase (se 4 (by rfl) ⟨184701, by rfl⟩ : syracuseStep 1970149 = 369403) (by norm_num)
theorem B2625533 : Blo 1166400 2625533 := bbase (se 3 (by rfl) ⟨492287, by rfl⟩ : syracuseStep 2625533 = 984575) (by norm_num)
theorem B1478665 : Blo 1166400 1478665 := bbase (se 2 (by rfl) ⟨554499, by rfl⟩ : syracuseStep 1478665 = 1108999) (by norm_num)
theorem B9973813 : Blo 1166400 9973813 := bbase (se 5 (by rfl) ⟨467522, by rfl⟩ : syracuseStep 9973813 = 935045) (by norm_num)
theorem B1970237 : Blo 1166400 1970237 := bbase (se 3 (by rfl) ⟨369419, by rfl⟩ : syracuseStep 1970237 = 738839) (by norm_num)
theorem B2625605 : Blo 1166400 2625605 := bbase (se 4 (by rfl) ⟨246150, by rfl⟩ : syracuseStep 2625605 = 492301) (by norm_num)
theorem B4206725 : Blo 1166400 4206725 := bbase (se 4 (by rfl) ⟨394380, by rfl⟩ : syracuseStep 4206725 = 788761) (by norm_num)
theorem B2216069 : Blo 1166400 2216069 := bbase (se 4 (by rfl) ⟨207756, by rfl⟩ : syracuseStep 2216069 = 415513) (by norm_num)
theorem B2625677 : Blo 1166400 2625677 := bbase (se 3 (by rfl) ⟨492314, by rfl⟩ : syracuseStep 2625677 = 984629) (by norm_num)
theorem B4436117 : Blo 1166400 4436117 := bbase (se 6 (by rfl) ⟨103971, by rfl⟩ : syracuseStep 4436117 = 207943) (by norm_num)
theorem B2953381 : Blo 1166400 2953381 := bbase (se 4 (by rfl) ⟨276879, by rfl⟩ : syracuseStep 2953381 = 553759) (by norm_num)
theorem B1970365 : Blo 1166400 1970365 := bbase (se 3 (by rfl) ⟨369443, by rfl⟩ : syracuseStep 1970365 = 738887) (by norm_num)
theorem B2625749 : Blo 1166400 2625749 := bbase (se 7 (by rfl) ⟨30770, by rfl⟩ : syracuseStep 2625749 = 61541) (by norm_num)
theorem B3739861 : Blo 1166400 3739861 := bbase (se 7 (by rfl) ⟨43826, by rfl⟩ : syracuseStep 3739861 = 87653) (by norm_num)
theorem B2953493 : Blo 1166400 2953493 := bbase (se 6 (by rfl) ⟨69222, by rfl⟩ : syracuseStep 2953493 = 138445) (by norm_num)
theorem B3739925 : Blo 1166400 3739925 := bbase (se 6 (by rfl) ⟨87654, by rfl⟩ : syracuseStep 3739925 = 175309) (by norm_num)
theorem B1970453 : Blo 1166400 1970453 := bbase (se 6 (by rfl) ⟨46182, by rfl⟩ : syracuseStep 1970453 = 92365) (by norm_num)
theorem B2625821 : Blo 1166400 2625821 := bbase (se 3 (by rfl) ⟨492341, by rfl⟩ : syracuseStep 2625821 = 984683) (by norm_num)
theorem B2494813 : Blo 1166400 2494813 := bbase (se 3 (by rfl) ⟨467777, by rfl⟩ : syracuseStep 2494813 = 935555) (by norm_num)
theorem B2625893 : Blo 1166400 2625893 := bbase (se 4 (by rfl) ⟨246177, by rfl⟩ : syracuseStep 2625893 = 492355) (by norm_num)
theorem B1970581 : Blo 1166400 1970581 := bbase (se 6 (by rfl) ⟨46185, by rfl⟩ : syracuseStep 1970581 = 92371) (by norm_num)
theorem B1896853 : Blo 1166400 1896853 := bbase (se 6 (by rfl) ⟨44457, by rfl⟩ : syracuseStep 1896853 = 88915) (by norm_num)
theorem B2625965 : Blo 1166400 2625965 := bbase (se 3 (by rfl) ⟨492368, by rfl⟩ : syracuseStep 2625965 = 984737) (by norm_num)
theorem B1995205 : Blo 1166400 1995205 := bbase (se 4 (by rfl) ⟨187050, by rfl⟩ : syracuseStep 1995205 = 374101) (by norm_num)
theorem B4493765 : Blo 1166400 4493765 := bbase (se 4 (by rfl) ⟨421290, by rfl⟩ : syracuseStep 4493765 = 842581) (by norm_num)
theorem B2953685 : Blo 1166400 2953685 := bbase (se 7 (by rfl) ⟨34613, by rfl⟩ : syracuseStep 2953685 = 69227) (by norm_num)
theorem B1970669 : Blo 1166400 1970669 := bbase (se 3 (by rfl) ⟨369500, by rfl⟩ : syracuseStep 1970669 = 739001) (by norm_num)
theorem B2494957 : Blo 1166400 2494957 := bbase (se 3 (by rfl) ⟨467804, by rfl⟩ : syracuseStep 2494957 = 935609) (by norm_num)
theorem B2626037 : Blo 1166400 2626037 := bbase (se 5 (by rfl) ⟨123095, by rfl⟩ : syracuseStep 2626037 = 246191) (by norm_num)
theorem B2626109 : Blo 1166400 2626109 := bbase (se 3 (by rfl) ⟨492395, by rfl⟩ : syracuseStep 2626109 = 984791) (by norm_num)
theorem B1749605 : Blo 1166400 1749605 := bbase (se 4 (by rfl) ⟨164025, by rfl⟩ : syracuseStep 1749605 = 328051) (by norm_num)
theorem B3936869 : Blo 1166400 3936869 := bbase (se 4 (by rfl) ⟨369081, by rfl⟩ : syracuseStep 3936869 = 738163) (by norm_num)
theorem B1970797 : Blo 1166400 1970797 := bbase (se 3 (by rfl) ⟨369524, by rfl⟩ : syracuseStep 1970797 = 739049) (by norm_num)
theorem B1749629 : Blo 1166400 1749629 := bbase (se 3 (by rfl) ⟨328055, by rfl⟩ : syracuseStep 1749629 = 656111) (by norm_num)
theorem B2626181 : Blo 1166400 2626181 := bbase (se 4 (by rfl) ⟨246204, by rfl⟩ : syracuseStep 2626181 = 492409) (by norm_num)
theorem B1749653 : Blo 1166400 1749653 := bbase (se 6 (by rfl) ⟨41007, by rfl⟩ : syracuseStep 1749653 = 82015) (by norm_num)
theorem B3551893 : Blo 1166400 3551893 := bbase (se 6 (by rfl) ⟨83247, by rfl⟩ : syracuseStep 3551893 = 166495) (by norm_num)
theorem B1749677 : Blo 1166400 1749677 := bbase (se 3 (by rfl) ⟨328064, by rfl⟩ : syracuseStep 1749677 = 656129) (by norm_num)
theorem B1749701 : Blo 1166400 1749701 := bbase (se 4 (by rfl) ⟨164034, by rfl⟩ : syracuseStep 1749701 = 328069) (by norm_num)
theorem B1970885 : Blo 1166400 1970885 := bbase (se 4 (by rfl) ⟨184770, by rfl⟩ : syracuseStep 1970885 = 369541) (by norm_num)
theorem B2626253 : Blo 1166400 2626253 := bbase (se 3 (by rfl) ⟨492422, by rfl⟩ : syracuseStep 2626253 = 984845) (by norm_num)
theorem B8418005 : Blo 1166400 8418005 := bbase (se 7 (by rfl) ⟨98648, by rfl⟩ : syracuseStep 8418005 = 197297) (by norm_num)
theorem B1749725 : Blo 1166400 1749725 := bbase (se 3 (by rfl) ⟨328073, by rfl⟩ : syracuseStep 1749725 = 656147) (by norm_num)
theorem B1749749 : Blo 1166400 1749749 := bbase (se 5 (by rfl) ⟨82019, by rfl⟩ : syracuseStep 1749749 = 164039) (by norm_num)
theorem B1348361 : Blo 1166400 1348361 := bbase (se 2 (by rfl) ⟨505635, by rfl⟩ : syracuseStep 1348361 = 1011271) (by norm_num)
theorem B1749773 : Blo 1166400 1749773 := bbase (se 3 (by rfl) ⟨328082, by rfl⟩ : syracuseStep 1749773 = 656165) (by norm_num)
theorem B2626325 : Blo 1166400 2626325 := bbase (se 6 (by rfl) ⟨61554, by rfl⟩ : syracuseStep 2626325 = 123109) (by norm_num)
theorem B1332001 : Blo 1166400 1332001 := bbase (se 2 (by rfl) ⟨499500, by rfl⟩ : syracuseStep 1332001 = 999001) (by norm_num)
theorem B1749797 : Blo 1166400 1749797 := bbase (se 4 (by rfl) ⟨164043, by rfl⟩ : syracuseStep 1749797 = 328087) (by norm_num)
theorem B2954029 : Blo 1166400 2954029 := bbase (se 3 (by rfl) ⟨553880, by rfl⟩ : syracuseStep 2954029 = 1107761) (by norm_num)
theorem B10654517 : Blo 1166400 10654517 := bbase (se 5 (by rfl) ⟨499430, by rfl⟩ : syracuseStep 10654517 = 998861) (by norm_num)
theorem B1749821 : Blo 1166400 1749821 := bbase (se 3 (by rfl) ⟨328091, by rfl⟩ : syracuseStep 1749821 = 656183) (by norm_num)
theorem B1971013 : Blo 1166400 1971013 := bbase (se 4 (by rfl) ⟨184782, by rfl⟩ : syracuseStep 1971013 = 369565) (by norm_num)
theorem B1749845 : Blo 1166400 1749845 := bbase (se 9 (by rfl) ⟨5126, by rfl⟩ : syracuseStep 1749845 = 10253) (by norm_num)
theorem B2626397 : Blo 1166400 2626397 := bbase (se 3 (by rfl) ⟨492449, by rfl⟩ : syracuseStep 2626397 = 984899) (by norm_num)
theorem B2495333 : Blo 1166400 2495333 := bbase (se 4 (by rfl) ⟨233937, by rfl⟩ : syracuseStep 2495333 = 467875) (by norm_num)
theorem B1749869 : Blo 1166400 1749869 := bbase (se 3 (by rfl) ⟨328100, by rfl⟩ : syracuseStep 1749869 = 656201) (by norm_num)
theorem B2216821 : Blo 1166400 2216821 := bbase (se 5 (by rfl) ⟨103913, by rfl⟩ : syracuseStep 2216821 = 207827) (by norm_num)
theorem B1749893 : Blo 1166400 1749893 := bbase (se 4 (by rfl) ⟨164052, by rfl⟩ : syracuseStep 1749893 = 328105) (by norm_num)
theorem B7484309 : Blo 1166400 7484309 := bbase (se 6 (by rfl) ⟨175413, by rfl⟩ : syracuseStep 7484309 = 350827) (by norm_num)
theorem B1749917 : Blo 1166400 1749917 := bbase (se 3 (by rfl) ⟨328109, by rfl⟩ : syracuseStep 1749917 = 656219) (by norm_num)
theorem B2954141 : Blo 1166400 2954141 := bbase (se 3 (by rfl) ⟨553901, by rfl⟩ : syracuseStep 2954141 = 1107803) (by norm_num)
theorem B1971101 : Blo 1166400 1971101 := bbase (se 3 (by rfl) ⟨369581, by rfl⟩ : syracuseStep 1971101 = 739163) (by norm_num)
theorem B2626469 : Blo 1166400 2626469 := bbase (se 4 (by rfl) ⟨246231, by rfl⟩ : syracuseStep 2626469 = 492463) (by norm_num)
theorem B1749941 : Blo 1166400 1749941 := bbase (se 5 (by rfl) ⟨82028, by rfl⟩ : syracuseStep 1749941 = 164057) (by norm_num)
theorem B1749965 : Blo 1166400 1749965 := bbase (se 3 (by rfl) ⟨328118, by rfl⟩ : syracuseStep 1749965 = 656237) (by norm_num)
theorem B1774541 : Blo 1166400 1774541 := bbase (se 3 (by rfl) ⟨332726, by rfl⟩ : syracuseStep 1774541 = 665453) (by norm_num)
theorem B4985813 : Blo 1166400 4985813 := bbase (se 7 (by rfl) ⟨58427, by rfl⟩ : syracuseStep 4985813 = 116855) (by norm_num)
theorem B2806741 : Blo 1166400 2806741 := bbase (se 7 (by rfl) ⟨32891, by rfl⟩ : syracuseStep 2806741 = 65783) (by norm_num)
theorem B1332193 : Blo 1166400 1332193 := bbase (se 2 (by rfl) ⟨499572, by rfl⟩ : syracuseStep 1332193 = 999145) (by norm_num)
theorem B1749989 : Blo 1166400 1749989 := bbase (se 4 (by rfl) ⟨164061, by rfl⟩ : syracuseStep 1749989 = 328123) (by norm_num)
theorem B2626541 : Blo 1166400 2626541 := bbase (se 3 (by rfl) ⟨492476, by rfl⟩ : syracuseStep 2626541 = 984953) (by norm_num)
theorem B5911541 : Blo 1166400 5911541 := bbase (se 5 (by rfl) ⟨277103, by rfl⟩ : syracuseStep 5911541 = 554207) (by norm_num)
theorem B1750013 : Blo 1166400 1750013 := bbase (se 3 (by rfl) ⟨328127, by rfl⟩ : syracuseStep 1750013 = 656255) (by norm_num)
theorem B2216965 : Blo 1166400 2216965 := bbase (se 4 (by rfl) ⟨207840, by rfl⟩ : syracuseStep 2216965 = 415681) (by norm_num)
theorem B3937301 : Blo 1166400 3937301 := bbase (se 6 (by rfl) ⟨92280, by rfl⟩ : syracuseStep 3937301 = 184561) (by norm_num)
theorem B1750037 : Blo 1166400 1750037 := bbase (se 6 (by rfl) ⟨41016, by rfl⟩ : syracuseStep 1750037 = 82033) (by norm_num)
theorem B1971229 : Blo 1166400 1971229 := bbase (se 3 (by rfl) ⟨369605, by rfl⟩ : syracuseStep 1971229 = 739211) (by norm_num)
theorem B1750061 : Blo 1166400 1750061 := bbase (se 3 (by rfl) ⟨328136, by rfl⟩ : syracuseStep 1750061 = 656273) (by norm_num)
theorem B2626613 : Blo 1166400 2626613 := bbase (se 5 (by rfl) ⟨123122, by rfl⟩ : syracuseStep 2626613 = 246245) (by norm_num)
theorem B1750085 : Blo 1166400 1750085 := bbase (se 4 (by rfl) ⟨164070, by rfl⟩ : syracuseStep 1750085 = 328141) (by norm_num)
theorem B1750109 : Blo 1166400 1750109 := bbase (se 3 (by rfl) ⟨328145, by rfl⟩ : syracuseStep 1750109 = 656291) (by norm_num)
theorem B2954333 : Blo 1166400 2954333 := bbase (se 3 (by rfl) ⟨553937, by rfl⟩ : syracuseStep 2954333 = 1107875) (by norm_num)
theorem B1750133 : Blo 1166400 1750133 := bbase (se 5 (by rfl) ⟨82037, by rfl⟩ : syracuseStep 1750133 = 164075) (by norm_num)
theorem B1971317 : Blo 1166400 1971317 := bbase (se 5 (by rfl) ⟨92405, by rfl⟩ : syracuseStep 1971317 = 184811) (by norm_num)
theorem B2626685 : Blo 1166400 2626685 := bbase (se 3 (by rfl) ⟨492503, by rfl⟩ : syracuseStep 2626685 = 985007) (by norm_num)
theorem B1750157 : Blo 1166400 1750157 := bbase (se 3 (by rfl) ⟨328154, by rfl⟩ : syracuseStep 1750157 = 656309) (by norm_num)
theorem B8869013 : Blo 1166400 8869013 := bbase (se 6 (by rfl) ⟨207867, by rfl⟩ : syracuseStep 8869013 = 415735) (by norm_num)
theorem B1750181 : Blo 1166400 1750181 := bbase (se 4 (by rfl) ⟨164079, by rfl⟩ : syracuseStep 1750181 = 328159) (by norm_num)
theorem B3323045 : Blo 1166400 3323045 := bbase (se 4 (by rfl) ⟨311535, by rfl⟩ : syracuseStep 3323045 = 623071) (by norm_num)
theorem B2217125 : Blo 1166400 2217125 := bbase (se 4 (by rfl) ⟨207855, by rfl⟩ : syracuseStep 2217125 = 415711) (by norm_num)
theorem B1750205 : Blo 1166400 1750205 := bbase (se 3 (by rfl) ⟨328163, by rfl⟩ : syracuseStep 1750205 = 656327) (by norm_num)
theorem B2626757 : Blo 1166400 2626757 := bbase (se 4 (by rfl) ⟨246258, by rfl⟩ : syracuseStep 2626757 = 492517) (by norm_num)
theorem B1750229 : Blo 1166400 1750229 := bbase (se 7 (by rfl) ⟨20510, by rfl⟩ : syracuseStep 1750229 = 41021) (by norm_num)
theorem B1750253 : Blo 1166400 1750253 := bbase (se 3 (by rfl) ⟨328172, by rfl⟩ : syracuseStep 1750253 = 656345) (by norm_num)
theorem B1971445 : Blo 1166400 1971445 := bbase (se 5 (by rfl) ⟨92411, by rfl⟩ : syracuseStep 1971445 = 184823) (by norm_num)
theorem B1750277 : Blo 1166400 1750277 := bbase (se 4 (by rfl) ⟨164088, by rfl⟩ : syracuseStep 1750277 = 328177) (by norm_num)
theorem B2626829 : Blo 1166400 2626829 := bbase (se 3 (by rfl) ⟨492530, by rfl⟩ : syracuseStep 2626829 = 985061) (by norm_num)
theorem B1750301 : Blo 1166400 1750301 := bbase (se 3 (by rfl) ⟨328181, by rfl⟩ : syracuseStep 1750301 = 656363) (by norm_num)
theorem B1750325 : Blo 1166400 1750325 := bbase (se 5 (by rfl) ⟨82046, by rfl⟩ : syracuseStep 1750325 = 164093) (by norm_num)
theorem B2217269 : Blo 1166400 2217269 := bbase (se 5 (by rfl) ⟨103934, by rfl⟩ : syracuseStep 2217269 = 207869) (by norm_num)
theorem B1750349 : Blo 1166400 1750349 := bbase (se 3 (by rfl) ⟨328190, by rfl⟩ : syracuseStep 1750349 = 656381) (by norm_num)
theorem B1971533 : Blo 1166400 1971533 := bbase (se 3 (by rfl) ⟨369662, by rfl⟩ : syracuseStep 1971533 = 739325) (by norm_num)
theorem B2364757 : Blo 1166400 2364757 := bbase (se 14 (by rfl) ⟨216, by rfl⟩ : syracuseStep 2364757 = 433) (by norm_num)
theorem B2626901 : Blo 1166400 2626901 := bbase (se 14 (by rfl) ⟨240, by rfl⟩ : syracuseStep 2626901 = 481) (by norm_num)
theorem B1750373 : Blo 1166400 1750373 := bbase (se 4 (by rfl) ⟨164097, by rfl⟩ : syracuseStep 1750373 = 328195) (by norm_num)
theorem B1750397 : Blo 1166400 1750397 := bbase (se 3 (by rfl) ⟨328199, by rfl⟩ : syracuseStep 1750397 = 656399) (by norm_num)
theorem B1750421 : Blo 1166400 1750421 := bbase (se 6 (by rfl) ⟨41025, by rfl⟩ : syracuseStep 1750421 = 82051) (by norm_num)
theorem B2626973 : Blo 1166400 2626973 := bbase (se 3 (by rfl) ⟨492557, by rfl⟩ : syracuseStep 2626973 = 985115) (by norm_num)
theorem B1750445 : Blo 1166400 1750445 := bbase (se 3 (by rfl) ⟨328208, by rfl⟩ : syracuseStep 1750445 = 656417) (by norm_num)
theorem B2954677 : Blo 1166400 2954677 := bbase (se 5 (by rfl) ⟨138500, by rfl⟩ : syracuseStep 2954677 = 277001) (by norm_num)
theorem B3937733 : Blo 1166400 3937733 := bbase (se 4 (by rfl) ⟨369162, by rfl⟩ : syracuseStep 3937733 = 738325) (by norm_num)
theorem B1750469 : Blo 1166400 1750469 := bbase (se 4 (by rfl) ⟨164106, by rfl⟩ : syracuseStep 1750469 = 328213) (by norm_num)
theorem B1971661 : Blo 1166400 1971661 := bbase (se 3 (by rfl) ⟨369686, by rfl⟩ : syracuseStep 1971661 = 739373) (by norm_num)
theorem B1750493 : Blo 1166400 1750493 := bbase (se 3 (by rfl) ⟨328217, by rfl⟩ : syracuseStep 1750493 = 656435) (by norm_num)
theorem B2627045 : Blo 1166400 2627045 := bbase (se 4 (by rfl) ⟨246285, by rfl⟩ : syracuseStep 2627045 = 492571) (by norm_num)
theorem B1750517 : Blo 1166400 1750517 := bbase (se 5 (by rfl) ⟨82055, by rfl⟩ : syracuseStep 1750517 = 164111) (by norm_num)
theorem B1750541 : Blo 1166400 1750541 := bbase (se 3 (by rfl) ⟨328226, by rfl⟩ : syracuseStep 1750541 = 656453) (by norm_num)
theorem B1750565 : Blo 1166400 1750565 := bbase (se 4 (by rfl) ⟨164115, by rfl⟩ : syracuseStep 1750565 = 328231) (by norm_num)
theorem B2954789 : Blo 1166400 2954789 := bbase (se 4 (by rfl) ⟨277011, by rfl⟩ : syracuseStep 2954789 = 554023) (by norm_num)
theorem B4208165 : Blo 1166400 4208165 := bbase (se 4 (by rfl) ⟨394515, by rfl⟩ : syracuseStep 4208165 = 789031) (by norm_num)
theorem B1578533 : Blo 1166400 1578533 := bbase (se 4 (by rfl) ⟨147987, by rfl⟩ : syracuseStep 1578533 = 295975) (by norm_num)
theorem B2627117 : Blo 1166400 2627117 := bbase (se 3 (by rfl) ⟨492584, by rfl⟩ : syracuseStep 2627117 = 985169) (by norm_num)
theorem B8861237 : Blo 1166400 8861237 := bbase (se 5 (by rfl) ⟨415370, by rfl⟩ : syracuseStep 8861237 = 830741) (by norm_num)
theorem B1750589 : Blo 1166400 1750589 := bbase (se 3 (by rfl) ⟨328235, by rfl⟩ : syracuseStep 1750589 = 656471) (by norm_num)
theorem B40416853 : Blo 1166400 40416853 := bbase (se 8 (by rfl) ⟨236817, by rfl⟩ : syracuseStep 40416853 = 473635) (by norm_num)
theorem B1750613 : Blo 1166400 1750613 := bbase (se 8 (by rfl) ⟨10257, by rfl⟩ : syracuseStep 1750613 = 20515) (by norm_num)
theorem B11982421 : Blo 1166400 11982421 := bbase (se 8 (by rfl) ⟨70209, by rfl⟩ : syracuseStep 11982421 = 140419) (by norm_num)
theorem B13301333 : Blo 1166400 13301333 := bbase (se 8 (by rfl) ⟨77937, by rfl⟩ : syracuseStep 13301333 = 155875) (by norm_num)
theorem B2217557 : Blo 1166400 2217557 := bbase (se 8 (by rfl) ⟨12993, by rfl⟩ : syracuseStep 2217557 = 25987) (by norm_num)
theorem B3995237 : Blo 1166400 3995237 := bbase (se 4 (by rfl) ⟨374553, by rfl⟩ : syracuseStep 3995237 = 749107) (by norm_num)
theorem B1750637 : Blo 1166400 1750637 := bbase (se 3 (by rfl) ⟨328244, by rfl⟩ : syracuseStep 1750637 = 656489) (by norm_num)
theorem B2627189 : Blo 1166400 2627189 := bbase (se 5 (by rfl) ⟨123149, by rfl⟩ : syracuseStep 2627189 = 246299) (by norm_num)
theorem B1750661 : Blo 1166400 1750661 := bbase (se 4 (by rfl) ⟨164124, by rfl⟩ : syracuseStep 1750661 = 328249) (by norm_num)
theorem B1750685 : Blo 1166400 1750685 := bbase (se 3 (by rfl) ⟨328253, by rfl⟩ : syracuseStep 1750685 = 656507) (by norm_num)
theorem B1750709 : Blo 1166400 1750709 := bbase (se 5 (by rfl) ⟨82064, by rfl⟩ : syracuseStep 1750709 = 164129) (by norm_num)
theorem B2627261 : Blo 1166400 2627261 := bbase (se 3 (by rfl) ⟨492611, by rfl⟩ : syracuseStep 2627261 = 985223) (by norm_num)
theorem B1750733 : Blo 1166400 1750733 := bbase (se 3 (by rfl) ⟨328262, by rfl⟩ : syracuseStep 1750733 = 656525) (by norm_num)
theorem B4429525 : Blo 1166400 4429525 := bbase (se 7 (by rfl) ⟨51908, by rfl⟩ : syracuseStep 4429525 = 103817) (by norm_num)
theorem B1750757 : Blo 1166400 1750757 := bbase (se 4 (by rfl) ⟨164133, by rfl⟩ : syracuseStep 1750757 = 328267) (by norm_num)
theorem B2954981 : Blo 1166400 2954981 := bbase (se 4 (by rfl) ⟨277029, by rfl⟩ : syracuseStep 2954981 = 554059) (by norm_num)
theorem B2217709 : Blo 1166400 2217709 := bbase (se 3 (by rfl) ⟨415820, by rfl⟩ : syracuseStep 2217709 = 831641) (by norm_num)
theorem B1750781 : Blo 1166400 1750781 := bbase (se 3 (by rfl) ⟨328271, by rfl⟩ : syracuseStep 1750781 = 656543) (by norm_num)
theorem B2627333 : Blo 1166400 2627333 := bbase (se 4 (by rfl) ⟨246312, by rfl⟩ : syracuseStep 2627333 = 492625) (by norm_num)
theorem B1750805 : Blo 1166400 1750805 := bbase (se 6 (by rfl) ⟨41034, by rfl⟩ : syracuseStep 1750805 = 82069) (by norm_num)
theorem B1750829 : Blo 1166400 1750829 := bbase (se 3 (by rfl) ⟨328280, by rfl⟩ : syracuseStep 1750829 = 656561) (by norm_num)
theorem B3323717 : Blo 1166400 3323717 := bbase (se 4 (by rfl) ⟨311598, by rfl⟩ : syracuseStep 3323717 = 623197) (by norm_num)
theorem B1750853 : Blo 1166400 1750853 := bbase (se 4 (by rfl) ⟨164142, by rfl⟩ : syracuseStep 1750853 = 328285) (by norm_num)
theorem B2627405 : Blo 1166400 2627405 := bbase (se 3 (by rfl) ⟨492638, by rfl⟩ : syracuseStep 2627405 = 985277) (by norm_num)
theorem B1660765 : Blo 1166400 1660765 := bbase (se 3 (by rfl) ⟨311393, by rfl⟩ : syracuseStep 1660765 = 622787) (by norm_num)
theorem B1750877 : Blo 1166400 1750877 := bbase (se 3 (by rfl) ⟨328289, by rfl⟩ : syracuseStep 1750877 = 656579) (by norm_num)
theorem B3938165 : Blo 1166400 3938165 := bbase (se 5 (by rfl) ⟨184601, by rfl⟩ : syracuseStep 3938165 = 369203) (by norm_num)
theorem B1750901 : Blo 1166400 1750901 := bbase (se 5 (by rfl) ⟨82073, by rfl⟩ : syracuseStep 1750901 = 164147) (by norm_num)
theorem B1750925 : Blo 1166400 1750925 := bbase (se 3 (by rfl) ⟨328298, by rfl⟩ : syracuseStep 1750925 = 656597) (by norm_num)
theorem B2627477 : Blo 1166400 2627477 := bbase (se 6 (by rfl) ⟨61581, by rfl⟩ : syracuseStep 2627477 = 123163) (by norm_num)
theorem B1750949 : Blo 1166400 1750949 := bbase (se 4 (by rfl) ⟨164151, by rfl⟩ : syracuseStep 1750949 = 328303) (by norm_num)
theorem B4986805 : Blo 1166400 4986805 := bbase (se 5 (by rfl) ⟨233756, by rfl⟩ : syracuseStep 4986805 = 467513) (by norm_num)
theorem B1750973 : Blo 1166400 1750973 := bbase (se 3 (by rfl) ⟨328307, by rfl⟩ : syracuseStep 1750973 = 656615) (by norm_num)
theorem B1750997 : Blo 1166400 1750997 := bbase (se 7 (by rfl) ⟨20519, by rfl⟩ : syracuseStep 1750997 = 41039) (by norm_num)
theorem B2627549 : Blo 1166400 2627549 := bbase (se 3 (by rfl) ⟨492665, by rfl⟩ : syracuseStep 2627549 = 985331) (by norm_num)
theorem B1751021 : Blo 1166400 1751021 := bbase (se 3 (by rfl) ⟨328316, by rfl⟩ : syracuseStep 1751021 = 656633) (by norm_num)
theorem B7100405 : Blo 1166400 7100405 := bbase (se 5 (by rfl) ⟨332831, by rfl⟩ : syracuseStep 7100405 = 665663) (by norm_num)
theorem B9975797 : Blo 1166400 9975797 := bbase (se 5 (by rfl) ⟨467615, by rfl⟩ : syracuseStep 9975797 = 935231) (by norm_num)
theorem B4429829 : Blo 1166400 4429829 := bbase (se 4 (by rfl) ⟨415296, by rfl⟩ : syracuseStep 4429829 = 830593) (by norm_num)
theorem B1751045 : Blo 1166400 1751045 := bbase (se 4 (by rfl) ⟨164160, by rfl⟩ : syracuseStep 1751045 = 328321) (by norm_num)
theorem B1751069 : Blo 1166400 1751069 := bbase (se 3 (by rfl) ⟨328325, by rfl⟩ : syracuseStep 1751069 = 656651) (by norm_num)
theorem B2218013 : Blo 1166400 2218013 := bbase (se 3 (by rfl) ⟨415877, by rfl⟩ : syracuseStep 2218013 = 831755) (by norm_num)
theorem B2627621 : Blo 1166400 2627621 := bbase (se 4 (by rfl) ⟨246339, by rfl⟩ : syracuseStep 2627621 = 492679) (by norm_num)
theorem B1660981 : Blo 1166400 1660981 := bbase (se 5 (by rfl) ⟨77858, by rfl⟩ : syracuseStep 1660981 = 155717) (by norm_num)
theorem B3790901 : Blo 1166400 3790901 := bbase (se 5 (by rfl) ⟨177698, by rfl⟩ : syracuseStep 3790901 = 355397) (by norm_num)
theorem B1751093 : Blo 1166400 1751093 := bbase (se 5 (by rfl) ⟨82082, by rfl⟩ : syracuseStep 1751093 = 164165) (by norm_num)
theorem B2955325 : Blo 1166400 2955325 := bbase (se 3 (by rfl) ⟨554123, by rfl⟩ : syracuseStep 2955325 = 1108247) (by norm_num)
theorem B1751117 : Blo 1166400 1751117 := bbase (se 3 (by rfl) ⟨328334, by rfl⟩ : syracuseStep 1751117 = 656669) (by norm_num)
theorem B14964821 : Blo 1166400 14964821 := bbase (se 8 (by rfl) ⟨87684, by rfl⟩ : syracuseStep 14964821 = 175369) (by norm_num)
theorem B1751141 : Blo 1166400 1751141 := bbase (se 4 (by rfl) ⟨164169, by rfl⟩ : syracuseStep 1751141 = 328339) (by norm_num)
theorem B2627693 : Blo 1166400 2627693 := bbase (se 3 (by rfl) ⟨492692, by rfl⟩ : syracuseStep 2627693 = 985385) (by norm_num)
theorem B1751165 : Blo 1166400 1751165 := bbase (se 3 (by rfl) ⟨328343, by rfl⟩ : syracuseStep 1751165 = 656687) (by norm_num)
theorem B1751189 : Blo 1166400 1751189 := bbase (se 6 (by rfl) ⟨41043, by rfl⟩ : syracuseStep 1751189 = 82087) (by norm_num)
theorem B1751213 : Blo 1166400 1751213 := bbase (se 3 (by rfl) ⟨328352, by rfl⟩ : syracuseStep 1751213 = 656705) (by norm_num)
theorem B2955437 : Blo 1166400 2955437 := bbase (se 3 (by rfl) ⟨554144, by rfl⟩ : syracuseStep 2955437 = 1108289) (by norm_num)
theorem B2627765 : Blo 1166400 2627765 := bbase (se 5 (by rfl) ⟨123176, by rfl⟩ : syracuseStep 2627765 = 246353) (by norm_num)
theorem B1751237 : Blo 1166400 1751237 := bbase (se 4 (by rfl) ⟨164178, by rfl⟩ : syracuseStep 1751237 = 328357) (by norm_num)
theorem B1751261 : Blo 1166400 1751261 := bbase (se 3 (by rfl) ⟨328361, by rfl⟩ : syracuseStep 1751261 = 656723) (by norm_num)
theorem B3324149 : Blo 1166400 3324149 := bbase (se 5 (by rfl) ⟨155819, by rfl⟩ : syracuseStep 3324149 = 311639) (by norm_num)
theorem B1751285 : Blo 1166400 1751285 := bbase (se 5 (by rfl) ⟨82091, by rfl⟩ : syracuseStep 1751285 = 164183) (by norm_num)
theorem B8534261 : Blo 1166400 8534261 := bbase (se 5 (by rfl) ⟨400043, by rfl⟩ : syracuseStep 8534261 = 800087) (by norm_num)
theorem B2627837 : Blo 1166400 2627837 := bbase (se 3 (by rfl) ⟨492719, by rfl⟩ : syracuseStep 2627837 = 985439) (by norm_num)
theorem B5912837 : Blo 1166400 5912837 := bbase (se 4 (by rfl) ⟨554328, by rfl⟩ : syracuseStep 5912837 = 1108657) (by norm_num)
theorem B1751309 : Blo 1166400 1751309 := bbase (se 3 (by rfl) ⟨328370, by rfl⟩ : syracuseStep 1751309 = 656741) (by norm_num)
theorem B2996509 : Blo 1166400 2996509 := bbase (se 3 (by rfl) ⟨561845, by rfl⟩ : syracuseStep 2996509 = 1123691) (by norm_num)
theorem B3938597 : Blo 1166400 3938597 := bbase (se 4 (by rfl) ⟨369243, by rfl⟩ : syracuseStep 3938597 = 738487) (by norm_num)
theorem B1751333 : Blo 1166400 1751333 := bbase (se 4 (by rfl) ⟨164187, by rfl⟩ : syracuseStep 1751333 = 328375) (by norm_num)
theorem B1751357 : Blo 1166400 1751357 := bbase (se 3 (by rfl) ⟨328379, by rfl⟩ : syracuseStep 1751357 = 656759) (by norm_num)
theorem B2627909 : Blo 1166400 2627909 := bbase (se 4 (by rfl) ⟨246366, by rfl⟩ : syracuseStep 2627909 = 492733) (by norm_num)
theorem B1751381 : Blo 1166400 1751381 := bbase (se 10 (by rfl) ⟨2565, by rfl⟩ : syracuseStep 1751381 = 5131) (by norm_num)
theorem B2881885 : Blo 1166400 2881885 := bbase (se 3 (by rfl) ⟨540353, by rfl⟩ : syracuseStep 2881885 = 1080707) (by norm_num)
theorem B1751405 : Blo 1166400 1751405 := bbase (se 3 (by rfl) ⟨328388, by rfl⟩ : syracuseStep 1751405 = 656777) (by norm_num)
theorem B2955629 : Blo 1166400 2955629 := bbase (se 3 (by rfl) ⟨554180, by rfl⟩ : syracuseStep 2955629 = 1108361) (by norm_num)
theorem B1849717 : Blo 1166400 1849717 := bbase (se 5 (by rfl) ⟨86705, by rfl⟩ : syracuseStep 1849717 = 173411) (by norm_num)
theorem B1751429 : Blo 1166400 1751429 := bbase (se 4 (by rfl) ⟨164196, by rfl⟩ : syracuseStep 1751429 = 328393) (by norm_num)
theorem B2627981 : Blo 1166400 2627981 := bbase (se 3 (by rfl) ⟨492746, by rfl⟩ : syracuseStep 2627981 = 985493) (by norm_num)
theorem B2365853 : Blo 1166400 2365853 := bbase (se 3 (by rfl) ⟨443597, by rfl⟩ : syracuseStep 2365853 = 887195) (by norm_num)
theorem B1751453 : Blo 1166400 1751453 := bbase (se 3 (by rfl) ⟨328397, by rfl⟩ : syracuseStep 1751453 = 656795) (by norm_num)
theorem B2365861 : Blo 1166400 2365861 := bbase (se 4 (by rfl) ⟨221799, by rfl⟩ : syracuseStep 2365861 = 443599) (by norm_num)
theorem B1661357 : Blo 1166400 1661357 := bbase (se 3 (by rfl) ⟨311504, by rfl⟩ : syracuseStep 1661357 = 623009) (by norm_num)
theorem B1751477 : Blo 1166400 1751477 := bbase (se 5 (by rfl) ⟨82100, by rfl⟩ : syracuseStep 1751477 = 164201) (by norm_num)
theorem B1751501 : Blo 1166400 1751501 := bbase (se 3 (by rfl) ⟨328406, by rfl⟩ : syracuseStep 1751501 = 656813) (by norm_num)
theorem B2628053 : Blo 1166400 2628053 := bbase (se 7 (by rfl) ⟨30797, by rfl⟩ : syracuseStep 2628053 = 61595) (by norm_num)
theorem B1751525 : Blo 1166400 1751525 := bbase (se 4 (by rfl) ⟨164205, by rfl⟩ : syracuseStep 1751525 = 328411) (by norm_num)
theorem B1751549 : Blo 1166400 1751549 := bbase (se 3 (by rfl) ⟨328415, by rfl⟩ : syracuseStep 1751549 = 656831) (by norm_num)
theorem B5610005 : Blo 1166400 5610005 := bbase (se 6 (by rfl) ⟨131484, by rfl⟩ : syracuseStep 5610005 = 262969) (by norm_num)
theorem B1751573 : Blo 1166400 1751573 := bbase (se 6 (by rfl) ⟨41052, by rfl⟩ : syracuseStep 1751573 = 82105) (by norm_num)
theorem B2628125 : Blo 1166400 2628125 := bbase (se 3 (by rfl) ⟨492773, by rfl⟩ : syracuseStep 2628125 = 985547) (by norm_num)
theorem B1751597 : Blo 1166400 1751597 := bbase (se 3 (by rfl) ⟨328424, by rfl⟩ : syracuseStep 1751597 = 656849) (by norm_num)
theorem B5323333 : Blo 1166400 5323333 := bbase (se 4 (by rfl) ⟨499062, by rfl⟩ : syracuseStep 5323333 = 998125) (by norm_num)
theorem B1751621 : Blo 1166400 1751621 := bbase (se 4 (by rfl) ⟨164214, by rfl⟩ : syracuseStep 1751621 = 328429) (by norm_num)
theorem B1751645 : Blo 1166400 1751645 := bbase (se 3 (by rfl) ⟨328433, by rfl⟩ : syracuseStep 1751645 = 656867) (by norm_num)
theorem B2628197 : Blo 1166400 2628197 := bbase (se 4 (by rfl) ⟨246393, by rfl⟩ : syracuseStep 2628197 = 492787) (by norm_num)
theorem B1751669 : Blo 1166400 1751669 := bbase (se 5 (by rfl) ⟨82109, by rfl⟩ : syracuseStep 1751669 = 164219) (by norm_num)
theorem B1751693 : Blo 1166400 1751693 := bbase (se 3 (by rfl) ⟨328442, by rfl⟩ : syracuseStep 1751693 = 656885) (by norm_num)
theorem B5905061 : Blo 1166400 5905061 := bbase (se 4 (by rfl) ⟨553599, by rfl⟩ : syracuseStep 5905061 = 1107199) (by norm_num)
theorem B1751717 : Blo 1166400 1751717 := bbase (se 4 (by rfl) ⟨164223, by rfl⟩ : syracuseStep 1751717 = 328447) (by norm_num)
theorem B2628269 : Blo 1166400 2628269 := bbase (se 3 (by rfl) ⟨492800, by rfl⟩ : syracuseStep 2628269 = 985601) (by norm_num)
theorem B2103997 : Blo 1166400 2103997 := bbase (se 3 (by rfl) ⟨394499, by rfl⟩ : syracuseStep 2103997 = 788999) (by norm_num)
theorem B1751741 : Blo 1166400 1751741 := bbase (se 3 (by rfl) ⟨328451, by rfl⟩ : syracuseStep 1751741 = 656903) (by norm_num)
theorem B1997509 : Blo 1166400 1997509 := bbase (se 4 (by rfl) ⟨187266, by rfl⟩ : syracuseStep 1997509 = 374533) (by norm_num)
theorem B2955973 : Blo 1166400 2955973 := bbase (se 4 (by rfl) ⟨277122, by rfl⟩ : syracuseStep 2955973 = 554245) (by norm_num)
theorem B3939029 : Blo 1166400 3939029 := bbase (se 7 (by rfl) ⟨46160, by rfl⟩ : syracuseStep 3939029 = 92321) (by norm_num)
theorem B1751765 : Blo 1166400 1751765 := bbase (se 7 (by rfl) ⟨20528, by rfl⟩ : syracuseStep 1751765 = 41057) (by norm_num)
theorem B1751789 : Blo 1166400 1751789 := bbase (se 3 (by rfl) ⟨328460, by rfl⟩ : syracuseStep 1751789 = 656921) (by norm_num)
theorem B2628341 : Blo 1166400 2628341 := bbase (se 5 (by rfl) ⟨123203, by rfl⟩ : syracuseStep 2628341 = 246407) (by norm_num)
theorem B1751813 : Blo 1166400 1751813 := bbase (se 4 (by rfl) ⟨164232, by rfl⟩ : syracuseStep 1751813 = 328465) (by norm_num)
theorem B1751837 : Blo 1166400 1751837 := bbase (se 3 (by rfl) ⟨328469, by rfl⟩ : syracuseStep 1751837 = 656939) (by norm_num)
theorem B2956085 : Blo 1166400 2956085 := bbase (se 5 (by rfl) ⟨138566, by rfl⟩ : syracuseStep 2956085 = 277133) (by norm_num)
theorem B1751861 : Blo 1166400 1751861 := bbase (se 5 (by rfl) ⟨82118, by rfl⟩ : syracuseStep 1751861 = 164237) (by norm_num)
theorem B2628413 : Blo 1166400 2628413 := bbase (se 3 (by rfl) ⟨492827, by rfl⟩ : syracuseStep 2628413 = 985655) (by norm_num)
theorem B1751885 : Blo 1166400 1751885 := bbase (se 3 (by rfl) ⟨328478, by rfl⟩ : syracuseStep 1751885 = 656957) (by norm_num)
theorem B1751909 : Blo 1166400 1751909 := bbase (se 4 (by rfl) ⟨164241, by rfl⟩ : syracuseStep 1751909 = 328483) (by norm_num)
theorem B1751933 : Blo 1166400 1751933 := bbase (se 3 (by rfl) ⟨328487, by rfl⟩ : syracuseStep 1751933 = 656975) (by norm_num)
theorem B2628485 : Blo 1166400 2628485 := bbase (se 4 (by rfl) ⟨246420, by rfl⟩ : syracuseStep 2628485 = 492841) (by norm_num)
theorem B2104213 : Blo 1166400 2104213 := bbase (se 6 (by rfl) ⟨49317, by rfl⟩ : syracuseStep 2104213 = 98635) (by norm_num)
theorem B1751957 : Blo 1166400 1751957 := bbase (se 6 (by rfl) ⟨41061, by rfl⟩ : syracuseStep 1751957 = 82123) (by norm_num)
theorem B1498009 : Blo 1166400 1498009 := bbase (se 2 (by rfl) ⟨561753, by rfl⟩ : syracuseStep 1498009 = 1123507) (by norm_num)
theorem B1751981 : Blo 1166400 1751981 := bbase (se 3 (by rfl) ⟨328496, by rfl⟩ : syracuseStep 1751981 = 656993) (by norm_num)
theorem B1752005 : Blo 1166400 1752005 := bbase (se 4 (by rfl) ⟨164250, by rfl⟩ : syracuseStep 1752005 = 328501) (by norm_num)
theorem B2628557 : Blo 1166400 2628557 := bbase (se 3 (by rfl) ⟨492854, by rfl⟩ : syracuseStep 2628557 = 985709) (by norm_num)
theorem B11369429 : Blo 1166400 11369429 := bbase (se 7 (by rfl) ⟨133235, by rfl⟩ : syracuseStep 11369429 = 266471) (by norm_num)
theorem B1752029 : Blo 1166400 1752029 := bbase (se 3 (by rfl) ⟨328505, by rfl⟩ : syracuseStep 1752029 = 657011) (by norm_num)
theorem B3324901 : Blo 1166400 3324901 := bbase (se 4 (by rfl) ⟨311709, by rfl⟩ : syracuseStep 3324901 = 623419) (by norm_num)
theorem B2956277 : Blo 1166400 2956277 := bbase (se 5 (by rfl) ⟨138575, by rfl⟩ : syracuseStep 2956277 = 277151) (by norm_num)
theorem B1752053 : Blo 1166400 1752053 := bbase (se 5 (by rfl) ⟨82127, by rfl⟩ : syracuseStep 1752053 = 164255) (by norm_num)
theorem B1752077 : Blo 1166400 1752077 := bbase (se 3 (by rfl) ⟨328514, by rfl⟩ : syracuseStep 1752077 = 657029) (by norm_num)
theorem B2628629 : Blo 1166400 2628629 := bbase (se 6 (by rfl) ⟨61608, by rfl⟩ : syracuseStep 2628629 = 123217) (by norm_num)
theorem B1752101 : Blo 1166400 1752101 := bbase (se 4 (by rfl) ⟨164259, by rfl⟩ : syracuseStep 1752101 = 328519) (by norm_num)
theorem B1752125 : Blo 1166400 1752125 := bbase (se 3 (by rfl) ⟨328523, by rfl⟩ : syracuseStep 1752125 = 657047) (by norm_num)
theorem B1752149 : Blo 1166400 1752149 := bbase (se 8 (by rfl) ⟨10266, by rfl⟩ : syracuseStep 1752149 = 20533) (by norm_num)
theorem B2628701 : Blo 1166400 2628701 := bbase (se 3 (by rfl) ⟨492881, by rfl⟩ : syracuseStep 2628701 = 985763) (by norm_num)
theorem B1752173 : Blo 1166400 1752173 := bbase (se 3 (by rfl) ⟨328532, by rfl⟩ : syracuseStep 1752173 = 657065) (by norm_num)
theorem B2399357 : Blo 1166400 2399357 := bbase (se 3 (by rfl) ⟨449879, by rfl⟩ : syracuseStep 2399357 = 899759) (by norm_num)
theorem B3939461 : Blo 1166400 3939461 := bbase (se 4 (by rfl) ⟨369324, by rfl⟩ : syracuseStep 3939461 = 738649) (by norm_num)
theorem B1752197 : Blo 1166400 1752197 := bbase (se 4 (by rfl) ⟨164268, by rfl⟩ : syracuseStep 1752197 = 328537) (by norm_num)
theorem B1752221 : Blo 1166400 1752221 := bbase (se 3 (by rfl) ⟨328541, by rfl⟩ : syracuseStep 1752221 = 657083) (by norm_num)
theorem B2628773 : Blo 1166400 2628773 := bbase (se 4 (by rfl) ⟨246447, by rfl⟩ : syracuseStep 2628773 = 492895) (by norm_num)
theorem B1752245 : Blo 1166400 1752245 := bbase (se 5 (by rfl) ⟨82136, by rfl⟩ : syracuseStep 1752245 = 164273) (by norm_num)
theorem B1752269 : Blo 1166400 1752269 := bbase (se 3 (by rfl) ⟨328550, by rfl⟩ : syracuseStep 1752269 = 657101) (by norm_num)
theorem B1752293 : Blo 1166400 1752293 := bbase (se 4 (by rfl) ⟨164277, by rfl⟩ : syracuseStep 1752293 = 328555) (by norm_num)
theorem B3742949 : Blo 1166400 3742949 := bbase (se 4 (by rfl) ⟨350901, by rfl⟩ : syracuseStep 3742949 = 701803) (by norm_num)
theorem B2628845 : Blo 1166400 2628845 := bbase (se 3 (by rfl) ⟨492908, by rfl⟩ : syracuseStep 2628845 = 985817) (by norm_num)
theorem B1752317 : Blo 1166400 1752317 := bbase (se 3 (by rfl) ⟨328559, by rfl⟩ : syracuseStep 1752317 = 657119) (by norm_num)
theorem B4799765 : Blo 1166400 4799765 := bbase (se 6 (by rfl) ⟨112494, by rfl⟩ : syracuseStep 4799765 = 224989) (by norm_num)
theorem B1752341 : Blo 1166400 1752341 := bbase (se 6 (by rfl) ⟨41070, by rfl⟩ : syracuseStep 1752341 = 82141) (by norm_num)
theorem B1752365 : Blo 1166400 1752365 := bbase (se 3 (by rfl) ⟨328568, by rfl⟩ : syracuseStep 1752365 = 657137) (by norm_num)
theorem B1752389 : Blo 1166400 1752389 := bbase (se 4 (by rfl) ⟨164286, by rfl⟩ : syracuseStep 1752389 = 328573) (by norm_num)
theorem B2956621 : Blo 1166400 2956621 := bbase (se 3 (by rfl) ⟨554366, by rfl⟩ : syracuseStep 2956621 = 1108733) (by norm_num)
theorem B27344213 : Blo 1166400 27344213 := bbase (se 11 (by rfl) ⟨20027, by rfl⟩ : syracuseStep 27344213 = 40055) (by norm_num)
theorem B1752413 : Blo 1166400 1752413 := bbase (se 3 (by rfl) ⟨328577, by rfl⟩ : syracuseStep 1752413 = 657155) (by norm_num)
theorem B1752437 : Blo 1166400 1752437 := bbase (se 5 (by rfl) ⟨82145, by rfl⟩ : syracuseStep 1752437 = 164291) (by norm_num)
theorem B1752461 : Blo 1166400 1752461 := bbase (se 3 (by rfl) ⟨328586, by rfl⟩ : syracuseStep 1752461 = 657173) (by norm_num)
theorem B1752485 : Blo 1166400 1752485 := bbase (se 4 (by rfl) ⟨164295, by rfl⟩ : syracuseStep 1752485 = 328591) (by norm_num)
theorem B2956733 : Blo 1166400 2956733 := bbase (se 3 (by rfl) ⟨554387, by rfl⟩ : syracuseStep 2956733 = 1108775) (by norm_num)
theorem B1752509 : Blo 1166400 1752509 := bbase (se 3 (by rfl) ⟨328595, by rfl⟩ : syracuseStep 1752509 = 657191) (by norm_num)
theorem B1752533 : Blo 1166400 1752533 := bbase (se 7 (by rfl) ⟨20537, by rfl⟩ : syracuseStep 1752533 = 41075) (by norm_num)
theorem B1752557 : Blo 1166400 1752557 := bbase (se 3 (by rfl) ⟨328604, by rfl⟩ : syracuseStep 1752557 = 657209) (by norm_num)
theorem B1752581 : Blo 1166400 1752581 := bbase (se 4 (by rfl) ⟨164304, by rfl⟩ : syracuseStep 1752581 = 328609) (by norm_num)
theorem B5914133 : Blo 1166400 5914133 := bbase (se 6 (by rfl) ⟨138612, by rfl⟩ : syracuseStep 5914133 = 277225) (by norm_num)
theorem B11214389 : Blo 1166400 11214389 := bbase (se 5 (by rfl) ⟨525674, by rfl⟩ : syracuseStep 11214389 = 1051349) (by norm_num)
theorem B3939893 : Blo 1166400 3939893 := bbase (se 5 (by rfl) ⟨184682, by rfl⟩ : syracuseStep 3939893 = 369365) (by norm_num)
theorem B2367029 : Blo 1166400 2367029 := bbase (se 5 (by rfl) ⟨110954, by rfl⟩ : syracuseStep 2367029 = 221909) (by norm_num)
theorem B3595877 : Blo 1166400 3595877 := bbase (se 4 (by rfl) ⟨337113, by rfl⟩ : syracuseStep 3595877 = 674227) (by norm_num)
theorem B2956925 : Blo 1166400 2956925 := bbase (se 3 (by rfl) ⟨554423, by rfl⟩ : syracuseStep 2956925 = 1108847) (by norm_num)
theorem B1539733 : Blo 1166400 1539733 := bbase (se 6 (by rfl) ⟨36087, by rfl⟩ : syracuseStep 1539733 = 72175) (by norm_num)
theorem B3153637 : Blo 1166400 3153637 := bbase (se 4 (by rfl) ⟨295653, by rfl⟩ : syracuseStep 3153637 = 591307) (by norm_num)
theorem B1662781 : Blo 1166400 1662781 := bbase (se 3 (by rfl) ⟨311771, by rfl⟩ : syracuseStep 1662781 = 623543) (by norm_num)
theorem B24600469 : Blo 1166400 24600469 := bbase (se 6 (by rfl) ⟨576573, by rfl⟩ : syracuseStep 24600469 = 1153147) (by norm_num)
theorem B5906357 : Blo 1166400 5906357 := bbase (se 5 (by rfl) ⟨276860, by rfl⟩ : syracuseStep 5906357 = 553721) (by norm_num)
theorem B2957269 : Blo 1166400 2957269 := bbase (se 7 (by rfl) ⟨34655, by rfl⟩ : syracuseStep 2957269 = 69311) (by norm_num)
theorem B3940325 : Blo 1166400 3940325 := bbase (se 4 (by rfl) ⟨369405, by rfl⟩ : syracuseStep 3940325 = 738811) (by norm_num)
theorem B3940433 : Blo 1166400 3940433 := bstep (se 2 (by rfl) ⟨1477662, by rfl⟩ : syracuseStep 3940433 = 2955325) B2955325
theorem B2957411 : Blo 1166400 2957411 := bstep (se 1 (by rfl) ⟨2218058, by rfl⟩ : syracuseStep 2957411 = 4436117) B4436117
theorem B1663345 : Blo 1166400 1663345 := bstep (se 2 (by rfl) ⟨623754, by rfl⟩ : syracuseStep 1663345 = 1247509) B1247509
theorem B63906245 : Blo 1166400 63906245 := bstep (se 4 (by rfl) ⟨5991210, by rfl⟩ : syracuseStep 63906245 = 11982421) B11982421
theorem B3842513 : Blo 1166400 3842513 := bstep (se 2 (by rfl) ⟨1440942, by rfl⟩ : syracuseStep 3842513 = 2881885) B2881885
theorem B3326417 : Blo 1166400 3326417 := bstep (se 2 (by rfl) ⟨1247406, by rfl⟩ : syracuseStep 3326417 = 2494813) B2494813
theorem B5612003 : Blo 1166400 5612003 := bstep (se 1 (by rfl) ⟨4209002, by rfl⟩ : syracuseStep 5612003 = 8418005) B8418005
theorem B14967281 : Blo 1166400 14967281 := bstep (se 2 (by rfl) ⟨5612730, by rfl⟩ : syracuseStep 14967281 = 11225461) B11225461
theorem B2466289 : Blo 1166400 2466289 := bstep (se 2 (by rfl) ⟨924858, by rfl⟩ : syracuseStep 2466289 = 1849717) B1849717
theorem B7103011 : Blo 1166400 7103011 := bstep (se 1 (by rfl) ⟨5327258, by rfl⟩ : syracuseStep 7103011 = 10654517) B10654517
theorem B3154481 : Blo 1166400 3154481 := bstep (se 2 (by rfl) ⟨1182930, by rfl⟩ : syracuseStep 3154481 = 2365861) B2365861
theorem B4989539 : Blo 1166400 4989539 := bstep (se 1 (by rfl) ⟨3742154, by rfl⟩ : syracuseStep 4989539 = 7484309) B7484309
theorem B3940973 : Blo 1166400 3940973 := bstep (se 3 (by rfl) ⟨738932, by rfl⟩ : syracuseStep 3940973 = 1477865) B1477865
theorem B3367565 : Blo 1166400 3367565 := bstep (se 3 (by rfl) ⟨631418, by rfl⟩ : syracuseStep 3367565 = 1262837) B1262837
theorem B22758029 : Blo 1166400 22758029 := bstep (se 3 (by rfl) ⟨4267130, by rfl⟩ : syracuseStep 22758029 = 8534261) B8534261
theorem B3326609 : Blo 1166400 3326609 := bstep (se 2 (by rfl) ⟨1247478, by rfl⟩ : syracuseStep 3326609 = 2494957) B2494957
theorem B3941027 : Blo 1166400 3941027 := bstep (se 1 (by rfl) ⟨2955770, by rfl⟩ : syracuseStep 3941027 = 5911541) B5911541
theorem B25608901 : Blo 1166400 25608901 := bstep (se 4 (by rfl) ⟨2400834, by rfl⟩ : syracuseStep 25608901 = 4801669) B4801669
theorem B1868579 : Blo 1166400 1868579 := bstep (se 1 (by rfl) ⟨1401434, by rfl⟩ : syracuseStep 1868579 = 2802869) B2802869
theorem B7480133 : Blo 1166400 7480133 := bstep (se 4 (by rfl) ⟨701262, by rfl⟩ : syracuseStep 7480133 = 1402525) B1402525
theorem B2245475 : Blo 1166400 2245475 := bstep (se 1 (by rfl) ⟨1684106, by rfl⟩ : syracuseStep 2245475 = 3368213) B3368213
theorem B2663345 : Blo 1166400 2663345 := bstep (se 2 (by rfl) ⟨998754, by rfl⟩ : syracuseStep 2663345 = 1997509) B1997509
theorem B3941297 : Blo 1166400 3941297 := bstep (se 2 (by rfl) ⟨1477986, by rfl⟩ : syracuseStep 3941297 = 2955973) B2955973
theorem B1246163 : Blo 1166400 1246163 := bstep (se 1 (by rfl) ⟨934622, by rfl⟩ : syracuseStep 1246163 = 1869245) B1869245
theorem B1868771 : Blo 1166400 1868771 := bstep (se 1 (by rfl) ⟨1401578, by rfl⟩ : syracuseStep 1868771 = 2803157) B2803157
theorem B5907491 : Blo 1166400 5907491 := bstep (se 1 (by rfl) ⟨4430618, by rfl⟩ : syracuseStep 5907491 = 8861237) B8861237
theorem B1262659 : Blo 1166400 1262659 := bstep (se 1 (by rfl) ⟨946994, by rfl⟩ : syracuseStep 1262659 = 1893989) B1893989
theorem B2663491 : Blo 1166400 2663491 := bstep (se 1 (by rfl) ⟨1997618, by rfl⟩ : syracuseStep 2663491 = 3995237) B3995237
theorem B6308941 : Blo 1166400 6308941 := bstep (se 3 (by rfl) ⟨1182926, by rfl⟩ : syracuseStep 6308941 = 2365853) B2365853
theorem B5989553 : Blo 1166400 5989553 := bstep (se 2 (by rfl) ⟨2246082, by rfl⟩ : syracuseStep 5989553 = 4492165) B4492165
theorem B16819397 : Blo 1166400 16819397 := bstep (se 4 (by rfl) ⟨1576818, by rfl⟩ : syracuseStep 16819397 = 3153637) B3153637
theorem B3736849 : Blo 1166400 3736849 := bstep (se 2 (by rfl) ⟨1401318, by rfl⟩ : syracuseStep 3736849 = 2802637) B2802637
theorem B4433201 : Blo 1166400 4433201 := bstep (se 2 (by rfl) ⟨1662450, by rfl⟩ : syracuseStep 4433201 = 3324901) B3324901
theorem B3941837 : Blo 1166400 3941837 := bstep (se 3 (by rfl) ⟨739094, by rfl⟩ : syracuseStep 3941837 = 1478189) B1478189
theorem B3941891 : Blo 1166400 3941891 := bstep (se 1 (by rfl) ⟨2956418, by rfl⟩ : syracuseStep 3941891 = 5912837) B5912837
theorem B3737105 : Blo 1166400 3737105 := bstep (se 2 (by rfl) ⟨1401414, by rfl⟩ : syracuseStep 3737105 = 2802829) B2802829
theorem B2491985 : Blo 1166400 2491985 := bstep (se 2 (by rfl) ⟨934494, by rfl⟩ : syracuseStep 2491985 = 1868989) B1868989
theorem B1312339 : Blo 1166400 1312339 := bstep (se 1 (by rfl) ⟨984254, by rfl⟩ : syracuseStep 1312339 = 1968509) B1968509
theorem B1246915 : Blo 1166400 1246915 := bstep (se 1 (by rfl) ⟨935186, by rfl⟩ : syracuseStep 1246915 = 1870373) B1870373
theorem B1312483 : Blo 1166400 1312483 := bstep (se 1 (by rfl) ⟨984362, by rfl⟩ : syracuseStep 1312483 = 1968725) B1968725
theorem B3942161 : Blo 1166400 3942161 := bstep (se 2 (by rfl) ⟨1478310, by rfl⟩ : syracuseStep 3942161 = 2956621) B2956621
theorem B6653765 : Blo 1166400 6653765 := bstep (se 4 (by rfl) ⟨623790, by rfl⟩ : syracuseStep 6653765 = 1247581) B1247581
theorem B5908301 : Blo 1166400 5908301 := bstep (se 3 (by rfl) ⟨1107806, by rfl⟩ : syracuseStep 5908301 = 2215613) B2215613
theorem B1312627 : Blo 1166400 1312627 := bstep (se 1 (by rfl) ⟨984470, by rfl⟩ : syracuseStep 1312627 = 1968941) B1968941
theorem B4982705 : Blo 1166400 4982705 := bstep (se 2 (by rfl) ⟨1868514, by rfl⟩ : syracuseStep 4982705 = 3737029) B3737029
theorem B1869745 : Blo 1166400 1869745 := bstep (se 2 (by rfl) ⟨701154, by rfl⟩ : syracuseStep 1869745 = 1402309) B1402309
theorem B1247171 : Blo 1166400 1247171 := bstep (se 1 (by rfl) ⟨935378, by rfl⟩ : syracuseStep 1247171 = 1870757) B1870757
theorem B7579619 : Blo 1166400 7579619 := bstep (se 1 (by rfl) ⟨5684714, by rfl⟩ : syracuseStep 7579619 = 11369429) B11369429
theorem B1312771 : Blo 1166400 1312771 := bstep (se 1 (by rfl) ⟨984578, by rfl⟩ : syracuseStep 1312771 = 1969157) B1969157
theorem B1599571 : Blo 1166400 1599571 := bstep (se 1 (by rfl) ⟨1199678, by rfl⟩ : syracuseStep 1599571 = 2399357) B2399357
theorem B53889137 : Blo 1166400 53889137 := bstep (se 2 (by rfl) ⟨20208426, by rfl⟩ : syracuseStep 53889137 = 40416853) B40416853
theorem B1312915 : Blo 1166400 1312915 := bstep (se 1 (by rfl) ⟨984686, by rfl⟩ : syracuseStep 1312915 = 1969373) B1969373
theorem B1476787 : Blo 1166400 1476787 := bstep (se 1 (by rfl) ⟨1107590, by rfl⟩ : syracuseStep 1476787 = 2215181) B2215181
theorem B13289669 : Blo 1166400 13289669 := bstep (se 4 (by rfl) ⟨1245906, by rfl⟩ : syracuseStep 13289669 = 2491813) B2491813
theorem B18229475 : Blo 1166400 18229475 := bstep (se 1 (by rfl) ⟨13672106, by rfl⟩ : syracuseStep 18229475 = 27344213) B27344213
theorem B6654221 : Blo 1166400 6654221 := bstep (se 3 (by rfl) ⟨1247666, by rfl⟩ : syracuseStep 6654221 = 2495333) B2495333
theorem B1968401 : Blo 1166400 1968401 := bstep (se 2 (by rfl) ⟨738150, by rfl⟩ : syracuseStep 1968401 = 1476301) B1476301
theorem B1476883 : Blo 1166400 1476883 := bstep (se 1 (by rfl) ⟨1107662, by rfl⟩ : syracuseStep 1476883 = 2215325) B2215325
theorem B2804003 : Blo 1166400 2804003 := bstep (se 1 (by rfl) ⟨2103002, by rfl⟩ : syracuseStep 2804003 = 4206005) B4206005
theorem B1313059 : Blo 1166400 1313059 := bstep (se 1 (by rfl) ⟨984794, by rfl⟩ : syracuseStep 1313059 = 1969589) B1969589
theorem B3942701 : Blo 1166400 3942701 := bstep (se 3 (by rfl) ⟨739256, by rfl⟩ : syracuseStep 3942701 = 1478513) B1478513
theorem B3942755 : Blo 1166400 3942755 := bstep (se 1 (by rfl) ⟨2957066, by rfl⟩ : syracuseStep 3942755 = 5914133) B5914133
theorem B1870193 : Blo 1166400 1870193 := bstep (se 2 (by rfl) ⟨701322, by rfl⟩ : syracuseStep 1870193 = 1402645) B1402645
theorem B6646157 : Blo 1166400 6646157 := bstep (se 3 (by rfl) ⟨1246154, by rfl⟩ : syracuseStep 6646157 = 2492309) B2492309
theorem B7588237 : Blo 1166400 7588237 := bstep (se 3 (by rfl) ⟨1422794, by rfl⟩ : syracuseStep 7588237 = 2845589) B2845589
theorem B1968529 : Blo 1166400 1968529 := bstep (se 2 (by rfl) ⟨738198, by rfl⟩ : syracuseStep 1968529 = 1476397) B1476397
theorem B1968563 : Blo 1166400 1968563 := bstep (se 1 (by rfl) ⟨1476422, by rfl⟩ : syracuseStep 1968563 = 2952845) B2952845
theorem B1313203 : Blo 1166400 1313203 := bstep (se 1 (by rfl) ⟨984902, by rfl⟩ : syracuseStep 1313203 = 1969805) B1969805
theorem B14969285 : Blo 1166400 14969285 := bstep (se 4 (by rfl) ⟨1403370, by rfl⟩ : syracuseStep 14969285 = 2806741) B2806741
theorem B2214353 : Blo 1166400 2214353 := bstep (se 2 (by rfl) ⟨830382, by rfl⟩ : syracuseStep 2214353 = 1660765) B1660765
theorem B1968691 : Blo 1166400 1968691 := bstep (se 1 (by rfl) ⟨1476518, by rfl⟩ : syracuseStep 1968691 = 2953037) B2953037
theorem B2804291 : Blo 1166400 2804291 := bstep (se 1 (by rfl) ⟨2103218, by rfl⟩ : syracuseStep 2804291 = 4206437) B4206437
theorem B1313347 : Blo 1166400 1313347 := bstep (se 1 (by rfl) ⟨985010, by rfl⟩ : syracuseStep 1313347 = 1970021) B1970021
theorem B3738221 : Blo 1166400 3738221 := bstep (se 3 (by rfl) ⟨700916, by rfl⟩ : syracuseStep 3738221 = 1401833) B1401833
theorem B3943025 : Blo 1166400 3943025 := bstep (se 2 (by rfl) ⟨1478634, by rfl⟩ : syracuseStep 3943025 = 2957269) B2957269
theorem B1968833 : Blo 1166400 1968833 := bstep (se 2 (by rfl) ⟨738312, by rfl⟩ : syracuseStep 1968833 = 1476625) B1476625
theorem B1313491 : Blo 1166400 1313491 := bstep (se 1 (by rfl) ⟨985118, by rfl⟩ : syracuseStep 1313491 = 1970237) B1970237
theorem B4434659 : Blo 1166400 4434659 := bstep (se 1 (by rfl) ⟨3325994, by rfl⟩ : syracuseStep 4434659 = 6651989) B6651989
theorem B2214641 : Blo 1166400 2214641 := bstep (se 2 (by rfl) ⟨830490, by rfl⟩ : syracuseStep 2214641 = 1660981) B1660981
theorem B13298417 : Blo 1166400 13298417 := bstep (se 2 (by rfl) ⟨4986906, by rfl⟩ : syracuseStep 13298417 = 9973813) B9973813
theorem B2804483 : Blo 1166400 2804483 := bstep (se 1 (by rfl) ⟨2103362, by rfl⟩ : syracuseStep 2804483 = 4206725) B4206725
theorem B1477379 : Blo 1166400 1477379 := bstep (se 1 (by rfl) ⟨1108034, by rfl⟩ : syracuseStep 1477379 = 2216069) B2216069
theorem B1968961 : Blo 1166400 1968961 := bstep (se 2 (by rfl) ⟨738360, by rfl⟩ : syracuseStep 1968961 = 1476721) B1476721
theorem B1968995 : Blo 1166400 1968995 := bstep (se 1 (by rfl) ⟨1476746, by rfl⟩ : syracuseStep 1968995 = 2953493) B2953493
theorem B2493283 : Blo 1166400 2493283 := bstep (se 1 (by rfl) ⟨1869962, by rfl⟩ : syracuseStep 2493283 = 3739925) B3739925
theorem B1313635 : Blo 1166400 1313635 := bstep (se 1 (by rfl) ⟨985226, by rfl⟩ : syracuseStep 1313635 = 1970453) B1970453
theorem B1969123 : Blo 1166400 1969123 := bstep (se 1 (by rfl) ⟨1476842, by rfl⟩ : syracuseStep 1969123 = 2953685) B2953685
theorem B1313779 : Blo 1166400 1313779 := bstep (se 1 (by rfl) ⟨985334, by rfl⟩ : syracuseStep 1313779 = 1970669) B1970669
theorem B2624561 : Blo 1166400 2624561 := bstep (se 2 (by rfl) ⟨984210, by rfl⟩ : syracuseStep 2624561 = 1968421) B1968421
theorem B1166403 : Blo 1166400 1166403 := bstep (se 1 (by rfl) ⟨874802, by rfl⟩ : syracuseStep 1166403 = 1749605) B1749605
theorem B2624579 : Blo 1166400 2624579 := bstep (se 1 (by rfl) ⟨1968434, by rfl⟩ : syracuseStep 2624579 = 3936869) B3936869
theorem B1166419 : Blo 1166400 1166419 := bstep (se 1 (by rfl) ⟨874814, by rfl⟩ : syracuseStep 1166419 = 1749629) B1749629
theorem B1166435 : Blo 1166400 1166435 := bstep (se 1 (by rfl) ⟨874826, by rfl⟩ : syracuseStep 1166435 = 1749653) B1749653
theorem B1969265 : Blo 1166400 1969265 := bstep (se 2 (by rfl) ⟨738474, by rfl⟩ : syracuseStep 1969265 = 1476949) B1476949
theorem B1166451 : Blo 1166400 1166451 := bstep (se 1 (by rfl) ⟨874838, by rfl⟩ : syracuseStep 1166451 = 1749677) B1749677
theorem B1166467 : Blo 1166400 1166467 := bstep (se 1 (by rfl) ⟨874850, by rfl⟩ : syracuseStep 1166467 = 1749701) B1749701
theorem B1313923 : Blo 1166400 1313923 := bstep (se 1 (by rfl) ⟨985442, by rfl⟩ : syracuseStep 1313923 = 1970885) B1970885
theorem B1166483 : Blo 1166400 1166483 := bstep (se 1 (by rfl) ⟨874862, by rfl⟩ : syracuseStep 1166483 = 1749725) B1749725
theorem B1166499 : Blo 1166400 1166499 := bstep (se 1 (by rfl) ⟨874874, by rfl⟩ : syracuseStep 1166499 = 1749749) B1749749
theorem B4730033 : Blo 1166400 4730033 := bstep (se 2 (by rfl) ⟨1773762, by rfl⟩ : syracuseStep 4730033 = 3547525) B3547525
theorem B1166515 : Blo 1166400 1166515 := bstep (se 1 (by rfl) ⟨874886, by rfl⟩ : syracuseStep 1166515 = 1749773) B1749773
theorem B1166531 : Blo 1166400 1166531 := bstep (se 1 (by rfl) ⟨874898, by rfl⟩ : syracuseStep 1166531 = 1749797) B1749797
theorem B1166547 : Blo 1166400 1166547 := bstep (se 1 (by rfl) ⟨874910, by rfl⟩ : syracuseStep 1166547 = 1749821) B1749821
theorem B1166563 : Blo 1166400 1166563 := bstep (se 1 (by rfl) ⟨874922, by rfl⟩ : syracuseStep 1166563 = 1749845) B1749845
theorem B1969393 : Blo 1166400 1969393 := bstep (se 2 (by rfl) ⟨738522, by rfl⟩ : syracuseStep 1969393 = 1477045) B1477045
theorem B1166579 : Blo 1166400 1166579 := bstep (se 1 (by rfl) ⟨874934, by rfl⟩ : syracuseStep 1166579 = 1749869) B1749869
theorem B1166595 : Blo 1166400 1166595 := bstep (se 1 (by rfl) ⟨874946, by rfl⟩ : syracuseStep 1166595 = 1749893) B1749893
theorem B1166611 : Blo 1166400 1166611 := bstep (se 1 (by rfl) ⟨874958, by rfl⟩ : syracuseStep 1166611 = 1749917) B1749917
theorem B1969427 : Blo 1166400 1969427 := bstep (se 1 (by rfl) ⟨1477070, by rfl⟩ : syracuseStep 1969427 = 2954141) B2954141
theorem B1314067 : Blo 1166400 1314067 := bstep (se 1 (by rfl) ⟨985550, by rfl⟩ : syracuseStep 1314067 = 1971101) B1971101
theorem B1166627 : Blo 1166400 1166627 := bstep (se 1 (by rfl) ⟨874970, by rfl⟩ : syracuseStep 1166627 = 1749941) B1749941
theorem B1166643 : Blo 1166400 1166643 := bstep (se 1 (by rfl) ⟨874982, by rfl⟩ : syracuseStep 1166643 = 1749965) B1749965
theorem B1166659 : Blo 1166400 1166659 := bstep (se 1 (by rfl) ⟨874994, by rfl⟩ : syracuseStep 1166659 = 1749989) B1749989
theorem B2624849 : Blo 1166400 2624849 := bstep (se 2 (by rfl) ⟨984318, by rfl⟩ : syracuseStep 2624849 = 1968637) B1968637
theorem B1166675 : Blo 1166400 1166675 := bstep (se 1 (by rfl) ⟨875006, by rfl⟩ : syracuseStep 1166675 = 1750013) B1750013
theorem B2624867 : Blo 1166400 2624867 := bstep (se 1 (by rfl) ⟨1968650, by rfl⟩ : syracuseStep 2624867 = 3937301) B3937301
theorem B1166691 : Blo 1166400 1166691 := bstep (se 1 (by rfl) ⟨875018, by rfl⟩ : syracuseStep 1166691 = 1750037) B1750037
theorem B1166707 : Blo 1166400 1166707 := bstep (se 1 (by rfl) ⟨875030, by rfl⟩ : syracuseStep 1166707 = 1750061) B1750061
theorem B1166723 : Blo 1166400 1166723 := bstep (se 1 (by rfl) ⟨875042, by rfl⟩ : syracuseStep 1166723 = 1750085) B1750085
theorem B1166739 : Blo 1166400 1166739 := bstep (se 1 (by rfl) ⟨875054, by rfl⟩ : syracuseStep 1166739 = 1750109) B1750109
theorem B1969555 : Blo 1166400 1969555 := bstep (se 1 (by rfl) ⟨1477166, by rfl⟩ : syracuseStep 1969555 = 2954333) B2954333
theorem B1166755 : Blo 1166400 1166755 := bstep (se 1 (by rfl) ⟨875066, by rfl⟩ : syracuseStep 1166755 = 1750133) B1750133
theorem B1314211 : Blo 1166400 1314211 := bstep (se 1 (by rfl) ⟨985658, by rfl⟩ : syracuseStep 1314211 = 1971317) B1971317
theorem B7097777 : Blo 1166400 7097777 := bstep (se 2 (by rfl) ⟨2661666, by rfl⟩ : syracuseStep 7097777 = 5323333) B5323333
theorem B1166771 : Blo 1166400 1166771 := bstep (se 1 (by rfl) ⟨875078, by rfl⟩ : syracuseStep 1166771 = 1750157) B1750157
theorem B1166787 : Blo 1166400 1166787 := bstep (se 1 (by rfl) ⟨875090, by rfl⟩ : syracuseStep 1166787 = 1750181) B1750181
theorem B2215363 : Blo 1166400 2215363 := bstep (se 1 (by rfl) ⟨1661522, by rfl⟩ : syracuseStep 2215363 = 3323045) B3323045
theorem B1478083 : Blo 1166400 1478083 := bstep (se 1 (by rfl) ⟨1108562, by rfl⟩ : syracuseStep 1478083 = 2217125) B2217125
theorem B18943429 : Blo 1166400 18943429 := bstep (se 4 (by rfl) ⟨1775946, by rfl⟩ : syracuseStep 18943429 = 3551893) B3551893
theorem B1166803 : Blo 1166400 1166803 := bstep (se 1 (by rfl) ⟨875102, by rfl⟩ : syracuseStep 1166803 = 1750205) B1750205
theorem B1166819 : Blo 1166400 1166819 := bstep (se 1 (by rfl) ⟨875114, by rfl⟩ : syracuseStep 1166819 = 1750229) B1750229
theorem B1166835 : Blo 1166400 1166835 := bstep (se 1 (by rfl) ⟨875126, by rfl⟩ : syracuseStep 1166835 = 1750253) B1750253
theorem B1166851 : Blo 1166400 1166851 := bstep (se 1 (by rfl) ⟨875138, by rfl⟩ : syracuseStep 1166851 = 1750277) B1750277
theorem B3157507 : Blo 1166400 3157507 := bstep (se 1 (by rfl) ⟨2368130, by rfl⟩ : syracuseStep 3157507 = 4736261) B4736261
theorem B1166867 : Blo 1166400 1166867 := bstep (se 1 (by rfl) ⟨875150, by rfl⟩ : syracuseStep 1166867 = 1750301) B1750301
theorem B1969697 : Blo 1166400 1969697 := bstep (se 2 (by rfl) ⟨738636, by rfl⟩ : syracuseStep 1969697 = 1477273) B1477273
theorem B1166883 : Blo 1166400 1166883 := bstep (se 1 (by rfl) ⟨875162, by rfl⟩ : syracuseStep 1166883 = 1750325) B1750325
theorem B1478179 : Blo 1166400 1478179 := bstep (se 1 (by rfl) ⟨1108634, by rfl⟩ : syracuseStep 1478179 = 2217269) B2217269
theorem B1166899 : Blo 1166400 1166899 := bstep (se 1 (by rfl) ⟨875174, by rfl⟩ : syracuseStep 1166899 = 1750349) B1750349
theorem B1314355 : Blo 1166400 1314355 := bstep (se 1 (by rfl) ⟨985766, by rfl⟩ : syracuseStep 1314355 = 1971533) B1971533
theorem B1166915 : Blo 1166400 1166915 := bstep (se 1 (by rfl) ⟨875186, by rfl⟩ : syracuseStep 1166915 = 1750373) B1750373
theorem B2805329 : Blo 1166400 2805329 := bstep (se 2 (by rfl) ⟨1051998, by rfl⟩ : syracuseStep 2805329 = 2103997) B2103997
theorem B1166931 : Blo 1166400 1166931 := bstep (se 1 (by rfl) ⟨875198, by rfl⟩ : syracuseStep 1166931 = 1750397) B1750397
theorem B1166947 : Blo 1166400 1166947 := bstep (se 1 (by rfl) ⟨875210, by rfl⟩ : syracuseStep 1166947 = 1750421) B1750421
theorem B7474801 : Blo 1166400 7474801 := bstep (se 2 (by rfl) ⟨2803050, by rfl⟩ : syracuseStep 7474801 = 5606101) B5606101
theorem B2625137 : Blo 1166400 2625137 := bstep (se 2 (by rfl) ⟨984426, by rfl⟩ : syracuseStep 2625137 = 1968853) B1968853
theorem B1166963 : Blo 1166400 1166963 := bstep (se 1 (by rfl) ⟨875222, by rfl⟩ : syracuseStep 1166963 = 1750445) B1750445
theorem B2625155 : Blo 1166400 2625155 := bstep (se 1 (by rfl) ⟨1968866, by rfl⟩ : syracuseStep 2625155 = 3937733) B3937733
theorem B1166979 : Blo 1166400 1166979 := bstep (se 1 (by rfl) ⟨875234, by rfl⟩ : syracuseStep 1166979 = 1750469) B1750469
theorem B1166995 : Blo 1166400 1166995 := bstep (se 1 (by rfl) ⟨875246, by rfl⟩ : syracuseStep 1166995 = 1750493) B1750493
theorem B1969825 : Blo 1166400 1969825 := bstep (se 2 (by rfl) ⟨738684, by rfl⟩ : syracuseStep 1969825 = 1477369) B1477369
theorem B1167011 : Blo 1166400 1167011 := bstep (se 1 (by rfl) ⟨875258, by rfl⟩ : syracuseStep 1167011 = 1750517) B1750517
theorem B1167027 : Blo 1166400 1167027 := bstep (se 1 (by rfl) ⟨875270, by rfl⟩ : syracuseStep 1167027 = 1750541) B1750541
theorem B1167043 : Blo 1166400 1167043 := bstep (se 1 (by rfl) ⟨875282, by rfl⟩ : syracuseStep 1167043 = 1750565) B1750565
theorem B1969859 : Blo 1166400 1969859 := bstep (se 1 (by rfl) ⟨1477394, by rfl⟩ : syracuseStep 1969859 = 2954789) B2954789
theorem B2805443 : Blo 1166400 2805443 := bstep (se 1 (by rfl) ⟨2104082, by rfl⟩ : syracuseStep 2805443 = 4208165) B4208165
theorem B4435661 : Blo 1166400 4435661 := bstep (se 3 (by rfl) ⟨831686, by rfl⟩ : syracuseStep 4435661 = 1663373) B1663373
theorem B1167059 : Blo 1166400 1167059 := bstep (se 1 (by rfl) ⟨875294, by rfl⟩ : syracuseStep 1167059 = 1750589) B1750589
theorem B1167075 : Blo 1166400 1167075 := bstep (se 1 (by rfl) ⟨875306, by rfl⟩ : syracuseStep 1167075 = 1750613) B1750613
theorem B8867555 : Blo 1166400 8867555 := bstep (se 1 (by rfl) ⟨6650666, by rfl⟩ : syracuseStep 8867555 = 13301333) B13301333
theorem B1167091 : Blo 1166400 1167091 := bstep (se 1 (by rfl) ⟨875318, by rfl⟩ : syracuseStep 1167091 = 1750637) B1750637
theorem B1167107 : Blo 1166400 1167107 := bstep (se 1 (by rfl) ⟨875330, by rfl⟩ : syracuseStep 1167107 = 1750661) B1750661
theorem B1167123 : Blo 1166400 1167123 := bstep (se 1 (by rfl) ⟨875342, by rfl⟩ : syracuseStep 1167123 = 1750685) B1750685
theorem B1167139 : Blo 1166400 1167139 := bstep (se 1 (by rfl) ⟨875354, by rfl⟩ : syracuseStep 1167139 = 1750709) B1750709
theorem B1167155 : Blo 1166400 1167155 := bstep (se 1 (by rfl) ⟨875366, by rfl⟩ : syracuseStep 1167155 = 1750733) B1750733
theorem B1167171 : Blo 1166400 1167171 := bstep (se 1 (by rfl) ⟨875378, by rfl⟩ : syracuseStep 1167171 = 1750757) B1750757
theorem B1969987 : Blo 1166400 1969987 := bstep (se 1 (by rfl) ⟨1477490, by rfl⟩ : syracuseStep 1969987 = 2954981) B2954981
theorem B1167187 : Blo 1166400 1167187 := bstep (se 1 (by rfl) ⟨875390, by rfl⟩ : syracuseStep 1167187 = 1750781) B1750781
theorem B1167203 : Blo 1166400 1167203 := bstep (se 1 (by rfl) ⟨875402, by rfl⟩ : syracuseStep 1167203 = 1750805) B1750805
theorem B2805617 : Blo 1166400 2805617 := bstep (se 2 (by rfl) ⟨1052106, by rfl⟩ : syracuseStep 2805617 = 2104213) B2104213
theorem B1167219 : Blo 1166400 1167219 := bstep (se 1 (by rfl) ⟨875414, by rfl⟩ : syracuseStep 1167219 = 1750829) B1750829
theorem B2215811 : Blo 1166400 2215811 := bstep (se 1 (by rfl) ⟨1661858, by rfl⟩ : syracuseStep 2215811 = 3323717) B3323717
theorem B1167235 : Blo 1166400 1167235 := bstep (se 1 (by rfl) ⟨875426, by rfl⟩ : syracuseStep 1167235 = 1750853) B1750853
theorem B2625425 : Blo 1166400 2625425 := bstep (se 2 (by rfl) ⟨984534, by rfl⟩ : syracuseStep 2625425 = 1969069) B1969069
theorem B1167251 : Blo 1166400 1167251 := bstep (se 1 (by rfl) ⟨875438, by rfl⟩ : syracuseStep 1167251 = 1750877) B1750877
theorem B2625443 : Blo 1166400 2625443 := bstep (se 1 (by rfl) ⟨1969082, by rfl⟩ : syracuseStep 2625443 = 3938165) B3938165
theorem B1167267 : Blo 1166400 1167267 := bstep (se 1 (by rfl) ⟨875450, by rfl⟩ : syracuseStep 1167267 = 1750901) B1750901
theorem B3739565 : Blo 1166400 3739565 := bstep (se 3 (by rfl) ⟨701168, by rfl⟩ : syracuseStep 3739565 = 1402337) B1402337
theorem B1167283 : Blo 1166400 1167283 := bstep (se 1 (by rfl) ⟨875462, by rfl⟩ : syracuseStep 1167283 = 1750925) B1750925
theorem B1167299 : Blo 1166400 1167299 := bstep (se 1 (by rfl) ⟨875474, by rfl⟩ : syracuseStep 1167299 = 1750949) B1750949
theorem B2953169 : Blo 1166400 2953169 := bstep (se 2 (by rfl) ⟨1107438, by rfl⟩ : syracuseStep 2953169 = 2214877) B2214877
theorem B1970129 : Blo 1166400 1970129 := bstep (se 2 (by rfl) ⟨738798, by rfl⟩ : syracuseStep 1970129 = 1477597) B1477597
theorem B1167315 : Blo 1166400 1167315 := bstep (se 1 (by rfl) ⟨875486, by rfl⟩ : syracuseStep 1167315 = 1750973) B1750973
theorem B1167331 : Blo 1166400 1167331 := bstep (se 1 (by rfl) ⟨875498, by rfl⟩ : syracuseStep 1167331 = 1750997) B1750997
theorem B1167347 : Blo 1166400 1167347 := bstep (se 1 (by rfl) ⟨875510, by rfl⟩ : syracuseStep 1167347 = 1751021) B1751021
theorem B2953219 : Blo 1166400 2953219 := bstep (se 1 (by rfl) ⟨2214914, by rfl⟩ : syracuseStep 2953219 = 4429829) B4429829
theorem B1167363 : Blo 1166400 1167363 := bstep (se 1 (by rfl) ⟨875522, by rfl⟩ : syracuseStep 1167363 = 1751045) B1751045
theorem B1167379 : Blo 1166400 1167379 := bstep (se 1 (by rfl) ⟨875534, by rfl⟩ : syracuseStep 1167379 = 1751069) B1751069
theorem B1478675 : Blo 1166400 1478675 := bstep (se 1 (by rfl) ⟨1109006, by rfl⟩ : syracuseStep 1478675 = 2218013) B2218013
theorem B2527267 : Blo 1166400 2527267 := bstep (se 1 (by rfl) ⟨1895450, by rfl⟩ : syracuseStep 2527267 = 3790901) B3790901
theorem B1167395 : Blo 1166400 1167395 := bstep (se 1 (by rfl) ⟨875546, by rfl⟩ : syracuseStep 1167395 = 1751093) B1751093
theorem B2494513 : Blo 1166400 2494513 := bstep (se 2 (by rfl) ⟨935442, by rfl⟩ : syracuseStep 2494513 = 1870885) B1870885
theorem B1167411 : Blo 1166400 1167411 := bstep (se 1 (by rfl) ⟨875558, by rfl⟩ : syracuseStep 1167411 = 1751117) B1751117
theorem B1167427 : Blo 1166400 1167427 := bstep (se 1 (by rfl) ⟨875570, by rfl⟩ : syracuseStep 1167427 = 1751141) B1751141
theorem B1970257 : Blo 1166400 1970257 := bstep (se 2 (by rfl) ⟨738846, by rfl⟩ : syracuseStep 1970257 = 1477693) B1477693
theorem B1167443 : Blo 1166400 1167443 := bstep (se 1 (by rfl) ⟨875582, by rfl⟩ : syracuseStep 1167443 = 1751165) B1751165
theorem B1167459 : Blo 1166400 1167459 := bstep (se 1 (by rfl) ⟨875594, by rfl⟩ : syracuseStep 1167459 = 1751189) B1751189
theorem B1167475 : Blo 1166400 1167475 := bstep (se 1 (by rfl) ⟨875606, by rfl⟩ : syracuseStep 1167475 = 1751213) B1751213
theorem B1970291 : Blo 1166400 1970291 := bstep (se 1 (by rfl) ⟨1477718, by rfl⟩ : syracuseStep 1970291 = 2955437) B2955437
theorem B1577089 : Blo 1166400 1577089 := bstep (se 2 (by rfl) ⟨591408, by rfl⟩ : syracuseStep 1577089 = 1182817) B1182817
theorem B1167491 : Blo 1166400 1167491 := bstep (se 1 (by rfl) ⟨875618, by rfl⟩ : syracuseStep 1167491 = 1751237) B1751237
theorem B7983245 : Blo 1166400 7983245 := bstep (se 3 (by rfl) ⟨1496858, by rfl⟩ : syracuseStep 7983245 = 2993717) B2993717
theorem B29905037 : Blo 1166400 29905037 := bstep (se 3 (by rfl) ⟨5607194, by rfl⟩ : syracuseStep 29905037 = 11214389) B11214389
theorem B2953361 : Blo 1166400 2953361 := bstep (se 2 (by rfl) ⟨1107510, by rfl⟩ : syracuseStep 2953361 = 2215021) B2215021
theorem B6312077 : Blo 1166400 6312077 := bstep (se 3 (by rfl) ⟨1183514, by rfl⟩ : syracuseStep 6312077 = 2367029) B2367029
theorem B1167507 : Blo 1166400 1167507 := bstep (se 1 (by rfl) ⟨875630, by rfl⟩ : syracuseStep 1167507 = 1751261) B1751261
theorem B2216099 : Blo 1166400 2216099 := bstep (se 1 (by rfl) ⟨1662074, by rfl⟩ : syracuseStep 2216099 = 3324149) B3324149
theorem B1167523 : Blo 1166400 1167523 := bstep (se 1 (by rfl) ⟨875642, by rfl⟩ : syracuseStep 1167523 = 1751285) B1751285
theorem B2625713 : Blo 1166400 2625713 := bstep (se 2 (by rfl) ⟨984642, by rfl⟩ : syracuseStep 2625713 = 1969285) B1969285
theorem B1167539 : Blo 1166400 1167539 := bstep (se 1 (by rfl) ⟨875654, by rfl⟩ : syracuseStep 1167539 = 1751309) B1751309
theorem B2625731 : Blo 1166400 2625731 := bstep (se 1 (by rfl) ⟨1969298, by rfl⟩ : syracuseStep 2625731 = 3938597) B3938597
theorem B1167555 : Blo 1166400 1167555 := bstep (se 1 (by rfl) ⟨875666, by rfl⟩ : syracuseStep 1167555 = 1751333) B1751333
theorem B1167571 : Blo 1166400 1167571 := bstep (se 1 (by rfl) ⟨875678, by rfl⟩ : syracuseStep 1167571 = 1751357) B1751357
theorem B1167587 : Blo 1166400 1167587 := bstep (se 1 (by rfl) ⟨875690, by rfl⟩ : syracuseStep 1167587 = 1751381) B1751381
theorem B1167603 : Blo 1166400 1167603 := bstep (se 1 (by rfl) ⟨875702, by rfl⟩ : syracuseStep 1167603 = 1751405) B1751405
theorem B1970419 : Blo 1166400 1970419 := bstep (se 1 (by rfl) ⟨1477814, by rfl⟩ : syracuseStep 1970419 = 2955629) B2955629
theorem B1167619 : Blo 1166400 1167619 := bstep (se 1 (by rfl) ⟨875714, by rfl⟩ : syracuseStep 1167619 = 1751429) B1751429
theorem B1167635 : Blo 1166400 1167635 := bstep (se 1 (by rfl) ⟨875726, by rfl⟩ : syracuseStep 1167635 = 1751453) B1751453
theorem B1167651 : Blo 1166400 1167651 := bstep (se 1 (by rfl) ⟨875738, by rfl⟩ : syracuseStep 1167651 = 1751477) B1751477
theorem B1167667 : Blo 1166400 1167667 := bstep (se 1 (by rfl) ⟨875750, by rfl⟩ : syracuseStep 1167667 = 1751501) B1751501
theorem B2994499 : Blo 1166400 2994499 := bstep (se 1 (by rfl) ⟨2245874, by rfl⟩ : syracuseStep 2994499 = 4491749) B4491749
theorem B1167683 : Blo 1166400 1167683 := bstep (se 1 (by rfl) ⟨875762, by rfl⟩ : syracuseStep 1167683 = 1751525) B1751525
theorem B4985165 : Blo 1166400 4985165 := bstep (se 3 (by rfl) ⟨934718, by rfl⟩ : syracuseStep 4985165 = 1869437) B1869437
theorem B1167699 : Blo 1166400 1167699 := bstep (se 1 (by rfl) ⟨875774, by rfl⟩ : syracuseStep 1167699 = 1751549) B1751549
theorem B3740003 : Blo 1166400 3740003 := bstep (se 1 (by rfl) ⟨2805002, by rfl⟩ : syracuseStep 3740003 = 5610005) B5610005
theorem B1167715 : Blo 1166400 1167715 := bstep (se 1 (by rfl) ⟨875786, by rfl⟩ : syracuseStep 1167715 = 1751573) B1751573
theorem B1167731 : Blo 1166400 1167731 := bstep (se 1 (by rfl) ⟨875798, by rfl⟩ : syracuseStep 1167731 = 1751597) B1751597
theorem B1970561 : Blo 1166400 1970561 := bstep (se 2 (by rfl) ⟨738960, by rfl⟩ : syracuseStep 1970561 = 1477921) B1477921
theorem B1167747 : Blo 1166400 1167747 := bstep (se 1 (by rfl) ⟨875810, by rfl⟩ : syracuseStep 1167747 = 1751621) B1751621
theorem B3936653 : Blo 1166400 3936653 := bstep (se 3 (by rfl) ⟨738122, by rfl⟩ : syracuseStep 3936653 = 1476245) B1476245
theorem B1167763 : Blo 1166400 1167763 := bstep (se 1 (by rfl) ⟨875822, by rfl⟩ : syracuseStep 1167763 = 1751645) B1751645
theorem B1167779 : Blo 1166400 1167779 := bstep (se 1 (by rfl) ⟨875834, by rfl⟩ : syracuseStep 1167779 = 1751669) B1751669
theorem B1167795 : Blo 1166400 1167795 := bstep (se 1 (by rfl) ⟨875846, by rfl⟩ : syracuseStep 1167795 = 1751693) B1751693
theorem B3936707 : Blo 1166400 3936707 := bstep (se 1 (by rfl) ⟨2952530, by rfl⟩ : syracuseStep 3936707 = 5905061) B5905061
theorem B1167811 : Blo 1166400 1167811 := bstep (se 1 (by rfl) ⟨875858, by rfl⟩ : syracuseStep 1167811 = 1751717) B1751717
theorem B12612037 : Blo 1166400 12612037 := bstep (se 4 (by rfl) ⟨1182378, by rfl⟩ : syracuseStep 12612037 = 2364757) B2364757
theorem B22434245 : Blo 1166400 22434245 := bstep (se 4 (by rfl) ⟨2103210, by rfl⟩ : syracuseStep 22434245 = 4206421) B4206421
theorem B2626001 : Blo 1166400 2626001 := bstep (se 2 (by rfl) ⟨984750, by rfl⟩ : syracuseStep 2626001 = 1969501) B1969501
theorem B1167827 : Blo 1166400 1167827 := bstep (se 1 (by rfl) ⟨875870, by rfl⟩ : syracuseStep 1167827 = 1751741) B1751741
theorem B2626019 : Blo 1166400 2626019 := bstep (se 1 (by rfl) ⟨1969514, by rfl⟩ : syracuseStep 2626019 = 3939029) B3939029
theorem B1167843 : Blo 1166400 1167843 := bstep (se 1 (by rfl) ⟨875882, by rfl⟩ : syracuseStep 1167843 = 1751765) B1751765
theorem B1167859 : Blo 1166400 1167859 := bstep (se 1 (by rfl) ⟨875894, by rfl⟩ : syracuseStep 1167859 = 1751789) B1751789
theorem B1970689 : Blo 1166400 1970689 := bstep (se 2 (by rfl) ⟨739008, by rfl⟩ : syracuseStep 1970689 = 1478017) B1478017
theorem B1167875 : Blo 1166400 1167875 := bstep (se 1 (by rfl) ⟨875906, by rfl⟩ : syracuseStep 1167875 = 1751813) B1751813
theorem B1167891 : Blo 1166400 1167891 := bstep (se 1 (by rfl) ⟨875918, by rfl⟩ : syracuseStep 1167891 = 1751837) B1751837
theorem B1970723 : Blo 1166400 1970723 := bstep (se 1 (by rfl) ⟨1478042, by rfl⟩ : syracuseStep 1970723 = 2956085) B2956085
theorem B1167907 : Blo 1166400 1167907 := bstep (se 1 (by rfl) ⟨875930, by rfl⟩ : syracuseStep 1167907 = 1751861) B1751861
theorem B1167923 : Blo 1166400 1167923 := bstep (se 1 (by rfl) ⟨875942, by rfl⟩ : syracuseStep 1167923 = 1751885) B1751885
theorem B1167939 : Blo 1166400 1167939 := bstep (se 1 (by rfl) ⟨875954, by rfl⟩ : syracuseStep 1167939 = 1751909) B1751909
theorem B6648389 : Blo 1166400 6648389 := bstep (se 4 (by rfl) ⟨623286, by rfl⟩ : syracuseStep 6648389 = 1246573) B1246573
theorem B1167955 : Blo 1166400 1167955 := bstep (se 1 (by rfl) ⟨875966, by rfl⟩ : syracuseStep 1167955 = 1751933) B1751933
theorem B1167971 : Blo 1166400 1167971 := bstep (se 1 (by rfl) ⟨875978, by rfl⟩ : syracuseStep 1167971 = 1751957) B1751957
theorem B1749617 : Blo 1166400 1749617 := bstep (se 2 (by rfl) ⟨656106, by rfl⟩ : syracuseStep 1749617 = 1312213) B1312213
theorem B1167987 : Blo 1166400 1167987 := bstep (se 1 (by rfl) ⟨875990, by rfl⟩ : syracuseStep 1167987 = 1751981) B1751981
theorem B1749635 : Blo 1166400 1749635 := bstep (se 1 (by rfl) ⟨1312226, by rfl⟩ : syracuseStep 1749635 = 2624453) B2624453
theorem B1168003 : Blo 1166400 1168003 := bstep (se 1 (by rfl) ⟨876002, by rfl⟩ : syracuseStep 1168003 = 1752005) B1752005
theorem B1168019 : Blo 1166400 1168019 := bstep (se 1 (by rfl) ⟨876014, by rfl⟩ : syracuseStep 1168019 = 1752029) B1752029
theorem B1749665 : Blo 1166400 1749665 := bstep (se 2 (by rfl) ⟨656124, by rfl⟩ : syracuseStep 1749665 = 1312249) B1312249
theorem B1970851 : Blo 1166400 1970851 := bstep (se 1 (by rfl) ⟨1478138, by rfl⟩ : syracuseStep 1970851 = 2956277) B2956277
theorem B1168035 : Blo 1166400 1168035 := bstep (se 1 (by rfl) ⟨876026, by rfl⟩ : syracuseStep 1168035 = 1752053) B1752053
theorem B5911217 : Blo 1166400 5911217 := bstep (se 2 (by rfl) ⟨2216706, by rfl⟩ : syracuseStep 5911217 = 4433413) B4433413
theorem B1749683 : Blo 1166400 1749683 := bstep (se 1 (by rfl) ⟨1312262, by rfl⟩ : syracuseStep 1749683 = 2624525) B2624525
theorem B1168051 : Blo 1166400 1168051 := bstep (se 1 (by rfl) ⟨876038, by rfl⟩ : syracuseStep 1168051 = 1752077) B1752077
theorem B1168067 : Blo 1166400 1168067 := bstep (se 1 (by rfl) ⟨876050, by rfl⟩ : syracuseStep 1168067 = 1752101) B1752101
theorem B1749713 : Blo 1166400 1749713 := bstep (se 2 (by rfl) ⟨656142, by rfl⟩ : syracuseStep 1749713 = 1312285) B1312285
theorem B3936977 : Blo 1166400 3936977 := bstep (se 2 (by rfl) ⟨1476366, by rfl⟩ : syracuseStep 3936977 = 2952733) B2952733
theorem B1168083 : Blo 1166400 1168083 := bstep (se 1 (by rfl) ⟨876062, by rfl⟩ : syracuseStep 1168083 = 1752125) B1752125
theorem B1749731 : Blo 1166400 1749731 := bstep (se 1 (by rfl) ⟨1312298, by rfl⟩ : syracuseStep 1749731 = 2624597) B2624597
theorem B1168099 : Blo 1166400 1168099 := bstep (se 1 (by rfl) ⟨876074, by rfl⟩ : syracuseStep 1168099 = 1752149) B1752149
theorem B2626289 : Blo 1166400 2626289 := bstep (se 2 (by rfl) ⟨984858, by rfl⟩ : syracuseStep 2626289 = 1969717) B1969717
theorem B1168115 : Blo 1166400 1168115 := bstep (se 1 (by rfl) ⟨876086, by rfl⟩ : syracuseStep 1168115 = 1752173) B1752173
theorem B1749761 : Blo 1166400 1749761 := bstep (se 2 (by rfl) ⟨656160, by rfl⟩ : syracuseStep 1749761 = 1312321) B1312321
theorem B2626307 : Blo 1166400 2626307 := bstep (se 1 (by rfl) ⟨1969730, by rfl⟩ : syracuseStep 2626307 = 3939461) B3939461
theorem B1168131 : Blo 1166400 1168131 := bstep (se 1 (by rfl) ⟨876098, by rfl⟩ : syracuseStep 1168131 = 1752197) B1752197
theorem B1749779 : Blo 1166400 1749779 := bstep (se 1 (by rfl) ⟨1312334, by rfl⟩ : syracuseStep 1749779 = 2624669) B2624669
theorem B1684243 : Blo 1166400 1684243 := bstep (se 1 (by rfl) ⟨1263182, by rfl⟩ : syracuseStep 1684243 = 2526365) B2526365
theorem B1168147 : Blo 1166400 1168147 := bstep (se 1 (by rfl) ⟨876110, by rfl⟩ : syracuseStep 1168147 = 1752221) B1752221
theorem B1168163 : Blo 1166400 1168163 := bstep (se 1 (by rfl) ⟨876122, by rfl⟩ : syracuseStep 1168163 = 1752245) B1752245
theorem B1749809 : Blo 1166400 1749809 := bstep (se 2 (by rfl) ⟨656178, by rfl⟩ : syracuseStep 1749809 = 1312357) B1312357
theorem B1970993 : Blo 1166400 1970993 := bstep (se 2 (by rfl) ⟨739122, by rfl⟩ : syracuseStep 1970993 = 1478245) B1478245
theorem B1168179 : Blo 1166400 1168179 := bstep (se 1 (by rfl) ⟨876134, by rfl⟩ : syracuseStep 1168179 = 1752269) B1752269
theorem B1749827 : Blo 1166400 1749827 := bstep (se 1 (by rfl) ⟨1312370, by rfl⟩ : syracuseStep 1749827 = 2624741) B2624741
theorem B3322691 : Blo 1166400 3322691 := bstep (se 1 (by rfl) ⟨2492018, by rfl⟩ : syracuseStep 3322691 = 4984037) B4984037
theorem B1168195 : Blo 1166400 1168195 := bstep (se 1 (by rfl) ⟨876146, by rfl⟩ : syracuseStep 1168195 = 1752293) B1752293
theorem B2495299 : Blo 1166400 2495299 := bstep (se 1 (by rfl) ⟨1871474, by rfl⟩ : syracuseStep 2495299 = 3742949) B3742949
theorem B1168211 : Blo 1166400 1168211 := bstep (se 1 (by rfl) ⟨876158, by rfl⟩ : syracuseStep 1168211 = 1752317) B1752317
theorem B1749857 : Blo 1166400 1749857 := bstep (se 2 (by rfl) ⟨656196, by rfl⟩ : syracuseStep 1749857 = 1312393) B1312393
theorem B3199843 : Blo 1166400 3199843 := bstep (se 1 (by rfl) ⟨2399882, by rfl⟩ : syracuseStep 3199843 = 4799765) B4799765
theorem B1168227 : Blo 1166400 1168227 := bstep (se 1 (by rfl) ⟨876170, by rfl⟩ : syracuseStep 1168227 = 1752341) B1752341
theorem B2052977 : Blo 1166400 2052977 := bstep (se 2 (by rfl) ⟨769866, by rfl⟩ : syracuseStep 2052977 = 1539733) B1539733
theorem B1749875 : Blo 1166400 1749875 := bstep (se 1 (by rfl) ⟨1312406, by rfl⟩ : syracuseStep 1749875 = 2624813) B2624813
theorem B1168243 : Blo 1166400 1168243 := bstep (se 1 (by rfl) ⟨876182, by rfl⟩ : syracuseStep 1168243 = 1752365) B1752365
theorem B1168259 : Blo 1166400 1168259 := bstep (se 1 (by rfl) ⟨876194, by rfl⟩ : syracuseStep 1168259 = 1752389) B1752389
theorem B1749905 : Blo 1166400 1749905 := bstep (se 2 (by rfl) ⟨656214, by rfl⟩ : syracuseStep 1749905 = 1312429) B1312429
theorem B1168275 : Blo 1166400 1168275 := bstep (se 1 (by rfl) ⟨876206, by rfl⟩ : syracuseStep 1168275 = 1752413) B1752413
theorem B1749923 : Blo 1166400 1749923 := bstep (se 1 (by rfl) ⟨1312442, by rfl⟩ : syracuseStep 1749923 = 2624885) B2624885
theorem B1168291 : Blo 1166400 1168291 := bstep (se 1 (by rfl) ⟨876218, by rfl⟩ : syracuseStep 1168291 = 1752437) B1752437
theorem B1971121 : Blo 1166400 1971121 := bstep (se 2 (by rfl) ⟨739170, by rfl⟩ : syracuseStep 1971121 = 1478341) B1478341
theorem B1168307 : Blo 1166400 1168307 := bstep (se 1 (by rfl) ⟨876230, by rfl⟩ : syracuseStep 1168307 = 1752461) B1752461
theorem B1749953 : Blo 1166400 1749953 := bstep (se 2 (by rfl) ⟨656232, by rfl⟩ : syracuseStep 1749953 = 1312465) B1312465
theorem B1168323 : Blo 1166400 1168323 := bstep (se 1 (by rfl) ⟨876242, by rfl⟩ : syracuseStep 1168323 = 1752485) B1752485
theorem B1749971 : Blo 1166400 1749971 := bstep (se 1 (by rfl) ⟨1312478, by rfl⟩ : syracuseStep 1749971 = 2624957) B2624957
theorem B1971155 : Blo 1166400 1971155 := bstep (se 1 (by rfl) ⟨1478366, by rfl⟩ : syracuseStep 1971155 = 2956733) B2956733
theorem B1168339 : Blo 1166400 1168339 := bstep (se 1 (by rfl) ⟨876254, by rfl⟩ : syracuseStep 1168339 = 1752509) B1752509
theorem B1168355 : Blo 1166400 1168355 := bstep (se 1 (by rfl) ⟨876266, by rfl⟩ : syracuseStep 1168355 = 1752533) B1752533
theorem B1750001 : Blo 1166400 1750001 := bstep (se 2 (by rfl) ⟨656250, by rfl⟩ : syracuseStep 1750001 = 1312501) B1312501
theorem B1168371 : Blo 1166400 1168371 := bstep (se 1 (by rfl) ⟨876278, by rfl⟩ : syracuseStep 1168371 = 1752557) B1752557
theorem B1750019 : Blo 1166400 1750019 := bstep (se 1 (by rfl) ⟨1312514, by rfl⟩ : syracuseStep 1750019 = 2625029) B2625029
theorem B1168387 : Blo 1166400 1168387 := bstep (se 1 (by rfl) ⟨876290, by rfl⟩ : syracuseStep 1168387 = 1752581) B1752581
theorem B2626577 : Blo 1166400 2626577 := bstep (se 2 (by rfl) ⟨984966, by rfl⟩ : syracuseStep 2626577 = 1969933) B1969933
theorem B1750049 : Blo 1166400 1750049 := bstep (se 2 (by rfl) ⟨656268, by rfl⟩ : syracuseStep 1750049 = 1312537) B1312537
theorem B2626595 : Blo 1166400 2626595 := bstep (se 1 (by rfl) ⟨1969946, by rfl⟩ : syracuseStep 2626595 = 3939893) B3939893
theorem B1750067 : Blo 1166400 1750067 := bstep (se 1 (by rfl) ⟨1312550, by rfl⟩ : syracuseStep 1750067 = 2625101) B2625101
theorem B2397251 : Blo 1166400 2397251 := bstep (se 1 (by rfl) ⟨1797938, by rfl⟩ : syracuseStep 2397251 = 3595877) B3595877
theorem B1750097 : Blo 1166400 1750097 := bstep (se 2 (by rfl) ⟨656286, by rfl⟩ : syracuseStep 1750097 = 1312573) B1312573
theorem B2217041 : Blo 1166400 2217041 := bstep (se 2 (by rfl) ⟨831390, by rfl⟩ : syracuseStep 2217041 = 1662781) B1662781
theorem B1971283 : Blo 1166400 1971283 := bstep (se 1 (by rfl) ⟨1478462, by rfl⟩ : syracuseStep 1971283 = 2956925) B2956925
theorem B1750115 : Blo 1166400 1750115 := bstep (se 1 (by rfl) ⟨1312586, by rfl⟩ : syracuseStep 1750115 = 2625173) B2625173
theorem B1684579 : Blo 1166400 1684579 := bstep (se 1 (by rfl) ⟨1263434, by rfl⟩ : syracuseStep 1684579 = 2526869) B2526869
theorem B2954353 : Blo 1166400 2954353 := bstep (se 2 (by rfl) ⟨1107882, by rfl⟩ : syracuseStep 2954353 = 2215765) B2215765
theorem B1750145 : Blo 1166400 1750145 := bstep (se 2 (by rfl) ⟨656304, by rfl⟩ : syracuseStep 1750145 = 1312609) B1312609
theorem B1750163 : Blo 1166400 1750163 := bstep (se 1 (by rfl) ⟨1312622, by rfl⟩ : syracuseStep 1750163 = 2625245) B2625245
theorem B1750193 : Blo 1166400 1750193 := bstep (se 2 (by rfl) ⟨656322, by rfl⟩ : syracuseStep 1750193 = 1312645) B1312645
theorem B1750211 : Blo 1166400 1750211 := bstep (se 1 (by rfl) ⟨1312658, by rfl⟩ : syracuseStep 1750211 = 2625317) B2625317
theorem B4732109 : Blo 1166400 4732109 := bstep (se 3 (by rfl) ⟨887270, by rfl⟩ : syracuseStep 4732109 = 1774541) B1774541
theorem B1750241 : Blo 1166400 1750241 := bstep (se 2 (by rfl) ⟨656340, by rfl⟩ : syracuseStep 1750241 = 1312681) B1312681
theorem B1971425 : Blo 1166400 1971425 := bstep (se 2 (by rfl) ⟨739284, by rfl⟩ : syracuseStep 1971425 = 1478569) B1478569
theorem B3937517 : Blo 1166400 3937517 := bstep (se 3 (by rfl) ⟨738284, by rfl⟩ : syracuseStep 3937517 = 1476569) B1476569
theorem B6649073 : Blo 1166400 6649073 := bstep (se 2 (by rfl) ⟨2493402, by rfl⟩ : syracuseStep 6649073 = 4986805) B4986805
theorem B1750259 : Blo 1166400 1750259 := bstep (se 1 (by rfl) ⟨1312694, by rfl⟩ : syracuseStep 1750259 = 2625389) B2625389
theorem B1750289 : Blo 1166400 1750289 := bstep (se 2 (by rfl) ⟨656358, by rfl⟩ : syracuseStep 1750289 = 1312717) B1312717
theorem B3937571 : Blo 1166400 3937571 := bstep (se 1 (by rfl) ⟨2953178, by rfl⟩ : syracuseStep 3937571 = 5906357) B5906357
theorem B5322019 : Blo 1166400 5322019 := bstep (se 1 (by rfl) ⟨3991514, by rfl⟩ : syracuseStep 5322019 = 7983029) B7983029
theorem B1750307 : Blo 1166400 1750307 := bstep (se 1 (by rfl) ⟨1312730, by rfl⟩ : syracuseStep 1750307 = 2625461) B2625461
theorem B2626865 : Blo 1166400 2626865 := bstep (se 2 (by rfl) ⟨985074, by rfl⟩ : syracuseStep 2626865 = 1970149) B1970149
theorem B1750337 : Blo 1166400 1750337 := bstep (se 2 (by rfl) ⟨656376, by rfl⟩ : syracuseStep 1750337 = 1312753) B1312753
theorem B2626883 : Blo 1166400 2626883 := bstep (se 1 (by rfl) ⟨1970162, by rfl⟩ : syracuseStep 2626883 = 3940325) B3940325
theorem B1750355 : Blo 1166400 1750355 := bstep (se 1 (by rfl) ⟨1312766, by rfl⟩ : syracuseStep 1750355 = 2625533) B2625533
theorem B1971553 : Blo 1166400 1971553 := bstep (se 2 (by rfl) ⟨739332, by rfl⟩ : syracuseStep 1971553 = 1478665) B1478665
theorem B1750385 : Blo 1166400 1750385 := bstep (se 2 (by rfl) ⟨656394, by rfl⟩ : syracuseStep 1750385 = 1312789) B1312789
theorem B1750403 : Blo 1166400 1750403 := bstep (se 1 (by rfl) ⟨1312802, by rfl⟩ : syracuseStep 1750403 = 2625605) B2625605
theorem B2954627 : Blo 1166400 2954627 := bstep (se 1 (by rfl) ⟨2215970, by rfl⟩ : syracuseStep 2954627 = 4431941) B4431941
theorem B1971587 : Blo 1166400 1971587 := bstep (se 1 (by rfl) ⟨1478690, by rfl⟩ : syracuseStep 1971587 = 2957381) B2957381
theorem B1750433 : Blo 1166400 1750433 := bstep (se 2 (by rfl) ⟨656412, by rfl⟩ : syracuseStep 1750433 = 1312825) B1312825
theorem B1750451 : Blo 1166400 1750451 := bstep (se 1 (by rfl) ⟨1312838, by rfl⟩ : syracuseStep 1750451 = 2625677) B2625677
theorem B14382517 : Blo 1166400 14382517 := bstep (se 5 (by rfl) ⟨674180, by rfl⟩ : syracuseStep 14382517 = 1348361) B1348361
theorem B1750481 : Blo 1166400 1750481 := bstep (se 2 (by rfl) ⟨656430, by rfl⟩ : syracuseStep 1750481 = 1312861) B1312861
theorem B1750499 : Blo 1166400 1750499 := bstep (se 1 (by rfl) ⟨1312874, by rfl⟩ : syracuseStep 1750499 = 2625749) B2625749
theorem B1750529 : Blo 1166400 1750529 := bstep (se 2 (by rfl) ⟨656448, by rfl⟩ : syracuseStep 1750529 = 1312897) B1312897
theorem B1750547 : Blo 1166400 1750547 := bstep (se 1 (by rfl) ⟨1312910, by rfl⟩ : syracuseStep 1750547 = 2625821) B2625821
theorem B3937841 : Blo 1166400 3937841 := bstep (se 2 (by rfl) ⟨1476690, by rfl⟩ : syracuseStep 3937841 = 2953381) B2953381
theorem B1750577 : Blo 1166400 1750577 := bstep (se 2 (by rfl) ⟨656466, by rfl⟩ : syracuseStep 1750577 = 1312933) B1312933
theorem B1750595 : Blo 1166400 1750595 := bstep (se 1 (by rfl) ⟨1312946, by rfl⟩ : syracuseStep 1750595 = 2625893) B2625893
theorem B2954819 : Blo 1166400 2954819 := bstep (se 1 (by rfl) ⟨2216114, by rfl⟩ : syracuseStep 2954819 = 4432229) B4432229
theorem B2627153 : Blo 1166400 2627153 := bstep (se 2 (by rfl) ⟨985182, by rfl⟩ : syracuseStep 2627153 = 1970365) B1970365
theorem B1750625 : Blo 1166400 1750625 := bstep (se 2 (by rfl) ⟨656484, by rfl⟩ : syracuseStep 1750625 = 1312969) B1312969
theorem B1496675 : Blo 1166400 1496675 := bstep (se 1 (by rfl) ⟨1122506, by rfl⟩ : syracuseStep 1496675 = 2245013) B2245013
theorem B2627171 : Blo 1166400 2627171 := bstep (se 1 (by rfl) ⟨1970378, by rfl⟩ : syracuseStep 2627171 = 3940757) B3940757
theorem B3323501 : Blo 1166400 3323501 := bstep (se 3 (by rfl) ⟨623156, by rfl⟩ : syracuseStep 3323501 = 1246313) B1246313
theorem B4986481 : Blo 1166400 4986481 := bstep (se 2 (by rfl) ⟨1869930, by rfl⟩ : syracuseStep 4986481 = 3739861) B3739861
theorem B1750643 : Blo 1166400 1750643 := bstep (se 1 (by rfl) ⟨1312982, by rfl⟩ : syracuseStep 1750643 = 2625965) B2625965
theorem B1750673 : Blo 1166400 1750673 := bstep (se 2 (by rfl) ⟨656502, by rfl⟩ : syracuseStep 1750673 = 1313005) B1313005
theorem B1750691 : Blo 1166400 1750691 := bstep (se 1 (by rfl) ⟨1313018, by rfl⟩ : syracuseStep 1750691 = 2626037) B2626037
theorem B1750721 : Blo 1166400 1750721 := bstep (se 2 (by rfl) ⟨656520, by rfl⟩ : syracuseStep 1750721 = 1313041) B1313041
theorem B3995345 : Blo 1166400 3995345 := bstep (se 2 (by rfl) ⟨1498254, by rfl⟩ : syracuseStep 3995345 = 2996509) B2996509
theorem B1750739 : Blo 1166400 1750739 := bstep (se 1 (by rfl) ⟨1313054, by rfl⟩ : syracuseStep 1750739 = 2626109) B2626109
theorem B1750769 : Blo 1166400 1750769 := bstep (se 2 (by rfl) ⟨656538, by rfl⟩ : syracuseStep 1750769 = 1313077) B1313077
theorem B1750787 : Blo 1166400 1750787 := bstep (se 1 (by rfl) ⟨1313090, by rfl⟩ : syracuseStep 1750787 = 2626181) B2626181
theorem B1775363 : Blo 1166400 1775363 := bstep (se 1 (by rfl) ⟨1331522, by rfl⟩ : syracuseStep 1775363 = 2663045) B2663045
theorem B1750817 : Blo 1166400 1750817 := bstep (se 2 (by rfl) ⟨656556, by rfl⟩ : syracuseStep 1750817 = 1313113) B1313113
theorem B3323693 : Blo 1166400 3323693 := bstep (se 3 (by rfl) ⟨623192, by rfl⟩ : syracuseStep 3323693 = 1246385) B1246385
theorem B1750835 : Blo 1166400 1750835 := bstep (se 1 (by rfl) ⟨1313126, by rfl⟩ : syracuseStep 1750835 = 2626253) B2626253
theorem B1750865 : Blo 1166400 1750865 := bstep (se 2 (by rfl) ⟨656574, by rfl⟩ : syracuseStep 1750865 = 1313149) B1313149
theorem B1750883 : Blo 1166400 1750883 := bstep (se 1 (by rfl) ⟨1313162, by rfl⟩ : syracuseStep 1750883 = 2626325) B2626325
theorem B2627441 : Blo 1166400 2627441 := bstep (se 2 (by rfl) ⟨985290, by rfl⟩ : syracuseStep 2627441 = 1970581) B1970581
theorem B2529137 : Blo 1166400 2529137 := bstep (se 2 (by rfl) ⟨948426, by rfl⟩ : syracuseStep 2529137 = 1896853) B1896853
theorem B1750913 : Blo 1166400 1750913 := bstep (se 2 (by rfl) ⟨656592, by rfl⟩ : syracuseStep 1750913 = 1313185) B1313185
theorem B2627459 : Blo 1166400 2627459 := bstep (se 1 (by rfl) ⟨1970594, by rfl⟩ : syracuseStep 2627459 = 3941189) B3941189
theorem B1750931 : Blo 1166400 1750931 := bstep (se 1 (by rfl) ⟨1313198, by rfl⟩ : syracuseStep 1750931 = 2626397) B2626397
theorem B2660273 : Blo 1166400 2660273 := bstep (se 2 (by rfl) ⟨997602, by rfl⟩ : syracuseStep 2660273 = 1995205) B1995205
theorem B1750961 : Blo 1166400 1750961 := bstep (se 2 (by rfl) ⟨656610, by rfl⟩ : syracuseStep 1750961 = 1313221) B1313221
theorem B1750979 : Blo 1166400 1750979 := bstep (se 1 (by rfl) ⟨1313234, by rfl⟩ : syracuseStep 1750979 = 2626469) B2626469
theorem B2217937 : Blo 1166400 2217937 := bstep (se 2 (by rfl) ⟨831726, by rfl⟩ : syracuseStep 2217937 = 1663453) B1663453
theorem B1751009 : Blo 1166400 1751009 := bstep (se 2 (by rfl) ⟨656628, by rfl⟩ : syracuseStep 1751009 = 1313257) B1313257
theorem B1751027 : Blo 1166400 1751027 := bstep (se 1 (by rfl) ⟨1313270, by rfl⟩ : syracuseStep 1751027 = 2626541) B2626541
theorem B1751057 : Blo 1166400 1751057 := bstep (se 2 (by rfl) ⟨656646, by rfl⟩ : syracuseStep 1751057 = 1313293) B1313293
theorem B1751075 : Blo 1166400 1751075 := bstep (se 1 (by rfl) ⟨1313306, by rfl⟩ : syracuseStep 1751075 = 2626613) B2626613
theorem B1751105 : Blo 1166400 1751105 := bstep (se 2 (by rfl) ⟨656664, by rfl⟩ : syracuseStep 1751105 = 1313329) B1313329
theorem B3938381 : Blo 1166400 3938381 := bstep (se 3 (by rfl) ⟨738446, by rfl⟩ : syracuseStep 3938381 = 1476893) B1476893
theorem B1751123 : Blo 1166400 1751123 := bstep (se 1 (by rfl) ⟨1313342, by rfl⟩ : syracuseStep 1751123 = 2626685) B2626685
theorem B5912675 : Blo 1166400 5912675 := bstep (se 1 (by rfl) ⟨4434506, by rfl⟩ : syracuseStep 5912675 = 8869013) B8869013
theorem B1751153 : Blo 1166400 1751153 := bstep (se 2 (by rfl) ⟨656682, by rfl⟩ : syracuseStep 1751153 = 1313365) B1313365
theorem B2218097 : Blo 1166400 2218097 := bstep (se 2 (by rfl) ⟨831786, by rfl⟩ : syracuseStep 2218097 = 1663573) B1663573
theorem B3938435 : Blo 1166400 3938435 := bstep (se 1 (by rfl) ⟨2953826, by rfl⟩ : syracuseStep 3938435 = 5907653) B5907653
theorem B1751171 : Blo 1166400 1751171 := bstep (se 1 (by rfl) ⟨1313378, by rfl⟩ : syracuseStep 1751171 = 2626757) B2626757
theorem B2627729 : Blo 1166400 2627729 := bstep (se 2 (by rfl) ⟨985398, by rfl⟩ : syracuseStep 2627729 = 1970797) B1970797
theorem B1751201 : Blo 1166400 1751201 := bstep (se 2 (by rfl) ⟨656700, by rfl⟩ : syracuseStep 1751201 = 1313401) B1313401
theorem B2627747 : Blo 1166400 2627747 := bstep (se 1 (by rfl) ⟨1970810, by rfl⟩ : syracuseStep 2627747 = 3941621) B3941621
theorem B1751219 : Blo 1166400 1751219 := bstep (se 1 (by rfl) ⟨1313414, by rfl⟩ : syracuseStep 1751219 = 2626829) B2626829
theorem B1751249 : Blo 1166400 1751249 := bstep (se 2 (by rfl) ⟨656718, by rfl⟩ : syracuseStep 1751249 = 1313437) B1313437
theorem B1751267 : Blo 1166400 1751267 := bstep (se 1 (by rfl) ⟨1313450, by rfl⟩ : syracuseStep 1751267 = 2626901) B2626901
theorem B3741923 : Blo 1166400 3741923 := bstep (se 1 (by rfl) ⟨2806442, by rfl⟩ : syracuseStep 3741923 = 5612885) B5612885
theorem B1751297 : Blo 1166400 1751297 := bstep (se 2 (by rfl) ⟨656736, by rfl⟩ : syracuseStep 1751297 = 1313473) B1313473
theorem B1751315 : Blo 1166400 1751315 := bstep (se 1 (by rfl) ⟨1313486, by rfl⟩ : syracuseStep 1751315 = 2626973) B2626973
theorem B1751345 : Blo 1166400 1751345 := bstep (se 2 (by rfl) ⟨656754, by rfl⟩ : syracuseStep 1751345 = 1313509) B1313509
theorem B1661249 : Blo 1166400 1661249 := bstep (se 2 (by rfl) ⟨622968, by rfl⟩ : syracuseStep 1661249 = 1245937) B1245937
theorem B1751363 : Blo 1166400 1751363 := bstep (se 1 (by rfl) ⟨1313522, by rfl⟩ : syracuseStep 1751363 = 2627045) B2627045
theorem B1751393 : Blo 1166400 1751393 := bstep (se 2 (by rfl) ⟨656772, by rfl⟩ : syracuseStep 1751393 = 1313545) B1313545
theorem B1751411 : Blo 1166400 1751411 := bstep (se 1 (by rfl) ⟨1313558, by rfl⟩ : syracuseStep 1751411 = 2627117) B2627117
theorem B1497475 : Blo 1166400 1497475 := bstep (se 1 (by rfl) ⟨1123106, by rfl⟩ : syracuseStep 1497475 = 2246213) B2246213
theorem B1776001 : Blo 1166400 1776001 := bstep (se 2 (by rfl) ⟨666000, by rfl⟩ : syracuseStep 1776001 = 1332001) B1332001
theorem B3938705 : Blo 1166400 3938705 := bstep (se 2 (by rfl) ⟨1477014, by rfl⟩ : syracuseStep 3938705 = 2954029) B2954029
theorem B1751441 : Blo 1166400 1751441 := bstep (se 2 (by rfl) ⟨656790, by rfl⟩ : syracuseStep 1751441 = 1313581) B1313581
theorem B1751459 : Blo 1166400 1751459 := bstep (se 1 (by rfl) ⟨1313594, by rfl⟩ : syracuseStep 1751459 = 2627189) B2627189
theorem B2628017 : Blo 1166400 2628017 := bstep (se 2 (by rfl) ⟨985506, by rfl⟩ : syracuseStep 2628017 = 1971013) B1971013
theorem B1751489 : Blo 1166400 1751489 := bstep (se 2 (by rfl) ⟨656808, by rfl⟩ : syracuseStep 1751489 = 1313617) B1313617
theorem B1685953 : Blo 1166400 1685953 := bstep (se 2 (by rfl) ⟨632232, by rfl⟩ : syracuseStep 1685953 = 1264465) B1264465
theorem B2628035 : Blo 1166400 2628035 := bstep (se 1 (by rfl) ⟨1971026, by rfl⟩ : syracuseStep 2628035 = 3942053) B3942053
theorem B4430285 : Blo 1166400 4430285 := bstep (se 3 (by rfl) ⟨830678, by rfl⟩ : syracuseStep 4430285 = 1661357) B1661357
theorem B1751507 : Blo 1166400 1751507 := bstep (se 1 (by rfl) ⟨1313630, by rfl⟩ : syracuseStep 1751507 = 2627261) B2627261
theorem B1751537 : Blo 1166400 1751537 := bstep (se 2 (by rfl) ⟨656826, by rfl⟩ : syracuseStep 1751537 = 1313653) B1313653
theorem B2955761 : Blo 1166400 2955761 := bstep (se 2 (by rfl) ⟨1108410, by rfl⟩ : syracuseStep 2955761 = 2216821) B2216821
theorem B1751555 : Blo 1166400 1751555 := bstep (se 1 (by rfl) ⟨1313666, by rfl⟩ : syracuseStep 1751555 = 2627333) B2627333
theorem B11983373 : Blo 1166400 11983373 := bstep (se 3 (by rfl) ⟨2246882, by rfl⟩ : syracuseStep 11983373 = 4493765) B4493765
theorem B1997345 : Blo 1166400 1997345 := bstep (se 2 (by rfl) ⟨749004, by rfl⟩ : syracuseStep 1997345 = 1498009) B1498009
theorem B1751585 : Blo 1166400 1751585 := bstep (se 2 (by rfl) ⟨656844, by rfl⟩ : syracuseStep 1751585 = 1313689) B1313689
theorem B2955811 : Blo 1166400 2955811 := bstep (se 1 (by rfl) ⟨2216858, by rfl⟩ : syracuseStep 2955811 = 4433717) B4433717
theorem B1751603 : Blo 1166400 1751603 := bstep (se 1 (by rfl) ⟨1313702, by rfl⟩ : syracuseStep 1751603 = 2627405) B2627405
theorem B1751633 : Blo 1166400 1751633 := bstep (se 2 (by rfl) ⟨656862, by rfl⟩ : syracuseStep 1751633 = 1313725) B1313725
theorem B1751651 : Blo 1166400 1751651 := bstep (se 1 (by rfl) ⟨1313738, by rfl⟩ : syracuseStep 1751651 = 2627477) B2627477
theorem B1751681 : Blo 1166400 1751681 := bstep (se 2 (by rfl) ⟨656880, by rfl⟩ : syracuseStep 1751681 = 1313761) B1313761
theorem B1776257 : Blo 1166400 1776257 := bstep (se 2 (by rfl) ⟨666096, by rfl⟩ : syracuseStep 1776257 = 1332193) B1332193
theorem B1751699 : Blo 1166400 1751699 := bstep (se 1 (by rfl) ⟨1313774, by rfl⟩ : syracuseStep 1751699 = 2627549) B2627549
theorem B4733603 : Blo 1166400 4733603 := bstep (se 1 (by rfl) ⟨3550202, by rfl⟩ : syracuseStep 4733603 = 7100405) B7100405
theorem B6650531 : Blo 1166400 6650531 := bstep (se 1 (by rfl) ⟨4987898, by rfl⟩ : syracuseStep 6650531 = 9975797) B9975797
theorem B2955953 : Blo 1166400 2955953 := bstep (se 2 (by rfl) ⟨1108482, by rfl⟩ : syracuseStep 2955953 = 2216965) B2216965
theorem B1751729 : Blo 1166400 1751729 := bstep (se 2 (by rfl) ⟨656898, by rfl⟩ : syracuseStep 1751729 = 1313797) B1313797
theorem B1751747 : Blo 1166400 1751747 := bstep (se 1 (by rfl) ⟨1313810, by rfl⟩ : syracuseStep 1751747 = 2627621) B2627621
theorem B2628305 : Blo 1166400 2628305 := bstep (se 2 (by rfl) ⟨985614, by rfl⟩ : syracuseStep 2628305 = 1971229) B1971229
theorem B1751777 : Blo 1166400 1751777 := bstep (se 2 (by rfl) ⟨656916, by rfl⟩ : syracuseStep 1751777 = 1313833) B1313833
theorem B9976547 : Blo 1166400 9976547 := bstep (se 1 (by rfl) ⟨7482410, by rfl⟩ : syracuseStep 9976547 = 14964821) B14964821
theorem B2628323 : Blo 1166400 2628323 := bstep (se 1 (by rfl) ⟨1971242, by rfl⟩ : syracuseStep 2628323 = 3942485) B3942485
theorem B1751795 : Blo 1166400 1751795 := bstep (se 1 (by rfl) ⟨1313846, by rfl⟩ : syracuseStep 1751795 = 2627693) B2627693
theorem B3324685 : Blo 1166400 3324685 := bstep (se 3 (by rfl) ⟨623378, by rfl⟩ : syracuseStep 3324685 = 1246757) B1246757
theorem B4209421 : Blo 1166400 4209421 := bstep (se 3 (by rfl) ⟨789266, by rfl⟩ : syracuseStep 4209421 = 1578533) B1578533
theorem B1751825 : Blo 1166400 1751825 := bstep (se 2 (by rfl) ⟨656934, by rfl⟩ : syracuseStep 1751825 = 1313869) B1313869
theorem B1751843 : Blo 1166400 1751843 := bstep (se 1 (by rfl) ⟨1313882, by rfl⟩ : syracuseStep 1751843 = 2627765) B2627765
theorem B1751873 : Blo 1166400 1751873 := bstep (se 2 (by rfl) ⟨656952, by rfl⟩ : syracuseStep 1751873 = 1313905) B1313905
theorem B1751891 : Blo 1166400 1751891 := bstep (se 1 (by rfl) ⟨1313918, by rfl⟩ : syracuseStep 1751891 = 2627837) B2627837
theorem B1751921 : Blo 1166400 1751921 := bstep (se 2 (by rfl) ⟨656970, by rfl⟩ : syracuseStep 1751921 = 1313941) B1313941
theorem B1751939 : Blo 1166400 1751939 := bstep (se 1 (by rfl) ⟨1313954, by rfl⟩ : syracuseStep 1751939 = 2627909) B2627909
theorem B5913485 : Blo 1166400 5913485 := bstep (se 3 (by rfl) ⟨1108778, by rfl⟩ : syracuseStep 5913485 = 2217557) B2217557
theorem B1751969 : Blo 1166400 1751969 := bstep (se 2 (by rfl) ⟨656988, by rfl⟩ : syracuseStep 1751969 = 1313977) B1313977
theorem B3939245 : Blo 1166400 3939245 := bstep (se 3 (by rfl) ⟨738608, by rfl⟩ : syracuseStep 3939245 = 1477217) B1477217
theorem B1751987 : Blo 1166400 1751987 := bstep (se 1 (by rfl) ⟨1313990, by rfl⟩ : syracuseStep 1751987 = 2627981) B2627981
theorem B1752017 : Blo 1166400 1752017 := bstep (se 2 (by rfl) ⟨657006, by rfl⟩ : syracuseStep 1752017 = 1314013) B1314013
theorem B3939299 : Blo 1166400 3939299 := bstep (se 1 (by rfl) ⟨2954474, by rfl⟩ : syracuseStep 3939299 = 5908949) B5908949
theorem B1752035 : Blo 1166400 1752035 := bstep (se 1 (by rfl) ⟨1314026, by rfl⟩ : syracuseStep 1752035 = 2628053) B2628053
theorem B2628593 : Blo 1166400 2628593 := bstep (se 2 (by rfl) ⟨985722, by rfl⟩ : syracuseStep 2628593 = 1971445) B1971445
theorem B1752065 : Blo 1166400 1752065 := bstep (se 2 (by rfl) ⟨657024, by rfl⟩ : syracuseStep 1752065 = 1314049) B1314049
theorem B2628611 : Blo 1166400 2628611 := bstep (se 1 (by rfl) ⟨1971458, by rfl⟩ : syracuseStep 2628611 = 3942917) B3942917
theorem B1752083 : Blo 1166400 1752083 := bstep (se 1 (by rfl) ⟨1314062, by rfl⟩ : syracuseStep 1752083 = 2628125) B2628125
theorem B1752113 : Blo 1166400 1752113 := bstep (se 2 (by rfl) ⟨657042, by rfl⟩ : syracuseStep 1752113 = 1314085) B1314085
theorem B1752131 : Blo 1166400 1752131 := bstep (se 1 (by rfl) ⟨1314098, by rfl⟩ : syracuseStep 1752131 = 2628197) B2628197
theorem B1752161 : Blo 1166400 1752161 := bstep (se 2 (by rfl) ⟨657060, by rfl⟩ : syracuseStep 1752161 = 1314121) B1314121
theorem B1752179 : Blo 1166400 1752179 := bstep (se 1 (by rfl) ⟨1314134, by rfl⟩ : syracuseStep 1752179 = 2628269) B2628269
theorem B1752209 : Blo 1166400 1752209 := bstep (se 2 (by rfl) ⟨657078, by rfl⟩ : syracuseStep 1752209 = 1314157) B1314157
theorem B1662115 : Blo 1166400 1662115 := bstep (se 1 (by rfl) ⟨1246586, by rfl⟩ : syracuseStep 1662115 = 2493173) B2493173
theorem B1752227 : Blo 1166400 1752227 := bstep (se 1 (by rfl) ⟨1314170, by rfl⟩ : syracuseStep 1752227 = 2628341) B2628341
theorem B1752257 : Blo 1166400 1752257 := bstep (se 2 (by rfl) ⟨657096, by rfl⟩ : syracuseStep 1752257 = 1314193) B1314193
theorem B1752275 : Blo 1166400 1752275 := bstep (se 1 (by rfl) ⟨1314206, by rfl⟩ : syracuseStep 1752275 = 2628413) B2628413
theorem B3939569 : Blo 1166400 3939569 := bstep (se 2 (by rfl) ⟨1477338, by rfl⟩ : syracuseStep 3939569 = 2954677) B2954677
theorem B1752305 : Blo 1166400 1752305 := bstep (se 2 (by rfl) ⟨657114, by rfl⟩ : syracuseStep 1752305 = 1314229) B1314229
theorem B1662211 : Blo 1166400 1662211 := bstep (se 1 (by rfl) ⟨1246658, by rfl⟩ : syracuseStep 1662211 = 2493317) B2493317
theorem B1752323 : Blo 1166400 1752323 := bstep (se 1 (by rfl) ⟨1314242, by rfl⟩ : syracuseStep 1752323 = 2628485) B2628485
theorem B2628881 : Blo 1166400 2628881 := bstep (se 2 (by rfl) ⟨985830, by rfl⟩ : syracuseStep 2628881 = 1971661) B1971661
theorem B1752353 : Blo 1166400 1752353 := bstep (se 2 (by rfl) ⟨657132, by rfl⟩ : syracuseStep 1752353 = 1314265) B1314265
theorem B2628899 : Blo 1166400 2628899 := bstep (se 1 (by rfl) ⟨1971674, by rfl⟩ : syracuseStep 2628899 = 3943349) B3943349
theorem B7200049 : Blo 1166400 7200049 := bstep (se 2 (by rfl) ⟨2700018, by rfl⟩ : syracuseStep 7200049 = 5400037) B5400037
theorem B1752371 : Blo 1166400 1752371 := bstep (se 1 (by rfl) ⟨1314278, by rfl⟩ : syracuseStep 1752371 = 2628557) B2628557
theorem B1752401 : Blo 1166400 1752401 := bstep (se 2 (by rfl) ⟨657150, by rfl⟩ : syracuseStep 1752401 = 1314301) B1314301
theorem B1752419 : Blo 1166400 1752419 := bstep (se 1 (by rfl) ⟨1314314, by rfl⟩ : syracuseStep 1752419 = 2628629) B2628629
theorem B1752449 : Blo 1166400 1752449 := bstep (se 2 (by rfl) ⟨657168, by rfl⟩ : syracuseStep 1752449 = 1314337) B1314337
theorem B3153293 : Blo 1166400 3153293 := bstep (se 3 (by rfl) ⟨591242, by rfl⟩ : syracuseStep 3153293 = 1182485) B1182485
theorem B1752467 : Blo 1166400 1752467 := bstep (se 1 (by rfl) ⟨1314350, by rfl⟩ : syracuseStep 1752467 = 2628701) B2628701
theorem B1752497 : Blo 1166400 1752497 := bstep (se 2 (by rfl) ⟨657186, by rfl⟩ : syracuseStep 1752497 = 1314373) B1314373
theorem B3153347 : Blo 1166400 3153347 := bstep (se 1 (by rfl) ⟨2365010, by rfl⟩ : syracuseStep 3153347 = 4730021) B4730021
theorem B2366915 : Blo 1166400 2366915 := bstep (se 1 (by rfl) ⟨1775186, by rfl⟩ : syracuseStep 2366915 = 3550373) B3550373
theorem B1752515 : Blo 1166400 1752515 := bstep (se 1 (by rfl) ⟨1314386, by rfl⟩ : syracuseStep 1752515 = 2628773) B2628773
theorem B1752545 : Blo 1166400 1752545 := bstep (se 2 (by rfl) ⟨657204, by rfl⟩ : syracuseStep 1752545 = 1314409) B1314409
theorem B1752563 : Blo 1166400 1752563 := bstep (se 1 (by rfl) ⟨1314422, by rfl⟩ : syracuseStep 1752563 = 2628845) B2628845
theorem B1752593 : Blo 1166400 1752593 := bstep (se 2 (by rfl) ⟨657222, by rfl⟩ : syracuseStep 1752593 = 1314445) B1314445
theorem B5906033 : Blo 1166400 5906033 := bstep (se 2 (by rfl) ⟨2214762, by rfl⟩ : syracuseStep 5906033 = 4429525) B4429525
theorem B2956945 : Blo 1166400 2956945 := bstep (se 2 (by rfl) ⟨1108854, by rfl⟩ : syracuseStep 2956945 = 2217709) B2217709
theorem B1662707 : Blo 1166400 1662707 := bstep (se 1 (by rfl) ⟨1247030, by rfl⟩ : syracuseStep 1662707 = 2494061) B2494061
theorem B3940109 : Blo 1166400 3940109 := bstep (se 3 (by rfl) ⟨738770, by rfl⟩ : syracuseStep 3940109 = 1477541) B1477541
theorem B3940163 : Blo 1166400 3940163 := bstep (se 1 (by rfl) ⟨2955122, by rfl⟩ : syracuseStep 3940163 = 5910245) B5910245
theorem B32800625 : Blo 1166400 32800625 := bstep (se 2 (by rfl) ⟨12300234, by rfl⟩ : syracuseStep 32800625 = 24600469) B24600469
theorem B13295501 : Blo 1166400 13295501 := bstep (se 3 (by rfl) ⟨2492906, by rfl⟩ : syracuseStep 13295501 = 4985813) B4985813
theorem B2957219 : Blo 1166400 2957219 := bstep (se 1 (by rfl) ⟨2217914, by rfl⟩ : syracuseStep 2957219 = 4435829) B4435829
theorem B3326017 : Blo 1166400 3326017 := bstep (se 2 (by rfl) ⟨1247256, by rfl⟩ : syracuseStep 3326017 = 2494513) B2494513
theorem B9978187 : Blo 1166400 9978187 := bstep (se 1 (by rfl) ⟨7483640, by rfl⟩ : syracuseStep 9978187 = 14967281) B14967281
theorem B4432259 : Blo 1166400 4432259 := bstep (se 1 (by rfl) ⟨3324194, by rfl⟩ : syracuseStep 4432259 = 6648389) B6648389
theorem B3326359 : Blo 1166400 3326359 := bstep (se 1 (by rfl) ⟨2494769, by rfl⟩ : syracuseStep 3326359 = 4989539) B4989539
theorem B2245043 : Blo 1166400 2245043 := bstep (se 1 (by rfl) ⟨1683782, by rfl⟩ : syracuseStep 2245043 = 3367565) B3367565
theorem B15172019 : Blo 1166400 15172019 := bstep (se 1 (by rfl) ⟨11379014, by rfl⟩ : syracuseStep 15172019 = 22758029) B22758029
theorem B3940811 : Blo 1166400 3940811 := bstep (se 1 (by rfl) ⟨2955608, by rfl⟩ : syracuseStep 3940811 = 5911217) B5911217
theorem B2368001 : Blo 1166400 2368001 := bstep (se 2 (by rfl) ⟨888000, by rfl⟩ : syracuseStep 2368001 = 1776001) B1776001
theorem B10117649 : Blo 1166400 10117649 := bstep (se 2 (by rfl) ⟨3794118, by rfl⟩ : syracuseStep 10117649 = 7588237) B7588237
theorem B1245719 : Blo 1166400 1245719 := bstep (se 1 (by rfl) ⟨934289, by rfl⟩ : syracuseStep 1245719 = 1868579) B1868579
theorem B9978461 : Blo 1166400 9978461 := bstep (se 3 (by rfl) ⟨1870961, by rfl⟩ : syracuseStep 9978461 = 3741923) B3741923
theorem B48611933 : Blo 1166400 48611933 := bstep (se 3 (by rfl) ⟨9114737, by rfl⟩ : syracuseStep 48611933 = 18229475) B18229475
theorem B3941081 : Blo 1166400 3941081 := bstep (se 2 (by rfl) ⟨1477905, by rfl⟩ : syracuseStep 3941081 = 2955811) B2955811
theorem B9470681 : Blo 1166400 9470681 := bstep (se 2 (by rfl) ⟨3551505, by rfl⟩ : syracuseStep 9470681 = 7103011) B7103011
theorem B3154739 : Blo 1166400 3154739 := bstep (se 1 (by rfl) ⟨2366054, by rfl⟩ : syracuseStep 3154739 = 4732109) B4732109
theorem B4432715 : Blo 1166400 4432715 := bstep (se 1 (by rfl) ⟨3324536, by rfl⟩ : syracuseStep 4432715 = 6649073) B6649073
theorem B34145201 : Blo 1166400 34145201 := bstep (se 2 (by rfl) ⟨12804450, by rfl⟩ : syracuseStep 34145201 = 25608901) B25608901
theorem B2491403 : Blo 1166400 2491403 := bstep (se 1 (by rfl) ⟨1868552, by rfl⟩ : syracuseStep 2491403 = 3737105) B3737105
theorem B4432913 : Blo 1166400 4432913 := bstep (se 2 (by rfl) ⟨1662342, by rfl⟩ : syracuseStep 4432913 = 3324685) B3324685
theorem B5612561 : Blo 1166400 5612561 := bstep (se 2 (by rfl) ⟨2104710, by rfl⟩ : syracuseStep 5612561 = 4209421) B4209421
theorem B3327065 : Blo 1166400 3327065 := bstep (se 2 (by rfl) ⟨1247649, by rfl⟩ : syracuseStep 3327065 = 2495299) B2495299
theorem B21898421 : Blo 1166400 21898421 := bstep (se 5 (by rfl) ⟨1026488, by rfl⟩ : syracuseStep 21898421 = 2052977) B2052977
theorem B8865125 : Blo 1166400 8865125 := bstep (se 4 (by rfl) ⟨831105, by rfl⟩ : syracuseStep 8865125 = 1662211) B1662211
theorem B26936725 : Blo 1166400 26936725 := bstep (se 6 (by rfl) ⟨631329, by rfl⟩ : syracuseStep 26936725 = 1262659) B1262659
theorem B3941783 : Blo 1166400 3941783 := bstep (se 1 (by rfl) ⟨2956337, by rfl⟩ : syracuseStep 3941783 = 5912675) B5912675
theorem B2246105 : Blo 1166400 2246105 := bstep (se 2 (by rfl) ⟨842289, by rfl⟩ : syracuseStep 2246105 = 1684579) B1684579
theorem B1312267 : Blo 1166400 1312267 := bstep (se 1 (by rfl) ⟨984200, by rfl⟩ : syracuseStep 1312267 = 1968401) B1968401
theorem B1869335 : Blo 1166400 1869335 := bstep (se 1 (by rfl) ⟨1402001, by rfl⟩ : syracuseStep 1869335 = 2804003) B2804003
theorem B1246795 : Blo 1166400 1246795 := bstep (se 1 (by rfl) ⟨935096, by rfl⟩ : syracuseStep 1246795 = 1870193) B1870193
theorem B3991133 : Blo 1166400 3991133 := bstep (se 3 (by rfl) ⟨748337, by rfl⟩ : syracuseStep 3991133 = 1496675) B1496675
theorem B1312375 : Blo 1166400 1312375 := bstep (se 1 (by rfl) ⟨984281, by rfl⟩ : syracuseStep 1312375 = 1968563) B1968563
theorem B9979523 : Blo 1166400 9979523 := bstep (se 1 (by rfl) ⟨7484642, by rfl⟩ : syracuseStep 9979523 = 14969285) B14969285
theorem B1476235 : Blo 1166400 1476235 := bstep (se 1 (by rfl) ⟨1107176, by rfl⟩ : syracuseStep 1476235 = 2214353) B2214353
theorem B7988915 : Blo 1166400 7988915 := bstep (se 1 (by rfl) ⟨5991686, by rfl⟩ : syracuseStep 7988915 = 11983373) B11983373
theorem B4982465 : Blo 1166400 4982465 := bstep (se 2 (by rfl) ⟨1868424, by rfl⟩ : syracuseStep 4982465 = 3736849) B3736849
theorem B1869527 : Blo 1166400 1869527 := bstep (se 1 (by rfl) ⟨1402145, by rfl⟩ : syracuseStep 1869527 = 2804291) B2804291
theorem B7096025 : Blo 1166400 7096025 := bstep (se 2 (by rfl) ⟨2661009, by rfl⟩ : syracuseStep 7096025 = 5322019) B5322019
theorem B2492147 : Blo 1166400 2492147 := bstep (se 1 (by rfl) ⟨1869110, by rfl⟩ : syracuseStep 2492147 = 3738221) B3738221
theorem B3155735 : Blo 1166400 3155735 := bstep (se 1 (by rfl) ⟨2366801, by rfl⟩ : syracuseStep 3155735 = 4733603) B4733603
theorem B4433687 : Blo 1166400 4433687 := bstep (se 1 (by rfl) ⟨3325265, by rfl⟩ : syracuseStep 4433687 = 6650531) B6650531
theorem B1312555 : Blo 1166400 1312555 := bstep (se 1 (by rfl) ⟨984416, by rfl⟩ : syracuseStep 1312555 = 1968833) B1968833
theorem B8865611 : Blo 1166400 8865611 := bstep (se 1 (by rfl) ⟨6649208, by rfl⟩ : syracuseStep 8865611 = 13298417) B13298417
theorem B1869655 : Blo 1166400 1869655 := bstep (se 1 (by rfl) ⟨1402241, by rfl⟩ : syracuseStep 1869655 = 2804483) B2804483
theorem B17065829 : Blo 1166400 17065829 := bstep (se 4 (by rfl) ⟨1599921, by rfl⟩ : syracuseStep 17065829 = 3199843) B3199843
theorem B1312663 : Blo 1166400 1312663 := bstep (se 1 (by rfl) ⟨984497, by rfl⟩ : syracuseStep 1312663 = 1968995) B1968995
theorem B25257905 : Blo 1166400 25257905 := bstep (se 2 (by rfl) ⟨9471714, by rfl⟩ : syracuseStep 25257905 = 18943429) B18943429
theorem B3942323 : Blo 1166400 3942323 := bstep (se 1 (by rfl) ⟨2956742, by rfl⟩ : syracuseStep 3942323 = 5913485) B5913485
theorem B4433885 : Blo 1166400 4433885 := bstep (se 3 (by rfl) ⟨831353, by rfl⟩ : syracuseStep 4433885 = 1662707) B1662707
theorem B1312843 : Blo 1166400 1312843 := bstep (se 1 (by rfl) ⟨984632, by rfl⟩ : syracuseStep 1312843 = 1969265) B1969265
theorem B1312951 : Blo 1166400 1312951 := bstep (se 1 (by rfl) ⟨984713, by rfl⟩ : syracuseStep 1312951 = 1969427) B1969427
theorem B3942593 : Blo 1166400 3942593 := bstep (se 2 (by rfl) ⟨1478472, by rfl⟩ : syracuseStep 3942593 = 2956945) B2956945
theorem B7481645 : Blo 1166400 7481645 := bstep (se 3 (by rfl) ⟨1402808, by rfl⟩ : syracuseStep 7481645 = 2805617) B2805617
theorem B1313131 : Blo 1166400 1313131 := bstep (se 1 (by rfl) ⟨984848, by rfl⟩ : syracuseStep 1313131 = 1969697) B1969697
theorem B1870219 : Blo 1166400 1870219 := bstep (se 1 (by rfl) ⟨1402664, by rfl⟩ : syracuseStep 1870219 = 2805329) B2805329
theorem B9972173 : Blo 1166400 9972173 := bstep (se 3 (by rfl) ⟨1869782, by rfl⟩ : syracuseStep 9972173 = 3739565) B3739565
theorem B1313239 : Blo 1166400 1313239 := bstep (se 1 (by rfl) ⟨984929, by rfl⟩ : syracuseStep 1313239 = 1969859) B1969859
theorem B1870295 : Blo 1166400 1870295 := bstep (se 1 (by rfl) ⟨1402721, by rfl⟩ : syracuseStep 1870295 = 2805443) B2805443
theorem B2492993 : Blo 1166400 2492993 := bstep (se 2 (by rfl) ⟨934872, by rfl⟩ : syracuseStep 2492993 = 1869745) B1869745
theorem B21867083 : Blo 1166400 21867083 := bstep (se 1 (by rfl) ⟨16400312, by rfl⟩ : syracuseStep 21867083 = 32800625) B32800625
theorem B1477207 : Blo 1166400 1477207 := bstep (se 1 (by rfl) ⟨1107905, by rfl⟩ : syracuseStep 1477207 = 2215811) B2215811
theorem B4983389 : Blo 1166400 4983389 := bstep (se 3 (by rfl) ⟨934385, by rfl⟩ : syracuseStep 4983389 = 1868771) B1868771
theorem B1968779 : Blo 1166400 1968779 := bstep (se 1 (by rfl) ⟨1476584, by rfl⟩ : syracuseStep 1968779 = 2953169) B2953169
theorem B1313419 : Blo 1166400 1313419 := bstep (se 1 (by rfl) ⟨985064, by rfl⟩ : syracuseStep 1313419 = 1970129) B1970129
theorem B3369689 : Blo 1166400 3369689 := bstep (se 2 (by rfl) ⟨1263633, by rfl⟩ : syracuseStep 3369689 = 2527267) B2527267
theorem B3943133 : Blo 1166400 3943133 := bstep (se 3 (by rfl) ⟨739337, by rfl⟩ : syracuseStep 3943133 = 1478675) B1478675
theorem B1313527 : Blo 1166400 1313527 := bstep (se 1 (by rfl) ⟨985145, by rfl⟩ : syracuseStep 1313527 = 1970291) B1970291
theorem B1968907 : Blo 1166400 1968907 := bstep (se 1 (by rfl) ⟨1476680, by rfl⟩ : syracuseStep 1968907 = 2953361) B2953361
theorem B2132761 : Blo 1166400 2132761 := bstep (se 2 (by rfl) ⟨799785, by rfl⟩ : syracuseStep 2132761 = 1599571) B1599571
theorem B2493335 : Blo 1166400 2493335 := bstep (se 1 (by rfl) ⟨1870001, by rfl⟩ : syracuseStep 2493335 = 3740003) B3740003
theorem B1969049 : Blo 1166400 1969049 := bstep (se 2 (by rfl) ⟨738393, by rfl⟩ : syracuseStep 1969049 = 1476787) B1476787
theorem B1313707 : Blo 1166400 1313707 := bstep (se 1 (by rfl) ⟨985280, by rfl⟩ : syracuseStep 1313707 = 1970561) B1970561
theorem B2624435 : Blo 1166400 2624435 := bstep (se 1 (by rfl) ⟨1968326, by rfl⟩ : syracuseStep 2624435 = 3936653) B3936653
theorem B2624471 : Blo 1166400 2624471 := bstep (se 1 (by rfl) ⟨1968353, by rfl⟩ : syracuseStep 2624471 = 3936707) B3936707
theorem B1313815 : Blo 1166400 1313815 := bstep (se 1 (by rfl) ⟨985361, by rfl⟩ : syracuseStep 1313815 = 1970723) B1970723
theorem B1969177 : Blo 1166400 1969177 := bstep (se 2 (by rfl) ⟨738441, by rfl⟩ : syracuseStep 1969177 = 1476883) B1476883
theorem B1166411 : Blo 1166400 1166411 := bstep (se 1 (by rfl) ⟨874808, by rfl⟩ : syracuseStep 1166411 = 1749617) B1749617
theorem B1166423 : Blo 1166400 1166423 := bstep (se 1 (by rfl) ⟨874817, by rfl⟩ : syracuseStep 1166423 = 1749635) B1749635
theorem B3992665 : Blo 1166400 3992665 := bstep (se 2 (by rfl) ⟨1497249, by rfl⟩ : syracuseStep 3992665 = 2994499) B2994499
theorem B5909597 : Blo 1166400 5909597 := bstep (se 3 (by rfl) ⟨1108049, by rfl⟩ : syracuseStep 5909597 = 2216099) B2216099
theorem B1166443 : Blo 1166400 1166443 := bstep (se 1 (by rfl) ⟨874832, by rfl⟩ : syracuseStep 1166443 = 1749665) B1749665
theorem B1166455 : Blo 1166400 1166455 := bstep (se 1 (by rfl) ⟨874841, by rfl⟩ : syracuseStep 1166455 = 1749683) B1749683
theorem B1166475 : Blo 1166400 1166475 := bstep (se 1 (by rfl) ⟨874856, by rfl⟩ : syracuseStep 1166475 = 1749713) B1749713
theorem B2624651 : Blo 1166400 2624651 := bstep (se 1 (by rfl) ⟨1968488, by rfl⟩ : syracuseStep 2624651 = 3936977) B3936977
theorem B1166487 : Blo 1166400 1166487 := bstep (se 1 (by rfl) ⟨874865, by rfl⟩ : syracuseStep 1166487 = 1749731) B1749731
theorem B1166507 : Blo 1166400 1166507 := bstep (se 1 (by rfl) ⟨874880, by rfl⟩ : syracuseStep 1166507 = 1749761) B1749761
theorem B1166519 : Blo 1166400 1166519 := bstep (se 1 (by rfl) ⟨874889, by rfl⟩ : syracuseStep 1166519 = 1749779) B1749779
theorem B2624705 : Blo 1166400 2624705 := bstep (se 2 (by rfl) ⟨984264, by rfl⟩ : syracuseStep 2624705 = 1968529) B1968529
theorem B1166539 : Blo 1166400 1166539 := bstep (se 1 (by rfl) ⟨874904, by rfl⟩ : syracuseStep 1166539 = 1749809) B1749809
theorem B1313995 : Blo 1166400 1313995 := bstep (se 1 (by rfl) ⟨985496, by rfl⟩ : syracuseStep 1313995 = 1970993) B1970993
theorem B1166551 : Blo 1166400 1166551 := bstep (se 1 (by rfl) ⟨874913, by rfl⟩ : syracuseStep 1166551 = 1749827) B1749827
theorem B2215127 : Blo 1166400 2215127 := bstep (se 1 (by rfl) ⟨1661345, by rfl⟩ : syracuseStep 2215127 = 3322691) B3322691
theorem B1166571 : Blo 1166400 1166571 := bstep (se 1 (by rfl) ⟨874928, by rfl⟩ : syracuseStep 1166571 = 1749857) B1749857
theorem B1166583 : Blo 1166400 1166583 := bstep (se 1 (by rfl) ⟨874937, by rfl⟩ : syracuseStep 1166583 = 1749875) B1749875
theorem B1166603 : Blo 1166400 1166603 := bstep (se 1 (by rfl) ⟨874952, by rfl⟩ : syracuseStep 1166603 = 1749905) B1749905
theorem B1166615 : Blo 1166400 1166615 := bstep (se 1 (by rfl) ⟨874961, by rfl⟩ : syracuseStep 1166615 = 1749923) B1749923
theorem B1166635 : Blo 1166400 1166635 := bstep (se 1 (by rfl) ⟨874976, by rfl⟩ : syracuseStep 1166635 = 1749953) B1749953
theorem B1166647 : Blo 1166400 1166647 := bstep (se 1 (by rfl) ⟨874985, by rfl⟩ : syracuseStep 1166647 = 1749971) B1749971
theorem B1314103 : Blo 1166400 1314103 := bstep (se 1 (by rfl) ⟨985577, by rfl⟩ : syracuseStep 1314103 = 1971155) B1971155
theorem B3288385 : Blo 1166400 3288385 := bstep (se 2 (by rfl) ⟨1233144, by rfl⟩ : syracuseStep 3288385 = 2466289) B2466289
theorem B1166667 : Blo 1166400 1166667 := bstep (se 1 (by rfl) ⟨875000, by rfl⟩ : syracuseStep 1166667 = 1750001) B1750001
theorem B1166679 : Blo 1166400 1166679 := bstep (se 1 (by rfl) ⟨875009, by rfl⟩ : syracuseStep 1166679 = 1750019) B1750019
theorem B1166699 : Blo 1166400 1166699 := bstep (se 1 (by rfl) ⟨875024, by rfl⟩ : syracuseStep 1166699 = 1750049) B1750049
theorem B1166711 : Blo 1166400 1166711 := bstep (se 1 (by rfl) ⟨875033, by rfl⟩ : syracuseStep 1166711 = 1750067) B1750067
theorem B1166731 : Blo 1166400 1166731 := bstep (se 1 (by rfl) ⟨875048, by rfl⟩ : syracuseStep 1166731 = 1750097) B1750097
theorem B1478027 : Blo 1166400 1478027 := bstep (se 1 (by rfl) ⟨1108520, by rfl⟩ : syracuseStep 1478027 = 2217041) B2217041
theorem B1166743 : Blo 1166400 1166743 := bstep (se 1 (by rfl) ⟨875057, by rfl⟩ : syracuseStep 1166743 = 1750115) B1750115
theorem B2624921 : Blo 1166400 2624921 := bstep (se 2 (by rfl) ⟨984345, by rfl⟩ : syracuseStep 2624921 = 1968691) B1968691
theorem B1166763 : Blo 1166400 1166763 := bstep (se 1 (by rfl) ⟨875072, by rfl⟩ : syracuseStep 1166763 = 1750145) B1750145
theorem B1166775 : Blo 1166400 1166775 := bstep (se 1 (by rfl) ⟨875081, by rfl⟩ : syracuseStep 1166775 = 1750163) B1750163
theorem B3993035 : Blo 1166400 3993035 := bstep (se 1 (by rfl) ⟨2994776, by rfl⟩ : syracuseStep 3993035 = 5989553) B5989553
theorem B1166795 : Blo 1166400 1166795 := bstep (se 1 (by rfl) ⟨875096, by rfl⟩ : syracuseStep 1166795 = 1750193) B1750193
theorem B1166807 : Blo 1166400 1166807 := bstep (se 1 (by rfl) ⟨875105, by rfl⟩ : syracuseStep 1166807 = 1750211) B1750211
theorem B1166827 : Blo 1166400 1166827 := bstep (se 1 (by rfl) ⟨875120, by rfl⟩ : syracuseStep 1166827 = 1750241) B1750241
theorem B1314283 : Blo 1166400 1314283 := bstep (se 1 (by rfl) ⟨985712, by rfl⟩ : syracuseStep 1314283 = 1971425) B1971425
theorem B2625011 : Blo 1166400 2625011 := bstep (se 1 (by rfl) ⟨1968758, by rfl⟩ : syracuseStep 2625011 = 3937517) B3937517
theorem B1166839 : Blo 1166400 1166839 := bstep (se 1 (by rfl) ⟨875129, by rfl⟩ : syracuseStep 1166839 = 1750259) B1750259
theorem B1166859 : Blo 1166400 1166859 := bstep (se 1 (by rfl) ⟨875144, by rfl⟩ : syracuseStep 1166859 = 1750289) B1750289
theorem B2625047 : Blo 1166400 2625047 := bstep (se 1 (by rfl) ⟨1968785, by rfl⟩ : syracuseStep 2625047 = 3937571) B3937571
theorem B1166871 : Blo 1166400 1166871 := bstep (se 1 (by rfl) ⟨875153, by rfl⟩ : syracuseStep 1166871 = 1750307) B1750307
theorem B1166891 : Blo 1166400 1166891 := bstep (se 1 (by rfl) ⟨875168, by rfl⟩ : syracuseStep 1166891 = 1750337) B1750337
theorem B1166903 : Blo 1166400 1166903 := bstep (se 1 (by rfl) ⟨875177, by rfl⟩ : syracuseStep 1166903 = 1750355) B1750355
theorem B1166923 : Blo 1166400 1166923 := bstep (se 1 (by rfl) ⟨875192, by rfl⟩ : syracuseStep 1166923 = 1750385) B1750385
theorem B1166935 : Blo 1166400 1166935 := bstep (se 1 (by rfl) ⟨875201, by rfl⟩ : syracuseStep 1166935 = 1750403) B1750403
theorem B1969751 : Blo 1166400 1969751 := bstep (se 1 (by rfl) ⟨1477313, by rfl⟩ : syracuseStep 1969751 = 2954627) B2954627
theorem B1314391 : Blo 1166400 1314391 := bstep (se 1 (by rfl) ⟨985793, by rfl⟩ : syracuseStep 1314391 = 1971587) B1971587
theorem B1166955 : Blo 1166400 1166955 := bstep (se 1 (by rfl) ⟨875216, by rfl⟩ : syracuseStep 1166955 = 1750433) B1750433
theorem B1166967 : Blo 1166400 1166967 := bstep (se 1 (by rfl) ⟨875225, by rfl⟩ : syracuseStep 1166967 = 1750451) B1750451
theorem B1166987 : Blo 1166400 1166987 := bstep (se 1 (by rfl) ⟨875240, by rfl⟩ : syracuseStep 1166987 = 1750481) B1750481
theorem B1166999 : Blo 1166400 1166999 := bstep (se 1 (by rfl) ⟨875249, by rfl⟩ : syracuseStep 1166999 = 1750499) B1750499
theorem B1167019 : Blo 1166400 1167019 := bstep (se 1 (by rfl) ⟨875264, by rfl⟩ : syracuseStep 1167019 = 1750529) B1750529
theorem B1167031 : Blo 1166400 1167031 := bstep (se 1 (by rfl) ⟨875273, by rfl⟩ : syracuseStep 1167031 = 1750547) B1750547
theorem B2625227 : Blo 1166400 2625227 := bstep (se 1 (by rfl) ⟨1968920, by rfl⟩ : syracuseStep 2625227 = 3937841) B3937841
theorem B1167051 : Blo 1166400 1167051 := bstep (se 1 (by rfl) ⟨875288, by rfl⟩ : syracuseStep 1167051 = 1750577) B1750577
theorem B1167063 : Blo 1166400 1167063 := bstep (se 1 (by rfl) ⟨875297, by rfl⟩ : syracuseStep 1167063 = 1750595) B1750595
theorem B1969879 : Blo 1166400 1969879 := bstep (se 1 (by rfl) ⟨1477409, by rfl⟩ : syracuseStep 1969879 = 2954819) B2954819
theorem B1167083 : Blo 1166400 1167083 := bstep (se 1 (by rfl) ⟨875312, by rfl⟩ : syracuseStep 1167083 = 1750625) B1750625
theorem B2215667 : Blo 1166400 2215667 := bstep (se 1 (by rfl) ⟨1661750, by rfl⟩ : syracuseStep 2215667 = 3323501) B3323501
theorem B1167095 : Blo 1166400 1167095 := bstep (se 1 (by rfl) ⟨875321, by rfl⟩ : syracuseStep 1167095 = 1750643) B1750643
theorem B2625281 : Blo 1166400 2625281 := bstep (se 2 (by rfl) ⟨984480, by rfl⟩ : syracuseStep 2625281 = 1968961) B1968961
theorem B1167115 : Blo 1166400 1167115 := bstep (se 1 (by rfl) ⟨875336, by rfl⟩ : syracuseStep 1167115 = 1750673) B1750673
theorem B1167127 : Blo 1166400 1167127 := bstep (se 1 (by rfl) ⟨875345, by rfl⟩ : syracuseStep 1167127 = 1750691) B1750691
theorem B1167147 : Blo 1166400 1167147 := bstep (se 1 (by rfl) ⟨875360, by rfl⟩ : syracuseStep 1167147 = 1750721) B1750721
theorem B1167159 : Blo 1166400 1167159 := bstep (se 1 (by rfl) ⟨875369, by rfl⟩ : syracuseStep 1167159 = 1750739) B1750739
theorem B1167179 : Blo 1166400 1167179 := bstep (se 1 (by rfl) ⟨875384, by rfl⟩ : syracuseStep 1167179 = 1750769) B1750769
theorem B1167191 : Blo 1166400 1167191 := bstep (se 1 (by rfl) ⟨875393, by rfl⟩ : syracuseStep 1167191 = 1750787) B1750787
theorem B6311773 : Blo 1166400 6311773 := bstep (se 3 (by rfl) ⟨1183457, by rfl⟩ : syracuseStep 6311773 = 2366915) B2366915
theorem B1167211 : Blo 1166400 1167211 := bstep (se 1 (by rfl) ⟨875408, by rfl⟩ : syracuseStep 1167211 = 1750817) B1750817
theorem B1167223 : Blo 1166400 1167223 := bstep (se 1 (by rfl) ⟨875417, by rfl⟩ : syracuseStep 1167223 = 1750835) B1750835
theorem B4435843 : Blo 1166400 4435843 := bstep (se 1 (by rfl) ⟨3326882, by rfl⟩ : syracuseStep 4435843 = 6653765) B6653765
theorem B1167243 : Blo 1166400 1167243 := bstep (se 1 (by rfl) ⟨875432, by rfl⟩ : syracuseStep 1167243 = 1750865) B1750865
theorem B1167255 : Blo 1166400 1167255 := bstep (se 1 (by rfl) ⟨875441, by rfl⟩ : syracuseStep 1167255 = 1750883) B1750883
theorem B1167275 : Blo 1166400 1167275 := bstep (se 1 (by rfl) ⟨875456, by rfl⟩ : syracuseStep 1167275 = 1750913) B1750913
theorem B1167287 : Blo 1166400 1167287 := bstep (se 1 (by rfl) ⟨875465, by rfl⟩ : syracuseStep 1167287 = 1750931) B1750931
theorem B1773515 : Blo 1166400 1773515 := bstep (se 1 (by rfl) ⟨1330136, by rfl⟩ : syracuseStep 1773515 = 2660273) B2660273
theorem B3321803 : Blo 1166400 3321803 := bstep (se 1 (by rfl) ⟨2491352, by rfl⟩ : syracuseStep 3321803 = 4982705) B4982705
theorem B1167307 : Blo 1166400 1167307 := bstep (se 1 (by rfl) ⟨875480, by rfl⟩ : syracuseStep 1167307 = 1750961) B1750961
theorem B1167319 : Blo 1166400 1167319 := bstep (se 1 (by rfl) ⟨875489, by rfl⟩ : syracuseStep 1167319 = 1750979) B1750979
theorem B2625497 : Blo 1166400 2625497 := bstep (se 2 (by rfl) ⟨984561, by rfl⟩ : syracuseStep 2625497 = 1969123) B1969123
theorem B1167339 : Blo 1166400 1167339 := bstep (se 1 (by rfl) ⟨875504, by rfl⟩ : syracuseStep 1167339 = 1751009) B1751009
theorem B1167351 : Blo 1166400 1167351 := bstep (se 1 (by rfl) ⟨875513, by rfl⟩ : syracuseStep 1167351 = 1751027) B1751027
theorem B1167371 : Blo 1166400 1167371 := bstep (se 1 (by rfl) ⟨875528, by rfl⟩ : syracuseStep 1167371 = 1751057) B1751057
theorem B1167383 : Blo 1166400 1167383 := bstep (se 1 (by rfl) ⟨875537, by rfl⟩ : syracuseStep 1167383 = 1751075) B1751075
theorem B1167403 : Blo 1166400 1167403 := bstep (se 1 (by rfl) ⟨875552, by rfl⟩ : syracuseStep 1167403 = 1751105) B1751105
theorem B2625587 : Blo 1166400 2625587 := bstep (se 1 (by rfl) ⟨1969190, by rfl⟩ : syracuseStep 2625587 = 3938381) B3938381
theorem B1167415 : Blo 1166400 1167415 := bstep (se 1 (by rfl) ⟨875561, by rfl⟩ : syracuseStep 1167415 = 1751123) B1751123
theorem B35926091 : Blo 1166400 35926091 := bstep (se 1 (by rfl) ⟨26944568, by rfl⟩ : syracuseStep 35926091 = 53889137) B53889137
theorem B1167435 : Blo 1166400 1167435 := bstep (se 1 (by rfl) ⟨875576, by rfl⟩ : syracuseStep 1167435 = 1751153) B1751153
theorem B1478731 : Blo 1166400 1478731 := bstep (se 1 (by rfl) ⟨1109048, by rfl⟩ : syracuseStep 1478731 = 2218097) B2218097
theorem B2625623 : Blo 1166400 2625623 := bstep (se 1 (by rfl) ⟨1969217, by rfl⟩ : syracuseStep 2625623 = 3938435) B3938435
theorem B1167447 : Blo 1166400 1167447 := bstep (se 1 (by rfl) ⟨875585, by rfl⟩ : syracuseStep 1167447 = 1751171) B1751171
theorem B3551321 : Blo 1166400 3551321 := bstep (se 2 (by rfl) ⟨1331745, by rfl⟩ : syracuseStep 3551321 = 2663491) B2663491
theorem B8982629 : Blo 1166400 8982629 := bstep (se 4 (by rfl) ⟨842121, by rfl⟩ : syracuseStep 8982629 = 1684243) B1684243
theorem B1167467 : Blo 1166400 1167467 := bstep (se 1 (by rfl) ⟨875600, by rfl⟩ : syracuseStep 1167467 = 1751201) B1751201
theorem B1167479 : Blo 1166400 1167479 := bstep (se 1 (by rfl) ⟨875609, by rfl⟩ : syracuseStep 1167479 = 1751219) B1751219
theorem B8859779 : Blo 1166400 8859779 := bstep (se 1 (by rfl) ⟨6644834, by rfl⟩ : syracuseStep 8859779 = 13289669) B13289669
theorem B1167499 : Blo 1166400 1167499 := bstep (se 1 (by rfl) ⟨875624, by rfl⟩ : syracuseStep 1167499 = 1751249) B1751249
theorem B1167511 : Blo 1166400 1167511 := bstep (se 1 (by rfl) ⟨875633, by rfl⟩ : syracuseStep 1167511 = 1751267) B1751267
theorem B1167531 : Blo 1166400 1167531 := bstep (se 1 (by rfl) ⟨875648, by rfl⟩ : syracuseStep 1167531 = 1751297) B1751297
theorem B4436147 : Blo 1166400 4436147 := bstep (se 1 (by rfl) ⟨3327110, by rfl⟩ : syracuseStep 4436147 = 6654221) B6654221
theorem B1167543 : Blo 1166400 1167543 := bstep (se 1 (by rfl) ⟨875657, by rfl⟩ : syracuseStep 1167543 = 1751315) B1751315
theorem B1167563 : Blo 1166400 1167563 := bstep (se 1 (by rfl) ⟨875672, by rfl⟩ : syracuseStep 1167563 = 1751345) B1751345
theorem B1167575 : Blo 1166400 1167575 := bstep (se 1 (by rfl) ⟨875681, by rfl⟩ : syracuseStep 1167575 = 1751363) B1751363
theorem B2216153 : Blo 1166400 2216153 := bstep (se 2 (by rfl) ⟨831057, by rfl⟩ : syracuseStep 2216153 = 1662115) B1662115
theorem B1167595 : Blo 1166400 1167595 := bstep (se 1 (by rfl) ⟨875696, by rfl⟩ : syracuseStep 1167595 = 1751393) B1751393
theorem B1167607 : Blo 1166400 1167607 := bstep (se 1 (by rfl) ⟨875705, by rfl⟩ : syracuseStep 1167607 = 1751411) B1751411
theorem B2625803 : Blo 1166400 2625803 := bstep (se 1 (by rfl) ⟨1969352, by rfl⟩ : syracuseStep 2625803 = 3938705) B3938705
theorem B1167627 : Blo 1166400 1167627 := bstep (se 1 (by rfl) ⟨875720, by rfl⟩ : syracuseStep 1167627 = 1751441) B1751441
theorem B1167639 : Blo 1166400 1167639 := bstep (se 1 (by rfl) ⟨875729, by rfl⟩ : syracuseStep 1167639 = 1751459) B1751459
theorem B1167659 : Blo 1166400 1167659 := bstep (se 1 (by rfl) ⟨875744, by rfl⟩ : syracuseStep 1167659 = 1751489) B1751489
theorem B2953523 : Blo 1166400 2953523 := bstep (se 1 (by rfl) ⟨2215142, by rfl⟩ : syracuseStep 2953523 = 4430285) B4430285
theorem B1167671 : Blo 1166400 1167671 := bstep (se 1 (by rfl) ⟨875753, by rfl⟩ : syracuseStep 1167671 = 1751507) B1751507
theorem B2625857 : Blo 1166400 2625857 := bstep (se 2 (by rfl) ⟨984696, by rfl⟩ : syracuseStep 2625857 = 1969393) B1969393
theorem B1167691 : Blo 1166400 1167691 := bstep (se 1 (by rfl) ⟨875768, by rfl⟩ : syracuseStep 1167691 = 1751537) B1751537
theorem B1970507 : Blo 1166400 1970507 := bstep (se 1 (by rfl) ⟨1477880, by rfl⟩ : syracuseStep 1970507 = 2955761) B2955761
theorem B1167703 : Blo 1166400 1167703 := bstep (se 1 (by rfl) ⟨875777, by rfl⟩ : syracuseStep 1167703 = 1751555) B1751555
theorem B1331563 : Blo 1166400 1331563 := bstep (se 1 (by rfl) ⟨998672, by rfl⟩ : syracuseStep 1331563 = 1997345) B1997345
theorem B1167723 : Blo 1166400 1167723 := bstep (se 1 (by rfl) ⟨875792, by rfl⟩ : syracuseStep 1167723 = 1751585) B1751585
theorem B1167735 : Blo 1166400 1167735 := bstep (se 1 (by rfl) ⟨875801, by rfl⟩ : syracuseStep 1167735 = 1751603) B1751603
theorem B1167755 : Blo 1166400 1167755 := bstep (se 1 (by rfl) ⟨875816, by rfl⟩ : syracuseStep 1167755 = 1751633) B1751633
theorem B1167767 : Blo 1166400 1167767 := bstep (se 1 (by rfl) ⟨875825, by rfl⟩ : syracuseStep 1167767 = 1751651) B1751651
theorem B1167787 : Blo 1166400 1167787 := bstep (se 1 (by rfl) ⟨875840, by rfl⟩ : syracuseStep 1167787 = 1751681) B1751681
theorem B1184171 : Blo 1166400 1184171 := bstep (se 1 (by rfl) ⟨888128, by rfl⟩ : syracuseStep 1184171 = 1776257) B1776257
theorem B1167799 : Blo 1166400 1167799 := bstep (se 1 (by rfl) ⟨875849, by rfl⟩ : syracuseStep 1167799 = 1751699) B1751699
theorem B1970635 : Blo 1166400 1970635 := bstep (se 1 (by rfl) ⟨1477976, by rfl⟩ : syracuseStep 1970635 = 2955953) B2955953
theorem B1167819 : Blo 1166400 1167819 := bstep (se 1 (by rfl) ⟨875864, by rfl⟩ : syracuseStep 1167819 = 1751729) B1751729
theorem B1167831 : Blo 1166400 1167831 := bstep (se 1 (by rfl) ⟨875873, by rfl⟩ : syracuseStep 1167831 = 1751747) B1751747
theorem B1167851 : Blo 1166400 1167851 := bstep (se 1 (by rfl) ⟨875888, by rfl⟩ : syracuseStep 1167851 = 1751777) B1751777
theorem B1167863 : Blo 1166400 1167863 := bstep (se 1 (by rfl) ⟨875897, by rfl⟩ : syracuseStep 1167863 = 1751795) B1751795
theorem B1167883 : Blo 1166400 1167883 := bstep (se 1 (by rfl) ⟨875912, by rfl⟩ : syracuseStep 1167883 = 1751825) B1751825
theorem B1167895 : Blo 1166400 1167895 := bstep (se 1 (by rfl) ⟨875921, by rfl⟩ : syracuseStep 1167895 = 1751843) B1751843
theorem B2626073 : Blo 1166400 2626073 := bstep (se 2 (by rfl) ⟨984777, by rfl⟩ : syracuseStep 2626073 = 1969555) B1969555
theorem B1167915 : Blo 1166400 1167915 := bstep (se 1 (by rfl) ⟨875936, by rfl⟩ : syracuseStep 1167915 = 1751873) B1751873
theorem B10654253 : Blo 1166400 10654253 := bstep (se 3 (by rfl) ⟨1997672, by rfl⟩ : syracuseStep 10654253 = 3995345) B3995345
theorem B1167927 : Blo 1166400 1167927 := bstep (se 1 (by rfl) ⟨875945, by rfl⟩ : syracuseStep 1167927 = 1751891) B1751891
theorem B1167947 : Blo 1166400 1167947 := bstep (se 1 (by rfl) ⟨875960, by rfl⟩ : syracuseStep 1167947 = 1751921) B1751921
theorem B1167959 : Blo 1166400 1167959 := bstep (se 1 (by rfl) ⟨875969, by rfl⟩ : syracuseStep 1167959 = 1751939) B1751939
theorem B2953817 : Blo 1166400 2953817 := bstep (se 2 (by rfl) ⟨1107681, by rfl⟩ : syracuseStep 2953817 = 2215363) B2215363
theorem B1970777 : Blo 1166400 1970777 := bstep (se 2 (by rfl) ⟨739041, by rfl⟩ : syracuseStep 1970777 = 1478083) B1478083
theorem B1167979 : Blo 1166400 1167979 := bstep (se 1 (by rfl) ⟨875984, by rfl⟩ : syracuseStep 1167979 = 1751969) B1751969
theorem B2626163 : Blo 1166400 2626163 := bstep (se 1 (by rfl) ⟨1969622, by rfl⟩ : syracuseStep 2626163 = 3939245) B3939245
theorem B1167991 : Blo 1166400 1167991 := bstep (se 1 (by rfl) ⟨875993, by rfl⟩ : syracuseStep 1167991 = 1751987) B1751987
theorem B1168011 : Blo 1166400 1168011 := bstep (se 1 (by rfl) ⟨876008, by rfl⟩ : syracuseStep 1168011 = 1752017) B1752017
theorem B2626199 : Blo 1166400 2626199 := bstep (se 1 (by rfl) ⟨1969649, by rfl⟩ : syracuseStep 2626199 = 3939299) B3939299
theorem B1168023 : Blo 1166400 1168023 := bstep (se 1 (by rfl) ⟨876017, by rfl⟩ : syracuseStep 1168023 = 1752035) B1752035
theorem B1168043 : Blo 1166400 1168043 := bstep (se 1 (by rfl) ⟨876032, by rfl⟩ : syracuseStep 1168043 = 1752065) B1752065
theorem B1168055 : Blo 1166400 1168055 := bstep (se 1 (by rfl) ⟨876041, by rfl⟩ : syracuseStep 1168055 = 1752083) B1752083
theorem B1749707 : Blo 1166400 1749707 := bstep (se 1 (by rfl) ⟨1312280, by rfl⟩ : syracuseStep 1749707 = 2624561) B2624561
theorem B1168075 : Blo 1166400 1168075 := bstep (se 1 (by rfl) ⟨876056, by rfl⟩ : syracuseStep 1168075 = 1752113) B1752113
theorem B1749719 : Blo 1166400 1749719 := bstep (se 1 (by rfl) ⟨1312289, by rfl⟩ : syracuseStep 1749719 = 2624579) B2624579
theorem B1168087 : Blo 1166400 1168087 := bstep (se 1 (by rfl) ⟨876065, by rfl⟩ : syracuseStep 1168087 = 1752131) B1752131
theorem B1970905 : Blo 1166400 1970905 := bstep (se 2 (by rfl) ⟨739089, by rfl⟩ : syracuseStep 1970905 = 1478179) B1478179
theorem B1168107 : Blo 1166400 1168107 := bstep (se 1 (by rfl) ⟨876080, by rfl⟩ : syracuseStep 1168107 = 1752161) B1752161
theorem B1168119 : Blo 1166400 1168119 := bstep (se 1 (by rfl) ⟨876089, by rfl⟩ : syracuseStep 1168119 = 1752179) B1752179
theorem B1168139 : Blo 1166400 1168139 := bstep (se 1 (by rfl) ⟨876104, by rfl⟩ : syracuseStep 1168139 = 1752209) B1752209
theorem B1168151 : Blo 1166400 1168151 := bstep (se 1 (by rfl) ⟨876113, by rfl⟩ : syracuseStep 1168151 = 1752227) B1752227
theorem B1749785 : Blo 1166400 1749785 := bstep (se 2 (by rfl) ⟨656169, by rfl⟩ : syracuseStep 1749785 = 1312339) B1312339
theorem B1168171 : Blo 1166400 1168171 := bstep (se 1 (by rfl) ⟨876128, by rfl⟩ : syracuseStep 1168171 = 1752257) B1752257
theorem B1168183 : Blo 1166400 1168183 := bstep (se 1 (by rfl) ⟨876137, by rfl⟩ : syracuseStep 1168183 = 1752275) B1752275
theorem B9966401 : Blo 1166400 9966401 := bstep (se 2 (by rfl) ⟨3737400, by rfl⟩ : syracuseStep 9966401 = 7474801) B7474801
theorem B6648641 : Blo 1166400 6648641 := bstep (se 2 (by rfl) ⟨2493240, by rfl⟩ : syracuseStep 6648641 = 4986481) B4986481
theorem B2626379 : Blo 1166400 2626379 := bstep (se 1 (by rfl) ⟨1969784, by rfl⟩ : syracuseStep 2626379 = 3939569) B3939569
theorem B1168203 : Blo 1166400 1168203 := bstep (se 1 (by rfl) ⟨876152, by rfl⟩ : syracuseStep 1168203 = 1752305) B1752305
theorem B1168215 : Blo 1166400 1168215 := bstep (se 1 (by rfl) ⟨876161, by rfl⟩ : syracuseStep 1168215 = 1752323) B1752323
theorem B1168235 : Blo 1166400 1168235 := bstep (se 1 (by rfl) ⟨876176, by rfl⟩ : syracuseStep 1168235 = 1752353) B1752353
theorem B1168247 : Blo 1166400 1168247 := bstep (se 1 (by rfl) ⟨876185, by rfl⟩ : syracuseStep 1168247 = 1752371) B1752371
theorem B2626433 : Blo 1166400 2626433 := bstep (se 2 (by rfl) ⟨984912, by rfl⟩ : syracuseStep 2626433 = 1969825) B1969825
theorem B1749899 : Blo 1166400 1749899 := bstep (se 1 (by rfl) ⟨1312424, by rfl⟩ : syracuseStep 1749899 = 2624849) B2624849
theorem B1168267 : Blo 1166400 1168267 := bstep (se 1 (by rfl) ⟨876200, by rfl⟩ : syracuseStep 1168267 = 1752401) B1752401
theorem B1749911 : Blo 1166400 1749911 := bstep (se 1 (by rfl) ⟨1312433, by rfl⟩ : syracuseStep 1749911 = 2624867) B2624867
theorem B1168279 : Blo 1166400 1168279 := bstep (se 1 (by rfl) ⟨876209, by rfl⟩ : syracuseStep 1168279 = 1752419) B1752419
theorem B1168299 : Blo 1166400 1168299 := bstep (se 1 (by rfl) ⟨876224, by rfl⟩ : syracuseStep 1168299 = 1752449) B1752449
theorem B2102195 : Blo 1166400 2102195 := bstep (se 1 (by rfl) ⟨1576646, by rfl⟩ : syracuseStep 2102195 = 3153293) B3153293
theorem B1168311 : Blo 1166400 1168311 := bstep (se 1 (by rfl) ⟨876233, by rfl⟩ : syracuseStep 1168311 = 1752467) B1752467
theorem B4731851 : Blo 1166400 4731851 := bstep (se 1 (by rfl) ⟨3548888, by rfl⟩ : syracuseStep 4731851 = 7097777) B7097777
theorem B1168331 : Blo 1166400 1168331 := bstep (se 1 (by rfl) ⟨876248, by rfl⟩ : syracuseStep 1168331 = 1752497) B1752497
theorem B2102231 : Blo 1166400 2102231 := bstep (se 1 (by rfl) ⟨1576673, by rfl⟩ : syracuseStep 2102231 = 3153347) B3153347
theorem B1749977 : Blo 1166400 1749977 := bstep (se 2 (by rfl) ⟨656241, by rfl⟩ : syracuseStep 1749977 = 1312483) B1312483
theorem B1168343 : Blo 1166400 1168343 := bstep (se 1 (by rfl) ⟨876257, by rfl⟩ : syracuseStep 1168343 = 1752515) B1752515
theorem B1168363 : Blo 1166400 1168363 := bstep (se 1 (by rfl) ⟨876272, by rfl⟩ : syracuseStep 1168363 = 1752545) B1752545
theorem B1168375 : Blo 1166400 1168375 := bstep (se 1 (by rfl) ⟨876281, by rfl⟩ : syracuseStep 1168375 = 1752563) B1752563
theorem B8991749 : Blo 1166400 8991749 := bstep (se 4 (by rfl) ⟨842976, by rfl⟩ : syracuseStep 8991749 = 1685953) B1685953
theorem B1168395 : Blo 1166400 1168395 := bstep (se 1 (by rfl) ⟨876296, by rfl⟩ : syracuseStep 1168395 = 1752593) B1752593
theorem B3937355 : Blo 1166400 3937355 := bstep (se 1 (by rfl) ⟨2953016, by rfl⟩ : syracuseStep 3937355 = 5906033) B5906033
theorem B1750091 : Blo 1166400 1750091 := bstep (se 1 (by rfl) ⟨1312568, by rfl⟩ : syracuseStep 1750091 = 2625137) B2625137
theorem B1750103 : Blo 1166400 1750103 := bstep (se 1 (by rfl) ⟨1312577, by rfl⟩ : syracuseStep 1750103 = 2625155) B2625155
theorem B2626649 : Blo 1166400 2626649 := bstep (se 2 (by rfl) ⟨984993, by rfl⟩ : syracuseStep 2626649 = 1969987) B1969987
theorem B5911703 : Blo 1166400 5911703 := bstep (se 1 (by rfl) ⟨4433777, by rfl⟩ : syracuseStep 5911703 = 8867555) B8867555
theorem B1750169 : Blo 1166400 1750169 := bstep (se 2 (by rfl) ⟨656313, by rfl⟩ : syracuseStep 1750169 = 1312627) B1312627
theorem B2626739 : Blo 1166400 2626739 := bstep (se 1 (by rfl) ⟨1970054, by rfl⟩ : syracuseStep 2626739 = 3940109) B3940109
theorem B2626775 : Blo 1166400 2626775 := bstep (se 1 (by rfl) ⟨1970081, by rfl⟩ : syracuseStep 2626775 = 3940163) B3940163
theorem B3323101 : Blo 1166400 3323101 := bstep (se 3 (by rfl) ⟨623081, by rfl⟩ : syracuseStep 3323101 = 1246163) B1246163
theorem B1750283 : Blo 1166400 1750283 := bstep (se 1 (by rfl) ⟨1312712, by rfl⟩ : syracuseStep 1750283 = 2625425) B2625425
theorem B1750295 : Blo 1166400 1750295 := bstep (se 1 (by rfl) ⟨1312721, by rfl⟩ : syracuseStep 1750295 = 2625443) B2625443
theorem B1971479 : Blo 1166400 1971479 := bstep (se 1 (by rfl) ⟨1478609, by rfl⟩ : syracuseStep 1971479 = 2957219) B2957219
theorem B3937625 : Blo 1166400 3937625 := bstep (se 2 (by rfl) ⟨1476609, by rfl⟩ : syracuseStep 3937625 = 2953219) B2953219
theorem B1750361 : Blo 1166400 1750361 := bstep (se 2 (by rfl) ⟨656385, by rfl⟩ : syracuseStep 1750361 = 1312771) B1312771
theorem B16840037 : Blo 1166400 16840037 := bstep (se 4 (by rfl) ⟨1578753, by rfl⟩ : syracuseStep 16840037 = 3157507) B3157507
theorem B2626955 : Blo 1166400 2626955 := bstep (se 1 (by rfl) ⟨1970216, by rfl⟩ : syracuseStep 2626955 = 3940433) B3940433
theorem B1971607 : Blo 1166400 1971607 := bstep (se 1 (by rfl) ⟨1478705, by rfl⟩ : syracuseStep 1971607 = 2957411) B2957411
theorem B19936691 : Blo 1166400 19936691 := bstep (se 1 (by rfl) ⟨14952518, by rfl⟩ : syracuseStep 19936691 = 29905037) B29905037
theorem B4208051 : Blo 1166400 4208051 := bstep (se 1 (by rfl) ⟨3156038, by rfl⟩ : syracuseStep 4208051 = 6312077) B6312077
theorem B2627009 : Blo 1166400 2627009 := bstep (se 2 (by rfl) ⟨985128, by rfl⟩ : syracuseStep 2627009 = 1970257) B1970257
theorem B1750475 : Blo 1166400 1750475 := bstep (se 1 (by rfl) ⟨1312856, by rfl⟩ : syracuseStep 1750475 = 2625713) B2625713
theorem B102282709 : Blo 1166400 102282709 := bstep (se 7 (by rfl) ⟨1198625, by rfl⟩ : syracuseStep 102282709 = 2397251) B2397251
theorem B1750487 : Blo 1166400 1750487 := bstep (se 1 (by rfl) ⟨1312865, by rfl⟩ : syracuseStep 1750487 = 2625731) B2625731
theorem B1750553 : Blo 1166400 1750553 := bstep (se 2 (by rfl) ⟨656457, by rfl⟩ : syracuseStep 1750553 = 1312915) B1312915
theorem B3323443 : Blo 1166400 3323443 := bstep (se 1 (by rfl) ⟨2492582, by rfl⟩ : syracuseStep 3323443 = 4985165) B4985165
theorem B14956163 : Blo 1166400 14956163 := bstep (se 1 (by rfl) ⟨11217122, by rfl⟩ : syracuseStep 14956163 = 22434245) B22434245
theorem B42604163 : Blo 1166400 42604163 := bstep (se 1 (by rfl) ⟨31953122, by rfl⟩ : syracuseStep 42604163 = 63906245) B63906245
theorem B1750667 : Blo 1166400 1750667 := bstep (se 1 (by rfl) ⟨1313000, by rfl⟩ : syracuseStep 1750667 = 2626001) B2626001
theorem B2561675 : Blo 1166400 2561675 := bstep (se 1 (by rfl) ⟨1921256, by rfl⟩ : syracuseStep 2561675 = 3842513) B3842513
theorem B2217611 : Blo 1166400 2217611 := bstep (se 1 (by rfl) ⟨1663208, by rfl⟩ : syracuseStep 2217611 = 3326417) B3326417
theorem B1750679 : Blo 1166400 1750679 := bstep (se 1 (by rfl) ⟨1313009, by rfl⟩ : syracuseStep 1750679 = 2626019) B2626019
theorem B3741335 : Blo 1166400 3741335 := bstep (se 1 (by rfl) ⟨2806001, by rfl⟩ : syracuseStep 3741335 = 5612003) B5612003
theorem B2627225 : Blo 1166400 2627225 := bstep (se 2 (by rfl) ⟨985209, by rfl⟩ : syracuseStep 2627225 = 1970419) B1970419
theorem B2102987 : Blo 1166400 2102987 := bstep (se 1 (by rfl) ⟨1577240, by rfl⟩ : syracuseStep 2102987 = 3154481) B3154481
theorem B21288653 : Blo 1166400 21288653 := bstep (se 3 (by rfl) ⟨3991622, by rfl⟩ : syracuseStep 21288653 = 7983245) B7983245
theorem B1750745 : Blo 1166400 1750745 := bstep (se 2 (by rfl) ⟨656529, by rfl⟩ : syracuseStep 1750745 = 1313059) B1313059
theorem B2627315 : Blo 1166400 2627315 := bstep (se 1 (by rfl) ⟨1970486, by rfl⟩ : syracuseStep 2627315 = 3940973) B3940973
theorem B2627351 : Blo 1166400 2627351 := bstep (se 1 (by rfl) ⟨1970513, by rfl⟩ : syracuseStep 2627351 = 3941027) B3941027
theorem B12613421 : Blo 1166400 12613421 := bstep (se 3 (by rfl) ⟨2365016, by rfl⟩ : syracuseStep 12613421 = 4730033) B4730033
theorem B2217793 : Blo 1166400 2217793 := bstep (se 2 (by rfl) ⟨831672, by rfl⟩ : syracuseStep 2217793 = 1663345) B1663345
theorem B1750859 : Blo 1166400 1750859 := bstep (se 1 (by rfl) ⟨1313144, by rfl⟩ : syracuseStep 1750859 = 2626289) B2626289
theorem B1750871 : Blo 1166400 1750871 := bstep (se 1 (by rfl) ⟨1313153, by rfl⟩ : syracuseStep 1750871 = 2626307) B2626307
theorem B1996633 : Blo 1166400 1996633 := bstep (se 2 (by rfl) ⟨748737, by rfl⟩ : syracuseStep 1996633 = 1497475) B1497475
theorem B4986755 : Blo 1166400 4986755 := bstep (se 1 (by rfl) ⟨3740066, by rfl⟩ : syracuseStep 4986755 = 7480133) B7480133
theorem B1496983 : Blo 1166400 1496983 := bstep (se 1 (by rfl) ⟨1122737, by rfl⟩ : syracuseStep 1496983 = 2245475) B2245475
theorem B1750937 : Blo 1166400 1750937 := bstep (se 2 (by rfl) ⟨656601, by rfl⟩ : syracuseStep 1750937 = 1313203) B1313203
theorem B16816049 : Blo 1166400 16816049 := bstep (se 2 (by rfl) ⟨6306018, by rfl⟩ : syracuseStep 16816049 = 12612037) B12612037
theorem B1775563 : Blo 1166400 1775563 := bstep (se 1 (by rfl) ⟨1331672, by rfl⟩ : syracuseStep 1775563 = 2663345) B2663345
theorem B2627531 : Blo 1166400 2627531 := bstep (se 1 (by rfl) ⟨1970648, by rfl⟩ : syracuseStep 2627531 = 3941297) B3941297
theorem B2627585 : Blo 1166400 2627585 := bstep (se 2 (by rfl) ⟨985344, by rfl⟩ : syracuseStep 2627585 = 1970689) B1970689
theorem B8411141 : Blo 1166400 8411141 := bstep (se 4 (by rfl) ⟨788544, by rfl⟩ : syracuseStep 8411141 = 1577089) B1577089
theorem B1751051 : Blo 1166400 1751051 := bstep (se 1 (by rfl) ⟨1313288, by rfl⟩ : syracuseStep 1751051 = 2626577) B2626577
theorem B3938327 : Blo 1166400 3938327 := bstep (se 1 (by rfl) ⟨2953745, by rfl⟩ : syracuseStep 3938327 = 5907491) B5907491
theorem B1751063 : Blo 1166400 1751063 := bstep (se 1 (by rfl) ⟨1313297, by rfl⟩ : syracuseStep 1751063 = 2626595) B2626595
theorem B1751129 : Blo 1166400 1751129 := bstep (se 2 (by rfl) ⟨656673, by rfl⟩ : syracuseStep 1751129 = 1313347) B1313347
theorem B11212931 : Blo 1166400 11212931 := bstep (se 1 (by rfl) ⟨8409698, by rfl⟩ : syracuseStep 11212931 = 16819397) B16819397
theorem B4429997 : Blo 1166400 4429997 := bstep (se 3 (by rfl) ⟨830624, by rfl⟩ : syracuseStep 4429997 = 1661249) B1661249
theorem B1751243 : Blo 1166400 1751243 := bstep (se 1 (by rfl) ⟨1313432, by rfl⟩ : syracuseStep 1751243 = 2626865) B2626865
theorem B2955467 : Blo 1166400 2955467 := bstep (se 1 (by rfl) ⟨2216600, by rfl⟩ : syracuseStep 2955467 = 4433201) B4433201
theorem B1751255 : Blo 1166400 1751255 := bstep (se 1 (by rfl) ⟨1313441, by rfl⟩ : syracuseStep 1751255 = 2626883) B2626883
theorem B2627801 : Blo 1166400 2627801 := bstep (se 2 (by rfl) ⟨985425, by rfl⟩ : syracuseStep 2627801 = 1970851) B1970851
theorem B1751321 : Blo 1166400 1751321 := bstep (se 2 (by rfl) ⟨656745, by rfl⟩ : syracuseStep 1751321 = 1313491) B1313491
theorem B2627891 : Blo 1166400 2627891 := bstep (se 1 (by rfl) ⟨1970918, by rfl⟩ : syracuseStep 2627891 = 3941837) B3941837
theorem B2627927 : Blo 1166400 2627927 := bstep (se 1 (by rfl) ⟨1970945, by rfl⟩ : syracuseStep 2627927 = 3941891) B3941891
theorem B1661323 : Blo 1166400 1661323 := bstep (se 1 (by rfl) ⟨1245992, by rfl⟩ : syracuseStep 1661323 = 2491985) B2491985
theorem B1751435 : Blo 1166400 1751435 := bstep (se 1 (by rfl) ⟨1313576, by rfl⟩ : syracuseStep 1751435 = 2627153) B2627153
theorem B1751447 : Blo 1166400 1751447 := bstep (se 1 (by rfl) ⟨1313585, by rfl⟩ : syracuseStep 1751447 = 2627171) B2627171
theorem B3324377 : Blo 1166400 3324377 := bstep (se 2 (by rfl) ⟨1246641, by rfl⟩ : syracuseStep 3324377 = 2493283) B2493283
theorem B1751513 : Blo 1166400 1751513 := bstep (se 2 (by rfl) ⟨656817, by rfl⟩ : syracuseStep 1751513 = 1313635) B1313635
theorem B2628107 : Blo 1166400 2628107 := bstep (se 1 (by rfl) ⟨1971080, by rfl⟩ : syracuseStep 2628107 = 3942161) B3942161
theorem B3938867 : Blo 1166400 3938867 := bstep (se 1 (by rfl) ⟨2954150, by rfl⟩ : syracuseStep 3938867 = 5908301) B5908301
theorem B2628161 : Blo 1166400 2628161 := bstep (se 2 (by rfl) ⟨985560, by rfl⟩ : syracuseStep 2628161 = 1971121) B1971121
theorem B1751627 : Blo 1166400 1751627 := bstep (se 1 (by rfl) ⟨1313720, by rfl⟩ : syracuseStep 1751627 = 2627441) B2627441
theorem B1686091 : Blo 1166400 1686091 := bstep (se 1 (by rfl) ⟨1264568, by rfl⟩ : syracuseStep 1686091 = 2529137) B2529137
theorem B1751639 : Blo 1166400 1751639 := bstep (se 1 (by rfl) ⟨1313729, by rfl⟩ : syracuseStep 1751639 = 2627459) B2627459
theorem B5053079 : Blo 1166400 5053079 := bstep (se 1 (by rfl) ⟨3789809, by rfl⟩ : syracuseStep 5053079 = 7579619) B7579619
theorem B1751705 : Blo 1166400 1751705 := bstep (se 2 (by rfl) ⟨656889, by rfl⟩ : syracuseStep 1751705 = 1313779) B1313779
theorem B1751819 : Blo 1166400 1751819 := bstep (se 1 (by rfl) ⟨1313864, by rfl⟩ : syracuseStep 1751819 = 2627729) B2627729
theorem B8411921 : Blo 1166400 8411921 := bstep (se 2 (by rfl) ⟨3154470, by rfl⟩ : syracuseStep 8411921 = 6308941) B6308941
theorem B1751831 : Blo 1166400 1751831 := bstep (se 1 (by rfl) ⟨1313873, by rfl⟩ : syracuseStep 1751831 = 2627747) B2627747
theorem B2628377 : Blo 1166400 2628377 := bstep (se 2 (by rfl) ⟨985641, by rfl⟩ : syracuseStep 2628377 = 1971283) B1971283
theorem B3939137 : Blo 1166400 3939137 := bstep (se 2 (by rfl) ⟨1477176, by rfl⟩ : syracuseStep 3939137 = 2954353) B2954353
theorem B1751897 : Blo 1166400 1751897 := bstep (se 2 (by rfl) ⟨656961, by rfl⟩ : syracuseStep 1751897 = 1313923) B1313923
theorem B2628467 : Blo 1166400 2628467 := bstep (se 1 (by rfl) ⟨1971350, by rfl⟩ : syracuseStep 2628467 = 3942701) B3942701
theorem B2628503 : Blo 1166400 2628503 := bstep (se 1 (by rfl) ⟨1971377, by rfl⟩ : syracuseStep 2628503 = 3942755) B3942755
theorem B4430771 : Blo 1166400 4430771 := bstep (se 1 (by rfl) ⟨3323078, by rfl⟩ : syracuseStep 4430771 = 6646157) B6646157
theorem B1752011 : Blo 1166400 1752011 := bstep (se 1 (by rfl) ⟨1314008, by rfl⟩ : syracuseStep 1752011 = 2628017) B2628017
theorem B1752023 : Blo 1166400 1752023 := bstep (se 1 (by rfl) ⟨1314017, by rfl⟩ : syracuseStep 1752023 = 2628035) B2628035
theorem B1752089 : Blo 1166400 1752089 := bstep (se 2 (by rfl) ⟨657033, by rfl⟩ : syracuseStep 1752089 = 1314067) B1314067
theorem B8870957 : Blo 1166400 8870957 := bstep (se 3 (by rfl) ⟨1663304, by rfl⟩ : syracuseStep 8870957 = 3326609) B3326609
theorem B9600065 : Blo 1166400 9600065 := bstep (se 2 (by rfl) ⟨3600024, by rfl⟩ : syracuseStep 9600065 = 7200049) B7200049
theorem B2628683 : Blo 1166400 2628683 := bstep (se 1 (by rfl) ⟨1971512, by rfl⟩ : syracuseStep 2628683 = 3943025) B3943025
theorem B2628737 : Blo 1166400 2628737 := bstep (se 2 (by rfl) ⟨985776, by rfl⟩ : syracuseStep 2628737 = 1971553) B1971553
theorem B1752203 : Blo 1166400 1752203 := bstep (se 1 (by rfl) ⟨1314152, by rfl⟩ : syracuseStep 1752203 = 2628305) B2628305
theorem B6651031 : Blo 1166400 6651031 := bstep (se 1 (by rfl) ⟨4988273, by rfl⟩ : syracuseStep 6651031 = 9976547) B9976547
theorem B2956439 : Blo 1166400 2956439 := bstep (se 1 (by rfl) ⟨2217329, by rfl⟩ : syracuseStep 2956439 = 4434659) B4434659
theorem B1752215 : Blo 1166400 1752215 := bstep (se 1 (by rfl) ⟨1314161, by rfl⟩ : syracuseStep 1752215 = 2628323) B2628323
theorem B1752281 : Blo 1166400 1752281 := bstep (se 2 (by rfl) ⟨657105, by rfl⟩ : syracuseStep 1752281 = 1314211) B1314211
theorem B19176689 : Blo 1166400 19176689 := bstep (se 2 (by rfl) ⟨7191258, by rfl⟩ : syracuseStep 19176689 = 14382517) B14382517
theorem B5905709 : Blo 1166400 5905709 := bstep (se 3 (by rfl) ⟨1107320, by rfl⟩ : syracuseStep 5905709 = 2214641) B2214641
theorem B1752395 : Blo 1166400 1752395 := bstep (se 1 (by rfl) ⟨1314296, by rfl⟩ : syracuseStep 1752395 = 2628593) B2628593
theorem B1752407 : Blo 1166400 1752407 := bstep (se 1 (by rfl) ⟨1314305, by rfl⟩ : syracuseStep 1752407 = 2628611) B2628611
theorem B3939677 : Blo 1166400 3939677 := bstep (se 3 (by rfl) ⟨738689, by rfl⟩ : syracuseStep 3939677 = 1477379) B1477379
theorem B4734301 : Blo 1166400 4734301 := bstep (se 3 (by rfl) ⟨887681, by rfl⟩ : syracuseStep 4734301 = 1775363) B1775363
theorem B1752473 : Blo 1166400 1752473 := bstep (se 2 (by rfl) ⟨657177, by rfl⟩ : syracuseStep 1752473 = 1314355) B1314355
theorem B8863181 : Blo 1166400 8863181 := bstep (se 3 (by rfl) ⟨1661846, by rfl⟩ : syracuseStep 8863181 = 3323693) B3323693
theorem B1752587 : Blo 1166400 1752587 := bstep (se 1 (by rfl) ⟨1314440, by rfl⟩ : syracuseStep 1752587 = 2628881) B2628881
theorem B1752599 : Blo 1166400 1752599 := bstep (se 1 (by rfl) ⟨1314449, by rfl⟩ : syracuseStep 1752599 = 2628899) B2628899
theorem B1662553 : Blo 1166400 1662553 := bstep (se 2 (by rfl) ⟨623457, by rfl⟩ : syracuseStep 1662553 = 1246915) B1246915
theorem B2957107 : Blo 1166400 2957107 := bstep (se 1 (by rfl) ⟨2217830, by rfl⟩ : syracuseStep 2957107 = 4435661) B4435661
theorem B3325789 : Blo 1166400 3325789 := bstep (se 3 (by rfl) ⟨623585, by rfl⟩ : syracuseStep 3325789 = 1247171) B1247171
theorem B8863667 : Blo 1166400 8863667 := bstep (se 1 (by rfl) ⟨6647750, by rfl⟩ : syracuseStep 8863667 = 13295501) B13295501
theorem B2957249 : Blo 1166400 2957249 := bstep (se 2 (by rfl) ⟨1108968, by rfl⟩ : syracuseStep 2957249 = 2217937) B2217937
theorem B6643741 : Blo 1166400 6643741 := bstep (se 3 (by rfl) ⟨1245701, by rfl⟩ : syracuseStep 6643741 = 2491403) B2491403
theorem B5988419 : Blo 1166400 5988419 := bstep (se 1 (by rfl) ⟨4491314, by rfl⟩ : syracuseStep 5988419 = 8982629) B8982629
theorem B5906519 : Blo 1166400 5906519 := bstep (se 1 (by rfl) ⟨4429889, by rfl⟩ : syracuseStep 5906519 = 8859779) B8859779
theorem B2957431 : Blo 1166400 2957431 := bstep (se 1 (by rfl) ⟨2218073, by rfl⟩ : syracuseStep 2957431 = 4436147) B4436147
theorem B9470189 : Blo 1166400 9470189 := bstep (se 3 (by rfl) ⟨1775660, by rfl⟩ : syracuseStep 9470189 = 3551321) B3551321
theorem B7102835 : Blo 1166400 7102835 := bstep (se 1 (by rfl) ⟨5327126, by rfl⟩ : syracuseStep 7102835 = 10654253) B10654253
theorem B6652307 : Blo 1166400 6652307 := bstep (se 1 (by rfl) ⟨4989230, by rfl⟩ : syracuseStep 6652307 = 9978461) B9978461
theorem B32407955 : Blo 1166400 32407955 := bstep (se 1 (by rfl) ⟨24305966, by rfl⟩ : syracuseStep 32407955 = 48611933) B48611933
theorem B13304249 : Blo 1166400 13304249 := bstep (se 2 (by rfl) ⟨4989093, by rfl⟩ : syracuseStep 13304249 = 9978187) B9978187
theorem B6644267 : Blo 1166400 6644267 := bstep (se 1 (by rfl) ⟨4983200, by rfl⟩ : syracuseStep 6644267 = 9966401) B9966401
theorem B4432427 : Blo 1166400 4432427 := bstep (se 1 (by rfl) ⟨3324320, by rfl⟩ : syracuseStep 4432427 = 6648641) B6648641
theorem B5907005 : Blo 1166400 5907005 := bstep (se 3 (by rfl) ⟨1107563, by rfl⟩ : syracuseStep 5907005 = 2215127) B2215127
theorem B1401463 : Blo 1166400 1401463 := bstep (se 1 (by rfl) ⟨1051097, by rfl⟩ : syracuseStep 1401463 = 2102195) B2102195
theorem B3154567 : Blo 1166400 3154567 := bstep (se 1 (by rfl) ⟨2365925, by rfl⟩ : syracuseStep 3154567 = 4731851) B4731851
theorem B3941135 : Blo 1166400 3941135 := bstep (se 1 (by rfl) ⟨2955851, by rfl⟩ : syracuseStep 3941135 = 5911703) B5911703
theorem B14598947 : Blo 1166400 14598947 := bstep (se 1 (by rfl) ⟨10949210, by rfl⟩ : syracuseStep 14598947 = 21898421) B21898421
theorem B1246223 : Blo 1166400 1246223 := bstep (se 1 (by rfl) ⟨934667, by rfl⟩ : syracuseStep 1246223 = 1869335) B1869335
theorem B3941405 : Blo 1166400 3941405 := bstep (se 3 (by rfl) ⟨739013, by rfl⟩ : syracuseStep 3941405 = 1478027) B1478027
theorem B2843681 : Blo 1166400 2843681 := bstep (se 2 (by rfl) ⟨1066380, by rfl⟩ : syracuseStep 2843681 = 2132761) B2132761
theorem B9970775 : Blo 1166400 9970775 := bstep (se 1 (by rfl) ⟨7478081, by rfl⟩ : syracuseStep 9970775 = 14956163) B14956163
theorem B28402775 : Blo 1166400 28402775 := bstep (se 1 (by rfl) ⟨21302081, by rfl⟩ : syracuseStep 28402775 = 42604163) B42604163
theorem B6653015 : Blo 1166400 6653015 := bstep (se 1 (by rfl) ⟨4989761, by rfl⟩ : syracuseStep 6653015 = 9979523) B9979523
theorem B1401991 : Blo 1166400 1401991 := bstep (se 1 (by rfl) ⟨1051493, by rfl⟩ : syracuseStep 1401991 = 2102987) B2102987
theorem B1246351 : Blo 1166400 1246351 := bstep (se 1 (by rfl) ⟨934763, by rfl⟩ : syracuseStep 1246351 = 1869527) B1869527
theorem B10643021 : Blo 1166400 10643021 := bstep (se 3 (by rfl) ⟨1995566, by rfl⟩ : syracuseStep 10643021 = 3991133) B3991133
theorem B1312519 : Blo 1166400 1312519 := bstep (se 1 (by rfl) ⟨984389, by rfl⟩ : syracuseStep 1312519 = 1968779) B1968779
theorem B3368719 : Blo 1166400 3368719 := bstep (se 1 (by rfl) ⟨2526539, by rfl⟩ : syracuseStep 3368719 = 5053079) B5053079
theorem B2246459 : Blo 1166400 2246459 := bstep (se 1 (by rfl) ⟨1684844, by rfl⟩ : syracuseStep 2246459 = 3369689) B3369689
theorem B35915633 : Blo 1166400 35915633 := bstep (se 2 (by rfl) ⟨13468362, by rfl⟩ : syracuseStep 35915633 = 26936725) B26936725
theorem B1312699 : Blo 1166400 1312699 := bstep (se 1 (by rfl) ⟨984524, by rfl⟩ : syracuseStep 1312699 = 1969049) B1969049
theorem B6645725 : Blo 1166400 6645725 := bstep (se 3 (by rfl) ⟨1246073, by rfl⟩ : syracuseStep 6645725 = 2492147) B2492147
theorem B6400043 : Blo 1166400 6400043 := bstep (se 1 (by rfl) ⟨4800032, by rfl⟩ : syracuseStep 6400043 = 9600065) B9600065
theorem B1968313 : Blo 1166400 1968313 := bstep (se 2 (by rfl) ⟨738117, by rfl⟩ : syracuseStep 1968313 = 1476235) B1476235
theorem B19949813 : Blo 1166400 19949813 := bstep (se 5 (by rfl) ⟨935147, by rfl⟩ : syracuseStep 19949813 = 1870295) B1870295
theorem B5908787 : Blo 1166400 5908787 := bstep (se 1 (by rfl) ⟨4431590, by rfl⟩ : syracuseStep 5908787 = 8863181) B8863181
theorem B1313167 : Blo 1166400 1313167 := bstep (se 1 (by rfl) ⟨984875, by rfl⟩ : syracuseStep 1313167 = 1969751) B1969751
theorem B3942809 : Blo 1166400 3942809 := bstep (se 2 (by rfl) ⟨1478553, by rfl⟩ : syracuseStep 3942809 = 2957107) B2957107
theorem B2492873 : Blo 1166400 2492873 := bstep (se 2 (by rfl) ⟨934827, by rfl⟩ : syracuseStep 2492873 = 1869655) B1869655
theorem B8415697 : Blo 1166400 8415697 := bstep (se 2 (by rfl) ⟨3155886, by rfl⟩ : syracuseStep 8415697 = 6311773) B6311773
theorem B4434385 : Blo 1166400 4434385 := bstep (se 2 (by rfl) ⟨1662894, by rfl⟩ : syracuseStep 4434385 = 3325789) B3325789
theorem B1477111 : Blo 1166400 1477111 := bstep (se 1 (by rfl) ⟨1107833, by rfl⟩ : syracuseStep 1477111 = 2215667) B2215667
theorem B4729373 : Blo 1166400 4729373 := bstep (se 3 (by rfl) ⟨886757, by rfl⟩ : syracuseStep 4729373 = 1773515) B1773515
theorem B5605949 : Blo 1166400 5605949 := bstep (se 3 (by rfl) ⟨1051115, by rfl⟩ : syracuseStep 5605949 = 2102231) B2102231
theorem B5909111 : Blo 1166400 5909111 := bstep (se 1 (by rfl) ⟨4431833, by rfl⟩ : syracuseStep 5909111 = 8863667) B8863667
theorem B2214535 : Blo 1166400 2214535 := bstep (se 1 (by rfl) ⟨1660901, by rfl⟩ : syracuseStep 2214535 = 3321803) B3321803
theorem B4434689 : Blo 1166400 4434689 := bstep (se 2 (by rfl) ⟨1663008, by rfl⟩ : syracuseStep 4434689 = 3326017) B3326017
theorem B1477435 : Blo 1166400 1477435 := bstep (se 1 (by rfl) ⟨1108076, by rfl⟩ : syracuseStep 1477435 = 2216153) B2216153
theorem B1969015 : Blo 1166400 1969015 := bstep (se 1 (by rfl) ⟨1476761, by rfl⟩ : syracuseStep 1969015 = 2953523) B2953523
theorem B1313671 : Blo 1166400 1313671 := bstep (se 1 (by rfl) ⟨985253, by rfl⟩ : syracuseStep 1313671 = 1970507) B1970507
theorem B1969211 : Blo 1166400 1969211 := bstep (se 1 (by rfl) ⟨1476908, by rfl⟩ : syracuseStep 1969211 = 2953817) B2953817
theorem B1313851 : Blo 1166400 1313851 := bstep (se 1 (by rfl) ⟨985388, by rfl⟩ : syracuseStep 1313851 = 1970777) B1970777
theorem B1166471 : Blo 1166400 1166471 := bstep (se 1 (by rfl) ⟨874853, by rfl⟩ : syracuseStep 1166471 = 1749707) B1749707
theorem B1166479 : Blo 1166400 1166479 := bstep (se 1 (by rfl) ⟨874859, by rfl⟩ : syracuseStep 1166479 = 1749719) B1749719
theorem B2215097 : Blo 1166400 2215097 := bstep (se 2 (by rfl) ⟨830661, by rfl⟩ : syracuseStep 2215097 = 1661323) B1661323
theorem B2493625 : Blo 1166400 2493625 := bstep (se 2 (by rfl) ⟨935109, by rfl⟩ : syracuseStep 2493625 = 1870219) B1870219
theorem B1166523 : Blo 1166400 1166523 := bstep (se 1 (by rfl) ⟨874892, by rfl⟩ : syracuseStep 1166523 = 1749785) B1749785
theorem B4435145 : Blo 1166400 4435145 := bstep (se 2 (by rfl) ⟨1663179, by rfl⟩ : syracuseStep 4435145 = 3326359) B3326359
theorem B1166599 : Blo 1166400 1166599 := bstep (se 1 (by rfl) ⟨874949, by rfl⟩ : syracuseStep 1166599 = 1749899) B1749899
theorem B1166607 : Blo 1166400 1166607 := bstep (se 1 (by rfl) ⟨874955, by rfl⟩ : syracuseStep 1166607 = 1749911) B1749911
theorem B51137837 : Blo 1166400 51137837 := bstep (se 3 (by rfl) ⟨9588344, by rfl⟩ : syracuseStep 51137837 = 19176689) B19176689
theorem B1166651 : Blo 1166400 1166651 := bstep (se 1 (by rfl) ⟨874988, by rfl⟩ : syracuseStep 1166651 = 1749977) B1749977
theorem B2624903 : Blo 1166400 2624903 := bstep (se 1 (by rfl) ⟨1968677, by rfl⟩ : syracuseStep 2624903 = 3937355) B3937355
theorem B1166727 : Blo 1166400 1166727 := bstep (se 1 (by rfl) ⟨875045, by rfl⟩ : syracuseStep 1166727 = 1750091) B1750091
theorem B1166735 : Blo 1166400 1166735 := bstep (se 1 (by rfl) ⟨875051, by rfl⟩ : syracuseStep 1166735 = 1750103) B1750103
theorem B2248121 : Blo 1166400 2248121 := bstep (se 2 (by rfl) ⟨843045, by rfl⟩ : syracuseStep 2248121 = 1686091) B1686091
theorem B1166779 : Blo 1166400 1166779 := bstep (se 1 (by rfl) ⟨875084, by rfl⟩ : syracuseStep 1166779 = 1750169) B1750169
theorem B1969609 : Blo 1166400 1969609 := bstep (se 2 (by rfl) ⟨738603, by rfl⟩ : syracuseStep 1969609 = 1477207) B1477207
theorem B1166855 : Blo 1166400 1166855 := bstep (se 1 (by rfl) ⟨875141, by rfl⟩ : syracuseStep 1166855 = 1750283) B1750283
theorem B1166863 : Blo 1166400 1166863 := bstep (se 1 (by rfl) ⟨875147, by rfl⟩ : syracuseStep 1166863 = 1750295) B1750295
theorem B1314319 : Blo 1166400 1314319 := bstep (se 1 (by rfl) ⟨985739, by rfl⟩ : syracuseStep 1314319 = 1971479) B1971479
theorem B2625083 : Blo 1166400 2625083 := bstep (se 1 (by rfl) ⟨1968812, by rfl⟩ : syracuseStep 2625083 = 3937625) B3937625
theorem B1166907 : Blo 1166400 1166907 := bstep (se 1 (by rfl) ⟨875180, by rfl⟩ : syracuseStep 1166907 = 1750361) B1750361
theorem B5910083 : Blo 1166400 5910083 := bstep (se 1 (by rfl) ⟨4432562, by rfl⟩ : syracuseStep 5910083 = 8865125) B8865125
theorem B11226691 : Blo 1166400 11226691 := bstep (se 1 (by rfl) ⟨8420018, by rfl⟩ : syracuseStep 11226691 = 16840037) B16840037
theorem B13291127 : Blo 1166400 13291127 := bstep (se 1 (by rfl) ⟨9968345, by rfl⟩ : syracuseStep 13291127 = 19936691) B19936691
theorem B2805367 : Blo 1166400 2805367 := bstep (se 1 (by rfl) ⟨2104025, by rfl⟩ : syracuseStep 2805367 = 4208051) B4208051
theorem B1166983 : Blo 1166400 1166983 := bstep (se 1 (by rfl) ⟨875237, by rfl⟩ : syracuseStep 1166983 = 1750475) B1750475
theorem B1166991 : Blo 1166400 1166991 := bstep (se 1 (by rfl) ⟨875243, by rfl⟩ : syracuseStep 1166991 = 1750487) B1750487
theorem B2625209 : Blo 1166400 2625209 := bstep (se 2 (by rfl) ⟨984453, by rfl⟩ : syracuseStep 2625209 = 1968907) B1968907
theorem B1167035 : Blo 1166400 1167035 := bstep (se 1 (by rfl) ⟨875276, by rfl⟩ : syracuseStep 1167035 = 1750553) B1750553
theorem B1167111 : Blo 1166400 1167111 := bstep (se 1 (by rfl) ⟨875333, by rfl⟩ : syracuseStep 1167111 = 1750667) B1750667
theorem B1478407 : Blo 1166400 1478407 := bstep (se 1 (by rfl) ⟨1108805, by rfl⟩ : syracuseStep 1478407 = 2217611) B2217611
theorem B1167119 : Blo 1166400 1167119 := bstep (se 1 (by rfl) ⟨875339, by rfl⟩ : syracuseStep 1167119 = 1750679) B1750679
theorem B2494223 : Blo 1166400 2494223 := bstep (se 1 (by rfl) ⟨1870667, by rfl⟩ : syracuseStep 2494223 = 3741335) B3741335
theorem B3157789 : Blo 1166400 3157789 := bstep (se 3 (by rfl) ⟨592085, by rfl⟩ : syracuseStep 3157789 = 1184171) B1184171
theorem B3321643 : Blo 1166400 3321643 := bstep (se 1 (by rfl) ⟨2491232, by rfl⟩ : syracuseStep 3321643 = 4982465) B4982465
theorem B14192435 : Blo 1166400 14192435 := bstep (se 1 (by rfl) ⟨10644326, by rfl⟩ : syracuseStep 14192435 = 21288653) B21288653
theorem B4730683 : Blo 1166400 4730683 := bstep (se 1 (by rfl) ⟨3548012, by rfl⟩ : syracuseStep 4730683 = 7096025) B7096025
theorem B1167163 : Blo 1166400 1167163 := bstep (se 1 (by rfl) ⟨875372, by rfl⟩ : syracuseStep 1167163 = 1750745) B1750745
theorem B8408947 : Blo 1166400 8408947 := bstep (se 1 (by rfl) ⟨6306710, by rfl⟩ : syracuseStep 8408947 = 12613421) B12613421
theorem B1167239 : Blo 1166400 1167239 := bstep (se 1 (by rfl) ⟨875429, by rfl⟩ : syracuseStep 1167239 = 1750859) B1750859
theorem B5910407 : Blo 1166400 5910407 := bstep (se 1 (by rfl) ⟨4432805, by rfl⟩ : syracuseStep 5910407 = 8865611) B8865611
theorem B1167247 : Blo 1166400 1167247 := bstep (se 1 (by rfl) ⟨875435, by rfl⟩ : syracuseStep 1167247 = 1750871) B1750871
theorem B1167291 : Blo 1166400 1167291 := bstep (se 1 (by rfl) ⟨875468, by rfl⟩ : syracuseStep 1167291 = 1750937) B1750937
theorem B11210699 : Blo 1166400 11210699 := bstep (se 1 (by rfl) ⟨8408024, by rfl⟩ : syracuseStep 11210699 = 16816049) B16816049
theorem B16838603 : Blo 1166400 16838603 := bstep (se 1 (by rfl) ⟨12628952, by rfl⟩ : syracuseStep 16838603 = 25257905) B25257905
theorem B5607427 : Blo 1166400 5607427 := bstep (se 1 (by rfl) ⟨4205570, by rfl⟩ : syracuseStep 5607427 = 8411141) B8411141
theorem B1167367 : Blo 1166400 1167367 := bstep (se 1 (by rfl) ⟨875525, by rfl⟩ : syracuseStep 1167367 = 1751051) B1751051
theorem B2625551 : Blo 1166400 2625551 := bstep (se 1 (by rfl) ⟨1969163, by rfl⟩ : syracuseStep 2625551 = 3938327) B3938327
theorem B1167375 : Blo 1166400 1167375 := bstep (se 1 (by rfl) ⟨875531, by rfl⟩ : syracuseStep 1167375 = 1751063) B1751063
theorem B2625569 : Blo 1166400 2625569 := bstep (se 2 (by rfl) ⟨984588, by rfl⟩ : syracuseStep 2625569 = 1969177) B1969177
theorem B26980397 : Blo 1166400 26980397 := bstep (se 3 (by rfl) ⟨5058824, by rfl⟩ : syracuseStep 26980397 = 10117649) B10117649
theorem B1167419 : Blo 1166400 1167419 := bstep (se 1 (by rfl) ⟨875564, by rfl⟩ : syracuseStep 1167419 = 1751129) B1751129
theorem B3321917 : Blo 1166400 3321917 := bstep (se 3 (by rfl) ⟨622859, by rfl⟩ : syracuseStep 3321917 = 1245719) B1245719
theorem B7475287 : Blo 1166400 7475287 := bstep (se 1 (by rfl) ⟨5606465, by rfl⟩ : syracuseStep 7475287 = 11212931) B11212931
theorem B2953331 : Blo 1166400 2953331 := bstep (se 1 (by rfl) ⟨2214998, by rfl⟩ : syracuseStep 2953331 = 4429997) B4429997
theorem B27324533 : Blo 1166400 27324533 := bstep (se 5 (by rfl) ⟨1280837, by rfl⟩ : syracuseStep 27324533 = 2561675) B2561675
theorem B1167495 : Blo 1166400 1167495 := bstep (se 1 (by rfl) ⟨875621, by rfl⟩ : syracuseStep 1167495 = 1751243) B1751243
theorem B1970311 : Blo 1166400 1970311 := bstep (se 1 (by rfl) ⟨1477733, by rfl⟩ : syracuseStep 1970311 = 2955467) B2955467
theorem B1167503 : Blo 1166400 1167503 := bstep (se 1 (by rfl) ⟨875627, by rfl⟩ : syracuseStep 1167503 = 1751255) B1751255
theorem B1167547 : Blo 1166400 1167547 := bstep (se 1 (by rfl) ⟨875660, by rfl⟩ : syracuseStep 1167547 = 1751321) B1751321
theorem B8868041 : Blo 1166400 8868041 := bstep (se 2 (by rfl) ⟨3325515, by rfl⟩ : syracuseStep 8868041 = 6651031) B6651031
theorem B1167623 : Blo 1166400 1167623 := bstep (se 1 (by rfl) ⟨875717, by rfl⟩ : syracuseStep 1167623 = 1751435) B1751435
theorem B1167631 : Blo 1166400 1167631 := bstep (se 1 (by rfl) ⟨875723, by rfl⟩ : syracuseStep 1167631 = 1751447) B1751447
theorem B6648115 : Blo 1166400 6648115 := bstep (se 1 (by rfl) ⟨4986086, by rfl⟩ : syracuseStep 6648115 = 9972173) B9972173
theorem B2216251 : Blo 1166400 2216251 := bstep (se 1 (by rfl) ⟨1662188, by rfl⟩ : syracuseStep 2216251 = 3324377) B3324377
theorem B1167675 : Blo 1166400 1167675 := bstep (se 1 (by rfl) ⟨875756, by rfl⟩ : syracuseStep 1167675 = 1751513) B1751513
theorem B2625911 : Blo 1166400 2625911 := bstep (se 1 (by rfl) ⟨1969433, by rfl⟩ : syracuseStep 2625911 = 3938867) B3938867
theorem B14578055 : Blo 1166400 14578055 := bstep (se 1 (by rfl) ⟨10933541, by rfl⟩ : syracuseStep 14578055 = 21867083) B21867083
theorem B1167751 : Blo 1166400 1167751 := bstep (se 1 (by rfl) ⟨875813, by rfl⟩ : syracuseStep 1167751 = 1751627) B1751627
theorem B1167759 : Blo 1166400 1167759 := bstep (se 1 (by rfl) ⟨875819, by rfl⟩ : syracuseStep 1167759 = 1751639) B1751639
theorem B3322259 : Blo 1166400 3322259 := bstep (se 1 (by rfl) ⟨2491694, by rfl⟩ : syracuseStep 3322259 = 4983389) B4983389
theorem B1167803 : Blo 1166400 1167803 := bstep (se 1 (by rfl) ⟨875852, by rfl⟩ : syracuseStep 1167803 = 1751705) B1751705
theorem B6312401 : Blo 1166400 6312401 := bstep (se 2 (by rfl) ⟨2367150, by rfl⟩ : syracuseStep 6312401 = 4734301) B4734301
theorem B21303773 : Blo 1166400 21303773 := bstep (se 3 (by rfl) ⟨3994457, by rfl⟩ : syracuseStep 21303773 = 7988915) B7988915
theorem B1167879 : Blo 1166400 1167879 := bstep (se 1 (by rfl) ⟨875909, by rfl⟩ : syracuseStep 1167879 = 1751819) B1751819
theorem B5607947 : Blo 1166400 5607947 := bstep (se 1 (by rfl) ⟨4205960, by rfl⟩ : syracuseStep 5607947 = 8411921) B8411921
theorem B1167887 : Blo 1166400 1167887 := bstep (se 1 (by rfl) ⟨875915, by rfl⟩ : syracuseStep 1167887 = 1751831) B1751831
theorem B2626091 : Blo 1166400 2626091 := bstep (se 1 (by rfl) ⟨1969568, by rfl⟩ : syracuseStep 2626091 = 3939137) B3939137
theorem B1167931 : Blo 1166400 1167931 := bstep (se 1 (by rfl) ⟨875948, by rfl⟩ : syracuseStep 1167931 = 1751897) B1751897
theorem B136376945 : Blo 1166400 136376945 := bstep (se 2 (by rfl) ⟨51141354, by rfl⟩ : syracuseStep 136376945 = 102282709) B102282709
theorem B1749623 : Blo 1166400 1749623 := bstep (se 1 (by rfl) ⟨1312217, by rfl⟩ : syracuseStep 1749623 = 2624435) B2624435
theorem B2953847 : Blo 1166400 2953847 := bstep (se 1 (by rfl) ⟨2215385, by rfl⟩ : syracuseStep 2953847 = 4430771) B4430771
theorem B1168007 : Blo 1166400 1168007 := bstep (se 1 (by rfl) ⟨876005, by rfl⟩ : syracuseStep 1168007 = 1752011) B1752011
theorem B1749647 : Blo 1166400 1749647 := bstep (se 1 (by rfl) ⟨1312235, by rfl⟩ : syracuseStep 1749647 = 2624471) B2624471
theorem B1168015 : Blo 1166400 1168015 := bstep (se 1 (by rfl) ⟨876011, by rfl⟩ : syracuseStep 1168015 = 1752023) B1752023
theorem B1749689 : Blo 1166400 1749689 := bstep (se 2 (by rfl) ⟨656133, by rfl⟩ : syracuseStep 1749689 = 1312267) B1312267
theorem B1168059 : Blo 1166400 1168059 := bstep (se 1 (by rfl) ⟨876044, by rfl⟩ : syracuseStep 1168059 = 1752089) B1752089
theorem B1749767 : Blo 1166400 1749767 := bstep (se 1 (by rfl) ⟨1312325, by rfl⟩ : syracuseStep 1749767 = 2624651) B2624651
theorem B1168135 : Blo 1166400 1168135 := bstep (se 1 (by rfl) ⟨876101, by rfl⟩ : syracuseStep 1168135 = 1752203) B1752203
theorem B1970959 : Blo 1166400 1970959 := bstep (se 1 (by rfl) ⟨1478219, by rfl⟩ : syracuseStep 1970959 = 2956439) B2956439
theorem B1168143 : Blo 1166400 1168143 := bstep (se 1 (by rfl) ⟨876107, by rfl⟩ : syracuseStep 1168143 = 1752215) B1752215
theorem B2216737 : Blo 1166400 2216737 := bstep (se 2 (by rfl) ⟨831276, by rfl⟩ : syracuseStep 2216737 = 1662553) B1662553
theorem B1749803 : Blo 1166400 1749803 := bstep (se 1 (by rfl) ⟨1312352, by rfl⟩ : syracuseStep 1749803 = 2624705) B2624705
theorem B1168187 : Blo 1166400 1168187 := bstep (se 1 (by rfl) ⟨876140, by rfl⟩ : syracuseStep 1168187 = 1752281) B1752281
theorem B1749833 : Blo 1166400 1749833 := bstep (se 2 (by rfl) ⟨656187, by rfl⟩ : syracuseStep 1749833 = 1312375) B1312375
theorem B3937139 : Blo 1166400 3937139 := bstep (se 1 (by rfl) ⟨2952854, by rfl⟩ : syracuseStep 3937139 = 5905709) B5905709
theorem B1168263 : Blo 1166400 1168263 := bstep (se 1 (by rfl) ⟨876197, by rfl⟩ : syracuseStep 1168263 = 1752395) B1752395
theorem B1168271 : Blo 1166400 1168271 := bstep (se 1 (by rfl) ⟨876203, by rfl⟩ : syracuseStep 1168271 = 1752407) B1752407
theorem B2626451 : Blo 1166400 2626451 := bstep (se 1 (by rfl) ⟨1969838, by rfl⟩ : syracuseStep 2626451 = 3939677) B3939677
theorem B1749947 : Blo 1166400 1749947 := bstep (se 1 (by rfl) ⟨1312460, by rfl⟩ : syracuseStep 1749947 = 2624921) B2624921
theorem B1168315 : Blo 1166400 1168315 := bstep (se 1 (by rfl) ⟨876236, by rfl⟩ : syracuseStep 1168315 = 1752473) B1752473
theorem B2626505 : Blo 1166400 2626505 := bstep (se 2 (by rfl) ⟨984939, by rfl⟩ : syracuseStep 2626505 = 1969879) B1969879
theorem B1750007 : Blo 1166400 1750007 := bstep (se 1 (by rfl) ⟨1312505, by rfl⟩ : syracuseStep 1750007 = 2625011) B2625011
theorem B1168391 : Blo 1166400 1168391 := bstep (se 1 (by rfl) ⟨876293, by rfl⟩ : syracuseStep 1168391 = 1752587) B1752587
theorem B1750031 : Blo 1166400 1750031 := bstep (se 1 (by rfl) ⟨1312523, by rfl⟩ : syracuseStep 1750031 = 2625047) B2625047
theorem B1168399 : Blo 1166400 1168399 := bstep (se 1 (by rfl) ⟨876299, by rfl⟩ : syracuseStep 1168399 = 1752599) B1752599
theorem B1750073 : Blo 1166400 1750073 := bstep (se 2 (by rfl) ⟨656277, by rfl⟩ : syracuseStep 1750073 = 1312555) B1312555
theorem B1750151 : Blo 1166400 1750151 := bstep (se 1 (by rfl) ⟨1312613, by rfl⟩ : syracuseStep 1750151 = 2625227) B2625227
theorem B1750187 : Blo 1166400 1750187 := bstep (se 1 (by rfl) ⟨1312640, by rfl⟩ : syracuseStep 1750187 = 2625281) B2625281
theorem B1750217 : Blo 1166400 1750217 := bstep (se 2 (by rfl) ⟨656331, by rfl⟩ : syracuseStep 1750217 = 1312663) B1312663
theorem B1995977 : Blo 1166400 1995977 := bstep (se 2 (by rfl) ⟨748491, by rfl⟩ : syracuseStep 1995977 = 1496983) B1496983
theorem B1971499 : Blo 1166400 1971499 := bstep (se 1 (by rfl) ⟨1478624, by rfl⟩ : syracuseStep 1971499 = 2957249) B2957249
theorem B1750331 : Blo 1166400 1750331 := bstep (se 1 (by rfl) ⟨1312748, by rfl⟩ : syracuseStep 1750331 = 2625497) B2625497
theorem B1750391 : Blo 1166400 1750391 := bstep (se 1 (by rfl) ⟨1312793, by rfl⟩ : syracuseStep 1750391 = 2625587) B2625587
theorem B23950727 : Blo 1166400 23950727 := bstep (se 1 (by rfl) ⟨17963045, by rfl⟩ : syracuseStep 23950727 = 35926091) B35926091
theorem B1750415 : Blo 1166400 1750415 := bstep (se 1 (by rfl) ⟨1312811, by rfl⟩ : syracuseStep 1750415 = 2625623) B2625623
theorem B1750457 : Blo 1166400 1750457 := bstep (se 2 (by rfl) ⟨656421, by rfl⟩ : syracuseStep 1750457 = 1312843) B1312843
theorem B1971641 : Blo 1166400 1971641 := bstep (se 2 (by rfl) ⟨739365, by rfl⟩ : syracuseStep 1971641 = 1478731) B1478731
theorem B1750535 : Blo 1166400 1750535 := bstep (se 1 (by rfl) ⟨1312901, by rfl⟩ : syracuseStep 1750535 = 2625803) B2625803
theorem B1750571 : Blo 1166400 1750571 := bstep (se 1 (by rfl) ⟨1312928, by rfl⟩ : syracuseStep 1750571 = 2625857) B2625857
theorem B1750601 : Blo 1166400 1750601 := bstep (se 2 (by rfl) ⟨656475, by rfl⟩ : syracuseStep 1750601 = 1312951) B1312951
theorem B2954839 : Blo 1166400 2954839 := bstep (se 1 (by rfl) ⟨2216129, by rfl⟩ : syracuseStep 2954839 = 4432259) B4432259
theorem B10114679 : Blo 1166400 10114679 := bstep (se 1 (by rfl) ⟨7586009, by rfl⟩ : syracuseStep 10114679 = 15172019) B15172019
theorem B2627207 : Blo 1166400 2627207 := bstep (se 1 (by rfl) ⟨1970405, by rfl⟩ : syracuseStep 2627207 = 3940811) B3940811
theorem B1750715 : Blo 1166400 1750715 := bstep (se 1 (by rfl) ⟨1313036, by rfl⟩ : syracuseStep 1750715 = 2626073) B2626073
theorem B6649573 : Blo 1166400 6649573 := bstep (se 4 (by rfl) ⟨623397, by rfl⟩ : syracuseStep 6649573 = 1246795) B1246795
theorem B1750775 : Blo 1166400 1750775 := bstep (se 1 (by rfl) ⟨1313081, by rfl⟩ : syracuseStep 1750775 = 2626163) B2626163
theorem B1750799 : Blo 1166400 1750799 := bstep (se 1 (by rfl) ⟨1313099, by rfl⟩ : syracuseStep 1750799 = 2626199) B2626199
theorem B1750841 : Blo 1166400 1750841 := bstep (se 2 (by rfl) ⟨656565, by rfl⟩ : syracuseStep 1750841 = 1313131) B1313131
theorem B1775417 : Blo 1166400 1775417 := bstep (se 2 (by rfl) ⟨665781, by rfl⟩ : syracuseStep 1775417 = 1331563) B1331563
theorem B2627387 : Blo 1166400 2627387 := bstep (se 1 (by rfl) ⟨1970540, by rfl⟩ : syracuseStep 2627387 = 3941081) B3941081
theorem B6313787 : Blo 1166400 6313787 := bstep (se 1 (by rfl) ⟨4735340, by rfl⟩ : syracuseStep 6313787 = 9470681) B9470681
theorem B33650549 : Blo 1166400 33650549 := bstep (se 5 (by rfl) ⟨1577369, by rfl⟩ : syracuseStep 33650549 = 3154739) B3154739
theorem B1750919 : Blo 1166400 1750919 := bstep (se 1 (by rfl) ⟨1313189, by rfl⟩ : syracuseStep 1750919 = 2626379) B2626379
theorem B2955143 : Blo 1166400 2955143 := bstep (se 1 (by rfl) ⟨2216357, by rfl⟩ : syracuseStep 2955143 = 4432715) B4432715
theorem B1750955 : Blo 1166400 1750955 := bstep (se 1 (by rfl) ⟨1313216, by rfl⟩ : syracuseStep 1750955 = 2626433) B2626433
theorem B2627513 : Blo 1166400 2627513 := bstep (se 2 (by rfl) ⟨985317, by rfl⟩ : syracuseStep 2627513 = 1970635) B1970635
theorem B1750985 : Blo 1166400 1750985 := bstep (se 2 (by rfl) ⟨656619, by rfl⟩ : syracuseStep 1750985 = 1313239) B1313239
theorem B22763467 : Blo 1166400 22763467 := bstep (se 1 (by rfl) ⟨17072600, by rfl⟩ : syracuseStep 22763467 = 34145201) B34145201
theorem B5994499 : Blo 1166400 5994499 := bstep (se 1 (by rfl) ⟨4495874, by rfl⟩ : syracuseStep 5994499 = 8991749) B8991749
theorem B2955275 : Blo 1166400 2955275 := bstep (se 1 (by rfl) ⟨2216456, by rfl⟩ : syracuseStep 2955275 = 4432913) B4432913
theorem B3741707 : Blo 1166400 3741707 := bstep (se 1 (by rfl) ⟨2806280, by rfl⟩ : syracuseStep 3741707 = 5612561) B5612561
theorem B1751099 : Blo 1166400 1751099 := bstep (se 1 (by rfl) ⟨1313324, by rfl⟩ : syracuseStep 1751099 = 2626649) B2626649
theorem B2218043 : Blo 1166400 2218043 := bstep (se 1 (by rfl) ⟨1663532, by rfl⟩ : syracuseStep 2218043 = 3327065) B3327065
theorem B1751159 : Blo 1166400 1751159 := bstep (se 1 (by rfl) ⟨1313369, by rfl⟩ : syracuseStep 1751159 = 2626739) B2626739
theorem B1751183 : Blo 1166400 1751183 := bstep (se 1 (by rfl) ⟨1313387, by rfl⟩ : syracuseStep 1751183 = 2626775) B2626775
theorem B1751225 : Blo 1166400 1751225 := bstep (se 2 (by rfl) ⟨656709, by rfl⟩ : syracuseStep 1751225 = 1313419) B1313419
theorem B1751303 : Blo 1166400 1751303 := bstep (se 1 (by rfl) ⟨1313477, by rfl⟩ : syracuseStep 1751303 = 2626955) B2626955
theorem B2627855 : Blo 1166400 2627855 := bstep (se 1 (by rfl) ⟨1970891, by rfl⟩ : syracuseStep 2627855 = 3941783) B3941783
theorem B2627873 : Blo 1166400 2627873 := bstep (se 2 (by rfl) ⟨985452, by rfl⟩ : syracuseStep 2627873 = 1970905) B1970905
theorem B1751339 : Blo 1166400 1751339 := bstep (se 1 (by rfl) ⟨1313504, by rfl⟩ : syracuseStep 1751339 = 2627009) B2627009
theorem B1497403 : Blo 1166400 1497403 := bstep (se 1 (by rfl) ⟨1123052, by rfl⟩ : syracuseStep 1497403 = 2246105) B2246105
theorem B1751369 : Blo 1166400 1751369 := bstep (se 2 (by rfl) ⟨656763, by rfl⟩ : syracuseStep 1751369 = 1313527) B1313527
theorem B1751483 : Blo 1166400 1751483 := bstep (se 1 (by rfl) ⟨1313612, by rfl⟩ : syracuseStep 1751483 = 2627225) B2627225
theorem B5986781 : Blo 1166400 5986781 := bstep (se 3 (by rfl) ⟨1122521, by rfl⟩ : syracuseStep 5986781 = 2245043) B2245043
theorem B1751543 : Blo 1166400 1751543 := bstep (se 1 (by rfl) ⟨1313657, by rfl⟩ : syracuseStep 1751543 = 2627315) B2627315
theorem B2103823 : Blo 1166400 2103823 := bstep (se 1 (by rfl) ⟨1577867, by rfl⟩ : syracuseStep 2103823 = 3155735) B3155735
theorem B1751567 : Blo 1166400 1751567 := bstep (se 1 (by rfl) ⟨1313675, by rfl⟩ : syracuseStep 1751567 = 2627351) B2627351
theorem B2955791 : Blo 1166400 2955791 := bstep (se 1 (by rfl) ⟨2216843, by rfl⟩ : syracuseStep 2955791 = 4433687) B4433687
theorem B10648093 : Blo 1166400 10648093 := bstep (se 3 (by rfl) ⟨1996517, by rfl⟩ : syracuseStep 10648093 = 3993035) B3993035
theorem B1751609 : Blo 1166400 1751609 := bstep (se 2 (by rfl) ⟨656853, by rfl⟩ : syracuseStep 1751609 = 1313707) B1313707
theorem B11377219 : Blo 1166400 11377219 := bstep (se 1 (by rfl) ⟨8532914, by rfl⟩ : syracuseStep 11377219 = 17065829) B17065829
theorem B3324503 : Blo 1166400 3324503 := bstep (se 1 (by rfl) ⟨2493377, by rfl⟩ : syracuseStep 3324503 = 4986755) B4986755
theorem B2628215 : Blo 1166400 2628215 := bstep (se 1 (by rfl) ⟨1971161, by rfl⟩ : syracuseStep 2628215 = 3942323) B3942323
theorem B1751687 : Blo 1166400 1751687 := bstep (se 1 (by rfl) ⟨1313765, by rfl⟩ : syracuseStep 1751687 = 2627531) B2627531
theorem B2955923 : Blo 1166400 2955923 := bstep (se 1 (by rfl) ⟨2216942, by rfl⟩ : syracuseStep 2955923 = 4433885) B4433885
theorem B1751723 : Blo 1166400 1751723 := bstep (se 1 (by rfl) ⟨1313792, by rfl⟩ : syracuseStep 1751723 = 2627585) B2627585
theorem B6314669 : Blo 1166400 6314669 := bstep (se 3 (by rfl) ⟨1184000, by rfl⟩ : syracuseStep 6314669 = 2368001) B2368001
theorem B1751753 : Blo 1166400 1751753 := bstep (se 2 (by rfl) ⟨656907, by rfl⟩ : syracuseStep 1751753 = 1313815) B1313815
theorem B5323553 : Blo 1166400 5323553 := bstep (se 2 (by rfl) ⟨1996332, by rfl⟩ : syracuseStep 5323553 = 3992665) B3992665
theorem B2628395 : Blo 1166400 2628395 := bstep (se 1 (by rfl) ⟨1971296, by rfl⟩ : syracuseStep 2628395 = 3942593) B3942593
theorem B1751867 : Blo 1166400 1751867 := bstep (se 1 (by rfl) ⟨1313900, by rfl⟩ : syracuseStep 1751867 = 2627801) B2627801
theorem B4987763 : Blo 1166400 4987763 := bstep (se 1 (by rfl) ⟨3740822, by rfl⟩ : syracuseStep 4987763 = 7481645) B7481645
theorem B1751927 : Blo 1166400 1751927 := bstep (se 1 (by rfl) ⟨1313945, by rfl⟩ : syracuseStep 1751927 = 2627891) B2627891
theorem B1751951 : Blo 1166400 1751951 := bstep (se 1 (by rfl) ⟨1313963, by rfl⟩ : syracuseStep 1751951 = 2627927) B2627927
theorem B1751993 : Blo 1166400 1751993 := bstep (se 2 (by rfl) ⟨656997, by rfl⟩ : syracuseStep 1751993 = 1313995) B1313995
theorem B4430801 : Blo 1166400 4430801 := bstep (se 2 (by rfl) ⟨1661550, by rfl⟩ : syracuseStep 4430801 = 3323101) B3323101
theorem B17538053 : Blo 1166400 17538053 := bstep (se 4 (by rfl) ⟨1644192, by rfl⟩ : syracuseStep 17538053 = 3288385) B3288385
theorem B1752071 : Blo 1166400 1752071 := bstep (se 1 (by rfl) ⟨1314053, by rfl⟩ : syracuseStep 1752071 = 2628107) B2628107
theorem B1661995 : Blo 1166400 1661995 := bstep (se 1 (by rfl) ⟨1246496, by rfl⟩ : syracuseStep 1661995 = 2492993) B2492993
theorem B1752107 : Blo 1166400 1752107 := bstep (se 1 (by rfl) ⟨1314080, by rfl⟩ : syracuseStep 1752107 = 2628161) B2628161
theorem B1752137 : Blo 1166400 1752137 := bstep (se 2 (by rfl) ⟨657051, by rfl⟩ : syracuseStep 1752137 = 1314103) B1314103
theorem B10648709 : Blo 1166400 10648709 := bstep (se 4 (by rfl) ⟨998316, by rfl⟩ : syracuseStep 10648709 = 1996633) B1996633
theorem B2628755 : Blo 1166400 2628755 := bstep (se 1 (by rfl) ⟨1971566, by rfl⟩ : syracuseStep 2628755 = 3943133) B3943133
theorem B1752251 : Blo 1166400 1752251 := bstep (se 1 (by rfl) ⟨1314188, by rfl⟩ : syracuseStep 1752251 = 2628377) B2628377
theorem B2628809 : Blo 1166400 2628809 := bstep (se 2 (by rfl) ⟨985803, by rfl⟩ : syracuseStep 2628809 = 1971607) B1971607
theorem B1752311 : Blo 1166400 1752311 := bstep (se 1 (by rfl) ⟨1314233, by rfl⟩ : syracuseStep 1752311 = 2628467) B2628467
theorem B1662223 : Blo 1166400 1662223 := bstep (se 1 (by rfl) ⟨1246667, by rfl⟩ : syracuseStep 1662223 = 2493335) B2493335
theorem B1752335 : Blo 1166400 1752335 := bstep (se 1 (by rfl) ⟨1314251, by rfl⟩ : syracuseStep 1752335 = 2628503) B2628503
theorem B1752377 : Blo 1166400 1752377 := bstep (se 2 (by rfl) ⟨657141, by rfl⟩ : syracuseStep 1752377 = 1314283) B1314283
theorem B5913971 : Blo 1166400 5913971 := bstep (se 1 (by rfl) ⟨4435478, by rfl⟩ : syracuseStep 5913971 = 8870957) B8870957
theorem B1752455 : Blo 1166400 1752455 := bstep (se 1 (by rfl) ⟨1314341, by rfl⟩ : syracuseStep 1752455 = 2628683) B2628683
theorem B3939731 : Blo 1166400 3939731 := bstep (se 1 (by rfl) ⟨2954798, by rfl⟩ : syracuseStep 3939731 = 5909597) B5909597
theorem B4431257 : Blo 1166400 4431257 := bstep (se 2 (by rfl) ⟨1661721, by rfl⟩ : syracuseStep 4431257 = 3323443) B3323443
theorem B1752491 : Blo 1166400 1752491 := bstep (se 1 (by rfl) ⟨1314368, by rfl⟩ : syracuseStep 1752491 = 2628737) B2628737
theorem B1752521 : Blo 1166400 1752521 := bstep (se 2 (by rfl) ⟨657195, by rfl⟩ : syracuseStep 1752521 = 1314391) B1314391
theorem B9469669 : Blo 1166400 9469669 := bstep (se 4 (by rfl) ⟨887781, by rfl⟩ : syracuseStep 9469669 = 1775563) B1775563
theorem B2957057 : Blo 1166400 2957057 := bstep (se 2 (by rfl) ⟨1108896, by rfl⟩ : syracuseStep 2957057 = 2217793) B2217793
theorem B5914457 : Blo 1166400 5914457 := bstep (se 2 (by rfl) ⟨2217921, by rfl⟩ : syracuseStep 5914457 = 4435843) B4435843
theorem B46768141 : Blo 1166400 46768141 := bstep (se 3 (by rfl) ⟨8769026, by rfl⟩ : syracuseStep 46768141 = 17538053) B17538053
theorem B5914781 : Blo 1166400 5914781 := bstep (se 3 (by rfl) ⟨1109021, by rfl⟩ : syracuseStep 5914781 = 2218043) B2218043
theorem B4735223 : Blo 1166400 4735223 := bstep (se 1 (by rfl) ⟨3551417, by rfl⟩ : syracuseStep 4735223 = 7102835) B7102835
theorem B8864153 : Blo 1166400 8864153 := bstep (se 2 (by rfl) ⟨3324057, by rfl⟩ : syracuseStep 8864153 = 6648115) B6648115
theorem B9732631 : Blo 1166400 9732631 := bstep (se 1 (by rfl) ⟨7299473, by rfl⟩ : syracuseStep 9732631 = 14598947) B14598947
theorem B23962229 : Blo 1166400 23962229 := bstep (se 5 (by rfl) ⟨1123229, by rfl⟩ : syracuseStep 23962229 = 2246459) B2246459
theorem B14197457 : Blo 1166400 14197457 := bstep (se 2 (by rfl) ⟨5324046, by rfl⟩ : syracuseStep 14197457 = 10648093) B10648093
theorem B1868617 : Blo 1166400 1868617 := bstep (se 2 (by rfl) ⟨700731, by rfl⟩ : syracuseStep 1868617 = 1401463) B1401463
theorem B15967151 : Blo 1166400 15967151 := bstep (se 1 (by rfl) ⟨11975363, by rfl⟩ : syracuseStep 15967151 = 23950727) B23950727
theorem B7095347 : Blo 1166400 7095347 := bstep (se 1 (by rfl) ⟨5321510, by rfl⟩ : syracuseStep 7095347 = 10643021) B10643021
theorem B3991187 : Blo 1166400 3991187 := bstep (se 1 (by rfl) ⟨2993390, by rfl⟩ : syracuseStep 3991187 = 5986781) B5986781
theorem B3737299 : Blo 1166400 3737299 := bstep (se 1 (by rfl) ⟨2802974, by rfl⟩ : syracuseStep 3737299 = 5605949) B5605949
theorem B3549035 : Blo 1166400 3549035 := bstep (se 1 (by rfl) ⟨2661776, by rfl⟩ : syracuseStep 3549035 = 5323553) B5323553
theorem B1312807 : Blo 1166400 1312807 := bstep (se 1 (by rfl) ⟨984605, by rfl⟩ : syracuseStep 1312807 = 1969211) B1969211
theorem B14968921 : Blo 1166400 14968921 := bstep (se 2 (by rfl) ⟨5613345, by rfl⟩ : syracuseStep 14968921 = 11226691) B11226691
theorem B1476731 : Blo 1166400 1476731 := bstep (se 1 (by rfl) ⟨1107548, by rfl⟩ : syracuseStep 1476731 = 2215097) B2215097
theorem B3942647 : Blo 1166400 3942647 := bstep (se 1 (by rfl) ⟨2956985, by rfl⟩ : syracuseStep 3942647 = 5913971) B5913971
theorem B8866097 : Blo 1166400 8866097 := bstep (se 2 (by rfl) ⟨3324786, by rfl⟩ : syracuseStep 8866097 = 6649573) B6649573
theorem B12626225 : Blo 1166400 12626225 := bstep (se 2 (by rfl) ⟨4734834, by rfl⟩ : syracuseStep 12626225 = 9469669) B9469669
theorem B4491625 : Blo 1166400 4491625 := bstep (se 2 (by rfl) ⟨1684359, by rfl⟩ : syracuseStep 4491625 = 3368719) B3368719
theorem B3942971 : Blo 1166400 3942971 := bstep (se 1 (by rfl) ⟨2957228, by rfl⟩ : syracuseStep 3942971 = 5914457) B5914457
theorem B7473799 : Blo 1166400 7473799 := bstep (se 1 (by rfl) ⟨5605349, by rfl⟩ : syracuseStep 7473799 = 11210699) B11210699
theorem B11225735 : Blo 1166400 11225735 := bstep (se 1 (by rfl) ⟨8419301, by rfl⟩ : syracuseStep 11225735 = 16838603) B16838603
theorem B8858321 : Blo 1166400 8858321 := bstep (se 2 (by rfl) ⟨3321870, by rfl⟩ : syracuseStep 8858321 = 6643741) B6643741
theorem B2214611 : Blo 1166400 2214611 := bstep (se 1 (by rfl) ⟨1660958, by rfl⟩ : syracuseStep 2214611 = 3321917) B3321917
theorem B3992279 : Blo 1166400 3992279 := bstep (se 1 (by rfl) ⟨2994209, by rfl⟩ : syracuseStep 3992279 = 5988419) B5988419
theorem B1968887 : Blo 1166400 1968887 := bstep (se 1 (by rfl) ⟨1476665, by rfl⟩ : syracuseStep 1968887 = 2953331) B2953331
theorem B3943241 : Blo 1166400 3943241 := bstep (se 2 (by rfl) ⟨1478715, by rfl⟩ : syracuseStep 3943241 = 2957431) B2957431
theorem B2624417 : Blo 1166400 2624417 := bstep (se 2 (by rfl) ⟨984156, by rfl⟩ : syracuseStep 2624417 = 1968313) B1968313
theorem B9718703 : Blo 1166400 9718703 := bstep (se 1 (by rfl) ⟨7289027, by rfl⟩ : syracuseStep 9718703 = 14578055) B14578055
theorem B2214839 : Blo 1166400 2214839 := bstep (se 1 (by rfl) ⟨1661129, by rfl⟩ : syracuseStep 2214839 = 3322259) B3322259
theorem B4434871 : Blo 1166400 4434871 := bstep (se 1 (by rfl) ⟨3326153, by rfl⟩ : syracuseStep 4434871 = 6652307) B6652307
theorem B21605303 : Blo 1166400 21605303 := bstep (se 1 (by rfl) ⟨16203977, by rfl⟩ : syracuseStep 21605303 = 32407955) B32407955
theorem B3738631 : Blo 1166400 3738631 := bstep (se 1 (by rfl) ⟨2803973, by rfl⟩ : syracuseStep 3738631 = 5607947) B5607947
theorem B90917963 : Blo 1166400 90917963 := bstep (se 1 (by rfl) ⟨68188472, by rfl⟩ : syracuseStep 90917963 = 136376945) B136376945
theorem B1166415 : Blo 1166400 1166415 := bstep (se 1 (by rfl) ⟨874811, by rfl⟩ : syracuseStep 1166415 = 1749623) B1749623
theorem B1969231 : Blo 1166400 1969231 := bstep (se 1 (by rfl) ⟨1476923, by rfl⟩ : syracuseStep 1969231 = 2953847) B2953847
theorem B1166431 : Blo 1166400 1166431 := bstep (se 1 (by rfl) ⟨874823, by rfl⟩ : syracuseStep 1166431 = 1749647) B1749647
theorem B1166459 : Blo 1166400 1166459 := bstep (se 1 (by rfl) ⟨874844, by rfl⟩ : syracuseStep 1166459 = 1749689) B1749689
theorem B1166511 : Blo 1166400 1166511 := bstep (se 1 (by rfl) ⟨874883, by rfl⟩ : syracuseStep 1166511 = 1749767) B1749767
theorem B1166535 : Blo 1166400 1166535 := bstep (se 1 (by rfl) ⟨874901, by rfl⟩ : syracuseStep 1166535 = 1749803) B1749803
theorem B1166555 : Blo 1166400 1166555 := bstep (se 1 (by rfl) ⟨874916, by rfl⟩ : syracuseStep 1166555 = 1749833) B1749833
theorem B2624759 : Blo 1166400 2624759 := bstep (se 1 (by rfl) ⟨1968569, by rfl⟩ : syracuseStep 2624759 = 3937139) B3937139
theorem B1166631 : Blo 1166400 1166631 := bstep (se 1 (by rfl) ⟨874973, by rfl⟩ : syracuseStep 1166631 = 1749947) B1749947
theorem B1969481 : Blo 1166400 1969481 := bstep (se 2 (by rfl) ⟨738555, by rfl⟩ : syracuseStep 1969481 = 1477111) B1477111
theorem B1166671 : Blo 1166400 1166671 := bstep (se 1 (by rfl) ⟨875003, by rfl⟩ : syracuseStep 1166671 = 1750007) B1750007
theorem B1166687 : Blo 1166400 1166687 := bstep (se 1 (by rfl) ⟨875015, by rfl⟩ : syracuseStep 1166687 = 1750031) B1750031
theorem B1166715 : Blo 1166400 1166715 := bstep (se 1 (by rfl) ⟨875036, by rfl⟩ : syracuseStep 1166715 = 1750073) B1750073
theorem B6647183 : Blo 1166400 6647183 := bstep (se 1 (by rfl) ⟨4985387, by rfl⟩ : syracuseStep 6647183 = 9970775) B9970775
theorem B18935183 : Blo 1166400 18935183 := bstep (se 1 (by rfl) ⟨14201387, by rfl⟩ : syracuseStep 18935183 = 28402775) B28402775
theorem B4435343 : Blo 1166400 4435343 := bstep (se 1 (by rfl) ⟨3326507, by rfl⟩ : syracuseStep 4435343 = 6653015) B6653015
theorem B1166767 : Blo 1166400 1166767 := bstep (se 1 (by rfl) ⟨875075, by rfl⟩ : syracuseStep 1166767 = 1750151) B1750151
theorem B1166791 : Blo 1166400 1166791 := bstep (se 1 (by rfl) ⟨875093, by rfl⟩ : syracuseStep 1166791 = 1750187) B1750187
theorem B1166811 : Blo 1166400 1166811 := bstep (se 1 (by rfl) ⟨875108, by rfl⟩ : syracuseStep 1166811 = 1750217) B1750217
theorem B1330651 : Blo 1166400 1330651 := bstep (se 1 (by rfl) ⟨997988, by rfl⟩ : syracuseStep 1330651 = 1995977) B1995977
theorem B2952713 : Blo 1166400 2952713 := bstep (se 2 (by rfl) ⟨1107267, by rfl⟩ : syracuseStep 2952713 = 2214535) B2214535
theorem B4206089 : Blo 1166400 4206089 := bstep (se 2 (by rfl) ⟨1577283, by rfl⟩ : syracuseStep 4206089 = 3154567) B3154567
theorem B1166887 : Blo 1166400 1166887 := bstep (se 1 (by rfl) ⟨875165, by rfl⟩ : syracuseStep 1166887 = 1750331) B1750331
theorem B1166927 : Blo 1166400 1166927 := bstep (se 1 (by rfl) ⟨875195, by rfl⟩ : syracuseStep 1166927 = 1750391) B1750391
theorem B1166943 : Blo 1166400 1166943 := bstep (se 1 (by rfl) ⟨875207, by rfl⟩ : syracuseStep 1166943 = 1750415) B1750415
theorem B1166971 : Blo 1166400 1166971 := bstep (se 1 (by rfl) ⟨875228, by rfl⟩ : syracuseStep 1166971 = 1750457) B1750457
theorem B1314427 : Blo 1166400 1314427 := bstep (se 1 (by rfl) ⟨985820, by rfl⟩ : syracuseStep 1314427 = 1971641) B1971641
theorem B1167023 : Blo 1166400 1167023 := bstep (se 1 (by rfl) ⟨875267, by rfl⟩ : syracuseStep 1167023 = 1750535) B1750535
theorem B1167047 : Blo 1166400 1167047 := bstep (se 1 (by rfl) ⟨875285, by rfl⟩ : syracuseStep 1167047 = 1750571) B1750571
theorem B1167067 : Blo 1166400 1167067 := bstep (se 1 (by rfl) ⟨875300, by rfl⟩ : syracuseStep 1167067 = 1750601) B1750601
theorem B1969913 : Blo 1166400 1969913 := bstep (se 2 (by rfl) ⟨738717, by rfl⟩ : syracuseStep 1969913 = 1477435) B1477435
theorem B1167143 : Blo 1166400 1167143 := bstep (se 1 (by rfl) ⟨875357, by rfl⟩ : syracuseStep 1167143 = 1750715) B1750715
theorem B2625353 : Blo 1166400 2625353 := bstep (se 2 (by rfl) ⟨984507, by rfl⟩ : syracuseStep 2625353 = 1969015) B1969015
theorem B1167183 : Blo 1166400 1167183 := bstep (se 1 (by rfl) ⟨875387, by rfl⟩ : syracuseStep 1167183 = 1750775) B1750775
theorem B1167199 : Blo 1166400 1167199 := bstep (se 1 (by rfl) ⟨875399, by rfl⟩ : syracuseStep 1167199 = 1750799) B1750799
theorem B1167227 : Blo 1166400 1167227 := bstep (se 1 (by rfl) ⟨875420, by rfl⟩ : syracuseStep 1167227 = 1750841) B1750841
theorem B22433699 : Blo 1166400 22433699 := bstep (se 1 (by rfl) ⟨16825274, by rfl⟩ : syracuseStep 22433699 = 33650549) B33650549
theorem B1167279 : Blo 1166400 1167279 := bstep (se 1 (by rfl) ⟨875459, by rfl⟩ : syracuseStep 1167279 = 1750919) B1750919
theorem B1970095 : Blo 1166400 1970095 := bstep (se 1 (by rfl) ⟨1477571, by rfl⟩ : syracuseStep 1970095 = 2955143) B2955143
theorem B1167303 : Blo 1166400 1167303 := bstep (se 1 (by rfl) ⟨875477, by rfl⟩ : syracuseStep 1167303 = 1750955) B1750955
theorem B1167323 : Blo 1166400 1167323 := bstep (se 1 (by rfl) ⟨875492, by rfl⟩ : syracuseStep 1167323 = 1750985) B1750985
theorem B1970183 : Blo 1166400 1970183 := bstep (se 1 (by rfl) ⟨1477637, by rfl⟩ : syracuseStep 1970183 = 2955275) B2955275
theorem B2494471 : Blo 1166400 2494471 := bstep (se 1 (by rfl) ⟨1870853, by rfl⟩ : syracuseStep 2494471 = 3741707) B3741707
theorem B1167399 : Blo 1166400 1167399 := bstep (se 1 (by rfl) ⟨875549, by rfl⟩ : syracuseStep 1167399 = 1751099) B1751099
theorem B2215993 : Blo 1166400 2215993 := bstep (se 2 (by rfl) ⟨830997, by rfl⟩ : syracuseStep 2215993 = 1661995) B1661995
theorem B1167439 : Blo 1166400 1167439 := bstep (se 1 (by rfl) ⟨875579, by rfl⟩ : syracuseStep 1167439 = 1751159) B1751159
theorem B1167455 : Blo 1166400 1167455 := bstep (se 1 (by rfl) ⟨875591, by rfl⟩ : syracuseStep 1167455 = 1751183) B1751183
theorem B1167483 : Blo 1166400 1167483 := bstep (se 1 (by rfl) ⟨875612, by rfl⟩ : syracuseStep 1167483 = 1751225) B1751225
theorem B13299875 : Blo 1166400 13299875 := bstep (se 1 (by rfl) ⟨9974906, by rfl⟩ : syracuseStep 13299875 = 19949813) B19949813
theorem B1167535 : Blo 1166400 1167535 := bstep (se 1 (by rfl) ⟨875651, by rfl⟩ : syracuseStep 1167535 = 1751303) B1751303
theorem B1167559 : Blo 1166400 1167559 := bstep (se 1 (by rfl) ⟨875669, by rfl⟩ : syracuseStep 1167559 = 1751339) B1751339
theorem B1167579 : Blo 1166400 1167579 := bstep (se 1 (by rfl) ⟨875684, by rfl⟩ : syracuseStep 1167579 = 1751369) B1751369
theorem B1167655 : Blo 1166400 1167655 := bstep (se 1 (by rfl) ⟨875741, by rfl⟩ : syracuseStep 1167655 = 1751483) B1751483
theorem B26972477 : Blo 1166400 26972477 := bstep (se 3 (by rfl) ⟨5057339, by rfl⟩ : syracuseStep 26972477 = 10114679) B10114679
theorem B1167695 : Blo 1166400 1167695 := bstep (se 1 (by rfl) ⟨875771, by rfl⟩ : syracuseStep 1167695 = 1751543) B1751543
theorem B1167711 : Blo 1166400 1167711 := bstep (se 1 (by rfl) ⟨875783, by rfl⟩ : syracuseStep 1167711 = 1751567) B1751567
theorem B1970527 : Blo 1166400 1970527 := bstep (se 1 (by rfl) ⟨1477895, by rfl⟩ : syracuseStep 1970527 = 2955791) B2955791
theorem B2216297 : Blo 1166400 2216297 := bstep (se 2 (by rfl) ⟨831111, by rfl⟩ : syracuseStep 2216297 = 1662223) B1662223
theorem B1167739 : Blo 1166400 1167739 := bstep (se 1 (by rfl) ⟨875804, by rfl⟩ : syracuseStep 1167739 = 1751609) B1751609
theorem B2216335 : Blo 1166400 2216335 := bstep (se 1 (by rfl) ⟨1662251, by rfl⟩ : syracuseStep 2216335 = 3324503) B3324503
theorem B1167791 : Blo 1166400 1167791 := bstep (se 1 (by rfl) ⟨875843, by rfl⟩ : syracuseStep 1167791 = 1751687) B1751687
theorem B1970615 : Blo 1166400 1970615 := bstep (se 1 (by rfl) ⟨1477961, by rfl⟩ : syracuseStep 1970615 = 2955923) B2955923
theorem B1167815 : Blo 1166400 1167815 := bstep (se 1 (by rfl) ⟨875861, by rfl⟩ : syracuseStep 1167815 = 1751723) B1751723
theorem B1167835 : Blo 1166400 1167835 := bstep (se 1 (by rfl) ⟨875876, by rfl⟩ : syracuseStep 1167835 = 1751753) B1751753
theorem B1167911 : Blo 1166400 1167911 := bstep (se 1 (by rfl) ⟨875933, by rfl⟩ : syracuseStep 1167911 = 1751867) B1751867
theorem B1167951 : Blo 1166400 1167951 := bstep (se 1 (by rfl) ⟨875963, by rfl⟩ : syracuseStep 1167951 = 1751927) B1751927
theorem B1167967 : Blo 1166400 1167967 := bstep (se 1 (by rfl) ⟨875975, by rfl⟩ : syracuseStep 1167967 = 1751951) B1751951
theorem B2626145 : Blo 1166400 2626145 := bstep (se 2 (by rfl) ⟨984804, by rfl⟩ : syracuseStep 2626145 = 1969609) B1969609
theorem B1167995 : Blo 1166400 1167995 := bstep (se 1 (by rfl) ⟨875996, by rfl⟩ : syracuseStep 1167995 = 1751993) B1751993
theorem B2953867 : Blo 1166400 2953867 := bstep (se 1 (by rfl) ⟨2215400, by rfl⟩ : syracuseStep 2953867 = 4430801) B4430801
theorem B1168047 : Blo 1166400 1168047 := bstep (se 1 (by rfl) ⟨876035, by rfl⟩ : syracuseStep 1168047 = 1752071) B1752071
theorem B1168071 : Blo 1166400 1168071 := bstep (se 1 (by rfl) ⟨876053, by rfl⟩ : syracuseStep 1168071 = 1752107) B1752107
theorem B1168091 : Blo 1166400 1168091 := bstep (se 1 (by rfl) ⟨876068, by rfl⟩ : syracuseStep 1168091 = 1752137) B1752137
theorem B7099139 : Blo 1166400 7099139 := bstep (se 1 (by rfl) ⟨5324354, by rfl⟩ : syracuseStep 7099139 = 10648709) B10648709
theorem B1168167 : Blo 1166400 1168167 := bstep (se 1 (by rfl) ⟨876125, by rfl⟩ : syracuseStep 1168167 = 1752251) B1752251
theorem B3740489 : Blo 1166400 3740489 := bstep (se 2 (by rfl) ⟨1402683, by rfl⟩ : syracuseStep 3740489 = 2805367) B2805367
theorem B1168207 : Blo 1166400 1168207 := bstep (se 1 (by rfl) ⟨876155, by rfl⟩ : syracuseStep 1168207 = 1752311) B1752311
theorem B1168223 : Blo 1166400 1168223 := bstep (se 1 (by rfl) ⟨876167, by rfl⟩ : syracuseStep 1168223 = 1752335) B1752335
theorem B34091891 : Blo 1166400 34091891 := bstep (se 1 (by rfl) ⟨25568918, by rfl⟩ : syracuseStep 34091891 = 51137837) B51137837
theorem B1168251 : Blo 1166400 1168251 := bstep (se 1 (by rfl) ⟨876188, by rfl⟩ : syracuseStep 1168251 = 1752377) B1752377
theorem B1749935 : Blo 1166400 1749935 := bstep (se 1 (by rfl) ⟨1312451, by rfl⟩ : syracuseStep 1749935 = 2624903) B2624903
theorem B1168303 : Blo 1166400 1168303 := bstep (se 1 (by rfl) ⟨876227, by rfl⟩ : syracuseStep 1168303 = 1752455) B1752455
theorem B2626487 : Blo 1166400 2626487 := bstep (se 1 (by rfl) ⟨1969865, by rfl⟩ : syracuseStep 2626487 = 3939731) B3939731
theorem B2954171 : Blo 1166400 2954171 := bstep (se 1 (by rfl) ⟨2215628, by rfl⟩ : syracuseStep 2954171 = 4431257) B4431257
theorem B1168327 : Blo 1166400 1168327 := bstep (se 1 (by rfl) ⟨876245, by rfl⟩ : syracuseStep 1168327 = 1752491) B1752491
theorem B1168347 : Blo 1166400 1168347 := bstep (se 1 (by rfl) ⟨876260, by rfl⟩ : syracuseStep 1168347 = 1752521) B1752521
theorem B1750025 : Blo 1166400 1750025 := bstep (se 2 (by rfl) ⟨656259, by rfl⟩ : syracuseStep 1750025 = 1312519) B1312519
theorem B1971209 : Blo 1166400 1971209 := bstep (se 2 (by rfl) ⟨739203, by rfl⟩ : syracuseStep 1971209 = 1478407) B1478407
theorem B1750055 : Blo 1166400 1750055 := bstep (se 1 (by rfl) ⟨1312541, by rfl⟩ : syracuseStep 1750055 = 2625083) B2625083
theorem B4428857 : Blo 1166400 4428857 := bstep (se 2 (by rfl) ⟨1660821, by rfl⟩ : syracuseStep 4428857 = 3321643) B3321643
theorem B8860751 : Blo 1166400 8860751 := bstep (se 1 (by rfl) ⟨6645563, by rfl⟩ : syracuseStep 8860751 = 13291127) B13291127
theorem B1750139 : Blo 1166400 1750139 := bstep (se 1 (by rfl) ⟨1312604, by rfl⟩ : syracuseStep 1750139 = 2625209) B2625209
theorem B11211929 : Blo 1166400 11211929 := bstep (se 2 (by rfl) ⟨4204473, by rfl⟩ : syracuseStep 11211929 = 8408947) B8408947
theorem B1971371 : Blo 1166400 1971371 := bstep (se 1 (by rfl) ⟨1478528, by rfl⟩ : syracuseStep 1971371 = 2957057) B2957057
theorem B1750265 : Blo 1166400 1750265 := bstep (se 2 (by rfl) ⟨656349, by rfl⟩ : syracuseStep 1750265 = 1312699) B1312699
theorem B7476569 : Blo 1166400 7476569 := bstep (se 2 (by rfl) ⟨2803713, by rfl⟩ : syracuseStep 7476569 = 5607427) B5607427
theorem B7992665 : Blo 1166400 7992665 := bstep (se 2 (by rfl) ⟨2997249, by rfl⟩ : syracuseStep 7992665 = 5994499) B5994499
theorem B1750367 : Blo 1166400 1750367 := bstep (se 1 (by rfl) ⟨1312775, by rfl⟩ : syracuseStep 1750367 = 2625551) B2625551
theorem B1750379 : Blo 1166400 1750379 := bstep (se 1 (by rfl) ⟨1312784, by rfl⟩ : syracuseStep 1750379 = 2625569) B2625569
theorem B17986931 : Blo 1166400 17986931 := bstep (se 1 (by rfl) ⟨13490198, by rfl⟩ : syracuseStep 17986931 = 26980397) B26980397
theorem B3323261 : Blo 1166400 3323261 := bstep (se 3 (by rfl) ⟨623111, by rfl⟩ : syracuseStep 3323261 = 1246223) B1246223
theorem B3937679 : Blo 1166400 3937679 := bstep (se 1 (by rfl) ⟨2953259, by rfl⟩ : syracuseStep 3937679 = 5906519) B5906519
theorem B18216355 : Blo 1166400 18216355 := bstep (se 1 (by rfl) ⟨13662266, by rfl⟩ : syracuseStep 18216355 = 27324533) B27324533
theorem B11220389 : Blo 1166400 11220389 := bstep (se 4 (by rfl) ⟨1051911, by rfl⟩ : syracuseStep 11220389 = 2103823) B2103823
theorem B7583149 : Blo 1166400 7583149 := bstep (se 3 (by rfl) ⟨1421840, by rfl⟩ : syracuseStep 7583149 = 2843681) B2843681
theorem B9967049 : Blo 1166400 9967049 := bstep (se 2 (by rfl) ⟨3737643, by rfl⟩ : syracuseStep 9967049 = 7475287) B7475287
theorem B5912027 : Blo 1166400 5912027 := bstep (se 1 (by rfl) ⟨4434020, by rfl⟩ : syracuseStep 5912027 = 8868041) B8868041
theorem B6313459 : Blo 1166400 6313459 := bstep (se 1 (by rfl) ⟨4735094, by rfl⟩ : syracuseStep 6313459 = 9470189) B9470189
theorem B2627081 : Blo 1166400 2627081 := bstep (se 2 (by rfl) ⟨985155, by rfl⟩ : syracuseStep 2627081 = 1970311) B1970311
theorem B1750607 : Blo 1166400 1750607 := bstep (se 1 (by rfl) ⟨1312955, by rfl⟩ : syracuseStep 1750607 = 2625911) B2625911
theorem B8869499 : Blo 1166400 8869499 := bstep (se 1 (by rfl) ⟨6652124, by rfl⟩ : syracuseStep 8869499 = 13304249) B13304249
theorem B4208267 : Blo 1166400 4208267 := bstep (se 1 (by rfl) ⟨3156200, by rfl⟩ : syracuseStep 4208267 = 6312401) B6312401
theorem B14202515 : Blo 1166400 14202515 := bstep (se 1 (by rfl) ⟨10651886, by rfl⟩ : syracuseStep 14202515 = 21303773) B21303773
theorem B4429511 : Blo 1166400 4429511 := bstep (se 1 (by rfl) ⟨3322133, by rfl⟩ : syracuseStep 4429511 = 6644267) B6644267
theorem B1750727 : Blo 1166400 1750727 := bstep (se 1 (by rfl) ⟨1313045, by rfl⟩ : syracuseStep 1750727 = 2626091) B2626091
theorem B2954951 : Blo 1166400 2954951 := bstep (se 1 (by rfl) ⟨2216213, by rfl⟩ : syracuseStep 2954951 = 4432427) B4432427
theorem B3938003 : Blo 1166400 3938003 := bstep (se 1 (by rfl) ⟨2953502, by rfl⟩ : syracuseStep 3938003 = 5907005) B5907005
theorem B1996537 : Blo 1166400 1996537 := bstep (se 2 (by rfl) ⟨748701, by rfl⟩ : syracuseStep 1996537 = 1497403) B1497403
theorem B2955001 : Blo 1166400 2955001 := bstep (se 2 (by rfl) ⟨1108125, by rfl⟩ : syracuseStep 2955001 = 2216251) B2216251
theorem B2627423 : Blo 1166400 2627423 := bstep (se 1 (by rfl) ⟨1970567, by rfl⟩ : syracuseStep 2627423 = 3941135) B3941135
theorem B1750889 : Blo 1166400 1750889 := bstep (se 2 (by rfl) ⟨656583, by rfl⟩ : syracuseStep 1750889 = 1313167) B1313167
theorem B1750967 : Blo 1166400 1750967 := bstep (se 1 (by rfl) ⟨1313225, by rfl⟩ : syracuseStep 1750967 = 2626451) B2626451
theorem B11220929 : Blo 1166400 11220929 := bstep (se 2 (by rfl) ⟨4207848, by rfl⟩ : syracuseStep 11220929 = 8415697) B8415697
theorem B5912513 : Blo 1166400 5912513 := bstep (se 2 (by rfl) ⟨2217192, by rfl⟩ : syracuseStep 5912513 = 4434385) B4434385
theorem B1751003 : Blo 1166400 1751003 := bstep (se 1 (by rfl) ⟨1313252, by rfl⟩ : syracuseStep 1751003 = 2626505) B2626505
theorem B2627603 : Blo 1166400 2627603 := bstep (se 1 (by rfl) ⟨1970702, by rfl⟩ : syracuseStep 2627603 = 3941405) B3941405
theorem B7477285 : Blo 1166400 7477285 := bstep (se 4 (by rfl) ⟨700995, by rfl⟩ : syracuseStep 7477285 = 1401991) B1401991
theorem B15169625 : Blo 1166400 15169625 := bstep (se 2 (by rfl) ⟨5688609, by rfl⟩ : syracuseStep 15169625 = 11377219) B11377219
theorem B2627945 : Blo 1166400 2627945 := bstep (se 2 (by rfl) ⟨985479, by rfl⟩ : syracuseStep 2627945 = 1970959) B1970959
theorem B2955649 : Blo 1166400 2955649 := bstep (se 2 (by rfl) ⟨1108368, by rfl⟩ : syracuseStep 2955649 = 2216737) B2216737
theorem B1751471 : Blo 1166400 1751471 := bstep (se 1 (by rfl) ⟨1313603, by rfl⟩ : syracuseStep 1751471 = 2627207) B2627207
theorem B5994989 : Blo 1166400 5994989 := bstep (se 3 (by rfl) ⟨1124060, by rfl⟩ : syracuseStep 5994989 = 2248121) B2248121
theorem B1751561 : Blo 1166400 1751561 := bstep (se 2 (by rfl) ⟨656835, by rfl⟩ : syracuseStep 1751561 = 1313671) B1313671
theorem B1751591 : Blo 1166400 1751591 := bstep (se 1 (by rfl) ⟨1313693, by rfl⟩ : syracuseStep 1751591 = 2627387) B2627387
theorem B4209191 : Blo 1166400 4209191 := bstep (se 1 (by rfl) ⟨3156893, by rfl⟩ : syracuseStep 4209191 = 6313787) B6313787
theorem B23943755 : Blo 1166400 23943755 := bstep (se 1 (by rfl) ⟨17957816, by rfl⟩ : syracuseStep 23943755 = 35915633) B35915633
theorem B1751675 : Blo 1166400 1751675 := bstep (se 1 (by rfl) ⟨1313756, by rfl⟩ : syracuseStep 1751675 = 2627513) B2627513
theorem B4430483 : Blo 1166400 4430483 := bstep (se 1 (by rfl) ⟨3322862, by rfl⟩ : syracuseStep 4430483 = 6645725) B6645725
theorem B4266695 : Blo 1166400 4266695 := bstep (se 1 (by rfl) ⟨3200021, by rfl⟩ : syracuseStep 4266695 = 6400043) B6400043
theorem B1751801 : Blo 1166400 1751801 := bstep (se 2 (by rfl) ⟨656925, by rfl⟩ : syracuseStep 1751801 = 1313851) B1313851
theorem B1751903 : Blo 1166400 1751903 := bstep (se 1 (by rfl) ⟨1313927, by rfl⟩ : syracuseStep 1751903 = 2627855) B2627855
theorem B1661801 : Blo 1166400 1661801 := bstep (se 2 (by rfl) ⟨623175, by rfl⟩ : syracuseStep 1661801 = 1246351) B1246351
theorem B1751915 : Blo 1166400 1751915 := bstep (se 1 (by rfl) ⟨1313936, by rfl⟩ : syracuseStep 1751915 = 2627873) B2627873
theorem B3939191 : Blo 1166400 3939191 := bstep (se 1 (by rfl) ⟨2954393, by rfl⟩ : syracuseStep 3939191 = 5908787) B5908787
theorem B3324833 : Blo 1166400 3324833 := bstep (se 2 (by rfl) ⟨1246812, by rfl⟩ : syracuseStep 3324833 = 2493625) B2493625
theorem B2628539 : Blo 1166400 2628539 := bstep (se 1 (by rfl) ⟨1971404, by rfl⟩ : syracuseStep 2628539 = 3942809) B3942809
theorem B1661915 : Blo 1166400 1661915 := bstep (se 1 (by rfl) ⟨1246436, by rfl⟩ : syracuseStep 1661915 = 2492873) B2492873
theorem B3152915 : Blo 1166400 3152915 := bstep (se 1 (by rfl) ⟨2364686, by rfl⟩ : syracuseStep 3152915 = 4729373) B4729373
theorem B2628665 : Blo 1166400 2628665 := bstep (se 2 (by rfl) ⟨985749, by rfl⟩ : syracuseStep 2628665 = 1971499) B1971499
theorem B3939407 : Blo 1166400 3939407 := bstep (se 1 (by rfl) ⟨2954555, by rfl⟩ : syracuseStep 3939407 = 5909111) B5909111
theorem B1752143 : Blo 1166400 1752143 := bstep (se 1 (by rfl) ⟨1314107, by rfl⟩ : syracuseStep 1752143 = 2628215) B2628215
theorem B4209779 : Blo 1166400 4209779 := bstep (se 1 (by rfl) ⟨3157334, by rfl⟩ : syracuseStep 4209779 = 6314669) B6314669
theorem B2956459 : Blo 1166400 2956459 := bstep (se 1 (by rfl) ⟨2217344, by rfl⟩ : syracuseStep 2956459 = 4434689) B4434689
theorem B1752263 : Blo 1166400 1752263 := bstep (se 1 (by rfl) ⟨1314197, by rfl⟩ : syracuseStep 1752263 = 2628395) B2628395
theorem B3325175 : Blo 1166400 3325175 := bstep (se 1 (by rfl) ⟨2493881, by rfl⟩ : syracuseStep 3325175 = 4987763) B4987763
theorem B1752425 : Blo 1166400 1752425 := bstep (se 2 (by rfl) ⟨657159, by rfl⟩ : syracuseStep 1752425 = 1314319) B1314319
theorem B1752503 : Blo 1166400 1752503 := bstep (se 1 (by rfl) ⟨1314377, by rfl⟩ : syracuseStep 1752503 = 2628755) B2628755
theorem B3939785 : Blo 1166400 3939785 := bstep (se 2 (by rfl) ⟨1477419, by rfl⟩ : syracuseStep 3939785 = 2954839) B2954839
theorem B2956763 : Blo 1166400 2956763 := bstep (se 1 (by rfl) ⟨2217572, by rfl⟩ : syracuseStep 2956763 = 4435145) B4435145
theorem B1752539 : Blo 1166400 1752539 := bstep (se 1 (by rfl) ⟨1314404, by rfl⟩ : syracuseStep 1752539 = 2628809) B2628809
theorem B4734445 : Blo 1166400 4734445 := bstep (se 3 (by rfl) ⟨887708, by rfl⟩ : syracuseStep 4734445 = 1775417) B1775417
theorem B4210385 : Blo 1166400 4210385 := bstep (se 2 (by rfl) ⟨1578894, by rfl⟩ : syracuseStep 4210385 = 3157789) B3157789
theorem B3940055 : Blo 1166400 3940055 := bstep (se 1 (by rfl) ⟨2955041, by rfl⟩ : syracuseStep 3940055 = 5910083) B5910083
theorem B6307577 : Blo 1166400 6307577 := bstep (se 2 (by rfl) ⟨2365341, by rfl⟩ : syracuseStep 6307577 = 4730683) B4730683
theorem B1662815 : Blo 1166400 1662815 := bstep (se 1 (by rfl) ⟨1247111, by rfl⟩ : syracuseStep 1662815 = 2494223) B2494223
theorem B9461623 : Blo 1166400 9461623 := bstep (se 1 (by rfl) ⟨7096217, by rfl⟩ : syracuseStep 9461623 = 14192435) B14192435
theorem B3940271 : Blo 1166400 3940271 := bstep (se 1 (by rfl) ⟨2955203, by rfl⟩ : syracuseStep 3940271 = 5910407) B5910407
theorem B30351289 : Blo 1166400 30351289 := bstep (se 2 (by rfl) ⟨11381733, by rfl⟩ : syracuseStep 30351289 = 22763467) B22763467
theorem B3325961 : Blo 1166400 3325961 := bstep (se 2 (by rfl) ⟨1247235, by rfl⟩ : syracuseStep 3325961 = 2494471) B2494471
theorem B62357521 : Blo 1166400 62357521 := bstep (se 2 (by rfl) ⟨23384070, by rfl⟩ : syracuseStep 62357521 = 46768141) B46768141
theorem B9969713 : Blo 1166400 9969713 := bstep (se 2 (by rfl) ⟨3738642, by rfl⟩ : syracuseStep 9969713 = 7477285) B7477285
theorem B17981651 : Blo 1166400 17981651 := bstep (se 1 (by rfl) ⟨13486238, by rfl⟩ : syracuseStep 17981651 = 26972477) B26972477
theorem B15974819 : Blo 1166400 15974819 := bstep (se 1 (by rfl) ⟨11981114, by rfl⟩ : syracuseStep 15974819 = 23962229) B23962229
theorem B5988833 : Blo 1166400 5988833 := bstep (se 2 (by rfl) ⟨2245812, by rfl⟩ : syracuseStep 5988833 = 4491625) B4491625
theorem B3940865 : Blo 1166400 3940865 := bstep (se 2 (by rfl) ⟨1477824, by rfl⟩ : syracuseStep 3940865 = 2955649) B2955649
theorem B12976841 : Blo 1166400 12976841 := bstep (se 2 (by rfl) ⟨4866315, by rfl⟩ : syracuseStep 12976841 = 9732631) B9732631
theorem B5907167 : Blo 1166400 5907167 := bstep (se 1 (by rfl) ⟨4430375, by rfl⟩ : syracuseStep 5907167 = 8860751) B8860751
theorem B7480259 : Blo 1166400 7480259 := bstep (se 1 (by rfl) ⟨5610194, by rfl⟩ : syracuseStep 7480259 = 11220389) B11220389
theorem B6644699 : Blo 1166400 6644699 := bstep (se 1 (by rfl) ⟨4983524, by rfl⟩ : syracuseStep 6644699 = 9967049) B9967049
theorem B3941351 : Blo 1166400 3941351 := bstep (se 1 (by rfl) ⟨2956013, by rfl⟩ : syracuseStep 3941351 = 5912027) B5912027
theorem B2491489 : Blo 1166400 2491489 := bstep (se 2 (by rfl) ⟨934308, by rfl⟩ : syracuseStep 2491489 = 1868617) B1868617
theorem B7480619 : Blo 1166400 7480619 := bstep (se 1 (by rfl) ⟨5610464, by rfl⟩ : syracuseStep 7480619 = 11220929) B11220929
theorem B3941675 : Blo 1166400 3941675 := bstep (se 1 (by rfl) ⟨2956256, by rfl⟩ : syracuseStep 3941675 = 5912513) B5912513
theorem B3941945 : Blo 1166400 3941945 := bstep (se 2 (by rfl) ⟨1478229, by rfl⟩ : syracuseStep 3941945 = 2956459) B2956459
theorem B1476407 : Blo 1166400 1476407 := bstep (se 1 (by rfl) ⟨1107305, by rfl⟩ : syracuseStep 1476407 = 2214611) B2214611
theorem B1312591 : Blo 1166400 1312591 := bstep (se 1 (by rfl) ⟨984443, by rfl⟩ : syracuseStep 1312591 = 1968887) B1968887
theorem B1476559 : Blo 1166400 1476559 := bstep (se 1 (by rfl) ⟨1107419, by rfl⟩ : syracuseStep 1476559 = 2214839) B2214839
theorem B1312987 : Blo 1166400 1312987 := bstep (se 1 (by rfl) ⟨984740, by rfl⟩ : syracuseStep 1312987 = 1969481) B1969481
theorem B4434173 : Blo 1166400 4434173 := bstep (se 3 (by rfl) ⟨831407, by rfl⟩ : syracuseStep 4434173 = 1662815) B1662815
theorem B4983065 : Blo 1166400 4983065 := bstep (se 2 (by rfl) ⟨1868649, by rfl⟩ : syracuseStep 4983065 = 3737299) B3737299
theorem B1968475 : Blo 1166400 1968475 := bstep (se 1 (by rfl) ⟨1476356, by rfl⟩ : syracuseStep 1968475 = 2952713) B2952713
theorem B2804059 : Blo 1166400 2804059 := bstep (se 1 (by rfl) ⟨2103044, by rfl⟩ : syracuseStep 2804059 = 4206089) B4206089
theorem B7096805 : Blo 1166400 7096805 := bstep (se 4 (by rfl) ⟨665325, by rfl⟩ : syracuseStep 7096805 = 1330651) B1330651
theorem B4205051 : Blo 1166400 4205051 := bstep (se 1 (by rfl) ⟨3153788, by rfl⟩ : syracuseStep 4205051 = 6307577) B6307577
theorem B1313275 : Blo 1166400 1313275 := bstep (se 1 (by rfl) ⟨984956, by rfl⟩ : syracuseStep 1313275 = 1969913) B1969913
theorem B1313455 : Blo 1166400 1313455 := bstep (se 1 (by rfl) ⟨985091, by rfl⟩ : syracuseStep 1313455 = 1970183) B1970183
theorem B3943187 : Blo 1166400 3943187 := bstep (se 1 (by rfl) ⟨2957390, by rfl⟩ : syracuseStep 3943187 = 5914781) B5914781
theorem B8866583 : Blo 1166400 8866583 := bstep (se 1 (by rfl) ⟨6649937, by rfl⟩ : syracuseStep 8866583 = 13299875) B13299875
theorem B19958561 : Blo 1166400 19958561 := bstep (se 2 (by rfl) ⟨7484460, by rfl⟩ : syracuseStep 19958561 = 14968921) B14968921
theorem B3156815 : Blo 1166400 3156815 := bstep (se 1 (by rfl) ⟨2367611, by rfl⟩ : syracuseStep 3156815 = 4735223) B4735223
theorem B1477531 : Blo 1166400 1477531 := bstep (se 1 (by rfl) ⟨1108148, by rfl⟩ : syracuseStep 1477531 = 2216297) B2216297
theorem B5909435 : Blo 1166400 5909435 := bstep (se 1 (by rfl) ⟨4432076, by rfl⟩ : syracuseStep 5909435 = 8864153) B8864153
theorem B1313743 : Blo 1166400 1313743 := bstep (se 1 (by rfl) ⟨985307, by rfl⟩ : syracuseStep 1313743 = 1970615) B1970615
theorem B11226077 : Blo 1166400 11226077 := bstep (se 3 (by rfl) ⟨2104889, by rfl⟩ : syracuseStep 11226077 = 4209779) B4209779
theorem B9464971 : Blo 1166400 9464971 := bstep (se 1 (by rfl) ⟨7098728, by rfl⟩ : syracuseStep 9464971 = 14197457) B14197457
theorem B2493659 : Blo 1166400 2493659 := bstep (se 1 (by rfl) ⟨1870244, by rfl⟩ : syracuseStep 2493659 = 3740489) B3740489
theorem B22727927 : Blo 1166400 22727927 := bstep (se 1 (by rfl) ⟨17045945, by rfl⟩ : syracuseStep 22727927 = 34091891) B34091891
theorem B1166623 : Blo 1166400 1166623 := bstep (se 1 (by rfl) ⟨874967, by rfl⟩ : syracuseStep 1166623 = 1749935) B1749935
theorem B10644767 : Blo 1166400 10644767 := bstep (se 1 (by rfl) ⟨7983575, by rfl⟩ : syracuseStep 10644767 = 15967151) B15967151
theorem B1969447 : Blo 1166400 1969447 := bstep (se 1 (by rfl) ⟨1477085, by rfl⟩ : syracuseStep 1969447 = 2954171) B2954171
theorem B1166683 : Blo 1166400 1166683 := bstep (se 1 (by rfl) ⟨875012, by rfl⟩ : syracuseStep 1166683 = 1750025) B1750025
theorem B1314139 : Blo 1166400 1314139 := bstep (se 1 (by rfl) ⟨985604, by rfl⟩ : syracuseStep 1314139 = 1971209) B1971209
theorem B1166703 : Blo 1166400 1166703 := bstep (se 1 (by rfl) ⟨875027, by rfl⟩ : syracuseStep 1166703 = 1750055) B1750055
theorem B4730231 : Blo 1166400 4730231 := bstep (se 1 (by rfl) ⟨3547673, by rfl⟩ : syracuseStep 4730231 = 7095347) B7095347
theorem B2952571 : Blo 1166400 2952571 := bstep (se 1 (by rfl) ⟨2214428, by rfl⟩ : syracuseStep 2952571 = 4428857) B4428857
theorem B1166759 : Blo 1166400 1166759 := bstep (se 1 (by rfl) ⟨875069, by rfl⟩ : syracuseStep 1166759 = 1750139) B1750139
theorem B7474619 : Blo 1166400 7474619 := bstep (se 1 (by rfl) ⟨5605964, by rfl⟩ : syracuseStep 7474619 = 11211929) B11211929
theorem B1314247 : Blo 1166400 1314247 := bstep (se 1 (by rfl) ⟨985685, by rfl⟩ : syracuseStep 1314247 = 1971371) B1971371
theorem B1166843 : Blo 1166400 1166843 := bstep (se 1 (by rfl) ⟨875132, by rfl⟩ : syracuseStep 1166843 = 1750265) B1750265
theorem B9965065 : Blo 1166400 9965065 := bstep (se 2 (by rfl) ⟨3736899, by rfl⟩ : syracuseStep 9965065 = 7473799) B7473799
theorem B4984379 : Blo 1166400 4984379 := bstep (se 1 (by rfl) ⟨3738284, by rfl⟩ : syracuseStep 4984379 = 7476569) B7476569
theorem B5328443 : Blo 1166400 5328443 := bstep (se 1 (by rfl) ⟨3996332, by rfl⟩ : syracuseStep 5328443 = 7992665) B7992665
theorem B1166911 : Blo 1166400 1166911 := bstep (se 1 (by rfl) ⟨875183, by rfl⟩ : syracuseStep 1166911 = 1750367) B1750367
theorem B1166919 : Blo 1166400 1166919 := bstep (se 1 (by rfl) ⟨875189, by rfl⟩ : syracuseStep 1166919 = 1750379) B1750379
theorem B2215507 : Blo 1166400 2215507 := bstep (se 1 (by rfl) ⟨1661630, by rfl⟩ : syracuseStep 2215507 = 3323261) B3323261
theorem B2625119 : Blo 1166400 2625119 := bstep (se 1 (by rfl) ⟨1968839, by rfl⟩ : syracuseStep 2625119 = 3937679) B3937679
theorem B1167071 : Blo 1166400 1167071 := bstep (se 1 (by rfl) ⟨875303, by rfl⟩ : syracuseStep 1167071 = 1750607) B1750607
theorem B2805511 : Blo 1166400 2805511 := bstep (se 1 (by rfl) ⟨2104133, by rfl⟩ : syracuseStep 2805511 = 4208267) B4208267
theorem B2953007 : Blo 1166400 2953007 := bstep (se 1 (by rfl) ⟨2214755, by rfl⟩ : syracuseStep 2953007 = 4429511) B4429511
theorem B1167151 : Blo 1166400 1167151 := bstep (se 1 (by rfl) ⟨875363, by rfl⟩ : syracuseStep 1167151 = 1750727) B1750727
theorem B1969967 : Blo 1166400 1969967 := bstep (se 1 (by rfl) ⟨1477475, by rfl⟩ : syracuseStep 1969967 = 2954951) B2954951
theorem B2625335 : Blo 1166400 2625335 := bstep (se 1 (by rfl) ⟨1969001, by rfl⟩ : syracuseStep 2625335 = 3938003) B3938003
theorem B1167259 : Blo 1166400 1167259 := bstep (se 1 (by rfl) ⟨875444, by rfl⟩ : syracuseStep 1167259 = 1750889) B1750889
theorem B1167311 : Blo 1166400 1167311 := bstep (se 1 (by rfl) ⟨875483, by rfl⟩ : syracuseStep 1167311 = 1750967) B1750967
theorem B1167335 : Blo 1166400 1167335 := bstep (se 1 (by rfl) ⟨875501, by rfl⟩ : syracuseStep 1167335 = 1751003) B1751003
theorem B4984841 : Blo 1166400 4984841 := bstep (se 2 (by rfl) ⟨1869315, by rfl⟩ : syracuseStep 4984841 = 3738631) B3738631
theorem B10113083 : Blo 1166400 10113083 := bstep (se 1 (by rfl) ⟨7584812, by rfl⟩ : syracuseStep 10113083 = 15169625) B15169625
theorem B2625641 : Blo 1166400 2625641 := bstep (se 2 (by rfl) ⟨984615, by rfl⟩ : syracuseStep 2625641 = 1969231) B1969231
theorem B5910731 : Blo 1166400 5910731 := bstep (se 1 (by rfl) ⟨4433048, by rfl⟩ : syracuseStep 5910731 = 8866097) B8866097
theorem B8417483 : Blo 1166400 8417483 := bstep (se 1 (by rfl) ⟨6313112, by rfl⟩ : syracuseStep 8417483 = 12626225) B12626225
theorem B1167647 : Blo 1166400 1167647 := bstep (se 1 (by rfl) ⟨875735, by rfl⟩ : syracuseStep 1167647 = 1751471) B1751471
theorem B1167707 : Blo 1166400 1167707 := bstep (se 1 (by rfl) ⟨875780, by rfl⟩ : syracuseStep 1167707 = 1751561) B1751561
theorem B1167727 : Blo 1166400 1167727 := bstep (se 1 (by rfl) ⟨875795, by rfl⟩ : syracuseStep 1167727 = 1751591) B1751591
theorem B2806127 : Blo 1166400 2806127 := bstep (se 1 (by rfl) ⟨2104595, by rfl⟩ : syracuseStep 2806127 = 4209191) B4209191
theorem B15962503 : Blo 1166400 15962503 := bstep (se 1 (by rfl) ⟨11971877, by rfl⟩ : syracuseStep 15962503 = 23943755) B23943755
theorem B1167783 : Blo 1166400 1167783 := bstep (se 1 (by rfl) ⟨875837, by rfl⟩ : syracuseStep 1167783 = 1751675) B1751675
theorem B7483823 : Blo 1166400 7483823 := bstep (se 1 (by rfl) ⟨5612867, by rfl⟩ : syracuseStep 7483823 = 11225735) B11225735
theorem B2953655 : Blo 1166400 2953655 := bstep (se 1 (by rfl) ⟨2215241, by rfl⟩ : syracuseStep 2953655 = 4430483) B4430483
theorem B1167867 : Blo 1166400 1167867 := bstep (se 1 (by rfl) ⟨875900, by rfl⟩ : syracuseStep 1167867 = 1751801) B1751801
theorem B11227693 : Blo 1166400 11227693 := bstep (se 3 (by rfl) ⟨2105192, by rfl⟩ : syracuseStep 11227693 = 4210385) B4210385
theorem B10646077 : Blo 1166400 10646077 := bstep (se 3 (by rfl) ⟨1996139, by rfl⟩ : syracuseStep 10646077 = 3992279) B3992279
theorem B1167935 : Blo 1166400 1167935 := bstep (se 1 (by rfl) ⟨875951, by rfl⟩ : syracuseStep 1167935 = 1751903) B1751903
theorem B1167943 : Blo 1166400 1167943 := bstep (se 1 (by rfl) ⟨875957, by rfl⟩ : syracuseStep 1167943 = 1751915) B1751915
theorem B2626127 : Blo 1166400 2626127 := bstep (se 1 (by rfl) ⟨1969595, by rfl⟩ : syracuseStep 2626127 = 3939191) B3939191
theorem B1749611 : Blo 1166400 1749611 := bstep (se 1 (by rfl) ⟨1312208, by rfl⟩ : syracuseStep 1749611 = 2624417) B2624417
theorem B2216555 : Blo 1166400 2216555 := bstep (se 1 (by rfl) ⟨1662416, by rfl⟩ : syracuseStep 2216555 = 3324833) B3324833
theorem B6312593 : Blo 1166400 6312593 := bstep (se 2 (by rfl) ⟨2367222, by rfl⟩ : syracuseStep 6312593 = 4734445) B4734445
theorem B8417945 : Blo 1166400 8417945 := bstep (se 2 (by rfl) ⟨3156729, by rfl⟩ : syracuseStep 8417945 = 6313459) B6313459
theorem B2101943 : Blo 1166400 2101943 := bstep (se 1 (by rfl) ⟨1576457, by rfl⟩ : syracuseStep 2101943 = 3152915) B3152915
theorem B2626271 : Blo 1166400 2626271 := bstep (se 1 (by rfl) ⟨1969703, by rfl⟩ : syracuseStep 2626271 = 3939407) B3939407
theorem B1168095 : Blo 1166400 1168095 := bstep (se 1 (by rfl) ⟨876071, by rfl⟩ : syracuseStep 1168095 = 1752143) B1752143
theorem B1168175 : Blo 1166400 1168175 := bstep (se 1 (by rfl) ⟨876131, by rfl⟩ : syracuseStep 1168175 = 1752263) B1752263
theorem B1749839 : Blo 1166400 1749839 := bstep (se 1 (by rfl) ⟨1312379, by rfl⟩ : syracuseStep 1749839 = 2624759) B2624759
theorem B2216783 : Blo 1166400 2216783 := bstep (se 1 (by rfl) ⟨1662587, by rfl⟩ : syracuseStep 2216783 = 3325175) B3325175
theorem B1168283 : Blo 1166400 1168283 := bstep (se 1 (by rfl) ⟨876212, by rfl⟩ : syracuseStep 1168283 = 1752425) B1752425
theorem B1168335 : Blo 1166400 1168335 := bstep (se 1 (by rfl) ⟨876251, by rfl⟩ : syracuseStep 1168335 = 1752503) B1752503
theorem B2626523 : Blo 1166400 2626523 := bstep (se 1 (by rfl) ⟨1969892, by rfl⟩ : syracuseStep 2626523 = 3939785) B3939785
theorem B1971175 : Blo 1166400 1971175 := bstep (se 1 (by rfl) ⟨1478381, by rfl⟩ : syracuseStep 1971175 = 2956763) B2956763
theorem B1168359 : Blo 1166400 1168359 := bstep (se 1 (by rfl) ⟨876269, by rfl⟩ : syracuseStep 1168359 = 1752539) B1752539
theorem B2626703 : Blo 1166400 2626703 := bstep (se 1 (by rfl) ⟨1970027, by rfl⟩ : syracuseStep 2626703 = 3940055) B3940055
theorem B1750235 : Blo 1166400 1750235 := bstep (se 1 (by rfl) ⟨1312676, by rfl⟩ : syracuseStep 1750235 = 2625353) B2625353
theorem B2626793 : Blo 1166400 2626793 := bstep (se 2 (by rfl) ⟨985047, by rfl⟩ : syracuseStep 2626793 = 1970095) B1970095
theorem B14955799 : Blo 1166400 14955799 := bstep (se 1 (by rfl) ⟨11216849, by rfl⟩ : syracuseStep 14955799 = 22433699) B22433699
theorem B2626847 : Blo 1166400 2626847 := bstep (se 1 (by rfl) ⟨1970135, by rfl⟩ : syracuseStep 2626847 = 3940271) B3940271
theorem B1750409 : Blo 1166400 1750409 := bstep (se 2 (by rfl) ⟨656403, by rfl⟩ : syracuseStep 1750409 = 1312807) B1312807
theorem B2954657 : Blo 1166400 2954657 := bstep (se 2 (by rfl) ⟨1107996, by rfl⟩ : syracuseStep 2954657 = 2215993) B2215993
theorem B3937949 : Blo 1166400 3937949 := bstep (se 3 (by rfl) ⟨738365, by rfl⟩ : syracuseStep 3937949 = 1476731) B1476731
theorem B1750763 : Blo 1166400 1750763 := bstep (se 1 (by rfl) ⟨1313072, by rfl⟩ : syracuseStep 1750763 = 2626145) B2626145
theorem B2627369 : Blo 1166400 2627369 := bstep (se 2 (by rfl) ⟨985263, by rfl⟩ : syracuseStep 2627369 = 1970527) B1970527
theorem B4732759 : Blo 1166400 4732759 := bstep (se 1 (by rfl) ⟨3549569, by rfl⟩ : syracuseStep 4732759 = 7099139) B7099139
theorem B2955113 : Blo 1166400 2955113 := bstep (se 2 (by rfl) ⟨1108167, by rfl⟩ : syracuseStep 2955113 = 2216335) B2216335
theorem B1750991 : Blo 1166400 1750991 := bstep (se 1 (by rfl) ⟨1313243, by rfl⟩ : syracuseStep 1750991 = 2626487) B2626487
theorem B3938489 : Blo 1166400 3938489 := bstep (se 2 (by rfl) ⟨1476933, by rfl⟩ : syracuseStep 3938489 = 2953867) B2953867
theorem B11991287 : Blo 1166400 11991287 := bstep (se 1 (by rfl) ⟨8993465, by rfl⟩ : syracuseStep 11991287 = 17986931) B17986931
theorem B1751387 : Blo 1166400 1751387 := bstep (se 1 (by rfl) ⟨1313540, by rfl⟩ : syracuseStep 1751387 = 2627081) B2627081
theorem B5912999 : Blo 1166400 5912999 := bstep (se 1 (by rfl) ⟨4434749, by rfl⟩ : syracuseStep 5912999 = 8869499) B8869499
theorem B2660791 : Blo 1166400 2660791 := bstep (se 1 (by rfl) ⟨1995593, by rfl⟩ : syracuseStep 2660791 = 3991187) B3991187
theorem B9468343 : Blo 1166400 9468343 := bstep (se 1 (by rfl) ⟨7101257, by rfl⟩ : syracuseStep 9468343 = 14202515) B14202515
theorem B1751615 : Blo 1166400 1751615 := bstep (se 1 (by rfl) ⟨1313711, by rfl⟩ : syracuseStep 1751615 = 2627423) B2627423
theorem B2366023 : Blo 1166400 2366023 := bstep (se 1 (by rfl) ⟨1774517, by rfl⟩ : syracuseStep 2366023 = 3549035) B3549035
theorem B5913161 : Blo 1166400 5913161 := bstep (se 2 (by rfl) ⟨2217435, by rfl⟩ : syracuseStep 5913161 = 4434871) B4434871
theorem B1751735 : Blo 1166400 1751735 := bstep (se 1 (by rfl) ⟨1313801, by rfl⟩ : syracuseStep 1751735 = 2627603) B2627603
theorem B2628431 : Blo 1166400 2628431 := bstep (se 1 (by rfl) ⟨1971323, by rfl⟩ : syracuseStep 2628431 = 3942647) B3942647
theorem B1751963 : Blo 1166400 1751963 := bstep (se 1 (by rfl) ⟨1313972, by rfl⟩ : syracuseStep 1751963 = 2627945) B2627945
theorem B3996659 : Blo 1166400 3996659 := bstep (se 1 (by rfl) ⟨2997494, by rfl⟩ : syracuseStep 3996659 = 5994989) B5994989
theorem B2628647 : Blo 1166400 2628647 := bstep (se 1 (by rfl) ⟨1971485, by rfl⟩ : syracuseStep 2628647 = 3942971) B3942971
theorem B5905547 : Blo 1166400 5905547 := bstep (se 1 (by rfl) ⟨4429160, by rfl⟩ : syracuseStep 5905547 = 8858321) B8858321
theorem B11377853 : Blo 1166400 11377853 := bstep (se 3 (by rfl) ⟨2133347, by rfl⟩ : syracuseStep 11377853 = 4266695) B4266695
theorem B24288473 : Blo 1166400 24288473 := bstep (se 2 (by rfl) ⟨9108177, by rfl⟩ : syracuseStep 24288473 = 18216355) B18216355
theorem B2628827 : Blo 1166400 2628827 := bstep (se 1 (by rfl) ⟨1971620, by rfl⟩ : syracuseStep 2628827 = 3943241) B3943241
theorem B6479135 : Blo 1166400 6479135 := bstep (se 1 (by rfl) ⟨4859351, by rfl⟩ : syracuseStep 6479135 = 9718703) B9718703
theorem B1752359 : Blo 1166400 1752359 := bstep (se 1 (by rfl) ⟨1314269, by rfl⟩ : syracuseStep 1752359 = 2628539) B2628539
theorem B1752443 : Blo 1166400 1752443 := bstep (se 1 (by rfl) ⟨1314332, by rfl⟩ : syracuseStep 1752443 = 2628665) B2628665
theorem B60611975 : Blo 1166400 60611975 := bstep (se 1 (by rfl) ⟨45458981, by rfl⟩ : syracuseStep 60611975 = 90917963) B90917963
theorem B1752569 : Blo 1166400 1752569 := bstep (se 2 (by rfl) ⟨657213, by rfl⟩ : syracuseStep 1752569 = 1314427) B1314427
theorem B40443461 : Blo 1166400 40443461 := bstep (se 4 (by rfl) ⟨3791574, by rfl⟩ : syracuseStep 40443461 = 7583149) B7583149
theorem B4431455 : Blo 1166400 4431455 := bstep (se 1 (by rfl) ⟨3323591, by rfl⟩ : syracuseStep 4431455 = 6647183) B6647183
theorem B12623455 : Blo 1166400 12623455 := bstep (se 1 (by rfl) ⟨9467591, by rfl⟩ : syracuseStep 12623455 = 18935183) B18935183
theorem B2956895 : Blo 1166400 2956895 := bstep (se 1 (by rfl) ⟨2217671, by rfl⟩ : syracuseStep 2956895 = 4435343) B4435343
theorem B4431469 : Blo 1166400 4431469 := bstep (se 3 (by rfl) ⟨830900, by rfl⟩ : syracuseStep 4431469 = 1661801) B1661801
theorem B2662049 : Blo 1166400 2662049 := bstep (se 2 (by rfl) ⟨998268, by rfl⟩ : syracuseStep 2662049 = 1996537) B1996537
theorem B3940001 : Blo 1166400 3940001 := bstep (se 2 (by rfl) ⟨1477500, by rfl⟩ : syracuseStep 3940001 = 2955001) B2955001
theorem B57614141 : Blo 1166400 57614141 := bstep (se 3 (by rfl) ⟨10802651, by rfl⟩ : syracuseStep 57614141 = 21605303) B21605303
theorem B12615497 : Blo 1166400 12615497 := bstep (se 2 (by rfl) ⟨4730811, by rfl⟩ : syracuseStep 12615497 = 9461623) B9461623
theorem B4431773 : Blo 1166400 4431773 := bstep (se 3 (by rfl) ⟨830957, by rfl⟩ : syracuseStep 4431773 = 1661915) B1661915
theorem B40468385 : Blo 1166400 40468385 := bstep (se 2 (by rfl) ⟨15175644, by rfl⟩ : syracuseStep 40468385 = 30351289) B30351289
theorem B6742055 : Blo 1166400 6742055 := bstep (se 1 (by rfl) ⟨5056541, by rfl⟩ : syracuseStep 6742055 = 10113083) B10113083
theorem B3940487 : Blo 1166400 3940487 := bstep (se 1 (by rfl) ⟨2955365, by rfl⟩ : syracuseStep 3940487 = 5910731) B5910731
theorem B5611655 : Blo 1166400 5611655 := bstep (se 1 (by rfl) ⟨4208741, by rfl⟩ : syracuseStep 5611655 = 8417483) B8417483
theorem B10649879 : Blo 1166400 10649879 := bstep (se 1 (by rfl) ⟨7987409, by rfl⟩ : syracuseStep 10649879 = 15974819) B15974819
theorem B4989215 : Blo 1166400 4989215 := bstep (se 1 (by rfl) ⟨3741911, by rfl⟩ : syracuseStep 4989215 = 7483823) B7483823
theorem B5611963 : Blo 1166400 5611963 := bstep (se 1 (by rfl) ⟨4208972, by rfl⟩ : syracuseStep 5611963 = 8417945) B8417945
theorem B1401295 : Blo 1166400 1401295 := bstep (se 1 (by rfl) ⟨1050971, by rfl⟩ : syracuseStep 1401295 = 2101943) B2101943
theorem B8651227 : Blo 1166400 8651227 := bstep (se 1 (by rfl) ⟨6488420, by rfl⟩ : syracuseStep 8651227 = 12976841) B12976841
theorem B21283337 : Blo 1166400 21283337 := bstep (se 2 (by rfl) ⟨7981251, by rfl⟩ : syracuseStep 21283337 = 15962503) B15962503
theorem B3547721 : Blo 1166400 3547721 := bstep (se 2 (by rfl) ⟨1330395, by rfl⟩ : syracuseStep 3547721 = 2660791) B2660791
theorem B12624457 : Blo 1166400 12624457 := bstep (se 2 (by rfl) ⟨4734171, by rfl⟩ : syracuseStep 12624457 = 9468343) B9468343
theorem B3154697 : Blo 1166400 3154697 := bstep (se 2 (by rfl) ⟨1183011, by rfl⟩ : syracuseStep 3154697 = 2366023) B2366023
theorem B19932317 : Blo 1166400 19932317 := bstep (se 3 (by rfl) ⟨3737309, by rfl⟩ : syracuseStep 19932317 = 7474619) B7474619
theorem B3941999 : Blo 1166400 3941999 := bstep (se 1 (by rfl) ⟨2956499, by rfl⟩ : syracuseStep 3941999 = 5912999) B5912999
theorem B2803367 : Blo 1166400 2803367 := bstep (se 1 (by rfl) ⟨2102525, by rfl⟩ : syracuseStep 2803367 = 4205051) B4205051
theorem B19941065 : Blo 1166400 19941065 := bstep (se 2 (by rfl) ⟨7477899, by rfl⟩ : syracuseStep 19941065 = 14955799) B14955799
theorem B3942107 : Blo 1166400 3942107 := bstep (se 1 (by rfl) ⟨2956580, by rfl⟩ : syracuseStep 3942107 = 5913161) B5913161
theorem B13305707 : Blo 1166400 13305707 := bstep (se 1 (by rfl) ⟨9979280, by rfl⟩ : syracuseStep 13305707 = 19958561) B19958561
theorem B5908625 : Blo 1166400 5908625 := bstep (se 2 (by rfl) ⟨2215734, by rfl⟩ : syracuseStep 5908625 = 4431469) B4431469
theorem B4319423 : Blo 1166400 4319423 := bstep (se 1 (by rfl) ⟨3239567, by rfl⟩ : syracuseStep 4319423 = 6479135) B6479135
theorem B7096511 : Blo 1166400 7096511 := bstep (se 1 (by rfl) ⟨5322383, by rfl⟩ : syracuseStep 7096511 = 10644767) B10644767
theorem B26962307 : Blo 1166400 26962307 := bstep (se 1 (by rfl) ⟨20221730, by rfl⟩ : syracuseStep 26962307 = 40443461) B40443461
theorem B6310345 : Blo 1166400 6310345 := bstep (se 2 (by rfl) ⟨2366379, by rfl⟩ : syracuseStep 6310345 = 4732759) B4732759
theorem B1968671 : Blo 1166400 1968671 := bstep (se 1 (by rfl) ⟨1476503, by rfl⟩ : syracuseStep 1968671 = 2953007) B2953007
theorem B1313311 : Blo 1166400 1313311 := bstep (se 1 (by rfl) ⟨984983, by rfl⟩ : syracuseStep 1313311 = 1969967) B1969967
theorem B1968745 : Blo 1166400 1968745 := bstep (se 2 (by rfl) ⟨738279, by rfl⟩ : syracuseStep 1968745 = 1476559) B1476559
theorem B26978923 : Blo 1166400 26978923 := bstep (se 1 (by rfl) ⟨20234192, by rfl⟩ : syracuseStep 26978923 = 40468385) B40468385
theorem B83143361 : Blo 1166400 83143361 := bstep (se 2 (by rfl) ⟨31178760, by rfl⟩ : syracuseStep 83143361 = 62357521) B62357521
theorem B6646475 : Blo 1166400 6646475 := bstep (se 1 (by rfl) ⟨4984856, by rfl⟩ : syracuseStep 6646475 = 9969713) B9969713
theorem B11987767 : Blo 1166400 11987767 := bstep (se 1 (by rfl) ⟨8990825, by rfl⟩ : syracuseStep 11987767 = 17981651) B17981651
theorem B1870751 : Blo 1166400 1870751 := bstep (se 1 (by rfl) ⟨1403063, by rfl⟩ : syracuseStep 1870751 = 2806127) B2806127
theorem B1969103 : Blo 1166400 1969103 := bstep (se 1 (by rfl) ⟨1476827, by rfl⟩ : syracuseStep 1969103 = 2953655) B2953655
theorem B3992555 : Blo 1166400 3992555 := bstep (se 1 (by rfl) ⟨2994416, by rfl⟩ : syracuseStep 3992555 = 5988833) B5988833
theorem B1166407 : Blo 1166400 1166407 := bstep (se 1 (by rfl) ⟨874805, by rfl⟩ : syracuseStep 1166407 = 1749611) B1749611
theorem B1477703 : Blo 1166400 1477703 := bstep (se 1 (by rfl) ⟨1108277, by rfl⟩ : syracuseStep 1477703 = 2216555) B2216555
theorem B2624633 : Blo 1166400 2624633 := bstep (se 2 (by rfl) ⟨984237, by rfl⟩ : syracuseStep 2624633 = 1968475) B1968475
theorem B3738745 : Blo 1166400 3738745 := bstep (se 2 (by rfl) ⟨1402029, by rfl⟩ : syracuseStep 3738745 = 2804059) B2804059
theorem B1166559 : Blo 1166400 1166559 := bstep (se 1 (by rfl) ⟨874919, by rfl⟩ : syracuseStep 1166559 = 1749839) B1749839
theorem B1477855 : Blo 1166400 1477855 := bstep (se 1 (by rfl) ⟨1108391, by rfl⟩ : syracuseStep 1477855 = 2216783) B2216783
theorem B31976765 : Blo 1166400 31976765 := bstep (se 3 (by rfl) ⟨5995643, by rfl⟩ : syracuseStep 31976765 = 11991287) B11991287
theorem B14970257 : Blo 1166400 14970257 := bstep (se 2 (by rfl) ⟨5613846, by rfl⟩ : syracuseStep 14970257 = 11227693) B11227693
theorem B1166823 : Blo 1166400 1166823 := bstep (se 1 (by rfl) ⟨875117, by rfl⟩ : syracuseStep 1166823 = 1750235) B1750235
theorem B1166939 : Blo 1166400 1166939 := bstep (se 1 (by rfl) ⟨875204, by rfl⟩ : syracuseStep 1166939 = 1750409) B1750409
theorem B1969771 : Blo 1166400 1969771 := bstep (se 1 (by rfl) ⟨1477328, by rfl⟩ : syracuseStep 1969771 = 2954657) B2954657
theorem B2625299 : Blo 1166400 2625299 := bstep (se 1 (by rfl) ⟨1968974, by rfl⟩ : syracuseStep 2625299 = 3937949) B3937949
theorem B1167175 : Blo 1166400 1167175 := bstep (se 1 (by rfl) ⟨875381, by rfl⟩ : syracuseStep 1167175 = 1750763) B1750763
theorem B1970041 : Blo 1166400 1970041 := bstep (se 2 (by rfl) ⟨738765, by rfl⟩ : syracuseStep 1970041 = 1477531) B1477531
theorem B1970075 : Blo 1166400 1970075 := bstep (se 1 (by rfl) ⟨1477556, by rfl⟩ : syracuseStep 1970075 = 2955113) B2955113
theorem B1167327 : Blo 1166400 1167327 := bstep (se 1 (by rfl) ⟨875495, by rfl⟩ : syracuseStep 1167327 = 1750991) B1750991
theorem B2625659 : Blo 1166400 2625659 := bstep (se 1 (by rfl) ⟨1969244, by rfl⟩ : syracuseStep 2625659 = 3938489) B3938489
theorem B3321985 : Blo 1166400 3321985 := bstep (se 2 (by rfl) ⟨1245744, by rfl⟩ : syracuseStep 3321985 = 2491489) B2491489
theorem B14209181 : Blo 1166400 14209181 := bstep (se 3 (by rfl) ⟨2664221, by rfl⟩ : syracuseStep 14209181 = 5328443) B5328443
theorem B12619961 : Blo 1166400 12619961 := bstep (se 2 (by rfl) ⟨4732485, by rfl⟩ : syracuseStep 12619961 = 9464971) B9464971
theorem B3322043 : Blo 1166400 3322043 := bstep (se 1 (by rfl) ⟨2491532, by rfl⟩ : syracuseStep 3322043 = 4983065) B4983065
theorem B1167591 : Blo 1166400 1167591 := bstep (se 1 (by rfl) ⟨875693, by rfl⟩ : syracuseStep 1167591 = 1751387) B1751387
theorem B4731203 : Blo 1166400 4731203 := bstep (se 1 (by rfl) ⟨3548402, by rfl⟩ : syracuseStep 4731203 = 7096805) B7096805
theorem B1167743 : Blo 1166400 1167743 := bstep (se 1 (by rfl) ⟨875807, by rfl⟩ : syracuseStep 1167743 = 1751615) B1751615
theorem B2625929 : Blo 1166400 2625929 := bstep (se 2 (by rfl) ⟨984723, by rfl⟩ : syracuseStep 2625929 = 1969447) B1969447
theorem B7098797 : Blo 1166400 7098797 := bstep (se 3 (by rfl) ⟨1331024, by rfl⟩ : syracuseStep 7098797 = 2662049) B2662049
theorem B1167823 : Blo 1166400 1167823 := bstep (se 1 (by rfl) ⟨875867, by rfl⟩ : syracuseStep 1167823 = 1751735) B1751735
theorem B3936761 : Blo 1166400 3936761 := bstep (se 2 (by rfl) ⟨1476285, by rfl⟩ : syracuseStep 3936761 = 2952571) B2952571
theorem B5911055 : Blo 1166400 5911055 := bstep (se 1 (by rfl) ⟨4433291, by rfl⟩ : syracuseStep 5911055 = 8866583) B8866583
theorem B1167975 : Blo 1166400 1167975 := bstep (se 1 (by rfl) ⟨875981, by rfl⟩ : syracuseStep 1167975 = 1751963) B1751963
theorem B7484051 : Blo 1166400 7484051 := bstep (se 1 (by rfl) ⟨5613038, by rfl⟩ : syracuseStep 7484051 = 11226077) B11226077
theorem B3937031 : Blo 1166400 3937031 := bstep (se 1 (by rfl) ⟨2952773, by rfl⟩ : syracuseStep 3937031 = 5905547) B5905547
theorem B2954009 : Blo 1166400 2954009 := bstep (se 2 (by rfl) ⟨1107753, by rfl⟩ : syracuseStep 2954009 = 2215507) B2215507
theorem B16831273 : Blo 1166400 16831273 := bstep (se 2 (by rfl) ⟨6311727, by rfl⟩ : syracuseStep 16831273 = 12623455) B12623455
theorem B16192315 : Blo 1166400 16192315 := bstep (se 1 (by rfl) ⟨12144236, by rfl⟩ : syracuseStep 16192315 = 24288473) B24288473
theorem B3937085 : Blo 1166400 3937085 := bstep (se 3 (by rfl) ⟨738203, by rfl⟩ : syracuseStep 3937085 = 1476407) B1476407
theorem B15151951 : Blo 1166400 15151951 := bstep (se 1 (by rfl) ⟨11363963, by rfl⟩ : syracuseStep 15151951 = 22727927) B22727927
theorem B1168239 : Blo 1166400 1168239 := bstep (se 1 (by rfl) ⟨876179, by rfl⟩ : syracuseStep 1168239 = 1752359) B1752359
theorem B8418173 : Blo 1166400 8418173 := bstep (se 3 (by rfl) ⟨1578407, by rfl⟩ : syracuseStep 8418173 = 3156815) B3156815
theorem B1168295 : Blo 1166400 1168295 := bstep (se 1 (by rfl) ⟨876221, by rfl⟩ : syracuseStep 1168295 = 1752443) B1752443
theorem B40407983 : Blo 1166400 40407983 := bstep (se 1 (by rfl) ⟨30305987, by rfl⟩ : syracuseStep 40407983 = 60611975) B60611975
theorem B1168379 : Blo 1166400 1168379 := bstep (se 1 (by rfl) ⟨876284, by rfl⟩ : syracuseStep 1168379 = 1752569) B1752569
theorem B3740681 : Blo 1166400 3740681 := bstep (se 2 (by rfl) ⟨1402755, by rfl⟩ : syracuseStep 3740681 = 2805511) B2805511
theorem B3322919 : Blo 1166400 3322919 := bstep (se 1 (by rfl) ⟨2492189, by rfl⟩ : syracuseStep 3322919 = 4984379) B4984379
theorem B1750079 : Blo 1166400 1750079 := bstep (se 1 (by rfl) ⟨1312559, by rfl⟩ : syracuseStep 1750079 = 2625119) B2625119
theorem B2954303 : Blo 1166400 2954303 := bstep (se 1 (by rfl) ⟨2215727, by rfl⟩ : syracuseStep 2954303 = 4431455) B4431455
theorem B1971263 : Blo 1166400 1971263 := bstep (se 1 (by rfl) ⟨1478447, by rfl⟩ : syracuseStep 1971263 = 2956895) B2956895
theorem B1750121 : Blo 1166400 1750121 := bstep (se 2 (by rfl) ⟨656295, by rfl⟩ : syracuseStep 1750121 = 1312591) B1312591
theorem B2626667 : Blo 1166400 2626667 := bstep (se 1 (by rfl) ⟨1970000, by rfl⟩ : syracuseStep 2626667 = 3940001) B3940001
theorem B1750223 : Blo 1166400 1750223 := bstep (se 1 (by rfl) ⟨1312667, by rfl⟩ : syracuseStep 1750223 = 2625335) B2625335
theorem B38409427 : Blo 1166400 38409427 := bstep (se 1 (by rfl) ⟨28807070, by rfl⟩ : syracuseStep 38409427 = 57614141) B57614141
theorem B8410331 : Blo 1166400 8410331 := bstep (se 1 (by rfl) ⟨6307748, by rfl⟩ : syracuseStep 8410331 = 12615497) B12615497
theorem B2954515 : Blo 1166400 2954515 := bstep (se 1 (by rfl) ⟨2215886, by rfl⟩ : syracuseStep 2954515 = 4431773) B4431773
theorem B3323227 : Blo 1166400 3323227 := bstep (se 1 (by rfl) ⟨2492420, by rfl⟩ : syracuseStep 3323227 = 4984841) B4984841
theorem B2217307 : Blo 1166400 2217307 := bstep (se 1 (by rfl) ⟨1662980, by rfl⟩ : syracuseStep 2217307 = 3325961) B3325961
theorem B1750427 : Blo 1166400 1750427 := bstep (se 1 (by rfl) ⟨1312820, by rfl⟩ : syracuseStep 1750427 = 2625641) B2625641
theorem B1750649 : Blo 1166400 1750649 := bstep (se 2 (by rfl) ⟨656493, by rfl⟩ : syracuseStep 1750649 = 1312987) B1312987
theorem B2627243 : Blo 1166400 2627243 := bstep (se 1 (by rfl) ⟨1970432, by rfl⟩ : syracuseStep 2627243 = 3940865) B3940865
theorem B1750751 : Blo 1166400 1750751 := bstep (se 1 (by rfl) ⟨1313063, by rfl⟩ : syracuseStep 1750751 = 2626127) B2626127
theorem B3938111 : Blo 1166400 3938111 := bstep (se 1 (by rfl) ⟨2953583, by rfl⟩ : syracuseStep 3938111 = 5907167) B5907167
theorem B1750847 : Blo 1166400 1750847 := bstep (se 1 (by rfl) ⟨1313135, by rfl⟩ : syracuseStep 1750847 = 2626271) B2626271
theorem B4986839 : Blo 1166400 4986839 := bstep (se 1 (by rfl) ⟨3740129, by rfl⟩ : syracuseStep 4986839 = 7480259) B7480259
theorem B4429799 : Blo 1166400 4429799 := bstep (se 1 (by rfl) ⟨3322349, by rfl⟩ : syracuseStep 4429799 = 6644699) B6644699
theorem B1751015 : Blo 1166400 1751015 := bstep (se 1 (by rfl) ⟨1313261, by rfl⟩ : syracuseStep 1751015 = 2626523) B2626523
theorem B2627567 : Blo 1166400 2627567 := bstep (se 1 (by rfl) ⟨1970675, by rfl⟩ : syracuseStep 2627567 = 3941351) B3941351
theorem B1751033 : Blo 1166400 1751033 := bstep (se 2 (by rfl) ⟨656637, by rfl⟩ : syracuseStep 1751033 = 1313275) B1313275
theorem B14194769 : Blo 1166400 14194769 := bstep (se 2 (by rfl) ⟨5323038, by rfl⟩ : syracuseStep 14194769 = 10646077) B10646077
theorem B1751135 : Blo 1166400 1751135 := bstep (se 1 (by rfl) ⟨1313351, by rfl⟩ : syracuseStep 1751135 = 2626703) B2626703
theorem B1751195 : Blo 1166400 1751195 := bstep (se 1 (by rfl) ⟨1313396, by rfl⟩ : syracuseStep 1751195 = 2626793) B2626793
theorem B1751231 : Blo 1166400 1751231 := bstep (se 1 (by rfl) ⟨1313423, by rfl⟩ : syracuseStep 1751231 = 2626847) B2626847
theorem B4987079 : Blo 1166400 4987079 := bstep (se 1 (by rfl) ⟨3740309, by rfl⟩ : syracuseStep 4987079 = 7480619) B7480619
theorem B2627783 : Blo 1166400 2627783 := bstep (se 1 (by rfl) ⟨1970837, by rfl⟩ : syracuseStep 2627783 = 3941675) B3941675
theorem B1751273 : Blo 1166400 1751273 := bstep (se 2 (by rfl) ⟨656727, by rfl⟩ : syracuseStep 1751273 = 1313455) B1313455
theorem B2627963 : Blo 1166400 2627963 := bstep (se 1 (by rfl) ⟨1970972, by rfl⟩ : syracuseStep 2627963 = 3941945) B3941945
theorem B1751579 : Blo 1166400 1751579 := bstep (se 1 (by rfl) ⟨1313684, by rfl⟩ : syracuseStep 1751579 = 2627369) B2627369
theorem B1751657 : Blo 1166400 1751657 := bstep (se 2 (by rfl) ⟨656871, by rfl⟩ : syracuseStep 1751657 = 1313743) B1313743
theorem B2628233 : Blo 1166400 2628233 := bstep (se 2 (by rfl) ⟨985587, by rfl⟩ : syracuseStep 2628233 = 1971175) B1971175
theorem B2956115 : Blo 1166400 2956115 := bstep (se 1 (by rfl) ⟨2217086, by rfl⟩ : syracuseStep 2956115 = 4434173) B4434173
theorem B16833581 : Blo 1166400 16833581 := bstep (se 3 (by rfl) ⟨3156296, by rfl⟩ : syracuseStep 16833581 = 6312593) B6312593
theorem B1752185 : Blo 1166400 1752185 := bstep (se 2 (by rfl) ⟨657069, by rfl⟩ : syracuseStep 1752185 = 1314139) B1314139
theorem B2628791 : Blo 1166400 2628791 := bstep (se 1 (by rfl) ⟨1971593, by rfl⟩ : syracuseStep 2628791 = 3943187) B3943187
theorem B1752287 : Blo 1166400 1752287 := bstep (se 1 (by rfl) ⟨1314215, by rfl⟩ : syracuseStep 1752287 = 2628431) B2628431
theorem B1752329 : Blo 1166400 1752329 := bstep (se 2 (by rfl) ⟨657123, by rfl⟩ : syracuseStep 1752329 = 1314247) B1314247
theorem B3939623 : Blo 1166400 3939623 := bstep (se 1 (by rfl) ⟨2954717, by rfl⟩ : syracuseStep 3939623 = 5909435) B5909435
theorem B13286753 : Blo 1166400 13286753 := bstep (se 2 (by rfl) ⟨4982532, by rfl⟩ : syracuseStep 13286753 = 9965065) B9965065
theorem B1752431 : Blo 1166400 1752431 := bstep (se 1 (by rfl) ⟨1314323, by rfl⟩ : syracuseStep 1752431 = 2628647) B2628647
theorem B7585235 : Blo 1166400 7585235 := bstep (se 1 (by rfl) ⟨5688926, by rfl⟩ : syracuseStep 7585235 = 11377853) B11377853
theorem B1662439 : Blo 1166400 1662439 := bstep (se 1 (by rfl) ⟨1246829, by rfl⟩ : syracuseStep 1662439 = 2493659) B2493659
theorem B1752551 : Blo 1166400 1752551 := bstep (se 1 (by rfl) ⟨1314413, by rfl⟩ : syracuseStep 1752551 = 2628827) B2628827
theorem B3153487 : Blo 1166400 3153487 := bstep (se 1 (by rfl) ⟨2365115, by rfl⟩ : syracuseStep 3153487 = 4730231) B4730231
theorem B10657757 : Blo 1166400 10657757 := bstep (se 3 (by rfl) ⟨1998329, by rfl⟩ : syracuseStep 10657757 = 3996659) B3996659
theorem B8413307 : Blo 1166400 8413307 := bstep (se 1 (by rfl) ⟨6309980, by rfl⟩ : syracuseStep 8413307 = 12619961) B12619961
theorem B3940541 : Blo 1166400 3940541 := bstep (se 3 (by rfl) ⟨738851, by rfl⟩ : syracuseStep 3940541 = 1477703) B1477703
theorem B3326143 : Blo 1166400 3326143 := bstep (se 1 (by rfl) ⟨2494607, by rfl⟩ : syracuseStep 3326143 = 4989215) B4989215
theorem B3154135 : Blo 1166400 3154135 := bstep (se 1 (by rfl) ⟨2365601, by rfl⟩ : syracuseStep 3154135 = 4731203) B4731203
theorem B14188891 : Blo 1166400 14188891 := bstep (se 1 (by rfl) ⟨10641668, by rfl⟩ : syracuseStep 14188891 = 21283337) B21283337
theorem B3940703 : Blo 1166400 3940703 := bstep (se 1 (by rfl) ⟨2955527, by rfl⟩ : syracuseStep 3940703 = 5911055) B5911055
theorem B4989367 : Blo 1166400 4989367 := bstep (se 1 (by rfl) ⟨3742025, by rfl⟩ : syracuseStep 4989367 = 7484051) B7484051
theorem B18924029 : Blo 1166400 18924029 := bstep (se 3 (by rfl) ⟨3548255, by rfl⟩ : syracuseStep 18924029 = 7096511) B7096511
theorem B8413793 : Blo 1166400 8413793 := bstep (se 2 (by rfl) ⟨3155172, by rfl⟩ : syracuseStep 8413793 = 6310345) B6310345
theorem B1868393 : Blo 1166400 1868393 := bstep (se 2 (by rfl) ⟨700647, by rfl⟩ : syracuseStep 1868393 = 1401295) B1401295
theorem B11534969 : Blo 1166400 11534969 := bstep (se 2 (by rfl) ⟨4325613, by rfl⟩ : syracuseStep 11534969 = 8651227) B8651227
theorem B13288211 : Blo 1166400 13288211 := bstep (se 1 (by rfl) ⟨9966158, by rfl⟩ : syracuseStep 13288211 = 19932317) B19932317
theorem B35971897 : Blo 1166400 35971897 := bstep (se 2 (by rfl) ⟨13489461, by rfl⟩ : syracuseStep 35971897 = 26978923) B26978923
theorem B15983689 : Blo 1166400 15983689 := bstep (se 2 (by rfl) ⟨5993883, by rfl⟩ : syracuseStep 15983689 = 11987767) B11987767
theorem B20202601 : Blo 1166400 20202601 := bstep (se 2 (by rfl) ⟨7575975, by rfl⟩ : syracuseStep 20202601 = 15151951) B15151951
theorem B17974871 : Blo 1166400 17974871 := bstep (se 1 (by rfl) ⟨13481153, by rfl⟩ : syracuseStep 17974871 = 26962307) B26962307
theorem B1312447 : Blo 1166400 1312447 := bstep (se 1 (by rfl) ⟨984335, by rfl⟩ : syracuseStep 1312447 = 1968671) B1968671
theorem B55428907 : Blo 1166400 55428907 := bstep (se 1 (by rfl) ⟨41571680, by rfl⟩ : syracuseStep 55428907 = 83143361) B83143361
theorem B1247167 : Blo 1166400 1247167 := bstep (se 1 (by rfl) ⟨935375, by rfl⟩ : syracuseStep 1247167 = 1870751) B1870751
theorem B1312735 : Blo 1166400 1312735 := bstep (se 1 (by rfl) ⟨984551, by rfl⟩ : syracuseStep 1312735 = 1969103) B1969103
theorem B4204649 : Blo 1166400 4204649 := bstep (se 2 (by rfl) ⟨1576743, by rfl⟩ : syracuseStep 4204649 = 3153487) B3153487
theorem B21317843 : Blo 1166400 21317843 := bstep (se 1 (by rfl) ⟨15988382, by rfl⟩ : syracuseStep 21317843 = 31976765) B31976765
theorem B8857835 : Blo 1166400 8857835 := bstep (se 1 (by rfl) ⟨6643376, by rfl⟩ : syracuseStep 8857835 = 13286753) B13286753
theorem B9980171 : Blo 1166400 9980171 := bstep (se 1 (by rfl) ⟨7485128, by rfl⟩ : syracuseStep 9980171 = 14970257) B14970257
theorem B5056823 : Blo 1166400 5056823 := bstep (se 1 (by rfl) ⟨3792617, by rfl⟩ : syracuseStep 5056823 = 7585235) B7585235
theorem B22448461 : Blo 1166400 22448461 := bstep (se 3 (by rfl) ⟨4209086, by rfl⟩ : syracuseStep 22448461 = 8418173) B8418173
theorem B1313383 : Blo 1166400 1313383 := bstep (se 1 (by rfl) ⟨985037, by rfl⟩ : syracuseStep 1313383 = 1970075) B1970075
theorem B7105171 : Blo 1166400 7105171 := bstep (se 1 (by rfl) ⟨5328878, by rfl⟩ : syracuseStep 7105171 = 10657757) B10657757
theorem B9472787 : Blo 1166400 9472787 := bstep (se 1 (by rfl) ⟨7104590, by rfl⟩ : syracuseStep 9472787 = 14209181) B14209181
theorem B2214695 : Blo 1166400 2214695 := bstep (se 1 (by rfl) ⟨1661021, by rfl⟩ : syracuseStep 2214695 = 3322043) B3322043
theorem B2624507 : Blo 1166400 2624507 := bstep (se 1 (by rfl) ⟨1968380, by rfl⟩ : syracuseStep 2624507 = 3936761) B3936761
theorem B2624687 : Blo 1166400 2624687 := bstep (se 1 (by rfl) ⟨1968515, by rfl⟩ : syracuseStep 2624687 = 3937031) B3937031
theorem B1969339 : Blo 1166400 1969339 := bstep (se 1 (by rfl) ⟨1477004, by rfl⟩ : syracuseStep 1969339 = 2954009) B2954009
theorem B2624723 : Blo 1166400 2624723 := bstep (se 1 (by rfl) ⟨1968542, by rfl⟩ : syracuseStep 2624723 = 3937085) B3937085
theorem B7482617 : Blo 1166400 7482617 := bstep (se 2 (by rfl) ⟨2805981, by rfl⟩ : syracuseStep 7482617 = 5611963) B5611963
theorem B26938655 : Blo 1166400 26938655 := bstep (se 1 (by rfl) ⟨20203991, by rfl⟩ : syracuseStep 26938655 = 40407983) B40407983
theorem B2215279 : Blo 1166400 2215279 := bstep (se 1 (by rfl) ⟨1661459, by rfl⟩ : syracuseStep 2215279 = 3322919) B3322919
theorem B1166719 : Blo 1166400 1166719 := bstep (se 1 (by rfl) ⟨875039, by rfl⟩ : syracuseStep 1166719 = 1750079) B1750079
theorem B1969535 : Blo 1166400 1969535 := bstep (se 1 (by rfl) ⟨1477151, by rfl⟩ : syracuseStep 1969535 = 2954303) B2954303
theorem B1314175 : Blo 1166400 1314175 := bstep (se 1 (by rfl) ⟨985631, by rfl⟩ : syracuseStep 1314175 = 1971263) B1971263
theorem B1166747 : Blo 1166400 1166747 := bstep (se 1 (by rfl) ⟨875060, by rfl⟩ : syracuseStep 1166747 = 1750121) B1750121
theorem B1166815 : Blo 1166400 1166815 := bstep (se 1 (by rfl) ⟨875111, by rfl⟩ : syracuseStep 1166815 = 1750223) B1750223
theorem B2624993 : Blo 1166400 2624993 := bstep (se 2 (by rfl) ⟨984372, by rfl⟩ : syracuseStep 2624993 = 1968745) B1968745
theorem B1166951 : Blo 1166400 1166951 := bstep (se 1 (by rfl) ⟨875213, by rfl⟩ : syracuseStep 1166951 = 1750427) B1750427
theorem B22441697 : Blo 1166400 22441697 := bstep (se 2 (by rfl) ⟨8415636, by rfl⟩ : syracuseStep 22441697 = 16831273) B16831273
theorem B21589753 : Blo 1166400 21589753 := bstep (se 2 (by rfl) ⟨8096157, by rfl⟩ : syracuseStep 21589753 = 16192315) B16192315
theorem B1167099 : Blo 1166400 1167099 := bstep (se 1 (by rfl) ⟨875324, by rfl⟩ : syracuseStep 1167099 = 1750649) B1750649
theorem B1167167 : Blo 1166400 1167167 := bstep (se 1 (by rfl) ⟨875375, by rfl⟩ : syracuseStep 1167167 = 1750751) B1750751
theorem B2625407 : Blo 1166400 2625407 := bstep (se 1 (by rfl) ⟨1969055, by rfl⟩ : syracuseStep 2625407 = 3938111) B3938111
theorem B1167231 : Blo 1166400 1167231 := bstep (se 1 (by rfl) ⟨875423, by rfl⟩ : syracuseStep 1167231 = 1750847) B1750847
theorem B2953199 : Blo 1166400 2953199 := bstep (se 1 (by rfl) ⟨2214899, by rfl⟩ : syracuseStep 2953199 = 4429799) B4429799
theorem B1167343 : Blo 1166400 1167343 := bstep (se 1 (by rfl) ⟨875507, by rfl⟩ : syracuseStep 1167343 = 1751015) B1751015
theorem B1167355 : Blo 1166400 1167355 := bstep (se 1 (by rfl) ⟨875516, by rfl⟩ : syracuseStep 1167355 = 1751033) B1751033
theorem B1167423 : Blo 1166400 1167423 := bstep (se 1 (by rfl) ⟨875567, by rfl⟩ : syracuseStep 1167423 = 1751135) B1751135
theorem B1167463 : Blo 1166400 1167463 := bstep (se 1 (by rfl) ⟨875597, by rfl⟩ : syracuseStep 1167463 = 1751195) B1751195
theorem B2879615 : Blo 1166400 2879615 := bstep (se 1 (by rfl) ⟨2159711, by rfl⟩ : syracuseStep 2879615 = 4319423) B4319423
theorem B1167487 : Blo 1166400 1167487 := bstep (se 1 (by rfl) ⟨875615, by rfl⟩ : syracuseStep 1167487 = 1751231) B1751231
theorem B1167515 : Blo 1166400 1167515 := bstep (se 1 (by rfl) ⟨875636, by rfl⟩ : syracuseStep 1167515 = 1751273) B1751273
theorem B4984993 : Blo 1166400 4984993 := bstep (se 2 (by rfl) ⟨1869372, by rfl⟩ : syracuseStep 4984993 = 3738745) B3738745
theorem B51212569 : Blo 1166400 51212569 := bstep (se 2 (by rfl) ⟨19204713, by rfl⟩ : syracuseStep 51212569 = 38409427) B38409427
theorem B1970473 : Blo 1166400 1970473 := bstep (se 2 (by rfl) ⟨738927, by rfl⟩ : syracuseStep 1970473 = 1477855) B1477855
theorem B1167719 : Blo 1166400 1167719 := bstep (se 1 (by rfl) ⟨875789, by rfl⟩ : syracuseStep 1167719 = 1751579) B1751579
theorem B1167771 : Blo 1166400 1167771 := bstep (se 1 (by rfl) ⟨875828, by rfl⟩ : syracuseStep 1167771 = 1751657) B1751657
theorem B7475645 : Blo 1166400 7475645 := bstep (se 3 (by rfl) ⟨1401683, by rfl⟩ : syracuseStep 7475645 = 2803367) B2803367
theorem B1970743 : Blo 1166400 1970743 := bstep (se 1 (by rfl) ⟨1478057, by rfl⟩ : syracuseStep 1970743 = 2956115) B2956115
theorem B2216585 : Blo 1166400 2216585 := bstep (se 2 (by rfl) ⟨831219, by rfl⟩ : syracuseStep 2216585 = 1662439) B1662439
theorem B1749755 : Blo 1166400 1749755 := bstep (se 1 (by rfl) ⟨1312316, by rfl⟩ : syracuseStep 1749755 = 2624633) B2624633
theorem B1168123 : Blo 1166400 1168123 := bstep (se 1 (by rfl) ⟨876092, by rfl⟩ : syracuseStep 1168123 = 1752185) B1752185
theorem B2626361 : Blo 1166400 2626361 := bstep (se 2 (by rfl) ⟨984885, by rfl⟩ : syracuseStep 2626361 = 1969771) B1969771
theorem B1168191 : Blo 1166400 1168191 := bstep (se 1 (by rfl) ⟨876143, by rfl⟩ : syracuseStep 1168191 = 1752287) B1752287
theorem B1168219 : Blo 1166400 1168219 := bstep (se 1 (by rfl) ⟨876164, by rfl⟩ : syracuseStep 1168219 = 1752329) B1752329
theorem B2626415 : Blo 1166400 2626415 := bstep (se 1 (by rfl) ⟨1969811, by rfl⟩ : syracuseStep 2626415 = 3939623) B3939623
theorem B1168287 : Blo 1166400 1168287 := bstep (se 1 (by rfl) ⟨876215, by rfl⟩ : syracuseStep 1168287 = 1752431) B1752431
theorem B1168367 : Blo 1166400 1168367 := bstep (se 1 (by rfl) ⟨876275, by rfl⟩ : syracuseStep 1168367 = 1752551) B1752551
theorem B2626721 : Blo 1166400 2626721 := bstep (se 2 (by rfl) ⟨985020, by rfl⟩ : syracuseStep 2626721 = 1970041) B1970041
theorem B1750199 : Blo 1166400 1750199 := bstep (se 1 (by rfl) ⟨1312649, by rfl⟩ : syracuseStep 1750199 = 2625299) B2625299
theorem B9975149 : Blo 1166400 9975149 := bstep (se 3 (by rfl) ⟨1870340, by rfl⟩ : syracuseStep 9975149 = 3740681) B3740681
theorem B4494703 : Blo 1166400 4494703 := bstep (se 1 (by rfl) ⟨3371027, by rfl⟩ : syracuseStep 4494703 = 6742055) B6742055
theorem B1750439 : Blo 1166400 1750439 := bstep (se 1 (by rfl) ⟨1312829, by rfl⟩ : syracuseStep 1750439 = 2625659) B2625659
theorem B2626991 : Blo 1166400 2626991 := bstep (se 1 (by rfl) ⟨1970243, by rfl⟩ : syracuseStep 2626991 = 3940487) B3940487
theorem B3741103 : Blo 1166400 3741103 := bstep (se 1 (by rfl) ⟨2805827, by rfl⟩ : syracuseStep 3741103 = 5611655) B5611655
theorem B4429313 : Blo 1166400 4429313 := bstep (se 2 (by rfl) ⟨1660992, by rfl⟩ : syracuseStep 4429313 = 3321985) B3321985
theorem B7099919 : Blo 1166400 7099919 := bstep (se 1 (by rfl) ⟨5324939, by rfl⟩ : syracuseStep 7099919 = 10649879) B10649879
theorem B37852717 : Blo 1166400 37852717 := bstep (se 3 (by rfl) ⟨7097384, by rfl⟩ : syracuseStep 37852717 = 14194769) B14194769
theorem B1750619 : Blo 1166400 1750619 := bstep (se 1 (by rfl) ⟨1312964, by rfl⟩ : syracuseStep 1750619 = 2625929) B2625929
theorem B2365147 : Blo 1166400 2365147 := bstep (se 1 (by rfl) ⟨1773860, by rfl⟩ : syracuseStep 2365147 = 3547721) B3547721
theorem B2103131 : Blo 1166400 2103131 := bstep (se 1 (by rfl) ⟨1577348, by rfl⟩ : syracuseStep 2103131 = 3154697) B3154697
theorem B22427549 : Blo 1166400 22427549 := bstep (se 3 (by rfl) ⟨4205165, by rfl⟩ : syracuseStep 22427549 = 8410331) B8410331
theorem B1751081 : Blo 1166400 1751081 := bstep (se 2 (by rfl) ⟨656655, by rfl⟩ : syracuseStep 1751081 = 1313311) B1313311
theorem B1751111 : Blo 1166400 1751111 := bstep (se 1 (by rfl) ⟨1313333, by rfl⟩ : syracuseStep 1751111 = 2626667) B2626667
theorem B16832609 : Blo 1166400 16832609 := bstep (se 2 (by rfl) ⟨6312228, by rfl⟩ : syracuseStep 16832609 = 12624457) B12624457
theorem B2627999 : Blo 1166400 2627999 := bstep (se 1 (by rfl) ⟨1970999, by rfl⟩ : syracuseStep 2627999 = 3941999) B3941999
theorem B1751495 : Blo 1166400 1751495 := bstep (se 1 (by rfl) ⟨1313621, by rfl⟩ : syracuseStep 1751495 = 2627243) B2627243
theorem B18930125 : Blo 1166400 18930125 := bstep (se 3 (by rfl) ⟨3549398, by rfl⟩ : syracuseStep 18930125 = 7098797) B7098797
theorem B13294043 : Blo 1166400 13294043 := bstep (se 1 (by rfl) ⟨9970532, by rfl⟩ : syracuseStep 13294043 = 19941065) B19941065
theorem B2628071 : Blo 1166400 2628071 := bstep (se 1 (by rfl) ⟨1971053, by rfl⟩ : syracuseStep 2628071 = 3942107) B3942107
theorem B8870471 : Blo 1166400 8870471 := bstep (se 1 (by rfl) ⟨6652853, by rfl⟩ : syracuseStep 8870471 = 13305707) B13305707
theorem B3324559 : Blo 1166400 3324559 := bstep (se 1 (by rfl) ⟨2493419, by rfl⟩ : syracuseStep 3324559 = 4986839) B4986839
theorem B1751711 : Blo 1166400 1751711 := bstep (se 1 (by rfl) ⟨1313783, by rfl⟩ : syracuseStep 1751711 = 2627567) B2627567
theorem B3939083 : Blo 1166400 3939083 := bstep (se 1 (by rfl) ⟨2954312, by rfl⟩ : syracuseStep 3939083 = 5908625) B5908625
theorem B3324719 : Blo 1166400 3324719 := bstep (se 1 (by rfl) ⟨2493539, by rfl⟩ : syracuseStep 3324719 = 4987079) B4987079
theorem B1751855 : Blo 1166400 1751855 := bstep (se 1 (by rfl) ⟨1313891, by rfl⟩ : syracuseStep 1751855 = 2627783) B2627783
theorem B1751975 : Blo 1166400 1751975 := bstep (se 1 (by rfl) ⟨1313981, by rfl⟩ : syracuseStep 1751975 = 2627963) B2627963
theorem B3939353 : Blo 1166400 3939353 := bstep (se 2 (by rfl) ⟨1477257, by rfl⟩ : syracuseStep 3939353 = 2954515) B2954515
theorem B1752155 : Blo 1166400 1752155 := bstep (se 1 (by rfl) ⟨1314116, by rfl⟩ : syracuseStep 1752155 = 2628233) B2628233
theorem B4430969 : Blo 1166400 4430969 := bstep (se 2 (by rfl) ⟨1661613, by rfl⟩ : syracuseStep 4430969 = 3323227) B3323227
theorem B2956409 : Blo 1166400 2956409 := bstep (se 2 (by rfl) ⟨1108653, by rfl⟩ : syracuseStep 2956409 = 2217307) B2217307
theorem B4430983 : Blo 1166400 4430983 := bstep (se 1 (by rfl) ⟨3323237, by rfl⟩ : syracuseStep 4430983 = 6646475) B6646475
theorem B2661703 : Blo 1166400 2661703 := bstep (se 1 (by rfl) ⟨1996277, by rfl⟩ : syracuseStep 2661703 = 3992555) B3992555
theorem B11222387 : Blo 1166400 11222387 := bstep (se 1 (by rfl) ⟨8416790, by rfl⟩ : syracuseStep 11222387 = 16833581) B16833581
theorem B1752527 : Blo 1166400 1752527 := bstep (se 1 (by rfl) ⟨1314395, by rfl⟩ : syracuseStep 1752527 = 2628791) B2628791
theorem B12616019 : Blo 1166400 12616019 := bstep (se 1 (by rfl) ⟨9462014, by rfl⟩ : syracuseStep 12616019 = 18924029) B18924029
theorem B6652489 : Blo 1166400 6652489 := bstep (se 2 (by rfl) ⟨2494683, by rfl⟩ : syracuseStep 6652489 = 4989367) B4989367
theorem B4432745 : Blo 1166400 4432745 := bstep (se 2 (by rfl) ⟨1662279, by rfl⟩ : syracuseStep 4432745 = 3324559) B3324559
theorem B50480333 : Blo 1166400 50480333 := bstep (se 3 (by rfl) ⟨9465062, by rfl⟩ : syracuseStep 50480333 = 18930125) B18930125
theorem B14951699 : Blo 1166400 14951699 := bstep (se 1 (by rfl) ⟨11213774, by rfl⟩ : syracuseStep 14951699 = 22427549) B22427549
theorem B2803099 : Blo 1166400 2803099 := bstep (se 1 (by rfl) ⟨2102324, by rfl⟩ : syracuseStep 2803099 = 4204649) B4204649
theorem B26936801 : Blo 1166400 26936801 := bstep (se 2 (by rfl) ⟨10101300, by rfl⟩ : syracuseStep 26936801 = 20202601) B20202601
theorem B6653447 : Blo 1166400 6653447 := bstep (se 1 (by rfl) ⟨4990085, by rfl⟩ : syracuseStep 6653447 = 9980171) B9980171
theorem B5907977 : Blo 1166400 5907977 := bstep (se 2 (by rfl) ⟨2215491, by rfl⟩ : syracuseStep 5907977 = 4430983) B4430983
theorem B4982381 : Blo 1166400 4982381 := bstep (se 3 (by rfl) ⟨934196, by rfl⟩ : syracuseStep 4982381 = 1868393) B1868393
theorem B1476463 : Blo 1166400 1476463 := bstep (se 1 (by rfl) ⟨1107347, by rfl⟩ : syracuseStep 1476463 = 2214695) B2214695
theorem B17959103 : Blo 1166400 17959103 := bstep (se 1 (by rfl) ⟨13469327, by rfl⟩ : syracuseStep 17959103 = 26938655) B26938655
theorem B7481591 : Blo 1166400 7481591 := bstep (se 1 (by rfl) ⟨5611193, by rfl⟩ : syracuseStep 7481591 = 11222387) B11222387
theorem B1313023 : Blo 1166400 1313023 := bstep (se 1 (by rfl) ⟨984767, by rfl⟩ : syracuseStep 1313023 = 1969535) B1969535
theorem B14961131 : Blo 1166400 14961131 := bstep (se 1 (by rfl) ⟨11220848, by rfl⟩ : syracuseStep 14961131 = 22441697) B22441697
theorem B1968799 : Blo 1166400 1968799 := bstep (se 1 (by rfl) ⟨1476599, by rfl⟩ : syracuseStep 1968799 = 2953199) B2953199
theorem B6646657 : Blo 1166400 6646657 := bstep (se 2 (by rfl) ⟨2492496, by rfl⟩ : syracuseStep 6646657 = 4984993) B4984993
theorem B4434857 : Blo 1166400 4434857 := bstep (se 2 (by rfl) ⟨1663071, by rfl⟩ : syracuseStep 4434857 = 3326143) B3326143
theorem B4205513 : Blo 1166400 4205513 := bstep (se 2 (by rfl) ⟨1577067, by rfl⟩ : syracuseStep 4205513 = 3154135) B3154135
theorem B4983763 : Blo 1166400 4983763 := bstep (se 1 (by rfl) ⟨3737822, by rfl⟩ : syracuseStep 4983763 = 7475645) B7475645
theorem B7678973 : Blo 1166400 7678973 := bstep (se 3 (by rfl) ⟨1439807, by rfl⟩ : syracuseStep 7678973 = 2879615) B2879615
theorem B68283425 : Blo 1166400 68283425 := bstep (se 2 (by rfl) ⟨25606284, by rfl⟩ : syracuseStep 68283425 = 51212569) B51212569
theorem B18918521 : Blo 1166400 18918521 := bstep (se 2 (by rfl) ⟨7094445, by rfl⟩ : syracuseStep 18918521 = 14188891) B14188891
theorem B1166503 : Blo 1166400 1166503 := bstep (se 1 (by rfl) ⟨874877, by rfl⟩ : syracuseStep 1166503 = 1749755) B1749755
theorem B8858807 : Blo 1166400 8858807 := bstep (se 1 (by rfl) ⟨6644105, by rfl⟩ : syracuseStep 8858807 = 13288211) B13288211
theorem B56847581 : Blo 1166400 56847581 := bstep (se 3 (by rfl) ⟨10658921, by rfl⟩ : syracuseStep 56847581 = 21317843) B21317843
theorem B1166799 : Blo 1166400 1166799 := bstep (se 1 (by rfl) ⟨875099, by rfl⟩ : syracuseStep 1166799 = 1750199) B1750199
theorem B9473561 : Blo 1166400 9473561 := bstep (se 2 (by rfl) ⟨3552585, by rfl⟩ : syracuseStep 9473561 = 7105171) B7105171
theorem B1166959 : Blo 1166400 1166959 := bstep (se 1 (by rfl) ⟨875219, by rfl⟩ : syracuseStep 1166959 = 1750439) B1750439
theorem B2952875 : Blo 1166400 2952875 := bstep (se 1 (by rfl) ⟨2214656, by rfl⟩ : syracuseStep 2952875 = 4429313) B4429313
theorem B1167079 : Blo 1166400 1167079 := bstep (se 1 (by rfl) ⟨875309, by rfl⟩ : syracuseStep 1167079 = 1750619) B1750619
theorem B1167387 : Blo 1166400 1167387 := bstep (se 1 (by rfl) ⟨875540, by rfl⟩ : syracuseStep 1167387 = 1751081) B1751081
theorem B1167407 : Blo 1166400 1167407 := bstep (se 1 (by rfl) ⟨875555, by rfl⟩ : syracuseStep 1167407 = 1751111) B1751111
theorem B21311585 : Blo 1166400 21311585 := bstep (se 2 (by rfl) ⟨7991844, by rfl⟩ : syracuseStep 21311585 = 15983689) B15983689
theorem B3371215 : Blo 1166400 3371215 := bstep (se 1 (by rfl) ⟨2528411, by rfl⟩ : syracuseStep 3371215 = 5056823) B5056823
theorem B2625785 : Blo 1166400 2625785 := bstep (se 2 (by rfl) ⟨984669, by rfl⟩ : syracuseStep 2625785 = 1969339) B1969339
theorem B1167663 : Blo 1166400 1167663 := bstep (se 1 (by rfl) ⟨875747, by rfl⟩ : syracuseStep 1167663 = 1751495) B1751495
theorem B5910893 : Blo 1166400 5910893 := bstep (se 3 (by rfl) ⟨1108292, by rfl⟩ : syracuseStep 5910893 = 2216585) B2216585
theorem B1167807 : Blo 1166400 1167807 := bstep (se 1 (by rfl) ⟨875855, by rfl⟩ : syracuseStep 1167807 = 1751711) B1751711
theorem B2953705 : Blo 1166400 2953705 := bstep (se 2 (by rfl) ⟨1107639, by rfl⟩ : syracuseStep 2953705 = 2215279) B2215279
theorem B5992937 : Blo 1166400 5992937 := bstep (se 2 (by rfl) ⟨2247351, by rfl⟩ : syracuseStep 5992937 = 4494703) B4494703
theorem B2626055 : Blo 1166400 2626055 := bstep (se 1 (by rfl) ⟨1969541, by rfl⟩ : syracuseStep 2626055 = 3939083) B3939083
theorem B2216479 : Blo 1166400 2216479 := bstep (se 1 (by rfl) ⟨1662359, by rfl⟩ : syracuseStep 2216479 = 3324719) B3324719
theorem B1167903 : Blo 1166400 1167903 := bstep (se 1 (by rfl) ⟨875927, by rfl⟩ : syracuseStep 1167903 = 1751855) B1751855
theorem B1167983 : Blo 1166400 1167983 := bstep (se 1 (by rfl) ⟨875987, by rfl⟩ : syracuseStep 1167983 = 1751975) B1751975
theorem B1749671 : Blo 1166400 1749671 := bstep (se 1 (by rfl) ⟨1312253, by rfl⟩ : syracuseStep 1749671 = 2624507) B2624507
theorem B2626235 : Blo 1166400 2626235 := bstep (se 1 (by rfl) ⟨1969676, by rfl⟩ : syracuseStep 2626235 = 3939353) B3939353
theorem B1168103 : Blo 1166400 1168103 := bstep (se 1 (by rfl) ⟨876077, by rfl⟩ : syracuseStep 1168103 = 1752155) B1752155
theorem B2953979 : Blo 1166400 2953979 := bstep (se 1 (by rfl) ⟨2215484, by rfl⟩ : syracuseStep 2953979 = 4430969) B4430969
theorem B1970939 : Blo 1166400 1970939 := bstep (se 1 (by rfl) ⟨1478204, by rfl⟩ : syracuseStep 1970939 = 2956409) B2956409
theorem B1749791 : Blo 1166400 1749791 := bstep (se 1 (by rfl) ⟨1312343, by rfl⟩ : syracuseStep 1749791 = 2624687) B2624687
theorem B1749815 : Blo 1166400 1749815 := bstep (se 1 (by rfl) ⟨1312361, by rfl⟩ : syracuseStep 1749815 = 2624723) B2624723
theorem B5608349 : Blo 1166400 5608349 := bstep (se 3 (by rfl) ⟨1051565, by rfl⟩ : syracuseStep 5608349 = 2103131) B2103131
theorem B1749929 : Blo 1166400 1749929 := bstep (se 2 (by rfl) ⟨656223, by rfl⟩ : syracuseStep 1749929 = 1312447) B1312447
theorem B1168351 : Blo 1166400 1168351 := bstep (se 1 (by rfl) ⟨876263, by rfl⟩ : syracuseStep 1168351 = 1752527) B1752527
theorem B1749995 : Blo 1166400 1749995 := bstep (se 1 (by rfl) ⟨1312496, by rfl⟩ : syracuseStep 1749995 = 2624993) B2624993
theorem B73905209 : Blo 1166400 73905209 := bstep (se 2 (by rfl) ⟨27714453, by rfl⟩ : syracuseStep 73905209 = 55428907) B55428907
theorem B1750271 : Blo 1166400 1750271 := bstep (se 1 (by rfl) ⟨1312703, by rfl⟩ : syracuseStep 1750271 = 2625407) B2625407
theorem B1750313 : Blo 1166400 1750313 := bstep (se 2 (by rfl) ⟨656367, by rfl⟩ : syracuseStep 1750313 = 1312735) B1312735
theorem B5608871 : Blo 1166400 5608871 := bstep (se 1 (by rfl) ⟨4206653, by rfl⟩ : syracuseStep 5608871 = 8413307) B8413307
theorem B2627027 : Blo 1166400 2627027 := bstep (se 1 (by rfl) ⟨1970270, by rfl⟩ : syracuseStep 2627027 = 3940541) B3940541
theorem B2627135 : Blo 1166400 2627135 := bstep (se 1 (by rfl) ⟨1970351, by rfl⟩ : syracuseStep 2627135 = 3940703) B3940703
theorem B2627297 : Blo 1166400 2627297 := bstep (se 2 (by rfl) ⟨985236, by rfl⟩ : syracuseStep 2627297 = 1970473) B1970473
theorem B5609195 : Blo 1166400 5609195 := bstep (se 1 (by rfl) ⟨4206896, by rfl⟩ : syracuseStep 5609195 = 8413793) B8413793
theorem B7689979 : Blo 1166400 7689979 := bstep (se 1 (by rfl) ⟨5767484, by rfl⟩ : syracuseStep 7689979 = 11534969) B11534969
theorem B29931281 : Blo 1166400 29931281 := bstep (se 2 (by rfl) ⟨11224230, by rfl⟩ : syracuseStep 29931281 = 22448461) B22448461
theorem B1750907 : Blo 1166400 1750907 := bstep (se 1 (by rfl) ⟨1313180, by rfl⟩ : syracuseStep 1750907 = 2626361) B2626361
theorem B1750943 : Blo 1166400 1750943 := bstep (se 1 (by rfl) ⟨1313207, by rfl⟩ : syracuseStep 1750943 = 2626415) B2626415
theorem B2627657 : Blo 1166400 2627657 := bstep (se 2 (by rfl) ⟨985371, by rfl⟩ : syracuseStep 2627657 = 1970743) B1970743
theorem B1751147 : Blo 1166400 1751147 := bstep (se 1 (by rfl) ⟨1313360, by rfl⟩ : syracuseStep 1751147 = 2626721) B2626721
theorem B1751177 : Blo 1166400 1751177 := bstep (se 2 (by rfl) ⟨656691, by rfl⟩ : syracuseStep 1751177 = 1313383) B1313383
theorem B6650099 : Blo 1166400 6650099 := bstep (se 1 (by rfl) ⟨4987574, by rfl⟩ : syracuseStep 6650099 = 9975149) B9975149
theorem B1751327 : Blo 1166400 1751327 := bstep (se 1 (by rfl) ⟨1313495, by rfl⟩ : syracuseStep 1751327 = 2626991) B2626991
theorem B4733279 : Blo 1166400 4733279 := bstep (se 1 (by rfl) ⟨3549959, by rfl⟩ : syracuseStep 4733279 = 7099919) B7099919
theorem B11983247 : Blo 1166400 11983247 := bstep (se 1 (by rfl) ⟨8987435, by rfl⟩ : syracuseStep 11983247 = 17974871) B17974871
theorem B47962529 : Blo 1166400 47962529 := bstep (se 2 (by rfl) ⟨17985948, by rfl⟩ : syracuseStep 47962529 = 35971897) B35971897
theorem B11221739 : Blo 1166400 11221739 := bstep (se 1 (by rfl) ⟨8416304, by rfl⟩ : syracuseStep 11221739 = 16832609) B16832609
theorem B5905223 : Blo 1166400 5905223 := bstep (se 1 (by rfl) ⟨4428917, by rfl⟩ : syracuseStep 5905223 = 8857835) B8857835
theorem B1751999 : Blo 1166400 1751999 := bstep (se 1 (by rfl) ⟨1313999, by rfl⟩ : syracuseStep 1751999 = 2627999) B2627999
theorem B8862695 : Blo 1166400 8862695 := bstep (se 1 (by rfl) ⟨6647021, by rfl⟩ : syracuseStep 8862695 = 13294043) B13294043
theorem B1752047 : Blo 1166400 1752047 := bstep (se 1 (by rfl) ⟨1314035, by rfl⟩ : syracuseStep 1752047 = 2628071) B2628071
theorem B14195749 : Blo 1166400 14195749 := bstep (se 4 (by rfl) ⟨1330851, by rfl⟩ : syracuseStep 14195749 = 2661703) B2661703
theorem B5913647 : Blo 1166400 5913647 := bstep (se 1 (by rfl) ⟨4435235, by rfl⟩ : syracuseStep 5913647 = 8870471) B8870471
theorem B1752233 : Blo 1166400 1752233 := bstep (se 2 (by rfl) ⟨657087, by rfl⟩ : syracuseStep 1752233 = 1314175) B1314175
theorem B6315191 : Blo 1166400 6315191 := bstep (se 1 (by rfl) ⟨4736393, by rfl⟩ : syracuseStep 6315191 = 9472787) B9472787
theorem B4988137 : Blo 1166400 4988137 := bstep (se 2 (by rfl) ⟨1870551, by rfl⟩ : syracuseStep 4988137 = 3741103) B3741103
theorem B50470289 : Blo 1166400 50470289 := bstep (se 2 (by rfl) ⟨18926358, by rfl⟩ : syracuseStep 50470289 = 37852717) B37852717
theorem B4988411 : Blo 1166400 4988411 := bstep (se 1 (by rfl) ⟨3741308, by rfl⟩ : syracuseStep 4988411 = 7482617) B7482617
theorem B3153529 : Blo 1166400 3153529 := bstep (se 2 (by rfl) ⟨1182573, by rfl⟩ : syracuseStep 3153529 = 2365147) B2365147
theorem B28786337 : Blo 1166400 28786337 := bstep (se 2 (by rfl) ⟨10794876, by rfl⟩ : syracuseStep 28786337 = 21589753) B21589753
theorem B6651557 : Blo 1166400 6651557 := bstep (se 4 (by rfl) ⟨623583, by rfl⟩ : syracuseStep 6651557 = 1247167) B1247167
theorem B3940595 : Blo 1166400 3940595 := bstep (se 1 (by rfl) ⟨2955446, by rfl⟩ : syracuseStep 3940595 = 5910893) B5910893
theorem B33653555 : Blo 1166400 33653555 := bstep (se 1 (by rfl) ⟨25240166, by rfl⟩ : syracuseStep 33653555 = 50480333) B50480333
theorem B17957867 : Blo 1166400 17957867 := bstep (se 1 (by rfl) ⟨13468400, by rfl⟩ : syracuseStep 17957867 = 26936801) B26936801
theorem B6645017 : Blo 1166400 6645017 := bstep (se 2 (by rfl) ⟨2491881, by rfl⟩ : syracuseStep 6645017 = 4983763) B4983763
theorem B4433399 : Blo 1166400 4433399 := bstep (se 1 (by rfl) ⟨3325049, by rfl⟩ : syracuseStep 4433399 = 6650099) B6650099
theorem B3155519 : Blo 1166400 3155519 := bstep (se 1 (by rfl) ⟨2366639, by rfl⟩ : syracuseStep 3155519 = 4733279) B4733279
theorem B7988831 : Blo 1166400 7988831 := bstep (se 1 (by rfl) ⟨5991623, by rfl⟩ : syracuseStep 7988831 = 11983247) B11983247
theorem B31975019 : Blo 1166400 31975019 := bstep (se 1 (by rfl) ⟨23981264, by rfl⟩ : syracuseStep 31975019 = 47962529) B47962529
theorem B7481159 : Blo 1166400 7481159 := bstep (se 1 (by rfl) ⟨5610869, by rfl⟩ : syracuseStep 7481159 = 11221739) B11221739
theorem B3737465 : Blo 1166400 3737465 := bstep (se 2 (by rfl) ⟨1401549, by rfl⟩ : syracuseStep 3737465 = 2803099) B2803099
theorem B2803675 : Blo 1166400 2803675 := bstep (se 1 (by rfl) ⟨2102756, by rfl⟩ : syracuseStep 2803675 = 4205513) B4205513
theorem B5908463 : Blo 1166400 5908463 := bstep (se 1 (by rfl) ⟨4431347, by rfl⟩ : syracuseStep 5908463 = 8862695) B8862695
theorem B3942431 : Blo 1166400 3942431 := bstep (se 1 (by rfl) ⟨2956823, by rfl⟩ : syracuseStep 3942431 = 5913647) B5913647
theorem B37898387 : Blo 1166400 37898387 := bstep (se 1 (by rfl) ⟨28423790, by rfl⟩ : syracuseStep 37898387 = 56847581) B56847581
theorem B4204705 : Blo 1166400 4204705 := bstep (se 2 (by rfl) ⟨1576764, by rfl⟩ : syracuseStep 4204705 = 3153529) B3153529
theorem B33646859 : Blo 1166400 33646859 := bstep (se 1 (by rfl) ⟨25235144, by rfl⟩ : syracuseStep 33646859 = 50470289) B50470289
theorem B4434371 : Blo 1166400 4434371 := bstep (se 1 (by rfl) ⟨3325778, by rfl⟩ : syracuseStep 4434371 = 6651557) B6651557
theorem B1968583 : Blo 1166400 1968583 := bstep (se 1 (by rfl) ⟨1476437, by rfl⟩ : syracuseStep 1968583 = 2952875) B2952875
theorem B1968617 : Blo 1166400 1968617 := bstep (se 2 (by rfl) ⟨738231, by rfl⟩ : syracuseStep 1968617 = 1476463) B1476463
theorem B14207723 : Blo 1166400 14207723 := bstep (se 1 (by rfl) ⟨10655792, by rfl⟩ : syracuseStep 14207723 = 21311585) B21311585
theorem B1166447 : Blo 1166400 1166447 := bstep (se 1 (by rfl) ⟨874835, by rfl⟩ : syracuseStep 1166447 = 1749671) B1749671
theorem B1969319 : Blo 1166400 1969319 := bstep (se 1 (by rfl) ⟨1476989, by rfl⟩ : syracuseStep 1969319 = 2953979) B2953979
theorem B1313959 : Blo 1166400 1313959 := bstep (se 1 (by rfl) ⟨985469, by rfl⟩ : syracuseStep 1313959 = 1970939) B1970939
theorem B1166527 : Blo 1166400 1166527 := bstep (se 1 (by rfl) ⟨874895, by rfl⟩ : syracuseStep 1166527 = 1749791) B1749791
theorem B1166543 : Blo 1166400 1166543 := bstep (se 1 (by rfl) ⟨874907, by rfl⟩ : syracuseStep 1166543 = 1749815) B1749815
theorem B3738899 : Blo 1166400 3738899 := bstep (se 1 (by rfl) ⟨2804174, by rfl⟩ : syracuseStep 3738899 = 5608349) B5608349
theorem B1166619 : Blo 1166400 1166619 := bstep (se 1 (by rfl) ⟨874964, by rfl⟩ : syracuseStep 1166619 = 1749929) B1749929
theorem B1166663 : Blo 1166400 1166663 := bstep (se 1 (by rfl) ⟨874997, by rfl⟩ : syracuseStep 1166663 = 1749995) B1749995
theorem B49270139 : Blo 1166400 49270139 := bstep (se 1 (by rfl) ⟨36952604, by rfl⟩ : syracuseStep 49270139 = 73905209) B73905209
theorem B1166847 : Blo 1166400 1166847 := bstep (se 1 (by rfl) ⟨875135, by rfl⟩ : syracuseStep 1166847 = 1750271) B1750271
theorem B1166875 : Blo 1166400 1166875 := bstep (se 1 (by rfl) ⟨875156, by rfl⟩ : syracuseStep 1166875 = 1750313) B1750313
theorem B2625065 : Blo 1166400 2625065 := bstep (se 2 (by rfl) ⟨984399, by rfl⟩ : syracuseStep 2625065 = 1968799) B1968799
theorem B3739247 : Blo 1166400 3739247 := bstep (se 1 (by rfl) ⟨2804435, by rfl⟩ : syracuseStep 3739247 = 5608871) B5608871
theorem B4435631 : Blo 1166400 4435631 := bstep (se 1 (by rfl) ⟨3326723, by rfl⟩ : syracuseStep 4435631 = 6653447) B6653447
theorem B3321587 : Blo 1166400 3321587 := bstep (se 1 (by rfl) ⟨2491190, by rfl⟩ : syracuseStep 3321587 = 4982381) B4982381
theorem B3739463 : Blo 1166400 3739463 := bstep (se 1 (by rfl) ⟨2804597, by rfl⟩ : syracuseStep 3739463 = 5609195) B5609195
theorem B1167271 : Blo 1166400 1167271 := bstep (se 1 (by rfl) ⟨875453, by rfl⟩ : syracuseStep 1167271 = 1750907) B1750907
theorem B1167295 : Blo 1166400 1167295 := bstep (se 1 (by rfl) ⟨875471, by rfl⟩ : syracuseStep 1167295 = 1750943) B1750943
theorem B41013221 : Blo 1166400 41013221 := bstep (se 4 (by rfl) ⟨3844989, by rfl⟩ : syracuseStep 41013221 = 7689979) B7689979
theorem B18927665 : Blo 1166400 18927665 := bstep (se 2 (by rfl) ⟨7097874, by rfl⟩ : syracuseStep 18927665 = 14195749) B14195749
theorem B1167431 : Blo 1166400 1167431 := bstep (se 1 (by rfl) ⟨875573, by rfl⟩ : syracuseStep 1167431 = 1751147) B1751147
theorem B1167451 : Blo 1166400 1167451 := bstep (se 1 (by rfl) ⟨875588, by rfl⟩ : syracuseStep 1167451 = 1751177) B1751177
theorem B11972735 : Blo 1166400 11972735 := bstep (se 1 (by rfl) ⟨8979551, by rfl⟩ : syracuseStep 11972735 = 17959103) B17959103
theorem B1167551 : Blo 1166400 1167551 := bstep (se 1 (by rfl) ⟨875663, by rfl⟩ : syracuseStep 1167551 = 1751327) B1751327
theorem B9974087 : Blo 1166400 9974087 := bstep (se 1 (by rfl) ⟨7480565, by rfl⟩ : syracuseStep 9974087 = 14961131) B14961131
theorem B3936815 : Blo 1166400 3936815 := bstep (se 1 (by rfl) ⟨2952611, by rfl⟩ : syracuseStep 3936815 = 5905223) B5905223
theorem B1167999 : Blo 1166400 1167999 := bstep (se 1 (by rfl) ⟨875999, by rfl⟩ : syracuseStep 1167999 = 1751999) B1751999
theorem B1168031 : Blo 1166400 1168031 := bstep (se 1 (by rfl) ⟨876023, by rfl⟩ : syracuseStep 1168031 = 1752047) B1752047
theorem B12612347 : Blo 1166400 12612347 := bstep (se 1 (by rfl) ⟨9459260, by rfl⟩ : syracuseStep 12612347 = 18918521) B18918521
theorem B1168155 : Blo 1166400 1168155 := bstep (se 1 (by rfl) ⟨876116, by rfl⟩ : syracuseStep 1168155 = 1752233) B1752233
theorem B19190891 : Blo 1166400 19190891 := bstep (se 1 (by rfl) ⟨14393168, by rfl⟩ : syracuseStep 19190891 = 28786337) B28786337
theorem B20477261 : Blo 1166400 20477261 := bstep (se 3 (by rfl) ⟨3839486, by rfl⟩ : syracuseStep 20477261 = 7678973) B7678973
theorem B1750523 : Blo 1166400 1750523 := bstep (se 1 (by rfl) ⟨1312892, by rfl⟩ : syracuseStep 1750523 = 2625785) B2625785
theorem B8410679 : Blo 1166400 8410679 := bstep (se 1 (by rfl) ⟨6308009, by rfl⟩ : syracuseStep 8410679 = 12616019) B12616019
theorem B4494953 : Blo 1166400 4494953 := bstep (se 2 (by rfl) ⟨1685607, by rfl⟩ : syracuseStep 4494953 = 3371215) B3371215
theorem B3995291 : Blo 1166400 3995291 := bstep (se 1 (by rfl) ⟨2996468, by rfl⟩ : syracuseStep 3995291 = 5992937) B5992937
theorem B1750697 : Blo 1166400 1750697 := bstep (se 2 (by rfl) ⟨656511, by rfl⟩ : syracuseStep 1750697 = 1313023) B1313023
theorem B1750703 : Blo 1166400 1750703 := bstep (se 1 (by rfl) ⟨1313027, by rfl⟩ : syracuseStep 1750703 = 2626055) B2626055
theorem B1750823 : Blo 1166400 1750823 := bstep (se 1 (by rfl) ⟨1313117, by rfl⟩ : syracuseStep 1750823 = 2626235) B2626235
theorem B2955163 : Blo 1166400 2955163 := bstep (se 1 (by rfl) ⟨2216372, by rfl⟩ : syracuseStep 2955163 = 4432745) B4432745
theorem B3938273 : Blo 1166400 3938273 := bstep (se 2 (by rfl) ⟨1476852, by rfl⟩ : syracuseStep 3938273 = 2953705) B2953705
theorem B2955305 : Blo 1166400 2955305 := bstep (se 2 (by rfl) ⟨1108239, by rfl⟩ : syracuseStep 2955305 = 2216479) B2216479
theorem B8869985 : Blo 1166400 8869985 := bstep (se 2 (by rfl) ⟨3326244, by rfl⟩ : syracuseStep 8869985 = 6652489) B6652489
theorem B9967799 : Blo 1166400 9967799 := bstep (se 1 (by rfl) ⟨7475849, by rfl⟩ : syracuseStep 9967799 = 14951699) B14951699
theorem B1751351 : Blo 1166400 1751351 := bstep (se 1 (by rfl) ⟨1313513, by rfl⟩ : syracuseStep 1751351 = 2627027) B2627027
theorem B3938651 : Blo 1166400 3938651 := bstep (se 1 (by rfl) ⟨2953988, by rfl⟩ : syracuseStep 3938651 = 5907977) B5907977
theorem B1751423 : Blo 1166400 1751423 := bstep (se 1 (by rfl) ⟨1313567, by rfl⟩ : syracuseStep 1751423 = 2627135) B2627135
theorem B1751531 : Blo 1166400 1751531 := bstep (se 1 (by rfl) ⟨1313648, by rfl⟩ : syracuseStep 1751531 = 2627297) B2627297
theorem B8862209 : Blo 1166400 8862209 := bstep (se 2 (by rfl) ⟨3323328, by rfl⟩ : syracuseStep 8862209 = 6646657) B6646657
theorem B19954187 : Blo 1166400 19954187 := bstep (se 1 (by rfl) ⟨14965640, by rfl⟩ : syracuseStep 19954187 = 29931281) B29931281
theorem B1751771 : Blo 1166400 1751771 := bstep (se 1 (by rfl) ⟨1313828, by rfl⟩ : syracuseStep 1751771 = 2627657) B2627657
theorem B4987727 : Blo 1166400 4987727 := bstep (se 1 (by rfl) ⟨3740795, by rfl⟩ : syracuseStep 4987727 = 7481591) B7481591
theorem B6650849 : Blo 1166400 6650849 := bstep (se 2 (by rfl) ⟨2494068, by rfl⟩ : syracuseStep 6650849 = 4988137) B4988137
theorem B2956571 : Blo 1166400 2956571 := bstep (se 1 (by rfl) ⟨2217428, by rfl⟩ : syracuseStep 2956571 = 4434857) B4434857
theorem B45522283 : Blo 1166400 45522283 := bstep (se 1 (by rfl) ⟨34141712, by rfl⟩ : syracuseStep 45522283 = 68283425) B68283425
theorem B5905871 : Blo 1166400 5905871 := bstep (se 1 (by rfl) ⟨4429403, by rfl⟩ : syracuseStep 5905871 = 8858807) B8858807
theorem B4210127 : Blo 1166400 4210127 := bstep (se 1 (by rfl) ⟨3157595, by rfl⟩ : syracuseStep 4210127 = 6315191) B6315191
theorem B3325607 : Blo 1166400 3325607 := bstep (se 1 (by rfl) ⟨2494205, by rfl⟩ : syracuseStep 3325607 = 4988411) B4988411
theorem B6315707 : Blo 1166400 6315707 := bstep (se 1 (by rfl) ⟨4736780, by rfl⟩ : syracuseStep 6315707 = 9473561) B9473561
theorem B51175709 : Blo 1166400 51175709 := bstep (se 3 (by rfl) ⟨9595445, by rfl⟩ : syracuseStep 51175709 = 19190891) B19190891
theorem B9970397 : Blo 1166400 9970397 := bstep (se 3 (by rfl) ⟨1869449, by rfl⟩ : syracuseStep 9970397 = 3738899) B3738899
theorem B5325887 : Blo 1166400 5325887 := bstep (se 1 (by rfl) ⟨3994415, by rfl⟩ : syracuseStep 5325887 = 7988831) B7988831
theorem B21316679 : Blo 1166400 21316679 := bstep (se 1 (by rfl) ⟨15987509, by rfl⟩ : syracuseStep 21316679 = 31975019) B31975019
theorem B2663527 : Blo 1166400 2663527 := bstep (se 1 (by rfl) ⟨1997645, by rfl⟩ : syracuseStep 2663527 = 3995291) B3995291
theorem B2491643 : Blo 1166400 2491643 := bstep (se 1 (by rfl) ⟨1868732, by rfl⟩ : syracuseStep 2491643 = 3737465) B3737465
theorem B25265591 : Blo 1166400 25265591 := bstep (se 1 (by rfl) ⟨18949193, by rfl⟩ : syracuseStep 25265591 = 37898387) B37898387
theorem B6645199 : Blo 1166400 6645199 := bstep (se 1 (by rfl) ⟨4983899, by rfl⟩ : syracuseStep 6645199 = 9967799) B9967799
theorem B22431239 : Blo 1166400 22431239 := bstep (se 1 (by rfl) ⟨16823429, by rfl⟩ : syracuseStep 22431239 = 33646859) B33646859
theorem B1312411 : Blo 1166400 1312411 := bstep (se 1 (by rfl) ⟨984308, by rfl⟩ : syracuseStep 1312411 = 1968617) B1968617
theorem B5908139 : Blo 1166400 5908139 := bstep (se 1 (by rfl) ⟨4431104, by rfl⟩ : syracuseStep 5908139 = 8862209) B8862209
theorem B60696377 : Blo 1166400 60696377 := bstep (se 2 (by rfl) ⟨22761141, by rfl⟩ : syracuseStep 60696377 = 45522283) B45522283
theorem B9471815 : Blo 1166400 9471815 := bstep (se 1 (by rfl) ⟨7103861, by rfl⟩ : syracuseStep 9471815 = 14207723) B14207723
theorem B4433899 : Blo 1166400 4433899 := bstep (se 1 (by rfl) ⟨3325424, by rfl⟩ : syracuseStep 4433899 = 6650849) B6650849
theorem B1312879 : Blo 1166400 1312879 := bstep (se 1 (by rfl) ⟨984659, by rfl⟩ : syracuseStep 1312879 = 1969319) B1969319
theorem B2492831 : Blo 1166400 2492831 := bstep (se 1 (by rfl) ⟨1869623, by rfl⟩ : syracuseStep 2492831 = 3739247) B3739247
theorem B2214391 : Blo 1166400 2214391 := bstep (se 1 (by rfl) ⟨1660793, by rfl⟩ : syracuseStep 2214391 = 3321587) B3321587
theorem B2492975 : Blo 1166400 2492975 := bstep (se 1 (by rfl) ⟨1869731, by rfl⟩ : syracuseStep 2492975 = 3739463) B3739463
theorem B3738233 : Blo 1166400 3738233 := bstep (se 2 (by rfl) ⟨1401837, by rfl⟩ : syracuseStep 3738233 = 2803675) B2803675
theorem B12618443 : Blo 1166400 12618443 := bstep (se 1 (by rfl) ⟨9463832, by rfl⟩ : syracuseStep 12618443 = 18927665) B18927665
theorem B7981823 : Blo 1166400 7981823 := bstep (se 1 (by rfl) ⟨5986367, by rfl⟩ : syracuseStep 7981823 = 11972735) B11972735
theorem B5606273 : Blo 1166400 5606273 := bstep (se 2 (by rfl) ⟨2102352, by rfl⟩ : syracuseStep 5606273 = 4204705) B4204705
theorem B2624543 : Blo 1166400 2624543 := bstep (se 1 (by rfl) ⟨1968407, by rfl⟩ : syracuseStep 2624543 = 3936815) B3936815
theorem B8408231 : Blo 1166400 8408231 := bstep (se 1 (by rfl) ⟨6306173, by rfl⟩ : syracuseStep 8408231 = 12612347) B12612347
theorem B2624777 : Blo 1166400 2624777 := bstep (se 2 (by rfl) ⟨984291, by rfl⟩ : syracuseStep 2624777 = 1968583) B1968583
theorem B13651507 : Blo 1166400 13651507 := bstep (se 1 (by rfl) ⟨10238630, by rfl⟩ : syracuseStep 13651507 = 20477261) B20477261
theorem B1167015 : Blo 1166400 1167015 := bstep (se 1 (by rfl) ⟨875261, by rfl⟩ : syracuseStep 1167015 = 1750523) B1750523
theorem B5607119 : Blo 1166400 5607119 := bstep (se 1 (by rfl) ⟨4205339, by rfl⟩ : syracuseStep 5607119 = 8410679) B8410679
theorem B1167131 : Blo 1166400 1167131 := bstep (se 1 (by rfl) ⟨875348, by rfl⟩ : syracuseStep 1167131 = 1750697) B1750697
theorem B1167135 : Blo 1166400 1167135 := bstep (se 1 (by rfl) ⟨875351, by rfl⟩ : syracuseStep 1167135 = 1750703) B1750703
theorem B1167215 : Blo 1166400 1167215 := bstep (se 1 (by rfl) ⟨875411, by rfl⟩ : syracuseStep 1167215 = 1750823) B1750823
theorem B2625515 : Blo 1166400 2625515 := bstep (se 1 (by rfl) ⟨1969136, by rfl⟩ : syracuseStep 2625515 = 3938273) B3938273
theorem B1970203 : Blo 1166400 1970203 := bstep (se 1 (by rfl) ⟨1477652, by rfl⟩ : syracuseStep 1970203 = 2955305) B2955305
theorem B1167567 : Blo 1166400 1167567 := bstep (se 1 (by rfl) ⟨875675, by rfl⟩ : syracuseStep 1167567 = 1751351) B1751351
theorem B2625767 : Blo 1166400 2625767 := bstep (se 1 (by rfl) ⟨1969325, by rfl⟩ : syracuseStep 2625767 = 3938651) B3938651
theorem B1167615 : Blo 1166400 1167615 := bstep (se 1 (by rfl) ⟨875711, by rfl⟩ : syracuseStep 1167615 = 1751423) B1751423
theorem B1167687 : Blo 1166400 1167687 := bstep (se 1 (by rfl) ⟨875765, by rfl⟩ : syracuseStep 1167687 = 1751531) B1751531
theorem B1167847 : Blo 1166400 1167847 := bstep (se 1 (by rfl) ⟨875885, by rfl⟩ : syracuseStep 1167847 = 1751771) B1751771
theorem B1971047 : Blo 1166400 1971047 := bstep (se 1 (by rfl) ⟨1478285, by rfl⟩ : syracuseStep 1971047 = 2956571) B2956571
theorem B32846759 : Blo 1166400 32846759 := bstep (se 1 (by rfl) ⟨24635069, by rfl⟩ : syracuseStep 32846759 = 49270139) B49270139
theorem B3937247 : Blo 1166400 3937247 := bstep (se 1 (by rfl) ⟨2952935, by rfl⟩ : syracuseStep 3937247 = 5905871) B5905871
theorem B2806751 : Blo 1166400 2806751 := bstep (se 1 (by rfl) ⟨2105063, by rfl⟩ : syracuseStep 2806751 = 4210127) B4210127
theorem B1750043 : Blo 1166400 1750043 := bstep (se 1 (by rfl) ⟨1312532, by rfl⟩ : syracuseStep 1750043 = 2625065) B2625065
theorem B2217071 : Blo 1166400 2217071 := bstep (se 1 (by rfl) ⟨1662803, by rfl⟩ : syracuseStep 2217071 = 3325607) B3325607
theorem B191550581 : Blo 1166400 191550581 := bstep (se 5 (by rfl) ⟨8978933, by rfl⟩ : syracuseStep 191550581 = 17957867) B17957867
theorem B109368589 : Blo 1166400 109368589 := bstep (se 3 (by rfl) ⟨20506610, by rfl⟩ : syracuseStep 109368589 = 41013221) B41013221
theorem B2627063 : Blo 1166400 2627063 := bstep (se 1 (by rfl) ⟨1970297, by rfl⟩ : syracuseStep 2627063 = 3940595) B3940595
theorem B6649391 : Blo 1166400 6649391 := bstep (se 1 (by rfl) ⟨4987043, by rfl⟩ : syracuseStep 6649391 = 9974087) B9974087
theorem B22435703 : Blo 1166400 22435703 := bstep (se 1 (by rfl) ⟨16826777, by rfl⟩ : syracuseStep 22435703 = 33653555) B33653555
theorem B4430011 : Blo 1166400 4430011 := bstep (se 1 (by rfl) ⟨3322508, by rfl⟩ : syracuseStep 4430011 = 6645017) B6645017
theorem B2955599 : Blo 1166400 2955599 := bstep (se 1 (by rfl) ⟨2216699, by rfl⟩ : syracuseStep 2955599 = 4433399) B4433399
theorem B2103679 : Blo 1166400 2103679 := bstep (se 1 (by rfl) ⟨1577759, by rfl⟩ : syracuseStep 2103679 = 3155519) B3155519
theorem B2996635 : Blo 1166400 2996635 := bstep (se 1 (by rfl) ⟨2247476, by rfl⟩ : syracuseStep 2996635 = 4494953) B4494953
theorem B4987439 : Blo 1166400 4987439 := bstep (se 1 (by rfl) ⟨3740579, by rfl⟩ : syracuseStep 4987439 = 7481159) B7481159
theorem B3938975 : Blo 1166400 3938975 := bstep (se 1 (by rfl) ⟨2954231, by rfl⟩ : syracuseStep 3938975 = 5908463) B5908463
theorem B2628287 : Blo 1166400 2628287 := bstep (se 1 (by rfl) ⟨1971215, by rfl⟩ : syracuseStep 2628287 = 3942431) B3942431
theorem B5913323 : Blo 1166400 5913323 := bstep (se 1 (by rfl) ⟨4434992, by rfl⟩ : syracuseStep 5913323 = 8869985) B8869985
theorem B1751945 : Blo 1166400 1751945 := bstep (se 2 (by rfl) ⟨656979, by rfl⟩ : syracuseStep 1751945 = 1313959) B1313959
theorem B2956247 : Blo 1166400 2956247 := bstep (se 1 (by rfl) ⟨2217185, by rfl⟩ : syracuseStep 2956247 = 4434371) B4434371
theorem B13302791 : Blo 1166400 13302791 := bstep (se 1 (by rfl) ⟨9977093, by rfl⟩ : syracuseStep 13302791 = 19954187) B19954187
theorem B3325151 : Blo 1166400 3325151 := bstep (se 1 (by rfl) ⟨2493863, by rfl⟩ : syracuseStep 3325151 = 4987727) B4987727
theorem B2957087 : Blo 1166400 2957087 := bstep (se 1 (by rfl) ⟨2217815, by rfl⟩ : syracuseStep 2957087 = 4435631) B4435631
theorem B4210471 : Blo 1166400 4210471 := bstep (se 1 (by rfl) ⟨3157853, by rfl⟩ : syracuseStep 4210471 = 6315707) B6315707
theorem B3940217 : Blo 1166400 3940217 := bstep (se 2 (by rfl) ⟨1477581, by rfl⟩ : syracuseStep 3940217 = 2955163) B2955163
theorem B5906681 : Blo 1166400 5906681 := bstep (se 2 (by rfl) ⟨2215005, by rfl⟩ : syracuseStep 5906681 = 4430011) B4430011
theorem B21897839 : Blo 1166400 21897839 := bstep (se 1 (by rfl) ⟨16423379, by rfl⟩ : syracuseStep 21897839 = 32846759) B32846759
theorem B16843727 : Blo 1166400 16843727 := bstep (se 1 (by rfl) ⟨12632795, by rfl⟩ : syracuseStep 16843727 = 25265591) B25265591
theorem B4432927 : Blo 1166400 4432927 := bstep (se 1 (by rfl) ⟨3324695, by rfl⟩ : syracuseStep 4432927 = 6649391) B6649391
theorem B2492155 : Blo 1166400 2492155 := bstep (se 1 (by rfl) ⟨1869116, by rfl⟩ : syracuseStep 2492155 = 3738233) B3738233
theorem B3942215 : Blo 1166400 3942215 := bstep (se 1 (by rfl) ⟨2956661, by rfl⟩ : syracuseStep 3942215 = 5913323) B5913323
theorem B3737515 : Blo 1166400 3737515 := bstep (se 1 (by rfl) ⟨2803136, by rfl⟩ : syracuseStep 3737515 = 5606273) B5606273
theorem B5605487 : Blo 1166400 5605487 := bstep (se 1 (by rfl) ⟨4204115, by rfl⟩ : syracuseStep 5605487 = 8408231) B8408231
theorem B5613961 : Blo 1166400 5613961 := bstep (se 2 (by rfl) ⟨2105235, by rfl⟩ : syracuseStep 5613961 = 4210471) B4210471
theorem B3738079 : Blo 1166400 3738079 := bstep (se 1 (by rfl) ⟨2803559, by rfl⟩ : syracuseStep 3738079 = 5607119) B5607119
theorem B6646931 : Blo 1166400 6646931 := bstep (se 1 (by rfl) ⟨4985198, by rfl⟩ : syracuseStep 6646931 = 9970397) B9970397
theorem B2804905 : Blo 1166400 2804905 := bstep (se 2 (by rfl) ⟨1051839, by rfl⟩ : syracuseStep 2804905 = 2103679) B2103679
theorem B1314031 : Blo 1166400 1314031 := bstep (se 1 (by rfl) ⟨985523, by rfl⟩ : syracuseStep 1314031 = 1971047) B1971047
theorem B8867069 : Blo 1166400 8867069 := bstep (se 3 (by rfl) ⟨1662575, by rfl⟩ : syracuseStep 8867069 = 3325151) B3325151
theorem B2624831 : Blo 1166400 2624831 := bstep (se 1 (by rfl) ⟨1968623, by rfl⟩ : syracuseStep 2624831 = 3937247) B3937247
theorem B1871167 : Blo 1166400 1871167 := bstep (se 1 (by rfl) ⟨1403375, by rfl⟩ : syracuseStep 1871167 = 2806751) B2806751
theorem B2952521 : Blo 1166400 2952521 := bstep (se 2 (by rfl) ⟨1107195, by rfl⟩ : syracuseStep 2952521 = 2214391) B2214391
theorem B1166695 : Blo 1166400 1166695 := bstep (se 1 (by rfl) ⟨875021, by rfl⟩ : syracuseStep 1166695 = 1750043) B1750043
theorem B3550591 : Blo 1166400 3550591 := bstep (se 1 (by rfl) ⟨2662943, by rfl⟩ : syracuseStep 3550591 = 5325887) B5325887
theorem B127700387 : Blo 1166400 127700387 := bstep (se 1 (by rfl) ⟨95775290, by rfl⟩ : syracuseStep 127700387 = 191550581) B191550581
theorem B14954159 : Blo 1166400 14954159 := bstep (se 1 (by rfl) ⟨11215619, by rfl⟩ : syracuseStep 14954159 = 22431239) B22431239
theorem B40464251 : Blo 1166400 40464251 := bstep (se 1 (by rfl) ⟨30348188, by rfl⟩ : syracuseStep 40464251 = 60696377) B60696377
theorem B6647933 : Blo 1166400 6647933 := bstep (se 3 (by rfl) ⟨1246487, by rfl⟩ : syracuseStep 6647933 = 2492975) B2492975
theorem B3551369 : Blo 1166400 3551369 := bstep (se 2 (by rfl) ⟨1331763, by rfl⟩ : syracuseStep 3551369 = 2663527) B2663527
theorem B1970399 : Blo 1166400 1970399 := bstep (se 1 (by rfl) ⟨1477799, by rfl⟩ : syracuseStep 1970399 = 2955599) B2955599
theorem B2625983 : Blo 1166400 2625983 := bstep (se 1 (by rfl) ⟨1969487, by rfl⟩ : syracuseStep 2625983 = 3938975) B3938975
theorem B5321215 : Blo 1166400 5321215 := bstep (se 1 (by rfl) ⟨3990911, by rfl⟩ : syracuseStep 5321215 = 7981823) B7981823
theorem B1167963 : Blo 1166400 1167963 := bstep (se 1 (by rfl) ⟨875972, by rfl⟩ : syracuseStep 1167963 = 1751945) B1751945
theorem B8860265 : Blo 1166400 8860265 := bstep (se 2 (by rfl) ⟨3322599, by rfl⟩ : syracuseStep 8860265 = 6645199) B6645199
theorem B1970831 : Blo 1166400 1970831 := bstep (se 1 (by rfl) ⟨1478123, by rfl⟩ : syracuseStep 1970831 = 2956247) B2956247
theorem B8868527 : Blo 1166400 8868527 := bstep (se 1 (by rfl) ⟨6651395, by rfl⟩ : syracuseStep 8868527 = 13302791) B13302791
theorem B1749695 : Blo 1166400 1749695 := bstep (se 1 (by rfl) ⟨1312271, by rfl⟩ : syracuseStep 1749695 = 2624543) B2624543
theorem B1749851 : Blo 1166400 1749851 := bstep (se 1 (by rfl) ⟨1312388, by rfl⟩ : syracuseStep 1749851 = 2624777) B2624777
theorem B1749881 : Blo 1166400 1749881 := bstep (se 2 (by rfl) ⟨656205, by rfl⟩ : syracuseStep 1749881 = 1312411) B1312411
theorem B1971391 : Blo 1166400 1971391 := bstep (se 1 (by rfl) ⟨1478543, by rfl⟩ : syracuseStep 1971391 = 2957087) B2957087
theorem B2626811 : Blo 1166400 2626811 := bstep (se 1 (by rfl) ⟨1970108, by rfl⟩ : syracuseStep 2626811 = 3940217) B3940217
theorem B5911865 : Blo 1166400 5911865 := bstep (se 2 (by rfl) ⟨2216949, by rfl⟩ : syracuseStep 5911865 = 4433899) B4433899
theorem B1750343 : Blo 1166400 1750343 := bstep (se 1 (by rfl) ⟨1312757, by rfl⟩ : syracuseStep 1750343 = 2625515) B2625515
theorem B2626937 : Blo 1166400 2626937 := bstep (se 2 (by rfl) ⟨985101, by rfl⟩ : syracuseStep 2626937 = 1970203) B1970203
theorem B1750505 : Blo 1166400 1750505 := bstep (se 2 (by rfl) ⟨656439, by rfl⟩ : syracuseStep 1750505 = 1312879) B1312879
theorem B1750511 : Blo 1166400 1750511 := bstep (se 1 (by rfl) ⟨1312883, by rfl⟩ : syracuseStep 1750511 = 2625767) B2625767
theorem B34117139 : Blo 1166400 34117139 := bstep (se 1 (by rfl) ⟨25587854, by rfl⟩ : syracuseStep 34117139 = 51175709) B51175709
theorem B5912189 : Blo 1166400 5912189 := bstep (se 3 (by rfl) ⟨1108535, by rfl⟩ : syracuseStep 5912189 = 2217071) B2217071
theorem B3995513 : Blo 1166400 3995513 := bstep (se 2 (by rfl) ⟨1498317, by rfl⟩ : syracuseStep 3995513 = 2996635) B2996635
theorem B14211119 : Blo 1166400 14211119 := bstep (se 1 (by rfl) ⟨10658339, by rfl⟩ : syracuseStep 14211119 = 21316679) B21316679
theorem B1661095 : Blo 1166400 1661095 := bstep (se 1 (by rfl) ⟨1245821, by rfl⟩ : syracuseStep 1661095 = 2491643) B2491643
theorem B1751375 : Blo 1166400 1751375 := bstep (se 1 (by rfl) ⟨1313531, by rfl⟩ : syracuseStep 1751375 = 2627063) B2627063
theorem B3938759 : Blo 1166400 3938759 := bstep (se 1 (by rfl) ⟨2954069, by rfl⟩ : syracuseStep 3938759 = 5908139) B5908139
theorem B6314543 : Blo 1166400 6314543 := bstep (se 1 (by rfl) ⟨4735907, by rfl⟩ : syracuseStep 6314543 = 9471815) B9471815
theorem B14957135 : Blo 1166400 14957135 := bstep (se 1 (by rfl) ⟨11217851, by rfl⟩ : syracuseStep 14957135 = 22435703) B22435703
theorem B1661887 : Blo 1166400 1661887 := bstep (se 1 (by rfl) ⟨1246415, by rfl⟩ : syracuseStep 1661887 = 2492831) B2492831
theorem B145824785 : Blo 1166400 145824785 := bstep (se 2 (by rfl) ⟨54684294, by rfl⟩ : syracuseStep 145824785 = 109368589) B109368589
theorem B3324959 : Blo 1166400 3324959 := bstep (se 1 (by rfl) ⟨2493719, by rfl⟩ : syracuseStep 3324959 = 4987439) B4987439
theorem B1752191 : Blo 1166400 1752191 := bstep (se 1 (by rfl) ⟨1314143, by rfl⟩ : syracuseStep 1752191 = 2628287) B2628287
theorem B8412295 : Blo 1166400 8412295 := bstep (se 1 (by rfl) ⟨6309221, by rfl⟩ : syracuseStep 8412295 = 12618443) B12618443
theorem B18202009 : Blo 1166400 18202009 := bstep (se 2 (by rfl) ⟨6825753, by rfl⟩ : syracuseStep 18202009 = 13651507) B13651507
theorem B4431955 : Blo 1166400 4431955 := bstep (se 1 (by rfl) ⟨3323966, by rfl⟩ : syracuseStep 4431955 = 6647933) B6647933
theorem B5906843 : Blo 1166400 5906843 := bstep (se 1 (by rfl) ⟨4430132, by rfl⟩ : syracuseStep 5906843 = 8860265) B8860265
theorem B14598559 : Blo 1166400 14598559 := bstep (se 1 (by rfl) ⟨10948919, by rfl⟩ : syracuseStep 14598559 = 21897839) B21897839
theorem B7094953 : Blo 1166400 7094953 := bstep (se 2 (by rfl) ⟨2660607, by rfl⟩ : syracuseStep 7094953 = 5321215) B5321215
theorem B3941243 : Blo 1166400 3941243 := bstep (se 1 (by rfl) ⟨2955932, by rfl⟩ : syracuseStep 3941243 = 5911865) B5911865
theorem B3941459 : Blo 1166400 3941459 := bstep (se 1 (by rfl) ⟨2956094, by rfl⟩ : syracuseStep 3941459 = 5912189) B5912189
theorem B2663675 : Blo 1166400 2663675 := bstep (se 1 (by rfl) ⟨1997756, by rfl⟩ : syracuseStep 2663675 = 3995513) B3995513
theorem B3736991 : Blo 1166400 3736991 := bstep (se 1 (by rfl) ⟨2802743, by rfl⟩ : syracuseStep 3736991 = 5605487) B5605487
theorem B37881269 : Blo 1166400 37881269 := bstep (se 5 (by rfl) ⟨1775684, by rfl⟩ : syracuseStep 37881269 = 3551369) B3551369
theorem B11216393 : Blo 1166400 11216393 := bstep (se 2 (by rfl) ⟨4206147, by rfl⟩ : syracuseStep 11216393 = 8412295) B8412295
theorem B9971423 : Blo 1166400 9971423 := bstep (se 1 (by rfl) ⟨7478567, by rfl⟩ : syracuseStep 9971423 = 14957135) B14957135
theorem B97216523 : Blo 1166400 97216523 := bstep (se 1 (by rfl) ⟨72912392, by rfl⟩ : syracuseStep 97216523 = 145824785) B145824785
theorem B1968347 : Blo 1166400 1968347 := bstep (se 1 (by rfl) ⟨1476260, by rfl⟩ : syracuseStep 1968347 = 2952521) B2952521
theorem B85133591 : Blo 1166400 85133591 := bstep (se 1 (by rfl) ⟨63850193, by rfl⟩ : syracuseStep 85133591 = 127700387) B127700387
theorem B4983353 : Blo 1166400 4983353 := bstep (se 2 (by rfl) ⟨1868757, by rfl⟩ : syracuseStep 4983353 = 3737515) B3737515
theorem B1313599 : Blo 1166400 1313599 := bstep (se 1 (by rfl) ⟨985199, by rfl⟩ : syracuseStep 1313599 = 1970399) B1970399
theorem B2214793 : Blo 1166400 2214793 := bstep (se 2 (by rfl) ⟨830547, by rfl⟩ : syracuseStep 2214793 = 1661095) B1661095
theorem B1313887 : Blo 1166400 1313887 := bstep (se 1 (by rfl) ⟨985415, by rfl⟩ : syracuseStep 1313887 = 1970831) B1970831
theorem B1166463 : Blo 1166400 1166463 := bstep (se 1 (by rfl) ⟨874847, by rfl⟩ : syracuseStep 1166463 = 1749695) B1749695
theorem B1166567 : Blo 1166400 1166567 := bstep (se 1 (by rfl) ⟨874925, by rfl⟩ : syracuseStep 1166567 = 1749851) B1749851
theorem B1166587 : Blo 1166400 1166587 := bstep (se 1 (by rfl) ⟨874940, by rfl⟩ : syracuseStep 1166587 = 1749881) B1749881
theorem B4984105 : Blo 1166400 4984105 := bstep (se 2 (by rfl) ⟨1869039, by rfl⟩ : syracuseStep 4984105 = 3738079) B3738079
theorem B1166895 : Blo 1166400 1166895 := bstep (se 1 (by rfl) ⟨875171, by rfl⟩ : syracuseStep 1166895 = 1750343) B1750343
theorem B1167003 : Blo 1166400 1167003 := bstep (se 1 (by rfl) ⟨875252, by rfl⟩ : syracuseStep 1167003 = 1750505) B1750505
theorem B1167007 : Blo 1166400 1167007 := bstep (se 1 (by rfl) ⟨875255, by rfl⟩ : syracuseStep 1167007 = 1750511) B1750511
theorem B22744759 : Blo 1166400 22744759 := bstep (se 1 (by rfl) ⟨17058569, by rfl⟩ : syracuseStep 22744759 = 34117139) B34117139
theorem B2215849 : Blo 1166400 2215849 := bstep (se 2 (by rfl) ⟨830943, by rfl⟩ : syracuseStep 2215849 = 1661887) B1661887
theorem B9474079 : Blo 1166400 9474079 := bstep (se 1 (by rfl) ⟨7105559, by rfl⟩ : syracuseStep 9474079 = 14211119) B14211119
theorem B5910569 : Blo 1166400 5910569 := bstep (se 2 (by rfl) ⟨2216463, by rfl⟩ : syracuseStep 5910569 = 4432927) B4432927
theorem B1167583 : Blo 1166400 1167583 := bstep (se 1 (by rfl) ⟨875687, by rfl⟩ : syracuseStep 1167583 = 1751375) B1751375
theorem B3739873 : Blo 1166400 3739873 := bstep (se 2 (by rfl) ⟨1402452, by rfl⟩ : syracuseStep 3739873 = 2804905) B2804905
theorem B2625839 : Blo 1166400 2625839 := bstep (se 1 (by rfl) ⟨1969379, by rfl⟩ : syracuseStep 2625839 = 3938759) B3938759
theorem B2494889 : Blo 1166400 2494889 := bstep (se 2 (by rfl) ⟨935583, by rfl⟩ : syracuseStep 2494889 = 1871167) B1871167
theorem B24269345 : Blo 1166400 24269345 := bstep (se 2 (by rfl) ⟨9101004, by rfl⟩ : syracuseStep 24269345 = 18202009) B18202009
theorem B2216639 : Blo 1166400 2216639 := bstep (se 1 (by rfl) ⟨1662479, by rfl⟩ : syracuseStep 2216639 = 3324959) B3324959
theorem B1168127 : Blo 1166400 1168127 := bstep (se 1 (by rfl) ⟨876095, by rfl⟩ : syracuseStep 1168127 = 1752191) B1752191
theorem B5911379 : Blo 1166400 5911379 := bstep (se 1 (by rfl) ⟨4433534, by rfl⟩ : syracuseStep 5911379 = 8867069) B8867069
theorem B1749887 : Blo 1166400 1749887 := bstep (se 1 (by rfl) ⟨1312415, by rfl⟩ : syracuseStep 1749887 = 2624831) B2624831
theorem B3322873 : Blo 1166400 3322873 := bstep (se 2 (by rfl) ⟨1246077, by rfl⟩ : syracuseStep 3322873 = 2492155) B2492155
theorem B3937787 : Blo 1166400 3937787 := bstep (se 1 (by rfl) ⟨2953340, by rfl⟩ : syracuseStep 3937787 = 5906681) B5906681
theorem B1750655 : Blo 1166400 1750655 := bstep (se 1 (by rfl) ⟨1312991, by rfl⟩ : syracuseStep 1750655 = 2625983) B2625983
theorem B5912351 : Blo 1166400 5912351 := bstep (se 1 (by rfl) ⟨4434263, by rfl⟩ : syracuseStep 5912351 = 8868527) B8868527
theorem B7485281 : Blo 1166400 7485281 := bstep (se 2 (by rfl) ⟨2806980, by rfl⟩ : syracuseStep 7485281 = 5613961) B5613961
theorem B1751207 : Blo 1166400 1751207 := bstep (se 1 (by rfl) ⟨1313405, by rfl⟩ : syracuseStep 1751207 = 2626811) B2626811
theorem B1751291 : Blo 1166400 1751291 := bstep (se 1 (by rfl) ⟨1313468, by rfl⟩ : syracuseStep 1751291 = 2626937) B2626937
theorem B2628143 : Blo 1166400 2628143 := bstep (se 1 (by rfl) ⟨1971107, by rfl⟩ : syracuseStep 2628143 = 3942215) B3942215
theorem B2628521 : Blo 1166400 2628521 := bstep (se 2 (by rfl) ⟨985695, by rfl⟩ : syracuseStep 2628521 = 1971391) B1971391
theorem B1752041 : Blo 1166400 1752041 := bstep (se 2 (by rfl) ⟨657015, by rfl⟩ : syracuseStep 1752041 = 1314031) B1314031
theorem B4209695 : Blo 1166400 4209695 := bstep (se 1 (by rfl) ⟨3157271, by rfl⟩ : syracuseStep 4209695 = 6314543) B6314543
theorem B4734121 : Blo 1166400 4734121 := bstep (se 2 (by rfl) ⟨1775295, by rfl⟩ : syracuseStep 4734121 = 3550591) B3550591
theorem B4431287 : Blo 1166400 4431287 := bstep (se 1 (by rfl) ⟨3323465, by rfl⟩ : syracuseStep 4431287 = 6646931) B6646931
theorem B9969439 : Blo 1166400 9969439 := bstep (se 1 (by rfl) ⟨7477079, by rfl⟩ : syracuseStep 9969439 = 14954159) B14954159
theorem B44916605 : Blo 1166400 44916605 := bstep (se 3 (by rfl) ⟨8421863, by rfl⟩ : syracuseStep 44916605 = 16843727) B16843727
theorem B26976167 : Blo 1166400 26976167 := bstep (se 1 (by rfl) ⟨20232125, by rfl⟩ : syracuseStep 26976167 = 40464251) B40464251
theorem B3940379 : Blo 1166400 3940379 := bstep (se 1 (by rfl) ⟨2955284, by rfl⟩ : syracuseStep 3940379 = 5910569) B5910569
theorem B12632105 : Blo 1166400 12632105 := bstep (se 2 (by rfl) ⟨4737039, by rfl⟩ : syracuseStep 12632105 = 9474079) B9474079
theorem B1663259 : Blo 1166400 1663259 := bstep (se 1 (by rfl) ⟨1247444, by rfl⟩ : syracuseStep 1663259 = 2494889) B2494889
theorem B16179563 : Blo 1166400 16179563 := bstep (se 1 (by rfl) ⟨12134672, by rfl⟩ : syracuseStep 16179563 = 24269345) B24269345
theorem B19464745 : Blo 1166400 19464745 := bstep (se 2 (by rfl) ⟨7299279, by rfl⟩ : syracuseStep 19464745 = 14598559) B14598559
theorem B3940919 : Blo 1166400 3940919 := bstep (se 1 (by rfl) ⟨2955689, by rfl⟩ : syracuseStep 3940919 = 5911379) B5911379
theorem B2491327 : Blo 1166400 2491327 := bstep (se 1 (by rfl) ⟨1868495, by rfl⟩ : syracuseStep 2491327 = 3736991) B3736991
theorem B3941567 : Blo 1166400 3941567 := bstep (se 1 (by rfl) ⟨2956175, by rfl⟩ : syracuseStep 3941567 = 5912351) B5912351
theorem B4990187 : Blo 1166400 4990187 := bstep (se 1 (by rfl) ⟨3742640, by rfl⟩ : syracuseStep 4990187 = 7485281) B7485281
theorem B1312231 : Blo 1166400 1312231 := bstep (se 1 (by rfl) ⟨984173, by rfl⟩ : syracuseStep 1312231 = 1968347) B1968347
theorem B56755727 : Blo 1166400 56755727 := bstep (se 1 (by rfl) ⟨42566795, by rfl⟩ : syracuseStep 56755727 = 85133591) B85133591
theorem B6645473 : Blo 1166400 6645473 := bstep (se 2 (by rfl) ⟨2492052, by rfl⟩ : syracuseStep 6645473 = 4984105) B4984105
theorem B29944403 : Blo 1166400 29944403 := bstep (se 1 (by rfl) ⟨22458302, by rfl⟩ : syracuseStep 29944403 = 44916605) B44916605
theorem B17984111 : Blo 1166400 17984111 := bstep (se 1 (by rfl) ⟨13488083, by rfl⟩ : syracuseStep 17984111 = 26976167) B26976167
theorem B5909273 : Blo 1166400 5909273 := bstep (se 2 (by rfl) ⟨2215977, by rfl⟩ : syracuseStep 5909273 = 4431955) B4431955
theorem B1477759 : Blo 1166400 1477759 := bstep (se 1 (by rfl) ⟨1108319, by rfl⟩ : syracuseStep 1477759 = 2216639) B2216639
theorem B1166591 : Blo 1166400 1166591 := bstep (se 1 (by rfl) ⟨874943, by rfl⟩ : syracuseStep 1166591 = 1749887) B1749887
theorem B2625191 : Blo 1166400 2625191 := bstep (se 1 (by rfl) ⟨1968893, by rfl⟩ : syracuseStep 2625191 = 3937787) B3937787
theorem B1167103 : Blo 1166400 1167103 := bstep (se 1 (by rfl) ⟨875327, by rfl⟩ : syracuseStep 1167103 = 1750655) B1750655
theorem B6647615 : Blo 1166400 6647615 := bstep (se 1 (by rfl) ⟨4985711, by rfl⟩ : syracuseStep 6647615 = 9971423) B9971423
theorem B2953057 : Blo 1166400 2953057 := bstep (se 2 (by rfl) ⟨1107396, by rfl⟩ : syracuseStep 2953057 = 2214793) B2214793
theorem B64811015 : Blo 1166400 64811015 := bstep (se 1 (by rfl) ⟨48608261, by rfl⟩ : syracuseStep 64811015 = 97216523) B97216523
theorem B1167471 : Blo 1166400 1167471 := bstep (se 1 (by rfl) ⟨875603, by rfl⟩ : syracuseStep 1167471 = 1751207) B1751207
theorem B1167527 : Blo 1166400 1167527 := bstep (se 1 (by rfl) ⟨875645, by rfl⟩ : syracuseStep 1167527 = 1751291) B1751291
theorem B6312161 : Blo 1166400 6312161 := bstep (se 2 (by rfl) ⟨2367060, by rfl⟩ : syracuseStep 6312161 = 4734121) B4734121
theorem B3322235 : Blo 1166400 3322235 := bstep (se 1 (by rfl) ⟨2491676, by rfl⟩ : syracuseStep 3322235 = 4983353) B4983353
theorem B1168027 : Blo 1166400 1168027 := bstep (se 1 (by rfl) ⟨876020, by rfl⟩ : syracuseStep 1168027 = 1752041) B1752041
theorem B2806463 : Blo 1166400 2806463 := bstep (se 1 (by rfl) ⟨2104847, by rfl⟩ : syracuseStep 2806463 = 4209695) B4209695
theorem B2954191 : Blo 1166400 2954191 := bstep (se 1 (by rfl) ⟨2215643, by rfl⟩ : syracuseStep 2954191 = 4431287) B4431287
theorem B13292585 : Blo 1166400 13292585 := bstep (se 2 (by rfl) ⟨4984719, by rfl⟩ : syracuseStep 13292585 = 9969439) B9969439
theorem B2954465 : Blo 1166400 2954465 := bstep (se 2 (by rfl) ⟨1107924, by rfl⟩ : syracuseStep 2954465 = 2215849) B2215849
theorem B1750559 : Blo 1166400 1750559 := bstep (se 1 (by rfl) ⟨1312919, by rfl⟩ : syracuseStep 1750559 = 2625839) B2625839
theorem B3937895 : Blo 1166400 3937895 := bstep (se 1 (by rfl) ⟨2953421, by rfl⟩ : syracuseStep 3937895 = 5906843) B5906843
theorem B4986497 : Blo 1166400 4986497 := bstep (se 2 (by rfl) ⟨1869936, by rfl⟩ : syracuseStep 4986497 = 3739873) B3739873
theorem B2627495 : Blo 1166400 2627495 := bstep (se 1 (by rfl) ⟨1970621, by rfl⟩ : syracuseStep 2627495 = 3941243) B3941243
theorem B2627639 : Blo 1166400 2627639 := bstep (se 1 (by rfl) ⟨1970729, by rfl⟩ : syracuseStep 2627639 = 3941459) B3941459
theorem B1775783 : Blo 1166400 1775783 := bstep (se 1 (by rfl) ⟨1331837, by rfl⟩ : syracuseStep 1775783 = 2663675) B2663675
theorem B9459937 : Blo 1166400 9459937 := bstep (se 2 (by rfl) ⟨3547476, by rfl⟩ : syracuseStep 9459937 = 7094953) B7094953
theorem B25254179 : Blo 1166400 25254179 := bstep (se 1 (by rfl) ⟨18940634, by rfl⟩ : syracuseStep 25254179 = 37881269) B37881269
theorem B7477595 : Blo 1166400 7477595 := bstep (se 1 (by rfl) ⟨5608196, by rfl⟩ : syracuseStep 7477595 = 11216393) B11216393
theorem B1751465 : Blo 1166400 1751465 := bstep (se 2 (by rfl) ⟨656799, by rfl⟩ : syracuseStep 1751465 = 1313599) B1313599
theorem B4430497 : Blo 1166400 4430497 := bstep (se 2 (by rfl) ⟨1661436, by rfl⟩ : syracuseStep 4430497 = 3322873) B3322873
theorem B1751849 : Blo 1166400 1751849 := bstep (se 2 (by rfl) ⟨656943, by rfl⟩ : syracuseStep 1751849 = 1313887) B1313887
theorem B1752095 : Blo 1166400 1752095 := bstep (se 1 (by rfl) ⟨1314071, by rfl⟩ : syracuseStep 1752095 = 2628143) B2628143
theorem B1752347 : Blo 1166400 1752347 := bstep (se 1 (by rfl) ⟨1314260, by rfl⟩ : syracuseStep 1752347 = 2628521) B2628521
theorem B30326345 : Blo 1166400 30326345 := bstep (se 2 (by rfl) ⟨11372379, by rfl⟩ : syracuseStep 30326345 = 22744759) B22744759
theorem B8421403 : Blo 1166400 8421403 := bstep (se 1 (by rfl) ⟨6316052, by rfl⟩ : syracuseStep 8421403 = 12632105) B12632105
theorem B4735421 : Blo 1166400 4735421 := bstep (se 3 (by rfl) ⟨887891, by rfl⟩ : syracuseStep 4735421 = 1775783) B1775783
theorem B25952993 : Blo 1166400 25952993 := bstep (se 2 (by rfl) ⟨9732372, by rfl⟩ : syracuseStep 25952993 = 19464745) B19464745
theorem B5907329 : Blo 1166400 5907329 := bstep (se 2 (by rfl) ⟨2215248, by rfl⟩ : syracuseStep 5907329 = 4430497) B4430497
theorem B16836119 : Blo 1166400 16836119 := bstep (se 1 (by rfl) ⟨12627089, by rfl⟩ : syracuseStep 16836119 = 25254179) B25254179
theorem B47957629 : Blo 1166400 47957629 := bstep (se 3 (by rfl) ⟨8992055, by rfl⟩ : syracuseStep 47957629 = 17984111) B17984111
theorem B43207343 : Blo 1166400 43207343 := bstep (se 1 (by rfl) ⟨32405507, by rfl⟩ : syracuseStep 43207343 = 64811015) B64811015
theorem B1870975 : Blo 1166400 1870975 := bstep (se 1 (by rfl) ⟨1403231, by rfl⟩ : syracuseStep 1870975 = 2806463) B2806463
theorem B13307165 : Blo 1166400 13307165 := bstep (se 3 (by rfl) ⟨2495093, by rfl⟩ : syracuseStep 13307165 = 4990187) B4990187
theorem B4435357 : Blo 1166400 4435357 := bstep (se 3 (by rfl) ⟨831629, by rfl⟩ : syracuseStep 4435357 = 1663259) B1663259
theorem B1969643 : Blo 1166400 1969643 := bstep (se 1 (by rfl) ⟨1477232, by rfl⟩ : syracuseStep 1969643 = 2954465) B2954465
theorem B8859293 : Blo 1166400 8859293 := bstep (se 3 (by rfl) ⟨1661117, by rfl⟩ : syracuseStep 8859293 = 3322235) B3322235
theorem B1167039 : Blo 1166400 1167039 := bstep (se 1 (by rfl) ⟨875279, by rfl⟩ : syracuseStep 1167039 = 1750559) B1750559
theorem B2625263 : Blo 1166400 2625263 := bstep (se 1 (by rfl) ⟨1968947, by rfl⟩ : syracuseStep 2625263 = 3937895) B3937895
theorem B3321769 : Blo 1166400 3321769 := bstep (se 2 (by rfl) ⟨1245663, by rfl⟩ : syracuseStep 3321769 = 2491327) B2491327
theorem B1970345 : Blo 1166400 1970345 := bstep (se 2 (by rfl) ⟨738879, by rfl⟩ : syracuseStep 1970345 = 1477759) B1477759
theorem B4985063 : Blo 1166400 4985063 := bstep (se 1 (by rfl) ⟨3738797, by rfl⟩ : syracuseStep 4985063 = 7477595) B7477595
theorem B1167643 : Blo 1166400 1167643 := bstep (se 1 (by rfl) ⟨875732, by rfl⟩ : syracuseStep 1167643 = 1751465) B1751465
theorem B1167899 : Blo 1166400 1167899 := bstep (se 1 (by rfl) ⟨875924, by rfl⟩ : syracuseStep 1167899 = 1751849) B1751849
theorem B1749641 : Blo 1166400 1749641 := bstep (se 2 (by rfl) ⟨656115, by rfl⟩ : syracuseStep 1749641 = 1312231) B1312231
theorem B1168063 : Blo 1166400 1168063 := bstep (se 1 (by rfl) ⟨876047, by rfl⟩ : syracuseStep 1168063 = 1752095) B1752095
theorem B1168231 : Blo 1166400 1168231 := bstep (se 1 (by rfl) ⟨876173, by rfl⟩ : syracuseStep 1168231 = 1752347) B1752347
theorem B1750127 : Blo 1166400 1750127 := bstep (se 1 (by rfl) ⟨1312595, by rfl⟩ : syracuseStep 1750127 = 2625191) B2625191
theorem B3937409 : Blo 1166400 3937409 := bstep (se 2 (by rfl) ⟨1476528, by rfl⟩ : syracuseStep 3937409 = 2953057) B2953057
theorem B2626919 : Blo 1166400 2626919 := bstep (se 1 (by rfl) ⟨1970189, by rfl⟩ : syracuseStep 2626919 = 3940379) B3940379
theorem B4208107 : Blo 1166400 4208107 := bstep (se 1 (by rfl) ⟨3156080, by rfl⟩ : syracuseStep 4208107 = 6312161) B6312161
theorem B10786375 : Blo 1166400 10786375 := bstep (se 1 (by rfl) ⟨8089781, by rfl⟩ : syracuseStep 10786375 = 16179563) B16179563
theorem B12613249 : Blo 1166400 12613249 := bstep (se 2 (by rfl) ⟨4729968, by rfl⟩ : syracuseStep 12613249 = 9459937) B9459937
theorem B2627279 : Blo 1166400 2627279 := bstep (se 1 (by rfl) ⟨1970459, by rfl⟩ : syracuseStep 2627279 = 3940919) B3940919
theorem B8861723 : Blo 1166400 8861723 := bstep (se 1 (by rfl) ⟨6646292, by rfl⟩ : syracuseStep 8861723 = 13292585) B13292585
theorem B2627711 : Blo 1166400 2627711 := bstep (se 1 (by rfl) ⟨1970783, by rfl⟩ : syracuseStep 2627711 = 3941567) B3941567
theorem B37837151 : Blo 1166400 37837151 := bstep (se 1 (by rfl) ⟨28377863, by rfl⟩ : syracuseStep 37837151 = 56755727) B56755727
theorem B3324331 : Blo 1166400 3324331 := bstep (se 1 (by rfl) ⟨2493248, by rfl⟩ : syracuseStep 3324331 = 4986497) B4986497
theorem B4430315 : Blo 1166400 4430315 := bstep (se 1 (by rfl) ⟨3322736, by rfl⟩ : syracuseStep 4430315 = 6645473) B6645473
theorem B3938921 : Blo 1166400 3938921 := bstep (se 2 (by rfl) ⟨1477095, by rfl⟩ : syracuseStep 3938921 = 2954191) B2954191
theorem B1751663 : Blo 1166400 1751663 := bstep (se 1 (by rfl) ⟨1313747, by rfl⟩ : syracuseStep 1751663 = 2627495) B2627495
theorem B1751759 : Blo 1166400 1751759 := bstep (se 1 (by rfl) ⟨1313819, by rfl⟩ : syracuseStep 1751759 = 2627639) B2627639
theorem B19962935 : Blo 1166400 19962935 := bstep (se 1 (by rfl) ⟨14972201, by rfl⟩ : syracuseStep 19962935 = 29944403) B29944403
theorem B3939515 : Blo 1166400 3939515 := bstep (se 1 (by rfl) ⟨2954636, by rfl⟩ : syracuseStep 3939515 = 5909273) B5909273
theorem B20217563 : Blo 1166400 20217563 := bstep (se 1 (by rfl) ⟨15163172, by rfl⟩ : syracuseStep 20217563 = 30326345) B30326345
theorem B4431743 : Blo 1166400 4431743 := bstep (se 1 (by rfl) ⟨3323807, by rfl⟩ : syracuseStep 4431743 = 6647615) B6647615
theorem B17301995 : Blo 1166400 17301995 := bstep (se 1 (by rfl) ⟨12976496, by rfl⟩ : syracuseStep 17301995 = 25952993) B25952993
theorem B4432441 : Blo 1166400 4432441 := bstep (se 2 (by rfl) ⟨1662165, by rfl⟩ : syracuseStep 4432441 = 3324331) B3324331
theorem B11224079 : Blo 1166400 11224079 := bstep (se 1 (by rfl) ⟨8418059, by rfl⟩ : syracuseStep 11224079 = 16836119) B16836119
theorem B5907815 : Blo 1166400 5907815 := bstep (se 1 (by rfl) ⟨4430861, by rfl⟩ : syracuseStep 5907815 = 8861723) B8861723
theorem B25224767 : Blo 1166400 25224767 := bstep (se 1 (by rfl) ⟨18918575, by rfl⟩ : syracuseStep 25224767 = 37837151) B37837151
theorem B28804895 : Blo 1166400 28804895 := bstep (se 1 (by rfl) ⟨21603671, by rfl⟩ : syracuseStep 28804895 = 43207343) B43207343
theorem B1313095 : Blo 1166400 1313095 := bstep (se 1 (by rfl) ⟨984821, by rfl⟩ : syracuseStep 1313095 = 1969643) B1969643
theorem B13478375 : Blo 1166400 13478375 := bstep (se 1 (by rfl) ⟨10108781, by rfl⟩ : syracuseStep 13478375 = 20217563) B20217563
theorem B1313563 : Blo 1166400 1313563 := bstep (se 1 (by rfl) ⟨985172, by rfl⟩ : syracuseStep 1313563 = 1970345) B1970345
theorem B3156947 : Blo 1166400 3156947 := bstep (se 1 (by rfl) ⟨2367710, by rfl⟩ : syracuseStep 3156947 = 4735421) B4735421
theorem B1166427 : Blo 1166400 1166427 := bstep (se 1 (by rfl) ⟨874820, by rfl⟩ : syracuseStep 1166427 = 1749641) B1749641
theorem B1166751 : Blo 1166400 1166751 := bstep (se 1 (by rfl) ⟨875063, by rfl⟩ : syracuseStep 1166751 = 1750127) B1750127
theorem B2624939 : Blo 1166400 2624939 := bstep (se 1 (by rfl) ⟨1968704, by rfl⟩ : syracuseStep 2624939 = 3937409) B3937409
theorem B2494633 : Blo 1166400 2494633 := bstep (se 2 (by rfl) ⟨935487, by rfl⟩ : syracuseStep 2494633 = 1870975) B1870975
theorem B2953543 : Blo 1166400 2953543 := bstep (se 1 (by rfl) ⟨2215157, by rfl⟩ : syracuseStep 2953543 = 4430315) B4430315
theorem B2625947 : Blo 1166400 2625947 := bstep (se 1 (by rfl) ⟨1969460, by rfl⟩ : syracuseStep 2625947 = 3938921) B3938921
theorem B1167775 : Blo 1166400 1167775 := bstep (se 1 (by rfl) ⟨875831, by rfl⟩ : syracuseStep 1167775 = 1751663) B1751663
theorem B1167839 : Blo 1166400 1167839 := bstep (se 1 (by rfl) ⟨875879, by rfl⟩ : syracuseStep 1167839 = 1751759) B1751759
theorem B13308623 : Blo 1166400 13308623 := bstep (se 1 (by rfl) ⟨9981467, by rfl⟩ : syracuseStep 13308623 = 19962935) B19962935
theorem B14381833 : Blo 1166400 14381833 := bstep (se 2 (by rfl) ⟨5393187, by rfl⟩ : syracuseStep 14381833 = 10786375) B10786375
theorem B2626343 : Blo 1166400 2626343 := bstep (se 1 (by rfl) ⟨1969757, by rfl⟩ : syracuseStep 2626343 = 3939515) B3939515
theorem B63943505 : Blo 1166400 63943505 := bstep (se 2 (by rfl) ⟨23978814, by rfl⟩ : syracuseStep 63943505 = 47957629) B47957629
theorem B1750175 : Blo 1166400 1750175 := bstep (se 1 (by rfl) ⟨1312631, by rfl⟩ : syracuseStep 1750175 = 2625263) B2625263
theorem B4429025 : Blo 1166400 4429025 := bstep (se 2 (by rfl) ⟨1660884, by rfl⟩ : syracuseStep 4429025 = 3321769) B3321769
theorem B2954495 : Blo 1166400 2954495 := bstep (se 1 (by rfl) ⟨2215871, by rfl⟩ : syracuseStep 2954495 = 4431743) B4431743
theorem B11228537 : Blo 1166400 11228537 := bstep (se 2 (by rfl) ⟨4210701, by rfl⟩ : syracuseStep 11228537 = 8421403) B8421403
theorem B3323375 : Blo 1166400 3323375 := bstep (se 1 (by rfl) ⟨2492531, by rfl⟩ : syracuseStep 3323375 = 4985063) B4985063
theorem B3938219 : Blo 1166400 3938219 := bstep (se 1 (by rfl) ⟨2953664, by rfl⟩ : syracuseStep 3938219 = 5907329) B5907329
theorem B1751279 : Blo 1166400 1751279 := bstep (se 1 (by rfl) ⟨1313459, by rfl⟩ : syracuseStep 1751279 = 2626919) B2626919
theorem B1751519 : Blo 1166400 1751519 := bstep (se 1 (by rfl) ⟨1313639, by rfl⟩ : syracuseStep 1751519 = 2627279) B2627279
theorem B1751807 : Blo 1166400 1751807 := bstep (se 1 (by rfl) ⟨1313855, by rfl⟩ : syracuseStep 1751807 = 2627711) B2627711
theorem B5913809 : Blo 1166400 5913809 := bstep (se 2 (by rfl) ⟨2217678, by rfl⟩ : syracuseStep 5913809 = 4435357) B4435357
theorem B5610809 : Blo 1166400 5610809 := bstep (se 2 (by rfl) ⟨2104053, by rfl⟩ : syracuseStep 5610809 = 4208107) B4208107
theorem B16817665 : Blo 1166400 16817665 := bstep (se 2 (by rfl) ⟨6306624, by rfl⟩ : syracuseStep 16817665 = 12613249) B12613249
theorem B8871443 : Blo 1166400 8871443 := bstep (se 1 (by rfl) ⟨6653582, by rfl⟩ : syracuseStep 8871443 = 13307165) B13307165
theorem B5906195 : Blo 1166400 5906195 := bstep (se 1 (by rfl) ⟨4429646, by rfl⟩ : syracuseStep 5906195 = 8859293) B8859293
theorem B3326177 : Blo 1166400 3326177 := bstep (se 2 (by rfl) ⟨1247316, by rfl⟩ : syracuseStep 3326177 = 2494633) B2494633
theorem B11534663 : Blo 1166400 11534663 := bstep (se 1 (by rfl) ⟨8650997, by rfl⟩ : syracuseStep 11534663 = 17301995) B17301995
theorem B8872415 : Blo 1166400 8872415 := bstep (se 1 (by rfl) ⟨6654311, by rfl⟩ : syracuseStep 8872415 = 13308623) B13308623
theorem B19203263 : Blo 1166400 19203263 := bstep (se 1 (by rfl) ⟨14402447, by rfl⟩ : syracuseStep 19203263 = 28804895) B28804895
theorem B22423553 : Blo 1166400 22423553 := bstep (se 2 (by rfl) ⟨8408832, by rfl⟩ : syracuseStep 22423553 = 16817665) B16817665
theorem B3942539 : Blo 1166400 3942539 := bstep (se 1 (by rfl) ⟨2956904, by rfl⟩ : syracuseStep 3942539 = 5913809) B5913809
theorem B7482719 : Blo 1166400 7482719 := bstep (se 1 (by rfl) ⟨5612039, by rfl⟩ : syracuseStep 7482719 = 11224079) B11224079
theorem B5909921 : Blo 1166400 5909921 := bstep (se 2 (by rfl) ⟨2216220, by rfl⟩ : syracuseStep 5909921 = 4432441) B4432441
theorem B1166783 : Blo 1166400 1166783 := bstep (se 1 (by rfl) ⟨875087, by rfl⟩ : syracuseStep 1166783 = 1750175) B1750175
theorem B2952683 : Blo 1166400 2952683 := bstep (se 1 (by rfl) ⟨2214512, by rfl⟩ : syracuseStep 2952683 = 4429025) B4429025
theorem B14962157 : Blo 1166400 14962157 := bstep (se 3 (by rfl) ⟨2805404, by rfl⟩ : syracuseStep 14962157 = 5610809) B5610809
theorem B1969663 : Blo 1166400 1969663 := bstep (se 1 (by rfl) ⟨1477247, by rfl⟩ : syracuseStep 1969663 = 2954495) B2954495
theorem B2215583 : Blo 1166400 2215583 := bstep (se 1 (by rfl) ⟨1661687, by rfl⟩ : syracuseStep 2215583 = 3323375) B3323375
theorem B2625479 : Blo 1166400 2625479 := bstep (se 1 (by rfl) ⟨1969109, by rfl⟩ : syracuseStep 2625479 = 3938219) B3938219
theorem B1167519 : Blo 1166400 1167519 := bstep (se 1 (by rfl) ⟨875639, by rfl⟩ : syracuseStep 1167519 = 1751279) B1751279
theorem B1167679 : Blo 1166400 1167679 := bstep (se 1 (by rfl) ⟨875759, by rfl⟩ : syracuseStep 1167679 = 1751519) B1751519
theorem B1167871 : Blo 1166400 1167871 := bstep (se 1 (by rfl) ⟨875903, by rfl⟩ : syracuseStep 1167871 = 1751807) B1751807
theorem B1749959 : Blo 1166400 1749959 := bstep (se 1 (by rfl) ⟨1312469, by rfl⟩ : syracuseStep 1749959 = 2624939) B2624939
theorem B3937463 : Blo 1166400 3937463 := bstep (se 1 (by rfl) ⟨2953097, by rfl⟩ : syracuseStep 3937463 = 5906195) B5906195
theorem B1750631 : Blo 1166400 1750631 := bstep (se 1 (by rfl) ⟨1312973, by rfl⟩ : syracuseStep 1750631 = 2625947) B2625947
theorem B3938057 : Blo 1166400 3938057 := bstep (se 2 (by rfl) ⟨1476771, by rfl⟩ : syracuseStep 3938057 = 2953543) B2953543
theorem B1750793 : Blo 1166400 1750793 := bstep (se 2 (by rfl) ⟨656547, by rfl⟩ : syracuseStep 1750793 = 1313095) B1313095
theorem B1750895 : Blo 1166400 1750895 := bstep (se 1 (by rfl) ⟨1313171, by rfl⟩ : syracuseStep 1750895 = 2626343) B2626343
theorem B42629003 : Blo 1166400 42629003 := bstep (se 1 (by rfl) ⟨31971752, by rfl⟩ : syracuseStep 42629003 = 63943505) B63943505
theorem B3938543 : Blo 1166400 3938543 := bstep (se 1 (by rfl) ⟨2953907, by rfl⟩ : syracuseStep 3938543 = 5907815) B5907815
theorem B7485691 : Blo 1166400 7485691 := bstep (se 1 (by rfl) ⟨5614268, by rfl⟩ : syracuseStep 7485691 = 11228537) B11228537
theorem B19175777 : Blo 1166400 19175777 := bstep (se 2 (by rfl) ⟨7190916, by rfl⟩ : syracuseStep 19175777 = 14381833) B14381833
theorem B1751417 : Blo 1166400 1751417 := bstep (se 2 (by rfl) ⟨656781, by rfl⟩ : syracuseStep 1751417 = 1313563) B1313563
theorem B16816511 : Blo 1166400 16816511 := bstep (se 1 (by rfl) ⟨12612383, by rfl⟩ : syracuseStep 16816511 = 25224767) B25224767
theorem B8985583 : Blo 1166400 8985583 := bstep (se 1 (by rfl) ⟨6739187, by rfl⟩ : syracuseStep 8985583 = 13478375) B13478375
theorem B2104631 : Blo 1166400 2104631 := bstep (se 1 (by rfl) ⟨1578473, by rfl⟩ : syracuseStep 2104631 = 3156947) B3156947
theorem B5914295 : Blo 1166400 5914295 := bstep (se 1 (by rfl) ⟨4435721, by rfl⟩ : syracuseStep 5914295 = 8871443) B8871443
theorem B5914943 : Blo 1166400 5914943 := bstep (se 1 (by rfl) ⟨4436207, by rfl⟩ : syracuseStep 5914943 = 8872415) B8872415
theorem B28419335 : Blo 1166400 28419335 := bstep (se 1 (by rfl) ⟨21314501, by rfl⟩ : syracuseStep 28419335 = 42629003) B42629003
theorem B1403087 : Blo 1166400 1403087 := bstep (se 1 (by rfl) ⟨1052315, by rfl⟩ : syracuseStep 1403087 = 2104631) B2104631
theorem B1968455 : Blo 1166400 1968455 := bstep (se 1 (by rfl) ⟨1476341, by rfl⟩ : syracuseStep 1968455 = 2952683) B2952683
theorem B1477055 : Blo 1166400 1477055 := bstep (se 1 (by rfl) ⟨1107791, by rfl⟩ : syracuseStep 1477055 = 2215583) B2215583
theorem B3942863 : Blo 1166400 3942863 := bstep (se 1 (by rfl) ⟨2957147, by rfl⟩ : syracuseStep 3942863 = 5914295) B5914295
theorem B9980921 : Blo 1166400 9980921 := bstep (se 2 (by rfl) ⟨3742845, by rfl⟩ : syracuseStep 9980921 = 7485691) B7485691
theorem B1166639 : Blo 1166400 1166639 := bstep (se 1 (by rfl) ⟨874979, by rfl⟩ : syracuseStep 1166639 = 1749959) B1749959
theorem B2624975 : Blo 1166400 2624975 := bstep (se 1 (by rfl) ⟨1968731, by rfl⟩ : syracuseStep 2624975 = 3937463) B3937463
theorem B1167087 : Blo 1166400 1167087 := bstep (se 1 (by rfl) ⟨875315, by rfl⟩ : syracuseStep 1167087 = 1750631) B1750631
theorem B2625371 : Blo 1166400 2625371 := bstep (se 1 (by rfl) ⟨1969028, by rfl⟩ : syracuseStep 2625371 = 3938057) B3938057
theorem B1167195 : Blo 1166400 1167195 := bstep (se 1 (by rfl) ⟨875396, by rfl⟩ : syracuseStep 1167195 = 1750793) B1750793
theorem B1167263 : Blo 1166400 1167263 := bstep (se 1 (by rfl) ⟨875447, by rfl⟩ : syracuseStep 1167263 = 1750895) B1750895
theorem B2625695 : Blo 1166400 2625695 := bstep (se 1 (by rfl) ⟨1969271, by rfl⟩ : syracuseStep 2625695 = 3938543) B3938543
theorem B12783851 : Blo 1166400 12783851 := bstep (se 1 (by rfl) ⟨9587888, by rfl⟩ : syracuseStep 12783851 = 19175777) B19175777
theorem B1167611 : Blo 1166400 1167611 := bstep (se 1 (by rfl) ⟨875708, by rfl⟩ : syracuseStep 1167611 = 1751417) B1751417
theorem B11211007 : Blo 1166400 11211007 := bstep (se 1 (by rfl) ⟨8408255, by rfl⟩ : syracuseStep 11211007 = 16816511) B16816511
theorem B2626217 : Blo 1166400 2626217 := bstep (se 2 (by rfl) ⟨984831, by rfl⟩ : syracuseStep 2626217 = 1969663) B1969663
theorem B9974771 : Blo 1166400 9974771 := bstep (se 1 (by rfl) ⟨7481078, by rfl⟩ : syracuseStep 9974771 = 14962157) B14962157
theorem B1750319 : Blo 1166400 1750319 := bstep (se 1 (by rfl) ⟨1312739, by rfl⟩ : syracuseStep 1750319 = 2625479) B2625479
theorem B2217451 : Blo 1166400 2217451 := bstep (se 1 (by rfl) ⟨1663088, by rfl⟩ : syracuseStep 2217451 = 3326177) B3326177
theorem B7689775 : Blo 1166400 7689775 := bstep (se 1 (by rfl) ⟨5767331, by rfl⟩ : syracuseStep 7689775 = 11534663) B11534663
theorem B12802175 : Blo 1166400 12802175 := bstep (se 1 (by rfl) ⟨9601631, by rfl⟩ : syracuseStep 12802175 = 19203263) B19203263
theorem B14949035 : Blo 1166400 14949035 := bstep (se 1 (by rfl) ⟨11211776, by rfl⟩ : syracuseStep 14949035 = 22423553) B22423553
theorem B2628359 : Blo 1166400 2628359 := bstep (se 1 (by rfl) ⟨1971269, by rfl⟩ : syracuseStep 2628359 = 3942539) B3942539
theorem B4988479 : Blo 1166400 4988479 := bstep (se 1 (by rfl) ⟨3741359, by rfl⟩ : syracuseStep 4988479 = 7482719) B7482719
theorem B3939947 : Blo 1166400 3939947 := bstep (se 1 (by rfl) ⟨2954960, by rfl⟩ : syracuseStep 3939947 = 5909921) B5909921
theorem B47923109 : Blo 1166400 47923109 := bstep (se 4 (by rfl) ⟨4492791, by rfl⟩ : syracuseStep 47923109 = 8985583) B8985583
theorem B1312303 : Blo 1166400 1312303 := bstep (se 1 (by rfl) ⟨984227, by rfl⟩ : syracuseStep 1312303 = 1968455) B1968455
theorem B6653947 : Blo 1166400 6653947 := bstep (se 1 (by rfl) ⟨4990460, by rfl⟩ : syracuseStep 6653947 = 9980921) B9980921
theorem B8522567 : Blo 1166400 8522567 := bstep (se 1 (by rfl) ⟨6391925, by rfl⟩ : syracuseStep 8522567 = 12783851) B12783851
theorem B3943295 : Blo 1166400 3943295 := bstep (se 1 (by rfl) ⟨2957471, by rfl⟩ : syracuseStep 3943295 = 5914943) B5914943
theorem B1166879 : Blo 1166400 1166879 := bstep (se 1 (by rfl) ⟨875159, by rfl⟩ : syracuseStep 1166879 = 1750319) B1750319
theorem B9966023 : Blo 1166400 9966023 := bstep (se 1 (by rfl) ⟨7474517, by rfl⟩ : syracuseStep 9966023 = 14949035) B14949035
theorem B10253033 : Blo 1166400 10253033 := bstep (se 2 (by rfl) ⟨3844887, by rfl⟩ : syracuseStep 10253033 = 7689775) B7689775
theorem B1749983 : Blo 1166400 1749983 := bstep (se 1 (by rfl) ⟨1312487, by rfl⟩ : syracuseStep 1749983 = 2624975) B2624975
theorem B2626631 : Blo 1166400 2626631 := bstep (se 1 (by rfl) ⟨1969973, by rfl⟩ : syracuseStep 2626631 = 3939947) B3939947
theorem B1750247 : Blo 1166400 1750247 := bstep (se 1 (by rfl) ⟨1312685, by rfl⟩ : syracuseStep 1750247 = 2625371) B2625371
theorem B1750463 : Blo 1166400 1750463 := bstep (se 1 (by rfl) ⟨1312847, by rfl⟩ : syracuseStep 1750463 = 2625695) B2625695
theorem B14948009 : Blo 1166400 14948009 := bstep (se 2 (by rfl) ⟨5605503, by rfl⟩ : syracuseStep 14948009 = 11211007) B11211007
theorem B1750811 : Blo 1166400 1750811 := bstep (se 1 (by rfl) ⟨1313108, by rfl⟩ : syracuseStep 1750811 = 2626217) B2626217
theorem B3741565 : Blo 1166400 3741565 := bstep (se 3 (by rfl) ⟨701543, by rfl⟩ : syracuseStep 3741565 = 1403087) B1403087
theorem B6649847 : Blo 1166400 6649847 := bstep (se 1 (by rfl) ⟨4987385, by rfl⟩ : syracuseStep 6649847 = 9974771) B9974771
theorem B18946223 : Blo 1166400 18946223 := bstep (se 1 (by rfl) ⟨14209667, by rfl⟩ : syracuseStep 18946223 = 28419335) B28419335
theorem B3938813 : Blo 1166400 3938813 := bstep (se 3 (by rfl) ⟨738527, by rfl⟩ : syracuseStep 3938813 = 1477055) B1477055
theorem B8534783 : Blo 1166400 8534783 := bstep (se 1 (by rfl) ⟨6401087, by rfl⟩ : syracuseStep 8534783 = 12802175) B12802175
theorem B2628575 : Blo 1166400 2628575 := bstep (se 1 (by rfl) ⟨1971431, by rfl⟩ : syracuseStep 2628575 = 3942863) B3942863
theorem B1752239 : Blo 1166400 1752239 := bstep (se 1 (by rfl) ⟨1314179, by rfl⟩ : syracuseStep 1752239 = 2628359) B2628359
theorem B2956601 : Blo 1166400 2956601 := bstep (se 2 (by rfl) ⟨1108725, by rfl⟩ : syracuseStep 2956601 = 2217451) B2217451
theorem B6651305 : Blo 1166400 6651305 := bstep (se 2 (by rfl) ⟨2494239, by rfl⟩ : syracuseStep 6651305 = 4988479) B4988479
theorem B31948739 : Blo 1166400 31948739 := bstep (se 1 (by rfl) ⟨23961554, by rfl⟩ : syracuseStep 31948739 = 47923109) B47923109
theorem B6644015 : Blo 1166400 6644015 := bstep (se 1 (by rfl) ⟨4983011, by rfl⟩ : syracuseStep 6644015 = 9966023) B9966023
theorem B4433231 : Blo 1166400 4433231 := bstep (se 1 (by rfl) ⟨3324923, by rfl⟩ : syracuseStep 4433231 = 6649847) B6649847
theorem B4434203 : Blo 1166400 4434203 := bstep (se 1 (by rfl) ⟨3325652, by rfl⟩ : syracuseStep 4434203 = 6651305) B6651305
theorem B6835355 : Blo 1166400 6835355 := bstep (se 1 (by rfl) ⟨5126516, by rfl⟩ : syracuseStep 6835355 = 10253033) B10253033
theorem B1166655 : Blo 1166400 1166655 := bstep (se 1 (by rfl) ⟨874991, by rfl⟩ : syracuseStep 1166655 = 1749983) B1749983
theorem B1166831 : Blo 1166400 1166831 := bstep (se 1 (by rfl) ⟨875123, by rfl⟩ : syracuseStep 1166831 = 1750247) B1750247
theorem B1166975 : Blo 1166400 1166975 := bstep (se 1 (by rfl) ⟨875231, by rfl⟩ : syracuseStep 1166975 = 1750463) B1750463
theorem B9965339 : Blo 1166400 9965339 := bstep (se 1 (by rfl) ⟨7474004, by rfl⟩ : syracuseStep 9965339 = 14948009) B14948009
theorem B1167207 : Blo 1166400 1167207 := bstep (se 1 (by rfl) ⟨875405, by rfl⟩ : syracuseStep 1167207 = 1750811) B1750811
theorem B2625875 : Blo 1166400 2625875 := bstep (se 1 (by rfl) ⟨1969406, by rfl⟩ : syracuseStep 2625875 = 3938813) B3938813
theorem B5689855 : Blo 1166400 5689855 := bstep (se 1 (by rfl) ⟨4267391, by rfl⟩ : syracuseStep 5689855 = 8534783) B8534783
theorem B5681711 : Blo 1166400 5681711 := bstep (se 1 (by rfl) ⟨4261283, by rfl⟩ : syracuseStep 5681711 = 8522567) B8522567
theorem B1749737 : Blo 1166400 1749737 := bstep (se 2 (by rfl) ⟨656151, by rfl⟩ : syracuseStep 1749737 = 1312303) B1312303
theorem B1168159 : Blo 1166400 1168159 := bstep (se 1 (by rfl) ⟨876119, by rfl⟩ : syracuseStep 1168159 = 1752239) B1752239
theorem B1971067 : Blo 1166400 1971067 := bstep (se 1 (by rfl) ⟨1478300, by rfl⟩ : syracuseStep 1971067 = 2956601) B2956601
theorem B1751087 : Blo 1166400 1751087 := bstep (se 1 (by rfl) ⟨1313315, by rfl⟩ : syracuseStep 1751087 = 2626631) B2626631
theorem B12630815 : Blo 1166400 12630815 := bstep (se 1 (by rfl) ⟨9473111, by rfl⟩ : syracuseStep 12630815 = 18946223) B18946223
theorem B2628863 : Blo 1166400 2628863 := bstep (se 1 (by rfl) ⟨1971647, by rfl⟩ : syracuseStep 2628863 = 3943295) B3943295
theorem B1752383 : Blo 1166400 1752383 := bstep (se 1 (by rfl) ⟨1314287, by rfl⟩ : syracuseStep 1752383 = 2628575) B2628575
theorem B4988753 : Blo 1166400 4988753 := bstep (se 2 (by rfl) ⟨1870782, by rfl⟩ : syracuseStep 4988753 = 3741565) B3741565
theorem B21299159 : Blo 1166400 21299159 := bstep (se 1 (by rfl) ⟨15974369, by rfl⟩ : syracuseStep 21299159 = 31948739) B31948739
theorem B8871929 : Blo 1166400 8871929 := bstep (se 2 (by rfl) ⟨3326973, by rfl⟩ : syracuseStep 8871929 = 6653947) B6653947
theorem B7586473 : Blo 1166400 7586473 := bstep (se 2 (by rfl) ⟨2844927, by rfl⟩ : syracuseStep 7586473 = 5689855) B5689855
theorem B4556903 : Blo 1166400 4556903 := bstep (se 1 (by rfl) ⟨3417677, by rfl⟩ : syracuseStep 4556903 = 6835355) B6835355
theorem B56797757 : Blo 1166400 56797757 := bstep (se 3 (by rfl) ⟨10649579, by rfl⟩ : syracuseStep 56797757 = 21299159) B21299159
theorem B3787807 : Blo 1166400 3787807 := bstep (se 1 (by rfl) ⟨2840855, by rfl⟩ : syracuseStep 3787807 = 5681711) B5681711
theorem B1166491 : Blo 1166400 1166491 := bstep (se 1 (by rfl) ⟨874868, by rfl⟩ : syracuseStep 1166491 = 1749737) B1749737
theorem B1167391 : Blo 1166400 1167391 := bstep (se 1 (by rfl) ⟨875543, by rfl⟩ : syracuseStep 1167391 = 1751087) B1751087
theorem B1168255 : Blo 1166400 1168255 := bstep (se 1 (by rfl) ⟨876191, by rfl⟩ : syracuseStep 1168255 = 1752383) B1752383
theorem B4429343 : Blo 1166400 4429343 := bstep (se 1 (by rfl) ⟨3322007, by rfl⟩ : syracuseStep 4429343 = 6644015) B6644015
theorem B1750583 : Blo 1166400 1750583 := bstep (se 1 (by rfl) ⟨1312937, by rfl⟩ : syracuseStep 1750583 = 2625875) B2625875
theorem B2955487 : Blo 1166400 2955487 := bstep (se 1 (by rfl) ⟨2216615, by rfl⟩ : syracuseStep 2955487 = 4433231) B4433231
theorem B2628089 : Blo 1166400 2628089 := bstep (se 2 (by rfl) ⟨985533, by rfl⟩ : syracuseStep 2628089 = 1971067) B1971067
theorem B2956135 : Blo 1166400 2956135 := bstep (se 1 (by rfl) ⟨2217101, by rfl⟩ : syracuseStep 2956135 = 4434203) B4434203
theorem B8420543 : Blo 1166400 8420543 := bstep (se 1 (by rfl) ⟨6315407, by rfl⟩ : syracuseStep 8420543 = 12630815) B12630815
theorem B1752575 : Blo 1166400 1752575 := bstep (se 1 (by rfl) ⟨1314431, by rfl⟩ : syracuseStep 1752575 = 2628863) B2628863
theorem B6643559 : Blo 1166400 6643559 := bstep (se 1 (by rfl) ⟨4982669, by rfl⟩ : syracuseStep 6643559 = 9965339) B9965339
theorem B3325835 : Blo 1166400 3325835 := bstep (se 1 (by rfl) ⟨2494376, by rfl⟩ : syracuseStep 3325835 = 4988753) B4988753
theorem B5914619 : Blo 1166400 5914619 := bstep (se 1 (by rfl) ⟨4435964, by rfl⟩ : syracuseStep 5914619 = 8871929) B8871929
theorem B3940649 : Blo 1166400 3940649 := bstep (se 2 (by rfl) ⟨1477743, by rfl⟩ : syracuseStep 3940649 = 2955487) B2955487
theorem B3941513 : Blo 1166400 3941513 := bstep (se 2 (by rfl) ⟨1478067, by rfl⟩ : syracuseStep 3941513 = 2956135) B2956135
theorem B37865171 : Blo 1166400 37865171 := bstep (se 1 (by rfl) ⟨28398878, by rfl⟩ : syracuseStep 37865171 = 56797757) B56797757
theorem B5613695 : Blo 1166400 5613695 := bstep (se 1 (by rfl) ⟨4210271, by rfl⟩ : syracuseStep 5613695 = 8420543) B8420543
theorem B3943079 : Blo 1166400 3943079 := bstep (se 1 (by rfl) ⟨2957309, by rfl⟩ : syracuseStep 3943079 = 5914619) B5914619
theorem B2952895 : Blo 1166400 2952895 := bstep (se 1 (by rfl) ⟨2214671, by rfl⟩ : syracuseStep 2952895 = 4429343) B4429343
theorem B1167055 : Blo 1166400 1167055 := bstep (se 1 (by rfl) ⟨875291, by rfl⟩ : syracuseStep 1167055 = 1750583) B1750583
theorem B48606965 : Blo 1166400 48606965 := bstep (se 5 (by rfl) ⟨2278451, by rfl⟩ : syracuseStep 48606965 = 4556903) B4556903
theorem B5050409 : Blo 1166400 5050409 := bstep (se 2 (by rfl) ⟨1893903, by rfl⟩ : syracuseStep 5050409 = 3787807) B3787807
theorem B1168383 : Blo 1166400 1168383 := bstep (se 1 (by rfl) ⟨876287, by rfl⟩ : syracuseStep 1168383 = 1752575) B1752575
theorem B4429039 : Blo 1166400 4429039 := bstep (se 1 (by rfl) ⟨3321779, by rfl⟩ : syracuseStep 4429039 = 6643559) B6643559
theorem B2217223 : Blo 1166400 2217223 := bstep (se 1 (by rfl) ⟨1662917, by rfl⟩ : syracuseStep 2217223 = 3325835) B3325835
theorem B10115297 : Blo 1166400 10115297 := bstep (se 2 (by rfl) ⟨3793236, by rfl⟩ : syracuseStep 10115297 = 7586473) B7586473
theorem B1752059 : Blo 1166400 1752059 := bstep (se 1 (by rfl) ⟨1314044, by rfl⟩ : syracuseStep 1752059 = 2628089) B2628089
theorem B13467757 : Blo 1166400 13467757 := bstep (se 3 (by rfl) ⟨2525204, by rfl⟩ : syracuseStep 13467757 = 5050409) B5050409
theorem B6743531 : Blo 1166400 6743531 := bstep (se 1 (by rfl) ⟨5057648, by rfl⟩ : syracuseStep 6743531 = 10115297) B10115297
theorem B1168039 : Blo 1166400 1168039 := bstep (se 1 (by rfl) ⟨876029, by rfl⟩ : syracuseStep 1168039 = 1752059) B1752059
theorem B3937193 : Blo 1166400 3937193 := bstep (se 2 (by rfl) ⟨1476447, by rfl⟩ : syracuseStep 3937193 = 2952895) B2952895
theorem B32404643 : Blo 1166400 32404643 := bstep (se 1 (by rfl) ⟨24303482, by rfl⟩ : syracuseStep 32404643 = 48606965) B48606965
theorem B2627099 : Blo 1166400 2627099 := bstep (se 1 (by rfl) ⟨1970324, by rfl⟩ : syracuseStep 2627099 = 3940649) B3940649
theorem B2627675 : Blo 1166400 2627675 := bstep (se 1 (by rfl) ⟨1970756, by rfl⟩ : syracuseStep 2627675 = 3941513) B3941513
theorem B3742463 : Blo 1166400 3742463 := bstep (se 1 (by rfl) ⟨2806847, by rfl⟩ : syracuseStep 3742463 = 5613695) B5613695
theorem B5905385 : Blo 1166400 5905385 := bstep (se 2 (by rfl) ⟨2214519, by rfl⟩ : syracuseStep 5905385 = 4429039) B4429039
theorem B2956297 : Blo 1166400 2956297 := bstep (se 2 (by rfl) ⟨1108611, by rfl⟩ : syracuseStep 2956297 = 2217223) B2217223
theorem B2628719 : Blo 1166400 2628719 := bstep (se 1 (by rfl) ⟨1971539, by rfl⟩ : syracuseStep 2628719 = 3943079) B3943079
theorem B100973789 : Blo 1166400 100973789 := bstep (se 3 (by rfl) ⟨18932585, by rfl⟩ : syracuseStep 100973789 = 37865171) B37865171
theorem B17957009 : Blo 1166400 17957009 := bstep (se 2 (by rfl) ⟨6733878, by rfl⟩ : syracuseStep 17957009 = 13467757) B13467757
theorem B21603095 : Blo 1166400 21603095 := bstep (se 1 (by rfl) ⟨16202321, by rfl⟩ : syracuseStep 21603095 = 32404643) B32404643
theorem B17982749 : Blo 1166400 17982749 := bstep (se 3 (by rfl) ⟨3371765, by rfl⟩ : syracuseStep 17982749 = 6743531) B6743531
theorem B3941729 : Blo 1166400 3941729 := bstep (se 2 (by rfl) ⟨1478148, by rfl⟩ : syracuseStep 3941729 = 2956297) B2956297
theorem B67315859 : Blo 1166400 67315859 := bstep (se 1 (by rfl) ⟨50486894, by rfl⟩ : syracuseStep 67315859 = 100973789) B100973789
theorem B2624795 : Blo 1166400 2624795 := bstep (se 1 (by rfl) ⟨1968596, by rfl⟩ : syracuseStep 2624795 = 3937193) B3937193
theorem B2494975 : Blo 1166400 2494975 := bstep (se 1 (by rfl) ⟨1871231, by rfl⟩ : syracuseStep 2494975 = 3742463) B3742463
theorem B3936923 : Blo 1166400 3936923 := bstep (se 1 (by rfl) ⟨2952692, by rfl⟩ : syracuseStep 3936923 = 5905385) B5905385
theorem B1751399 : Blo 1166400 1751399 := bstep (se 1 (by rfl) ⟨1313549, by rfl⟩ : syracuseStep 1751399 = 2627099) B2627099
theorem B1751783 : Blo 1166400 1751783 := bstep (se 1 (by rfl) ⟨1313837, by rfl⟩ : syracuseStep 1751783 = 2627675) B2627675
theorem B1752479 : Blo 1166400 1752479 := bstep (se 1 (by rfl) ⟨1314359, by rfl⟩ : syracuseStep 1752479 = 2628719) B2628719
theorem B14402063 : Blo 1166400 14402063 := bstep (se 1 (by rfl) ⟨10801547, by rfl⟩ : syracuseStep 14402063 = 21603095) B21603095
theorem B3326633 : Blo 1166400 3326633 := bstep (se 2 (by rfl) ⟨1247487, by rfl⟩ : syracuseStep 3326633 = 2494975) B2494975
theorem B44877239 : Blo 1166400 44877239 := bstep (se 1 (by rfl) ⟨33657929, by rfl⟩ : syracuseStep 44877239 = 67315859) B67315859
theorem B47885357 : Blo 1166400 47885357 := bstep (se 3 (by rfl) ⟨8978504, by rfl⟩ : syracuseStep 47885357 = 17957009) B17957009
theorem B2624615 : Blo 1166400 2624615 := bstep (se 1 (by rfl) ⟨1968461, by rfl⟩ : syracuseStep 2624615 = 3936923) B3936923
theorem B11988499 : Blo 1166400 11988499 := bstep (se 1 (by rfl) ⟨8991374, by rfl⟩ : syracuseStep 11988499 = 17982749) B17982749
theorem B1167599 : Blo 1166400 1167599 := bstep (se 1 (by rfl) ⟨875699, by rfl⟩ : syracuseStep 1167599 = 1751399) B1751399
theorem B1167855 : Blo 1166400 1167855 := bstep (se 1 (by rfl) ⟨875891, by rfl⟩ : syracuseStep 1167855 = 1751783) B1751783
theorem B1749863 : Blo 1166400 1749863 := bstep (se 1 (by rfl) ⟨1312397, by rfl⟩ : syracuseStep 1749863 = 2624795) B2624795
theorem B1168319 : Blo 1166400 1168319 := bstep (se 1 (by rfl) ⟨876239, by rfl⟩ : syracuseStep 1168319 = 1752479) B1752479
theorem B2627819 : Blo 1166400 2627819 := bstep (se 1 (by rfl) ⟨1970864, by rfl⟩ : syracuseStep 2627819 = 3941729) B3941729
theorem B9601375 : Blo 1166400 9601375 := bstep (se 1 (by rfl) ⟨7201031, by rfl⟩ : syracuseStep 9601375 = 14402063) B14402063
theorem B29918159 : Blo 1166400 29918159 := bstep (se 1 (by rfl) ⟨22438619, by rfl⟩ : syracuseStep 29918159 = 44877239) B44877239
theorem B15984665 : Blo 1166400 15984665 := bstep (se 2 (by rfl) ⟨5994249, by rfl⟩ : syracuseStep 15984665 = 11988499) B11988499
theorem B1166575 : Blo 1166400 1166575 := bstep (se 1 (by rfl) ⟨874931, by rfl⟩ : syracuseStep 1166575 = 1749863) B1749863
theorem B1749743 : Blo 1166400 1749743 := bstep (se 1 (by rfl) ⟨1312307, by rfl⟩ : syracuseStep 1749743 = 2624615) B2624615
theorem B2217755 : Blo 1166400 2217755 := bstep (se 1 (by rfl) ⟨1663316, by rfl⟩ : syracuseStep 2217755 = 3326633) B3326633
theorem B1751879 : Blo 1166400 1751879 := bstep (se 1 (by rfl) ⟨1313909, by rfl⟩ : syracuseStep 1751879 = 2627819) B2627819
theorem B31923571 : Blo 1166400 31923571 := bstep (se 1 (by rfl) ⟨23942678, by rfl⟩ : syracuseStep 31923571 = 47885357) B47885357
theorem B1166495 : Blo 1166400 1166495 := bstep (se 1 (by rfl) ⟨874871, by rfl⟩ : syracuseStep 1166495 = 1749743) B1749743
theorem B1478503 : Blo 1166400 1478503 := bstep (se 1 (by rfl) ⟨1108877, by rfl⟩ : syracuseStep 1478503 = 2217755) B2217755
theorem B1167919 : Blo 1166400 1167919 := bstep (se 1 (by rfl) ⟨875939, by rfl⟩ : syracuseStep 1167919 = 1751879) B1751879
theorem B12801833 : Blo 1166400 12801833 := bstep (se 2 (by rfl) ⟨4800687, by rfl⟩ : syracuseStep 12801833 = 9601375) B9601375
theorem B19945439 : Blo 1166400 19945439 := bstep (se 1 (by rfl) ⟨14959079, by rfl⟩ : syracuseStep 19945439 = 29918159) B29918159
theorem B10656443 : Blo 1166400 10656443 := bstep (se 1 (by rfl) ⟨7992332, by rfl⟩ : syracuseStep 10656443 = 15984665) B15984665
theorem B42564761 : Blo 1166400 42564761 := bstep (se 2 (by rfl) ⟨15961785, by rfl⟩ : syracuseStep 42564761 = 31923571) B31923571
theorem B13296959 : Blo 1166400 13296959 := bstep (se 1 (by rfl) ⟨9972719, by rfl⟩ : syracuseStep 13296959 = 19945439) B19945439
theorem B7104295 : Blo 1166400 7104295 := bstep (se 1 (by rfl) ⟨5328221, by rfl⟩ : syracuseStep 7104295 = 10656443) B10656443
theorem B1971337 : Blo 1166400 1971337 := bstep (se 2 (by rfl) ⟨739251, by rfl⟩ : syracuseStep 1971337 = 1478503) B1478503
theorem B8534555 : Blo 1166400 8534555 := bstep (se 1 (by rfl) ⟨6400916, by rfl⟩ : syracuseStep 8534555 = 12801833) B12801833
theorem B28376507 : Blo 1166400 28376507 := bstep (se 1 (by rfl) ⟨21282380, by rfl⟩ : syracuseStep 28376507 = 42564761) B42564761
theorem B8864639 : Blo 1166400 8864639 := bstep (se 1 (by rfl) ⟨6648479, by rfl⟩ : syracuseStep 8864639 = 13296959) B13296959
theorem B18917671 : Blo 1166400 18917671 := bstep (se 1 (by rfl) ⟨14188253, by rfl⟩ : syracuseStep 18917671 = 28376507) B28376507
theorem B9472393 : Blo 1166400 9472393 := bstep (se 2 (by rfl) ⟨3552147, by rfl⟩ : syracuseStep 9472393 = 7104295) B7104295
theorem B5689703 : Blo 1166400 5689703 := bstep (se 1 (by rfl) ⟨4267277, by rfl⟩ : syracuseStep 5689703 = 8534555) B8534555
theorem B2628449 : Blo 1166400 2628449 := bstep (se 2 (by rfl) ⟨985668, by rfl⟩ : syracuseStep 2628449 = 1971337) B1971337
theorem B25223561 : Blo 1166400 25223561 := bstep (se 2 (by rfl) ⟨9458835, by rfl⟩ : syracuseStep 25223561 = 18917671) B18917671
theorem B15172541 : Blo 1166400 15172541 := bstep (se 3 (by rfl) ⟨2844851, by rfl⟩ : syracuseStep 15172541 = 5689703) B5689703
theorem B5909759 : Blo 1166400 5909759 := bstep (se 1 (by rfl) ⟨4432319, by rfl⟩ : syracuseStep 5909759 = 8864639) B8864639
theorem B12629857 : Blo 1166400 12629857 := bstep (se 2 (by rfl) ⟨4736196, by rfl⟩ : syracuseStep 12629857 = 9472393) B9472393
theorem B1752299 : Blo 1166400 1752299 := bstep (se 1 (by rfl) ⟨1314224, by rfl⟩ : syracuseStep 1752299 = 2628449) B2628449
theorem B1168199 : Blo 1166400 1168199 := bstep (se 1 (by rfl) ⟨876149, by rfl⟩ : syracuseStep 1168199 = 1752299) B1752299
theorem B16839809 : Blo 1166400 16839809 := bstep (se 2 (by rfl) ⟨6314928, by rfl⟩ : syracuseStep 16839809 = 12629857) B12629857
theorem B16815707 : Blo 1166400 16815707 := bstep (se 1 (by rfl) ⟨12611780, by rfl⟩ : syracuseStep 16815707 = 25223561) B25223561
theorem B10115027 : Blo 1166400 10115027 := bstep (se 1 (by rfl) ⟨7586270, by rfl⟩ : syracuseStep 10115027 = 15172541) B15172541
theorem B3939839 : Blo 1166400 3939839 := bstep (se 1 (by rfl) ⟨2954879, by rfl⟩ : syracuseStep 3939839 = 5909759) B5909759
theorem B6743351 : Blo 1166400 6743351 := bstep (se 1 (by rfl) ⟨5057513, by rfl⟩ : syracuseStep 6743351 = 10115027) B10115027
theorem B11226539 : Blo 1166400 11226539 := bstep (se 1 (by rfl) ⟨8419904, by rfl⟩ : syracuseStep 11226539 = 16839809) B16839809
theorem B11210471 : Blo 1166400 11210471 := bstep (se 1 (by rfl) ⟨8407853, by rfl⟩ : syracuseStep 11210471 = 16815707) B16815707
theorem B2626559 : Blo 1166400 2626559 := bstep (se 1 (by rfl) ⟨1969919, by rfl⟩ : syracuseStep 2626559 = 3939839) B3939839
theorem B7473647 : Blo 1166400 7473647 := bstep (se 1 (by rfl) ⟨5605235, by rfl⟩ : syracuseStep 7473647 = 11210471) B11210471
theorem B7484359 : Blo 1166400 7484359 := bstep (se 1 (by rfl) ⟨5613269, by rfl⟩ : syracuseStep 7484359 = 11226539) B11226539
theorem B1751039 : Blo 1166400 1751039 := bstep (se 1 (by rfl) ⟨1313279, by rfl⟩ : syracuseStep 1751039 = 2626559) B2626559
theorem B4495567 : Blo 1166400 4495567 := bstep (se 1 (by rfl) ⟨3371675, by rfl⟩ : syracuseStep 4495567 = 6743351) B6743351
theorem B9979145 : Blo 1166400 9979145 := bstep (se 2 (by rfl) ⟨3742179, by rfl⟩ : syracuseStep 9979145 = 7484359) B7484359
theorem B4982431 : Blo 1166400 4982431 := bstep (se 1 (by rfl) ⟨3736823, by rfl⟩ : syracuseStep 4982431 = 7473647) B7473647
theorem B1167359 : Blo 1166400 1167359 := bstep (se 1 (by rfl) ⟨875519, by rfl⟩ : syracuseStep 1167359 = 1751039) B1751039
theorem B5994089 : Blo 1166400 5994089 := bstep (se 2 (by rfl) ⟨2247783, by rfl⟩ : syracuseStep 5994089 = 4495567) B4495567
theorem B6652763 : Blo 1166400 6652763 := bstep (se 1 (by rfl) ⟨4989572, by rfl⟩ : syracuseStep 6652763 = 9979145) B9979145
theorem B3996059 : Blo 1166400 3996059 := bstep (se 1 (by rfl) ⟨2997044, by rfl⟩ : syracuseStep 3996059 = 5994089) B5994089
theorem B6643241 : Blo 1166400 6643241 := bstep (se 2 (by rfl) ⟨2491215, by rfl⟩ : syracuseStep 6643241 = 4982431) B4982431
theorem B4435175 : Blo 1166400 4435175 := bstep (se 1 (by rfl) ⟨3326381, by rfl⟩ : syracuseStep 4435175 = 6652763) B6652763
theorem B4428827 : Blo 1166400 4428827 := bstep (se 1 (by rfl) ⟨3321620, by rfl⟩ : syracuseStep 4428827 = 6643241) B6643241
theorem B10656157 : Blo 1166400 10656157 := bstep (se 3 (by rfl) ⟨1998029, by rfl⟩ : syracuseStep 10656157 = 3996059) B3996059
theorem B14208209 : Blo 1166400 14208209 := bstep (se 2 (by rfl) ⟨5328078, by rfl⟩ : syracuseStep 14208209 = 10656157) B10656157
theorem B2952551 : Blo 1166400 2952551 := bstep (se 1 (by rfl) ⟨2214413, by rfl⟩ : syracuseStep 2952551 = 4428827) B4428827
theorem B2956783 : Blo 1166400 2956783 := bstep (se 1 (by rfl) ⟨2217587, by rfl⟩ : syracuseStep 2956783 = 4435175) B4435175
theorem B3942377 : Blo 1166400 3942377 := bstep (se 2 (by rfl) ⟨1478391, by rfl⟩ : syracuseStep 3942377 = 2956783) B2956783
theorem B9472139 : Blo 1166400 9472139 := bstep (se 1 (by rfl) ⟨7104104, by rfl⟩ : syracuseStep 9472139 = 14208209) B14208209
theorem B1968367 : Blo 1166400 1968367 := bstep (se 1 (by rfl) ⟨1476275, by rfl⟩ : syracuseStep 1968367 = 2952551) B2952551
theorem B2624489 : Blo 1166400 2624489 := bstep (se 2 (by rfl) ⟨984183, by rfl⟩ : syracuseStep 2624489 = 1968367) B1968367
theorem B2628251 : Blo 1166400 2628251 := bstep (se 1 (by rfl) ⟨1971188, by rfl⟩ : syracuseStep 2628251 = 3942377) B3942377
theorem B6314759 : Blo 1166400 6314759 := bstep (se 1 (by rfl) ⟨4736069, by rfl⟩ : syracuseStep 6314759 = 9472139) B9472139
theorem B1749659 : Blo 1166400 1749659 := bstep (se 1 (by rfl) ⟨1312244, by rfl⟩ : syracuseStep 1749659 = 2624489) B2624489
theorem B1752167 : Blo 1166400 1752167 := bstep (se 1 (by rfl) ⟨1314125, by rfl⟩ : syracuseStep 1752167 = 2628251) B2628251
theorem B4209839 : Blo 1166400 4209839 := bstep (se 1 (by rfl) ⟨3157379, by rfl⟩ : syracuseStep 4209839 = 6314759) B6314759
theorem B1166439 : Blo 1166400 1166439 := bstep (se 1 (by rfl) ⟨874829, by rfl⟩ : syracuseStep 1166439 = 1749659) B1749659
theorem B1168111 : Blo 1166400 1168111 := bstep (se 1 (by rfl) ⟨876083, by rfl⟩ : syracuseStep 1168111 = 1752167) B1752167
theorem B2806559 : Blo 1166400 2806559 := bstep (se 1 (by rfl) ⟨2104919, by rfl⟩ : syracuseStep 2806559 = 4209839) B4209839
theorem B1871039 : Blo 1166400 1871039 := bstep (se 1 (by rfl) ⟨1403279, by rfl⟩ : syracuseStep 1871039 = 2806559) B2806559
theorem B4989437 : Blo 1166400 4989437 := bstep (se 3 (by rfl) ⟨935519, by rfl⟩ : syracuseStep 4989437 = 1871039) B1871039
theorem B3326291 : Blo 1166400 3326291 := bstep (se 1 (by rfl) ⟨2494718, by rfl⟩ : syracuseStep 3326291 = 4989437) B4989437
theorem B2217527 : Blo 1166400 2217527 := bstep (se 1 (by rfl) ⟨1663145, by rfl⟩ : syracuseStep 2217527 = 3326291) B3326291
theorem B1478351 : Blo 1166400 1478351 := bstep (se 1 (by rfl) ⟨1108763, by rfl⟩ : syracuseStep 1478351 = 2217527) B2217527
theorem B3942269 : Blo 1166400 3942269 := bstep (se 3 (by rfl) ⟨739175, by rfl⟩ : syracuseStep 3942269 = 1478351) B1478351
theorem B2628179 : Blo 1166400 2628179 := bstep (se 1 (by rfl) ⟨1971134, by rfl⟩ : syracuseStep 2628179 = 3942269) B3942269
theorem B1752119 : Blo 1166400 1752119 := bstep (se 1 (by rfl) ⟨1314089, by rfl⟩ : syracuseStep 1752119 = 2628179) B2628179
theorem B1168079 : Blo 1166400 1168079 := bstep (se 1 (by rfl) ⟨876059, by rfl⟩ : syracuseStep 1168079 = 1752119) B1752119

theorem C0 (j : ℕ) (h1 : 291600 ≤ j) (h2 : j ≤ 292099) : Blo 1166400 (4 * j + 3) := by
  interval_cases j
  · exact B1166403
  · exact B1166407
  · exact B1166411
  · exact B1166415
  · exact B1166419
  · exact B1166423
  · exact B1166427
  · exact B1166431
  · exact B1166435
  · exact B1166439
  · exact B1166443
  · exact B1166447
  · exact B1166451
  · exact B1166455
  · exact B1166459
  · exact B1166463
  · exact B1166467
  · exact B1166471
  · exact B1166475
  · exact B1166479
  · exact B1166483
  · exact B1166487
  · exact B1166491
  · exact B1166495
  · exact B1166499
  · exact B1166503
  · exact B1166507
  · exact B1166511
  · exact B1166515
  · exact B1166519
  · exact B1166523
  · exact B1166527
  · exact B1166531
  · exact B1166535
  · exact B1166539
  · exact B1166543
  · exact B1166547
  · exact B1166551
  · exact B1166555
  · exact B1166559
  · exact B1166563
  · exact B1166567
  · exact B1166571
  · exact B1166575
  · exact B1166579
  · exact B1166583
  · exact B1166587
  · exact B1166591
  · exact B1166595
  · exact B1166599
  · exact B1166603
  · exact B1166607
  · exact B1166611
  · exact B1166615
  · exact B1166619
  · exact B1166623
  · exact B1166627
  · exact B1166631
  · exact B1166635
  · exact B1166639
  · exact B1166643
  · exact B1166647
  · exact B1166651
  · exact B1166655
  · exact B1166659
  · exact B1166663
  · exact B1166667
  · exact B1166671
  · exact B1166675
  · exact B1166679
  · exact B1166683
  · exact B1166687
  · exact B1166691
  · exact B1166695
  · exact B1166699
  · exact B1166703
  · exact B1166707
  · exact B1166711
  · exact B1166715
  · exact B1166719
  · exact B1166723
  · exact B1166727
  · exact B1166731
  · exact B1166735
  · exact B1166739
  · exact B1166743
  · exact B1166747
  · exact B1166751
  · exact B1166755
  · exact B1166759
  · exact B1166763
  · exact B1166767
  · exact B1166771
  · exact B1166775
  · exact B1166779
  · exact B1166783
  · exact B1166787
  · exact B1166791
  · exact B1166795
  · exact B1166799
  · exact B1166803
  · exact B1166807
  · exact B1166811
  · exact B1166815
  · exact B1166819
  · exact B1166823
  · exact B1166827
  · exact B1166831
  · exact B1166835
  · exact B1166839
  · exact B1166843
  · exact B1166847
  · exact B1166851
  · exact B1166855
  · exact B1166859
  · exact B1166863
  · exact B1166867
  · exact B1166871
  · exact B1166875
  · exact B1166879
  · exact B1166883
  · exact B1166887
  · exact B1166891
  · exact B1166895
  · exact B1166899
  · exact B1166903
  · exact B1166907
  · exact B1166911
  · exact B1166915
  · exact B1166919
  · exact B1166923
  · exact B1166927
  · exact B1166931
  · exact B1166935
  · exact B1166939
  · exact B1166943
  · exact B1166947
  · exact B1166951
  · exact B1166955
  · exact B1166959
  · exact B1166963
  · exact B1166967
  · exact B1166971
  · exact B1166975
  · exact B1166979
  · exact B1166983
  · exact B1166987
  · exact B1166991
  · exact B1166995
  · exact B1166999
  · exact B1167003
  · exact B1167007
  · exact B1167011
  · exact B1167015
  · exact B1167019
  · exact B1167023
  · exact B1167027
  · exact B1167031
  · exact B1167035
  · exact B1167039
  · exact B1167043
  · exact B1167047
  · exact B1167051
  · exact B1167055
  · exact B1167059
  · exact B1167063
  · exact B1167067
  · exact B1167071
  · exact B1167075
  · exact B1167079
  · exact B1167083
  · exact B1167087
  · exact B1167091
  · exact B1167095
  · exact B1167099
  · exact B1167103
  · exact B1167107
  · exact B1167111
  · exact B1167115
  · exact B1167119
  · exact B1167123
  · exact B1167127
  · exact B1167131
  · exact B1167135
  · exact B1167139
  · exact B1167143
  · exact B1167147
  · exact B1167151
  · exact B1167155
  · exact B1167159
  · exact B1167163
  · exact B1167167
  · exact B1167171
  · exact B1167175
  · exact B1167179
  · exact B1167183
  · exact B1167187
  · exact B1167191
  · exact B1167195
  · exact B1167199
  · exact B1167203
  · exact B1167207
  · exact B1167211
  · exact B1167215
  · exact B1167219
  · exact B1167223
  · exact B1167227
  · exact B1167231
  · exact B1167235
  · exact B1167239
  · exact B1167243
  · exact B1167247
  · exact B1167251
  · exact B1167255
  · exact B1167259
  · exact B1167263
  · exact B1167267
  · exact B1167271
  · exact B1167275
  · exact B1167279
  · exact B1167283
  · exact B1167287
  · exact B1167291
  · exact B1167295
  · exact B1167299
  · exact B1167303
  · exact B1167307
  · exact B1167311
  · exact B1167315
  · exact B1167319
  · exact B1167323
  · exact B1167327
  · exact B1167331
  · exact B1167335
  · exact B1167339
  · exact B1167343
  · exact B1167347
  · exact B1167351
  · exact B1167355
  · exact B1167359
  · exact B1167363
  · exact B1167367
  · exact B1167371
  · exact B1167375
  · exact B1167379
  · exact B1167383
  · exact B1167387
  · exact B1167391
  · exact B1167395
  · exact B1167399
  · exact B1167403
  · exact B1167407
  · exact B1167411
  · exact B1167415
  · exact B1167419
  · exact B1167423
  · exact B1167427
  · exact B1167431
  · exact B1167435
  · exact B1167439
  · exact B1167443
  · exact B1167447
  · exact B1167451
  · exact B1167455
  · exact B1167459
  · exact B1167463
  · exact B1167467
  · exact B1167471
  · exact B1167475
  · exact B1167479
  · exact B1167483
  · exact B1167487
  · exact B1167491
  · exact B1167495
  · exact B1167499
  · exact B1167503
  · exact B1167507
  · exact B1167511
  · exact B1167515
  · exact B1167519
  · exact B1167523
  · exact B1167527
  · exact B1167531
  · exact B1167535
  · exact B1167539
  · exact B1167543
  · exact B1167547
  · exact B1167551
  · exact B1167555
  · exact B1167559
  · exact B1167563
  · exact B1167567
  · exact B1167571
  · exact B1167575
  · exact B1167579
  · exact B1167583
  · exact B1167587
  · exact B1167591
  · exact B1167595
  · exact B1167599
  · exact B1167603
  · exact B1167607
  · exact B1167611
  · exact B1167615
  · exact B1167619
  · exact B1167623
  · exact B1167627
  · exact B1167631
  · exact B1167635
  · exact B1167639
  · exact B1167643
  · exact B1167647
  · exact B1167651
  · exact B1167655
  · exact B1167659
  · exact B1167663
  · exact B1167667
  · exact B1167671
  · exact B1167675
  · exact B1167679
  · exact B1167683
  · exact B1167687
  · exact B1167691
  · exact B1167695
  · exact B1167699
  · exact B1167703
  · exact B1167707
  · exact B1167711
  · exact B1167715
  · exact B1167719
  · exact B1167723
  · exact B1167727
  · exact B1167731
  · exact B1167735
  · exact B1167739
  · exact B1167743
  · exact B1167747
  · exact B1167751
  · exact B1167755
  · exact B1167759
  · exact B1167763
  · exact B1167767
  · exact B1167771
  · exact B1167775
  · exact B1167779
  · exact B1167783
  · exact B1167787
  · exact B1167791
  · exact B1167795
  · exact B1167799
  · exact B1167803
  · exact B1167807
  · exact B1167811
  · exact B1167815
  · exact B1167819
  · exact B1167823
  · exact B1167827
  · exact B1167831
  · exact B1167835
  · exact B1167839
  · exact B1167843
  · exact B1167847
  · exact B1167851
  · exact B1167855
  · exact B1167859
  · exact B1167863
  · exact B1167867
  · exact B1167871
  · exact B1167875
  · exact B1167879
  · exact B1167883
  · exact B1167887
  · exact B1167891
  · exact B1167895
  · exact B1167899
  · exact B1167903
  · exact B1167907
  · exact B1167911
  · exact B1167915
  · exact B1167919
  · exact B1167923
  · exact B1167927
  · exact B1167931
  · exact B1167935
  · exact B1167939
  · exact B1167943
  · exact B1167947
  · exact B1167951
  · exact B1167955
  · exact B1167959
  · exact B1167963
  · exact B1167967
  · exact B1167971
  · exact B1167975
  · exact B1167979
  · exact B1167983
  · exact B1167987
  · exact B1167991
  · exact B1167995
  · exact B1167999
  · exact B1168003
  · exact B1168007
  · exact B1168011
  · exact B1168015
  · exact B1168019
  · exact B1168023
  · exact B1168027
  · exact B1168031
  · exact B1168035
  · exact B1168039
  · exact B1168043
  · exact B1168047
  · exact B1168051
  · exact B1168055
  · exact B1168059
  · exact B1168063
  · exact B1168067
  · exact B1168071
  · exact B1168075
  · exact B1168079
  · exact B1168083
  · exact B1168087
  · exact B1168091
  · exact B1168095
  · exact B1168099
  · exact B1168103
  · exact B1168107
  · exact B1168111
  · exact B1168115
  · exact B1168119
  · exact B1168123
  · exact B1168127
  · exact B1168131
  · exact B1168135
  · exact B1168139
  · exact B1168143
  · exact B1168147
  · exact B1168151
  · exact B1168155
  · exact B1168159
  · exact B1168163
  · exact B1168167
  · exact B1168171
  · exact B1168175
  · exact B1168179
  · exact B1168183
  · exact B1168187
  · exact B1168191
  · exact B1168195
  · exact B1168199
  · exact B1168203
  · exact B1168207
  · exact B1168211
  · exact B1168215
  · exact B1168219
  · exact B1168223
  · exact B1168227
  · exact B1168231
  · exact B1168235
  · exact B1168239
  · exact B1168243
  · exact B1168247
  · exact B1168251
  · exact B1168255
  · exact B1168259
  · exact B1168263
  · exact B1168267
  · exact B1168271
  · exact B1168275
  · exact B1168279
  · exact B1168283
  · exact B1168287
  · exact B1168291
  · exact B1168295
  · exact B1168299
  · exact B1168303
  · exact B1168307
  · exact B1168311
  · exact B1168315
  · exact B1168319
  · exact B1168323
  · exact B1168327
  · exact B1168331
  · exact B1168335
  · exact B1168339
  · exact B1168343
  · exact B1168347
  · exact B1168351
  · exact B1168355
  · exact B1168359
  · exact B1168363
  · exact B1168367
  · exact B1168371
  · exact B1168375
  · exact B1168379
  · exact B1168383
  · exact B1168387
  · exact B1168391
  · exact B1168395
  · exact B1168399

theorem solution (m : ℕ) (hlo : 1166400 ≤ m) (hhi : m ≤ 1168400) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 291600 ≤ j := by omega
    have hj2 : j ≤ 292099 := by omega
    have hb : Blo 1166400 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
