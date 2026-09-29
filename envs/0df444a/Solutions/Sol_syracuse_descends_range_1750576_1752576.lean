-- Prove2me | solution 1 for syracuse_descends_range_1750576_1752576
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:36:34.122591+00:00
-- url     : https://prove2.me/submissions/b80dd3a5-5878-4d62-8e35-a9f2c4234f04

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


theorem B9469973 : Blo 1750576 9469973 := bbase (se 6 (by rfl) ⟨221952, by rfl⟩ : syracuseStep 9469973 = 443905) (by norm_num)
theorem B2662445 : Blo 1750576 2662445 := bbase (se 3 (by rfl) ⟨499208, by rfl⟩ : syracuseStep 2662445 = 998417) (by norm_num)
theorem B3940397 : Blo 1750576 3940397 := bbase (se 3 (by rfl) ⟨738824, by rfl⟩ : syracuseStep 3940397 = 1477649) (by norm_num)
theorem B2957357 : Blo 1750576 2957357 := bbase (se 3 (by rfl) ⟨554504, by rfl⟩ : syracuseStep 2957357 = 1109009) (by norm_num)
theorem B8863829 : Blo 1750576 8863829 := bbase (se 8 (by rfl) ⟨51936, by rfl⟩ : syracuseStep 8863829 = 103873) (by norm_num)
theorem B6651989 : Blo 1750576 6651989 := bbase (se 8 (by rfl) ⟨38976, by rfl⟩ : syracuseStep 6651989 = 77953) (by norm_num)
theorem B3940469 : Blo 1750576 3940469 := bbase (se 5 (by rfl) ⟨184709, by rfl⟩ : syracuseStep 3940469 = 369419) (by norm_num)
theorem B3326093 : Blo 1750576 3326093 := bbase (se 3 (by rfl) ⟨623642, by rfl⟩ : syracuseStep 3326093 = 1247285) (by norm_num)
theorem B9978005 : Blo 1750576 9978005 := bbase (se 6 (by rfl) ⟨233859, by rfl⟩ : syracuseStep 9978005 = 467719) (by norm_num)
theorem B2162873 : Blo 1750576 2162873 := bbase (se 2 (by rfl) ⟨811077, by rfl⟩ : syracuseStep 2162873 = 1622155) (by norm_num)
theorem B3940541 : Blo 1750576 3940541 := bbase (se 3 (by rfl) ⟨738851, by rfl⟩ : syracuseStep 3940541 = 1477703) (by norm_num)
theorem B4432117 : Blo 1750576 4432117 := bbase (se 5 (by rfl) ⟨207755, by rfl⟩ : syracuseStep 4432117 = 415511) (by norm_num)
theorem B3940613 : Blo 1750576 3940613 := bbase (se 4 (by rfl) ⟨369432, by rfl⟩ : syracuseStep 3940613 = 738865) (by norm_num)
theorem B3940685 : Blo 1750576 3940685 := bbase (se 3 (by rfl) ⟨738878, by rfl⟩ : syracuseStep 3940685 = 1477757) (by norm_num)
theorem B4432229 : Blo 1750576 4432229 := bbase (se 4 (by rfl) ⟨415521, by rfl⟩ : syracuseStep 4432229 = 831043) (by norm_num)
theorem B6652277 : Blo 1750576 6652277 := bbase (se 5 (by rfl) ⟨311825, by rfl⟩ : syracuseStep 6652277 = 623651) (by norm_num)
theorem B3940757 : Blo 1750576 3940757 := bbase (se 6 (by rfl) ⟨92361, by rfl⟩ : syracuseStep 3940757 = 184723) (by norm_num)
theorem B4735397 : Blo 1750576 4735397 := bbase (se 4 (by rfl) ⟨443943, by rfl⟩ : syracuseStep 4735397 = 887887) (by norm_num)
theorem B3940829 : Blo 1750576 3940829 := bbase (se 3 (by rfl) ⟨738905, by rfl⟩ : syracuseStep 3940829 = 1477811) (by norm_num)
theorem B7102949 : Blo 1750576 7102949 := bbase (se 4 (by rfl) ⟨665901, by rfl⟩ : syracuseStep 7102949 = 1331803) (by norm_num)
theorem B4989413 : Blo 1750576 4989413 := bbase (se 4 (by rfl) ⟨467757, by rfl⟩ : syracuseStep 4989413 = 935515) (by norm_num)
theorem B4432421 : Blo 1750576 4432421 := bbase (se 4 (by rfl) ⟨415539, by rfl⟩ : syracuseStep 4432421 = 831079) (by norm_num)
theorem B3940901 : Blo 1750576 3940901 := bbase (se 4 (by rfl) ⟨369459, by rfl⟩ : syracuseStep 3940901 = 738919) (by norm_num)
theorem B2368045 : Blo 1750576 2368045 := bbase (se 3 (by rfl) ⟨444008, by rfl⟩ : syracuseStep 2368045 = 888017) (by norm_num)
theorem B3940973 : Blo 1750576 3940973 := bbase (se 3 (by rfl) ⟨738932, by rfl⟩ : syracuseStep 3940973 = 1477865) (by norm_num)
theorem B3941045 : Blo 1750576 3941045 := bbase (se 5 (by rfl) ⟨184736, by rfl⟩ : syracuseStep 3941045 = 369473) (by norm_num)
theorem B3941117 : Blo 1750576 3941117 := bbase (se 3 (by rfl) ⟨738959, by rfl⟩ : syracuseStep 3941117 = 1477919) (by norm_num)
theorem B3941189 : Blo 1750576 3941189 := bbase (se 4 (by rfl) ⟨369486, by rfl⟩ : syracuseStep 3941189 = 738973) (by norm_num)
theorem B6398837 : Blo 1750576 6398837 := bbase (se 5 (by rfl) ⟨299945, by rfl⟩ : syracuseStep 6398837 = 599891) (by norm_num)
theorem B4432765 : Blo 1750576 4432765 := bbase (se 3 (by rfl) ⟨831143, by rfl⟩ : syracuseStep 4432765 = 1662287) (by norm_num)
theorem B3326845 : Blo 1750576 3326845 := bbase (se 3 (by rfl) ⟨623783, by rfl⟩ : syracuseStep 3326845 = 1247567) (by norm_num)
theorem B3941261 : Blo 1750576 3941261 := bbase (se 3 (by rfl) ⟨738986, by rfl⟩ : syracuseStep 3941261 = 1477973) (by norm_num)
theorem B3941333 : Blo 1750576 3941333 := bbase (se 7 (by rfl) ⟨46187, by rfl⟩ : syracuseStep 3941333 = 92375) (by norm_num)
theorem B2368477 : Blo 1750576 2368477 := bbase (se 3 (by rfl) ⟨444089, by rfl⟩ : syracuseStep 2368477 = 888179) (by norm_num)
theorem B4432877 : Blo 1750576 4432877 := bbase (se 3 (by rfl) ⟨831164, by rfl⟩ : syracuseStep 4432877 = 1662329) (by norm_num)
theorem B3326989 : Blo 1750576 3326989 := bbase (se 3 (by rfl) ⟨623810, by rfl⟩ : syracuseStep 3326989 = 1247621) (by norm_num)
theorem B3941405 : Blo 1750576 3941405 := bbase (se 3 (by rfl) ⟨739013, by rfl⟩ : syracuseStep 3941405 = 1478027) (by norm_num)
theorem B4555829 : Blo 1750576 4555829 := bbase (se 5 (by rfl) ⟨213554, by rfl⟩ : syracuseStep 4555829 = 427109) (by norm_num)
theorem B3941477 : Blo 1750576 3941477 := bbase (se 4 (by rfl) ⟨369513, by rfl⟩ : syracuseStep 3941477 = 739027) (by norm_num)
theorem B4801669 : Blo 1750576 4801669 := bbase (se 4 (by rfl) ⟨450156, by rfl⟩ : syracuseStep 4801669 = 900313) (by norm_num)
theorem B4433069 : Blo 1750576 4433069 := bbase (se 3 (by rfl) ⟨831200, by rfl⟩ : syracuseStep 4433069 = 1662401) (by norm_num)
theorem B3941549 : Blo 1750576 3941549 := bbase (se 3 (by rfl) ⟨739040, by rfl⟩ : syracuseStep 3941549 = 1478081) (by norm_num)
theorem B3327149 : Blo 1750576 3327149 := bbase (se 3 (by rfl) ⟨623840, by rfl⟩ : syracuseStep 3327149 = 1247681) (by norm_num)
theorem B3941621 : Blo 1750576 3941621 := bbase (se 5 (by rfl) ⟨184763, by rfl⟩ : syracuseStep 3941621 = 369527) (by norm_num)
theorem B4736261 : Blo 1750576 4736261 := bbase (se 4 (by rfl) ⟨444024, by rfl⟩ : syracuseStep 4736261 = 888049) (by norm_num)
theorem B3941693 : Blo 1750576 3941693 := bbase (se 3 (by rfl) ⟨739067, by rfl⟩ : syracuseStep 3941693 = 1478135) (by norm_num)
theorem B5612885 : Blo 1750576 5612885 := bbase (se 12 (by rfl) ⟨2055, by rfl⟩ : syracuseStep 5612885 = 4111) (by norm_num)
theorem B8865125 : Blo 1750576 8865125 := bbase (se 4 (by rfl) ⟨831105, by rfl⟩ : syracuseStep 8865125 = 1662211) (by norm_num)
theorem B3941765 : Blo 1750576 3941765 := bbase (se 4 (by rfl) ⟨369540, by rfl⟩ : syracuseStep 3941765 = 739081) (by norm_num)
theorem B12625301 : Blo 1750576 12625301 := bbase (se 6 (by rfl) ⟨295905, by rfl⟩ : syracuseStep 12625301 = 591811) (by norm_num)
theorem B3941837 : Blo 1750576 3941837 := bbase (se 3 (by rfl) ⟨739094, by rfl⟩ : syracuseStep 3941837 = 1478189) (by norm_num)
theorem B4433413 : Blo 1750576 4433413 := bbase (se 4 (by rfl) ⟨415632, by rfl⟩ : syracuseStep 4433413 = 831265) (by norm_num)
theorem B3941909 : Blo 1750576 3941909 := bbase (se 6 (by rfl) ⟨92388, by rfl⟩ : syracuseStep 3941909 = 184777) (by norm_num)
theorem B6653461 : Blo 1750576 6653461 := bbase (se 6 (by rfl) ⟨155940, by rfl⟩ : syracuseStep 6653461 = 311881) (by norm_num)
theorem B3941981 : Blo 1750576 3941981 := bbase (se 3 (by rfl) ⟨739121, by rfl⟩ : syracuseStep 3941981 = 1478243) (by norm_num)
theorem B4433525 : Blo 1750576 4433525 := bbase (se 5 (by rfl) ⟨207821, by rfl⟩ : syracuseStep 4433525 = 415643) (by norm_num)
theorem B1869437 : Blo 1750576 1869437 := bbase (se 3 (by rfl) ⟨350519, by rfl⟩ : syracuseStep 1869437 = 701039) (by norm_num)
theorem B3942053 : Blo 1750576 3942053 := bbase (se 4 (by rfl) ⟨369567, by rfl⟩ : syracuseStep 3942053 = 739135) (by norm_num)
theorem B3942125 : Blo 1750576 3942125 := bbase (se 3 (by rfl) ⟨739148, by rfl⟩ : syracuseStep 3942125 = 1478297) (by norm_num)
theorem B4433717 : Blo 1750576 4433717 := bbase (se 5 (by rfl) ⟨207830, by rfl⟩ : syracuseStep 4433717 = 415661) (by norm_num)
theorem B3942197 : Blo 1750576 3942197 := bbase (se 5 (by rfl) ⟨184790, by rfl⟩ : syracuseStep 3942197 = 369581) (by norm_num)
theorem B6653765 : Blo 1750576 6653765 := bbase (se 4 (by rfl) ⟨623790, by rfl⟩ : syracuseStep 6653765 = 1247581) (by norm_num)
theorem B15976277 : Blo 1750576 15976277 := bbase (se 9 (by rfl) ⟨46805, by rfl⟩ : syracuseStep 15976277 = 93611) (by norm_num)
theorem B1869689 : Blo 1750576 1869689 := bbase (se 2 (by rfl) ⟨701133, by rfl⟩ : syracuseStep 1869689 = 1402267) (by norm_num)
theorem B3942269 : Blo 1750576 3942269 := bbase (se 3 (by rfl) ⟨739175, by rfl⟩ : syracuseStep 3942269 = 1478351) (by norm_num)
theorem B3942341 : Blo 1750576 3942341 := bbase (se 4 (by rfl) ⟨369594, by rfl⟩ : syracuseStep 3942341 = 739189) (by norm_num)
theorem B7481317 : Blo 1750576 7481317 := bbase (se 4 (by rfl) ⟨701373, by rfl⟩ : syracuseStep 7481317 = 1402747) (by norm_num)
theorem B3942413 : Blo 1750576 3942413 := bbase (se 3 (by rfl) ⟨739202, by rfl⟩ : syracuseStep 3942413 = 1478405) (by norm_num)
theorem B5908517 : Blo 1750576 5908517 := bbase (se 4 (by rfl) ⟨553923, by rfl⟩ : syracuseStep 5908517 = 1107847) (by norm_num)
theorem B2246725 : Blo 1750576 2246725 := bbase (se 4 (by rfl) ⟨210630, by rfl⟩ : syracuseStep 2246725 = 421261) (by norm_num)
theorem B115198037 : Blo 1750576 115198037 := bbase (se 8 (by rfl) ⟨674988, by rfl⟩ : syracuseStep 115198037 = 1349977) (by norm_num)
theorem B3942485 : Blo 1750576 3942485 := bbase (se 8 (by rfl) ⟨23100, by rfl⟩ : syracuseStep 3942485 = 46201) (by norm_num)
theorem B4434061 : Blo 1750576 4434061 := bbase (se 3 (by rfl) ⟨831386, by rfl⟩ : syracuseStep 4434061 = 1662773) (by norm_num)
theorem B3549341 : Blo 1750576 3549341 := bbase (se 3 (by rfl) ⟨665501, by rfl⟩ : syracuseStep 3549341 = 1331003) (by norm_num)
theorem B3942557 : Blo 1750576 3942557 := bbase (se 3 (by rfl) ⟨739229, by rfl⟩ : syracuseStep 3942557 = 1478459) (by norm_num)
theorem B3942629 : Blo 1750576 3942629 := bbase (se 4 (by rfl) ⟨369621, by rfl⟩ : syracuseStep 3942629 = 739243) (by norm_num)
theorem B4434173 : Blo 1750576 4434173 := bbase (se 3 (by rfl) ⟨831407, by rfl⟩ : syracuseStep 4434173 = 1662815) (by norm_num)
theorem B3942701 : Blo 1750576 3942701 := bbase (se 3 (by rfl) ⟨739256, by rfl⟩ : syracuseStep 3942701 = 1478513) (by norm_num)
theorem B1870133 : Blo 1750576 1870133 := bbase (se 5 (by rfl) ⟨87662, by rfl⟩ : syracuseStep 1870133 = 175325) (by norm_num)
theorem B11225461 : Blo 1750576 11225461 := bbase (se 5 (by rfl) ⟨526193, by rfl⟩ : syracuseStep 11225461 = 1052387) (by norm_num)
theorem B3942773 : Blo 1750576 3942773 := bbase (se 5 (by rfl) ⟨184817, by rfl⟩ : syracuseStep 3942773 = 369635) (by norm_num)
theorem B2492861 : Blo 1750576 2492861 := bbase (se 3 (by rfl) ⟨467411, by rfl⟩ : syracuseStep 2492861 = 934823) (by norm_num)
theorem B4434365 : Blo 1750576 4434365 := bbase (se 3 (by rfl) ⟨831443, by rfl⟩ : syracuseStep 4434365 = 1662887) (by norm_num)
theorem B3942845 : Blo 1750576 3942845 := bbase (se 3 (by rfl) ⟨739283, by rfl⟩ : syracuseStep 3942845 = 1478567) (by norm_num)
theorem B11217365 : Blo 1750576 11217365 := bbase (se 7 (by rfl) ⟨131453, by rfl⟩ : syracuseStep 11217365 = 262907) (by norm_num)
theorem B5908949 : Blo 1750576 5908949 := bbase (se 7 (by rfl) ⟨69245, by rfl⟩ : syracuseStep 5908949 = 138491) (by norm_num)
theorem B4491749 : Blo 1750576 4491749 := bbase (se 4 (by rfl) ⟨421101, by rfl⟩ : syracuseStep 4491749 = 842203) (by norm_num)
theorem B5401093 : Blo 1750576 5401093 := bbase (se 4 (by rfl) ⟨506352, by rfl⟩ : syracuseStep 5401093 = 1012705) (by norm_num)
theorem B3942917 : Blo 1750576 3942917 := bbase (se 4 (by rfl) ⟨369648, by rfl⟩ : syracuseStep 3942917 = 739297) (by norm_num)
theorem B1870381 : Blo 1750576 1870381 := bbase (se 3 (by rfl) ⟨350696, by rfl⟩ : syracuseStep 1870381 = 701393) (by norm_num)
theorem B16206389 : Blo 1750576 16206389 := bbase (se 5 (by rfl) ⟨759674, by rfl⟩ : syracuseStep 16206389 = 1519349) (by norm_num)
theorem B3942989 : Blo 1750576 3942989 := bbase (se 3 (by rfl) ⟨739310, by rfl⟩ : syracuseStep 3942989 = 1478621) (by norm_num)
theorem B12143189 : Blo 1750576 12143189 := bbase (se 8 (by rfl) ⟨71151, by rfl⟩ : syracuseStep 12143189 = 142303) (by norm_num)
theorem B8866421 : Blo 1750576 8866421 := bbase (se 5 (by rfl) ⟨415613, by rfl⟩ : syracuseStep 8866421 = 831227) (by norm_num)
theorem B3943061 : Blo 1750576 3943061 := bbase (se 6 (by rfl) ⟨92415, by rfl⟩ : syracuseStep 3943061 = 184831) (by norm_num)
theorem B4491973 : Blo 1750576 4491973 := bbase (se 4 (by rfl) ⟨421122, by rfl⟩ : syracuseStep 4491973 = 842245) (by norm_num)
theorem B3943133 : Blo 1750576 3943133 := bbase (se 3 (by rfl) ⟨739337, by rfl⟩ : syracuseStep 3943133 = 1478675) (by norm_num)
theorem B8416021 : Blo 1750576 8416021 := bbase (se 6 (by rfl) ⟨197250, by rfl⟩ : syracuseStep 8416021 = 394501) (by norm_num)
theorem B4434709 : Blo 1750576 4434709 := bbase (se 6 (by rfl) ⟨103938, by rfl⟩ : syracuseStep 4434709 = 207877) (by norm_num)
theorem B2132761 : Blo 1750576 2132761 := bbase (se 2 (by rfl) ⟨799785, by rfl⟩ : syracuseStep 2132761 = 1599571) (by norm_num)
theorem B3943205 : Blo 1750576 3943205 := bbase (se 4 (by rfl) ⟨369675, by rfl⟩ : syracuseStep 3943205 = 739351) (by norm_num)
theorem B7105333 : Blo 1750576 7105333 := bbase (se 5 (by rfl) ⟨333062, by rfl⟩ : syracuseStep 7105333 = 666125) (by norm_num)
theorem B2132825 : Blo 1750576 2132825 := bbase (se 2 (by rfl) ⟨799809, by rfl⟩ : syracuseStep 2132825 = 1599619) (by norm_num)
theorem B3943277 : Blo 1750576 3943277 := bbase (se 3 (by rfl) ⟨739364, by rfl⟩ : syracuseStep 3943277 = 1478729) (by norm_num)
theorem B5909381 : Blo 1750576 5909381 := bbase (se 4 (by rfl) ⟨554004, by rfl⟩ : syracuseStep 5909381 = 1108009) (by norm_num)
theorem B4434821 : Blo 1750576 4434821 := bbase (se 4 (by rfl) ⟨415764, by rfl⟩ : syracuseStep 4434821 = 831529) (by norm_num)
theorem B9972629 : Blo 1750576 9972629 := bbase (se 6 (by rfl) ⟨233733, by rfl⟩ : syracuseStep 9972629 = 467467) (by norm_num)
theorem B2845589 : Blo 1750576 2845589 := bbase (se 6 (by rfl) ⟨66693, by rfl⟩ : syracuseStep 2845589 = 133387) (by norm_num)
theorem B1870825 : Blo 1750576 1870825 := bbase (se 2 (by rfl) ⟨701559, by rfl⟩ : syracuseStep 1870825 = 1403119) (by norm_num)
theorem B2804725 : Blo 1750576 2804725 := bbase (se 5 (by rfl) ⟨131471, by rfl⟩ : syracuseStep 2804725 = 262943) (by norm_num)
theorem B1870885 : Blo 1750576 1870885 := bbase (se 4 (by rfl) ⟨175395, by rfl⟩ : syracuseStep 1870885 = 350791) (by norm_num)
theorem B4435013 : Blo 1750576 4435013 := bbase (se 4 (by rfl) ⟨415782, by rfl⟩ : syracuseStep 4435013 = 831565) (by norm_num)
theorem B3550373 : Blo 1750576 3550373 := bbase (se 4 (by rfl) ⟨332847, by rfl⟩ : syracuseStep 3550373 = 665695) (by norm_num)
theorem B2493613 : Blo 1750576 2493613 := bbase (se 3 (by rfl) ⟨467552, by rfl⟩ : syracuseStep 2493613 = 935105) (by norm_num)
theorem B1969429 : Blo 1750576 1969429 := bbase (se 6 (by rfl) ⟨46158, by rfl⟩ : syracuseStep 1969429 = 92317) (by norm_num)
theorem B5909813 : Blo 1750576 5909813 := bbase (se 5 (by rfl) ⟨277022, by rfl⟩ : syracuseStep 5909813 = 554045) (by norm_num)
theorem B1969465 : Blo 1750576 1969465 := bbase (se 2 (by rfl) ⟨738549, by rfl⟩ : syracuseStep 1969465 = 1477099) (by norm_num)
theorem B1969501 : Blo 1750576 1969501 := bbase (se 3 (by rfl) ⟨369281, by rfl⟩ : syracuseStep 1969501 = 738563) (by norm_num)
theorem B1871201 : Blo 1750576 1871201 := bbase (se 2 (by rfl) ⟨701700, by rfl⟩ : syracuseStep 1871201 = 1403401) (by norm_num)
theorem B1969537 : Blo 1750576 1969537 := bbase (se 2 (by rfl) ⟨738576, by rfl⟩ : syracuseStep 1969537 = 1477153) (by norm_num)
theorem B11980181 : Blo 1750576 11980181 := bbase (se 6 (by rfl) ⟨280785, by rfl⟩ : syracuseStep 11980181 = 561571) (by norm_num)
theorem B4435357 : Blo 1750576 4435357 := bbase (se 3 (by rfl) ⟨831629, by rfl⟩ : syracuseStep 4435357 = 1663259) (by norm_num)
theorem B1969573 : Blo 1750576 1969573 := bbase (se 4 (by rfl) ⟨184647, by rfl⟩ : syracuseStep 1969573 = 369295) (by norm_num)
theorem B2248121 : Blo 1750576 2248121 := bbase (se 2 (by rfl) ⟨843045, by rfl⟩ : syracuseStep 2248121 = 1686091) (by norm_num)
theorem B1969609 : Blo 1750576 1969609 := bbase (se 2 (by rfl) ⟨738603, by rfl⟩ : syracuseStep 1969609 = 1477207) (by norm_num)
theorem B1969645 : Blo 1750576 1969645 := bbase (se 3 (by rfl) ⟨369308, by rfl⟩ : syracuseStep 1969645 = 738617) (by norm_num)
theorem B4435469 : Blo 1750576 4435469 := bbase (se 3 (by rfl) ⟨831650, by rfl⟩ : syracuseStep 4435469 = 1663301) (by norm_num)
theorem B1969681 : Blo 1750576 1969681 := bbase (se 2 (by rfl) ⟨738630, by rfl⟩ : syracuseStep 1969681 = 1477261) (by norm_num)
theorem B5123621 : Blo 1750576 5123621 := bbase (se 4 (by rfl) ⟨480339, by rfl⟩ : syracuseStep 5123621 = 960679) (by norm_num)
theorem B1969717 : Blo 1750576 1969717 := bbase (se 5 (by rfl) ⟨92330, by rfl⟩ : syracuseStep 1969717 = 184661) (by norm_num)
theorem B1969753 : Blo 1750576 1969753 := bbase (se 2 (by rfl) ⟨738657, by rfl⟩ : syracuseStep 1969753 = 1477315) (by norm_num)
theorem B2248285 : Blo 1750576 2248285 := bbase (se 3 (by rfl) ⟨421553, by rfl⟩ : syracuseStep 2248285 = 843107) (by norm_num)
theorem B1969789 : Blo 1750576 1969789 := bbase (se 3 (by rfl) ⟨369335, by rfl⟩ : syracuseStep 1969789 = 738671) (by norm_num)
theorem B1969825 : Blo 1750576 1969825 := bbase (se 2 (by rfl) ⟨738684, by rfl⟩ : syracuseStep 1969825 = 1477369) (by norm_num)
theorem B2215613 : Blo 1750576 2215613 := bbase (se 3 (by rfl) ⟨415427, by rfl⟩ : syracuseStep 2215613 = 830855) (by norm_num)
theorem B1969861 : Blo 1750576 1969861 := bbase (se 4 (by rfl) ⟨184674, by rfl⟩ : syracuseStep 1969861 = 369349) (by norm_num)
theorem B3157709 : Blo 1750576 3157709 := bbase (se 3 (by rfl) ⟨592070, by rfl⟩ : syracuseStep 3157709 = 1184141) (by norm_num)
theorem B4435661 : Blo 1750576 4435661 := bbase (se 3 (by rfl) ⟨831686, by rfl⟩ : syracuseStep 4435661 = 1663373) (by norm_num)
theorem B5910245 : Blo 1750576 5910245 := bbase (se 4 (by rfl) ⟨554085, by rfl⟩ : syracuseStep 5910245 = 1108171) (by norm_num)
theorem B1969897 : Blo 1750576 1969897 := bbase (se 2 (by rfl) ⟨738711, by rfl⟩ : syracuseStep 1969897 = 1477423) (by norm_num)
theorem B2215669 : Blo 1750576 2215669 := bbase (se 5 (by rfl) ⟨103859, by rfl⟩ : syracuseStep 2215669 = 207719) (by norm_num)
theorem B1969933 : Blo 1750576 1969933 := bbase (se 3 (by rfl) ⟨369362, by rfl⟩ : syracuseStep 1969933 = 738725) (by norm_num)
theorem B3739421 : Blo 1750576 3739421 := bbase (se 3 (by rfl) ⟨701141, by rfl⟩ : syracuseStep 3739421 = 1402283) (by norm_num)
theorem B3157789 : Blo 1750576 3157789 := bbase (se 3 (by rfl) ⟨592085, by rfl⟩ : syracuseStep 3157789 = 1184171) (by norm_num)
theorem B1969969 : Blo 1750576 1969969 := bbase (se 2 (by rfl) ⟨738738, by rfl⟩ : syracuseStep 1969969 = 1477477) (by norm_num)
theorem B2215765 : Blo 1750576 2215765 := bbase (se 9 (by rfl) ⟨6491, by rfl⟩ : syracuseStep 2215765 = 12983) (by norm_num)
theorem B1970005 : Blo 1750576 1970005 := bbase (se 9 (by rfl) ⟨5771, by rfl⟩ : syracuseStep 1970005 = 11543) (by norm_num)
theorem B1970041 : Blo 1750576 1970041 := bbase (se 2 (by rfl) ⟨738765, by rfl⟩ : syracuseStep 1970041 = 1477531) (by norm_num)
theorem B8867717 : Blo 1750576 8867717 := bbase (se 4 (by rfl) ⟨831348, by rfl⟩ : syracuseStep 8867717 = 1662697) (by norm_num)
theorem B1970077 : Blo 1750576 1970077 := bbase (se 3 (by rfl) ⟨369389, by rfl⟩ : syracuseStep 1970077 = 738779) (by norm_num)
theorem B3739565 : Blo 1750576 3739565 := bbase (se 3 (by rfl) ⟨701168, by rfl⟩ : syracuseStep 3739565 = 1402337) (by norm_num)
theorem B1970113 : Blo 1750576 1970113 := bbase (se 2 (by rfl) ⟨738792, by rfl⟩ : syracuseStep 1970113 = 1477585) (by norm_num)
theorem B2494405 : Blo 1750576 2494405 := bbase (se 4 (by rfl) ⟨233850, by rfl⟩ : syracuseStep 2494405 = 467701) (by norm_num)
theorem B4050893 : Blo 1750576 4050893 := bbase (se 3 (by rfl) ⟨759542, by rfl⟩ : syracuseStep 4050893 = 1519085) (by norm_num)
theorem B2805725 : Blo 1750576 2805725 := bbase (se 3 (by rfl) ⟨526073, by rfl⟩ : syracuseStep 2805725 = 1052147) (by norm_num)
theorem B1970149 : Blo 1750576 1970149 := bbase (se 4 (by rfl) ⟨184701, by rfl⟩ : syracuseStep 1970149 = 369403) (by norm_num)
theorem B2215937 : Blo 1750576 2215937 := bbase (se 2 (by rfl) ⟨830976, by rfl⟩ : syracuseStep 2215937 = 1661953) (by norm_num)
theorem B3158021 : Blo 1750576 3158021 := bbase (se 4 (by rfl) ⟨296064, by rfl⟩ : syracuseStep 3158021 = 592129) (by norm_num)
theorem B1970185 : Blo 1750576 1970185 := bbase (se 2 (by rfl) ⟨738819, by rfl⟩ : syracuseStep 1970185 = 1477639) (by norm_num)
theorem B4436005 : Blo 1750576 4436005 := bbase (se 4 (by rfl) ⟨415875, by rfl⟩ : syracuseStep 4436005 = 831751) (by norm_num)
theorem B1970221 : Blo 1750576 1970221 := bbase (se 3 (by rfl) ⟨369416, by rfl⟩ : syracuseStep 1970221 = 738833) (by norm_num)
theorem B9973813 : Blo 1750576 9973813 := bbase (se 5 (by rfl) ⟨467522, by rfl⟩ : syracuseStep 9973813 = 935045) (by norm_num)
theorem B5992501 : Blo 1750576 5992501 := bbase (se 5 (by rfl) ⟨280898, by rfl⟩ : syracuseStep 5992501 = 561797) (by norm_num)
theorem B2215993 : Blo 1750576 2215993 := bbase (se 2 (by rfl) ⟨830997, by rfl⟩ : syracuseStep 2215993 = 1661995) (by norm_num)
theorem B1970257 : Blo 1750576 1970257 := bbase (se 2 (by rfl) ⟨738846, by rfl⟩ : syracuseStep 1970257 = 1477693) (by norm_num)
theorem B1970293 : Blo 1750576 1970293 := bbase (se 5 (by rfl) ⟨92357, by rfl⟩ : syracuseStep 1970293 = 184715) (by norm_num)
theorem B5910677 : Blo 1750576 5910677 := bbase (se 6 (by rfl) ⟨138531, by rfl⟩ : syracuseStep 5910677 = 277063) (by norm_num)
theorem B4436117 : Blo 1750576 4436117 := bbase (se 6 (by rfl) ⟨103971, by rfl⟩ : syracuseStep 4436117 = 207943) (by norm_num)
theorem B2216089 : Blo 1750576 2216089 := bbase (se 2 (by rfl) ⟨831033, by rfl⟩ : syracuseStep 2216089 = 1662067) (by norm_num)
theorem B1970329 : Blo 1750576 1970329 := bbase (se 2 (by rfl) ⟨738873, by rfl⟩ : syracuseStep 1970329 = 1477747) (by norm_num)
theorem B1970365 : Blo 1750576 1970365 := bbase (se 3 (by rfl) ⟨369443, by rfl⟩ : syracuseStep 1970365 = 738887) (by norm_num)
theorem B1970401 : Blo 1750576 1970401 := bbase (se 2 (by rfl) ⟨738900, by rfl⟩ : syracuseStep 1970401 = 1477801) (by norm_num)
theorem B1970437 : Blo 1750576 1970437 := bbase (se 4 (by rfl) ⟨184728, by rfl⟩ : syracuseStep 1970437 = 369457) (by norm_num)
theorem B3739925 : Blo 1750576 3739925 := bbase (se 6 (by rfl) ⟨87654, by rfl⟩ : syracuseStep 3739925 = 175309) (by norm_num)
theorem B2494741 : Blo 1750576 2494741 := bbase (se 6 (by rfl) ⟨58470, by rfl⟩ : syracuseStep 2494741 = 116941) (by norm_num)
theorem B6648101 : Blo 1750576 6648101 := bbase (se 4 (by rfl) ⟨623259, by rfl⟩ : syracuseStep 6648101 = 1246519) (by norm_num)
theorem B1970473 : Blo 1750576 1970473 := bbase (se 2 (by rfl) ⟨738927, by rfl⟩ : syracuseStep 1970473 = 1477855) (by norm_num)
theorem B2216261 : Blo 1750576 2216261 := bbase (se 4 (by rfl) ⟨207774, by rfl⟩ : syracuseStep 2216261 = 415549) (by norm_num)
theorem B2625869 : Blo 1750576 2625869 := bbase (se 3 (by rfl) ⟨492350, by rfl⟩ : syracuseStep 2625869 = 984701) (by norm_num)
theorem B1970509 : Blo 1750576 1970509 := bbase (se 3 (by rfl) ⟨369470, by rfl⟩ : syracuseStep 1970509 = 738941) (by norm_num)
theorem B2625893 : Blo 1750576 2625893 := bbase (se 4 (by rfl) ⟨246177, by rfl⟩ : syracuseStep 2625893 = 492355) (by norm_num)
theorem B1970545 : Blo 1750576 1970545 := bbase (se 2 (by rfl) ⟨738954, by rfl⟩ : syracuseStep 1970545 = 1477909) (by norm_num)
theorem B2625917 : Blo 1750576 2625917 := bbase (se 3 (by rfl) ⟨492359, by rfl⟩ : syracuseStep 2625917 = 984719) (by norm_num)
theorem B2216317 : Blo 1750576 2216317 := bbase (se 3 (by rfl) ⟨415559, by rfl⟩ : syracuseStep 2216317 = 831119) (by norm_num)
theorem B4985221 : Blo 1750576 4985221 := bbase (se 4 (by rfl) ⟨467364, by rfl⟩ : syracuseStep 4985221 = 934729) (by norm_num)
theorem B3551629 : Blo 1750576 3551629 := bbase (se 3 (by rfl) ⟨665930, by rfl⟩ : syracuseStep 3551629 = 1331861) (by norm_num)
theorem B2625941 : Blo 1750576 2625941 := bbase (se 6 (by rfl) ⟨61545, by rfl⟩ : syracuseStep 2625941 = 123091) (by norm_num)
theorem B1970581 : Blo 1750576 1970581 := bbase (se 6 (by rfl) ⟨46185, by rfl⟩ : syracuseStep 1970581 = 92371) (by norm_num)
theorem B2625965 : Blo 1750576 2625965 := bbase (se 3 (by rfl) ⟨492368, by rfl⟩ : syracuseStep 2625965 = 984737) (by norm_num)
theorem B1970617 : Blo 1750576 1970617 := bbase (se 2 (by rfl) ⟨738981, by rfl⟩ : syracuseStep 1970617 = 1477963) (by norm_num)
theorem B2625989 : Blo 1750576 2625989 := bbase (se 4 (by rfl) ⟨246186, by rfl⟩ : syracuseStep 2625989 = 492373) (by norm_num)
theorem B2626013 : Blo 1750576 2626013 := bbase (se 3 (by rfl) ⟨492377, by rfl⟩ : syracuseStep 2626013 = 984755) (by norm_num)
theorem B2216413 : Blo 1750576 2216413 := bbase (se 3 (by rfl) ⟨415577, by rfl⟩ : syracuseStep 2216413 = 831155) (by norm_num)
theorem B1970653 : Blo 1750576 1970653 := bbase (se 3 (by rfl) ⟨369497, by rfl⟩ : syracuseStep 1970653 = 738995) (by norm_num)
theorem B2494957 : Blo 1750576 2494957 := bbase (se 3 (by rfl) ⟨467804, by rfl⟩ : syracuseStep 2494957 = 935609) (by norm_num)
theorem B2626037 : Blo 1750576 2626037 := bbase (se 5 (by rfl) ⟨123095, by rfl⟩ : syracuseStep 2626037 = 246191) (by norm_num)
theorem B1970689 : Blo 1750576 1970689 := bbase (se 2 (by rfl) ⟨739008, by rfl⟩ : syracuseStep 1970689 = 1478017) (by norm_num)
theorem B2626061 : Blo 1750576 2626061 := bbase (se 3 (by rfl) ⟨492386, by rfl⟩ : syracuseStep 2626061 = 984773) (by norm_num)
theorem B4985381 : Blo 1750576 4985381 := bbase (se 4 (by rfl) ⟨467379, by rfl⟩ : syracuseStep 4985381 = 934759) (by norm_num)
theorem B2626085 : Blo 1750576 2626085 := bbase (se 4 (by rfl) ⟨246195, by rfl⟩ : syracuseStep 2626085 = 492391) (by norm_num)
theorem B1970725 : Blo 1750576 1970725 := bbase (se 4 (by rfl) ⟨184755, by rfl⟩ : syracuseStep 1970725 = 369511) (by norm_num)
theorem B2626109 : Blo 1750576 2626109 := bbase (se 3 (by rfl) ⟨492395, by rfl⟩ : syracuseStep 2626109 = 984791) (by norm_num)
theorem B6648389 : Blo 1750576 6648389 := bbase (se 4 (by rfl) ⟨623286, by rfl⟩ : syracuseStep 6648389 = 1246573) (by norm_num)
theorem B5911109 : Blo 1750576 5911109 := bbase (se 4 (by rfl) ⟨554166, by rfl⟩ : syracuseStep 5911109 = 1108333) (by norm_num)
theorem B1970761 : Blo 1750576 1970761 := bbase (se 2 (by rfl) ⟨739035, by rfl⟩ : syracuseStep 1970761 = 1478071) (by norm_num)
theorem B2626133 : Blo 1750576 2626133 := bbase (se 8 (by rfl) ⟨15387, by rfl⟩ : syracuseStep 2626133 = 30775) (by norm_num)
theorem B2626157 : Blo 1750576 2626157 := bbase (se 3 (by rfl) ⟨492404, by rfl⟩ : syracuseStep 2626157 = 984809) (by norm_num)
theorem B1970797 : Blo 1750576 1970797 := bbase (se 3 (by rfl) ⟨369524, by rfl⟩ : syracuseStep 1970797 = 739049) (by norm_num)
theorem B2626181 : Blo 1750576 2626181 := bbase (se 4 (by rfl) ⟨246204, by rfl⟩ : syracuseStep 2626181 = 492409) (by norm_num)
theorem B2216585 : Blo 1750576 2216585 := bbase (se 2 (by rfl) ⟨831219, by rfl⟩ : syracuseStep 2216585 = 1662439) (by norm_num)
theorem B1970833 : Blo 1750576 1970833 := bbase (se 2 (by rfl) ⟨739062, by rfl⟩ : syracuseStep 1970833 = 1478125) (by norm_num)
theorem B2626205 : Blo 1750576 2626205 := bbase (se 3 (by rfl) ⟨492413, by rfl⟩ : syracuseStep 2626205 = 984827) (by norm_num)
theorem B2626229 : Blo 1750576 2626229 := bbase (se 5 (by rfl) ⟨123104, by rfl⟩ : syracuseStep 2626229 = 246209) (by norm_num)
theorem B1970869 : Blo 1750576 1970869 := bbase (se 5 (by rfl) ⟨92384, by rfl⟩ : syracuseStep 1970869 = 184769) (by norm_num)
theorem B2216641 : Blo 1750576 2216641 := bbase (se 2 (by rfl) ⟨831240, by rfl⟩ : syracuseStep 2216641 = 1662481) (by norm_num)
theorem B2626253 : Blo 1750576 2626253 := bbase (se 3 (by rfl) ⟨492422, by rfl⟩ : syracuseStep 2626253 = 984845) (by norm_num)
theorem B1970905 : Blo 1750576 1970905 := bbase (se 2 (by rfl) ⟨739089, by rfl⟩ : syracuseStep 1970905 = 1478179) (by norm_num)
theorem B2626277 : Blo 1750576 2626277 := bbase (se 4 (by rfl) ⟨246213, by rfl⟩ : syracuseStep 2626277 = 492427) (by norm_num)
theorem B2626301 : Blo 1750576 2626301 := bbase (se 3 (by rfl) ⟨492431, by rfl⟩ : syracuseStep 2626301 = 984863) (by norm_num)
theorem B1970941 : Blo 1750576 1970941 := bbase (se 3 (by rfl) ⟨369551, by rfl⟩ : syracuseStep 1970941 = 739103) (by norm_num)
theorem B4985621 : Blo 1750576 4985621 := bbase (se 6 (by rfl) ⟨116850, by rfl⟩ : syracuseStep 4985621 = 233701) (by norm_num)
theorem B2626325 : Blo 1750576 2626325 := bbase (se 6 (by rfl) ⟨61554, by rfl⟩ : syracuseStep 2626325 = 123109) (by norm_num)
theorem B2216737 : Blo 1750576 2216737 := bbase (se 2 (by rfl) ⟨831276, by rfl⟩ : syracuseStep 2216737 = 1662553) (by norm_num)
theorem B1970977 : Blo 1750576 1970977 := bbase (se 2 (by rfl) ⟨739116, by rfl⟩ : syracuseStep 1970977 = 1478233) (by norm_num)
theorem B2626349 : Blo 1750576 2626349 := bbase (se 3 (by rfl) ⟨492440, by rfl⟩ : syracuseStep 2626349 = 984881) (by norm_num)
theorem B2626373 : Blo 1750576 2626373 := bbase (se 4 (by rfl) ⟨246222, by rfl⟩ : syracuseStep 2626373 = 492445) (by norm_num)
theorem B2700101 : Blo 1750576 2700101 := bbase (se 4 (by rfl) ⟨253134, by rfl⟩ : syracuseStep 2700101 = 506269) (by norm_num)
theorem B1971013 : Blo 1750576 1971013 := bbase (se 4 (by rfl) ⟨184782, by rfl⟩ : syracuseStep 1971013 = 369565) (by norm_num)
theorem B2626397 : Blo 1750576 2626397 := bbase (se 3 (by rfl) ⟨492449, by rfl⟩ : syracuseStep 2626397 = 984899) (by norm_num)
theorem B2495333 : Blo 1750576 2495333 := bbase (se 4 (by rfl) ⟨233937, by rfl⟩ : syracuseStep 2495333 = 467875) (by norm_num)
theorem B1971049 : Blo 1750576 1971049 := bbase (se 2 (by rfl) ⟨739143, by rfl⟩ : syracuseStep 1971049 = 1478287) (by norm_num)
theorem B2052977 : Blo 1750576 2052977 := bbase (se 2 (by rfl) ⟨769866, by rfl⟩ : syracuseStep 2052977 = 1539733) (by norm_num)
theorem B2626421 : Blo 1750576 2626421 := bbase (se 5 (by rfl) ⟨123113, by rfl⟩ : syracuseStep 2626421 = 246227) (by norm_num)
theorem B2954117 : Blo 1750576 2954117 := bbase (se 4 (by rfl) ⟨276948, by rfl⟩ : syracuseStep 2954117 = 553897) (by norm_num)
theorem B1848205 : Blo 1750576 1848205 := bbase (se 3 (by rfl) ⟨346538, by rfl⟩ : syracuseStep 1848205 = 693077) (by norm_num)
theorem B2626445 : Blo 1750576 2626445 := bbase (se 3 (by rfl) ⟨492458, by rfl⟩ : syracuseStep 2626445 = 984917) (by norm_num)
theorem B1971085 : Blo 1750576 1971085 := bbase (se 3 (by rfl) ⟨369578, by rfl⟩ : syracuseStep 1971085 = 739157) (by norm_num)
theorem B7484309 : Blo 1750576 7484309 := bbase (se 6 (by rfl) ⟨175413, by rfl⟩ : syracuseStep 7484309 = 350827) (by norm_num)
theorem B2626469 : Blo 1750576 2626469 := bbase (se 4 (by rfl) ⟨246231, by rfl⟩ : syracuseStep 2626469 = 492463) (by norm_num)
theorem B1971121 : Blo 1750576 1971121 := bbase (se 2 (by rfl) ⟨739170, by rfl⟩ : syracuseStep 1971121 = 1478341) (by norm_num)
theorem B2626493 : Blo 1750576 2626493 := bbase (se 3 (by rfl) ⟨492467, by rfl⟩ : syracuseStep 2626493 = 984935) (by norm_num)
theorem B4207549 : Blo 1750576 4207549 := bbase (se 3 (by rfl) ⟨788915, by rfl⟩ : syracuseStep 4207549 = 1577831) (by norm_num)
theorem B1774541 : Blo 1750576 1774541 := bbase (se 3 (by rfl) ⟨332726, by rfl⟩ : syracuseStep 1774541 = 665453) (by norm_num)
theorem B2216909 : Blo 1750576 2216909 := bbase (se 3 (by rfl) ⟨415670, by rfl⟩ : syracuseStep 2216909 = 831341) (by norm_num)
theorem B4985813 : Blo 1750576 4985813 := bbase (se 7 (by rfl) ⟨58427, by rfl⟩ : syracuseStep 4985813 = 116855) (by norm_num)
theorem B2626517 : Blo 1750576 2626517 := bbase (se 7 (by rfl) ⟨30779, by rfl⟩ : syracuseStep 2626517 = 61559) (by norm_num)
theorem B1971157 : Blo 1750576 1971157 := bbase (se 7 (by rfl) ⟨23099, by rfl⟩ : syracuseStep 1971157 = 46199) (by norm_num)
theorem B2626541 : Blo 1750576 2626541 := bbase (se 3 (by rfl) ⟨492476, by rfl⟩ : syracuseStep 2626541 = 984953) (by norm_num)
theorem B5911541 : Blo 1750576 5911541 := bbase (se 5 (by rfl) ⟨277103, by rfl⟩ : syracuseStep 5911541 = 554207) (by norm_num)
theorem B1971193 : Blo 1750576 1971193 := bbase (se 2 (by rfl) ⟨739197, by rfl⟩ : syracuseStep 1971193 = 1478395) (by norm_num)
theorem B2954245 : Blo 1750576 2954245 := bbase (se 4 (by rfl) ⟨276960, by rfl⟩ : syracuseStep 2954245 = 553921) (by norm_num)
theorem B2626565 : Blo 1750576 2626565 := bbase (se 4 (by rfl) ⟨246240, by rfl⟩ : syracuseStep 2626565 = 492481) (by norm_num)
theorem B2216965 : Blo 1750576 2216965 := bbase (se 4 (by rfl) ⟨207840, by rfl⟩ : syracuseStep 2216965 = 415681) (by norm_num)
theorem B9466901 : Blo 1750576 9466901 := bbase (se 6 (by rfl) ⟨221880, by rfl⟩ : syracuseStep 9466901 = 443761) (by norm_num)
theorem B2626589 : Blo 1750576 2626589 := bbase (se 3 (by rfl) ⟨492485, by rfl⟩ : syracuseStep 2626589 = 984971) (by norm_num)
theorem B1971229 : Blo 1750576 1971229 := bbase (se 3 (by rfl) ⟨369605, by rfl⟩ : syracuseStep 1971229 = 739211) (by norm_num)
theorem B2626613 : Blo 1750576 2626613 := bbase (se 5 (by rfl) ⟨123122, by rfl⟩ : syracuseStep 2626613 = 246245) (by norm_num)
theorem B1971265 : Blo 1750576 1971265 := bbase (se 2 (by rfl) ⟨739224, by rfl⟩ : syracuseStep 1971265 = 1478449) (by norm_num)
theorem B2626637 : Blo 1750576 2626637 := bbase (se 3 (by rfl) ⟨492494, by rfl⟩ : syracuseStep 2626637 = 984989) (by norm_num)
theorem B2954333 : Blo 1750576 2954333 := bbase (se 3 (by rfl) ⟨553937, by rfl⟩ : syracuseStep 2954333 = 1107875) (by norm_num)
theorem B2626661 : Blo 1750576 2626661 := bbase (se 4 (by rfl) ⟨246249, by rfl⟩ : syracuseStep 2626661 = 492499) (by norm_num)
theorem B4494437 : Blo 1750576 4494437 := bbase (se 4 (by rfl) ⟨421353, by rfl⟩ : syracuseStep 4494437 = 842707) (by norm_num)
theorem B2217061 : Blo 1750576 2217061 := bbase (se 4 (by rfl) ⟨207849, by rfl⟩ : syracuseStep 2217061 = 415699) (by norm_num)
theorem B1971301 : Blo 1750576 1971301 := bbase (se 4 (by rfl) ⟨184809, by rfl⟩ : syracuseStep 1971301 = 369619) (by norm_num)
theorem B2626685 : Blo 1750576 2626685 := bbase (se 3 (by rfl) ⟨492503, by rfl⟩ : syracuseStep 2626685 = 985007) (by norm_num)
theorem B1971337 : Blo 1750576 1971337 := bbase (se 2 (by rfl) ⟨739251, by rfl⟩ : syracuseStep 1971337 = 1478503) (by norm_num)
theorem B3740813 : Blo 1750576 3740813 := bbase (se 3 (by rfl) ⟨701402, by rfl⟩ : syracuseStep 3740813 = 1402805) (by norm_num)
theorem B2626709 : Blo 1750576 2626709 := bbase (se 6 (by rfl) ⟨61563, by rfl⟩ : syracuseStep 2626709 = 123127) (by norm_num)
theorem B8869013 : Blo 1750576 8869013 := bbase (se 6 (by rfl) ⟨207867, by rfl⟩ : syracuseStep 8869013 = 415735) (by norm_num)
theorem B4207781 : Blo 1750576 4207781 := bbase (se 4 (by rfl) ⟨394479, by rfl⟩ : syracuseStep 4207781 = 788959) (by norm_num)
theorem B2626733 : Blo 1750576 2626733 := bbase (se 3 (by rfl) ⟨492512, by rfl⟩ : syracuseStep 2626733 = 985025) (by norm_num)
theorem B1971373 : Blo 1750576 1971373 := bbase (se 3 (by rfl) ⟨369632, by rfl⟩ : syracuseStep 1971373 = 739265) (by norm_num)
theorem B2626757 : Blo 1750576 2626757 := bbase (se 4 (by rfl) ⟨246258, by rfl⟩ : syracuseStep 2626757 = 492517) (by norm_num)
theorem B1774801 : Blo 1750576 1774801 := bbase (se 2 (by rfl) ⟨665550, by rfl⟩ : syracuseStep 1774801 = 1331101) (by norm_num)
theorem B1971409 : Blo 1750576 1971409 := bbase (se 2 (by rfl) ⟨739278, by rfl⟩ : syracuseStep 1971409 = 1478557) (by norm_num)
theorem B2954461 : Blo 1750576 2954461 := bbase (se 3 (by rfl) ⟨553961, by rfl⟩ : syracuseStep 2954461 = 1107923) (by norm_num)
theorem B2626781 : Blo 1750576 2626781 := bbase (se 3 (by rfl) ⟨492521, by rfl⟩ : syracuseStep 2626781 = 985043) (by norm_num)
theorem B2626805 : Blo 1750576 2626805 := bbase (se 5 (by rfl) ⟨123131, by rfl⟩ : syracuseStep 2626805 = 246263) (by norm_num)
theorem B1971445 : Blo 1750576 1971445 := bbase (se 5 (by rfl) ⟨92411, by rfl⟩ : syracuseStep 1971445 = 184823) (by norm_num)
theorem B2626829 : Blo 1750576 2626829 := bbase (se 3 (by rfl) ⟨492530, by rfl⟩ : syracuseStep 2626829 = 985061) (by norm_num)
theorem B2217233 : Blo 1750576 2217233 := bbase (se 2 (by rfl) ⟨831462, by rfl⟩ : syracuseStep 2217233 = 1662925) (by norm_num)
theorem B1971481 : Blo 1750576 1971481 := bbase (se 2 (by rfl) ⟨739305, by rfl⟩ : syracuseStep 1971481 = 1478611) (by norm_num)
theorem B2626853 : Blo 1750576 2626853 := bbase (se 4 (by rfl) ⟨246267, by rfl⟩ : syracuseStep 2626853 = 492535) (by norm_num)
theorem B2954549 : Blo 1750576 2954549 := bbase (se 5 (by rfl) ⟨138494, by rfl⟩ : syracuseStep 2954549 = 276989) (by norm_num)
theorem B4207925 : Blo 1750576 4207925 := bbase (se 5 (by rfl) ⟨197246, by rfl⟩ : syracuseStep 4207925 = 394493) (by norm_num)
theorem B2626877 : Blo 1750576 2626877 := bbase (se 3 (by rfl) ⟨492539, by rfl⟩ : syracuseStep 2626877 = 985079) (by norm_num)
theorem B1971517 : Blo 1750576 1971517 := bbase (se 3 (by rfl) ⟨369659, by rfl⟩ : syracuseStep 1971517 = 739319) (by norm_num)
theorem B2217289 : Blo 1750576 2217289 := bbase (se 2 (by rfl) ⟨831483, by rfl⟩ : syracuseStep 2217289 = 1662967) (by norm_num)
theorem B2626901 : Blo 1750576 2626901 := bbase (se 14 (by rfl) ⟨240, by rfl⟩ : syracuseStep 2626901 = 481) (by norm_num)
theorem B182064469 : Blo 1750576 182064469 := bbase (se 14 (by rfl) ⟨16668, by rfl⟩ : syracuseStep 182064469 = 33337) (by norm_num)
theorem B1971553 : Blo 1750576 1971553 := bbase (se 2 (by rfl) ⟨739332, by rfl⟩ : syracuseStep 1971553 = 1478665) (by norm_num)
theorem B6739301 : Blo 1750576 6739301 := bbase (se 4 (by rfl) ⟨631809, by rfl⟩ : syracuseStep 6739301 = 1263619) (by norm_num)
theorem B3790189 : Blo 1750576 3790189 := bbase (se 3 (by rfl) ⟨710660, by rfl⟩ : syracuseStep 3790189 = 1421321) (by norm_num)
theorem B2626925 : Blo 1750576 2626925 := bbase (se 3 (by rfl) ⟨492548, by rfl⟩ : syracuseStep 2626925 = 985097) (by norm_num)
theorem B2626949 : Blo 1750576 2626949 := bbase (se 4 (by rfl) ⟨246276, by rfl⟩ : syracuseStep 2626949 = 492553) (by norm_num)
theorem B3741061 : Blo 1750576 3741061 := bbase (se 4 (by rfl) ⟨350724, by rfl⟩ : syracuseStep 3741061 = 701449) (by norm_num)
theorem B1971589 : Blo 1750576 1971589 := bbase (se 4 (by rfl) ⟨184836, by rfl⟩ : syracuseStep 1971589 = 369673) (by norm_num)
theorem B2626973 : Blo 1750576 2626973 := bbase (se 3 (by rfl) ⟨492557, by rfl⟩ : syracuseStep 2626973 = 985115) (by norm_num)
theorem B5911973 : Blo 1750576 5911973 := bbase (se 4 (by rfl) ⟨554247, by rfl⟩ : syracuseStep 5911973 = 1108495) (by norm_num)
theorem B2217385 : Blo 1750576 2217385 := bbase (se 2 (by rfl) ⟨831519, by rfl⟩ : syracuseStep 2217385 = 1663039) (by norm_num)
theorem B1971625 : Blo 1750576 1971625 := bbase (se 2 (by rfl) ⟨739359, by rfl⟩ : syracuseStep 1971625 = 1478719) (by norm_num)
theorem B2954677 : Blo 1750576 2954677 := bbase (se 5 (by rfl) ⟨138500, by rfl⟩ : syracuseStep 2954677 = 277001) (by norm_num)
theorem B2626997 : Blo 1750576 2626997 := bbase (se 5 (by rfl) ⟨123140, by rfl⟩ : syracuseStep 2626997 = 246281) (by norm_num)
theorem B2807237 : Blo 1750576 2807237 := bbase (se 4 (by rfl) ⟨263178, by rfl⟩ : syracuseStep 2807237 = 526357) (by norm_num)
theorem B2627021 : Blo 1750576 2627021 := bbase (se 3 (by rfl) ⟨492566, by rfl⟩ : syracuseStep 2627021 = 985133) (by norm_num)
theorem B2627045 : Blo 1750576 2627045 := bbase (se 4 (by rfl) ⟨246285, by rfl⟩ : syracuseStep 2627045 = 492571) (by norm_num)
theorem B2627069 : Blo 1750576 2627069 := bbase (se 3 (by rfl) ⟨492575, by rfl⟩ : syracuseStep 2627069 = 985151) (by norm_num)
theorem B3323405 : Blo 1750576 3323405 := bbase (se 3 (by rfl) ⟨623138, by rfl⟩ : syracuseStep 3323405 = 1246277) (by norm_num)
theorem B2954765 : Blo 1750576 2954765 := bbase (se 3 (by rfl) ⟨554018, by rfl⟩ : syracuseStep 2954765 = 1108037) (by norm_num)
theorem B2627093 : Blo 1750576 2627093 := bbase (se 6 (by rfl) ⟨61572, by rfl⟩ : syracuseStep 2627093 = 123145) (by norm_num)
theorem B4208165 : Blo 1750576 4208165 := bbase (se 4 (by rfl) ⟨394515, by rfl⟩ : syracuseStep 4208165 = 789031) (by norm_num)
theorem B2995757 : Blo 1750576 2995757 := bbase (se 3 (by rfl) ⟨561704, by rfl⟩ : syracuseStep 2995757 = 1123409) (by norm_num)
theorem B2627117 : Blo 1750576 2627117 := bbase (se 3 (by rfl) ⟨492584, by rfl⟩ : syracuseStep 2627117 = 985169) (by norm_num)
theorem B2627141 : Blo 1750576 2627141 := bbase (se 4 (by rfl) ⟨246294, by rfl⟩ : syracuseStep 2627141 = 492589) (by norm_num)
theorem B11982421 : Blo 1750576 11982421 := bbase (se 8 (by rfl) ⟨70209, by rfl⟩ : syracuseStep 11982421 = 140419) (by norm_num)
theorem B13301333 : Blo 1750576 13301333 := bbase (se 8 (by rfl) ⟨77937, by rfl⟩ : syracuseStep 13301333 = 155875) (by norm_num)
theorem B2217557 : Blo 1750576 2217557 := bbase (se 8 (by rfl) ⟨12993, by rfl⟩ : syracuseStep 2217557 = 25987) (by norm_num)
theorem B2627165 : Blo 1750576 2627165 := bbase (se 3 (by rfl) ⟨492593, by rfl⟩ : syracuseStep 2627165 = 985187) (by norm_num)
theorem B3995237 : Blo 1750576 3995237 := bbase (se 4 (by rfl) ⟨374553, by rfl⟩ : syracuseStep 3995237 = 749107) (by norm_num)
theorem B6313573 : Blo 1750576 6313573 := bbase (se 4 (by rfl) ⟨591897, by rfl⟩ : syracuseStep 6313573 = 1183795) (by norm_num)
theorem B2627189 : Blo 1750576 2627189 := bbase (se 5 (by rfl) ⟨123149, by rfl⟩ : syracuseStep 2627189 = 246299) (by norm_num)
theorem B2954893 : Blo 1750576 2954893 := bbase (se 3 (by rfl) ⟨554042, by rfl⟩ : syracuseStep 2954893 = 1108085) (by norm_num)
theorem B2627213 : Blo 1750576 2627213 := bbase (se 3 (by rfl) ⟨492602, by rfl⟩ : syracuseStep 2627213 = 985205) (by norm_num)
theorem B2217613 : Blo 1750576 2217613 := bbase (se 3 (by rfl) ⟨415802, by rfl⟩ : syracuseStep 2217613 = 831605) (by norm_num)
theorem B2627237 : Blo 1750576 2627237 := bbase (se 4 (by rfl) ⟨246303, by rfl⟩ : syracuseStep 2627237 = 492607) (by norm_num)
theorem B2627261 : Blo 1750576 2627261 := bbase (se 3 (by rfl) ⟨492611, by rfl⟩ : syracuseStep 2627261 = 985223) (by norm_num)
theorem B2627285 : Blo 1750576 2627285 := bbase (se 7 (by rfl) ⟨30788, by rfl⟩ : syracuseStep 2627285 = 61577) (by norm_num)
theorem B2954981 : Blo 1750576 2954981 := bbase (se 4 (by rfl) ⟨277029, by rfl⟩ : syracuseStep 2954981 = 554059) (by norm_num)
theorem B6649573 : Blo 1750576 6649573 := bbase (se 4 (by rfl) ⟨623397, by rfl⟩ : syracuseStep 6649573 = 1246795) (by norm_num)
theorem B2627309 : Blo 1750576 2627309 := bbase (se 3 (by rfl) ⟨492620, by rfl⟩ : syracuseStep 2627309 = 985241) (by norm_num)
theorem B2217709 : Blo 1750576 2217709 := bbase (se 3 (by rfl) ⟨415820, by rfl⟩ : syracuseStep 2217709 = 831641) (by norm_num)
theorem B1996537 : Blo 1750576 1996537 := bbase (se 2 (by rfl) ⟨748701, by rfl⟩ : syracuseStep 1996537 = 1497403) (by norm_num)
theorem B2627333 : Blo 1750576 2627333 := bbase (se 4 (by rfl) ⟨246312, by rfl⟩ : syracuseStep 2627333 = 492625) (by norm_num)
theorem B2627357 : Blo 1750576 2627357 := bbase (se 3 (by rfl) ⟨492629, by rfl⟩ : syracuseStep 2627357 = 985259) (by norm_num)
theorem B3323693 : Blo 1750576 3323693 := bbase (se 3 (by rfl) ⟨623192, by rfl⟩ : syracuseStep 3323693 = 1246385) (by norm_num)
theorem B2627381 : Blo 1750576 2627381 := bbase (se 5 (by rfl) ⟨123158, by rfl⟩ : syracuseStep 2627381 = 246317) (by norm_num)
theorem B1775417 : Blo 1750576 1775417 := bbase (se 2 (by rfl) ⟨665781, by rfl⟩ : syracuseStep 1775417 = 1331563) (by norm_num)
theorem B2627405 : Blo 1750576 2627405 := bbase (se 3 (by rfl) ⟨492638, by rfl⟩ : syracuseStep 2627405 = 985277) (by norm_num)
theorem B5912405 : Blo 1750576 5912405 := bbase (se 9 (by rfl) ⟨17321, by rfl⟩ : syracuseStep 5912405 = 34643) (by norm_num)
theorem B1996633 : Blo 1750576 1996633 := bbase (se 2 (by rfl) ⟨748737, by rfl⟩ : syracuseStep 1996633 = 1497475) (by norm_num)
theorem B2955109 : Blo 1750576 2955109 := bbase (se 4 (by rfl) ⟨277041, by rfl⟩ : syracuseStep 2955109 = 554083) (by norm_num)
theorem B2627429 : Blo 1750576 2627429 := bbase (se 4 (by rfl) ⟨246321, by rfl⟩ : syracuseStep 2627429 = 492643) (by norm_num)
theorem B2627453 : Blo 1750576 2627453 := bbase (se 3 (by rfl) ⟨492647, by rfl⟩ : syracuseStep 2627453 = 985295) (by norm_num)
theorem B3741565 : Blo 1750576 3741565 := bbase (se 3 (by rfl) ⟨701543, by rfl⟩ : syracuseStep 3741565 = 1403087) (by norm_num)
theorem B7485317 : Blo 1750576 7485317 := bbase (se 4 (by rfl) ⟨701748, by rfl⟩ : syracuseStep 7485317 = 1403497) (by norm_num)
theorem B2627477 : Blo 1750576 2627477 := bbase (se 6 (by rfl) ⟨61581, by rfl⟩ : syracuseStep 2627477 = 123163) (by norm_num)
theorem B2217881 : Blo 1750576 2217881 := bbase (se 2 (by rfl) ⟨831705, by rfl⟩ : syracuseStep 2217881 = 1663411) (by norm_num)
theorem B2627501 : Blo 1750576 2627501 := bbase (se 3 (by rfl) ⟨492656, by rfl⟩ : syracuseStep 2627501 = 985313) (by norm_num)
theorem B4986805 : Blo 1750576 4986805 := bbase (se 5 (by rfl) ⟨233756, by rfl⟩ : syracuseStep 4986805 = 467513) (by norm_num)
theorem B2955197 : Blo 1750576 2955197 := bbase (se 3 (by rfl) ⟨554099, by rfl⟩ : syracuseStep 2955197 = 1108199) (by norm_num)
theorem B3323845 : Blo 1750576 3323845 := bbase (se 4 (by rfl) ⟨311610, by rfl⟩ : syracuseStep 3323845 = 623221) (by norm_num)
theorem B2627525 : Blo 1750576 2627525 := bbase (se 4 (by rfl) ⟨246330, by rfl⟩ : syracuseStep 2627525 = 492661) (by norm_num)
theorem B2217937 : Blo 1750576 2217937 := bbase (se 2 (by rfl) ⟨831726, by rfl⟩ : syracuseStep 2217937 = 1663453) (by norm_num)
theorem B2627549 : Blo 1750576 2627549 := bbase (se 3 (by rfl) ⟨492665, by rfl⟩ : syracuseStep 2627549 = 985331) (by norm_num)
theorem B13293557 : Blo 1750576 13293557 := bbase (se 5 (by rfl) ⟨623135, by rfl⟩ : syracuseStep 13293557 = 1246271) (by norm_num)
theorem B7100405 : Blo 1750576 7100405 := bbase (se 5 (by rfl) ⟨332831, by rfl⟩ : syracuseStep 7100405 = 665663) (by norm_num)
theorem B9975797 : Blo 1750576 9975797 := bbase (se 5 (by rfl) ⟨467615, by rfl⟩ : syracuseStep 9975797 = 935231) (by norm_num)
theorem B2627573 : Blo 1750576 2627573 := bbase (se 5 (by rfl) ⟨123167, by rfl⟩ : syracuseStep 2627573 = 246335) (by norm_num)
theorem B2627597 : Blo 1750576 2627597 := bbase (se 3 (by rfl) ⟨492674, by rfl⟩ : syracuseStep 2627597 = 985349) (by norm_num)
theorem B6649877 : Blo 1750576 6649877 := bbase (se 6 (by rfl) ⟨155856, by rfl⟩ : syracuseStep 6649877 = 311713) (by norm_num)
theorem B2627621 : Blo 1750576 2627621 := bbase (se 4 (by rfl) ⟨246339, by rfl⟩ : syracuseStep 2627621 = 492679) (by norm_num)
theorem B2218033 : Blo 1750576 2218033 := bbase (se 2 (by rfl) ⟨831762, by rfl⟩ : syracuseStep 2218033 = 1663525) (by norm_num)
theorem B3790901 : Blo 1750576 3790901 := bbase (se 5 (by rfl) ⟨177698, by rfl⟩ : syracuseStep 3790901 = 355397) (by norm_num)
theorem B2955325 : Blo 1750576 2955325 := bbase (se 3 (by rfl) ⟨554123, by rfl⟩ : syracuseStep 2955325 = 1108247) (by norm_num)
theorem B2627645 : Blo 1750576 2627645 := bbase (se 3 (by rfl) ⟨492683, by rfl⟩ : syracuseStep 2627645 = 985367) (by norm_num)
theorem B14964821 : Blo 1750576 14964821 := bbase (se 8 (by rfl) ⟨87684, by rfl⟩ : syracuseStep 14964821 = 175369) (by norm_num)
theorem B2627669 : Blo 1750576 2627669 := bbase (se 8 (by rfl) ⟨15396, by rfl⟩ : syracuseStep 2627669 = 30793) (by norm_num)
theorem B2627693 : Blo 1750576 2627693 := bbase (se 3 (by rfl) ⟨492692, by rfl⟩ : syracuseStep 2627693 = 985385) (by norm_num)
theorem B2627717 : Blo 1750576 2627717 := bbase (se 4 (by rfl) ⟨246348, by rfl⟩ : syracuseStep 2627717 = 492697) (by norm_num)
theorem B2955413 : Blo 1750576 2955413 := bbase (se 6 (by rfl) ⟨69267, by rfl⟩ : syracuseStep 2955413 = 138535) (by norm_num)
theorem B2627741 : Blo 1750576 2627741 := bbase (se 3 (by rfl) ⟨492701, by rfl⟩ : syracuseStep 2627741 = 985403) (by norm_num)
theorem B2627765 : Blo 1750576 2627765 := bbase (se 5 (by rfl) ⟨123176, by rfl⟩ : syracuseStep 2627765 = 246353) (by norm_num)
theorem B2627789 : Blo 1750576 2627789 := bbase (se 3 (by rfl) ⟨492710, by rfl⟩ : syracuseStep 2627789 = 985421) (by norm_num)
theorem B14956757 : Blo 1750576 14956757 := bbase (se 7 (by rfl) ⟨175274, by rfl⟩ : syracuseStep 14956757 = 350549) (by norm_num)
theorem B2627813 : Blo 1750576 2627813 := bbase (se 4 (by rfl) ⟨246357, by rfl⟩ : syracuseStep 2627813 = 492715) (by norm_num)
theorem B3324149 : Blo 1750576 3324149 := bbase (se 5 (by rfl) ⟨155819, by rfl⟩ : syracuseStep 3324149 = 311639) (by norm_num)
theorem B8534261 : Blo 1750576 8534261 := bbase (se 5 (by rfl) ⟨400043, by rfl⟩ : syracuseStep 8534261 = 800087) (by norm_num)
theorem B2627837 : Blo 1750576 2627837 := bbase (se 3 (by rfl) ⟨492719, by rfl⟩ : syracuseStep 2627837 = 985439) (by norm_num)
theorem B5912837 : Blo 1750576 5912837 := bbase (se 4 (by rfl) ⟨554328, by rfl⟩ : syracuseStep 5912837 = 1108657) (by norm_num)
theorem B2955541 : Blo 1750576 2955541 := bbase (se 6 (by rfl) ⟨69270, by rfl⟩ : syracuseStep 2955541 = 138541) (by norm_num)
theorem B2627861 : Blo 1750576 2627861 := bbase (se 6 (by rfl) ⟨61590, by rfl⟩ : syracuseStep 2627861 = 123181) (by norm_num)
theorem B2996509 : Blo 1750576 2996509 := bbase (se 3 (by rfl) ⟨561845, by rfl⟩ : syracuseStep 2996509 = 1123691) (by norm_num)
theorem B4208933 : Blo 1750576 4208933 := bbase (se 4 (by rfl) ⟨394587, by rfl⟩ : syracuseStep 4208933 = 789175) (by norm_num)
theorem B2627885 : Blo 1750576 2627885 := bbase (se 3 (by rfl) ⟨492728, by rfl⟩ : syracuseStep 2627885 = 985457) (by norm_num)
theorem B2103617 : Blo 1750576 2103617 := bbase (se 2 (by rfl) ⟨788856, by rfl⟩ : syracuseStep 2103617 = 1577713) (by norm_num)
theorem B2627909 : Blo 1750576 2627909 := bbase (se 4 (by rfl) ⟨246366, by rfl⟩ : syracuseStep 2627909 = 492733) (by norm_num)
theorem B2881885 : Blo 1750576 2881885 := bbase (se 3 (by rfl) ⟨540353, by rfl⟩ : syracuseStep 2881885 = 1080707) (by norm_num)
theorem B2627933 : Blo 1750576 2627933 := bbase (se 3 (by rfl) ⟨492737, by rfl⟩ : syracuseStep 2627933 = 985475) (by norm_num)
theorem B2955629 : Blo 1750576 2955629 := bbase (se 3 (by rfl) ⟨554180, by rfl⟩ : syracuseStep 2955629 = 1108361) (by norm_num)
theorem B2627957 : Blo 1750576 2627957 := bbase (se 5 (by rfl) ⟨123185, by rfl⟩ : syracuseStep 2627957 = 246371) (by norm_num)
theorem B1776001 : Blo 1750576 1776001 := bbase (se 2 (by rfl) ⟨666000, by rfl⟩ : syracuseStep 1776001 = 1332001) (by norm_num)
theorem B5609861 : Blo 1750576 5609861 := bbase (se 4 (by rfl) ⟨525924, by rfl⟩ : syracuseStep 5609861 = 1051849) (by norm_num)
theorem B2627981 : Blo 1750576 2627981 := bbase (se 3 (by rfl) ⟨492746, by rfl⟩ : syracuseStep 2627981 = 985493) (by norm_num)
theorem B2628005 : Blo 1750576 2628005 := bbase (se 4 (by rfl) ⟨246375, by rfl⟩ : syracuseStep 2628005 = 492751) (by norm_num)
theorem B8870309 : Blo 1750576 8870309 := bbase (se 4 (by rfl) ⟨831591, by rfl⟩ : syracuseStep 8870309 = 1663183) (by norm_num)
theorem B2628029 : Blo 1750576 2628029 := bbase (se 3 (by rfl) ⟨492755, by rfl⟩ : syracuseStep 2628029 = 985511) (by norm_num)
theorem B2628053 : Blo 1750576 2628053 := bbase (se 7 (by rfl) ⟨30797, by rfl⟩ : syracuseStep 2628053 = 61595) (by norm_num)
theorem B2955757 : Blo 1750576 2955757 := bbase (se 3 (by rfl) ⟨554204, by rfl⟩ : syracuseStep 2955757 = 1108409) (by norm_num)
theorem B2628077 : Blo 1750576 2628077 := bbase (se 3 (by rfl) ⟨492764, by rfl⟩ : syracuseStep 2628077 = 985529) (by norm_num)
theorem B3938813 : Blo 1750576 3938813 := bbase (se 3 (by rfl) ⟨738527, by rfl⟩ : syracuseStep 3938813 = 1477055) (by norm_num)
theorem B5609989 : Blo 1750576 5609989 := bbase (se 4 (by rfl) ⟨525936, by rfl⟩ : syracuseStep 5609989 = 1051873) (by norm_num)
theorem B2628101 : Blo 1750576 2628101 := bbase (se 4 (by rfl) ⟨246384, by rfl⟩ : syracuseStep 2628101 = 492769) (by norm_num)
theorem B2628125 : Blo 1750576 2628125 := bbase (se 3 (by rfl) ⟨492773, by rfl⟩ : syracuseStep 2628125 = 985547) (by norm_num)
theorem B2628149 : Blo 1750576 2628149 := bbase (se 5 (by rfl) ⟨123194, by rfl⟩ : syracuseStep 2628149 = 246389) (by norm_num)
theorem B3938885 : Blo 1750576 3938885 := bbase (se 4 (by rfl) ⟨369270, by rfl⟩ : syracuseStep 3938885 = 738541) (by norm_num)
theorem B2955845 : Blo 1750576 2955845 := bbase (se 4 (by rfl) ⟨277110, by rfl⟩ : syracuseStep 2955845 = 554221) (by norm_num)
theorem B2628173 : Blo 1750576 2628173 := bbase (se 3 (by rfl) ⟨492782, by rfl⟩ : syracuseStep 2628173 = 985565) (by norm_num)
theorem B2628197 : Blo 1750576 2628197 := bbase (se 4 (by rfl) ⟨246393, by rfl⟩ : syracuseStep 2628197 = 492787) (by norm_num)
theorem B2628221 : Blo 1750576 2628221 := bbase (se 3 (by rfl) ⟨492791, by rfl⟩ : syracuseStep 2628221 = 985583) (by norm_num)
theorem B3938957 : Blo 1750576 3938957 := bbase (se 3 (by rfl) ⟨738554, by rfl⟩ : syracuseStep 3938957 = 1477109) (by norm_num)
theorem B2628245 : Blo 1750576 2628245 := bbase (se 6 (by rfl) ⟨61599, by rfl⟩ : syracuseStep 2628245 = 123199) (by norm_num)
theorem B1776277 : Blo 1750576 1776277 := bbase (se 6 (by rfl) ⟨41631, by rfl⟩ : syracuseStep 1776277 = 83263) (by norm_num)
theorem B2628269 : Blo 1750576 2628269 := bbase (se 3 (by rfl) ⟨492800, by rfl⟩ : syracuseStep 2628269 = 985601) (by norm_num)
theorem B5913269 : Blo 1750576 5913269 := bbase (se 5 (by rfl) ⟨277184, by rfl⟩ : syracuseStep 5913269 = 554369) (by norm_num)
theorem B1997509 : Blo 1750576 1997509 := bbase (se 4 (by rfl) ⟨187266, by rfl⟩ : syracuseStep 1997509 = 374533) (by norm_num)
theorem B2955973 : Blo 1750576 2955973 := bbase (se 4 (by rfl) ⟨277122, by rfl⟩ : syracuseStep 2955973 = 554245) (by norm_num)
theorem B2628293 : Blo 1750576 2628293 := bbase (se 4 (by rfl) ⟨246402, by rfl⟩ : syracuseStep 2628293 = 492805) (by norm_num)
theorem B4496077 : Blo 1750576 4496077 := bbase (se 3 (by rfl) ⟨843014, by rfl⟩ : syracuseStep 4496077 = 1686029) (by norm_num)
theorem B3939029 : Blo 1750576 3939029 := bbase (se 7 (by rfl) ⟨46160, by rfl⟩ : syracuseStep 3939029 = 92321) (by norm_num)
theorem B2628317 : Blo 1750576 2628317 := bbase (se 3 (by rfl) ⟨492809, by rfl⟩ : syracuseStep 2628317 = 985619) (by norm_num)
theorem B2628341 : Blo 1750576 2628341 := bbase (se 5 (by rfl) ⟨123203, by rfl⟩ : syracuseStep 2628341 = 246407) (by norm_num)
theorem B3742453 : Blo 1750576 3742453 := bbase (se 5 (by rfl) ⟨175427, by rfl⟩ : syracuseStep 3742453 = 350855) (by norm_num)
theorem B7478021 : Blo 1750576 7478021 := bbase (se 4 (by rfl) ⟨701064, by rfl⟩ : syracuseStep 7478021 = 1402129) (by norm_num)
theorem B2628365 : Blo 1750576 2628365 := bbase (se 3 (by rfl) ⟨492818, by rfl⟩ : syracuseStep 2628365 = 985637) (by norm_num)
theorem B3939101 : Blo 1750576 3939101 := bbase (se 3 (by rfl) ⟨738581, by rfl⟩ : syracuseStep 3939101 = 1477163) (by norm_num)
theorem B2956061 : Blo 1750576 2956061 := bbase (se 3 (by rfl) ⟨554261, by rfl⟩ : syracuseStep 2956061 = 1108523) (by norm_num)
theorem B8534821 : Blo 1750576 8534821 := bbase (se 4 (by rfl) ⟨800139, by rfl⟩ : syracuseStep 8534821 = 1600279) (by norm_num)
theorem B2628389 : Blo 1750576 2628389 := bbase (se 4 (by rfl) ⟨246411, by rfl⟩ : syracuseStep 2628389 = 492823) (by norm_num)
theorem B2628413 : Blo 1750576 2628413 := bbase (se 3 (by rfl) ⟨492827, by rfl⟩ : syracuseStep 2628413 = 985655) (by norm_num)
theorem B8862533 : Blo 1750576 8862533 := bbase (se 4 (by rfl) ⟨830862, by rfl⟩ : syracuseStep 8862533 = 1661725) (by norm_num)
theorem B2628437 : Blo 1750576 2628437 := bbase (se 9 (by rfl) ⟨7700, by rfl⟩ : syracuseStep 2628437 = 15401) (by norm_num)
theorem B3939173 : Blo 1750576 3939173 := bbase (se 4 (by rfl) ⟨369297, by rfl⟩ : syracuseStep 3939173 = 738595) (by norm_num)
theorem B1997669 : Blo 1750576 1997669 := bbase (se 4 (by rfl) ⟨187281, by rfl⟩ : syracuseStep 1997669 = 374563) (by norm_num)
theorem B2628461 : Blo 1750576 2628461 := bbase (se 3 (by rfl) ⟨492836, by rfl⟩ : syracuseStep 2628461 = 985673) (by norm_num)
theorem B8420213 : Blo 1750576 8420213 := bbase (se 5 (by rfl) ⟨394697, by rfl⟩ : syracuseStep 8420213 = 789395) (by norm_num)
theorem B2628485 : Blo 1750576 2628485 := bbase (se 4 (by rfl) ⟨246420, by rfl⟩ : syracuseStep 2628485 = 492841) (by norm_num)
theorem B3791765 : Blo 1750576 3791765 := bbase (se 6 (by rfl) ⟨88869, by rfl⟩ : syracuseStep 3791765 = 177739) (by norm_num)
theorem B2956189 : Blo 1750576 2956189 := bbase (se 3 (by rfl) ⟨554285, by rfl⟩ : syracuseStep 2956189 = 1108571) (by norm_num)
theorem B2628509 : Blo 1750576 2628509 := bbase (se 3 (by rfl) ⟨492845, by rfl⟩ : syracuseStep 2628509 = 985691) (by norm_num)
theorem B3939245 : Blo 1750576 3939245 := bbase (se 3 (by rfl) ⟨738608, by rfl⟩ : syracuseStep 3939245 = 1477217) (by norm_num)
theorem B2628533 : Blo 1750576 2628533 := bbase (se 5 (by rfl) ⟨123212, by rfl⟩ : syracuseStep 2628533 = 246425) (by norm_num)
theorem B2628557 : Blo 1750576 2628557 := bbase (se 3 (by rfl) ⟨492854, by rfl⟩ : syracuseStep 2628557 = 985709) (by norm_num)
theorem B3324901 : Blo 1750576 3324901 := bbase (se 4 (by rfl) ⟨311709, by rfl⟩ : syracuseStep 3324901 = 623419) (by norm_num)
theorem B2628581 : Blo 1750576 2628581 := bbase (se 4 (by rfl) ⟨246429, by rfl⟩ : syracuseStep 2628581 = 492859) (by norm_num)
theorem B3939317 : Blo 1750576 3939317 := bbase (se 5 (by rfl) ⟨184655, by rfl⟩ : syracuseStep 3939317 = 369311) (by norm_num)
theorem B2956277 : Blo 1750576 2956277 := bbase (se 5 (by rfl) ⟨138575, by rfl⟩ : syracuseStep 2956277 = 277151) (by norm_num)
theorem B2628605 : Blo 1750576 2628605 := bbase (se 3 (by rfl) ⟨492863, by rfl⟩ : syracuseStep 2628605 = 985727) (by norm_num)
theorem B4987909 : Blo 1750576 4987909 := bbase (se 4 (by rfl) ⟨467616, by rfl⟩ : syracuseStep 4987909 = 935233) (by norm_num)
theorem B2628629 : Blo 1750576 2628629 := bbase (se 6 (by rfl) ⟨61608, by rfl⟩ : syracuseStep 2628629 = 123217) (by norm_num)
theorem B2628653 : Blo 1750576 2628653 := bbase (se 3 (by rfl) ⟨492872, by rfl⟩ : syracuseStep 2628653 = 985745) (by norm_num)
theorem B3939389 : Blo 1750576 3939389 := bbase (se 3 (by rfl) ⟨738635, by rfl⟩ : syracuseStep 3939389 = 1477271) (by norm_num)
theorem B2628677 : Blo 1750576 2628677 := bbase (se 4 (by rfl) ⟨246438, by rfl⟩ : syracuseStep 2628677 = 492877) (by norm_num)
theorem B2628701 : Blo 1750576 2628701 := bbase (se 3 (by rfl) ⟨492881, by rfl⟩ : syracuseStep 2628701 = 985763) (by norm_num)
theorem B5913701 : Blo 1750576 5913701 := bbase (se 4 (by rfl) ⟨554409, by rfl⟩ : syracuseStep 5913701 = 1108819) (by norm_num)
theorem B3325045 : Blo 1750576 3325045 := bbase (se 5 (by rfl) ⟨155861, by rfl⟩ : syracuseStep 3325045 = 311723) (by norm_num)
theorem B2956405 : Blo 1750576 2956405 := bbase (se 5 (by rfl) ⟨138581, by rfl⟩ : syracuseStep 2956405 = 277163) (by norm_num)
theorem B2628725 : Blo 1750576 2628725 := bbase (se 5 (by rfl) ⟨123221, by rfl⟩ : syracuseStep 2628725 = 246443) (by norm_num)
theorem B3939461 : Blo 1750576 3939461 := bbase (se 4 (by rfl) ⟨369324, by rfl⟩ : syracuseStep 3939461 = 738649) (by norm_num)
theorem B2628749 : Blo 1750576 2628749 := bbase (se 3 (by rfl) ⟨492890, by rfl⟩ : syracuseStep 2628749 = 985781) (by norm_num)
theorem B2628773 : Blo 1750576 2628773 := bbase (se 4 (by rfl) ⟨246447, by rfl⟩ : syracuseStep 2628773 = 492895) (by norm_num)
theorem B2628797 : Blo 1750576 2628797 := bbase (se 3 (by rfl) ⟨492899, by rfl⟩ : syracuseStep 2628797 = 985799) (by norm_num)
theorem B3939533 : Blo 1750576 3939533 := bbase (se 3 (by rfl) ⟨738662, by rfl⟩ : syracuseStep 3939533 = 1477325) (by norm_num)
theorem B2956493 : Blo 1750576 2956493 := bbase (se 3 (by rfl) ⟨554342, by rfl⟩ : syracuseStep 2956493 = 1108685) (by norm_num)
theorem B2628821 : Blo 1750576 2628821 := bbase (se 7 (by rfl) ⟨30806, by rfl⟩ : syracuseStep 2628821 = 61613) (by norm_num)
theorem B3742949 : Blo 1750576 3742949 := bbase (se 4 (by rfl) ⟨350901, by rfl⟩ : syracuseStep 3742949 = 701803) (by norm_num)
theorem B2628845 : Blo 1750576 2628845 := bbase (se 3 (by rfl) ⟨492908, by rfl⟩ : syracuseStep 2628845 = 985817) (by norm_num)
theorem B3939605 : Blo 1750576 3939605 := bbase (se 6 (by rfl) ⟨92334, by rfl⟩ : syracuseStep 3939605 = 184669) (by norm_num)
theorem B3325205 : Blo 1750576 3325205 := bbase (se 6 (by rfl) ⟨77934, by rfl⟩ : syracuseStep 3325205 = 155869) (by norm_num)
theorem B4799765 : Blo 1750576 4799765 := bbase (se 6 (by rfl) ⟨112494, by rfl⟩ : syracuseStep 4799765 = 224989) (by norm_num)
theorem B2956621 : Blo 1750576 2956621 := bbase (se 3 (by rfl) ⟨554366, by rfl⟩ : syracuseStep 2956621 = 1108733) (by norm_num)
theorem B3939677 : Blo 1750576 3939677 := bbase (se 3 (by rfl) ⟨738689, by rfl⟩ : syracuseStep 3939677 = 1477379) (by norm_num)
theorem B3939749 : Blo 1750576 3939749 := bbase (se 4 (by rfl) ⟨369351, by rfl⟩ : syracuseStep 3939749 = 738703) (by norm_num)
theorem B3325349 : Blo 1750576 3325349 := bbase (se 4 (by rfl) ⟨311751, by rfl⟩ : syracuseStep 3325349 = 623503) (by norm_num)
theorem B2956709 : Blo 1750576 2956709 := bbase (se 4 (by rfl) ⟨277191, by rfl⟩ : syracuseStep 2956709 = 554383) (by norm_num)
theorem B3939821 : Blo 1750576 3939821 := bbase (se 3 (by rfl) ⟨738716, by rfl⟩ : syracuseStep 3939821 = 1477433) (by norm_num)
theorem B2104813 : Blo 1750576 2104813 := bbase (se 3 (by rfl) ⟨394652, by rfl⟩ : syracuseStep 2104813 = 789305) (by norm_num)
theorem B5914133 : Blo 1750576 5914133 := bbase (se 6 (by rfl) ⟨138612, by rfl⟩ : syracuseStep 5914133 = 277225) (by norm_num)
theorem B2956837 : Blo 1750576 2956837 := bbase (se 4 (by rfl) ⟨277203, by rfl⟩ : syracuseStep 2956837 = 554407) (by norm_num)
theorem B3939893 : Blo 1750576 3939893 := bbase (se 5 (by rfl) ⟨184682, by rfl⟩ : syracuseStep 3939893 = 369365) (by norm_num)
theorem B2104885 : Blo 1750576 2104885 := bbase (se 5 (by rfl) ⟨98666, by rfl⟩ : syracuseStep 2104885 = 197333) (by norm_num)
theorem B4431469 : Blo 1750576 4431469 := bbase (se 3 (by rfl) ⟨830900, by rfl⟩ : syracuseStep 4431469 = 1661801) (by norm_num)
theorem B3939965 : Blo 1750576 3939965 := bbase (se 3 (by rfl) ⟨738743, by rfl⟩ : syracuseStep 3939965 = 1477487) (by norm_num)
theorem B2956925 : Blo 1750576 2956925 := bbase (se 3 (by rfl) ⟨554423, by rfl⟩ : syracuseStep 2956925 = 1108847) (by norm_num)
theorem B4210309 : Blo 1750576 4210309 := bbase (se 4 (by rfl) ⟨394716, by rfl⟩ : syracuseStep 4210309 = 789433) (by norm_num)
theorem B8871605 : Blo 1750576 8871605 := bbase (se 5 (by rfl) ⟨415856, by rfl⟩ : syracuseStep 8871605 = 831713) (by norm_num)
theorem B3940037 : Blo 1750576 3940037 := bbase (se 4 (by rfl) ⟨369378, by rfl⟩ : syracuseStep 3940037 = 738757) (by norm_num)
theorem B3325637 : Blo 1750576 3325637 := bbase (se 4 (by rfl) ⟨311778, by rfl⟩ : syracuseStep 3325637 = 623557) (by norm_num)
theorem B4431581 : Blo 1750576 4431581 := bbase (se 3 (by rfl) ⟨830921, by rfl⟩ : syracuseStep 4431581 = 1661843) (by norm_num)
theorem B2957053 : Blo 1750576 2957053 := bbase (se 3 (by rfl) ⟨554447, by rfl⟩ : syracuseStep 2957053 = 1108895) (by norm_num)
theorem B3940109 : Blo 1750576 3940109 := bbase (se 3 (by rfl) ⟨738770, by rfl⟩ : syracuseStep 3940109 = 1477541) (by norm_num)
theorem B8986405 : Blo 1750576 8986405 := bbase (se 4 (by rfl) ⟨842475, by rfl⟩ : syracuseStep 8986405 = 1684951) (by norm_num)
theorem B3940181 : Blo 1750576 3940181 := bbase (se 9 (by rfl) ⟨11543, by rfl⟩ : syracuseStep 3940181 = 23087) (by norm_num)
theorem B2957141 : Blo 1750576 2957141 := bbase (se 9 (by rfl) ⟨8663, by rfl⟩ : syracuseStep 2957141 = 17327) (by norm_num)
theorem B3325789 : Blo 1750576 3325789 := bbase (se 3 (by rfl) ⟨623585, by rfl⟩ : syracuseStep 3325789 = 1247171) (by norm_num)
theorem B7987045 : Blo 1750576 7987045 := bbase (se 4 (by rfl) ⟨748785, by rfl⟩ : syracuseStep 7987045 = 1497571) (by norm_num)
theorem B4431773 : Blo 1750576 4431773 := bbase (se 3 (by rfl) ⟨830957, by rfl⟩ : syracuseStep 4431773 = 1661915) (by norm_num)
theorem B3940253 : Blo 1750576 3940253 := bbase (se 3 (by rfl) ⟨738797, by rfl⟩ : syracuseStep 3940253 = 1477595) (by norm_num)
theorem B5914565 : Blo 1750576 5914565 := bbase (se 4 (by rfl) ⟨554490, by rfl⟩ : syracuseStep 5914565 = 1108981) (by norm_num)
theorem B2957269 : Blo 1750576 2957269 := bbase (se 7 (by rfl) ⟨34655, by rfl⟩ : syracuseStep 2957269 = 69311) (by norm_num)
theorem B3940325 : Blo 1750576 3940325 := bbase (se 4 (by rfl) ⟨369405, by rfl⟩ : syracuseStep 3940325 = 738811) (by norm_num)
theorem B2105347 : Blo 1750576 2105347 := bstep (se 1 (by rfl) ⟨1579010, by rfl⟩ : syracuseStep 2105347 = 3158021) B3158021
theorem B5914673 : Blo 1750576 5914673 := bstep (se 2 (by rfl) ⟨2218002, by rfl⟩ : syracuseStep 5914673 = 4436005) B4436005
theorem B2957377 : Blo 1750576 2957377 := bstep (se 2 (by rfl) ⟨1109016, by rfl⟩ : syracuseStep 2957377 = 2218033) B2218033
theorem B3940433 : Blo 1750576 3940433 := bstep (se 2 (by rfl) ⟨1477662, by rfl⟩ : syracuseStep 3940433 = 2955325) B2955325
theorem B3940451 : Blo 1750576 3940451 := bstep (se 1 (by rfl) ⟨2955338, by rfl⟩ : syracuseStep 3940451 = 5910677) B5910677
theorem B6652003 : Blo 1750576 6652003 := bstep (se 1 (by rfl) ⟨4989002, by rfl⟩ : syracuseStep 6652003 = 9978005) B9978005
theorem B2957411 : Blo 1750576 2957411 := bstep (se 1 (by rfl) ⟨2218058, by rfl⟩ : syracuseStep 2957411 = 4436117) B4436117
theorem B4432067 : Blo 1750576 4432067 := bstep (se 1 (by rfl) ⟨3324050, by rfl⟩ : syracuseStep 4432067 = 6648101) B6648101
theorem B3326275 : Blo 1750576 3326275 := bstep (se 1 (by rfl) ⟨2494706, by rfl⟩ : syracuseStep 3326275 = 4989413) B4989413
theorem B3940721 : Blo 1750576 3940721 := bstep (se 2 (by rfl) ⟨1477770, by rfl⟩ : syracuseStep 3940721 = 2955541) B2955541
theorem B3326321 : Blo 1750576 3326321 := bstep (se 2 (by rfl) ⟨1247370, by rfl⟩ : syracuseStep 3326321 = 2494741) B2494741
theorem B4432259 : Blo 1750576 4432259 := bstep (se 1 (by rfl) ⟨3324194, by rfl⟩ : syracuseStep 4432259 = 6648389) B6648389
theorem B3940739 : Blo 1750576 3940739 := bstep (se 1 (by rfl) ⟨2955554, by rfl⟩ : syracuseStep 3940739 = 5911109) B5911109
theorem B63906245 : Blo 1750576 63906245 := bstep (se 4 (by rfl) ⟨5991210, by rfl⟩ : syracuseStep 63906245 = 11982421) B11982421
theorem B3842513 : Blo 1750576 3842513 := bstep (se 2 (by rfl) ⟨1440942, by rfl⟩ : syracuseStep 3842513 = 2881885) B2881885
theorem B5767661 : Blo 1750576 5767661 := bstep (se 3 (by rfl) ⟨1081436, by rfl⟩ : syracuseStep 5767661 = 2162873) B2162873
theorem B14967281 : Blo 1750576 14967281 := bstep (se 2 (by rfl) ⟨5612730, by rfl⟩ : syracuseStep 14967281 = 11225461) B11225461
theorem B2368001 : Blo 1750576 2368001 := bstep (se 2 (by rfl) ⟨888000, by rfl⟩ : syracuseStep 2368001 = 1776001) B1776001
theorem B4735505 : Blo 1750576 4735505 := bstep (se 2 (by rfl) ⟨1775814, by rfl⟩ : syracuseStep 4735505 = 3551629) B3551629
theorem B4989539 : Blo 1750576 4989539 := bstep (se 1 (by rfl) ⟨3742154, by rfl⟩ : syracuseStep 4989539 = 7484309) B7484309
theorem B22758029 : Blo 1750576 22758029 := bstep (se 3 (by rfl) ⟨4267130, by rfl⟩ : syracuseStep 22758029 = 8534261) B8534261
theorem B3941009 : Blo 1750576 3941009 := bstep (se 2 (by rfl) ⟨1477878, by rfl⟩ : syracuseStep 3941009 = 2955757) B2955757
theorem B3326609 : Blo 1750576 3326609 := bstep (se 2 (by rfl) ⟨1247478, by rfl⟩ : syracuseStep 3326609 = 2494957) B2494957
theorem B3941027 : Blo 1750576 3941027 := bstep (se 1 (by rfl) ⟨2955770, by rfl⟩ : syracuseStep 3941027 = 5911541) B5911541
theorem B7479985 : Blo 1750576 7479985 := bstep (se 2 (by rfl) ⟨2804994, by rfl⟩ : syracuseStep 7479985 = 5609989) B5609989
theorem B7201457 : Blo 1750576 7201457 := bstep (se 2 (by rfl) ⟨2700546, by rfl⟩ : syracuseStep 7201457 = 5401093) B5401093
theorem B25608901 : Blo 1750576 25608901 := bstep (se 4 (by rfl) ⟨2400834, by rfl⟩ : syracuseStep 25608901 = 4801669) B4801669
theorem B11223821 : Blo 1750576 11223821 := bstep (se 3 (by rfl) ⟨2104466, by rfl⟩ : syracuseStep 11223821 = 4208933) B4208933
theorem B2368369 : Blo 1750576 2368369 := bstep (se 2 (by rfl) ⟨888138, by rfl⟩ : syracuseStep 2368369 = 1776277) B1776277
theorem B4989869 : Blo 1750576 4989869 := bstep (se 3 (by rfl) ⟨935600, by rfl⟩ : syracuseStep 4989869 = 1871201) B1871201
theorem B5989297 : Blo 1750576 5989297 := bstep (se 2 (by rfl) ⟨2245986, by rfl⟩ : syracuseStep 5989297 = 4491973) B4491973
theorem B2663345 : Blo 1750576 2663345 := bstep (se 2 (by rfl) ⟨998754, by rfl⟩ : syracuseStep 2663345 = 1997509) B1997509
theorem B3941297 : Blo 1750576 3941297 := bstep (se 2 (by rfl) ⟨1477986, by rfl⟩ : syracuseStep 3941297 = 2955973) B2955973
theorem B3941315 : Blo 1750576 3941315 := bstep (se 1 (by rfl) ⟨2955986, by rfl⟩ : syracuseStep 3941315 = 5911973) B5911973
theorem B4989937 : Blo 1750576 4989937 := bstep (se 2 (by rfl) ⟨1871226, by rfl⟩ : syracuseStep 4989937 = 3742453) B3742453
theorem B2843681 : Blo 1750576 2843681 := bstep (se 2 (by rfl) ⟨1066380, by rfl⟩ : syracuseStep 2843681 = 2132761) B2132761
theorem B11379761 : Blo 1750576 11379761 := bstep (se 2 (by rfl) ⟨4267410, by rfl⟩ : syracuseStep 11379761 = 8534821) B8534821
theorem B2663491 : Blo 1750576 2663491 := bstep (se 1 (by rfl) ⟨1997618, by rfl⟩ : syracuseStep 2663491 = 3995237) B3995237
theorem B21898421 : Blo 1750576 21898421 := bstep (se 5 (by rfl) ⟨1026488, by rfl⟩ : syracuseStep 21898421 = 2052977) B2052977
theorem B3941585 : Blo 1750576 3941585 := bstep (se 2 (by rfl) ⟨1478094, by rfl⟩ : syracuseStep 3941585 = 2956189) B2956189
theorem B10650851 : Blo 1750576 10650851 := bstep (se 1 (by rfl) ⟨7988138, by rfl⟩ : syracuseStep 10650851 = 15976277) B15976277
theorem B3941603 : Blo 1750576 3941603 := bstep (se 1 (by rfl) ⟨2956202, by rfl⟩ : syracuseStep 3941603 = 5912405) B5912405
theorem B4990211 : Blo 1750576 4990211 := bstep (se 1 (by rfl) ⟨3742658, by rfl⟩ : syracuseStep 4990211 = 7485317) B7485317
theorem B18941197 : Blo 1750576 18941197 := bstep (se 3 (by rfl) ⟨3551474, by rfl⟩ : syracuseStep 18941197 = 7102949) B7102949
theorem B4433201 : Blo 1750576 4433201 := bstep (se 2 (by rfl) ⟨1662450, by rfl⟩ : syracuseStep 4433201 = 3324901) B3324901
theorem B4433251 : Blo 1750576 4433251 := bstep (se 1 (by rfl) ⟨3324938, by rfl⟩ : syracuseStep 4433251 = 6649877) B6649877
theorem B9971171 : Blo 1750576 9971171 := bstep (se 1 (by rfl) ⟨7478378, by rfl⟩ : syracuseStep 9971171 = 14956757) B14956757
theorem B4433393 : Blo 1750576 4433393 := bstep (se 2 (by rfl) ⟨1662522, by rfl⟩ : syracuseStep 4433393 = 3325045) B3325045
theorem B3941873 : Blo 1750576 3941873 := bstep (se 2 (by rfl) ⟨1478202, by rfl⟩ : syracuseStep 3941873 = 2956405) B2956405
theorem B3941891 : Blo 1750576 3941891 := bstep (se 1 (by rfl) ⟨2956418, by rfl⟩ : syracuseStep 3941891 = 5912837) B5912837
theorem B8095459 : Blo 1750576 8095459 := bstep (se 1 (by rfl) ⟨6071594, by rfl⟩ : syracuseStep 8095459 = 12143189) B12143189
theorem B3942161 : Blo 1750576 3942161 := bstep (se 2 (by rfl) ⟨1478310, by rfl⟩ : syracuseStep 3942161 = 2956621) B2956621
theorem B3942179 : Blo 1750576 3942179 := bstep (se 1 (by rfl) ⟨2956634, by rfl⟩ : syracuseStep 3942179 = 5913269) B5913269
theorem B5908301 : Blo 1750576 5908301 := bstep (se 3 (by rfl) ⟨1107806, by rfl⟩ : syracuseStep 5908301 = 2215613) B2215613
theorem B5908355 : Blo 1750576 5908355 := bstep (se 1 (by rfl) ⟨4431266, by rfl⟩ : syracuseStep 5908355 = 8862533) B8862533
theorem B5613475 : Blo 1750576 5613475 := bstep (se 1 (by rfl) ⟨4210106, by rfl⟩ : syracuseStep 5613475 = 8420213) B8420213
theorem B3942449 : Blo 1750576 3942449 := bstep (se 2 (by rfl) ⟨1478418, by rfl⟩ : syracuseStep 3942449 = 2956837) B2956837
theorem B3942467 : Blo 1750576 3942467 := bstep (se 1 (by rfl) ⟨2956850, by rfl⟩ : syracuseStep 3942467 = 5913701) B5913701
theorem B5908625 : Blo 1750576 5908625 := bstep (se 2 (by rfl) ⟨2215734, by rfl⟩ : syracuseStep 5908625 = 4431469) B4431469
theorem B5613745 : Blo 1750576 5613745 := bstep (se 2 (by rfl) ⟨2105154, by rfl⟩ : syracuseStep 5613745 = 4210309) B4210309
theorem B5687533 : Blo 1750576 5687533 := bstep (se 3 (by rfl) ⟨1066412, by rfl⟩ : syracuseStep 5687533 = 2132825) B2132825
theorem B5327117 : Blo 1750576 5327117 := bstep (se 3 (by rfl) ⟨998834, by rfl⟩ : syracuseStep 5327117 = 1997669) B1997669
theorem B6654221 : Blo 1750576 6654221 := bstep (se 3 (by rfl) ⟨1247666, by rfl⟩ : syracuseStep 6654221 = 2495333) B2495333
theorem B8866097 : Blo 1750576 8866097 := bstep (se 2 (by rfl) ⟨3324786, by rfl⟩ : syracuseStep 8866097 = 6649573) B6649573
theorem B3942737 : Blo 1750576 3942737 := bstep (se 2 (by rfl) ⟨1478526, by rfl⟩ : syracuseStep 3942737 = 2957053) B2957053
theorem B3942755 : Blo 1750576 3942755 := bstep (se 1 (by rfl) ⟨2957066, by rfl⟩ : syracuseStep 3942755 = 5914133) B5914133
theorem B7588237 : Blo 1750576 7588237 := bstep (se 3 (by rfl) ⟨1422794, by rfl⟩ : syracuseStep 7588237 = 2845589) B2845589
theorem B9972173 : Blo 1750576 9972173 := bstep (se 3 (by rfl) ⟨1869782, by rfl⟩ : syracuseStep 9972173 = 3739565) B3739565
theorem B4434385 : Blo 1750576 4434385 := bstep (se 2 (by rfl) ⟨1662894, by rfl⟩ : syracuseStep 4434385 = 3325789) B3325789
theorem B2492947 : Blo 1750576 2492947 := bstep (se 1 (by rfl) ⟨1869710, by rfl⟩ : syracuseStep 2492947 = 3739421) B3739421
theorem B7481933 : Blo 1750576 7481933 := bstep (se 3 (by rfl) ⟨1402862, by rfl⟩ : syracuseStep 7481933 = 2805725) B2805725
theorem B3943025 : Blo 1750576 3943025 := bstep (se 2 (by rfl) ⟨1478634, by rfl⟩ : syracuseStep 3943025 = 2957269) B2957269
theorem B3943043 : Blo 1750576 3943043 := bstep (se 1 (by rfl) ⟨2957282, by rfl⟩ : syracuseStep 3943043 = 5914565) B5914565
theorem B5909165 : Blo 1750576 5909165 := bstep (se 3 (by rfl) ⟨1107968, by rfl⟩ : syracuseStep 5909165 = 2215937) B2215937
theorem B5909219 : Blo 1750576 5909219 := bstep (se 1 (by rfl) ⟨4431914, by rfl⟩ : syracuseStep 5909219 = 8863829) B8863829
theorem B4434659 : Blo 1750576 4434659 := bstep (se 1 (by rfl) ⟨3325994, by rfl⟩ : syracuseStep 4434659 = 6651989) B6651989
theorem B13298417 : Blo 1750576 13298417 := bstep (se 2 (by rfl) ⟨4986906, by rfl⟩ : syracuseStep 13298417 = 9973813) B9973813
theorem B7990001 : Blo 1750576 7990001 := bstep (se 2 (by rfl) ⟨2996250, by rfl⟩ : syracuseStep 7990001 = 5992501) B5992501
theorem B2493283 : Blo 1750576 2493283 := bstep (se 1 (by rfl) ⟨1869962, by rfl⟩ : syracuseStep 2493283 = 3739925) B3739925
theorem B4434851 : Blo 1750576 4434851 := bstep (se 1 (by rfl) ⟨3326138, by rfl⟩ : syracuseStep 4434851 = 6652277) B6652277
theorem B3156931 : Blo 1750576 3156931 := bstep (se 1 (by rfl) ⟨2367698, by rfl⟩ : syracuseStep 3156931 = 4735397) B4735397
theorem B11226053 : Blo 1750576 11226053 := bstep (se 4 (by rfl) ⟨1052442, by rfl⟩ : syracuseStep 11226053 = 2104885) B2104885
theorem B5909489 : Blo 1750576 5909489 := bstep (se 2 (by rfl) ⟨2216058, by rfl⟩ : syracuseStep 5909489 = 4432117) B4432117
theorem B9464909 : Blo 1750576 9464909 := bstep (se 3 (by rfl) ⟨1774670, by rfl⟩ : syracuseStep 9464909 = 3549341) B3549341
theorem B6646961 : Blo 1750576 6646961 := bstep (se 2 (by rfl) ⟨2492610, by rfl⟩ : syracuseStep 6646961 = 4985221) B4985221
theorem B1969411 : Blo 1750576 1969411 := bstep (se 1 (by rfl) ⟨1477058, by rfl⟩ : syracuseStep 1969411 = 2954117) B2954117
theorem B6311267 : Blo 1750576 6311267 := bstep (se 1 (by rfl) ⟨4733450, by rfl⟩ : syracuseStep 6311267 = 9466901) B9466901
theorem B2493841 : Blo 1750576 2493841 := bstep (se 2 (by rfl) ⟨935190, by rfl⟩ : syracuseStep 2493841 = 1870381) B1870381
theorem B3157393 : Blo 1750576 3157393 := bstep (se 2 (by rfl) ⟨1184022, by rfl⟩ : syracuseStep 3157393 = 2368045) B2368045
theorem B1969555 : Blo 1750576 1969555 := bstep (se 1 (by rfl) ⟨1477166, by rfl⟩ : syracuseStep 1969555 = 2954333) B2954333
theorem B2493875 : Blo 1750576 2493875 := bstep (se 1 (by rfl) ⟨1870406, by rfl⟩ : syracuseStep 2493875 = 3740813) B3740813
theorem B2805187 : Blo 1750576 2805187 := bstep (se 1 (by rfl) ⟨2103890, by rfl⟩ : syracuseStep 2805187 = 4207781) B4207781
theorem B3157507 : Blo 1750576 3157507 := bstep (se 1 (by rfl) ⟨2368130, by rfl⟩ : syracuseStep 3157507 = 4736261) B4736261
theorem B5910029 : Blo 1750576 5910029 := bstep (se 3 (by rfl) ⟨1108130, by rfl⟩ : syracuseStep 5910029 = 2216261) B2216261
theorem B1969699 : Blo 1750576 1969699 := bstep (se 1 (by rfl) ⟨1477274, by rfl⟩ : syracuseStep 1969699 = 2954549) B2954549
theorem B2805283 : Blo 1750576 2805283 := bstep (se 1 (by rfl) ⟨2103962, by rfl⟩ : syracuseStep 2805283 = 4207925) B4207925
theorem B5910083 : Blo 1750576 5910083 := bstep (se 1 (by rfl) ⟨4432562, by rfl⟩ : syracuseStep 5910083 = 8865125) B8865125
theorem B8416867 : Blo 1750576 8416867 := bstep (se 1 (by rfl) ⟨6312650, by rfl⟩ : syracuseStep 8416867 = 12625301) B12625301
theorem B2215603 : Blo 1750576 2215603 := bstep (se 1 (by rfl) ⟨1661702, by rfl⟩ : syracuseStep 2215603 = 3323405) B3323405
theorem B1969843 : Blo 1750576 1969843 := bstep (se 1 (by rfl) ⟨1477382, by rfl⟩ : syracuseStep 1969843 = 2954765) B2954765
theorem B2805443 : Blo 1750576 2805443 := bstep (se 1 (by rfl) ⟨2104082, by rfl⟩ : syracuseStep 2805443 = 4208165) B4208165
theorem B8867555 : Blo 1750576 8867555 := bstep (se 1 (by rfl) ⟨6650666, by rfl⟩ : syracuseStep 8867555 = 13301333) B13301333
theorem B9473777 : Blo 1750576 9473777 := bstep (se 2 (by rfl) ⟨3552666, by rfl⟩ : syracuseStep 9473777 = 7105333) B7105333
theorem B1969987 : Blo 1750576 1969987 := bstep (se 1 (by rfl) ⟨1477490, by rfl⟩ : syracuseStep 1969987 = 2954981) B2954981
theorem B6647629 : Blo 1750576 6647629 := bstep (se 3 (by rfl) ⟨1246430, by rfl⟩ : syracuseStep 6647629 = 2492861) B2492861
theorem B5910353 : Blo 1750576 5910353 := bstep (se 2 (by rfl) ⟨2216382, by rfl⟩ : syracuseStep 5910353 = 4432765) B4432765
theorem B4435793 : Blo 1750576 4435793 := bstep (se 2 (by rfl) ⟨1663422, by rfl⟩ : syracuseStep 4435793 = 3326845) B3326845
theorem B4435843 : Blo 1750576 4435843 := bstep (se 1 (by rfl) ⟨3326882, by rfl⟩ : syracuseStep 4435843 = 6653765) B6653765
theorem B3157969 : Blo 1750576 3157969 := bstep (se 2 (by rfl) ⟨1184238, by rfl⟩ : syracuseStep 3157969 = 2368477) B2368477
theorem B1970131 : Blo 1750576 1970131 := bstep (se 1 (by rfl) ⟨1477598, by rfl⟩ : syracuseStep 1970131 = 2955197) B2955197
theorem B2494433 : Blo 1750576 2494433 := bstep (se 2 (by rfl) ⟨935412, by rfl⟩ : syracuseStep 2494433 = 1870825) B1870825
theorem B4435985 : Blo 1750576 4435985 := bstep (se 2 (by rfl) ⟨1663494, by rfl⟩ : syracuseStep 4435985 = 3326989) B3326989
theorem B2527267 : Blo 1750576 2527267 := bstep (se 1 (by rfl) ⟨1895450, by rfl⟩ : syracuseStep 2527267 = 3790901) B3790901
theorem B2494513 : Blo 1750576 2494513 := bstep (se 2 (by rfl) ⟨935442, by rfl⟩ : syracuseStep 2494513 = 1870885) B1870885
theorem B1970275 : Blo 1750576 1970275 := bstep (se 1 (by rfl) ⟨1477706, by rfl⟩ : syracuseStep 1970275 = 2955413) B2955413
theorem B2216099 : Blo 1750576 2216099 := bstep (se 1 (by rfl) ⟨1662074, by rfl⟩ : syracuseStep 2216099 = 3324149) B3324149
theorem B1970419 : Blo 1750576 1970419 := bstep (se 1 (by rfl) ⟨1477814, by rfl⟩ : syracuseStep 1970419 = 2955629) B2955629
theorem B3739907 : Blo 1750576 3739907 := bstep (se 1 (by rfl) ⟨2804930, by rfl⟩ : syracuseStep 3739907 = 5609861) B5609861
theorem B2994499 : Blo 1750576 2994499 := bstep (se 1 (by rfl) ⟨2245874, by rfl⟩ : syracuseStep 2994499 = 4491749) B4491749
theorem B4985165 : Blo 1750576 4985165 := bstep (se 3 (by rfl) ⟨934718, by rfl⟩ : syracuseStep 4985165 = 1869437) B1869437
theorem B2625875 : Blo 1750576 2625875 := bstep (se 1 (by rfl) ⟨1969406, by rfl⟩ : syracuseStep 2625875 = 3938813) B3938813
theorem B5910893 : Blo 1750576 5910893 := bstep (se 3 (by rfl) ⟨1108292, by rfl⟩ : syracuseStep 5910893 = 2216585) B2216585
theorem B2625905 : Blo 1750576 2625905 := bstep (se 2 (by rfl) ⟨984714, by rfl⟩ : syracuseStep 2625905 = 1969429) B1969429
theorem B2625923 : Blo 1750576 2625923 := bstep (se 1 (by rfl) ⟨1969442, by rfl⟩ : syracuseStep 2625923 = 3938885) B3938885
theorem B1970563 : Blo 1750576 1970563 := bstep (se 1 (by rfl) ⟨1477922, by rfl⟩ : syracuseStep 1970563 = 2955845) B2955845
theorem B2625953 : Blo 1750576 2625953 := bstep (se 2 (by rfl) ⟨984732, by rfl⟩ : syracuseStep 2625953 = 1969465) B1969465
theorem B5910947 : Blo 1750576 5910947 := bstep (se 1 (by rfl) ⟨4433210, by rfl⟩ : syracuseStep 5910947 = 8866421) B8866421
theorem B2625971 : Blo 1750576 2625971 := bstep (se 1 (by rfl) ⟨1969478, by rfl⟩ : syracuseStep 2625971 = 3938957) B3938957
theorem B2626001 : Blo 1750576 2626001 := bstep (se 2 (by rfl) ⟨984750, by rfl⟩ : syracuseStep 2626001 = 1969501) B1969501
theorem B2626019 : Blo 1750576 2626019 := bstep (se 1 (by rfl) ⟨1969514, by rfl⟩ : syracuseStep 2626019 = 3939029) B3939029
theorem B2626049 : Blo 1750576 2626049 := bstep (se 2 (by rfl) ⟨984768, by rfl⟩ : syracuseStep 2626049 = 1969537) B1969537
theorem B4985347 : Blo 1750576 4985347 := bstep (se 1 (by rfl) ⟨3739010, by rfl⟩ : syracuseStep 4985347 = 7478021) B7478021
theorem B8868365 : Blo 1750576 8868365 := bstep (se 3 (by rfl) ⟨1662818, by rfl⟩ : syracuseStep 8868365 = 3325637) B3325637
theorem B2626067 : Blo 1750576 2626067 := bstep (se 1 (by rfl) ⟨1969550, by rfl⟩ : syracuseStep 2626067 = 3939101) B3939101
theorem B1970707 : Blo 1750576 1970707 := bstep (se 1 (by rfl) ⟨1478030, by rfl⟩ : syracuseStep 1970707 = 2956061) B2956061
theorem B2626097 : Blo 1750576 2626097 := bstep (se 2 (by rfl) ⟨984786, by rfl⟩ : syracuseStep 2626097 = 1969573) B1969573
theorem B2626115 : Blo 1750576 2626115 := bstep (se 1 (by rfl) ⟨1969586, by rfl⟩ : syracuseStep 2626115 = 3939173) B3939173
theorem B2626145 : Blo 1750576 2626145 := bstep (se 2 (by rfl) ⟨984804, by rfl⟩ : syracuseStep 2626145 = 1969609) B1969609
theorem B6648419 : Blo 1750576 6648419 := bstep (se 1 (by rfl) ⟨4986314, by rfl⟩ : syracuseStep 6648419 = 9972629) B9972629
theorem B2527843 : Blo 1750576 2527843 := bstep (se 1 (by rfl) ⟨1895882, by rfl⟩ : syracuseStep 2527843 = 3791765) B3791765
theorem B2626163 : Blo 1750576 2626163 := bstep (se 1 (by rfl) ⟨1969622, by rfl⟩ : syracuseStep 2626163 = 3939245) B3939245
theorem B2626193 : Blo 1750576 2626193 := bstep (se 2 (by rfl) ⟨984822, by rfl⟩ : syracuseStep 2626193 = 1969645) B1969645
theorem B2806417 : Blo 1750576 2806417 := bstep (se 2 (by rfl) ⟨1052406, by rfl⟩ : syracuseStep 2806417 = 2104813) B2104813
theorem B2626211 : Blo 1750576 2626211 := bstep (se 1 (by rfl) ⟨1969658, by rfl⟩ : syracuseStep 2626211 = 3939317) B3939317
theorem B1970851 : Blo 1750576 1970851 := bstep (se 1 (by rfl) ⟨1478138, by rfl⟩ : syracuseStep 1970851 = 2956277) B2956277
theorem B5911217 : Blo 1750576 5911217 := bstep (se 2 (by rfl) ⟨2216706, by rfl⟩ : syracuseStep 5911217 = 4433413) B4433413
theorem B2626241 : Blo 1750576 2626241 := bstep (se 2 (by rfl) ⟨984840, by rfl⟩ : syracuseStep 2626241 = 1969681) B1969681
theorem B2626259 : Blo 1750576 2626259 := bstep (se 1 (by rfl) ⟨1969694, by rfl⟩ : syracuseStep 2626259 = 3939389) B3939389
theorem B2626289 : Blo 1750576 2626289 := bstep (se 2 (by rfl) ⟨984858, by rfl⟩ : syracuseStep 2626289 = 1969717) B1969717
theorem B2626307 : Blo 1750576 2626307 := bstep (se 1 (by rfl) ⟨1969730, by rfl⟩ : syracuseStep 2626307 = 3939461) B3939461
theorem B2626337 : Blo 1750576 2626337 := bstep (se 2 (by rfl) ⟨984876, by rfl⟩ : syracuseStep 2626337 = 1969753) B1969753
theorem B8418097 : Blo 1750576 8418097 := bstep (se 2 (by rfl) ⟨3156786, by rfl⟩ : syracuseStep 8418097 = 6313573) B6313573
theorem B2626355 : Blo 1750576 2626355 := bstep (se 1 (by rfl) ⟨1969766, by rfl⟩ : syracuseStep 2626355 = 3939533) B3939533
theorem B1970995 : Blo 1750576 1970995 := bstep (se 1 (by rfl) ⟨1478246, by rfl⟩ : syracuseStep 1970995 = 2956493) B2956493
theorem B33682229 : Blo 1750576 33682229 := bstep (se 5 (by rfl) ⟨1578854, by rfl⟩ : syracuseStep 33682229 = 3157709) B3157709
theorem B2495299 : Blo 1750576 2495299 := bstep (se 1 (by rfl) ⟨1871474, by rfl⟩ : syracuseStep 2495299 = 3742949) B3742949
theorem B2626385 : Blo 1750576 2626385 := bstep (se 2 (by rfl) ⟨984894, by rfl⟩ : syracuseStep 2626385 = 1969789) B1969789
theorem B2626403 : Blo 1750576 2626403 := bstep (se 1 (by rfl) ⟨1969802, by rfl⟩ : syracuseStep 2626403 = 3939605) B3939605
theorem B2216803 : Blo 1750576 2216803 := bstep (se 1 (by rfl) ⟨1662602, by rfl⟩ : syracuseStep 2216803 = 3325205) B3325205
theorem B3199843 : Blo 1750576 3199843 := bstep (se 1 (by rfl) ⟨2399882, by rfl⟩ : syracuseStep 3199843 = 4799765) B4799765
theorem B2626433 : Blo 1750576 2626433 := bstep (se 2 (by rfl) ⟨984912, by rfl⟩ : syracuseStep 2626433 = 1969825) B1969825
theorem B2626451 : Blo 1750576 2626451 := bstep (se 1 (by rfl) ⟨1969838, by rfl⟩ : syracuseStep 2626451 = 3939677) B3939677
theorem B2626481 : Blo 1750576 2626481 := bstep (se 2 (by rfl) ⟨984930, by rfl⟩ : syracuseStep 2626481 = 1969861) B1969861
theorem B2626499 : Blo 1750576 2626499 := bstep (se 1 (by rfl) ⟨1969874, by rfl⟩ : syracuseStep 2626499 = 3939749) B3939749
theorem B2216899 : Blo 1750576 2216899 := bstep (se 1 (by rfl) ⟨1662674, by rfl⟩ : syracuseStep 2216899 = 3325349) B3325349
theorem B1971139 : Blo 1750576 1971139 := bstep (se 1 (by rfl) ⟨1478354, by rfl⟩ : syracuseStep 1971139 = 2956709) B2956709
theorem B2626529 : Blo 1750576 2626529 := bstep (se 2 (by rfl) ⟨984948, by rfl⟩ : syracuseStep 2626529 = 1969897) B1969897
theorem B4985837 : Blo 1750576 4985837 := bstep (se 3 (by rfl) ⟨934844, by rfl⟩ : syracuseStep 4985837 = 1869689) B1869689
theorem B2954225 : Blo 1750576 2954225 := bstep (se 2 (by rfl) ⟨1107834, by rfl⟩ : syracuseStep 2954225 = 2215669) B2215669
theorem B2626547 : Blo 1750576 2626547 := bstep (se 1 (by rfl) ⟨1969910, by rfl⟩ : syracuseStep 2626547 = 3939821) B3939821
theorem B2626577 : Blo 1750576 2626577 := bstep (se 2 (by rfl) ⟨984966, by rfl⟩ : syracuseStep 2626577 = 1969933) B1969933
theorem B2626595 : Blo 1750576 2626595 := bstep (se 1 (by rfl) ⟨1969946, by rfl⟩ : syracuseStep 2626595 = 3939893) B3939893
theorem B11981873 : Blo 1750576 11981873 := bstep (se 2 (by rfl) ⟨4493202, by rfl⟩ : syracuseStep 11981873 = 8986405) B8986405
theorem B2626625 : Blo 1750576 2626625 := bstep (se 2 (by rfl) ⟨984984, by rfl⟩ : syracuseStep 2626625 = 1969969) B1969969
theorem B2626643 : Blo 1750576 2626643 := bstep (se 1 (by rfl) ⟨1969982, by rfl⟩ : syracuseStep 2626643 = 3939965) B3939965
theorem B1971283 : Blo 1750576 1971283 := bstep (se 1 (by rfl) ⟨1478462, by rfl⟩ : syracuseStep 1971283 = 2956925) B2956925
theorem B2954353 : Blo 1750576 2954353 := bstep (se 2 (by rfl) ⟨1107882, by rfl⟩ : syracuseStep 2954353 = 2215765) B2215765
theorem B2626673 : Blo 1750576 2626673 := bstep (se 2 (by rfl) ⟨985002, by rfl⟩ : syracuseStep 2626673 = 1970005) B1970005
theorem B2626691 : Blo 1750576 2626691 := bstep (se 1 (by rfl) ⟨1970018, by rfl⟩ : syracuseStep 2626691 = 3940037) B3940037
theorem B2954387 : Blo 1750576 2954387 := bstep (se 1 (by rfl) ⟨2215790, by rfl⟩ : syracuseStep 2954387 = 4431581) B4431581
theorem B2626721 : Blo 1750576 2626721 := bstep (se 2 (by rfl) ⟨985020, by rfl⟩ : syracuseStep 2626721 = 1970041) B1970041
theorem B2626739 : Blo 1750576 2626739 := bstep (se 1 (by rfl) ⟨1970054, by rfl⟩ : syracuseStep 2626739 = 3940109) B3940109
theorem B4732109 : Blo 1750576 4732109 := bstep (se 3 (by rfl) ⟨887270, by rfl⟩ : syracuseStep 4732109 = 1774541) B1774541
theorem B5911757 : Blo 1750576 5911757 := bstep (se 3 (by rfl) ⟨1108454, by rfl⟩ : syracuseStep 5911757 = 2216909) B2216909
theorem B2626769 : Blo 1750576 2626769 := bstep (se 2 (by rfl) ⟨985038, by rfl⟩ : syracuseStep 2626769 = 1970077) B1970077
theorem B2626787 : Blo 1750576 2626787 := bstep (se 1 (by rfl) ⟨1970090, by rfl⟩ : syracuseStep 2626787 = 3940181) B3940181
theorem B1971427 : Blo 1750576 1971427 := bstep (se 1 (by rfl) ⟨1478570, by rfl⟩ : syracuseStep 1971427 = 2957141) B2957141
theorem B6649073 : Blo 1750576 6649073 := bstep (se 2 (by rfl) ⟨2493402, by rfl⟩ : syracuseStep 6649073 = 4986805) B4986805
theorem B2626817 : Blo 1750576 2626817 := bstep (se 2 (by rfl) ⟨985056, by rfl⟩ : syracuseStep 2626817 = 1970113) B1970113
theorem B5911811 : Blo 1750576 5911811 := bstep (se 1 (by rfl) ⟨4433858, by rfl⟩ : syracuseStep 5911811 = 8867717) B8867717
theorem B2954515 : Blo 1750576 2954515 := bstep (se 1 (by rfl) ⟨2215886, by rfl⟩ : syracuseStep 2954515 = 4431773) B4431773
theorem B2626835 : Blo 1750576 2626835 := bstep (se 1 (by rfl) ⟨1970126, by rfl⟩ : syracuseStep 2626835 = 3940253) B3940253
theorem B2626865 : Blo 1750576 2626865 := bstep (se 2 (by rfl) ⟨985074, by rfl⟩ : syracuseStep 2626865 = 1970149) B1970149
theorem B9975089 : Blo 1750576 9975089 := bstep (se 2 (by rfl) ⟨3740658, by rfl⟩ : syracuseStep 9975089 = 7481317) B7481317
theorem B2700595 : Blo 1750576 2700595 := bstep (se 1 (by rfl) ⟨2025446, by rfl⟩ : syracuseStep 2700595 = 4050893) B4050893
theorem B2626883 : Blo 1750576 2626883 := bstep (se 1 (by rfl) ⟨1970162, by rfl⟩ : syracuseStep 2626883 = 3940325) B3940325
theorem B2626913 : Blo 1750576 2626913 := bstep (se 2 (by rfl) ⟨985092, by rfl⟩ : syracuseStep 2626913 = 1970185) B1970185
theorem B6313315 : Blo 1750576 6313315 := bstep (se 1 (by rfl) ⟨4734986, by rfl⟩ : syracuseStep 6313315 = 9469973) B9469973
theorem B1774963 : Blo 1750576 1774963 := bstep (se 1 (by rfl) ⟨1331222, by rfl⟩ : syracuseStep 1774963 = 2662445) B2662445
theorem B2626931 : Blo 1750576 2626931 := bstep (se 1 (by rfl) ⟨1970198, by rfl⟩ : syracuseStep 2626931 = 3940397) B3940397
theorem B1971571 : Blo 1750576 1971571 := bstep (se 1 (by rfl) ⟨1478678, by rfl⟩ : syracuseStep 1971571 = 2957357) B2957357
theorem B2626961 : Blo 1750576 2626961 := bstep (se 2 (by rfl) ⟨985110, by rfl⟩ : syracuseStep 2626961 = 1970221) B1970221
theorem B2954657 : Blo 1750576 2954657 := bstep (se 2 (by rfl) ⟨1107996, by rfl⟩ : syracuseStep 2954657 = 2215993) B2215993
theorem B2626979 : Blo 1750576 2626979 := bstep (se 1 (by rfl) ⟨1970234, by rfl⟩ : syracuseStep 2626979 = 3940469) B3940469
theorem B2995633 : Blo 1750576 2995633 := bstep (se 2 (by rfl) ⟨1123362, by rfl⟩ : syracuseStep 2995633 = 2246725) B2246725
theorem B2217395 : Blo 1750576 2217395 := bstep (se 1 (by rfl) ⟨1663046, by rfl⟩ : syracuseStep 2217395 = 3326093) B3326093
theorem B2627009 : Blo 1750576 2627009 := bstep (se 2 (by rfl) ⟨985128, by rfl⟩ : syracuseStep 2627009 = 1970257) B1970257
theorem B2627027 : Blo 1750576 2627027 := bstep (se 1 (by rfl) ⟨1970270, by rfl⟩ : syracuseStep 2627027 = 3940541) B3940541
theorem B2627057 : Blo 1750576 2627057 := bstep (se 2 (by rfl) ⟨985146, by rfl⟩ : syracuseStep 2627057 = 1970293) B1970293
theorem B2627075 : Blo 1750576 2627075 := bstep (se 1 (by rfl) ⟨1970306, by rfl⟩ : syracuseStep 2627075 = 3940613) B3940613
theorem B5912081 : Blo 1750576 5912081 := bstep (se 2 (by rfl) ⟨2217030, by rfl⟩ : syracuseStep 5912081 = 4434061) B4434061
theorem B2954785 : Blo 1750576 2954785 := bstep (se 2 (by rfl) ⟨1108044, by rfl⟩ : syracuseStep 2954785 = 2216089) B2216089
theorem B2627105 : Blo 1750576 2627105 := bstep (se 2 (by rfl) ⟨985164, by rfl⟩ : syracuseStep 2627105 = 1970329) B1970329
theorem B1750579 : Blo 1750576 1750579 := bstep (se 1 (by rfl) ⟨1312934, by rfl⟩ : syracuseStep 1750579 = 2625869) B2625869
theorem B2627123 : Blo 1750576 2627123 := bstep (se 1 (by rfl) ⟨1970342, by rfl⟩ : syracuseStep 2627123 = 3940685) B3940685
theorem B1750595 : Blo 1750576 1750595 := bstep (se 1 (by rfl) ⟨1312946, by rfl⟩ : syracuseStep 1750595 = 2625893) B2625893
theorem B2954819 : Blo 1750576 2954819 := bstep (se 1 (by rfl) ⟨2216114, by rfl⟩ : syracuseStep 2954819 = 4432229) B4432229
theorem B2627153 : Blo 1750576 2627153 := bstep (se 2 (by rfl) ⟨985182, by rfl⟩ : syracuseStep 2627153 = 1970365) B1970365
theorem B1750611 : Blo 1750576 1750611 := bstep (se 1 (by rfl) ⟨1312958, by rfl⟩ : syracuseStep 1750611 = 2625917) B2625917
theorem B1750627 : Blo 1750576 1750627 := bstep (se 1 (by rfl) ⟨1312970, by rfl⟩ : syracuseStep 1750627 = 2625941) B2625941
theorem B2627171 : Blo 1750576 2627171 := bstep (se 1 (by rfl) ⟨1970378, by rfl⟩ : syracuseStep 2627171 = 3940757) B3940757
theorem B1750643 : Blo 1750576 1750643 := bstep (se 1 (by rfl) ⟨1312982, by rfl⟩ : syracuseStep 1750643 = 2625965) B2625965
theorem B2627201 : Blo 1750576 2627201 := bstep (se 2 (by rfl) ⟨985200, by rfl⟩ : syracuseStep 2627201 = 1970401) B1970401
theorem B1750659 : Blo 1750576 1750659 := bstep (se 1 (by rfl) ⟨1312994, by rfl⟩ : syracuseStep 1750659 = 2625989) B2625989
theorem B1750675 : Blo 1750576 1750675 := bstep (se 1 (by rfl) ⟨1313006, by rfl⟩ : syracuseStep 1750675 = 2626013) B2626013
theorem B2627219 : Blo 1750576 2627219 := bstep (se 1 (by rfl) ⟨1970414, by rfl⟩ : syracuseStep 2627219 = 3940829) B3940829
theorem B1750691 : Blo 1750576 1750691 := bstep (se 1 (by rfl) ⟨1313018, by rfl⟩ : syracuseStep 1750691 = 2626037) B2626037
theorem B2627249 : Blo 1750576 2627249 := bstep (se 2 (by rfl) ⟨985218, by rfl⟩ : syracuseStep 2627249 = 1970437) B1970437
theorem B1750707 : Blo 1750576 1750707 := bstep (se 1 (by rfl) ⟨1313030, by rfl⟩ : syracuseStep 1750707 = 2626061) B2626061
theorem B3323587 : Blo 1750576 3323587 := bstep (se 1 (by rfl) ⟨2492690, by rfl⟩ : syracuseStep 3323587 = 4985381) B4985381
theorem B1750723 : Blo 1750576 1750723 := bstep (se 1 (by rfl) ⟨1313042, by rfl⟩ : syracuseStep 1750723 = 2626085) B2626085
theorem B2954947 : Blo 1750576 2954947 := bstep (se 1 (by rfl) ⟨2216210, by rfl⟩ : syracuseStep 2954947 = 4432421) B4432421
theorem B2627267 : Blo 1750576 2627267 := bstep (se 1 (by rfl) ⟨1970450, by rfl⟩ : syracuseStep 2627267 = 3940901) B3940901
theorem B3995345 : Blo 1750576 3995345 := bstep (se 2 (by rfl) ⟨1498254, by rfl⟩ : syracuseStep 3995345 = 2996509) B2996509
theorem B1750739 : Blo 1750576 1750739 := bstep (se 1 (by rfl) ⟨1313054, by rfl⟩ : syracuseStep 1750739 = 2626109) B2626109
theorem B2627297 : Blo 1750576 2627297 := bstep (se 2 (by rfl) ⟨985236, by rfl⟩ : syracuseStep 2627297 = 1970473) B1970473
theorem B1750755 : Blo 1750576 1750755 := bstep (se 1 (by rfl) ⟨1313066, by rfl⟩ : syracuseStep 1750755 = 2626133) B2626133
theorem B1750771 : Blo 1750576 1750771 := bstep (se 1 (by rfl) ⟨1313078, by rfl⟩ : syracuseStep 1750771 = 2626157) B2626157
theorem B2627315 : Blo 1750576 2627315 := bstep (se 1 (by rfl) ⟨1970486, by rfl⟩ : syracuseStep 2627315 = 3940973) B3940973
theorem B1750787 : Blo 1750576 1750787 := bstep (se 1 (by rfl) ⟨1313090, by rfl⟩ : syracuseStep 1750787 = 2626181) B2626181
theorem B2627345 : Blo 1750576 2627345 := bstep (se 2 (by rfl) ⟨985254, by rfl⟩ : syracuseStep 2627345 = 1970509) B1970509
theorem B1750803 : Blo 1750576 1750803 := bstep (se 1 (by rfl) ⟨1313102, by rfl⟩ : syracuseStep 1750803 = 2626205) B2626205
theorem B1750819 : Blo 1750576 1750819 := bstep (se 1 (by rfl) ⟨1313114, by rfl⟩ : syracuseStep 1750819 = 2626229) B2626229
theorem B2627363 : Blo 1750576 2627363 := bstep (se 1 (by rfl) ⟨1970522, by rfl⟩ : syracuseStep 2627363 = 3941045) B3941045
theorem B1750835 : Blo 1750576 1750835 := bstep (se 1 (by rfl) ⟨1313126, by rfl⟩ : syracuseStep 1750835 = 2626253) B2626253
theorem B2627393 : Blo 1750576 2627393 := bstep (se 2 (by rfl) ⟨985272, by rfl⟩ : syracuseStep 2627393 = 1970545) B1970545
theorem B1750851 : Blo 1750576 1750851 := bstep (se 1 (by rfl) ⟨1313138, by rfl⟩ : syracuseStep 1750851 = 2626277) B2626277
theorem B2955089 : Blo 1750576 2955089 := bstep (se 2 (by rfl) ⟨1108158, by rfl⟩ : syracuseStep 2955089 = 2216317) B2216317
theorem B1750867 : Blo 1750576 1750867 := bstep (se 1 (by rfl) ⟨1313150, by rfl⟩ : syracuseStep 1750867 = 2626301) B2626301
theorem B2627411 : Blo 1750576 2627411 := bstep (se 1 (by rfl) ⟨1970558, by rfl⟩ : syracuseStep 2627411 = 3941117) B3941117
theorem B3323747 : Blo 1750576 3323747 := bstep (se 1 (by rfl) ⟨2492810, by rfl⟩ : syracuseStep 3323747 = 4985621) B4985621
theorem B1750883 : Blo 1750576 1750883 := bstep (se 1 (by rfl) ⟨1313162, by rfl⟩ : syracuseStep 1750883 = 2626325) B2626325
theorem B2627441 : Blo 1750576 2627441 := bstep (se 2 (by rfl) ⟨985290, by rfl⟩ : syracuseStep 2627441 = 1970581) B1970581
theorem B1750899 : Blo 1750576 1750899 := bstep (se 1 (by rfl) ⟨1313174, by rfl⟩ : syracuseStep 1750899 = 2626349) B2626349
theorem B1750915 : Blo 1750576 1750915 := bstep (se 1 (by rfl) ⟨1313186, by rfl⟩ : syracuseStep 1750915 = 2626373) B2626373
theorem B2627459 : Blo 1750576 2627459 := bstep (se 1 (by rfl) ⟨1970594, by rfl⟩ : syracuseStep 2627459 = 3941189) B3941189
theorem B1750931 : Blo 1750576 1750931 := bstep (se 1 (by rfl) ⟨1313198, by rfl⟩ : syracuseStep 1750931 = 2626397) B2626397
theorem B2627489 : Blo 1750576 2627489 := bstep (se 2 (by rfl) ⟨985308, by rfl⟩ : syracuseStep 2627489 = 1970617) B1970617
theorem B1750947 : Blo 1750576 1750947 := bstep (se 1 (by rfl) ⟨1313210, by rfl⟩ : syracuseStep 1750947 = 2626421) B2626421
theorem B4265891 : Blo 1750576 4265891 := bstep (se 1 (by rfl) ⟨3199418, by rfl⟩ : syracuseStep 4265891 = 6398837) B6398837
theorem B1750963 : Blo 1750576 1750963 := bstep (se 1 (by rfl) ⟨1313222, by rfl⟩ : syracuseStep 1750963 = 2626445) B2626445
theorem B2627507 : Blo 1750576 2627507 := bstep (se 1 (by rfl) ⟨1970630, by rfl⟩ : syracuseStep 2627507 = 3941261) B3941261
theorem B1750979 : Blo 1750576 1750979 := bstep (se 1 (by rfl) ⟨1313234, by rfl⟩ : syracuseStep 1750979 = 2626469) B2626469
theorem B2955217 : Blo 1750576 2955217 := bstep (se 2 (by rfl) ⟨1108206, by rfl⟩ : syracuseStep 2955217 = 2216413) B2216413
theorem B2627537 : Blo 1750576 2627537 := bstep (se 2 (by rfl) ⟨985326, by rfl⟩ : syracuseStep 2627537 = 1970653) B1970653
theorem B1750995 : Blo 1750576 1750995 := bstep (se 1 (by rfl) ⟨1313246, by rfl⟩ : syracuseStep 1750995 = 2626493) B2626493
theorem B1751011 : Blo 1750576 1751011 := bstep (se 1 (by rfl) ⟨1313258, by rfl⟩ : syracuseStep 1751011 = 2626517) B2626517
theorem B2627555 : Blo 1750576 2627555 := bstep (se 1 (by rfl) ⟨1970666, by rfl⟩ : syracuseStep 2627555 = 3941333) B3941333
theorem B1751027 : Blo 1750576 1751027 := bstep (se 1 (by rfl) ⟨1313270, by rfl⟩ : syracuseStep 1751027 = 2626541) B2626541
theorem B2955251 : Blo 1750576 2955251 := bstep (se 1 (by rfl) ⟨2216438, by rfl⟩ : syracuseStep 2955251 = 4432877) B4432877
theorem B2627585 : Blo 1750576 2627585 := bstep (se 2 (by rfl) ⟨985344, by rfl⟩ : syracuseStep 2627585 = 1970689) B1970689
theorem B1751043 : Blo 1750576 1751043 := bstep (se 1 (by rfl) ⟨1313282, by rfl⟩ : syracuseStep 1751043 = 2626565) B2626565
theorem B1751059 : Blo 1750576 1751059 := bstep (se 1 (by rfl) ⟨1313294, by rfl⟩ : syracuseStep 1751059 = 2626589) B2626589
theorem B2627603 : Blo 1750576 2627603 := bstep (se 1 (by rfl) ⟨1970702, by rfl⟩ : syracuseStep 2627603 = 3941405) B3941405
theorem B1751075 : Blo 1750576 1751075 := bstep (se 1 (by rfl) ⟨1313306, by rfl⟩ : syracuseStep 1751075 = 2626613) B2626613
theorem B3037219 : Blo 1750576 3037219 := bstep (se 1 (by rfl) ⟨2277914, by rfl⟩ : syracuseStep 3037219 = 4555829) B4555829
theorem B5912621 : Blo 1750576 5912621 := bstep (se 3 (by rfl) ⟨1108616, by rfl⟩ : syracuseStep 5912621 = 2217233) B2217233
theorem B2627633 : Blo 1750576 2627633 := bstep (se 2 (by rfl) ⟨985362, by rfl⟩ : syracuseStep 2627633 = 1970725) B1970725
theorem B1751091 : Blo 1750576 1751091 := bstep (se 1 (by rfl) ⟨1313318, by rfl⟩ : syracuseStep 1751091 = 2626637) B2626637
theorem B1751107 : Blo 1750576 1751107 := bstep (se 1 (by rfl) ⟨1313330, by rfl⟩ : syracuseStep 1751107 = 2626661) B2626661
theorem B2996291 : Blo 1750576 2996291 := bstep (se 1 (by rfl) ⟨2247218, by rfl⟩ : syracuseStep 2996291 = 4494437) B4494437
theorem B2627651 : Blo 1750576 2627651 := bstep (se 1 (by rfl) ⟨1970738, by rfl⟩ : syracuseStep 2627651 = 3941477) B3941477
theorem B1751123 : Blo 1750576 1751123 := bstep (se 1 (by rfl) ⟨1313342, by rfl⟩ : syracuseStep 1751123 = 2626685) B2626685
theorem B2627681 : Blo 1750576 2627681 := bstep (se 2 (by rfl) ⟨985380, by rfl⟩ : syracuseStep 2627681 = 1970761) B1970761
theorem B1751139 : Blo 1750576 1751139 := bstep (se 1 (by rfl) ⟨1313354, by rfl⟩ : syracuseStep 1751139 = 2626709) B2626709
theorem B5912675 : Blo 1750576 5912675 := bstep (se 1 (by rfl) ⟨4434506, by rfl⟩ : syracuseStep 5912675 = 8869013) B8869013
theorem B1751155 : Blo 1750576 1751155 := bstep (se 1 (by rfl) ⟨1313366, by rfl⟩ : syracuseStep 1751155 = 2626733) B2626733
theorem B2955379 : Blo 1750576 2955379 := bstep (se 1 (by rfl) ⟨2216534, by rfl⟩ : syracuseStep 2955379 = 4433069) B4433069
theorem B2627699 : Blo 1750576 2627699 := bstep (se 1 (by rfl) ⟨1970774, by rfl⟩ : syracuseStep 2627699 = 3941549) B3941549
theorem B2218099 : Blo 1750576 2218099 := bstep (se 1 (by rfl) ⟨1663574, by rfl⟩ : syracuseStep 2218099 = 3327149) B3327149
theorem B1751171 : Blo 1750576 1751171 := bstep (se 1 (by rfl) ⟨1313378, by rfl⟩ : syracuseStep 1751171 = 2626757) B2626757
theorem B4987021 : Blo 1750576 4987021 := bstep (se 3 (by rfl) ⟨935066, by rfl⟩ : syracuseStep 4987021 = 1870133) B1870133
theorem B2627729 : Blo 1750576 2627729 := bstep (se 2 (by rfl) ⟨985398, by rfl⟩ : syracuseStep 2627729 = 1970797) B1970797
theorem B1751187 : Blo 1750576 1751187 := bstep (se 1 (by rfl) ⟨1313390, by rfl⟩ : syracuseStep 1751187 = 2626781) B2626781
theorem B1751203 : Blo 1750576 1751203 := bstep (se 1 (by rfl) ⟨1313402, by rfl⟩ : syracuseStep 1751203 = 2626805) B2626805
theorem B2627747 : Blo 1750576 2627747 := bstep (se 1 (by rfl) ⟨1970810, by rfl⟩ : syracuseStep 2627747 = 3941621) B3941621
theorem B5609645 : Blo 1750576 5609645 := bstep (se 3 (by rfl) ⟨1051808, by rfl⟩ : syracuseStep 5609645 = 2103617) B2103617
theorem B1751219 : Blo 1750576 1751219 := bstep (se 1 (by rfl) ⟨1313414, by rfl⟩ : syracuseStep 1751219 = 2626829) B2626829
theorem B2627777 : Blo 1750576 2627777 := bstep (se 2 (by rfl) ⟨985416, by rfl⟩ : syracuseStep 2627777 = 1970833) B1970833
theorem B1751235 : Blo 1750576 1751235 := bstep (se 1 (by rfl) ⟨1313426, by rfl⟩ : syracuseStep 1751235 = 2626853) B2626853
theorem B1751251 : Blo 1750576 1751251 := bstep (se 1 (by rfl) ⟨1313438, by rfl⟩ : syracuseStep 1751251 = 2626877) B2626877
theorem B2627795 : Blo 1750576 2627795 := bstep (se 1 (by rfl) ⟨1970846, by rfl⟩ : syracuseStep 2627795 = 3941693) B3941693
theorem B1751267 : Blo 1750576 1751267 := bstep (se 1 (by rfl) ⟨1313450, by rfl⟩ : syracuseStep 1751267 = 2626901) B2626901
theorem B3741923 : Blo 1750576 3741923 := bstep (se 1 (by rfl) ⟨2806442, by rfl⟩ : syracuseStep 3741923 = 5612885) B5612885
theorem B2627825 : Blo 1750576 2627825 := bstep (se 2 (by rfl) ⟨985434, by rfl⟩ : syracuseStep 2627825 = 1970869) B1970869
theorem B1751283 : Blo 1750576 1751283 := bstep (se 1 (by rfl) ⟨1313462, by rfl⟩ : syracuseStep 1751283 = 2626925) B2626925
theorem B2955521 : Blo 1750576 2955521 := bstep (se 2 (by rfl) ⟨1108320, by rfl⟩ : syracuseStep 2955521 = 2216641) B2216641
theorem B1751299 : Blo 1750576 1751299 := bstep (se 1 (by rfl) ⟨1313474, by rfl⟩ : syracuseStep 1751299 = 2626949) B2626949
theorem B2627843 : Blo 1750576 2627843 := bstep (se 1 (by rfl) ⟨1970882, by rfl⟩ : syracuseStep 2627843 = 3941765) B3941765
theorem B17971469 : Blo 1750576 17971469 := bstep (se 3 (by rfl) ⟨3369650, by rfl⟩ : syracuseStep 17971469 = 6739301) B6739301
theorem B5994769 : Blo 1750576 5994769 := bstep (se 2 (by rfl) ⟨2248038, by rfl⟩ : syracuseStep 5994769 = 4496077) B4496077
theorem B1751315 : Blo 1750576 1751315 := bstep (se 1 (by rfl) ⟨1313486, by rfl⟩ : syracuseStep 1751315 = 2626973) B2626973
theorem B2627873 : Blo 1750576 2627873 := bstep (se 2 (by rfl) ⟨985452, by rfl⟩ : syracuseStep 2627873 = 1970905) B1970905
theorem B1751331 : Blo 1750576 1751331 := bstep (se 1 (by rfl) ⟨1313498, by rfl⟩ : syracuseStep 1751331 = 2626997) B2626997
theorem B1751347 : Blo 1750576 1751347 := bstep (se 1 (by rfl) ⟨1313510, by rfl⟩ : syracuseStep 1751347 = 2627021) B2627021
theorem B2627891 : Blo 1750576 2627891 := bstep (se 1 (by rfl) ⟨1970918, by rfl⟩ : syracuseStep 2627891 = 3941837) B3941837
theorem B1751363 : Blo 1750576 1751363 := bstep (se 1 (by rfl) ⟨1313522, by rfl⟩ : syracuseStep 1751363 = 2627045) B2627045
theorem B2627921 : Blo 1750576 2627921 := bstep (se 2 (by rfl) ⟨985470, by rfl⟩ : syracuseStep 2627921 = 1970941) B1970941
theorem B1751379 : Blo 1750576 1751379 := bstep (se 1 (by rfl) ⟨1313534, by rfl⟩ : syracuseStep 1751379 = 2627069) B2627069
theorem B1751395 : Blo 1750576 1751395 := bstep (se 1 (by rfl) ⟨1313546, by rfl⟩ : syracuseStep 1751395 = 2627093) B2627093
theorem B2627939 : Blo 1750576 2627939 := bstep (se 1 (by rfl) ⟨1970954, by rfl⟩ : syracuseStep 2627939 = 3941909) B3941909
theorem B11221361 : Blo 1750576 11221361 := bstep (se 2 (by rfl) ⟨4208010, by rfl⟩ : syracuseStep 11221361 = 8416021) B8416021
theorem B5912945 : Blo 1750576 5912945 := bstep (se 2 (by rfl) ⟨2217354, by rfl⟩ : syracuseStep 5912945 = 4434709) B4434709
theorem B1997171 : Blo 1750576 1997171 := bstep (se 1 (by rfl) ⟨1497878, by rfl⟩ : syracuseStep 1997171 = 2995757) B2995757
theorem B1751411 : Blo 1750576 1751411 := bstep (se 1 (by rfl) ⟨1313558, by rfl⟩ : syracuseStep 1751411 = 2627117) B2627117
theorem B2955649 : Blo 1750576 2955649 := bstep (se 2 (by rfl) ⟨1108368, by rfl⟩ : syracuseStep 2955649 = 2216737) B2216737
theorem B2627969 : Blo 1750576 2627969 := bstep (se 2 (by rfl) ⟨985488, by rfl⟩ : syracuseStep 2627969 = 1970977) B1970977
theorem B1751427 : Blo 1750576 1751427 := bstep (se 1 (by rfl) ⟨1313570, by rfl⟩ : syracuseStep 1751427 = 2627141) B2627141
theorem B31947149 : Blo 1750576 31947149 := bstep (se 3 (by rfl) ⟨5990090, by rfl⟩ : syracuseStep 31947149 = 11980181) B11980181
theorem B1751443 : Blo 1750576 1751443 := bstep (se 1 (by rfl) ⟨1313582, by rfl⟩ : syracuseStep 1751443 = 2627165) B2627165
theorem B2627987 : Blo 1750576 2627987 := bstep (se 1 (by rfl) ⟨1970990, by rfl⟩ : syracuseStep 2627987 = 3941981) B3941981
theorem B1751459 : Blo 1750576 1751459 := bstep (se 1 (by rfl) ⟨1313594, by rfl⟩ : syracuseStep 1751459 = 2627189) B2627189
theorem B2955683 : Blo 1750576 2955683 := bstep (se 1 (by rfl) ⟨2216762, by rfl⟩ : syracuseStep 2955683 = 4433525) B4433525
theorem B2628017 : Blo 1750576 2628017 := bstep (se 2 (by rfl) ⟨985506, by rfl⟩ : syracuseStep 2628017 = 1971013) B1971013
theorem B1751475 : Blo 1750576 1751475 := bstep (se 1 (by rfl) ⟨1313606, by rfl⟩ : syracuseStep 1751475 = 2627213) B2627213
theorem B1751491 : Blo 1750576 1751491 := bstep (se 1 (by rfl) ⟨1313618, by rfl⟩ : syracuseStep 1751491 = 2627237) B2627237
theorem B2628035 : Blo 1750576 2628035 := bstep (se 1 (by rfl) ⟨1971026, by rfl⟩ : syracuseStep 2628035 = 3942053) B3942053
theorem B1751507 : Blo 1750576 1751507 := bstep (se 1 (by rfl) ⟨1313630, by rfl⟩ : syracuseStep 1751507 = 2627261) B2627261
theorem B2628065 : Blo 1750576 2628065 := bstep (se 2 (by rfl) ⟨985524, by rfl⟩ : syracuseStep 2628065 = 1971049) B1971049
theorem B1751523 : Blo 1750576 1751523 := bstep (se 1 (by rfl) ⟨1313642, by rfl⟩ : syracuseStep 1751523 = 2627285) B2627285
theorem B5994989 : Blo 1750576 5994989 := bstep (se 3 (by rfl) ⟨1124060, by rfl⟩ : syracuseStep 5994989 = 2248121) B2248121
theorem B1751539 : Blo 1750576 1751539 := bstep (se 1 (by rfl) ⟨1313654, by rfl⟩ : syracuseStep 1751539 = 2627309) B2627309
theorem B2628083 : Blo 1750576 2628083 := bstep (se 1 (by rfl) ⟨1971062, by rfl⟩ : syracuseStep 2628083 = 3942125) B3942125
theorem B1751555 : Blo 1750576 1751555 := bstep (se 1 (by rfl) ⟨1313666, by rfl⟩ : syracuseStep 1751555 = 2627333) B2627333
theorem B7485965 : Blo 1750576 7485965 := bstep (se 3 (by rfl) ⟨1403618, by rfl⟩ : syracuseStep 7485965 = 2807237) B2807237
theorem B2464273 : Blo 1750576 2464273 := bstep (se 2 (by rfl) ⟨924102, by rfl⟩ : syracuseStep 2464273 = 1848205) B1848205
theorem B1751571 : Blo 1750576 1751571 := bstep (se 1 (by rfl) ⟨1313678, by rfl⟩ : syracuseStep 1751571 = 2627357) B2627357
theorem B2628113 : Blo 1750576 2628113 := bstep (se 2 (by rfl) ⟨985542, by rfl⟩ : syracuseStep 2628113 = 1971085) B1971085
theorem B1751587 : Blo 1750576 1751587 := bstep (se 1 (by rfl) ⟨1313690, by rfl⟩ : syracuseStep 1751587 = 2627381) B2627381
theorem B2955811 : Blo 1750576 2955811 := bstep (se 1 (by rfl) ⟨2216858, by rfl⟩ : syracuseStep 2955811 = 4433717) B4433717
theorem B2628131 : Blo 1750576 2628131 := bstep (se 1 (by rfl) ⟨1971098, by rfl⟩ : syracuseStep 2628131 = 3942197) B3942197
theorem B1751603 : Blo 1750576 1751603 := bstep (se 1 (by rfl) ⟨1313702, by rfl⟩ : syracuseStep 1751603 = 2627405) B2627405
theorem B2628161 : Blo 1750576 2628161 := bstep (se 2 (by rfl) ⟨985560, by rfl⟩ : syracuseStep 2628161 = 1971121) B1971121
theorem B1751619 : Blo 1750576 1751619 := bstep (se 1 (by rfl) ⟨1313714, by rfl⟩ : syracuseStep 1751619 = 2627429) B2627429
theorem B5610065 : Blo 1750576 5610065 := bstep (se 2 (by rfl) ⟨2103774, by rfl⟩ : syracuseStep 5610065 = 4207549) B4207549
theorem B1751635 : Blo 1750576 1751635 := bstep (se 1 (by rfl) ⟨1313726, by rfl⟩ : syracuseStep 1751635 = 2627453) B2627453
theorem B2628179 : Blo 1750576 2628179 := bstep (se 1 (by rfl) ⟨1971134, by rfl⟩ : syracuseStep 2628179 = 3942269) B3942269
theorem B1751651 : Blo 1750576 1751651 := bstep (se 1 (by rfl) ⟨1313738, by rfl⟩ : syracuseStep 1751651 = 2627477) B2627477
theorem B2628209 : Blo 1750576 2628209 := bstep (se 2 (by rfl) ⟨985578, by rfl⟩ : syracuseStep 2628209 = 1971157) B1971157
theorem B1751667 : Blo 1750576 1751667 := bstep (se 1 (by rfl) ⟨1313750, by rfl⟩ : syracuseStep 1751667 = 2627501) B2627501
theorem B1751683 : Blo 1750576 1751683 := bstep (se 1 (by rfl) ⟨1313762, by rfl⟩ : syracuseStep 1751683 = 2627525) B2627525
theorem B2628227 : Blo 1750576 2628227 := bstep (se 1 (by rfl) ⟨1971170, by rfl⟩ : syracuseStep 2628227 = 3942341) B3942341
theorem B1751699 : Blo 1750576 1751699 := bstep (se 1 (by rfl) ⟨1313774, by rfl⟩ : syracuseStep 1751699 = 2627549) B2627549
theorem B2628257 : Blo 1750576 2628257 := bstep (se 2 (by rfl) ⟨985596, by rfl⟩ : syracuseStep 2628257 = 1971193) B1971193
theorem B8862371 : Blo 1750576 8862371 := bstep (se 1 (by rfl) ⟨6646778, by rfl⟩ : syracuseStep 8862371 = 13293557) B13293557
theorem B4733603 : Blo 1750576 4733603 := bstep (se 1 (by rfl) ⟨3550202, by rfl⟩ : syracuseStep 4733603 = 7100405) B7100405
theorem B6650531 : Blo 1750576 6650531 := bstep (se 1 (by rfl) ⟨4987898, by rfl⟩ : syracuseStep 6650531 = 9975797) B9975797
theorem B1751715 : Blo 1750576 1751715 := bstep (se 1 (by rfl) ⟨1313786, by rfl⟩ : syracuseStep 1751715 = 2627573) B2627573
theorem B3938993 : Blo 1750576 3938993 := bstep (se 2 (by rfl) ⟨1477122, by rfl⟩ : syracuseStep 3938993 = 2954245) B2954245
theorem B6650545 : Blo 1750576 6650545 := bstep (se 2 (by rfl) ⟨2493954, by rfl⟩ : syracuseStep 6650545 = 4987909) B4987909
theorem B2955953 : Blo 1750576 2955953 := bstep (se 2 (by rfl) ⟨1108482, by rfl⟩ : syracuseStep 2955953 = 2216965) B2216965
theorem B1751731 : Blo 1750576 1751731 := bstep (se 1 (by rfl) ⟨1313798, by rfl⟩ : syracuseStep 1751731 = 2627597) B2627597
theorem B2628275 : Blo 1750576 2628275 := bstep (se 1 (by rfl) ⟨1971206, by rfl⟩ : syracuseStep 2628275 = 3942413) B3942413
theorem B3939011 : Blo 1750576 3939011 := bstep (se 1 (by rfl) ⟨2954258, by rfl⟩ : syracuseStep 3939011 = 5908517) B5908517
theorem B1751747 : Blo 1750576 1751747 := bstep (se 1 (by rfl) ⟨1313810, by rfl⟩ : syracuseStep 1751747 = 2627621) B2627621
theorem B2628305 : Blo 1750576 2628305 := bstep (se 2 (by rfl) ⟨985614, by rfl⟩ : syracuseStep 2628305 = 1971229) B1971229
theorem B1751763 : Blo 1750576 1751763 := bstep (se 1 (by rfl) ⟨1313822, by rfl⟩ : syracuseStep 1751763 = 2627645) B2627645
theorem B9976547 : Blo 1750576 9976547 := bstep (se 1 (by rfl) ⟨7482410, by rfl⟩ : syracuseStep 9976547 = 14964821) B14964821
theorem B1751779 : Blo 1750576 1751779 := bstep (se 1 (by rfl) ⟨1313834, by rfl⟩ : syracuseStep 1751779 = 2627669) B2627669
theorem B76798691 : Blo 1750576 76798691 := bstep (se 1 (by rfl) ⟨57599018, by rfl⟩ : syracuseStep 76798691 = 115198037) B115198037
theorem B2628323 : Blo 1750576 2628323 := bstep (se 1 (by rfl) ⟨1971242, by rfl⟩ : syracuseStep 2628323 = 3942485) B3942485
theorem B1751795 : Blo 1750576 1751795 := bstep (se 1 (by rfl) ⟨1313846, by rfl⟩ : syracuseStep 1751795 = 2627693) B2627693
theorem B2628353 : Blo 1750576 2628353 := bstep (se 2 (by rfl) ⟨985632, by rfl⟩ : syracuseStep 2628353 = 1971265) B1971265
theorem B1751811 : Blo 1750576 1751811 := bstep (se 1 (by rfl) ⟨1313858, by rfl⟩ : syracuseStep 1751811 = 2627717) B2627717
theorem B13662989 : Blo 1750576 13662989 := bstep (se 3 (by rfl) ⟨2561810, by rfl⟩ : syracuseStep 13662989 = 5123621) B5123621
theorem B1751827 : Blo 1750576 1751827 := bstep (se 1 (by rfl) ⟨1313870, by rfl⟩ : syracuseStep 1751827 = 2627741) B2627741
theorem B2628371 : Blo 1750576 2628371 := bstep (se 1 (by rfl) ⟨1971278, by rfl⟩ : syracuseStep 2628371 = 3942557) B3942557
theorem B1751843 : Blo 1750576 1751843 := bstep (se 1 (by rfl) ⟨1313882, by rfl⟩ : syracuseStep 1751843 = 2627765) B2627765
theorem B2956081 : Blo 1750576 2956081 := bstep (se 2 (by rfl) ⟨1108530, by rfl⟩ : syracuseStep 2956081 = 2217061) B2217061
theorem B1751859 : Blo 1750576 1751859 := bstep (se 1 (by rfl) ⟨1313894, by rfl⟩ : syracuseStep 1751859 = 2627789) B2627789
theorem B2628401 : Blo 1750576 2628401 := bstep (se 2 (by rfl) ⟨985650, by rfl⟩ : syracuseStep 2628401 = 1971301) B1971301
theorem B1751875 : Blo 1750576 1751875 := bstep (se 1 (by rfl) ⟨1313906, by rfl⟩ : syracuseStep 1751875 = 2627813) B2627813
theorem B2628419 : Blo 1750576 2628419 := bstep (se 1 (by rfl) ⟨1971314, by rfl⟩ : syracuseStep 2628419 = 3942629) B3942629
theorem B2956115 : Blo 1750576 2956115 := bstep (se 1 (by rfl) ⟨2217086, by rfl⟩ : syracuseStep 2956115 = 4434173) B4434173
theorem B1751891 : Blo 1750576 1751891 := bstep (se 1 (by rfl) ⟨1313918, by rfl⟩ : syracuseStep 1751891 = 2627837) B2627837
theorem B2628449 : Blo 1750576 2628449 := bstep (se 2 (by rfl) ⟨985668, by rfl⟩ : syracuseStep 2628449 = 1971337) B1971337
theorem B1751907 : Blo 1750576 1751907 := bstep (se 1 (by rfl) ⟨1313930, by rfl⟩ : syracuseStep 1751907 = 2627861) B2627861
theorem B1751923 : Blo 1750576 1751923 := bstep (se 1 (by rfl) ⟨1313942, by rfl⟩ : syracuseStep 1751923 = 2627885) B2627885
theorem B2628467 : Blo 1750576 2628467 := bstep (se 1 (by rfl) ⟨1971350, by rfl⟩ : syracuseStep 2628467 = 3942701) B3942701
theorem B1751939 : Blo 1750576 1751939 := bstep (se 1 (by rfl) ⟨1313954, by rfl⟩ : syracuseStep 1751939 = 2627909) B2627909
theorem B5913485 : Blo 1750576 5913485 := bstep (se 3 (by rfl) ⟨1108778, by rfl⟩ : syracuseStep 5913485 = 2217557) B2217557
theorem B3324817 : Blo 1750576 3324817 := bstep (se 2 (by rfl) ⟨1246806, by rfl⟩ : syracuseStep 3324817 = 2493613) B2493613
theorem B2628497 : Blo 1750576 2628497 := bstep (se 2 (by rfl) ⟨985686, by rfl⟩ : syracuseStep 2628497 = 1971373) B1971373
theorem B1751955 : Blo 1750576 1751955 := bstep (se 1 (by rfl) ⟨1313966, by rfl⟩ : syracuseStep 1751955 = 2627933) B2627933
theorem B1751971 : Blo 1750576 1751971 := bstep (se 1 (by rfl) ⟨1313978, by rfl⟩ : syracuseStep 1751971 = 2627957) B2627957
theorem B2628515 : Blo 1750576 2628515 := bstep (se 1 (by rfl) ⟨1971386, by rfl⟩ : syracuseStep 2628515 = 3942773) B3942773
theorem B1751987 : Blo 1750576 1751987 := bstep (se 1 (by rfl) ⟨1313990, by rfl⟩ : syracuseStep 1751987 = 2627981) B2627981
theorem B2366401 : Blo 1750576 2366401 := bstep (se 2 (by rfl) ⟨887400, by rfl⟩ : syracuseStep 2366401 = 1774801) B1774801
theorem B1752003 : Blo 1750576 1752003 := bstep (se 1 (by rfl) ⟨1314002, by rfl⟩ : syracuseStep 1752003 = 2628005) B2628005
theorem B5913539 : Blo 1750576 5913539 := bstep (se 1 (by rfl) ⟨4435154, by rfl⟩ : syracuseStep 5913539 = 8870309) B8870309
theorem B2628545 : Blo 1750576 2628545 := bstep (se 2 (by rfl) ⟨985704, by rfl⟩ : syracuseStep 2628545 = 1971409) B1971409
theorem B3939281 : Blo 1750576 3939281 := bstep (se 2 (by rfl) ⟨1477230, by rfl⟩ : syracuseStep 3939281 = 2954461) B2954461
theorem B2956243 : Blo 1750576 2956243 := bstep (se 1 (by rfl) ⟨2217182, by rfl⟩ : syracuseStep 2956243 = 4434365) B4434365
theorem B1752019 : Blo 1750576 1752019 := bstep (se 1 (by rfl) ⟨1314014, by rfl⟩ : syracuseStep 1752019 = 2628029) B2628029
theorem B2628563 : Blo 1750576 2628563 := bstep (se 1 (by rfl) ⟨1971422, by rfl⟩ : syracuseStep 2628563 = 3942845) B3942845
theorem B7478243 : Blo 1750576 7478243 := bstep (se 1 (by rfl) ⟨5608682, by rfl⟩ : syracuseStep 7478243 = 11217365) B11217365
theorem B3939299 : Blo 1750576 3939299 := bstep (se 1 (by rfl) ⟨2954474, by rfl⟩ : syracuseStep 3939299 = 5908949) B5908949
theorem B1752035 : Blo 1750576 1752035 := bstep (se 1 (by rfl) ⟨1314026, by rfl⟩ : syracuseStep 1752035 = 2628053) B2628053
theorem B2628593 : Blo 1750576 2628593 := bstep (se 2 (by rfl) ⟨985722, by rfl⟩ : syracuseStep 2628593 = 1971445) B1971445
theorem B1752051 : Blo 1750576 1752051 := bstep (se 1 (by rfl) ⟨1314038, by rfl⟩ : syracuseStep 1752051 = 2628077) B2628077
theorem B1752067 : Blo 1750576 1752067 := bstep (se 1 (by rfl) ⟨1314050, by rfl⟩ : syracuseStep 1752067 = 2628101) B2628101
theorem B2628611 : Blo 1750576 2628611 := bstep (se 1 (by rfl) ⟨1971458, by rfl⟩ : syracuseStep 2628611 = 3942917) B3942917
theorem B1752083 : Blo 1750576 1752083 := bstep (se 1 (by rfl) ⟨1314062, by rfl⟩ : syracuseStep 1752083 = 2628125) B2628125
theorem B2628641 : Blo 1750576 2628641 := bstep (se 2 (by rfl) ⟨985740, by rfl⟩ : syracuseStep 2628641 = 1971481) B1971481
theorem B1752099 : Blo 1750576 1752099 := bstep (se 1 (by rfl) ⟨1314074, by rfl⟩ : syracuseStep 1752099 = 2628149) B2628149
theorem B10804259 : Blo 1750576 10804259 := bstep (se 1 (by rfl) ⟨8103194, by rfl⟩ : syracuseStep 10804259 = 16206389) B16206389
theorem B1752115 : Blo 1750576 1752115 := bstep (se 1 (by rfl) ⟨1314086, by rfl⟩ : syracuseStep 1752115 = 2628173) B2628173
theorem B2628659 : Blo 1750576 2628659 := bstep (se 1 (by rfl) ⟨1971494, by rfl⟩ : syracuseStep 2628659 = 3942989) B3942989
theorem B1752131 : Blo 1750576 1752131 := bstep (se 1 (by rfl) ⟨1314098, by rfl⟩ : syracuseStep 1752131 = 2628197) B2628197
theorem B2628689 : Blo 1750576 2628689 := bstep (se 2 (by rfl) ⟨985758, by rfl⟩ : syracuseStep 2628689 = 1971517) B1971517
theorem B1752147 : Blo 1750576 1752147 := bstep (se 1 (by rfl) ⟨1314110, by rfl⟩ : syracuseStep 1752147 = 2628221) B2628221
theorem B2956385 : Blo 1750576 2956385 := bstep (se 2 (by rfl) ⟨1108644, by rfl⟩ : syracuseStep 2956385 = 2217289) B2217289
theorem B1752163 : Blo 1750576 1752163 := bstep (se 1 (by rfl) ⟨1314122, by rfl⟩ : syracuseStep 1752163 = 2628245) B2628245
theorem B2628707 : Blo 1750576 2628707 := bstep (se 1 (by rfl) ⟨1971530, by rfl⟩ : syracuseStep 2628707 = 3943061) B3943061
theorem B242752625 : Blo 1750576 242752625 := bstep (se 2 (by rfl) ⟨91032234, by rfl⟩ : syracuseStep 242752625 = 182064469) B182064469
theorem B1752179 : Blo 1750576 1752179 := bstep (se 1 (by rfl) ⟨1314134, by rfl⟩ : syracuseStep 1752179 = 2628269) B2628269
theorem B2628737 : Blo 1750576 2628737 := bstep (se 2 (by rfl) ⟨985776, by rfl⟩ : syracuseStep 2628737 = 1971553) B1971553
theorem B1752195 : Blo 1750576 1752195 := bstep (se 1 (by rfl) ⟨1314146, by rfl⟩ : syracuseStep 1752195 = 2628293) B2628293
theorem B10648709 : Blo 1750576 10648709 := bstep (se 4 (by rfl) ⟨998316, by rfl⟩ : syracuseStep 10648709 = 1996633) B1996633
theorem B5053585 : Blo 1750576 5053585 := bstep (se 2 (by rfl) ⟨1895094, by rfl⟩ : syracuseStep 5053585 = 3790189) B3790189
theorem B1752211 : Blo 1750576 1752211 := bstep (se 1 (by rfl) ⟨1314158, by rfl⟩ : syracuseStep 1752211 = 2628317) B2628317
theorem B2628755 : Blo 1750576 2628755 := bstep (se 1 (by rfl) ⟨1971566, by rfl⟩ : syracuseStep 2628755 = 3943133) B3943133
theorem B1752227 : Blo 1750576 1752227 := bstep (se 1 (by rfl) ⟨1314170, by rfl⟩ : syracuseStep 1752227 = 2628341) B2628341
theorem B4988081 : Blo 1750576 4988081 := bstep (se 2 (by rfl) ⟨1870530, by rfl⟩ : syracuseStep 4988081 = 3741061) B3741061
theorem B2628785 : Blo 1750576 2628785 := bstep (se 2 (by rfl) ⟨985794, by rfl⟩ : syracuseStep 2628785 = 1971589) B1971589
theorem B1752243 : Blo 1750576 1752243 := bstep (se 1 (by rfl) ⟨1314182, by rfl⟩ : syracuseStep 1752243 = 2628365) B2628365
theorem B1752259 : Blo 1750576 1752259 := bstep (se 1 (by rfl) ⟨1314194, by rfl⟩ : syracuseStep 1752259 = 2628389) B2628389
theorem B2628803 : Blo 1750576 2628803 := bstep (se 1 (by rfl) ⟨1971602, by rfl⟩ : syracuseStep 2628803 = 3943205) B3943205
theorem B5913809 : Blo 1750576 5913809 := bstep (se 2 (by rfl) ⟨2217678, by rfl⟩ : syracuseStep 5913809 = 4435357) B4435357
theorem B1752275 : Blo 1750576 1752275 := bstep (se 1 (by rfl) ⟨1314206, by rfl⟩ : syracuseStep 1752275 = 2628413) B2628413
theorem B2956513 : Blo 1750576 2956513 := bstep (se 2 (by rfl) ⟨1108692, by rfl⟩ : syracuseStep 2956513 = 2217385) B2217385
theorem B1752291 : Blo 1750576 1752291 := bstep (se 1 (by rfl) ⟨1314218, by rfl⟩ : syracuseStep 1752291 = 2628437) B2628437
theorem B2628833 : Blo 1750576 2628833 := bstep (se 2 (by rfl) ⟨985812, by rfl⟩ : syracuseStep 2628833 = 1971625) B1971625
theorem B3939569 : Blo 1750576 3939569 := bstep (se 2 (by rfl) ⟨1477338, by rfl⟩ : syracuseStep 3939569 = 2954677) B2954677
theorem B1752307 : Blo 1750576 1752307 := bstep (se 1 (by rfl) ⟨1314230, by rfl⟩ : syracuseStep 1752307 = 2628461) B2628461
theorem B2628851 : Blo 1750576 2628851 := bstep (se 1 (by rfl) ⟨1971638, by rfl⟩ : syracuseStep 2628851 = 3943277) B3943277
theorem B3939587 : Blo 1750576 3939587 := bstep (se 1 (by rfl) ⟨2954690, by rfl⟩ : syracuseStep 3939587 = 5909381) B5909381
theorem B2956547 : Blo 1750576 2956547 := bstep (se 1 (by rfl) ⟨2217410, by rfl⟩ : syracuseStep 2956547 = 4434821) B4434821
theorem B1752323 : Blo 1750576 1752323 := bstep (se 1 (by rfl) ⟨1314242, by rfl⟩ : syracuseStep 1752323 = 2628485) B2628485
theorem B1752339 : Blo 1750576 1752339 := bstep (se 1 (by rfl) ⟨1314254, by rfl⟩ : syracuseStep 1752339 = 2628509) B2628509
theorem B1752355 : Blo 1750576 1752355 := bstep (se 1 (by rfl) ⟨1314266, by rfl⟩ : syracuseStep 1752355 = 2628533) B2628533
theorem B1752371 : Blo 1750576 1752371 := bstep (se 1 (by rfl) ⟨1314278, by rfl⟩ : syracuseStep 1752371 = 2628557) B2628557
theorem B1752387 : Blo 1750576 1752387 := bstep (se 1 (by rfl) ⟨1314290, by rfl⟩ : syracuseStep 1752387 = 2628581) B2628581
theorem B1752403 : Blo 1750576 1752403 := bstep (se 1 (by rfl) ⟨1314302, by rfl⟩ : syracuseStep 1752403 = 2628605) B2628605
theorem B1752419 : Blo 1750576 1752419 := bstep (se 1 (by rfl) ⟨1314314, by rfl⟩ : syracuseStep 1752419 = 2628629) B2628629
theorem B8871281 : Blo 1750576 8871281 := bstep (se 2 (by rfl) ⟨3326730, by rfl⟩ : syracuseStep 8871281 = 6653461) B6653461
theorem B1752435 : Blo 1750576 1752435 := bstep (se 1 (by rfl) ⟨1314326, by rfl⟩ : syracuseStep 1752435 = 2628653) B2628653
theorem B2956675 : Blo 1750576 2956675 := bstep (se 1 (by rfl) ⟨2217506, by rfl⟩ : syracuseStep 2956675 = 4435013) B4435013
theorem B1752451 : Blo 1750576 1752451 := bstep (se 1 (by rfl) ⟨1314338, by rfl⟩ : syracuseStep 1752451 = 2628677) B2628677
theorem B1752467 : Blo 1750576 1752467 := bstep (se 1 (by rfl) ⟨1314350, by rfl⟩ : syracuseStep 1752467 = 2628701) B2628701
theorem B1752483 : Blo 1750576 1752483 := bstep (se 1 (by rfl) ⟨1314362, by rfl⟩ : syracuseStep 1752483 = 2628725) B2628725
theorem B1752499 : Blo 1750576 1752499 := bstep (se 1 (by rfl) ⟨1314374, by rfl⟩ : syracuseStep 1752499 = 2628749) B2628749
theorem B2366915 : Blo 1750576 2366915 := bstep (se 1 (by rfl) ⟨1775186, by rfl⟩ : syracuseStep 2366915 = 3550373) B3550373
theorem B1752515 : Blo 1750576 1752515 := bstep (se 1 (by rfl) ⟨1314386, by rfl⟩ : syracuseStep 1752515 = 2628773) B2628773
theorem B8863181 : Blo 1750576 8863181 := bstep (se 3 (by rfl) ⟨1661846, by rfl⟩ : syracuseStep 8863181 = 3323693) B3323693
theorem B2997713 : Blo 1750576 2997713 := bstep (se 2 (by rfl) ⟨1124142, by rfl⟩ : syracuseStep 2997713 = 2248285) B2248285
theorem B1752531 : Blo 1750576 1752531 := bstep (se 1 (by rfl) ⟨1314398, by rfl⟩ : syracuseStep 1752531 = 2628797) B2628797
theorem B1752547 : Blo 1750576 1752547 := bstep (se 1 (by rfl) ⟨1314410, by rfl⟩ : syracuseStep 1752547 = 2628821) B2628821
theorem B4734445 : Blo 1750576 4734445 := bstep (se 3 (by rfl) ⟨887708, by rfl⟩ : syracuseStep 4734445 = 1775417) B1775417
theorem B1752563 : Blo 1750576 1752563 := bstep (se 1 (by rfl) ⟨1314422, by rfl⟩ : syracuseStep 1752563 = 2628845) B2628845
theorem B7200269 : Blo 1750576 7200269 := bstep (se 3 (by rfl) ⟨1350050, by rfl⟩ : syracuseStep 7200269 = 2700101) B2700101
theorem B3939857 : Blo 1750576 3939857 := bstep (se 2 (by rfl) ⟨1477446, by rfl⟩ : syracuseStep 3939857 = 2954893) B2954893
theorem B2956817 : Blo 1750576 2956817 := bstep (se 2 (by rfl) ⟨1108806, by rfl⟩ : syracuseStep 2956817 = 2217613) B2217613
theorem B3939875 : Blo 1750576 3939875 := bstep (se 1 (by rfl) ⟨2954906, by rfl⟩ : syracuseStep 3939875 = 5909813) B5909813
theorem B2956945 : Blo 1750576 2956945 := bstep (se 2 (by rfl) ⟨1108854, by rfl⟩ : syracuseStep 2956945 = 2217709) B2217709
theorem B2662049 : Blo 1750576 2662049 := bstep (se 2 (by rfl) ⟨998268, by rfl⟩ : syracuseStep 2662049 = 1996537) B1996537
theorem B2956979 : Blo 1750576 2956979 := bstep (se 1 (by rfl) ⟨2217734, by rfl⟩ : syracuseStep 2956979 = 4435469) B4435469
theorem B4210385 : Blo 1750576 4210385 := bstep (se 2 (by rfl) ⟨1578894, by rfl⟩ : syracuseStep 4210385 = 3157789) B3157789
theorem B5914349 : Blo 1750576 5914349 := bstep (se 3 (by rfl) ⟨1108940, by rfl⟩ : syracuseStep 5914349 = 2217881) B2217881
theorem B5914403 : Blo 1750576 5914403 := bstep (se 1 (by rfl) ⟨4435802, by rfl⟩ : syracuseStep 5914403 = 8871605) B8871605
theorem B10649393 : Blo 1750576 10649393 := bstep (se 2 (by rfl) ⟨3993522, by rfl⟩ : syracuseStep 10649393 = 7987045) B7987045
theorem B3940145 : Blo 1750576 3940145 := bstep (se 2 (by rfl) ⟨1477554, by rfl⟩ : syracuseStep 3940145 = 2955109) B2955109
theorem B2957107 : Blo 1750576 2957107 := bstep (se 1 (by rfl) ⟨2217830, by rfl⟩ : syracuseStep 2957107 = 4435661) B4435661
theorem B3940163 : Blo 1750576 3940163 := bstep (se 1 (by rfl) ⟨2955122, by rfl⟩ : syracuseStep 3940163 = 5910245) B5910245
theorem B4988753 : Blo 1750576 4988753 := bstep (se 2 (by rfl) ⟨1870782, by rfl⟩ : syracuseStep 4988753 = 3741565) B3741565
theorem B13295501 : Blo 1750576 13295501 := bstep (se 3 (by rfl) ⟨2492906, by rfl⟩ : syracuseStep 13295501 = 4985813) B4985813
theorem B4431793 : Blo 1750576 4431793 := bstep (se 2 (by rfl) ⟨1661922, by rfl⟩ : syracuseStep 4431793 = 3323845) B3323845
theorem B3325873 : Blo 1750576 3325873 := bstep (se 2 (by rfl) ⟨1247202, by rfl⟩ : syracuseStep 3325873 = 2494405) B2494405
theorem B2957249 : Blo 1750576 2957249 := bstep (se 2 (by rfl) ⟨1108968, by rfl⟩ : syracuseStep 2957249 = 2217937) B2217937
theorem B14958533 : Blo 1750576 14958533 := bstep (se 4 (by rfl) ⟨1402362, by rfl⟩ : syracuseStep 14958533 = 2804725) B2804725
theorem B2957323 : Blo 1750576 2957323 := bstep (se 1 (by rfl) ⟨2217992, by rfl⟩ : syracuseStep 2957323 = 4435985) B4435985
theorem B3326017 : Blo 1750576 3326017 := bstep (se 2 (by rfl) ⟨1247256, by rfl⟩ : syracuseStep 3326017 = 2494513) B2494513
theorem B3940505 : Blo 1750576 3940505 := bstep (se 2 (by rfl) ⟨1477689, by rfl⟩ : syracuseStep 3940505 = 2955379) B2955379
theorem B2957465 : Blo 1750576 2957465 := bstep (se 2 (by rfl) ⟨1109049, by rfl⟩ : syracuseStep 2957465 = 2218099) B2218099
theorem B25239757 : Blo 1750576 25239757 := bstep (se 3 (by rfl) ⟨4732454, by rfl⟩ : syracuseStep 25239757 = 9464909) B9464909
theorem B3940595 : Blo 1750576 3940595 := bstep (se 1 (by rfl) ⟨2955446, by rfl⟩ : syracuseStep 3940595 = 5910893) B5910893
theorem B3940631 : Blo 1750576 3940631 := bstep (se 1 (by rfl) ⟨2955473, by rfl⟩ : syracuseStep 3940631 = 5910947) B5910947
theorem B9978187 : Blo 1750576 9978187 := bstep (se 1 (by rfl) ⟨7483640, by rfl⟩ : syracuseStep 9978187 = 14967281) B14967281
theorem B4432279 : Blo 1750576 4432279 := bstep (se 1 (by rfl) ⟨3324209, by rfl⟩ : syracuseStep 4432279 = 6648419) B6648419
theorem B3326359 : Blo 1750576 3326359 := bstep (se 1 (by rfl) ⟨2494769, by rfl⟩ : syracuseStep 3326359 = 4989539) B4989539
theorem B15172019 : Blo 1750576 15172019 := bstep (se 1 (by rfl) ⟨11379014, by rfl⟩ : syracuseStep 15172019 = 22758029) B22758029
theorem B3940811 : Blo 1750576 3940811 := bstep (se 1 (by rfl) ⟨2955608, by rfl⟩ : syracuseStep 3940811 = 5911217) B5911217
theorem B4800971 : Blo 1750576 4800971 := bstep (se 1 (by rfl) ⟨3600728, by rfl⟩ : syracuseStep 4800971 = 7201457) B7201457
theorem B3940865 : Blo 1750576 3940865 := bstep (se 2 (by rfl) ⟨1477824, by rfl⟩ : syracuseStep 3940865 = 2955649) B2955649
theorem B10117649 : Blo 1750576 10117649 := bstep (se 2 (by rfl) ⟨3794118, by rfl⟩ : syracuseStep 10117649 = 7588237) B7588237
theorem B22454819 : Blo 1750576 22454819 := bstep (se 1 (by rfl) ⟨16841114, by rfl⟩ : syracuseStep 22454819 = 33682229) B33682229
theorem B9978461 : Blo 1750576 9978461 := bstep (se 3 (by rfl) ⟨1870961, by rfl⟩ : syracuseStep 9978461 = 3741923) B3741923
theorem B3326579 : Blo 1750576 3326579 := bstep (se 1 (by rfl) ⟨2494934, by rfl⟩ : syracuseStep 3326579 = 4989869) B4989869
theorem B3285697 : Blo 1750576 3285697 := bstep (se 2 (by rfl) ⟨1232136, by rfl⟩ : syracuseStep 3285697 = 2464273) B2464273
theorem B7987915 : Blo 1750576 7987915 := bstep (se 1 (by rfl) ⟨5990936, by rfl⟩ : syracuseStep 7987915 = 11981873) B11981873
theorem B7586507 : Blo 1750576 7586507 := bstep (se 1 (by rfl) ⟨5689880, by rfl⟩ : syracuseStep 7586507 = 11379761) B11379761
theorem B3941081 : Blo 1750576 3941081 := bstep (se 2 (by rfl) ⟨1477905, by rfl⟩ : syracuseStep 3941081 = 2955811) B2955811
theorem B14598947 : Blo 1750576 14598947 := bstep (se 1 (by rfl) ⟨10949210, by rfl⟩ : syracuseStep 14598947 = 21898421) B21898421
theorem B3154739 : Blo 1750576 3154739 := bstep (se 1 (by rfl) ⟨2366054, by rfl⟩ : syracuseStep 3154739 = 4732109) B4732109
theorem B3941171 : Blo 1750576 3941171 := bstep (se 1 (by rfl) ⟨2955878, by rfl⟩ : syracuseStep 3941171 = 5911757) B5911757
theorem B4432715 : Blo 1750576 4432715 := bstep (se 1 (by rfl) ⟨3324536, by rfl⟩ : syracuseStep 4432715 = 6649073) B6649073
theorem B3941207 : Blo 1750576 3941207 := bstep (se 1 (by rfl) ⟨2955905, by rfl⟩ : syracuseStep 3941207 = 5911811) B5911811
theorem B3326807 : Blo 1750576 3326807 := bstep (se 1 (by rfl) ⟨2495105, by rfl⟩ : syracuseStep 3326807 = 4990211) B4990211
theorem B34145201 : Blo 1750576 34145201 := bstep (se 2 (by rfl) ⟨12804450, by rfl⟩ : syracuseStep 34145201 = 25608901) B25608901
theorem B3941387 : Blo 1750576 3941387 := bstep (se 1 (by rfl) ⟨2956040, by rfl⟩ : syracuseStep 3941387 = 5912081) B5912081
theorem B3941441 : Blo 1750576 3941441 := bstep (se 2 (by rfl) ⟨1478040, by rfl⟩ : syracuseStep 3941441 = 2956081) B2956081
theorem B11224129 : Blo 1750576 11224129 := bstep (se 2 (by rfl) ⟨4209048, by rfl⟩ : syracuseStep 11224129 = 8418097) B8418097
theorem B3327065 : Blo 1750576 3327065 := bstep (se 2 (by rfl) ⟨1247649, by rfl⟩ : syracuseStep 3327065 = 2495299) B2495299
theorem B4433089 : Blo 1750576 4433089 := bstep (se 2 (by rfl) ⟨1662408, by rfl⟩ : syracuseStep 4433089 = 3324817) B3324817
theorem B3155201 : Blo 1750576 3155201 := bstep (se 2 (by rfl) ⟨1183200, by rfl⟩ : syracuseStep 3155201 = 2366401) B2366401
theorem B2843927 : Blo 1750576 2843927 := bstep (se 1 (by rfl) ⟨2132945, by rfl⟩ : syracuseStep 2843927 = 4265891) B4265891
theorem B3941657 : Blo 1750576 3941657 := bstep (se 2 (by rfl) ⟨1478121, by rfl⟩ : syracuseStep 3941657 = 2956243) B2956243
theorem B6653249 : Blo 1750576 6653249 := bstep (se 2 (by rfl) ⟨2494968, by rfl⟩ : syracuseStep 6653249 = 4989937) B4989937
theorem B3941747 : Blo 1750576 3941747 := bstep (se 1 (by rfl) ⟨2956310, by rfl⟩ : syracuseStep 3941747 = 5912621) B5912621
theorem B3941783 : Blo 1750576 3941783 := bstep (se 1 (by rfl) ⟨2956337, by rfl⟩ : syracuseStep 3941783 = 5912675) B5912675
theorem B14960173 : Blo 1750576 14960173 := bstep (se 3 (by rfl) ⟨2805032, by rfl⟩ : syracuseStep 14960173 = 5610065) B5610065
theorem B7480907 : Blo 1750576 7480907 := bstep (se 1 (by rfl) ⟨5610680, by rfl⟩ : syracuseStep 7480907 = 11221361) B11221361
theorem B3941963 : Blo 1750576 3941963 := bstep (se 1 (by rfl) ⟨2956472, by rfl⟩ : syracuseStep 3941963 = 5912945) B5912945
theorem B3942017 : Blo 1750576 3942017 := bstep (se 2 (by rfl) ⟨1478256, by rfl⟩ : syracuseStep 3942017 = 2956513) B2956513
theorem B4990643 : Blo 1750576 4990643 := bstep (se 1 (by rfl) ⟨3742982, by rfl⟩ : syracuseStep 4990643 = 7485965) B7485965
theorem B5908247 : Blo 1750576 5908247 := bstep (se 1 (by rfl) ⟨4431185, by rfl⟩ : syracuseStep 5908247 = 8862371) B8862371
theorem B3155735 : Blo 1750576 3155735 := bstep (se 1 (by rfl) ⟨2366801, by rfl⟩ : syracuseStep 3155735 = 4733603) B4733603
theorem B4433687 : Blo 1750576 4433687 := bstep (se 1 (by rfl) ⟨3325265, by rfl⟩ : syracuseStep 4433687 = 6650531) B6650531
theorem B8865611 : Blo 1750576 8865611 := bstep (se 1 (by rfl) ⟨6649208, by rfl⟩ : syracuseStep 8865611 = 13298417) B13298417
theorem B5326667 : Blo 1750576 5326667 := bstep (se 1 (by rfl) ⟨3995000, by rfl⟩ : syracuseStep 5326667 = 7990001) B7990001
theorem B3942233 : Blo 1750576 3942233 := bstep (se 2 (by rfl) ⟨1478337, by rfl⟩ : syracuseStep 3942233 = 2956675) B2956675
theorem B17065829 : Blo 1750576 17065829 := bstep (se 4 (by rfl) ⟨1599921, by rfl⟩ : syracuseStep 17065829 = 3199843) B3199843
theorem B3942323 : Blo 1750576 3942323 := bstep (se 1 (by rfl) ⟨2956742, by rfl⟩ : syracuseStep 3942323 = 5913485) B5913485
theorem B3942359 : Blo 1750576 3942359 := bstep (se 1 (by rfl) ⟨2956769, by rfl⟩ : syracuseStep 3942359 = 5913539) B5913539
theorem B7202839 : Blo 1750576 7202839 := bstep (se 1 (by rfl) ⟨5402129, by rfl⟩ : syracuseStep 7202839 = 10804259) B10804259
theorem B161835083 : Blo 1750576 161835083 := bstep (se 1 (by rfl) ⟨121376312, by rfl⟩ : syracuseStep 161835083 = 242752625) B242752625
theorem B3942539 : Blo 1750576 3942539 := bstep (se 1 (by rfl) ⟨2956904, by rfl⟩ : syracuseStep 3942539 = 5913809) B5913809
theorem B3942593 : Blo 1750576 3942593 := bstep (se 2 (by rfl) ⟨1478472, by rfl⟩ : syracuseStep 3942593 = 2956945) B2956945
theorem B15976709 : Blo 1750576 15976709 := bstep (se 4 (by rfl) ⟨1497816, by rfl⟩ : syracuseStep 15976709 = 2995633) B2995633
theorem B5908787 : Blo 1750576 5908787 := bstep (se 1 (by rfl) ⟨4431590, by rfl⟩ : syracuseStep 5908787 = 8863181) B8863181
theorem B3942809 : Blo 1750576 3942809 := bstep (se 2 (by rfl) ⟨1478553, by rfl⟩ : syracuseStep 3942809 = 2957107) B2957107
theorem B1870295 : Blo 1750576 1870295 := bstep (se 1 (by rfl) ⟨1402721, by rfl⟩ : syracuseStep 1870295 = 2805443) B2805443
theorem B3942899 : Blo 1750576 3942899 := bstep (se 1 (by rfl) ⟨2957174, by rfl⟩ : syracuseStep 3942899 = 5914349) B5914349
theorem B3942935 : Blo 1750576 3942935 := bstep (se 1 (by rfl) ⟨2957201, by rfl⟩ : syracuseStep 3942935 = 5914403) B5914403
theorem B5909057 : Blo 1750576 5909057 := bstep (se 2 (by rfl) ⟨2215896, by rfl⟩ : syracuseStep 5909057 = 4431793) B4431793
theorem B4434497 : Blo 1750576 4434497 := bstep (se 2 (by rfl) ⟨1662936, by rfl⟩ : syracuseStep 4434497 = 3325873) B3325873
theorem B9972355 : Blo 1750576 9972355 := bstep (se 1 (by rfl) ⟨7479266, by rfl⟩ : syracuseStep 9972355 = 14958533) B14958533
theorem B3943115 : Blo 1750576 3943115 := bstep (se 1 (by rfl) ⟨2957336, by rfl⟩ : syracuseStep 3943115 = 5914673) B5914673
theorem B3369689 : Blo 1750576 3369689 := bstep (se 2 (by rfl) ⟨1263633, by rfl⟩ : syracuseStep 3369689 = 2527267) B2527267
theorem B3943169 : Blo 1750576 3943169 := bstep (se 2 (by rfl) ⟨1478688, by rfl⟩ : syracuseStep 3943169 = 2957377) B2957377
theorem B2493271 : Blo 1750576 2493271 := bstep (se 1 (by rfl) ⟨1869953, by rfl⟩ : syracuseStep 2493271 = 3739907) B3739907
theorem B14961509 : Blo 1750576 14961509 := bstep (se 4 (by rfl) ⟨1402641, by rfl⟩ : syracuseStep 14961509 = 2805283) B2805283
theorem B16198501 : Blo 1750576 16198501 := bstep (se 4 (by rfl) ⟨1518609, by rfl⟩ : syracuseStep 16198501 = 3037219) B3037219
theorem B3845107 : Blo 1750576 3845107 := bstep (se 1 (by rfl) ⟨2883830, by rfl⟩ : syracuseStep 3845107 = 5767661) B5767661
theorem B3157003 : Blo 1750576 3157003 := bstep (se 1 (by rfl) ⟨2367752, by rfl⟩ : syracuseStep 3157003 = 4735505) B4735505
theorem B3992665 : Blo 1750576 3992665 := bstep (se 2 (by rfl) ⟨1497249, by rfl⟩ : syracuseStep 3992665 = 2994499) B2994499
theorem B4435033 : Blo 1750576 4435033 := bstep (se 2 (by rfl) ⟨1663137, by rfl⟩ : syracuseStep 4435033 = 3326275) B3326275
theorem B5909597 : Blo 1750576 5909597 := bstep (se 3 (by rfl) ⟨1108049, by rfl⟩ : syracuseStep 5909597 = 2216099) B2216099
theorem B7482547 : Blo 1750576 7482547 := bstep (se 1 (by rfl) ⟨5611910, by rfl⟩ : syracuseStep 7482547 = 11223821) B11223821
theorem B1969483 : Blo 1750576 1969483 := bstep (se 1 (by rfl) ⟨1477112, by rfl⟩ : syracuseStep 1969483 = 2954225) B2954225
theorem B6647129 : Blo 1750576 6647129 := bstep (se 2 (by rfl) ⟨2492673, by rfl⟩ : syracuseStep 6647129 = 4985347) B4985347
theorem B1969591 : Blo 1750576 1969591 := bstep (se 1 (by rfl) ⟨1477193, by rfl⟩ : syracuseStep 1969591 = 2954387) B2954387
theorem B3370457 : Blo 1750576 3370457 := bstep (se 2 (by rfl) ⟨1263921, by rfl⟩ : syracuseStep 3370457 = 2527843) B2527843
theorem B9973313 : Blo 1750576 9973313 := bstep (se 2 (by rfl) ⟨3739992, by rfl⟩ : syracuseStep 9973313 = 7479985) B7479985
theorem B8867393 : Blo 1750576 8867393 := bstep (se 2 (by rfl) ⟨3325272, by rfl⟩ : syracuseStep 8867393 = 6650545) B6650545
theorem B1969771 : Blo 1750576 1969771 := bstep (se 1 (by rfl) ⟨1477328, by rfl⟩ : syracuseStep 1969771 = 2954657) B2954657
theorem B6647447 : Blo 1750576 6647447 := bstep (se 1 (by rfl) ⟨4985585, by rfl⟩ : syracuseStep 6647447 = 9971171) B9971171
theorem B1969879 : Blo 1750576 1969879 := bstep (se 1 (by rfl) ⟨1477409, by rfl⟩ : syracuseStep 1969879 = 2954819) B2954819
theorem B6311773 : Blo 1750576 6311773 := bstep (se 3 (by rfl) ⟨1183457, by rfl⟩ : syracuseStep 6311773 = 2366915) B2366915
theorem B21303157 : Blo 1750576 21303157 := bstep (se 5 (by rfl) ⟨998585, by rfl⟩ : syracuseStep 21303157 = 1997171) B1997171
theorem B1970059 : Blo 1750576 1970059 := bstep (se 1 (by rfl) ⟨1477544, by rfl⟩ : syracuseStep 1970059 = 2955089) B2955089
theorem B2215831 : Blo 1750576 2215831 := bstep (se 1 (by rfl) ⟨1661873, by rfl⟩ : syracuseStep 2215831 = 3323747) B3323747
theorem B1970167 : Blo 1750576 1970167 := bstep (se 1 (by rfl) ⟨1477625, by rfl⟩ : syracuseStep 1970167 = 2955251) B2955251
theorem B3551321 : Blo 1750576 3551321 := bstep (se 2 (by rfl) ⟨1331745, by rfl⟩ : syracuseStep 3551321 = 2663491) B2663491
theorem B3739763 : Blo 1750576 3739763 := bstep (se 1 (by rfl) ⟨2804822, by rfl⟩ : syracuseStep 3739763 = 5609645) B5609645
theorem B1970347 : Blo 1750576 1970347 := bstep (se 1 (by rfl) ⟨1477760, by rfl⟩ : syracuseStep 1970347 = 2955521) B2955521
theorem B11980979 : Blo 1750576 11980979 := bstep (se 1 (by rfl) ⟨8985734, by rfl⟩ : syracuseStep 11980979 = 17971469) B17971469
theorem B3551411 : Blo 1750576 3551411 := bstep (se 1 (by rfl) ⟨2663558, by rfl⟩ : syracuseStep 3551411 = 5327117) B5327117
theorem B4436147 : Blo 1750576 4436147 := bstep (se 1 (by rfl) ⟨3327110, by rfl⟩ : syracuseStep 4436147 = 6654221) B6654221
theorem B6738113 : Blo 1750576 6738113 := bstep (se 2 (by rfl) ⟨2526792, by rfl⟩ : syracuseStep 6738113 = 5053585) B5053585
theorem B5910731 : Blo 1750576 5910731 := bstep (se 1 (by rfl) ⟨4433048, by rfl⟩ : syracuseStep 5910731 = 8866097) B8866097
theorem B1970455 : Blo 1750576 1970455 := bstep (se 1 (by rfl) ⟨1477841, by rfl⟩ : syracuseStep 1970455 = 2955683) B2955683
theorem B6648115 : Blo 1750576 6648115 := bstep (se 1 (by rfl) ⟨4986086, by rfl⟩ : syracuseStep 6648115 = 9972173) B9972173
theorem B2625881 : Blo 1750576 2625881 := bstep (se 2 (by rfl) ⟨984705, by rfl⟩ : syracuseStep 2625881 = 1969411) B1969411
theorem B3600793 : Blo 1750576 3600793 := bstep (se 2 (by rfl) ⟨1350297, by rfl⟩ : syracuseStep 3600793 = 2700595) B2700595
theorem B7098797 : Blo 1750576 7098797 := bstep (se 3 (by rfl) ⟨1331024, by rfl⟩ : syracuseStep 7098797 = 2662049) B2662049
theorem B2625995 : Blo 1750576 2625995 := bstep (se 1 (by rfl) ⟨1969496, by rfl⟩ : syracuseStep 2625995 = 3938993) B3938993
theorem B1970635 : Blo 1750576 1970635 := bstep (se 1 (by rfl) ⟨1477976, by rfl⟩ : syracuseStep 1970635 = 2955953) B2955953
theorem B2626007 : Blo 1750576 2626007 := bstep (se 1 (by rfl) ⟨1969505, by rfl⟩ : syracuseStep 2626007 = 3939011) B3939011
theorem B5911001 : Blo 1750576 5911001 := bstep (se 2 (by rfl) ⟨2216625, by rfl⟩ : syracuseStep 5911001 = 4433251) B4433251
theorem B8417753 : Blo 1750576 8417753 := bstep (se 2 (by rfl) ⟨3156657, by rfl⟩ : syracuseStep 8417753 = 6313315) B6313315
theorem B2626073 : Blo 1750576 2626073 := bstep (se 2 (by rfl) ⟨984777, by rfl⟩ : syracuseStep 2626073 = 1969555) B1969555
theorem B10654253 : Blo 1750576 10654253 := bstep (se 3 (by rfl) ⟨1997672, by rfl⟩ : syracuseStep 10654253 = 3995345) B3995345
theorem B11227693 : Blo 1750576 11227693 := bstep (se 3 (by rfl) ⟨2105192, by rfl⟩ : syracuseStep 11227693 = 4210385) B4210385
theorem B1970743 : Blo 1750576 1970743 := bstep (se 1 (by rfl) ⟨1478057, by rfl⟩ : syracuseStep 1970743 = 2956115) B2956115
theorem B3740249 : Blo 1750576 3740249 := bstep (se 2 (by rfl) ⟨1402593, by rfl⟩ : syracuseStep 3740249 = 2805187) B2805187
theorem B9466469 : Blo 1750576 9466469 := bstep (se 4 (by rfl) ⟨887481, by rfl⟩ : syracuseStep 9466469 = 1774963) B1774963
theorem B7484035 : Blo 1750576 7484035 := bstep (se 1 (by rfl) ⟨5613026, by rfl⟩ : syracuseStep 7484035 = 11226053) B11226053
theorem B2626187 : Blo 1750576 2626187 := bstep (se 1 (by rfl) ⟨1969640, by rfl⟩ : syracuseStep 2626187 = 3939281) B3939281
theorem B6312593 : Blo 1750576 6312593 := bstep (se 2 (by rfl) ⟨2367222, by rfl⟩ : syracuseStep 6312593 = 4734445) B4734445
theorem B4985495 : Blo 1750576 4985495 := bstep (se 1 (by rfl) ⟨3739121, by rfl⟩ : syracuseStep 4985495 = 7478243) B7478243
theorem B2626199 : Blo 1750576 2626199 := bstep (se 1 (by rfl) ⟨1969649, by rfl⟩ : syracuseStep 2626199 = 3939299) B3939299
theorem B2626265 : Blo 1750576 2626265 := bstep (se 2 (by rfl) ⟨984849, by rfl⟩ : syracuseStep 2626265 = 1969699) B1969699
theorem B1970923 : Blo 1750576 1970923 := bstep (se 1 (by rfl) ⟨1478192, by rfl⟩ : syracuseStep 1970923 = 2956385) B2956385
theorem B7099139 : Blo 1750576 7099139 := bstep (se 1 (by rfl) ⟨5324354, by rfl⟩ : syracuseStep 7099139 = 10648709) B10648709
theorem B2626379 : Blo 1750576 2626379 := bstep (se 1 (by rfl) ⟨1969784, by rfl⟩ : syracuseStep 2626379 = 3939569) B3939569
theorem B2626391 : Blo 1750576 2626391 := bstep (se 1 (by rfl) ⟨1969793, by rfl⟩ : syracuseStep 2626391 = 3939587) B3939587
theorem B1971031 : Blo 1750576 1971031 := bstep (se 1 (by rfl) ⟨1478273, by rfl⟩ : syracuseStep 1971031 = 2956547) B2956547
theorem B4207511 : Blo 1750576 4207511 := bstep (se 1 (by rfl) ⟨3155633, by rfl⟩ : syracuseStep 4207511 = 6311267) B6311267
theorem B2954137 : Blo 1750576 2954137 := bstep (se 2 (by rfl) ⟨1107801, by rfl⟩ : syracuseStep 2954137 = 2215603) B2215603
theorem B2626457 : Blo 1750576 2626457 := bstep (se 2 (by rfl) ⟨984921, by rfl⟩ : syracuseStep 2626457 = 1969843) B1969843
theorem B10793945 : Blo 1750576 10793945 := bstep (se 2 (by rfl) ⟨4047729, by rfl⟩ : syracuseStep 10793945 = 8095459) B8095459
theorem B2626571 : Blo 1750576 2626571 := bstep (se 1 (by rfl) ⟨1969928, by rfl⟩ : syracuseStep 2626571 = 3939857) B3939857
theorem B1971211 : Blo 1750576 1971211 := bstep (se 1 (by rfl) ⟨1478408, by rfl⟩ : syracuseStep 1971211 = 2956817) B2956817
theorem B2626583 : Blo 1750576 2626583 := bstep (se 1 (by rfl) ⟨1969937, by rfl⟩ : syracuseStep 2626583 = 3939875) B3939875
theorem B2626649 : Blo 1750576 2626649 := bstep (se 2 (by rfl) ⟨984993, by rfl⟩ : syracuseStep 2626649 = 1969987) B1969987
theorem B1971319 : Blo 1750576 1971319 := bstep (se 1 (by rfl) ⟨1478489, by rfl⟩ : syracuseStep 1971319 = 2956979) B2956979
theorem B5911703 : Blo 1750576 5911703 := bstep (se 1 (by rfl) ⟨4433777, by rfl⟩ : syracuseStep 5911703 = 8867555) B8867555
theorem B7099595 : Blo 1750576 7099595 := bstep (se 1 (by rfl) ⟨5324696, by rfl⟩ : syracuseStep 7099595 = 10649393) B10649393
theorem B2626763 : Blo 1750576 2626763 := bstep (se 1 (by rfl) ⟨1970072, by rfl⟩ : syracuseStep 2626763 = 3940145) B3940145
theorem B2626775 : Blo 1750576 2626775 := bstep (se 1 (by rfl) ⟨1970081, by rfl⟩ : syracuseStep 2626775 = 3940163) B3940163
theorem B7484633 : Blo 1750576 7484633 := bstep (se 2 (by rfl) ⟨2806737, by rfl⟩ : syracuseStep 7484633 = 5613475) B5613475
theorem B2626841 : Blo 1750576 2626841 := bstep (se 2 (by rfl) ⟨985065, by rfl⟩ : syracuseStep 2626841 = 1970131) B1970131
theorem B1971499 : Blo 1750576 1971499 := bstep (se 1 (by rfl) ⟨1478624, by rfl⟩ : syracuseStep 1971499 = 2957249) B2957249
theorem B2807129 : Blo 1750576 2807129 := bstep (se 2 (by rfl) ⟨1052673, by rfl⟩ : syracuseStep 2807129 = 2105347) B2105347
theorem B16840037 : Blo 1750576 16840037 := bstep (se 4 (by rfl) ⟨1578753, by rfl⟩ : syracuseStep 16840037 = 3157507) B3157507
theorem B2626955 : Blo 1750576 2626955 := bstep (se 1 (by rfl) ⟨1970216, by rfl⟩ : syracuseStep 2626955 = 3940433) B3940433
theorem B2626967 : Blo 1750576 2626967 := bstep (se 1 (by rfl) ⟨1970225, by rfl⟩ : syracuseStep 2626967 = 3940451) B3940451
theorem B1971607 : Blo 1750576 1971607 := bstep (se 1 (by rfl) ⟨1478705, by rfl⟩ : syracuseStep 1971607 = 2957411) B2957411
theorem B7583149 : Blo 1750576 7583149 := bstep (se 3 (by rfl) ⟨1421840, by rfl⟩ : syracuseStep 7583149 = 2843681) B2843681
theorem B2954711 : Blo 1750576 2954711 := bstep (se 1 (by rfl) ⟨2216033, by rfl⟩ : syracuseStep 2954711 = 4432067) B4432067
theorem B2627033 : Blo 1750576 2627033 := bstep (se 2 (by rfl) ⟨985137, by rfl⟩ : syracuseStep 2627033 = 1970275) B1970275
theorem B8869337 : Blo 1750576 8869337 := bstep (se 2 (by rfl) ⟨3326001, by rfl⟩ : syracuseStep 8869337 = 6652003) B6652003
theorem B6649361 : Blo 1750576 6649361 := bstep (se 2 (by rfl) ⟨2493510, by rfl⟩ : syracuseStep 6649361 = 4987021) B4987021
theorem B3323443 : Blo 1750576 3323443 := bstep (se 1 (by rfl) ⟨2492582, by rfl⟩ : syracuseStep 3323443 = 4985165) B4985165
theorem B1750583 : Blo 1750576 1750583 := bstep (se 1 (by rfl) ⟨1312937, by rfl⟩ : syracuseStep 1750583 = 2625875) B2625875
theorem B7484993 : Blo 1750576 7484993 := bstep (se 2 (by rfl) ⟨2806872, by rfl⟩ : syracuseStep 7484993 = 5613745) B5613745
theorem B1750603 : Blo 1750576 1750603 := bstep (se 1 (by rfl) ⟨1312952, by rfl⟩ : syracuseStep 1750603 = 2625905) B2625905
theorem B2627147 : Blo 1750576 2627147 := bstep (se 1 (by rfl) ⟨1970360, by rfl⟩ : syracuseStep 2627147 = 3940721) B3940721
theorem B2217547 : Blo 1750576 2217547 := bstep (se 1 (by rfl) ⟨1663160, by rfl⟩ : syracuseStep 2217547 = 3326321) B3326321
theorem B1750615 : Blo 1750576 1750615 := bstep (se 1 (by rfl) ⟨1312961, by rfl⟩ : syracuseStep 1750615 = 2625923) B2625923
theorem B2954839 : Blo 1750576 2954839 := bstep (se 1 (by rfl) ⟨2216129, by rfl⟩ : syracuseStep 2954839 = 4432259) B4432259
theorem B2627159 : Blo 1750576 2627159 := bstep (se 1 (by rfl) ⟨1970369, by rfl⟩ : syracuseStep 2627159 = 3940739) B3940739
theorem B1750635 : Blo 1750576 1750635 := bstep (se 1 (by rfl) ⟨1312976, by rfl⟩ : syracuseStep 1750635 = 2625953) B2625953
theorem B1750647 : Blo 1750576 1750647 := bstep (se 1 (by rfl) ⟨1312985, by rfl⟩ : syracuseStep 1750647 = 2625971) B2625971
theorem B42604163 : Blo 1750576 42604163 := bstep (se 1 (by rfl) ⟨31953122, by rfl⟩ : syracuseStep 42604163 = 63906245) B63906245
theorem B1750667 : Blo 1750576 1750667 := bstep (se 1 (by rfl) ⟨1313000, by rfl⟩ : syracuseStep 1750667 = 2626001) B2626001
theorem B2561675 : Blo 1750576 2561675 := bstep (se 1 (by rfl) ⟨1921256, by rfl⟩ : syracuseStep 2561675 = 3842513) B3842513
theorem B7583377 : Blo 1750576 7583377 := bstep (se 2 (by rfl) ⟨2843766, by rfl⟩ : syracuseStep 7583377 = 5687533) B5687533
theorem B1750679 : Blo 1750576 1750679 := bstep (se 1 (by rfl) ⟨1313009, by rfl⟩ : syracuseStep 1750679 = 2626019) B2626019
theorem B2627225 : Blo 1750576 2627225 := bstep (se 2 (by rfl) ⟨985209, by rfl⟩ : syracuseStep 2627225 = 1970419) B1970419
theorem B1750699 : Blo 1750576 1750699 := bstep (se 1 (by rfl) ⟨1313024, by rfl⟩ : syracuseStep 1750699 = 2626049) B2626049
theorem B5912243 : Blo 1750576 5912243 := bstep (se 1 (by rfl) ⟨4434182, by rfl⟩ : syracuseStep 5912243 = 8868365) B8868365
theorem B1750711 : Blo 1750576 1750711 := bstep (se 1 (by rfl) ⟨1313033, by rfl⟩ : syracuseStep 1750711 = 2626067) B2626067
theorem B7993025 : Blo 1750576 7993025 := bstep (se 2 (by rfl) ⟨2997384, by rfl⟩ : syracuseStep 7993025 = 5994769) B5994769
theorem B1750731 : Blo 1750576 1750731 := bstep (se 1 (by rfl) ⟨1313048, by rfl⟩ : syracuseStep 1750731 = 2626097) B2626097
theorem B1750743 : Blo 1750576 1750743 := bstep (se 1 (by rfl) ⟨1313057, by rfl⟩ : syracuseStep 1750743 = 2626115) B2626115
theorem B1750763 : Blo 1750576 1750763 := bstep (se 1 (by rfl) ⟨1313072, by rfl⟩ : syracuseStep 1750763 = 2626145) B2626145
theorem B1750775 : Blo 1750576 1750775 := bstep (se 1 (by rfl) ⟨1313081, by rfl⟩ : syracuseStep 1750775 = 2626163) B2626163
theorem B1750795 : Blo 1750576 1750795 := bstep (se 1 (by rfl) ⟨1313096, by rfl⟩ : syracuseStep 1750795 = 2626193) B2626193
theorem B2627339 : Blo 1750576 2627339 := bstep (se 1 (by rfl) ⟨1970504, by rfl⟩ : syracuseStep 2627339 = 3941009) B3941009
theorem B1750807 : Blo 1750576 1750807 := bstep (se 1 (by rfl) ⟨1313105, by rfl⟩ : syracuseStep 1750807 = 2626211) B2626211
theorem B2627351 : Blo 1750576 2627351 := bstep (se 1 (by rfl) ⟨1970513, by rfl⟩ : syracuseStep 2627351 = 3941027) B3941027
theorem B1750827 : Blo 1750576 1750827 := bstep (se 1 (by rfl) ⟨1313120, by rfl⟩ : syracuseStep 1750827 = 2626241) B2626241
theorem B1750839 : Blo 1750576 1750839 := bstep (se 1 (by rfl) ⟨1313129, by rfl⟩ : syracuseStep 1750839 = 2626259) B2626259
theorem B1750859 : Blo 1750576 1750859 := bstep (se 1 (by rfl) ⟨1313144, by rfl⟩ : syracuseStep 1750859 = 2626289) B2626289
theorem B1750871 : Blo 1750576 1750871 := bstep (se 1 (by rfl) ⟨1313153, by rfl⟩ : syracuseStep 1750871 = 2626307) B2626307
theorem B2627417 : Blo 1750576 2627417 := bstep (se 2 (by rfl) ⟨985281, by rfl⟩ : syracuseStep 2627417 = 1970563) B1970563
theorem B1750891 : Blo 1750576 1750891 := bstep (se 1 (by rfl) ⟨1313168, by rfl⟩ : syracuseStep 1750891 = 2626337) B2626337
theorem B1750903 : Blo 1750576 1750903 := bstep (se 1 (by rfl) ⟨1313177, by rfl⟩ : syracuseStep 1750903 = 2626355) B2626355
theorem B1750923 : Blo 1750576 1750923 := bstep (se 1 (by rfl) ⟨1313192, by rfl⟩ : syracuseStep 1750923 = 2626385) B2626385
theorem B1750935 : Blo 1750576 1750935 := bstep (se 1 (by rfl) ⟨1313201, by rfl⟩ : syracuseStep 1750935 = 2626403) B2626403
theorem B1750955 : Blo 1750576 1750955 := bstep (se 1 (by rfl) ⟨1313216, by rfl⟩ : syracuseStep 1750955 = 2626433) B2626433
theorem B1750967 : Blo 1750576 1750967 := bstep (se 1 (by rfl) ⟨1313225, by rfl⟩ : syracuseStep 1750967 = 2626451) B2626451
theorem B5912513 : Blo 1750576 5912513 := bstep (se 2 (by rfl) ⟨2217192, by rfl⟩ : syracuseStep 5912513 = 4434385) B4434385
theorem B1750987 : Blo 1750576 1750987 := bstep (se 1 (by rfl) ⟨1313240, by rfl⟩ : syracuseStep 1750987 = 2626481) B2626481
theorem B1775563 : Blo 1750576 1775563 := bstep (se 1 (by rfl) ⟨1331672, by rfl⟩ : syracuseStep 1775563 = 2663345) B2663345
theorem B2627531 : Blo 1750576 2627531 := bstep (se 1 (by rfl) ⟨1970648, by rfl⟩ : syracuseStep 2627531 = 3941297) B3941297
theorem B1750999 : Blo 1750576 1750999 := bstep (se 1 (by rfl) ⟨1313249, by rfl⟩ : syracuseStep 1750999 = 2626499) B2626499
theorem B2627543 : Blo 1750576 2627543 := bstep (se 1 (by rfl) ⟨1970657, by rfl⟩ : syracuseStep 2627543 = 3941315) B3941315
theorem B1751019 : Blo 1750576 1751019 := bstep (se 1 (by rfl) ⟨1313264, by rfl⟩ : syracuseStep 1751019 = 2626529) B2626529
theorem B3323891 : Blo 1750576 3323891 := bstep (se 1 (by rfl) ⟨2492918, by rfl⟩ : syracuseStep 3323891 = 4985837) B4985837
theorem B1751031 : Blo 1750576 1751031 := bstep (se 1 (by rfl) ⟨1313273, by rfl⟩ : syracuseStep 1751031 = 2626547) B2626547
theorem B1751051 : Blo 1750576 1751051 := bstep (se 1 (by rfl) ⟨1313288, by rfl⟩ : syracuseStep 1751051 = 2626577) B2626577
theorem B1751063 : Blo 1750576 1751063 := bstep (se 1 (by rfl) ⟨1313297, by rfl⟩ : syracuseStep 1751063 = 2626595) B2626595
theorem B3323929 : Blo 1750576 3323929 := bstep (se 2 (by rfl) ⟨1246473, by rfl⟩ : syracuseStep 3323929 = 2492947) B2492947
theorem B2627609 : Blo 1750576 2627609 := bstep (se 2 (by rfl) ⟨985353, by rfl⟩ : syracuseStep 2627609 = 1970707) B1970707
theorem B1751083 : Blo 1750576 1751083 := bstep (se 1 (by rfl) ⟨1313312, by rfl⟩ : syracuseStep 1751083 = 2626625) B2626625
theorem B1751095 : Blo 1750576 1751095 := bstep (se 1 (by rfl) ⟨1313321, by rfl⟩ : syracuseStep 1751095 = 2626643) B2626643
theorem B1751115 : Blo 1750576 1751115 := bstep (se 1 (by rfl) ⟨1313336, by rfl⟩ : syracuseStep 1751115 = 2626673) B2626673
theorem B1751127 : Blo 1750576 1751127 := bstep (se 1 (by rfl) ⟨1313345, by rfl⟩ : syracuseStep 1751127 = 2626691) B2626691
theorem B1751147 : Blo 1750576 1751147 := bstep (se 1 (by rfl) ⟨1313360, by rfl⟩ : syracuseStep 1751147 = 2626721) B2626721
theorem B1751159 : Blo 1750576 1751159 := bstep (se 1 (by rfl) ⟨1313369, by rfl⟩ : syracuseStep 1751159 = 2626739) B2626739
theorem B1751179 : Blo 1750576 1751179 := bstep (se 1 (by rfl) ⟨1313384, by rfl⟩ : syracuseStep 1751179 = 2626769) B2626769
theorem B2627723 : Blo 1750576 2627723 := bstep (se 1 (by rfl) ⟨1970792, by rfl⟩ : syracuseStep 2627723 = 3941585) B3941585
theorem B1751191 : Blo 1750576 1751191 := bstep (se 1 (by rfl) ⟨1313393, by rfl⟩ : syracuseStep 1751191 = 2626787) B2626787
theorem B7100567 : Blo 1750576 7100567 := bstep (se 1 (by rfl) ⟨5325425, by rfl⟩ : syracuseStep 7100567 = 10650851) B10650851
theorem B2627735 : Blo 1750576 2627735 := bstep (se 1 (by rfl) ⟨1970801, by rfl⟩ : syracuseStep 2627735 = 3941603) B3941603
theorem B1751211 : Blo 1750576 1751211 := bstep (se 1 (by rfl) ⟨1313408, by rfl⟩ : syracuseStep 1751211 = 2626817) B2626817
theorem B1751223 : Blo 1750576 1751223 := bstep (se 1 (by rfl) ⟨1313417, by rfl⟩ : syracuseStep 1751223 = 2626835) B2626835
theorem B3741889 : Blo 1750576 3741889 := bstep (se 2 (by rfl) ⟨1403208, by rfl⟩ : syracuseStep 3741889 = 2806417) B2806417
theorem B1751243 : Blo 1750576 1751243 := bstep (se 1 (by rfl) ⟨1313432, by rfl⟩ : syracuseStep 1751243 = 2626865) B2626865
theorem B2955467 : Blo 1750576 2955467 := bstep (se 1 (by rfl) ⟨2216600, by rfl⟩ : syracuseStep 2955467 = 4433201) B4433201
theorem B6650059 : Blo 1750576 6650059 := bstep (se 1 (by rfl) ⟨4987544, by rfl⟩ : syracuseStep 6650059 = 9975089) B9975089
theorem B1751255 : Blo 1750576 1751255 := bstep (se 1 (by rfl) ⟨1313441, by rfl⟩ : syracuseStep 1751255 = 2626883) B2626883
theorem B2627801 : Blo 1750576 2627801 := bstep (se 2 (by rfl) ⟨985425, by rfl⟩ : syracuseStep 2627801 = 1970851) B1970851
theorem B1751275 : Blo 1750576 1751275 := bstep (se 1 (by rfl) ⟨1313456, by rfl⟩ : syracuseStep 1751275 = 2626913) B2626913
theorem B1751287 : Blo 1750576 1751287 := bstep (se 1 (by rfl) ⟨1313465, by rfl⟩ : syracuseStep 1751287 = 2626931) B2626931
theorem B1751307 : Blo 1750576 1751307 := bstep (se 1 (by rfl) ⟨1313480, by rfl⟩ : syracuseStep 1751307 = 2626961) B2626961
theorem B1751319 : Blo 1750576 1751319 := bstep (se 1 (by rfl) ⟨1313489, by rfl⟩ : syracuseStep 1751319 = 2626979) B2626979
theorem B1751339 : Blo 1750576 1751339 := bstep (se 1 (by rfl) ⟨1313504, by rfl⟩ : syracuseStep 1751339 = 2627009) B2627009
theorem B1751351 : Blo 1750576 1751351 := bstep (se 1 (by rfl) ⟨1313513, by rfl⟩ : syracuseStep 1751351 = 2627027) B2627027
theorem B1751371 : Blo 1750576 1751371 := bstep (se 1 (by rfl) ⟨1313528, by rfl⟩ : syracuseStep 1751371 = 2627057) B2627057
theorem B2955595 : Blo 1750576 2955595 := bstep (se 1 (by rfl) ⟨2216696, by rfl⟩ : syracuseStep 2955595 = 4433393) B4433393
theorem B2627915 : Blo 1750576 2627915 := bstep (se 1 (by rfl) ⟨1970936, by rfl⟩ : syracuseStep 2627915 = 3941873) B3941873
theorem B1751383 : Blo 1750576 1751383 := bstep (se 1 (by rfl) ⟨1313537, by rfl⟩ : syracuseStep 1751383 = 2627075) B2627075
theorem B2627927 : Blo 1750576 2627927 := bstep (se 1 (by rfl) ⟨1970945, by rfl⟩ : syracuseStep 2627927 = 3941891) B3941891
theorem B1751403 : Blo 1750576 1751403 := bstep (se 1 (by rfl) ⟨1313552, by rfl⟩ : syracuseStep 1751403 = 2627105) B2627105
theorem B1751415 : Blo 1750576 1751415 := bstep (se 1 (by rfl) ⟨1313561, by rfl⟩ : syracuseStep 1751415 = 2627123) B2627123
theorem B1751435 : Blo 1750576 1751435 := bstep (se 1 (by rfl) ⟨1313576, by rfl⟩ : syracuseStep 1751435 = 2627153) B2627153
theorem B1751447 : Blo 1750576 1751447 := bstep (se 1 (by rfl) ⟨1313585, by rfl⟩ : syracuseStep 1751447 = 2627171) B2627171
theorem B2627993 : Blo 1750576 2627993 := bstep (se 2 (by rfl) ⟨985497, by rfl⟩ : syracuseStep 2627993 = 1970995) B1970995
theorem B1751467 : Blo 1750576 1751467 := bstep (se 1 (by rfl) ⟨1313600, by rfl⟩ : syracuseStep 1751467 = 2627201) B2627201
theorem B1751479 : Blo 1750576 1751479 := bstep (se 1 (by rfl) ⟨1313609, by rfl⟩ : syracuseStep 1751479 = 2627219) B2627219
theorem B1751499 : Blo 1750576 1751499 := bstep (se 1 (by rfl) ⟨1313624, by rfl⟩ : syracuseStep 1751499 = 2627249) B2627249
theorem B1751511 : Blo 1750576 1751511 := bstep (se 1 (by rfl) ⟨1313633, by rfl⟩ : syracuseStep 1751511 = 2627267) B2627267
theorem B3324377 : Blo 1750576 3324377 := bstep (se 2 (by rfl) ⟨1246641, by rfl⟩ : syracuseStep 3324377 = 2493283) B2493283
theorem B2955737 : Blo 1750576 2955737 := bstep (se 2 (by rfl) ⟨1108401, by rfl⟩ : syracuseStep 2955737 = 2216803) B2216803
theorem B6650333 : Blo 1750576 6650333 := bstep (se 3 (by rfl) ⟨1246937, by rfl⟩ : syracuseStep 6650333 = 2493875) B2493875
theorem B5913053 : Blo 1750576 5913053 := bstep (se 3 (by rfl) ⟨1108697, by rfl⟩ : syracuseStep 5913053 = 2217395) B2217395
theorem B1751531 : Blo 1750576 1751531 := bstep (se 1 (by rfl) ⟨1313648, by rfl⟩ : syracuseStep 1751531 = 2627297) B2627297
theorem B1751543 : Blo 1750576 1751543 := bstep (se 1 (by rfl) ⟨1313657, by rfl⟩ : syracuseStep 1751543 = 2627315) B2627315
theorem B1751563 : Blo 1750576 1751563 := bstep (se 1 (by rfl) ⟨1313672, by rfl⟩ : syracuseStep 1751563 = 2627345) B2627345
theorem B2628107 : Blo 1750576 2628107 := bstep (se 1 (by rfl) ⟨1971080, by rfl⟩ : syracuseStep 2628107 = 3942161) B3942161
theorem B1751575 : Blo 1750576 1751575 := bstep (se 1 (by rfl) ⟨1313681, by rfl⟩ : syracuseStep 1751575 = 2627363) B2627363
theorem B2628119 : Blo 1750576 2628119 := bstep (se 1 (by rfl) ⟨1971089, by rfl⟩ : syracuseStep 2628119 = 3942179) B3942179
theorem B1751595 : Blo 1750576 1751595 := bstep (se 1 (by rfl) ⟨1313696, by rfl⟩ : syracuseStep 1751595 = 2627393) B2627393
theorem B3938867 : Blo 1750576 3938867 := bstep (se 1 (by rfl) ⟨2954150, by rfl⟩ : syracuseStep 3938867 = 5908301) B5908301
theorem B1751607 : Blo 1750576 1751607 := bstep (se 1 (by rfl) ⟨1313705, by rfl⟩ : syracuseStep 1751607 = 2627411) B2627411
theorem B7985729 : Blo 1750576 7985729 := bstep (se 2 (by rfl) ⟨2994648, by rfl⟩ : syracuseStep 7985729 = 5989297) B5989297
theorem B1751627 : Blo 1750576 1751627 := bstep (se 1 (by rfl) ⟨1313720, by rfl⟩ : syracuseStep 1751627 = 2627441) B2627441
theorem B3938903 : Blo 1750576 3938903 := bstep (se 1 (by rfl) ⟨2954177, by rfl⟩ : syracuseStep 3938903 = 5908355) B5908355
theorem B1751639 : Blo 1750576 1751639 := bstep (se 1 (by rfl) ⟨1313729, by rfl⟩ : syracuseStep 1751639 = 2627459) B2627459
theorem B2955865 : Blo 1750576 2955865 := bstep (se 2 (by rfl) ⟨1108449, by rfl⟩ : syracuseStep 2955865 = 2216899) B2216899
theorem B4209241 : Blo 1750576 4209241 := bstep (se 2 (by rfl) ⟨1578465, by rfl⟩ : syracuseStep 4209241 = 3156931) B3156931
theorem B2628185 : Blo 1750576 2628185 := bstep (se 2 (by rfl) ⟨985569, by rfl⟩ : syracuseStep 2628185 = 1971139) B1971139
theorem B1751659 : Blo 1750576 1751659 := bstep (se 1 (by rfl) ⟨1313744, by rfl⟩ : syracuseStep 1751659 = 2627489) B2627489
theorem B1751671 : Blo 1750576 1751671 := bstep (se 1 (by rfl) ⟨1313753, by rfl⟩ : syracuseStep 1751671 = 2627507) B2627507
theorem B1751691 : Blo 1750576 1751691 := bstep (se 1 (by rfl) ⟨1313768, by rfl⟩ : syracuseStep 1751691 = 2627537) B2627537
theorem B1751703 : Blo 1750576 1751703 := bstep (se 1 (by rfl) ⟨1313777, by rfl⟩ : syracuseStep 1751703 = 2627555) B2627555
theorem B1751723 : Blo 1750576 1751723 := bstep (se 1 (by rfl) ⟨1313792, by rfl⟩ : syracuseStep 1751723 = 2627585) B2627585
theorem B6314669 : Blo 1750576 6314669 := bstep (se 3 (by rfl) ⟨1184000, by rfl⟩ : syracuseStep 6314669 = 2368001) B2368001
theorem B1751735 : Blo 1750576 1751735 := bstep (se 1 (by rfl) ⟨1313801, by rfl⟩ : syracuseStep 1751735 = 2627603) B2627603
theorem B1751755 : Blo 1750576 1751755 := bstep (se 1 (by rfl) ⟨1313816, by rfl⟩ : syracuseStep 1751755 = 2627633) B2627633
theorem B2628299 : Blo 1750576 2628299 := bstep (se 1 (by rfl) ⟨1971224, by rfl⟩ : syracuseStep 2628299 = 3942449) B3942449
theorem B1997527 : Blo 1750576 1997527 := bstep (se 1 (by rfl) ⟨1498145, by rfl⟩ : syracuseStep 1997527 = 2996291) B2996291
theorem B1751767 : Blo 1750576 1751767 := bstep (se 1 (by rfl) ⟨1313825, by rfl⟩ : syracuseStep 1751767 = 2627651) B2627651
theorem B2628311 : Blo 1750576 2628311 := bstep (se 1 (by rfl) ⟨1971233, by rfl⟩ : syracuseStep 2628311 = 3942467) B3942467
theorem B1751787 : Blo 1750576 1751787 := bstep (se 1 (by rfl) ⟨1313840, by rfl⟩ : syracuseStep 1751787 = 2627681) B2627681
theorem B1751799 : Blo 1750576 1751799 := bstep (se 1 (by rfl) ⟨1313849, by rfl⟩ : syracuseStep 1751799 = 2627699) B2627699
theorem B3939083 : Blo 1750576 3939083 := bstep (se 1 (by rfl) ⟨2954312, by rfl⟩ : syracuseStep 3939083 = 5908625) B5908625
theorem B1751819 : Blo 1750576 1751819 := bstep (se 1 (by rfl) ⟨1313864, by rfl⟩ : syracuseStep 1751819 = 2627729) B2627729
theorem B1751831 : Blo 1750576 1751831 := bstep (se 1 (by rfl) ⟨1313873, by rfl⟩ : syracuseStep 1751831 = 2627747) B2627747
theorem B2628377 : Blo 1750576 2628377 := bstep (se 2 (by rfl) ⟨985641, by rfl⟩ : syracuseStep 2628377 = 1971283) B1971283
theorem B1751851 : Blo 1750576 1751851 := bstep (se 1 (by rfl) ⟨1313888, by rfl⟩ : syracuseStep 1751851 = 2627777) B2627777
theorem B1751863 : Blo 1750576 1751863 := bstep (se 1 (by rfl) ⟨1313897, by rfl⟩ : syracuseStep 1751863 = 2627795) B2627795
theorem B3939137 : Blo 1750576 3939137 := bstep (se 2 (by rfl) ⟨1477176, by rfl⟩ : syracuseStep 3939137 = 2954353) B2954353
theorem B1751883 : Blo 1750576 1751883 := bstep (se 1 (by rfl) ⟨1313912, by rfl⟩ : syracuseStep 1751883 = 2627825) B2627825
theorem B1751895 : Blo 1750576 1751895 := bstep (se 1 (by rfl) ⟨1313921, by rfl⟩ : syracuseStep 1751895 = 2627843) B2627843
theorem B1751915 : Blo 1750576 1751915 := bstep (se 1 (by rfl) ⟨1313936, by rfl⟩ : syracuseStep 1751915 = 2627873) B2627873
theorem B1751927 : Blo 1750576 1751927 := bstep (se 1 (by rfl) ⟨1313945, by rfl⟩ : syracuseStep 1751927 = 2627891) B2627891
theorem B1751947 : Blo 1750576 1751947 := bstep (se 1 (by rfl) ⟨1313960, by rfl⟩ : syracuseStep 1751947 = 2627921) B2627921
theorem B2628491 : Blo 1750576 2628491 := bstep (se 1 (by rfl) ⟨1971368, by rfl⟩ : syracuseStep 2628491 = 3942737) B3942737
theorem B1751959 : Blo 1750576 1751959 := bstep (se 1 (by rfl) ⟨1313969, by rfl⟩ : syracuseStep 1751959 = 2627939) B2627939
theorem B2628503 : Blo 1750576 2628503 := bstep (se 1 (by rfl) ⟨1971377, by rfl⟩ : syracuseStep 2628503 = 3942755) B3942755
theorem B1751979 : Blo 1750576 1751979 := bstep (se 1 (by rfl) ⟨1313984, by rfl⟩ : syracuseStep 1751979 = 2627969) B2627969
theorem B21298099 : Blo 1750576 21298099 := bstep (se 1 (by rfl) ⟨15973574, by rfl⟩ : syracuseStep 21298099 = 31947149) B31947149
theorem B1751991 : Blo 1750576 1751991 := bstep (se 1 (by rfl) ⟨1313993, by rfl⟩ : syracuseStep 1751991 = 2627987) B2627987
theorem B1752011 : Blo 1750576 1752011 := bstep (se 1 (by rfl) ⟨1314008, by rfl⟩ : syracuseStep 1752011 = 2628017) B2628017
theorem B1752023 : Blo 1750576 1752023 := bstep (se 1 (by rfl) ⟨1314017, by rfl⟩ : syracuseStep 1752023 = 2628035) B2628035
theorem B2628569 : Blo 1750576 2628569 := bstep (se 2 (by rfl) ⟨985713, by rfl⟩ : syracuseStep 2628569 = 1971427) B1971427
theorem B1752043 : Blo 1750576 1752043 := bstep (se 1 (by rfl) ⟨1314032, by rfl⟩ : syracuseStep 1752043 = 2628065) B2628065
theorem B3996659 : Blo 1750576 3996659 := bstep (se 1 (by rfl) ⟨2997494, by rfl⟩ : syracuseStep 3996659 = 5994989) B5994989
theorem B1752055 : Blo 1750576 1752055 := bstep (se 1 (by rfl) ⟨1314041, by rfl⟩ : syracuseStep 1752055 = 2628083) B2628083
theorem B1752075 : Blo 1750576 1752075 := bstep (se 1 (by rfl) ⟨1314056, by rfl⟩ : syracuseStep 1752075 = 2628113) B2628113
theorem B25254929 : Blo 1750576 25254929 := bstep (se 2 (by rfl) ⟨9470598, by rfl⟩ : syracuseStep 25254929 = 18941197) B18941197
theorem B1752087 : Blo 1750576 1752087 := bstep (se 1 (by rfl) ⟨1314065, by rfl⟩ : syracuseStep 1752087 = 2628131) B2628131
theorem B3939353 : Blo 1750576 3939353 := bstep (se 2 (by rfl) ⟨1477257, by rfl⟩ : syracuseStep 3939353 = 2954515) B2954515
theorem B1752107 : Blo 1750576 1752107 := bstep (se 1 (by rfl) ⟨1314080, by rfl⟩ : syracuseStep 1752107 = 2628161) B2628161
theorem B8870957 : Blo 1750576 8870957 := bstep (se 3 (by rfl) ⟨1663304, by rfl⟩ : syracuseStep 8870957 = 3326609) B3326609
theorem B4987955 : Blo 1750576 4987955 := bstep (se 1 (by rfl) ⟨3740966, by rfl⟩ : syracuseStep 4987955 = 7481933) B7481933
theorem B1752119 : Blo 1750576 1752119 := bstep (se 1 (by rfl) ⟨1314089, by rfl⟩ : syracuseStep 1752119 = 2628179) B2628179
theorem B1752139 : Blo 1750576 1752139 := bstep (se 1 (by rfl) ⟨1314104, by rfl⟩ : syracuseStep 1752139 = 2628209) B2628209
theorem B2628683 : Blo 1750576 2628683 := bstep (se 1 (by rfl) ⟨1971512, by rfl⟩ : syracuseStep 2628683 = 3943025) B3943025
theorem B1752151 : Blo 1750576 1752151 := bstep (se 1 (by rfl) ⟨1314113, by rfl⟩ : syracuseStep 1752151 = 2628227) B2628227
theorem B2628695 : Blo 1750576 2628695 := bstep (se 1 (by rfl) ⟨1971521, by rfl⟩ : syracuseStep 2628695 = 3943043) B3943043
theorem B1752171 : Blo 1750576 1752171 := bstep (se 1 (by rfl) ⟨1314128, by rfl⟩ : syracuseStep 1752171 = 2628257) B2628257
theorem B3939443 : Blo 1750576 3939443 := bstep (se 1 (by rfl) ⟨2954582, by rfl⟩ : syracuseStep 3939443 = 5909165) B5909165
theorem B1752183 : Blo 1750576 1752183 := bstep (se 1 (by rfl) ⟨1314137, by rfl⟩ : syracuseStep 1752183 = 2628275) B2628275
theorem B1752203 : Blo 1750576 1752203 := bstep (se 1 (by rfl) ⟨1314152, by rfl⟩ : syracuseStep 1752203 = 2628305) B2628305
theorem B3939479 : Blo 1750576 3939479 := bstep (se 1 (by rfl) ⟨2954609, by rfl⟩ : syracuseStep 3939479 = 5909219) B5909219
theorem B6651031 : Blo 1750576 6651031 := bstep (se 1 (by rfl) ⟨4988273, by rfl⟩ : syracuseStep 6651031 = 9976547) B9976547
theorem B51199127 : Blo 1750576 51199127 := bstep (se 1 (by rfl) ⟨38399345, by rfl⟩ : syracuseStep 51199127 = 76798691) B76798691
theorem B2956439 : Blo 1750576 2956439 := bstep (se 1 (by rfl) ⟨2217329, by rfl⟩ : syracuseStep 2956439 = 4434659) B4434659
theorem B1752215 : Blo 1750576 1752215 := bstep (se 1 (by rfl) ⟨1314161, by rfl⟩ : syracuseStep 1752215 = 2628323) B2628323
theorem B2628761 : Blo 1750576 2628761 := bstep (se 2 (by rfl) ⟨985785, by rfl⟩ : syracuseStep 2628761 = 1971571) B1971571
theorem B1752235 : Blo 1750576 1752235 := bstep (se 1 (by rfl) ⟨1314176, by rfl⟩ : syracuseStep 1752235 = 2628353) B2628353
theorem B9108659 : Blo 1750576 9108659 := bstep (se 1 (by rfl) ⟨6831494, by rfl⟩ : syracuseStep 9108659 = 13662989) B13662989
theorem B1752247 : Blo 1750576 1752247 := bstep (se 1 (by rfl) ⟨1314185, by rfl⟩ : syracuseStep 1752247 = 2628371) B2628371
theorem B3325121 : Blo 1750576 3325121 := bstep (se 2 (by rfl) ⟨1246920, by rfl⟩ : syracuseStep 3325121 = 2493841) B2493841
theorem B4209857 : Blo 1750576 4209857 := bstep (se 2 (by rfl) ⟨1578696, by rfl⟩ : syracuseStep 4209857 = 3157393) B3157393
theorem B1752267 : Blo 1750576 1752267 := bstep (se 1 (by rfl) ⟨1314200, by rfl⟩ : syracuseStep 1752267 = 2628401) B2628401
theorem B1752279 : Blo 1750576 1752279 := bstep (se 1 (by rfl) ⟨1314209, by rfl⟩ : syracuseStep 1752279 = 2628419) B2628419
theorem B1752299 : Blo 1750576 1752299 := bstep (se 1 (by rfl) ⟨1314224, by rfl⟩ : syracuseStep 1752299 = 2628449) B2628449
theorem B1752311 : Blo 1750576 1752311 := bstep (se 1 (by rfl) ⟨1314233, by rfl⟩ : syracuseStep 1752311 = 2628467) B2628467
theorem B12631301 : Blo 1750576 12631301 := bstep (se 4 (by rfl) ⟨1184184, by rfl⟩ : syracuseStep 12631301 = 2368369) B2368369
theorem B1752331 : Blo 1750576 1752331 := bstep (se 1 (by rfl) ⟨1314248, by rfl⟩ : syracuseStep 1752331 = 2628497) B2628497
theorem B2956567 : Blo 1750576 2956567 := bstep (se 1 (by rfl) ⟨2217425, by rfl⟩ : syracuseStep 2956567 = 4434851) B4434851
theorem B1752343 : Blo 1750576 1752343 := bstep (se 1 (by rfl) ⟨1314257, by rfl⟩ : syracuseStep 1752343 = 2628515) B2628515
theorem B1752363 : Blo 1750576 1752363 := bstep (se 1 (by rfl) ⟨1314272, by rfl⟩ : syracuseStep 1752363 = 2628545) B2628545
theorem B1752375 : Blo 1750576 1752375 := bstep (se 1 (by rfl) ⟨1314281, by rfl⟩ : syracuseStep 1752375 = 2628563) B2628563
theorem B3939659 : Blo 1750576 3939659 := bstep (se 1 (by rfl) ⟨2954744, by rfl⟩ : syracuseStep 3939659 = 5909489) B5909489
theorem B1752395 : Blo 1750576 1752395 := bstep (se 1 (by rfl) ⟨1314296, by rfl⟩ : syracuseStep 1752395 = 2628593) B2628593
theorem B1752407 : Blo 1750576 1752407 := bstep (se 1 (by rfl) ⟨1314305, by rfl⟩ : syracuseStep 1752407 = 2628611) B2628611
theorem B1752427 : Blo 1750576 1752427 := bstep (se 1 (by rfl) ⟨1314320, by rfl⟩ : syracuseStep 1752427 = 2628641) B2628641
theorem B1752439 : Blo 1750576 1752439 := bstep (se 1 (by rfl) ⟨1314329, by rfl⟩ : syracuseStep 1752439 = 2628659) B2628659
theorem B3939713 : Blo 1750576 3939713 := bstep (se 2 (by rfl) ⟨1477392, by rfl⟩ : syracuseStep 3939713 = 2954785) B2954785
theorem B1752459 : Blo 1750576 1752459 := bstep (se 1 (by rfl) ⟨1314344, by rfl⟩ : syracuseStep 1752459 = 2628689) B2628689
theorem B1752471 : Blo 1750576 1752471 := bstep (se 1 (by rfl) ⟨1314353, by rfl⟩ : syracuseStep 1752471 = 2628707) B2628707
theorem B1752491 : Blo 1750576 1752491 := bstep (se 1 (by rfl) ⟨1314368, by rfl⟩ : syracuseStep 1752491 = 2628737) B2628737
theorem B1752503 : Blo 1750576 1752503 := bstep (se 1 (by rfl) ⟨1314377, by rfl⟩ : syracuseStep 1752503 = 2628755) B2628755
theorem B4431307 : Blo 1750576 4431307 := bstep (se 1 (by rfl) ⟨3323480, by rfl⟩ : syracuseStep 4431307 = 6646961) B6646961
theorem B3325387 : Blo 1750576 3325387 := bstep (se 1 (by rfl) ⟨2494040, by rfl⟩ : syracuseStep 3325387 = 4988081) B4988081
theorem B1752523 : Blo 1750576 1752523 := bstep (se 1 (by rfl) ⟨1314392, by rfl⟩ : syracuseStep 1752523 = 2628785) B2628785
theorem B1752535 : Blo 1750576 1752535 := bstep (se 1 (by rfl) ⟨1314401, by rfl⟩ : syracuseStep 1752535 = 2628803) B2628803
theorem B11222489 : Blo 1750576 11222489 := bstep (se 2 (by rfl) ⟨4208433, by rfl⟩ : syracuseStep 11222489 = 8416867) B8416867
theorem B1752555 : Blo 1750576 1752555 := bstep (se 1 (by rfl) ⟨1314416, by rfl⟩ : syracuseStep 1752555 = 2628833) B2628833
theorem B1752567 : Blo 1750576 1752567 := bstep (se 1 (by rfl) ⟨1314425, by rfl⟩ : syracuseStep 1752567 = 2628851) B2628851
theorem B5914187 : Blo 1750576 5914187 := bstep (se 1 (by rfl) ⟨4435640, by rfl⟩ : syracuseStep 5914187 = 8871281) B8871281
theorem B4431449 : Blo 1750576 4431449 := bstep (se 2 (by rfl) ⟨1661793, by rfl⟩ : syracuseStep 4431449 = 3323587) B3323587
theorem B3939929 : Blo 1750576 3939929 := bstep (se 2 (by rfl) ⟨1477473, by rfl⟩ : syracuseStep 3939929 = 2954947) B2954947
theorem B1998475 : Blo 1750576 1998475 := bstep (se 1 (by rfl) ⟨1498856, by rfl⟩ : syracuseStep 1998475 = 2997713) B2997713
theorem B3940019 : Blo 1750576 3940019 := bstep (se 1 (by rfl) ⟨2955014, by rfl⟩ : syracuseStep 3940019 = 5910029) B5910029
theorem B4800179 : Blo 1750576 4800179 := bstep (se 1 (by rfl) ⟨3600134, by rfl⟩ : syracuseStep 4800179 = 7200269) B7200269
theorem B3940055 : Blo 1750576 3940055 := bstep (se 1 (by rfl) ⟨2955041, by rfl⟩ : syracuseStep 3940055 = 5910083) B5910083
theorem B8863505 : Blo 1750576 8863505 := bstep (se 2 (by rfl) ⟨3323814, by rfl⟩ : syracuseStep 8863505 = 6647629) B6647629
theorem B6315851 : Blo 1750576 6315851 := bstep (se 1 (by rfl) ⟨4736888, by rfl⟩ : syracuseStep 6315851 = 9473777) B9473777
theorem B5914457 : Blo 1750576 5914457 := bstep (se 2 (by rfl) ⟨2217921, by rfl⟩ : syracuseStep 5914457 = 4435843) B4435843
theorem B3940235 : Blo 1750576 3940235 := bstep (se 1 (by rfl) ⟨2955176, by rfl⟩ : syracuseStep 3940235 = 5910353) B5910353
theorem B3325835 : Blo 1750576 3325835 := bstep (se 1 (by rfl) ⟨2494376, by rfl⟩ : syracuseStep 3325835 = 4988753) B4988753
theorem B2957195 : Blo 1750576 2957195 := bstep (se 1 (by rfl) ⟨2217896, by rfl⟩ : syracuseStep 2957195 = 4435793) B4435793
theorem B6651821 : Blo 1750576 6651821 := bstep (se 3 (by rfl) ⟨1247216, by rfl⟩ : syracuseStep 6651821 = 2494433) B2494433
theorem B8863667 : Blo 1750576 8863667 := bstep (se 1 (by rfl) ⟨6647750, by rfl⟩ : syracuseStep 8863667 = 13295501) B13295501
theorem B3940289 : Blo 1750576 3940289 := bstep (se 2 (by rfl) ⟨1477608, by rfl⟩ : syracuseStep 3940289 = 2955217) B2955217
theorem B4210625 : Blo 1750576 4210625 := bstep (se 2 (by rfl) ⟨1578984, by rfl⟩ : syracuseStep 4210625 = 3157969) B3157969
theorem B4431905 : Blo 1750576 4431905 := bstep (se 2 (by rfl) ⟨1661964, by rfl⟩ : syracuseStep 4431905 = 3323929) B3323929
theorem B7987319 : Blo 1750576 7987319 := bstep (se 1 (by rfl) ⟨5990489, by rfl⟩ : syracuseStep 7987319 = 11980979) B11980979
theorem B2957431 : Blo 1750576 2957431 := bstep (se 1 (by rfl) ⟨2218073, by rfl⟩ : syracuseStep 2957431 = 4436147) B4436147
theorem B3940487 : Blo 1750576 3940487 := bstep (se 1 (by rfl) ⟨2955365, by rfl⟩ : syracuseStep 3940487 = 5910731) B5910731
theorem B9470189 : Blo 1750576 9470189 := bstep (se 3 (by rfl) ⟨1775660, by rfl⟩ : syracuseStep 9470189 = 3551321) B3551321
theorem B4989185 : Blo 1750576 4989185 := bstep (se 2 (by rfl) ⟨1870944, by rfl⟩ : syracuseStep 4989185 = 3741889) B3741889
theorem B33653009 : Blo 1750576 33653009 := bstep (se 2 (by rfl) ⟨12619878, by rfl⟩ : syracuseStep 33653009 = 25239757) B25239757
theorem B3940667 : Blo 1750576 3940667 := bstep (se 1 (by rfl) ⟨2955500, by rfl⟩ : syracuseStep 3940667 = 5911001) B5911001
theorem B5611835 : Blo 1750576 5611835 := bstep (se 1 (by rfl) ⟨4208876, by rfl⟩ : syracuseStep 5611835 = 8417753) B8417753
theorem B7102835 : Blo 1750576 7102835 := bstep (se 1 (by rfl) ⟨5327126, by rfl⟩ : syracuseStep 7102835 = 10654253) B10654253
theorem B6652307 : Blo 1750576 6652307 := bstep (se 1 (by rfl) ⟨4989230, by rfl⟩ : syracuseStep 6652307 = 9978461) B9978461
theorem B8864153 : Blo 1750576 8864153 := bstep (se 2 (by rfl) ⟨3324057, by rfl⟩ : syracuseStep 8864153 = 6648115) B6648115
theorem B3940793 : Blo 1750576 3940793 := bstep (se 2 (by rfl) ⟨1477797, by rfl⟩ : syracuseStep 3940793 = 2955595) B2955595
theorem B13304249 : Blo 1750576 13304249 := bstep (se 2 (by rfl) ⟨4989093, by rfl⟩ : syracuseStep 13304249 = 9978187) B9978187
theorem B24289757 : Blo 1750576 24289757 := bstep (se 3 (by rfl) ⟨4554329, by rfl⟩ : syracuseStep 24289757 = 9108659) B9108659
theorem B9470429 : Blo 1750576 9470429 := bstep (se 3 (by rfl) ⟨1775705, by rfl⟩ : syracuseStep 9470429 = 3551411) B3551411
theorem B9732631 : Blo 1750576 9732631 := bstep (se 1 (by rfl) ⟨7299473, by rfl⟩ : syracuseStep 9732631 = 14598947) B14598947
theorem B10658533 : Blo 1750576 10658533 := bstep (se 4 (by rfl) ⟨999237, by rfl⟩ : syracuseStep 10658533 = 1998475) B1998475
theorem B3941135 : Blo 1750576 3941135 := bstep (se 1 (by rfl) ⟨2955851, by rfl⟩ : syracuseStep 3941135 = 5911703) B5911703
theorem B3941153 : Blo 1750576 3941153 := bstep (se 2 (by rfl) ⟨1477932, by rfl⟩ : syracuseStep 3941153 = 2955865) B2955865
theorem B5612321 : Blo 1750576 5612321 := bstep (se 2 (by rfl) ⟨2104620, by rfl⟩ : syracuseStep 5612321 = 4209241) B4209241
theorem B4989755 : Blo 1750576 4989755 := bstep (se 1 (by rfl) ⟨3742316, by rfl⟩ : syracuseStep 4989755 = 7484633) B7484633
theorem B13296473 : Blo 1750576 13296473 := bstep (se 2 (by rfl) ⟨4986177, by rfl⟩ : syracuseStep 13296473 = 9972355) B9972355
theorem B9978713 : Blo 1750576 9978713 := bstep (se 2 (by rfl) ⟨3742017, by rfl⟩ : syracuseStep 9978713 = 7484035) B7484035
theorem B2663369 : Blo 1750576 2663369 := bstep (se 2 (by rfl) ⟨998763, by rfl⟩ : syracuseStep 2663369 = 1997527) B1997527
theorem B4432907 : Blo 1750576 4432907 := bstep (se 1 (by rfl) ⟨3324680, by rfl⟩ : syracuseStep 4432907 = 6649361) B6649361
theorem B4989995 : Blo 1750576 4989995 := bstep (se 1 (by rfl) ⟨3742496, by rfl⟩ : syracuseStep 4989995 = 7484993) B7484993
theorem B28402775 : Blo 1750576 28402775 := bstep (se 1 (by rfl) ⟨21302081, by rfl⟩ : syracuseStep 28402775 = 42604163) B42604163
theorem B3941495 : Blo 1750576 3941495 := bstep (se 1 (by rfl) ⟨2956121, by rfl⟩ : syracuseStep 3941495 = 5912243) B5912243
theorem B3327095 : Blo 1750576 3327095 := bstep (se 1 (by rfl) ⟨2495321, by rfl⟩ : syracuseStep 3327095 = 4990643) B4990643
theorem B3941675 : Blo 1750576 3941675 := bstep (se 1 (by rfl) ⟨2956256, by rfl⟩ : syracuseStep 3941675 = 5912513) B5912513
theorem B107890055 : Blo 1750576 107890055 := bstep (se 1 (by rfl) ⟨80917541, by rfl⟩ : syracuseStep 107890055 = 161835083) B161835083
theorem B10651139 : Blo 1750576 10651139 := bstep (se 1 (by rfl) ⟨7988354, by rfl⟩ : syracuseStep 10651139 = 15976709) B15976709
theorem B4433555 : Blo 1750576 4433555 := bstep (se 1 (by rfl) ⟨3325166, by rfl⟩ : syracuseStep 4433555 = 6650333) B6650333
theorem B3942035 : Blo 1750576 3942035 := bstep (se 1 (by rfl) ⟨2956526, by rfl⟩ : syracuseStep 3942035 = 5913053) B5913053
theorem B3942089 : Blo 1750576 3942089 := bstep (se 2 (by rfl) ⟨1478283, by rfl⟩ : syracuseStep 3942089 = 2956567) B2956567
theorem B13297445 : Blo 1750576 13297445 := bstep (se 4 (by rfl) ⟨1246635, by rfl⟩ : syracuseStep 13297445 = 2493271) B2493271
theorem B2246459 : Blo 1750576 2246459 := bstep (se 1 (by rfl) ⟨1684844, by rfl⟩ : syracuseStep 2246459 = 3369689) B3369689
theorem B5908409 : Blo 1750576 5908409 := bstep (se 2 (by rfl) ⟨2215653, by rfl⟩ : syracuseStep 5908409 = 4431307) B4431307
theorem B4433849 : Blo 1750576 4433849 := bstep (se 2 (by rfl) ⟨1662693, by rfl⟩ : syracuseStep 4433849 = 3325387) B3325387
theorem B16836619 : Blo 1750576 16836619 := bstep (se 1 (by rfl) ⟨12627464, by rfl⟩ : syracuseStep 16836619 = 25254929) B25254929
theorem B19204229 : Blo 1750576 19204229 := bstep (se 4 (by rfl) ⟨1800396, by rfl⟩ : syracuseStep 19204229 = 3600793) B3600793
theorem B10111169 : Blo 1750576 10111169 := bstep (se 2 (by rfl) ⟨3791688, by rfl⟩ : syracuseStep 10111169 = 7583377) B7583377
theorem B19949813 : Blo 1750576 19949813 := bstep (se 5 (by rfl) ⟨935147, by rfl⟩ : syracuseStep 19949813 = 1870295) B1870295
theorem B2246971 : Blo 1750576 2246971 := bstep (se 1 (by rfl) ⟨1685228, by rfl⟩ : syracuseStep 2246971 = 3370457) B3370457
theorem B7481659 : Blo 1750576 7481659 := bstep (se 1 (by rfl) ⟨5611244, by rfl⟩ : syracuseStep 7481659 = 11222489) B11222489
theorem B3942791 : Blo 1750576 3942791 := bstep (se 1 (by rfl) ⟨2957093, by rfl⟩ : syracuseStep 3942791 = 5914187) B5914187
theorem B8415697 : Blo 1750576 8415697 := bstep (se 2 (by rfl) ⟨3155886, by rfl⟩ : syracuseStep 8415697 = 6311773) B6311773
theorem B28404209 : Blo 1750576 28404209 := bstep (se 2 (by rfl) ⟨10651578, by rfl⟩ : syracuseStep 28404209 = 21303157) B21303157
theorem B5909003 : Blo 1750576 5909003 := bstep (se 1 (by rfl) ⟨4431752, by rfl⟩ : syracuseStep 5909003 = 8863505) B8863505
theorem B3942971 : Blo 1750576 3942971 := bstep (se 1 (by rfl) ⟨2957228, by rfl⟩ : syracuseStep 3942971 = 5914457) B5914457
theorem B4434547 : Blo 1750576 4434547 := bstep (se 1 (by rfl) ⟨3325910, by rfl⟩ : syracuseStep 4434547 = 6651821) B6651821
theorem B5909111 : Blo 1750576 5909111 := bstep (se 1 (by rfl) ⟨4431833, by rfl⟩ : syracuseStep 5909111 = 8863667) B8863667
theorem B3943097 : Blo 1750576 3943097 := bstep (se 2 (by rfl) ⟨1478661, by rfl⟩ : syracuseStep 3943097 = 2957323) B2957323
theorem B9603785 : Blo 1750576 9603785 := bstep (se 2 (by rfl) ⟨3601419, by rfl⟩ : syracuseStep 9603785 = 7202839) B7202839
theorem B2493175 : Blo 1750576 2493175 := bstep (se 1 (by rfl) ⟨1869881, by rfl⟩ : syracuseStep 2493175 = 3739763) B3739763
theorem B4434689 : Blo 1750576 4434689 := bstep (se 2 (by rfl) ⟨1663008, by rfl⟩ : syracuseStep 4434689 = 3326017) B3326017
theorem B8866745 : Blo 1750576 8866745 := bstep (se 2 (by rfl) ⟨3325029, by rfl⟩ : syracuseStep 8866745 = 6650059) B6650059
theorem B14969879 : Blo 1750576 14969879 := bstep (se 1 (by rfl) ⟨11227409, by rfl⟩ : syracuseStep 14969879 = 22454819) B22454819
theorem B2493499 : Blo 1750576 2493499 := bstep (se 1 (by rfl) ⟨1870124, by rfl⟩ : syracuseStep 2493499 = 3740249) B3740249
theorem B6310979 : Blo 1750576 6310979 := bstep (se 1 (by rfl) ⟨4733234, by rfl⟩ : syracuseStep 6310979 = 9466469) B9466469
theorem B17968301 : Blo 1750576 17968301 := bstep (se 3 (by rfl) ⟨3369056, by rfl⟩ : syracuseStep 17968301 = 6738113) B6738113
theorem B5909705 : Blo 1750576 5909705 := bstep (se 2 (by rfl) ⟨2216139, by rfl⟩ : syracuseStep 5909705 = 4432279) B4432279
theorem B4435145 : Blo 1750576 4435145 := bstep (se 2 (by rfl) ⟨1663179, by rfl⟩ : syracuseStep 4435145 = 3326359) B3326359
theorem B7195963 : Blo 1750576 7195963 := bstep (se 1 (by rfl) ⟨5396972, by rfl⟩ : syracuseStep 7195963 = 10793945) B10793945
theorem B14970257 : Blo 1750576 14970257 := bstep (se 2 (by rfl) ⟨5613846, by rfl⟩ : syracuseStep 14970257 = 11227693) B11227693
theorem B1895951 : Blo 1750576 1895951 := bstep (se 1 (by rfl) ⟨1421963, by rfl⟩ : syracuseStep 1895951 = 2843927) B2843927
theorem B4435499 : Blo 1750576 4435499 := bstep (se 1 (by rfl) ⟨3326624, by rfl⟩ : syracuseStep 4435499 = 6653249) B6653249
theorem B1871419 : Blo 1750576 1871419 := bstep (se 1 (by rfl) ⟨1403564, by rfl⟩ : syracuseStep 1871419 = 2807129) B2807129
theorem B11226691 : Blo 1750576 11226691 := bstep (se 1 (by rfl) ⟨8420018, by rfl⟩ : syracuseStep 11226691 = 16840037) B16840037
theorem B1969807 : Blo 1750576 1969807 := bstep (se 1 (by rfl) ⟨1477355, by rfl⟩ : syracuseStep 1969807 = 2954711) B2954711
theorem B42602213 : Blo 1750576 42602213 := bstep (se 4 (by rfl) ⟨3993957, by rfl⟩ : syracuseStep 42602213 = 7987915) B7987915
theorem B5328683 : Blo 1750576 5328683 := bstep (se 1 (by rfl) ⟨3996512, by rfl⟩ : syracuseStep 5328683 = 7993025) B7993025
theorem B21598001 : Blo 1750576 21598001 := bstep (se 2 (by rfl) ⟨8099250, by rfl⟩ : syracuseStep 21598001 = 16198501) B16198501
theorem B5910407 : Blo 1750576 5910407 := bstep (se 1 (by rfl) ⟨4432805, by rfl⟩ : syracuseStep 5910407 = 8865611) B8865611
theorem B3551111 : Blo 1750576 3551111 := bstep (se 1 (by rfl) ⟨2663333, by rfl⟩ : syracuseStep 3551111 = 5326667) B5326667
theorem B28397465 : Blo 1750576 28397465 := bstep (se 2 (by rfl) ⟨10649049, by rfl⟩ : syracuseStep 28397465 = 21298099) B21298099
theorem B2215927 : Blo 1750576 2215927 := bstep (se 1 (by rfl) ⟨1661945, by rfl⟩ : syracuseStep 2215927 = 3323891) B3323891
theorem B26980397 : Blo 1750576 26980397 := bstep (se 3 (by rfl) ⟨5058824, by rfl⟩ : syracuseStep 26980397 = 10117649) B10117649
theorem B27324533 : Blo 1750576 27324533 := bstep (se 5 (by rfl) ⟨1280837, by rfl⟩ : syracuseStep 27324533 = 2561675) B2561675
theorem B1970311 : Blo 1750576 1970311 := bstep (se 1 (by rfl) ⟨1477733, by rfl⟩ : syracuseStep 1970311 = 2955467) B2955467
theorem B8868041 : Blo 1750576 8868041 := bstep (se 2 (by rfl) ⟨3325515, by rfl⟩ : syracuseStep 8868041 = 6651031) B6651031
theorem B5910785 : Blo 1750576 5910785 := bstep (se 2 (by rfl) ⟨2216544, by rfl⟩ : syracuseStep 5910785 = 4433089) B4433089
theorem B2216251 : Blo 1750576 2216251 := bstep (se 1 (by rfl) ⟨1662188, by rfl⟩ : syracuseStep 2216251 = 3324377) B3324377
theorem B1970491 : Blo 1750576 1970491 := bstep (se 1 (by rfl) ⟨1477868, by rfl⟩ : syracuseStep 1970491 = 2955737) B2955737
theorem B2625911 : Blo 1750576 2625911 := bstep (se 1 (by rfl) ⟨1969433, by rfl⟩ : syracuseStep 2625911 = 3938867) B3938867
theorem B2625935 : Blo 1750576 2625935 := bstep (se 1 (by rfl) ⟨1969451, by rfl⟩ : syracuseStep 2625935 = 3938903) B3938903
theorem B2625977 : Blo 1750576 2625977 := bstep (se 2 (by rfl) ⟨984741, by rfl⟩ : syracuseStep 2625977 = 1969483) B1969483
theorem B12800477 : Blo 1750576 12800477 := bstep (se 3 (by rfl) ⟨2400089, by rfl⟩ : syracuseStep 12800477 = 4800179) B4800179
theorem B2626055 : Blo 1750576 2626055 := bstep (se 1 (by rfl) ⟨1969541, by rfl⟩ : syracuseStep 2626055 = 3939083) B3939083
theorem B20230685 : Blo 1750576 20230685 := bstep (se 3 (by rfl) ⟨3793253, by rfl⟩ : syracuseStep 20230685 = 7586507) B7586507
theorem B2626091 : Blo 1750576 2626091 := bstep (se 1 (by rfl) ⟨1969568, by rfl⟩ : syracuseStep 2626091 = 3939137) B3939137
theorem B9974339 : Blo 1750576 9974339 := bstep (se 1 (by rfl) ⟨7480754, by rfl⟩ : syracuseStep 9974339 = 14961509) B14961509
theorem B2626121 : Blo 1750576 2626121 := bstep (se 2 (by rfl) ⟨984795, by rfl⟩ : syracuseStep 2626121 = 1969591) B1969591
theorem B2626235 : Blo 1750576 2626235 := bstep (se 1 (by rfl) ⟨1969676, by rfl⟩ : syracuseStep 2626235 = 3939353) B3939353
theorem B2626295 : Blo 1750576 2626295 := bstep (se 1 (by rfl) ⟨1969721, by rfl⟩ : syracuseStep 2626295 = 3939443) B3939443
theorem B2626319 : Blo 1750576 2626319 := bstep (se 1 (by rfl) ⟨1969739, by rfl⟩ : syracuseStep 2626319 = 3939479) B3939479
theorem B34132751 : Blo 1750576 34132751 := bstep (se 1 (by rfl) ⟨25599563, by rfl⟩ : syracuseStep 34132751 = 51199127) B51199127
theorem B1970959 : Blo 1750576 1970959 := bstep (se 1 (by rfl) ⟨1478219, by rfl⟩ : syracuseStep 1970959 = 2956439) B2956439
theorem B2216747 : Blo 1750576 2216747 := bstep (se 1 (by rfl) ⟨1662560, by rfl⟩ : syracuseStep 2216747 = 3325121) B3325121
theorem B2806571 : Blo 1750576 2806571 := bstep (se 1 (by rfl) ⟨2104928, by rfl⟩ : syracuseStep 2806571 = 4209857) B4209857
theorem B2626361 : Blo 1750576 2626361 := bstep (se 2 (by rfl) ⟨984885, by rfl⟩ : syracuseStep 2626361 = 1969771) B1969771
theorem B2626439 : Blo 1750576 2626439 := bstep (se 1 (by rfl) ⟨1969829, by rfl⟩ : syracuseStep 2626439 = 3939659) B3939659
theorem B2626475 : Blo 1750576 2626475 := bstep (se 1 (by rfl) ⟨1969856, by rfl⟩ : syracuseStep 2626475 = 3939713) B3939713
theorem B2626505 : Blo 1750576 2626505 := bstep (se 2 (by rfl) ⟨984939, by rfl⟩ : syracuseStep 2626505 = 1969879) B1969879
theorem B6648875 : Blo 1750576 6648875 := bstep (se 1 (by rfl) ⟨4986656, by rfl⟩ : syracuseStep 6648875 = 9973313) B9973313
theorem B5911595 : Blo 1750576 5911595 := bstep (se 1 (by rfl) ⟨4433696, by rfl⟩ : syracuseStep 5911595 = 8867393) B8867393
theorem B2954299 : Blo 1750576 2954299 := bstep (se 1 (by rfl) ⟨2215724, by rfl⟩ : syracuseStep 2954299 = 4431449) B4431449
theorem B2626619 : Blo 1750576 2626619 := bstep (se 1 (by rfl) ⟨1969964, by rfl⟩ : syracuseStep 2626619 = 3939929) B3939929
theorem B11220029 : Blo 1750576 11220029 := bstep (se 3 (by rfl) ⟨2103755, by rfl⟩ : syracuseStep 11220029 = 4207511) B4207511
theorem B2626679 : Blo 1750576 2626679 := bstep (se 1 (by rfl) ⟨1970009, by rfl⟩ : syracuseStep 2626679 = 3940019) B3940019
theorem B2626703 : Blo 1750576 2626703 := bstep (se 1 (by rfl) ⟨1970027, by rfl⟩ : syracuseStep 2626703 = 3940055) B3940055
theorem B2626745 : Blo 1750576 2626745 := bstep (se 2 (by rfl) ⟨985029, by rfl⟩ : syracuseStep 2626745 = 1970059) B1970059
theorem B2954441 : Blo 1750576 2954441 := bstep (se 2 (by rfl) ⟨1107915, by rfl⟩ : syracuseStep 2954441 = 2215831) B2215831
theorem B2626823 : Blo 1750576 2626823 := bstep (se 1 (by rfl) ⟨1970117, by rfl⟩ : syracuseStep 2626823 = 3940235) B3940235
theorem B2217223 : Blo 1750576 2217223 := bstep (se 1 (by rfl) ⟨1662917, by rfl⟩ : syracuseStep 2217223 = 3325835) B3325835
theorem B1971463 : Blo 1750576 1971463 := bstep (se 1 (by rfl) ⟨1478597, by rfl⟩ : syracuseStep 1971463 = 2957195) B2957195
theorem B2626859 : Blo 1750576 2626859 := bstep (se 1 (by rfl) ⟨1970144, by rfl⟩ : syracuseStep 2626859 = 3940289) B3940289
theorem B2807083 : Blo 1750576 2807083 := bstep (se 1 (by rfl) ⟨2105312, by rfl⟩ : syracuseStep 2807083 = 4210625) B4210625
theorem B2626889 : Blo 1750576 2626889 := bstep (se 2 (by rfl) ⟨985083, by rfl⟩ : syracuseStep 2626889 = 1970167) B1970167
theorem B2627003 : Blo 1750576 2627003 := bstep (se 1 (by rfl) ⟨1970252, by rfl⟩ : syracuseStep 2627003 = 3940505) B3940505
theorem B1971643 : Blo 1750576 1971643 := bstep (se 1 (by rfl) ⟨1478732, by rfl⟩ : syracuseStep 1971643 = 2957465) B2957465
theorem B2627063 : Blo 1750576 2627063 := bstep (se 1 (by rfl) ⟨1970297, by rfl⟩ : syracuseStep 2627063 = 3940595) B3940595
theorem B2627087 : Blo 1750576 2627087 := bstep (se 1 (by rfl) ⟨1970315, by rfl⟩ : syracuseStep 2627087 = 3940631) B3940631
theorem B2627129 : Blo 1750576 2627129 := bstep (se 2 (by rfl) ⟨985173, by rfl⟩ : syracuseStep 2627129 = 1970347) B1970347
theorem B1750587 : Blo 1750576 1750587 := bstep (se 1 (by rfl) ⟨1312940, by rfl⟩ : syracuseStep 1750587 = 2625881) B2625881
theorem B10114679 : Blo 1750576 10114679 := bstep (se 1 (by rfl) ⟨7586009, by rfl⟩ : syracuseStep 10114679 = 15172019) B15172019
theorem B1750663 : Blo 1750576 1750663 := bstep (se 1 (by rfl) ⟨1312997, by rfl⟩ : syracuseStep 1750663 = 2625995) B2625995
theorem B2627207 : Blo 1750576 2627207 := bstep (se 1 (by rfl) ⟨1970405, by rfl⟩ : syracuseStep 2627207 = 3940811) B3940811
theorem B3200647 : Blo 1750576 3200647 := bstep (se 1 (by rfl) ⟨2400485, by rfl⟩ : syracuseStep 3200647 = 4800971) B4800971
theorem B1750671 : Blo 1750576 1750671 := bstep (se 1 (by rfl) ⟨1313003, by rfl⟩ : syracuseStep 1750671 = 2626007) B2626007
theorem B2627243 : Blo 1750576 2627243 := bstep (se 1 (by rfl) ⟨1970432, by rfl⟩ : syracuseStep 2627243 = 3940865) B3940865
theorem B1750715 : Blo 1750576 1750715 := bstep (se 1 (by rfl) ⟨1313036, by rfl⟩ : syracuseStep 1750715 = 2626073) B2626073
theorem B2627273 : Blo 1750576 2627273 := bstep (se 2 (by rfl) ⟨985227, by rfl⟩ : syracuseStep 2627273 = 1970455) B1970455
theorem B2217719 : Blo 1750576 2217719 := bstep (se 1 (by rfl) ⟨1663289, by rfl⟩ : syracuseStep 2217719 = 3326579) B3326579
theorem B1750791 : Blo 1750576 1750791 := bstep (se 1 (by rfl) ⟨1313093, by rfl⟩ : syracuseStep 1750791 = 2626187) B2626187
theorem B3323663 : Blo 1750576 3323663 := bstep (se 1 (by rfl) ⟨2492747, by rfl⟩ : syracuseStep 3323663 = 4985495) B4985495
theorem B1750799 : Blo 1750576 1750799 := bstep (se 1 (by rfl) ⟨1313099, by rfl⟩ : syracuseStep 1750799 = 2626199) B2626199
theorem B1750843 : Blo 1750576 1750843 := bstep (se 1 (by rfl) ⟨1313132, by rfl⟩ : syracuseStep 1750843 = 2626265) B2626265
theorem B2627387 : Blo 1750576 2627387 := bstep (se 1 (by rfl) ⟨1970540, by rfl⟩ : syracuseStep 2627387 = 3941081) B3941081
theorem B4732759 : Blo 1750576 4732759 := bstep (se 1 (by rfl) ⟨3549569, by rfl⟩ : syracuseStep 4732759 = 7099139) B7099139
theorem B33650549 : Blo 1750576 33650549 := bstep (se 5 (by rfl) ⟨1577369, by rfl⟩ : syracuseStep 33650549 = 3154739) B3154739
theorem B2627447 : Blo 1750576 2627447 := bstep (se 1 (by rfl) ⟨1970585, by rfl⟩ : syracuseStep 2627447 = 3941171) B3941171
theorem B1750919 : Blo 1750576 1750919 := bstep (se 1 (by rfl) ⟨1313189, by rfl⟩ : syracuseStep 1750919 = 2626379) B2626379
theorem B2955143 : Blo 1750576 2955143 := bstep (se 1 (by rfl) ⟨2216357, by rfl⟩ : syracuseStep 2955143 = 4432715) B4432715
theorem B1750927 : Blo 1750576 1750927 := bstep (se 1 (by rfl) ⟨1313195, by rfl⟩ : syracuseStep 1750927 = 2626391) B2626391
theorem B2627471 : Blo 1750576 2627471 := bstep (se 1 (by rfl) ⟨1970603, by rfl⟩ : syracuseStep 2627471 = 3941207) B3941207
theorem B2217871 : Blo 1750576 2217871 := bstep (se 1 (by rfl) ⟨1663403, by rfl⟩ : syracuseStep 2217871 = 3326807) B3326807
theorem B2627513 : Blo 1750576 2627513 := bstep (se 2 (by rfl) ⟨985317, by rfl⟩ : syracuseStep 2627513 = 1970635) B1970635
theorem B1750971 : Blo 1750576 1750971 := bstep (se 1 (by rfl) ⟨1313228, by rfl⟩ : syracuseStep 1750971 = 2626457) B2626457
theorem B22763467 : Blo 1750576 22763467 := bstep (se 1 (by rfl) ⟨17072600, by rfl⟩ : syracuseStep 22763467 = 34145201) B34145201
theorem B1751047 : Blo 1750576 1751047 := bstep (se 1 (by rfl) ⟨1313285, by rfl⟩ : syracuseStep 1751047 = 2626571) B2626571
theorem B2627591 : Blo 1750576 2627591 := bstep (se 1 (by rfl) ⟨1970693, by rfl⟩ : syracuseStep 2627591 = 3941387) B3941387
theorem B1751055 : Blo 1750576 1751055 := bstep (se 1 (by rfl) ⟨1313291, by rfl⟩ : syracuseStep 1751055 = 2626583) B2626583
theorem B2627627 : Blo 1750576 2627627 := bstep (se 1 (by rfl) ⟨1970720, by rfl⟩ : syracuseStep 2627627 = 3941441) B3941441
theorem B1751099 : Blo 1750576 1751099 := bstep (se 1 (by rfl) ⟨1313324, by rfl⟩ : syracuseStep 1751099 = 2626649) B2626649
theorem B2218043 : Blo 1750576 2218043 := bstep (se 1 (by rfl) ⟨1663532, by rfl⟩ : syracuseStep 2218043 = 3327065) B3327065
theorem B2627657 : Blo 1750576 2627657 := bstep (se 2 (by rfl) ⟨985371, by rfl⟩ : syracuseStep 2627657 = 1970743) B1970743
theorem B4733063 : Blo 1750576 4733063 := bstep (se 1 (by rfl) ⟨3549797, by rfl⟩ : syracuseStep 4733063 = 7099595) B7099595
theorem B1751175 : Blo 1750576 1751175 := bstep (se 1 (by rfl) ⟨1313381, by rfl⟩ : syracuseStep 1751175 = 2626763) B2626763
theorem B1751183 : Blo 1750576 1751183 := bstep (se 1 (by rfl) ⟨1313387, by rfl⟩ : syracuseStep 1751183 = 2626775) B2626775
theorem B2103467 : Blo 1750576 2103467 := bstep (se 1 (by rfl) ⟨1577600, by rfl⟩ : syracuseStep 2103467 = 3155201) B3155201
theorem B1751227 : Blo 1750576 1751227 := bstep (se 1 (by rfl) ⟨1313420, by rfl⟩ : syracuseStep 1751227 = 2626841) B2626841
theorem B2627771 : Blo 1750576 2627771 := bstep (se 1 (by rfl) ⟨1970828, by rfl⟩ : syracuseStep 2627771 = 3941657) B3941657
theorem B2627831 : Blo 1750576 2627831 := bstep (se 1 (by rfl) ⟨1970873, by rfl⟩ : syracuseStep 2627831 = 3941747) B3941747
theorem B4380929 : Blo 1750576 4380929 := bstep (se 2 (by rfl) ⟨1642848, by rfl⟩ : syracuseStep 4380929 = 3285697) B3285697
theorem B1751303 : Blo 1750576 1751303 := bstep (se 1 (by rfl) ⟨1313477, by rfl⟩ : syracuseStep 1751303 = 2626955) B2626955
theorem B1751311 : Blo 1750576 1751311 := bstep (se 1 (by rfl) ⟨1313483, by rfl⟩ : syracuseStep 1751311 = 2626967) B2626967
theorem B2627855 : Blo 1750576 2627855 := bstep (se 1 (by rfl) ⟨1970891, by rfl⟩ : syracuseStep 2627855 = 3941783) B3941783
theorem B2627897 : Blo 1750576 2627897 := bstep (se 2 (by rfl) ⟨985461, by rfl⟩ : syracuseStep 2627897 = 1970923) B1970923
theorem B1751355 : Blo 1750576 1751355 := bstep (se 1 (by rfl) ⟨1313516, by rfl⟩ : syracuseStep 1751355 = 2627033) B2627033
theorem B5912891 : Blo 1750576 5912891 := bstep (se 1 (by rfl) ⟨4434668, by rfl⟩ : syracuseStep 5912891 = 8869337) B8869337
theorem B4987271 : Blo 1750576 4987271 := bstep (se 1 (by rfl) ⟨3740453, by rfl⟩ : syracuseStep 4987271 = 7480907) B7480907
theorem B1751431 : Blo 1750576 1751431 := bstep (se 1 (by rfl) ⟨1313573, by rfl⟩ : syracuseStep 1751431 = 2627147) B2627147
theorem B2627975 : Blo 1750576 2627975 := bstep (se 1 (by rfl) ⟨1970981, by rfl⟩ : syracuseStep 2627975 = 3941963) B3941963
theorem B1751439 : Blo 1750576 1751439 := bstep (se 1 (by rfl) ⟨1313579, by rfl⟩ : syracuseStep 1751439 = 2627159) B2627159
theorem B2628011 : Blo 1750576 2628011 := bstep (se 1 (by rfl) ⟨1971008, by rfl⟩ : syracuseStep 2628011 = 3942017) B3942017
theorem B1751483 : Blo 1750576 1751483 := bstep (se 1 (by rfl) ⟨1313612, by rfl⟩ : syracuseStep 1751483 = 2627225) B2627225
theorem B2628041 : Blo 1750576 2628041 := bstep (se 2 (by rfl) ⟨985515, by rfl⟩ : syracuseStep 2628041 = 1971031) B1971031
theorem B18930125 : Blo 1750576 18930125 := bstep (se 3 (by rfl) ⟨3549398, by rfl⟩ : syracuseStep 18930125 = 7098797) B7098797
theorem B1751559 : Blo 1750576 1751559 := bstep (se 1 (by rfl) ⟨1313669, by rfl⟩ : syracuseStep 1751559 = 2627339) B2627339
theorem B3938831 : Blo 1750576 3938831 := bstep (se 1 (by rfl) ⟨2954123, by rfl⟩ : syracuseStep 3938831 = 5908247) B5908247
theorem B2103823 : Blo 1750576 2103823 := bstep (se 1 (by rfl) ⟨1577867, by rfl⟩ : syracuseStep 2103823 = 3155735) B3155735
theorem B1751567 : Blo 1750576 1751567 := bstep (se 1 (by rfl) ⟨1313675, by rfl⟩ : syracuseStep 1751567 = 2627351) B2627351
theorem B2955791 : Blo 1750576 2955791 := bstep (se 1 (by rfl) ⟨2216843, by rfl⟩ : syracuseStep 2955791 = 4433687) B4433687
theorem B3938849 : Blo 1750576 3938849 := bstep (se 2 (by rfl) ⟨1477068, by rfl⟩ : syracuseStep 3938849 = 2954137) B2954137
theorem B1751611 : Blo 1750576 1751611 := bstep (se 1 (by rfl) ⟨1313708, by rfl⟩ : syracuseStep 1751611 = 2627417) B2627417
theorem B2628155 : Blo 1750576 2628155 := bstep (se 1 (by rfl) ⟨1971116, by rfl⟩ : syracuseStep 2628155 = 3942233) B3942233
theorem B11377219 : Blo 1750576 11377219 := bstep (se 1 (by rfl) ⟨8532914, by rfl⟩ : syracuseStep 11377219 = 17065829) B17065829
theorem B2628215 : Blo 1750576 2628215 := bstep (se 1 (by rfl) ⟨1971161, by rfl⟩ : syracuseStep 2628215 = 3942323) B3942323
theorem B1751687 : Blo 1750576 1751687 := bstep (se 1 (by rfl) ⟨1313765, by rfl⟩ : syracuseStep 1751687 = 2627531) B2627531
theorem B1751695 : Blo 1750576 1751695 := bstep (se 1 (by rfl) ⟨1313771, by rfl⟩ : syracuseStep 1751695 = 2627543) B2627543
theorem B2628239 : Blo 1750576 2628239 := bstep (se 1 (by rfl) ⟨1971179, by rfl⟩ : syracuseStep 2628239 = 3942359) B3942359
theorem B5126809 : Blo 1750576 5126809 := bstep (se 2 (by rfl) ⟨1922553, by rfl⟩ : syracuseStep 5126809 = 3845107) B3845107
theorem B4209337 : Blo 1750576 4209337 := bstep (se 2 (by rfl) ⟨1578501, by rfl⟩ : syracuseStep 4209337 = 3157003) B3157003
theorem B2628281 : Blo 1750576 2628281 := bstep (se 2 (by rfl) ⟨985605, by rfl⟩ : syracuseStep 2628281 = 1971211) B1971211
theorem B1751739 : Blo 1750576 1751739 := bstep (se 1 (by rfl) ⟨1313804, by rfl⟩ : syracuseStep 1751739 = 2627609) B2627609
theorem B14965505 : Blo 1750576 14965505 := bstep (se 2 (by rfl) ⟨5612064, by rfl⟩ : syracuseStep 14965505 = 11224129) B11224129
theorem B1751815 : Blo 1750576 1751815 := bstep (se 1 (by rfl) ⟨1313861, by rfl⟩ : syracuseStep 1751815 = 2627723) B2627723
theorem B2628359 : Blo 1750576 2628359 := bstep (se 1 (by rfl) ⟨1971269, by rfl⟩ : syracuseStep 2628359 = 3942539) B3942539
theorem B4733711 : Blo 1750576 4733711 := bstep (se 1 (by rfl) ⟨3550283, by rfl⟩ : syracuseStep 4733711 = 7100567) B7100567
theorem B1751823 : Blo 1750576 1751823 := bstep (se 1 (by rfl) ⟨1313867, by rfl⟩ : syracuseStep 1751823 = 2627735) B2627735
theorem B5323553 : Blo 1750576 5323553 := bstep (se 2 (by rfl) ⟨1996332, by rfl⟩ : syracuseStep 5323553 = 3992665) B3992665
theorem B5913377 : Blo 1750576 5913377 := bstep (se 2 (by rfl) ⟨2217516, by rfl⟩ : syracuseStep 5913377 = 4435033) B4435033
theorem B2628395 : Blo 1750576 2628395 := bstep (se 1 (by rfl) ⟨1971296, by rfl⟩ : syracuseStep 2628395 = 3942593) B3942593
theorem B1751867 : Blo 1750576 1751867 := bstep (se 1 (by rfl) ⟨1313900, by rfl⟩ : syracuseStep 1751867 = 2627801) B2627801
theorem B2628425 : Blo 1750576 2628425 := bstep (se 2 (by rfl) ⟨985659, by rfl⟩ : syracuseStep 2628425 = 1971319) B1971319
theorem B3939191 : Blo 1750576 3939191 := bstep (se 1 (by rfl) ⟨2954393, by rfl⟩ : syracuseStep 3939191 = 5908787) B5908787
theorem B1751943 : Blo 1750576 1751943 := bstep (se 1 (by rfl) ⟨1313957, by rfl⟩ : syracuseStep 1751943 = 2627915) B2627915
theorem B1751951 : Blo 1750576 1751951 := bstep (se 1 (by rfl) ⟨1313963, by rfl⟩ : syracuseStep 1751951 = 2627927) B2627927
theorem B9976729 : Blo 1750576 9976729 := bstep (se 2 (by rfl) ⟨3741273, by rfl⟩ : syracuseStep 9976729 = 7482547) B7482547
theorem B1751995 : Blo 1750576 1751995 := bstep (se 1 (by rfl) ⟨1313996, by rfl⟩ : syracuseStep 1751995 = 2627993) B2627993
theorem B2628539 : Blo 1750576 2628539 := bstep (se 1 (by rfl) ⟨1971404, by rfl⟩ : syracuseStep 2628539 = 3942809) B3942809
theorem B2628599 : Blo 1750576 2628599 := bstep (se 1 (by rfl) ⟨1971449, by rfl⟩ : syracuseStep 2628599 = 3942899) B3942899
theorem B1752071 : Blo 1750576 1752071 := bstep (se 1 (by rfl) ⟨1314053, by rfl⟩ : syracuseStep 1752071 = 2628107) B2628107
theorem B1752079 : Blo 1750576 1752079 := bstep (se 1 (by rfl) ⟨1314059, by rfl⟩ : syracuseStep 1752079 = 2628119) B2628119
theorem B2628623 : Blo 1750576 2628623 := bstep (se 1 (by rfl) ⟨1971467, by rfl⟩ : syracuseStep 2628623 = 3942935) B3942935
theorem B5323819 : Blo 1750576 5323819 := bstep (se 1 (by rfl) ⟨3992864, by rfl⟩ : syracuseStep 5323819 = 7985729) B7985729
theorem B3939371 : Blo 1750576 3939371 := bstep (se 1 (by rfl) ⟨2954528, by rfl⟩ : syracuseStep 3939371 = 5909057) B5909057
theorem B16833581 : Blo 1750576 16833581 := bstep (se 3 (by rfl) ⟨3156296, by rfl⟩ : syracuseStep 16833581 = 6312593) B6312593
theorem B2956331 : Blo 1750576 2956331 := bstep (se 1 (by rfl) ⟨2217248, by rfl⟩ : syracuseStep 2956331 = 4434497) B4434497
theorem B2628665 : Blo 1750576 2628665 := bstep (se 2 (by rfl) ⟨985749, by rfl⟩ : syracuseStep 2628665 = 1971499) B1971499
theorem B1752123 : Blo 1750576 1752123 := bstep (se 1 (by rfl) ⟨1314092, by rfl⟩ : syracuseStep 1752123 = 2628185) B2628185
theorem B4209779 : Blo 1750576 4209779 := bstep (se 1 (by rfl) ⟨3157334, by rfl⟩ : syracuseStep 4209779 = 6314669) B6314669
theorem B1752199 : Blo 1750576 1752199 := bstep (se 1 (by rfl) ⟨1314149, by rfl⟩ : syracuseStep 1752199 = 2628299) B2628299
theorem B2628743 : Blo 1750576 2628743 := bstep (se 1 (by rfl) ⟨1971557, by rfl⟩ : syracuseStep 2628743 = 3943115) B3943115
theorem B1752207 : Blo 1750576 1752207 := bstep (se 1 (by rfl) ⟨1314155, by rfl⟩ : syracuseStep 1752207 = 2628311) B2628311
theorem B2628779 : Blo 1750576 2628779 := bstep (se 1 (by rfl) ⟨1971584, by rfl⟩ : syracuseStep 2628779 = 3943169) B3943169
theorem B1752251 : Blo 1750576 1752251 := bstep (se 1 (by rfl) ⟨1314188, by rfl⟩ : syracuseStep 1752251 = 2628377) B2628377
theorem B2628809 : Blo 1750576 2628809 := bstep (se 2 (by rfl) ⟨985803, by rfl⟩ : syracuseStep 2628809 = 1971607) B1971607
theorem B1752327 : Blo 1750576 1752327 := bstep (se 1 (by rfl) ⟨1314245, by rfl⟩ : syracuseStep 1752327 = 2628491) B2628491
theorem B1752335 : Blo 1750576 1752335 := bstep (se 1 (by rfl) ⟨1314251, by rfl⟩ : syracuseStep 1752335 = 2628503) B2628503
theorem B1752379 : Blo 1750576 1752379 := bstep (se 1 (by rfl) ⟨1314284, by rfl⟩ : syracuseStep 1752379 = 2628569) B2628569
theorem B5913971 : Blo 1750576 5913971 := bstep (se 1 (by rfl) ⟨4435478, by rfl⟩ : syracuseStep 5913971 = 8870957) B8870957
theorem B3325303 : Blo 1750576 3325303 := bstep (se 1 (by rfl) ⟨2493977, by rfl⟩ : syracuseStep 3325303 = 4987955) B4987955
theorem B1752455 : Blo 1750576 1752455 := bstep (se 1 (by rfl) ⟨1314341, by rfl⟩ : syracuseStep 1752455 = 2628683) B2628683
theorem B1752463 : Blo 1750576 1752463 := bstep (se 1 (by rfl) ⟨1314347, by rfl⟩ : syracuseStep 1752463 = 2628695) B2628695
theorem B19946897 : Blo 1750576 19946897 := bstep (se 2 (by rfl) ⟨7480086, by rfl⟩ : syracuseStep 19946897 = 14960173) B14960173
theorem B3939731 : Blo 1750576 3939731 := bstep (se 1 (by rfl) ⟨2954798, by rfl⟩ : syracuseStep 3939731 = 5909597) B5909597
theorem B4431257 : Blo 1750576 4431257 := bstep (se 2 (by rfl) ⟨1661721, by rfl⟩ : syracuseStep 4431257 = 3323443) B3323443
theorem B2956729 : Blo 1750576 2956729 := bstep (se 2 (by rfl) ⟨1108773, by rfl⟩ : syracuseStep 2956729 = 2217547) B2217547
theorem B1752507 : Blo 1750576 1752507 := bstep (se 1 (by rfl) ⟨1314380, by rfl⟩ : syracuseStep 1752507 = 2628761) B2628761
theorem B3939785 : Blo 1750576 3939785 := bstep (se 2 (by rfl) ⟨1477419, by rfl⟩ : syracuseStep 3939785 = 2954839) B2954839
theorem B8420867 : Blo 1750576 8420867 := bstep (se 1 (by rfl) ⟨6315650, by rfl⟩ : syracuseStep 8420867 = 12631301) B12631301
theorem B16842269 : Blo 1750576 16842269 := bstep (se 3 (by rfl) ⟨3157925, by rfl⟩ : syracuseStep 16842269 = 6315851) B6315851
theorem B4431419 : Blo 1750576 4431419 := bstep (se 1 (by rfl) ⟨3323564, by rfl⟩ : syracuseStep 4431419 = 6647129) B6647129
theorem B40443461 : Blo 1750576 40443461 := bstep (se 4 (by rfl) ⟨3791574, by rfl⟩ : syracuseStep 40443461 = 7583149) B7583149
theorem B9469669 : Blo 1750576 9469669 := bstep (se 4 (by rfl) ⟨887781, by rfl⟩ : syracuseStep 9469669 = 1775563) B1775563
theorem B4431631 : Blo 1750576 4431631 := bstep (se 1 (by rfl) ⟨3323723, by rfl⟩ : syracuseStep 4431631 = 6647447) B6647447
theorem B10657757 : Blo 1750576 10657757 := bstep (se 3 (by rfl) ⟨1998329, by rfl⟩ : syracuseStep 10657757 = 3996659) B3996659
theorem B5324879 : Blo 1750576 5324879 := bstep (se 1 (by rfl) ⟨3993659, by rfl⟩ : syracuseStep 5324879 = 7987319) B7987319
theorem B5914781 : Blo 1750576 5914781 := bstep (se 3 (by rfl) ⟨1109021, by rfl⟩ : syracuseStep 5914781 = 2218043) B2218043
theorem B3940523 : Blo 1750576 3940523 := bstep (se 1 (by rfl) ⟨2955392, by rfl⟩ : syracuseStep 3940523 = 5910785) B5910785
theorem B3326123 : Blo 1750576 3326123 := bstep (se 1 (by rfl) ⟨2494592, by rfl⟩ : syracuseStep 3326123 = 4989185) B4989185
theorem B4735223 : Blo 1750576 4735223 := bstep (se 1 (by rfl) ⟨3551417, by rfl⟩ : syracuseStep 4735223 = 7102835) B7102835
theorem B8872253 : Blo 1750576 8872253 := bstep (se 3 (by rfl) ⟨1663547, by rfl⟩ : syracuseStep 8872253 = 3327095) B3327095
theorem B3326503 : Blo 1750576 3326503 := bstep (se 1 (by rfl) ⟨2494877, by rfl⟩ : syracuseStep 3326503 = 4989755) B4989755
theorem B8864315 : Blo 1750576 8864315 := bstep (se 1 (by rfl) ⟨6648236, by rfl⟩ : syracuseStep 8864315 = 13296473) B13296473
theorem B6652475 : Blo 1750576 6652475 := bstep (se 1 (by rfl) ⟨4989356, by rfl⟩ : syracuseStep 6652475 = 9978713) B9978713
theorem B23962229 : Blo 1750576 23962229 := bstep (se 5 (by rfl) ⟨1123229, by rfl⟩ : syracuseStep 23962229 = 2246459) B2246459
theorem B4432583 : Blo 1750576 4432583 := bstep (se 1 (by rfl) ⟨3324437, by rfl⟩ : syracuseStep 4432583 = 6648875) B6648875
theorem B3941063 : Blo 1750576 3941063 := bstep (se 1 (by rfl) ⟨2955797, by rfl⟩ : syracuseStep 3941063 = 5911595) B5911595
theorem B12976841 : Blo 1750576 12976841 := bstep (se 2 (by rfl) ⟨4866315, by rfl⟩ : syracuseStep 12976841 = 9732631) B9732631
theorem B3326663 : Blo 1750576 3326663 := bstep (se 1 (by rfl) ⟨2494997, by rfl⟩ : syracuseStep 3326663 = 4989995) B4989995
theorem B7480019 : Blo 1750576 7480019 := bstep (se 1 (by rfl) ⟨5610014, by rfl⟩ : syracuseStep 7480019 = 11220029) B11220029
theorem B71926703 : Blo 1750576 71926703 := bstep (se 1 (by rfl) ⟨53945027, by rfl⟩ : syracuseStep 71926703 = 107890055) B107890055
theorem B8864963 : Blo 1750576 8864963 := bstep (se 1 (by rfl) ⟨6648722, by rfl⟩ : syracuseStep 8864963 = 13297445) B13297445
theorem B50480333 : Blo 1750576 50480333 := bstep (se 3 (by rfl) ⟨9465062, by rfl⟩ : syracuseStep 50480333 = 18930125) B18930125
theorem B5055869 : Blo 1750576 5055869 := bstep (se 3 (by rfl) ⟨947975, by rfl⟩ : syracuseStep 5055869 = 1895951) B1895951
theorem B3155375 : Blo 1750576 3155375 := bstep (se 1 (by rfl) ⟨2366531, by rfl⟩ : syracuseStep 3155375 = 4733063) B4733063
theorem B3941927 : Blo 1750576 3941927 := bstep (se 1 (by rfl) ⟨2956445, by rfl⟩ : syracuseStep 3941927 = 5912891) B5912891
theorem B9594617 : Blo 1750576 9594617 := bstep (se 2 (by rfl) ⟨3597981, by rfl⟩ : syracuseStep 9594617 = 7195963) B7195963
theorem B4433737 : Blo 1750576 4433737 := bstep (se 2 (by rfl) ⟨1662651, by rfl⟩ : syracuseStep 4433737 = 3325303) B3325303
theorem B3155807 : Blo 1750576 3155807 := bstep (se 1 (by rfl) ⟨2366855, by rfl⟩ : syracuseStep 3155807 = 4733711) B4733711
theorem B3549035 : Blo 1750576 3549035 := bstep (se 1 (by rfl) ⟨2661776, by rfl⟩ : syracuseStep 3549035 = 5323553) B5323553
theorem B3942251 : Blo 1750576 3942251 := bstep (se 1 (by rfl) ⟨2956688, by rfl⟩ : syracuseStep 3942251 = 5913377) B5913377
theorem B3942305 : Blo 1750576 3942305 := bstep (se 2 (by rfl) ⟨1478364, by rfl⟩ : syracuseStep 3942305 = 2956729) B2956729
theorem B9979919 : Blo 1750576 9979919 := bstep (se 1 (by rfl) ⟨7484939, by rfl⟩ : syracuseStep 9979919 = 14969879) B14969879
theorem B14968921 : Blo 1750576 14968921 := bstep (se 2 (by rfl) ⟨5613345, by rfl⟩ : syracuseStep 14968921 = 11226691) B11226691
theorem B11978867 : Blo 1750576 11978867 := bstep (se 1 (by rfl) ⟨8984150, by rfl⟩ : syracuseStep 11978867 = 17968301) B17968301
theorem B3942647 : Blo 1750576 3942647 := bstep (se 1 (by rfl) ⟨2956985, by rfl⟩ : syracuseStep 3942647 = 5913971) B5913971
theorem B13297931 : Blo 1750576 13297931 := bstep (se 1 (by rfl) ⟨9973448, by rfl⟩ : syracuseStep 13297931 = 19946897) B19946897
theorem B9980171 : Blo 1750576 9980171 := bstep (se 1 (by rfl) ⟨7485128, by rfl⟩ : syracuseStep 9980171 = 14970257) B14970257
theorem B12626225 : Blo 1750576 12626225 := bstep (se 2 (by rfl) ⟨4734834, by rfl⟩ : syracuseStep 12626225 = 9469669) B9469669
theorem B5613911 : Blo 1750576 5613911 := bstep (se 1 (by rfl) ⟨4210433, by rfl⟩ : syracuseStep 5613911 = 8420867) B8420867
theorem B5908841 : Blo 1750576 5908841 := bstep (se 2 (by rfl) ⟨2215815, by rfl⟩ : syracuseStep 5908841 = 4431631) B4431631
theorem B26962307 : Blo 1750576 26962307 := bstep (se 1 (by rfl) ⟨20221730, by rfl⟩ : syracuseStep 26962307 = 40443461) B40443461
theorem B6310345 : Blo 1750576 6310345 := bstep (se 2 (by rfl) ⟨2366379, by rfl⟩ : syracuseStep 6310345 = 4732759) B4732759
theorem B7105171 : Blo 1750576 7105171 := bstep (se 1 (by rfl) ⟨5328878, by rfl⟩ : syracuseStep 7105171 = 10657757) B10657757
theorem B22448825 : Blo 1750576 22448825 := bstep (se 2 (by rfl) ⟨8418309, by rfl⟩ : syracuseStep 22448825 = 16836619) B16836619
theorem B3943241 : Blo 1750576 3943241 := bstep (se 2 (by rfl) ⟨1478715, by rfl⟩ : syracuseStep 3943241 = 2957431) B2957431
theorem B4434871 : Blo 1750576 4434871 := bstep (se 1 (by rfl) ⟨3326153, by rfl⟩ : syracuseStep 4434871 = 6652307) B6652307
theorem B5909435 : Blo 1750576 5909435 := bstep (se 1 (by rfl) ⟨4432076, by rfl⟩ : syracuseStep 5909435 = 8864153) B8864153
theorem B11226077 : Blo 1750576 11226077 := bstep (se 3 (by rfl) ⟨2104889, by rfl⟩ : syracuseStep 11226077 = 4209779) B4209779
theorem B13487123 : Blo 1750576 13487123 := bstep (se 1 (by rfl) ⟨10115342, by rfl⟩ : syracuseStep 13487123 = 20230685) B20230685
theorem B1871047 : Blo 1750576 1871047 := bstep (se 1 (by rfl) ⟨1403285, by rfl⟩ : syracuseStep 1871047 = 2806571) B2806571
theorem B18935183 : Blo 1750576 18935183 := bstep (se 1 (by rfl) ⟨14201387, by rfl⟩ : syracuseStep 18935183 = 28402775) B28402775
theorem B1969627 : Blo 1750576 1969627 := bstep (se 1 (by rfl) ⟨1477220, by rfl⟩ : syracuseStep 1969627 = 2954441) B2954441
theorem B6835745 : Blo 1750576 6835745 := bstep (se 2 (by rfl) ⟨2563404, by rfl⟩ : syracuseStep 6835745 = 5126809) B5126809
theorem B22449797 : Blo 1750576 22449797 := bstep (se 4 (by rfl) ⟨2104668, by rfl⟩ : syracuseStep 22449797 = 4209337) B4209337
theorem B13299389 : Blo 1750576 13299389 := bstep (se 3 (by rfl) ⟨2493635, by rfl⟩ : syracuseStep 13299389 = 4987271) B4987271
theorem B2215775 : Blo 1750576 2215775 := bstep (se 1 (by rfl) ⟨1661831, by rfl⟩ : syracuseStep 2215775 = 3323663) B3323663
theorem B22433699 : Blo 1750576 22433699 := bstep (se 1 (by rfl) ⟨16825274, by rfl⟩ : syracuseStep 22433699 = 33650549) B33650549
theorem B1970095 : Blo 1750576 1970095 := bstep (se 1 (by rfl) ⟨1477571, by rfl⟩ : syracuseStep 1970095 = 2955143) B2955143
theorem B7098425 : Blo 1750576 7098425 := bstep (se 2 (by rfl) ⟨2661909, by rfl⟩ : syracuseStep 7098425 = 5323819) B5323819
theorem B13299875 : Blo 1750576 13299875 := bstep (se 1 (by rfl) ⟨9974906, by rfl⟩ : syracuseStep 13299875 = 19949813) B19949813
theorem B2920619 : Blo 1750576 2920619 := bstep (se 1 (by rfl) ⟨2190464, by rfl⟩ : syracuseStep 2920619 = 4380929) B4380929
theorem B26972477 : Blo 1750576 26972477 := bstep (se 3 (by rfl) ⟨5057339, by rfl⟩ : syracuseStep 26972477 = 10114679) B10114679
theorem B18936139 : Blo 1750576 18936139 := bstep (se 1 (by rfl) ⟨14202104, by rfl⟩ : syracuseStep 18936139 = 28404209) B28404209
theorem B2625887 : Blo 1750576 2625887 := bstep (se 1 (by rfl) ⟨1969415, by rfl⟩ : syracuseStep 2625887 = 3938831) B3938831
theorem B1970527 : Blo 1750576 1970527 := bstep (se 1 (by rfl) ⟨1477895, by rfl⟩ : syracuseStep 1970527 = 2955791) B2955791
theorem B2625899 : Blo 1750576 2625899 := bstep (se 1 (by rfl) ⟨1969424, by rfl⟩ : syracuseStep 2625899 = 3938849) B3938849
theorem B6402523 : Blo 1750576 6402523 := bstep (se 1 (by rfl) ⟨4801892, by rfl⟩ : syracuseStep 6402523 = 9603785) B9603785
theorem B2626127 : Blo 1750576 2626127 := bstep (se 1 (by rfl) ⟨1969595, by rfl⟩ : syracuseStep 2626127 = 3939191) B3939191
theorem B5911163 : Blo 1750576 5911163 := bstep (se 1 (by rfl) ⟨4433372, by rfl⟩ : syracuseStep 5911163 = 8866745) B8866745
theorem B2626247 : Blo 1750576 2626247 := bstep (se 1 (by rfl) ⟨1969685, by rfl⟩ : syracuseStep 2626247 = 3939371) B3939371
theorem B1970887 : Blo 1750576 1970887 := bstep (se 1 (by rfl) ⟨1478165, by rfl⟩ : syracuseStep 1970887 = 2956331) B2956331
theorem B4207319 : Blo 1750576 4207319 := bstep (se 1 (by rfl) ⟨3155489, by rfl⟩ : syracuseStep 4207319 = 6310979) B6310979
theorem B2495225 : Blo 1750576 2495225 := bstep (se 2 (by rfl) ⟨935709, by rfl⟩ : syracuseStep 2495225 = 1871419) B1871419
theorem B5911325 : Blo 1750576 5911325 := bstep (se 3 (by rfl) ⟨1108373, by rfl⟩ : syracuseStep 5911325 = 2216747) B2216747
theorem B2626409 : Blo 1750576 2626409 := bstep (se 2 (by rfl) ⟨984903, by rfl⟩ : syracuseStep 2626409 = 1969807) B1969807
theorem B2626487 : Blo 1750576 2626487 := bstep (se 1 (by rfl) ⟨1969865, by rfl⟩ : syracuseStep 2626487 = 3939731) B3939731
theorem B2954171 : Blo 1750576 2954171 := bstep (se 1 (by rfl) ⟨2215628, by rfl⟩ : syracuseStep 2954171 = 4431257) B4431257
theorem B2626523 : Blo 1750576 2626523 := bstep (se 1 (by rfl) ⟨1969892, by rfl⟩ : syracuseStep 2626523 = 3939785) B3939785
theorem B11228179 : Blo 1750576 11228179 := bstep (se 1 (by rfl) ⟨8421134, by rfl⟩ : syracuseStep 11228179 = 16842269) B16842269
theorem B2954279 : Blo 1750576 2954279 := bstep (se 1 (by rfl) ⟨2215709, by rfl⟩ : syracuseStep 2954279 = 4431419) B4431419
theorem B3552455 : Blo 1750576 3552455 := bstep (se 1 (by rfl) ⟨2664341, by rfl⟩ : syracuseStep 3552455 = 5328683) B5328683
theorem B14398667 : Blo 1750576 14398667 := bstep (se 1 (by rfl) ⟨10799000, by rfl⟩ : syracuseStep 14398667 = 21598001) B21598001
theorem B2954569 : Blo 1750576 2954569 := bstep (se 2 (by rfl) ⟨1107963, by rfl⟩ : syracuseStep 2954569 = 2215927) B2215927
theorem B2954603 : Blo 1750576 2954603 := bstep (se 1 (by rfl) ⟨2215952, by rfl⟩ : syracuseStep 2954603 = 4431905) B4431905
theorem B17986931 : Blo 1750576 17986931 := bstep (se 1 (by rfl) ⟨13490198, by rfl⟩ : syracuseStep 17986931 = 26980397) B26980397
theorem B18216355 : Blo 1750576 18216355 := bstep (se 1 (by rfl) ⟨13662266, by rfl⟩ : syracuseStep 18216355 = 27324533) B27324533
theorem B11220389 : Blo 1750576 11220389 := bstep (se 4 (by rfl) ⟨1051911, by rfl⟩ : syracuseStep 11220389 = 2103823) B2103823
theorem B2626991 : Blo 1750576 2626991 := bstep (se 1 (by rfl) ⟨1970243, by rfl⟩ : syracuseStep 2626991 = 3940487) B3940487
theorem B5912027 : Blo 1750576 5912027 := bstep (se 1 (by rfl) ⟨4434020, by rfl⟩ : syracuseStep 5912027 = 8868041) B8868041
theorem B6313459 : Blo 1750576 6313459 := bstep (se 1 (by rfl) ⟨4735094, by rfl⟩ : syracuseStep 6313459 = 9470189) B9470189
theorem B2627081 : Blo 1750576 2627081 := bstep (se 2 (by rfl) ⟨985155, by rfl⟩ : syracuseStep 2627081 = 1970311) B1970311
theorem B22435339 : Blo 1750576 22435339 := bstep (se 1 (by rfl) ⟨16826504, by rfl⟩ : syracuseStep 22435339 = 33653009) B33653009
theorem B2627111 : Blo 1750576 2627111 := bstep (se 1 (by rfl) ⟨1970333, by rfl⟩ : syracuseStep 2627111 = 3940667) B3940667
theorem B3741223 : Blo 1750576 3741223 := bstep (se 1 (by rfl) ⟨2805917, by rfl⟩ : syracuseStep 3741223 = 5611835) B5611835
theorem B1750607 : Blo 1750576 1750607 := bstep (se 1 (by rfl) ⟨1312955, by rfl⟩ : syracuseStep 1750607 = 2625911) B2625911
theorem B1750623 : Blo 1750576 1750623 := bstep (se 1 (by rfl) ⟨1312967, by rfl⟩ : syracuseStep 1750623 = 2625935) B2625935
theorem B1750651 : Blo 1750576 1750651 := bstep (se 1 (by rfl) ⟨1312988, by rfl⟩ : syracuseStep 1750651 = 2625977) B2625977
theorem B2627195 : Blo 1750576 2627195 := bstep (se 1 (by rfl) ⟨1970396, by rfl⟩ : syracuseStep 2627195 = 3940793) B3940793
theorem B8869499 : Blo 1750576 8869499 := bstep (se 1 (by rfl) ⟨6652124, by rfl⟩ : syracuseStep 8869499 = 13304249) B13304249
theorem B16193171 : Blo 1750576 16193171 := bstep (se 1 (by rfl) ⟨12144878, by rfl⟩ : syracuseStep 16193171 = 24289757) B24289757
theorem B6313619 : Blo 1750576 6313619 := bstep (se 1 (by rfl) ⟨4735214, by rfl⟩ : syracuseStep 6313619 = 9470429) B9470429
theorem B1750703 : Blo 1750576 1750703 := bstep (se 1 (by rfl) ⟨1313027, by rfl⟩ : syracuseStep 1750703 = 2626055) B2626055
theorem B1750727 : Blo 1750576 1750727 := bstep (se 1 (by rfl) ⟨1313045, by rfl⟩ : syracuseStep 1750727 = 2626091) B2626091
theorem B6649559 : Blo 1750576 6649559 := bstep (se 1 (by rfl) ⟨4987169, by rfl⟩ : syracuseStep 6649559 = 9974339) B9974339
theorem B1750747 : Blo 1750576 1750747 := bstep (se 1 (by rfl) ⟨1313060, by rfl⟩ : syracuseStep 1750747 = 2626121) B2626121
theorem B2955001 : Blo 1750576 2955001 := bstep (se 2 (by rfl) ⟨1108125, by rfl⟩ : syracuseStep 2955001 = 2216251) B2216251
theorem B2995961 : Blo 1750576 2995961 := bstep (se 2 (by rfl) ⟨1123485, by rfl⟩ : syracuseStep 2995961 = 2246971) B2246971
theorem B9975545 : Blo 1750576 9975545 := bstep (se 2 (by rfl) ⟨3740829, by rfl⟩ : syracuseStep 9975545 = 7481659) B7481659
theorem B2627321 : Blo 1750576 2627321 := bstep (se 2 (by rfl) ⟨985245, by rfl⟩ : syracuseStep 2627321 = 1970491) B1970491
theorem B5609245 : Blo 1750576 5609245 := bstep (se 3 (by rfl) ⟨1051733, by rfl⟩ : syracuseStep 5609245 = 2103467) B2103467
theorem B1750823 : Blo 1750576 1750823 := bstep (se 1 (by rfl) ⟨1313117, by rfl⟩ : syracuseStep 1750823 = 2626235) B2626235
theorem B1750863 : Blo 1750576 1750863 := bstep (se 1 (by rfl) ⟨1313147, by rfl⟩ : syracuseStep 1750863 = 2626295) B2626295
theorem B1750879 : Blo 1750576 1750879 := bstep (se 1 (by rfl) ⟨1313159, by rfl⟩ : syracuseStep 1750879 = 2626319) B2626319
theorem B2627423 : Blo 1750576 2627423 := bstep (se 1 (by rfl) ⟨1970567, by rfl⟩ : syracuseStep 2627423 = 3941135) B3941135
theorem B22755167 : Blo 1750576 22755167 := bstep (se 1 (by rfl) ⟨17066375, by rfl⟩ : syracuseStep 22755167 = 34132751) B34132751
theorem B2627435 : Blo 1750576 2627435 := bstep (se 1 (by rfl) ⟨1970576, by rfl⟩ : syracuseStep 2627435 = 3941153) B3941153
theorem B3741547 : Blo 1750576 3741547 := bstep (se 1 (by rfl) ⟨2806160, by rfl⟩ : syracuseStep 3741547 = 5612321) B5612321
theorem B1750907 : Blo 1750576 1750907 := bstep (se 1 (by rfl) ⟨1313180, by rfl⟩ : syracuseStep 1750907 = 2626361) B2626361
theorem B1750959 : Blo 1750576 1750959 := bstep (se 1 (by rfl) ⟨1313219, by rfl⟩ : syracuseStep 1750959 = 2626439) B2626439
theorem B11220929 : Blo 1750576 11220929 := bstep (se 2 (by rfl) ⟨4207848, by rfl⟩ : syracuseStep 11220929 = 8415697) B8415697
theorem B1750983 : Blo 1750576 1750983 := bstep (se 1 (by rfl) ⟨1313237, by rfl⟩ : syracuseStep 1750983 = 2626475) B2626475
theorem B1751003 : Blo 1750576 1751003 := bstep (se 1 (by rfl) ⟨1313252, by rfl⟩ : syracuseStep 1751003 = 2626505) B2626505
theorem B1775579 : Blo 1750576 1775579 := bstep (se 1 (by rfl) ⟨1331684, by rfl⟩ : syracuseStep 1775579 = 2663369) B2663369
theorem B2955271 : Blo 1750576 2955271 := bstep (se 1 (by rfl) ⟨2216453, by rfl⟩ : syracuseStep 2955271 = 4432907) B4432907
theorem B1751079 : Blo 1750576 1751079 := bstep (se 1 (by rfl) ⟨1313309, by rfl⟩ : syracuseStep 1751079 = 2626619) B2626619
theorem B1751119 : Blo 1750576 1751119 := bstep (se 1 (by rfl) ⟨1313339, by rfl⟩ : syracuseStep 1751119 = 2626679) B2626679
theorem B2627663 : Blo 1750576 2627663 := bstep (se 1 (by rfl) ⟨1970747, by rfl⟩ : syracuseStep 2627663 = 3941495) B3941495
theorem B15169625 : Blo 1750576 15169625 := bstep (se 2 (by rfl) ⟨5688609, by rfl⟩ : syracuseStep 15169625 = 11377219) B11377219
theorem B1751135 : Blo 1750576 1751135 := bstep (se 1 (by rfl) ⟨1313351, by rfl⟩ : syracuseStep 1751135 = 2626703) B2626703
theorem B1751163 : Blo 1750576 1751163 := bstep (se 1 (by rfl) ⟨1313372, by rfl⟩ : syracuseStep 1751163 = 2626745) B2626745
theorem B5912729 : Blo 1750576 5912729 := bstep (se 2 (by rfl) ⟨2217273, by rfl⟩ : syracuseStep 5912729 = 4434547) B4434547
theorem B1751215 : Blo 1750576 1751215 := bstep (se 1 (by rfl) ⟨1313411, by rfl⟩ : syracuseStep 1751215 = 2626823) B2626823
theorem B1751239 : Blo 1750576 1751239 := bstep (se 1 (by rfl) ⟨1313429, by rfl⟩ : syracuseStep 1751239 = 2626859) B2626859
theorem B2627783 : Blo 1750576 2627783 := bstep (se 1 (by rfl) ⟨1970837, by rfl⟩ : syracuseStep 2627783 = 3941675) B3941675
theorem B1751259 : Blo 1750576 1751259 := bstep (se 1 (by rfl) ⟨1313444, by rfl⟩ : syracuseStep 1751259 = 2626889) B2626889
theorem B1751335 : Blo 1750576 1751335 := bstep (se 1 (by rfl) ⟨1313501, by rfl⟩ : syracuseStep 1751335 = 2627003) B2627003
theorem B14211377 : Blo 1750576 14211377 := bstep (se 2 (by rfl) ⟨5329266, by rfl⟩ : syracuseStep 14211377 = 10658533) B10658533
theorem B3324233 : Blo 1750576 3324233 := bstep (se 2 (by rfl) ⟨1246587, by rfl⟩ : syracuseStep 3324233 = 2493175) B2493175
theorem B1751375 : Blo 1750576 1751375 := bstep (se 1 (by rfl) ⟨1313531, by rfl⟩ : syracuseStep 1751375 = 2627063) B2627063
theorem B7100759 : Blo 1750576 7100759 := bstep (se 1 (by rfl) ⟨5325569, by rfl⟩ : syracuseStep 7100759 = 10651139) B10651139
theorem B1751391 : Blo 1750576 1751391 := bstep (se 1 (by rfl) ⟨1313543, by rfl⟩ : syracuseStep 1751391 = 2627087) B2627087
theorem B2627945 : Blo 1750576 2627945 := bstep (se 2 (by rfl) ⟨985479, by rfl⟩ : syracuseStep 2627945 = 1970959) B1970959
theorem B1751419 : Blo 1750576 1751419 := bstep (se 1 (by rfl) ⟨1313564, by rfl⟩ : syracuseStep 1751419 = 2627129) B2627129
theorem B1751471 : Blo 1750576 1751471 := bstep (se 1 (by rfl) ⟨1313603, by rfl⟩ : syracuseStep 1751471 = 2627207) B2627207
theorem B2955703 : Blo 1750576 2955703 := bstep (se 1 (by rfl) ⟨2216777, by rfl⟩ : syracuseStep 2955703 = 4433555) B4433555
theorem B2628023 : Blo 1750576 2628023 := bstep (se 1 (by rfl) ⟨1971017, by rfl⟩ : syracuseStep 2628023 = 3942035) B3942035
theorem B1751495 : Blo 1750576 1751495 := bstep (se 1 (by rfl) ⟨1313621, by rfl⟩ : syracuseStep 1751495 = 2627243) B2627243
theorem B1751515 : Blo 1750576 1751515 := bstep (se 1 (by rfl) ⟨1313636, by rfl⟩ : syracuseStep 1751515 = 2627273) B2627273
theorem B2628059 : Blo 1750576 2628059 := bstep (se 1 (by rfl) ⟨1971044, by rfl⟩ : syracuseStep 2628059 = 3942089) B3942089
theorem B13302305 : Blo 1750576 13302305 := bstep (se 2 (by rfl) ⟨4988364, by rfl⟩ : syracuseStep 13302305 = 9976729) B9976729
theorem B1751591 : Blo 1750576 1751591 := bstep (se 1 (by rfl) ⟨1313693, by rfl⟩ : syracuseStep 1751591 = 2627387) B2627387
theorem B34134605 : Blo 1750576 34134605 := bstep (se 3 (by rfl) ⟨6400238, by rfl⟩ : syracuseStep 34134605 = 12800477) B12800477
theorem B1751631 : Blo 1750576 1751631 := bstep (se 1 (by rfl) ⟨1313723, by rfl⟩ : syracuseStep 1751631 = 2627447) B2627447
theorem B1751647 : Blo 1750576 1751647 := bstep (se 1 (by rfl) ⟨1313735, by rfl⟩ : syracuseStep 1751647 = 2627471) B2627471
theorem B3938939 : Blo 1750576 3938939 := bstep (se 1 (by rfl) ⟨2954204, by rfl⟩ : syracuseStep 3938939 = 5908409) B5908409
theorem B2955899 : Blo 1750576 2955899 := bstep (se 1 (by rfl) ⟨2216924, by rfl⟩ : syracuseStep 2955899 = 4433849) B4433849
theorem B1751675 : Blo 1750576 1751675 := bstep (se 1 (by rfl) ⟨1313756, by rfl⟩ : syracuseStep 1751675 = 2627513) B2627513
theorem B1751727 : Blo 1750576 1751727 := bstep (se 1 (by rfl) ⟨1313795, by rfl⟩ : syracuseStep 1751727 = 2627591) B2627591
theorem B1751751 : Blo 1750576 1751751 := bstep (se 1 (by rfl) ⟨1313813, by rfl⟩ : syracuseStep 1751751 = 2627627) B2627627
theorem B1751771 : Blo 1750576 1751771 := bstep (se 1 (by rfl) ⟨1313828, by rfl⟩ : syracuseStep 1751771 = 2627657) B2627657
theorem B3939065 : Blo 1750576 3939065 := bstep (se 2 (by rfl) ⟨1477149, by rfl⟩ : syracuseStep 3939065 = 2954299) B2954299
theorem B3324665 : Blo 1750576 3324665 := bstep (se 2 (by rfl) ⟨1246749, by rfl⟩ : syracuseStep 3324665 = 2493499) B2493499
theorem B12802819 : Blo 1750576 12802819 := bstep (se 1 (by rfl) ⟨9602114, by rfl⟩ : syracuseStep 12802819 = 19204229) B19204229
theorem B1751847 : Blo 1750576 1751847 := bstep (se 1 (by rfl) ⟨1313885, by rfl⟩ : syracuseStep 1751847 = 2627771) B2627771
theorem B6740779 : Blo 1750576 6740779 := bstep (se 1 (by rfl) ⟨5055584, by rfl⟩ : syracuseStep 6740779 = 10111169) B10111169
theorem B1751887 : Blo 1750576 1751887 := bstep (se 1 (by rfl) ⟨1313915, by rfl⟩ : syracuseStep 1751887 = 2627831) B2627831
theorem B1751903 : Blo 1750576 1751903 := bstep (se 1 (by rfl) ⟨1313927, by rfl⟩ : syracuseStep 1751903 = 2627855) B2627855
theorem B1751931 : Blo 1750576 1751931 := bstep (se 1 (by rfl) ⟨1313948, by rfl⟩ : syracuseStep 1751931 = 2627897) B2627897
theorem B1751983 : Blo 1750576 1751983 := bstep (se 1 (by rfl) ⟨1313987, by rfl⟩ : syracuseStep 1751983 = 2627975) B2627975
theorem B2628527 : Blo 1750576 2628527 := bstep (se 1 (by rfl) ⟨1971395, by rfl⟩ : syracuseStep 2628527 = 3942791) B3942791
theorem B1752007 : Blo 1750576 1752007 := bstep (se 1 (by rfl) ⟨1314005, by rfl⟩ : syracuseStep 1752007 = 2628011) B2628011
theorem B1752027 : Blo 1750576 1752027 := bstep (se 1 (by rfl) ⟨1314020, by rfl⟩ : syracuseStep 1752027 = 2628041) B2628041
theorem B3939335 : Blo 1750576 3939335 := bstep (se 1 (by rfl) ⟨2954501, by rfl⟩ : syracuseStep 3939335 = 5909003) B5909003
theorem B2956297 : Blo 1750576 2956297 := bstep (se 2 (by rfl) ⟨1108611, by rfl⟩ : syracuseStep 2956297 = 2217223) B2217223
theorem B2628617 : Blo 1750576 2628617 := bstep (se 2 (by rfl) ⟨985731, by rfl⟩ : syracuseStep 2628617 = 1971463) B1971463
theorem B1752103 : Blo 1750576 1752103 := bstep (se 1 (by rfl) ⟨1314077, by rfl⟩ : syracuseStep 1752103 = 2628155) B2628155
theorem B2628647 : Blo 1750576 2628647 := bstep (se 1 (by rfl) ⟨1971485, by rfl⟩ : syracuseStep 2628647 = 3942971) B3942971
theorem B3742777 : Blo 1750576 3742777 := bstep (se 2 (by rfl) ⟨1403541, by rfl⟩ : syracuseStep 3742777 = 2807083) B2807083
theorem B3939407 : Blo 1750576 3939407 := bstep (se 1 (by rfl) ⟨2954555, by rfl⟩ : syracuseStep 3939407 = 5909111) B5909111
theorem B1752143 : Blo 1750576 1752143 := bstep (se 1 (by rfl) ⟨1314107, by rfl⟩ : syracuseStep 1752143 = 2628215) B2628215
theorem B1752159 : Blo 1750576 1752159 := bstep (se 1 (by rfl) ⟨1314119, by rfl⟩ : syracuseStep 1752159 = 2628239) B2628239
theorem B1752187 : Blo 1750576 1752187 := bstep (se 1 (by rfl) ⟨1314140, by rfl⟩ : syracuseStep 1752187 = 2628281) B2628281
theorem B2628731 : Blo 1750576 2628731 := bstep (se 1 (by rfl) ⟨1971548, by rfl⟩ : syracuseStep 2628731 = 3943097) B3943097
theorem B9977003 : Blo 1750576 9977003 := bstep (se 1 (by rfl) ⟨7482752, by rfl⟩ : syracuseStep 9977003 = 14965505) B14965505
theorem B2956459 : Blo 1750576 2956459 := bstep (se 1 (by rfl) ⟨2217344, by rfl⟩ : syracuseStep 2956459 = 4434689) B4434689
theorem B1752239 : Blo 1750576 1752239 := bstep (se 1 (by rfl) ⟨1314179, by rfl⟩ : syracuseStep 1752239 = 2628359) B2628359
theorem B1752263 : Blo 1750576 1752263 := bstep (se 1 (by rfl) ⟨1314197, by rfl⟩ : syracuseStep 1752263 = 2628395) B2628395
theorem B1752283 : Blo 1750576 1752283 := bstep (se 1 (by rfl) ⟨1314212, by rfl⟩ : syracuseStep 1752283 = 2628425) B2628425
theorem B2628857 : Blo 1750576 2628857 := bstep (se 2 (by rfl) ⟨985821, by rfl⟩ : syracuseStep 2628857 = 1971643) B1971643
theorem B113605901 : Blo 1750576 113605901 := bstep (se 3 (by rfl) ⟨21301106, by rfl⟩ : syracuseStep 113605901 = 42602213) B42602213
theorem B1752359 : Blo 1750576 1752359 := bstep (se 1 (by rfl) ⟨1314269, by rfl⟩ : syracuseStep 1752359 = 2628539) B2628539
theorem B5913917 : Blo 1750576 5913917 := bstep (se 3 (by rfl) ⟨1108859, by rfl⟩ : syracuseStep 5913917 = 2217719) B2217719
theorem B1752399 : Blo 1750576 1752399 := bstep (se 1 (by rfl) ⟨1314299, by rfl⟩ : syracuseStep 1752399 = 2628599) B2628599
theorem B1752415 : Blo 1750576 1752415 := bstep (se 1 (by rfl) ⟨1314311, by rfl⟩ : syracuseStep 1752415 = 2628623) B2628623
theorem B11222387 : Blo 1750576 11222387 := bstep (se 1 (by rfl) ⟨8416790, by rfl⟩ : syracuseStep 11222387 = 16833581) B16833581
theorem B1752443 : Blo 1750576 1752443 := bstep (se 1 (by rfl) ⟨1314332, by rfl⟩ : syracuseStep 1752443 = 2628665) B2628665
theorem B1752495 : Blo 1750576 1752495 := bstep (se 1 (by rfl) ⟨1314371, by rfl⟩ : syracuseStep 1752495 = 2628743) B2628743
theorem B1752519 : Blo 1750576 1752519 := bstep (se 1 (by rfl) ⟨1314389, by rfl⟩ : syracuseStep 1752519 = 2628779) B2628779
theorem B3939803 : Blo 1750576 3939803 := bstep (se 1 (by rfl) ⟨2954852, by rfl⟩ : syracuseStep 3939803 = 5909705) B5909705
theorem B2956763 : Blo 1750576 2956763 := bstep (se 1 (by rfl) ⟨2217572, by rfl⟩ : syracuseStep 2956763 = 4435145) B4435145
theorem B1752539 : Blo 1750576 1752539 := bstep (se 1 (by rfl) ⟨1314404, by rfl⟩ : syracuseStep 1752539 = 2628809) B2628809
theorem B4267529 : Blo 1750576 4267529 := bstep (se 2 (by rfl) ⟨1600323, by rfl⟩ : syracuseStep 4267529 = 3200647) B3200647
theorem B2956999 : Blo 1750576 2956999 := bstep (se 1 (by rfl) ⟨2217749, by rfl⟩ : syracuseStep 2956999 = 4435499) B4435499
theorem B2957161 : Blo 1750576 2957161 := bstep (se 2 (by rfl) ⟨1108935, by rfl⟩ : syracuseStep 2957161 = 2217871) B2217871
theorem B3940271 : Blo 1750576 3940271 := bstep (se 1 (by rfl) ⟨2955203, by rfl⟩ : syracuseStep 3940271 = 5910407) B5910407
theorem B2367407 : Blo 1750576 2367407 := bstep (se 1 (by rfl) ⟨1775555, by rfl⟩ : syracuseStep 2367407 = 3551111) B3551111
theorem B30351289 : Blo 1750576 30351289 := bstep (se 2 (by rfl) ⟨11381733, by rfl⟩ : syracuseStep 30351289 = 22763467) B22763467
theorem B18931643 : Blo 1750576 18931643 := bstep (se 1 (by rfl) ⟨14198732, by rfl⟩ : syracuseStep 18931643 = 28397465) B28397465
theorem B3940361 : Blo 1750576 3940361 := bstep (se 2 (by rfl) ⟨1477635, by rfl⟩ : syracuseStep 3940361 = 2955271) B2955271
theorem B17981651 : Blo 1750576 17981651 := bstep (se 1 (by rfl) ⟨13486238, by rfl⟩ : syracuseStep 17981651 = 26972477) B26972477
theorem B5914835 : Blo 1750576 5914835 := bstep (se 1 (by rfl) ⟨4436126, by rfl⟩ : syracuseStep 5914835 = 8872253) B8872253
theorem B15974819 : Blo 1750576 15974819 := bstep (se 1 (by rfl) ⟨11981114, by rfl⟩ : syracuseStep 15974819 = 23962229) B23962229
theorem B3940775 : Blo 1750576 3940775 := bstep (se 1 (by rfl) ⟨2955581, by rfl⟩ : syracuseStep 3940775 = 5911163) B5911163
theorem B25248185 : Blo 1750576 25248185 := bstep (se 2 (by rfl) ⟨9468069, by rfl⟩ : syracuseStep 25248185 = 18936139) B18936139
theorem B8651227 : Blo 1750576 8651227 := bstep (se 1 (by rfl) ⟨6488420, by rfl⟩ : syracuseStep 8651227 = 12976841) B12976841
theorem B3940883 : Blo 1750576 3940883 := bstep (se 1 (by rfl) ⟨2955662, by rfl⟩ : syracuseStep 3940883 = 5911325) B5911325
theorem B3940937 : Blo 1750576 3940937 := bstep (se 2 (by rfl) ⟨1477851, by rfl⟩ : syracuseStep 3940937 = 2955703) B2955703
theorem B8413793 : Blo 1750576 8413793 := bstep (se 2 (by rfl) ⟨3155172, by rfl⟩ : syracuseStep 8413793 = 6310345) B6310345
theorem B8536697 : Blo 1750576 8536697 := bstep (se 2 (by rfl) ⟨3201261, by rfl⟩ : syracuseStep 8536697 = 6402523) B6402523
theorem B33653555 : Blo 1750576 33653555 := bstep (se 1 (by rfl) ⟨25240166, by rfl⟩ : syracuseStep 33653555 = 50480333) B50480333
theorem B7480259 : Blo 1750576 7480259 := bstep (se 1 (by rfl) ⟨5610194, by rfl⟩ : syracuseStep 7480259 = 11220389) B11220389
theorem B3941351 : Blo 1750576 3941351 := bstep (se 1 (by rfl) ⟨2956013, by rfl⟩ : syracuseStep 3941351 = 5912027) B5912027
theorem B8987705 : Blo 1750576 8987705 := bstep (se 2 (by rfl) ⟨3370389, by rfl⟩ : syracuseStep 8987705 = 6740779) B6740779
theorem B4433039 : Blo 1750576 4433039 := bstep (se 1 (by rfl) ⟨3324779, by rfl⟩ : syracuseStep 4433039 = 6649559) B6649559
theorem B7480619 : Blo 1750576 7480619 := bstep (se 1 (by rfl) ⟨5610464, by rfl⟩ : syracuseStep 7480619 = 11220929) B11220929
theorem B6653279 : Blo 1750576 6653279 := bstep (se 1 (by rfl) ⟨4989959, by rfl⟩ : syracuseStep 6653279 = 9979919) B9979919
theorem B3941729 : Blo 1750576 3941729 := bstep (se 2 (by rfl) ⟨1478148, by rfl⟩ : syracuseStep 3941729 = 2956297) B2956297
theorem B3941819 : Blo 1750576 3941819 := bstep (se 1 (by rfl) ⟨2956364, by rfl⟩ : syracuseStep 3941819 = 5912729) B5912729
theorem B8865287 : Blo 1750576 8865287 := bstep (se 1 (by rfl) ⟨6648965, by rfl⟩ : syracuseStep 8865287 = 13297931) B13297931
theorem B6653447 : Blo 1750576 6653447 := bstep (se 1 (by rfl) ⟨4990085, by rfl⟩ : syracuseStep 6653447 = 9980171) B9980171
theorem B3941945 : Blo 1750576 3941945 := bstep (se 2 (by rfl) ⟨1478229, by rfl⟩ : syracuseStep 3941945 = 2956459) B2956459
theorem B17974871 : Blo 1750576 17974871 := bstep (se 1 (by rfl) ⟨13481153, by rfl⟩ : syracuseStep 17974871 = 26962307) B26962307
theorem B25585645 : Blo 1750576 25585645 := bstep (se 3 (by rfl) ⟨4797308, by rfl⟩ : syracuseStep 25585645 = 9594617) B9594617
theorem B8865773 : Blo 1750576 8865773 := bstep (se 3 (by rfl) ⟨1662332, by rfl⟩ : syracuseStep 8865773 = 3324665) B3324665
theorem B7989229 : Blo 1750576 7989229 := bstep (se 3 (by rfl) ⟨1497980, by rfl⟩ : syracuseStep 7989229 = 2995961) B2995961
theorem B6653933 : Blo 1750576 6653933 := bstep (se 3 (by rfl) ⟨1247612, by rfl⟩ : syracuseStep 6653933 = 2495225) B2495225
theorem B75737267 : Blo 1750576 75737267 := bstep (se 1 (by rfl) ⟨56802950, by rfl⟩ : syracuseStep 75737267 = 113605901) B113605901
theorem B3942611 : Blo 1750576 3942611 := bstep (se 1 (by rfl) ⟨2956958, by rfl⟩ : syracuseStep 3942611 = 5913917) B5913917
theorem B7481591 : Blo 1750576 7481591 := bstep (se 1 (by rfl) ⟨5611193, by rfl⟩ : syracuseStep 7481591 = 11222387) B11222387
theorem B5908733 : Blo 1750576 5908733 := bstep (se 3 (by rfl) ⟨1107887, by rfl⟩ : syracuseStep 5908733 = 2215775) B2215775
theorem B8415485 : Blo 1750576 8415485 := bstep (se 3 (by rfl) ⟨1577903, by rfl⟩ : syracuseStep 8415485 = 3155807) B3155807
theorem B3942665 : Blo 1750576 3942665 := bstep (se 2 (by rfl) ⟨1478499, by rfl⟩ : syracuseStep 3942665 = 2956999) B2956999
theorem B2845019 : Blo 1750576 2845019 := bstep (se 1 (by rfl) ⟨2133764, by rfl⟩ : syracuseStep 2845019 = 4267529) B4267529
theorem B4557163 : Blo 1750576 4557163 := bstep (se 1 (by rfl) ⟨3417872, by rfl⟩ : syracuseStep 4557163 = 6835745) B6835745
theorem B8866259 : Blo 1750576 8866259 := bstep (se 1 (by rfl) ⟨6649694, by rfl⟩ : syracuseStep 8866259 = 13299389) B13299389
theorem B3942881 : Blo 1750576 3942881 := bstep (se 2 (by rfl) ⟨1478580, by rfl⟩ : syracuseStep 3942881 = 2957161) B2957161
theorem B3549919 : Blo 1750576 3549919 := bstep (se 1 (by rfl) ⟨2662439, by rfl⟩ : syracuseStep 3549919 = 5324879) B5324879
theorem B3943187 : Blo 1750576 3943187 := bstep (se 1 (by rfl) ⟨2957390, by rfl⟩ : syracuseStep 3943187 = 5914781) B5914781
theorem B8866583 : Blo 1750576 8866583 := bstep (se 1 (by rfl) ⟨6649937, by rfl⟩ : syracuseStep 8866583 = 13299875) B13299875
theorem B19958561 : Blo 1750576 19958561 := bstep (se 2 (by rfl) ⟨7484460, by rfl⟩ : syracuseStep 19958561 = 14968921) B14968921
theorem B3156815 : Blo 1750576 3156815 := bstep (se 1 (by rfl) ⟨2367611, by rfl⟩ : syracuseStep 3156815 = 4735223) B4735223
theorem B5909543 : Blo 1750576 5909543 := bstep (se 1 (by rfl) ⟨4432157, by rfl⟩ : syracuseStep 5909543 = 8864315) B8864315
theorem B4434983 : Blo 1750576 4434983 := bstep (se 1 (by rfl) ⟨3326237, by rfl⟩ : syracuseStep 4434983 = 6652475) B6652475
theorem B2804879 : Blo 1750576 2804879 := bstep (se 1 (by rfl) ⟨2103659, by rfl⟩ : syracuseStep 2804879 = 4207319) B4207319
theorem B9473213 : Blo 1750576 9473213 := bstep (se 3 (by rfl) ⟨1776227, by rfl⟩ : syracuseStep 9473213 = 3552455) B3552455
theorem B47951135 : Blo 1750576 47951135 := bstep (se 1 (by rfl) ⟨35963351, by rfl⟩ : syracuseStep 47951135 = 71926703) B71926703
theorem B1969447 : Blo 1750576 1969447 := bstep (se 1 (by rfl) ⟨1477085, by rfl⟩ : syracuseStep 1969447 = 2954171) B2954171
theorem B1969519 : Blo 1750576 1969519 := bstep (se 1 (by rfl) ⟨1477139, by rfl⟩ : syracuseStep 1969519 = 2954279) B2954279
theorem B4435337 : Blo 1750576 4435337 := bstep (se 2 (by rfl) ⟨1663251, by rfl⟩ : syracuseStep 4435337 = 3326503) B3326503
theorem B5909975 : Blo 1750576 5909975 := bstep (se 1 (by rfl) ⟨4432481, by rfl⟩ : syracuseStep 5909975 = 8864963) B8864963
theorem B9473561 : Blo 1750576 9473561 := bstep (se 2 (by rfl) ⟨3552585, by rfl⟩ : syracuseStep 9473561 = 7105171) B7105171
theorem B1969735 : Blo 1750576 1969735 := bstep (se 1 (by rfl) ⟨1477301, by rfl⟩ : syracuseStep 1969735 = 2954603) B2954603
theorem B3370579 : Blo 1750576 3370579 := bstep (se 1 (by rfl) ⟨2527934, by rfl⟩ : syracuseStep 3370579 = 5055869) B5055869
theorem B14970905 : Blo 1750576 14970905 := bstep (se 2 (by rfl) ⟨5614089, by rfl⟩ : syracuseStep 14970905 = 11228179) B11228179
theorem B10113083 : Blo 1750576 10113083 := bstep (se 1 (by rfl) ⟨7584812, by rfl⟩ : syracuseStep 10113083 = 15169625) B15169625
theorem B8417483 : Blo 1750576 8417483 := bstep (se 1 (by rfl) ⟨6313112, by rfl⟩ : syracuseStep 8417483 = 12626225) B12626225
theorem B9474251 : Blo 1750576 9474251 := bstep (se 1 (by rfl) ⟨7105688, by rfl⟩ : syracuseStep 9474251 = 14211377) B14211377
theorem B2216155 : Blo 1750576 2216155 := bstep (se 1 (by rfl) ⟨1662116, by rfl⟩ : syracuseStep 2216155 = 3324233) B3324233
theorem B2494729 : Blo 1750576 2494729 := bstep (se 2 (by rfl) ⟨935523, by rfl⟩ : syracuseStep 2494729 = 1871047) B1871047
theorem B8868203 : Blo 1750576 8868203 := bstep (se 1 (by rfl) ⟨6651152, by rfl⟩ : syracuseStep 8868203 = 13302305) B13302305
theorem B2625959 : Blo 1750576 2625959 := bstep (se 1 (by rfl) ⟨1969469, by rfl⟩ : syracuseStep 2625959 = 3938939) B3938939
theorem B1970599 : Blo 1750576 1970599 := bstep (se 1 (by rfl) ⟨1477949, by rfl⟩ : syracuseStep 1970599 = 2955899) B2955899
theorem B2626043 : Blo 1750576 2626043 := bstep (se 1 (by rfl) ⟨1969532, by rfl⟩ : syracuseStep 2626043 = 3939065) B3939065
theorem B2626169 : Blo 1750576 2626169 := bstep (se 2 (by rfl) ⟨984813, by rfl⟩ : syracuseStep 2626169 = 1969627) B1969627
theorem B7484051 : Blo 1750576 7484051 := bstep (se 1 (by rfl) ⟨5613038, by rfl⟩ : syracuseStep 7484051 = 11226077) B11226077
theorem B8417945 : Blo 1750576 8417945 := bstep (se 2 (by rfl) ⟨3156729, by rfl⟩ : syracuseStep 8417945 = 6313459) B6313459
theorem B2626223 : Blo 1750576 2626223 := bstep (se 1 (by rfl) ⟨1969667, by rfl⟩ : syracuseStep 2626223 = 3939335) B3939335
theorem B8991415 : Blo 1750576 8991415 := bstep (se 1 (by rfl) ⟨6743561, by rfl⟩ : syracuseStep 8991415 = 13487123) B13487123
theorem B29913785 : Blo 1750576 29913785 := bstep (se 2 (by rfl) ⟨11217669, by rfl⟩ : syracuseStep 29913785 = 22435339) B22435339
theorem B2626271 : Blo 1750576 2626271 := bstep (se 1 (by rfl) ⟨1969703, by rfl⟩ : syracuseStep 2626271 = 3939407) B3939407
theorem B2626535 : Blo 1750576 2626535 := bstep (se 1 (by rfl) ⟨1969901, by rfl⟩ : syracuseStep 2626535 = 3939803) B3939803
theorem B1971175 : Blo 1750576 1971175 := bstep (se 1 (by rfl) ⟨1478381, by rfl⟩ : syracuseStep 1971175 = 2956763) B2956763
theorem B5911649 : Blo 1750576 5911649 := bstep (se 2 (by rfl) ⟨2216868, by rfl⟩ : syracuseStep 5911649 = 4433737) B4433737
theorem B6313085 : Blo 1750576 6313085 := bstep (se 3 (by rfl) ⟨1183703, by rfl⟩ : syracuseStep 6313085 = 2367407) B2367407
theorem B2626793 : Blo 1750576 2626793 := bstep (se 2 (by rfl) ⟨985047, by rfl⟩ : syracuseStep 2626793 = 1970095) B1970095
theorem B14955799 : Blo 1750576 14955799 := bstep (se 1 (by rfl) ⟨11216849, by rfl⟩ : syracuseStep 14955799 = 22433699) B22433699
theorem B2626847 : Blo 1750576 2626847 := bstep (se 1 (by rfl) ⟨1970135, by rfl⟩ : syracuseStep 2626847 = 3940271) B3940271
theorem B12621095 : Blo 1750576 12621095 := bstep (se 1 (by rfl) ⟨9465821, by rfl⟩ : syracuseStep 12621095 = 18931643) B18931643
theorem B4732283 : Blo 1750576 4732283 := bstep (se 1 (by rfl) ⟨3549212, by rfl⟩ : syracuseStep 4732283 = 7098425) B7098425
theorem B2627015 : Blo 1750576 2627015 := bstep (se 1 (by rfl) ⟨1970261, by rfl⟩ : syracuseStep 2627015 = 3940523) B3940523
theorem B1750591 : Blo 1750576 1750591 := bstep (se 1 (by rfl) ⟨1312943, by rfl⟩ : syracuseStep 1750591 = 2625887) B2625887
theorem B1750599 : Blo 1750576 1750599 := bstep (se 1 (by rfl) ⟨1312949, by rfl⟩ : syracuseStep 1750599 = 2625899) B2625899
theorem B19961477 : Blo 1750576 19961477 := bstep (se 4 (by rfl) ⟨1871388, by rfl⟩ : syracuseStep 19961477 = 3742777) B3742777
theorem B1750751 : Blo 1750576 1750751 := bstep (se 1 (by rfl) ⟨1313063, by rfl⟩ : syracuseStep 1750751 = 2626127) B2626127
theorem B7788317 : Blo 1750576 7788317 := bstep (se 3 (by rfl) ⟨1460309, by rfl⟩ : syracuseStep 7788317 = 2920619) B2920619
theorem B8869661 : Blo 1750576 8869661 := bstep (se 3 (by rfl) ⟨1663061, by rfl⟩ : syracuseStep 8869661 = 3326123) B3326123
theorem B2627369 : Blo 1750576 2627369 := bstep (se 2 (by rfl) ⟨985263, by rfl⟩ : syracuseStep 2627369 = 1970527) B1970527
theorem B1750831 : Blo 1750576 1750831 := bstep (se 1 (by rfl) ⟨1313123, by rfl⟩ : syracuseStep 1750831 = 2626247) B2626247
theorem B2955055 : Blo 1750576 2955055 := bstep (se 1 (by rfl) ⟨2216291, by rfl⟩ : syracuseStep 2955055 = 4432583) B4432583
theorem B2627375 : Blo 1750576 2627375 := bstep (se 1 (by rfl) ⟨1970531, by rfl⟩ : syracuseStep 2627375 = 3941063) B3941063
theorem B2217775 : Blo 1750576 2217775 := bstep (se 1 (by rfl) ⟨1663331, by rfl⟩ : syracuseStep 2217775 = 3326663) B3326663
theorem B4986679 : Blo 1750576 4986679 := bstep (se 1 (by rfl) ⟨3740009, by rfl⟩ : syracuseStep 4986679 = 7480019) B7480019
theorem B1750939 : Blo 1750576 1750939 := bstep (se 1 (by rfl) ⟨1313204, by rfl⟩ : syracuseStep 1750939 = 2626409) B2626409
theorem B1750991 : Blo 1750576 1750991 := bstep (se 1 (by rfl) ⟨1313243, by rfl⟩ : syracuseStep 1750991 = 2626487) B2626487
theorem B1751015 : Blo 1750576 1751015 := bstep (se 1 (by rfl) ⟨1313261, by rfl⟩ : syracuseStep 1751015 = 2626523) B2626523
theorem B9599111 : Blo 1750576 9599111 := bstep (se 1 (by rfl) ⟨7199333, by rfl⟩ : syracuseStep 9599111 = 14398667) B14398667
theorem B11991287 : Blo 1750576 11991287 := bstep (se 1 (by rfl) ⟨8993465, by rfl⟩ : syracuseStep 11991287 = 17986931) B17986931
theorem B2627849 : Blo 1750576 2627849 := bstep (se 2 (by rfl) ⟨985443, by rfl⟩ : syracuseStep 2627849 = 1970887) B1970887
theorem B2103583 : Blo 1750576 2103583 := bstep (se 1 (by rfl) ⟨1577687, by rfl⟩ : syracuseStep 2103583 = 3155375) B3155375
theorem B1751327 : Blo 1750576 1751327 := bstep (se 1 (by rfl) ⟨1313495, by rfl⟩ : syracuseStep 1751327 = 2626991) B2626991
theorem B17070425 : Blo 1750576 17070425 := bstep (se 2 (by rfl) ⟨6401409, by rfl⟩ : syracuseStep 17070425 = 12802819) B12802819
theorem B1751387 : Blo 1750576 1751387 := bstep (se 1 (by rfl) ⟨1313540, by rfl⟩ : syracuseStep 1751387 = 2627081) B2627081
theorem B1751407 : Blo 1750576 1751407 := bstep (se 1 (by rfl) ⟨1313555, by rfl⟩ : syracuseStep 1751407 = 2627111) B2627111
theorem B2627951 : Blo 1750576 2627951 := bstep (se 1 (by rfl) ⟨1970963, by rfl⟩ : syracuseStep 2627951 = 3941927) B3941927
theorem B1751463 : Blo 1750576 1751463 := bstep (se 1 (by rfl) ⟨1313597, by rfl⟩ : syracuseStep 1751463 = 2627195) B2627195
theorem B5912999 : Blo 1750576 5912999 := bstep (se 1 (by rfl) ⟨4434749, by rfl⟩ : syracuseStep 5912999 = 8869499) B8869499
theorem B10795447 : Blo 1750576 10795447 := bstep (se 1 (by rfl) ⟨8096585, by rfl⟩ : syracuseStep 10795447 = 16193171) B16193171
theorem B4209079 : Blo 1750576 4209079 := bstep (se 1 (by rfl) ⟨3156809, by rfl⟩ : syracuseStep 4209079 = 6313619) B6313619
theorem B6650363 : Blo 1750576 6650363 := bstep (se 1 (by rfl) ⟨4987772, by rfl⟩ : syracuseStep 6650363 = 9975545) B9975545
theorem B1751547 : Blo 1750576 1751547 := bstep (se 1 (by rfl) ⟨1313660, by rfl⟩ : syracuseStep 1751547 = 2627321) B2627321
theorem B1751615 : Blo 1750576 1751615 := bstep (se 1 (by rfl) ⟨1313711, by rfl⟩ : syracuseStep 1751615 = 2627423) B2627423
theorem B15170111 : Blo 1750576 15170111 := bstep (se 1 (by rfl) ⟨11377583, by rfl⟩ : syracuseStep 15170111 = 22755167) B22755167
theorem B2366023 : Blo 1750576 2366023 := bstep (se 1 (by rfl) ⟨1774517, by rfl⟩ : syracuseStep 2366023 = 3549035) B3549035
theorem B1751623 : Blo 1750576 1751623 := bstep (se 1 (by rfl) ⟨1313717, by rfl⟩ : syracuseStep 1751623 = 2627435) B2627435
theorem B5913161 : Blo 1750576 5913161 := bstep (se 2 (by rfl) ⟨2217435, by rfl⟩ : syracuseStep 5913161 = 4434871) B4434871
theorem B2628167 : Blo 1750576 2628167 := bstep (se 1 (by rfl) ⟨1971125, by rfl⟩ : syracuseStep 2628167 = 3942251) B3942251
theorem B2628203 : Blo 1750576 2628203 := bstep (se 1 (by rfl) ⟨1971152, by rfl⟩ : syracuseStep 2628203 = 3942305) B3942305
theorem B1751775 : Blo 1750576 1751775 := bstep (se 1 (by rfl) ⟨1313831, by rfl⟩ : syracuseStep 1751775 = 2627663) B2627663
theorem B7985911 : Blo 1750576 7985911 := bstep (se 1 (by rfl) ⟨5989433, by rfl⟩ : syracuseStep 7985911 = 11978867) B11978867
theorem B1751855 : Blo 1750576 1751855 := bstep (se 1 (by rfl) ⟨1313891, by rfl⟩ : syracuseStep 1751855 = 2627783) B2627783
theorem B2628431 : Blo 1750576 2628431 := bstep (se 1 (by rfl) ⟨1971323, by rfl⟩ : syracuseStep 2628431 = 3942647) B3942647
theorem B4733839 : Blo 1750576 4733839 := bstep (se 1 (by rfl) ⟨3550379, by rfl⟩ : syracuseStep 4733839 = 7100759) B7100759
theorem B3742607 : Blo 1750576 3742607 := bstep (se 1 (by rfl) ⟨2806955, by rfl⟩ : syracuseStep 3742607 = 5613911) B5613911
theorem B3939227 : Blo 1750576 3939227 := bstep (se 1 (by rfl) ⟨2954420, by rfl⟩ : syracuseStep 3939227 = 5908841) B5908841
theorem B1751963 : Blo 1750576 1751963 := bstep (se 1 (by rfl) ⟨1313972, by rfl⟩ : syracuseStep 1751963 = 2627945) B2627945
theorem B1752015 : Blo 1750576 1752015 := bstep (se 1 (by rfl) ⟨1314011, by rfl⟩ : syracuseStep 1752015 = 2628023) B2628023
theorem B1752039 : Blo 1750576 1752039 := bstep (se 1 (by rfl) ⟨1314029, by rfl⟩ : syracuseStep 1752039 = 2628059) B2628059
theorem B22756403 : Blo 1750576 22756403 := bstep (se 1 (by rfl) ⟨17067302, by rfl⟩ : syracuseStep 22756403 = 34134605) B34134605
theorem B3939425 : Blo 1750576 3939425 := bstep (se 2 (by rfl) ⟨1477284, by rfl⟩ : syracuseStep 3939425 = 2954569) B2954569
theorem B14965883 : Blo 1750576 14965883 := bstep (se 1 (by rfl) ⟨11224412, by rfl⟩ : syracuseStep 14965883 = 22448825) B22448825
theorem B24288473 : Blo 1750576 24288473 := bstep (se 2 (by rfl) ⟨9108177, by rfl⟩ : syracuseStep 24288473 = 18216355) B18216355
theorem B2628827 : Blo 1750576 2628827 := bstep (se 1 (by rfl) ⟨1971620, by rfl⟩ : syracuseStep 2628827 = 3943241) B3943241
theorem B1752351 : Blo 1750576 1752351 := bstep (se 1 (by rfl) ⟨1314263, by rfl⟩ : syracuseStep 1752351 = 2628527) B2628527
theorem B3939623 : Blo 1750576 3939623 := bstep (se 1 (by rfl) ⟨2954717, by rfl⟩ : syracuseStep 3939623 = 5909435) B5909435
theorem B1752411 : Blo 1750576 1752411 := bstep (se 1 (by rfl) ⟨1314308, by rfl⟩ : syracuseStep 1752411 = 2628617) B2628617
theorem B1752431 : Blo 1750576 1752431 := bstep (se 1 (by rfl) ⟨1314323, by rfl⟩ : syracuseStep 1752431 = 2628647) B2628647
theorem B4988297 : Blo 1750576 4988297 := bstep (se 2 (by rfl) ⟨1870611, by rfl⟩ : syracuseStep 4988297 = 3741223) B3741223
theorem B1752487 : Blo 1750576 1752487 := bstep (se 1 (by rfl) ⟨1314365, by rfl⟩ : syracuseStep 1752487 = 2628731) B2628731
theorem B6651335 : Blo 1750576 6651335 := bstep (se 1 (by rfl) ⟨4988501, by rfl⟩ : syracuseStep 6651335 = 9977003) B9977003
theorem B1752571 : Blo 1750576 1752571 := bstep (se 1 (by rfl) ⟨1314428, by rfl⟩ : syracuseStep 1752571 = 2628857) B2628857
theorem B12623455 : Blo 1750576 12623455 := bstep (se 1 (by rfl) ⟨9467591, by rfl⟩ : syracuseStep 12623455 = 18935183) B18935183
theorem B3940001 : Blo 1750576 3940001 := bstep (se 2 (by rfl) ⟨1477500, by rfl⟩ : syracuseStep 3940001 = 2955001) B2955001
theorem B7478993 : Blo 1750576 7478993 := bstep (se 2 (by rfl) ⟨2804622, by rfl⟩ : syracuseStep 7478993 = 5609245) B5609245
theorem B14966531 : Blo 1750576 14966531 := bstep (se 1 (by rfl) ⟨11224898, by rfl⟩ : syracuseStep 14966531 = 22449797) B22449797
theorem B4988729 : Blo 1750576 4988729 := bstep (se 2 (by rfl) ⟨1870773, by rfl⟩ : syracuseStep 4988729 = 3741547) B3741547
theorem B4734877 : Blo 1750576 4734877 := bstep (se 3 (by rfl) ⟨887789, by rfl⟩ : syracuseStep 4734877 = 1775579) B1775579
theorem B40468385 : Blo 1750576 40468385 := bstep (se 2 (by rfl) ⟨15175644, by rfl⟩ : syracuseStep 40468385 = 30351289) B30351289
theorem B6742055 : Blo 1750576 6742055 := bstep (se 1 (by rfl) ⟨5056541, by rfl⟩ : syracuseStep 6742055 = 10113083) B10113083
theorem B5611655 : Blo 1750576 5611655 := bstep (se 1 (by rfl) ⟨4208741, by rfl⟩ : syracuseStep 5611655 = 8417483) B8417483
theorem B10649879 : Blo 1750576 10649879 := bstep (se 1 (by rfl) ⟨7987409, by rfl⟩ : syracuseStep 10649879 = 15974819) B15974819
theorem B83075381 : Blo 1750576 83075381 := bstep (se 5 (by rfl) ⟨3894158, by rfl⟩ : syracuseStep 83075381 = 7788317) B7788317
theorem B7479677 : Blo 1750576 7479677 := bstep (se 3 (by rfl) ⟨1402439, by rfl⟩ : syracuseStep 7479677 = 2804879) B2804879
theorem B4989367 : Blo 1750576 4989367 := bstep (se 1 (by rfl) ⟨3742025, by rfl⟩ : syracuseStep 4989367 = 7484051) B7484051
theorem B5611963 : Blo 1750576 5611963 := bstep (se 1 (by rfl) ⟨4208972, by rfl⟩ : syracuseStep 5611963 = 8417945) B8417945
theorem B25264669 : Blo 1750576 25264669 := bstep (se 3 (by rfl) ⟨4737125, by rfl⟩ : syracuseStep 25264669 = 9474251) B9474251
theorem B14393929 : Blo 1750576 14393929 := bstep (se 2 (by rfl) ⟨5397723, by rfl⟩ : syracuseStep 14393929 = 10795447) B10795447
theorem B5612105 : Blo 1750576 5612105 := bstep (se 2 (by rfl) ⟨2104539, by rfl⟩ : syracuseStep 5612105 = 4209079) B4209079
theorem B11534969 : Blo 1750576 11534969 := bstep (se 2 (by rfl) ⟨4325613, by rfl⟩ : syracuseStep 11534969 = 8651227) B8651227
theorem B3941099 : Blo 1750576 3941099 := bstep (se 1 (by rfl) ⟨2955824, by rfl⟩ : syracuseStep 3941099 = 5911649) B5911649
theorem B3154697 : Blo 1750576 3154697 := bstep (se 2 (by rfl) ⟨1183011, by rfl⟩ : syracuseStep 3154697 = 2366023) B2366023
theorem B8414063 : Blo 1750576 8414063 := bstep (se 1 (by rfl) ⟨6310547, by rfl⟩ : syracuseStep 8414063 = 12621095) B12621095
theorem B3154855 : Blo 1750576 3154855 := bstep (se 1 (by rfl) ⟨2366141, by rfl⟩ : syracuseStep 3154855 = 4732283) B4732283
theorem B13305221 : Blo 1750576 13305221 := bstep (se 4 (by rfl) ⟨1247364, by rfl⟩ : syracuseStep 13305221 = 2494729) B2494729
theorem B6399407 : Blo 1750576 6399407 := bstep (se 1 (by rfl) ⟨4799555, by rfl⟩ : syracuseStep 6399407 = 9599111) B9599111
theorem B11380283 : Blo 1750576 11380283 := bstep (se 1 (by rfl) ⟨8535212, by rfl⟩ : syracuseStep 11380283 = 17070425) B17070425
theorem B3941999 : Blo 1750576 3941999 := bstep (se 1 (by rfl) ⟨2956499, by rfl⟩ : syracuseStep 3941999 = 5912999) B5912999
theorem B4433575 : Blo 1750576 4433575 := bstep (se 1 (by rfl) ⟨3325181, by rfl⟩ : syracuseStep 4433575 = 6650363) B6650363
theorem B19941065 : Blo 1750576 19941065 := bstep (se 2 (by rfl) ⟨7477899, by rfl⟩ : syracuseStep 19941065 = 14955799) B14955799
theorem B3942107 : Blo 1750576 3942107 := bstep (se 1 (by rfl) ⟨2956580, by rfl⟩ : syracuseStep 3942107 = 5913161) B5913161
theorem B13305707 : Blo 1750576 13305707 := bstep (se 1 (by rfl) ⟨9979280, by rfl⟩ : syracuseStep 13305707 = 19958561) B19958561
theorem B31967423 : Blo 1750576 31967423 := bstep (se 1 (by rfl) ⟨23975567, by rfl⟩ : syracuseStep 31967423 = 47951135) B47951135
theorem B4434223 : Blo 1750576 4434223 := bstep (se 1 (by rfl) ⟨3325667, by rfl⟩ : syracuseStep 4434223 = 6651335) B6651335
theorem B26978923 : Blo 1750576 26978923 := bstep (se 1 (by rfl) ⟨20234192, by rfl⟩ : syracuseStep 26978923 = 40468385) B40468385
theorem B34114193 : Blo 1750576 34114193 := bstep (se 2 (by rfl) ⟨12792822, by rfl⟩ : syracuseStep 34114193 = 25585645) B25585645
theorem B10652305 : Blo 1750576 10652305 := bstep (se 2 (by rfl) ⟨3994614, by rfl⟩ : syracuseStep 10652305 = 7989229) B7989229
theorem B9980603 : Blo 1750576 9980603 := bstep (se 1 (by rfl) ⟨7485452, by rfl⟩ : syracuseStep 9980603 = 14970905) B14970905
theorem B11987767 : Blo 1750576 11987767 := bstep (se 1 (by rfl) ⟨8990825, by rfl⟩ : syracuseStep 11987767 = 17981651) B17981651
theorem B3943223 : Blo 1750576 3943223 := bstep (se 1 (by rfl) ⟨2957417, by rfl⟩ : syracuseStep 3943223 = 5914835) B5914835
theorem B2804777 : Blo 1750576 2804777 := bstep (se 2 (by rfl) ⟨1051791, by rfl⟩ : syracuseStep 2804777 = 2103583) B2103583
theorem B17976421 : Blo 1750576 17976421 := bstep (se 4 (by rfl) ⟨1685289, by rfl⟩ : syracuseStep 17976421 = 3370579) B3370579
theorem B19942523 : Blo 1750576 19942523 := bstep (se 1 (by rfl) ⟨14956892, by rfl⟩ : syracuseStep 19942523 = 29913785) B29913785
theorem B31976765 : Blo 1750576 31976765 := bstep (se 3 (by rfl) ⟨5995643, by rfl⟩ : syracuseStep 31976765 = 11991287) B11991287
theorem B5991803 : Blo 1750576 5991803 := bstep (se 1 (by rfl) ⟨4493852, by rfl⟩ : syracuseStep 5991803 = 8987705) B8987705
theorem B4435519 : Blo 1750576 4435519 := bstep (se 1 (by rfl) ⟨3326639, by rfl⟩ : syracuseStep 4435519 = 6653279) B6653279
theorem B5910191 : Blo 1750576 5910191 := bstep (se 1 (by rfl) ⟨4432643, by rfl⟩ : syracuseStep 5910191 = 8865287) B8865287
theorem B4435631 : Blo 1750576 4435631 := bstep (se 1 (by rfl) ⟨3326723, by rfl⟩ : syracuseStep 4435631 = 6653447) B6653447
theorem B13307651 : Blo 1750576 13307651 := bstep (se 1 (by rfl) ⟨9980738, by rfl⟩ : syracuseStep 13307651 = 19961477) B19961477
theorem B6311785 : Blo 1750576 6311785 := bstep (se 2 (by rfl) ⟨2366919, by rfl⟩ : syracuseStep 6311785 = 4733839) B4733839
theorem B5910515 : Blo 1750576 5910515 := bstep (se 1 (by rfl) ⟨4432886, by rfl⟩ : syracuseStep 5910515 = 8865773) B8865773
theorem B4435955 : Blo 1750576 4435955 := bstep (se 1 (by rfl) ⟨3326966, by rfl⟩ : syracuseStep 4435955 = 6653933) B6653933
theorem B50491511 : Blo 1750576 50491511 := bstep (se 1 (by rfl) ⟨37868633, by rfl⟩ : syracuseStep 50491511 = 75737267) B75737267
theorem B1896679 : Blo 1750576 1896679 := bstep (se 1 (by rfl) ⟨1422509, by rfl⟩ : syracuseStep 1896679 = 2845019) B2845019
theorem B5910839 : Blo 1750576 5910839 := bstep (se 1 (by rfl) ⟨4433129, by rfl⟩ : syracuseStep 5910839 = 8866259) B8866259
theorem B10113407 : Blo 1750576 10113407 := bstep (se 1 (by rfl) ⟨7585055, by rfl⟩ : syracuseStep 10113407 = 15170111) B15170111
theorem B2625929 : Blo 1750576 2625929 := bstep (se 2 (by rfl) ⟨984723, by rfl⟩ : syracuseStep 2625929 = 1969447) B1969447
theorem B2626025 : Blo 1750576 2626025 := bstep (se 2 (by rfl) ⟨984759, by rfl⟩ : syracuseStep 2626025 = 1969519) B1969519
theorem B5911055 : Blo 1750576 5911055 := bstep (se 1 (by rfl) ⟨4433291, by rfl⟩ : syracuseStep 5911055 = 8866583) B8866583
theorem B19943981 : Blo 1750576 19943981 := bstep (se 3 (by rfl) ⟨3739496, by rfl⟩ : syracuseStep 19943981 = 7478993) B7478993
theorem B2495071 : Blo 1750576 2495071 := bstep (se 1 (by rfl) ⟨1871303, by rfl⟩ : syracuseStep 2495071 = 3742607) B3742607
theorem B2626151 : Blo 1750576 2626151 := bstep (se 1 (by rfl) ⟨1969613, by rfl⟩ : syracuseStep 2626151 = 3939227) B3939227
theorem B2626283 : Blo 1750576 2626283 := bstep (se 1 (by rfl) ⟨1969712, by rfl⟩ : syracuseStep 2626283 = 3939425) B3939425
theorem B2626313 : Blo 1750576 2626313 := bstep (se 2 (by rfl) ⟨984867, by rfl⟩ : syracuseStep 2626313 = 1969735) B1969735
theorem B16831273 : Blo 1750576 16831273 := bstep (se 2 (by rfl) ⟨6311727, by rfl⟩ : syracuseStep 16831273 = 12623455) B12623455
theorem B16192315 : Blo 1750576 16192315 := bstep (se 1 (by rfl) ⟨12144236, by rfl⟩ : syracuseStep 16192315 = 24288473) B24288473
theorem B2626415 : Blo 1750576 2626415 := bstep (se 1 (by rfl) ⟨1969811, by rfl⟩ : syracuseStep 2626415 = 3939623) B3939623
theorem B8418173 : Blo 1750576 8418173 := bstep (se 3 (by rfl) ⟨1578407, by rfl⟩ : syracuseStep 8418173 = 3156815) B3156815
theorem B6648905 : Blo 1750576 6648905 := bstep (se 2 (by rfl) ⟨2493339, by rfl⟩ : syracuseStep 6648905 = 4986679) B4986679
theorem B2626667 : Blo 1750576 2626667 := bstep (se 1 (by rfl) ⟨1970000, by rfl⟩ : syracuseStep 2626667 = 3940001) B3940001
theorem B6313169 : Blo 1750576 6313169 := bstep (se 2 (by rfl) ⟨2367438, by rfl⟩ : syracuseStep 6313169 = 4734877) B4734877
theorem B2626907 : Blo 1750576 2626907 := bstep (se 1 (by rfl) ⟨1970180, by rfl⟩ : syracuseStep 2626907 = 3940361) B3940361
theorem B5912135 : Blo 1750576 5912135 := bstep (se 1 (by rfl) ⟨4434101, by rfl⟩ : syracuseStep 5912135 = 8868203) B8868203
theorem B1750639 : Blo 1750576 1750639 := bstep (se 1 (by rfl) ⟨1312979, by rfl⟩ : syracuseStep 1750639 = 2625959) B2625959
theorem B2627183 : Blo 1750576 2627183 := bstep (se 1 (by rfl) ⟨1970387, by rfl⟩ : syracuseStep 2627183 = 3940775) B3940775
theorem B2954873 : Blo 1750576 2954873 := bstep (se 2 (by rfl) ⟨1108077, by rfl⟩ : syracuseStep 2954873 = 2216155) B2216155
theorem B16832123 : Blo 1750576 16832123 := bstep (se 1 (by rfl) ⟨12624092, by rfl⟩ : syracuseStep 16832123 = 25248185) B25248185
theorem B1750695 : Blo 1750576 1750695 := bstep (se 1 (by rfl) ⟨1313021, by rfl⟩ : syracuseStep 1750695 = 2626043) B2626043
theorem B2627255 : Blo 1750576 2627255 := bstep (se 1 (by rfl) ⟨1970441, by rfl⟩ : syracuseStep 2627255 = 3940883) B3940883
theorem B2627291 : Blo 1750576 2627291 := bstep (se 1 (by rfl) ⟨1970468, by rfl⟩ : syracuseStep 2627291 = 3940937) B3940937
theorem B5609195 : Blo 1750576 5609195 := bstep (se 1 (by rfl) ⟨4206896, by rfl⟩ : syracuseStep 5609195 = 8413793) B8413793
theorem B1750779 : Blo 1750576 1750779 := bstep (se 1 (by rfl) ⟨1313084, by rfl⟩ : syracuseStep 1750779 = 2626169) B2626169
theorem B5691131 : Blo 1750576 5691131 := bstep (se 1 (by rfl) ⟨4268348, by rfl⟩ : syracuseStep 5691131 = 8536697) B8536697
theorem B1750815 : Blo 1750576 1750815 := bstep (se 1 (by rfl) ⟨1313111, by rfl⟩ : syracuseStep 1750815 = 2626223) B2626223
theorem B6076217 : Blo 1750576 6076217 := bstep (se 2 (by rfl) ⟨2278581, by rfl⟩ : syracuseStep 6076217 = 4557163) B4557163
theorem B1750847 : Blo 1750576 1750847 := bstep (se 1 (by rfl) ⟨1313135, by rfl⟩ : syracuseStep 1750847 = 2626271) B2626271
theorem B25261901 : Blo 1750576 25261901 := bstep (se 3 (by rfl) ⟨4736606, by rfl⟩ : syracuseStep 25261901 = 9473213) B9473213
theorem B22435703 : Blo 1750576 22435703 := bstep (se 1 (by rfl) ⟨16826777, by rfl⟩ : syracuseStep 22435703 = 33653555) B33653555
theorem B2627465 : Blo 1750576 2627465 := bstep (se 2 (by rfl) ⟨985299, by rfl⟩ : syracuseStep 2627465 = 1970599) B1970599
theorem B4986839 : Blo 1750576 4986839 := bstep (se 1 (by rfl) ⟨3740129, by rfl⟩ : syracuseStep 4986839 = 7480259) B7480259
theorem B1751023 : Blo 1750576 1751023 := bstep (se 1 (by rfl) ⟨1313267, by rfl⟩ : syracuseStep 1751023 = 2626535) B2626535
theorem B2627567 : Blo 1750576 2627567 := bstep (se 1 (by rfl) ⟨1970675, by rfl⟩ : syracuseStep 2627567 = 3941351) B3941351
theorem B4208723 : Blo 1750576 4208723 := bstep (se 1 (by rfl) ⟨3156542, by rfl⟩ : syracuseStep 4208723 = 6313085) B6313085
theorem B2955359 : Blo 1750576 2955359 := bstep (se 1 (by rfl) ⟨2216519, by rfl⟩ : syracuseStep 2955359 = 4433039) B4433039
theorem B1751195 : Blo 1750576 1751195 := bstep (se 1 (by rfl) ⟨1313396, by rfl⟩ : syracuseStep 1751195 = 2626793) B2626793
theorem B1751231 : Blo 1750576 1751231 := bstep (se 1 (by rfl) ⟨1313423, by rfl⟩ : syracuseStep 1751231 = 2626847) B2626847
theorem B4987079 : Blo 1750576 4987079 := bstep (se 1 (by rfl) ⟨3740309, by rfl⟩ : syracuseStep 4987079 = 7480619) B7480619
theorem B2627819 : Blo 1750576 2627819 := bstep (se 1 (by rfl) ⟨1970864, by rfl⟩ : syracuseStep 2627819 = 3941729) B3941729
theorem B47954213 : Blo 1750576 47954213 := bstep (se 4 (by rfl) ⟨4495707, by rfl⟩ : syracuseStep 47954213 = 8991415) B8991415
theorem B2627879 : Blo 1750576 2627879 := bstep (se 1 (by rfl) ⟨1970909, by rfl⟩ : syracuseStep 2627879 = 3941819) B3941819
theorem B4733225 : Blo 1750576 4733225 := bstep (se 2 (by rfl) ⟨1774959, by rfl⟩ : syracuseStep 4733225 = 3549919) B3549919
theorem B1751343 : Blo 1750576 1751343 := bstep (se 1 (by rfl) ⟨1313507, by rfl⟩ : syracuseStep 1751343 = 2627015) B2627015
theorem B10647881 : Blo 1750576 10647881 := bstep (se 2 (by rfl) ⟨3992955, by rfl⟩ : syracuseStep 10647881 = 7985911) B7985911
theorem B2627963 : Blo 1750576 2627963 := bstep (se 1 (by rfl) ⟨1970972, by rfl⟩ : syracuseStep 2627963 = 3941945) B3941945
theorem B11983247 : Blo 1750576 11983247 := bstep (se 1 (by rfl) ⟨8987435, by rfl⟩ : syracuseStep 11983247 = 17974871) B17974871
theorem B5913107 : Blo 1750576 5913107 := bstep (se 1 (by rfl) ⟨4434830, by rfl⟩ : syracuseStep 5913107 = 8869661) B8869661
theorem B1751579 : Blo 1750576 1751579 := bstep (se 1 (by rfl) ⟨1313684, by rfl⟩ : syracuseStep 1751579 = 2627369) B2627369
theorem B1751583 : Blo 1750576 1751583 := bstep (se 1 (by rfl) ⟨1313687, by rfl⟩ : syracuseStep 1751583 = 2627375) B2627375
theorem B2628233 : Blo 1750576 2628233 := bstep (se 2 (by rfl) ⟨985587, by rfl⟩ : syracuseStep 2628233 = 1971175) B1971175
theorem B2628407 : Blo 1750576 2628407 := bstep (se 1 (by rfl) ⟨1971305, by rfl⟩ : syracuseStep 2628407 = 3942611) B3942611
theorem B4987727 : Blo 1750576 4987727 := bstep (se 1 (by rfl) ⟨3740795, by rfl⟩ : syracuseStep 4987727 = 7481591) B7481591
theorem B3939155 : Blo 1750576 3939155 := bstep (se 1 (by rfl) ⟨2954366, by rfl⟩ : syracuseStep 3939155 = 5908733) B5908733
theorem B5610323 : Blo 1750576 5610323 := bstep (se 1 (by rfl) ⟨4207742, by rfl⟩ : syracuseStep 5610323 = 8415485) B8415485
theorem B1751899 : Blo 1750576 1751899 := bstep (se 1 (by rfl) ⟨1313924, by rfl⟩ : syracuseStep 1751899 = 2627849) B2627849
theorem B2628443 : Blo 1750576 2628443 := bstep (se 1 (by rfl) ⟨1971332, by rfl⟩ : syracuseStep 2628443 = 3942665) B3942665
theorem B1751967 : Blo 1750576 1751967 := bstep (se 1 (by rfl) ⟨1313975, by rfl⟩ : syracuseStep 1751967 = 2627951) B2627951
theorem B2628587 : Blo 1750576 2628587 := bstep (se 1 (by rfl) ⟨1971440, by rfl⟩ : syracuseStep 2628587 = 3942881) B3942881
theorem B1752111 : Blo 1750576 1752111 := bstep (se 1 (by rfl) ⟨1314083, by rfl⟩ : syracuseStep 1752111 = 2628167) B2628167
theorem B1752135 : Blo 1750576 1752135 := bstep (se 1 (by rfl) ⟨1314101, by rfl⟩ : syracuseStep 1752135 = 2628203) B2628203
theorem B2628791 : Blo 1750576 2628791 := bstep (se 1 (by rfl) ⟨1971593, by rfl⟩ : syracuseStep 2628791 = 3943187) B3943187
theorem B1752287 : Blo 1750576 1752287 := bstep (se 1 (by rfl) ⟨1314215, by rfl⟩ : syracuseStep 1752287 = 2628431) B2628431
theorem B3939695 : Blo 1750576 3939695 := bstep (se 1 (by rfl) ⟨2954771, by rfl⟩ : syracuseStep 3939695 = 5909543) B5909543
theorem B2956655 : Blo 1750576 2956655 := bstep (se 1 (by rfl) ⟨2217491, by rfl⟩ : syracuseStep 2956655 = 4434983) B4434983
theorem B15170935 : Blo 1750576 15170935 := bstep (se 1 (by rfl) ⟨11378201, by rfl⟩ : syracuseStep 15170935 = 22756403) B22756403
theorem B9977255 : Blo 1750576 9977255 := bstep (se 1 (by rfl) ⟨7482941, by rfl⟩ : syracuseStep 9977255 = 14965883) B14965883
theorem B1752551 : Blo 1750576 1752551 := bstep (se 1 (by rfl) ⟨1314413, by rfl⟩ : syracuseStep 1752551 = 2628827) B2628827
theorem B13303277 : Blo 1750576 13303277 := bstep (se 3 (by rfl) ⟨2494364, by rfl⟩ : syracuseStep 13303277 = 4988729) B4988729
theorem B3325531 : Blo 1750576 3325531 := bstep (se 1 (by rfl) ⟨2494148, by rfl⟩ : syracuseStep 3325531 = 4988297) B4988297
theorem B2956891 : Blo 1750576 2956891 := bstep (se 1 (by rfl) ⟨2217668, by rfl⟩ : syracuseStep 2956891 = 4435337) B4435337
theorem B3939983 : Blo 1750576 3939983 := bstep (se 1 (by rfl) ⟨2954987, by rfl⟩ : syracuseStep 3939983 = 5909975) B5909975
theorem B6315707 : Blo 1750576 6315707 := bstep (se 1 (by rfl) ⟨4736780, by rfl⟩ : syracuseStep 6315707 = 9473561) B9473561
theorem B3940073 : Blo 1750576 3940073 := bstep (se 2 (by rfl) ⟨1477527, by rfl⟩ : syracuseStep 3940073 = 2955055) B2955055
theorem B2957033 : Blo 1750576 2957033 := bstep (se 2 (by rfl) ⟨1108887, by rfl⟩ : syracuseStep 2957033 = 2217775) B2217775
theorem B9977687 : Blo 1750576 9977687 := bstep (se 1 (by rfl) ⟨7483265, by rfl⟩ : syracuseStep 9977687 = 14966531) B14966531
theorem B33661007 : Blo 1750576 33661007 := bstep (se 1 (by rfl) ⟨25245755, by rfl⟩ : syracuseStep 33661007 = 50491511) B50491511
theorem B3940559 : Blo 1750576 3940559 := bstep (se 1 (by rfl) ⟨2955419, by rfl⟩ : syracuseStep 3940559 = 5910839) B5910839
theorem B6742271 : Blo 1750576 6742271 := bstep (se 1 (by rfl) ⟨5056703, by rfl⟩ : syracuseStep 6742271 = 10113407) B10113407
theorem B3940703 : Blo 1750576 3940703 := bstep (se 1 (by rfl) ⟨2955527, by rfl⟩ : syracuseStep 3940703 = 5911055) B5911055
theorem B13295987 : Blo 1750576 13295987 := bstep (se 1 (by rfl) ⟨9971990, by rfl⟩ : syracuseStep 13295987 = 19943981) B19943981
theorem B6652489 : Blo 1750576 6652489 := bstep (se 2 (by rfl) ⟨2494683, by rfl⟩ : syracuseStep 6652489 = 4989367) B4989367
theorem B33686225 : Blo 1750576 33686225 := bstep (se 2 (by rfl) ⟨12632334, by rfl⟩ : syracuseStep 33686225 = 25264669) B25264669
theorem B4432603 : Blo 1750576 4432603 := bstep (se 1 (by rfl) ⟨3324452, by rfl⟩ : syracuseStep 4432603 = 6648905) B6648905
theorem B3326761 : Blo 1750576 3326761 := bstep (se 2 (by rfl) ⟨1247535, by rfl⟩ : syracuseStep 3326761 = 2495071) B2495071
theorem B35971897 : Blo 1750576 35971897 := bstep (se 2 (by rfl) ⟨13489461, by rfl⟩ : syracuseStep 35971897 = 26978923) B26978923
theorem B7586855 : Blo 1750576 7586855 := bstep (se 1 (by rfl) ⟨5690141, by rfl⟩ : syracuseStep 7586855 = 11380283) B11380283
theorem B3941423 : Blo 1750576 3941423 := bstep (se 1 (by rfl) ⟨2956067, by rfl⟩ : syracuseStep 3941423 = 5912135) B5912135
theorem B15983689 : Blo 1750576 15983689 := bstep (se 2 (by rfl) ⟨5993883, by rfl⟩ : syracuseStep 15983689 = 11987767) B11987767
theorem B3794087 : Blo 1750576 3794087 := bstep (se 1 (by rfl) ⟨2845565, by rfl⟩ : syracuseStep 3794087 = 5691131) B5691131
theorem B3155483 : Blo 1750576 3155483 := bstep (se 1 (by rfl) ⟨2366612, by rfl⟩ : syracuseStep 3155483 = 4733225) B4733225
theorem B7988831 : Blo 1750576 7988831 := bstep (se 1 (by rfl) ⟨5991623, by rfl⟩ : syracuseStep 7988831 = 11983247) B11983247
theorem B3942071 : Blo 1750576 3942071 := bstep (se 1 (by rfl) ⟨2956553, by rfl⟩ : syracuseStep 3942071 = 5913107) B5913107
theorem B22742795 : Blo 1750576 22742795 := bstep (se 1 (by rfl) ⟨17057096, by rfl⟩ : syracuseStep 22742795 = 34114193) B34114193
theorem B6653735 : Blo 1750576 6653735 := bstep (se 1 (by rfl) ⟨4990301, by rfl⟩ : syracuseStep 6653735 = 9980603) B9980603
theorem B20227913 : Blo 1750576 20227913 := bstep (se 2 (by rfl) ⟨7585467, by rfl⟩ : syracuseStep 20227913 = 15170935) B15170935
theorem B1869851 : Blo 1750576 1869851 := bstep (se 1 (by rfl) ⟨1402388, by rfl⟩ : syracuseStep 1869851 = 2804777) B2804777
theorem B4434041 : Blo 1750576 4434041 := bstep (se 2 (by rfl) ⟨1662765, by rfl⟩ : syracuseStep 4434041 = 3325531) B3325531
theorem B3942521 : Blo 1750576 3942521 := bstep (se 2 (by rfl) ⟨1478445, by rfl⟩ : syracuseStep 3942521 = 2956891) B2956891
theorem B2957303 : Blo 1750576 2957303 := bstep (se 1 (by rfl) ⟨2217977, by rfl⟩ : syracuseStep 2957303 = 4435955) B4435955
theorem B21317843 : Blo 1750576 21317843 := bstep (se 1 (by rfl) ⟨15988382, by rfl⟩ : syracuseStep 21317843 = 31976765) B31976765
theorem B22448461 : Blo 1750576 22448461 := bstep (se 3 (by rfl) ⟨4209086, by rfl⟩ : syracuseStep 22448461 = 8418173) B8418173
theorem B8415713 : Blo 1750576 8415713 := bstep (se 2 (by rfl) ⟨3155892, by rfl⟩ : syracuseStep 8415713 = 6311785) B6311785
theorem B7482617 : Blo 1750576 7482617 := bstep (se 2 (by rfl) ⟨2805981, by rfl⟩ : syracuseStep 7482617 = 5611963) B5611963
theorem B22441697 : Blo 1750576 22441697 := bstep (se 2 (by rfl) ⟨8415636, by rfl⟩ : syracuseStep 22441697 = 16831273) B16831273
theorem B21589753 : Blo 1750576 21589753 := bstep (se 2 (by rfl) ⟨8096157, by rfl⟩ : syracuseStep 21589753 = 16192315) B16192315
theorem B1969915 : Blo 1750576 1969915 := bstep (se 1 (by rfl) ⟨1477436, by rfl⟩ : syracuseStep 1969915 = 2954873) B2954873
theorem B3739463 : Blo 1750576 3739463 := bstep (se 1 (by rfl) ⟨2804597, by rfl⟩ : syracuseStep 3739463 = 5609195) B5609195
theorem B4050811 : Blo 1750576 4050811 := bstep (se 1 (by rfl) ⟨3038108, by rfl⟩ : syracuseStep 4050811 = 6076217) B6076217
theorem B4206473 : Blo 1750576 4206473 := bstep (se 2 (by rfl) ⟨1577427, by rfl⟩ : syracuseStep 4206473 = 3154855) B3154855
theorem B2805815 : Blo 1750576 2805815 := bstep (se 1 (by rfl) ⟨2104361, by rfl⟩ : syracuseStep 2805815 = 4208723) B4208723
theorem B1970239 : Blo 1750576 1970239 := bstep (se 1 (by rfl) ⟨1477679, by rfl⟩ : syracuseStep 1970239 = 2955359) B2955359
theorem B21311615 : Blo 1750576 21311615 := bstep (se 1 (by rfl) ⟨15983711, by rfl⟩ : syracuseStep 21311615 = 31967423) B31967423
theorem B31969475 : Blo 1750576 31969475 := bstep (se 1 (by rfl) ⟨23977106, by rfl⟩ : syracuseStep 31969475 = 47954213) B47954213
theorem B7098587 : Blo 1750576 7098587 := bstep (se 1 (by rfl) ⟨5323940, by rfl⟩ : syracuseStep 7098587 = 10647881) B10647881
theorem B2626103 : Blo 1750576 2626103 := bstep (se 1 (by rfl) ⟨1969577, by rfl⟩ : syracuseStep 2626103 = 3939155) B3939155
theorem B3740215 : Blo 1750576 3740215 := bstep (se 1 (by rfl) ⟨2805161, by rfl⟩ : syracuseStep 3740215 = 5610323) B5610323
theorem B5911433 : Blo 1750576 5911433 := bstep (se 2 (by rfl) ⟨2216787, by rfl⟩ : syracuseStep 5911433 = 4433575) B4433575
theorem B2626463 : Blo 1750576 2626463 := bstep (se 1 (by rfl) ⟨1969847, by rfl⟩ : syracuseStep 2626463 = 3939695) B3939695
theorem B1971103 : Blo 1750576 1971103 := bstep (se 1 (by rfl) ⟨1478327, by rfl⟩ : syracuseStep 1971103 = 2956655) B2956655
theorem B3994535 : Blo 1750576 3994535 := bstep (se 1 (by rfl) ⟨2995901, by rfl⟩ : syracuseStep 3994535 = 5991803) B5991803
theorem B8868851 : Blo 1750576 8868851 := bstep (se 1 (by rfl) ⟨6651638, by rfl⟩ : syracuseStep 8868851 = 13303277) B13303277
theorem B2626655 : Blo 1750576 2626655 := bstep (se 1 (by rfl) ⟨1969991, by rfl⟩ : syracuseStep 2626655 = 3939983) B3939983
theorem B2626715 : Blo 1750576 2626715 := bstep (se 1 (by rfl) ⟨1970036, by rfl⟩ : syracuseStep 2626715 = 3940073) B3940073
theorem B1971355 : Blo 1750576 1971355 := bstep (se 1 (by rfl) ⟨1478516, by rfl⟩ : syracuseStep 1971355 = 2957033) B2957033
theorem B4494703 : Blo 1750576 4494703 := bstep (se 1 (by rfl) ⟨3371027, by rfl⟩ : syracuseStep 4494703 = 6742055) B6742055
theorem B3741103 : Blo 1750576 3741103 := bstep (se 1 (by rfl) ⟨2805827, by rfl⟩ : syracuseStep 3741103 = 5611655) B5611655
theorem B7099919 : Blo 1750576 7099919 := bstep (se 1 (by rfl) ⟨5324939, by rfl⟩ : syracuseStep 7099919 = 10649879) B10649879
theorem B55383587 : Blo 1750576 55383587 := bstep (se 1 (by rfl) ⟨41537690, by rfl⟩ : syracuseStep 55383587 = 83075381) B83075381
theorem B4986451 : Blo 1750576 4986451 := bstep (se 1 (by rfl) ⟨3739838, by rfl⟩ : syracuseStep 4986451 = 7479677) B7479677
theorem B1750619 : Blo 1750576 1750619 := bstep (se 1 (by rfl) ⟨1312964, by rfl⟩ : syracuseStep 1750619 = 2625929) B2625929
theorem B2528905 : Blo 1750576 2528905 := bstep (se 2 (by rfl) ⟨948339, by rfl⟩ : syracuseStep 2528905 = 1896679) B1896679
theorem B1750683 : Blo 1750576 1750683 := bstep (se 1 (by rfl) ⟨1313012, by rfl⟩ : syracuseStep 1750683 = 2626025) B2626025
theorem B3741403 : Blo 1750576 3741403 := bstep (se 1 (by rfl) ⟨2806052, by rfl⟩ : syracuseStep 3741403 = 5612105) B5612105
theorem B5912297 : Blo 1750576 5912297 := bstep (se 2 (by rfl) ⟨2217111, by rfl⟩ : syracuseStep 5912297 = 4434223) B4434223
theorem B1750767 : Blo 1750576 1750767 := bstep (se 1 (by rfl) ⟨1313075, by rfl⟩ : syracuseStep 1750767 = 2626151) B2626151
theorem B7689979 : Blo 1750576 7689979 := bstep (se 1 (by rfl) ⟨5767484, by rfl⟩ : syracuseStep 7689979 = 11534969) B11534969
theorem B1750855 : Blo 1750576 1750855 := bstep (se 1 (by rfl) ⟨1313141, by rfl⟩ : syracuseStep 1750855 = 2626283) B2626283
theorem B2627399 : Blo 1750576 2627399 := bstep (se 1 (by rfl) ⟨1970549, by rfl⟩ : syracuseStep 2627399 = 3941099) B3941099
theorem B2103131 : Blo 1750576 2103131 := bstep (se 1 (by rfl) ⟨1577348, by rfl⟩ : syracuseStep 2103131 = 3154697) B3154697
theorem B1750875 : Blo 1750576 1750875 := bstep (se 1 (by rfl) ⟨1313156, by rfl⟩ : syracuseStep 1750875 = 2626313) B2626313
theorem B1750943 : Blo 1750576 1750943 := bstep (se 1 (by rfl) ⟨1313207, by rfl⟩ : syracuseStep 1750943 = 2626415) B2626415
theorem B5609375 : Blo 1750576 5609375 := bstep (se 1 (by rfl) ⟨4207031, by rfl⟩ : syracuseStep 5609375 = 8414063) B8414063
theorem B1751111 : Blo 1750576 1751111 := bstep (se 1 (by rfl) ⟨1313333, by rfl⟩ : syracuseStep 1751111 = 2626667) B2626667
theorem B19191905 : Blo 1750576 19191905 := bstep (se 2 (by rfl) ⟨7196964, by rfl⟩ : syracuseStep 19191905 = 14393929) B14393929
theorem B4208779 : Blo 1750576 4208779 := bstep (se 1 (by rfl) ⟨3156584, by rfl⟩ : syracuseStep 4208779 = 6313169) B6313169
theorem B14203073 : Blo 1750576 14203073 := bstep (se 2 (by rfl) ⟨5326152, by rfl⟩ : syracuseStep 14203073 = 10652305) B10652305
theorem B1751271 : Blo 1750576 1751271 := bstep (se 1 (by rfl) ⟨1313453, by rfl⟩ : syracuseStep 1751271 = 2626907) B2626907
theorem B8870147 : Blo 1750576 8870147 := bstep (se 1 (by rfl) ⟨6652610, by rfl⟩ : syracuseStep 8870147 = 13305221) B13305221
theorem B4266271 : Blo 1750576 4266271 := bstep (se 1 (by rfl) ⟨3199703, by rfl⟩ : syracuseStep 4266271 = 6399407) B6399407
theorem B1751455 : Blo 1750576 1751455 := bstep (se 1 (by rfl) ⟨1313591, by rfl⟩ : syracuseStep 1751455 = 2627183) B2627183
theorem B2627999 : Blo 1750576 2627999 := bstep (se 1 (by rfl) ⟨1970999, by rfl⟩ : syracuseStep 2627999 = 3941999) B3941999
theorem B11221415 : Blo 1750576 11221415 := bstep (se 1 (by rfl) ⟨8416061, by rfl⟩ : syracuseStep 11221415 = 16832123) B16832123
theorem B1751503 : Blo 1750576 1751503 := bstep (se 1 (by rfl) ⟨1313627, by rfl⟩ : syracuseStep 1751503 = 2627255) B2627255
theorem B13294043 : Blo 1750576 13294043 := bstep (se 1 (by rfl) ⟨9970532, by rfl⟩ : syracuseStep 13294043 = 19941065) B19941065
theorem B1751527 : Blo 1750576 1751527 := bstep (se 1 (by rfl) ⟨1313645, by rfl⟩ : syracuseStep 1751527 = 2627291) B2627291
theorem B2628071 : Blo 1750576 2628071 := bstep (se 1 (by rfl) ⟨1971053, by rfl⟩ : syracuseStep 2628071 = 3942107) B3942107
theorem B16841267 : Blo 1750576 16841267 := bstep (se 1 (by rfl) ⟨12630950, by rfl⟩ : syracuseStep 16841267 = 25261901) B25261901
theorem B8870471 : Blo 1750576 8870471 := bstep (se 1 (by rfl) ⟨6652853, by rfl⟩ : syracuseStep 8870471 = 13305707) B13305707
theorem B14957135 : Blo 1750576 14957135 := bstep (se 1 (by rfl) ⟨11217851, by rfl⟩ : syracuseStep 14957135 = 22435703) B22435703
theorem B1751643 : Blo 1750576 1751643 := bstep (se 1 (by rfl) ⟨1313732, by rfl⟩ : syracuseStep 1751643 = 2627465) B2627465
theorem B3324559 : Blo 1750576 3324559 := bstep (se 1 (by rfl) ⟨2493419, by rfl⟩ : syracuseStep 3324559 = 4986839) B4986839
theorem B1751711 : Blo 1750576 1751711 := bstep (se 1 (by rfl) ⟨1313783, by rfl⟩ : syracuseStep 1751711 = 2627567) B2627567
theorem B3324719 : Blo 1750576 3324719 := bstep (se 1 (by rfl) ⟨2493539, by rfl⟩ : syracuseStep 3324719 = 4987079) B4987079
theorem B23968561 : Blo 1750576 23968561 := bstep (se 2 (by rfl) ⟨8988210, by rfl⟩ : syracuseStep 23968561 = 17976421) B17976421
theorem B1751879 : Blo 1750576 1751879 := bstep (se 1 (by rfl) ⟨1313909, by rfl⟩ : syracuseStep 1751879 = 2627819) B2627819
theorem B1751919 : Blo 1750576 1751919 := bstep (se 1 (by rfl) ⟨1313939, by rfl⟩ : syracuseStep 1751919 = 2627879) B2627879
theorem B1751975 : Blo 1750576 1751975 := bstep (se 1 (by rfl) ⟨1313981, by rfl⟩ : syracuseStep 1751975 = 2627963) B2627963
theorem B1752155 : Blo 1750576 1752155 := bstep (se 1 (by rfl) ⟨1314116, by rfl⟩ : syracuseStep 1752155 = 2628233) B2628233
theorem B1752271 : Blo 1750576 1752271 := bstep (se 1 (by rfl) ⟨1314203, by rfl⟩ : syracuseStep 1752271 = 2628407) B2628407
theorem B2628815 : Blo 1750576 2628815 := bstep (se 1 (by rfl) ⟨1971611, by rfl⟩ : syracuseStep 2628815 = 3943223) B3943223
theorem B3325151 : Blo 1750576 3325151 := bstep (se 1 (by rfl) ⟨2493863, by rfl⟩ : syracuseStep 3325151 = 4987727) B4987727
theorem B1752295 : Blo 1750576 1752295 := bstep (se 1 (by rfl) ⟨1314221, by rfl⟩ : syracuseStep 1752295 = 2628443) B2628443
theorem B1752391 : Blo 1750576 1752391 := bstep (se 1 (by rfl) ⟨1314293, by rfl⟩ : syracuseStep 1752391 = 2628587) B2628587
theorem B13295015 : Blo 1750576 13295015 := bstep (se 1 (by rfl) ⟨9971261, by rfl⟩ : syracuseStep 13295015 = 19942523) B19942523
theorem B5914025 : Blo 1750576 5914025 := bstep (se 2 (by rfl) ⟨2217759, by rfl⟩ : syracuseStep 5914025 = 4435519) B4435519
theorem B1752527 : Blo 1750576 1752527 := bstep (se 1 (by rfl) ⟨1314395, by rfl⟩ : syracuseStep 1752527 = 2628791) B2628791
theorem B6651503 : Blo 1750576 6651503 := bstep (se 1 (by rfl) ⟨4988627, by rfl⟩ : syracuseStep 6651503 = 9977255) B9977255
theorem B3940127 : Blo 1750576 3940127 := bstep (se 1 (by rfl) ⟨2955095, by rfl⟩ : syracuseStep 3940127 = 5910191) B5910191
theorem B2957087 : Blo 1750576 2957087 := bstep (se 1 (by rfl) ⟨2217815, by rfl⟩ : syracuseStep 2957087 = 4435631) B4435631
theorem B4210471 : Blo 1750576 4210471 := bstep (se 1 (by rfl) ⟨3157853, by rfl⟩ : syracuseStep 4210471 = 6315707) B6315707
theorem B8871767 : Blo 1750576 8871767 := bstep (se 1 (by rfl) ⟨6653825, by rfl⟩ : syracuseStep 8871767 = 13307651) B13307651
theorem B6651791 : Blo 1750576 6651791 := bstep (se 1 (by rfl) ⟨4988843, by rfl⟩ : syracuseStep 6651791 = 9977687) B9977687
theorem B3940343 : Blo 1750576 3940343 := bstep (se 1 (by rfl) ⟨2955257, by rfl⟩ : syracuseStep 3940343 = 5910515) B5910515
theorem B8863991 : Blo 1750576 8863991 := bstep (se 1 (by rfl) ⟨6647993, by rfl⟩ : syracuseStep 8863991 = 13295987) B13295987
theorem B3940955 : Blo 1750576 3940955 := bstep (se 1 (by rfl) ⟨2955716, by rfl⟩ : syracuseStep 3940955 = 5911433) B5911433
theorem B22446821 : Blo 1750576 22446821 := bstep (se 4 (by rfl) ⟨2104389, by rfl⟩ : syracuseStep 22446821 = 4208779) B4208779
theorem B4432745 : Blo 1750576 4432745 := bstep (se 2 (by rfl) ⟨1662279, by rfl⟩ : syracuseStep 4432745 = 3324559) B3324559
theorem B36922391 : Blo 1750576 36922391 := bstep (se 1 (by rfl) ⟨27691793, by rfl⟩ : syracuseStep 36922391 = 55383587) B55383587
theorem B5325887 : Blo 1750576 5325887 := bstep (se 1 (by rfl) ⟨3994415, by rfl⟩ : syracuseStep 5325887 = 7988831) B7988831
theorem B31958081 : Blo 1750576 31958081 := bstep (se 2 (by rfl) ⟨11984280, by rfl⟩ : syracuseStep 31958081 = 23968561) B23968561
theorem B3941531 : Blo 1750576 3941531 := bstep (se 1 (by rfl) ⟨2956148, by rfl⟩ : syracuseStep 3941531 = 5912297) B5912297
theorem B13485275 : Blo 1750576 13485275 := bstep (se 1 (by rfl) ⟨10113956, by rfl⟩ : syracuseStep 13485275 = 20227913) B20227913
theorem B7480943 : Blo 1750576 7480943 := bstep (se 1 (by rfl) ⟨5610707, by rfl⟩ : syracuseStep 7480943 = 11221415) B11221415
theorem B9971423 : Blo 1750576 9971423 := bstep (se 1 (by rfl) ⟨7478567, by rfl⟩ : syracuseStep 9971423 = 14957135) B14957135
theorem B3942683 : Blo 1750576 3942683 := bstep (se 1 (by rfl) ⟨2957012, by rfl⟩ : syracuseStep 3942683 = 5914025) B5914025
theorem B5613961 : Blo 1750576 5613961 := bstep (se 2 (by rfl) ⟨2105235, by rfl⟩ : syracuseStep 5613961 = 4210471) B4210471
theorem B4434335 : Blo 1750576 4434335 := bstep (se 1 (by rfl) ⟨3325751, by rfl⟩ : syracuseStep 4434335 = 6651503) B6651503
theorem B10652093 : Blo 1750576 10652093 := bstep (se 3 (by rfl) ⟨1997267, by rfl⟩ : syracuseStep 10652093 = 3994535) B3994535
theorem B14961131 : Blo 1750576 14961131 := bstep (se 1 (by rfl) ⟨11220848, by rfl⟩ : syracuseStep 14961131 = 22441697) B22441697
theorem B5401081 : Blo 1750576 5401081 := bstep (se 2 (by rfl) ⟨2025405, by rfl⟩ : syracuseStep 5401081 = 4050811) B4050811
theorem B2492975 : Blo 1750576 2492975 := bstep (se 1 (by rfl) ⟨1869731, by rfl⟩ : syracuseStep 2492975 = 3739463) B3739463
theorem B2804315 : Blo 1750576 2804315 := bstep (se 1 (by rfl) ⟨2103236, by rfl⟩ : syracuseStep 2804315 = 4206473) B4206473
theorem B4434527 : Blo 1750576 4434527 := bstep (se 1 (by rfl) ⟨3325895, by rfl⟩ : syracuseStep 4434527 = 6651791) B6651791
theorem B1870543 : Blo 1750576 1870543 := bstep (se 1 (by rfl) ⟨1402907, by rfl⟩ : syracuseStep 1870543 = 2805815) B2805815
theorem B22440671 : Blo 1750576 22440671 := bstep (se 1 (by rfl) ⟨16830503, by rfl⟩ : syracuseStep 22440671 = 33661007) B33661007
theorem B14207743 : Blo 1750576 14207743 := bstep (se 1 (by rfl) ⟨10655807, by rfl⟩ : syracuseStep 14207743 = 21311615) B21311615
theorem B5688361 : Blo 1750576 5688361 := bstep (se 2 (by rfl) ⟨2133135, by rfl⟩ : syracuseStep 5688361 = 4266271) B4266271
theorem B22457483 : Blo 1750576 22457483 := bstep (se 1 (by rfl) ⟨16843112, by rfl⟩ : syracuseStep 22457483 = 33686225) B33686225
theorem B37874861 : Blo 1750576 37874861 := bstep (se 3 (by rfl) ⟨7101536, by rfl⟩ : syracuseStep 37874861 = 14203073) B14203073
theorem B56847581 : Blo 1750576 56847581 := bstep (se 3 (by rfl) ⟨10658921, by rfl⟩ : syracuseStep 56847581 = 21317843) B21317843
theorem B8867069 : Blo 1750576 8867069 := bstep (se 3 (by rfl) ⟨1662575, by rfl⟩ : syracuseStep 8867069 = 3325151) B3325151
theorem B5057903 : Blo 1750576 5057903 := bstep (se 1 (by rfl) ⟨3793427, by rfl⟩ : syracuseStep 5057903 = 7586855) B7586855
theorem B5910137 : Blo 1750576 5910137 := bstep (se 2 (by rfl) ⟨2216301, by rfl⟩ : syracuseStep 5910137 = 4432603) B4432603
theorem B4435681 : Blo 1750576 4435681 := bstep (se 2 (by rfl) ⟨1663380, by rfl⟩ : syracuseStep 4435681 = 3326761) B3326761
theorem B4435823 : Blo 1750576 4435823 := bstep (se 1 (by rfl) ⟨3326867, by rfl⟩ : syracuseStep 4435823 = 6653735) B6653735
theorem B3739583 : Blo 1750576 3739583 := bstep (se 1 (by rfl) ⟨2804687, by rfl⟩ : syracuseStep 3739583 = 5609375) B5609375
theorem B41013221 : Blo 1750576 41013221 := bstep (se 4 (by rfl) ⟨3844989, by rfl⟩ : syracuseStep 41013221 = 7689979) B7689979
theorem B21311585 : Blo 1750576 21311585 := bstep (se 2 (by rfl) ⟨7991844, by rfl⟩ : syracuseStep 21311585 = 15983689) B15983689
theorem B11227511 : Blo 1750576 11227511 := bstep (se 1 (by rfl) ⟨8420633, by rfl⟩ : syracuseStep 11227511 = 16841267) B16841267
theorem B5992937 : Blo 1750576 5992937 := bstep (se 2 (by rfl) ⟨2247351, by rfl⟩ : syracuseStep 5992937 = 4494703) B4494703
theorem B2216479 : Blo 1750576 2216479 := bstep (se 1 (by rfl) ⟨1662359, by rfl⟩ : syracuseStep 2216479 = 3324719) B3324719
theorem B6648601 : Blo 1750576 6648601 := bstep (se 2 (by rfl) ⟨2493225, by rfl⟩ : syracuseStep 6648601 = 4986451) B4986451
theorem B3371873 : Blo 1750576 3371873 := bstep (se 2 (by rfl) ⟨1264452, by rfl⟩ : syracuseStep 3371873 = 2528905) B2528905
theorem B5608349 : Blo 1750576 5608349 := bstep (se 3 (by rfl) ⟨1051565, by rfl⟩ : syracuseStep 5608349 = 2103131) B2103131
theorem B2626553 : Blo 1750576 2626553 := bstep (se 2 (by rfl) ⟨984957, by rfl⟩ : syracuseStep 2626553 = 1969915) B1969915
theorem B2626751 : Blo 1750576 2626751 := bstep (se 1 (by rfl) ⟨1970063, by rfl⟩ : syracuseStep 2626751 = 3940127) B3940127
theorem B1971391 : Blo 1750576 1971391 := bstep (se 1 (by rfl) ⟨1478543, by rfl⟩ : syracuseStep 1971391 = 2957087) B2957087
theorem B2626895 : Blo 1750576 2626895 := bstep (se 1 (by rfl) ⟨1970171, by rfl⟩ : syracuseStep 2626895 = 3940343) B3940343
theorem B1971535 : Blo 1750576 1971535 := bstep (se 1 (by rfl) ⟨1478651, by rfl⟩ : syracuseStep 1971535 = 2957303) B2957303
theorem B4986269 : Blo 1750576 4986269 := bstep (se 3 (by rfl) ⟨934925, by rfl⟩ : syracuseStep 4986269 = 1869851) B1869851
theorem B2626985 : Blo 1750576 2626985 := bstep (se 2 (by rfl) ⟨985119, by rfl⟩ : syracuseStep 2626985 = 1970239) B1970239
theorem B21312983 : Blo 1750576 21312983 := bstep (se 1 (by rfl) ⟨15984737, by rfl⟩ : syracuseStep 21312983 = 31969475) B31969475
theorem B2627039 : Blo 1750576 2627039 := bstep (se 1 (by rfl) ⟨1970279, by rfl⟩ : syracuseStep 2627039 = 3940559) B3940559
theorem B4732391 : Blo 1750576 4732391 := bstep (se 1 (by rfl) ⟨3549293, by rfl⟩ : syracuseStep 4732391 = 7098587) B7098587
theorem B4494847 : Blo 1750576 4494847 := bstep (se 1 (by rfl) ⟨3371135, by rfl⟩ : syracuseStep 4494847 = 6742271) B6742271
theorem B2627135 : Blo 1750576 2627135 := bstep (se 1 (by rfl) ⟨1970351, by rfl⟩ : syracuseStep 2627135 = 3940703) B3940703
theorem B1750735 : Blo 1750576 1750735 := bstep (se 1 (by rfl) ⟨1313051, by rfl⟩ : syracuseStep 1750735 = 2626103) B2626103
theorem B29931281 : Blo 1750576 29931281 := bstep (se 2 (by rfl) ⟨11224230, by rfl⟩ : syracuseStep 29931281 = 22448461) B22448461
theorem B1750975 : Blo 1750576 1750975 := bstep (se 1 (by rfl) ⟨1313231, by rfl⟩ : syracuseStep 1750975 = 2626463) B2626463
theorem B5912567 : Blo 1750576 5912567 := bstep (se 1 (by rfl) ⟨4434425, by rfl⟩ : syracuseStep 5912567 = 8868851) B8868851
theorem B2627615 : Blo 1750576 2627615 := bstep (se 1 (by rfl) ⟨1970711, by rfl⟩ : syracuseStep 2627615 = 3941423) B3941423
theorem B1751103 : Blo 1750576 1751103 := bstep (se 1 (by rfl) ⟨1313327, by rfl⟩ : syracuseStep 1751103 = 2626655) B2626655
theorem B4986953 : Blo 1750576 4986953 := bstep (se 2 (by rfl) ⟨1870107, by rfl⟩ : syracuseStep 4986953 = 3740215) B3740215
theorem B8869985 : Blo 1750576 8869985 := bstep (se 2 (by rfl) ⟨3326244, by rfl⟩ : syracuseStep 8869985 = 6652489) B6652489
theorem B1751143 : Blo 1750576 1751143 := bstep (se 1 (by rfl) ⟨1313357, by rfl⟩ : syracuseStep 1751143 = 2626715) B2626715
theorem B2529391 : Blo 1750576 2529391 := bstep (se 1 (by rfl) ⟨1897043, by rfl⟩ : syracuseStep 2529391 = 3794087) B3794087
theorem B4733279 : Blo 1750576 4733279 := bstep (se 1 (by rfl) ⟨3549959, by rfl⟩ : syracuseStep 4733279 = 7099919) B7099919
theorem B2103655 : Blo 1750576 2103655 := bstep (se 1 (by rfl) ⟨1577741, by rfl⟩ : syracuseStep 2103655 = 3155483) B3155483
theorem B47962529 : Blo 1750576 47962529 := bstep (se 2 (by rfl) ⟨17985948, by rfl⟩ : syracuseStep 47962529 = 35971897) B35971897
theorem B2628047 : Blo 1750576 2628047 := bstep (se 1 (by rfl) ⟨1971035, by rfl⟩ : syracuseStep 2628047 = 3942071) B3942071
theorem B15161863 : Blo 1750576 15161863 := bstep (se 1 (by rfl) ⟨11371397, by rfl⟩ : syracuseStep 15161863 = 22742795) B22742795
theorem B2628137 : Blo 1750576 2628137 := bstep (se 2 (by rfl) ⟨985551, by rfl⟩ : syracuseStep 2628137 = 1971103) B1971103
theorem B1751599 : Blo 1750576 1751599 := bstep (se 1 (by rfl) ⟨1313699, by rfl⟩ : syracuseStep 1751599 = 2627399) B2627399
theorem B12794603 : Blo 1750576 12794603 := bstep (se 1 (by rfl) ⟨9595952, by rfl⟩ : syracuseStep 12794603 = 19191905) B19191905
theorem B2956027 : Blo 1750576 2956027 := bstep (se 1 (by rfl) ⟨2217020, by rfl⟩ : syracuseStep 2956027 = 4434041) B4434041
theorem B2628347 : Blo 1750576 2628347 := bstep (se 1 (by rfl) ⟨1971260, by rfl⟩ : syracuseStep 2628347 = 3942521) B3942521
theorem B5913431 : Blo 1750576 5913431 := bstep (se 1 (by rfl) ⟨4435073, by rfl⟩ : syracuseStep 5913431 = 8870147) B8870147
theorem B2628473 : Blo 1750576 2628473 := bstep (se 2 (by rfl) ⟨985677, by rfl⟩ : syracuseStep 2628473 = 1971355) B1971355
theorem B1751999 : Blo 1750576 1751999 := bstep (se 1 (by rfl) ⟨1313999, by rfl⟩ : syracuseStep 1751999 = 2627999) B2627999
theorem B8862695 : Blo 1750576 8862695 := bstep (se 1 (by rfl) ⟨6647021, by rfl⟩ : syracuseStep 8862695 = 13294043) B13294043
theorem B5610475 : Blo 1750576 5610475 := bstep (se 1 (by rfl) ⟨4207856, by rfl⟩ : syracuseStep 5610475 = 8415713) B8415713
theorem B1752047 : Blo 1750576 1752047 := bstep (se 1 (by rfl) ⟨1314035, by rfl⟩ : syracuseStep 1752047 = 2628071) B2628071
theorem B5913647 : Blo 1750576 5913647 := bstep (se 1 (by rfl) ⟨4435235, by rfl⟩ : syracuseStep 5913647 = 8870471) B8870471
theorem B4988137 : Blo 1750576 4988137 := bstep (se 2 (by rfl) ⟨1870551, by rfl⟩ : syracuseStep 4988137 = 3741103) B3741103
theorem B1752543 : Blo 1750576 1752543 := bstep (se 1 (by rfl) ⟨1314407, by rfl⟩ : syracuseStep 1752543 = 2628815) B2628815
theorem B4988411 : Blo 1750576 4988411 := bstep (se 1 (by rfl) ⟨3741308, by rfl⟩ : syracuseStep 4988411 = 7482617) B7482617
theorem B8863343 : Blo 1750576 8863343 := bstep (se 1 (by rfl) ⟨6647507, by rfl⟩ : syracuseStep 8863343 = 13295015) B13295015
theorem B4988537 : Blo 1750576 4988537 := bstep (se 2 (by rfl) ⟨1870701, by rfl⟩ : syracuseStep 4988537 = 3741403) B3741403
theorem B28786337 : Blo 1750576 28786337 := bstep (se 2 (by rfl) ⟨10794876, by rfl⟩ : syracuseStep 28786337 = 21589753) B21589753
theorem B5914511 : Blo 1750576 5914511 := bstep (se 1 (by rfl) ⟨4435883, by rfl⟩ : syracuseStep 5914511 = 8871767) B8871767
theorem B7201441 : Blo 1750576 7201441 := bstep (se 2 (by rfl) ⟨2700540, by rfl⟩ : syracuseStep 7201441 = 5401081) B5401081
theorem B3941369 : Blo 1750576 3941369 := bstep (se 2 (by rfl) ⟨1478013, by rfl⟩ : syracuseStep 3941369 = 2956027) B2956027
theorem B8864801 : Blo 1750576 8864801 := bstep (se 2 (by rfl) ⟨3324300, by rfl⟩ : syracuseStep 8864801 = 6648601) B6648601
theorem B3941711 : Blo 1750576 3941711 := bstep (se 1 (by rfl) ⟨2956283, by rfl⟩ : syracuseStep 3941711 = 5912567) B5912567
theorem B3155519 : Blo 1750576 3155519 := bstep (se 1 (by rfl) ⟨2366639, by rfl⟩ : syracuseStep 3155519 = 4733279) B4733279
theorem B31975019 : Blo 1750576 31975019 := bstep (se 1 (by rfl) ⟨23981264, by rfl⟩ : syracuseStep 31975019 = 47962529) B47962529
theorem B14960447 : Blo 1750576 14960447 := bstep (se 1 (by rfl) ⟨11220335, by rfl⟩ : syracuseStep 14960447 = 22440671) B22440671
theorem B3942287 : Blo 1750576 3942287 := bstep (se 1 (by rfl) ⟨2956715, by rfl⟩ : syracuseStep 3942287 = 5913431) B5913431
theorem B5908463 : Blo 1750576 5908463 := bstep (se 1 (by rfl) ⟨4431347, by rfl⟩ : syracuseStep 5908463 = 8862695) B8862695
theorem B3942431 : Blo 1750576 3942431 := bstep (se 1 (by rfl) ⟨2956823, by rfl⟩ : syracuseStep 3942431 = 5913647) B5913647
theorem B25249907 : Blo 1750576 25249907 := bstep (se 1 (by rfl) ⟨18937430, by rfl⟩ : syracuseStep 25249907 = 37874861) B37874861
theorem B37898387 : Blo 1750576 37898387 := bstep (se 1 (by rfl) ⟨28423790, by rfl⟩ : syracuseStep 37898387 = 56847581) B56847581
theorem B5908895 : Blo 1750576 5908895 := bstep (se 1 (by rfl) ⟨4431671, by rfl⟩ : syracuseStep 5908895 = 8863343) B8863343
theorem B3943007 : Blo 1750576 3943007 := bstep (se 1 (by rfl) ⟨2957255, by rfl⟩ : syracuseStep 3943007 = 5914511) B5914511
theorem B2493055 : Blo 1750576 2493055 := bstep (se 1 (by rfl) ⟨1869791, by rfl⟩ : syracuseStep 2493055 = 3739583) B3739583
theorem B14207723 : Blo 1750576 14207723 := bstep (se 1 (by rfl) ⟨10655792, by rfl⟩ : syracuseStep 14207723 = 21311585) B21311585
theorem B5909327 : Blo 1750576 5909327 := bstep (se 1 (by rfl) ⟨4431995, by rfl⟩ : syracuseStep 5909327 = 8863991) B8863991
theorem B2804873 : Blo 1750576 2804873 := bstep (se 2 (by rfl) ⟨1051827, by rfl⟩ : syracuseStep 2804873 = 2103655) B2103655
theorem B3738899 : Blo 1750576 3738899 := bstep (se 1 (by rfl) ⟨2804174, by rfl⟩ : syracuseStep 3738899 = 5608349) B5608349
theorem B3550591 : Blo 1750576 3550591 := bstep (se 1 (by rfl) ⟨2662943, by rfl⟩ : syracuseStep 3550591 = 5325887) B5325887
theorem B8990183 : Blo 1750576 8990183 := bstep (se 1 (by rfl) ⟨6742637, by rfl⟩ : syracuseStep 8990183 = 13485275) B13485275
theorem B14208655 : Blo 1750576 14208655 := bstep (se 1 (by rfl) ⟨10656491, by rfl⟩ : syracuseStep 14208655 = 21312983) B21312983
theorem B6647615 : Blo 1750576 6647615 := bstep (se 1 (by rfl) ⟨4985711, by rfl⟩ : syracuseStep 6647615 = 9971423) B9971423
theorem B12619709 : Blo 1750576 12619709 := bstep (se 3 (by rfl) ⟨2366195, by rfl⟩ : syracuseStep 12619709 = 4732391) B4732391
theorem B6647933 : Blo 1750576 6647933 := bstep (se 3 (by rfl) ⟨1246487, by rfl⟩ : syracuseStep 6647933 = 2492975) B2492975
theorem B9974087 : Blo 1750576 9974087 := bstep (se 1 (by rfl) ⟨7480565, by rfl⟩ : syracuseStep 9974087 = 14961131) B14961131
theorem B5993129 : Blo 1750576 5993129 := bstep (se 2 (by rfl) ⟨2247423, by rfl⟩ : syracuseStep 5993129 = 4494847) B4494847
theorem B14971655 : Blo 1750576 14971655 := bstep (se 1 (by rfl) ⟨11228741, by rfl⟩ : syracuseStep 14971655 = 22457483) B22457483
theorem B5911379 : Blo 1750576 5911379 := bstep (se 1 (by rfl) ⟨4433534, by rfl⟩ : syracuseStep 5911379 = 8867069) B8867069
theorem B3371935 : Blo 1750576 3371935 := bstep (se 1 (by rfl) ⟨2528951, by rfl⟩ : syracuseStep 3371935 = 5057903) B5057903
theorem B8991661 : Blo 1750576 8991661 := bstep (se 3 (by rfl) ⟨1685936, by rfl⟩ : syracuseStep 8991661 = 3371873) B3371873
theorem B19190891 : Blo 1750576 19190891 := bstep (se 1 (by rfl) ⟨14393168, by rfl⟩ : syracuseStep 19190891 = 28786337) B28786337
theorem B136475765 : Blo 1750576 136475765 := bstep (se 5 (by rfl) ⟨6397301, by rfl⟩ : syracuseStep 136475765 = 12794603) B12794603
theorem B29922533 : Blo 1750576 29922533 := bstep (se 4 (by rfl) ⟨2805237, by rfl⟩ : syracuseStep 29922533 = 5610475) B5610475
theorem B109368589 : Blo 1750576 109368589 := bstep (se 3 (by rfl) ⟨20506610, by rfl⟩ : syracuseStep 109368589 = 41013221) B41013221
theorem B3372521 : Blo 1750576 3372521 := bstep (se 2 (by rfl) ⟨1264695, by rfl⟩ : syracuseStep 3372521 = 2529391) B2529391
theorem B3995291 : Blo 1750576 3995291 := bstep (se 1 (by rfl) ⟨2996468, by rfl⟩ : syracuseStep 3995291 = 5992937) B5992937
theorem B2627303 : Blo 1750576 2627303 := bstep (se 1 (by rfl) ⟨1970477, by rfl⟩ : syracuseStep 2627303 = 3940955) B3940955
theorem B14964547 : Blo 1750576 14964547 := bstep (se 1 (by rfl) ⟨11223410, by rfl⟩ : syracuseStep 14964547 = 22446821) B22446821
theorem B7485281 : Blo 1750576 7485281 := bstep (se 2 (by rfl) ⟨2806980, by rfl⟩ : syracuseStep 7485281 = 5613961) B5613961
theorem B2955163 : Blo 1750576 2955163 := bstep (se 1 (by rfl) ⟨2216372, by rfl⟩ : syracuseStep 2955163 = 4432745) B4432745
theorem B1751035 : Blo 1750576 1751035 := bstep (se 1 (by rfl) ⟨1313276, by rfl⟩ : syracuseStep 1751035 = 2626553) B2626553
theorem B20215817 : Blo 1750576 20215817 := bstep (se 2 (by rfl) ⟨7580931, by rfl⟩ : syracuseStep 20215817 = 15161863) B15161863
theorem B24614927 : Blo 1750576 24614927 := bstep (se 1 (by rfl) ⟨18461195, by rfl⟩ : syracuseStep 24614927 = 36922391) B36922391
theorem B2955305 : Blo 1750576 2955305 := bstep (se 2 (by rfl) ⟨1108239, by rfl⟩ : syracuseStep 2955305 = 2216479) B2216479
theorem B21305387 : Blo 1750576 21305387 := bstep (se 1 (by rfl) ⟨15979040, by rfl⟩ : syracuseStep 21305387 = 31958081) B31958081
theorem B2627687 : Blo 1750576 2627687 := bstep (se 1 (by rfl) ⟨1970765, by rfl⟩ : syracuseStep 2627687 = 3941531) B3941531
theorem B1751167 : Blo 1750576 1751167 := bstep (se 1 (by rfl) ⟨1313375, by rfl⟩ : syracuseStep 1751167 = 2626751) B2626751
theorem B1751263 : Blo 1750576 1751263 := bstep (se 1 (by rfl) ⟨1313447, by rfl⟩ : syracuseStep 1751263 = 2626895) B2626895
theorem B3324179 : Blo 1750576 3324179 := bstep (se 1 (by rfl) ⟨2493134, by rfl⟩ : syracuseStep 3324179 = 4986269) B4986269
theorem B1751323 : Blo 1750576 1751323 := bstep (se 1 (by rfl) ⟨1313492, by rfl⟩ : syracuseStep 1751323 = 2626985) B2626985
theorem B29940029 : Blo 1750576 29940029 := bstep (se 3 (by rfl) ⟨5613755, by rfl⟩ : syracuseStep 29940029 = 11227511) B11227511
theorem B1751359 : Blo 1750576 1751359 := bstep (se 1 (by rfl) ⟨1313519, by rfl⟩ : syracuseStep 1751359 = 2627039) B2627039
theorem B1751423 : Blo 1750576 1751423 := bstep (se 1 (by rfl) ⟨1313567, by rfl⟩ : syracuseStep 1751423 = 2627135) B2627135
theorem B4987295 : Blo 1750576 4987295 := bstep (se 1 (by rfl) ⟨3740471, by rfl⟩ : syracuseStep 4987295 = 7480943) B7480943
theorem B9976229 : Blo 1750576 9976229 := bstep (se 4 (by rfl) ⟨935271, by rfl⟩ : syracuseStep 9976229 = 1870543) B1870543
theorem B19954187 : Blo 1750576 19954187 := bstep (se 1 (by rfl) ⟨14965640, by rfl⟩ : syracuseStep 19954187 = 29931281) B29931281
theorem B75774629 : Blo 1750576 75774629 := bstep (se 4 (by rfl) ⟨7103871, by rfl⟩ : syracuseStep 75774629 = 14207743) B14207743
theorem B1751743 : Blo 1750576 1751743 := bstep (se 1 (by rfl) ⟨1313807, by rfl⟩ : syracuseStep 1751743 = 2627615) B2627615
theorem B3324635 : Blo 1750576 3324635 := bstep (se 1 (by rfl) ⟨2493476, by rfl⟩ : syracuseStep 3324635 = 4986953) B4986953
theorem B7584481 : Blo 1750576 7584481 := bstep (se 2 (by rfl) ⟨2844180, by rfl⟩ : syracuseStep 7584481 = 5688361) B5688361
theorem B5913323 : Blo 1750576 5913323 := bstep (se 1 (by rfl) ⟨4434992, by rfl⟩ : syracuseStep 5913323 = 8869985) B8869985
theorem B2628455 : Blo 1750576 2628455 := bstep (se 1 (by rfl) ⟨1971341, by rfl⟩ : syracuseStep 2628455 = 3942683) B3942683
theorem B7478173 : Blo 1750576 7478173 := bstep (se 3 (by rfl) ⟨1402157, by rfl⟩ : syracuseStep 7478173 = 2804315) B2804315
theorem B2628521 : Blo 1750576 2628521 := bstep (se 2 (by rfl) ⟨985695, by rfl⟩ : syracuseStep 2628521 = 1971391) B1971391
theorem B2956223 : Blo 1750576 2956223 := bstep (se 1 (by rfl) ⟨2217167, by rfl⟩ : syracuseStep 2956223 = 4434335) B4434335
theorem B7101395 : Blo 1750576 7101395 := bstep (se 1 (by rfl) ⟨5326046, by rfl⟩ : syracuseStep 7101395 = 10652093) B10652093
theorem B1752031 : Blo 1750576 1752031 := bstep (se 1 (by rfl) ⟨1314023, by rfl⟩ : syracuseStep 1752031 = 2628047) B2628047
theorem B6650849 : Blo 1750576 6650849 := bstep (se 2 (by rfl) ⟨2494068, by rfl⟩ : syracuseStep 6650849 = 4988137) B4988137
theorem B1752091 : Blo 1750576 1752091 := bstep (se 1 (by rfl) ⟨1314068, by rfl⟩ : syracuseStep 1752091 = 2628137) B2628137
theorem B2956351 : Blo 1750576 2956351 := bstep (se 1 (by rfl) ⟨2217263, by rfl⟩ : syracuseStep 2956351 = 4434527) B4434527
theorem B2628713 : Blo 1750576 2628713 := bstep (se 2 (by rfl) ⟨985767, by rfl⟩ : syracuseStep 2628713 = 1971535) B1971535
theorem B1752231 : Blo 1750576 1752231 := bstep (se 1 (by rfl) ⟨1314173, by rfl⟩ : syracuseStep 1752231 = 2628347) B2628347
theorem B1752315 : Blo 1750576 1752315 := bstep (se 1 (by rfl) ⟨1314236, by rfl⟩ : syracuseStep 1752315 = 2628473) B2628473
theorem B5914241 : Blo 1750576 5914241 := bstep (se 2 (by rfl) ⟨2217840, by rfl⟩ : syracuseStep 5914241 = 4435681) B4435681
theorem B3325607 : Blo 1750576 3325607 := bstep (se 1 (by rfl) ⟨2494205, by rfl⟩ : syracuseStep 3325607 = 4988411) B4988411
theorem B3940091 : Blo 1750576 3940091 := bstep (se 1 (by rfl) ⟨2955068, by rfl⟩ : syracuseStep 3940091 = 5910137) B5910137
theorem B3325691 : Blo 1750576 3325691 := bstep (se 1 (by rfl) ⟨2494268, by rfl⟩ : syracuseStep 3325691 = 4988537) B4988537
theorem B2957215 : Blo 1750576 2957215 := bstep (se 1 (by rfl) ⟨2217911, by rfl⟩ : syracuseStep 2957215 = 4435823) B4435823
theorem B4431955 : Blo 1750576 4431955 := bstep (se 1 (by rfl) ⟨3323966, by rfl⟩ : syracuseStep 4431955 = 6647933) B6647933
theorem B51175709 : Blo 1750576 51175709 := bstep (se 3 (by rfl) ⟨9595445, by rfl⟩ : syracuseStep 51175709 = 19190891) B19190891
theorem B7479661 : Blo 1750576 7479661 := bstep (se 3 (by rfl) ⟨1402436, by rfl⟩ : syracuseStep 7479661 = 2804873) B2804873
theorem B3940919 : Blo 1750576 3940919 := bstep (se 1 (by rfl) ⟨2955689, by rfl⟩ : syracuseStep 3940919 = 5911379) B5911379
theorem B9970397 : Blo 1750576 9970397 := bstep (se 3 (by rfl) ⟨1869449, by rfl⟩ : syracuseStep 9970397 = 3738899) B3738899
theorem B8864477 : Blo 1750576 8864477 := bstep (se 3 (by rfl) ⟨1662089, by rfl⟩ : syracuseStep 8864477 = 3324179) B3324179
theorem B19948355 : Blo 1750576 19948355 := bstep (se 1 (by rfl) ⟨14961266, by rfl⟩ : syracuseStep 19948355 = 29922533) B29922533
theorem B9601921 : Blo 1750576 9601921 := bstep (se 2 (by rfl) ⟨3600720, by rfl⟩ : syracuseStep 9601921 = 7201441) B7201441
theorem B21316679 : Blo 1750576 21316679 := bstep (se 1 (by rfl) ⟨15987509, by rfl⟩ : syracuseStep 21316679 = 31975019) B31975019
theorem B2663527 : Blo 1750576 2663527 := bstep (se 1 (by rfl) ⟨1997645, by rfl⟩ : syracuseStep 2663527 = 3995291) B3995291
theorem B9970897 : Blo 1750576 9970897 := bstep (se 2 (by rfl) ⟨3739086, by rfl⟩ : syracuseStep 9970897 = 7478173) B7478173
theorem B4990187 : Blo 1750576 4990187 := bstep (se 1 (by rfl) ⟨3742640, by rfl⟩ : syracuseStep 4990187 = 7485281) B7485281
theorem B13477211 : Blo 1750576 13477211 := bstep (se 1 (by rfl) ⟨10107908, by rfl⟩ : syracuseStep 13477211 = 20215817) B20215817
theorem B16409951 : Blo 1750576 16409951 := bstep (se 1 (by rfl) ⟨12307463, by rfl⟩ : syracuseStep 16409951 = 24614927) B24614927
theorem B3941801 : Blo 1750576 3941801 := bstep (se 2 (by rfl) ⟨1478175, by rfl⟩ : syracuseStep 3941801 = 2956351) B2956351
theorem B25265591 : Blo 1750576 25265591 := bstep (se 1 (by rfl) ⟨18949193, by rfl⟩ : syracuseStep 25265591 = 37898387) B37898387
theorem B9471815 : Blo 1750576 9471815 := bstep (se 1 (by rfl) ⟨7103861, by rfl⟩ : syracuseStep 9471815 = 14207723) B14207723
theorem B3942215 : Blo 1750576 3942215 := bstep (se 1 (by rfl) ⟨2956661, by rfl⟩ : syracuseStep 3942215 = 5913323) B5913323
theorem B4433899 : Blo 1750576 4433899 := bstep (se 1 (by rfl) ⟨3325424, by rfl⟩ : syracuseStep 4433899 = 6650849) B6650849
theorem B3942827 : Blo 1750576 3942827 := bstep (se 1 (by rfl) ⟨2957120, by rfl⟩ : syracuseStep 3942827 = 5914241) B5914241
theorem B3942953 : Blo 1750576 3942953 := bstep (se 2 (by rfl) ⟨1478607, by rfl⟩ : syracuseStep 3942953 = 2957215) B2957215
theorem B56814365 : Blo 1750576 56814365 := bstep (se 3 (by rfl) ⟨10652693, by rfl⟩ : syracuseStep 56814365 = 21305387) B21305387
theorem B9981103 : Blo 1750576 9981103 := bstep (se 1 (by rfl) ⟨7485827, by rfl⟩ : syracuseStep 9981103 = 14971655) B14971655
theorem B5909867 : Blo 1750576 5909867 := bstep (se 1 (by rfl) ⟨4432400, by rfl⟩ : syracuseStep 5909867 = 8864801) B8864801
theorem B90983843 : Blo 1750576 90983843 := bstep (se 1 (by rfl) ⟨68237882, by rfl⟩ : syracuseStep 90983843 = 136475765) B136475765
theorem B9973631 : Blo 1750576 9973631 := bstep (se 1 (by rfl) ⟨7480223, by rfl⟩ : syracuseStep 9973631 = 14960447) B14960447
theorem B11988881 : Blo 1750576 11988881 := bstep (se 2 (by rfl) ⟨4495830, by rfl⟩ : syracuseStep 11988881 = 8991661) B8991661
theorem B1970203 : Blo 1750576 1970203 := bstep (se 1 (by rfl) ⟨1477652, by rfl⟩ : syracuseStep 1970203 = 2955305) B2955305
theorem B19960019 : Blo 1750576 19960019 := bstep (se 1 (by rfl) ⟨14970014, by rfl⟩ : syracuseStep 19960019 = 29940029) B29940029
theorem B50516419 : Blo 1750576 50516419 := bstep (se 1 (by rfl) ⟨37887314, by rfl⟩ : syracuseStep 50516419 = 75774629) B75774629
theorem B2216423 : Blo 1750576 2216423 := bstep (se 1 (by rfl) ⟨1662317, by rfl⟩ : syracuseStep 2216423 = 3324635) B3324635
theorem B1970815 : Blo 1750576 1970815 := bstep (se 1 (by rfl) ⟨1478111, by rfl⟩ : syracuseStep 1970815 = 2956223) B2956223
theorem B18944873 : Blo 1750576 18944873 := bstep (se 2 (by rfl) ⟨7104327, by rfl⟩ : syracuseStep 18944873 = 14208655) B14208655
theorem B5993455 : Blo 1750576 5993455 := bstep (se 1 (by rfl) ⟨4495091, by rfl⟩ : syracuseStep 5993455 = 8990183) B8990183
theorem B19952729 : Blo 1750576 19952729 := bstep (se 2 (by rfl) ⟨7482273, by rfl⟩ : syracuseStep 19952729 = 14964547) B14964547
theorem B2217071 : Blo 1750576 2217071 := bstep (se 1 (by rfl) ⟨1662803, by rfl⟩ : syracuseStep 2217071 = 3325607) B3325607
theorem B2626727 : Blo 1750576 2626727 := bstep (se 1 (by rfl) ⟨1970045, by rfl⟩ : syracuseStep 2626727 = 3940091) B3940091
theorem B2217127 : Blo 1750576 2217127 := bstep (se 1 (by rfl) ⟨1662845, by rfl⟩ : syracuseStep 2217127 = 3325691) B3325691
theorem B6649391 : Blo 1750576 6649391 := bstep (se 1 (by rfl) ⟨4987043, by rfl⟩ : syracuseStep 6649391 = 9974087) B9974087
theorem B2627579 : Blo 1750576 2627579 := bstep (se 1 (by rfl) ⟨1970684, by rfl⟩ : syracuseStep 2627579 = 3941369) B3941369
theorem B3324073 : Blo 1750576 3324073 := bstep (se 2 (by rfl) ⟨1246527, by rfl⟩ : syracuseStep 3324073 = 2493055) B2493055
theorem B2627807 : Blo 1750576 2627807 := bstep (se 1 (by rfl) ⟨1970855, by rfl⟩ : syracuseStep 2627807 = 3941711) B3941711
theorem B2103679 : Blo 1750576 2103679 := bstep (se 1 (by rfl) ⟨1577759, by rfl⟩ : syracuseStep 2103679 = 3155519) B3155519
theorem B1751535 : Blo 1750576 1751535 := bstep (se 1 (by rfl) ⟨1313651, by rfl⟩ : syracuseStep 1751535 = 2627303) B2627303
theorem B40450565 : Blo 1750576 40450565 := bstep (se 4 (by rfl) ⟨3792240, by rfl⟩ : syracuseStep 40450565 = 7584481) B7584481
theorem B4495913 : Blo 1750576 4495913 := bstep (se 2 (by rfl) ⟨1685967, by rfl⟩ : syracuseStep 4495913 = 3371935) B3371935
theorem B2628191 : Blo 1750576 2628191 := bstep (se 1 (by rfl) ⟨1971143, by rfl⟩ : syracuseStep 2628191 = 3942287) B3942287
theorem B8993389 : Blo 1750576 8993389 := bstep (se 3 (by rfl) ⟨1686260, by rfl⟩ : syracuseStep 8993389 = 3372521) B3372521
theorem B3938975 : Blo 1750576 3938975 := bstep (se 1 (by rfl) ⟨2954231, by rfl⟩ : syracuseStep 3938975 = 5908463) B5908463
theorem B2628287 : Blo 1750576 2628287 := bstep (se 1 (by rfl) ⟨1971215, by rfl⟩ : syracuseStep 2628287 = 3942431) B3942431
theorem B1751791 : Blo 1750576 1751791 := bstep (se 1 (by rfl) ⟨1313843, by rfl⟩ : syracuseStep 1751791 = 2627687) B2627687
theorem B16833271 : Blo 1750576 16833271 := bstep (se 1 (by rfl) ⟨12624953, by rfl⟩ : syracuseStep 16833271 = 25249907) B25249907
theorem B3995419 : Blo 1750576 3995419 := bstep (se 1 (by rfl) ⟨2996564, by rfl⟩ : syracuseStep 3995419 = 5993129) B5993129
theorem B3939263 : Blo 1750576 3939263 := bstep (se 1 (by rfl) ⟨2954447, by rfl⟩ : syracuseStep 3939263 = 5908895) B5908895
theorem B3324863 : Blo 1750576 3324863 := bstep (se 1 (by rfl) ⟨2493647, by rfl⟩ : syracuseStep 3324863 = 4987295) B4987295
theorem B6650819 : Blo 1750576 6650819 := bstep (se 1 (by rfl) ⟨4988114, by rfl⟩ : syracuseStep 6650819 = 9976229) B9976229
theorem B13302791 : Blo 1750576 13302791 := bstep (se 1 (by rfl) ⟨9977093, by rfl⟩ : syracuseStep 13302791 = 19954187) B19954187
theorem B145824785 : Blo 1750576 145824785 := bstep (se 2 (by rfl) ⟨54684294, by rfl⟩ : syracuseStep 145824785 = 109368589) B109368589
theorem B2628671 : Blo 1750576 2628671 := bstep (se 1 (by rfl) ⟨1971503, by rfl⟩ : syracuseStep 2628671 = 3943007) B3943007
theorem B4734121 : Blo 1750576 4734121 := bstep (se 2 (by rfl) ⟨1775295, by rfl⟩ : syracuseStep 4734121 = 3550591) B3550591
theorem B3939551 : Blo 1750576 3939551 := bstep (se 1 (by rfl) ⟨2954663, by rfl⟩ : syracuseStep 3939551 = 5909327) B5909327
theorem B1752303 : Blo 1750576 1752303 := bstep (se 1 (by rfl) ⟨1314227, by rfl⟩ : syracuseStep 1752303 = 2628455) B2628455
theorem B1752347 : Blo 1750576 1752347 := bstep (se 1 (by rfl) ⟨1314260, by rfl⟩ : syracuseStep 1752347 = 2628521) B2628521
theorem B4734263 : Blo 1750576 4734263 := bstep (se 1 (by rfl) ⟨3550697, by rfl⟩ : syracuseStep 4734263 = 7101395) B7101395
theorem B1752475 : Blo 1750576 1752475 := bstep (se 1 (by rfl) ⟨1314356, by rfl⟩ : syracuseStep 1752475 = 2628713) B2628713
theorem B3940217 : Blo 1750576 3940217 := bstep (se 2 (by rfl) ⟨1477581, by rfl⟩ : syracuseStep 3940217 = 2955163) B2955163
theorem B4431743 : Blo 1750576 4431743 := bstep (se 1 (by rfl) ⟨3323807, by rfl⟩ : syracuseStep 4431743 = 6647615) B6647615
theorem B8413139 : Blo 1750576 8413139 := bstep (se 1 (by rfl) ⟨6309854, by rfl⟩ : syracuseStep 8413139 = 12619709) B12619709
theorem B4432097 : Blo 1750576 4432097 := bstep (se 2 (by rfl) ⟨1662036, by rfl⟩ : syracuseStep 4432097 = 3324073) B3324073
theorem B67355225 : Blo 1750576 67355225 := bstep (se 2 (by rfl) ⟨25258209, by rfl⟩ : syracuseStep 67355225 = 50516419) B50516419
theorem B16843727 : Blo 1750576 16843727 := bstep (se 1 (by rfl) ⟨12632795, by rfl⟩ : syracuseStep 16843727 = 25265591) B25265591
theorem B4432927 : Blo 1750576 4432927 := bstep (se 1 (by rfl) ⟨3324695, by rfl⟩ : syracuseStep 4432927 = 6649391) B6649391
theorem B4433879 : Blo 1750576 4433879 := bstep (se 1 (by rfl) ⟨3325409, by rfl⟩ : syracuseStep 4433879 = 6650819) B6650819
theorem B51210245 : Blo 1750576 51210245 := bstep (se 4 (by rfl) ⟨4800960, by rfl⟩ : syracuseStep 51210245 = 9601921) B9601921
theorem B97216523 : Blo 1750576 97216523 := bstep (se 1 (by rfl) ⟨72912392, by rfl⟩ : syracuseStep 97216523 = 145824785) B145824785
theorem B3156175 : Blo 1750576 3156175 := bstep (se 1 (by rfl) ⟨2367131, by rfl⟩ : syracuseStep 3156175 = 4734263) B4734263
theorem B60655895 : Blo 1750576 60655895 := bstep (se 1 (by rfl) ⟨45491921, by rfl⟩ : syracuseStep 60655895 = 90983843) B90983843
theorem B5327225 : Blo 1750576 5327225 := bstep (se 2 (by rfl) ⟨1997709, by rfl⟩ : syracuseStep 5327225 = 3995419) B3995419
theorem B5909273 : Blo 1750576 5909273 := bstep (se 2 (by rfl) ⟨2215977, by rfl⟩ : syracuseStep 5909273 = 4431955) B4431955
theorem B13306679 : Blo 1750576 13306679 := bstep (se 1 (by rfl) ⟨9980009, by rfl⟩ : syracuseStep 13306679 = 19960019) B19960019
theorem B9972881 : Blo 1750576 9972881 := bstep (se 2 (by rfl) ⟨3739830, by rfl⟩ : syracuseStep 9972881 = 7479661) B7479661
theorem B6646931 : Blo 1750576 6646931 := bstep (se 1 (by rfl) ⟨4985198, by rfl⟩ : syracuseStep 6646931 = 9970397) B9970397
theorem B5909651 : Blo 1750576 5909651 := bstep (se 1 (by rfl) ⟨4432238, by rfl⟩ : syracuseStep 5909651 = 8864477) B8864477
theorem B2804905 : Blo 1750576 2804905 := bstep (se 2 (by rfl) ⟨1051839, by rfl⟩ : syracuseStep 2804905 = 2103679) B2103679
theorem B13298903 : Blo 1750576 13298903 := bstep (se 1 (by rfl) ⟨9974177, by rfl⟩ : syracuseStep 13298903 = 19948355) B19948355
theorem B13307165 : Blo 1750576 13307165 := bstep (se 3 (by rfl) ⟨2495093, by rfl⟩ : syracuseStep 13307165 = 4990187) B4990187
theorem B10939967 : Blo 1750576 10939967 := bstep (se 1 (by rfl) ⟨8204975, by rfl⟩ : syracuseStep 10939967 = 16409951) B16409951
theorem B5910461 : Blo 1750576 5910461 := bstep (se 3 (by rfl) ⟨1108211, by rfl⟩ : syracuseStep 5910461 = 2216423) B2216423
theorem B7991273 : Blo 1750576 7991273 := bstep (se 2 (by rfl) ⟨2996727, by rfl⟩ : syracuseStep 7991273 = 5993455) B5993455
theorem B3551369 : Blo 1750576 3551369 := bstep (se 2 (by rfl) ⟨1331763, by rfl⟩ : syracuseStep 3551369 = 2663527) B2663527
theorem B6312161 : Blo 1750576 6312161 := bstep (se 2 (by rfl) ⟨2367060, by rfl⟩ : syracuseStep 6312161 = 4734121) B4734121
theorem B13308137 : Blo 1750576 13308137 := bstep (se 2 (by rfl) ⟨4990551, by rfl⟩ : syracuseStep 13308137 = 9981103) B9981103
theorem B2625983 : Blo 1750576 2625983 := bstep (se 1 (by rfl) ⟨1969487, by rfl⟩ : syracuseStep 2625983 = 3938975) B3938975
theorem B37876243 : Blo 1750576 37876243 := bstep (se 1 (by rfl) ⟨28407182, by rfl⟩ : syracuseStep 37876243 = 56814365) B56814365
theorem B2626175 : Blo 1750576 2626175 := bstep (se 1 (by rfl) ⟨1969631, by rfl⟩ : syracuseStep 2626175 = 3939263) B3939263
theorem B2216575 : Blo 1750576 2216575 := bstep (se 1 (by rfl) ⟨1662431, by rfl⟩ : syracuseStep 2216575 = 3324863) B3324863
theorem B8868527 : Blo 1750576 8868527 := bstep (se 1 (by rfl) ⟨6651395, by rfl⟩ : syracuseStep 8868527 = 13302791) B13302791
theorem B2626367 : Blo 1750576 2626367 := bstep (se 1 (by rfl) ⟨1969775, by rfl⟩ : syracuseStep 2626367 = 3939551) B3939551
theorem B2626811 : Blo 1750576 2626811 := bstep (se 1 (by rfl) ⟨1970108, by rfl⟩ : syracuseStep 2626811 = 3940217) B3940217
theorem B2954495 : Blo 1750576 2954495 := bstep (se 1 (by rfl) ⟨2215871, by rfl⟩ : syracuseStep 2954495 = 4431743) B4431743
theorem B6649087 : Blo 1750576 6649087 := bstep (se 1 (by rfl) ⟨4986815, by rfl⟩ : syracuseStep 6649087 = 9973631) B9973631
theorem B7992587 : Blo 1750576 7992587 := bstep (se 1 (by rfl) ⟨5994440, by rfl⟩ : syracuseStep 7992587 = 11988881) B11988881
theorem B5608759 : Blo 1750576 5608759 := bstep (se 1 (by rfl) ⟨4206569, by rfl⟩ : syracuseStep 5608759 = 8413139) B8413139
theorem B5911865 : Blo 1750576 5911865 := bstep (se 2 (by rfl) ⟨2216949, by rfl⟩ : syracuseStep 5911865 = 4433899) B4433899
theorem B2626937 : Blo 1750576 2626937 := bstep (se 2 (by rfl) ⟨985101, by rfl⟩ : syracuseStep 2626937 = 1970203) B1970203
theorem B34117139 : Blo 1750576 34117139 := bstep (se 1 (by rfl) ⟨25587854, by rfl⟩ : syracuseStep 34117139 = 51175709) B51175709
theorem B5912189 : Blo 1750576 5912189 := bstep (se 3 (by rfl) ⟨1108535, by rfl⟩ : syracuseStep 5912189 = 2217071) B2217071
theorem B2627279 : Blo 1750576 2627279 := bstep (se 1 (by rfl) ⟨1970459, by rfl⟩ : syracuseStep 2627279 = 3940919) B3940919
theorem B12629915 : Blo 1750576 12629915 := bstep (se 1 (by rfl) ⟨9472436, by rfl⟩ : syracuseStep 12629915 = 18944873) B18944873
theorem B14211119 : Blo 1750576 14211119 := bstep (se 1 (by rfl) ⟨10658339, by rfl⟩ : syracuseStep 14211119 = 21316679) B21316679
theorem B13301819 : Blo 1750576 13301819 := bstep (se 1 (by rfl) ⟨9976364, by rfl⟩ : syracuseStep 13301819 = 19952729) B19952729
theorem B1751151 : Blo 1750576 1751151 := bstep (se 1 (by rfl) ⟨1313363, by rfl⟩ : syracuseStep 1751151 = 2626727) B2626727
theorem B11991185 : Blo 1750576 11991185 := bstep (se 2 (by rfl) ⟨4496694, by rfl⟩ : syracuseStep 11991185 = 8993389) B8993389
theorem B2627753 : Blo 1750576 2627753 := bstep (se 2 (by rfl) ⟨985407, by rfl⟩ : syracuseStep 2627753 = 1970815) B1970815
theorem B8984807 : Blo 1750576 8984807 := bstep (se 1 (by rfl) ⟨6738605, by rfl⟩ : syracuseStep 8984807 = 13477211) B13477211
theorem B2627867 : Blo 1750576 2627867 := bstep (se 1 (by rfl) ⟨1970900, by rfl⟩ : syracuseStep 2627867 = 3941801) B3941801
theorem B22444361 : Blo 1750576 22444361 := bstep (se 2 (by rfl) ⟨8416635, by rfl⟩ : syracuseStep 22444361 = 16833271) B16833271
theorem B6314543 : Blo 1750576 6314543 := bstep (se 1 (by rfl) ⟨4735907, by rfl⟩ : syracuseStep 6314543 = 9471815) B9471815
theorem B2628143 : Blo 1750576 2628143 := bstep (se 1 (by rfl) ⟨1971107, by rfl⟩ : syracuseStep 2628143 = 3942215) B3942215
theorem B1751719 : Blo 1750576 1751719 := bstep (se 1 (by rfl) ⟨1313789, by rfl⟩ : syracuseStep 1751719 = 2627579) B2627579
theorem B1751871 : Blo 1750576 1751871 := bstep (se 1 (by rfl) ⟨1313903, by rfl⟩ : syracuseStep 1751871 = 2627807) B2627807
theorem B2956169 : Blo 1750576 2956169 := bstep (se 2 (by rfl) ⟨1108563, by rfl⟩ : syracuseStep 2956169 = 2217127) B2217127
theorem B13294529 : Blo 1750576 13294529 := bstep (se 2 (by rfl) ⟨4985448, by rfl⟩ : syracuseStep 13294529 = 9970897) B9970897
theorem B2628551 : Blo 1750576 2628551 := bstep (se 1 (by rfl) ⟨1971413, by rfl⟩ : syracuseStep 2628551 = 3942827) B3942827
theorem B26967043 : Blo 1750576 26967043 := bstep (se 1 (by rfl) ⟨20225282, by rfl⟩ : syracuseStep 26967043 = 40450565) B40450565
theorem B2997275 : Blo 1750576 2997275 := bstep (se 1 (by rfl) ⟨2247956, by rfl⟩ : syracuseStep 2997275 = 4495913) B4495913
theorem B2628635 : Blo 1750576 2628635 := bstep (se 1 (by rfl) ⟨1971476, by rfl⟩ : syracuseStep 2628635 = 3942953) B3942953
theorem B1752127 : Blo 1750576 1752127 := bstep (se 1 (by rfl) ⟨1314095, by rfl⟩ : syracuseStep 1752127 = 2628191) B2628191
theorem B1752191 : Blo 1750576 1752191 := bstep (se 1 (by rfl) ⟨1314143, by rfl⟩ : syracuseStep 1752191 = 2628287) B2628287
theorem B1752447 : Blo 1750576 1752447 := bstep (se 1 (by rfl) ⟨1314335, by rfl⟩ : syracuseStep 1752447 = 2628671) B2628671
theorem B3939911 : Blo 1750576 3939911 := bstep (se 1 (by rfl) ⟨2954933, by rfl⟩ : syracuseStep 3939911 = 5909867) B5909867
theorem B8872091 : Blo 1750576 8872091 := bstep (se 1 (by rfl) ⟨6654068, by rfl⟩ : syracuseStep 8872091 = 13308137) B13308137
theorem B3941243 : Blo 1750576 3941243 := bstep (se 1 (by rfl) ⟨2955932, by rfl⟩ : syracuseStep 3941243 = 5911865) B5911865
theorem B3941459 : Blo 1750576 3941459 := bstep (se 1 (by rfl) ⟨2956094, by rfl⟩ : syracuseStep 3941459 = 5912189) B5912189
theorem B35956057 : Blo 1750576 35956057 := bstep (se 2 (by rfl) ⟨13483521, by rfl⟩ : syracuseStep 35956057 = 26967043) B26967043
theorem B37881269 : Blo 1750576 37881269 := bstep (se 5 (by rfl) ⟨1775684, by rfl⟩ : syracuseStep 37881269 = 3551369) B3551369
theorem B5989871 : Blo 1750576 5989871 := bstep (se 1 (by rfl) ⟨4492403, by rfl⟩ : syracuseStep 5989871 = 8984807) B8984807
theorem B40437263 : Blo 1750576 40437263 := bstep (se 1 (by rfl) ⟨30327947, by rfl⟩ : syracuseStep 40437263 = 60655895) B60655895
theorem B8865449 : Blo 1750576 8865449 := bstep (se 2 (by rfl) ⟨3324543, by rfl⟩ : syracuseStep 8865449 = 6649087) B6649087
theorem B8865935 : Blo 1750576 8865935 := bstep (se 1 (by rfl) ⟨6649451, by rfl⟩ : syracuseStep 8865935 = 13298903) B13298903
theorem B7293311 : Blo 1750576 7293311 := bstep (se 1 (by rfl) ⟨5469983, by rfl⟩ : syracuseStep 7293311 = 10939967) B10939967
theorem B5327515 : Blo 1750576 5327515 := bstep (se 1 (by rfl) ⟨3995636, by rfl⟩ : syracuseStep 5327515 = 7991273) B7991273
theorem B44903483 : Blo 1750576 44903483 := bstep (se 1 (by rfl) ⟨33677612, by rfl⟩ : syracuseStep 44903483 = 67355225) B67355225
theorem B1969663 : Blo 1750576 1969663 := bstep (se 1 (by rfl) ⟨1477247, by rfl⟩ : syracuseStep 1969663 = 2954495) B2954495
theorem B5328391 : Blo 1750576 5328391 := bstep (se 1 (by rfl) ⟨3996293, by rfl⟩ : syracuseStep 5328391 = 7992587) B7992587
theorem B22744759 : Blo 1750576 22744759 := bstep (se 1 (by rfl) ⟨17058569, by rfl⟩ : syracuseStep 22744759 = 34117139) B34117139
theorem B34140163 : Blo 1750576 34140163 := bstep (se 1 (by rfl) ⟨25605122, by rfl⟩ : syracuseStep 34140163 = 51210245) B51210245
theorem B64811015 : Blo 1750576 64811015 := bstep (se 1 (by rfl) ⟨48608261, by rfl⟩ : syracuseStep 64811015 = 97216523) B97216523
theorem B9474079 : Blo 1750576 9474079 := bstep (se 1 (by rfl) ⟨7105559, by rfl⟩ : syracuseStep 9474079 = 14211119) B14211119
theorem B8867879 : Blo 1750576 8867879 := bstep (se 1 (by rfl) ⟨6650909, by rfl⟩ : syracuseStep 8867879 = 13301819) B13301819
theorem B5910569 : Blo 1750576 5910569 := bstep (se 2 (by rfl) ⟨2216463, by rfl⟩ : syracuseStep 5910569 = 4432927) B4432927
theorem B14962907 : Blo 1750576 14962907 := bstep (se 1 (by rfl) ⟨11222180, by rfl⟩ : syracuseStep 14962907 = 22444361) B22444361
theorem B3739873 : Blo 1750576 3739873 := bstep (se 2 (by rfl) ⟨1402452, by rfl⟩ : syracuseStep 3739873 = 2804905) B2804905
theorem B3551483 : Blo 1750576 3551483 := bstep (se 1 (by rfl) ⟨2663612, by rfl⟩ : syracuseStep 3551483 = 5327225) B5327225
theorem B1970779 : Blo 1750576 1970779 := bstep (se 1 (by rfl) ⟨1478084, by rfl⟩ : syracuseStep 1970779 = 2956169) B2956169
theorem B6648587 : Blo 1750576 6648587 := bstep (se 1 (by rfl) ⟨4986440, by rfl⟩ : syracuseStep 6648587 = 9972881) B9972881
theorem B2626607 : Blo 1750576 2626607 := bstep (se 1 (by rfl) ⟨1969955, by rfl⟩ : syracuseStep 2626607 = 3939911) B3939911
theorem B2954731 : Blo 1750576 2954731 := bstep (se 1 (by rfl) ⟨2216048, by rfl⟩ : syracuseStep 2954731 = 4432097) B4432097
theorem B4208107 : Blo 1750576 4208107 := bstep (se 1 (by rfl) ⟨3156080, by rfl⟩ : syracuseStep 4208107 = 6312161) B6312161
theorem B4208233 : Blo 1750576 4208233 := bstep (se 2 (by rfl) ⟨1578087, by rfl⟩ : syracuseStep 4208233 = 3156175) B3156175
theorem B31970933 : Blo 1750576 31970933 := bstep (se 5 (by rfl) ⟨1498637, by rfl⟩ : syracuseStep 31970933 = 2997275) B2997275
theorem B1750655 : Blo 1750576 1750655 := bstep (se 1 (by rfl) ⟨1312991, by rfl⟩ : syracuseStep 1750655 = 2625983) B2625983
theorem B1750783 : Blo 1750576 1750783 := bstep (se 1 (by rfl) ⟨1313087, by rfl⟩ : syracuseStep 1750783 = 2626175) B2626175
theorem B5912351 : Blo 1750576 5912351 := bstep (se 1 (by rfl) ⟨4434263, by rfl⟩ : syracuseStep 5912351 = 8868527) B8868527
theorem B1750911 : Blo 1750576 1750911 := bstep (se 1 (by rfl) ⟨1313183, by rfl⟩ : syracuseStep 1750911 = 2626367) B2626367
theorem B50501657 : Blo 1750576 50501657 := bstep (se 2 (by rfl) ⟨18938121, by rfl⟩ : syracuseStep 50501657 = 37876243) B37876243
theorem B1751207 : Blo 1750576 1751207 := bstep (se 1 (by rfl) ⟨1313405, by rfl⟩ : syracuseStep 1751207 = 2626811) B2626811
theorem B2955433 : Blo 1750576 2955433 := bstep (se 2 (by rfl) ⟨1108287, by rfl⟩ : syracuseStep 2955433 = 2216575) B2216575
theorem B1751291 : Blo 1750576 1751291 := bstep (se 1 (by rfl) ⟨1313468, by rfl⟩ : syracuseStep 1751291 = 2626937) B2626937
theorem B1751519 : Blo 1750576 1751519 := bstep (se 1 (by rfl) ⟨1313639, by rfl⟩ : syracuseStep 1751519 = 2627279) B2627279
theorem B8419943 : Blo 1750576 8419943 := bstep (se 1 (by rfl) ⟨6314957, by rfl⟩ : syracuseStep 8419943 = 12629915) B12629915
theorem B2955919 : Blo 1750576 2955919 := bstep (se 1 (by rfl) ⟨2216939, by rfl⟩ : syracuseStep 2955919 = 4433879) B4433879
theorem B7994123 : Blo 1750576 7994123 := bstep (se 1 (by rfl) ⟨5995592, by rfl⟩ : syracuseStep 7994123 = 11991185) B11991185
theorem B1751835 : Blo 1750576 1751835 := bstep (se 1 (by rfl) ⟨1313876, by rfl⟩ : syracuseStep 1751835 = 2627753) B2627753
theorem B1751911 : Blo 1750576 1751911 := bstep (se 1 (by rfl) ⟨1313933, by rfl⟩ : syracuseStep 1751911 = 2627867) B2627867
theorem B4209695 : Blo 1750576 4209695 := bstep (se 1 (by rfl) ⟨3157271, by rfl⟩ : syracuseStep 4209695 = 6314543) B6314543
theorem B1752095 : Blo 1750576 1752095 := bstep (se 1 (by rfl) ⟨1314071, by rfl⟩ : syracuseStep 1752095 = 2628143) B2628143
theorem B7478345 : Blo 1750576 7478345 := bstep (se 2 (by rfl) ⟨2804379, by rfl⟩ : syracuseStep 7478345 = 5608759) B5608759
theorem B3939515 : Blo 1750576 3939515 := bstep (se 1 (by rfl) ⟨2954636, by rfl⟩ : syracuseStep 3939515 = 5909273) B5909273
theorem B8871119 : Blo 1750576 8871119 := bstep (se 1 (by rfl) ⟨6653339, by rfl⟩ : syracuseStep 8871119 = 13306679) B13306679
theorem B8863019 : Blo 1750576 8863019 := bstep (se 1 (by rfl) ⟨6647264, by rfl⟩ : syracuseStep 8863019 = 13294529) B13294529
theorem B1752367 : Blo 1750576 1752367 := bstep (se 1 (by rfl) ⟨1314275, by rfl⟩ : syracuseStep 1752367 = 2628551) B2628551
theorem B1752423 : Blo 1750576 1752423 := bstep (se 1 (by rfl) ⟨1314317, by rfl⟩ : syracuseStep 1752423 = 2628635) B2628635
theorem B4431287 : Blo 1750576 4431287 := bstep (se 1 (by rfl) ⟨3323465, by rfl⟩ : syracuseStep 4431287 = 6646931) B6646931
theorem B3939767 : Blo 1750576 3939767 := bstep (se 1 (by rfl) ⟨2954825, by rfl⟩ : syracuseStep 3939767 = 5909651) B5909651
theorem B8871443 : Blo 1750576 8871443 := bstep (se 1 (by rfl) ⟨6653582, by rfl⟩ : syracuseStep 8871443 = 13307165) B13307165
theorem B44916605 : Blo 1750576 44916605 := bstep (se 3 (by rfl) ⟨8421863, by rfl⟩ : syracuseStep 44916605 = 16843727) B16843727
theorem B3940307 : Blo 1750576 3940307 := bstep (se 1 (by rfl) ⟨2955230, by rfl⟩ : syracuseStep 3940307 = 5910461) B5910461
theorem B3940379 : Blo 1750576 3940379 := bstep (se 1 (by rfl) ⟨2955284, by rfl⟩ : syracuseStep 3940379 = 5910569) B5910569
theorem B12632105 : Blo 1750576 12632105 := bstep (se 2 (by rfl) ⟨4737039, by rfl⟩ : syracuseStep 12632105 = 9474079) B9474079
theorem B5914727 : Blo 1750576 5914727 := bstep (se 1 (by rfl) ⟨4436045, by rfl⟩ : syracuseStep 5914727 = 8872091) B8872091
theorem B3940577 : Blo 1750576 3940577 := bstep (se 2 (by rfl) ⟨1477716, by rfl⟩ : syracuseStep 3940577 = 2955433) B2955433
theorem B4432391 : Blo 1750576 4432391 := bstep (se 1 (by rfl) ⟨3324293, by rfl⟩ : syracuseStep 4432391 = 6648587) B6648587
theorem B9470621 : Blo 1750576 9470621 := bstep (se 3 (by rfl) ⟨1775741, by rfl⟩ : syracuseStep 9470621 = 3551483) B3551483
theorem B3941225 : Blo 1750576 3941225 := bstep (se 2 (by rfl) ⟨1477959, by rfl⟩ : syracuseStep 3941225 = 2955919) B2955919
theorem B3941567 : Blo 1750576 3941567 := bstep (se 1 (by rfl) ⟨2956175, by rfl⟩ : syracuseStep 3941567 = 5912351) B5912351
theorem B107832701 : Blo 1750576 107832701 := bstep (se 3 (by rfl) ⟨20218631, by rfl⟩ : syracuseStep 107832701 = 40437263) B40437263
theorem B5613295 : Blo 1750576 5613295 := bstep (se 1 (by rfl) ⟨4209971, by rfl⟩ : syracuseStep 5613295 = 8419943) B8419943
theorem B47941409 : Blo 1750576 47941409 := bstep (se 2 (by rfl) ⟨17978028, by rfl⟩ : syracuseStep 47941409 = 35956057) B35956057
theorem B7104521 : Blo 1750576 7104521 := bstep (se 2 (by rfl) ⟨2664195, by rfl⟩ : syracuseStep 7104521 = 5328391) B5328391
theorem B29935655 : Blo 1750576 29935655 := bstep (se 1 (by rfl) ⟨22451741, by rfl⟩ : syracuseStep 29935655 = 44903483) B44903483
theorem B5908679 : Blo 1750576 5908679 := bstep (se 1 (by rfl) ⟨4431509, by rfl⟩ : syracuseStep 5908679 = 8863019) B8863019
theorem B21313955 : Blo 1750576 21313955 := bstep (se 1 (by rfl) ⟨15985466, by rfl⟩ : syracuseStep 21313955 = 31970933) B31970933
theorem B29944403 : Blo 1750576 29944403 := bstep (se 1 (by rfl) ⟨22458302, by rfl⟩ : syracuseStep 29944403 = 44916605) B44916605
theorem B43207343 : Blo 1750576 43207343 := bstep (se 1 (by rfl) ⟨32405507, by rfl⟩ : syracuseStep 43207343 = 64811015) B64811015
theorem B28413413 : Blo 1750576 28413413 := bstep (se 4 (by rfl) ⟨2663757, by rfl⟩ : syracuseStep 28413413 = 5327515) B5327515
theorem B3993247 : Blo 1750576 3993247 := bstep (se 1 (by rfl) ⟨2994935, by rfl⟩ : syracuseStep 3993247 = 5989871) B5989871
theorem B5910299 : Blo 1750576 5910299 := bstep (se 1 (by rfl) ⟨4432724, by rfl⟩ : syracuseStep 5910299 = 8865449) B8865449
theorem B5910623 : Blo 1750576 5910623 := bstep (se 1 (by rfl) ⟨4432967, by rfl⟩ : syracuseStep 5910623 = 8865935) B8865935
theorem B4862207 : Blo 1750576 4862207 := bstep (se 1 (by rfl) ⟨3646655, by rfl⟩ : syracuseStep 4862207 = 7293311) B7293311
theorem B5329415 : Blo 1750576 5329415 := bstep (se 1 (by rfl) ⟨3997061, by rfl⟩ : syracuseStep 5329415 = 7994123) B7994123
theorem B2626217 : Blo 1750576 2626217 := bstep (se 2 (by rfl) ⟨984831, by rfl⟩ : syracuseStep 2626217 = 1969663) B1969663
theorem B2806463 : Blo 1750576 2806463 := bstep (se 1 (by rfl) ⟨2104847, by rfl⟩ : syracuseStep 2806463 = 4209695) B4209695
theorem B4985563 : Blo 1750576 4985563 := bstep (se 1 (by rfl) ⟨3739172, by rfl⟩ : syracuseStep 4985563 = 7478345) B7478345
theorem B2626343 : Blo 1750576 2626343 := bstep (se 1 (by rfl) ⟨1969757, by rfl⟩ : syracuseStep 2626343 = 3939515) B3939515
theorem B2954191 : Blo 1750576 2954191 := bstep (se 1 (by rfl) ⟨2215643, by rfl⟩ : syracuseStep 2954191 = 4431287) B4431287
theorem B2626511 : Blo 1750576 2626511 := bstep (se 1 (by rfl) ⟨1969883, by rfl⟩ : syracuseStep 2626511 = 3939767) B3939767
theorem B2626871 : Blo 1750576 2626871 := bstep (se 1 (by rfl) ⟨1970153, by rfl⟩ : syracuseStep 2626871 = 3940307) B3940307
theorem B45520217 : Blo 1750576 45520217 := bstep (se 2 (by rfl) ⟨17070081, by rfl⟩ : syracuseStep 45520217 = 34140163) B34140163
theorem B5911919 : Blo 1750576 5911919 := bstep (se 1 (by rfl) ⟨4433939, by rfl⟩ : syracuseStep 5911919 = 8867879) B8867879
theorem B9975271 : Blo 1750576 9975271 := bstep (se 1 (by rfl) ⟨7481453, by rfl⟩ : syracuseStep 9975271 = 14962907) B14962907
theorem B4986497 : Blo 1750576 4986497 := bstep (se 2 (by rfl) ⟨1869936, by rfl⟩ : syracuseStep 4986497 = 3739873) B3739873
theorem B2627495 : Blo 1750576 2627495 := bstep (se 1 (by rfl) ⟨1970621, by rfl⟩ : syracuseStep 2627495 = 3941243) B3941243
theorem B1751071 : Blo 1750576 1751071 := bstep (se 1 (by rfl) ⟨1313303, by rfl⟩ : syracuseStep 1751071 = 2626607) B2626607
theorem B2627639 : Blo 1750576 2627639 := bstep (se 1 (by rfl) ⟨1970729, by rfl⟩ : syracuseStep 2627639 = 3941459) B3941459
theorem B2627705 : Blo 1750576 2627705 := bstep (se 2 (by rfl) ⟨985389, by rfl⟩ : syracuseStep 2627705 = 1970779) B1970779
theorem B25254179 : Blo 1750576 25254179 := bstep (se 1 (by rfl) ⟨18940634, by rfl⟩ : syracuseStep 25254179 = 37881269) B37881269
theorem B33667771 : Blo 1750576 33667771 := bstep (se 1 (by rfl) ⟨25250828, by rfl⟩ : syracuseStep 33667771 = 50501657) B50501657
theorem B3939641 : Blo 1750576 3939641 := bstep (se 2 (by rfl) ⟨1477365, by rfl⟩ : syracuseStep 3939641 = 2954731) B2954731
theorem B5610809 : Blo 1750576 5610809 := bstep (se 2 (by rfl) ⟨2104053, by rfl⟩ : syracuseStep 5610809 = 4208107) B4208107
theorem B5914079 : Blo 1750576 5914079 := bstep (se 1 (by rfl) ⟨4435559, by rfl⟩ : syracuseStep 5914079 = 8871119) B8871119
theorem B5610977 : Blo 1750576 5610977 := bstep (se 2 (by rfl) ⟨2104116, by rfl⟩ : syracuseStep 5610977 = 4208233) B4208233
theorem B30326345 : Blo 1750576 30326345 := bstep (se 2 (by rfl) ⟨11372379, by rfl⟩ : syracuseStep 30326345 = 22744759) B22744759
theorem B5914295 : Blo 1750576 5914295 := bstep (se 1 (by rfl) ⟨4435721, by rfl⟩ : syracuseStep 5914295 = 8871443) B8871443
theorem B8421403 : Blo 1750576 8421403 := bstep (se 1 (by rfl) ⟨6316052, by rfl⟩ : syracuseStep 8421403 = 12632105) B12632105
theorem B3940415 : Blo 1750576 3940415 := bstep (se 1 (by rfl) ⟨2955311, by rfl⟩ : syracuseStep 3940415 = 5910623) B5910623
theorem B3941279 : Blo 1750576 3941279 := bstep (se 1 (by rfl) ⟨2955959, by rfl⟩ : syracuseStep 3941279 = 5911919) B5911919
theorem B19957103 : Blo 1750576 19957103 := bstep (se 1 (by rfl) ⟨14967827, by rfl⟩ : syracuseStep 19957103 = 29935655) B29935655
theorem B16836119 : Blo 1750576 16836119 := bstep (se 1 (by rfl) ⟨12627089, by rfl⟩ : syracuseStep 16836119 = 25254179) B25254179
theorem B28804895 : Blo 1750576 28804895 := bstep (se 1 (by rfl) ⟨21603671, by rfl⟩ : syracuseStep 28804895 = 43207343) B43207343
theorem B3942719 : Blo 1750576 3942719 := bstep (se 1 (by rfl) ⟨2957039, by rfl⟩ : syracuseStep 3942719 = 5914079) B5914079
theorem B18942275 : Blo 1750576 18942275 := bstep (se 1 (by rfl) ⟨14206706, by rfl⟩ : syracuseStep 18942275 = 28413413) B28413413
theorem B3942863 : Blo 1750576 3942863 := bstep (se 1 (by rfl) ⟨2957147, by rfl⟩ : syracuseStep 3942863 = 5914295) B5914295
theorem B3943151 : Blo 1750576 3943151 := bstep (se 1 (by rfl) ⟨2957363, by rfl⟩ : syracuseStep 3943151 = 5914727) B5914727
theorem B1870975 : Blo 1750576 1870975 := bstep (se 1 (by rfl) ⟨1403231, by rfl⟩ : syracuseStep 1870975 = 2806463) B2806463
theorem B14962157 : Blo 1750576 14962157 := bstep (se 3 (by rfl) ⟨2805404, by rfl⟩ : syracuseStep 14962157 = 5610809) B5610809
theorem B30346811 : Blo 1750576 30346811 := bstep (se 1 (by rfl) ⟨22760108, by rfl⟩ : syracuseStep 30346811 = 45520217) B45520217
theorem B71888467 : Blo 1750576 71888467 := bstep (se 1 (by rfl) ⟨53916350, by rfl⟩ : syracuseStep 71888467 = 107832701) B107832701
theorem B6647417 : Blo 1750576 6647417 := bstep (se 2 (by rfl) ⟨2492781, by rfl⟩ : syracuseStep 6647417 = 4985563) B4985563
theorem B31960939 : Blo 1750576 31960939 := bstep (se 1 (by rfl) ⟨23970704, by rfl⟩ : syracuseStep 31960939 = 47941409) B47941409
theorem B14209303 : Blo 1750576 14209303 := bstep (se 1 (by rfl) ⟨10656977, by rfl⟩ : syracuseStep 14209303 = 21313955) B21313955
theorem B13300361 : Blo 1750576 13300361 := bstep (se 2 (by rfl) ⟨4987635, by rfl⟩ : syracuseStep 13300361 = 9975271) B9975271
theorem B2626427 : Blo 1750576 2626427 := bstep (se 1 (by rfl) ⟨1969820, by rfl⟩ : syracuseStep 2626427 = 3939641) B3939641
theorem B7484393 : Blo 1750576 7484393 := bstep (se 2 (by rfl) ⟨2806647, by rfl⟩ : syracuseStep 7484393 = 5613295) B5613295
theorem B3740651 : Blo 1750576 3740651 := bstep (se 1 (by rfl) ⟨2805488, by rfl⟩ : syracuseStep 3740651 = 5610977) B5610977
theorem B2626919 : Blo 1750576 2626919 := bstep (se 1 (by rfl) ⟨1970189, by rfl⟩ : syracuseStep 2626919 = 3940379) B3940379
theorem B18945389 : Blo 1750576 18945389 := bstep (se 3 (by rfl) ⟨3552260, by rfl⟩ : syracuseStep 18945389 = 7104521) B7104521
theorem B2627051 : Blo 1750576 2627051 := bstep (se 1 (by rfl) ⟨1970288, by rfl⟩ : syracuseStep 2627051 = 3940577) B3940577
theorem B3241471 : Blo 1750576 3241471 := bstep (se 1 (by rfl) ⟨2431103, by rfl⟩ : syracuseStep 3241471 = 4862207) B4862207
theorem B2954927 : Blo 1750576 2954927 := bstep (se 1 (by rfl) ⟨2216195, by rfl⟩ : syracuseStep 2954927 = 4432391) B4432391
theorem B3552943 : Blo 1750576 3552943 := bstep (se 1 (by rfl) ⟨2664707, by rfl⟩ : syracuseStep 3552943 = 5329415) B5329415
theorem B6313747 : Blo 1750576 6313747 := bstep (se 1 (by rfl) ⟨4735310, by rfl⟩ : syracuseStep 6313747 = 9470621) B9470621
theorem B1750811 : Blo 1750576 1750811 := bstep (se 1 (by rfl) ⟨1313108, by rfl⟩ : syracuseStep 1750811 = 2626217) B2626217
theorem B1750895 : Blo 1750576 1750895 := bstep (se 1 (by rfl) ⟨1313171, by rfl⟩ : syracuseStep 1750895 = 2626343) B2626343
theorem B2627483 : Blo 1750576 2627483 := bstep (se 1 (by rfl) ⟨1970612, by rfl⟩ : syracuseStep 2627483 = 3941225) B3941225
theorem B1751007 : Blo 1750576 1751007 := bstep (se 1 (by rfl) ⟨1313255, by rfl⟩ : syracuseStep 1751007 = 2626511) B2626511
theorem B2627711 : Blo 1750576 2627711 := bstep (se 1 (by rfl) ⟨1970783, by rfl⟩ : syracuseStep 2627711 = 3941567) B3941567
theorem B1751247 : Blo 1750576 1751247 := bstep (se 1 (by rfl) ⟨1313435, by rfl⟩ : syracuseStep 1751247 = 2626871) B2626871
theorem B44890361 : Blo 1750576 44890361 := bstep (se 2 (by rfl) ⟨16833885, by rfl⟩ : syracuseStep 44890361 = 33667771) B33667771
theorem B3324331 : Blo 1750576 3324331 := bstep (se 1 (by rfl) ⟨2493248, by rfl⟩ : syracuseStep 3324331 = 4986497) B4986497
theorem B3938921 : Blo 1750576 3938921 := bstep (se 2 (by rfl) ⟨1477095, by rfl⟩ : syracuseStep 3938921 = 2954191) B2954191
theorem B1751663 : Blo 1750576 1751663 := bstep (se 1 (by rfl) ⟨1313747, by rfl⟩ : syracuseStep 1751663 = 2627495) B2627495
theorem B1751759 : Blo 1750576 1751759 := bstep (se 1 (by rfl) ⟨1313819, by rfl⟩ : syracuseStep 1751759 = 2627639) B2627639
theorem B1751803 : Blo 1750576 1751803 := bstep (se 1 (by rfl) ⟨1313852, by rfl⟩ : syracuseStep 1751803 = 2627705) B2627705
theorem B3939119 : Blo 1750576 3939119 := bstep (se 1 (by rfl) ⟨2954339, by rfl⟩ : syracuseStep 3939119 = 5908679) B5908679
theorem B19962935 : Blo 1750576 19962935 := bstep (se 1 (by rfl) ⟨14972201, by rfl⟩ : syracuseStep 19962935 = 29944403) B29944403
theorem B5324329 : Blo 1750576 5324329 := bstep (se 2 (by rfl) ⟨1996623, by rfl⟩ : syracuseStep 5324329 = 3993247) B3993247
theorem B20217563 : Blo 1750576 20217563 := bstep (se 1 (by rfl) ⟨15163172, by rfl⟩ : syracuseStep 20217563 = 30326345) B30326345
theorem B3940199 : Blo 1750576 3940199 := bstep (se 1 (by rfl) ⟨2955149, by rfl⟩ : syracuseStep 3940199 = 5910299) B5910299
theorem B4432441 : Blo 1750576 4432441 := bstep (se 2 (by rfl) ⟨1662165, by rfl⟩ : syracuseStep 4432441 = 3324331) B3324331
theorem B4989595 : Blo 1750576 4989595 := bstep (se 1 (by rfl) ⟨3742196, by rfl⟩ : syracuseStep 4989595 = 7484393) B7484393
theorem B13304735 : Blo 1750576 13304735 := bstep (se 1 (by rfl) ⟨9978551, by rfl⟩ : syracuseStep 13304735 = 19957103) B19957103
theorem B11224079 : Blo 1750576 11224079 := bstep (se 1 (by rfl) ⟨8418059, by rfl⟩ : syracuseStep 11224079 = 16836119) B16836119
theorem B19203263 : Blo 1750576 19203263 := bstep (se 1 (by rfl) ⟨14402447, by rfl⟩ : syracuseStep 19203263 = 28804895) B28804895
theorem B29926907 : Blo 1750576 29926907 := bstep (se 1 (by rfl) ⟨22445180, by rfl⟩ : syracuseStep 29926907 = 44890361) B44890361
theorem B4737257 : Blo 1750576 4737257 := bstep (se 2 (by rfl) ⟨1776471, by rfl⟩ : syracuseStep 4737257 = 3552943) B3552943
theorem B13478375 : Blo 1750576 13478375 := bstep (se 1 (by rfl) ⟨10108781, by rfl⟩ : syracuseStep 13478375 = 20217563) B20217563
theorem B8866907 : Blo 1750576 8866907 := bstep (se 1 (by rfl) ⟨6650180, by rfl⟩ : syracuseStep 8866907 = 13300361) B13300361
theorem B2493767 : Blo 1750576 2493767 := bstep (se 1 (by rfl) ⟨1870325, by rfl⟩ : syracuseStep 2493767 = 3740651) B3740651
theorem B1969951 : Blo 1750576 1969951 := bstep (se 1 (by rfl) ⟨1477463, by rfl⟩ : syracuseStep 1969951 = 2954927) B2954927
theorem B2494633 : Blo 1750576 2494633 := bstep (se 2 (by rfl) ⟨935487, by rfl⟩ : syracuseStep 2494633 = 1870975) B1870975
theorem B12628183 : Blo 1750576 12628183 := bstep (se 1 (by rfl) ⟨9471137, by rfl⟩ : syracuseStep 12628183 = 18942275) B18942275
theorem B2625947 : Blo 1750576 2625947 := bstep (se 1 (by rfl) ⟨1969460, by rfl⟩ : syracuseStep 2625947 = 3938921) B3938921
theorem B2626079 : Blo 1750576 2626079 := bstep (se 1 (by rfl) ⟨1969559, by rfl⟩ : syracuseStep 2626079 = 3939119) B3939119
theorem B4321961 : Blo 1750576 4321961 := bstep (se 2 (by rfl) ⟨1620735, by rfl⟩ : syracuseStep 4321961 = 3241471) B3241471
theorem B13308623 : Blo 1750576 13308623 := bstep (se 1 (by rfl) ⟨9981467, by rfl⟩ : syracuseStep 13308623 = 19962935) B19962935
theorem B7099105 : Blo 1750576 7099105 := bstep (se 2 (by rfl) ⟨2662164, by rfl⟩ : syracuseStep 7099105 = 5324329) B5324329
theorem B95851289 : Blo 1750576 95851289 := bstep (se 2 (by rfl) ⟨35944233, by rfl⟩ : syracuseStep 95851289 = 71888467) B71888467
theorem B9974771 : Blo 1750576 9974771 := bstep (se 1 (by rfl) ⟨7481078, by rfl⟩ : syracuseStep 9974771 = 14962157) B14962157
theorem B8418329 : Blo 1750576 8418329 := bstep (se 2 (by rfl) ⟨3156873, by rfl⟩ : syracuseStep 8418329 = 6313747) B6313747
theorem B20231207 : Blo 1750576 20231207 := bstep (se 1 (by rfl) ⟨15173405, by rfl⟩ : syracuseStep 20231207 = 30346811) B30346811
theorem B2626799 : Blo 1750576 2626799 := bstep (se 1 (by rfl) ⟨1970099, by rfl⟩ : syracuseStep 2626799 = 3940199) B3940199
theorem B11228537 : Blo 1750576 11228537 := bstep (se 2 (by rfl) ⟨4210701, by rfl⟩ : syracuseStep 11228537 = 8421403) B8421403
theorem B2626943 : Blo 1750576 2626943 := bstep (se 1 (by rfl) ⟨1970207, by rfl⟩ : syracuseStep 2626943 = 3940415) B3940415
theorem B18945737 : Blo 1750576 18945737 := bstep (se 2 (by rfl) ⟨7104651, by rfl⟩ : syracuseStep 18945737 = 14209303) B14209303
theorem B1750951 : Blo 1750576 1750951 := bstep (se 1 (by rfl) ⟨1313213, by rfl⟩ : syracuseStep 1750951 = 2626427) B2626427
theorem B2627519 : Blo 1750576 2627519 := bstep (se 1 (by rfl) ⟨1970639, by rfl⟩ : syracuseStep 2627519 = 3941279) B3941279
theorem B1751279 : Blo 1750576 1751279 := bstep (se 1 (by rfl) ⟨1313459, by rfl⟩ : syracuseStep 1751279 = 2626919) B2626919
theorem B12630259 : Blo 1750576 12630259 := bstep (se 1 (by rfl) ⟨9472694, by rfl⟩ : syracuseStep 12630259 = 18945389) B18945389
theorem B1751367 : Blo 1750576 1751367 := bstep (se 1 (by rfl) ⟨1313525, by rfl⟩ : syracuseStep 1751367 = 2627051) B2627051
theorem B1751655 : Blo 1750576 1751655 := bstep (se 1 (by rfl) ⟨1313741, by rfl⟩ : syracuseStep 1751655 = 2627483) B2627483
theorem B1751807 : Blo 1750576 1751807 := bstep (se 1 (by rfl) ⟨1313855, by rfl⟩ : syracuseStep 1751807 = 2627711) B2627711
theorem B2628479 : Blo 1750576 2628479 := bstep (se 1 (by rfl) ⟨1971359, by rfl⟩ : syracuseStep 2628479 = 3942719) B3942719
theorem B2628575 : Blo 1750576 2628575 := bstep (se 1 (by rfl) ⟨1971431, by rfl⟩ : syracuseStep 2628575 = 3942863) B3942863
theorem B2628767 : Blo 1750576 2628767 := bstep (se 1 (by rfl) ⟨1971575, by rfl⟩ : syracuseStep 2628767 = 3943151) B3943151
theorem B4431611 : Blo 1750576 4431611 := bstep (se 1 (by rfl) ⟨3323708, by rfl⟩ : syracuseStep 4431611 = 6647417) B6647417
theorem B42614585 : Blo 1750576 42614585 := bstep (se 2 (by rfl) ⟨15980469, by rfl⟩ : syracuseStep 42614585 = 31960939) B31960939
theorem B3326177 : Blo 1750576 3326177 := bstep (se 2 (by rfl) ⟨1247316, by rfl⟩ : syracuseStep 3326177 = 2494633) B2494633
theorem B8872415 : Blo 1750576 8872415 := bstep (se 1 (by rfl) ⟨6654311, by rfl⟩ : syracuseStep 8872415 = 13308623) B13308623
theorem B5612219 : Blo 1750576 5612219 := bstep (se 1 (by rfl) ⟨4209164, by rfl⟩ : syracuseStep 5612219 = 8418329) B8418329
theorem B6652793 : Blo 1750576 6652793 := bstep (se 2 (by rfl) ⟨2494797, by rfl⟩ : syracuseStep 6652793 = 4989595) B4989595
theorem B16837577 : Blo 1750576 16837577 := bstep (se 2 (by rfl) ⟨6314091, by rfl⟩ : syracuseStep 16837577 = 12628183) B12628183
theorem B63900859 : Blo 1750576 63900859 := bstep (se 1 (by rfl) ⟨47925644, by rfl⟩ : syracuseStep 63900859 = 95851289) B95851289
theorem B7482719 : Blo 1750576 7482719 := bstep (se 1 (by rfl) ⟨5612039, by rfl⟩ : syracuseStep 7482719 = 11224079) B11224079
theorem B13487471 : Blo 1750576 13487471 := bstep (se 1 (by rfl) ⟨10115603, by rfl⟩ : syracuseStep 13487471 = 20231207) B20231207
theorem B5909921 : Blo 1750576 5909921 := bstep (se 2 (by rfl) ⟨2216220, by rfl⟩ : syracuseStep 5909921 = 4432441) B4432441
theorem B9465473 : Blo 1750576 9465473 := bstep (se 2 (by rfl) ⟨3549552, by rfl⟩ : syracuseStep 9465473 = 7099105) B7099105
theorem B19951271 : Blo 1750576 19951271 := bstep (se 1 (by rfl) ⟨14963453, by rfl⟩ : syracuseStep 19951271 = 29926907) B29926907
theorem B3158171 : Blo 1750576 3158171 := bstep (se 1 (by rfl) ⟨2368628, by rfl⟩ : syracuseStep 3158171 = 4737257) B4737257
theorem B5911271 : Blo 1750576 5911271 := bstep (se 1 (by rfl) ⟨4433453, by rfl⟩ : syracuseStep 5911271 = 8866907) B8866907
theorem B2626601 : Blo 1750576 2626601 := bstep (se 2 (by rfl) ⟨984975, by rfl⟩ : syracuseStep 2626601 = 1969951) B1969951
theorem B2954407 : Blo 1750576 2954407 := bstep (se 1 (by rfl) ⟨2215805, by rfl⟩ : syracuseStep 2954407 = 4431611) B4431611
theorem B1750631 : Blo 1750576 1750631 := bstep (se 1 (by rfl) ⟨1312973, by rfl⟩ : syracuseStep 1750631 = 2625947) B2625947
theorem B16840345 : Blo 1750576 16840345 := bstep (se 2 (by rfl) ⟨6315129, by rfl⟩ : syracuseStep 16840345 = 12630259) B12630259
theorem B1750719 : Blo 1750576 1750719 := bstep (se 1 (by rfl) ⟨1313039, by rfl⟩ : syracuseStep 1750719 = 2626079) B2626079
theorem B2881307 : Blo 1750576 2881307 := bstep (se 1 (by rfl) ⟨2160980, by rfl⟩ : syracuseStep 2881307 = 4321961) B4321961
theorem B8869823 : Blo 1750576 8869823 := bstep (se 1 (by rfl) ⟨6652367, by rfl⟩ : syracuseStep 8869823 = 13304735) B13304735
theorem B6649847 : Blo 1750576 6649847 := bstep (se 1 (by rfl) ⟨4987385, by rfl⟩ : syracuseStep 6649847 = 9974771) B9974771
theorem B12802175 : Blo 1750576 12802175 := bstep (se 1 (by rfl) ⟨9601631, by rfl⟩ : syracuseStep 12802175 = 19203263) B19203263
theorem B1751199 : Blo 1750576 1751199 := bstep (se 1 (by rfl) ⟨1313399, by rfl⟩ : syracuseStep 1751199 = 2626799) B2626799
theorem B6650045 : Blo 1750576 6650045 := bstep (se 3 (by rfl) ⟨1246883, by rfl⟩ : syracuseStep 6650045 = 2493767) B2493767
theorem B7485691 : Blo 1750576 7485691 := bstep (se 1 (by rfl) ⟨5614268, by rfl⟩ : syracuseStep 7485691 = 11228537) B11228537
theorem B1751295 : Blo 1750576 1751295 := bstep (se 1 (by rfl) ⟨1313471, by rfl⟩ : syracuseStep 1751295 = 2626943) B2626943
theorem B12630491 : Blo 1750576 12630491 := bstep (se 1 (by rfl) ⟨9472868, by rfl⟩ : syracuseStep 12630491 = 18945737) B18945737
theorem B1751679 : Blo 1750576 1751679 := bstep (se 1 (by rfl) ⟨1313759, by rfl⟩ : syracuseStep 1751679 = 2627519) B2627519
theorem B8985583 : Blo 1750576 8985583 := bstep (se 1 (by rfl) ⟨6739187, by rfl⟩ : syracuseStep 8985583 = 13478375) B13478375
theorem B1752319 : Blo 1750576 1752319 := bstep (se 1 (by rfl) ⟨1314239, by rfl⟩ : syracuseStep 1752319 = 2628479) B2628479
theorem B1752383 : Blo 1750576 1752383 := bstep (se 1 (by rfl) ⟨1314287, by rfl⟩ : syracuseStep 1752383 = 2628575) B2628575
theorem B1752511 : Blo 1750576 1752511 := bstep (se 1 (by rfl) ⟨1314383, by rfl⟩ : syracuseStep 1752511 = 2628767) B2628767
theorem B28409723 : Blo 1750576 28409723 := bstep (se 1 (by rfl) ⟨21307292, by rfl⟩ : syracuseStep 28409723 = 42614585) B42614585
theorem B2105447 : Blo 1750576 2105447 := bstep (se 1 (by rfl) ⟨1579085, by rfl⟩ : syracuseStep 2105447 = 3158171) B3158171
theorem B5914943 : Blo 1750576 5914943 := bstep (se 1 (by rfl) ⟨4436207, by rfl⟩ : syracuseStep 5914943 = 8872415) B8872415
theorem B3940847 : Blo 1750576 3940847 := bstep (se 1 (by rfl) ⟨2955635, by rfl⟩ : syracuseStep 3940847 = 5911271) B5911271
theorem B4433231 : Blo 1750576 4433231 := bstep (se 1 (by rfl) ⟨3324923, by rfl⟩ : syracuseStep 4433231 = 6649847) B6649847
theorem B4433363 : Blo 1750576 4433363 := bstep (se 1 (by rfl) ⟨3325022, by rfl⟩ : syracuseStep 4433363 = 6650045) B6650045
theorem B11225051 : Blo 1750576 11225051 := bstep (se 1 (by rfl) ⟨8418788, by rfl⟩ : syracuseStep 11225051 = 16837577) B16837577
theorem B6310315 : Blo 1750576 6310315 := bstep (se 1 (by rfl) ⟨4732736, by rfl⟩ : syracuseStep 6310315 = 9465473) B9465473
theorem B9980921 : Blo 1750576 9980921 := bstep (se 2 (by rfl) ⟨3742845, by rfl⟩ : syracuseStep 9980921 = 7485691) B7485691
theorem B4435195 : Blo 1750576 4435195 := bstep (se 1 (by rfl) ⟨3326396, by rfl⟩ : syracuseStep 4435195 = 6652793) B6652793
theorem B1920871 : Blo 1750576 1920871 := bstep (se 1 (by rfl) ⟨1440653, by rfl⟩ : syracuseStep 1920871 = 2881307) B2881307
theorem B85201145 : Blo 1750576 85201145 := bstep (se 2 (by rfl) ⟨31950429, by rfl⟩ : syracuseStep 85201145 = 63900859) B63900859
theorem B8991647 : Blo 1750576 8991647 := bstep (se 1 (by rfl) ⟨6743735, by rfl⟩ : syracuseStep 8991647 = 13487471) B13487471
theorem B13300847 : Blo 1750576 13300847 := bstep (se 1 (by rfl) ⟨9975635, by rfl⟩ : syracuseStep 13300847 = 19951271) B19951271
theorem B2217451 : Blo 1750576 2217451 := bstep (se 1 (by rfl) ⟨1663088, by rfl⟩ : syracuseStep 2217451 = 3326177) B3326177
theorem B3741479 : Blo 1750576 3741479 := bstep (se 1 (by rfl) ⟨2806109, by rfl⟩ : syracuseStep 3741479 = 5612219) B5612219
theorem B1751067 : Blo 1750576 1751067 := bstep (se 1 (by rfl) ⟨1313300, by rfl⟩ : syracuseStep 1751067 = 2626601) B2626601
theorem B5913215 : Blo 1750576 5913215 := bstep (se 1 (by rfl) ⟨4434911, by rfl⟩ : syracuseStep 5913215 = 8869823) B8869823
theorem B8534783 : Blo 1750576 8534783 := bstep (se 1 (by rfl) ⟨6401087, by rfl⟩ : syracuseStep 8534783 = 12802175) B12802175
theorem B3939209 : Blo 1750576 3939209 := bstep (se 2 (by rfl) ⟨1477203, by rfl⟩ : syracuseStep 3939209 = 2954407) B2954407
theorem B8420327 : Blo 1750576 8420327 := bstep (se 1 (by rfl) ⟨6315245, by rfl⟩ : syracuseStep 8420327 = 12630491) B12630491
theorem B22453793 : Blo 1750576 22453793 := bstep (se 2 (by rfl) ⟨8420172, by rfl⟩ : syracuseStep 22453793 = 16840345) B16840345
theorem B4988479 : Blo 1750576 4988479 := bstep (se 1 (by rfl) ⟨3741359, by rfl⟩ : syracuseStep 4988479 = 7482719) B7482719
theorem B3939947 : Blo 1750576 3939947 := bstep (se 1 (by rfl) ⟨2954960, by rfl⟩ : syracuseStep 3939947 = 5909921) B5909921
theorem B47923109 : Blo 1750576 47923109 := bstep (se 4 (by rfl) ⟨4492791, by rfl⟩ : syracuseStep 47923109 = 8985583) B8985583
theorem B18939815 : Blo 1750576 18939815 := bstep (se 1 (by rfl) ⟨14204861, by rfl⟩ : syracuseStep 18939815 = 28409723) B28409723
theorem B3942143 : Blo 1750576 3942143 := bstep (se 1 (by rfl) ⟨2956607, by rfl⟩ : syracuseStep 3942143 = 5913215) B5913215
theorem B5613551 : Blo 1750576 5613551 := bstep (se 1 (by rfl) ⟨4210163, by rfl⟩ : syracuseStep 5613551 = 8420327) B8420327
theorem B6653947 : Blo 1750576 6653947 := bstep (se 1 (by rfl) ⟨4990460, by rfl⟩ : syracuseStep 6653947 = 9980921) B9980921
theorem B33655013 : Blo 1750576 33655013 := bstep (se 4 (by rfl) ⟨3155157, by rfl⟩ : syracuseStep 33655013 = 6310315) B6310315
theorem B14969195 : Blo 1750576 14969195 := bstep (se 1 (by rfl) ⟨11226896, by rfl⟩ : syracuseStep 14969195 = 22453793) B22453793
theorem B12626543 : Blo 1750576 12626543 := bstep (se 1 (by rfl) ⟨9469907, by rfl⟩ : syracuseStep 12626543 = 18939815) B18939815
theorem B3943295 : Blo 1750576 3943295 := bstep (se 1 (by rfl) ⟨2957471, by rfl⟩ : syracuseStep 3943295 = 5914943) B5914943
theorem B5614525 : Blo 1750576 5614525 := bstep (se 3 (by rfl) ⟨1052723, by rfl⟩ : syracuseStep 5614525 = 2105447) B2105447
theorem B8867231 : Blo 1750576 8867231 := bstep (se 1 (by rfl) ⟨6650423, by rfl⟩ : syracuseStep 8867231 = 13300847) B13300847
theorem B2494319 : Blo 1750576 2494319 := bstep (se 1 (by rfl) ⟨1870739, by rfl⟩ : syracuseStep 2494319 = 3741479) B3741479
theorem B7483367 : Blo 1750576 7483367 := bstep (se 1 (by rfl) ⟨5612525, by rfl⟩ : syracuseStep 7483367 = 11225051) B11225051
theorem B5689855 : Blo 1750576 5689855 := bstep (se 1 (by rfl) ⟨4267391, by rfl⟩ : syracuseStep 5689855 = 8534783) B8534783
theorem B2626139 : Blo 1750576 2626139 := bstep (se 1 (by rfl) ⟨1969604, by rfl⟩ : syracuseStep 2626139 = 3939209) B3939209
theorem B2626631 : Blo 1750576 2626631 := bstep (se 1 (by rfl) ⟨1969973, by rfl⟩ : syracuseStep 2626631 = 3939947) B3939947
theorem B2561161 : Blo 1750576 2561161 := bstep (se 2 (by rfl) ⟨960435, by rfl⟩ : syracuseStep 2561161 = 1920871) B1920871
theorem B56800763 : Blo 1750576 56800763 := bstep (se 1 (by rfl) ⟨42600572, by rfl⟩ : syracuseStep 56800763 = 85201145) B85201145
theorem B2627231 : Blo 1750576 2627231 := bstep (se 1 (by rfl) ⟨1970423, by rfl⟩ : syracuseStep 2627231 = 3940847) B3940847
theorem B5994431 : Blo 1750576 5994431 := bstep (se 1 (by rfl) ⟨4495823, by rfl⟩ : syracuseStep 5994431 = 8991647) B8991647
theorem B2955487 : Blo 1750576 2955487 := bstep (se 1 (by rfl) ⟨2216615, by rfl⟩ : syracuseStep 2955487 = 4433231) B4433231
theorem B2955575 : Blo 1750576 2955575 := bstep (se 1 (by rfl) ⟨2216681, by rfl⟩ : syracuseStep 2955575 = 4433363) B4433363
theorem B5913593 : Blo 1750576 5913593 := bstep (se 2 (by rfl) ⟨2217597, by rfl⟩ : syracuseStep 5913593 = 4435195) B4435195
theorem B2956601 : Blo 1750576 2956601 := bstep (se 2 (by rfl) ⟨1108725, by rfl⟩ : syracuseStep 2956601 = 2217451) B2217451
theorem B6651305 : Blo 1750576 6651305 := bstep (se 2 (by rfl) ⟨2494239, by rfl⟩ : syracuseStep 6651305 = 4988479) B4988479
theorem B31948739 : Blo 1750576 31948739 := bstep (se 1 (by rfl) ⟨23961554, by rfl⟩ : syracuseStep 31948739 = 47923109) B47923109
theorem B3940649 : Blo 1750576 3940649 := bstep (se 2 (by rfl) ⟨1477743, by rfl⟩ : syracuseStep 3940649 = 2955487) B2955487
theorem B7586473 : Blo 1750576 7586473 := bstep (se 2 (by rfl) ⟨2844927, by rfl⟩ : syracuseStep 7586473 = 5689855) B5689855
theorem B9979463 : Blo 1750576 9979463 := bstep (se 1 (by rfl) ⟨7484597, by rfl⟩ : syracuseStep 9979463 = 14969195) B14969195
theorem B3942395 : Blo 1750576 3942395 := bstep (se 1 (by rfl) ⟨2956796, by rfl⟩ : syracuseStep 3942395 = 5913593) B5913593
theorem B4434203 : Blo 1750576 4434203 := bstep (se 1 (by rfl) ⟨3325652, by rfl⟩ : syracuseStep 4434203 = 6651305) B6651305
theorem B37867175 : Blo 1750576 37867175 := bstep (se 1 (by rfl) ⟨28400381, by rfl⟩ : syracuseStep 37867175 = 56800763) B56800763
theorem B1970383 : Blo 1750576 1970383 := bstep (se 1 (by rfl) ⟨1477787, by rfl⟩ : syracuseStep 1970383 = 2955575) B2955575
theorem B8417695 : Blo 1750576 8417695 := bstep (se 1 (by rfl) ⟨6313271, by rfl⟩ : syracuseStep 8417695 = 12626543) B12626543
theorem B1971067 : Blo 1750576 1971067 := bstep (se 1 (by rfl) ⟨1478300, by rfl⟩ : syracuseStep 1971067 = 2956601) B2956601
theorem B5911487 : Blo 1750576 5911487 := bstep (se 1 (by rfl) ⟨4433615, by rfl⟩ : syracuseStep 5911487 = 8867231) B8867231
theorem B1750759 : Blo 1750576 1750759 := bstep (se 1 (by rfl) ⟨1313069, by rfl⟩ : syracuseStep 1750759 = 2626139) B2626139
theorem B1751087 : Blo 1750576 1751087 := bstep (se 1 (by rfl) ⟨1313315, by rfl⟩ : syracuseStep 1751087 = 2626631) B2626631
theorem B1751487 : Blo 1750576 1751487 := bstep (se 1 (by rfl) ⟨1313615, by rfl⟩ : syracuseStep 1751487 = 2627231) B2627231
theorem B2628095 : Blo 1750576 2628095 := bstep (se 1 (by rfl) ⟨1971071, by rfl⟩ : syracuseStep 2628095 = 3942143) B3942143
theorem B7486033 : Blo 1750576 7486033 := bstep (se 2 (by rfl) ⟨2807262, by rfl⟩ : syracuseStep 7486033 = 5614525) B5614525
theorem B3996287 : Blo 1750576 3996287 := bstep (se 1 (by rfl) ⟨2997215, by rfl⟩ : syracuseStep 3996287 = 5994431) B5994431
theorem B3742367 : Blo 1750576 3742367 := bstep (se 1 (by rfl) ⟨2806775, by rfl⟩ : syracuseStep 3742367 = 5613551) B5613551
theorem B22436675 : Blo 1750576 22436675 := bstep (se 1 (by rfl) ⟨16827506, by rfl⟩ : syracuseStep 22436675 = 33655013) B33655013
theorem B3414881 : Blo 1750576 3414881 := bstep (se 2 (by rfl) ⟨1280580, by rfl⟩ : syracuseStep 3414881 = 2561161) B2561161
theorem B2628863 : Blo 1750576 2628863 := bstep (se 1 (by rfl) ⟨1971647, by rfl⟩ : syracuseStep 2628863 = 3943295) B3943295
theorem B6651517 : Blo 1750576 6651517 := bstep (se 3 (by rfl) ⟨1247159, by rfl⟩ : syracuseStep 6651517 = 2494319) B2494319
theorem B19955645 : Blo 1750576 19955645 := bstep (se 3 (by rfl) ⟨3741683, by rfl⟩ : syracuseStep 19955645 = 7483367) B7483367
theorem B21299159 : Blo 1750576 21299159 := bstep (se 1 (by rfl) ⟨15974369, by rfl⟩ : syracuseStep 21299159 = 31948739) B31948739
theorem B8871929 : Blo 1750576 8871929 := bstep (se 2 (by rfl) ⟨3326973, by rfl⟩ : syracuseStep 8871929 = 6653947) B6653947
theorem B11223593 : Blo 1750576 11223593 := bstep (se 2 (by rfl) ⟨4208847, by rfl⟩ : syracuseStep 11223593 = 8417695) B8417695
theorem B3940991 : Blo 1750576 3940991 := bstep (se 1 (by rfl) ⟨2955743, by rfl⟩ : syracuseStep 3940991 = 5911487) B5911487
theorem B6652975 : Blo 1750576 6652975 := bstep (se 1 (by rfl) ⟨4989731, by rfl⟩ : syracuseStep 6652975 = 9979463) B9979463
theorem B9979645 : Blo 1750576 9979645 := bstep (se 3 (by rfl) ⟨1871183, by rfl⟩ : syracuseStep 9979645 = 3742367) B3742367
theorem B2664191 : Blo 1750576 2664191 := bstep (se 1 (by rfl) ⟨1998143, by rfl⟩ : syracuseStep 2664191 = 3996287) B3996287
theorem B56797757 : Blo 1750576 56797757 := bstep (se 3 (by rfl) ⟨10649579, by rfl⟩ : syracuseStep 56797757 = 21299159) B21299159
theorem B9981377 : Blo 1750576 9981377 := bstep (se 2 (by rfl) ⟨3743016, by rfl⟩ : syracuseStep 9981377 = 7486033) B7486033
theorem B8868689 : Blo 1750576 8868689 := bstep (se 2 (by rfl) ⟨3325758, by rfl⟩ : syracuseStep 8868689 = 6651517) B6651517
theorem B25244783 : Blo 1750576 25244783 := bstep (se 1 (by rfl) ⟨18933587, by rfl⟩ : syracuseStep 25244783 = 37867175) B37867175
theorem B2627099 : Blo 1750576 2627099 := bstep (se 1 (by rfl) ⟨1970324, by rfl⟩ : syracuseStep 2627099 = 3940649) B3940649
theorem B2627177 : Blo 1750576 2627177 := bstep (se 2 (by rfl) ⟨985191, by rfl⟩ : syracuseStep 2627177 = 1970383) B1970383
theorem B10115297 : Blo 1750576 10115297 := bstep (se 2 (by rfl) ⟨3793236, by rfl⟩ : syracuseStep 10115297 = 7586473) B7586473
theorem B2628089 : Blo 1750576 2628089 := bstep (se 2 (by rfl) ⟨985533, by rfl⟩ : syracuseStep 2628089 = 1971067) B1971067
theorem B2628263 : Blo 1750576 2628263 := bstep (se 1 (by rfl) ⟨1971197, by rfl⟩ : syracuseStep 2628263 = 3942395) B3942395
theorem B2956135 : Blo 1750576 2956135 := bstep (se 1 (by rfl) ⟨2217101, by rfl⟩ : syracuseStep 2956135 = 4434203) B4434203
theorem B1752063 : Blo 1750576 1752063 := bstep (se 1 (by rfl) ⟨1314047, by rfl⟩ : syracuseStep 1752063 = 2628095) B2628095
theorem B14957783 : Blo 1750576 14957783 := bstep (se 1 (by rfl) ⟨11218337, by rfl⟩ : syracuseStep 14957783 = 22436675) B22436675
theorem B2276587 : Blo 1750576 2276587 := bstep (se 1 (by rfl) ⟨1707440, by rfl⟩ : syracuseStep 2276587 = 3414881) B3414881
theorem B1752575 : Blo 1750576 1752575 := bstep (se 1 (by rfl) ⟨1314431, by rfl⟩ : syracuseStep 1752575 = 2628863) B2628863
theorem B13303763 : Blo 1750576 13303763 := bstep (se 1 (by rfl) ⟨9977822, by rfl⟩ : syracuseStep 13303763 = 19955645) B19955645
theorem B5914619 : Blo 1750576 5914619 := bstep (se 1 (by rfl) ⟨4435964, by rfl⟩ : syracuseStep 5914619 = 8871929) B8871929
theorem B3941513 : Blo 1750576 3941513 := bstep (se 2 (by rfl) ⟨1478067, by rfl⟩ : syracuseStep 3941513 = 2956135) B2956135
theorem B6743531 : Blo 1750576 6743531 := bstep (se 1 (by rfl) ⟨5057648, by rfl⟩ : syracuseStep 6743531 = 10115297) B10115297
theorem B37865171 : Blo 1750576 37865171 := bstep (se 1 (by rfl) ⟨28398878, by rfl⟩ : syracuseStep 37865171 = 56797757) B56797757
theorem B7104509 : Blo 1750576 7104509 := bstep (se 3 (by rfl) ⟨1332095, by rfl⟩ : syracuseStep 7104509 = 2664191) B2664191
theorem B9971855 : Blo 1750576 9971855 := bstep (se 1 (by rfl) ⟨7478891, by rfl⟩ : syracuseStep 9971855 = 14957783) B14957783
theorem B6654251 : Blo 1750576 6654251 := bstep (se 1 (by rfl) ⟨4990688, by rfl⟩ : syracuseStep 6654251 = 9981377) B9981377
theorem B13306193 : Blo 1750576 13306193 := bstep (se 2 (by rfl) ⟨4989822, by rfl⟩ : syracuseStep 13306193 = 9979645) B9979645
theorem B3943079 : Blo 1750576 3943079 := bstep (se 1 (by rfl) ⟨2957309, by rfl⟩ : syracuseStep 3943079 = 5914619) B5914619
theorem B7482395 : Blo 1750576 7482395 := bstep (se 1 (by rfl) ⟨5611796, by rfl⟩ : syracuseStep 7482395 = 11223593) B11223593
theorem B16829855 : Blo 1750576 16829855 := bstep (se 1 (by rfl) ⟨12622391, by rfl⟩ : syracuseStep 16829855 = 25244783) B25244783
theorem B3035449 : Blo 1750576 3035449 := bstep (se 2 (by rfl) ⟨1138293, by rfl⟩ : syracuseStep 3035449 = 2276587) B2276587
theorem B8869175 : Blo 1750576 8869175 := bstep (se 1 (by rfl) ⟨6651881, by rfl⟩ : syracuseStep 8869175 = 13303763) B13303763
theorem B2627327 : Blo 1750576 2627327 := bstep (se 1 (by rfl) ⟨1970495, by rfl⟩ : syracuseStep 2627327 = 3940991) B3940991
theorem B5912459 : Blo 1750576 5912459 := bstep (se 1 (by rfl) ⟨4434344, by rfl⟩ : syracuseStep 5912459 = 8868689) B8868689
theorem B1751399 : Blo 1750576 1751399 := bstep (se 1 (by rfl) ⟨1313549, by rfl⟩ : syracuseStep 1751399 = 2627099) B2627099
theorem B1751451 : Blo 1750576 1751451 := bstep (se 1 (by rfl) ⟨1313588, by rfl⟩ : syracuseStep 1751451 = 2627177) B2627177
theorem B8870633 : Blo 1750576 8870633 := bstep (se 2 (by rfl) ⟨3326487, by rfl⟩ : syracuseStep 8870633 = 6652975) B6652975
theorem B1752059 : Blo 1750576 1752059 := bstep (se 1 (by rfl) ⟨1314044, by rfl⟩ : syracuseStep 1752059 = 2628089) B2628089
theorem B1752175 : Blo 1750576 1752175 := bstep (se 1 (by rfl) ⟨1314131, by rfl⟩ : syracuseStep 1752175 = 2628263) B2628263
theorem B4047265 : Blo 1750576 4047265 := bstep (se 2 (by rfl) ⟨1517724, by rfl⟩ : syracuseStep 4047265 = 3035449) B3035449
theorem B3941639 : Blo 1750576 3941639 := bstep (se 1 (by rfl) ⟨2956229, by rfl⟩ : syracuseStep 3941639 = 5912459) B5912459
theorem B17982749 : Blo 1750576 17982749 := bstep (se 3 (by rfl) ⟨3371765, by rfl⟩ : syracuseStep 17982749 = 6743531) B6743531
theorem B4736339 : Blo 1750576 4736339 := bstep (se 1 (by rfl) ⟨3552254, by rfl⟩ : syracuseStep 4736339 = 7104509) B7104509
theorem B6647903 : Blo 1750576 6647903 := bstep (se 1 (by rfl) ⟨4985927, by rfl⟩ : syracuseStep 6647903 = 9971855) B9971855
theorem B4436167 : Blo 1750576 4436167 := bstep (se 1 (by rfl) ⟨3327125, by rfl⟩ : syracuseStep 4436167 = 6654251) B6654251
theorem B11219903 : Blo 1750576 11219903 := bstep (se 1 (by rfl) ⟨8414927, by rfl⟩ : syracuseStep 11219903 = 16829855) B16829855
theorem B2627675 : Blo 1750576 2627675 := bstep (se 1 (by rfl) ⟨1970756, by rfl⟩ : syracuseStep 2627675 = 3941513) B3941513
theorem B5912783 : Blo 1750576 5912783 := bstep (se 1 (by rfl) ⟨4434587, by rfl⟩ : syracuseStep 5912783 = 8869175) B8869175
theorem B1751551 : Blo 1750576 1751551 := bstep (se 1 (by rfl) ⟨1313663, by rfl⟩ : syracuseStep 1751551 = 2627327) B2627327
theorem B8870795 : Blo 1750576 8870795 := bstep (se 1 (by rfl) ⟨6653096, by rfl⟩ : syracuseStep 8870795 = 13306193) B13306193
theorem B2628719 : Blo 1750576 2628719 := bstep (se 1 (by rfl) ⟨1971539, by rfl⟩ : syracuseStep 2628719 = 3943079) B3943079
theorem B5913755 : Blo 1750576 5913755 := bstep (se 1 (by rfl) ⟨4435316, by rfl⟩ : syracuseStep 5913755 = 8870633) B8870633
theorem B100973789 : Blo 1750576 100973789 := bstep (se 3 (by rfl) ⟨18932585, by rfl⟩ : syracuseStep 100973789 = 37865171) B37865171
theorem B4988263 : Blo 1750576 4988263 := bstep (se 1 (by rfl) ⟨3741197, by rfl⟩ : syracuseStep 4988263 = 7482395) B7482395
theorem B4431935 : Blo 1750576 4431935 := bstep (se 1 (by rfl) ⟨3323951, by rfl⟩ : syracuseStep 4431935 = 6647903) B6647903
theorem B5914889 : Blo 1750576 5914889 := bstep (se 2 (by rfl) ⟨2218083, by rfl⟩ : syracuseStep 5914889 = 4436167) B4436167
theorem B7479935 : Blo 1750576 7479935 := bstep (se 1 (by rfl) ⟨5609951, by rfl⟩ : syracuseStep 7479935 = 11219903) B11219903
theorem B3941855 : Blo 1750576 3941855 := bstep (se 1 (by rfl) ⟨2956391, by rfl⟩ : syracuseStep 3941855 = 5912783) B5912783
theorem B3942503 : Blo 1750576 3942503 := bstep (se 1 (by rfl) ⟨2956877, by rfl⟩ : syracuseStep 3942503 = 5913755) B5913755
theorem B67315859 : Blo 1750576 67315859 := bstep (se 1 (by rfl) ⟨50486894, by rfl⟩ : syracuseStep 67315859 = 100973789) B100973789
theorem B11988499 : Blo 1750576 11988499 := bstep (se 1 (by rfl) ⟨8991374, by rfl⟩ : syracuseStep 11988499 = 17982749) B17982749
theorem B3157559 : Blo 1750576 3157559 := bstep (se 1 (by rfl) ⟨2368169, by rfl⟩ : syracuseStep 3157559 = 4736339) B4736339
theorem B2627759 : Blo 1750576 2627759 := bstep (se 1 (by rfl) ⟨1970819, by rfl⟩ : syracuseStep 2627759 = 3941639) B3941639
theorem B1751783 : Blo 1750576 1751783 := bstep (se 1 (by rfl) ⟨1313837, by rfl⟩ : syracuseStep 1751783 = 2627675) B2627675
theorem B6651017 : Blo 1750576 6651017 := bstep (se 2 (by rfl) ⟨2494131, by rfl⟩ : syracuseStep 6651017 = 4988263) B4988263
theorem B5913863 : Blo 1750576 5913863 := bstep (se 1 (by rfl) ⟨4435397, by rfl⟩ : syracuseStep 5913863 = 8870795) B8870795
theorem B1752479 : Blo 1750576 1752479 := bstep (se 1 (by rfl) ⟨1314359, by rfl⟩ : syracuseStep 1752479 = 2628719) B2628719
theorem B21585413 : Blo 1750576 21585413 := bstep (se 4 (by rfl) ⟨2023632, by rfl⟩ : syracuseStep 21585413 = 4047265) B4047265
theorem B44877239 : Blo 1750576 44877239 := bstep (se 1 (by rfl) ⟨33657929, by rfl⟩ : syracuseStep 44877239 = 67315859) B67315859
theorem B15984665 : Blo 1750576 15984665 := bstep (se 2 (by rfl) ⟨5994249, by rfl⟩ : syracuseStep 15984665 = 11988499) B11988499
theorem B4434011 : Blo 1750576 4434011 := bstep (se 1 (by rfl) ⟨3325508, by rfl⟩ : syracuseStep 4434011 = 6651017) B6651017
theorem B3942575 : Blo 1750576 3942575 := bstep (se 1 (by rfl) ⟨2956931, by rfl⟩ : syracuseStep 3942575 = 5913863) B5913863
theorem B3943259 : Blo 1750576 3943259 := bstep (se 1 (by rfl) ⟨2957444, by rfl⟩ : syracuseStep 3943259 = 5914889) B5914889
theorem B57561101 : Blo 1750576 57561101 := bstep (se 3 (by rfl) ⟨10792706, by rfl⟩ : syracuseStep 57561101 = 21585413) B21585413
theorem B2954623 : Blo 1750576 2954623 := bstep (se 1 (by rfl) ⟨2215967, by rfl⟩ : syracuseStep 2954623 = 4431935) B4431935
theorem B4986623 : Blo 1750576 4986623 := bstep (se 1 (by rfl) ⟨3739967, by rfl⟩ : syracuseStep 4986623 = 7479935) B7479935
theorem B2627903 : Blo 1750576 2627903 := bstep (se 1 (by rfl) ⟨1970927, by rfl⟩ : syracuseStep 2627903 = 3941855) B3941855
theorem B2628335 : Blo 1750576 2628335 := bstep (se 1 (by rfl) ⟨1971251, by rfl⟩ : syracuseStep 2628335 = 3942503) B3942503
theorem B1751839 : Blo 1750576 1751839 := bstep (se 1 (by rfl) ⟨1313879, by rfl⟩ : syracuseStep 1751839 = 2627759) B2627759
theorem B2105039 : Blo 1750576 2105039 := bstep (se 1 (by rfl) ⟨1578779, by rfl⟩ : syracuseStep 2105039 = 3157559) B3157559
theorem B29918159 : Blo 1750576 29918159 := bstep (se 1 (by rfl) ⟨22438619, by rfl⟩ : syracuseStep 29918159 = 44877239) B44877239
theorem B5613437 : Blo 1750576 5613437 := bstep (se 3 (by rfl) ⟨1052519, by rfl⟩ : syracuseStep 5613437 = 2105039) B2105039
theorem B38374067 : Blo 1750576 38374067 := bstep (se 1 (by rfl) ⟨28780550, by rfl⟩ : syracuseStep 38374067 = 57561101) B57561101
theorem B3324415 : Blo 1750576 3324415 := bstep (se 1 (by rfl) ⟨2493311, by rfl⟩ : syracuseStep 3324415 = 4986623) B4986623
theorem B10656443 : Blo 1750576 10656443 := bstep (se 1 (by rfl) ⟨7992332, by rfl⟩ : syracuseStep 10656443 = 15984665) B15984665
theorem B2956007 : Blo 1750576 2956007 := bstep (se 1 (by rfl) ⟨2217005, by rfl⟩ : syracuseStep 2956007 = 4434011) B4434011
theorem B2628383 : Blo 1750576 2628383 := bstep (se 1 (by rfl) ⟨1971287, by rfl⟩ : syracuseStep 2628383 = 3942575) B3942575
theorem B1751935 : Blo 1750576 1751935 := bstep (se 1 (by rfl) ⟨1313951, by rfl⟩ : syracuseStep 1751935 = 2627903) B2627903
theorem B1752223 : Blo 1750576 1752223 := bstep (se 1 (by rfl) ⟨1314167, by rfl⟩ : syracuseStep 1752223 = 2628335) B2628335
theorem B3939497 : Blo 1750576 3939497 := bstep (se 2 (by rfl) ⟨1477311, by rfl⟩ : syracuseStep 3939497 = 2954623) B2954623
theorem B2628839 : Blo 1750576 2628839 := bstep (se 1 (by rfl) ⟨1971629, by rfl⟩ : syracuseStep 2628839 = 3943259) B3943259
theorem B4432553 : Blo 1750576 4432553 := bstep (se 2 (by rfl) ⟨1662207, by rfl⟩ : syracuseStep 4432553 = 3324415) B3324415
theorem B7104295 : Blo 1750576 7104295 := bstep (se 1 (by rfl) ⟨5328221, by rfl⟩ : syracuseStep 7104295 = 10656443) B10656443
theorem B1970671 : Blo 1750576 1970671 := bstep (se 1 (by rfl) ⟨1478003, by rfl⟩ : syracuseStep 1970671 = 2956007) B2956007
theorem B2626331 : Blo 1750576 2626331 := bstep (se 1 (by rfl) ⟨1969748, by rfl⟩ : syracuseStep 2626331 = 3939497) B3939497
theorem B19945439 : Blo 1750576 19945439 := bstep (se 1 (by rfl) ⟨14959079, by rfl⟩ : syracuseStep 19945439 = 29918159) B29918159
theorem B3742291 : Blo 1750576 3742291 := bstep (se 1 (by rfl) ⟨2806718, by rfl⟩ : syracuseStep 3742291 = 5613437) B5613437
theorem B25582711 : Blo 1750576 25582711 := bstep (se 1 (by rfl) ⟨19187033, by rfl⟩ : syracuseStep 25582711 = 38374067) B38374067
theorem B1752255 : Blo 1750576 1752255 := bstep (se 1 (by rfl) ⟨1314191, by rfl⟩ : syracuseStep 1752255 = 2628383) B2628383
theorem B1752559 : Blo 1750576 1752559 := bstep (se 1 (by rfl) ⟨1314419, by rfl⟩ : syracuseStep 1752559 = 2628839) B2628839
theorem B4989721 : Blo 1750576 4989721 := bstep (se 2 (by rfl) ⟨1871145, by rfl⟩ : syracuseStep 4989721 = 3742291) B3742291
theorem B13296959 : Blo 1750576 13296959 := bstep (se 1 (by rfl) ⟨9972719, by rfl⟩ : syracuseStep 13296959 = 19945439) B19945439
theorem B9472393 : Blo 1750576 9472393 := bstep (se 2 (by rfl) ⟨3552147, by rfl⟩ : syracuseStep 9472393 = 7104295) B7104295
theorem B2955035 : Blo 1750576 2955035 := bstep (se 1 (by rfl) ⟨2216276, by rfl⟩ : syracuseStep 2955035 = 4432553) B4432553
theorem B1750887 : Blo 1750576 1750887 := bstep (se 1 (by rfl) ⟨1313165, by rfl⟩ : syracuseStep 1750887 = 2626331) B2626331
theorem B2627561 : Blo 1750576 2627561 := bstep (se 2 (by rfl) ⟨985335, by rfl⟩ : syracuseStep 2627561 = 1970671) B1970671
theorem B34110281 : Blo 1750576 34110281 := bstep (se 2 (by rfl) ⟨12791355, by rfl⟩ : syracuseStep 34110281 = 25582711) B25582711
theorem B8864639 : Blo 1750576 8864639 := bstep (se 1 (by rfl) ⟨6648479, by rfl⟩ : syracuseStep 8864639 = 13296959) B13296959
theorem B6652961 : Blo 1750576 6652961 := bstep (se 2 (by rfl) ⟨2494860, by rfl⟩ : syracuseStep 6652961 = 4989721) B4989721
theorem B1970023 : Blo 1750576 1970023 := bstep (se 1 (by rfl) ⟨1477517, by rfl⟩ : syracuseStep 1970023 = 2955035) B2955035
theorem B12629857 : Blo 1750576 12629857 := bstep (se 2 (by rfl) ⟨4736196, by rfl⟩ : syracuseStep 12629857 = 9472393) B9472393
theorem B1751707 : Blo 1750576 1751707 := bstep (se 1 (by rfl) ⟨1313780, by rfl⟩ : syracuseStep 1751707 = 2627561) B2627561
theorem B22740187 : Blo 1750576 22740187 := bstep (se 1 (by rfl) ⟨17055140, by rfl⟩ : syracuseStep 22740187 = 34110281) B34110281
theorem B30320249 : Blo 1750576 30320249 := bstep (se 2 (by rfl) ⟨11370093, by rfl⟩ : syracuseStep 30320249 = 22740187) B22740187
theorem B5909759 : Blo 1750576 5909759 := bstep (se 1 (by rfl) ⟨4432319, by rfl⟩ : syracuseStep 5909759 = 8864639) B8864639
theorem B4435307 : Blo 1750576 4435307 := bstep (se 1 (by rfl) ⟨3326480, by rfl⟩ : syracuseStep 4435307 = 6652961) B6652961
theorem B16839809 : Blo 1750576 16839809 := bstep (se 2 (by rfl) ⟨6314928, by rfl⟩ : syracuseStep 16839809 = 12629857) B12629857
theorem B2626697 : Blo 1750576 2626697 := bstep (se 2 (by rfl) ⟨985011, by rfl⟩ : syracuseStep 2626697 = 1970023) B1970023
theorem B11226539 : Blo 1750576 11226539 := bstep (se 1 (by rfl) ⟨8419904, by rfl⟩ : syracuseStep 11226539 = 16839809) B16839809
theorem B323415989 : Blo 1750576 323415989 := bstep (se 5 (by rfl) ⟨15160124, by rfl⟩ : syracuseStep 323415989 = 30320249) B30320249
theorem B1751131 : Blo 1750576 1751131 := bstep (se 1 (by rfl) ⟨1313348, by rfl⟩ : syracuseStep 1751131 = 2626697) B2626697
theorem B3939839 : Blo 1750576 3939839 := bstep (se 1 (by rfl) ⟨2954879, by rfl⟩ : syracuseStep 3939839 = 5909759) B5909759
theorem B2956871 : Blo 1750576 2956871 := bstep (se 1 (by rfl) ⟨2217653, by rfl⟩ : syracuseStep 2956871 = 4435307) B4435307
theorem B7484359 : Blo 1750576 7484359 := bstep (se 1 (by rfl) ⟨5613269, by rfl⟩ : syracuseStep 7484359 = 11226539) B11226539
theorem B2626559 : Blo 1750576 2626559 := bstep (se 1 (by rfl) ⟨1969919, by rfl⟩ : syracuseStep 2626559 = 3939839) B3939839
theorem B1971247 : Blo 1750576 1971247 := bstep (se 1 (by rfl) ⟨1478435, by rfl⟩ : syracuseStep 1971247 = 2956871) B2956871
theorem B215610659 : Blo 1750576 215610659 := bstep (se 1 (by rfl) ⟨161707994, by rfl⟩ : syracuseStep 215610659 = 323415989) B323415989
theorem B9979145 : Blo 1750576 9979145 := bstep (se 2 (by rfl) ⟨3742179, by rfl⟩ : syracuseStep 9979145 = 7484359) B7484359
theorem B143740439 : Blo 1750576 143740439 := bstep (se 1 (by rfl) ⟨107805329, by rfl⟩ : syracuseStep 143740439 = 215610659) B215610659
theorem B1751039 : Blo 1750576 1751039 := bstep (se 1 (by rfl) ⟨1313279, by rfl⟩ : syracuseStep 1751039 = 2626559) B2626559
theorem B2628329 : Blo 1750576 2628329 := bstep (se 2 (by rfl) ⟨985623, by rfl⟩ : syracuseStep 2628329 = 1971247) B1971247
theorem B6652763 : Blo 1750576 6652763 := bstep (se 1 (by rfl) ⟨4989572, by rfl⟩ : syracuseStep 6652763 = 9979145) B9979145
theorem B95826959 : Blo 1750576 95826959 := bstep (se 1 (by rfl) ⟨71870219, by rfl⟩ : syracuseStep 95826959 = 143740439) B143740439
theorem B1752219 : Blo 1750576 1752219 := bstep (se 1 (by rfl) ⟨1314164, by rfl⟩ : syracuseStep 1752219 = 2628329) B2628329
theorem B4435175 : Blo 1750576 4435175 := bstep (se 1 (by rfl) ⟨3326381, by rfl⟩ : syracuseStep 4435175 = 6652763) B6652763
theorem B63884639 : Blo 1750576 63884639 := bstep (se 1 (by rfl) ⟨47913479, by rfl⟩ : syracuseStep 63884639 = 95826959) B95826959
theorem B2956783 : Blo 1750576 2956783 := bstep (se 1 (by rfl) ⟨2217587, by rfl⟩ : syracuseStep 2956783 = 4435175) B4435175
theorem B42589759 : Blo 1750576 42589759 := bstep (se 1 (by rfl) ⟨31942319, by rfl⟩ : syracuseStep 42589759 = 63884639) B63884639
theorem B3942377 : Blo 1750576 3942377 := bstep (se 2 (by rfl) ⟨1478391, by rfl⟩ : syracuseStep 3942377 = 2956783) B2956783
theorem B56786345 : Blo 1750576 56786345 := bstep (se 2 (by rfl) ⟨21294879, by rfl⟩ : syracuseStep 56786345 = 42589759) B42589759
theorem B37857563 : Blo 1750576 37857563 := bstep (se 1 (by rfl) ⟨28393172, by rfl⟩ : syracuseStep 37857563 = 56786345) B56786345
theorem B2628251 : Blo 1750576 2628251 := bstep (se 1 (by rfl) ⟨1971188, by rfl⟩ : syracuseStep 2628251 = 3942377) B3942377
theorem B25238375 : Blo 1750576 25238375 := bstep (se 1 (by rfl) ⟨18928781, by rfl⟩ : syracuseStep 25238375 = 37857563) B37857563
theorem B1752167 : Blo 1750576 1752167 := bstep (se 1 (by rfl) ⟨1314125, by rfl⟩ : syracuseStep 1752167 = 2628251) B2628251
theorem B16825583 : Blo 1750576 16825583 := bstep (se 1 (by rfl) ⟨12619187, by rfl⟩ : syracuseStep 16825583 = 25238375) B25238375
theorem B11217055 : Blo 1750576 11217055 := bstep (se 1 (by rfl) ⟨8412791, by rfl⟩ : syracuseStep 11217055 = 16825583) B16825583
theorem B14956073 : Blo 1750576 14956073 := bstep (se 2 (by rfl) ⟨5608527, by rfl⟩ : syracuseStep 14956073 = 11217055) B11217055
theorem B9970715 : Blo 1750576 9970715 := bstep (se 1 (by rfl) ⟨7478036, by rfl⟩ : syracuseStep 9970715 = 14956073) B14956073
theorem B6647143 : Blo 1750576 6647143 := bstep (se 1 (by rfl) ⟨4985357, by rfl⟩ : syracuseStep 6647143 = 9970715) B9970715
theorem B8862857 : Blo 1750576 8862857 := bstep (se 2 (by rfl) ⟨3323571, by rfl⟩ : syracuseStep 8862857 = 6647143) B6647143
theorem B5908571 : Blo 1750576 5908571 := bstep (se 1 (by rfl) ⟨4431428, by rfl⟩ : syracuseStep 5908571 = 8862857) B8862857
theorem B3939047 : Blo 1750576 3939047 := bstep (se 1 (by rfl) ⟨2954285, by rfl⟩ : syracuseStep 3939047 = 5908571) B5908571
theorem B2626031 : Blo 1750576 2626031 := bstep (se 1 (by rfl) ⟨1969523, by rfl⟩ : syracuseStep 2626031 = 3939047) B3939047
theorem B1750687 : Blo 1750576 1750687 := bstep (se 1 (by rfl) ⟨1313015, by rfl⟩ : syracuseStep 1750687 = 2626031) B2626031

theorem C0 (j : ℕ) (h1 : 437644 ≤ j) (h2 : j ≤ 438143) : Blo 1750576 (4 * j + 3) := by
  interval_cases j
  · exact B1750579
  · exact B1750583
  · exact B1750587
  · exact B1750591
  · exact B1750595
  · exact B1750599
  · exact B1750603
  · exact B1750607
  · exact B1750611
  · exact B1750615
  · exact B1750619
  · exact B1750623
  · exact B1750627
  · exact B1750631
  · exact B1750635
  · exact B1750639
  · exact B1750643
  · exact B1750647
  · exact B1750651
  · exact B1750655
  · exact B1750659
  · exact B1750663
  · exact B1750667
  · exact B1750671
  · exact B1750675
  · exact B1750679
  · exact B1750683
  · exact B1750687
  · exact B1750691
  · exact B1750695
  · exact B1750699
  · exact B1750703
  · exact B1750707
  · exact B1750711
  · exact B1750715
  · exact B1750719
  · exact B1750723
  · exact B1750727
  · exact B1750731
  · exact B1750735
  · exact B1750739
  · exact B1750743
  · exact B1750747
  · exact B1750751
  · exact B1750755
  · exact B1750759
  · exact B1750763
  · exact B1750767
  · exact B1750771
  · exact B1750775
  · exact B1750779
  · exact B1750783
  · exact B1750787
  · exact B1750791
  · exact B1750795
  · exact B1750799
  · exact B1750803
  · exact B1750807
  · exact B1750811
  · exact B1750815
  · exact B1750819
  · exact B1750823
  · exact B1750827
  · exact B1750831
  · exact B1750835
  · exact B1750839
  · exact B1750843
  · exact B1750847
  · exact B1750851
  · exact B1750855
  · exact B1750859
  · exact B1750863
  · exact B1750867
  · exact B1750871
  · exact B1750875
  · exact B1750879
  · exact B1750883
  · exact B1750887
  · exact B1750891
  · exact B1750895
  · exact B1750899
  · exact B1750903
  · exact B1750907
  · exact B1750911
  · exact B1750915
  · exact B1750919
  · exact B1750923
  · exact B1750927
  · exact B1750931
  · exact B1750935
  · exact B1750939
  · exact B1750943
  · exact B1750947
  · exact B1750951
  · exact B1750955
  · exact B1750959
  · exact B1750963
  · exact B1750967
  · exact B1750971
  · exact B1750975
  · exact B1750979
  · exact B1750983
  · exact B1750987
  · exact B1750991
  · exact B1750995
  · exact B1750999
  · exact B1751003
  · exact B1751007
  · exact B1751011
  · exact B1751015
  · exact B1751019
  · exact B1751023
  · exact B1751027
  · exact B1751031
  · exact B1751035
  · exact B1751039
  · exact B1751043
  · exact B1751047
  · exact B1751051
  · exact B1751055
  · exact B1751059
  · exact B1751063
  · exact B1751067
  · exact B1751071
  · exact B1751075
  · exact B1751079
  · exact B1751083
  · exact B1751087
  · exact B1751091
  · exact B1751095
  · exact B1751099
  · exact B1751103
  · exact B1751107
  · exact B1751111
  · exact B1751115
  · exact B1751119
  · exact B1751123
  · exact B1751127
  · exact B1751131
  · exact B1751135
  · exact B1751139
  · exact B1751143
  · exact B1751147
  · exact B1751151
  · exact B1751155
  · exact B1751159
  · exact B1751163
  · exact B1751167
  · exact B1751171
  · exact B1751175
  · exact B1751179
  · exact B1751183
  · exact B1751187
  · exact B1751191
  · exact B1751195
  · exact B1751199
  · exact B1751203
  · exact B1751207
  · exact B1751211
  · exact B1751215
  · exact B1751219
  · exact B1751223
  · exact B1751227
  · exact B1751231
  · exact B1751235
  · exact B1751239
  · exact B1751243
  · exact B1751247
  · exact B1751251
  · exact B1751255
  · exact B1751259
  · exact B1751263
  · exact B1751267
  · exact B1751271
  · exact B1751275
  · exact B1751279
  · exact B1751283
  · exact B1751287
  · exact B1751291
  · exact B1751295
  · exact B1751299
  · exact B1751303
  · exact B1751307
  · exact B1751311
  · exact B1751315
  · exact B1751319
  · exact B1751323
  · exact B1751327
  · exact B1751331
  · exact B1751335
  · exact B1751339
  · exact B1751343
  · exact B1751347
  · exact B1751351
  · exact B1751355
  · exact B1751359
  · exact B1751363
  · exact B1751367
  · exact B1751371
  · exact B1751375
  · exact B1751379
  · exact B1751383
  · exact B1751387
  · exact B1751391
  · exact B1751395
  · exact B1751399
  · exact B1751403
  · exact B1751407
  · exact B1751411
  · exact B1751415
  · exact B1751419
  · exact B1751423
  · exact B1751427
  · exact B1751431
  · exact B1751435
  · exact B1751439
  · exact B1751443
  · exact B1751447
  · exact B1751451
  · exact B1751455
  · exact B1751459
  · exact B1751463
  · exact B1751467
  · exact B1751471
  · exact B1751475
  · exact B1751479
  · exact B1751483
  · exact B1751487
  · exact B1751491
  · exact B1751495
  · exact B1751499
  · exact B1751503
  · exact B1751507
  · exact B1751511
  · exact B1751515
  · exact B1751519
  · exact B1751523
  · exact B1751527
  · exact B1751531
  · exact B1751535
  · exact B1751539
  · exact B1751543
  · exact B1751547
  · exact B1751551
  · exact B1751555
  · exact B1751559
  · exact B1751563
  · exact B1751567
  · exact B1751571
  · exact B1751575
  · exact B1751579
  · exact B1751583
  · exact B1751587
  · exact B1751591
  · exact B1751595
  · exact B1751599
  · exact B1751603
  · exact B1751607
  · exact B1751611
  · exact B1751615
  · exact B1751619
  · exact B1751623
  · exact B1751627
  · exact B1751631
  · exact B1751635
  · exact B1751639
  · exact B1751643
  · exact B1751647
  · exact B1751651
  · exact B1751655
  · exact B1751659
  · exact B1751663
  · exact B1751667
  · exact B1751671
  · exact B1751675
  · exact B1751679
  · exact B1751683
  · exact B1751687
  · exact B1751691
  · exact B1751695
  · exact B1751699
  · exact B1751703
  · exact B1751707
  · exact B1751711
  · exact B1751715
  · exact B1751719
  · exact B1751723
  · exact B1751727
  · exact B1751731
  · exact B1751735
  · exact B1751739
  · exact B1751743
  · exact B1751747
  · exact B1751751
  · exact B1751755
  · exact B1751759
  · exact B1751763
  · exact B1751767
  · exact B1751771
  · exact B1751775
  · exact B1751779
  · exact B1751783
  · exact B1751787
  · exact B1751791
  · exact B1751795
  · exact B1751799
  · exact B1751803
  · exact B1751807
  · exact B1751811
  · exact B1751815
  · exact B1751819
  · exact B1751823
  · exact B1751827
  · exact B1751831
  · exact B1751835
  · exact B1751839
  · exact B1751843
  · exact B1751847
  · exact B1751851
  · exact B1751855
  · exact B1751859
  · exact B1751863
  · exact B1751867
  · exact B1751871
  · exact B1751875
  · exact B1751879
  · exact B1751883
  · exact B1751887
  · exact B1751891
  · exact B1751895
  · exact B1751899
  · exact B1751903
  · exact B1751907
  · exact B1751911
  · exact B1751915
  · exact B1751919
  · exact B1751923
  · exact B1751927
  · exact B1751931
  · exact B1751935
  · exact B1751939
  · exact B1751943
  · exact B1751947
  · exact B1751951
  · exact B1751955
  · exact B1751959
  · exact B1751963
  · exact B1751967
  · exact B1751971
  · exact B1751975
  · exact B1751979
  · exact B1751983
  · exact B1751987
  · exact B1751991
  · exact B1751995
  · exact B1751999
  · exact B1752003
  · exact B1752007
  · exact B1752011
  · exact B1752015
  · exact B1752019
  · exact B1752023
  · exact B1752027
  · exact B1752031
  · exact B1752035
  · exact B1752039
  · exact B1752043
  · exact B1752047
  · exact B1752051
  · exact B1752055
  · exact B1752059
  · exact B1752063
  · exact B1752067
  · exact B1752071
  · exact B1752075
  · exact B1752079
  · exact B1752083
  · exact B1752087
  · exact B1752091
  · exact B1752095
  · exact B1752099
  · exact B1752103
  · exact B1752107
  · exact B1752111
  · exact B1752115
  · exact B1752119
  · exact B1752123
  · exact B1752127
  · exact B1752131
  · exact B1752135
  · exact B1752139
  · exact B1752143
  · exact B1752147
  · exact B1752151
  · exact B1752155
  · exact B1752159
  · exact B1752163
  · exact B1752167
  · exact B1752171
  · exact B1752175
  · exact B1752179
  · exact B1752183
  · exact B1752187
  · exact B1752191
  · exact B1752195
  · exact B1752199
  · exact B1752203
  · exact B1752207
  · exact B1752211
  · exact B1752215
  · exact B1752219
  · exact B1752223
  · exact B1752227
  · exact B1752231
  · exact B1752235
  · exact B1752239
  · exact B1752243
  · exact B1752247
  · exact B1752251
  · exact B1752255
  · exact B1752259
  · exact B1752263
  · exact B1752267
  · exact B1752271
  · exact B1752275
  · exact B1752279
  · exact B1752283
  · exact B1752287
  · exact B1752291
  · exact B1752295
  · exact B1752299
  · exact B1752303
  · exact B1752307
  · exact B1752311
  · exact B1752315
  · exact B1752319
  · exact B1752323
  · exact B1752327
  · exact B1752331
  · exact B1752335
  · exact B1752339
  · exact B1752343
  · exact B1752347
  · exact B1752351
  · exact B1752355
  · exact B1752359
  · exact B1752363
  · exact B1752367
  · exact B1752371
  · exact B1752375
  · exact B1752379
  · exact B1752383
  · exact B1752387
  · exact B1752391
  · exact B1752395
  · exact B1752399
  · exact B1752403
  · exact B1752407
  · exact B1752411
  · exact B1752415
  · exact B1752419
  · exact B1752423
  · exact B1752427
  · exact B1752431
  · exact B1752435
  · exact B1752439
  · exact B1752443
  · exact B1752447
  · exact B1752451
  · exact B1752455
  · exact B1752459
  · exact B1752463
  · exact B1752467
  · exact B1752471
  · exact B1752475
  · exact B1752479
  · exact B1752483
  · exact B1752487
  · exact B1752491
  · exact B1752495
  · exact B1752499
  · exact B1752503
  · exact B1752507
  · exact B1752511
  · exact B1752515
  · exact B1752519
  · exact B1752523
  · exact B1752527
  · exact B1752531
  · exact B1752535
  · exact B1752539
  · exact B1752543
  · exact B1752547
  · exact B1752551
  · exact B1752555
  · exact B1752559
  · exact B1752563
  · exact B1752567
  · exact B1752571
  · exact B1752575

theorem solution (m : ℕ) (hlo : 1750576 ≤ m) (hhi : m ≤ 1752576) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 437644 ≤ j := by omega
    have hj2 : j ≤ 438143 := by omega
    have hb : Blo 1750576 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
