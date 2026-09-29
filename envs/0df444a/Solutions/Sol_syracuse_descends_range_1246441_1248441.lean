-- Prove2me | solution 1 for syracuse_descends_range_1246441_1248441
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:11:13.892393+00:00
-- url     : https://prove2.me/submissions/50fc44e9-a51d-4be0-b2ad-e2f4566139ad

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


theorem B5996549 : Blo 1246441 5996549 := bbase (se 4 (by rfl) ⟨562176, by rfl⟩ : syracuseStep 5996549 = 1124353) (by norm_num)
theorem B2105365 : Blo 1246441 2105365 := bbase (se 6 (by rfl) ⟨49344, by rfl⟩ : syracuseStep 2105365 = 98689) (by norm_num)
theorem B1998901 : Blo 1246441 1998901 := bbase (se 5 (by rfl) ⟨93698, by rfl⟩ : syracuseStep 1998901 = 187397) (by norm_num)
theorem B4210757 : Blo 1246441 4210757 := bbase (se 4 (by rfl) ⟨394758, by rfl⟩ : syracuseStep 4210757 = 789517) (by norm_num)
theorem B2105453 : Blo 1246441 2105453 := bbase (se 3 (by rfl) ⟨394772, by rfl⟩ : syracuseStep 2105453 = 789545) (by norm_num)
theorem B3997829 : Blo 1246441 3997829 := bbase (se 4 (by rfl) ⟨374796, by rfl⟩ : syracuseStep 3997829 = 749593) (by norm_num)
theorem B1622209 : Blo 1246441 1622209 := bbase (se 2 (by rfl) ⟨608328, by rfl⟩ : syracuseStep 1622209 = 1216657) (by norm_num)
theorem B2367701 : Blo 1246441 2367701 := bbase (se 7 (by rfl) ⟨27746, by rfl⟩ : syracuseStep 2367701 = 55493) (by norm_num)
theorem B4735205 : Blo 1246441 4735205 := bbase (se 4 (by rfl) ⟨443925, by rfl⟩ : syracuseStep 4735205 = 887851) (by norm_num)
theorem B2105581 : Blo 1246441 2105581 := bbase (se 3 (by rfl) ⟨394796, by rfl⟩ : syracuseStep 2105581 = 789593) (by norm_num)
theorem B3997957 : Blo 1246441 3997957 := bbase (se 4 (by rfl) ⟨374808, by rfl⟩ : syracuseStep 3997957 = 749617) (by norm_num)
theorem B2105669 : Blo 1246441 2105669 := bbase (se 4 (by rfl) ⟨197406, by rfl⟩ : syracuseStep 2105669 = 394813) (by norm_num)
theorem B2662733 : Blo 1246441 2662733 := bbase (se 3 (by rfl) ⟨499262, by rfl⟩ : syracuseStep 2662733 = 998525) (by norm_num)
theorem B2662741 : Blo 1246441 2662741 := bbase (se 10 (by rfl) ⟨3900, by rfl⟩ : syracuseStep 2662741 = 7801) (by norm_num)
theorem B2105797 : Blo 1246441 2105797 := bbase (se 4 (by rfl) ⟨197418, by rfl⟩ : syracuseStep 2105797 = 394837) (by norm_num)
theorem B1999325 : Blo 1246441 1999325 := bbase (se 3 (by rfl) ⟨374873, by rfl⟩ : syracuseStep 1999325 = 749747) (by norm_num)
theorem B2998757 : Blo 1246441 2998757 := bbase (se 4 (by rfl) ⟨281133, by rfl⟩ : syracuseStep 2998757 = 562267) (by norm_num)
theorem B4211189 : Blo 1246441 4211189 := bbase (se 5 (by rfl) ⟨197399, by rfl⟩ : syracuseStep 4211189 = 394799) (by norm_num)
theorem B4735493 : Blo 1246441 4735493 := bbase (se 4 (by rfl) ⟨443952, by rfl⟩ : syracuseStep 4735493 = 887905) (by norm_num)
theorem B3998213 : Blo 1246441 3998213 := bbase (se 4 (by rfl) ⟨374832, by rfl⟩ : syracuseStep 3998213 = 749665) (by norm_num)
theorem B25960981 : Blo 1246441 25960981 := bbase (se 6 (by rfl) ⟨608460, by rfl⟩ : syracuseStep 25960981 = 1216921) (by norm_num)
theorem B2105885 : Blo 1246441 2105885 := bbase (se 3 (by rfl) ⟨394853, by rfl⟩ : syracuseStep 2105885 = 789707) (by norm_num)
theorem B2163245 : Blo 1246441 2163245 := bbase (se 3 (by rfl) ⟨405608, by rfl⟩ : syracuseStep 2163245 = 811217) (by norm_num)
theorem B2998853 : Blo 1246441 2998853 := bbase (se 4 (by rfl) ⟨281142, by rfl⟩ : syracuseStep 2998853 = 562285) (by norm_num)
theorem B1499801 : Blo 1246441 1499801 := bbase (se 2 (by rfl) ⟨562425, by rfl⟩ : syracuseStep 1499801 = 1124851) (by norm_num)
theorem B2106013 : Blo 1246441 2106013 := bbase (se 3 (by rfl) ⟨394877, by rfl⟩ : syracuseStep 2106013 = 789755) (by norm_num)
theorem B7996117 : Blo 1246441 7996117 := bbase (se 7 (by rfl) ⟨93704, by rfl⟩ : syracuseStep 7996117 = 187409) (by norm_num)
theorem B2106101 : Blo 1246441 2106101 := bbase (se 5 (by rfl) ⟨98723, by rfl⟩ : syracuseStep 2106101 = 197447) (by norm_num)
theorem B1999613 : Blo 1246441 1999613 := bbase (se 3 (by rfl) ⟨374927, by rfl⟩ : syracuseStep 1999613 = 749855) (by norm_num)
theorem B7103285 : Blo 1246441 7103285 := bbase (se 5 (by rfl) ⟨332966, by rfl⟩ : syracuseStep 7103285 = 665933) (by norm_num)
theorem B207496021 : Blo 1246441 207496021 := bbase (se 9 (by rfl) ⟨607898, by rfl⟩ : syracuseStep 207496021 = 1215797) (by norm_num)
theorem B2106229 : Blo 1246441 2106229 := bbase (se 5 (by rfl) ⟨98729, by rfl⟩ : syracuseStep 2106229 = 197459) (by norm_num)
theorem B2597765 : Blo 1246441 2597765 := bbase (se 4 (by rfl) ⟨243540, by rfl⟩ : syracuseStep 2597765 = 487081) (by norm_num)
theorem B4932485 : Blo 1246441 4932485 := bbase (se 4 (by rfl) ⟨462420, by rfl⟩ : syracuseStep 4932485 = 924841) (by norm_num)
theorem B4211621 : Blo 1246441 4211621 := bbase (se 4 (by rfl) ⟨394839, by rfl⟩ : syracuseStep 4211621 = 789679) (by norm_num)
theorem B2368453 : Blo 1246441 2368453 := bbase (se 4 (by rfl) ⟨222042, by rfl⟩ : syracuseStep 2368453 = 444085) (by norm_num)
theorem B2106317 : Blo 1246441 2106317 := bbase (se 3 (by rfl) ⟨394934, by rfl⟩ : syracuseStep 2106317 = 789869) (by norm_num)
theorem B11994101 : Blo 1246441 11994101 := bbase (se 5 (by rfl) ⟨562223, by rfl⟩ : syracuseStep 11994101 = 1124447) (by norm_num)
theorem B2106445 : Blo 1246441 2106445 := bbase (se 3 (by rfl) ⟨394958, by rfl⟩ : syracuseStep 2106445 = 789917) (by norm_num)
theorem B2368597 : Blo 1246441 2368597 := bbase (se 8 (by rfl) ⟨13878, by rfl⟩ : syracuseStep 2368597 = 27757) (by norm_num)
theorem B6317189 : Blo 1246441 6317189 := bbase (se 4 (by rfl) ⟨592236, by rfl⟩ : syracuseStep 6317189 = 1184473) (by norm_num)
theorem B13477013 : Blo 1246441 13477013 := bbase (se 6 (by rfl) ⟨315867, by rfl⟩ : syracuseStep 13477013 = 631735) (by norm_num)
theorem B2106533 : Blo 1246441 2106533 := bbase (se 4 (by rfl) ⟨197487, by rfl⟩ : syracuseStep 2106533 = 394975) (by norm_num)
theorem B2368757 : Blo 1246441 2368757 := bbase (se 5 (by rfl) ⟨111035, by rfl⟩ : syracuseStep 2368757 = 222071) (by norm_num)
theorem B3155213 : Blo 1246441 3155213 := bbase (se 3 (by rfl) ⟨591602, by rfl⟩ : syracuseStep 3155213 = 1183205) (by norm_num)
theorem B2106661 : Blo 1246441 2106661 := bbase (se 4 (by rfl) ⟨197499, by rfl⟩ : syracuseStep 2106661 = 394999) (by norm_num)
theorem B5326165 : Blo 1246441 5326165 := bbase (se 12 (by rfl) ⟨1950, by rfl⟩ : syracuseStep 5326165 = 3901) (by norm_num)
theorem B4212053 : Blo 1246441 4212053 := bbase (se 12 (by rfl) ⟨1542, by rfl⟩ : syracuseStep 4212053 = 3085) (by norm_num)
theorem B2368901 : Blo 1246441 2368901 := bbase (se 4 (by rfl) ⟨222084, by rfl⟩ : syracuseStep 2368901 = 444169) (by norm_num)
theorem B1402249 : Blo 1246441 1402249 := bbase (se 2 (by rfl) ⟨525843, by rfl⟩ : syracuseStep 1402249 = 1051687) (by norm_num)
theorem B4105637 : Blo 1246441 4105637 := bbase (se 4 (by rfl) ⟨384903, by rfl⟩ : syracuseStep 4105637 = 769807) (by norm_num)
theorem B1402285 : Blo 1246441 1402285 := bbase (se 3 (by rfl) ⟨262928, by rfl⟩ : syracuseStep 1402285 = 525857) (by norm_num)
theorem B2663869 : Blo 1246441 2663869 := bbase (se 3 (by rfl) ⟨499475, by rfl⟩ : syracuseStep 2663869 = 998951) (by norm_num)
theorem B1402321 : Blo 1246441 1402321 := bbase (se 2 (by rfl) ⟨525870, by rfl⟩ : syracuseStep 1402321 = 1051741) (by norm_num)
theorem B1402357 : Blo 1246441 1402357 := bbase (se 5 (by rfl) ⟨65735, by rfl⟩ : syracuseStep 1402357 = 131471) (by norm_num)
theorem B1402393 : Blo 1246441 1402393 := bbase (se 2 (by rfl) ⟨525897, by rfl⟩ : syracuseStep 1402393 = 1051795) (by norm_num)
theorem B2885149 : Blo 1246441 2885149 := bbase (se 3 (by rfl) ⟨540965, by rfl⟩ : syracuseStep 2885149 = 1081931) (by norm_num)
theorem B1402429 : Blo 1246441 1402429 := bbase (se 3 (by rfl) ⟨262955, by rfl⟩ : syracuseStep 1402429 = 525911) (by norm_num)
theorem B1402465 : Blo 1246441 1402465 := bbase (se 2 (by rfl) ⟨525924, by rfl⟩ : syracuseStep 1402465 = 1051849) (by norm_num)
theorem B3155557 : Blo 1246441 3155557 := bbase (se 4 (by rfl) ⟨295833, by rfl⟩ : syracuseStep 3155557 = 591667) (by norm_num)
theorem B1402501 : Blo 1246441 1402501 := bbase (se 4 (by rfl) ⟨131484, by rfl⟩ : syracuseStep 1402501 = 262969) (by norm_num)
theorem B2246285 : Blo 1246441 2246285 := bbase (se 3 (by rfl) ⟨421178, by rfl⟩ : syracuseStep 2246285 = 842357) (by norm_num)
theorem B4736677 : Blo 1246441 4736677 := bbase (se 4 (by rfl) ⟨444063, by rfl⟩ : syracuseStep 4736677 = 888127) (by norm_num)
theorem B2369189 : Blo 1246441 2369189 := bbase (se 4 (by rfl) ⟨222111, by rfl⟩ : syracuseStep 2369189 = 444223) (by norm_num)
theorem B1402537 : Blo 1246441 1402537 := bbase (se 2 (by rfl) ⟨525951, by rfl⟩ : syracuseStep 1402537 = 1051903) (by norm_num)
theorem B1402573 : Blo 1246441 1402573 := bbase (se 3 (by rfl) ⟨262982, by rfl⟩ : syracuseStep 1402573 = 525965) (by norm_num)
theorem B2246357 : Blo 1246441 2246357 := bbase (se 7 (by rfl) ⟨26324, by rfl⟩ : syracuseStep 2246357 = 52649) (by norm_num)
theorem B3155669 : Blo 1246441 3155669 := bbase (se 7 (by rfl) ⟨36980, by rfl⟩ : syracuseStep 3155669 = 73961) (by norm_num)
theorem B1402609 : Blo 1246441 1402609 := bbase (se 2 (by rfl) ⟨525978, by rfl⟩ : syracuseStep 1402609 = 1051957) (by norm_num)
theorem B10397429 : Blo 1246441 10397429 := bbase (se 5 (by rfl) ⟨487379, by rfl⟩ : syracuseStep 10397429 = 974759) (by norm_num)
theorem B4212485 : Blo 1246441 4212485 := bbase (se 4 (by rfl) ⟨394920, by rfl⟩ : syracuseStep 4212485 = 789841) (by norm_num)
theorem B1402645 : Blo 1246441 1402645 := bbase (se 6 (by rfl) ⟨32874, by rfl⟩ : syracuseStep 1402645 = 65749) (by norm_num)
theorem B2664245 : Blo 1246441 2664245 := bbase (se 5 (by rfl) ⟨124886, by rfl⟩ : syracuseStep 2664245 = 249773) (by norm_num)
theorem B1402681 : Blo 1246441 1402681 := bbase (se 2 (by rfl) ⟨526005, by rfl⟩ : syracuseStep 1402681 = 1052011) (by norm_num)
theorem B2369341 : Blo 1246441 2369341 := bbase (se 3 (by rfl) ⟨444251, by rfl⟩ : syracuseStep 2369341 = 888503) (by norm_num)
theorem B1402717 : Blo 1246441 1402717 := bbase (se 3 (by rfl) ⟨263009, by rfl⟩ : syracuseStep 1402717 = 526019) (by norm_num)
theorem B1869677 : Blo 1246441 1869677 := bbase (se 3 (by rfl) ⟨350564, by rfl⟩ : syracuseStep 1869677 = 701129) (by norm_num)
theorem B1402753 : Blo 1246441 1402753 := bbase (se 2 (by rfl) ⟨526032, by rfl⟩ : syracuseStep 1402753 = 1052065) (by norm_num)
theorem B1869701 : Blo 1246441 1869701 := bbase (se 4 (by rfl) ⟨175284, by rfl⟩ : syracuseStep 1869701 = 350569) (by norm_num)
theorem B3155861 : Blo 1246441 3155861 := bbase (se 6 (by rfl) ⟨73965, by rfl⟩ : syracuseStep 3155861 = 147931) (by norm_num)
theorem B1869725 : Blo 1246441 1869725 := bbase (se 3 (by rfl) ⟨350573, by rfl⟩ : syracuseStep 1869725 = 701147) (by norm_num)
theorem B1402789 : Blo 1246441 1402789 := bbase (se 4 (by rfl) ⟨131511, by rfl⟩ : syracuseStep 1402789 = 263023) (by norm_num)
theorem B2246573 : Blo 1246441 2246573 := bbase (se 3 (by rfl) ⟨421232, by rfl⟩ : syracuseStep 2246573 = 842465) (by norm_num)
theorem B1869749 : Blo 1246441 1869749 := bbase (se 5 (by rfl) ⟨87644, by rfl⟩ : syracuseStep 1869749 = 175289) (by norm_num)
theorem B1402825 : Blo 1246441 1402825 := bbase (se 2 (by rfl) ⟨526059, by rfl⟩ : syracuseStep 1402825 = 1052119) (by norm_num)
theorem B1869773 : Blo 1246441 1869773 := bbase (se 3 (by rfl) ⟨350582, by rfl⟩ : syracuseStep 1869773 = 701165) (by norm_num)
theorem B7104469 : Blo 1246441 7104469 := bbase (se 7 (by rfl) ⟨83255, by rfl⟩ : syracuseStep 7104469 = 166511) (by norm_num)
theorem B4736981 : Blo 1246441 4736981 := bbase (se 7 (by rfl) ⟨55511, by rfl⟩ : syracuseStep 4736981 = 111023) (by norm_num)
theorem B5998549 : Blo 1246441 5998549 := bbase (se 7 (by rfl) ⟨70295, by rfl⟩ : syracuseStep 5998549 = 140591) (by norm_num)
theorem B1869797 : Blo 1246441 1869797 := bbase (se 4 (by rfl) ⟨175293, by rfl⟩ : syracuseStep 1869797 = 350587) (by norm_num)
theorem B1402861 : Blo 1246441 1402861 := bbase (se 3 (by rfl) ⟨263036, by rfl⟩ : syracuseStep 1402861 = 526073) (by norm_num)
theorem B1869821 : Blo 1246441 1869821 := bbase (se 3 (by rfl) ⟨350591, by rfl⟩ : syracuseStep 1869821 = 701183) (by norm_num)
theorem B1402897 : Blo 1246441 1402897 := bbase (se 2 (by rfl) ⟨526086, by rfl⟩ : syracuseStep 1402897 = 1052173) (by norm_num)
theorem B1869845 : Blo 1246441 1869845 := bbase (se 6 (by rfl) ⟨43824, by rfl⟩ : syracuseStep 1869845 = 87649) (by norm_num)
theorem B1869869 : Blo 1246441 1869869 := bbase (se 3 (by rfl) ⟨350600, by rfl⟩ : syracuseStep 1869869 = 701201) (by norm_num)
theorem B1402933 : Blo 1246441 1402933 := bbase (se 5 (by rfl) ⟨65762, by rfl⟩ : syracuseStep 1402933 = 131525) (by norm_num)
theorem B6490165 : Blo 1246441 6490165 := bbase (se 5 (by rfl) ⟨304226, by rfl⟩ : syracuseStep 6490165 = 608453) (by norm_num)
theorem B1869893 : Blo 1246441 1869893 := bbase (se 4 (by rfl) ⟨175302, by rfl⟩ : syracuseStep 1869893 = 350605) (by norm_num)
theorem B1402969 : Blo 1246441 1402969 := bbase (se 2 (by rfl) ⟨526113, by rfl⟩ : syracuseStep 1402969 = 1052227) (by norm_num)
theorem B1869917 : Blo 1246441 1869917 := bbase (se 3 (by rfl) ⟨350609, by rfl⟩ : syracuseStep 1869917 = 701219) (by norm_num)
theorem B2369645 : Blo 1246441 2369645 := bbase (se 3 (by rfl) ⟨444308, by rfl⟩ : syracuseStep 2369645 = 888617) (by norm_num)
theorem B1869941 : Blo 1246441 1869941 := bbase (se 5 (by rfl) ⟨87653, by rfl⟩ : syracuseStep 1869941 = 175307) (by norm_num)
theorem B1403005 : Blo 1246441 1403005 := bbase (se 3 (by rfl) ⟨263063, by rfl⟩ : syracuseStep 1403005 = 526127) (by norm_num)
theorem B1869965 : Blo 1246441 1869965 := bbase (se 3 (by rfl) ⟨350618, by rfl⟩ : syracuseStep 1869965 = 701237) (by norm_num)
theorem B1403041 : Blo 1246441 1403041 := bbase (se 2 (by rfl) ⟨526140, by rfl⟩ : syracuseStep 1403041 = 1052281) (by norm_num)
theorem B1869989 : Blo 1246441 1869989 := bbase (se 4 (by rfl) ⟨175311, by rfl⟩ : syracuseStep 1869989 = 350623) (by norm_num)
theorem B4212917 : Blo 1246441 4212917 := bbase (se 5 (by rfl) ⟨197480, by rfl⟩ : syracuseStep 4212917 = 394961) (by norm_num)
theorem B1870013 : Blo 1246441 1870013 := bbase (se 3 (by rfl) ⟨350627, by rfl⟩ : syracuseStep 1870013 = 701255) (by norm_num)
theorem B1403077 : Blo 1246441 1403077 := bbase (se 4 (by rfl) ⟨131538, by rfl⟩ : syracuseStep 1403077 = 263077) (by norm_num)
theorem B1870037 : Blo 1246441 1870037 := bbase (se 7 (by rfl) ⟨21914, by rfl⟩ : syracuseStep 1870037 = 43829) (by norm_num)
theorem B1403113 : Blo 1246441 1403113 := bbase (se 2 (by rfl) ⟨526167, by rfl⟩ : syracuseStep 1403113 = 1052335) (by norm_num)
theorem B1870061 : Blo 1246441 1870061 := bbase (se 3 (by rfl) ⟨350636, by rfl⟩ : syracuseStep 1870061 = 701273) (by norm_num)
theorem B3156205 : Blo 1246441 3156205 := bbase (se 3 (by rfl) ⟨591788, by rfl⟩ : syracuseStep 3156205 = 1183577) (by norm_num)
theorem B1870085 : Blo 1246441 1870085 := bbase (se 4 (by rfl) ⟨175320, by rfl⟩ : syracuseStep 1870085 = 350641) (by norm_num)
theorem B1403149 : Blo 1246441 1403149 := bbase (se 3 (by rfl) ⟨263090, by rfl⟩ : syracuseStep 1403149 = 526181) (by norm_num)
theorem B1870109 : Blo 1246441 1870109 := bbase (se 3 (by rfl) ⟨350645, by rfl⟩ : syracuseStep 1870109 = 701291) (by norm_num)
theorem B1403185 : Blo 1246441 1403185 := bbase (se 2 (by rfl) ⟨526194, by rfl⟩ : syracuseStep 1403185 = 1052389) (by norm_num)
theorem B1870133 : Blo 1246441 1870133 := bbase (se 5 (by rfl) ⟨87662, by rfl⟩ : syracuseStep 1870133 = 175325) (by norm_num)
theorem B1870157 : Blo 1246441 1870157 := bbase (se 3 (by rfl) ⟨350654, by rfl⟩ : syracuseStep 1870157 = 701309) (by norm_num)
theorem B1403221 : Blo 1246441 1403221 := bbase (se 10 (by rfl) ⟨2055, by rfl⟩ : syracuseStep 1403221 = 4111) (by norm_num)
theorem B3156317 : Blo 1246441 3156317 := bbase (se 3 (by rfl) ⟨591809, by rfl⟩ : syracuseStep 3156317 = 1183619) (by norm_num)
theorem B1870181 : Blo 1246441 1870181 := bbase (se 4 (by rfl) ⟨175329, by rfl⟩ : syracuseStep 1870181 = 350659) (by norm_num)
theorem B2845037 : Blo 1246441 2845037 := bbase (se 3 (by rfl) ⟨533444, by rfl⟩ : syracuseStep 2845037 = 1066889) (by norm_num)
theorem B1263989 : Blo 1246441 1263989 := bbase (se 5 (by rfl) ⟨59249, by rfl⟩ : syracuseStep 1263989 = 118499) (by norm_num)
theorem B1403257 : Blo 1246441 1403257 := bbase (se 2 (by rfl) ⟨526221, by rfl⟩ : syracuseStep 1403257 = 1052443) (by norm_num)
theorem B1870205 : Blo 1246441 1870205 := bbase (se 3 (by rfl) ⟨350663, by rfl⟩ : syracuseStep 1870205 = 701327) (by norm_num)
theorem B1870229 : Blo 1246441 1870229 := bbase (se 6 (by rfl) ⟨43833, by rfl⟩ : syracuseStep 1870229 = 87667) (by norm_num)
theorem B6318485 : Blo 1246441 6318485 := bbase (se 6 (by rfl) ⟨148089, by rfl⟩ : syracuseStep 6318485 = 296179) (by norm_num)
theorem B2132381 : Blo 1246441 2132381 := bbase (se 3 (by rfl) ⟨399821, by rfl⟩ : syracuseStep 2132381 = 799643) (by norm_num)
theorem B1403293 : Blo 1246441 1403293 := bbase (se 3 (by rfl) ⟨263117, by rfl⟩ : syracuseStep 1403293 = 526235) (by norm_num)
theorem B1870253 : Blo 1246441 1870253 := bbase (se 3 (by rfl) ⟨350672, by rfl⟩ : syracuseStep 1870253 = 701345) (by norm_num)
theorem B11372981 : Blo 1246441 11372981 := bbase (se 5 (by rfl) ⟨533108, by rfl⟩ : syracuseStep 11372981 = 1066217) (by norm_num)
theorem B1403329 : Blo 1246441 1403329 := bbase (se 2 (by rfl) ⟨526248, by rfl⟩ : syracuseStep 1403329 = 1052497) (by norm_num)
theorem B1870277 : Blo 1246441 1870277 := bbase (se 4 (by rfl) ⟨175338, by rfl⟩ : syracuseStep 1870277 = 350677) (by norm_num)
theorem B1599953 : Blo 1246441 1599953 := bbase (se 2 (by rfl) ⟨599982, by rfl⟩ : syracuseStep 1599953 = 1199965) (by norm_num)
theorem B1870301 : Blo 1246441 1870301 := bbase (se 3 (by rfl) ⟨350681, by rfl⟩ : syracuseStep 1870301 = 701363) (by norm_num)
theorem B1403365 : Blo 1246441 1403365 := bbase (se 4 (by rfl) ⟨131565, by rfl⟩ : syracuseStep 1403365 = 263131) (by norm_num)
theorem B1870325 : Blo 1246441 1870325 := bbase (se 5 (by rfl) ⟨87671, by rfl⟩ : syracuseStep 1870325 = 175343) (by norm_num)
theorem B1403401 : Blo 1246441 1403401 := bbase (se 2 (by rfl) ⟨526275, by rfl⟩ : syracuseStep 1403401 = 1052551) (by norm_num)
theorem B1870349 : Blo 1246441 1870349 := bbase (se 3 (by rfl) ⟨350690, by rfl⟩ : syracuseStep 1870349 = 701381) (by norm_num)
theorem B3156509 : Blo 1246441 3156509 := bbase (se 3 (by rfl) ⟨591845, by rfl⟩ : syracuseStep 3156509 = 1183691) (by norm_num)
theorem B1870373 : Blo 1246441 1870373 := bbase (se 4 (by rfl) ⟨175347, by rfl⟩ : syracuseStep 1870373 = 350695) (by norm_num)
theorem B1403437 : Blo 1246441 1403437 := bbase (se 3 (by rfl) ⟨263144, by rfl⟩ : syracuseStep 1403437 = 526289) (by norm_num)
theorem B1870397 : Blo 1246441 1870397 := bbase (se 3 (by rfl) ⟨350699, by rfl⟩ : syracuseStep 1870397 = 701399) (by norm_num)
theorem B1403473 : Blo 1246441 1403473 := bbase (se 2 (by rfl) ⟨526302, by rfl⟩ : syracuseStep 1403473 = 1052605) (by norm_num)
theorem B1870421 : Blo 1246441 1870421 := bbase (se 8 (by rfl) ⟨10959, by rfl⟩ : syracuseStep 1870421 = 21919) (by norm_num)
theorem B5991013 : Blo 1246441 5991013 := bbase (se 4 (by rfl) ⟨561657, by rfl⟩ : syracuseStep 5991013 = 1123315) (by norm_num)
theorem B4213349 : Blo 1246441 4213349 := bbase (se 4 (by rfl) ⟨395001, by rfl⟩ : syracuseStep 4213349 = 790003) (by norm_num)
theorem B1870445 : Blo 1246441 1870445 := bbase (se 3 (by rfl) ⟨350708, by rfl⟩ : syracuseStep 1870445 = 701417) (by norm_num)
theorem B1403509 : Blo 1246441 1403509 := bbase (se 5 (by rfl) ⟨65789, by rfl⟩ : syracuseStep 1403509 = 131579) (by norm_num)
theorem B2845309 : Blo 1246441 2845309 := bbase (se 3 (by rfl) ⟨533495, by rfl⟩ : syracuseStep 2845309 = 1066991) (by norm_num)
theorem B1870469 : Blo 1246441 1870469 := bbase (se 4 (by rfl) ⟨175356, by rfl⟩ : syracuseStep 1870469 = 350713) (by norm_num)
theorem B1403545 : Blo 1246441 1403545 := bbase (se 2 (by rfl) ⟨526329, by rfl⟩ : syracuseStep 1403545 = 1052659) (by norm_num)
theorem B1870493 : Blo 1246441 1870493 := bbase (se 3 (by rfl) ⟨350717, by rfl⟩ : syracuseStep 1870493 = 701435) (by norm_num)
theorem B1870517 : Blo 1246441 1870517 := bbase (se 5 (by rfl) ⟨87680, by rfl⟩ : syracuseStep 1870517 = 175361) (by norm_num)
theorem B1403581 : Blo 1246441 1403581 := bbase (se 3 (by rfl) ⟨263171, by rfl⟩ : syracuseStep 1403581 = 526343) (by norm_num)
theorem B1870541 : Blo 1246441 1870541 := bbase (se 3 (by rfl) ⟨350726, by rfl⟩ : syracuseStep 1870541 = 701453) (by norm_num)
theorem B1403617 : Blo 1246441 1403617 := bbase (se 2 (by rfl) ⟨526356, by rfl⟩ : syracuseStep 1403617 = 1052713) (by norm_num)
theorem B1870565 : Blo 1246441 1870565 := bbase (se 4 (by rfl) ⟨175365, by rfl⟩ : syracuseStep 1870565 = 350731) (by norm_num)
theorem B1870589 : Blo 1246441 1870589 := bbase (se 3 (by rfl) ⟨350735, by rfl⟩ : syracuseStep 1870589 = 701471) (by norm_num)
theorem B1403653 : Blo 1246441 1403653 := bbase (se 4 (by rfl) ⟨131592, by rfl⟩ : syracuseStep 1403653 = 263185) (by norm_num)
theorem B1870613 : Blo 1246441 1870613 := bbase (se 6 (by rfl) ⟨43842, by rfl⟩ : syracuseStep 1870613 = 87685) (by norm_num)
theorem B5327653 : Blo 1246441 5327653 := bbase (se 4 (by rfl) ⟨499467, by rfl⟩ : syracuseStep 5327653 = 998935) (by norm_num)
theorem B1403689 : Blo 1246441 1403689 := bbase (se 2 (by rfl) ⟨526383, by rfl⟩ : syracuseStep 1403689 = 1052767) (by norm_num)
theorem B2804525 : Blo 1246441 2804525 := bbase (se 3 (by rfl) ⟨525848, by rfl⟩ : syracuseStep 2804525 = 1051697) (by norm_num)
theorem B1870637 : Blo 1246441 1870637 := bbase (se 3 (by rfl) ⟨350744, by rfl⟩ : syracuseStep 1870637 = 701489) (by norm_num)
theorem B6310709 : Blo 1246441 6310709 := bbase (se 5 (by rfl) ⟨295814, by rfl⟩ : syracuseStep 6310709 = 591629) (by norm_num)
theorem B5327669 : Blo 1246441 5327669 := bbase (se 5 (by rfl) ⟨249734, by rfl⟩ : syracuseStep 5327669 = 499469) (by norm_num)
theorem B1870661 : Blo 1246441 1870661 := bbase (se 4 (by rfl) ⟨175374, by rfl⟩ : syracuseStep 1870661 = 350749) (by norm_num)
theorem B2132813 : Blo 1246441 2132813 := bbase (se 3 (by rfl) ⟨399902, by rfl⟩ : syracuseStep 2132813 = 799805) (by norm_num)
theorem B1403725 : Blo 1246441 1403725 := bbase (se 3 (by rfl) ⟨263198, by rfl⟩ : syracuseStep 1403725 = 526397) (by norm_num)
theorem B1870685 : Blo 1246441 1870685 := bbase (se 3 (by rfl) ⟨350753, by rfl⟩ : syracuseStep 1870685 = 701507) (by norm_num)
theorem B1403761 : Blo 1246441 1403761 := bbase (se 2 (by rfl) ⟨526410, by rfl⟩ : syracuseStep 1403761 = 1052821) (by norm_num)
theorem B2804597 : Blo 1246441 2804597 := bbase (se 5 (by rfl) ⟨131465, by rfl⟩ : syracuseStep 2804597 = 262931) (by norm_num)
theorem B1870709 : Blo 1246441 1870709 := bbase (se 5 (by rfl) ⟨87689, by rfl⟩ : syracuseStep 1870709 = 175379) (by norm_num)
theorem B3156853 : Blo 1246441 3156853 := bbase (se 5 (by rfl) ⟨147977, by rfl⟩ : syracuseStep 3156853 = 295955) (by norm_num)
theorem B1518473 : Blo 1246441 1518473 := bbase (se 2 (by rfl) ⟨569427, by rfl⟩ : syracuseStep 1518473 = 1138855) (by norm_num)
theorem B1870733 : Blo 1246441 1870733 := bbase (se 3 (by rfl) ⟨350762, by rfl⟩ : syracuseStep 1870733 = 701525) (by norm_num)
theorem B1403797 : Blo 1246441 1403797 := bbase (se 6 (by rfl) ⟨32901, by rfl⟩ : syracuseStep 1403797 = 65803) (by norm_num)
theorem B1870757 : Blo 1246441 1870757 := bbase (se 4 (by rfl) ⟨175383, by rfl⟩ : syracuseStep 1870757 = 350767) (by norm_num)
theorem B2845621 : Blo 1246441 2845621 := bbase (se 5 (by rfl) ⟨133388, by rfl⟩ : syracuseStep 2845621 = 266777) (by norm_num)
theorem B1403833 : Blo 1246441 1403833 := bbase (se 2 (by rfl) ⟨526437, by rfl⟩ : syracuseStep 1403833 = 1052875) (by norm_num)
theorem B2804669 : Blo 1246441 2804669 := bbase (se 3 (by rfl) ⟨525875, by rfl⟩ : syracuseStep 2804669 = 1051751) (by norm_num)
theorem B1870781 : Blo 1246441 1870781 := bbase (se 3 (by rfl) ⟨350771, by rfl⟩ : syracuseStep 1870781 = 701543) (by norm_num)
theorem B1870805 : Blo 1246441 1870805 := bbase (se 7 (by rfl) ⟨21923, by rfl⟩ : syracuseStep 1870805 = 43847) (by norm_num)
theorem B1403869 : Blo 1246441 1403869 := bbase (se 3 (by rfl) ⟨263225, by rfl⟩ : syracuseStep 1403869 = 526451) (by norm_num)
theorem B3156965 : Blo 1246441 3156965 := bbase (se 4 (by rfl) ⟨295965, by rfl⟩ : syracuseStep 3156965 = 591931) (by norm_num)
theorem B1870829 : Blo 1246441 1870829 := bbase (se 3 (by rfl) ⟨350780, by rfl⟩ : syracuseStep 1870829 = 701561) (by norm_num)
theorem B1403905 : Blo 1246441 1403905 := bbase (se 2 (by rfl) ⟨526464, by rfl⟩ : syracuseStep 1403905 = 1052929) (by norm_num)
theorem B2804741 : Blo 1246441 2804741 := bbase (se 4 (by rfl) ⟨262944, by rfl⟩ : syracuseStep 2804741 = 525889) (by norm_num)
theorem B1870853 : Blo 1246441 1870853 := bbase (se 4 (by rfl) ⟨175392, by rfl⟩ : syracuseStep 1870853 = 350785) (by norm_num)
theorem B6925333 : Blo 1246441 6925333 := bbase (se 6 (by rfl) ⟨162312, by rfl⟩ : syracuseStep 6925333 = 324625) (by norm_num)
theorem B1870877 : Blo 1246441 1870877 := bbase (se 3 (by rfl) ⟨350789, by rfl⟩ : syracuseStep 1870877 = 701579) (by norm_num)
theorem B1403941 : Blo 1246441 1403941 := bbase (se 4 (by rfl) ⟨131619, by rfl⟩ : syracuseStep 1403941 = 263239) (by norm_num)
theorem B1870901 : Blo 1246441 1870901 := bbase (se 5 (by rfl) ⟨87698, by rfl⟩ : syracuseStep 1870901 = 175397) (by norm_num)
theorem B1403977 : Blo 1246441 1403977 := bbase (se 2 (by rfl) ⟨526491, by rfl⟩ : syracuseStep 1403977 = 1052983) (by norm_num)
theorem B2804813 : Blo 1246441 2804813 := bbase (se 3 (by rfl) ⟨525902, by rfl⟩ : syracuseStep 2804813 = 1051805) (by norm_num)
theorem B1870925 : Blo 1246441 1870925 := bbase (se 3 (by rfl) ⟨350798, by rfl⟩ : syracuseStep 1870925 = 701597) (by norm_num)
theorem B1870949 : Blo 1246441 1870949 := bbase (se 4 (by rfl) ⟨175401, by rfl⟩ : syracuseStep 1870949 = 350803) (by norm_num)
theorem B1404013 : Blo 1246441 1404013 := bbase (se 3 (by rfl) ⟨263252, by rfl⟩ : syracuseStep 1404013 = 526505) (by norm_num)
theorem B1870973 : Blo 1246441 1870973 := bbase (se 3 (by rfl) ⟨350807, by rfl⟩ : syracuseStep 1870973 = 701615) (by norm_num)
theorem B1404049 : Blo 1246441 1404049 := bbase (se 2 (by rfl) ⟨526518, by rfl⟩ : syracuseStep 1404049 = 1053037) (by norm_num)
theorem B2804885 : Blo 1246441 2804885 := bbase (se 6 (by rfl) ⟨65739, by rfl⟩ : syracuseStep 2804885 = 131479) (by norm_num)
theorem B1870997 : Blo 1246441 1870997 := bbase (se 6 (by rfl) ⟨43851, by rfl⟩ : syracuseStep 1870997 = 87703) (by norm_num)
theorem B3157157 : Blo 1246441 3157157 := bbase (se 4 (by rfl) ⟨295983, by rfl⟩ : syracuseStep 3157157 = 591967) (by norm_num)
theorem B1871021 : Blo 1246441 1871021 := bbase (se 3 (by rfl) ⟨350816, by rfl⟩ : syracuseStep 1871021 = 701633) (by norm_num)
theorem B1404085 : Blo 1246441 1404085 := bbase (se 5 (by rfl) ⟨65816, by rfl⟩ : syracuseStep 1404085 = 131633) (by norm_num)
theorem B1871045 : Blo 1246441 1871045 := bbase (se 4 (by rfl) ⟨175410, by rfl⟩ : syracuseStep 1871045 = 350821) (by norm_num)
theorem B6745301 : Blo 1246441 6745301 := bbase (se 7 (by rfl) ⟨79046, by rfl⟩ : syracuseStep 6745301 = 158093) (by norm_num)
theorem B1518809 : Blo 1246441 1518809 := bbase (se 2 (by rfl) ⟨569553, by rfl⟩ : syracuseStep 1518809 = 1139107) (by norm_num)
theorem B1404121 : Blo 1246441 1404121 := bbase (se 2 (by rfl) ⟨526545, by rfl⟩ : syracuseStep 1404121 = 1053091) (by norm_num)
theorem B2804957 : Blo 1246441 2804957 := bbase (se 3 (by rfl) ⟨525929, by rfl⟩ : syracuseStep 2804957 = 1051859) (by norm_num)
theorem B1871069 : Blo 1246441 1871069 := bbase (se 3 (by rfl) ⟨350825, by rfl⟩ : syracuseStep 1871069 = 701651) (by norm_num)
theorem B1871093 : Blo 1246441 1871093 := bbase (se 5 (by rfl) ⟨87707, by rfl⟩ : syracuseStep 1871093 = 175415) (by norm_num)
theorem B1404157 : Blo 1246441 1404157 := bbase (se 3 (by rfl) ⟨263279, by rfl⟩ : syracuseStep 1404157 = 526559) (by norm_num)
theorem B1871117 : Blo 1246441 1871117 := bbase (se 3 (by rfl) ⟨350834, by rfl⟩ : syracuseStep 1871117 = 701669) (by norm_num)
theorem B1404193 : Blo 1246441 1404193 := bbase (se 2 (by rfl) ⟨526572, by rfl⟩ : syracuseStep 1404193 = 1053145) (by norm_num)
theorem B2805029 : Blo 1246441 2805029 := bbase (se 4 (by rfl) ⟨262971, by rfl⟩ : syracuseStep 2805029 = 525943) (by norm_num)
theorem B1871141 : Blo 1246441 1871141 := bbase (se 4 (by rfl) ⟨175419, by rfl⟩ : syracuseStep 1871141 = 350839) (by norm_num)
theorem B1871165 : Blo 1246441 1871165 := bbase (se 3 (by rfl) ⟨350843, by rfl⟩ : syracuseStep 1871165 = 701687) (by norm_num)
theorem B1404229 : Blo 1246441 1404229 := bbase (se 4 (by rfl) ⟨131646, by rfl⟩ : syracuseStep 1404229 = 263293) (by norm_num)
theorem B3550549 : Blo 1246441 3550549 := bbase (se 11 (by rfl) ⟨2600, by rfl⟩ : syracuseStep 3550549 = 5201) (by norm_num)
theorem B1871189 : Blo 1246441 1871189 := bbase (se 11 (by rfl) ⟨1370, by rfl⟩ : syracuseStep 1871189 = 2741) (by norm_num)
theorem B1404265 : Blo 1246441 1404265 := bbase (se 2 (by rfl) ⟨526599, by rfl⟩ : syracuseStep 1404265 = 1053199) (by norm_num)
theorem B2805101 : Blo 1246441 2805101 := bbase (se 3 (by rfl) ⟨525956, by rfl⟩ : syracuseStep 2805101 = 1051913) (by norm_num)
theorem B1895789 : Blo 1246441 1895789 := bbase (se 3 (by rfl) ⟨355460, by rfl⟩ : syracuseStep 1895789 = 710921) (by norm_num)
theorem B1871213 : Blo 1246441 1871213 := bbase (se 3 (by rfl) ⟨350852, by rfl⟩ : syracuseStep 1871213 = 701705) (by norm_num)
theorem B7196021 : Blo 1246441 7196021 := bbase (se 5 (by rfl) ⟨337313, by rfl⟩ : syracuseStep 7196021 = 674627) (by norm_num)
theorem B1871237 : Blo 1246441 1871237 := bbase (se 4 (by rfl) ⟨175428, by rfl⟩ : syracuseStep 1871237 = 350857) (by norm_num)
theorem B1404301 : Blo 1246441 1404301 := bbase (se 3 (by rfl) ⟨263306, by rfl⟩ : syracuseStep 1404301 = 526613) (by norm_num)
theorem B1871261 : Blo 1246441 1871261 := bbase (se 3 (by rfl) ⟨350861, by rfl⟩ : syracuseStep 1871261 = 701723) (by norm_num)
theorem B2665885 : Blo 1246441 2665885 := bbase (se 3 (by rfl) ⟨499853, by rfl⟩ : syracuseStep 2665885 = 999707) (by norm_num)
theorem B1404337 : Blo 1246441 1404337 := bbase (se 2 (by rfl) ⟨526626, by rfl⟩ : syracuseStep 1404337 = 1053253) (by norm_num)
theorem B2805173 : Blo 1246441 2805173 := bbase (se 5 (by rfl) ⟨131492, by rfl⟩ : syracuseStep 2805173 = 262985) (by norm_num)
theorem B1871285 : Blo 1246441 1871285 := bbase (se 5 (by rfl) ⟨87716, by rfl⟩ : syracuseStep 1871285 = 175433) (by norm_num)
theorem B1871309 : Blo 1246441 1871309 := bbase (se 3 (by rfl) ⟨350870, by rfl⟩ : syracuseStep 1871309 = 701741) (by norm_num)
theorem B1404373 : Blo 1246441 1404373 := bbase (se 7 (by rfl) ⟨16457, by rfl⟩ : syracuseStep 1404373 = 32915) (by norm_num)
theorem B1871333 : Blo 1246441 1871333 := bbase (se 4 (by rfl) ⟨175437, by rfl⟩ : syracuseStep 1871333 = 350875) (by norm_num)
theorem B3550709 : Blo 1246441 3550709 := bbase (se 5 (by rfl) ⟨166439, by rfl⟩ : syracuseStep 3550709 = 332879) (by norm_num)
theorem B1404409 : Blo 1246441 1404409 := bbase (se 2 (by rfl) ⟨526653, by rfl⟩ : syracuseStep 1404409 = 1053307) (by norm_num)
theorem B2805245 : Blo 1246441 2805245 := bbase (se 3 (by rfl) ⟨525983, by rfl⟩ : syracuseStep 2805245 = 1051967) (by norm_num)
theorem B3157501 : Blo 1246441 3157501 := bbase (se 3 (by rfl) ⟨592031, by rfl⟩ : syracuseStep 3157501 = 1184063) (by norm_num)
theorem B1871357 : Blo 1246441 1871357 := bbase (se 3 (by rfl) ⟨350879, by rfl⟩ : syracuseStep 1871357 = 701759) (by norm_num)
theorem B1871381 : Blo 1246441 1871381 := bbase (se 6 (by rfl) ⟨43860, by rfl⟩ : syracuseStep 1871381 = 87721) (by norm_num)
theorem B1404445 : Blo 1246441 1404445 := bbase (se 3 (by rfl) ⟨263333, by rfl⟩ : syracuseStep 1404445 = 526667) (by norm_num)
theorem B1871405 : Blo 1246441 1871405 := bbase (se 3 (by rfl) ⟨350888, by rfl⟩ : syracuseStep 1871405 = 701777) (by norm_num)
theorem B1404481 : Blo 1246441 1404481 := bbase (se 2 (by rfl) ⟨526680, by rfl⟩ : syracuseStep 1404481 = 1053361) (by norm_num)
theorem B2805317 : Blo 1246441 2805317 := bbase (se 4 (by rfl) ⟨262998, by rfl⟩ : syracuseStep 2805317 = 525997) (by norm_num)
theorem B1871429 : Blo 1246441 1871429 := bbase (se 4 (by rfl) ⟨175446, by rfl⟩ : syracuseStep 1871429 = 350893) (by norm_num)
theorem B1871453 : Blo 1246441 1871453 := bbase (se 3 (by rfl) ⟨350897, by rfl⟩ : syracuseStep 1871453 = 701795) (by norm_num)
theorem B3157613 : Blo 1246441 3157613 := bbase (se 3 (by rfl) ⟨592052, by rfl⟩ : syracuseStep 3157613 = 1184105) (by norm_num)
theorem B1871477 : Blo 1246441 1871477 := bbase (se 5 (by rfl) ⟨87725, by rfl⟩ : syracuseStep 1871477 = 175451) (by norm_num)
theorem B2805389 : Blo 1246441 2805389 := bbase (se 3 (by rfl) ⟨526010, by rfl⟩ : syracuseStep 2805389 = 1052021) (by norm_num)
theorem B1871501 : Blo 1246441 1871501 := bbase (se 3 (by rfl) ⟨350906, by rfl⟩ : syracuseStep 1871501 = 701813) (by norm_num)
theorem B1871525 : Blo 1246441 1871525 := bbase (se 4 (by rfl) ⟨175455, by rfl⟩ : syracuseStep 1871525 = 350911) (by norm_num)
theorem B6319781 : Blo 1246441 6319781 := bbase (se 4 (by rfl) ⟨592479, by rfl⟩ : syracuseStep 6319781 = 1184959) (by norm_num)
theorem B1560253 : Blo 1246441 1560253 := bbase (se 3 (by rfl) ⟨292547, by rfl⟩ : syracuseStep 1560253 = 585095) (by norm_num)
theorem B1871549 : Blo 1246441 1871549 := bbase (se 3 (by rfl) ⟨350915, by rfl⟩ : syracuseStep 1871549 = 701831) (by norm_num)
theorem B2805461 : Blo 1246441 2805461 := bbase (se 7 (by rfl) ⟨32876, by rfl⟩ : syracuseStep 2805461 = 65753) (by norm_num)
theorem B1871573 : Blo 1246441 1871573 := bbase (se 7 (by rfl) ⟨21932, by rfl⟩ : syracuseStep 1871573 = 43865) (by norm_num)
theorem B3550949 : Blo 1246441 3550949 := bbase (se 4 (by rfl) ⟨332901, by rfl⟩ : syracuseStep 3550949 = 665803) (by norm_num)
theorem B1871597 : Blo 1246441 1871597 := bbase (se 3 (by rfl) ⟨350924, by rfl⟩ : syracuseStep 1871597 = 701849) (by norm_num)
theorem B1871621 : Blo 1246441 1871621 := bbase (se 4 (by rfl) ⟨175464, by rfl⟩ : syracuseStep 1871621 = 350929) (by norm_num)
theorem B2805533 : Blo 1246441 2805533 := bbase (se 3 (by rfl) ⟨526037, by rfl⟩ : syracuseStep 2805533 = 1052075) (by norm_num)
theorem B1871645 : Blo 1246441 1871645 := bbase (se 3 (by rfl) ⟨350933, by rfl⟩ : syracuseStep 1871645 = 701867) (by norm_num)
theorem B3157805 : Blo 1246441 3157805 := bbase (se 3 (by rfl) ⟨592088, by rfl⟩ : syracuseStep 3157805 = 1184177) (by norm_num)
theorem B1871669 : Blo 1246441 1871669 := bbase (se 5 (by rfl) ⟨87734, by rfl⟩ : syracuseStep 1871669 = 175469) (by norm_num)
theorem B1871693 : Blo 1246441 1871693 := bbase (se 3 (by rfl) ⟨350942, by rfl⟩ : syracuseStep 1871693 = 701885) (by norm_num)
theorem B2846549 : Blo 1246441 2846549 := bbase (se 9 (by rfl) ⟨8339, by rfl⟩ : syracuseStep 2846549 = 16679) (by norm_num)
theorem B2805605 : Blo 1246441 2805605 := bbase (se 4 (by rfl) ⟨263025, by rfl⟩ : syracuseStep 2805605 = 526051) (by norm_num)
theorem B1871717 : Blo 1246441 1871717 := bbase (se 4 (by rfl) ⟨175473, by rfl⟩ : syracuseStep 1871717 = 350947) (by norm_num)
theorem B1871741 : Blo 1246441 1871741 := bbase (se 3 (by rfl) ⟨350951, by rfl⟩ : syracuseStep 1871741 = 701903) (by norm_num)
theorem B7106453 : Blo 1246441 7106453 := bbase (se 6 (by rfl) ⟨166557, by rfl⟩ : syracuseStep 7106453 = 333115) (by norm_num)
theorem B1871765 : Blo 1246441 1871765 := bbase (se 6 (by rfl) ⟨43869, by rfl⟩ : syracuseStep 1871765 = 87739) (by norm_num)
theorem B3551141 : Blo 1246441 3551141 := bbase (se 4 (by rfl) ⟨332919, by rfl⟩ : syracuseStep 3551141 = 665839) (by norm_num)
theorem B2805677 : Blo 1246441 2805677 := bbase (se 3 (by rfl) ⟨526064, by rfl⟩ : syracuseStep 2805677 = 1052129) (by norm_num)
theorem B1871789 : Blo 1246441 1871789 := bbase (se 3 (by rfl) ⟨350960, by rfl⟩ : syracuseStep 1871789 = 701921) (by norm_num)
theorem B1871813 : Blo 1246441 1871813 := bbase (se 4 (by rfl) ⟨175482, by rfl⟩ : syracuseStep 1871813 = 350965) (by norm_num)
theorem B1871837 : Blo 1246441 1871837 := bbase (se 3 (by rfl) ⟨350969, by rfl⟩ : syracuseStep 1871837 = 701939) (by norm_num)
theorem B2805749 : Blo 1246441 2805749 := bbase (se 5 (by rfl) ⟨131519, by rfl⟩ : syracuseStep 2805749 = 263039) (by norm_num)
theorem B1871861 : Blo 1246441 1871861 := bbase (se 5 (by rfl) ⟨87743, by rfl⟩ : syracuseStep 1871861 = 175487) (by norm_num)
theorem B1871885 : Blo 1246441 1871885 := bbase (se 3 (by rfl) ⟨350978, by rfl⟩ : syracuseStep 1871885 = 701957) (by norm_num)
theorem B4739093 : Blo 1246441 4739093 := bbase (se 6 (by rfl) ⟨111072, by rfl⟩ : syracuseStep 4739093 = 222145) (by norm_num)
theorem B2846749 : Blo 1246441 2846749 := bbase (se 3 (by rfl) ⟨533765, by rfl⟩ : syracuseStep 2846749 = 1067531) (by norm_num)
theorem B1871909 : Blo 1246441 1871909 := bbase (se 4 (by rfl) ⟨175491, by rfl⟩ : syracuseStep 1871909 = 350983) (by norm_num)
theorem B2805821 : Blo 1246441 2805821 := bbase (se 3 (by rfl) ⟨526091, by rfl⟩ : syracuseStep 2805821 = 1052183) (by norm_num)
theorem B1871933 : Blo 1246441 1871933 := bbase (se 3 (by rfl) ⟨350987, by rfl⟩ : syracuseStep 1871933 = 701975) (by norm_num)
theorem B6312005 : Blo 1246441 6312005 := bbase (se 4 (by rfl) ⟨591750, by rfl⟩ : syracuseStep 6312005 = 1183501) (by norm_num)
theorem B1871957 : Blo 1246441 1871957 := bbase (se 8 (by rfl) ⟨10968, by rfl⟩ : syracuseStep 1871957 = 21937) (by norm_num)
theorem B1871981 : Blo 1246441 1871981 := bbase (se 3 (by rfl) ⟨350996, by rfl⟩ : syracuseStep 1871981 = 701993) (by norm_num)
theorem B2805893 : Blo 1246441 2805893 := bbase (se 4 (by rfl) ⟨263052, by rfl⟩ : syracuseStep 2805893 = 526105) (by norm_num)
theorem B3158149 : Blo 1246441 3158149 := bbase (se 4 (by rfl) ⟨296076, by rfl⟩ : syracuseStep 3158149 = 592153) (by norm_num)
theorem B1872005 : Blo 1246441 1872005 := bbase (se 4 (by rfl) ⟨175500, by rfl⟩ : syracuseStep 1872005 = 351001) (by norm_num)
theorem B1872029 : Blo 1246441 1872029 := bbase (se 3 (by rfl) ⟨351005, by rfl⟩ : syracuseStep 1872029 = 702011) (by norm_num)
theorem B1896629 : Blo 1246441 1896629 := bbase (se 5 (by rfl) ⟨88904, by rfl⟩ : syracuseStep 1896629 = 177809) (by norm_num)
theorem B1872053 : Blo 1246441 1872053 := bbase (se 5 (by rfl) ⟨87752, by rfl⟩ : syracuseStep 1872053 = 175505) (by norm_num)
theorem B2699453 : Blo 1246441 2699453 := bbase (se 3 (by rfl) ⟨506147, by rfl⟩ : syracuseStep 2699453 = 1012295) (by norm_num)
theorem B5689541 : Blo 1246441 5689541 := bbase (se 4 (by rfl) ⟨533394, by rfl⟩ : syracuseStep 5689541 = 1066789) (by norm_num)
theorem B2805965 : Blo 1246441 2805965 := bbase (se 3 (by rfl) ⟨526118, by rfl⟩ : syracuseStep 2805965 = 1052237) (by norm_num)
theorem B1872077 : Blo 1246441 1872077 := bbase (se 3 (by rfl) ⟨351014, by rfl⟩ : syracuseStep 1872077 = 702029) (by norm_num)
theorem B10809557 : Blo 1246441 10809557 := bbase (se 7 (by rfl) ⟨126674, by rfl⟩ : syracuseStep 10809557 = 253349) (by norm_num)
theorem B1872101 : Blo 1246441 1872101 := bbase (se 4 (by rfl) ⟨175509, by rfl⟩ : syracuseStep 1872101 = 351019) (by norm_num)
theorem B3158261 : Blo 1246441 3158261 := bbase (se 5 (by rfl) ⟨148043, by rfl⟩ : syracuseStep 3158261 = 296087) (by norm_num)
theorem B1872125 : Blo 1246441 1872125 := bbase (se 3 (by rfl) ⟨351023, by rfl⟩ : syracuseStep 1872125 = 702047) (by norm_num)
theorem B4206869 : Blo 1246441 4206869 := bbase (se 6 (by rfl) ⟨98598, by rfl⟩ : syracuseStep 4206869 = 197197) (by norm_num)
theorem B2806037 : Blo 1246441 2806037 := bbase (se 6 (by rfl) ⟨65766, by rfl⟩ : syracuseStep 2806037 = 131533) (by norm_num)
theorem B1872149 : Blo 1246441 1872149 := bbase (se 6 (by rfl) ⟨43878, by rfl⟩ : syracuseStep 1872149 = 87757) (by norm_num)
theorem B1872173 : Blo 1246441 1872173 := bbase (se 3 (by rfl) ⟨351032, by rfl⟩ : syracuseStep 1872173 = 702065) (by norm_num)
theorem B4739381 : Blo 1246441 4739381 := bbase (se 5 (by rfl) ⟨222158, by rfl⟩ : syracuseStep 4739381 = 444317) (by norm_num)
theorem B1872197 : Blo 1246441 1872197 := bbase (se 4 (by rfl) ⟨175518, by rfl⟩ : syracuseStep 1872197 = 351037) (by norm_num)
theorem B2806109 : Blo 1246441 2806109 := bbase (se 3 (by rfl) ⟨526145, by rfl⟩ : syracuseStep 2806109 = 1052291) (by norm_num)
theorem B1872221 : Blo 1246441 1872221 := bbase (se 3 (by rfl) ⟨351041, by rfl⟩ : syracuseStep 1872221 = 702083) (by norm_num)
theorem B1872245 : Blo 1246441 1872245 := bbase (se 5 (by rfl) ⟨87761, by rfl⟩ : syracuseStep 1872245 = 175523) (by norm_num)
theorem B1872269 : Blo 1246441 1872269 := bbase (se 3 (by rfl) ⟨351050, by rfl⟩ : syracuseStep 1872269 = 702101) (by norm_num)
theorem B2806181 : Blo 1246441 2806181 := bbase (se 4 (by rfl) ⟨263079, by rfl⟩ : syracuseStep 2806181 = 526159) (by norm_num)
theorem B1872293 : Blo 1246441 1872293 := bbase (se 4 (by rfl) ⟨175527, by rfl⟩ : syracuseStep 1872293 = 351055) (by norm_num)
theorem B3158453 : Blo 1246441 3158453 := bbase (se 5 (by rfl) ⟨148052, by rfl⟩ : syracuseStep 3158453 = 296105) (by norm_num)
theorem B1872317 : Blo 1246441 1872317 := bbase (se 3 (by rfl) ⟨351059, by rfl⟩ : syracuseStep 1872317 = 702119) (by norm_num)
theorem B1872341 : Blo 1246441 1872341 := bbase (se 7 (by rfl) ⟨21941, by rfl⟩ : syracuseStep 1872341 = 43883) (by norm_num)
theorem B2806253 : Blo 1246441 2806253 := bbase (se 3 (by rfl) ⟨526172, by rfl⟩ : syracuseStep 2806253 = 1052345) (by norm_num)
theorem B1872365 : Blo 1246441 1872365 := bbase (se 3 (by rfl) ⟨351068, by rfl⟩ : syracuseStep 1872365 = 702137) (by norm_num)
theorem B1872389 : Blo 1246441 1872389 := bbase (se 4 (by rfl) ⟨175536, by rfl⟩ : syracuseStep 1872389 = 351073) (by norm_num)
theorem B1872413 : Blo 1246441 1872413 := bbase (se 3 (by rfl) ⟨351077, by rfl⟩ : syracuseStep 1872413 = 702155) (by norm_num)
theorem B2806325 : Blo 1246441 2806325 := bbase (se 5 (by rfl) ⟨131546, by rfl⟩ : syracuseStep 2806325 = 263093) (by norm_num)
theorem B1872437 : Blo 1246441 1872437 := bbase (se 5 (by rfl) ⟨87770, by rfl⟩ : syracuseStep 1872437 = 175541) (by norm_num)
theorem B1872461 : Blo 1246441 1872461 := bbase (se 3 (by rfl) ⟨351086, by rfl⟩ : syracuseStep 1872461 = 702173) (by norm_num)
theorem B1872485 : Blo 1246441 1872485 := bbase (se 4 (by rfl) ⟨175545, by rfl⟩ : syracuseStep 1872485 = 351091) (by norm_num)
theorem B2806397 : Blo 1246441 2806397 := bbase (se 3 (by rfl) ⟨526199, by rfl⟩ : syracuseStep 2806397 = 1052399) (by norm_num)
theorem B1872509 : Blo 1246441 1872509 := bbase (se 3 (by rfl) ⟨351095, by rfl⟩ : syracuseStep 1872509 = 702191) (by norm_num)
theorem B5403269 : Blo 1246441 5403269 := bbase (se 4 (by rfl) ⟨506556, by rfl⟩ : syracuseStep 5403269 = 1013113) (by norm_num)
theorem B1331849 : Blo 1246441 1331849 := bbase (se 2 (by rfl) ⟨499443, by rfl⟩ : syracuseStep 1331849 = 998887) (by norm_num)
theorem B1872533 : Blo 1246441 1872533 := bbase (se 6 (by rfl) ⟨43887, by rfl⟩ : syracuseStep 1872533 = 87775) (by norm_num)
theorem B6402725 : Blo 1246441 6402725 := bbase (se 4 (by rfl) ⟨600255, by rfl⟩ : syracuseStep 6402725 = 1200511) (by norm_num)
theorem B1872557 : Blo 1246441 1872557 := bbase (se 3 (by rfl) ⟨351104, by rfl⟩ : syracuseStep 1872557 = 702209) (by norm_num)
theorem B1577657 : Blo 1246441 1577657 := bbase (se 2 (by rfl) ⟨591621, by rfl⟩ : syracuseStep 1577657 = 1183243) (by norm_num)
theorem B4207301 : Blo 1246441 4207301 := bbase (se 4 (by rfl) ⟨394434, by rfl⟩ : syracuseStep 4207301 = 788869) (by norm_num)
theorem B2806469 : Blo 1246441 2806469 := bbase (se 4 (by rfl) ⟨263106, by rfl⟩ : syracuseStep 2806469 = 526213) (by norm_num)
theorem B1872581 : Blo 1246441 1872581 := bbase (se 4 (by rfl) ⟨175554, by rfl⟩ : syracuseStep 1872581 = 351109) (by norm_num)
theorem B1872605 : Blo 1246441 1872605 := bbase (se 3 (by rfl) ⟨351113, by rfl⟩ : syracuseStep 1872605 = 702227) (by norm_num)
theorem B1577713 : Blo 1246441 1577713 := bbase (se 2 (by rfl) ⟨591642, by rfl⟩ : syracuseStep 1577713 = 1183285) (by norm_num)
theorem B1872629 : Blo 1246441 1872629 := bbase (se 5 (by rfl) ⟨87779, by rfl⟩ : syracuseStep 1872629 = 175559) (by norm_num)
theorem B2806541 : Blo 1246441 2806541 := bbase (se 3 (by rfl) ⟨526226, by rfl⟩ : syracuseStep 2806541 = 1052453) (by norm_num)
theorem B3158797 : Blo 1246441 3158797 := bbase (se 3 (by rfl) ⟨592274, by rfl⟩ : syracuseStep 3158797 = 1184549) (by norm_num)
theorem B1872653 : Blo 1246441 1872653 := bbase (se 3 (by rfl) ⟨351122, by rfl⟩ : syracuseStep 1872653 = 702245) (by norm_num)
theorem B10654517 : Blo 1246441 10654517 := bbase (se 5 (by rfl) ⟨499430, by rfl⟩ : syracuseStep 10654517 = 998861) (by norm_num)
theorem B1577809 : Blo 1246441 1577809 := bbase (se 2 (by rfl) ⟨591678, by rfl⟩ : syracuseStep 1577809 = 1183357) (by norm_num)
theorem B2806613 : Blo 1246441 2806613 := bbase (se 9 (by rfl) ⟨8222, by rfl⟩ : syracuseStep 2806613 = 16445) (by norm_num)
theorem B3158909 : Blo 1246441 3158909 := bbase (se 3 (by rfl) ⟨592295, by rfl⟩ : syracuseStep 3158909 = 1184591) (by norm_num)
theorem B3552133 : Blo 1246441 3552133 := bbase (se 4 (by rfl) ⟨333012, by rfl⟩ : syracuseStep 3552133 = 666025) (by norm_num)
theorem B2806685 : Blo 1246441 2806685 := bbase (se 3 (by rfl) ⟨526253, by rfl⟩ : syracuseStep 2806685 = 1052507) (by norm_num)
theorem B6157237 : Blo 1246441 6157237 := bbase (se 5 (by rfl) ⟨288620, by rfl⟩ : syracuseStep 6157237 = 577241) (by norm_num)
theorem B3601349 : Blo 1246441 3601349 := bbase (se 4 (by rfl) ⟨337626, by rfl⟩ : syracuseStep 3601349 = 675253) (by norm_num)
theorem B2806757 : Blo 1246441 2806757 := bbase (se 4 (by rfl) ⟨263133, by rfl⟩ : syracuseStep 2806757 = 526267) (by norm_num)
theorem B1577981 : Blo 1246441 1577981 := bbase (se 3 (by rfl) ⟨295871, by rfl⟩ : syracuseStep 1577981 = 591743) (by norm_num)
theorem B5329925 : Blo 1246441 5329925 := bbase (se 4 (by rfl) ⟨499680, by rfl⟩ : syracuseStep 5329925 = 999361) (by norm_num)
theorem B2806829 : Blo 1246441 2806829 := bbase (se 3 (by rfl) ⟨526280, by rfl⟩ : syracuseStep 2806829 = 1052561) (by norm_num)
theorem B1578037 : Blo 1246441 1578037 := bbase (se 5 (by rfl) ⟨73970, by rfl⟩ : syracuseStep 1578037 = 147941) (by norm_num)
theorem B3159101 : Blo 1246441 3159101 := bbase (se 3 (by rfl) ⟨592331, by rfl⟩ : syracuseStep 3159101 = 1184663) (by norm_num)
theorem B1332293 : Blo 1246441 1332293 := bbase (se 4 (by rfl) ⟨124902, by rfl⟩ : syracuseStep 1332293 = 249805) (by norm_num)
theorem B4207733 : Blo 1246441 4207733 := bbase (se 5 (by rfl) ⟨197237, by rfl⟩ : syracuseStep 4207733 = 394475) (by norm_num)
theorem B2806901 : Blo 1246441 2806901 := bbase (se 5 (by rfl) ⟨131573, by rfl⟩ : syracuseStep 2806901 = 263147) (by norm_num)
theorem B1578133 : Blo 1246441 1578133 := bbase (se 6 (by rfl) ⟨36987, by rfl⟩ : syracuseStep 1578133 = 73975) (by norm_num)
theorem B2806973 : Blo 1246441 2806973 := bbase (se 3 (by rfl) ⟨526307, by rfl⟩ : syracuseStep 2806973 = 1052615) (by norm_num)
theorem B8541397 : Blo 1246441 8541397 := bbase (se 7 (by rfl) ⟨100094, by rfl⟩ : syracuseStep 8541397 = 200189) (by norm_num)
theorem B2807045 : Blo 1246441 2807045 := bbase (se 4 (by rfl) ⟨263160, by rfl⟩ : syracuseStep 2807045 = 526321) (by norm_num)
theorem B2995469 : Blo 1246441 2995469 := bbase (se 3 (by rfl) ⟨561650, by rfl⟩ : syracuseStep 2995469 = 1123301) (by norm_num)
theorem B1332541 : Blo 1246441 1332541 := bbase (se 3 (by rfl) ⟨249851, by rfl⟩ : syracuseStep 1332541 = 499703) (by norm_num)
theorem B1578305 : Blo 1246441 1578305 := bbase (se 2 (by rfl) ⟨591864, by rfl⟩ : syracuseStep 1578305 = 1183729) (by norm_num)
theorem B2807117 : Blo 1246441 2807117 := bbase (se 3 (by rfl) ⟨526334, by rfl⟩ : syracuseStep 2807117 = 1052669) (by norm_num)
theorem B6313301 : Blo 1246441 6313301 := bbase (se 16 (by rfl) ⟨144, by rfl⟩ : syracuseStep 6313301 = 289) (by norm_num)
theorem B1578361 : Blo 1246441 1578361 := bbase (se 2 (by rfl) ⟨591885, by rfl⟩ : syracuseStep 1578361 = 1183771) (by norm_num)
theorem B1774973 : Blo 1246441 1774973 := bbase (se 3 (by rfl) ⟨332807, by rfl⟩ : syracuseStep 1774973 = 665615) (by norm_num)
theorem B2807189 : Blo 1246441 2807189 := bbase (se 6 (by rfl) ⟨65793, by rfl⟩ : syracuseStep 2807189 = 131587) (by norm_num)
theorem B3159445 : Blo 1246441 3159445 := bbase (se 6 (by rfl) ⟨74049, by rfl⟩ : syracuseStep 3159445 = 148099) (by norm_num)
theorem B1684909 : Blo 1246441 1684909 := bbase (se 3 (by rfl) ⟨315920, by rfl⟩ : syracuseStep 1684909 = 631841) (by norm_num)
theorem B2528725 : Blo 1246441 2528725 := bbase (se 7 (by rfl) ⟨29633, by rfl⟩ : syracuseStep 2528725 = 59267) (by norm_num)
theorem B9475541 : Blo 1246441 9475541 := bbase (se 7 (by rfl) ⟨111041, by rfl⟩ : syracuseStep 9475541 = 222083) (by norm_num)
theorem B38426069 : Blo 1246441 38426069 := bbase (se 7 (by rfl) ⟨450305, by rfl⟩ : syracuseStep 38426069 = 900611) (by norm_num)
theorem B1578457 : Blo 1246441 1578457 := bbase (se 2 (by rfl) ⟨591921, by rfl⟩ : syracuseStep 1578457 = 1183843) (by norm_num)
theorem B2807261 : Blo 1246441 2807261 := bbase (se 3 (by rfl) ⟨526361, by rfl⟩ : syracuseStep 2807261 = 1052723) (by norm_num)
theorem B3159557 : Blo 1246441 3159557 := bbase (se 4 (by rfl) ⟨296208, by rfl⟩ : syracuseStep 3159557 = 592417) (by norm_num)
theorem B4208165 : Blo 1246441 4208165 := bbase (se 4 (by rfl) ⟨394515, by rfl⟩ : syracuseStep 4208165 = 789031) (by norm_num)
theorem B2807333 : Blo 1246441 2807333 := bbase (se 4 (by rfl) ⟨263187, by rfl⟩ : syracuseStep 2807333 = 526375) (by norm_num)
theorem B3995189 : Blo 1246441 3995189 := bbase (se 5 (by rfl) ⟨187274, by rfl⟩ : syracuseStep 3995189 = 374549) (by norm_num)
theorem B7992917 : Blo 1246441 7992917 := bbase (se 8 (by rfl) ⟨46833, by rfl⟩ : syracuseStep 7992917 = 93667) (by norm_num)
theorem B2807405 : Blo 1246441 2807405 := bbase (se 3 (by rfl) ⟨526388, by rfl⟩ : syracuseStep 2807405 = 1052777) (by norm_num)
theorem B1898101 : Blo 1246441 1898101 := bbase (se 5 (by rfl) ⟨88973, by rfl⟩ : syracuseStep 1898101 = 177947) (by norm_num)
theorem B1578629 : Blo 1246441 1578629 := bbase (se 4 (by rfl) ⟨147996, by rfl⟩ : syracuseStep 1578629 = 295993) (by norm_num)
theorem B2807477 : Blo 1246441 2807477 := bbase (se 5 (by rfl) ⟨131600, by rfl⟩ : syracuseStep 2807477 = 263201) (by norm_num)
theorem B1578685 : Blo 1246441 1578685 := bbase (se 3 (by rfl) ⟨296003, by rfl⟩ : syracuseStep 1578685 = 592007) (by norm_num)
theorem B1898173 : Blo 1246441 1898173 := bbase (se 3 (by rfl) ⟨355907, by rfl⟩ : syracuseStep 1898173 = 711815) (by norm_num)
theorem B1685189 : Blo 1246441 1685189 := bbase (se 4 (by rfl) ⟨157986, by rfl⟩ : syracuseStep 1685189 = 315973) (by norm_num)
theorem B3159749 : Blo 1246441 3159749 := bbase (se 4 (by rfl) ⟨296226, by rfl⟩ : syracuseStep 3159749 = 592453) (by norm_num)
theorem B1332973 : Blo 1246441 1332973 := bbase (se 3 (by rfl) ⟨249932, by rfl⟩ : syracuseStep 1332973 = 499865) (by norm_num)
theorem B2807549 : Blo 1246441 2807549 := bbase (se 3 (by rfl) ⟨526415, by rfl⟩ : syracuseStep 2807549 = 1052831) (by norm_num)
theorem B1578781 : Blo 1246441 1578781 := bbase (se 3 (by rfl) ⟨296021, by rfl⟩ : syracuseStep 1578781 = 592043) (by norm_num)
theorem B1996589 : Blo 1246441 1996589 := bbase (se 3 (by rfl) ⟨374360, by rfl⟩ : syracuseStep 1996589 = 748721) (by norm_num)
theorem B1333045 : Blo 1246441 1333045 := bbase (se 5 (by rfl) ⟨62486, by rfl⟩ : syracuseStep 1333045 = 124973) (by norm_num)
theorem B2807621 : Blo 1246441 2807621 := bbase (se 4 (by rfl) ⟨263214, by rfl⟩ : syracuseStep 2807621 = 526429) (by norm_num)
theorem B4732789 : Blo 1246441 4732789 := bbase (se 5 (by rfl) ⟨221849, by rfl⟩ : syracuseStep 4732789 = 443699) (by norm_num)
theorem B9467765 : Blo 1246441 9467765 := bbase (se 5 (by rfl) ⟨443801, by rfl⟩ : syracuseStep 9467765 = 887603) (by norm_num)
theorem B1423229 : Blo 1246441 1423229 := bbase (se 3 (by rfl) ⟨266855, by rfl⟩ : syracuseStep 1423229 = 533711) (by norm_num)
theorem B2807693 : Blo 1246441 2807693 := bbase (se 3 (by rfl) ⟨526442, by rfl⟩ : syracuseStep 2807693 = 1052885) (by norm_num)
theorem B1775525 : Blo 1246441 1775525 := bbase (se 4 (by rfl) ⟨166455, by rfl⟩ : syracuseStep 1775525 = 332911) (by norm_num)
theorem B3372965 : Blo 1246441 3372965 := bbase (se 4 (by rfl) ⟨316215, by rfl⟩ : syracuseStep 3372965 = 632431) (by norm_num)
theorem B1578953 : Blo 1246441 1578953 := bbase (se 2 (by rfl) ⟨592107, by rfl⟩ : syracuseStep 1578953 = 1184215) (by norm_num)
theorem B4208597 : Blo 1246441 4208597 := bbase (se 7 (by rfl) ⟨49319, by rfl⟩ : syracuseStep 4208597 = 98639) (by norm_num)
theorem B3553237 : Blo 1246441 3553237 := bbase (se 7 (by rfl) ⟨41639, by rfl⟩ : syracuseStep 3553237 = 83279) (by norm_num)
theorem B2807765 : Blo 1246441 2807765 := bbase (se 7 (by rfl) ⟨32903, by rfl⟩ : syracuseStep 2807765 = 65807) (by norm_num)
theorem B1579009 : Blo 1246441 1579009 := bbase (se 2 (by rfl) ⟨592128, by rfl⟩ : syracuseStep 1579009 = 1184257) (by norm_num)
theorem B2807837 : Blo 1246441 2807837 := bbase (se 3 (by rfl) ⟨526469, by rfl⟩ : syracuseStep 2807837 = 1052939) (by norm_num)
theorem B3160093 : Blo 1246441 3160093 := bbase (se 3 (by rfl) ⟨592517, by rfl⟩ : syracuseStep 3160093 = 1185035) (by norm_num)
theorem B3037229 : Blo 1246441 3037229 := bbase (se 3 (by rfl) ⟨569480, by rfl⟩ : syracuseStep 3037229 = 1138961) (by norm_num)
theorem B7108661 : Blo 1246441 7108661 := bbase (se 5 (by rfl) ⟨333218, by rfl⟩ : syracuseStep 7108661 = 666437) (by norm_num)
theorem B3037253 : Blo 1246441 3037253 := bbase (se 4 (by rfl) ⟨284742, by rfl⟩ : syracuseStep 3037253 = 569485) (by norm_num)
theorem B1579105 : Blo 1246441 1579105 := bbase (se 2 (by rfl) ⟨592164, by rfl⟩ : syracuseStep 1579105 = 1184329) (by norm_num)
theorem B2807909 : Blo 1246441 2807909 := bbase (se 4 (by rfl) ⟨263241, by rfl⟩ : syracuseStep 2807909 = 526483) (by norm_num)
theorem B2103421 : Blo 1246441 2103421 := bbase (se 3 (by rfl) ⟨394391, by rfl⟩ : syracuseStep 2103421 = 788783) (by norm_num)
theorem B4733093 : Blo 1246441 4733093 := bbase (se 4 (by rfl) ⟨443727, by rfl⟩ : syracuseStep 4733093 = 887455) (by norm_num)
theorem B2807981 : Blo 1246441 2807981 := bbase (se 3 (by rfl) ⟨526496, by rfl⟩ : syracuseStep 2807981 = 1052993) (by norm_num)
theorem B2103509 : Blo 1246441 2103509 := bbase (se 7 (by rfl) ⟨24650, by rfl⟩ : syracuseStep 2103509 = 49301) (by norm_num)
theorem B10115285 : Blo 1246441 10115285 := bbase (se 7 (by rfl) ⟨118538, by rfl⟩ : syracuseStep 10115285 = 237077) (by norm_num)
theorem B11991253 : Blo 1246441 11991253 := bbase (se 7 (by rfl) ⟨140522, by rfl⟩ : syracuseStep 11991253 = 281045) (by norm_num)
theorem B2808053 : Blo 1246441 2808053 := bbase (se 5 (by rfl) ⟨131627, by rfl⟩ : syracuseStep 2808053 = 263255) (by norm_num)
theorem B1579277 : Blo 1246441 1579277 := bbase (se 3 (by rfl) ⟨296114, by rfl⟩ : syracuseStep 1579277 = 592229) (by norm_num)
theorem B2808125 : Blo 1246441 2808125 := bbase (se 3 (by rfl) ⟨526523, by rfl⟩ : syracuseStep 2808125 = 1053047) (by norm_num)
theorem B1579333 : Blo 1246441 1579333 := bbase (se 4 (by rfl) ⟨148062, by rfl⟩ : syracuseStep 1579333 = 296125) (by norm_num)
theorem B2103637 : Blo 1246441 2103637 := bbase (se 10 (by rfl) ⟨3081, by rfl⟩ : syracuseStep 2103637 = 6163) (by norm_num)
theorem B3373397 : Blo 1246441 3373397 := bbase (se 10 (by rfl) ⟨4941, by rfl⟩ : syracuseStep 3373397 = 9883) (by norm_num)
theorem B1849717 : Blo 1246441 1849717 := bbase (se 5 (by rfl) ⟨86705, by rfl⟩ : syracuseStep 1849717 = 173411) (by norm_num)
theorem B2398589 : Blo 1246441 2398589 := bbase (se 3 (by rfl) ⟨449735, by rfl⟩ : syracuseStep 2398589 = 899471) (by norm_num)
theorem B4209029 : Blo 1246441 4209029 := bbase (se 4 (by rfl) ⟨394596, by rfl⟩ : syracuseStep 4209029 = 789193) (by norm_num)
theorem B2808197 : Blo 1246441 2808197 := bbase (se 4 (by rfl) ⟨263268, by rfl⟩ : syracuseStep 2808197 = 526537) (by norm_num)
theorem B1579429 : Blo 1246441 1579429 := bbase (se 4 (by rfl) ⟨148071, by rfl⟩ : syracuseStep 1579429 = 296143) (by norm_num)
theorem B2103725 : Blo 1246441 2103725 := bbase (se 3 (by rfl) ⟨394448, by rfl⟩ : syracuseStep 2103725 = 788897) (by norm_num)
theorem B1497533 : Blo 1246441 1497533 := bbase (se 3 (by rfl) ⟨280787, by rfl⟩ : syracuseStep 1497533 = 561575) (by norm_num)
theorem B2808269 : Blo 1246441 2808269 := bbase (se 3 (by rfl) ⟨526550, by rfl⟩ : syracuseStep 2808269 = 1053101) (by norm_num)
theorem B2808341 : Blo 1246441 2808341 := bbase (se 6 (by rfl) ⟨65820, by rfl⟩ : syracuseStep 2808341 = 131641) (by norm_num)
theorem B2103853 : Blo 1246441 2103853 := bbase (se 3 (by rfl) ⟨394472, by rfl⟩ : syracuseStep 2103853 = 788945) (by norm_num)
theorem B1997389 : Blo 1246441 1997389 := bbase (se 3 (by rfl) ⟨374510, by rfl⟩ : syracuseStep 1997389 = 749021) (by norm_num)
theorem B1579601 : Blo 1246441 1579601 := bbase (se 2 (by rfl) ⟨592350, by rfl⟩ : syracuseStep 1579601 = 1184701) (by norm_num)
theorem B2808413 : Blo 1246441 2808413 := bbase (se 3 (by rfl) ⟨526577, by rfl⟩ : syracuseStep 2808413 = 1053155) (by norm_num)
theorem B6314597 : Blo 1246441 6314597 := bbase (se 4 (by rfl) ⟨591993, by rfl⟩ : syracuseStep 6314597 = 1183987) (by norm_num)
theorem B2103941 : Blo 1246441 2103941 := bbase (se 4 (by rfl) ⟨197244, by rfl⟩ : syracuseStep 2103941 = 394489) (by norm_num)
theorem B1579657 : Blo 1246441 1579657 := bbase (se 2 (by rfl) ⟨592371, by rfl⟩ : syracuseStep 1579657 = 1184743) (by norm_num)
theorem B1776277 : Blo 1246441 1776277 := bbase (se 6 (by rfl) ⟨41631, by rfl⟩ : syracuseStep 1776277 = 83263) (by norm_num)
theorem B2808485 : Blo 1246441 2808485 := bbase (se 4 (by rfl) ⟨263295, by rfl⟩ : syracuseStep 2808485 = 526591) (by norm_num)
theorem B5995205 : Blo 1246441 5995205 := bbase (se 4 (by rfl) ⟨562050, by rfl⟩ : syracuseStep 5995205 = 1124101) (by norm_num)
theorem B1579753 : Blo 1246441 1579753 := bbase (se 2 (by rfl) ⟨592407, by rfl⟩ : syracuseStep 1579753 = 1184815) (by norm_num)
theorem B2808557 : Blo 1246441 2808557 := bbase (se 3 (by rfl) ⟨526604, by rfl⟩ : syracuseStep 2808557 = 1053209) (by norm_num)
theorem B2104069 : Blo 1246441 2104069 := bbase (se 4 (by rfl) ⟨197256, by rfl⟩ : syracuseStep 2104069 = 394513) (by norm_num)
theorem B1497865 : Blo 1246441 1497865 := bbase (se 2 (by rfl) ⟨561699, by rfl⟩ : syracuseStep 1497865 = 1123399) (by norm_num)
theorem B4209461 : Blo 1246441 4209461 := bbase (se 5 (by rfl) ⟨197318, by rfl⟩ : syracuseStep 4209461 = 394637) (by norm_num)
theorem B3996469 : Blo 1246441 3996469 := bbase (se 5 (by rfl) ⟨187334, by rfl⟩ : syracuseStep 3996469 = 374669) (by norm_num)
theorem B2808629 : Blo 1246441 2808629 := bbase (se 5 (by rfl) ⟨131654, by rfl⟩ : syracuseStep 2808629 = 263309) (by norm_num)
theorem B2104157 : Blo 1246441 2104157 := bbase (se 3 (by rfl) ⟨394529, by rfl⟩ : syracuseStep 2104157 = 789059) (by norm_num)
theorem B2882429 : Blo 1246441 2882429 := bbase (se 3 (by rfl) ⟨540455, by rfl⟩ : syracuseStep 2882429 = 1080911) (by norm_num)
theorem B2808701 : Blo 1246441 2808701 := bbase (se 3 (by rfl) ⟨526631, by rfl⟩ : syracuseStep 2808701 = 1053263) (by norm_num)
theorem B1579925 : Blo 1246441 1579925 := bbase (se 6 (by rfl) ⟨37029, by rfl⟩ : syracuseStep 1579925 = 74059) (by norm_num)
theorem B2562997 : Blo 1246441 2562997 := bbase (se 5 (by rfl) ⟨120140, by rfl⟩ : syracuseStep 2562997 = 240281) (by norm_num)
theorem B2808773 : Blo 1246441 2808773 := bbase (se 4 (by rfl) ⟨263322, by rfl⟩ : syracuseStep 2808773 = 526645) (by norm_num)
theorem B1579981 : Blo 1246441 1579981 := bbase (se 3 (by rfl) ⟨296246, by rfl⟩ : syracuseStep 1579981 = 592493) (by norm_num)
theorem B9608149 : Blo 1246441 9608149 := bbase (se 7 (by rfl) ⟨112595, by rfl⟩ : syracuseStep 9608149 = 225191) (by norm_num)
theorem B2104285 : Blo 1246441 2104285 := bbase (se 3 (by rfl) ⟨394553, by rfl⟩ : syracuseStep 2104285 = 789107) (by norm_num)
theorem B2808845 : Blo 1246441 2808845 := bbase (se 3 (by rfl) ⟨526658, by rfl⟩ : syracuseStep 2808845 = 1053317) (by norm_num)
theorem B2366509 : Blo 1246441 2366509 := bbase (se 3 (by rfl) ⟨443720, by rfl⟩ : syracuseStep 2366509 = 887441) (by norm_num)
theorem B2104373 : Blo 1246441 2104373 := bbase (se 5 (by rfl) ⟨98642, by rfl⟩ : syracuseStep 2104373 = 197285) (by norm_num)
theorem B22772821 : Blo 1246441 22772821 := bbase (se 8 (by rfl) ⟨133434, by rfl⟩ : syracuseStep 22772821 = 266869) (by norm_num)
theorem B2808917 : Blo 1246441 2808917 := bbase (se 8 (by rfl) ⟨16458, by rfl⟩ : syracuseStep 2808917 = 32917) (by norm_num)
theorem B1997941 : Blo 1246441 1997941 := bbase (se 5 (by rfl) ⟨93653, by rfl⟩ : syracuseStep 1997941 = 187307) (by norm_num)
theorem B12795029 : Blo 1246441 12795029 := bbase (se 6 (by rfl) ⟨299883, by rfl⟩ : syracuseStep 12795029 = 599767) (by norm_num)
theorem B5061781 : Blo 1246441 5061781 := bbase (se 6 (by rfl) ⟨118635, by rfl⟩ : syracuseStep 5061781 = 237271) (by norm_num)
theorem B2808989 : Blo 1246441 2808989 := bbase (se 3 (by rfl) ⟨526685, by rfl⟩ : syracuseStep 2808989 = 1053371) (by norm_num)
theorem B2104501 : Blo 1246441 2104501 := bbase (se 5 (by rfl) ⟨98648, by rfl⟩ : syracuseStep 2104501 = 197297) (by norm_num)
theorem B2366653 : Blo 1246441 2366653 := bbase (se 3 (by rfl) ⟨443747, by rfl⟩ : syracuseStep 2366653 = 887495) (by norm_num)
theorem B4209893 : Blo 1246441 4209893 := bbase (se 4 (by rfl) ⟨394677, by rfl⟩ : syracuseStep 4209893 = 789355) (by norm_num)
theorem B2104589 : Blo 1246441 2104589 := bbase (se 3 (by rfl) ⟨394610, by rfl⟩ : syracuseStep 2104589 = 789221) (by norm_num)
theorem B2702605 : Blo 1246441 2702605 := bbase (se 3 (by rfl) ⟨506738, by rfl⟩ : syracuseStep 2702605 = 1013477) (by norm_num)
theorem B2366813 : Blo 1246441 2366813 := bbase (se 3 (by rfl) ⟨443777, by rfl⟩ : syracuseStep 2366813 = 887555) (by norm_num)
theorem B1998197 : Blo 1246441 1998197 := bbase (se 5 (by rfl) ⟨93665, by rfl⟩ : syracuseStep 1998197 = 187331) (by norm_num)
theorem B2104717 : Blo 1246441 2104717 := bbase (se 3 (by rfl) ⟨394634, by rfl⟩ : syracuseStep 2104717 = 789269) (by norm_num)
theorem B1777069 : Blo 1246441 1777069 := bbase (se 3 (by rfl) ⟨333200, by rfl⟩ : syracuseStep 1777069 = 666401) (by norm_num)
theorem B3554741 : Blo 1246441 3554741 := bbase (se 5 (by rfl) ⟨166628, by rfl⟩ : syracuseStep 3554741 = 333257) (by norm_num)
theorem B2104805 : Blo 1246441 2104805 := bbase (se 4 (by rfl) ⟨197325, by rfl⟩ : syracuseStep 2104805 = 394651) (by norm_num)
theorem B2366957 : Blo 1246441 2366957 := bbase (se 3 (by rfl) ⟨443804, by rfl⟩ : syracuseStep 2366957 = 887609) (by norm_num)
theorem B2883077 : Blo 1246441 2883077 := bbase (se 4 (by rfl) ⟨270288, by rfl⟩ : syracuseStep 2883077 = 540577) (by norm_num)
theorem B2104933 : Blo 1246441 2104933 := bbase (se 4 (by rfl) ⟨197337, by rfl⟩ : syracuseStep 2104933 = 394675) (by norm_num)
theorem B1498753 : Blo 1246441 1498753 := bbase (se 2 (by rfl) ⟨562032, by rfl⟩ : syracuseStep 1498753 = 1124065) (by norm_num)
theorem B4210325 : Blo 1246441 4210325 := bbase (se 6 (by rfl) ⟨98679, by rfl⟩ : syracuseStep 4210325 = 197359) (by norm_num)
theorem B2105021 : Blo 1246441 2105021 := bbase (se 3 (by rfl) ⟨394691, by rfl⟩ : syracuseStep 2105021 = 789383) (by norm_num)
theorem B3202757 : Blo 1246441 3202757 := bbase (se 4 (by rfl) ⟨300258, by rfl⟩ : syracuseStep 3202757 = 600517) (by norm_num)
theorem B10657493 : Blo 1246441 10657493 := bbase (se 7 (by rfl) ⟨124892, by rfl⟩ : syracuseStep 10657493 = 249785) (by norm_num)
theorem B1777405 : Blo 1246441 1777405 := bbase (se 3 (by rfl) ⟨333263, by rfl⟩ : syracuseStep 1777405 = 666527) (by norm_num)
theorem B2367245 : Blo 1246441 2367245 := bbase (se 3 (by rfl) ⟨443858, by rfl⟩ : syracuseStep 2367245 = 887717) (by norm_num)
theorem B2105149 : Blo 1246441 2105149 := bbase (se 3 (by rfl) ⟨394715, by rfl⟩ : syracuseStep 2105149 = 789431) (by norm_num)
theorem B2662229 : Blo 1246441 2662229 := bbase (se 9 (by rfl) ⟨7799, by rfl⟩ : syracuseStep 2662229 = 15599) (by norm_num)
theorem B6315893 : Blo 1246441 6315893 := bbase (se 5 (by rfl) ⟨296057, by rfl⟩ : syracuseStep 6315893 = 592115) (by norm_num)
theorem B2105237 : Blo 1246441 2105237 := bbase (se 6 (by rfl) ⟨49341, by rfl⟩ : syracuseStep 2105237 = 98683) (by norm_num)
theorem B2367397 : Blo 1246441 2367397 := bbase (se 4 (by rfl) ⟨221943, by rfl⟩ : syracuseStep 2367397 = 443887) (by norm_num)
theorem B2998237 : Blo 1246441 2998237 := bbase (se 3 (by rfl) ⟨562169, by rfl⟩ : syracuseStep 2998237 = 1124339) (by norm_num)
theorem B2105345 : Blo 1246441 2105345 := bstep (se 2 (by rfl) ⟨789504, by rfl⟩ : syracuseStep 2105345 = 1579009) B1579009
theorem B15990797 : Blo 1246441 15990797 := bstep (se 3 (by rfl) ⟨2998274, by rfl⟩ : syracuseStep 15990797 = 5996549) B5996549
theorem B2105473 : Blo 1246441 2105473 := bstep (se 2 (by rfl) ⟨789552, by rfl⟩ : syracuseStep 2105473 = 1579105) B1579105
theorem B2105507 : Blo 1246441 2105507 := bstep (se 1 (by rfl) ⟨1579130, by rfl⟩ : syracuseStep 2105507 = 3158261) B3158261
theorem B4210865 : Blo 1246441 4210865 := bstep (se 2 (by rfl) ⟨1579074, by rfl⟩ : syracuseStep 4210865 = 3158149) B3158149
theorem B2162945 : Blo 1246441 2162945 := bstep (se 2 (by rfl) ⟨811104, by rfl⟩ : syracuseStep 2162945 = 1622209) B1622209
theorem B2105635 : Blo 1246441 2105635 := bstep (se 1 (by rfl) ⟨1579226, by rfl⟩ : syracuseStep 2105635 = 3158453) B3158453
theorem B1999171 : Blo 1246441 1999171 := bstep (se 1 (by rfl) ⟨1499378, by rfl⟩ : syracuseStep 1999171 = 2998757) B2998757
theorem B1999235 : Blo 1246441 1999235 := bstep (se 1 (by rfl) ⟨1499426, by rfl⟩ : syracuseStep 1999235 = 2998853) B2998853
theorem B2105777 : Blo 1246441 2105777 := bstep (se 2 (by rfl) ⟨789666, by rfl⟩ : syracuseStep 2105777 = 1579333) B1579333
theorem B4268483 : Blo 1246441 4268483 := bstep (se 1 (by rfl) ⟨3201362, by rfl⟩ : syracuseStep 4268483 = 6402725) B6402725
theorem B2466289 : Blo 1246441 2466289 := bstep (se 2 (by rfl) ⟨924858, by rfl⟩ : syracuseStep 2466289 = 1849717) B1849717
theorem B15172109 : Blo 1246441 15172109 := bstep (se 3 (by rfl) ⟨2844770, by rfl⟩ : syracuseStep 15172109 = 5689541) B5689541
theorem B7103011 : Blo 1246441 7103011 := bstep (se 1 (by rfl) ⟨5327258, by rfl⟩ : syracuseStep 7103011 = 10654517) B10654517
theorem B4735523 : Blo 1246441 4735523 := bstep (se 1 (by rfl) ⟨3551642, by rfl⟩ : syracuseStep 4735523 = 7103285) B7103285
theorem B2105905 : Blo 1246441 2105905 := bstep (se 2 (by rfl) ⟨789714, by rfl⟩ : syracuseStep 2105905 = 1579429) B1579429
theorem B2105939 : Blo 1246441 2105939 := bstep (se 1 (by rfl) ⟨1579454, by rfl⟩ : syracuseStep 2105939 = 3158909) B3158909
theorem B2400899 : Blo 1246441 2400899 := bstep (se 1 (by rfl) ⟨1800674, by rfl⟩ : syracuseStep 2400899 = 3601349) B3601349
theorem B7996067 : Blo 1246441 7996067 := bstep (se 1 (by rfl) ⟨5997050, by rfl⟩ : syracuseStep 7996067 = 11994101) B11994101
theorem B4211405 : Blo 1246441 4211405 := bstep (se 3 (by rfl) ⟨789638, by rfl⟩ : syracuseStep 4211405 = 1579277) B1579277
theorem B2106067 : Blo 1246441 2106067 := bstep (se 1 (by rfl) ⟨1579550, by rfl⟩ : syracuseStep 2106067 = 3159101) B3159101
theorem B4211459 : Blo 1246441 4211459 := bstep (se 1 (by rfl) ⟨3158594, by rfl⟩ : syracuseStep 4211459 = 6317189) B6317189
theorem B3793745 : Blo 1246441 3793745 := bstep (se 2 (by rfl) ⟨1422654, by rfl⟩ : syracuseStep 3793745 = 2845309) B2845309
theorem B2106209 : Blo 1246441 2106209 := bstep (se 2 (by rfl) ⟨789828, by rfl⟩ : syracuseStep 2106209 = 1579657) B1579657
theorem B2368369 : Blo 1246441 2368369 := bstep (se 2 (by rfl) ⟨888138, by rfl⟩ : syracuseStep 2368369 = 1776277) B1776277
theorem B2737091 : Blo 1246441 2737091 := bstep (se 1 (by rfl) ⟨2052818, by rfl⟩ : syracuseStep 2737091 = 4105637) B4105637
theorem B5055437 : Blo 1246441 5055437 := bstep (se 3 (by rfl) ⟨947894, by rfl⟩ : syracuseStep 5055437 = 1895789) B1895789
theorem B2106337 : Blo 1246441 2106337 := bstep (se 2 (by rfl) ⟨789876, by rfl⟩ : syracuseStep 2106337 = 1579753) B1579753
theorem B6317027 : Blo 1246441 6317027 := bstep (se 1 (by rfl) ⟨4737770, by rfl⟩ : syracuseStep 6317027 = 9475541) B9475541
theorem B25617379 : Blo 1246441 25617379 := bstep (se 1 (by rfl) ⟨19213034, by rfl⟩ : syracuseStep 25617379 = 38426069) B38426069
theorem B2106371 : Blo 1246441 2106371 := bstep (se 1 (by rfl) ⟨1579778, by rfl⟩ : syracuseStep 2106371 = 3159557) B3159557
theorem B4211729 : Blo 1246441 4211729 := bstep (se 2 (by rfl) ⟨1579398, by rfl⟩ : syracuseStep 4211729 = 3158797) B3158797
theorem B2663459 : Blo 1246441 2663459 := bstep (se 1 (by rfl) ⟨1997594, by rfl⟩ : syracuseStep 2663459 = 3995189) B3995189
theorem B7103537 : Blo 1246441 7103537 := bstep (se 2 (by rfl) ⟨2663826, by rfl⟩ : syracuseStep 7103537 = 5327653) B5327653
theorem B276661361 : Blo 1246441 276661361 := bstep (se 2 (by rfl) ⟨103748010, by rfl⟩ : syracuseStep 276661361 = 207496021) B207496021
theorem B2106499 : Blo 1246441 2106499 := bstep (se 1 (by rfl) ⟨1579874, by rfl⟩ : syracuseStep 2106499 = 3159749) B3159749
theorem B30327949 : Blo 1246441 30327949 := bstep (se 3 (by rfl) ⟨5686490, by rfl⟩ : syracuseStep 30327949 = 11372981) B11372981
theorem B6931619 : Blo 1246441 6931619 := bstep (se 1 (by rfl) ⟨5198714, by rfl⟩ : syracuseStep 6931619 = 10397429) B10397429
theorem B4736177 : Blo 1246441 4736177 := bstep (se 2 (by rfl) ⟨1776066, by rfl⟩ : syracuseStep 4736177 = 3552133) B3552133
theorem B8209649 : Blo 1246441 8209649 := bstep (se 2 (by rfl) ⟨3078618, by rfl⟩ : syracuseStep 8209649 = 6157237) B6157237
theorem B3417329 : Blo 1246441 3417329 := bstep (se 2 (by rfl) ⟨1281498, by rfl⟩ : syracuseStep 3417329 = 2562997) B2562997
theorem B1246451 : Blo 1246441 1246451 := bstep (se 1 (by rfl) ⟨934838, by rfl⟩ : syracuseStep 1246451 = 1869677) B1869677
theorem B3794161 : Blo 1246441 3794161 := bstep (se 2 (by rfl) ⟨1422810, by rfl⟩ : syracuseStep 3794161 = 2845621) B2845621
theorem B1246467 : Blo 1246441 1246467 := bstep (se 1 (by rfl) ⟨934850, by rfl⟩ : syracuseStep 1246467 = 1869701) B1869701
theorem B2106641 : Blo 1246441 2106641 := bstep (se 2 (by rfl) ⟨789990, by rfl⟩ : syracuseStep 2106641 = 1579981) B1579981
theorem B1246483 : Blo 1246441 1246483 := bstep (se 1 (by rfl) ⟨934862, by rfl⟩ : syracuseStep 1246483 = 1869725) B1869725
theorem B1246499 : Blo 1246441 1246499 := bstep (se 1 (by rfl) ⟨934874, by rfl⟩ : syracuseStep 1246499 = 1869749) B1869749
theorem B1246515 : Blo 1246441 1246515 := bstep (se 1 (by rfl) ⟨934886, by rfl⟩ : syracuseStep 1246515 = 1869773) B1869773
theorem B1246531 : Blo 1246441 1246531 := bstep (se 1 (by rfl) ⟨934898, by rfl⟩ : syracuseStep 1246531 = 1869797) B1869797
theorem B1246547 : Blo 1246441 1246547 := bstep (se 1 (by rfl) ⟨934910, by rfl⟩ : syracuseStep 1246547 = 1869821) B1869821
theorem B1246563 : Blo 1246441 1246563 := bstep (se 1 (by rfl) ⟨934922, by rfl⟩ : syracuseStep 1246563 = 1869845) B1869845
theorem B9233777 : Blo 1246441 9233777 := bstep (se 2 (by rfl) ⟨3462666, by rfl⟩ : syracuseStep 9233777 = 6925333) B6925333
theorem B1246579 : Blo 1246441 1246579 := bstep (se 1 (by rfl) ⟨934934, by rfl⟩ : syracuseStep 1246579 = 1869869) B1869869
theorem B2024819 : Blo 1246441 2024819 := bstep (se 1 (by rfl) ⟨1518614, by rfl⟩ : syracuseStep 2024819 = 3037229) B3037229
theorem B1246595 : Blo 1246441 1246595 := bstep (se 1 (by rfl) ⟨934946, by rfl⟩ : syracuseStep 1246595 = 1869893) B1869893
theorem B3155345 : Blo 1246441 3155345 := bstep (se 2 (by rfl) ⟨1183254, by rfl⟩ : syracuseStep 3155345 = 2366509) B2366509
theorem B1246611 : Blo 1246441 1246611 := bstep (se 1 (by rfl) ⟨934958, by rfl⟩ : syracuseStep 1246611 = 1869917) B1869917
theorem B1246627 : Blo 1246441 1246627 := bstep (se 1 (by rfl) ⟨934970, by rfl⟩ : syracuseStep 1246627 = 1869941) B1869941
theorem B1246643 : Blo 1246441 1246643 := bstep (se 1 (by rfl) ⟨934982, by rfl⟩ : syracuseStep 1246643 = 1869965) B1869965
theorem B3155395 : Blo 1246441 3155395 := bstep (se 1 (by rfl) ⟨2366546, by rfl⟩ : syracuseStep 3155395 = 4733093) B4733093
theorem B1246659 : Blo 1246441 1246659 := bstep (se 1 (by rfl) ⟨934994, by rfl⟩ : syracuseStep 1246659 = 1869989) B1869989
theorem B5768653 : Blo 1246441 5768653 := bstep (se 3 (by rfl) ⟨1081622, by rfl⟩ : syracuseStep 5768653 = 2163245) B2163245
theorem B1246675 : Blo 1246441 1246675 := bstep (se 1 (by rfl) ⟨935006, by rfl⟩ : syracuseStep 1246675 = 1870013) B1870013
theorem B1402339 : Blo 1246441 1402339 := bstep (se 1 (by rfl) ⟨1051754, by rfl⟩ : syracuseStep 1402339 = 2103509) B2103509
theorem B1246691 : Blo 1246441 1246691 := bstep (se 1 (by rfl) ⟨935018, by rfl⟩ : syracuseStep 1246691 = 1870037) B1870037
theorem B2663921 : Blo 1246441 2663921 := bstep (se 2 (by rfl) ⟨998970, by rfl⟩ : syracuseStep 2663921 = 1997941) B1997941
theorem B1246707 : Blo 1246441 1246707 := bstep (se 1 (by rfl) ⟨935030, by rfl⟩ : syracuseStep 1246707 = 1870061) B1870061
theorem B1246723 : Blo 1246441 1246723 := bstep (se 1 (by rfl) ⟨935042, by rfl⟩ : syracuseStep 1246723 = 1870085) B1870085
theorem B1246739 : Blo 1246441 1246739 := bstep (se 1 (by rfl) ⟨935054, by rfl⟩ : syracuseStep 1246739 = 1870109) B1870109
theorem B1246755 : Blo 1246441 1246755 := bstep (se 1 (by rfl) ⟨935066, by rfl⟩ : syracuseStep 1246755 = 1870133) B1870133
theorem B4212269 : Blo 1246441 4212269 := bstep (se 3 (by rfl) ⟨789800, by rfl⟩ : syracuseStep 4212269 = 1579601) B1579601
theorem B1246771 : Blo 1246441 1246771 := bstep (se 1 (by rfl) ⟨935078, by rfl⟩ : syracuseStep 1246771 = 1870157) B1870157
theorem B1246787 : Blo 1246441 1246787 := bstep (se 1 (by rfl) ⟨935090, by rfl⟩ : syracuseStep 1246787 = 1870181) B1870181
theorem B3155537 : Blo 1246441 3155537 := bstep (se 2 (by rfl) ⟨1183326, by rfl⟩ : syracuseStep 3155537 = 2366653) B2366653
theorem B1599059 : Blo 1246441 1599059 := bstep (se 1 (by rfl) ⟨1199294, by rfl⟩ : syracuseStep 1599059 = 2398589) B2398589
theorem B1246803 : Blo 1246441 1246803 := bstep (se 1 (by rfl) ⟨935102, by rfl⟩ : syracuseStep 1246803 = 1870205) B1870205
theorem B1246819 : Blo 1246441 1246819 := bstep (se 1 (by rfl) ⟨935114, by rfl⟩ : syracuseStep 1246819 = 1870229) B1870229
theorem B4212323 : Blo 1246441 4212323 := bstep (se 1 (by rfl) ⟨3159242, by rfl⟩ : syracuseStep 4212323 = 6318485) B6318485
theorem B11388529 : Blo 1246441 11388529 := bstep (se 2 (by rfl) ⟨4270698, by rfl⟩ : syracuseStep 11388529 = 8541397) B8541397
theorem B1402483 : Blo 1246441 1402483 := bstep (se 1 (by rfl) ⟨1051862, by rfl⟩ : syracuseStep 1402483 = 2103725) B2103725
theorem B1246835 : Blo 1246441 1246835 := bstep (se 1 (by rfl) ⟨935126, by rfl⟩ : syracuseStep 1246835 = 1870253) B1870253
theorem B1246851 : Blo 1246441 1246851 := bstep (se 1 (by rfl) ⟨935138, by rfl⟩ : syracuseStep 1246851 = 1870277) B1870277
theorem B1246867 : Blo 1246441 1246867 := bstep (se 1 (by rfl) ⟨935150, by rfl⟩ : syracuseStep 1246867 = 1870301) B1870301
theorem B1246883 : Blo 1246441 1246883 := bstep (se 1 (by rfl) ⟨935162, by rfl⟩ : syracuseStep 1246883 = 1870325) B1870325
theorem B1246899 : Blo 1246441 1246899 := bstep (se 1 (by rfl) ⟨935174, by rfl⟩ : syracuseStep 1246899 = 1870349) B1870349
theorem B1246915 : Blo 1246441 1246915 := bstep (se 1 (by rfl) ⟨935186, by rfl⟩ : syracuseStep 1246915 = 1870373) B1870373
theorem B1246931 : Blo 1246441 1246931 := bstep (se 1 (by rfl) ⟨935198, by rfl⟩ : syracuseStep 1246931 = 1870397) B1870397
theorem B1246947 : Blo 1246441 1246947 := bstep (se 1 (by rfl) ⟨935210, by rfl⟩ : syracuseStep 1246947 = 1870421) B1870421
theorem B3999469 : Blo 1246441 3999469 := bstep (se 3 (by rfl) ⟨749900, by rfl⟩ : syracuseStep 3999469 = 1499801) B1499801
theorem B1246963 : Blo 1246441 1246963 := bstep (se 1 (by rfl) ⟨935222, by rfl⟩ : syracuseStep 1246963 = 1870445) B1870445
theorem B1402627 : Blo 1246441 1402627 := bstep (se 1 (by rfl) ⟨1051970, by rfl⟩ : syracuseStep 1402627 = 2103941) B2103941
theorem B1246979 : Blo 1246441 1246979 := bstep (se 1 (by rfl) ⟨935234, by rfl⟩ : syracuseStep 1246979 = 1870469) B1870469
theorem B6317837 : Blo 1246441 6317837 := bstep (se 3 (by rfl) ⟨1184594, by rfl⟩ : syracuseStep 6317837 = 2369189) B2369189
theorem B1246995 : Blo 1246441 1246995 := bstep (se 1 (by rfl) ⟨935246, by rfl⟩ : syracuseStep 1246995 = 1870493) B1870493
theorem B1247011 : Blo 1246441 1247011 := bstep (se 1 (by rfl) ⟨935258, by rfl⟩ : syracuseStep 1247011 = 1870517) B1870517
theorem B1247027 : Blo 1246441 1247027 := bstep (se 1 (by rfl) ⟨935270, by rfl⟩ : syracuseStep 1247027 = 1870541) B1870541
theorem B1247043 : Blo 1246441 1247043 := bstep (se 1 (by rfl) ⟨935282, by rfl⟩ : syracuseStep 1247043 = 1870565) B1870565
theorem B1247059 : Blo 1246441 1247059 := bstep (se 1 (by rfl) ⟨935294, by rfl⟩ : syracuseStep 1247059 = 1870589) B1870589
theorem B1869665 : Blo 1246441 1869665 := bstep (se 2 (by rfl) ⟨701124, by rfl⟩ : syracuseStep 1869665 = 1402249) B1402249
theorem B1247075 : Blo 1246441 1247075 := bstep (se 1 (by rfl) ⟨935306, by rfl⟩ : syracuseStep 1247075 = 1870613) B1870613
theorem B4212593 : Blo 1246441 4212593 := bstep (se 2 (by rfl) ⟨1579722, by rfl⟩ : syracuseStep 4212593 = 3159445) B3159445
theorem B1869683 : Blo 1246441 1869683 := bstep (se 1 (by rfl) ⟨1402262, by rfl⟩ : syracuseStep 1869683 = 2804525) B2804525
theorem B1247091 : Blo 1246441 1247091 := bstep (se 1 (by rfl) ⟨935318, by rfl⟩ : syracuseStep 1247091 = 1870637) B1870637
theorem B1247107 : Blo 1246441 1247107 := bstep (se 1 (by rfl) ⟨935330, by rfl⟩ : syracuseStep 1247107 = 1870661) B1870661
theorem B1869713 : Blo 1246441 1869713 := bstep (se 2 (by rfl) ⟨701142, by rfl⟩ : syracuseStep 1869713 = 1402285) B1402285
theorem B2246545 : Blo 1246441 2246545 := bstep (se 2 (by rfl) ⟨842454, by rfl⟩ : syracuseStep 2246545 = 1684909) B1684909
theorem B1402771 : Blo 1246441 1402771 := bstep (se 1 (by rfl) ⟨1052078, by rfl⟩ : syracuseStep 1402771 = 2104157) B2104157
theorem B1247123 : Blo 1246441 1247123 := bstep (se 1 (by rfl) ⟨935342, by rfl⟩ : syracuseStep 1247123 = 1870685) B1870685
theorem B2369425 : Blo 1246441 2369425 := bstep (se 2 (by rfl) ⟨888534, by rfl⟩ : syracuseStep 2369425 = 1777069) B1777069
theorem B1869731 : Blo 1246441 1869731 := bstep (se 1 (by rfl) ⟨1402298, by rfl⟩ : syracuseStep 1869731 = 2804597) B2804597
theorem B1247139 : Blo 1246441 1247139 := bstep (se 1 (by rfl) ⟨935354, by rfl⟩ : syracuseStep 1247139 = 1870709) B1870709
theorem B1247155 : Blo 1246441 1247155 := bstep (se 1 (by rfl) ⟨935366, by rfl⟩ : syracuseStep 1247155 = 1870733) B1870733
theorem B1869761 : Blo 1246441 1869761 := bstep (se 2 (by rfl) ⟨701160, by rfl⟩ : syracuseStep 1869761 = 1402321) B1402321
theorem B1247171 : Blo 1246441 1247171 := bstep (se 1 (by rfl) ⟨935378, by rfl⟩ : syracuseStep 1247171 = 1870757) B1870757
theorem B1869779 : Blo 1246441 1869779 := bstep (se 1 (by rfl) ⟨1402334, by rfl⟩ : syracuseStep 1869779 = 2804669) B2804669
theorem B1247187 : Blo 1246441 1247187 := bstep (se 1 (by rfl) ⟨935390, by rfl⟩ : syracuseStep 1247187 = 1870781) B1870781
theorem B1247203 : Blo 1246441 1247203 := bstep (se 1 (by rfl) ⟨935402, by rfl⟩ : syracuseStep 1247203 = 1870805) B1870805
theorem B1869809 : Blo 1246441 1869809 := bstep (se 2 (by rfl) ⟨701178, by rfl⟩ : syracuseStep 1869809 = 1402357) B1402357
theorem B1247219 : Blo 1246441 1247219 := bstep (se 1 (by rfl) ⟨935414, by rfl⟩ : syracuseStep 1247219 = 1870829) B1870829
theorem B1869827 : Blo 1246441 1869827 := bstep (se 1 (by rfl) ⟨1402370, by rfl⟩ : syracuseStep 1869827 = 2804741) B2804741
theorem B1247235 : Blo 1246441 1247235 := bstep (se 1 (by rfl) ⟨935426, by rfl⟩ : syracuseStep 1247235 = 1870853) B1870853
theorem B1247251 : Blo 1246441 1247251 := bstep (se 1 (by rfl) ⟨935438, by rfl⟩ : syracuseStep 1247251 = 1870877) B1870877
theorem B1869857 : Blo 1246441 1869857 := bstep (se 2 (by rfl) ⟨701196, by rfl⟩ : syracuseStep 1869857 = 1402393) B1402393
theorem B1402915 : Blo 1246441 1402915 := bstep (se 1 (by rfl) ⟨1052186, by rfl⟩ : syracuseStep 1402915 = 2104373) B2104373
theorem B1247267 : Blo 1246441 1247267 := bstep (se 1 (by rfl) ⟨935450, by rfl⟩ : syracuseStep 1247267 = 1870901) B1870901
theorem B1869875 : Blo 1246441 1869875 := bstep (se 1 (by rfl) ⟨1402406, by rfl⟩ : syracuseStep 1869875 = 2804813) B2804813
theorem B1247283 : Blo 1246441 1247283 := bstep (se 1 (by rfl) ⟨935462, by rfl⟩ : syracuseStep 1247283 = 1870925) B1870925
theorem B1247299 : Blo 1246441 1247299 := bstep (se 1 (by rfl) ⟨935474, by rfl⟩ : syracuseStep 1247299 = 1870949) B1870949
theorem B1869905 : Blo 1246441 1869905 := bstep (se 2 (by rfl) ⟨701214, by rfl⟩ : syracuseStep 1869905 = 1402429) B1402429
theorem B1247315 : Blo 1246441 1247315 := bstep (se 1 (by rfl) ⟨935486, by rfl⟩ : syracuseStep 1247315 = 1870973) B1870973
theorem B1869923 : Blo 1246441 1869923 := bstep (se 1 (by rfl) ⟨1402442, by rfl⟩ : syracuseStep 1869923 = 2804885) B2804885
theorem B8530019 : Blo 1246441 8530019 := bstep (se 1 (by rfl) ⟨6397514, by rfl⟩ : syracuseStep 8530019 = 12795029) B12795029
theorem B1247331 : Blo 1246441 1247331 := bstep (se 1 (by rfl) ⟨935498, by rfl⟩ : syracuseStep 1247331 = 1870997) B1870997
theorem B1247347 : Blo 1246441 1247347 := bstep (se 1 (by rfl) ⟨935510, by rfl⟩ : syracuseStep 1247347 = 1871021) B1871021
theorem B1869953 : Blo 1246441 1869953 := bstep (se 2 (by rfl) ⟨701232, by rfl⟩ : syracuseStep 1869953 = 1402465) B1402465
theorem B1247363 : Blo 1246441 1247363 := bstep (se 1 (by rfl) ⟨935522, by rfl⟩ : syracuseStep 1247363 = 1871045) B1871045
theorem B1869971 : Blo 1246441 1869971 := bstep (se 1 (by rfl) ⟨1402478, by rfl⟩ : syracuseStep 1869971 = 2804957) B2804957
theorem B1247379 : Blo 1246441 1247379 := bstep (se 1 (by rfl) ⟨935534, by rfl⟩ : syracuseStep 1247379 = 1871069) B1871069
theorem B1247395 : Blo 1246441 1247395 := bstep (se 1 (by rfl) ⟨935546, by rfl⟩ : syracuseStep 1247395 = 1871093) B1871093
theorem B1870001 : Blo 1246441 1870001 := bstep (se 2 (by rfl) ⟨701250, by rfl⟩ : syracuseStep 1870001 = 1402501) B1402501
theorem B1403059 : Blo 1246441 1403059 := bstep (se 1 (by rfl) ⟨1052294, by rfl⟩ : syracuseStep 1403059 = 2104589) B2104589
theorem B1247411 : Blo 1246441 1247411 := bstep (se 1 (by rfl) ⟨935558, by rfl⟩ : syracuseStep 1247411 = 1871117) B1871117
theorem B1870019 : Blo 1246441 1870019 := bstep (se 1 (by rfl) ⟨1402514, by rfl⟩ : syracuseStep 1870019 = 2805029) B2805029
theorem B1247427 : Blo 1246441 1247427 := bstep (se 1 (by rfl) ⟨935570, by rfl⟩ : syracuseStep 1247427 = 1871141) B1871141
theorem B1247443 : Blo 1246441 1247443 := bstep (se 1 (by rfl) ⟨935582, by rfl⟩ : syracuseStep 1247443 = 1871165) B1871165
theorem B1870049 : Blo 1246441 1870049 := bstep (se 2 (by rfl) ⟨701268, by rfl⟩ : syracuseStep 1870049 = 1402537) B1402537
theorem B1247459 : Blo 1246441 1247459 := bstep (se 1 (by rfl) ⟨935594, by rfl⟩ : syracuseStep 1247459 = 1871189) B1871189
theorem B1870067 : Blo 1246441 1870067 := bstep (se 1 (by rfl) ⟨1402550, by rfl⟩ : syracuseStep 1870067 = 2805101) B2805101
theorem B1247475 : Blo 1246441 1247475 := bstep (se 1 (by rfl) ⟨935606, by rfl⟩ : syracuseStep 1247475 = 1871213) B1871213
theorem B1247491 : Blo 1246441 1247491 := bstep (se 1 (by rfl) ⟨935618, by rfl⟩ : syracuseStep 1247491 = 1871237) B1871237
theorem B1870097 : Blo 1246441 1870097 := bstep (se 2 (by rfl) ⟨701286, by rfl⟩ : syracuseStep 1870097 = 1402573) B1402573
theorem B1247507 : Blo 1246441 1247507 := bstep (se 1 (by rfl) ⟨935630, by rfl⟩ : syracuseStep 1247507 = 1871261) B1871261
theorem B1870115 : Blo 1246441 1870115 := bstep (se 1 (by rfl) ⟨1402586, by rfl⟩ : syracuseStep 1870115 = 2805173) B2805173
theorem B1247523 : Blo 1246441 1247523 := bstep (se 1 (by rfl) ⟨935642, by rfl⟩ : syracuseStep 1247523 = 1871285) B1871285
theorem B2369827 : Blo 1246441 2369827 := bstep (se 1 (by rfl) ⟨1777370, by rfl⟩ : syracuseStep 2369827 = 3554741) B3554741
theorem B1247539 : Blo 1246441 1247539 := bstep (se 1 (by rfl) ⟨935654, by rfl⟩ : syracuseStep 1247539 = 1871309) B1871309
theorem B1870145 : Blo 1246441 1870145 := bstep (se 2 (by rfl) ⟨701304, by rfl⟩ : syracuseStep 1870145 = 1402609) B1402609
theorem B1403203 : Blo 1246441 1403203 := bstep (se 1 (by rfl) ⟨1052402, by rfl⟩ : syracuseStep 1403203 = 2104805) B2104805
theorem B1247555 : Blo 1246441 1247555 := bstep (se 1 (by rfl) ⟨935666, by rfl⟩ : syracuseStep 1247555 = 1871333) B1871333
theorem B3795277 : Blo 1246441 3795277 := bstep (se 3 (by rfl) ⟨711614, by rfl⟩ : syracuseStep 3795277 = 1423229) B1423229
theorem B2369873 : Blo 1246441 2369873 := bstep (se 2 (by rfl) ⟨888702, by rfl⟩ : syracuseStep 2369873 = 1777405) B1777405
theorem B1870163 : Blo 1246441 1870163 := bstep (se 1 (by rfl) ⟨1402622, by rfl⟩ : syracuseStep 1870163 = 2805245) B2805245
theorem B1247571 : Blo 1246441 1247571 := bstep (se 1 (by rfl) ⟨935678, by rfl⟩ : syracuseStep 1247571 = 1871357) B1871357
theorem B1247587 : Blo 1246441 1247587 := bstep (se 1 (by rfl) ⟨935690, by rfl⟩ : syracuseStep 1247587 = 1871381) B1871381
theorem B4049261 : Blo 1246441 4049261 := bstep (se 3 (by rfl) ⟨759236, by rfl⟩ : syracuseStep 4049261 = 1518473) B1518473
theorem B1870193 : Blo 1246441 1870193 := bstep (se 2 (by rfl) ⟨701322, by rfl⟩ : syracuseStep 1870193 = 1402645) B1402645
theorem B1247603 : Blo 1246441 1247603 := bstep (se 1 (by rfl) ⟨935702, by rfl⟩ : syracuseStep 1247603 = 1871405) B1871405
theorem B1870211 : Blo 1246441 1870211 := bstep (se 1 (by rfl) ⟨1402658, by rfl⟩ : syracuseStep 1870211 = 2805317) B2805317
theorem B1247619 : Blo 1246441 1247619 := bstep (se 1 (by rfl) ⟨935714, by rfl⟩ : syracuseStep 1247619 = 1871429) B1871429
theorem B4213133 : Blo 1246441 4213133 := bstep (se 3 (by rfl) ⟨789962, by rfl⟩ : syracuseStep 4213133 = 1579925) B1579925
theorem B1247635 : Blo 1246441 1247635 := bstep (se 1 (by rfl) ⟨935726, by rfl⟩ : syracuseStep 1247635 = 1871453) B1871453
theorem B1870241 : Blo 1246441 1870241 := bstep (se 2 (by rfl) ⟨701340, by rfl⟩ : syracuseStep 1870241 = 1402681) B1402681
theorem B1247651 : Blo 1246441 1247651 := bstep (se 1 (by rfl) ⟨935738, by rfl⟩ : syracuseStep 1247651 = 1871477) B1871477
theorem B1870259 : Blo 1246441 1870259 := bstep (se 1 (by rfl) ⟨1402694, by rfl⟩ : syracuseStep 1870259 = 2805389) B2805389
theorem B1247667 : Blo 1246441 1247667 := bstep (se 1 (by rfl) ⟨935750, by rfl⟩ : syracuseStep 1247667 = 1871501) B1871501
theorem B1247683 : Blo 1246441 1247683 := bstep (se 1 (by rfl) ⟨935762, by rfl⟩ : syracuseStep 1247683 = 1871525) B1871525
theorem B4213187 : Blo 1246441 4213187 := bstep (se 1 (by rfl) ⟨3159890, by rfl⟩ : syracuseStep 4213187 = 6319781) B6319781
theorem B51243461 : Blo 1246441 51243461 := bstep (se 4 (by rfl) ⟨4804074, by rfl⟩ : syracuseStep 51243461 = 9608149) B9608149
theorem B5990861 : Blo 1246441 5990861 := bstep (se 3 (by rfl) ⟨1123286, by rfl⟩ : syracuseStep 5990861 = 2246573) B2246573
theorem B1870289 : Blo 1246441 1870289 := bstep (se 2 (by rfl) ⟨701358, by rfl⟩ : syracuseStep 1870289 = 1402717) B1402717
theorem B1403347 : Blo 1246441 1403347 := bstep (se 1 (by rfl) ⟨1052510, by rfl⟩ : syracuseStep 1403347 = 2105021) B2105021
theorem B1247699 : Blo 1246441 1247699 := bstep (se 1 (by rfl) ⟨935774, by rfl⟩ : syracuseStep 1247699 = 1871549) B1871549
theorem B1870307 : Blo 1246441 1870307 := bstep (se 1 (by rfl) ⟨1402730, by rfl⟩ : syracuseStep 1870307 = 2805461) B2805461
theorem B7104995 : Blo 1246441 7104995 := bstep (se 1 (by rfl) ⟨5328746, by rfl⟩ : syracuseStep 7104995 = 10657493) B10657493
theorem B1247715 : Blo 1246441 1247715 := bstep (se 1 (by rfl) ⟨935786, by rfl⟩ : syracuseStep 1247715 = 1871573) B1871573
theorem B6310385 : Blo 1246441 6310385 := bstep (se 2 (by rfl) ⟨2366394, by rfl⟩ : syracuseStep 6310385 = 4732789) B4732789
theorem B1247731 : Blo 1246441 1247731 := bstep (se 1 (by rfl) ⟨935798, by rfl⟩ : syracuseStep 1247731 = 1871597) B1871597
theorem B1870337 : Blo 1246441 1870337 := bstep (se 2 (by rfl) ⟨701376, by rfl⟩ : syracuseStep 1870337 = 1402753) B1402753
theorem B1247747 : Blo 1246441 1247747 := bstep (se 1 (by rfl) ⟨935810, by rfl⟩ : syracuseStep 1247747 = 1871621) B1871621
theorem B1870355 : Blo 1246441 1870355 := bstep (se 1 (by rfl) ⟨1402766, by rfl⟩ : syracuseStep 1870355 = 2805533) B2805533
theorem B1247763 : Blo 1246441 1247763 := bstep (se 1 (by rfl) ⟨935822, by rfl⟩ : syracuseStep 1247763 = 1871645) B1871645
theorem B1247779 : Blo 1246441 1247779 := bstep (se 1 (by rfl) ⟨935834, by rfl⟩ : syracuseStep 1247779 = 1871669) B1871669
theorem B1870385 : Blo 1246441 1870385 := bstep (se 2 (by rfl) ⟨701394, by rfl⟩ : syracuseStep 1870385 = 1402789) B1402789
theorem B3156529 : Blo 1246441 3156529 := bstep (se 2 (by rfl) ⟨1183698, by rfl⟩ : syracuseStep 3156529 = 2367397) B2367397
theorem B1247795 : Blo 1246441 1247795 := bstep (se 1 (by rfl) ⟨935846, by rfl⟩ : syracuseStep 1247795 = 1871693) B1871693
theorem B1870403 : Blo 1246441 1870403 := bstep (se 1 (by rfl) ⟨1402802, by rfl⟩ : syracuseStep 1870403 = 2805605) B2805605
theorem B1247811 : Blo 1246441 1247811 := bstep (se 1 (by rfl) ⟨935858, by rfl⟩ : syracuseStep 1247811 = 1871717) B1871717
theorem B1247827 : Blo 1246441 1247827 := bstep (se 1 (by rfl) ⟨935870, by rfl⟩ : syracuseStep 1247827 = 1871741) B1871741
theorem B1870433 : Blo 1246441 1870433 := bstep (se 2 (by rfl) ⟨701412, by rfl⟩ : syracuseStep 1870433 = 1402825) B1402825
theorem B1403491 : Blo 1246441 1403491 := bstep (se 1 (by rfl) ⟨1052618, by rfl⟩ : syracuseStep 1403491 = 2105237) B2105237
theorem B4737635 : Blo 1246441 4737635 := bstep (se 1 (by rfl) ⟨3553226, by rfl⟩ : syracuseStep 4737635 = 7106453) B7106453
theorem B1247843 : Blo 1246441 1247843 := bstep (se 1 (by rfl) ⟨935882, by rfl⟩ : syracuseStep 1247843 = 1871765) B1871765
theorem B9472625 : Blo 1246441 9472625 := bstep (se 2 (by rfl) ⟨3552234, by rfl⟩ : syracuseStep 9472625 = 7104469) B7104469
theorem B4737649 : Blo 1246441 4737649 := bstep (se 2 (by rfl) ⟨1776618, by rfl⟩ : syracuseStep 4737649 = 3553237) B3553237
theorem B1870451 : Blo 1246441 1870451 := bstep (se 1 (by rfl) ⟨1402838, by rfl⟩ : syracuseStep 1870451 = 2805677) B2805677
theorem B1247859 : Blo 1246441 1247859 := bstep (se 1 (by rfl) ⟨935894, by rfl⟩ : syracuseStep 1247859 = 1871789) B1871789
theorem B7998065 : Blo 1246441 7998065 := bstep (se 2 (by rfl) ⟨2999274, by rfl⟩ : syracuseStep 7998065 = 5998549) B5998549
theorem B1247875 : Blo 1246441 1247875 := bstep (se 1 (by rfl) ⟨935906, by rfl⟩ : syracuseStep 1247875 = 1871813) B1871813
theorem B1870481 : Blo 1246441 1870481 := bstep (se 2 (by rfl) ⟨701430, by rfl⟩ : syracuseStep 1870481 = 1402861) B1402861
theorem B1247891 : Blo 1246441 1247891 := bstep (se 1 (by rfl) ⟨935918, by rfl⟩ : syracuseStep 1247891 = 1871837) B1871837
theorem B1870499 : Blo 1246441 1870499 := bstep (se 1 (by rfl) ⟨1402874, by rfl⟩ : syracuseStep 1870499 = 2805749) B2805749
theorem B1247907 : Blo 1246441 1247907 := bstep (se 1 (by rfl) ⟨935930, by rfl⟩ : syracuseStep 1247907 = 1871861) B1871861
theorem B1247923 : Blo 1246441 1247923 := bstep (se 1 (by rfl) ⟨935942, by rfl⟩ : syracuseStep 1247923 = 1871885) B1871885
theorem B1870529 : Blo 1246441 1870529 := bstep (se 2 (by rfl) ⟨701448, by rfl⟩ : syracuseStep 1870529 = 1402897) B1402897
theorem B1247939 : Blo 1246441 1247939 := bstep (se 1 (by rfl) ⟨935954, by rfl⟩ : syracuseStep 1247939 = 1871909) B1871909
theorem B3795665 : Blo 1246441 3795665 := bstep (se 2 (by rfl) ⟨1423374, by rfl⟩ : syracuseStep 3795665 = 2846749) B2846749
theorem B4213457 : Blo 1246441 4213457 := bstep (se 2 (by rfl) ⟨1580046, by rfl⟩ : syracuseStep 4213457 = 3160093) B3160093
theorem B1870547 : Blo 1246441 1870547 := bstep (se 1 (by rfl) ⟨1402910, by rfl⟩ : syracuseStep 1870547 = 2805821) B2805821
theorem B1247955 : Blo 1246441 1247955 := bstep (se 1 (by rfl) ⟨935966, by rfl⟩ : syracuseStep 1247955 = 1871933) B1871933
theorem B1247971 : Blo 1246441 1247971 := bstep (se 1 (by rfl) ⟨935978, by rfl⟩ : syracuseStep 1247971 = 1871957) B1871957
theorem B1870577 : Blo 1246441 1870577 := bstep (se 2 (by rfl) ⟨701466, by rfl⟩ : syracuseStep 1870577 = 1402933) B1402933
theorem B8653553 : Blo 1246441 8653553 := bstep (se 2 (by rfl) ⟨3245082, by rfl⟩ : syracuseStep 8653553 = 6490165) B6490165
theorem B1403635 : Blo 1246441 1403635 := bstep (se 1 (by rfl) ⟨1052726, by rfl⟩ : syracuseStep 1403635 = 2105453) B2105453
theorem B1247987 : Blo 1246441 1247987 := bstep (se 1 (by rfl) ⟨935990, by rfl⟩ : syracuseStep 1247987 = 1871981) B1871981
theorem B1870595 : Blo 1246441 1870595 := bstep (se 1 (by rfl) ⟨1402946, by rfl⟩ : syracuseStep 1870595 = 2805893) B2805893
theorem B2665219 : Blo 1246441 2665219 := bstep (se 1 (by rfl) ⟨1998914, by rfl⟩ : syracuseStep 2665219 = 3997829) B3997829
theorem B1248003 : Blo 1246441 1248003 := bstep (se 1 (by rfl) ⟨936002, by rfl⟩ : syracuseStep 1248003 = 1872005) B1872005
theorem B1248019 : Blo 1246441 1248019 := bstep (se 1 (by rfl) ⟨936014, by rfl⟩ : syracuseStep 1248019 = 1872029) B1872029
theorem B1870625 : Blo 1246441 1870625 := bstep (se 2 (by rfl) ⟨701484, by rfl⟩ : syracuseStep 1870625 = 1402969) B1402969
theorem B1248035 : Blo 1246441 1248035 := bstep (se 1 (by rfl) ⟨936026, by rfl⟩ : syracuseStep 1248035 = 1872053) B1872053
theorem B1870643 : Blo 1246441 1870643 := bstep (se 1 (by rfl) ⟨1402982, by rfl⟩ : syracuseStep 1870643 = 2805965) B2805965
theorem B1248051 : Blo 1246441 1248051 := bstep (se 1 (by rfl) ⟨936038, by rfl⟩ : syracuseStep 1248051 = 1872077) B1872077
theorem B3156803 : Blo 1246441 3156803 := bstep (se 1 (by rfl) ⟨2367602, by rfl⟩ : syracuseStep 3156803 = 4735205) B4735205
theorem B1248067 : Blo 1246441 1248067 := bstep (se 1 (by rfl) ⟨936050, by rfl⟩ : syracuseStep 1248067 = 1872101) B1872101
theorem B2804561 : Blo 1246441 2804561 := bstep (se 2 (by rfl) ⟨1051710, by rfl⟩ : syracuseStep 2804561 = 2103421) B2103421
theorem B1870673 : Blo 1246441 1870673 := bstep (se 2 (by rfl) ⟨701502, by rfl⟩ : syracuseStep 1870673 = 1403005) B1403005
theorem B1248083 : Blo 1246441 1248083 := bstep (se 1 (by rfl) ⟨936062, by rfl⟩ : syracuseStep 1248083 = 1872125) B1872125
theorem B2804579 : Blo 1246441 2804579 := bstep (se 1 (by rfl) ⟨2103434, by rfl⟩ : syracuseStep 2804579 = 4206869) B4206869
theorem B1870691 : Blo 1246441 1870691 := bstep (se 1 (by rfl) ⟨1403018, by rfl⟩ : syracuseStep 1870691 = 2806037) B2806037
theorem B1248099 : Blo 1246441 1248099 := bstep (se 1 (by rfl) ⟨936074, by rfl⟩ : syracuseStep 1248099 = 1872149) B1872149
theorem B1248115 : Blo 1246441 1248115 := bstep (se 1 (by rfl) ⟨936086, by rfl⟩ : syracuseStep 1248115 = 1872173) B1872173
theorem B1870721 : Blo 1246441 1870721 := bstep (se 2 (by rfl) ⟨701520, by rfl⟩ : syracuseStep 1870721 = 1403041) B1403041
theorem B1403779 : Blo 1246441 1403779 := bstep (se 1 (by rfl) ⟨1052834, by rfl⟩ : syracuseStep 1403779 = 2105669) B2105669
theorem B1248131 : Blo 1246441 1248131 := bstep (se 1 (by rfl) ⟨936098, by rfl⟩ : syracuseStep 1248131 = 1872197) B1872197
theorem B1870739 : Blo 1246441 1870739 := bstep (se 1 (by rfl) ⟨1403054, by rfl⟩ : syracuseStep 1870739 = 2806109) B2806109
theorem B1248147 : Blo 1246441 1248147 := bstep (se 1 (by rfl) ⟨936110, by rfl⟩ : syracuseStep 1248147 = 1872221) B1872221
theorem B1248163 : Blo 1246441 1248163 := bstep (se 1 (by rfl) ⟨936122, by rfl⟩ : syracuseStep 1248163 = 1872245) B1872245
theorem B1870769 : Blo 1246441 1870769 := bstep (se 2 (by rfl) ⟨701538, by rfl⟩ : syracuseStep 1870769 = 1403077) B1403077
theorem B1248179 : Blo 1246441 1248179 := bstep (se 1 (by rfl) ⟨936134, by rfl⟩ : syracuseStep 1248179 = 1872269) B1872269
theorem B1870787 : Blo 1246441 1870787 := bstep (se 1 (by rfl) ⟨1403090, by rfl⟩ : syracuseStep 1870787 = 2806181) B2806181
theorem B1248195 : Blo 1246441 1248195 := bstep (se 1 (by rfl) ⟨936146, by rfl⟩ : syracuseStep 1248195 = 1872293) B1872293
theorem B10660805 : Blo 1246441 10660805 := bstep (se 4 (by rfl) ⟨999450, by rfl⟩ : syracuseStep 10660805 = 1998901) B1998901
theorem B1248211 : Blo 1246441 1248211 := bstep (se 1 (by rfl) ⟨936158, by rfl⟩ : syracuseStep 1248211 = 1872317) B1872317
theorem B1870817 : Blo 1246441 1870817 := bstep (se 2 (by rfl) ⟨701556, by rfl⟩ : syracuseStep 1870817 = 1403113) B1403113
theorem B1248227 : Blo 1246441 1248227 := bstep (se 1 (by rfl) ⟨936170, by rfl⟩ : syracuseStep 1248227 = 1872341) B1872341
theorem B1870835 : Blo 1246441 1870835 := bstep (se 1 (by rfl) ⟨1403126, by rfl⟩ : syracuseStep 1870835 = 2806253) B2806253
theorem B1248243 : Blo 1246441 1248243 := bstep (se 1 (by rfl) ⟨936182, by rfl⟩ : syracuseStep 1248243 = 1872365) B1872365
theorem B3156995 : Blo 1246441 3156995 := bstep (se 1 (by rfl) ⟨2367746, by rfl⟩ : syracuseStep 3156995 = 4735493) B4735493
theorem B2665475 : Blo 1246441 2665475 := bstep (se 1 (by rfl) ⟨1999106, by rfl⟩ : syracuseStep 2665475 = 3998213) B3998213
theorem B1248259 : Blo 1246441 1248259 := bstep (se 1 (by rfl) ⟨936194, by rfl⟩ : syracuseStep 1248259 = 1872389) B1872389
theorem B1870865 : Blo 1246441 1870865 := bstep (se 2 (by rfl) ⟨701574, by rfl⟩ : syracuseStep 1870865 = 1403149) B1403149
theorem B1403923 : Blo 1246441 1403923 := bstep (se 1 (by rfl) ⟨1052942, by rfl⟩ : syracuseStep 1403923 = 2105885) B2105885
theorem B1248275 : Blo 1246441 1248275 := bstep (se 1 (by rfl) ⟨936206, by rfl⟩ : syracuseStep 1248275 = 1872413) B1872413
theorem B1870883 : Blo 1246441 1870883 := bstep (se 1 (by rfl) ⟨1403162, by rfl⟩ : syracuseStep 1870883 = 2806325) B2806325
theorem B1248291 : Blo 1246441 1248291 := bstep (se 1 (by rfl) ⟨936218, by rfl⟩ : syracuseStep 1248291 = 1872437) B1872437
theorem B1248307 : Blo 1246441 1248307 := bstep (se 1 (by rfl) ⟨936230, by rfl⟩ : syracuseStep 1248307 = 1872461) B1872461
theorem B1870913 : Blo 1246441 1870913 := bstep (se 2 (by rfl) ⟨701592, by rfl⟩ : syracuseStep 1870913 = 1403185) B1403185
theorem B1248323 : Blo 1246441 1248323 := bstep (se 1 (by rfl) ⟨936242, by rfl⟩ : syracuseStep 1248323 = 1872485) B1872485
theorem B10652741 : Blo 1246441 10652741 := bstep (se 4 (by rfl) ⟨998694, by rfl⟩ : syracuseStep 10652741 = 1997389) B1997389
theorem B1870931 : Blo 1246441 1870931 := bstep (se 1 (by rfl) ⟨1403198, by rfl⟩ : syracuseStep 1870931 = 2806397) B2806397
theorem B1248339 : Blo 1246441 1248339 := bstep (se 1 (by rfl) ⟨936254, by rfl⟩ : syracuseStep 1248339 = 1872509) B1872509
theorem B1248355 : Blo 1246441 1248355 := bstep (se 1 (by rfl) ⟨936266, by rfl⟩ : syracuseStep 1248355 = 1872533) B1872533
theorem B2804849 : Blo 1246441 2804849 := bstep (se 2 (by rfl) ⟨1051818, by rfl⟩ : syracuseStep 2804849 = 2103637) B2103637
theorem B3550321 : Blo 1246441 3550321 := bstep (se 2 (by rfl) ⟨1331370, by rfl⟩ : syracuseStep 3550321 = 2662741) B2662741
theorem B1870961 : Blo 1246441 1870961 := bstep (se 2 (by rfl) ⟨701610, by rfl⟩ : syracuseStep 1870961 = 1403221) B1403221
theorem B1248371 : Blo 1246441 1248371 := bstep (se 1 (by rfl) ⟨936278, by rfl⟩ : syracuseStep 1248371 = 1872557) B1872557
theorem B2804867 : Blo 1246441 2804867 := bstep (se 1 (by rfl) ⟨2103650, by rfl⟩ : syracuseStep 2804867 = 4207301) B4207301
theorem B1870979 : Blo 1246441 1870979 := bstep (se 1 (by rfl) ⟨1403234, by rfl⟩ : syracuseStep 1870979 = 2806469) B2806469
theorem B1248387 : Blo 1246441 1248387 := bstep (se 1 (by rfl) ⟨936290, by rfl⟩ : syracuseStep 1248387 = 1872581) B1872581
theorem B5057677 : Blo 1246441 5057677 := bstep (se 3 (by rfl) ⟨948314, by rfl⟩ : syracuseStep 5057677 = 1896629) B1896629
theorem B1248403 : Blo 1246441 1248403 := bstep (se 1 (by rfl) ⟨936302, by rfl⟩ : syracuseStep 1248403 = 1872605) B1872605
theorem B1871009 : Blo 1246441 1871009 := bstep (se 2 (by rfl) ⟨701628, by rfl⟩ : syracuseStep 1871009 = 1403257) B1403257
theorem B1404067 : Blo 1246441 1404067 := bstep (se 1 (by rfl) ⟨1053050, by rfl⟩ : syracuseStep 1404067 = 2106101) B2106101
theorem B1248419 : Blo 1246441 1248419 := bstep (se 1 (by rfl) ⟨936314, by rfl⟩ : syracuseStep 1248419 = 1872629) B1872629
theorem B1871027 : Blo 1246441 1871027 := bstep (se 1 (by rfl) ⟨1403270, by rfl⟩ : syracuseStep 1871027 = 2806541) B2806541
theorem B1248435 : Blo 1246441 1248435 := bstep (se 1 (by rfl) ⟨936326, by rfl⟩ : syracuseStep 1248435 = 1872653) B1872653
theorem B31952069 : Blo 1246441 31952069 := bstep (se 4 (by rfl) ⟨2995506, by rfl⟩ : syracuseStep 31952069 = 5991013) B5991013
theorem B1871057 : Blo 1246441 1871057 := bstep (se 2 (by rfl) ⟨701646, by rfl⟩ : syracuseStep 1871057 = 1403293) B1403293
theorem B1871075 : Blo 1246441 1871075 := bstep (se 1 (by rfl) ⟨1403306, by rfl⟩ : syracuseStep 1871075 = 2806613) B2806613
theorem B4050157 : Blo 1246441 4050157 := bstep (se 3 (by rfl) ⟨759404, by rfl⟩ : syracuseStep 4050157 = 1518809) B1518809
theorem B1871105 : Blo 1246441 1871105 := bstep (se 2 (by rfl) ⟨701664, by rfl⟩ : syracuseStep 1871105 = 1403329) B1403329
theorem B3288323 : Blo 1246441 3288323 := bstep (se 1 (by rfl) ⟨2466242, by rfl⟩ : syracuseStep 3288323 = 4932485) B4932485
theorem B1871123 : Blo 1246441 1871123 := bstep (se 1 (by rfl) ⟨1403342, by rfl⟩ : syracuseStep 1871123 = 2806685) B2806685
theorem B1871153 : Blo 1246441 1871153 := bstep (se 2 (by rfl) ⟨701682, by rfl⟩ : syracuseStep 1871153 = 1403365) B1403365
theorem B1404211 : Blo 1246441 1404211 := bstep (se 1 (by rfl) ⟨1053158, by rfl⟩ : syracuseStep 1404211 = 2106317) B2106317
theorem B1871171 : Blo 1246441 1871171 := bstep (se 1 (by rfl) ⟨1403378, by rfl⟩ : syracuseStep 1871171 = 2806757) B2806757
theorem B1871201 : Blo 1246441 1871201 := bstep (se 2 (by rfl) ⟨701700, by rfl⟩ : syracuseStep 1871201 = 1403401) B1403401
theorem B34614641 : Blo 1246441 34614641 := bstep (se 2 (by rfl) ⟨12980490, by rfl⟩ : syracuseStep 34614641 = 25960981) B25960981
theorem B1871219 : Blo 1246441 1871219 := bstep (se 1 (by rfl) ⟨1403414, by rfl⟩ : syracuseStep 1871219 = 2806829) B2806829
theorem B2805137 : Blo 1246441 2805137 := bstep (se 2 (by rfl) ⟨1051926, by rfl⟩ : syracuseStep 2805137 = 2103853) B2103853
theorem B1871249 : Blo 1246441 1871249 := bstep (se 2 (by rfl) ⟨701718, by rfl⟩ : syracuseStep 1871249 = 1403437) B1403437
theorem B2805155 : Blo 1246441 2805155 := bstep (se 1 (by rfl) ⟨2103866, by rfl⟩ : syracuseStep 2805155 = 4207733) B4207733
theorem B1871267 : Blo 1246441 1871267 := bstep (se 1 (by rfl) ⟨1403450, by rfl⟩ : syracuseStep 1871267 = 2806901) B2806901
theorem B1871297 : Blo 1246441 1871297 := bstep (se 2 (by rfl) ⟨701736, by rfl⟩ : syracuseStep 1871297 = 1403473) B1403473
theorem B1404355 : Blo 1246441 1404355 := bstep (se 1 (by rfl) ⟨1053266, by rfl⟩ : syracuseStep 1404355 = 2106533) B2106533
theorem B1871315 : Blo 1246441 1871315 := bstep (se 1 (by rfl) ⟨1403486, by rfl⟩ : syracuseStep 1871315 = 2806973) B2806973
theorem B1871345 : Blo 1246441 1871345 := bstep (se 2 (by rfl) ⟨701754, by rfl⟩ : syracuseStep 1871345 = 1403509) B1403509
theorem B1871363 : Blo 1246441 1871363 := bstep (se 1 (by rfl) ⟨1403522, by rfl⟩ : syracuseStep 1871363 = 2807045) B2807045
theorem B1871393 : Blo 1246441 1871393 := bstep (se 2 (by rfl) ⟨701772, by rfl⟩ : syracuseStep 1871393 = 1403545) B1403545
theorem B1871411 : Blo 1246441 1871411 := bstep (se 1 (by rfl) ⟨1403558, by rfl⟩ : syracuseStep 1871411 = 2807117) B2807117
theorem B1871441 : Blo 1246441 1871441 := bstep (se 2 (by rfl) ⟨701790, by rfl⟩ : syracuseStep 1871441 = 1403581) B1403581
theorem B1871459 : Blo 1246441 1871459 := bstep (se 1 (by rfl) ⟨1403594, by rfl⟩ : syracuseStep 1871459 = 2807189) B2807189
theorem B10661489 : Blo 1246441 10661489 := bstep (se 2 (by rfl) ⟨3998058, by rfl⟩ : syracuseStep 10661489 = 7996117) B7996117
theorem B1871489 : Blo 1246441 1871489 := bstep (se 2 (by rfl) ⟨701808, by rfl⟩ : syracuseStep 1871489 = 1403617) B1403617
theorem B3370637 : Blo 1246441 3370637 := bstep (se 3 (by rfl) ⟨631994, by rfl⟩ : syracuseStep 3370637 = 1263989) B1263989
theorem B1871507 : Blo 1246441 1871507 := bstep (se 1 (by rfl) ⟨1403630, by rfl⟩ : syracuseStep 1871507 = 2807261) B2807261
theorem B2805425 : Blo 1246441 2805425 := bstep (se 2 (by rfl) ⟨1052034, by rfl⟩ : syracuseStep 2805425 = 2104069) B2104069
theorem B1871537 : Blo 1246441 1871537 := bstep (se 2 (by rfl) ⟨701826, by rfl⟩ : syracuseStep 1871537 = 1403653) B1403653
theorem B2805443 : Blo 1246441 2805443 := bstep (se 1 (by rfl) ⟨2104082, by rfl⟩ : syracuseStep 2805443 = 4208165) B4208165
theorem B1871555 : Blo 1246441 1871555 := bstep (se 1 (by rfl) ⟨1403666, by rfl⟩ : syracuseStep 1871555 = 2807333) B2807333
theorem B1871585 : Blo 1246441 1871585 := bstep (se 2 (by rfl) ⟨701844, by rfl⟩ : syracuseStep 1871585 = 1403689) B1403689
theorem B5328611 : Blo 1246441 5328611 := bstep (se 1 (by rfl) ⟨3996458, by rfl⟩ : syracuseStep 5328611 = 7992917) B7992917
theorem B1871603 : Blo 1246441 1871603 := bstep (se 1 (by rfl) ⟨1403702, by rfl⟩ : syracuseStep 1871603 = 2807405) B2807405
theorem B1871633 : Blo 1246441 1871633 := bstep (se 2 (by rfl) ⟨701862, by rfl⟩ : syracuseStep 1871633 = 1403725) B1403725
theorem B1871651 : Blo 1246441 1871651 := bstep (se 1 (by rfl) ⟨1403738, by rfl⟩ : syracuseStep 1871651 = 2807477) B2807477
theorem B1871681 : Blo 1246441 1871681 := bstep (se 2 (by rfl) ⟨701880, by rfl⟩ : syracuseStep 1871681 = 1403761) B1403761
theorem B3993421 : Blo 1246441 3993421 := bstep (se 3 (by rfl) ⟨748766, by rfl⟩ : syracuseStep 3993421 = 1497533) B1497533
theorem B1871699 : Blo 1246441 1871699 := bstep (se 1 (by rfl) ⟨1403774, by rfl⟩ : syracuseStep 1871699 = 2807549) B2807549
theorem B1871729 : Blo 1246441 1871729 := bstep (se 2 (by rfl) ⟨701898, by rfl⟩ : syracuseStep 1871729 = 1403797) B1403797
theorem B1871747 : Blo 1246441 1871747 := bstep (se 1 (by rfl) ⟨1403810, by rfl⟩ : syracuseStep 1871747 = 2807621) B2807621
theorem B1871777 : Blo 1246441 1871777 := bstep (se 2 (by rfl) ⟨701916, by rfl⟩ : syracuseStep 1871777 = 1403833) B1403833
theorem B6311843 : Blo 1246441 6311843 := bstep (se 1 (by rfl) ⟨4733882, by rfl⟩ : syracuseStep 6311843 = 9467765) B9467765
theorem B3157937 : Blo 1246441 3157937 := bstep (se 2 (by rfl) ⟨1184226, by rfl⟩ : syracuseStep 3157937 = 2368453) B2368453
theorem B1871795 : Blo 1246441 1871795 := bstep (se 1 (by rfl) ⟨1403846, by rfl⟩ : syracuseStep 1871795 = 2807693) B2807693
theorem B2248643 : Blo 1246441 2248643 := bstep (se 1 (by rfl) ⟨1686482, by rfl⟩ : syracuseStep 2248643 = 3372965) B3372965
theorem B2805713 : Blo 1246441 2805713 := bstep (se 2 (by rfl) ⟨1052142, by rfl⟩ : syracuseStep 2805713 = 2104285) B2104285
theorem B1871825 : Blo 1246441 1871825 := bstep (se 2 (by rfl) ⟨701934, by rfl⟩ : syracuseStep 1871825 = 1403869) B1403869
theorem B2805731 : Blo 1246441 2805731 := bstep (se 1 (by rfl) ⟨2104298, by rfl⟩ : syracuseStep 2805731 = 4208597) B4208597
theorem B3157987 : Blo 1246441 3157987 := bstep (se 1 (by rfl) ⟨2368490, by rfl⟩ : syracuseStep 3157987 = 4736981) B4736981
theorem B1871843 : Blo 1246441 1871843 := bstep (se 1 (by rfl) ⟨1403882, by rfl⟩ : syracuseStep 1871843 = 2807765) B2807765
theorem B1871873 : Blo 1246441 1871873 := bstep (se 2 (by rfl) ⟨701952, by rfl⟩ : syracuseStep 1871873 = 1403905) B1403905
theorem B1871891 : Blo 1246441 1871891 := bstep (se 1 (by rfl) ⟨1403918, by rfl⟩ : syracuseStep 1871891 = 2807837) B2807837
theorem B4739107 : Blo 1246441 4739107 := bstep (se 1 (by rfl) ⟨3554330, by rfl⟩ : syracuseStep 4739107 = 7108661) B7108661
theorem B1871921 : Blo 1246441 1871921 := bstep (se 2 (by rfl) ⟨701970, by rfl⟩ : syracuseStep 1871921 = 1403941) B1403941
theorem B1871939 : Blo 1246441 1871939 := bstep (se 1 (by rfl) ⟨1403954, by rfl⟩ : syracuseStep 1871939 = 2807909) B2807909
theorem B1871969 : Blo 1246441 1871969 := bstep (se 2 (by rfl) ⟨701988, by rfl⟩ : syracuseStep 1871969 = 1403977) B1403977
theorem B3158129 : Blo 1246441 3158129 := bstep (se 2 (by rfl) ⟨1184298, by rfl⟩ : syracuseStep 3158129 = 2368597) B2368597
theorem B30363761 : Blo 1246441 30363761 := bstep (se 2 (by rfl) ⟨11386410, by rfl⟩ : syracuseStep 30363761 = 22772821) B22772821
theorem B1871987 : Blo 1246441 1871987 := bstep (se 1 (by rfl) ⟨1403990, by rfl⟩ : syracuseStep 1871987 = 2807981) B2807981
theorem B1872017 : Blo 1246441 1872017 := bstep (se 2 (by rfl) ⟨702006, by rfl⟩ : syracuseStep 1872017 = 1404013) B1404013
theorem B1872035 : Blo 1246441 1872035 := bstep (se 1 (by rfl) ⟨1404026, by rfl⟩ : syracuseStep 1872035 = 2808053) B2808053
theorem B1872065 : Blo 1246441 1872065 := bstep (se 2 (by rfl) ⟨702024, by rfl⟩ : syracuseStep 1872065 = 1404049) B1404049
theorem B1872083 : Blo 1246441 1872083 := bstep (se 1 (by rfl) ⟨1404062, by rfl⟩ : syracuseStep 1872083 = 2808125) B2808125
theorem B2248931 : Blo 1246441 2248931 := bstep (se 1 (by rfl) ⟨1686698, by rfl⟩ : syracuseStep 2248931 = 3373397) B3373397
theorem B2806001 : Blo 1246441 2806001 := bstep (se 2 (by rfl) ⟨1052250, by rfl⟩ : syracuseStep 2806001 = 2104501) B2104501
theorem B1872113 : Blo 1246441 1872113 := bstep (se 2 (by rfl) ⟨702042, by rfl⟩ : syracuseStep 1872113 = 1404085) B1404085
theorem B1896691 : Blo 1246441 1896691 := bstep (se 1 (by rfl) ⟨1422518, by rfl⟩ : syracuseStep 1896691 = 2845037) B2845037
theorem B2806019 : Blo 1246441 2806019 := bstep (se 1 (by rfl) ⟨2104514, by rfl⟩ : syracuseStep 2806019 = 4209029) B4209029
theorem B1872131 : Blo 1246441 1872131 := bstep (se 1 (by rfl) ⟨1404098, by rfl⟩ : syracuseStep 1872131 = 2808197) B2808197
theorem B1421587 : Blo 1246441 1421587 := bstep (se 1 (by rfl) ⟨1066190, by rfl⟩ : syracuseStep 1421587 = 2132381) B2132381
theorem B1872161 : Blo 1246441 1872161 := bstep (se 2 (by rfl) ⟨702060, by rfl⟩ : syracuseStep 1872161 = 1404121) B1404121
theorem B1872179 : Blo 1246441 1872179 := bstep (se 1 (by rfl) ⟨1404134, by rfl⟩ : syracuseStep 1872179 = 2808269) B2808269
theorem B7106885 : Blo 1246441 7106885 := bstep (se 4 (by rfl) ⟨666270, by rfl⟩ : syracuseStep 7106885 = 1332541) B1332541
theorem B1872209 : Blo 1246441 1872209 := bstep (se 2 (by rfl) ⟨702078, by rfl⟩ : syracuseStep 1872209 = 1404157) B1404157
theorem B1872227 : Blo 1246441 1872227 := bstep (se 1 (by rfl) ⟨1404170, by rfl⟩ : syracuseStep 1872227 = 2808341) B2808341
theorem B3551597 : Blo 1246441 3551597 := bstep (se 3 (by rfl) ⟨665924, by rfl⟩ : syracuseStep 3551597 = 1331849) B1331849
theorem B1872257 : Blo 1246441 1872257 := bstep (se 2 (by rfl) ⟨702096, by rfl⟩ : syracuseStep 1872257 = 1404193) B1404193
theorem B1872275 : Blo 1246441 1872275 := bstep (se 1 (by rfl) ⟨1404206, by rfl⟩ : syracuseStep 1872275 = 2808413) B2808413
theorem B1872305 : Blo 1246441 1872305 := bstep (se 2 (by rfl) ⟨702114, by rfl⟩ : syracuseStep 1872305 = 1404229) B1404229
theorem B1872323 : Blo 1246441 1872323 := bstep (se 1 (by rfl) ⟨1404242, by rfl⟩ : syracuseStep 1872323 = 2808485) B2808485
theorem B1872353 : Blo 1246441 1872353 := bstep (se 2 (by rfl) ⟨702132, by rfl⟩ : syracuseStep 1872353 = 1404265) B1404265
theorem B4207085 : Blo 1246441 4207085 := bstep (se 3 (by rfl) ⟨788828, by rfl⟩ : syracuseStep 4207085 = 1577657) B1577657
theorem B1872371 : Blo 1246441 1872371 := bstep (se 1 (by rfl) ⟨1404278, by rfl⟩ : syracuseStep 1872371 = 2808557) B2808557
theorem B4493837 : Blo 1246441 4493837 := bstep (se 3 (by rfl) ⟨842594, by rfl⟩ : syracuseStep 4493837 = 1685189) B1685189
theorem B2806289 : Blo 1246441 2806289 := bstep (se 2 (by rfl) ⟨1052358, by rfl⟩ : syracuseStep 2806289 = 2104717) B2104717
theorem B1872401 : Blo 1246441 1872401 := bstep (se 2 (by rfl) ⟨702150, by rfl⟩ : syracuseStep 1872401 = 1404301) B1404301
theorem B4207139 : Blo 1246441 4207139 := bstep (se 1 (by rfl) ⟨3155354, by rfl⟩ : syracuseStep 4207139 = 6310709) B6310709
theorem B2806307 : Blo 1246441 2806307 := bstep (se 1 (by rfl) ⟨2104730, by rfl⟩ : syracuseStep 2806307 = 4209461) B4209461
theorem B3551779 : Blo 1246441 3551779 := bstep (se 1 (by rfl) ⟨2663834, by rfl⟩ : syracuseStep 3551779 = 5327669) B5327669
theorem B1872419 : Blo 1246441 1872419 := bstep (se 1 (by rfl) ⟨1404314, by rfl⟩ : syracuseStep 1872419 = 2808629) B2808629
theorem B1421875 : Blo 1246441 1421875 := bstep (se 1 (by rfl) ⟨1066406, by rfl⟩ : syracuseStep 1421875 = 2132813) B2132813
theorem B1872449 : Blo 1246441 1872449 := bstep (se 2 (by rfl) ⟨702168, by rfl⟩ : syracuseStep 1872449 = 1404337) B1404337
theorem B3551825 : Blo 1246441 3551825 := bstep (se 2 (by rfl) ⟨1331934, by rfl⟩ : syracuseStep 3551825 = 2663869) B2663869
theorem B1921619 : Blo 1246441 1921619 := bstep (se 1 (by rfl) ⟨1441214, by rfl⟩ : syracuseStep 1921619 = 2882429) B2882429
theorem B1872467 : Blo 1246441 1872467 := bstep (se 1 (by rfl) ⟨1404350, by rfl⟩ : syracuseStep 1872467 = 2808701) B2808701
theorem B3371633 : Blo 1246441 3371633 := bstep (se 2 (by rfl) ⟨1264362, by rfl⟩ : syracuseStep 3371633 = 2528725) B2528725
theorem B1872497 : Blo 1246441 1872497 := bstep (se 2 (by rfl) ⟨702186, by rfl⟩ : syracuseStep 1872497 = 1404373) B1404373
theorem B1872515 : Blo 1246441 1872515 := bstep (se 1 (by rfl) ⟨1404386, by rfl⟩ : syracuseStep 1872515 = 2808773) B2808773
theorem B1872545 : Blo 1246441 1872545 := bstep (se 2 (by rfl) ⟨702204, by rfl⟩ : syracuseStep 1872545 = 1404409) B1404409
theorem B1872563 : Blo 1246441 1872563 := bstep (se 1 (by rfl) ⟨1404422, by rfl⟩ : syracuseStep 1872563 = 2808845) B2808845
theorem B6312653 : Blo 1246441 6312653 := bstep (se 3 (by rfl) ⟨1183622, by rfl⟩ : syracuseStep 6312653 = 2367245) B2367245
theorem B3846865 : Blo 1246441 3846865 := bstep (se 2 (by rfl) ⟨1442574, by rfl⟩ : syracuseStep 3846865 = 2885149) B2885149
theorem B1872593 : Blo 1246441 1872593 := bstep (se 2 (by rfl) ⟨702222, by rfl⟩ : syracuseStep 1872593 = 1404445) B1404445
theorem B1872611 : Blo 1246441 1872611 := bstep (se 1 (by rfl) ⟨1404458, by rfl⟩ : syracuseStep 1872611 = 2808917) B2808917
theorem B1872641 : Blo 1246441 1872641 := bstep (se 2 (by rfl) ⟨702240, by rfl⟩ : syracuseStep 1872641 = 1404481) B1404481
theorem B1872659 : Blo 1246441 1872659 := bstep (se 1 (by rfl) ⟨1404494, by rfl⟩ : syracuseStep 1872659 = 2808989) B2808989
theorem B4207409 : Blo 1246441 4207409 := bstep (se 2 (by rfl) ⟨1577778, by rfl⟩ : syracuseStep 4207409 = 3155557) B3155557
theorem B2806577 : Blo 1246441 2806577 := bstep (se 2 (by rfl) ⟨1052466, by rfl⟩ : syracuseStep 2806577 = 2104933) B2104933
theorem B2806595 : Blo 1246441 2806595 := bstep (se 1 (by rfl) ⟨2104946, by rfl⟩ : syracuseStep 2806595 = 4209893) B4209893
theorem B7590797 : Blo 1246441 7590797 := bstep (se 3 (by rfl) ⟨1423274, by rfl⟩ : syracuseStep 7590797 = 2846549) B2846549
theorem B1577875 : Blo 1246441 1577875 := bstep (se 1 (by rfl) ⟨1183406, by rfl⟩ : syracuseStep 1577875 = 2366813) B2366813
theorem B4797347 : Blo 1246441 4797347 := bstep (se 1 (by rfl) ⟨3598010, by rfl⟩ : syracuseStep 4797347 = 7196021) B7196021
theorem B1332131 : Blo 1246441 1332131 := bstep (se 1 (by rfl) ⟨999098, by rfl⟩ : syracuseStep 1332131 = 1998197) B1998197
theorem B1577971 : Blo 1246441 1577971 := bstep (se 1 (by rfl) ⟨1183478, by rfl⟩ : syracuseStep 1577971 = 2366957) B2366957
theorem B1922051 : Blo 1246441 1922051 := bstep (se 1 (by rfl) ⟨1441538, by rfl⟩ : syracuseStep 1922051 = 2883077) B2883077
theorem B6927373 : Blo 1246441 6927373 := bstep (se 3 (by rfl) ⟨1298882, by rfl⟩ : syracuseStep 6927373 = 2597765) B2597765
theorem B2806865 : Blo 1246441 2806865 := bstep (se 2 (by rfl) ⟨1052574, by rfl⟩ : syracuseStep 2806865 = 2105149) B2105149
theorem B3159121 : Blo 1246441 3159121 := bstep (se 2 (by rfl) ⟨1184670, by rfl⟩ : syracuseStep 3159121 = 2369341) B2369341
theorem B2806883 : Blo 1246441 2806883 := bstep (se 1 (by rfl) ⟨2105162, by rfl⟩ : syracuseStep 2806883 = 4210325) B4210325
theorem B2135171 : Blo 1246441 2135171 := bstep (se 1 (by rfl) ⟨1601378, by rfl⟩ : syracuseStep 2135171 = 3202757) B3202757
theorem B1774819 : Blo 1246441 1774819 := bstep (se 1 (by rfl) ⟨1331114, by rfl⟩ : syracuseStep 1774819 = 2662229) B2662229
theorem B4207949 : Blo 1246441 4207949 := bstep (se 3 (by rfl) ⟨788990, by rfl⟩ : syracuseStep 4207949 = 1577981) B1577981
theorem B3159395 : Blo 1246441 3159395 := bstep (se 1 (by rfl) ⟨2369546, by rfl⟩ : syracuseStep 3159395 = 4739093) B4739093
theorem B2807153 : Blo 1246441 2807153 := bstep (se 2 (by rfl) ⟨1052682, by rfl⟩ : syracuseStep 2807153 = 2105365) B2105365
theorem B4208003 : Blo 1246441 4208003 := bstep (se 1 (by rfl) ⟨3156002, by rfl⟩ : syracuseStep 4208003 = 6312005) B6312005
theorem B2807171 : Blo 1246441 2807171 := bstep (se 1 (by rfl) ⟨2105378, by rfl⟩ : syracuseStep 2807171 = 4210757) B4210757
theorem B1578467 : Blo 1246441 1578467 := bstep (se 1 (by rfl) ⟨1183850, by rfl⟩ : syracuseStep 1578467 = 2367701) B2367701
theorem B7206371 : Blo 1246441 7206371 := bstep (se 1 (by rfl) ⟨5404778, by rfl⟩ : syracuseStep 7206371 = 10809557) B10809557
theorem B8099341 : Blo 1246441 8099341 := bstep (se 3 (by rfl) ⟨1518626, by rfl⟩ : syracuseStep 8099341 = 3037253) B3037253
theorem B3159587 : Blo 1246441 3159587 := bstep (se 1 (by rfl) ⟨2369690, by rfl⟩ : syracuseStep 3159587 = 4739381) B4739381
theorem B15988337 : Blo 1246441 15988337 := bstep (se 2 (by rfl) ⟨5995626, by rfl⟩ : syracuseStep 15988337 = 11991253) B11991253
theorem B4208273 : Blo 1246441 4208273 := bstep (se 2 (by rfl) ⟨1578102, by rfl⟩ : syracuseStep 4208273 = 3156205) B3156205
theorem B2807441 : Blo 1246441 2807441 := bstep (se 2 (by rfl) ⟨1052790, by rfl⟩ : syracuseStep 2807441 = 2105581) B2105581
theorem B1332883 : Blo 1246441 1332883 := bstep (se 1 (by rfl) ⟨999662, by rfl⟩ : syracuseStep 1332883 = 1999325) B1999325
theorem B2807459 : Blo 1246441 2807459 := bstep (se 1 (by rfl) ⟨2105594, by rfl⟩ : syracuseStep 2807459 = 4211189) B4211189
theorem B5330609 : Blo 1246441 5330609 := bstep (se 2 (by rfl) ⟨1998978, by rfl⟩ : syracuseStep 5330609 = 3997957) B3997957
theorem B3602179 : Blo 1246441 3602179 := bstep (se 1 (by rfl) ⟨2701634, by rfl⟩ : syracuseStep 3602179 = 5403269) B5403269
theorem B7198541 : Blo 1246441 7198541 := bstep (se 3 (by rfl) ⟨1349726, by rfl⟩ : syracuseStep 7198541 = 2699453) B2699453
theorem B26974093 : Blo 1246441 26974093 := bstep (se 3 (by rfl) ⟨5057642, by rfl⟩ : syracuseStep 26974093 = 10115285) B10115285
theorem B2807729 : Blo 1246441 2807729 := bstep (se 2 (by rfl) ⟨1052898, by rfl⟩ : syracuseStep 2807729 = 2105797) B2105797
theorem B2807747 : Blo 1246441 2807747 := bstep (se 1 (by rfl) ⟨2105810, by rfl⟩ : syracuseStep 2807747 = 4211621) B4211621
theorem B3553283 : Blo 1246441 3553283 := bstep (se 1 (by rfl) ⟨2664962, by rfl⟩ : syracuseStep 3553283 = 5329925) B5329925
theorem B7993349 : Blo 1246441 7993349 := bstep (se 4 (by rfl) ⟨749376, by rfl⟩ : syracuseStep 7993349 = 1498753) B1498753
theorem B14211125 : Blo 1246441 14211125 := bstep (se 5 (by rfl) ⟨666146, by rfl⟩ : syracuseStep 14211125 = 1332293) B1332293
theorem B8984675 : Blo 1246441 8984675 := bstep (se 1 (by rfl) ⟨6738506, by rfl⟩ : syracuseStep 8984675 = 13477013) B13477013
theorem B1579171 : Blo 1246441 1579171 := bstep (se 1 (by rfl) ⟨1184378, by rfl⟩ : syracuseStep 1579171 = 2368757) B2368757
theorem B4208813 : Blo 1246441 4208813 := bstep (se 3 (by rfl) ⟨789152, by rfl⟩ : syracuseStep 4208813 = 1578305) B1578305
theorem B2103475 : Blo 1246441 2103475 := bstep (se 1 (by rfl) ⟨1577606, by rfl⟩ : syracuseStep 2103475 = 3155213) B3155213
theorem B1996979 : Blo 1246441 1996979 := bstep (se 1 (by rfl) ⟨1497734, by rfl⟩ : syracuseStep 1996979 = 2995469) B2995469
theorem B7100621 : Blo 1246441 7100621 := bstep (se 3 (by rfl) ⟨1331366, by rfl⟩ : syracuseStep 7100621 = 2662733) B2662733
theorem B2808017 : Blo 1246441 2808017 := bstep (se 2 (by rfl) ⟨1053006, by rfl⟩ : syracuseStep 2808017 = 2106013) B2106013
theorem B4208867 : Blo 1246441 4208867 := bstep (se 1 (by rfl) ⟨3156650, by rfl⟩ : syracuseStep 4208867 = 6313301) B6313301
theorem B2808035 : Blo 1246441 2808035 := bstep (se 1 (by rfl) ⟨2106026, by rfl⟩ : syracuseStep 2808035 = 4212053) B4212053
theorem B1579267 : Blo 1246441 1579267 := bstep (se 1 (by rfl) ⟨1184450, by rfl⟩ : syracuseStep 1579267 = 2368901) B2368901
theorem B2103617 : Blo 1246441 2103617 := bstep (se 2 (by rfl) ⟨788856, by rfl⟩ : syracuseStep 2103617 = 1577713) B1577713
theorem B10123589 : Blo 1246441 10123589 := bstep (se 4 (by rfl) ⟨949086, by rfl⟩ : syracuseStep 10123589 = 1898173) B1898173
theorem B4733261 : Blo 1246441 4733261 := bstep (se 3 (by rfl) ⟨887486, by rfl⟩ : syracuseStep 4733261 = 1774973) B1774973
theorem B1997153 : Blo 1246441 1997153 := bstep (se 2 (by rfl) ⟨748932, by rfl⟩ : syracuseStep 1997153 = 1497865) B1497865
theorem B1497523 : Blo 1246441 1497523 := bstep (se 1 (by rfl) ⟨1123142, by rfl⟩ : syracuseStep 1497523 = 2246285) B2246285
theorem B2103745 : Blo 1246441 2103745 := bstep (se 2 (by rfl) ⟨788904, by rfl⟩ : syracuseStep 2103745 = 1577809) B1577809
theorem B1497571 : Blo 1246441 1497571 := bstep (se 1 (by rfl) ⟨1123178, by rfl⟩ : syracuseStep 1497571 = 2246357) B2246357
theorem B2103779 : Blo 1246441 2103779 := bstep (se 1 (by rfl) ⟨1577834, by rfl⟩ : syracuseStep 2103779 = 3155669) B3155669
theorem B4209137 : Blo 1246441 4209137 := bstep (se 2 (by rfl) ⟨1578426, by rfl⟩ : syracuseStep 4209137 = 3156853) B3156853
theorem B2808305 : Blo 1246441 2808305 := bstep (se 2 (by rfl) ⟨1053114, by rfl⟩ : syracuseStep 2808305 = 2106229) B2106229
theorem B2808323 : Blo 1246441 2808323 := bstep (se 1 (by rfl) ⟨2106242, by rfl⟩ : syracuseStep 2808323 = 4212485) B4212485
theorem B1776163 : Blo 1246441 1776163 := bstep (se 1 (by rfl) ⟨1332122, by rfl⟩ : syracuseStep 1776163 = 2664245) B2664245
theorem B4266541 : Blo 1246441 4266541 := bstep (se 3 (by rfl) ⟨799976, by rfl⟩ : syracuseStep 4266541 = 1599953) B1599953
theorem B2103907 : Blo 1246441 2103907 := bstep (se 1 (by rfl) ⟨1577930, by rfl⟩ : syracuseStep 2103907 = 3155861) B3155861
theorem B2104049 : Blo 1246441 2104049 := bstep (se 2 (by rfl) ⟨789018, by rfl⟩ : syracuseStep 2104049 = 1578037) B1578037
theorem B1579763 : Blo 1246441 1579763 := bstep (se 1 (by rfl) ⟨1184822, by rfl⟩ : syracuseStep 1579763 = 2369645) B2369645
theorem B2808593 : Blo 1246441 2808593 := bstep (se 2 (by rfl) ⟨1053222, by rfl⟩ : syracuseStep 2808593 = 2106445) B2106445
theorem B2808611 : Blo 1246441 2808611 := bstep (se 1 (by rfl) ⟨2106458, by rfl⟩ : syracuseStep 2808611 = 4212917) B4212917
theorem B2104177 : Blo 1246441 2104177 := bstep (se 2 (by rfl) ⟨789066, by rfl⟩ : syracuseStep 2104177 = 1578133) B1578133
theorem B6749041 : Blo 1246441 6749041 := bstep (se 2 (by rfl) ⟨2530890, by rfl⟩ : syracuseStep 6749041 = 5061781) B5061781
theorem B2104211 : Blo 1246441 2104211 := bstep (se 1 (by rfl) ⟨1578158, by rfl⟩ : syracuseStep 2104211 = 3156317) B3156317
theorem B21314501 : Blo 1246441 21314501 := bstep (se 4 (by rfl) ⟨1998234, by rfl⟩ : syracuseStep 21314501 = 3996469) B3996469
theorem B4209677 : Blo 1246441 4209677 := bstep (se 3 (by rfl) ⟨789314, by rfl⟩ : syracuseStep 4209677 = 1578629) B1578629
theorem B3603473 : Blo 1246441 3603473 := bstep (se 2 (by rfl) ⟨1351302, by rfl⟩ : syracuseStep 3603473 = 2702605) B2702605
theorem B2104339 : Blo 1246441 2104339 := bstep (se 1 (by rfl) ⟨1578254, by rfl⟩ : syracuseStep 2104339 = 3156509) B3156509
theorem B2808881 : Blo 1246441 2808881 := bstep (se 2 (by rfl) ⟨1053330, by rfl⟩ : syracuseStep 2808881 = 2106661) B2106661
theorem B4209731 : Blo 1246441 4209731 := bstep (se 1 (by rfl) ⟨3157298, by rfl⟩ : syracuseStep 4209731 = 6314597) B6314597
theorem B2808899 : Blo 1246441 2808899 := bstep (se 1 (by rfl) ⟨2106674, by rfl⟩ : syracuseStep 2808899 = 4213349) B4213349
theorem B4734065 : Blo 1246441 4734065 := bstep (se 2 (by rfl) ⟨1775274, by rfl⟩ : syracuseStep 4734065 = 3550549) B3550549
theorem B7101553 : Blo 1246441 7101553 := bstep (se 2 (by rfl) ⟨2663082, by rfl⟩ : syracuseStep 7101553 = 5326165) B5326165
theorem B3996803 : Blo 1246441 3996803 := bstep (se 1 (by rfl) ⟨2997602, by rfl⟩ : syracuseStep 3996803 = 5995205) B5995205
theorem B2104481 : Blo 1246441 2104481 := bstep (se 2 (by rfl) ⟨789180, by rfl⟩ : syracuseStep 2104481 = 1578361) B1578361
theorem B3554513 : Blo 1246441 3554513 := bstep (se 2 (by rfl) ⟨1332942, by rfl⟩ : syracuseStep 3554513 = 2665885) B2665885
theorem B2104609 : Blo 1246441 2104609 := bstep (se 2 (by rfl) ⟨789228, by rfl⟩ : syracuseStep 2104609 = 1578457) B1578457
theorem B2104643 : Blo 1246441 2104643 := bstep (se 1 (by rfl) ⟨1578482, by rfl⟩ : syracuseStep 2104643 = 3156965) B3156965
theorem B5332301 : Blo 1246441 5332301 := bstep (se 3 (by rfl) ⟨999806, by rfl⟩ : syracuseStep 5332301 = 1999613) B1999613
theorem B4210001 : Blo 1246441 4210001 := bstep (se 2 (by rfl) ⟨1578750, by rfl⟩ : syracuseStep 4210001 = 3157501) B3157501
theorem B2104771 : Blo 1246441 2104771 := bstep (se 1 (by rfl) ⟨1578578, by rfl⟩ : syracuseStep 2104771 = 3157157) B3157157
theorem B5324237 : Blo 1246441 5324237 := bstep (se 3 (by rfl) ⟨998294, by rfl⟩ : syracuseStep 5324237 = 1996589) B1996589
theorem B4496867 : Blo 1246441 4496867 := bstep (se 1 (by rfl) ⟨3372650, by rfl⟩ : syracuseStep 4496867 = 6745301) B6745301
theorem B2530801 : Blo 1246441 2530801 := bstep (se 2 (by rfl) ⟨949050, by rfl⟩ : syracuseStep 2530801 = 1898101) B1898101
theorem B6315569 : Blo 1246441 6315569 := bstep (se 2 (by rfl) ⟨2368338, by rfl⟩ : syracuseStep 6315569 = 4736677) B4736677
theorem B2080337 : Blo 1246441 2080337 := bstep (se 2 (by rfl) ⟨780126, by rfl⟩ : syracuseStep 2080337 = 1560253) B1560253
theorem B2104913 : Blo 1246441 2104913 := bstep (se 2 (by rfl) ⟨789342, by rfl⟩ : syracuseStep 2104913 = 1578685) B1578685
theorem B1777297 : Blo 1246441 1777297 := bstep (se 2 (by rfl) ⟨666486, by rfl⟩ : syracuseStep 1777297 = 1332973) B1332973
theorem B2367139 : Blo 1246441 2367139 := bstep (se 1 (by rfl) ⟨1775354, by rfl⟩ : syracuseStep 2367139 = 3550709) B3550709
theorem B2105041 : Blo 1246441 2105041 := bstep (se 2 (by rfl) ⟨789390, by rfl⟩ : syracuseStep 2105041 = 1578781) B1578781
theorem B1777393 : Blo 1246441 1777393 := bstep (se 2 (by rfl) ⟨666522, by rfl⟩ : syracuseStep 1777393 = 1333045) B1333045
theorem B2105075 : Blo 1246441 2105075 := bstep (se 1 (by rfl) ⟨1578806, by rfl⟩ : syracuseStep 2105075 = 3157613) B3157613
theorem B4734733 : Blo 1246441 4734733 := bstep (se 3 (by rfl) ⟨887762, by rfl⟩ : syracuseStep 4734733 = 1775525) B1775525
theorem B9469709 : Blo 1246441 9469709 := bstep (se 3 (by rfl) ⟨1775570, by rfl⟩ : syracuseStep 9469709 = 3551141) B3551141
theorem B2367299 : Blo 1246441 2367299 := bstep (se 1 (by rfl) ⟨1775474, by rfl⟩ : syracuseStep 2367299 = 3550949) B3550949
theorem B4210541 : Blo 1246441 4210541 := bstep (se 3 (by rfl) ⟨789476, by rfl⟩ : syracuseStep 4210541 = 1578953) B1578953
theorem B2105203 : Blo 1246441 2105203 := bstep (se 1 (by rfl) ⟨1578902, by rfl⟩ : syracuseStep 2105203 = 3157805) B3157805
theorem B4210595 : Blo 1246441 4210595 := bstep (se 1 (by rfl) ⟨3157946, by rfl⟩ : syracuseStep 4210595 = 6315893) B6315893
theorem B3997649 : Blo 1246441 3997649 := bstep (se 2 (by rfl) ⟨1499118, by rfl⟩ : syracuseStep 3997649 = 2998237) B2998237
theorem B43196485 : Blo 1246441 43196485 := bstep (se 4 (by rfl) ⟨4049670, by rfl⟩ : syracuseStep 43196485 = 8099341) B8099341
theorem B2105419 : Blo 1246441 2105419 := bstep (se 1 (by rfl) ⟨1579064, by rfl⟩ : syracuseStep 2105419 = 3158129) B3158129
theorem B20242507 : Blo 1246441 20242507 := bstep (se 1 (by rfl) ⟨15181880, by rfl⟩ : syracuseStep 20242507 = 30363761) B30363761
theorem B1441963 : Blo 1246441 1441963 := bstep (se 1 (by rfl) ⟨1081472, by rfl⟩ : syracuseStep 1441963 = 2162945) B2162945
theorem B2105561 : Blo 1246441 2105561 := bstep (se 2 (by rfl) ⟨789585, by rfl⟩ : syracuseStep 2105561 = 1579171) B1579171
theorem B2367731 : Blo 1246441 2367731 := bstep (se 1 (by rfl) ⟨1775798, by rfl⟩ : syracuseStep 2367731 = 3551597) B3551597
theorem B2105689 : Blo 1246441 2105689 := bstep (se 2 (by rfl) ⟨789633, by rfl⟩ : syracuseStep 2105689 = 1579267) B1579267
theorem B10658141 : Blo 1246441 10658141 := bstep (se 3 (by rfl) ⟨1998401, by rfl⟩ : syracuseStep 10658141 = 3996803) B3996803
theorem B5693789 : Blo 1246441 5693789 := bstep (se 3 (by rfl) ⟨1067585, by rfl⟩ : syracuseStep 5693789 = 2135171) B2135171
theorem B2367883 : Blo 1246441 2367883 := bstep (se 1 (by rfl) ⟨1775912, by rfl⟩ : syracuseStep 2367883 = 3551825) B3551825
theorem B5325277 : Blo 1246441 5325277 := bstep (se 3 (by rfl) ⟨998489, by rfl⟩ : syracuseStep 5325277 = 1996979) B1996979
theorem B5997149 : Blo 1246441 5997149 := bstep (se 3 (by rfl) ⟨1124465, by rfl⟩ : syracuseStep 5997149 = 2248931) B2248931
theorem B4211351 : Blo 1246441 4211351 := bstep (se 1 (by rfl) ⟨3158513, by rfl⟩ : syracuseStep 4211351 = 6317027) B6317027
theorem B4735691 : Blo 1246441 4735691 := bstep (se 1 (by rfl) ⟨3551768, by rfl⟩ : syracuseStep 4735691 = 7103537) B7103537
theorem B9470681 : Blo 1246441 9470681 := bstep (se 2 (by rfl) ⟨3551505, by rfl⟩ : syracuseStep 9470681 = 7103011) B7103011
theorem B4735705 : Blo 1246441 4735705 := bstep (se 2 (by rfl) ⟨1775889, by rfl⟩ : syracuseStep 4735705 = 3551779) B3551779
theorem B2368217 : Blo 1246441 2368217 := bstep (se 2 (by rfl) ⟨888081, by rfl⟩ : syracuseStep 2368217 = 1776163) B1776163
theorem B4621079 : Blo 1246441 4621079 := bstep (se 1 (by rfl) ⟨3465809, by rfl⟩ : syracuseStep 4621079 = 6931619) B6931619
theorem B6316865 : Blo 1246441 6316865 := bstep (se 2 (by rfl) ⟨2368824, by rfl⟩ : syracuseStep 6316865 = 4737649) B4737649
theorem B5473099 : Blo 1246441 5473099 := bstep (se 1 (by rfl) ⟨4104824, by rfl⟩ : syracuseStep 5473099 = 8209649) B8209649
theorem B2278219 : Blo 1246441 2278219 := bstep (se 1 (by rfl) ⟨1708664, by rfl⟩ : syracuseStep 2278219 = 3417329) B3417329
theorem B2106263 : Blo 1246441 2106263 := bstep (se 1 (by rfl) ⟨1579697, by rfl⟩ : syracuseStep 2106263 = 3159395) B3159395
theorem B5129153 : Blo 1246441 5129153 := bstep (se 2 (by rfl) ⟨1923432, by rfl⟩ : syracuseStep 5129153 = 3846865) B3846865
theorem B2106391 : Blo 1246441 2106391 := bstep (se 1 (by rfl) ⟨1579793, by rfl⟩ : syracuseStep 2106391 = 3159587) B3159587
theorem B10658891 : Blo 1246441 10658891 := bstep (se 1 (by rfl) ⟨7994168, by rfl⟩ : syracuseStep 10658891 = 15988337) B15988337
theorem B4211891 : Blo 1246441 4211891 := bstep (se 1 (by rfl) ⟨3158918, by rfl⟩ : syracuseStep 4211891 = 6317837) B6317837
theorem B1246443 : Blo 1246441 1246443 := bstep (se 1 (by rfl) ⟨934832, by rfl⟩ : syracuseStep 1246443 = 1869665) B1869665
theorem B1246455 : Blo 1246441 1246455 := bstep (se 1 (by rfl) ⟨934841, by rfl⟩ : syracuseStep 1246455 = 1869683) B1869683
theorem B9479429 : Blo 1246441 9479429 := bstep (se 4 (by rfl) ⟨888696, by rfl⟩ : syracuseStep 9479429 = 1777393) B1777393
theorem B1246475 : Blo 1246441 1246475 := bstep (se 1 (by rfl) ⟨934856, by rfl⟩ : syracuseStep 1246475 = 1869713) B1869713
theorem B1246487 : Blo 1246441 1246487 := bstep (se 1 (by rfl) ⟨934865, by rfl⟩ : syracuseStep 1246487 = 1869731) B1869731
theorem B1246507 : Blo 1246441 1246507 := bstep (se 1 (by rfl) ⟨934880, by rfl⟩ : syracuseStep 1246507 = 1869761) B1869761
theorem B1246519 : Blo 1246441 1246519 := bstep (se 1 (by rfl) ⟨934889, by rfl⟩ : syracuseStep 1246519 = 1869779) B1869779
theorem B1246539 : Blo 1246441 1246539 := bstep (se 1 (by rfl) ⟨934904, by rfl⟩ : syracuseStep 1246539 = 1869809) B1869809
theorem B1246551 : Blo 1246441 1246551 := bstep (se 1 (by rfl) ⟨934913, by rfl⟩ : syracuseStep 1246551 = 1869827) B1869827
theorem B2368855 : Blo 1246441 2368855 := bstep (se 1 (by rfl) ⟨1776641, by rfl⟩ : syracuseStep 2368855 = 3553283) B3553283
theorem B1246571 : Blo 1246441 1246571 := bstep (se 1 (by rfl) ⟨934928, by rfl⟩ : syracuseStep 1246571 = 1869857) B1869857
theorem B1246583 : Blo 1246441 1246583 := bstep (se 1 (by rfl) ⟨934937, by rfl⟩ : syracuseStep 1246583 = 1869875) B1869875
theorem B1246603 : Blo 1246441 1246603 := bstep (se 1 (by rfl) ⟨934952, by rfl⟩ : syracuseStep 1246603 = 1869905) B1869905
theorem B5989783 : Blo 1246441 5989783 := bstep (se 1 (by rfl) ⟨4492337, by rfl⟩ : syracuseStep 5989783 = 8984675) B8984675
theorem B1246615 : Blo 1246441 1246615 := bstep (se 1 (by rfl) ⟨934961, by rfl⟩ : syracuseStep 1246615 = 1869923) B1869923
theorem B5686679 : Blo 1246441 5686679 := bstep (se 1 (by rfl) ⟨4265009, by rfl⟩ : syracuseStep 5686679 = 8530019) B8530019
theorem B1246635 : Blo 1246441 1246635 := bstep (se 1 (by rfl) ⟨934976, by rfl⟩ : syracuseStep 1246635 = 1869953) B1869953
theorem B1246647 : Blo 1246441 1246647 := bstep (se 1 (by rfl) ⟨934985, by rfl⟩ : syracuseStep 1246647 = 1869971) B1869971
theorem B4212161 : Blo 1246441 4212161 := bstep (se 2 (by rfl) ⟨1579560, by rfl⟩ : syracuseStep 4212161 = 3159121) B3159121
theorem B1246667 : Blo 1246441 1246667 := bstep (se 1 (by rfl) ⟨935000, by rfl⟩ : syracuseStep 1246667 = 1870001) B1870001
theorem B1246679 : Blo 1246441 1246679 := bstep (se 1 (by rfl) ⟨935009, by rfl⟩ : syracuseStep 1246679 = 1870019) B1870019
theorem B1246699 : Blo 1246441 1246699 := bstep (se 1 (by rfl) ⟨935024, by rfl⟩ : syracuseStep 1246699 = 1870049) B1870049
theorem B1246711 : Blo 1246441 1246711 := bstep (se 1 (by rfl) ⟨935033, by rfl⟩ : syracuseStep 1246711 = 1870067) B1870067
theorem B1246731 : Blo 1246441 1246731 := bstep (se 1 (by rfl) ⟨935048, by rfl⟩ : syracuseStep 1246731 = 1870097) B1870097
theorem B40437265 : Blo 1246441 40437265 := bstep (se 2 (by rfl) ⟨15163974, by rfl⟩ : syracuseStep 40437265 = 30327949) B30327949
theorem B6743569 : Blo 1246441 6743569 := bstep (se 2 (by rfl) ⟨2528838, by rfl⟩ : syracuseStep 6743569 = 5057677) B5057677
theorem B1246743 : Blo 1246441 1246743 := bstep (se 1 (by rfl) ⟨935057, by rfl⟩ : syracuseStep 1246743 = 1870115) B1870115
theorem B1402411 : Blo 1246441 1402411 := bstep (se 1 (by rfl) ⟨1051808, by rfl⟩ : syracuseStep 1402411 = 2103617) B2103617
theorem B1246763 : Blo 1246441 1246763 := bstep (se 1 (by rfl) ⟨935072, by rfl⟩ : syracuseStep 1246763 = 1870145) B1870145
theorem B5547565 : Blo 1246441 5547565 := bstep (se 3 (by rfl) ⟨1040168, by rfl⟩ : syracuseStep 5547565 = 2080337) B2080337
theorem B3155507 : Blo 1246441 3155507 := bstep (se 1 (by rfl) ⟨2366630, by rfl⟩ : syracuseStep 3155507 = 4733261) B4733261
theorem B1246775 : Blo 1246441 1246775 := bstep (se 1 (by rfl) ⟨935081, by rfl⟩ : syracuseStep 1246775 = 1870163) B1870163
theorem B1246795 : Blo 1246441 1246795 := bstep (se 1 (by rfl) ⟨935096, by rfl⟩ : syracuseStep 1246795 = 1870193) B1870193
theorem B1246807 : Blo 1246441 1246807 := bstep (se 1 (by rfl) ⟨935105, by rfl⟩ : syracuseStep 1246807 = 1870211) B1870211
theorem B1246827 : Blo 1246441 1246827 := bstep (se 1 (by rfl) ⟨935120, by rfl⟩ : syracuseStep 1246827 = 1870241) B1870241
theorem B1246839 : Blo 1246441 1246839 := bstep (se 1 (by rfl) ⟨935129, by rfl⟩ : syracuseStep 1246839 = 1870259) B1870259
theorem B34162307 : Blo 1246441 34162307 := bstep (se 1 (by rfl) ⟨25621730, by rfl⟩ : syracuseStep 34162307 = 51243461) B51243461
theorem B1246859 : Blo 1246441 1246859 := bstep (se 1 (by rfl) ⟨935144, by rfl⟩ : syracuseStep 1246859 = 1870289) B1870289
theorem B5400209 : Blo 1246441 5400209 := bstep (se 2 (by rfl) ⟨2025078, by rfl⟩ : syracuseStep 5400209 = 4050157) B4050157
theorem B1402519 : Blo 1246441 1402519 := bstep (se 1 (by rfl) ⟨1051889, by rfl⟩ : syracuseStep 1402519 = 2103779) B2103779
theorem B1246871 : Blo 1246441 1246871 := bstep (se 1 (by rfl) ⟨935153, by rfl⟩ : syracuseStep 1246871 = 1870307) B1870307
theorem B4736663 : Blo 1246441 4736663 := bstep (se 1 (by rfl) ⟨3552497, by rfl⟩ : syracuseStep 4736663 = 7104995) B7104995
theorem B1246891 : Blo 1246441 1246891 := bstep (se 1 (by rfl) ⟨935168, by rfl⟩ : syracuseStep 1246891 = 1870337) B1870337
theorem B1246903 : Blo 1246441 1246903 := bstep (se 1 (by rfl) ⟨935177, by rfl⟩ : syracuseStep 1246903 = 1870355) B1870355
theorem B1246923 : Blo 1246441 1246923 := bstep (se 1 (by rfl) ⟨935192, by rfl⟩ : syracuseStep 1246923 = 1870385) B1870385
theorem B8988365 : Blo 1246441 8988365 := bstep (se 3 (by rfl) ⟨1685318, by rfl⟩ : syracuseStep 8988365 = 3370637) B3370637
theorem B1246935 : Blo 1246441 1246935 := bstep (se 1 (by rfl) ⟨935201, by rfl⟩ : syracuseStep 1246935 = 1870403) B1870403
theorem B1246955 : Blo 1246441 1246955 := bstep (se 1 (by rfl) ⟨935216, by rfl⟩ : syracuseStep 1246955 = 1870433) B1870433
theorem B1246967 : Blo 1246441 1246967 := bstep (se 1 (by rfl) ⟨935225, by rfl⟩ : syracuseStep 1246967 = 1870451) B1870451
theorem B1246987 : Blo 1246441 1246987 := bstep (se 1 (by rfl) ⟨935240, by rfl⟩ : syracuseStep 1246987 = 1870481) B1870481
theorem B1246999 : Blo 1246441 1246999 := bstep (se 1 (by rfl) ⟨935249, by rfl⟩ : syracuseStep 1246999 = 1870499) B1870499
theorem B1247019 : Blo 1246441 1247019 := bstep (se 1 (by rfl) ⟨935264, by rfl⟩ : syracuseStep 1247019 = 1870529) B1870529
theorem B1247031 : Blo 1246441 1247031 := bstep (se 1 (by rfl) ⟨935273, by rfl⟩ : syracuseStep 1247031 = 1870547) B1870547
theorem B1402699 : Blo 1246441 1402699 := bstep (se 1 (by rfl) ⟨1052024, by rfl⟩ : syracuseStep 1402699 = 2104049) B2104049
theorem B1247051 : Blo 1246441 1247051 := bstep (se 1 (by rfl) ⟨935288, by rfl⟩ : syracuseStep 1247051 = 1870577) B1870577
theorem B5769035 : Blo 1246441 5769035 := bstep (se 1 (by rfl) ⟨4326776, by rfl⟩ : syracuseStep 5769035 = 8653553) B8653553
theorem B1247063 : Blo 1246441 1247063 := bstep (se 1 (by rfl) ⟨935297, by rfl⟩ : syracuseStep 1247063 = 1870595) B1870595
theorem B1247083 : Blo 1246441 1247083 := bstep (se 1 (by rfl) ⟨935312, by rfl⟩ : syracuseStep 1247083 = 1870625) B1870625
theorem B1247095 : Blo 1246441 1247095 := bstep (se 1 (by rfl) ⟨935321, by rfl⟩ : syracuseStep 1247095 = 1870643) B1870643
theorem B1869707 : Blo 1246441 1869707 := bstep (se 1 (by rfl) ⟨1402280, by rfl⟩ : syracuseStep 1869707 = 2804561) B2804561
theorem B1247115 : Blo 1246441 1247115 := bstep (se 1 (by rfl) ⟨935336, by rfl⟩ : syracuseStep 1247115 = 1870673) B1870673
theorem B1869719 : Blo 1246441 1869719 := bstep (se 1 (by rfl) ⟨1402289, by rfl⟩ : syracuseStep 1869719 = 2804579) B2804579
theorem B1247127 : Blo 1246441 1247127 := bstep (se 1 (by rfl) ⟨935345, by rfl⟩ : syracuseStep 1247127 = 1870691) B1870691
theorem B1247147 : Blo 1246441 1247147 := bstep (se 1 (by rfl) ⟨935360, by rfl⟩ : syracuseStep 1247147 = 1870721) B1870721
theorem B1402807 : Blo 1246441 1402807 := bstep (se 1 (by rfl) ⟨1052105, by rfl⟩ : syracuseStep 1402807 = 2104211) B2104211
theorem B1247159 : Blo 1246441 1247159 := bstep (se 1 (by rfl) ⟨935369, by rfl⟩ : syracuseStep 1247159 = 1870739) B1870739
theorem B1247179 : Blo 1246441 1247179 := bstep (se 1 (by rfl) ⟨935384, by rfl⟩ : syracuseStep 1247179 = 1870769) B1870769
theorem B1247191 : Blo 1246441 1247191 := bstep (se 1 (by rfl) ⟨935393, by rfl⟩ : syracuseStep 1247191 = 1870787) B1870787
theorem B1869785 : Blo 1246441 1869785 := bstep (se 2 (by rfl) ⟨701169, by rfl⟩ : syracuseStep 1869785 = 1402339) B1402339
theorem B4212701 : Blo 1246441 4212701 := bstep (se 3 (by rfl) ⟨789881, by rfl⟩ : syracuseStep 4212701 = 1579763) B1579763
theorem B1247211 : Blo 1246441 1247211 := bstep (se 1 (by rfl) ⟨935408, by rfl⟩ : syracuseStep 1247211 = 1870817) B1870817
theorem B1247223 : Blo 1246441 1247223 := bstep (se 1 (by rfl) ⟨935417, by rfl⟩ : syracuseStep 1247223 = 1870835) B1870835
theorem B1247243 : Blo 1246441 1247243 := bstep (se 1 (by rfl) ⟨935432, by rfl⟩ : syracuseStep 1247243 = 1870865) B1870865
theorem B2402315 : Blo 1246441 2402315 := bstep (se 1 (by rfl) ⟨1801736, by rfl⟩ : syracuseStep 2402315 = 3603473) B3603473
theorem B1247255 : Blo 1246441 1247255 := bstep (se 1 (by rfl) ⟨935441, by rfl⟩ : syracuseStep 1247255 = 1870883) B1870883
theorem B1247275 : Blo 1246441 1247275 := bstep (se 1 (by rfl) ⟨935456, by rfl⟩ : syracuseStep 1247275 = 1870913) B1870913
theorem B1247287 : Blo 1246441 1247287 := bstep (se 1 (by rfl) ⟨935465, by rfl⟩ : syracuseStep 1247287 = 1870931) B1870931
theorem B1869899 : Blo 1246441 1869899 := bstep (se 1 (by rfl) ⟨1402424, by rfl⟩ : syracuseStep 1869899 = 2804849) B2804849
theorem B3156043 : Blo 1246441 3156043 := bstep (se 1 (by rfl) ⟨2367032, by rfl⟩ : syracuseStep 3156043 = 4734065) B4734065
theorem B1247307 : Blo 1246441 1247307 := bstep (se 1 (by rfl) ⟨935480, by rfl⟩ : syracuseStep 1247307 = 1870961) B1870961
theorem B1869911 : Blo 1246441 1869911 := bstep (se 1 (by rfl) ⟨1402433, by rfl⟩ : syracuseStep 1869911 = 2804867) B2804867
theorem B1247319 : Blo 1246441 1247319 := bstep (se 1 (by rfl) ⟨935489, by rfl⟩ : syracuseStep 1247319 = 1870979) B1870979
theorem B1402987 : Blo 1246441 1402987 := bstep (se 1 (by rfl) ⟨1052240, by rfl⟩ : syracuseStep 1402987 = 2104481) B2104481
theorem B1247339 : Blo 1246441 1247339 := bstep (se 1 (by rfl) ⟨935504, by rfl⟩ : syracuseStep 1247339 = 1871009) B1871009
theorem B1247351 : Blo 1246441 1247351 := bstep (se 1 (by rfl) ⟨935513, by rfl⟩ : syracuseStep 1247351 = 1871027) B1871027
theorem B21301379 : Blo 1246441 21301379 := bstep (se 1 (by rfl) ⟨15976034, by rfl⟩ : syracuseStep 21301379 = 31952069) B31952069
theorem B1247371 : Blo 1246441 1247371 := bstep (se 1 (by rfl) ⟨935528, by rfl⟩ : syracuseStep 1247371 = 1871057) B1871057
theorem B2369675 : Blo 1246441 2369675 := bstep (se 1 (by rfl) ⟨1777256, by rfl⟩ : syracuseStep 2369675 = 3554513) B3554513
theorem B1247383 : Blo 1246441 1247383 := bstep (se 1 (by rfl) ⟨935537, by rfl⟩ : syracuseStep 1247383 = 1871075) B1871075
theorem B1869977 : Blo 1246441 1869977 := bstep (se 2 (by rfl) ⟨701241, by rfl⟩ : syracuseStep 1869977 = 1402483) B1402483
theorem B1247403 : Blo 1246441 1247403 := bstep (se 1 (by rfl) ⟨935552, by rfl⟩ : syracuseStep 1247403 = 1871105) B1871105
theorem B1247415 : Blo 1246441 1247415 := bstep (se 1 (by rfl) ⟨935561, by rfl⟩ : syracuseStep 1247415 = 1871123) B1871123
theorem B2369729 : Blo 1246441 2369729 := bstep (se 2 (by rfl) ⟨888648, by rfl⟩ : syracuseStep 2369729 = 1777297) B1777297
theorem B1247435 : Blo 1246441 1247435 := bstep (se 1 (by rfl) ⟨935576, by rfl⟩ : syracuseStep 1247435 = 1871153) B1871153
theorem B1403095 : Blo 1246441 1403095 := bstep (se 1 (by rfl) ⟨1052321, by rfl⟩ : syracuseStep 1403095 = 2104643) B2104643
theorem B1247447 : Blo 1246441 1247447 := bstep (se 1 (by rfl) ⟨935585, by rfl⟩ : syracuseStep 1247447 = 1871171) B1871171
theorem B3156185 : Blo 1246441 3156185 := bstep (se 2 (by rfl) ⟨1183569, by rfl⟩ : syracuseStep 3156185 = 2367139) B2367139
theorem B1247467 : Blo 1246441 1247467 := bstep (se 1 (by rfl) ⟨935600, by rfl⟩ : syracuseStep 1247467 = 1871201) B1871201
theorem B1247479 : Blo 1246441 1247479 := bstep (se 1 (by rfl) ⟨935609, by rfl⟩ : syracuseStep 1247479 = 1871219) B1871219
theorem B1870091 : Blo 1246441 1870091 := bstep (se 1 (by rfl) ⟨1402568, by rfl⟩ : syracuseStep 1870091 = 2805137) B2805137
theorem B1247499 : Blo 1246441 1247499 := bstep (se 1 (by rfl) ⟨935624, by rfl⟩ : syracuseStep 1247499 = 1871249) B1871249
theorem B1870103 : Blo 1246441 1870103 := bstep (se 1 (by rfl) ⟨1402577, by rfl⟩ : syracuseStep 1870103 = 2805155) B2805155
theorem B1247511 : Blo 1246441 1247511 := bstep (se 1 (by rfl) ⟨935633, by rfl⟩ : syracuseStep 1247511 = 1871267) B1871267
theorem B1247531 : Blo 1246441 1247531 := bstep (se 1 (by rfl) ⟨935648, by rfl⟩ : syracuseStep 1247531 = 1871297) B1871297
theorem B3549491 : Blo 1246441 3549491 := bstep (se 1 (by rfl) ⟨2662118, by rfl⟩ : syracuseStep 3549491 = 5324237) B5324237
theorem B1247543 : Blo 1246441 1247543 := bstep (se 1 (by rfl) ⟨935657, by rfl⟩ : syracuseStep 1247543 = 1871315) B1871315
theorem B1247563 : Blo 1246441 1247563 := bstep (se 1 (by rfl) ⟨935672, by rfl⟩ : syracuseStep 1247563 = 1871345) B1871345
theorem B1247575 : Blo 1246441 1247575 := bstep (se 1 (by rfl) ⟨935681, by rfl⟩ : syracuseStep 1247575 = 1871363) B1871363
theorem B1870169 : Blo 1246441 1870169 := bstep (se 2 (by rfl) ⟨701313, by rfl⟩ : syracuseStep 1870169 = 1402627) B1402627
theorem B4802905 : Blo 1246441 4802905 := bstep (se 2 (by rfl) ⟨1801089, by rfl⟩ : syracuseStep 4802905 = 3602179) B3602179
theorem B1247595 : Blo 1246441 1247595 := bstep (se 1 (by rfl) ⟨935696, by rfl⟩ : syracuseStep 1247595 = 1871393) B1871393
theorem B1247607 : Blo 1246441 1247607 := bstep (se 1 (by rfl) ⟨935705, by rfl⟩ : syracuseStep 1247607 = 1871411) B1871411
theorem B1403275 : Blo 1246441 1403275 := bstep (se 1 (by rfl) ⟨1052456, by rfl⟩ : syracuseStep 1403275 = 2104913) B2104913
theorem B1247627 : Blo 1246441 1247627 := bstep (se 1 (by rfl) ⟨935720, by rfl⟩ : syracuseStep 1247627 = 1871441) B1871441
theorem B1247639 : Blo 1246441 1247639 := bstep (se 1 (by rfl) ⟨935729, by rfl⟩ : syracuseStep 1247639 = 1871459) B1871459
theorem B1247659 : Blo 1246441 1247659 := bstep (se 1 (by rfl) ⟨935744, by rfl⟩ : syracuseStep 1247659 = 1871489) B1871489
theorem B1247671 : Blo 1246441 1247671 := bstep (se 1 (by rfl) ⟨935753, by rfl⟩ : syracuseStep 1247671 = 1871507) B1871507
theorem B1870283 : Blo 1246441 1870283 := bstep (se 1 (by rfl) ⟨1402712, by rfl⟩ : syracuseStep 1870283 = 2805425) B2805425
theorem B1247691 : Blo 1246441 1247691 := bstep (se 1 (by rfl) ⟨935768, by rfl⟩ : syracuseStep 1247691 = 1871537) B1871537
theorem B1870295 : Blo 1246441 1870295 := bstep (se 1 (by rfl) ⟨1402721, by rfl⟩ : syracuseStep 1870295 = 2805443) B2805443
theorem B1247703 : Blo 1246441 1247703 := bstep (se 1 (by rfl) ⟨935777, by rfl⟩ : syracuseStep 1247703 = 1871555) B1871555
theorem B1247723 : Blo 1246441 1247723 := bstep (se 1 (by rfl) ⟨935792, by rfl⟩ : syracuseStep 1247723 = 1871585) B1871585
theorem B1403383 : Blo 1246441 1403383 := bstep (se 1 (by rfl) ⟨1052537, by rfl⟩ : syracuseStep 1403383 = 2105075) B2105075
theorem B1247735 : Blo 1246441 1247735 := bstep (se 1 (by rfl) ⟨935801, by rfl⟩ : syracuseStep 1247735 = 1871603) B1871603
theorem B1247755 : Blo 1246441 1247755 := bstep (se 1 (by rfl) ⟨935816, by rfl⟩ : syracuseStep 1247755 = 1871633) B1871633
theorem B35965457 : Blo 1246441 35965457 := bstep (se 2 (by rfl) ⟨13487046, by rfl⟩ : syracuseStep 35965457 = 26974093) B26974093
theorem B1247767 : Blo 1246441 1247767 := bstep (se 1 (by rfl) ⟨935825, by rfl⟩ : syracuseStep 1247767 = 1871651) B1871651
theorem B1870361 : Blo 1246441 1870361 := bstep (se 2 (by rfl) ⟨701385, by rfl⟩ : syracuseStep 1870361 = 1402771) B1402771
theorem B1247787 : Blo 1246441 1247787 := bstep (se 1 (by rfl) ⟨935840, by rfl⟩ : syracuseStep 1247787 = 1871681) B1871681
theorem B1247799 : Blo 1246441 1247799 := bstep (se 1 (by rfl) ⟨935849, by rfl⟩ : syracuseStep 1247799 = 1871699) B1871699
theorem B1247819 : Blo 1246441 1247819 := bstep (se 1 (by rfl) ⟨935864, by rfl⟩ : syracuseStep 1247819 = 1871729) B1871729
theorem B1247831 : Blo 1246441 1247831 := bstep (se 1 (by rfl) ⟨935873, by rfl⟩ : syracuseStep 1247831 = 1871747) B1871747
theorem B1247851 : Blo 1246441 1247851 := bstep (se 1 (by rfl) ⟨935888, by rfl⟩ : syracuseStep 1247851 = 1871777) B1871777
theorem B1247863 : Blo 1246441 1247863 := bstep (se 1 (by rfl) ⟨935897, by rfl⟩ : syracuseStep 1247863 = 1871795) B1871795
theorem B1870475 : Blo 1246441 1870475 := bstep (se 1 (by rfl) ⟨1402856, by rfl⟩ : syracuseStep 1870475 = 2805713) B2805713
theorem B2665099 : Blo 1246441 2665099 := bstep (se 1 (by rfl) ⟨1998824, by rfl⟩ : syracuseStep 2665099 = 3997649) B3997649
theorem B1247883 : Blo 1246441 1247883 := bstep (se 1 (by rfl) ⟨935912, by rfl⟩ : syracuseStep 1247883 = 1871825) B1871825
theorem B1870487 : Blo 1246441 1870487 := bstep (se 1 (by rfl) ⟨1402865, by rfl⟩ : syracuseStep 1870487 = 2805731) B2805731
theorem B1247895 : Blo 1246441 1247895 := bstep (se 1 (by rfl) ⟨935921, by rfl⟩ : syracuseStep 1247895 = 1871843) B1871843
theorem B1403563 : Blo 1246441 1403563 := bstep (se 1 (by rfl) ⟨1052672, by rfl⟩ : syracuseStep 1403563 = 2105345) B2105345
theorem B1247915 : Blo 1246441 1247915 := bstep (se 1 (by rfl) ⟨935936, by rfl⟩ : syracuseStep 1247915 = 1871873) B1871873
theorem B10660531 : Blo 1246441 10660531 := bstep (se 1 (by rfl) ⟨7995398, by rfl⟩ : syracuseStep 10660531 = 15990797) B15990797
theorem B1247927 : Blo 1246441 1247927 := bstep (se 1 (by rfl) ⟨935945, by rfl⟩ : syracuseStep 1247927 = 1871891) B1871891
theorem B1247947 : Blo 1246441 1247947 := bstep (se 1 (by rfl) ⟨935960, by rfl⟩ : syracuseStep 1247947 = 1871921) B1871921
theorem B1247959 : Blo 1246441 1247959 := bstep (se 1 (by rfl) ⟨935969, by rfl⟩ : syracuseStep 1247959 = 1871939) B1871939
theorem B1870553 : Blo 1246441 1870553 := bstep (se 2 (by rfl) ⟨701457, by rfl⟩ : syracuseStep 1870553 = 1402915) B1402915
theorem B6318809 : Blo 1246441 6318809 := bstep (se 2 (by rfl) ⟨2369553, by rfl⟩ : syracuseStep 6318809 = 4739107) B4739107
theorem B1247979 : Blo 1246441 1247979 := bstep (se 1 (by rfl) ⟨935984, by rfl⟩ : syracuseStep 1247979 = 1871969) B1871969
theorem B1247991 : Blo 1246441 1247991 := bstep (se 1 (by rfl) ⟨935993, by rfl⟩ : syracuseStep 1247991 = 1871987) B1871987
theorem B1248011 : Blo 1246441 1248011 := bstep (se 1 (by rfl) ⟨936008, by rfl⟩ : syracuseStep 1248011 = 1872017) B1872017
theorem B1403671 : Blo 1246441 1403671 := bstep (se 1 (by rfl) ⟨1052753, by rfl⟩ : syracuseStep 1403671 = 2105507) B2105507
theorem B1248023 : Blo 1246441 1248023 := bstep (se 1 (by rfl) ⟨936017, by rfl⟩ : syracuseStep 1248023 = 1872035) B1872035
theorem B1248043 : Blo 1246441 1248043 := bstep (se 1 (by rfl) ⟨936032, by rfl⟩ : syracuseStep 1248043 = 1872065) B1872065
theorem B1248055 : Blo 1246441 1248055 := bstep (se 1 (by rfl) ⟨936041, by rfl⟩ : syracuseStep 1248055 = 1872083) B1872083
theorem B1870667 : Blo 1246441 1870667 := bstep (se 1 (by rfl) ⟨1403000, by rfl⟩ : syracuseStep 1870667 = 2806001) B2806001
theorem B1248075 : Blo 1246441 1248075 := bstep (se 1 (by rfl) ⟨936056, by rfl⟩ : syracuseStep 1248075 = 1872113) B1872113
theorem B1870679 : Blo 1246441 1870679 := bstep (se 1 (by rfl) ⟨1403009, by rfl⟩ : syracuseStep 1870679 = 2806019) B2806019
theorem B1248087 : Blo 1246441 1248087 := bstep (se 1 (by rfl) ⟨936065, by rfl⟩ : syracuseStep 1248087 = 1872131) B1872131
theorem B1248107 : Blo 1246441 1248107 := bstep (se 1 (by rfl) ⟨936080, by rfl⟩ : syracuseStep 1248107 = 1872161) B1872161
theorem B1248119 : Blo 1246441 1248119 := bstep (se 1 (by rfl) ⟨936089, by rfl⟩ : syracuseStep 1248119 = 1872179) B1872179
theorem B4737923 : Blo 1246441 4737923 := bstep (se 1 (by rfl) ⟨3553442, by rfl⟩ : syracuseStep 4737923 = 7106885) B7106885
theorem B1248139 : Blo 1246441 1248139 := bstep (se 1 (by rfl) ⟨936104, by rfl⟩ : syracuseStep 1248139 = 1872209) B1872209
theorem B1248151 : Blo 1246441 1248151 := bstep (se 1 (by rfl) ⟨936113, by rfl⟩ : syracuseStep 1248151 = 1872227) B1872227
theorem B2804633 : Blo 1246441 2804633 := bstep (se 2 (by rfl) ⟨1051737, by rfl⟩ : syracuseStep 2804633 = 2103475) B2103475
theorem B1870745 : Blo 1246441 1870745 := bstep (se 2 (by rfl) ⟨701529, by rfl⟩ : syracuseStep 1870745 = 1403059) B1403059
theorem B1248171 : Blo 1246441 1248171 := bstep (se 1 (by rfl) ⟨936128, by rfl⟩ : syracuseStep 1248171 = 1872257) B1872257
theorem B1248183 : Blo 1246441 1248183 := bstep (se 1 (by rfl) ⟨936137, by rfl⟩ : syracuseStep 1248183 = 1872275) B1872275
theorem B1403851 : Blo 1246441 1403851 := bstep (se 1 (by rfl) ⟨1052888, by rfl⟩ : syracuseStep 1403851 = 2105777) B2105777
theorem B1248203 : Blo 1246441 1248203 := bstep (se 1 (by rfl) ⟨936152, by rfl⟩ : syracuseStep 1248203 = 1872305) B1872305
theorem B2845655 : Blo 1246441 2845655 := bstep (se 1 (by rfl) ⟨2134241, by rfl⟩ : syracuseStep 2845655 = 4268483) B4268483
theorem B1248215 : Blo 1246441 1248215 := bstep (se 1 (by rfl) ⟨936161, by rfl⟩ : syracuseStep 1248215 = 1872323) B1872323
theorem B1248235 : Blo 1246441 1248235 := bstep (se 1 (by rfl) ⟨936176, by rfl⟩ : syracuseStep 1248235 = 1872353) B1872353
theorem B2804723 : Blo 1246441 2804723 := bstep (se 1 (by rfl) ⟨2103542, by rfl⟩ : syracuseStep 2804723 = 4207085) B4207085
theorem B1248247 : Blo 1246441 1248247 := bstep (se 1 (by rfl) ⟨936185, by rfl⟩ : syracuseStep 1248247 = 1872371) B1872371
theorem B1870859 : Blo 1246441 1870859 := bstep (se 1 (by rfl) ⟨1403144, by rfl⟩ : syracuseStep 1870859 = 2806289) B2806289
theorem B1248267 : Blo 1246441 1248267 := bstep (se 1 (by rfl) ⟨936200, by rfl⟩ : syracuseStep 1248267 = 1872401) B1872401
theorem B2804759 : Blo 1246441 2804759 := bstep (se 1 (by rfl) ⟨2103569, by rfl⟩ : syracuseStep 2804759 = 4207139) B4207139
theorem B3157015 : Blo 1246441 3157015 := bstep (se 1 (by rfl) ⟨2367761, by rfl⟩ : syracuseStep 3157015 = 4735523) B4735523
theorem B1895449 : Blo 1246441 1895449 := bstep (se 2 (by rfl) ⟨710793, by rfl⟩ : syracuseStep 1895449 = 1421587) B1421587
theorem B1870871 : Blo 1246441 1870871 := bstep (se 1 (by rfl) ⟨1403153, by rfl⟩ : syracuseStep 1870871 = 2806307) B2806307
theorem B1248279 : Blo 1246441 1248279 := bstep (se 1 (by rfl) ⟨936209, by rfl⟩ : syracuseStep 1248279 = 1872419) B1872419
theorem B1248299 : Blo 1246441 1248299 := bstep (se 1 (by rfl) ⟨936224, by rfl⟩ : syracuseStep 1248299 = 1872449) B1872449
theorem B1281079 : Blo 1246441 1281079 := bstep (se 1 (by rfl) ⟨960809, by rfl⟩ : syracuseStep 1281079 = 1921619) B1921619
theorem B1403959 : Blo 1246441 1403959 := bstep (se 1 (by rfl) ⟨1052969, by rfl⟩ : syracuseStep 1403959 = 2105939) B2105939
theorem B1248311 : Blo 1246441 1248311 := bstep (se 1 (by rfl) ⟨936233, by rfl⟩ : syracuseStep 1248311 = 1872467) B1872467
theorem B2247755 : Blo 1246441 2247755 := bstep (se 1 (by rfl) ⟨1685816, by rfl⟩ : syracuseStep 2247755 = 3371633) B3371633
theorem B1248331 : Blo 1246441 1248331 := bstep (se 1 (by rfl) ⟨936248, by rfl⟩ : syracuseStep 1248331 = 1872497) B1872497
theorem B1870937 : Blo 1246441 1870937 := bstep (se 2 (by rfl) ⟨701601, by rfl⟩ : syracuseStep 1870937 = 1403203) B1403203
theorem B2665561 : Blo 1246441 2665561 := bstep (se 2 (by rfl) ⟨999585, by rfl⟩ : syracuseStep 2665561 = 1999171) B1999171
theorem B1248343 : Blo 1246441 1248343 := bstep (se 1 (by rfl) ⟨936257, by rfl⟩ : syracuseStep 1248343 = 1872515) B1872515
theorem B1248363 : Blo 1246441 1248363 := bstep (se 1 (by rfl) ⟨936272, by rfl⟩ : syracuseStep 1248363 = 1872545) B1872545
theorem B1248375 : Blo 1246441 1248375 := bstep (se 1 (by rfl) ⟨936281, by rfl⟩ : syracuseStep 1248375 = 1872563) B1872563
theorem B1248395 : Blo 1246441 1248395 := bstep (se 1 (by rfl) ⟨936296, by rfl⟩ : syracuseStep 1248395 = 1872593) B1872593
theorem B1248407 : Blo 1246441 1248407 := bstep (se 1 (by rfl) ⟨936305, by rfl⟩ : syracuseStep 1248407 = 1872611) B1872611
theorem B1248427 : Blo 1246441 1248427 := bstep (se 1 (by rfl) ⟨936320, by rfl⟩ : syracuseStep 1248427 = 1872641) B1872641
theorem B1248439 : Blo 1246441 1248439 := bstep (se 1 (by rfl) ⟨936329, by rfl⟩ : syracuseStep 1248439 = 1872659) B1872659
theorem B2804939 : Blo 1246441 2804939 := bstep (se 1 (by rfl) ⟨2103704, by rfl⟩ : syracuseStep 2804939 = 4207409) B4207409
theorem B1871051 : Blo 1246441 1871051 := bstep (se 1 (by rfl) ⟨1403288, by rfl⟩ : syracuseStep 1871051 = 2806577) B2806577
theorem B1871063 : Blo 1246441 1871063 := bstep (se 1 (by rfl) ⟨1403297, by rfl⟩ : syracuseStep 1871063 = 2806595) B2806595
theorem B1404139 : Blo 1246441 1404139 := bstep (se 1 (by rfl) ⟨1053104, by rfl⟩ : syracuseStep 1404139 = 2106209) B2106209
theorem B2804993 : Blo 1246441 2804993 := bstep (se 2 (by rfl) ⟨1051872, by rfl⟩ : syracuseStep 2804993 = 2103745) B2103745
theorem B60738821 : Blo 1246441 60738821 := bstep (se 4 (by rfl) ⟨5694264, by rfl⟩ : syracuseStep 60738821 = 11388529) B11388529
theorem B1871129 : Blo 1246441 1871129 := bstep (se 2 (by rfl) ⟨701673, by rfl⟩ : syracuseStep 1871129 = 1403347) B1403347
theorem B3370291 : Blo 1246441 3370291 := bstep (se 1 (by rfl) ⟨2527718, by rfl⟩ : syracuseStep 3370291 = 5055437) B5055437
theorem B3288385 : Blo 1246441 3288385 := bstep (se 2 (by rfl) ⟨1233144, by rfl⟩ : syracuseStep 3288385 = 2466289) B2466289
theorem B1281367 : Blo 1246441 1281367 := bstep (se 1 (by rfl) ⟨961025, by rfl⟩ : syracuseStep 1281367 = 1922051) B1922051
theorem B1404247 : Blo 1246441 1404247 := bstep (se 1 (by rfl) ⟨1053185, by rfl⟩ : syracuseStep 1404247 = 2106371) B2106371
theorem B1871243 : Blo 1246441 1871243 := bstep (se 1 (by rfl) ⟨1403432, by rfl⟩ : syracuseStep 1871243 = 2806865) B2806865
theorem B5688721 : Blo 1246441 5688721 := bstep (se 2 (by rfl) ⟨2133270, by rfl⟩ : syracuseStep 5688721 = 4266541) B4266541
theorem B1871255 : Blo 1246441 1871255 := bstep (se 1 (by rfl) ⟨1403441, by rfl⟩ : syracuseStep 1871255 = 2806883) B2806883
theorem B1895833 : Blo 1246441 1895833 := bstep (se 2 (by rfl) ⟨710937, by rfl⟩ : syracuseStep 1895833 = 1421875) B1421875
theorem B3157451 : Blo 1246441 3157451 := bstep (se 1 (by rfl) ⟨2368088, by rfl⟩ : syracuseStep 3157451 = 4736177) B4736177
theorem B2805209 : Blo 1246441 2805209 := bstep (se 2 (by rfl) ⟨1051953, by rfl⟩ : syracuseStep 2805209 = 2103907) B2103907
theorem B1871321 : Blo 1246441 1871321 := bstep (se 2 (by rfl) ⟨701745, by rfl⟩ : syracuseStep 1871321 = 1403491) B1403491
theorem B1404427 : Blo 1246441 1404427 := bstep (se 1 (by rfl) ⟨1053320, by rfl⟩ : syracuseStep 1404427 = 2106641) B2106641
theorem B26996237 : Blo 1246441 26996237 := bstep (se 3 (by rfl) ⟨5061794, by rfl⟩ : syracuseStep 26996237 = 10123589) B10123589
theorem B2805299 : Blo 1246441 2805299 := bstep (se 1 (by rfl) ⟨2103974, by rfl⟩ : syracuseStep 2805299 = 4207949) B4207949
theorem B6155851 : Blo 1246441 6155851 := bstep (se 1 (by rfl) ⟨4616888, by rfl⟩ : syracuseStep 6155851 = 9233777) B9233777
theorem B1871435 : Blo 1246441 1871435 := bstep (se 1 (by rfl) ⟨1403576, by rfl⟩ : syracuseStep 1871435 = 2807153) B2807153
theorem B2805335 : Blo 1246441 2805335 := bstep (se 1 (by rfl) ⟨2104001, by rfl⟩ : syracuseStep 2805335 = 4208003) B4208003
theorem B1871447 : Blo 1246441 1871447 := bstep (se 1 (by rfl) ⟨1403585, by rfl⟩ : syracuseStep 1871447 = 2807171) B2807171
theorem B4804247 : Blo 1246441 4804247 := bstep (se 1 (by rfl) ⟨3603185, by rfl⟩ : syracuseStep 4804247 = 7206371) B7206371
theorem B1871513 : Blo 1246441 1871513 := bstep (se 2 (by rfl) ⟨701817, by rfl⟩ : syracuseStep 1871513 = 1403635) B1403635
theorem B2805515 : Blo 1246441 2805515 := bstep (se 1 (by rfl) ⟨2104136, by rfl⟩ : syracuseStep 2805515 = 4208273) B4208273
theorem B1871627 : Blo 1246441 1871627 := bstep (se 1 (by rfl) ⟨1403720, by rfl⟩ : syracuseStep 1871627 = 2807441) B2807441
theorem B1871639 : Blo 1246441 1871639 := bstep (se 1 (by rfl) ⟨1403729, by rfl⟩ : syracuseStep 1871639 = 2807459) B2807459
theorem B2805569 : Blo 1246441 2805569 := bstep (se 2 (by rfl) ⟨1052088, by rfl⟩ : syracuseStep 2805569 = 2104177) B2104177
theorem B3157825 : Blo 1246441 3157825 := bstep (se 2 (by rfl) ⟨1184184, by rfl⟩ : syracuseStep 3157825 = 2368369) B2368369
theorem B8998721 : Blo 1246441 8998721 := bstep (se 2 (by rfl) ⟨3374520, by rfl⟩ : syracuseStep 8998721 = 6749041) B6749041
theorem B1871705 : Blo 1246441 1871705 := bstep (se 2 (by rfl) ⟨701889, by rfl⟩ : syracuseStep 1871705 = 1403779) B1403779
theorem B1871819 : Blo 1246441 1871819 := bstep (se 1 (by rfl) ⟨1403864, by rfl⟩ : syracuseStep 1871819 = 2807729) B2807729
theorem B1871831 : Blo 1246441 1871831 := bstep (se 1 (by rfl) ⟨1403873, by rfl⟩ : syracuseStep 1871831 = 2807747) B2807747
theorem B34156505 : Blo 1246441 34156505 := bstep (se 2 (by rfl) ⟨12808689, by rfl⟩ : syracuseStep 34156505 = 25617379) B25617379
theorem B5328899 : Blo 1246441 5328899 := bstep (se 1 (by rfl) ⟨3996674, by rfl⟩ : syracuseStep 5328899 = 7993349) B7993349
theorem B9236497 : Blo 1246441 9236497 := bstep (se 2 (by rfl) ⟨3463686, by rfl⟩ : syracuseStep 9236497 = 6927373) B6927373
theorem B2805785 : Blo 1246441 2805785 := bstep (se 2 (by rfl) ⟨1052169, by rfl⟩ : syracuseStep 2805785 = 2104339) B2104339
theorem B1871897 : Blo 1246441 1871897 := bstep (se 2 (by rfl) ⟨701961, by rfl⟩ : syracuseStep 1871897 = 1403923) B1403923
theorem B9474083 : Blo 1246441 9474083 := bstep (se 1 (by rfl) ⟨7105562, by rfl⟩ : syracuseStep 9474083 = 14211125) B14211125
theorem B2805875 : Blo 1246441 2805875 := bstep (se 1 (by rfl) ⟨2104406, by rfl⟩ : syracuseStep 2805875 = 4208813) B4208813
theorem B1872011 : Blo 1246441 1872011 := bstep (se 1 (by rfl) ⟨1404008, by rfl⟩ : syracuseStep 1872011 = 2808017) B2808017
theorem B2805911 : Blo 1246441 2805911 := bstep (se 1 (by rfl) ⟨2104433, by rfl⟩ : syracuseStep 2805911 = 4208867) B4208867
theorem B1872023 : Blo 1246441 1872023 := bstep (se 1 (by rfl) ⟨1404017, by rfl⟩ : syracuseStep 1872023 = 2808035) B2808035
theorem B1872089 : Blo 1246441 1872089 := bstep (se 2 (by rfl) ⟨702033, by rfl⟩ : syracuseStep 1872089 = 1404067) B1404067
theorem B4264157 : Blo 1246441 4264157 := bstep (se 3 (by rfl) ⟨799529, by rfl⟩ : syracuseStep 4264157 = 1599059) B1599059
theorem B1331435 : Blo 1246441 1331435 := bstep (se 1 (by rfl) ⟨998576, by rfl⟩ : syracuseStep 1331435 = 1997153) B1997153
theorem B2699507 : Blo 1246441 2699507 := bstep (se 1 (by rfl) ⟨2024630, by rfl⟩ : syracuseStep 2699507 = 4049261) B4049261
theorem B3993907 : Blo 1246441 3993907 := bstep (se 1 (by rfl) ⟨2995430, by rfl⟩ : syracuseStep 3993907 = 5990861) B5990861
theorem B5058881 : Blo 1246441 5058881 := bstep (se 2 (by rfl) ⟨1897080, by rfl⟩ : syracuseStep 5058881 = 3794161) B3794161
theorem B4206923 : Blo 1246441 4206923 := bstep (se 1 (by rfl) ⟨3155192, by rfl⟩ : syracuseStep 4206923 = 6310385) B6310385
theorem B2806091 : Blo 1246441 2806091 := bstep (se 1 (by rfl) ⟨2104568, by rfl⟩ : syracuseStep 2806091 = 4209137) B4209137
theorem B1872203 : Blo 1246441 1872203 := bstep (se 1 (by rfl) ⟨1404152, by rfl⟩ : syracuseStep 1872203 = 2808305) B2808305
theorem B1872215 : Blo 1246441 1872215 := bstep (se 1 (by rfl) ⟨1404161, by rfl⟩ : syracuseStep 1872215 = 2808323) B2808323
theorem B6402397 : Blo 1246441 6402397 := bstep (se 3 (by rfl) ⟨1200449, by rfl⟩ : syracuseStep 6402397 = 2400899) B2400899
theorem B2806145 : Blo 1246441 2806145 := bstep (se 2 (by rfl) ⟨1052304, by rfl⟩ : syracuseStep 2806145 = 2104609) B2104609
theorem B3158423 : Blo 1246441 3158423 := bstep (se 1 (by rfl) ⟨2368817, by rfl⟩ : syracuseStep 3158423 = 4737635) B4737635
theorem B1872281 : Blo 1246441 1872281 := bstep (se 2 (by rfl) ⟨702105, by rfl⟩ : syracuseStep 1872281 = 1404211) B1404211
theorem B1872395 : Blo 1246441 1872395 := bstep (se 1 (by rfl) ⟨1404296, by rfl⟩ : syracuseStep 1872395 = 2808593) B2808593
theorem B1872407 : Blo 1246441 1872407 := bstep (se 1 (by rfl) ⟨1404305, by rfl⟩ : syracuseStep 1872407 = 2808611) B2808611
theorem B10121773 : Blo 1246441 10121773 := bstep (se 3 (by rfl) ⟨1897832, by rfl⟩ : syracuseStep 10121773 = 3795665) B3795665
theorem B4207193 : Blo 1246441 4207193 := bstep (se 2 (by rfl) ⟨1577697, by rfl⟩ : syracuseStep 4207193 = 3155395) B3155395
theorem B2806361 : Blo 1246441 2806361 := bstep (se 2 (by rfl) ⟨1052385, by rfl⟩ : syracuseStep 2806361 = 2104771) B2104771
theorem B1872473 : Blo 1246441 1872473 := bstep (se 2 (by rfl) ⟨702177, by rfl⟩ : syracuseStep 1872473 = 1404355) B1404355
theorem B14209667 : Blo 1246441 14209667 := bstep (se 1 (by rfl) ⟨10657250, by rfl⟩ : syracuseStep 14209667 = 21314501) B21314501
theorem B7107203 : Blo 1246441 7107203 := bstep (se 1 (by rfl) ⟨5330402, by rfl⟩ : syracuseStep 7107203 = 10660805) B10660805
theorem B2806451 : Blo 1246441 2806451 := bstep (se 1 (by rfl) ⟨2104838, by rfl⟩ : syracuseStep 2806451 = 4209677) B4209677
theorem B1872587 : Blo 1246441 1872587 := bstep (se 1 (by rfl) ⟨1404440, by rfl⟩ : syracuseStep 1872587 = 2808881) B2808881
theorem B2806487 : Blo 1246441 2806487 := bstep (se 1 (by rfl) ⟨2104865, by rfl⟩ : syracuseStep 2806487 = 4209731) B4209731
theorem B1872599 : Blo 1246441 1872599 := bstep (se 1 (by rfl) ⟨1404449, by rfl⟩ : syracuseStep 1872599 = 2808899) B2808899
theorem B2192215 : Blo 1246441 2192215 := bstep (se 1 (by rfl) ⟨1644161, by rfl⟩ : syracuseStep 2192215 = 3288323) B3288323
theorem B2806667 : Blo 1246441 2806667 := bstep (se 1 (by rfl) ⟨2105000, by rfl⟩ : syracuseStep 2806667 = 4210001) B4210001
theorem B2806721 : Blo 1246441 2806721 := bstep (se 2 (by rfl) ⟨1052520, by rfl⟩ : syracuseStep 2806721 = 2105041) B2105041
theorem B6312977 : Blo 1246441 6312977 := bstep (se 2 (by rfl) ⟨2367366, by rfl⟩ : syracuseStep 6312977 = 4734733) B4734733
theorem B7107659 : Blo 1246441 7107659 := bstep (se 1 (by rfl) ⟨5330744, by rfl⟩ : syracuseStep 7107659 = 10661489) B10661489
theorem B12792925 : Blo 1246441 12792925 := bstep (se 3 (by rfl) ⟨2398673, by rfl⟩ : syracuseStep 12792925 = 4797347) B4797347
theorem B3552349 : Blo 1246441 3552349 := bstep (se 3 (by rfl) ⟨666065, by rfl⟩ : syracuseStep 3552349 = 1332131) B1332131
theorem B3552407 : Blo 1246441 3552407 := bstep (se 1 (by rfl) ⟨2664305, by rfl⟩ : syracuseStep 3552407 = 5328611) B5328611
theorem B2806937 : Blo 1246441 2806937 := bstep (se 2 (by rfl) ⟨1052601, by rfl⟩ : syracuseStep 2806937 = 2105203) B2105203
theorem B6313139 : Blo 1246441 6313139 := bstep (se 1 (by rfl) ⟨4734854, by rfl⟩ : syracuseStep 6313139 = 9469709) B9469709
theorem B2995393 : Blo 1246441 2995393 := bstep (se 2 (by rfl) ⟨1123272, by rfl⟩ : syracuseStep 2995393 = 2246545) B2246545
theorem B3159233 : Blo 1246441 3159233 := bstep (se 2 (by rfl) ⟨1184712, by rfl⟩ : syracuseStep 3159233 = 2369425) B2369425
theorem B1578199 : Blo 1246441 1578199 := bstep (se 1 (by rfl) ⟨1183649, by rfl⟩ : syracuseStep 1578199 = 2367299) B2367299
theorem B2807027 : Blo 1246441 2807027 := bstep (se 1 (by rfl) ⟨2105270, by rfl⟩ : syracuseStep 2807027 = 4210541) B4210541
theorem B4207895 : Blo 1246441 4207895 := bstep (se 1 (by rfl) ⟨3155921, by rfl⟩ : syracuseStep 4207895 = 6311843) B6311843
theorem B2807063 : Blo 1246441 2807063 := bstep (se 1 (by rfl) ⟨2105297, by rfl⟩ : syracuseStep 2807063 = 4210595) B4210595
theorem B2807243 : Blo 1246441 2807243 := bstep (se 1 (by rfl) ⟨2105432, by rfl⟩ : syracuseStep 2807243 = 4210865) B4210865
theorem B2807297 : Blo 1246441 2807297 := bstep (se 2 (by rfl) ⟨1052736, by rfl⟩ : syracuseStep 2807297 = 2105473) B2105473
theorem B1332823 : Blo 1246441 1332823 := bstep (se 1 (by rfl) ⟨999617, by rfl⟩ : syracuseStep 1332823 = 1999235) B1999235
theorem B2528921 : Blo 1246441 2528921 := bstep (se 2 (by rfl) ⟨948345, by rfl⟩ : syracuseStep 2528921 = 1896691) B1896691
theorem B10114739 : Blo 1246441 10114739 := bstep (se 1 (by rfl) ⟨7586054, by rfl⟩ : syracuseStep 10114739 = 15172109) B15172109
theorem B2807513 : Blo 1246441 2807513 := bstep (se 2 (by rfl) ⟨1052817, by rfl⟩ : syracuseStep 2807513 = 2105635) B2105635
theorem B3159769 : Blo 1246441 3159769 := bstep (se 2 (by rfl) ⟨1184913, by rfl⟩ : syracuseStep 3159769 = 2369827) B2369827
theorem B5060369 : Blo 1246441 5060369 := bstep (se 2 (by rfl) ⟨1897638, by rfl⟩ : syracuseStep 5060369 = 3795277) B3795277
theorem B5330711 : Blo 1246441 5330711 := bstep (se 1 (by rfl) ⟨3998033, by rfl⟩ : syracuseStep 5330711 = 7996067) B7996067
theorem B4208435 : Blo 1246441 4208435 := bstep (se 1 (by rfl) ⟨3156326, by rfl⟩ : syracuseStep 4208435 = 6312653) B6312653
theorem B2807603 : Blo 1246441 2807603 := bstep (se 1 (by rfl) ⟨2105702, by rfl⟩ : syracuseStep 2807603 = 4211405) B4211405
theorem B2807639 : Blo 1246441 2807639 := bstep (se 1 (by rfl) ⟨2105729, by rfl⟩ : syracuseStep 2807639 = 4211459) B4211459
theorem B2529163 : Blo 1246441 2529163 := bstep (se 1 (by rfl) ⟨1896872, by rfl⟩ : syracuseStep 2529163 = 3793745) B3793745
theorem B1996697 : Blo 1246441 1996697 := bstep (se 2 (by rfl) ⟨748761, by rfl⟩ : syracuseStep 1996697 = 1497523) B1497523
theorem B5060531 : Blo 1246441 5060531 := bstep (se 1 (by rfl) ⟨3795398, by rfl⟩ : syracuseStep 5060531 = 7590797) B7590797
theorem B2807819 : Blo 1246441 2807819 := bstep (se 1 (by rfl) ⟨2105864, by rfl⟩ : syracuseStep 2807819 = 4211729) B4211729
theorem B1775639 : Blo 1246441 1775639 := bstep (se 1 (by rfl) ⟨1331729, by rfl⟩ : syracuseStep 1775639 = 2663459) B2663459
theorem B4208705 : Blo 1246441 4208705 := bstep (se 2 (by rfl) ⟨1578264, by rfl⟩ : syracuseStep 4208705 = 3156529) B3156529
theorem B2807873 : Blo 1246441 2807873 := bstep (se 2 (by rfl) ⟨1052952, by rfl⟩ : syracuseStep 2807873 = 2105905) B2105905
theorem B184440907 : Blo 1246441 184440907 := bstep (se 1 (by rfl) ⟨138330680, by rfl⟩ : syracuseStep 184440907 = 276661361) B276661361
theorem B1349879 : Blo 1246441 1349879 := bstep (se 1 (by rfl) ⟨1012409, by rfl⟩ : syracuseStep 1349879 = 2024819) B2024819
theorem B2103563 : Blo 1246441 2103563 := bstep (se 1 (by rfl) ⟨1577672, by rfl⟩ : syracuseStep 2103563 = 3155345) B3155345
theorem B2808089 : Blo 1246441 2808089 := bstep (se 2 (by rfl) ⟨1053033, by rfl⟩ : syracuseStep 2808089 = 2106067) B2106067
theorem B1775947 : Blo 1246441 1775947 := bstep (se 1 (by rfl) ⟨1331960, by rfl⟩ : syracuseStep 1775947 = 2663921) B2663921
theorem B3553625 : Blo 1246441 3553625 := bstep (se 2 (by rfl) ⟨1332609, by rfl⟩ : syracuseStep 3553625 = 2665219) B2665219
theorem B2808179 : Blo 1246441 2808179 := bstep (se 1 (by rfl) ⟨2106134, by rfl⟩ : syracuseStep 2808179 = 4212269) B4212269
theorem B2103691 : Blo 1246441 2103691 := bstep (se 1 (by rfl) ⟨1577768, by rfl⟩ : syracuseStep 2103691 = 3155537) B3155537
theorem B2808215 : Blo 1246441 2808215 := bstep (se 1 (by rfl) ⟨2106161, by rfl⟩ : syracuseStep 2808215 = 4212323) B4212323
theorem B3553739 : Blo 1246441 3553739 := bstep (se 1 (by rfl) ⟨2665304, by rfl⟩ : syracuseStep 3553739 = 5330609) B5330609
theorem B2103833 : Blo 1246441 2103833 := bstep (se 2 (by rfl) ⟨788937, by rfl⟩ : syracuseStep 2103833 = 1577875) B1577875
theorem B4799027 : Blo 1246441 4799027 := bstep (se 1 (by rfl) ⟨3599270, by rfl⟩ : syracuseStep 4799027 = 7198541) B7198541
theorem B2808395 : Blo 1246441 2808395 := bstep (se 1 (by rfl) ⟨2106296, by rfl⟩ : syracuseStep 2808395 = 4212593) B4212593
theorem B4209245 : Blo 1246441 4209245 := bstep (se 3 (by rfl) ⟨789233, by rfl⟩ : syracuseStep 4209245 = 1578467) B1578467
theorem B2808449 : Blo 1246441 2808449 := bstep (se 2 (by rfl) ⟨1053168, by rfl⟩ : syracuseStep 2808449 = 2106337) B2106337
theorem B2103961 : Blo 1246441 2103961 := bstep (se 2 (by rfl) ⟨788985, by rfl⟩ : syracuseStep 2103961 = 1577971) B1577971
theorem B11983565 : Blo 1246441 11983565 := bstep (se 3 (by rfl) ⟨2246918, by rfl⟩ : syracuseStep 11983565 = 4493837) B4493837
theorem B4733747 : Blo 1246441 4733747 := bstep (se 1 (by rfl) ⟨3550310, by rfl⟩ : syracuseStep 4733747 = 7100621) B7100621
theorem B4733761 : Blo 1246441 4733761 := bstep (se 2 (by rfl) ⟨1775160, by rfl⟩ : syracuseStep 4733761 = 3550321) B3550321
theorem B9468737 : Blo 1246441 9468737 := bstep (se 2 (by rfl) ⟨3550776, by rfl⟩ : syracuseStep 9468737 = 7101553) B7101553
theorem B2808665 : Blo 1246441 2808665 := bstep (se 2 (by rfl) ⟨1053249, by rfl⟩ : syracuseStep 2808665 = 2106499) B2106499
theorem B1579915 : Blo 1246441 1579915 := bstep (se 1 (by rfl) ⟨1184936, by rfl⟩ : syracuseStep 1579915 = 2369873) B2369873
theorem B2808755 : Blo 1246441 2808755 := bstep (se 1 (by rfl) ⟨2106566, by rfl⟩ : syracuseStep 2808755 = 4213133) B4213133
theorem B2808791 : Blo 1246441 2808791 := bstep (se 1 (by rfl) ⟨2106593, by rfl⟩ : syracuseStep 2808791 = 4213187) B4213187
theorem B2366425 : Blo 1246441 2366425 := bstep (se 2 (by rfl) ⟨887409, by rfl⟩ : syracuseStep 2366425 = 1774819) B1774819
theorem B6315083 : Blo 1246441 6315083 := bstep (se 1 (by rfl) ⟨4736312, by rfl⟩ : syracuseStep 6315083 = 9472625) B9472625
theorem B5332043 : Blo 1246441 5332043 := bstep (se 1 (by rfl) ⟨3999032, by rfl⟩ : syracuseStep 5332043 = 7998065) B7998065
theorem B2808971 : Blo 1246441 2808971 := bstep (se 1 (by rfl) ⟨2106728, by rfl⟩ : syracuseStep 2808971 = 4213457) B4213457
theorem B2104535 : Blo 1246441 2104535 := bstep (se 1 (by rfl) ⟨1578401, by rfl⟩ : syracuseStep 2104535 = 3156803) B3156803
theorem B7691537 : Blo 1246441 7691537 := bstep (se 2 (by rfl) ⟨2884326, by rfl⟩ : syracuseStep 7691537 = 5768653) B5768653
theorem B3374401 : Blo 1246441 3374401 := bstep (se 2 (by rfl) ⟨1265400, by rfl⟩ : syracuseStep 3374401 = 2530801) B2530801
theorem B2104663 : Blo 1246441 2104663 := bstep (se 1 (by rfl) ⟨1578497, by rfl⟩ : syracuseStep 2104663 = 3156995) B3156995
theorem B1776983 : Blo 1246441 1776983 := bstep (se 1 (by rfl) ⟨1332737, by rfl⟩ : syracuseStep 1776983 = 2665475) B2665475
theorem B7101827 : Blo 1246441 7101827 := bstep (se 1 (by rfl) ⟨5326370, by rfl⟩ : syracuseStep 7101827 = 10652741) B10652741
theorem B1777177 : Blo 1246441 1777177 := bstep (se 2 (by rfl) ⟨666441, by rfl⟩ : syracuseStep 1777177 = 1332883) B1332883
theorem B3554867 : Blo 1246441 3554867 := bstep (se 1 (by rfl) ⟨2666150, by rfl⟩ : syracuseStep 3554867 = 5332301) B5332301
theorem B23076427 : Blo 1246441 23076427 := bstep (se 1 (by rfl) ⟨17307320, by rfl⟩ : syracuseStep 23076427 = 34614641) B34614641
theorem B5332625 : Blo 1246441 5332625 := bstep (se 2 (by rfl) ⟨1999734, by rfl⟩ : syracuseStep 5332625 = 3999469) B3999469
theorem B2997911 : Blo 1246441 2997911 := bstep (se 1 (by rfl) ⟨2248433, by rfl⟩ : syracuseStep 2997911 = 4496867) B4496867
theorem B4210379 : Blo 1246441 4210379 := bstep (se 1 (by rfl) ⟨3157784, by rfl⟩ : syracuseStep 4210379 = 6315569) B6315569
theorem B5324561 : Blo 1246441 5324561 := bstep (se 2 (by rfl) ⟨1996710, by rfl⟩ : syracuseStep 5324561 = 3993421) B3993421
theorem B7298909 : Blo 1246441 7298909 := bstep (se 3 (by rfl) ⟨1368545, by rfl⟩ : syracuseStep 7298909 = 2737091) B2737091
theorem B7987045 : Blo 1246441 7987045 := bstep (se 4 (by rfl) ⟨748785, by rfl⟩ : syracuseStep 7987045 = 1497571) B1497571
theorem B2105291 : Blo 1246441 2105291 := bstep (se 1 (by rfl) ⟨1578968, by rfl⟩ : syracuseStep 2105291 = 3157937) B3157937
theorem B1499095 : Blo 1246441 1499095 := bstep (se 1 (by rfl) ⟨1124321, by rfl⟩ : syracuseStep 1499095 = 2248643) B2248643
theorem B4210649 : Blo 1246441 4210649 := bstep (se 2 (by rfl) ⟨1578993, by rfl⟩ : syracuseStep 4210649 = 3157987) B3157987
theorem B6316055 : Blo 1246441 6316055 := bstep (se 1 (by rfl) ⟨4737041, by rfl⟩ : syracuseStep 6316055 = 9474083) B9474083
theorem B4735037 : Blo 1246441 4735037 := bstep (se 3 (by rfl) ⟨887819, by rfl⟩ : syracuseStep 4735037 = 1775639) B1775639
theorem B2105615 : Blo 1246441 2105615 := bstep (se 1 (by rfl) ⟨1579211, by rfl⟩ : syracuseStep 2105615 = 3158423) B3158423
theorem B6832421 : Blo 1246441 6832421 := bstep (se 4 (by rfl) ⟨640539, by rfl⟩ : syracuseStep 6832421 = 1281079) B1281079
theorem B3998099 : Blo 1246441 3998099 := bstep (se 1 (by rfl) ⟨2998574, by rfl⟩ : syracuseStep 3998099 = 5997149) B5997149
theorem B5325209 : Blo 1246441 5325209 := bstep (se 2 (by rfl) ⟨1996953, by rfl⟩ : syracuseStep 5325209 = 3993907) B3993907
theorem B2367929 : Blo 1246441 2367929 := bstep (se 2 (by rfl) ⟨887973, by rfl⟩ : syracuseStep 2367929 = 1775947) B1775947
theorem B8536529 : Blo 1246441 8536529 := bstep (se 2 (by rfl) ⟨3201198, by rfl⟩ : syracuseStep 8536529 = 6402397) B6402397
theorem B3080719 : Blo 1246441 3080719 := bstep (se 1 (by rfl) ⟨2310539, by rfl⟩ : syracuseStep 3080719 = 4621079) B4621079
theorem B4211243 : Blo 1246441 4211243 := bstep (se 1 (by rfl) ⟨3158432, by rfl⟩ : syracuseStep 4211243 = 6316865) B6316865
theorem B11371085 : Blo 1246441 11371085 := bstep (se 3 (by rfl) ⟨2132078, by rfl⟩ : syracuseStep 11371085 = 4264157) B4264157
theorem B2368271 : Blo 1246441 2368271 := bstep (se 1 (by rfl) ⟨1776203, by rfl⟩ : syracuseStep 2368271 = 3552407) B3552407
theorem B2106155 : Blo 1246441 2106155 := bstep (se 1 (by rfl) ⟨1579616, by rfl⟩ : syracuseStep 2106155 = 3159233) B3159233
theorem B14214041 : Blo 1246441 14214041 := bstep (se 2 (by rfl) ⟨5330265, by rfl⟩ : syracuseStep 14214041 = 10660531) B10660531
theorem B22774871 : Blo 1246441 22774871 := bstep (se 1 (by rfl) ⟨17081153, by rfl⟩ : syracuseStep 22774871 = 34162307) B34162307
theorem B6743159 : Blo 1246441 6743159 := bstep (se 1 (by rfl) ⟨5057369, by rfl⟩ : syracuseStep 6743159 = 10114739) B10114739
theorem B2106553 : Blo 1246441 2106553 := bstep (se 2 (by rfl) ⟨789957, by rfl⟩ : syracuseStep 2106553 = 1579915) B1579915
theorem B1246471 : Blo 1246441 1246471 := bstep (se 1 (by rfl) ⟨934853, by rfl⟩ : syracuseStep 1246471 = 1869707) B1869707
theorem B1246479 : Blo 1246441 1246479 := bstep (se 1 (by rfl) ⟨934859, by rfl⟩ : syracuseStep 1246479 = 1869719) B1869719
theorem B3155233 : Blo 1246441 3155233 := bstep (se 2 (by rfl) ⟨1183212, by rfl⟩ : syracuseStep 3155233 = 2366425) B2366425
theorem B1246523 : Blo 1246441 1246523 := bstep (se 1 (by rfl) ⟨934892, by rfl⟩ : syracuseStep 1246523 = 1869785) B1869785
theorem B1246599 : Blo 1246441 1246599 := bstep (se 1 (by rfl) ⟨934949, by rfl⟩ : syracuseStep 1246599 = 1869899) B1869899
theorem B1246607 : Blo 1246441 1246607 := bstep (se 1 (by rfl) ⟨934955, by rfl⟩ : syracuseStep 1246607 = 1869911) B1869911
theorem B1246651 : Blo 1246441 1246651 := bstep (se 1 (by rfl) ⟨934988, by rfl⟩ : syracuseStep 1246651 = 1869977) B1869977
theorem B17057233 : Blo 1246441 17057233 := bstep (se 2 (by rfl) ⟨6396462, by rfl⟩ : syracuseStep 17057233 = 12792925) B12792925
theorem B4736465 : Blo 1246441 4736465 := bstep (se 2 (by rfl) ⟨1776174, by rfl⟩ : syracuseStep 4736465 = 3552349) B3552349
theorem B1402375 : Blo 1246441 1402375 := bstep (se 1 (by rfl) ⟨1051781, by rfl⟩ : syracuseStep 1402375 = 2103563) B2103563
theorem B1246727 : Blo 1246441 1246727 := bstep (se 1 (by rfl) ⟨935045, by rfl⟩ : syracuseStep 1246727 = 1870091) B1870091
theorem B1246735 : Blo 1246441 1246735 := bstep (se 1 (by rfl) ⟨935051, by rfl⟩ : syracuseStep 1246735 = 1870103) B1870103
theorem B1246779 : Blo 1246441 1246779 := bstep (se 1 (by rfl) ⟨935084, by rfl⟩ : syracuseStep 1246779 = 1870169) B1870169
theorem B2369083 : Blo 1246441 2369083 := bstep (se 1 (by rfl) ⟨1776812, by rfl⟩ : syracuseStep 2369083 = 3553625) B3553625
theorem B17974885 : Blo 1246441 17974885 := bstep (se 4 (by rfl) ⟨1685145, by rfl⟩ : syracuseStep 17974885 = 3370291) B3370291
theorem B1246855 : Blo 1246441 1246855 := bstep (se 1 (by rfl) ⟨935141, by rfl⟩ : syracuseStep 1246855 = 1870283) B1870283
theorem B2369159 : Blo 1246441 2369159 := bstep (se 1 (by rfl) ⟨1776869, by rfl⟩ : syracuseStep 2369159 = 3553739) B3553739
theorem B1246863 : Blo 1246441 1246863 := bstep (se 1 (by rfl) ⟨935147, by rfl⟩ : syracuseStep 1246863 = 1870295) B1870295
theorem B1402555 : Blo 1246441 1402555 := bstep (se 1 (by rfl) ⟨1051916, by rfl⟩ : syracuseStep 1402555 = 2103833) B2103833
theorem B1246907 : Blo 1246441 1246907 := bstep (se 1 (by rfl) ⟨935180, by rfl⟩ : syracuseStep 1246907 = 1870361) B1870361
theorem B4499201 : Blo 1246441 4499201 := bstep (se 2 (by rfl) ⟨1687200, by rfl⟩ : syracuseStep 4499201 = 3374401) B3374401
theorem B1246983 : Blo 1246441 1246983 := bstep (se 1 (by rfl) ⟨935237, by rfl⟩ : syracuseStep 1246983 = 1870475) B1870475
theorem B1246991 : Blo 1246441 1246991 := bstep (se 1 (by rfl) ⟨935243, by rfl⟩ : syracuseStep 1246991 = 1870487) B1870487
theorem B7989043 : Blo 1246441 7989043 := bstep (se 1 (by rfl) ⟨5991782, by rfl⟩ : syracuseStep 7989043 = 11983565) B11983565
theorem B1247035 : Blo 1246441 1247035 := bstep (se 1 (by rfl) ⟨935276, by rfl⟩ : syracuseStep 1247035 = 1870553) B1870553
theorem B4212539 : Blo 1246441 4212539 := bstep (se 1 (by rfl) ⟨3159404, by rfl⟩ : syracuseStep 4212539 = 6318809) B6318809
theorem B3155831 : Blo 1246441 3155831 := bstep (se 1 (by rfl) ⟨2366873, by rfl⟩ : syracuseStep 3155831 = 4733747) B4733747
theorem B1247111 : Blo 1246441 1247111 := bstep (se 1 (by rfl) ⟨935333, by rfl⟩ : syracuseStep 1247111 = 1870667) B1870667
theorem B1247119 : Blo 1246441 1247119 := bstep (se 1 (by rfl) ⟨935339, by rfl⟩ : syracuseStep 1247119 = 1870679) B1870679
theorem B1869755 : Blo 1246441 1869755 := bstep (se 1 (by rfl) ⟨1402316, by rfl⟩ : syracuseStep 1869755 = 2804633) B2804633
theorem B1247163 : Blo 1246441 1247163 := bstep (se 1 (by rfl) ⟨935372, by rfl⟩ : syracuseStep 1247163 = 1870745) B1870745
theorem B1869815 : Blo 1246441 1869815 := bstep (se 1 (by rfl) ⟨1402361, by rfl⟩ : syracuseStep 1869815 = 2804723) B2804723
theorem B1247239 : Blo 1246441 1247239 := bstep (se 1 (by rfl) ⟨935429, by rfl⟩ : syracuseStep 1247239 = 1870859) B1870859
theorem B1869839 : Blo 1246441 1869839 := bstep (se 1 (by rfl) ⟨1402379, by rfl⟩ : syracuseStep 1869839 = 2804759) B2804759
theorem B1247247 : Blo 1246441 1247247 := bstep (se 1 (by rfl) ⟨935435, by rfl⟩ : syracuseStep 1247247 = 1870871) B1870871
theorem B2369569 : Blo 1246441 2369569 := bstep (se 2 (by rfl) ⟨888588, by rfl⟩ : syracuseStep 2369569 = 1777177) B1777177
theorem B1869881 : Blo 1246441 1869881 := bstep (se 2 (by rfl) ⟨701205, by rfl⟩ : syracuseStep 1869881 = 1402411) B1402411
theorem B1247291 : Blo 1246441 1247291 := bstep (se 1 (by rfl) ⟨935468, by rfl⟩ : syracuseStep 1247291 = 1870937) B1870937
theorem B1869959 : Blo 1246441 1869959 := bstep (se 1 (by rfl) ⟨1402469, by rfl⟩ : syracuseStep 1869959 = 2804939) B2804939
theorem B1247367 : Blo 1246441 1247367 := bstep (se 1 (by rfl) ⟨935525, by rfl⟩ : syracuseStep 1247367 = 1871051) B1871051
theorem B1403023 : Blo 1246441 1403023 := bstep (se 1 (by rfl) ⟨1052267, by rfl⟩ : syracuseStep 1403023 = 2104535) B2104535
theorem B1247375 : Blo 1246441 1247375 := bstep (se 1 (by rfl) ⟨935531, by rfl⟩ : syracuseStep 1247375 = 1871063) B1871063
theorem B1869995 : Blo 1246441 1869995 := bstep (se 1 (by rfl) ⟨1402496, by rfl⟩ : syracuseStep 1869995 = 2804993) B2804993
theorem B1247419 : Blo 1246441 1247419 := bstep (se 1 (by rfl) ⟨935564, by rfl⟩ : syracuseStep 1247419 = 1871129) B1871129
theorem B1870025 : Blo 1246441 1870025 := bstep (se 2 (by rfl) ⟨701259, by rfl⟩ : syracuseStep 1870025 = 1402519) B1402519
theorem B1247495 : Blo 1246441 1247495 := bstep (se 1 (by rfl) ⟨935621, by rfl⟩ : syracuseStep 1247495 = 1871243) B1871243
theorem B1247503 : Blo 1246441 1247503 := bstep (se 1 (by rfl) ⟨935627, by rfl⟩ : syracuseStep 1247503 = 1871255) B1871255
theorem B4213025 : Blo 1246441 4213025 := bstep (se 2 (by rfl) ⟨1579884, by rfl⟩ : syracuseStep 4213025 = 3159769) B3159769
theorem B1870139 : Blo 1246441 1870139 := bstep (se 1 (by rfl) ⟨1402604, by rfl⟩ : syracuseStep 1870139 = 2805209) B2805209
theorem B1247547 : Blo 1246441 1247547 := bstep (se 1 (by rfl) ⟨935660, by rfl⟩ : syracuseStep 1247547 = 1871321) B1871321
theorem B1870199 : Blo 1246441 1870199 := bstep (se 1 (by rfl) ⟨1402649, by rfl⟩ : syracuseStep 1870199 = 2805299) B2805299
theorem B2369911 : Blo 1246441 2369911 := bstep (se 1 (by rfl) ⟨1777433, by rfl⟩ : syracuseStep 2369911 = 3554867) B3554867
theorem B1247623 : Blo 1246441 1247623 := bstep (se 1 (by rfl) ⟨935717, by rfl⟩ : syracuseStep 1247623 = 1871435) B1871435
theorem B1870223 : Blo 1246441 1870223 := bstep (se 1 (by rfl) ⟨1402667, by rfl⟩ : syracuseStep 1870223 = 2805335) B2805335
theorem B1247631 : Blo 1246441 1247631 := bstep (se 1 (by rfl) ⟨935723, by rfl⟩ : syracuseStep 1247631 = 1871447) B1871447
theorem B1870265 : Blo 1246441 1870265 := bstep (se 2 (by rfl) ⟨701349, by rfl⟩ : syracuseStep 1870265 = 1402699) B1402699
theorem B1247675 : Blo 1246441 1247675 := bstep (se 1 (by rfl) ⟨935756, by rfl⟩ : syracuseStep 1247675 = 1871513) B1871513
theorem B1870343 : Blo 1246441 1870343 := bstep (se 1 (by rfl) ⟨1402757, by rfl⟩ : syracuseStep 1870343 = 2805515) B2805515
theorem B1247751 : Blo 1246441 1247751 := bstep (se 1 (by rfl) ⟨935813, by rfl⟩ : syracuseStep 1247751 = 1871627) B1871627
theorem B3549707 : Blo 1246441 3549707 := bstep (se 1 (by rfl) ⟨2662280, by rfl⟩ : syracuseStep 3549707 = 5324561) B5324561
theorem B1247759 : Blo 1246441 1247759 := bstep (se 1 (by rfl) ⟨935819, by rfl⟩ : syracuseStep 1247759 = 1871639) B1871639
theorem B1870379 : Blo 1246441 1870379 := bstep (se 1 (by rfl) ⟨1402784, by rfl⟩ : syracuseStep 1870379 = 2805569) B2805569
theorem B5999147 : Blo 1246441 5999147 := bstep (se 1 (by rfl) ⟨4499360, by rfl⟩ : syracuseStep 5999147 = 8998721) B8998721
theorem B1247803 : Blo 1246441 1247803 := bstep (se 1 (by rfl) ⟨935852, by rfl⟩ : syracuseStep 1247803 = 1871705) B1871705
theorem B1870409 : Blo 1246441 1870409 := bstep (se 2 (by rfl) ⟨701403, by rfl⟩ : syracuseStep 1870409 = 1402807) B1402807
theorem B1403527 : Blo 1246441 1403527 := bstep (se 1 (by rfl) ⟨1052645, by rfl⟩ : syracuseStep 1403527 = 2105291) B2105291
theorem B1247879 : Blo 1246441 1247879 := bstep (se 1 (by rfl) ⟨935909, by rfl⟩ : syracuseStep 1247879 = 1871819) B1871819
theorem B1247887 : Blo 1246441 1247887 := bstep (se 1 (by rfl) ⟨935915, by rfl⟩ : syracuseStep 1247887 = 1871831) B1871831
theorem B1870523 : Blo 1246441 1870523 := bstep (se 1 (by rfl) ⟨1402892, by rfl⟩ : syracuseStep 1870523 = 2805785) B2805785
theorem B1247931 : Blo 1246441 1247931 := bstep (se 1 (by rfl) ⟨935948, by rfl⟩ : syracuseStep 1247931 = 1871897) B1871897
theorem B12315329 : Blo 1246441 12315329 := bstep (se 2 (by rfl) ⟨4618248, by rfl⟩ : syracuseStep 12315329 = 9236497) B9236497
theorem B1870583 : Blo 1246441 1870583 := bstep (se 1 (by rfl) ⟨1402937, by rfl⟩ : syracuseStep 1870583 = 2805875) B2805875
theorem B1248007 : Blo 1246441 1248007 := bstep (se 1 (by rfl) ⟨936005, by rfl⟩ : syracuseStep 1248007 = 1872011) B1872011
theorem B1870607 : Blo 1246441 1870607 := bstep (se 1 (by rfl) ⟨1402955, by rfl⟩ : syracuseStep 1870607 = 2805911) B2805911
theorem B1248015 : Blo 1246441 1248015 := bstep (se 1 (by rfl) ⟨936011, by rfl⟩ : syracuseStep 1248015 = 1872023) B1872023
theorem B1870649 : Blo 1246441 1870649 := bstep (se 2 (by rfl) ⟨701493, by rfl⟩ : syracuseStep 1870649 = 1402987) B1402987
theorem B1403707 : Blo 1246441 1403707 := bstep (se 1 (by rfl) ⟨1052780, by rfl⟩ : syracuseStep 1403707 = 2105561) B2105561
theorem B1248059 : Blo 1246441 1248059 := bstep (se 1 (by rfl) ⟨936044, by rfl⟩ : syracuseStep 1248059 = 1872089) B1872089
theorem B2804615 : Blo 1246441 2804615 := bstep (se 1 (by rfl) ⟨2103461, by rfl⟩ : syracuseStep 2804615 = 4206923) B4206923
theorem B1870727 : Blo 1246441 1870727 := bstep (se 1 (by rfl) ⟨1403045, by rfl⟩ : syracuseStep 1870727 = 2806091) B2806091
theorem B1248135 : Blo 1246441 1248135 := bstep (se 1 (by rfl) ⟨936101, by rfl⟩ : syracuseStep 1248135 = 1872203) B1872203
theorem B1248143 : Blo 1246441 1248143 := bstep (se 1 (by rfl) ⟨936107, by rfl⟩ : syracuseStep 1248143 = 1872215) B1872215
theorem B7105427 : Blo 1246441 7105427 := bstep (se 1 (by rfl) ⟨5329070, by rfl⟩ : syracuseStep 7105427 = 10658141) B10658141
theorem B3795859 : Blo 1246441 3795859 := bstep (se 1 (by rfl) ⟨2846894, by rfl⟩ : syracuseStep 3795859 = 5693789) B5693789
theorem B1870763 : Blo 1246441 1870763 := bstep (se 1 (by rfl) ⟨1403072, by rfl⟩ : syracuseStep 1870763 = 2806145) B2806145
theorem B1248187 : Blo 1246441 1248187 := bstep (se 1 (by rfl) ⟨936140, by rfl⟩ : syracuseStep 1248187 = 1872281) B1872281
theorem B1870793 : Blo 1246441 1870793 := bstep (se 2 (by rfl) ⟨701547, by rfl⟩ : syracuseStep 1870793 = 1403095) B1403095
theorem B1248263 : Blo 1246441 1248263 := bstep (se 1 (by rfl) ⟨936197, by rfl⟩ : syracuseStep 1248263 = 1872395) B1872395
theorem B1248271 : Blo 1246441 1248271 := bstep (se 1 (by rfl) ⟨936203, by rfl⟩ : syracuseStep 1248271 = 1872407) B1872407
theorem B6319133 : Blo 1246441 6319133 := bstep (se 3 (by rfl) ⟨1184837, by rfl⟩ : syracuseStep 6319133 = 2369675) B2369675
theorem B2804795 : Blo 1246441 2804795 := bstep (se 1 (by rfl) ⟨2103596, by rfl⟩ : syracuseStep 2804795 = 4207193) B4207193
theorem B1870907 : Blo 1246441 1870907 := bstep (se 1 (by rfl) ⟨1403180, by rfl⟩ : syracuseStep 1870907 = 2806361) B2806361
theorem B1248315 : Blo 1246441 1248315 := bstep (se 1 (by rfl) ⟨936236, by rfl⟩ : syracuseStep 1248315 = 1872473) B1872473
theorem B9473111 : Blo 1246441 9473111 := bstep (se 1 (by rfl) ⟨7104833, by rfl⟩ : syracuseStep 9473111 = 14209667) B14209667
theorem B4738135 : Blo 1246441 4738135 := bstep (se 1 (by rfl) ⟨3553601, by rfl⟩ : syracuseStep 4738135 = 7107203) B7107203
theorem B1870967 : Blo 1246441 1870967 := bstep (se 1 (by rfl) ⟨1403225, by rfl⟩ : syracuseStep 1870967 = 2806451) B2806451
theorem B3157127 : Blo 1246441 3157127 := bstep (se 1 (by rfl) ⟨2367845, by rfl⟩ : syracuseStep 3157127 = 4735691) B4735691
theorem B1248391 : Blo 1246441 1248391 := bstep (se 1 (by rfl) ⟨936293, by rfl⟩ : syracuseStep 1248391 = 1872587) B1872587
theorem B1870991 : Blo 1246441 1870991 := bstep (se 1 (by rfl) ⟨1403243, by rfl⟩ : syracuseStep 1870991 = 2806487) B2806487
theorem B1248399 : Blo 1246441 1248399 := bstep (se 1 (by rfl) ⟨936299, by rfl⟩ : syracuseStep 1248399 = 1872599) B1872599
theorem B2804921 : Blo 1246441 2804921 := bstep (se 2 (by rfl) ⟨1051845, by rfl⟩ : syracuseStep 2804921 = 2103691) B2103691
theorem B3157177 : Blo 1246441 3157177 := bstep (se 2 (by rfl) ⟨1183941, by rfl⟩ : syracuseStep 3157177 = 2367883) B2367883
theorem B1871033 : Blo 1246441 1871033 := bstep (se 2 (by rfl) ⟨701637, by rfl⟩ : syracuseStep 1871033 = 1403275) B1403275
theorem B1871111 : Blo 1246441 1871111 := bstep (se 1 (by rfl) ⟨1403333, by rfl⟩ : syracuseStep 1871111 = 2806667) B2806667
theorem B1404175 : Blo 1246441 1404175 := bstep (se 1 (by rfl) ⟨1053131, by rfl⟩ : syracuseStep 1404175 = 2106263) B2106263
theorem B3550493 : Blo 1246441 3550493 := bstep (se 3 (by rfl) ⟨665717, by rfl⟩ : syracuseStep 3550493 = 1331435) B1331435
theorem B1871147 : Blo 1246441 1871147 := bstep (se 1 (by rfl) ⟨1403360, by rfl⟩ : syracuseStep 1871147 = 2806721) B2806721
theorem B3419435 : Blo 1246441 3419435 := bstep (se 1 (by rfl) ⟨2564576, by rfl⟩ : syracuseStep 3419435 = 5129153) B5129153
theorem B3599677 : Blo 1246441 3599677 := bstep (se 3 (by rfl) ⟨674939, by rfl⟩ : syracuseStep 3599677 = 1349879) B1349879
theorem B1871177 : Blo 1246441 1871177 := bstep (se 2 (by rfl) ⟨701691, by rfl⟩ : syracuseStep 1871177 = 1403383) B1403383
theorem B7105927 : Blo 1246441 7105927 := bstep (se 1 (by rfl) ⟨5329445, by rfl⟩ : syracuseStep 7105927 = 10658891) B10658891
theorem B4738439 : Blo 1246441 4738439 := bstep (se 1 (by rfl) ⟨3553829, by rfl⟩ : syracuseStep 4738439 = 7107659) B7107659
theorem B13495697 : Blo 1246441 13495697 := bstep (se 2 (by rfl) ⟨5060886, by rfl⟩ : syracuseStep 13495697 = 10121773) B10121773
theorem B1871291 : Blo 1246441 1871291 := bstep (se 1 (by rfl) ⟨1403468, by rfl⟩ : syracuseStep 1871291 = 2806937) B2806937
theorem B1871351 : Blo 1246441 1871351 := bstep (se 1 (by rfl) ⟨1403513, by rfl⟩ : syracuseStep 1871351 = 2807027) B2807027
theorem B6319619 : Blo 1246441 6319619 := bstep (se 1 (by rfl) ⟨4739714, by rfl⟩ : syracuseStep 6319619 = 9479429) B9479429
theorem B2805263 : Blo 1246441 2805263 := bstep (se 1 (by rfl) ⟨2103947, by rfl⟩ : syracuseStep 2805263 = 4207895) B4207895
theorem B1871375 : Blo 1246441 1871375 := bstep (se 1 (by rfl) ⟨1403531, by rfl⟩ : syracuseStep 1871375 = 2807063) B2807063
theorem B2805281 : Blo 1246441 2805281 := bstep (se 2 (by rfl) ⟨1051980, by rfl⟩ : syracuseStep 2805281 = 2103961) B2103961
theorem B1871417 : Blo 1246441 1871417 := bstep (se 2 (by rfl) ⟨701781, by rfl⟩ : syracuseStep 1871417 = 1403563) B1403563
theorem B4738621 : Blo 1246441 4738621 := bstep (se 3 (by rfl) ⟨888491, by rfl⟩ : syracuseStep 4738621 = 1776983) B1776983
theorem B1871495 : Blo 1246441 1871495 := bstep (se 1 (by rfl) ⟨1403621, by rfl⟩ : syracuseStep 1871495 = 2807243) B2807243
theorem B1871531 : Blo 1246441 1871531 := bstep (se 1 (by rfl) ⟨1403648, by rfl⟩ : syracuseStep 1871531 = 2807297) B2807297
theorem B1871561 : Blo 1246441 1871561 := bstep (se 2 (by rfl) ⟨701835, by rfl⟩ : syracuseStep 1871561 = 1403671) B1403671
theorem B6311681 : Blo 1246441 6311681 := bstep (se 2 (by rfl) ⟨2366880, by rfl⟩ : syracuseStep 6311681 = 4733761) B4733761
theorem B3600139 : Blo 1246441 3600139 := bstep (se 1 (by rfl) ⟨2700104, by rfl⟩ : syracuseStep 3600139 = 5400209) B5400209
theorem B3157775 : Blo 1246441 3157775 := bstep (se 1 (by rfl) ⟨2368331, by rfl⟩ : syracuseStep 3157775 = 4736663) B4736663
theorem B1871675 : Blo 1246441 1871675 := bstep (se 1 (by rfl) ⟨1403756, by rfl⟩ : syracuseStep 1871675 = 2807513) B2807513
theorem B2805623 : Blo 1246441 2805623 := bstep (se 1 (by rfl) ⟨2104217, by rfl⟩ : syracuseStep 2805623 = 4208435) B4208435
theorem B1871735 : Blo 1246441 1871735 := bstep (se 1 (by rfl) ⟨1403801, by rfl⟩ : syracuseStep 1871735 = 2807603) B2807603
theorem B3846023 : Blo 1246441 3846023 := bstep (se 1 (by rfl) ⟨2884517, by rfl⟩ : syracuseStep 3846023 = 5769035) B5769035
theorem B1871759 : Blo 1246441 1871759 := bstep (se 1 (by rfl) ⟨1403819, by rfl⟩ : syracuseStep 1871759 = 2807639) B2807639
theorem B1871801 : Blo 1246441 1871801 := bstep (se 2 (by rfl) ⟨701925, by rfl⟩ : syracuseStep 1871801 = 1403851) B1403851
theorem B1871879 : Blo 1246441 1871879 := bstep (se 1 (by rfl) ⟨1403909, by rfl⟩ : syracuseStep 1871879 = 2807819) B2807819
theorem B1601543 : Blo 1246441 1601543 := bstep (se 1 (by rfl) ⟨1201157, by rfl⟩ : syracuseStep 1601543 = 2402315) B2402315
theorem B2527265 : Blo 1246441 2527265 := bstep (se 2 (by rfl) ⟨947724, by rfl⟩ : syracuseStep 2527265 = 1895449) B1895449
theorem B2805803 : Blo 1246441 2805803 := bstep (se 1 (by rfl) ⟨2104352, by rfl⟩ : syracuseStep 2805803 = 4208705) B4208705
theorem B1871915 : Blo 1246441 1871915 := bstep (se 1 (by rfl) ⟨1403936, by rfl⟩ : syracuseStep 1871915 = 2807873) B2807873
theorem B1871945 : Blo 1246441 1871945 := bstep (se 2 (by rfl) ⟨701979, by rfl⟩ : syracuseStep 1871945 = 1403959) B1403959
theorem B14200919 : Blo 1246441 14200919 := bstep (se 1 (by rfl) ⟨10650689, by rfl⟩ : syracuseStep 14200919 = 21301379) B21301379
theorem B1872059 : Blo 1246441 1872059 := bstep (se 1 (by rfl) ⟨1404044, by rfl⟩ : syracuseStep 1872059 = 2808089) B2808089
theorem B1872119 : Blo 1246441 1872119 := bstep (se 1 (by rfl) ⟨1404089, by rfl⟩ : syracuseStep 1872119 = 2808179) B2808179
theorem B3993857 : Blo 1246441 3993857 := bstep (se 2 (by rfl) ⟨1497696, by rfl⟩ : syracuseStep 3993857 = 2995393) B2995393
theorem B1872143 : Blo 1246441 1872143 := bstep (se 1 (by rfl) ⟨1404107, by rfl⟩ : syracuseStep 1872143 = 2808215) B2808215
theorem B1872185 : Blo 1246441 1872185 := bstep (se 2 (by rfl) ⟨702069, by rfl⟩ : syracuseStep 1872185 = 1404139) B1404139
theorem B3199351 : Blo 1246441 3199351 := bstep (se 1 (by rfl) ⟨2399513, by rfl⟩ : syracuseStep 3199351 = 4799027) B4799027
theorem B1872263 : Blo 1246441 1872263 := bstep (se 1 (by rfl) ⟨1404197, by rfl⟩ : syracuseStep 1872263 = 2808395) B2808395
theorem B2806163 : Blo 1246441 2806163 := bstep (se 1 (by rfl) ⟨2104622, by rfl⟩ : syracuseStep 2806163 = 4209245) B4209245
theorem B1872299 : Blo 1246441 1872299 := bstep (se 1 (by rfl) ⟨1404224, by rfl⟩ : syracuseStep 1872299 = 2808449) B2808449
theorem B1708489 : Blo 1246441 1708489 := bstep (se 2 (by rfl) ⟨640683, by rfl⟩ : syracuseStep 1708489 = 1281367) B1281367
theorem B2806217 : Blo 1246441 2806217 := bstep (se 2 (by rfl) ⟨1052331, by rfl⟩ : syracuseStep 2806217 = 2104663) B2104663
theorem B3158473 : Blo 1246441 3158473 := bstep (se 2 (by rfl) ⟨1184427, by rfl⟩ : syracuseStep 3158473 = 2368855) B2368855
theorem B1872329 : Blo 1246441 1872329 := bstep (se 2 (by rfl) ⟨702123, by rfl⟩ : syracuseStep 1872329 = 1404247) B1404247
theorem B2527777 : Blo 1246441 2527777 := bstep (se 2 (by rfl) ⟨947916, by rfl⟩ : syracuseStep 2527777 = 1895833) B1895833
theorem B6312491 : Blo 1246441 6312491 := bstep (se 1 (by rfl) ⟨4734368, by rfl⟩ : syracuseStep 6312491 = 9468737) B9468737
theorem B1872443 : Blo 1246441 1872443 := bstep (se 1 (by rfl) ⟨1404332, by rfl⟩ : syracuseStep 1872443 = 2808665) B2808665
theorem B3158615 : Blo 1246441 3158615 := bstep (se 1 (by rfl) ⟨2368961, by rfl⟩ : syracuseStep 3158615 = 4737923) B4737923
theorem B1872503 : Blo 1246441 1872503 := bstep (se 1 (by rfl) ⟨1404377, by rfl⟩ : syracuseStep 1872503 = 2808755) B2808755
theorem B1897103 : Blo 1246441 1897103 := bstep (se 1 (by rfl) ⟨1422827, by rfl⟩ : syracuseStep 1897103 = 2845655) B2845655
theorem B1872527 : Blo 1246441 1872527 := bstep (se 1 (by rfl) ⟨1404395, by rfl⟩ : syracuseStep 1872527 = 2808791) B2808791
theorem B1872569 : Blo 1246441 1872569 := bstep (se 2 (by rfl) ⟨702213, by rfl⟩ : syracuseStep 1872569 = 1404427) B1404427
theorem B53916353 : Blo 1246441 53916353 := bstep (se 2 (by rfl) ⟨20218632, by rfl⟩ : syracuseStep 53916353 = 40437265) B40437265
theorem B8991425 : Blo 1246441 8991425 := bstep (se 2 (by rfl) ⟨3371784, by rfl⟩ : syracuseStep 8991425 = 6743569) B6743569
theorem B13488869 : Blo 1246441 13488869 := bstep (se 4 (by rfl) ⟨1264581, by rfl⟩ : syracuseStep 13488869 = 2529163) B2529163
theorem B1872647 : Blo 1246441 1872647 := bstep (se 1 (by rfl) ⟨1404485, by rfl⟩ : syracuseStep 1872647 = 2808971) B2808971
theorem B2806919 : Blo 1246441 2806919 := bstep (se 1 (by rfl) ⟨2105189, by rfl⟩ : syracuseStep 2806919 = 4210379) B4210379
theorem B2807099 : Blo 1246441 2807099 := bstep (se 1 (by rfl) ⟨2105324, by rfl⟩ : syracuseStep 2807099 = 4210649) B4210649
theorem B22771003 : Blo 1246441 22771003 := bstep (se 1 (by rfl) ⟨17078252, by rfl⟩ : syracuseStep 22771003 = 34156505) B34156505
theorem B3552599 : Blo 1246441 3552599 := bstep (se 1 (by rfl) ⟨2664449, by rfl⟩ : syracuseStep 3552599 = 5328899) B5328899
theorem B57595313 : Blo 1246441 57595313 := bstep (se 2 (by rfl) ⟨21598242, by rfl⟩ : syracuseStep 57595313 = 43196485) B43196485
theorem B4208057 : Blo 1246441 4208057 := bstep (se 2 (by rfl) ⟨1578021, by rfl⟩ : syracuseStep 4208057 = 3156043) B3156043
theorem B2807225 : Blo 1246441 2807225 := bstep (se 2 (by rfl) ⟨1052709, by rfl⟩ : syracuseStep 2807225 = 2105419) B2105419
theorem B26990009 : Blo 1246441 26990009 := bstep (se 2 (by rfl) ⟨10121253, by rfl⟩ : syracuseStep 26990009 = 20242507) B20242507
theorem B1799671 : Blo 1246441 1799671 := bstep (se 1 (by rfl) ⟨1349753, by rfl⟩ : syracuseStep 1799671 = 2699507) B2699507
theorem B5994013 : Blo 1246441 5994013 := bstep (se 3 (by rfl) ⟨1123877, by rfl⟩ : syracuseStep 5994013 = 2247755) B2247755
theorem B3372587 : Blo 1246441 3372587 := bstep (se 1 (by rfl) ⟨2529440, by rfl⟩ : syracuseStep 3372587 = 5058881) B5058881
theorem B1922617 : Blo 1246441 1922617 := bstep (se 2 (by rfl) ⟨720981, by rfl⟩ : syracuseStep 1922617 = 1441963) B1441963
theorem B983684837 : Blo 1246441 983684837 := bstep (se 4 (by rfl) ⟨92220453, by rfl⟩ : syracuseStep 983684837 = 184440907) B184440907
theorem B2807567 : Blo 1246441 2807567 := bstep (se 1 (by rfl) ⟨2105675, by rfl⟩ : syracuseStep 2807567 = 4211351) B4211351
theorem B2807585 : Blo 1246441 2807585 := bstep (se 2 (by rfl) ⟨1052844, by rfl⟩ : syracuseStep 2807585 = 2105689) B2105689
theorem B6403873 : Blo 1246441 6403873 := bstep (se 2 (by rfl) ⟨2401452, by rfl⟩ : syracuseStep 6403873 = 4802905) B4802905
theorem B6313787 : Blo 1246441 6313787 := bstep (se 1 (by rfl) ⟨4735340, by rfl⟩ : syracuseStep 6313787 = 9470681) B9470681
theorem B7100369 : Blo 1246441 7100369 := bstep (se 2 (by rfl) ⟨2662638, by rfl⟩ : syracuseStep 7100369 = 5325277) B5325277
theorem B6313949 : Blo 1246441 6313949 := bstep (se 3 (by rfl) ⟨1183865, by rfl⟩ : syracuseStep 6313949 = 2367731) B2367731
theorem B4208651 : Blo 1246441 4208651 := bstep (se 1 (by rfl) ⟨3156488, by rfl⟩ : syracuseStep 4208651 = 6312977) B6312977
theorem B20510765 : Blo 1246441 20510765 := bstep (se 3 (by rfl) ⟨3845768, by rfl⟩ : syracuseStep 20510765 = 7691537) B7691537
theorem B4208759 : Blo 1246441 4208759 := bstep (se 1 (by rfl) ⟨3156569, by rfl⟩ : syracuseStep 4208759 = 6313139) B6313139
theorem B2807927 : Blo 1246441 2807927 := bstep (se 1 (by rfl) ⟨2105945, by rfl⟩ : syracuseStep 2807927 = 4211891) B4211891
theorem B3553465 : Blo 1246441 3553465 := bstep (se 2 (by rfl) ⟨1332549, by rfl⟩ : syracuseStep 3553465 = 2665099) B2665099
theorem B3791119 : Blo 1246441 3791119 := bstep (se 1 (by rfl) ⟨2843339, by rfl⟩ : syracuseStep 3791119 = 5686679) B5686679
theorem B6314273 : Blo 1246441 6314273 := bstep (se 2 (by rfl) ⟨2367852, by rfl⟩ : syracuseStep 6314273 = 4735705) B4735705
theorem B2808107 : Blo 1246441 2808107 := bstep (se 1 (by rfl) ⟨2106080, by rfl⟩ : syracuseStep 2808107 = 4212161) B4212161
theorem B2103671 : Blo 1246441 2103671 := bstep (se 1 (by rfl) ⟨1577753, by rfl⟩ : syracuseStep 2103671 = 3155507) B3155507
theorem B7297465 : Blo 1246441 7297465 := bstep (se 2 (by rfl) ⟨2736549, by rfl⟩ : syracuseStep 7297465 = 5473099) B5473099
theorem B3037625 : Blo 1246441 3037625 := bstep (se 2 (by rfl) ⟨1139109, by rfl⟩ : syracuseStep 3037625 = 2278219) B2278219
theorem B1685947 : Blo 1246441 1685947 := bstep (se 1 (by rfl) ⟨1264460, by rfl⟩ : syracuseStep 1685947 = 2528921) B2528921
theorem B3373579 : Blo 1246441 3373579 := bstep (se 1 (by rfl) ⟨2530184, by rfl⟩ : syracuseStep 3373579 = 5060369) B5060369
theorem B3553807 : Blo 1246441 3553807 := bstep (se 1 (by rfl) ⟨2665355, by rfl⟩ : syracuseStep 3553807 = 5330711) B5330711
theorem B3373687 : Blo 1246441 3373687 := bstep (se 1 (by rfl) ⟨2530265, by rfl⟩ : syracuseStep 3373687 = 5060531) B5060531
theorem B2808467 : Blo 1246441 2808467 := bstep (se 1 (by rfl) ⟨2106350, by rfl⟩ : syracuseStep 2808467 = 4212701) B4212701
theorem B4209353 : Blo 1246441 4209353 := bstep (se 2 (by rfl) ⟨1578507, by rfl⟩ : syracuseStep 4209353 = 3157015) B3157015
theorem B2808521 : Blo 1246441 2808521 := bstep (se 2 (by rfl) ⟨1053195, by rfl⟩ : syracuseStep 2808521 = 2106391) B2106391
theorem B3554081 : Blo 1246441 3554081 := bstep (se 2 (by rfl) ⟨1332780, by rfl⟩ : syracuseStep 3554081 = 2665561) B2665561
theorem B1579819 : Blo 1246441 1579819 := bstep (se 1 (by rfl) ⟨1184864, by rfl⟩ : syracuseStep 1579819 = 2369729) B2369729
theorem B2104123 : Blo 1246441 2104123 := bstep (se 1 (by rfl) ⟨1578092, by rfl⟩ : syracuseStep 2104123 = 3156185) B3156185
theorem B2366327 : Blo 1246441 2366327 := bstep (se 1 (by rfl) ⟨1774745, by rfl⟩ : syracuseStep 2366327 = 3549491) B3549491
theorem B2104265 : Blo 1246441 2104265 := bstep (se 2 (by rfl) ⟨789099, by rfl⟩ : syracuseStep 2104265 = 1578199) B1578199
theorem B17538053 : Blo 1246441 17538053 := bstep (se 4 (by rfl) ⟨1644192, by rfl⟩ : syracuseStep 17538053 = 3288385) B3288385
theorem B23976971 : Blo 1246441 23976971 := bstep (se 1 (by rfl) ⟨17982728, by rfl⟩ : syracuseStep 23976971 = 35965457) B35965457
theorem B46767253 : Blo 1246441 46767253 := bstep (se 6 (by rfl) ⟨1096107, by rfl⟩ : syracuseStep 46767253 = 2192215) B2192215
theorem B7584961 : Blo 1246441 7584961 := bstep (se 2 (by rfl) ⟨2844360, by rfl⟩ : syracuseStep 7584961 = 5688721) B5688721
theorem B7986377 : Blo 1246441 7986377 := bstep (se 2 (by rfl) ⟨2994891, by rfl⟩ : syracuseStep 7986377 = 5989783) B5989783
theorem B23968973 : Blo 1246441 23968973 := bstep (se 3 (by rfl) ⟨4494182, by rfl⟩ : syracuseStep 23968973 = 8988365) B8988365
theorem B6315245 : Blo 1246441 6315245 := bstep (se 3 (by rfl) ⟨1184108, by rfl⟩ : syracuseStep 6315245 = 2368217) B2368217
theorem B4210055 : Blo 1246441 4210055 := bstep (se 1 (by rfl) ⟨3157541, by rfl⟩ : syracuseStep 4210055 = 6315083) B6315083
theorem B3554695 : Blo 1246441 3554695 := bstep (se 1 (by rfl) ⟨2666021, by rfl⟩ : syracuseStep 3554695 = 5332043) B5332043
theorem B7396753 : Blo 1246441 7396753 := bstep (se 2 (by rfl) ⟨2773782, by rfl⟩ : syracuseStep 7396753 = 5547565) B5547565
theorem B8207801 : Blo 1246441 8207801 := bstep (se 2 (by rfl) ⟨3077925, by rfl⟩ : syracuseStep 8207801 = 6155851) B6155851
theorem B30768569 : Blo 1246441 30768569 := bstep (se 2 (by rfl) ⟨11538213, by rfl⟩ : syracuseStep 30768569 = 23076427) B23076427
theorem B1777097 : Blo 1246441 1777097 := bstep (se 2 (by rfl) ⟨666411, by rfl⟩ : syracuseStep 1777097 = 1332823) B1332823
theorem B40492547 : Blo 1246441 40492547 := bstep (se 1 (by rfl) ⟨30369410, by rfl⟩ : syracuseStep 40492547 = 60738821) B60738821
theorem B4734551 : Blo 1246441 4734551 := bstep (se 1 (by rfl) ⟨3550913, by rfl⟩ : syracuseStep 4734551 = 7101827) B7101827
theorem B2104967 : Blo 1246441 2104967 := bstep (se 1 (by rfl) ⟨1578725, by rfl⟩ : syracuseStep 2104967 = 3157451) B3157451
theorem B17997491 : Blo 1246441 17997491 := bstep (se 1 (by rfl) ⟨13498118, by rfl⟩ : syracuseStep 17997491 = 26996237) B26996237
theorem B5324525 : Blo 1246441 5324525 := bstep (se 3 (by rfl) ⟨998348, by rfl⟩ : syracuseStep 5324525 = 1996697) B1996697
theorem B4210433 : Blo 1246441 4210433 := bstep (se 2 (by rfl) ⟨1578912, by rfl⟩ : syracuseStep 4210433 = 3157825) B3157825
theorem B3555083 : Blo 1246441 3555083 := bstep (se 1 (by rfl) ⟨2666312, by rfl⟩ : syracuseStep 3555083 = 5332625) B5332625
theorem B1998607 : Blo 1246441 1998607 := bstep (se 1 (by rfl) ⟨1498955, by rfl⟩ : syracuseStep 1998607 = 2997911) B2997911
theorem B3202831 : Blo 1246441 3202831 := bstep (se 1 (by rfl) ⟨2402123, by rfl⟩ : syracuseStep 3202831 = 4804247) B4804247
theorem B10649393 : Blo 1246441 10649393 := bstep (se 2 (by rfl) ⟨3993522, by rfl⟩ : syracuseStep 10649393 = 7987045) B7987045
theorem B4865939 : Blo 1246441 4865939 := bstep (se 1 (by rfl) ⟨3649454, by rfl⟩ : syracuseStep 4865939 = 7298909) B7298909
theorem B1998793 : Blo 1246441 1998793 := bstep (se 2 (by rfl) ⟨749547, by rfl⟩ : syracuseStep 1998793 = 1499095) B1499095
theorem B46768141 : Blo 1246441 46768141 := bstep (se 3 (by rfl) ⟨8769026, by rfl⟩ : syracuseStep 46768141 = 17538053) B17538053
theorem B4210703 : Blo 1246441 4210703 := bstep (se 1 (by rfl) ⟨3158027, by rfl⟩ : syracuseStep 4210703 = 6316055) B6316055
theorem B2662571 : Blo 1246441 2662571 := bstep (se 1 (by rfl) ⟨1996928, by rfl⟩ : syracuseStep 2662571 = 3993857) B3993857
theorem B4554947 : Blo 1246441 4554947 := bstep (se 1 (by rfl) ⟨3416210, by rfl⟩ : syracuseStep 4554947 = 6832421) B6832421
theorem B5054825 : Blo 1246441 5054825 := bstep (se 2 (by rfl) ⟨1895559, by rfl⟩ : syracuseStep 5054825 = 3791119) B3791119
theorem B2105743 : Blo 1246441 2105743 := bstep (se 1 (by rfl) ⟨1579307, by rfl⟩ : syracuseStep 2105743 = 3158615) B3158615
theorem B2277985 : Blo 1246441 2277985 := bstep (se 2 (by rfl) ⟨854244, by rfl⟩ : syracuseStep 2277985 = 1708489) B1708489
theorem B4211297 : Blo 1246441 4211297 := bstep (se 2 (by rfl) ⟨1579236, by rfl⟩ : syracuseStep 4211297 = 3158473) B3158473
theorem B4498105 : Blo 1246441 4498105 := bstep (se 2 (by rfl) ⟨1686789, by rfl⟩ : syracuseStep 4498105 = 3373579) B3373579
theorem B9118493 : Blo 1246441 9118493 := bstep (se 3 (by rfl) ⟨1709717, by rfl⟩ : syracuseStep 9118493 = 3419435) B3419435
theorem B4498249 : Blo 1246441 4498249 := bstep (se 2 (by rfl) ⟨1686843, by rfl⟩ : syracuseStep 4498249 = 3373687) B3373687
theorem B38396875 : Blo 1246441 38396875 := bstep (se 1 (by rfl) ⟨28797656, by rfl⟩ : syracuseStep 38396875 = 57595313) B57595313
theorem B2106425 : Blo 1246441 2106425 := bstep (se 2 (by rfl) ⟨789909, by rfl⟩ : syracuseStep 2106425 = 1579819) B1579819
theorem B2999467 : Blo 1246441 2999467 := bstep (se 1 (by rfl) ⟨2249600, by rfl⟩ : syracuseStep 2999467 = 4499201) B4499201
theorem B1246503 : Blo 1246441 1246503 := bstep (se 1 (by rfl) ⟨934877, by rfl⟩ : syracuseStep 1246503 = 1869755) B1869755
theorem B1246543 : Blo 1246441 1246543 := bstep (se 1 (by rfl) ⟨934907, by rfl⟩ : syracuseStep 1246543 = 1869815) B1869815
theorem B1246559 : Blo 1246441 1246559 := bstep (se 1 (by rfl) ⟨934919, by rfl⟩ : syracuseStep 1246559 = 1869839) B1869839
theorem B13673843 : Blo 1246441 13673843 := bstep (se 1 (by rfl) ⟨10255382, by rfl⟩ : syracuseStep 13673843 = 20510765) B20510765
theorem B1246587 : Blo 1246441 1246587 := bstep (se 1 (by rfl) ⟨934940, by rfl⟩ : syracuseStep 1246587 = 1869881) B1869881
theorem B1246639 : Blo 1246441 1246639 := bstep (se 1 (by rfl) ⟨934979, by rfl⟩ : syracuseStep 1246639 = 1869959) B1869959
theorem B1246663 : Blo 1246441 1246663 := bstep (se 1 (by rfl) ⟨934997, by rfl⟩ : syracuseStep 1246663 = 1869995) B1869995
theorem B6317513 : Blo 1246441 6317513 := bstep (se 2 (by rfl) ⟨2369067, by rfl⟩ : syracuseStep 6317513 = 4738135) B4738135
theorem B1246683 : Blo 1246441 1246683 := bstep (se 1 (by rfl) ⟨935012, by rfl⟩ : syracuseStep 1246683 = 1870025) B1870025
theorem B1246759 : Blo 1246441 1246759 := bstep (se 1 (by rfl) ⟨935069, by rfl⟩ : syracuseStep 1246759 = 1870139) B1870139
theorem B1402447 : Blo 1246441 1402447 := bstep (se 1 (by rfl) ⟨1051835, by rfl⟩ : syracuseStep 1402447 = 2103671) B2103671
theorem B1246799 : Blo 1246441 1246799 := bstep (se 1 (by rfl) ⟨935099, by rfl⟩ : syracuseStep 1246799 = 1870199) B1870199
theorem B1246815 : Blo 1246441 1246815 := bstep (se 1 (by rfl) ⟨935111, by rfl⟩ : syracuseStep 1246815 = 1870223) B1870223
theorem B1246843 : Blo 1246441 1246843 := bstep (se 1 (by rfl) ⟨935132, by rfl⟩ : syracuseStep 1246843 = 1870265) B1870265
theorem B2025083 : Blo 1246441 2025083 := bstep (se 1 (by rfl) ⟨1518812, by rfl⟩ : syracuseStep 2025083 = 3037625) B3037625
theorem B1246895 : Blo 1246441 1246895 := bstep (se 1 (by rfl) ⟨935171, by rfl⟩ : syracuseStep 1246895 = 1870343) B1870343
theorem B1246919 : Blo 1246441 1246919 := bstep (se 1 (by rfl) ⟨935189, by rfl⟩ : syracuseStep 1246919 = 1870379) B1870379
theorem B3999431 : Blo 1246441 3999431 := bstep (se 1 (by rfl) ⟨2999573, by rfl⟩ : syracuseStep 3999431 = 5999147) B5999147
theorem B1246939 : Blo 1246441 1246939 := bstep (se 1 (by rfl) ⟨935204, by rfl⟩ : syracuseStep 1246939 = 1870409) B1870409
theorem B30361337 : Blo 1246441 30361337 := bstep (se 2 (by rfl) ⟨11385501, by rfl⟩ : syracuseStep 30361337 = 22771003) B22771003
theorem B1247015 : Blo 1246441 1247015 := bstep (se 1 (by rfl) ⟨935261, by rfl⟩ : syracuseStep 1247015 = 1870523) B1870523
theorem B8210219 : Blo 1246441 8210219 := bstep (se 1 (by rfl) ⟨6157664, by rfl⟩ : syracuseStep 8210219 = 12315329) B12315329
theorem B1247055 : Blo 1246441 1247055 := bstep (se 1 (by rfl) ⟨935291, by rfl⟩ : syracuseStep 1247055 = 1870583) B1870583
theorem B1247071 : Blo 1246441 1247071 := bstep (se 1 (by rfl) ⟨935303, by rfl⟩ : syracuseStep 1247071 = 1870607) B1870607
theorem B2369387 : Blo 1246441 2369387 := bstep (se 1 (by rfl) ⟨1777040, by rfl⟩ : syracuseStep 2369387 = 3554081) B3554081
theorem B1247099 : Blo 1246441 1247099 := bstep (se 1 (by rfl) ⟨935324, by rfl⟩ : syracuseStep 1247099 = 1870649) B1870649
theorem B1869743 : Blo 1246441 1869743 := bstep (se 1 (by rfl) ⟨1402307, by rfl⟩ : syracuseStep 1869743 = 2804615) B2804615
theorem B1247151 : Blo 1246441 1247151 := bstep (se 1 (by rfl) ⟨935363, by rfl⟩ : syracuseStep 1247151 = 1870727) B1870727
theorem B4736951 : Blo 1246441 4736951 := bstep (se 1 (by rfl) ⟨3552713, by rfl⟩ : syracuseStep 4736951 = 7105427) B7105427
theorem B1247175 : Blo 1246441 1247175 := bstep (se 1 (by rfl) ⟨935381, by rfl⟩ : syracuseStep 1247175 = 1870763) B1870763
theorem B1402843 : Blo 1246441 1402843 := bstep (se 1 (by rfl) ⟨1052132, by rfl⟩ : syracuseStep 1402843 = 2104265) B2104265
theorem B1247195 : Blo 1246441 1247195 := bstep (se 1 (by rfl) ⟨935396, by rfl⟩ : syracuseStep 1247195 = 1870793) B1870793
theorem B15984647 : Blo 1246441 15984647 := bstep (se 1 (by rfl) ⟨11988485, by rfl⟩ : syracuseStep 15984647 = 23976971) B23976971
theorem B1869833 : Blo 1246441 1869833 := bstep (se 2 (by rfl) ⟨701187, by rfl⟩ : syracuseStep 1869833 = 1402375) B1402375
theorem B4212755 : Blo 1246441 4212755 := bstep (se 1 (by rfl) ⟨3159566, by rfl⟩ : syracuseStep 4212755 = 6319133) B6319133
theorem B1869863 : Blo 1246441 1869863 := bstep (se 1 (by rfl) ⟨1402397, by rfl⟩ : syracuseStep 1869863 = 2804795) B2804795
theorem B1247271 : Blo 1246441 1247271 := bstep (se 1 (by rfl) ⟨935453, by rfl⟩ : syracuseStep 1247271 = 1870907) B1870907
theorem B1247311 : Blo 1246441 1247311 := bstep (se 1 (by rfl) ⟨935483, by rfl⟩ : syracuseStep 1247311 = 1870967) B1870967
theorem B6318161 : Blo 1246441 6318161 := bstep (se 2 (by rfl) ⟨2369310, by rfl⟩ : syracuseStep 6318161 = 4738621) B4738621
theorem B1247327 : Blo 1246441 1247327 := bstep (se 1 (by rfl) ⟨935495, by rfl⟩ : syracuseStep 1247327 = 1870991) B1870991
theorem B20244581 : Blo 1246441 20244581 := bstep (se 4 (by rfl) ⟨1897929, by rfl⟩ : syracuseStep 20244581 = 3795859) B3795859
theorem B1869947 : Blo 1246441 1869947 := bstep (se 1 (by rfl) ⟨1402460, by rfl⟩ : syracuseStep 1869947 = 2804921) B2804921
theorem B1247355 : Blo 1246441 1247355 := bstep (se 1 (by rfl) ⟨935516, by rfl⟩ : syracuseStep 1247355 = 1871033) B1871033
theorem B1247407 : Blo 1246441 1247407 := bstep (se 1 (by rfl) ⟨935555, by rfl⟩ : syracuseStep 1247407 = 1871111) B1871111
theorem B1247431 : Blo 1246441 1247431 := bstep (se 1 (by rfl) ⟨935573, by rfl⟩ : syracuseStep 1247431 = 1871147) B1871147
theorem B1247451 : Blo 1246441 1247451 := bstep (se 1 (by rfl) ⟨935588, by rfl⟩ : syracuseStep 1247451 = 1871177) B1871177
theorem B1870073 : Blo 1246441 1870073 := bstep (se 2 (by rfl) ⟨701277, by rfl⟩ : syracuseStep 1870073 = 1402555) B1402555
theorem B8997131 : Blo 1246441 8997131 := bstep (se 1 (by rfl) ⟨6747848, by rfl⟩ : syracuseStep 8997131 = 13495697) B13495697
theorem B1247527 : Blo 1246441 1247527 := bstep (se 1 (by rfl) ⟨935645, by rfl⟩ : syracuseStep 1247527 = 1871291) B1871291
theorem B1247567 : Blo 1246441 1247567 := bstep (se 1 (by rfl) ⟨935675, by rfl⟩ : syracuseStep 1247567 = 1871351) B1871351
theorem B4213079 : Blo 1246441 4213079 := bstep (se 1 (by rfl) ⟨3159809, by rfl⟩ : syracuseStep 4213079 = 6319619) B6319619
theorem B26995031 : Blo 1246441 26995031 := bstep (se 1 (by rfl) ⟨20246273, by rfl⟩ : syracuseStep 26995031 = 40492547) B40492547
theorem B1870175 : Blo 1246441 1870175 := bstep (se 1 (by rfl) ⟨1402631, by rfl⟩ : syracuseStep 1870175 = 2805263) B2805263
theorem B1247583 : Blo 1246441 1247583 := bstep (se 1 (by rfl) ⟨935687, by rfl⟩ : syracuseStep 1247583 = 1871375) B1871375
theorem B2664809 : Blo 1246441 2664809 := bstep (se 2 (by rfl) ⟨999303, by rfl⟩ : syracuseStep 2664809 = 1998607) B1998607
theorem B4270441 : Blo 1246441 4270441 := bstep (se 2 (by rfl) ⟨1601415, by rfl⟩ : syracuseStep 4270441 = 3202831) B3202831
theorem B1870187 : Blo 1246441 1870187 := bstep (se 1 (by rfl) ⟨1402640, by rfl⟩ : syracuseStep 1870187 = 2805281) B2805281
theorem B1247611 : Blo 1246441 1247611 := bstep (se 1 (by rfl) ⟨935708, by rfl⟩ : syracuseStep 1247611 = 1871417) B1871417
theorem B8538497 : Blo 1246441 8538497 := bstep (se 2 (by rfl) ⟨3201936, by rfl⟩ : syracuseStep 8538497 = 6403873) B6403873
theorem B3156367 : Blo 1246441 3156367 := bstep (se 1 (by rfl) ⟨2367275, by rfl⟩ : syracuseStep 3156367 = 4734551) B4734551
theorem B10652057 : Blo 1246441 10652057 := bstep (se 2 (by rfl) ⟨3994521, by rfl⟩ : syracuseStep 10652057 = 7989043) B7989043
theorem B1403311 : Blo 1246441 1403311 := bstep (se 1 (by rfl) ⟨1052483, by rfl⟩ : syracuseStep 1403311 = 2104967) B2104967
theorem B1247663 : Blo 1246441 1247663 := bstep (se 1 (by rfl) ⟨935747, by rfl⟩ : syracuseStep 1247663 = 1871495) B1871495
theorem B1247687 : Blo 1246441 1247687 := bstep (se 1 (by rfl) ⟨935765, by rfl⟩ : syracuseStep 1247687 = 1871531) B1871531
theorem B1247707 : Blo 1246441 1247707 := bstep (se 1 (by rfl) ⟨935780, by rfl⟩ : syracuseStep 1247707 = 1871561) B1871561
theorem B3549683 : Blo 1246441 3549683 := bstep (se 1 (by rfl) ⟨2662262, by rfl⟩ : syracuseStep 3549683 = 5324525) B5324525
theorem B2370055 : Blo 1246441 2370055 := bstep (se 1 (by rfl) ⟨1777541, by rfl⟩ : syracuseStep 2370055 = 3555083) B3555083
theorem B1247783 : Blo 1246441 1247783 := bstep (se 1 (by rfl) ⟨935837, by rfl⟩ : syracuseStep 1247783 = 1871675) B1871675
theorem B1870415 : Blo 1246441 1870415 := bstep (se 1 (by rfl) ⟨1402811, by rfl⟩ : syracuseStep 1870415 = 2805623) B2805623
theorem B1247823 : Blo 1246441 1247823 := bstep (se 1 (by rfl) ⟨935867, by rfl⟩ : syracuseStep 1247823 = 1871735) B1871735
theorem B1247839 : Blo 1246441 1247839 := bstep (se 1 (by rfl) ⟨935879, by rfl⟩ : syracuseStep 1247839 = 1871759) B1871759
theorem B2665057 : Blo 1246441 2665057 := bstep (se 2 (by rfl) ⟨999396, by rfl⟩ : syracuseStep 2665057 = 1998793) B1998793
theorem B1247867 : Blo 1246441 1247867 := bstep (se 1 (by rfl) ⟨935900, by rfl⟩ : syracuseStep 1247867 = 1871801) B1871801
theorem B1247919 : Blo 1246441 1247919 := bstep (se 1 (by rfl) ⟨935939, by rfl⟩ : syracuseStep 1247919 = 1871879) B1871879
theorem B4270781 : Blo 1246441 4270781 := bstep (se 3 (by rfl) ⟨800771, by rfl⟩ : syracuseStep 4270781 = 1601543) B1601543
theorem B1870535 : Blo 1246441 1870535 := bstep (se 1 (by rfl) ⟨1402901, by rfl⟩ : syracuseStep 1870535 = 2805803) B2805803
theorem B1247943 : Blo 1246441 1247943 := bstep (se 1 (by rfl) ⟨935957, by rfl⟩ : syracuseStep 1247943 = 1871915) B1871915
theorem B3156691 : Blo 1246441 3156691 := bstep (se 1 (by rfl) ⟨2367518, by rfl⟩ : syracuseStep 3156691 = 4735037) B4735037
theorem B1247963 : Blo 1246441 1247963 := bstep (se 1 (by rfl) ⟨935972, by rfl⟩ : syracuseStep 1247963 = 1871945) B1871945
theorem B1248039 : Blo 1246441 1248039 := bstep (se 1 (by rfl) ⟨936029, by rfl⟩ : syracuseStep 1248039 = 1872059) B1872059
theorem B1248079 : Blo 1246441 1248079 := bstep (se 1 (by rfl) ⟨936059, by rfl⟩ : syracuseStep 1248079 = 1872119) B1872119
theorem B1403743 : Blo 1246441 1403743 := bstep (se 1 (by rfl) ⟨1052807, by rfl⟩ : syracuseStep 1403743 = 2105615) B2105615
theorem B1248095 : Blo 1246441 1248095 := bstep (se 1 (by rfl) ⟨936071, by rfl⟩ : syracuseStep 1248095 = 1872143) B1872143
theorem B1870697 : Blo 1246441 1870697 := bstep (se 2 (by rfl) ⟨701511, by rfl⟩ : syracuseStep 1870697 = 1403023) B1403023
theorem B1248123 : Blo 1246441 1248123 := bstep (se 1 (by rfl) ⟨936092, by rfl⟩ : syracuseStep 1248123 = 1872185) B1872185
theorem B4737953 : Blo 1246441 4737953 := bstep (se 2 (by rfl) ⟨1776732, by rfl⟩ : syracuseStep 4737953 = 3553465) B3553465
theorem B1248175 : Blo 1246441 1248175 := bstep (se 1 (by rfl) ⟨936131, by rfl⟩ : syracuseStep 1248175 = 1872263) B1872263
theorem B1870775 : Blo 1246441 1870775 := bstep (se 1 (by rfl) ⟨1403081, by rfl⟩ : syracuseStep 1870775 = 2806163) B2806163
theorem B2665399 : Blo 1246441 2665399 := bstep (se 1 (by rfl) ⟨1999049, by rfl⟩ : syracuseStep 2665399 = 3998099) B3998099
theorem B3550139 : Blo 1246441 3550139 := bstep (se 1 (by rfl) ⟨2662604, by rfl⟩ : syracuseStep 3550139 = 5325209) B5325209
theorem B1248199 : Blo 1246441 1248199 := bstep (se 1 (by rfl) ⟨936149, by rfl⟩ : syracuseStep 1248199 = 1872299) B1872299
theorem B1870811 : Blo 1246441 1870811 := bstep (se 1 (by rfl) ⟨1403108, by rfl⟩ : syracuseStep 1870811 = 2806217) B2806217
theorem B1248219 : Blo 1246441 1248219 := bstep (se 1 (by rfl) ⟨936164, by rfl⟩ : syracuseStep 1248219 = 1872329) B1872329
theorem B1248295 : Blo 1246441 1248295 := bstep (se 1 (by rfl) ⟨936221, by rfl⟩ : syracuseStep 1248295 = 1872443) B1872443
theorem B7580723 : Blo 1246441 7580723 := bstep (se 1 (by rfl) ⟨5685542, by rfl⟩ : syracuseStep 7580723 = 11371085) B11371085
theorem B1248335 : Blo 1246441 1248335 := bstep (se 1 (by rfl) ⟨936251, by rfl⟩ : syracuseStep 1248335 = 1872503) B1872503
theorem B1248351 : Blo 1246441 1248351 := bstep (se 1 (by rfl) ⟨936263, by rfl⟩ : syracuseStep 1248351 = 1872527) B1872527
theorem B1248379 : Blo 1246441 1248379 := bstep (se 1 (by rfl) ⟨936284, by rfl⟩ : syracuseStep 1248379 = 1872569) B1872569
theorem B1248431 : Blo 1246441 1248431 := bstep (se 1 (by rfl) ⟨936323, by rfl⟩ : syracuseStep 1248431 = 1872647) B1872647
theorem B1404103 : Blo 1246441 1404103 := bstep (se 1 (by rfl) ⟨1053077, by rfl⟩ : syracuseStep 1404103 = 2106155) B2106155
theorem B2247929 : Blo 1246441 2247929 := bstep (se 2 (by rfl) ⟨842973, by rfl⟩ : syracuseStep 2247929 = 1685947) B1685947
theorem B4738409 : Blo 1246441 4738409 := bstep (se 2 (by rfl) ⟨1776903, by rfl⟩ : syracuseStep 4738409 = 3553807) B3553807
theorem B3370369 : Blo 1246441 3370369 := bstep (se 2 (by rfl) ⟨1263888, by rfl⟩ : syracuseStep 3370369 = 2527777) B2527777
theorem B15183247 : Blo 1246441 15183247 := bstep (se 1 (by rfl) ⟨11387435, by rfl⟩ : syracuseStep 15183247 = 22774871) B22774871
theorem B1871279 : Blo 1246441 1871279 := bstep (se 1 (by rfl) ⟨1403459, by rfl⟩ : syracuseStep 1871279 = 2806919) B2806919
theorem B1871369 : Blo 1246441 1871369 := bstep (se 2 (by rfl) ⟨701763, by rfl⟩ : syracuseStep 1871369 = 1403527) B1403527
theorem B1871399 : Blo 1246441 1871399 := bstep (se 1 (by rfl) ⟨1403549, by rfl⟩ : syracuseStep 1871399 = 2807099) B2807099
theorem B9473597 : Blo 1246441 9473597 := bstep (se 3 (by rfl) ⟨1776299, by rfl⟩ : syracuseStep 9473597 = 3552599) B3552599
theorem B2805371 : Blo 1246441 2805371 := bstep (se 1 (by rfl) ⟨2104028, by rfl⟩ : syracuseStep 2805371 = 4208057) B4208057
theorem B1871483 : Blo 1246441 1871483 := bstep (se 1 (by rfl) ⟨1403612, by rfl⟩ : syracuseStep 1871483 = 2807225) B2807225
theorem B17993339 : Blo 1246441 17993339 := bstep (se 1 (by rfl) ⟨13495004, by rfl⟩ : syracuseStep 17993339 = 26990009) B26990009
theorem B3157643 : Blo 1246441 3157643 := bstep (se 1 (by rfl) ⟨2368232, by rfl⟩ : syracuseStep 3157643 = 4736465) B4736465
theorem B2248391 : Blo 1246441 2248391 := bstep (se 1 (by rfl) ⟨1686293, by rfl⟩ : syracuseStep 2248391 = 3372587) B3372587
theorem B2805497 : Blo 1246441 2805497 := bstep (se 2 (by rfl) ⟨1052061, by rfl⟩ : syracuseStep 2805497 = 2104123) B2104123
theorem B1871609 : Blo 1246441 1871609 := bstep (se 2 (by rfl) ⟨701853, by rfl⟩ : syracuseStep 1871609 = 1403707) B1403707
theorem B655789891 : Blo 1246441 655789891 := bstep (se 1 (by rfl) ⟨491842418, by rfl⟩ : syracuseStep 655789891 = 983684837) B983684837
theorem B1871711 : Blo 1246441 1871711 := bstep (se 1 (by rfl) ⟨1403783, by rfl⟩ : syracuseStep 1871711 = 2807567) B2807567
theorem B1871723 : Blo 1246441 1871723 := bstep (se 1 (by rfl) ⟨1403792, by rfl⟩ : syracuseStep 1871723 = 2807585) B2807585
theorem B4738925 : Blo 1246441 4738925 := bstep (se 3 (by rfl) ⟨888548, by rfl⟩ : syracuseStep 4738925 = 1777097) B1777097
theorem B2805767 : Blo 1246441 2805767 := bstep (se 1 (by rfl) ⟨2104325, by rfl⟩ : syracuseStep 2805767 = 4208651) B4208651
theorem B2805839 : Blo 1246441 2805839 := bstep (se 1 (by rfl) ⟨2104379, by rfl⟩ : syracuseStep 2805839 = 4208759) B4208759
theorem B1871951 : Blo 1246441 1871951 := bstep (se 1 (by rfl) ⟨1403963, by rfl⟩ : syracuseStep 1871951 = 2807927) B2807927
theorem B1872071 : Blo 1246441 1872071 := bstep (se 1 (by rfl) ⟨1404053, by rfl⟩ : syracuseStep 1872071 = 2808107) B2808107
theorem B10113281 : Blo 1246441 10113281 := bstep (se 2 (by rfl) ⟨3792480, by rfl⟩ : syracuseStep 10113281 = 7584961) B7584961
theorem B1872233 : Blo 1246441 1872233 := bstep (se 2 (by rfl) ⟨702087, by rfl⟩ : syracuseStep 1872233 = 1404175) B1404175
theorem B5058941 : Blo 1246441 5058941 := bstep (se 3 (by rfl) ⟨948551, by rfl⟩ : syracuseStep 5058941 = 1897103) B1897103
theorem B4206977 : Blo 1246441 4206977 := bstep (se 2 (by rfl) ⟨1577616, by rfl⟩ : syracuseStep 4206977 = 3155233) B3155233
theorem B1872311 : Blo 1246441 1872311 := bstep (se 1 (by rfl) ⟨1404233, by rfl⟩ : syracuseStep 1872311 = 2808467) B2808467
theorem B2806235 : Blo 1246441 2806235 := bstep (se 1 (by rfl) ⟨2104676, by rfl⟩ : syracuseStep 2806235 = 4209353) B4209353
theorem B1872347 : Blo 1246441 1872347 := bstep (se 1 (by rfl) ⟨1404260, by rfl⟩ : syracuseStep 1872347 = 2808521) B2808521
theorem B9474569 : Blo 1246441 9474569 := bstep (se 2 (by rfl) ⟨3552963, by rfl⟩ : syracuseStep 9474569 = 7105927) B7105927
theorem B4739593 : Blo 1246441 4739593 := bstep (se 2 (by rfl) ⟨1777347, by rfl⟩ : syracuseStep 4739593 = 3554695) B3554695
theorem B1577551 : Blo 1246441 1577551 := bstep (se 1 (by rfl) ⟨1183163, by rfl⟩ : syracuseStep 1577551 = 2366327) B2366327
theorem B7992017 : Blo 1246441 7992017 := bstep (se 2 (by rfl) ⟨2997006, by rfl⟩ : syracuseStep 7992017 = 5994013) B5994013
theorem B3158777 : Blo 1246441 3158777 := bstep (se 2 (by rfl) ⟨1184541, by rfl⟩ : syracuseStep 3158777 = 2369083) B2369083
theorem B23966513 : Blo 1246441 23966513 := bstep (se 2 (by rfl) ⟨8987442, by rfl⟩ : syracuseStep 23966513 = 17974885) B17974885
theorem B15979315 : Blo 1246441 15979315 := bstep (se 1 (by rfl) ⟨11984486, by rfl⟩ : syracuseStep 15979315 = 23968973) B23968973
theorem B2806703 : Blo 1246441 2806703 := bstep (se 1 (by rfl) ⟨2105027, by rfl⟩ : syracuseStep 2806703 = 4210055) B4210055
theorem B3158959 : Blo 1246441 3158959 := bstep (se 1 (by rfl) ⟨2369219, by rfl⟩ : syracuseStep 3158959 = 4738439) B4738439
theorem B11998327 : Blo 1246441 11998327 := bstep (se 1 (by rfl) ⟨8998745, by rfl⟩ : syracuseStep 11998327 = 17997491) B17997491
theorem B4207787 : Blo 1246441 4207787 := bstep (se 1 (by rfl) ⟨3155840, by rfl⟩ : syracuseStep 4207787 = 6311681) B6311681
theorem B2806955 : Blo 1246441 2806955 := bstep (se 1 (by rfl) ⟨2105216, by rfl⟩ : syracuseStep 2806955 = 4210433) B4210433
theorem B7099595 : Blo 1246441 7099595 := bstep (se 1 (by rfl) ⟨5324696, by rfl⟩ : syracuseStep 7099595 = 10649393) B10649393
theorem B1684843 : Blo 1246441 1684843 := bstep (se 1 (by rfl) ⟨1263632, by rfl⟩ : syracuseStep 1684843 = 2527265) B2527265
theorem B3159425 : Blo 1246441 3159425 := bstep (se 2 (by rfl) ⟨1184784, by rfl⟩ : syracuseStep 3159425 = 2369569) B2369569
theorem B9467279 : Blo 1246441 9467279 := bstep (se 1 (by rfl) ⟨7100459, by rfl⟩ : syracuseStep 9467279 = 14200919) B14200919
theorem B16430501 : Blo 1246441 16430501 := bstep (se 4 (by rfl) ⟨1540359, by rfl⟩ : syracuseStep 16430501 = 3080719) B3080719
theorem B1578619 : Blo 1246441 1578619 := bstep (se 1 (by rfl) ⟨1183964, by rfl⟩ : syracuseStep 1578619 = 2367929) B2367929
theorem B5691019 : Blo 1246441 5691019 := bstep (se 1 (by rfl) ⟨4268264, by rfl⟩ : syracuseStep 5691019 = 8536529) B8536529
theorem B4208327 : Blo 1246441 4208327 := bstep (se 1 (by rfl) ⟨3156245, by rfl⟩ : syracuseStep 4208327 = 6312491) B6312491
theorem B2807495 : Blo 1246441 2807495 := bstep (se 1 (by rfl) ⟨2105621, by rfl⟩ : syracuseStep 2807495 = 4211243) B4211243
theorem B35944235 : Blo 1246441 35944235 := bstep (se 1 (by rfl) ⟨26958176, by rfl⟩ : syracuseStep 35944235 = 53916353) B53916353
theorem B5994283 : Blo 1246441 5994283 := bstep (se 1 (by rfl) ⟨4495712, by rfl⟩ : syracuseStep 5994283 = 8991425) B8991425
theorem B8992579 : Blo 1246441 8992579 := bstep (se 1 (by rfl) ⟨6744434, by rfl⟩ : syracuseStep 8992579 = 13488869) B13488869
theorem B4265801 : Blo 1246441 4265801 := bstep (se 2 (by rfl) ⟨1599675, by rfl⟩ : syracuseStep 4265801 = 3199351) B3199351
theorem B3159881 : Blo 1246441 3159881 := bstep (se 2 (by rfl) ⟨1184955, by rfl⟩ : syracuseStep 3159881 = 2369911) B2369911
theorem B1578847 : Blo 1246441 1578847 := bstep (se 1 (by rfl) ⟨1184135, by rfl⟩ : syracuseStep 1578847 = 2368271) B2368271
theorem B21297005 : Blo 1246441 21297005 := bstep (se 3 (by rfl) ⟨3993188, by rfl⟩ : syracuseStep 21297005 = 7986377) B7986377
theorem B9729953 : Blo 1246441 9729953 := bstep (se 2 (by rfl) ⟨3648732, by rfl⟩ : syracuseStep 9729953 = 7297465) B7297465
theorem B9476027 : Blo 1246441 9476027 := bstep (se 1 (by rfl) ⟨7107020, by rfl⟩ : syracuseStep 9476027 = 14214041) B14214041
theorem B4495439 : Blo 1246441 4495439 := bstep (se 1 (by rfl) ⟨3371579, by rfl⟩ : syracuseStep 4495439 = 6743159) B6743159
theorem B1579439 : Blo 1246441 1579439 := bstep (se 1 (by rfl) ⟨1184579, by rfl⟩ : syracuseStep 1579439 = 2369159) B2369159
theorem B4209191 : Blo 1246441 4209191 := bstep (se 1 (by rfl) ⟨3156893, by rfl⟩ : syracuseStep 4209191 = 6313787) B6313787
theorem B2808359 : Blo 1246441 2808359 := bstep (se 1 (by rfl) ⟨2106269, by rfl⟩ : syracuseStep 2808359 = 4212539) B4212539
theorem B2103887 : Blo 1246441 2103887 := bstep (se 1 (by rfl) ⟨1577915, by rfl⟩ : syracuseStep 2103887 = 3155831) B3155831
theorem B4733579 : Blo 1246441 4733579 := bstep (se 1 (by rfl) ⟨3550184, by rfl⟩ : syracuseStep 4733579 = 7100369) B7100369
theorem B4209299 : Blo 1246441 4209299 := bstep (se 1 (by rfl) ⟨3156974, by rfl⟩ : syracuseStep 4209299 = 6313949) B6313949
theorem B4209515 : Blo 1246441 4209515 := bstep (se 1 (by rfl) ⟨3157136, by rfl⟩ : syracuseStep 4209515 = 6314273) B6314273
theorem B2808683 : Blo 1246441 2808683 := bstep (se 1 (by rfl) ⟨2106512, by rfl⟩ : syracuseStep 2808683 = 4213025) B4213025
theorem B62356337 : Blo 1246441 62356337 := bstep (se 2 (by rfl) ⟨23383626, by rfl⟩ : syracuseStep 62356337 = 46767253) B46767253
theorem B4209569 : Blo 1246441 4209569 := bstep (se 2 (by rfl) ⟨1578588, by rfl⟩ : syracuseStep 4209569 = 3157177) B3157177
theorem B2808737 : Blo 1246441 2808737 := bstep (se 2 (by rfl) ⟨1053276, by rfl⟩ : syracuseStep 2808737 = 2106553) B2106553
theorem B2366471 : Blo 1246441 2366471 := bstep (se 1 (by rfl) ⟨1774853, by rfl⟩ : syracuseStep 2366471 = 3549707) B3549707
theorem B4799569 : Blo 1246441 4799569 := bstep (se 2 (by rfl) ⟨1799838, by rfl⟩ : syracuseStep 4799569 = 3599677) B3599677
theorem B9862337 : Blo 1246441 9862337 := bstep (se 2 (by rfl) ⟨3698376, by rfl⟩ : syracuseStep 9862337 = 7396753) B7396753
theorem B2399561 : Blo 1246441 2399561 := bstep (se 2 (by rfl) ⟨899835, by rfl⟩ : syracuseStep 2399561 = 1799671) B1799671
theorem B6315407 : Blo 1246441 6315407 := bstep (se 1 (by rfl) ⟨4736555, by rfl⟩ : syracuseStep 6315407 = 9473111) B9473111
theorem B2563489 : Blo 1246441 2563489 := bstep (se 2 (by rfl) ⟨961308, by rfl⟩ : syracuseStep 2563489 = 1922617) B1922617
theorem B2104751 : Blo 1246441 2104751 := bstep (se 1 (by rfl) ⟨1578563, by rfl⟩ : syracuseStep 2104751 = 3157127) B3157127
theorem B4210163 : Blo 1246441 4210163 := bstep (se 1 (by rfl) ⟨3157622, by rfl⟩ : syracuseStep 4210163 = 6315245) B6315245
theorem B2366995 : Blo 1246441 2366995 := bstep (se 1 (by rfl) ⟨1775246, by rfl⟩ : syracuseStep 2366995 = 3550493) B3550493
theorem B5471867 : Blo 1246441 5471867 := bstep (se 1 (by rfl) ⟨4103900, by rfl⟩ : syracuseStep 5471867 = 8207801) B8207801
theorem B20512379 : Blo 1246441 20512379 := bstep (se 1 (by rfl) ⟨15384284, by rfl⟩ : syracuseStep 20512379 = 30768569) B30768569
theorem B4800185 : Blo 1246441 4800185 := bstep (se 2 (by rfl) ⟨1800069, by rfl⟩ : syracuseStep 4800185 = 3600139) B3600139
theorem B90971909 : Blo 1246441 90971909 := bstep (se 4 (by rfl) ⟨8528616, by rfl⟩ : syracuseStep 90971909 = 17057233) B17057233
theorem B2105183 : Blo 1246441 2105183 := bstep (se 1 (by rfl) ⟨1578887, by rfl⟩ : syracuseStep 2105183 = 3157775) B3157775
theorem B2564015 : Blo 1246441 2564015 := bstep (se 1 (by rfl) ⟨1923011, by rfl⟩ : syracuseStep 2564015 = 3846023) B3846023
theorem B3243959 : Blo 1246441 3243959 := bstep (se 1 (by rfl) ⟨2432969, by rfl⟩ : syracuseStep 3243959 = 4865939) B4865939
theorem B62357521 : Blo 1246441 62357521 := bstep (se 2 (by rfl) ⟨23384070, by rfl⟩ : syracuseStep 62357521 = 46768141) B46768141
theorem B6742187 : Blo 1246441 6742187 := bstep (se 1 (by rfl) ⟨5056640, by rfl⟩ : syracuseStep 6742187 = 10113281) B10113281
theorem B6316379 : Blo 1246441 6316379 := bstep (se 1 (by rfl) ⟨4737284, by rfl⟩ : syracuseStep 6316379 = 9474569) B9474569
theorem B5693921 : Blo 1246441 5693921 := bstep (se 2 (by rfl) ⟨2135220, by rfl⟩ : syracuseStep 5693921 = 4270441) B4270441
theorem B2105851 : Blo 1246441 2105851 := bstep (se 1 (by rfl) ⟨1579388, by rfl⟩ : syracuseStep 2105851 = 3158777) B3158777
theorem B6078995 : Blo 1246441 6078995 := bstep (se 1 (by rfl) ⟨4559246, by rfl⟩ : syracuseStep 6078995 = 9118493) B9118493
theorem B5997473 : Blo 1246441 5997473 := bstep (se 2 (by rfl) ⟨2249052, by rfl⟩ : syracuseStep 5997473 = 4498105) B4498105
theorem B2106283 : Blo 1246441 2106283 := bstep (se 1 (by rfl) ⟨1579712, by rfl⟩ : syracuseStep 2106283 = 3159425) B3159425
theorem B10953667 : Blo 1246441 10953667 := bstep (se 1 (by rfl) ⟨8215250, by rfl⟩ : syracuseStep 10953667 = 16430501) B16430501
theorem B4211675 : Blo 1246441 4211675 := bstep (se 1 (by rfl) ⟨3158756, by rfl⟩ : syracuseStep 4211675 = 6317513) B6317513
theorem B5997665 : Blo 1246441 5997665 := bstep (se 2 (by rfl) ⟨2249124, by rfl⟩ : syracuseStep 5997665 = 4498249) B4498249
theorem B4211837 : Blo 1246441 4211837 := bstep (se 3 (by rfl) ⟨789719, by rfl⟩ : syracuseStep 4211837 = 1579439) B1579439
theorem B23962823 : Blo 1246441 23962823 := bstep (se 1 (by rfl) ⟨17972117, by rfl⟩ : syracuseStep 23962823 = 35944235) B35944235
theorem B2843867 : Blo 1246441 2843867 := bstep (se 1 (by rfl) ⟨2132900, by rfl⟩ : syracuseStep 2843867 = 4265801) B4265801
theorem B2106587 : Blo 1246441 2106587 := bstep (se 1 (by rfl) ⟨1579940, by rfl⟩ : syracuseStep 2106587 = 3159881) B3159881
theorem B4211945 : Blo 1246441 4211945 := bstep (se 2 (by rfl) ⟨1579479, by rfl⟩ : syracuseStep 4211945 = 3158959) B3158959
theorem B14198003 : Blo 1246441 14198003 := bstep (se 1 (by rfl) ⟨10648502, by rfl⟩ : syracuseStep 14198003 = 21297005) B21297005
theorem B1246495 : Blo 1246441 1246495 := bstep (se 1 (by rfl) ⟨934871, by rfl⟩ : syracuseStep 1246495 = 1869743) B1869743
theorem B6317351 : Blo 1246441 6317351 := bstep (se 1 (by rfl) ⟨4738013, by rfl⟩ : syracuseStep 6317351 = 9476027) B9476027
theorem B1246555 : Blo 1246441 1246555 := bstep (se 1 (by rfl) ⟨934916, by rfl⟩ : syracuseStep 1246555 = 1869833) B1869833
theorem B1246575 : Blo 1246441 1246575 := bstep (se 1 (by rfl) ⟨934931, by rfl⟩ : syracuseStep 1246575 = 1869863) B1869863
theorem B4212107 : Blo 1246441 4212107 := bstep (se 1 (by rfl) ⟨3159080, by rfl⟩ : syracuseStep 4212107 = 6318161) B6318161
theorem B1246631 : Blo 1246441 1246631 := bstep (se 1 (by rfl) ⟨934973, by rfl⟩ : syracuseStep 1246631 = 1869947) B1869947
theorem B6399425 : Blo 1246441 6399425 := bstep (se 2 (by rfl) ⟨2399784, by rfl⟩ : syracuseStep 6399425 = 4799569) B4799569
theorem B1246715 : Blo 1246441 1246715 := bstep (se 1 (by rfl) ⟨935036, by rfl⟩ : syracuseStep 1246715 = 1870073) B1870073
theorem B5998087 : Blo 1246441 5998087 := bstep (se 1 (by rfl) ⟨4498565, by rfl⟩ : syracuseStep 5998087 = 8997131) B8997131
theorem B3999289 : Blo 1246441 3999289 := bstep (se 2 (by rfl) ⟨1499733, by rfl⟩ : syracuseStep 3999289 = 2999467) B2999467
theorem B1246783 : Blo 1246441 1246783 := bstep (se 1 (by rfl) ⟨935087, by rfl⟩ : syracuseStep 1246783 = 1870175) B1870175
theorem B1246791 : Blo 1246441 1246791 := bstep (se 1 (by rfl) ⟨935093, by rfl⟩ : syracuseStep 1246791 = 1870187) B1870187
theorem B1402591 : Blo 1246441 1402591 := bstep (se 1 (by rfl) ⟨1051943, by rfl⟩ : syracuseStep 1402591 = 2103887) B2103887
theorem B1246943 : Blo 1246441 1246943 := bstep (se 1 (by rfl) ⟨935207, by rfl⟩ : syracuseStep 1246943 = 1870415) B1870415
theorem B3155719 : Blo 1246441 3155719 := bstep (se 1 (by rfl) ⟨2366789, by rfl⟩ : syracuseStep 3155719 = 4733579) B4733579
theorem B1247023 : Blo 1246441 1247023 := bstep (se 1 (by rfl) ⟨935267, by rfl⟩ : syracuseStep 1247023 = 1870535) B1870535
theorem B20244329 : Blo 1246441 20244329 := bstep (se 2 (by rfl) ⟨7591623, by rfl⟩ : syracuseStep 20244329 = 15183247) B15183247
theorem B3417985 : Blo 1246441 3417985 := bstep (se 2 (by rfl) ⟨1281744, by rfl⟩ : syracuseStep 3417985 = 2563489) B2563489
theorem B1247131 : Blo 1246441 1247131 := bstep (se 1 (by rfl) ⟨935348, by rfl⟩ : syracuseStep 1247131 = 1870697) B1870697
theorem B1247183 : Blo 1246441 1247183 := bstep (se 1 (by rfl) ⟨935387, by rfl⟩ : syracuseStep 1247183 = 1870775) B1870775
theorem B1247207 : Blo 1246441 1247207 := bstep (se 1 (by rfl) ⟨935405, by rfl⟩ : syracuseStep 1247207 = 1870811) B1870811
theorem B3155993 : Blo 1246441 3155993 := bstep (se 2 (by rfl) ⟨1183497, by rfl⟩ : syracuseStep 3155993 = 2366995) B2366995
theorem B1869929 : Blo 1246441 1869929 := bstep (se 2 (by rfl) ⟨701223, by rfl⟩ : syracuseStep 1869929 = 1402447) B1402447
theorem B7588025 : Blo 1246441 7588025 := bstep (se 2 (by rfl) ⟨2845509, by rfl⟩ : syracuseStep 7588025 = 5691019) B5691019
theorem B1599707 : Blo 1246441 1599707 := bstep (se 1 (by rfl) ⟨1199780, by rfl⟩ : syracuseStep 1599707 = 2399561) B2399561
theorem B1403167 : Blo 1246441 1403167 := bstep (se 1 (by rfl) ⟨1052375, by rfl⟩ : syracuseStep 1403167 = 2104751) B2104751
theorem B1247519 : Blo 1246441 1247519 := bstep (se 1 (by rfl) ⟨935639, by rfl⟩ : syracuseStep 1247519 = 1871279) B1871279
theorem B1247579 : Blo 1246441 1247579 := bstep (se 1 (by rfl) ⟨935684, by rfl⟩ : syracuseStep 1247579 = 1871369) B1871369
theorem B1247599 : Blo 1246441 1247599 := bstep (se 1 (by rfl) ⟨935699, by rfl⟩ : syracuseStep 1247599 = 1871399) B1871399
theorem B3647911 : Blo 1246441 3647911 := bstep (se 1 (by rfl) ⟨2735933, by rfl⟩ : syracuseStep 3647911 = 5471867) B5471867
theorem B1870247 : Blo 1246441 1870247 := bstep (se 1 (by rfl) ⟨1402685, by rfl⟩ : syracuseStep 1870247 = 2805371) B2805371
theorem B1247655 : Blo 1246441 1247655 := bstep (se 1 (by rfl) ⟨935741, by rfl⟩ : syracuseStep 1247655 = 1871483) B1871483
theorem B13674919 : Blo 1246441 13674919 := bstep (se 1 (by rfl) ⟨10256189, by rfl⟩ : syracuseStep 13674919 = 20512379) B20512379
theorem B11995559 : Blo 1246441 11995559 := bstep (se 1 (by rfl) ⟨8996669, by rfl⟩ : syracuseStep 11995559 = 17993339) B17993339
theorem B1870331 : Blo 1246441 1870331 := bstep (se 1 (by rfl) ⟨1402748, by rfl⟩ : syracuseStep 1870331 = 2805497) B2805497
theorem B1247739 : Blo 1246441 1247739 := bstep (se 1 (by rfl) ⟨935804, by rfl⟩ : syracuseStep 1247739 = 1871609) B1871609
theorem B60647939 : Blo 1246441 60647939 := bstep (se 1 (by rfl) ⟨45485954, by rfl⟩ : syracuseStep 60647939 = 90971909) B90971909
theorem B1403455 : Blo 1246441 1403455 := bstep (se 1 (by rfl) ⟨1052591, by rfl⟩ : syracuseStep 1403455 = 2105183) B2105183
theorem B1247807 : Blo 1246441 1247807 := bstep (se 1 (by rfl) ⟨935855, by rfl⟩ : syracuseStep 1247807 = 1871711) B1871711
theorem B1247815 : Blo 1246441 1247815 := bstep (se 1 (by rfl) ⟨935861, by rfl⟩ : syracuseStep 1247815 = 1871723) B1871723
theorem B1870457 : Blo 1246441 1870457 := bstep (se 2 (by rfl) ⟨701421, by rfl⟩ : syracuseStep 1870457 = 1402843) B1402843
theorem B1870511 : Blo 1246441 1870511 := bstep (se 1 (by rfl) ⟨1402883, by rfl⟩ : syracuseStep 1870511 = 2805767) B2805767
theorem B1870559 : Blo 1246441 1870559 := bstep (se 1 (by rfl) ⟨1402919, by rfl⟩ : syracuseStep 1870559 = 2805839) B2805839
theorem B1247967 : Blo 1246441 1247967 := bstep (se 1 (by rfl) ⟨935975, by rfl⟩ : syracuseStep 1247967 = 1871951) B1871951
theorem B1248047 : Blo 1246441 1248047 := bstep (se 1 (by rfl) ⟨936035, by rfl⟩ : syracuseStep 1248047 = 1872071) B1872071
theorem B11987837 : Blo 1246441 11987837 := bstep (se 3 (by rfl) ⟨2247719, by rfl⟩ : syracuseStep 11987837 = 4495439) B4495439
theorem B3369883 : Blo 1246441 3369883 := bstep (se 1 (by rfl) ⟨2527412, by rfl⟩ : syracuseStep 3369883 = 5054825) B5054825
theorem B1248155 : Blo 1246441 1248155 := bstep (se 1 (by rfl) ⟨936116, by rfl⟩ : syracuseStep 1248155 = 1872233) B1872233
theorem B2804651 : Blo 1246441 2804651 := bstep (se 1 (by rfl) ⟨2103488, by rfl⟩ : syracuseStep 2804651 = 4206977) B4206977
theorem B1248207 : Blo 1246441 1248207 := bstep (se 1 (by rfl) ⟨936155, by rfl⟩ : syracuseStep 1248207 = 1872311) B1872311
theorem B1870823 : Blo 1246441 1870823 := bstep (se 1 (by rfl) ⟨1403117, by rfl⟩ : syracuseStep 1870823 = 2806235) B2806235
theorem B1248231 : Blo 1246441 1248231 := bstep (se 1 (by rfl) ⟨936173, by rfl⟩ : syracuseStep 1248231 = 1872347) B1872347
theorem B5328011 : Blo 1246441 5328011 := bstep (se 1 (by rfl) ⟨3996008, by rfl⟩ : syracuseStep 5328011 = 7992017) B7992017
theorem B15977675 : Blo 1246441 15977675 := bstep (se 1 (by rfl) ⟨11983256, by rfl⟩ : syracuseStep 15977675 = 23966513) B23966513
theorem B1871081 : Blo 1246441 1871081 := bstep (se 2 (by rfl) ⟨701655, by rfl⟩ : syracuseStep 1871081 = 1403311) B1403311
theorem B1871135 : Blo 1246441 1871135 := bstep (se 1 (by rfl) ⟨1403351, by rfl⟩ : syracuseStep 1871135 = 2806703) B2806703
theorem B6319457 : Blo 1246441 6319457 := bstep (se 2 (by rfl) ⟨2369796, by rfl⟩ : syracuseStep 6319457 = 4739593) B4739593
theorem B1404283 : Blo 1246441 1404283 := bstep (se 1 (by rfl) ⟨1053212, by rfl⟩ : syracuseStep 1404283 = 2106425) B2106425
theorem B2805191 : Blo 1246441 2805191 := bstep (se 1 (by rfl) ⟨2103893, by rfl⟩ : syracuseStep 2805191 = 4207787) B4207787
theorem B1871303 : Blo 1246441 1871303 := bstep (se 1 (by rfl) ⟨1403477, by rfl⟩ : syracuseStep 1871303 = 2806955) B2806955
theorem B6311519 : Blo 1246441 6311519 := bstep (se 1 (by rfl) ⟨4733639, by rfl⟩ : syracuseStep 6311519 = 9467279) B9467279
theorem B1871657 : Blo 1246441 1871657 := bstep (se 2 (by rfl) ⟨701871, by rfl⟩ : syracuseStep 1871657 = 1403743) B1403743
theorem B2805551 : Blo 1246441 2805551 := bstep (se 1 (by rfl) ⟨2104163, by rfl⟩ : syracuseStep 2805551 = 4208327) B4208327
theorem B1871663 : Blo 1246441 1871663 := bstep (se 1 (by rfl) ⟨1403747, by rfl⟩ : syracuseStep 1871663 = 2807495) B2807495
theorem B2666287 : Blo 1246441 2666287 := bstep (se 1 (by rfl) ⟨1999715, by rfl⟩ : syracuseStep 2666287 = 3999431) B3999431
theorem B51195833 : Blo 1246441 51195833 := bstep (se 2 (by rfl) ⟨19198437, by rfl⟩ : syracuseStep 51195833 = 38396875) B38396875
theorem B3157967 : Blo 1246441 3157967 := bstep (se 1 (by rfl) ⟨2368475, by rfl⟩ : syracuseStep 3157967 = 4736951) B4736951
theorem B9465821 : Blo 1246441 9465821 := bstep (se 3 (by rfl) ⟨1774841, by rfl⟩ : syracuseStep 9465821 = 3549683) B3549683
theorem B13496387 : Blo 1246441 13496387 := bstep (se 1 (by rfl) ⟨10122290, by rfl⟩ : syracuseStep 13496387 = 20244581) B20244581
theorem B1872137 : Blo 1246441 1872137 := bstep (se 2 (by rfl) ⟨702051, by rfl⟩ : syracuseStep 1872137 = 1404103) B1404103
theorem B2806127 : Blo 1246441 2806127 := bstep (se 1 (by rfl) ⟨2104595, by rfl⟩ : syracuseStep 2806127 = 4209191) B4209191
theorem B1872239 : Blo 1246441 1872239 := bstep (se 1 (by rfl) ⟨1404179, by rfl⟩ : syracuseStep 1872239 = 2808359) B2808359
theorem B2806199 : Blo 1246441 2806199 := bstep (se 1 (by rfl) ⟨2104649, by rfl⟩ : syracuseStep 2806199 = 4209299) B4209299
theorem B2847187 : Blo 1246441 2847187 := bstep (se 1 (by rfl) ⟨2135390, by rfl⟩ : syracuseStep 2847187 = 4270781) B4270781
theorem B4493825 : Blo 1246441 4493825 := bstep (se 2 (by rfl) ⟨1685184, by rfl⟩ : syracuseStep 4493825 = 3370369) B3370369
theorem B2806343 : Blo 1246441 2806343 := bstep (se 1 (by rfl) ⟨2104757, by rfl⟩ : syracuseStep 2806343 = 4209515) B4209515
theorem B1872455 : Blo 1246441 1872455 := bstep (se 1 (by rfl) ⟨1404341, by rfl⟩ : syracuseStep 1872455 = 2808683) B2808683
theorem B41570891 : Blo 1246441 41570891 := bstep (se 1 (by rfl) ⟨31178168, by rfl⟩ : syracuseStep 41570891 = 62356337) B62356337
theorem B2806379 : Blo 1246441 2806379 := bstep (se 1 (by rfl) ⟨2104784, by rfl⟩ : syracuseStep 2806379 = 4209569) B4209569
theorem B3158635 : Blo 1246441 3158635 := bstep (se 1 (by rfl) ⟨2368976, by rfl⟩ : syracuseStep 3158635 = 4737953) B4737953
theorem B1872491 : Blo 1246441 1872491 := bstep (se 1 (by rfl) ⟨1404368, by rfl⟩ : syracuseStep 1872491 = 2808737) B2808737
theorem B1577647 : Blo 1246441 1577647 := bstep (se 1 (by rfl) ⟨1183235, by rfl⟩ : syracuseStep 1577647 = 2366471) B2366471
theorem B21893917 : Blo 1246441 21893917 := bstep (se 3 (by rfl) ⟨4105109, by rfl⟩ : syracuseStep 21893917 = 8210219) B8210219
theorem B6574891 : Blo 1246441 6574891 := bstep (se 1 (by rfl) ⟨4931168, by rfl⟩ : syracuseStep 6574891 = 9862337) B9862337
theorem B3158939 : Blo 1246441 3158939 := bstep (se 1 (by rfl) ⟨2369204, by rfl⟩ : syracuseStep 3158939 = 4738409) B4738409
theorem B2806775 : Blo 1246441 2806775 := bstep (se 1 (by rfl) ⟨2105081, by rfl⟩ : syracuseStep 2806775 = 4210163) B4210163
theorem B7992377 : Blo 1246441 7992377 := bstep (se 2 (by rfl) ⟨2997141, by rfl⟩ : syracuseStep 7992377 = 5994283) B5994283
theorem B874386521 : Blo 1246441 874386521 := bstep (se 2 (by rfl) ⟨327894945, by rfl⟩ : syracuseStep 874386521 = 655789891) B655789891
theorem B11990105 : Blo 1246441 11990105 := bstep (se 2 (by rfl) ⟨4496289, by rfl⟩ : syracuseStep 11990105 = 8992579) B8992579
theorem B3200123 : Blo 1246441 3200123 := bstep (se 1 (by rfl) ⟨2400092, by rfl⟩ : syracuseStep 3200123 = 4800185) B4800185
theorem B6837373 : Blo 1246441 6837373 := bstep (se 3 (by rfl) ⟨1282007, by rfl⟩ : syracuseStep 6837373 = 2564015) B2564015
theorem B3159283 : Blo 1246441 3159283 := bstep (se 1 (by rfl) ⟨2369462, by rfl⟩ : syracuseStep 3159283 = 4738925) B4738925
theorem B2807135 : Blo 1246441 2807135 := bstep (se 1 (by rfl) ⟨2105351, by rfl⟩ : syracuseStep 2807135 = 4210703) B4210703
theorem B1775047 : Blo 1246441 1775047 := bstep (se 1 (by rfl) ⟨1331285, by rfl⟩ : syracuseStep 1775047 = 2662571) B2662571
theorem B3036631 : Blo 1246441 3036631 := bstep (se 1 (by rfl) ⟨2277473, by rfl⟩ : syracuseStep 3036631 = 4554947) B4554947
theorem B20215261 : Blo 1246441 20215261 := bstep (se 3 (by rfl) ⟨3790361, by rfl⟩ : syracuseStep 20215261 = 7580723) B7580723
theorem B2807531 : Blo 1246441 2807531 := bstep (se 1 (by rfl) ⟨2105648, by rfl⟩ : syracuseStep 2807531 = 4211297) B4211297
theorem B4208489 : Blo 1246441 4208489 := bstep (se 2 (by rfl) ⟨1578183, by rfl⟩ : syracuseStep 4208489 = 3156367) B3156367
theorem B2807657 : Blo 1246441 2807657 := bstep (se 2 (by rfl) ⟨1052871, by rfl⟩ : syracuseStep 2807657 = 2105743) B2105743
theorem B3160073 : Blo 1246441 3160073 := bstep (se 2 (by rfl) ⟨1185027, by rfl⟩ : syracuseStep 3160073 = 2370055) B2370055
theorem B2103401 : Blo 1246441 2103401 := bstep (se 2 (by rfl) ⟨788775, by rfl⟩ : syracuseStep 2103401 = 1577551) B1577551
theorem B3037313 : Blo 1246441 3037313 := bstep (se 2 (by rfl) ⟨1138992, by rfl⟩ : syracuseStep 3037313 = 2277985) B2277985
theorem B3553409 : Blo 1246441 3553409 := bstep (se 2 (by rfl) ⟨1332528, by rfl⟩ : syracuseStep 3553409 = 2665057) B2665057
theorem B4733063 : Blo 1246441 4733063 := bstep (se 1 (by rfl) ⟨3549797, by rfl⟩ : syracuseStep 4733063 = 7099595) B7099595
theorem B9115895 : Blo 1246441 9115895 := bstep (se 1 (by rfl) ⟨6836921, by rfl⟩ : syracuseStep 9115895 = 13673843) B13673843
theorem B4208921 : Blo 1246441 4208921 := bstep (se 2 (by rfl) ⟨1578345, by rfl⟩ : syracuseStep 4208921 = 3156691) B3156691
theorem B13490509 : Blo 1246441 13490509 := bstep (se 3 (by rfl) ⟨2529470, by rfl⟩ : syracuseStep 13490509 = 5058941) B5058941
theorem B21305753 : Blo 1246441 21305753 := bstep (se 2 (by rfl) ⟨7989657, by rfl⟩ : syracuseStep 21305753 = 15979315) B15979315
theorem B1350055 : Blo 1246441 1350055 := bstep (se 1 (by rfl) ⟨1012541, by rfl⟩ : syracuseStep 1350055 = 2025083) B2025083
theorem B20240891 : Blo 1246441 20240891 := bstep (se 1 (by rfl) ⟨15180668, by rfl⟩ : syracuseStep 20240891 = 30361337) B30361337
theorem B1579591 : Blo 1246441 1579591 := bstep (se 1 (by rfl) ⟨1184693, by rfl⟩ : syracuseStep 1579591 = 2369387) B2369387
theorem B3553865 : Blo 1246441 3553865 := bstep (se 2 (by rfl) ⟨1332699, by rfl⟩ : syracuseStep 3553865 = 2665399) B2665399
theorem B6486635 : Blo 1246441 6486635 := bstep (se 1 (by rfl) ⟨4864976, by rfl⟩ : syracuseStep 6486635 = 9729953) B9729953
theorem B10656431 : Blo 1246441 10656431 := bstep (se 1 (by rfl) ⟨7992323, by rfl⟩ : syracuseStep 10656431 = 15984647) B15984647
theorem B2808503 : Blo 1246441 2808503 := bstep (se 1 (by rfl) ⟨2106377, by rfl⟩ : syracuseStep 2808503 = 4212755) B4212755
theorem B15997769 : Blo 1246441 15997769 := bstep (se 2 (by rfl) ⟨5999163, by rfl⟩ : syracuseStep 15997769 = 11998327) B11998327
theorem B2808719 : Blo 1246441 2808719 := bstep (se 1 (by rfl) ⟨2106539, by rfl⟩ : syracuseStep 2808719 = 4213079) B4213079
theorem B17996687 : Blo 1246441 17996687 := bstep (se 1 (by rfl) ⟨13497515, by rfl⟩ : syracuseStep 17996687 = 26995031) B26995031
theorem B1776539 : Blo 1246441 1776539 := bstep (se 1 (by rfl) ⟨1332404, by rfl⟩ : syracuseStep 1776539 = 2664809) B2664809
theorem B5692331 : Blo 1246441 5692331 := bstep (se 1 (by rfl) ⟨4269248, by rfl⟩ : syracuseStep 5692331 = 8538497) B8538497
theorem B7101371 : Blo 1246441 7101371 := bstep (se 1 (by rfl) ⟨5326028, by rfl⟩ : syracuseStep 7101371 = 10652057) B10652057
theorem B8985829 : Blo 1246441 8985829 := bstep (se 4 (by rfl) ⟨842421, by rfl⟩ : syracuseStep 8985829 = 1684843) B1684843
theorem B2366759 : Blo 1246441 2366759 := bstep (se 1 (by rfl) ⟨1775069, by rfl⟩ : syracuseStep 2366759 = 3550139) B3550139
theorem B2104825 : Blo 1246441 2104825 := bstep (se 2 (by rfl) ⟨789309, by rfl⟩ : syracuseStep 2104825 = 1578619) B1578619
theorem B1498619 : Blo 1246441 1498619 := bstep (se 1 (by rfl) ⟨1123964, by rfl⟩ : syracuseStep 1498619 = 2247929) B2247929
theorem B4210271 : Blo 1246441 4210271 := bstep (se 1 (by rfl) ⟨3157703, by rfl⟩ : syracuseStep 4210271 = 6315407) B6315407
theorem B6315731 : Blo 1246441 6315731 := bstep (se 1 (by rfl) ⟨4736798, by rfl⟩ : syracuseStep 6315731 = 9473597) B9473597
theorem B2105095 : Blo 1246441 2105095 := bstep (se 1 (by rfl) ⟨1578821, by rfl⟩ : syracuseStep 2105095 = 3157643) B3157643
theorem B2105129 : Blo 1246441 2105129 := bstep (se 2 (by rfl) ⟨789423, by rfl⟩ : syracuseStep 2105129 = 1578847) B1578847
theorem B1498927 : Blo 1246441 1498927 := bstep (se 1 (by rfl) ⟨1124195, by rfl⟩ : syracuseStep 1498927 = 2248391) B2248391
theorem B2162639 : Blo 1246441 2162639 := bstep (se 1 (by rfl) ⟨1621979, by rfl⟩ : syracuseStep 2162639 = 3243959) B3243959
theorem B4210919 : Blo 1246441 4210919 := bstep (se 1 (by rfl) ⟨3158189, by rfl⟩ : syracuseStep 4210919 = 6316379) B6316379
theorem B27713927 : Blo 1246441 27713927 := bstep (se 1 (by rfl) ⟨20785445, by rfl⟩ : syracuseStep 27713927 = 41570891) B41570891
theorem B2105959 : Blo 1246441 2105959 := bstep (se 1 (by rfl) ⟨1579469, by rfl⟩ : syracuseStep 2105959 = 3158939) B3158939
theorem B3998315 : Blo 1246441 3998315 := bstep (se 1 (by rfl) ⟨2998736, by rfl⟩ : syracuseStep 3998315 = 5997473) B5997473
theorem B2106121 : Blo 1246441 2106121 := bstep (se 2 (by rfl) ⟨789795, by rfl⟩ : syracuseStep 2106121 = 1579591) B1579591
theorem B15975215 : Blo 1246441 15975215 := bstep (se 1 (by rfl) ⟨11981411, by rfl⟩ : syracuseStep 15975215 = 23962823) B23962823
theorem B4211513 : Blo 1246441 4211513 := bstep (se 2 (by rfl) ⟨1579317, by rfl⟩ : syracuseStep 4211513 = 3158635) B3158635
theorem B4211567 : Blo 1246441 4211567 := bstep (se 1 (by rfl) ⟨3158675, by rfl⟩ : syracuseStep 4211567 = 6317351) B6317351
theorem B8766521 : Blo 1246441 8766521 := bstep (se 2 (by rfl) ⟨3287445, by rfl⟩ : syracuseStep 8766521 = 6574891) B6574891
theorem B2106715 : Blo 1246441 2106715 := bstep (se 1 (by rfl) ⟨1580036, by rfl⟩ : syracuseStep 2106715 = 3160073) B3160073
theorem B1402267 : Blo 1246441 1402267 := bstep (se 1 (by rfl) ⟨1051700, by rfl⟩ : syracuseStep 1402267 = 2103401) B2103401
theorem B1246619 : Blo 1246441 1246619 := bstep (se 1 (by rfl) ⟨934964, by rfl⟩ : syracuseStep 1246619 = 1869929) B1869929
theorem B2024875 : Blo 1246441 2024875 := bstep (se 1 (by rfl) ⟨1518656, by rfl⟩ : syracuseStep 2024875 = 3037313) B3037313
theorem B2368939 : Blo 1246441 2368939 := bstep (se 1 (by rfl) ⟨1776704, by rfl⟩ : syracuseStep 2368939 = 3553409) B3553409
theorem B3155375 : Blo 1246441 3155375 := bstep (se 1 (by rfl) ⟨2366531, by rfl⟩ : syracuseStep 3155375 = 4733063) B4733063
theorem B1246831 : Blo 1246441 1246831 := bstep (se 1 (by rfl) ⟨935123, by rfl⟩ : syracuseStep 1246831 = 1870247) B1870247
theorem B7997039 : Blo 1246441 7997039 := bstep (se 1 (by rfl) ⟨5997779, by rfl⟩ : syracuseStep 7997039 = 11995559) B11995559
theorem B4212377 : Blo 1246441 4212377 := bstep (se 2 (by rfl) ⟨1579641, by rfl⟩ : syracuseStep 4212377 = 3159283) B3159283
theorem B1246887 : Blo 1246441 1246887 := bstep (se 1 (by rfl) ⟨935165, by rfl⟩ : syracuseStep 1246887 = 1870331) B1870331
theorem B13493927 : Blo 1246441 13493927 := bstep (se 1 (by rfl) ⟨10120445, by rfl⟩ : syracuseStep 13493927 = 20240891) B20240891
theorem B2369243 : Blo 1246441 2369243 := bstep (se 1 (by rfl) ⟨1776932, by rfl⟩ : syracuseStep 2369243 = 3553865) B3553865
theorem B1246971 : Blo 1246441 1246971 := bstep (se 1 (by rfl) ⟨935228, by rfl⟩ : syracuseStep 1246971 = 1870457) B1870457
theorem B1247007 : Blo 1246441 1247007 := bstep (se 1 (by rfl) ⟨935255, by rfl⟩ : syracuseStep 1247007 = 1870511) B1870511
theorem B7104287 : Blo 1246441 7104287 := bstep (se 1 (by rfl) ⟨5328215, by rfl⟩ : syracuseStep 7104287 = 10656431) B10656431
theorem B1247039 : Blo 1246441 1247039 := bstep (se 1 (by rfl) ⟨935279, by rfl⟩ : syracuseStep 1247039 = 1870559) B1870559
theorem B1869767 : Blo 1246441 1869767 := bstep (se 1 (by rfl) ⟨1402325, by rfl⟩ : syracuseStep 1869767 = 2804651) B2804651
theorem B4048841 : Blo 1246441 4048841 := bstep (se 2 (by rfl) ⟨1518315, by rfl⟩ : syracuseStep 4048841 = 3036631) B3036631
theorem B3794887 : Blo 1246441 3794887 := bstep (se 1 (by rfl) ⟨2846165, by rfl⟩ : syracuseStep 3794887 = 5692331) B5692331
theorem B26953681 : Blo 1246441 26953681 := bstep (se 2 (by rfl) ⟨10107630, by rfl⟩ : syracuseStep 26953681 = 20215261) B20215261
theorem B1247215 : Blo 1246441 1247215 := bstep (se 1 (by rfl) ⟨935411, by rfl⟩ : syracuseStep 1247215 = 1870823) B1870823
theorem B7997449 : Blo 1246441 7997449 := bstep (se 2 (by rfl) ⟨2999043, by rfl⟩ : syracuseStep 7997449 = 5998087) B5998087
theorem B10651783 : Blo 1246441 10651783 := bstep (se 1 (by rfl) ⟨7988837, by rfl⟩ : syracuseStep 10651783 = 15977675) B15977675
theorem B1247387 : Blo 1246441 1247387 := bstep (se 1 (by rfl) ⟨935540, by rfl⟩ : syracuseStep 1247387 = 1871081) B1871081
theorem B1247423 : Blo 1246441 1247423 := bstep (se 1 (by rfl) ⟨935567, by rfl⟩ : syracuseStep 1247423 = 1871135) B1871135
theorem B4212971 : Blo 1246441 4212971 := bstep (se 1 (by rfl) ⟨3159728, by rfl⟩ : syracuseStep 4212971 = 6319457) B6319457
theorem B1870121 : Blo 1246441 1870121 := bstep (se 2 (by rfl) ⟨701295, by rfl⟩ : syracuseStep 1870121 = 1402591) B1402591
theorem B1870127 : Blo 1246441 1870127 := bstep (se 1 (by rfl) ⟨1402595, by rfl⟩ : syracuseStep 1870127 = 2805191) B2805191
theorem B1247535 : Blo 1246441 1247535 := bstep (se 1 (by rfl) ⟨935651, by rfl⟩ : syracuseStep 1247535 = 1871303) B1871303
theorem B4737437 : Blo 1246441 4737437 := bstep (se 3 (by rfl) ⟨888269, by rfl⟩ : syracuseStep 4737437 = 1776539) B1776539
theorem B4557313 : Blo 1246441 4557313 := bstep (se 2 (by rfl) ⟨1708992, by rfl⟩ : syracuseStep 4557313 = 3417985) B3417985
theorem B1403419 : Blo 1246441 1403419 := bstep (se 1 (by rfl) ⟨1052564, by rfl⟩ : syracuseStep 1403419 = 2105129) B2105129
theorem B1247771 : Blo 1246441 1247771 := bstep (se 1 (by rfl) ⟨935828, by rfl⟩ : syracuseStep 1247771 = 1871657) B1871657
theorem B1870367 : Blo 1246441 1870367 := bstep (se 1 (by rfl) ⟨1402775, by rfl⟩ : syracuseStep 1870367 = 2805551) B2805551
theorem B1247775 : Blo 1246441 1247775 := bstep (se 1 (by rfl) ⟨935831, by rfl⟩ : syracuseStep 1247775 = 1871663) B1871663
theorem B34130555 : Blo 1246441 34130555 := bstep (se 1 (by rfl) ⟨25597916, by rfl⟩ : syracuseStep 34130555 = 51195833) B51195833
theorem B6310547 : Blo 1246441 6310547 := bstep (se 1 (by rfl) ⟨4732910, by rfl⟩ : syracuseStep 6310547 = 9465821) B9465821
theorem B83143361 : Blo 1246441 83143361 := bstep (se 2 (by rfl) ⟨31178760, by rfl⟩ : syracuseStep 83143361 = 62357521) B62357521
theorem B1248091 : Blo 1246441 1248091 := bstep (se 1 (by rfl) ⟨936068, by rfl⟩ : syracuseStep 1248091 = 1872137) B1872137
theorem B35990365 : Blo 1246441 35990365 := bstep (se 3 (by rfl) ⟨6748193, by rfl⟩ : syracuseStep 35990365 = 13496387) B13496387
theorem B1870751 : Blo 1246441 1870751 := bstep (se 1 (by rfl) ⟨1403063, by rfl⟩ : syracuseStep 1870751 = 2806127) B2806127
theorem B1248159 : Blo 1246441 1248159 := bstep (se 1 (by rfl) ⟨936119, by rfl⟩ : syracuseStep 1248159 = 1872239) B1872239
theorem B15993773 : Blo 1246441 15993773 := bstep (se 3 (by rfl) ⟨2998832, by rfl⟩ : syracuseStep 15993773 = 5997665) B5997665
theorem B1870799 : Blo 1246441 1870799 := bstep (se 1 (by rfl) ⟨1403099, by rfl⟩ : syracuseStep 1870799 = 2806199) B2806199
theorem B3795947 : Blo 1246441 3795947 := bstep (se 1 (by rfl) ⟨2846960, by rfl⟩ : syracuseStep 3795947 = 5693921) B5693921
theorem B1870889 : Blo 1246441 1870889 := bstep (se 2 (by rfl) ⟨701583, by rfl⟩ : syracuseStep 1870889 = 1403167) B1403167
theorem B1870895 : Blo 1246441 1870895 := bstep (se 1 (by rfl) ⟨1403171, by rfl⟩ : syracuseStep 1870895 = 2806343) B2806343
theorem B1248303 : Blo 1246441 1248303 := bstep (se 1 (by rfl) ⟨936227, by rfl⟩ : syracuseStep 1248303 = 1872455) B1872455
theorem B1870919 : Blo 1246441 1870919 := bstep (se 1 (by rfl) ⟨1403189, by rfl⟩ : syracuseStep 1870919 = 2806379) B2806379
theorem B1248327 : Blo 1246441 1248327 := bstep (se 1 (by rfl) ⟨936245, by rfl⟩ : syracuseStep 1248327 = 1872491) B1872491
theorem B3796249 : Blo 1246441 3796249 := bstep (se 2 (by rfl) ⟨1423593, by rfl⟩ : syracuseStep 3796249 = 2847187) B2847187
theorem B1871183 : Blo 1246441 1871183 := bstep (se 1 (by rfl) ⟨1403387, by rfl⟩ : syracuseStep 1871183 = 2806775) B2806775
theorem B5328251 : Blo 1246441 5328251 := bstep (se 1 (by rfl) ⟨3996188, by rfl⟩ : syracuseStep 5328251 = 7992377) B7992377
theorem B2133415 : Blo 1246441 2133415 := bstep (se 1 (by rfl) ⟨1600061, by rfl⟩ : syracuseStep 2133415 = 3200123) B3200123
theorem B1871273 : Blo 1246441 1871273 := bstep (se 2 (by rfl) ⟨701727, by rfl⟩ : syracuseStep 1871273 = 1403455) B1403455
theorem B6311357 : Blo 1246441 6311357 := bstep (se 3 (by rfl) ⟨1183379, by rfl⟩ : syracuseStep 6311357 = 2366759) B2366759
theorem B1404391 : Blo 1246441 1404391 := bstep (se 1 (by rfl) ⟨1053293, by rfl⟩ : syracuseStep 1404391 = 2106587) B2106587
theorem B9465335 : Blo 1246441 9465335 := bstep (se 1 (by rfl) ⟨7099001, by rfl⟩ : syracuseStep 9465335 = 14198003) B14198003
theorem B1871423 : Blo 1246441 1871423 := bstep (se 1 (by rfl) ⟨1403567, by rfl⟩ : syracuseStep 1871423 = 2807135) B2807135
theorem B29191889 : Blo 1246441 29191889 := bstep (se 2 (by rfl) ⟨10946958, by rfl⟩ : syracuseStep 29191889 = 21893917) B21893917
theorem B1871687 : Blo 1246441 1871687 := bstep (se 1 (by rfl) ⟨1403765, by rfl⟩ : syracuseStep 1871687 = 2807531) B2807531
theorem B4493177 : Blo 1246441 4493177 := bstep (se 2 (by rfl) ⟨1684941, by rfl⟩ : syracuseStep 4493177 = 3369883) B3369883
theorem B2805659 : Blo 1246441 2805659 := bstep (se 1 (by rfl) ⟨2104244, by rfl⟩ : syracuseStep 2805659 = 4208489) B4208489
theorem B1871771 : Blo 1246441 1871771 := bstep (se 1 (by rfl) ⟨1403828, by rfl⟩ : syracuseStep 1871771 = 2807657) B2807657
theorem B13496219 : Blo 1246441 13496219 := bstep (se 1 (by rfl) ⟨10122164, by rfl⟩ : syracuseStep 13496219 = 20244329) B20244329
theorem B5058683 : Blo 1246441 5058683 := bstep (se 1 (by rfl) ⟨3794012, by rfl⟩ : syracuseStep 5058683 = 7588025) B7588025
theorem B2805947 : Blo 1246441 2805947 := bstep (se 1 (by rfl) ⟨2104460, by rfl⟩ : syracuseStep 2805947 = 4208921) B4208921
theorem B11981105 : Blo 1246441 11981105 := bstep (se 2 (by rfl) ⟨4492914, by rfl⟩ : syracuseStep 11981105 = 8985829) B8985829
theorem B40431959 : Blo 1246441 40431959 := bstep (se 1 (by rfl) ⟨30323969, by rfl⟩ : syracuseStep 40431959 = 60647939) B60647939
theorem B1872335 : Blo 1246441 1872335 := bstep (se 1 (by rfl) ⟨1404251, by rfl⟩ : syracuseStep 1872335 = 2808503) B2808503
theorem B1872377 : Blo 1246441 1872377 := bstep (se 2 (by rfl) ⟨702141, by rfl⟩ : syracuseStep 1872377 = 1404283) B1404283
theorem B7991891 : Blo 1246441 7991891 := bstep (se 1 (by rfl) ⟨5993918, by rfl⟩ : syracuseStep 7991891 = 11987837) B11987837
theorem B1872479 : Blo 1246441 1872479 := bstep (se 1 (by rfl) ⟨1404359, by rfl⟩ : syracuseStep 1872479 = 2808719) B2808719
theorem B11997791 : Blo 1246441 11997791 := bstep (se 1 (by rfl) ⟨8998343, by rfl⟩ : syracuseStep 11997791 = 17996687) B17996687
theorem B2806433 : Blo 1246441 2806433 := bstep (se 2 (by rfl) ⟨1052412, by rfl⟩ : syracuseStep 2806433 = 2104825) B2104825
theorem B3552007 : Blo 1246441 3552007 := bstep (se 1 (by rfl) ⟨2664005, by rfl⟩ : syracuseStep 3552007 = 5328011) B5328011
theorem B4207625 : Blo 1246441 4207625 := bstep (se 2 (by rfl) ⟨1577859, by rfl⟩ : syracuseStep 4207625 = 3155719) B3155719
theorem B2806793 : Blo 1246441 2806793 := bstep (se 2 (by rfl) ⟨1052547, by rfl⟩ : syracuseStep 2806793 = 2105095) B2105095
theorem B4207679 : Blo 1246441 4207679 := bstep (se 1 (by rfl) ⟨3155759, by rfl⟩ : syracuseStep 4207679 = 6311519) B6311519
theorem B2806847 : Blo 1246441 2806847 := bstep (se 1 (by rfl) ⟨2105135, by rfl⟩ : syracuseStep 2806847 = 4210271) B4210271
theorem B4494791 : Blo 1246441 4494791 := bstep (se 1 (by rfl) ⟨3371093, by rfl⟩ : syracuseStep 4494791 = 6742187) B6742187
theorem B2995883 : Blo 1246441 2995883 := bstep (se 1 (by rfl) ⟨2246912, by rfl⟩ : syracuseStep 2995883 = 4493825) B4493825
theorem B4052663 : Blo 1246441 4052663 := bstep (se 1 (by rfl) ⟨3039497, by rfl⟩ : syracuseStep 4052663 = 6078995) B6078995
theorem B17987345 : Blo 1246441 17987345 := bstep (se 2 (by rfl) ⟨6745254, by rfl⟩ : syracuseStep 17987345 = 13490509) B13490509
theorem B4863881 : Blo 1246441 4863881 := bstep (se 2 (by rfl) ⟨1823955, by rfl⟩ : syracuseStep 4863881 = 3647911) B3647911
theorem B1800073 : Blo 1246441 1800073 := bstep (se 2 (by rfl) ⟨675027, by rfl⟩ : syracuseStep 1800073 = 1350055) B1350055
theorem B18233225 : Blo 1246441 18233225 := bstep (se 2 (by rfl) ⟨6837459, by rfl⟩ : syracuseStep 18233225 = 13674919) B13674919
theorem B7583645 : Blo 1246441 7583645 := bstep (se 3 (by rfl) ⟨1421933, by rfl⟩ : syracuseStep 7583645 = 2843867) B2843867
theorem B4265885 : Blo 1246441 4265885 := bstep (se 3 (by rfl) ⟨799853, by rfl⟩ : syracuseStep 4265885 = 1599707) B1599707
theorem B2807783 : Blo 1246441 2807783 := bstep (se 1 (by rfl) ⟨2105837, by rfl⟩ : syracuseStep 2807783 = 4211675) B4211675
theorem B2807801 : Blo 1246441 2807801 := bstep (se 2 (by rfl) ⟨1052925, by rfl⟩ : syracuseStep 2807801 = 2105851) B2105851
theorem B582924347 : Blo 1246441 582924347 := bstep (se 1 (by rfl) ⟨437193260, by rfl⟩ : syracuseStep 582924347 = 874386521) B874386521
theorem B7993403 : Blo 1246441 7993403 := bstep (se 1 (by rfl) ⟨5995052, by rfl⟩ : syracuseStep 7993403 = 11990105) B11990105
theorem B2807891 : Blo 1246441 2807891 := bstep (se 1 (by rfl) ⟨2105918, by rfl⟩ : syracuseStep 2807891 = 4211837) B4211837
theorem B2807963 : Blo 1246441 2807963 := bstep (se 1 (by rfl) ⟨2105972, by rfl⟩ : syracuseStep 2807963 = 4211945) B4211945
theorem B2103529 : Blo 1246441 2103529 := bstep (se 2 (by rfl) ⟨788823, by rfl⟩ : syracuseStep 2103529 = 1577647) B1577647
theorem B2808071 : Blo 1246441 2808071 := bstep (se 1 (by rfl) ⟨2106053, by rfl⟩ : syracuseStep 2808071 = 4212107) B4212107
theorem B4266283 : Blo 1246441 4266283 := bstep (se 1 (by rfl) ⟨3199712, by rfl⟩ : syracuseStep 4266283 = 6399425) B6399425
theorem B2808377 : Blo 1246441 2808377 := bstep (se 2 (by rfl) ⟨1053141, by rfl⟩ : syracuseStep 2808377 = 2106283) B2106283
theorem B14604889 : Blo 1246441 14604889 := bstep (se 2 (by rfl) ⟨5476833, by rfl⟩ : syracuseStep 14604889 = 10953667) B10953667
theorem B3996317 : Blo 1246441 3996317 := bstep (se 3 (by rfl) ⟨749309, by rfl⟩ : syracuseStep 3996317 = 1498619) B1498619
theorem B2103995 : Blo 1246441 2103995 := bstep (se 1 (by rfl) ⟨1577996, by rfl⟩ : syracuseStep 2103995 = 3155993) B3155993
theorem B6077263 : Blo 1246441 6077263 := bstep (se 1 (by rfl) ⟨4557947, by rfl⟩ : syracuseStep 6077263 = 9115895) B9115895
theorem B9116497 : Blo 1246441 9116497 := bstep (se 2 (by rfl) ⟨3418686, by rfl⟩ : syracuseStep 9116497 = 6837373) B6837373
theorem B14203835 : Blo 1246441 14203835 := bstep (se 1 (by rfl) ⟨10652876, by rfl⟩ : syracuseStep 14203835 = 21305753) B21305753
theorem B4324423 : Blo 1246441 4324423 := bstep (se 1 (by rfl) ⟨3243317, by rfl⟩ : syracuseStep 4324423 = 6486635) B6486635
theorem B10665179 : Blo 1246441 10665179 := bstep (se 1 (by rfl) ⟨7998884, by rfl⟩ : syracuseStep 10665179 = 15997769) B15997769
theorem B2366729 : Blo 1246441 2366729 := bstep (se 2 (by rfl) ⟨887523, by rfl⟩ : syracuseStep 2366729 = 1775047) B1775047
theorem B4734247 : Blo 1246441 4734247 := bstep (se 1 (by rfl) ⟨3550685, by rfl⟩ : syracuseStep 4734247 = 7101371) B7101371
theorem B5332385 : Blo 1246441 5332385 := bstep (se 2 (by rfl) ⟨1999644, by rfl⟩ : syracuseStep 5332385 = 3999289) B3999289
theorem B1998569 : Blo 1246441 1998569 := bstep (se 2 (by rfl) ⟨749463, by rfl⟩ : syracuseStep 1998569 = 1498927) B1498927
theorem B3555049 : Blo 1246441 3555049 := bstep (se 2 (by rfl) ⟨1333143, by rfl⟩ : syracuseStep 3555049 = 2666287) B2666287
theorem B4210487 : Blo 1246441 4210487 := bstep (se 1 (by rfl) ⟨3157865, by rfl⟩ : syracuseStep 4210487 = 6315731) B6315731
theorem B5767037 : Blo 1246441 5767037 := bstep (se 3 (by rfl) ⟨1081319, by rfl⟩ : syracuseStep 5767037 = 2162639) B2162639
theorem B2105311 : Blo 1246441 2105311 := bstep (se 1 (by rfl) ⟨1578983, by rfl⟩ : syracuseStep 2105311 = 3157967) B3157967
theorem B7987403 : Blo 1246441 7987403 := bstep (se 1 (by rfl) ⟨5990552, by rfl⟩ : syracuseStep 7987403 = 11981105) B11981105
theorem B10650143 : Blo 1246441 10650143 := bstep (se 1 (by rfl) ⟨7987607, by rfl⟩ : syracuseStep 10650143 = 15975215) B15975215
theorem B19473185 : Blo 1246441 19473185 := bstep (se 2 (by rfl) ⟨7302444, by rfl⟩ : syracuseStep 19473185 = 14604889) B14604889
theorem B4736009 : Blo 1246441 4736009 := bstep (se 2 (by rfl) ⟨1776003, by rfl⟩ : syracuseStep 4736009 = 3552007) B3552007
theorem B8103017 : Blo 1246441 8103017 := bstep (se 2 (by rfl) ⟨3038631, by rfl⟩ : syracuseStep 8103017 = 6077263) B6077263
theorem B8995951 : Blo 1246441 8995951 := bstep (se 1 (by rfl) ⟨6746963, by rfl⟩ : syracuseStep 8995951 = 13493927) B13493927
theorem B4736191 : Blo 1246441 4736191 := bstep (se 1 (by rfl) ⟨3552143, by rfl⟩ : syracuseStep 4736191 = 7104287) B7104287
theorem B2843923 : Blo 1246441 2843923 := bstep (se 1 (by rfl) ⟨2132942, by rfl⟩ : syracuseStep 2843923 = 4265885) B4265885
theorem B1246511 : Blo 1246441 1246511 := bstep (se 1 (by rfl) ⟨934883, by rfl⟩ : syracuseStep 1246511 = 1869767) B1869767
theorem B1246747 : Blo 1246441 1246747 := bstep (se 1 (by rfl) ⟨935060, by rfl⟩ : syracuseStep 1246747 = 1870121) B1870121
theorem B1246751 : Blo 1246441 1246751 := bstep (se 1 (by rfl) ⟨935063, by rfl⟩ : syracuseStep 1246751 = 1870127) B1870127
theorem B1246911 : Blo 1246441 1246911 := bstep (se 1 (by rfl) ⟨935183, by rfl⟩ : syracuseStep 1246911 = 1870367) B1870367
theorem B2664211 : Blo 1246441 2664211 := bstep (se 1 (by rfl) ⟨1998158, by rfl⟩ : syracuseStep 2664211 = 3996317) B3996317
theorem B1402663 : Blo 1246441 1402663 := bstep (se 1 (by rfl) ⟨1051997, by rfl⟩ : syracuseStep 1402663 = 2103995) B2103995
theorem B55428907 : Blo 1246441 55428907 := bstep (se 1 (by rfl) ⟨41571680, by rfl⟩ : syracuseStep 55428907 = 83143361) B83143361
theorem B1869689 : Blo 1246441 1869689 := bstep (se 2 (by rfl) ⟨701133, by rfl⟩ : syracuseStep 1869689 = 1402267) B1402267
theorem B2844553 : Blo 1246441 2844553 := bstep (se 2 (by rfl) ⟨1066707, by rfl⟩ : syracuseStep 2844553 = 2133415) B2133415
theorem B1247167 : Blo 1246441 1247167 := bstep (se 1 (by rfl) ⟨935375, by rfl⟩ : syracuseStep 1247167 = 1870751) B1870751
theorem B1247199 : Blo 1246441 1247199 := bstep (se 1 (by rfl) ⟨935399, by rfl⟩ : syracuseStep 1247199 = 1870799) B1870799
theorem B1247259 : Blo 1246441 1247259 := bstep (se 1 (by rfl) ⟨935444, by rfl⟩ : syracuseStep 1247259 = 1870889) B1870889
theorem B1247263 : Blo 1246441 1247263 := bstep (se 1 (by rfl) ⟨935447, by rfl⟩ : syracuseStep 1247263 = 1870895) B1870895
theorem B1247279 : Blo 1246441 1247279 := bstep (se 1 (by rfl) ⟨935459, by rfl⟩ : syracuseStep 1247279 = 1870919) B1870919
theorem B1247455 : Blo 1246441 1247455 := bstep (se 1 (by rfl) ⟨935591, by rfl⟩ : syracuseStep 1247455 = 1871183) B1871183
theorem B1247515 : Blo 1246441 1247515 := bstep (se 1 (by rfl) ⟨935636, by rfl⟩ : syracuseStep 1247515 = 1871273) B1871273
theorem B6310223 : Blo 1246441 6310223 := bstep (se 1 (by rfl) ⟨4732667, by rfl⟩ : syracuseStep 6310223 = 9465335) B9465335
theorem B1247615 : Blo 1246441 1247615 := bstep (se 1 (by rfl) ⟨935711, by rfl⟩ : syracuseStep 1247615 = 1871423) B1871423
theorem B1247791 : Blo 1246441 1247791 := bstep (se 1 (by rfl) ⟨935843, by rfl⟩ : syracuseStep 1247791 = 1871687) B1871687
theorem B3844691 : Blo 1246441 3844691 := bstep (se 1 (by rfl) ⟨2883518, by rfl⟩ : syracuseStep 3844691 = 5767037) B5767037
theorem B1870439 : Blo 1246441 1870439 := bstep (se 1 (by rfl) ⟨1402829, by rfl⟩ : syracuseStep 1870439 = 2805659) B2805659
theorem B1247847 : Blo 1246441 1247847 := bstep (se 1 (by rfl) ⟨935885, by rfl⟩ : syracuseStep 1247847 = 1871771) B1871771
theorem B8997479 : Blo 1246441 8997479 := bstep (se 1 (by rfl) ⟨6748109, by rfl⟩ : syracuseStep 8997479 = 13496219) B13496219
theorem B1870631 : Blo 1246441 1870631 := bstep (se 1 (by rfl) ⟨1402973, by rfl⟩ : syracuseStep 1870631 = 2805947) B2805947
theorem B26954639 : Blo 1246441 26954639 := bstep (se 1 (by rfl) ⟨20215979, by rfl⟩ : syracuseStep 26954639 = 40431959) B40431959
theorem B18475951 : Blo 1246441 18475951 := bstep (se 1 (by rfl) ⟨13856963, by rfl⟩ : syracuseStep 18475951 = 27713927) B27713927
theorem B1248223 : Blo 1246441 1248223 := bstep (se 1 (by rfl) ⟨936167, by rfl⟩ : syracuseStep 1248223 = 1872335) B1872335
theorem B2804705 : Blo 1246441 2804705 := bstep (se 2 (by rfl) ⟨1051764, by rfl⟩ : syracuseStep 2804705 = 2103529) B2103529
theorem B1248251 : Blo 1246441 1248251 := bstep (se 1 (by rfl) ⟨936188, by rfl⟩ : syracuseStep 1248251 = 1872377) B1872377
theorem B5327927 : Blo 1246441 5327927 := bstep (se 1 (by rfl) ⟨3995945, by rfl⟩ : syracuseStep 5327927 = 7991891) B7991891
theorem B5688377 : Blo 1246441 5688377 := bstep (se 2 (by rfl) ⟨2133141, by rfl⟩ : syracuseStep 5688377 = 4266283) B4266283
theorem B1248319 : Blo 1246441 1248319 := bstep (se 1 (by rfl) ⟨936239, by rfl⟩ : syracuseStep 1248319 = 1872479) B1872479
theorem B7998527 : Blo 1246441 7998527 := bstep (se 1 (by rfl) ⟨5998895, by rfl⟩ : syracuseStep 7998527 = 11997791) B11997791
theorem B2665543 : Blo 1246441 2665543 := bstep (se 1 (by rfl) ⟨1999157, by rfl⟩ : syracuseStep 2665543 = 3998315) B3998315
theorem B1870955 : Blo 1246441 1870955 := bstep (se 1 (by rfl) ⟨1403216, by rfl⟩ : syracuseStep 1870955 = 2806433) B2806433
theorem B2805083 : Blo 1246441 2805083 := bstep (se 1 (by rfl) ⟨2103812, by rfl⟩ : syracuseStep 2805083 = 4207625) B4207625
theorem B1871195 : Blo 1246441 1871195 := bstep (se 1 (by rfl) ⟨1403396, by rfl⟩ : syracuseStep 1871195 = 2806793) B2806793
theorem B1871225 : Blo 1246441 1871225 := bstep (se 2 (by rfl) ⟨701709, by rfl⟩ : syracuseStep 1871225 = 1403419) B1403419
theorem B5844347 : Blo 1246441 5844347 := bstep (se 1 (by rfl) ⟨4383260, by rfl⟩ : syracuseStep 5844347 = 8766521) B8766521
theorem B2805119 : Blo 1246441 2805119 := bstep (se 1 (by rfl) ⟨2103839, by rfl⟩ : syracuseStep 2805119 = 4207679) B4207679
theorem B1871231 : Blo 1246441 1871231 := bstep (se 1 (by rfl) ⟨1403423, by rfl⟩ : syracuseStep 1871231 = 2806847) B2806847
theorem B2699227 : Blo 1246441 2699227 := bstep (se 1 (by rfl) ⟨2024420, by rfl⟩ : syracuseStep 2699227 = 4048841) B4048841
theorem B1871855 : Blo 1246441 1871855 := bstep (se 1 (by rfl) ⟨1403891, by rfl⟩ : syracuseStep 1871855 = 2807783) B2807783
theorem B1871867 : Blo 1246441 1871867 := bstep (se 1 (by rfl) ⟨1403900, by rfl⟩ : syracuseStep 1871867 = 2807801) B2807801
theorem B388616231 : Blo 1246441 388616231 := bstep (se 1 (by rfl) ⟨291462173, by rfl⟩ : syracuseStep 388616231 = 582924347) B582924347
theorem B5328935 : Blo 1246441 5328935 := bstep (se 1 (by rfl) ⟨3996701, by rfl⟩ : syracuseStep 5328935 = 7993403) B7993403
theorem B1871927 : Blo 1246441 1871927 := bstep (se 1 (by rfl) ⟨1403945, by rfl⟩ : syracuseStep 1871927 = 2807891) B2807891
theorem B1871975 : Blo 1246441 1871975 := bstep (se 1 (by rfl) ⟨1403981, by rfl⟩ : syracuseStep 1871975 = 2807963) B2807963
theorem B1872047 : Blo 1246441 1872047 := bstep (se 1 (by rfl) ⟨1404035, by rfl⟩ : syracuseStep 1872047 = 2808071) B2808071
theorem B3158291 : Blo 1246441 3158291 := bstep (se 1 (by rfl) ⟨2368718, by rfl⟩ : syracuseStep 3158291 = 4737437) B4737437
theorem B1872251 : Blo 1246441 1872251 := bstep (se 1 (by rfl) ⟨1404188, by rfl⟩ : syracuseStep 1872251 = 2808377) B2808377
theorem B6312329 : Blo 1246441 6312329 := bstep (se 2 (by rfl) ⟨2367123, by rfl⟩ : syracuseStep 6312329 = 4734247) B4734247
theorem B22753703 : Blo 1246441 22753703 := bstep (se 1 (by rfl) ⟨17065277, by rfl⟩ : syracuseStep 22753703 = 34130555) B34130555
theorem B4207031 : Blo 1246441 4207031 := bstep (se 1 (by rfl) ⟨3155273, by rfl⟩ : syracuseStep 4207031 = 6310547) B6310547
theorem B2699833 : Blo 1246441 2699833 := bstep (se 2 (by rfl) ⟨1012437, by rfl⟩ : syracuseStep 2699833 = 2024875) B2024875
theorem B3158585 : Blo 1246441 3158585 := bstep (se 2 (by rfl) ⟨1184469, by rfl⟩ : syracuseStep 3158585 = 2368939) B2368939
theorem B10662515 : Blo 1246441 10662515 := bstep (se 1 (by rfl) ⟨7996886, by rfl⟩ : syracuseStep 10662515 = 15993773) B15993773
theorem B1872521 : Blo 1246441 1872521 := bstep (se 2 (by rfl) ⟨702195, by rfl⟩ : syracuseStep 1872521 = 1404391) B1404391
theorem B1577819 : Blo 1246441 1577819 := bstep (se 1 (by rfl) ⟨1183364, by rfl⟩ : syracuseStep 1577819 = 2366729) B2366729
theorem B3552167 : Blo 1246441 3552167 := bstep (se 1 (by rfl) ⟨2664125, by rfl⟩ : syracuseStep 3552167 = 5328251) B5328251
theorem B4207571 : Blo 1246441 4207571 := bstep (se 1 (by rfl) ⟨3155678, by rfl⟩ : syracuseStep 4207571 = 6311357) B6311357
theorem B4740065 : Blo 1246441 4740065 := bstep (se 2 (by rfl) ⟨1777524, by rfl⟩ : syracuseStep 4740065 = 3555049) B3555049
theorem B20223053 : Blo 1246441 20223053 := bstep (se 3 (by rfl) ⟨3791822, by rfl⟩ : syracuseStep 20223053 = 7583645) B7583645
theorem B19461259 : Blo 1246441 19461259 := bstep (se 1 (by rfl) ⟨14595944, by rfl⟩ : syracuseStep 19461259 = 29191889) B29191889
theorem B1332379 : Blo 1246441 1332379 := bstep (se 1 (by rfl) ⟨999284, by rfl⟩ : syracuseStep 1332379 = 1998569) B1998569
theorem B2806991 : Blo 1246441 2806991 := bstep (se 1 (by rfl) ⟨2105243, by rfl⟩ : syracuseStep 2806991 = 4210487) B4210487
theorem B2995451 : Blo 1246441 2995451 := bstep (se 1 (by rfl) ⟨2246588, by rfl⟩ : syracuseStep 2995451 = 4493177) B4493177
theorem B5059849 : Blo 1246441 5059849 := bstep (se 2 (by rfl) ⟨1897443, by rfl⟩ : syracuseStep 5059849 = 3794887) B3794887
theorem B2807081 : Blo 1246441 2807081 := bstep (se 2 (by rfl) ⟨1052655, by rfl⟩ : syracuseStep 2807081 = 2105311) B2105311
theorem B10663265 : Blo 1246441 10663265 := bstep (se 2 (by rfl) ⟨3998724, by rfl⟩ : syracuseStep 10663265 = 7997449) B7997449
theorem B3372455 : Blo 1246441 3372455 := bstep (se 1 (by rfl) ⟨2529341, by rfl⟩ : syracuseStep 3372455 = 5058683) B5058683
theorem B2807279 : Blo 1246441 2807279 := bstep (se 1 (by rfl) ⟨2105459, by rfl⟩ : syracuseStep 2807279 = 4210919) B4210919
theorem B14202377 : Blo 1246441 14202377 := bstep (se 2 (by rfl) ⟨5325891, by rfl⟩ : syracuseStep 14202377 = 10651783) B10651783
theorem B2807675 : Blo 1246441 2807675 := bstep (se 1 (by rfl) ⟨2105756, by rfl⟩ : syracuseStep 2807675 = 4211513) B4211513
theorem B2807711 : Blo 1246441 2807711 := bstep (se 1 (by rfl) ⟨2105783, by rfl⟩ : syracuseStep 2807711 = 4211567) B4211567
theorem B6076417 : Blo 1246441 6076417 := bstep (se 2 (by rfl) ⟨2278656, by rfl⟩ : syracuseStep 6076417 = 4557313) B4557313
theorem B2807945 : Blo 1246441 2807945 := bstep (se 2 (by rfl) ⟨1052979, by rfl⟩ : syracuseStep 2807945 = 2105959) B2105959
theorem B2103583 : Blo 1246441 2103583 := bstep (se 1 (by rfl) ⟨1577687, by rfl⟩ : syracuseStep 2103583 = 3155375) B3155375
theorem B2996527 : Blo 1246441 2996527 := bstep (se 1 (by rfl) ⟨2247395, by rfl⟩ : syracuseStep 2996527 = 4494791) B4494791
theorem B2808161 : Blo 1246441 2808161 := bstep (se 2 (by rfl) ⟨1053060, by rfl⟩ : syracuseStep 2808161 = 2106121) B2106121
theorem B5331359 : Blo 1246441 5331359 := bstep (se 1 (by rfl) ⟨3998519, by rfl⟩ : syracuseStep 5331359 = 7997039) B7997039
theorem B2808251 : Blo 1246441 2808251 := bstep (se 1 (by rfl) ⟨2106188, by rfl⟩ : syracuseStep 2808251 = 4212377) B4212377
theorem B12155329 : Blo 1246441 12155329 := bstep (se 2 (by rfl) ⟨4558248, by rfl⟩ : syracuseStep 12155329 = 9116497) B9116497
theorem B1997255 : Blo 1246441 1997255 := bstep (se 1 (by rfl) ⟨1497941, by rfl⟩ : syracuseStep 1997255 = 2995883) B2995883
theorem B2701775 : Blo 1246441 2701775 := bstep (se 1 (by rfl) ⟨2026331, by rfl⟩ : syracuseStep 2701775 = 4052663) B4052663
theorem B47987153 : Blo 1246441 47987153 := bstep (se 2 (by rfl) ⟨17995182, by rfl⟩ : syracuseStep 47987153 = 35990365) B35990365
theorem B1579495 : Blo 1246441 1579495 := bstep (se 1 (by rfl) ⟨1184621, by rfl⟩ : syracuseStep 1579495 = 2369243) B2369243
theorem B11991563 : Blo 1246441 11991563 := bstep (se 1 (by rfl) ⟨8993672, by rfl⟩ : syracuseStep 11991563 = 17987345) B17987345
theorem B3242587 : Blo 1246441 3242587 := bstep (se 1 (by rfl) ⟨2431940, by rfl⟩ : syracuseStep 3242587 = 4863881) B4863881
theorem B12155483 : Blo 1246441 12155483 := bstep (se 1 (by rfl) ⟨9116612, by rfl⟩ : syracuseStep 12155483 = 18233225) B18233225
theorem B5765897 : Blo 1246441 5765897 := bstep (se 2 (by rfl) ⟨2162211, by rfl⟩ : syracuseStep 5765897 = 4324423) B4324423
theorem B2808647 : Blo 1246441 2808647 := bstep (se 1 (by rfl) ⟨2106485, by rfl⟩ : syracuseStep 2808647 = 4212971) B4212971
theorem B5061665 : Blo 1246441 5061665 := bstep (se 2 (by rfl) ⟨1898124, by rfl⟩ : syracuseStep 5061665 = 3796249) B3796249
theorem B2808953 : Blo 1246441 2808953 := bstep (se 2 (by rfl) ⟨1053357, by rfl⟩ : syracuseStep 2808953 = 2106715) B2106715
theorem B9469223 : Blo 1246441 9469223 := bstep (se 1 (by rfl) ⟨7101917, by rfl⟩ : syracuseStep 9469223 = 14203835) B14203835
theorem B2530631 : Blo 1246441 2530631 := bstep (se 1 (by rfl) ⟨1897973, by rfl⟩ : syracuseStep 2530631 = 3795947) B3795947
theorem B9600389 : Blo 1246441 9600389 := bstep (se 4 (by rfl) ⟨900036, by rfl⟩ : syracuseStep 9600389 = 1800073) B1800073
theorem B7110119 : Blo 1246441 7110119 := bstep (se 1 (by rfl) ⟨5332589, by rfl⟩ : syracuseStep 7110119 = 10665179) B10665179
theorem B3554923 : Blo 1246441 3554923 := bstep (se 1 (by rfl) ⟨2666192, by rfl⟩ : syracuseStep 3554923 = 5332385) B5332385
theorem B35938241 : Blo 1246441 35938241 := bstep (se 2 (by rfl) ⟨13476840, by rfl⟩ : syracuseStep 35938241 = 26953681) B26953681
theorem B8101889 : Blo 1246441 8101889 := bstep (se 2 (by rfl) ⟨3038208, by rfl⟩ : syracuseStep 8101889 = 6076417) B6076417
theorem B5324935 : Blo 1246441 5324935 := bstep (se 1 (by rfl) ⟨3993701, by rfl⟩ : syracuseStep 5324935 = 7987403) B7987403
theorem B2105527 : Blo 1246441 2105527 := bstep (se 1 (by rfl) ⟨1579145, by rfl⟩ : syracuseStep 2105527 = 3158291) B3158291
theorem B2105723 : Blo 1246441 2105723 := bstep (se 1 (by rfl) ⟨1579292, by rfl⟩ : syracuseStep 2105723 = 3158585) B3158585
theorem B2368111 : Blo 1246441 2368111 := bstep (se 1 (by rfl) ⟨1776083, by rfl⟩ : syracuseStep 2368111 = 3552167) B3552167
theorem B2105993 : Blo 1246441 2105993 := bstep (se 2 (by rfl) ⟨789747, by rfl⟩ : syracuseStep 2105993 = 1579495) B1579495
theorem B5326013 : Blo 1246441 5326013 := bstep (se 3 (by rfl) ⟨998627, by rfl⟩ : syracuseStep 5326013 = 1997255) B1997255
theorem B24634601 : Blo 1246441 24634601 := bstep (se 2 (by rfl) ⟨9237975, by rfl⟩ : syracuseStep 24634601 = 18475951) B18475951
theorem B1246459 : Blo 1246441 1246459 := bstep (se 1 (by rfl) ⟨934844, by rfl⟩ : syracuseStep 1246459 = 1869689) B1869689
theorem B11994601 : Blo 1246441 11994601 := bstep (se 2 (by rfl) ⟨4497975, by rfl⟩ : syracuseStep 11994601 = 8995951) B8995951
theorem B31991435 : Blo 1246441 31991435 := bstep (se 1 (by rfl) ⟨23993576, by rfl⟩ : syracuseStep 31991435 = 47987153) B47987153
theorem B8103655 : Blo 1246441 8103655 := bstep (se 1 (by rfl) ⟨6077741, by rfl⟩ : syracuseStep 8103655 = 12155483) B12155483
theorem B1246959 : Blo 1246441 1246959 := bstep (se 1 (by rfl) ⟨935219, by rfl⟩ : syracuseStep 1246959 = 1870439) B1870439
theorem B5998319 : Blo 1246441 5998319 := bstep (se 1 (by rfl) ⟨4498739, by rfl⟩ : syracuseStep 5998319 = 8997479) B8997479
theorem B3843931 : Blo 1246441 3843931 := bstep (se 1 (by rfl) ⟨2882948, by rfl⟩ : syracuseStep 3843931 = 5765897) B5765897
theorem B1247087 : Blo 1246441 1247087 := bstep (se 1 (by rfl) ⟨935315, by rfl⟩ : syracuseStep 1247087 = 1870631) B1870631
theorem B1869803 : Blo 1246441 1869803 := bstep (se 1 (by rfl) ⟨1402352, by rfl⟩ : syracuseStep 1869803 = 2804705) B2804705
theorem B1247303 : Blo 1246441 1247303 := bstep (se 1 (by rfl) ⟨935477, by rfl⟩ : syracuseStep 1247303 = 1870955) B1870955
theorem B1870055 : Blo 1246441 1870055 := bstep (se 1 (by rfl) ⟨1402541, by rfl⟩ : syracuseStep 1870055 = 2805083) B2805083
theorem B1247463 : Blo 1246441 1247463 := bstep (se 1 (by rfl) ⟨935597, by rfl⟩ : syracuseStep 1247463 = 1871195) B1871195
theorem B1247483 : Blo 1246441 1247483 := bstep (se 1 (by rfl) ⟨935612, by rfl⟩ : syracuseStep 1247483 = 1871225) B1871225
theorem B1870079 : Blo 1246441 1870079 := bstep (se 1 (by rfl) ⟨1402559, by rfl⟩ : syracuseStep 1870079 = 2805119) B2805119
theorem B1247487 : Blo 1246441 1247487 := bstep (se 1 (by rfl) ⟨935615, by rfl⟩ : syracuseStep 1247487 = 1871231) B1871231
theorem B6400259 : Blo 1246441 6400259 := bstep (se 1 (by rfl) ⟨4800194, by rfl⟩ : syracuseStep 6400259 = 9600389) B9600389
theorem B1870217 : Blo 1246441 1870217 := bstep (se 2 (by rfl) ⟨701331, by rfl⟩ : syracuseStep 1870217 = 1402663) B1402663
theorem B14395877 : Blo 1246441 14395877 := bstep (se 4 (by rfl) ⟨1349613, by rfl⟩ : syracuseStep 14395877 = 2699227) B2699227
theorem B1247903 : Blo 1246441 1247903 := bstep (se 1 (by rfl) ⟨935927, by rfl⟩ : syracuseStep 1247903 = 1871855) B1871855
theorem B1247911 : Blo 1246441 1247911 := bstep (se 1 (by rfl) ⟨935933, by rfl⟩ : syracuseStep 1247911 = 1871867) B1871867
theorem B1247951 : Blo 1246441 1247951 := bstep (se 1 (by rfl) ⟨935963, by rfl⟩ : syracuseStep 1247951 = 1871927) B1871927
theorem B1247983 : Blo 1246441 1247983 := bstep (se 1 (by rfl) ⟨935987, by rfl⟩ : syracuseStep 1247983 = 1871975) B1871975
theorem B1248031 : Blo 1246441 1248031 := bstep (se 1 (by rfl) ⟨936023, by rfl⟩ : syracuseStep 1248031 = 1872047) B1872047
theorem B1248167 : Blo 1246441 1248167 := bstep (se 1 (by rfl) ⟨936125, by rfl⟩ : syracuseStep 1248167 = 1872251) B1872251
theorem B2804687 : Blo 1246441 2804687 := bstep (se 1 (by rfl) ⟨2103515, by rfl⟩ : syracuseStep 2804687 = 4207031) B4207031
theorem B2804777 : Blo 1246441 2804777 := bstep (se 2 (by rfl) ⟨1051791, by rfl⟩ : syracuseStep 2804777 = 2103583) B2103583
theorem B1248347 : Blo 1246441 1248347 := bstep (se 1 (by rfl) ⟨936260, by rfl⟩ : syracuseStep 1248347 = 1872521) B1872521
theorem B2805047 : Blo 1246441 2805047 := bstep (se 1 (by rfl) ⟨2103785, by rfl⟩ : syracuseStep 2805047 = 4207571) B4207571
theorem B3157339 : Blo 1246441 3157339 := bstep (se 1 (by rfl) ⟨2368004, by rfl⟩ : syracuseStep 3157339 = 4736009) B4736009
theorem B5402011 : Blo 1246441 5402011 := bstep (se 1 (by rfl) ⟨4051508, by rfl⟩ : syracuseStep 5402011 = 8103017) B8103017
theorem B3599777 : Blo 1246441 3599777 := bstep (se 2 (by rfl) ⟨1349916, by rfl⟩ : syracuseStep 3599777 = 2699833) B2699833
theorem B1871327 : Blo 1246441 1871327 := bstep (se 1 (by rfl) ⟨1403495, by rfl⟩ : syracuseStep 1871327 = 2806991) B2806991
theorem B1871387 : Blo 1246441 1871387 := bstep (se 1 (by rfl) ⟨1403540, by rfl⟩ : syracuseStep 1871387 = 2807081) B2807081
theorem B2248303 : Blo 1246441 2248303 := bstep (se 1 (by rfl) ⟨1686227, by rfl⟩ : syracuseStep 2248303 = 3372455) B3372455
theorem B1871519 : Blo 1246441 1871519 := bstep (se 1 (by rfl) ⟨1403639, by rfl⟩ : syracuseStep 1871519 = 2807279) B2807279
theorem B14216957 : Blo 1246441 14216957 := bstep (se 3 (by rfl) ⟨2665679, by rfl⟩ : syracuseStep 14216957 = 5331359) B5331359
theorem B1871783 : Blo 1246441 1871783 := bstep (se 1 (by rfl) ⟨1403837, by rfl⟩ : syracuseStep 1871783 = 2807675) B2807675
theorem B1871807 : Blo 1246441 1871807 := bstep (se 1 (by rfl) ⟨1403855, by rfl⟩ : syracuseStep 1871807 = 2807711) B2807711
theorem B1871963 : Blo 1246441 1871963 := bstep (se 1 (by rfl) ⟨1403972, by rfl⟩ : syracuseStep 1871963 = 2807945) B2807945
theorem B25948345 : Blo 1246441 25948345 := bstep (se 2 (by rfl) ⟨9730629, by rfl⟩ : syracuseStep 25948345 = 19461259) B19461259
theorem B4206815 : Blo 1246441 4206815 := bstep (se 1 (by rfl) ⟨3155111, by rfl⟩ : syracuseStep 4206815 = 6310223) B6310223
theorem B1872107 : Blo 1246441 1872107 := bstep (se 1 (by rfl) ⟨1404080, by rfl⟩ : syracuseStep 1872107 = 2808161) B2808161
theorem B1872167 : Blo 1246441 1872167 := bstep (se 1 (by rfl) ⟨1404125, by rfl⟩ : syracuseStep 1872167 = 2808251) B2808251
theorem B6746465 : Blo 1246441 6746465 := bstep (se 2 (by rfl) ⟨2529924, by rfl⟩ : syracuseStep 6746465 = 5059849) B5059849
theorem B1872431 : Blo 1246441 1872431 := bstep (se 1 (by rfl) ⟨1404323, by rfl⟩ : syracuseStep 1872431 = 2808647) B2808647
theorem B17969759 : Blo 1246441 17969759 := bstep (se 1 (by rfl) ⟨13477319, by rfl⟩ : syracuseStep 17969759 = 26954639) B26954639
theorem B3551951 : Blo 1246441 3551951 := bstep (se 1 (by rfl) ⟨2663963, by rfl⟩ : syracuseStep 3551951 = 5327927) B5327927
theorem B1872635 : Blo 1246441 1872635 := bstep (se 1 (by rfl) ⟨1404476, by rfl⟩ : syracuseStep 1872635 = 2808953) B2808953
theorem B4739897 : Blo 1246441 4739897 := bstep (se 2 (by rfl) ⟨1777461, by rfl⟩ : syracuseStep 4739897 = 3554923) B3554923
theorem B6312815 : Blo 1246441 6312815 := bstep (se 1 (by rfl) ⟨4734611, by rfl⟩ : syracuseStep 6312815 = 9469223) B9469223
theorem B4207517 : Blo 1246441 4207517 := bstep (se 3 (by rfl) ⟨788909, by rfl⟩ : syracuseStep 4207517 = 1577819) B1577819
theorem B4740079 : Blo 1246441 4740079 := bstep (se 1 (by rfl) ⟨3555059, by rfl⟩ : syracuseStep 4740079 = 7110119) B7110119
theorem B64828421 : Blo 1246441 64828421 := bstep (se 4 (by rfl) ⟨6077664, by rfl⟩ : syracuseStep 64828421 = 12155329) B12155329
theorem B3552281 : Blo 1246441 3552281 := bstep (se 2 (by rfl) ⟨1332105, by rfl⟩ : syracuseStep 3552281 = 2664211) B2664211
theorem B73905209 : Blo 1246441 73905209 := bstep (se 2 (by rfl) ⟨27714453, by rfl⟩ : syracuseStep 73905209 = 55428907) B55428907
theorem B23958827 : Blo 1246441 23958827 := bstep (se 1 (by rfl) ⟨17969120, by rfl⟩ : syracuseStep 23958827 = 35938241) B35938241
theorem B259077487 : Blo 1246441 259077487 := bstep (se 1 (by rfl) ⟨194308115, by rfl⟩ : syracuseStep 259077487 = 388616231) B388616231
theorem B3552623 : Blo 1246441 3552623 := bstep (se 1 (by rfl) ⟨2664467, by rfl⟩ : syracuseStep 3552623 = 5328935) B5328935
theorem B4208219 : Blo 1246441 4208219 := bstep (se 1 (by rfl) ⟨3156164, by rfl⟩ : syracuseStep 4208219 = 6312329) B6312329
theorem B15169135 : Blo 1246441 15169135 := bstep (se 1 (by rfl) ⟨11376851, by rfl⟩ : syracuseStep 15169135 = 22753703) B22753703
theorem B7100095 : Blo 1246441 7100095 := bstep (se 1 (by rfl) ⟨5325071, by rfl⟩ : syracuseStep 7100095 = 10650143) B10650143
theorem B3995369 : Blo 1246441 3995369 := bstep (se 2 (by rfl) ⟨1498263, by rfl⟩ : syracuseStep 3995369 = 2996527) B2996527
theorem B7108343 : Blo 1246441 7108343 := bstep (se 1 (by rfl) ⟨5331257, by rfl⟩ : syracuseStep 7108343 = 10662515) B10662515
theorem B12982123 : Blo 1246441 12982123 := bstep (se 1 (by rfl) ⟨9736592, by rfl⟩ : syracuseStep 12982123 = 19473185) B19473185
theorem B3160043 : Blo 1246441 3160043 := bstep (se 1 (by rfl) ⟨2370032, by rfl⟩ : syracuseStep 3160043 = 4740065) B4740065
theorem B13482035 : Blo 1246441 13482035 := bstep (se 1 (by rfl) ⟨10111526, by rfl⟩ : syracuseStep 13482035 = 20223053) B20223053
theorem B4323449 : Blo 1246441 4323449 := bstep (se 2 (by rfl) ⟨1621293, by rfl⟩ : syracuseStep 4323449 = 3242587) B3242587
theorem B1996967 : Blo 1246441 1996967 := bstep (se 1 (by rfl) ⟨1497725, by rfl⟩ : syracuseStep 1996967 = 2995451) B2995451
theorem B7108843 : Blo 1246441 7108843 := bstep (se 1 (by rfl) ⟨5331632, by rfl⟩ : syracuseStep 7108843 = 10663265) B10663265
theorem B9468251 : Blo 1246441 9468251 := bstep (se 1 (by rfl) ⟨7101188, by rfl⟩ : syracuseStep 9468251 = 14202377) B14202377
theorem B62339701 : Blo 1246441 62339701 := bstep (se 5 (by rfl) ⟨2922173, by rfl⟩ : syracuseStep 62339701 = 5844347) B5844347
theorem B3554057 : Blo 1246441 3554057 := bstep (se 2 (by rfl) ⟨1332771, by rfl⟩ : syracuseStep 3554057 = 2665543) B2665543
theorem B1776505 : Blo 1246441 1776505 := bstep (se 2 (by rfl) ⟨666189, by rfl⟩ : syracuseStep 1776505 = 1332379) B1332379
theorem B6314921 : Blo 1246441 6314921 := bstep (se 2 (by rfl) ⟨2368095, by rfl⟩ : syracuseStep 6314921 = 4736191) B4736191
theorem B1801183 : Blo 1246441 1801183 := bstep (se 1 (by rfl) ⟨1350887, by rfl⟩ : syracuseStep 1801183 = 2701775) B2701775
theorem B7994375 : Blo 1246441 7994375 := bstep (se 1 (by rfl) ⟨5995781, by rfl⟩ : syracuseStep 7994375 = 11991563) B11991563
theorem B3791897 : Blo 1246441 3791897 := bstep (se 2 (by rfl) ⟨1421961, by rfl⟩ : syracuseStep 3791897 = 2843923) B2843923
theorem B2563127 : Blo 1246441 2563127 := bstep (se 1 (by rfl) ⟨1922345, by rfl⟩ : syracuseStep 2563127 = 3844691) B3844691
theorem B3374443 : Blo 1246441 3374443 := bstep (se 1 (by rfl) ⟨2530832, by rfl⟩ : syracuseStep 3374443 = 5061665) B5061665
theorem B3792251 : Blo 1246441 3792251 := bstep (se 1 (by rfl) ⟨2844188, by rfl⟩ : syracuseStep 3792251 = 5688377) B5688377
theorem B5332351 : Blo 1246441 5332351 := bstep (se 1 (by rfl) ⟨3999263, by rfl⟩ : syracuseStep 5332351 = 7998527) B7998527
theorem B1687087 : Blo 1246441 1687087 := bstep (se 1 (by rfl) ⟨1265315, by rfl⟩ : syracuseStep 1687087 = 2530631) B2530631
theorem B3792737 : Blo 1246441 3792737 := bstep (se 2 (by rfl) ⟨1422276, by rfl⟩ : syracuseStep 3792737 = 2844553) B2844553
theorem B4497643 : Blo 1246441 4497643 := bstep (se 1 (by rfl) ⟨3373232, by rfl⟩ : syracuseStep 4497643 = 6746465) B6746465
theorem B9478457 : Blo 1246441 9478457 := bstep (se 2 (by rfl) ⟨3554421, by rfl⟩ : syracuseStep 9478457 = 7108843) B7108843
theorem B2367967 : Blo 1246441 2367967 := bstep (se 1 (by rfl) ⟨1775975, by rfl⟩ : syracuseStep 2367967 = 3551951) B3551951
theorem B2368187 : Blo 1246441 2368187 := bstep (se 1 (by rfl) ⟨1776140, by rfl⟩ : syracuseStep 2368187 = 3552281) B3552281
theorem B2368415 : Blo 1246441 2368415 := bstep (se 1 (by rfl) ⟨1776311, by rfl⟩ : syracuseStep 2368415 = 3552623) B3552623
theorem B2663579 : Blo 1246441 2663579 := bstep (se 1 (by rfl) ⟨1997684, by rfl⟩ : syracuseStep 2663579 = 3995369) B3995369
theorem B3998879 : Blo 1246441 3998879 := bstep (se 1 (by rfl) ⟨2999159, by rfl⟩ : syracuseStep 3998879 = 5998319) B5998319
theorem B2368673 : Blo 1246441 2368673 := bstep (se 2 (by rfl) ⟨888252, by rfl⟩ : syracuseStep 2368673 = 1776505) B1776505
theorem B2401577 : Blo 1246441 2401577 := bstep (se 2 (by rfl) ⟨900591, by rfl⟩ : syracuseStep 2401577 = 1801183) B1801183
theorem B1246535 : Blo 1246441 1246535 := bstep (se 1 (by rfl) ⟨934901, by rfl⟩ : syracuseStep 1246535 = 1869803) B1869803
theorem B2106695 : Blo 1246441 2106695 := bstep (se 1 (by rfl) ⟨1580021, by rfl⟩ : syracuseStep 2106695 = 3160043) B3160043
theorem B8988023 : Blo 1246441 8988023 := bstep (se 1 (by rfl) ⟨6741017, by rfl⟩ : syracuseStep 8988023 = 13482035) B13482035
theorem B1246703 : Blo 1246441 1246703 := bstep (se 1 (by rfl) ⟨935027, by rfl⟩ : syracuseStep 1246703 = 1870055) B1870055
theorem B1246719 : Blo 1246441 1246719 := bstep (se 1 (by rfl) ⟨935039, by rfl⟩ : syracuseStep 1246719 = 1870079) B1870079
theorem B1246811 : Blo 1246441 1246811 := bstep (se 1 (by rfl) ⟨935108, by rfl⟩ : syracuseStep 1246811 = 1870217) B1870217
theorem B7202681 : Blo 1246441 7202681 := bstep (se 2 (by rfl) ⟨2701005, by rfl⟩ : syracuseStep 7202681 = 5402011) B5402011
theorem B1869791 : Blo 1246441 1869791 := bstep (se 1 (by rfl) ⟨1402343, by rfl⟩ : syracuseStep 1869791 = 2804687) B2804687
theorem B15992801 : Blo 1246441 15992801 := bstep (se 2 (by rfl) ⟨5997300, by rfl⟩ : syracuseStep 15992801 = 11994601) B11994601
theorem B1869851 : Blo 1246441 1869851 := bstep (se 1 (by rfl) ⟨1402388, by rfl⟩ : syracuseStep 1869851 = 2804777) B2804777
theorem B1870031 : Blo 1246441 1870031 := bstep (se 1 (by rfl) ⟨1402523, by rfl⟩ : syracuseStep 1870031 = 2805047) B2805047
theorem B1247551 : Blo 1246441 1247551 := bstep (se 1 (by rfl) ⟨935663, by rfl⟩ : syracuseStep 1247551 = 1871327) B1871327
theorem B1247591 : Blo 1246441 1247591 := bstep (se 1 (by rfl) ⟨935693, by rfl⟩ : syracuseStep 1247591 = 1871387) B1871387
theorem B1247679 : Blo 1246441 1247679 := bstep (se 1 (by rfl) ⟨935759, by rfl⟩ : syracuseStep 1247679 = 1871519) B1871519
theorem B1247855 : Blo 1246441 1247855 := bstep (se 1 (by rfl) ⟨935891, by rfl⟩ : syracuseStep 1247855 = 1871783) B1871783
theorem B1247871 : Blo 1246441 1247871 := bstep (se 1 (by rfl) ⟨935903, by rfl⟩ : syracuseStep 1247871 = 1871807) B1871807
theorem B5401259 : Blo 1246441 5401259 := bstep (se 1 (by rfl) ⟨4050944, by rfl⟩ : syracuseStep 5401259 = 8101889) B8101889
theorem B1247975 : Blo 1246441 1247975 := bstep (se 1 (by rfl) ⟨935981, by rfl⟩ : syracuseStep 1247975 = 1871963) B1871963
theorem B2804543 : Blo 1246441 2804543 := bstep (se 1 (by rfl) ⟨2103407, by rfl⟩ : syracuseStep 2804543 = 4206815) B4206815
theorem B1248071 : Blo 1246441 1248071 := bstep (se 1 (by rfl) ⟨936053, by rfl⟩ : syracuseStep 1248071 = 1872107) B1872107
theorem B1248111 : Blo 1246441 1248111 := bstep (se 1 (by rfl) ⟨936083, by rfl⟩ : syracuseStep 1248111 = 1872167) B1872167
theorem B34597793 : Blo 1246441 34597793 := bstep (se 2 (by rfl) ⟨12974172, by rfl⟩ : syracuseStep 34597793 = 25948345) B25948345
theorem B8997797 : Blo 1246441 8997797 := bstep (se 4 (by rfl) ⟨843543, by rfl⟩ : syracuseStep 8997797 = 1687087) B1687087
theorem B1403815 : Blo 1246441 1403815 := bstep (se 1 (by rfl) ⟨1052861, by rfl⟩ : syracuseStep 1403815 = 2105723) B2105723
theorem B1248287 : Blo 1246441 1248287 := bstep (se 1 (by rfl) ⟨936215, by rfl⟩ : syracuseStep 1248287 = 1872431) B1872431
theorem B11979839 : Blo 1246441 11979839 := bstep (se 1 (by rfl) ⟨8984879, by rfl⟩ : syracuseStep 11979839 = 17969759) B17969759
theorem B1403995 : Blo 1246441 1403995 := bstep (se 1 (by rfl) ⟨1052996, by rfl⟩ : syracuseStep 1403995 = 2105993) B2105993
theorem B1248423 : Blo 1246441 1248423 := bstep (se 1 (by rfl) ⟨936317, by rfl⟩ : syracuseStep 1248423 = 1872635) B1872635
theorem B27340021 : Blo 1246441 27340021 := bstep (se 5 (by rfl) ⟨1281563, by rfl⟩ : syracuseStep 27340021 = 2563127) B2563127
theorem B2805011 : Blo 1246441 2805011 := bstep (se 1 (by rfl) ⟨2103758, by rfl⟩ : syracuseStep 2805011 = 4207517) B4207517
theorem B49270139 : Blo 1246441 49270139 := bstep (se 1 (by rfl) ⟨36952604, by rfl⟩ : syracuseStep 49270139 = 73905209) B73905209
theorem B3550675 : Blo 1246441 3550675 := bstep (se 1 (by rfl) ⟨2663006, by rfl⟩ : syracuseStep 3550675 = 5326013) B5326013
theorem B3157481 : Blo 1246441 3157481 := bstep (se 2 (by rfl) ⟨1184055, by rfl⟩ : syracuseStep 3157481 = 2368111) B2368111
theorem B83119601 : Blo 1246441 83119601 := bstep (se 2 (by rfl) ⟨31169850, by rfl⟩ : syracuseStep 83119601 = 62339701) B62339701
theorem B2805479 : Blo 1246441 2805479 := bstep (se 1 (by rfl) ⟨2104109, by rfl⟩ : syracuseStep 2805479 = 4208219) B4208219
theorem B21327623 : Blo 1246441 21327623 := bstep (se 1 (by rfl) ⟨15995717, by rfl⟩ : syracuseStep 21327623 = 31991435) B31991435
theorem B4738895 : Blo 1246441 4738895 := bstep (se 1 (by rfl) ⟨3554171, by rfl⟩ : syracuseStep 4738895 = 7108343) B7108343
theorem B6320105 : Blo 1246441 6320105 := bstep (se 2 (by rfl) ⟨2370039, by rfl⟩ : syracuseStep 6320105 = 4740079) B4740079
theorem B1331311 : Blo 1246441 1331311 := bstep (se 1 (by rfl) ⟨998483, by rfl⟩ : syracuseStep 1331311 = 1996967) B1996967
theorem B6312167 : Blo 1246441 6312167 := bstep (se 1 (by rfl) ⟨4734125, by rfl⟩ : syracuseStep 6312167 = 9468251) B9468251
theorem B9597251 : Blo 1246441 9597251 := bstep (se 1 (by rfl) ⟨7197938, by rfl⟩ : syracuseStep 9597251 = 14395877) B14395877
theorem B345436649 : Blo 1246441 345436649 := bstep (se 2 (by rfl) ⟨129538743, by rfl⟩ : syracuseStep 345436649 = 259077487) B259077487
theorem B5329583 : Blo 1246441 5329583 := bstep (se 1 (by rfl) ⟨3997187, by rfl⟩ : syracuseStep 5329583 = 7994375) B7994375
theorem B2527931 : Blo 1246441 2527931 := bstep (se 1 (by rfl) ⟨1895948, by rfl⟩ : syracuseStep 2527931 = 3791897) B3791897
theorem B2528167 : Blo 1246441 2528167 := bstep (se 1 (by rfl) ⟨1896125, by rfl⟩ : syracuseStep 2528167 = 3792251) B3792251
theorem B9466793 : Blo 1246441 9466793 := bstep (se 2 (by rfl) ⟨3550047, by rfl⟩ : syracuseStep 9466793 = 7100095) B7100095
theorem B5125241 : Blo 1246441 5125241 := bstep (se 2 (by rfl) ⟨1921965, by rfl⟩ : syracuseStep 5125241 = 3843931) B3843931
theorem B2528491 : Blo 1246441 2528491 := bstep (se 1 (by rfl) ⟨1896368, by rfl⟩ : syracuseStep 2528491 = 3792737) B3792737
theorem B7099913 : Blo 1246441 7099913 := bstep (se 2 (by rfl) ⟨2662467, by rfl⟩ : syracuseStep 7099913 = 5324935) B5324935
theorem B2807369 : Blo 1246441 2807369 := bstep (se 2 (by rfl) ⟨1052763, by rfl⟩ : syracuseStep 2807369 = 2105527) B2105527
theorem B3159931 : Blo 1246441 3159931 := bstep (se 1 (by rfl) ⟨2369948, by rfl⟩ : syracuseStep 3159931 = 4739897) B4739897
theorem B4208543 : Blo 1246441 4208543 := bstep (se 1 (by rfl) ⟨3156407, by rfl⟩ : syracuseStep 4208543 = 6312815) B6312815
theorem B43218947 : Blo 1246441 43218947 := bstep (se 1 (by rfl) ⟨32414210, by rfl⟩ : syracuseStep 43218947 = 64828421) B64828421
theorem B16423067 : Blo 1246441 16423067 := bstep (se 1 (by rfl) ⟨12317300, by rfl⟩ : syracuseStep 16423067 = 24634601) B24634601
theorem B15972551 : Blo 1246441 15972551 := bstep (se 1 (by rfl) ⟨11979413, by rfl⟩ : syracuseStep 15972551 = 23958827) B23958827
theorem B2882299 : Blo 1246441 2882299 := bstep (se 1 (by rfl) ⟨2161724, by rfl⟩ : syracuseStep 2882299 = 4323449) B4323449
theorem B4266839 : Blo 1246441 4266839 := bstep (se 1 (by rfl) ⟨3200129, by rfl⟩ : syracuseStep 4266839 = 6400259) B6400259
theorem B4209785 : Blo 1246441 4209785 := bstep (se 2 (by rfl) ⟨1578669, by rfl⟩ : syracuseStep 4209785 = 3157339) B3157339
theorem B7109801 : Blo 1246441 7109801 := bstep (se 2 (by rfl) ⟨2666175, by rfl⟩ : syracuseStep 7109801 = 5332351) B5332351
theorem B17997029 : Blo 1246441 17997029 := bstep (se 4 (by rfl) ⟨1687221, by rfl⟩ : syracuseStep 17997029 = 3374443) B3374443
theorem B4209947 : Blo 1246441 4209947 := bstep (se 1 (by rfl) ⟨3157460, by rfl⟩ : syracuseStep 4209947 = 6314921) B6314921
theorem B9477485 : Blo 1246441 9477485 := bstep (se 3 (by rfl) ⟨1777028, by rfl⟩ : syracuseStep 9477485 = 3554057) B3554057
theorem B20225513 : Blo 1246441 20225513 := bstep (se 2 (by rfl) ⟨7584567, by rfl⟩ : syracuseStep 20225513 = 15169135) B15169135
theorem B2997737 : Blo 1246441 2997737 := bstep (se 2 (by rfl) ⟨1124151, by rfl⟩ : syracuseStep 2997737 = 2248303) B2248303
theorem B2399851 : Blo 1246441 2399851 := bstep (se 1 (by rfl) ⟨1799888, by rfl⟩ : syracuseStep 2399851 = 3599777) B3599777
theorem B10804873 : Blo 1246441 10804873 := bstep (se 2 (by rfl) ⟨4051827, by rfl⟩ : syracuseStep 10804873 = 8103655) B8103655
theorem B17309497 : Blo 1246441 17309497 := bstep (se 2 (by rfl) ⟨6491061, by rfl⟩ : syracuseStep 17309497 = 12982123) B12982123
theorem B9477971 : Blo 1246441 9477971 := bstep (se 1 (by rfl) ⟨7108478, by rfl⟩ : syracuseStep 9477971 = 14216957) B14216957
theorem B5996857 : Blo 1246441 5996857 := bstep (se 2 (by rfl) ⟨2248821, by rfl⟩ : syracuseStep 5996857 = 4497643) B4497643
theorem B3416827 : Blo 1246441 3416827 := bstep (se 1 (by rfl) ⟨2562620, by rfl⟩ : syracuseStep 3416827 = 5125241) B5125241
theorem B25592669 : Blo 1246441 25592669 := bstep (se 3 (by rfl) ⟨4798625, by rfl⟩ : syracuseStep 25592669 = 9597251) B9597251
theorem B3843065 : Blo 1246441 3843065 := bstep (se 2 (by rfl) ⟨1441149, by rfl⟩ : syracuseStep 3843065 = 2882299) B2882299
theorem B4801787 : Blo 1246441 4801787 := bstep (se 1 (by rfl) ⟨3601340, by rfl⟩ : syracuseStep 4801787 = 7202681) B7202681
theorem B1246527 : Blo 1246441 1246527 := bstep (se 1 (by rfl) ⟨934895, by rfl⟩ : syracuseStep 1246527 = 1869791) B1869791
theorem B28812631 : Blo 1246441 28812631 := bstep (se 1 (by rfl) ⟨21609473, by rfl⟩ : syracuseStep 28812631 = 43218947) B43218947
theorem B1246567 : Blo 1246441 1246567 := bstep (se 1 (by rfl) ⟨934925, by rfl⟩ : syracuseStep 1246567 = 1869851) B1869851
theorem B1246687 : Blo 1246441 1246687 := bstep (se 1 (by rfl) ⟨935015, by rfl⟩ : syracuseStep 1246687 = 1870031) B1870031
theorem B1869695 : Blo 1246441 1869695 := bstep (se 1 (by rfl) ⟨1402271, by rfl⟩ : syracuseStep 1869695 = 2804543) B2804543
theorem B2844559 : Blo 1246441 2844559 := bstep (se 1 (by rfl) ⟨2133419, by rfl⟩ : syracuseStep 2844559 = 4266839) B4266839
theorem B5998531 : Blo 1246441 5998531 := bstep (se 1 (by rfl) ⟨4498898, by rfl⟩ : syracuseStep 5998531 = 8997797) B8997797
theorem B1870007 : Blo 1246441 1870007 := bstep (se 1 (by rfl) ⟨1402505, by rfl⟩ : syracuseStep 1870007 = 2805011) B2805011
theorem B6318323 : Blo 1246441 6318323 := bstep (se 1 (by rfl) ⟨4738742, by rfl⟩ : syracuseStep 6318323 = 9477485) B9477485
theorem B55413067 : Blo 1246441 55413067 := bstep (se 1 (by rfl) ⟨41559800, by rfl⟩ : syracuseStep 55413067 = 83119601) B83119601
theorem B23079329 : Blo 1246441 23079329 := bstep (se 2 (by rfl) ⟨8654748, by rfl⟩ : syracuseStep 23079329 = 17309497) B17309497
theorem B1870319 : Blo 1246441 1870319 := bstep (se 1 (by rfl) ⟨1402739, by rfl⟩ : syracuseStep 1870319 = 2805479) B2805479
theorem B4213241 : Blo 1246441 4213241 := bstep (se 2 (by rfl) ⟨1579965, by rfl⟩ : syracuseStep 4213241 = 3159931) B3159931
theorem B6318647 : Blo 1246441 6318647 := bstep (se 1 (by rfl) ⟨4738985, by rfl⟩ : syracuseStep 6318647 = 9477971) B9477971
theorem B4213403 : Blo 1246441 4213403 := bstep (se 1 (by rfl) ⟨3160052, by rfl⟩ : syracuseStep 4213403 = 6320105) B6320105
theorem B6318971 : Blo 1246441 6318971 := bstep (se 1 (by rfl) ⟨4739228, by rfl⟩ : syracuseStep 6318971 = 9478457) B9478457
theorem B12799205 : Blo 1246441 12799205 := bstep (se 4 (by rfl) ⟨1199925, by rfl⟩ : syracuseStep 12799205 = 2399851) B2399851
theorem B6311195 : Blo 1246441 6311195 := bstep (se 1 (by rfl) ⟨4733396, by rfl⟩ : syracuseStep 6311195 = 9466793) B9466793
theorem B3157289 : Blo 1246441 3157289 := bstep (se 2 (by rfl) ⟨1183983, by rfl⟩ : syracuseStep 3157289 = 2367967) B2367967
theorem B2665919 : Blo 1246441 2665919 := bstep (se 1 (by rfl) ⟨1999439, by rfl⟩ : syracuseStep 2665919 = 3998879) B3998879
theorem B1601051 : Blo 1246441 1601051 := bstep (se 1 (by rfl) ⟨1200788, by rfl⟩ : syracuseStep 1601051 = 2401577) B2401577
theorem B1404463 : Blo 1246441 1404463 := bstep (se 1 (by rfl) ⟨1053347, by rfl⟩ : syracuseStep 1404463 = 2106695) B2106695
theorem B5992015 : Blo 1246441 5992015 := bstep (se 1 (by rfl) ⟨4494011, by rfl⟩ : syracuseStep 5992015 = 8988023) B8988023
theorem B1871579 : Blo 1246441 1871579 := bstep (se 1 (by rfl) ⟨1403684, by rfl⟩ : syracuseStep 1871579 = 2807369) B2807369
theorem B3370889 : Blo 1246441 3370889 := bstep (se 2 (by rfl) ⟨1264083, by rfl⟩ : syracuseStep 3370889 = 2528167) B2528167
theorem B1871753 : Blo 1246441 1871753 := bstep (se 2 (by rfl) ⟨701907, by rfl⟩ : syracuseStep 1871753 = 1403815) B1403815
theorem B2805695 : Blo 1246441 2805695 := bstep (se 1 (by rfl) ⟨2104271, by rfl⟩ : syracuseStep 2805695 = 4208543) B4208543
theorem B10661867 : Blo 1246441 10661867 := bstep (se 1 (by rfl) ⟨7996400, by rfl⟩ : syracuseStep 10661867 = 15992801) B15992801
theorem B10948711 : Blo 1246441 10948711 := bstep (se 1 (by rfl) ⟨8211533, by rfl⟩ : syracuseStep 10948711 = 16423067) B16423067
theorem B1871993 : Blo 1246441 1871993 := bstep (se 2 (by rfl) ⟨701997, by rfl⟩ : syracuseStep 1871993 = 1403995) B1403995
theorem B3371321 : Blo 1246441 3371321 := bstep (se 2 (by rfl) ⟨1264245, by rfl⟩ : syracuseStep 3371321 = 2528491) B2528491
theorem B3600839 : Blo 1246441 3600839 := bstep (se 1 (by rfl) ⟨2700629, by rfl⟩ : syracuseStep 3600839 = 5401259) B5401259
theorem B23065195 : Blo 1246441 23065195 := bstep (se 1 (by rfl) ⟨17298896, by rfl⟩ : syracuseStep 23065195 = 34597793) B34597793
theorem B2806523 : Blo 1246441 2806523 := bstep (se 1 (by rfl) ⟨2104892, by rfl⟩ : syracuseStep 2806523 = 4209785) B4209785
theorem B4739867 : Blo 1246441 4739867 := bstep (se 1 (by rfl) ⟨3554900, by rfl⟩ : syracuseStep 4739867 = 7109801) B7109801
theorem B11998019 : Blo 1246441 11998019 := bstep (se 1 (by rfl) ⟨8998514, by rfl⟩ : syracuseStep 11998019 = 17997029) B17997029
theorem B14406497 : Blo 1246441 14406497 := bstep (se 2 (by rfl) ⟨5402436, by rfl⟩ : syracuseStep 14406497 = 10804873) B10804873
theorem B2806631 : Blo 1246441 2806631 := bstep (se 1 (by rfl) ⟨2104973, by rfl⟩ : syracuseStep 2806631 = 4209947) B4209947
theorem B32846759 : Blo 1246441 32846759 := bstep (se 1 (by rfl) ⟨24635069, by rfl⟩ : syracuseStep 32846759 = 49270139) B49270139
theorem B14218415 : Blo 1246441 14218415 := bstep (se 1 (by rfl) ⟨10663811, by rfl⟩ : syracuseStep 14218415 = 21327623) B21327623
theorem B3159263 : Blo 1246441 3159263 := bstep (se 1 (by rfl) ⟨2369447, by rfl⟩ : syracuseStep 3159263 = 4738895) B4738895
theorem B1775081 : Blo 1246441 1775081 := bstep (se 2 (by rfl) ⟨665655, by rfl⟩ : syracuseStep 1775081 = 1331311) B1331311
theorem B4208111 : Blo 1246441 4208111 := bstep (se 1 (by rfl) ⟨3156083, by rfl⟩ : syracuseStep 4208111 = 6312167) B6312167
theorem B230291099 : Blo 1246441 230291099 := bstep (se 1 (by rfl) ⟨172718324, by rfl⟩ : syracuseStep 230291099 = 345436649) B345436649
theorem B3553055 : Blo 1246441 3553055 := bstep (se 1 (by rfl) ⟨2664791, by rfl⟩ : syracuseStep 3553055 = 5329583) B5329583
theorem B1685287 : Blo 1246441 1685287 := bstep (se 1 (by rfl) ⟨1263965, by rfl⟩ : syracuseStep 1685287 = 2527931) B2527931
theorem B1578791 : Blo 1246441 1578791 := bstep (se 1 (by rfl) ⟨1184093, by rfl⟩ : syracuseStep 1578791 = 2368187) B2368187
theorem B1578943 : Blo 1246441 1578943 := bstep (se 1 (by rfl) ⟨1184207, by rfl⟩ : syracuseStep 1578943 = 2368415) B2368415
theorem B1775719 : Blo 1246441 1775719 := bstep (se 1 (by rfl) ⟨1331789, by rfl⟩ : syracuseStep 1775719 = 2663579) B2663579
theorem B1579115 : Blo 1246441 1579115 := bstep (se 1 (by rfl) ⟨1184336, by rfl⟩ : syracuseStep 1579115 = 2368673) B2368673
theorem B4733275 : Blo 1246441 4733275 := bstep (se 1 (by rfl) ⟨3549956, by rfl⟩ : syracuseStep 4733275 = 7099913) B7099913
theorem B10648367 : Blo 1246441 10648367 := bstep (se 1 (by rfl) ⟨7986275, by rfl⟩ : syracuseStep 10648367 = 15972551) B15972551
theorem B36453361 : Blo 1246441 36453361 := bstep (se 2 (by rfl) ⟨13670010, by rfl⟩ : syracuseStep 36453361 = 27340021) B27340021
theorem B4734233 : Blo 1246441 4734233 := bstep (se 2 (by rfl) ⟨1775337, by rfl⟩ : syracuseStep 4734233 = 3550675) B3550675
theorem B7986559 : Blo 1246441 7986559 := bstep (se 1 (by rfl) ⟨5989919, by rfl⟩ : syracuseStep 7986559 = 11979839) B11979839
theorem B13483675 : Blo 1246441 13483675 := bstep (se 1 (by rfl) ⟨10112756, by rfl⟩ : syracuseStep 13483675 = 20225513) B20225513
theorem B2104987 : Blo 1246441 2104987 := bstep (se 1 (by rfl) ⟨1578740, by rfl⟩ : syracuseStep 2104987 = 3157481) B3157481
theorem B1998491 : Blo 1246441 1998491 := bstep (se 1 (by rfl) ⟨1498868, by rfl⟩ : syracuseStep 1998491 = 2997737) B2997737
theorem B2367625 : Blo 1246441 2367625 := bstep (se 2 (by rfl) ⟨887859, by rfl⟩ : syracuseStep 2367625 = 1775719) B1775719
theorem B14598281 : Blo 1246441 14598281 := bstep (se 2 (by rfl) ⟨5474355, by rfl⟩ : syracuseStep 14598281 = 10948711) B10948711
theorem B4210973 : Blo 1246441 4210973 := bstep (se 3 (by rfl) ⟨789557, by rfl⟩ : syracuseStep 4210973 = 1579115) B1579115
theorem B2400559 : Blo 1246441 2400559 := bstep (se 1 (by rfl) ⟨1800419, by rfl⟩ : syracuseStep 2400559 = 3600839) B3600839
theorem B7995809 : Blo 1246441 7995809 := bstep (se 2 (by rfl) ⟨2998428, by rfl⟩ : syracuseStep 7995809 = 5996857) B5996857
theorem B73884089 : Blo 1246441 73884089 := bstep (se 2 (by rfl) ⟨27706533, by rfl⟩ : syracuseStep 73884089 = 55413067) B55413067
theorem B21897839 : Blo 1246441 21897839 := bstep (se 1 (by rfl) ⟨16423379, by rfl⟩ : syracuseStep 21897839 = 32846759) B32846759
theorem B9478943 : Blo 1246441 9478943 := bstep (se 1 (by rfl) ⟨7109207, by rfl⟩ : syracuseStep 9478943 = 14218415) B14218415
theorem B30753593 : Blo 1246441 30753593 := bstep (se 2 (by rfl) ⟨11532597, by rfl⟩ : syracuseStep 30753593 = 23065195) B23065195
theorem B2106175 : Blo 1246441 2106175 := bstep (se 1 (by rfl) ⟨1579631, by rfl⟩ : syracuseStep 2106175 = 3159263) B3159263
theorem B4555769 : Blo 1246441 4555769 := bstep (se 2 (by rfl) ⟨1708413, by rfl⟩ : syracuseStep 4555769 = 3416827) B3416827
theorem B153527399 : Blo 1246441 153527399 := bstep (se 1 (by rfl) ⟨115145549, by rfl⟩ : syracuseStep 153527399 = 230291099) B230291099
theorem B2368703 : Blo 1246441 2368703 := bstep (se 1 (by rfl) ⟨1776527, by rfl⟩ : syracuseStep 2368703 = 3553055) B3553055
theorem B1246463 : Blo 1246441 1246463 := bstep (se 1 (by rfl) ⟨934847, by rfl⟩ : syracuseStep 1246463 = 1869695) B1869695
theorem B48604481 : Blo 1246441 48604481 := bstep (se 2 (by rfl) ⟨18226680, by rfl⟩ : syracuseStep 48604481 = 36453361) B36453361
theorem B4269469 : Blo 1246441 4269469 := bstep (se 3 (by rfl) ⟨800525, by rfl⟩ : syracuseStep 4269469 = 1601051) B1601051
theorem B1246671 : Blo 1246441 1246671 := bstep (se 1 (by rfl) ⟨935003, by rfl⟩ : syracuseStep 1246671 = 1870007) B1870007
theorem B4212215 : Blo 1246441 4212215 := bstep (se 1 (by rfl) ⟨3159161, by rfl⟩ : syracuseStep 4212215 = 6318323) B6318323
theorem B15386219 : Blo 1246441 15386219 := bstep (se 1 (by rfl) ⟨11539664, by rfl⟩ : syracuseStep 15386219 = 23079329) B23079329
theorem B1246879 : Blo 1246441 1246879 := bstep (se 1 (by rfl) ⟨935159, by rfl⟩ : syracuseStep 1246879 = 1870319) B1870319
theorem B4212431 : Blo 1246441 4212431 := bstep (se 1 (by rfl) ⟨3159323, by rfl⟩ : syracuseStep 4212431 = 6318647) B6318647
theorem B4212647 : Blo 1246441 4212647 := bstep (se 1 (by rfl) ⟨3159485, by rfl⟩ : syracuseStep 4212647 = 6318971) B6318971
theorem B7989353 : Blo 1246441 7989353 := bstep (se 2 (by rfl) ⟨2996007, by rfl⟩ : syracuseStep 7989353 = 5992015) B5992015
theorem B3156155 : Blo 1246441 3156155 := bstep (se 1 (by rfl) ⟨2367116, by rfl⟩ : syracuseStep 3156155 = 4734233) B4734233
theorem B2247049 : Blo 1246441 2247049 := bstep (se 2 (by rfl) ⟨842643, by rfl⟩ : syracuseStep 2247049 = 1685287) B1685287
theorem B1247719 : Blo 1246441 1247719 := bstep (se 1 (by rfl) ⟨935789, by rfl⟩ : syracuseStep 1247719 = 1871579) B1871579
theorem B7998041 : Blo 1246441 7998041 := bstep (se 2 (by rfl) ⟨2999265, by rfl⟩ : syracuseStep 7998041 = 5998531) B5998531
theorem B2247259 : Blo 1246441 2247259 := bstep (se 1 (by rfl) ⟨1685444, by rfl⟩ : syracuseStep 2247259 = 3370889) B3370889
theorem B1247835 : Blo 1246441 1247835 := bstep (se 1 (by rfl) ⟨935876, by rfl⟩ : syracuseStep 1247835 = 1871753) B1871753
theorem B1870463 : Blo 1246441 1870463 := bstep (se 1 (by rfl) ⟨1402847, by rfl⟩ : syracuseStep 1870463 = 2805695) B2805695
theorem B1247995 : Blo 1246441 1247995 := bstep (se 1 (by rfl) ⟨935996, by rfl⟩ : syracuseStep 1247995 = 1871993) B1871993
theorem B6311033 : Blo 1246441 6311033 := bstep (se 2 (by rfl) ⟨2366637, by rfl⟩ : syracuseStep 6311033 = 4733275) B4733275
theorem B1871015 : Blo 1246441 1871015 := bstep (se 1 (by rfl) ⟨1403261, by rfl⟩ : syracuseStep 1871015 = 2806523) B2806523
theorem B7998679 : Blo 1246441 7998679 := bstep (se 1 (by rfl) ⟨5999009, by rfl⟩ : syracuseStep 7998679 = 11998019) B11998019
theorem B9604331 : Blo 1246441 9604331 := bstep (se 1 (by rfl) ⟨7203248, by rfl⟩ : syracuseStep 9604331 = 14406497) B14406497
theorem B1871087 : Blo 1246441 1871087 := bstep (se 1 (by rfl) ⟨1403315, by rfl⟩ : syracuseStep 1871087 = 2806631) B2806631
theorem B8990189 : Blo 1246441 8990189 := bstep (se 3 (by rfl) ⟨1685660, by rfl⟩ : syracuseStep 8990189 = 3371321) B3371321
theorem B2805407 : Blo 1246441 2805407 := bstep (se 1 (by rfl) ⟨2104055, by rfl⟩ : syracuseStep 2805407 = 4208111) B4208111
theorem B5329309 : Blo 1246441 5329309 := bstep (se 3 (by rfl) ⟨999245, by rfl⟩ : syracuseStep 5329309 = 1998491) B1998491
theorem B38416841 : Blo 1246441 38416841 := bstep (se 2 (by rfl) ⟨14406315, by rfl⟩ : syracuseStep 38416841 = 28812631) B28812631
theorem B7098911 : Blo 1246441 7098911 := bstep (se 1 (by rfl) ⟨5324183, by rfl⟩ : syracuseStep 7098911 = 10648367) B10648367
theorem B1872617 : Blo 1246441 1872617 := bstep (se 2 (by rfl) ⟨702231, by rfl⟩ : syracuseStep 1872617 = 1404463) B1404463
theorem B8532803 : Blo 1246441 8532803 := bstep (se 1 (by rfl) ⟨6399602, by rfl⟩ : syracuseStep 8532803 = 12799205) B12799205
theorem B4207463 : Blo 1246441 4207463 := bstep (se 1 (by rfl) ⟨3155597, by rfl⟩ : syracuseStep 4207463 = 6311195) B6311195
theorem B17978233 : Blo 1246441 17978233 := bstep (se 2 (by rfl) ⟨6741837, by rfl⟩ : syracuseStep 17978233 = 13483675) B13483675
theorem B2806649 : Blo 1246441 2806649 := bstep (se 2 (by rfl) ⟨1052493, by rfl⟩ : syracuseStep 2806649 = 2104987) B2104987
theorem B7107911 : Blo 1246441 7107911 := bstep (se 1 (by rfl) ⟨5330933, by rfl⟩ : syracuseStep 7107911 = 10661867) B10661867
theorem B3159911 : Blo 1246441 3159911 := bstep (se 1 (by rfl) ⟨2369933, by rfl⟩ : syracuseStep 3159911 = 4739867) B4739867
theorem B17061779 : Blo 1246441 17061779 := bstep (se 1 (by rfl) ⟨12796334, by rfl⟩ : syracuseStep 17061779 = 25592669) B25592669
theorem B2562043 : Blo 1246441 2562043 := bstep (se 1 (by rfl) ⟨1921532, by rfl⟩ : syracuseStep 2562043 = 3843065) B3843065
theorem B3201191 : Blo 1246441 3201191 := bstep (se 1 (by rfl) ⟨2400893, by rfl⟩ : syracuseStep 3201191 = 4801787) B4801787
theorem B7109117 : Blo 1246441 7109117 := bstep (se 3 (by rfl) ⟨1332959, by rfl⟩ : syracuseStep 7109117 = 2665919) B2665919
theorem B4733549 : Blo 1246441 4733549 := bstep (se 3 (by rfl) ⟨887540, by rfl⟩ : syracuseStep 4733549 = 1775081) B1775081
theorem B2808827 : Blo 1246441 2808827 := bstep (se 1 (by rfl) ⟨2106620, by rfl⟩ : syracuseStep 2808827 = 4213241) B4213241
theorem B2808935 : Blo 1246441 2808935 := bstep (se 1 (by rfl) ⟨2106701, by rfl⟩ : syracuseStep 2808935 = 4213403) B4213403
theorem B10648745 : Blo 1246441 10648745 := bstep (se 2 (by rfl) ⟨3993279, by rfl⟩ : syracuseStep 10648745 = 7986559) B7986559
theorem B4210109 : Blo 1246441 4210109 := bstep (se 3 (by rfl) ⟨789395, by rfl⟩ : syracuseStep 4210109 = 1578791) B1578791
theorem B2104859 : Blo 1246441 2104859 := bstep (se 1 (by rfl) ⟨1578644, by rfl⟩ : syracuseStep 2104859 = 3157289) B3157289
theorem B3792745 : Blo 1246441 3792745 := bstep (se 2 (by rfl) ⟨1422279, by rfl⟩ : syracuseStep 3792745 = 2844559) B2844559
theorem B2105257 : Blo 1246441 2105257 := bstep (se 2 (by rfl) ⟨789471, by rfl⟩ : syracuseStep 2105257 = 1578943) B1578943
theorem B9732187 : Blo 1246441 9732187 := bstep (se 1 (by rfl) ⟨7299140, by rfl⟩ : syracuseStep 9732187 = 14598281) B14598281
theorem B3416057 : Blo 1246441 3416057 := bstep (se 2 (by rfl) ⟨1281021, by rfl⟩ : syracuseStep 3416057 = 2562043) B2562043
theorem B14598559 : Blo 1246441 14598559 := bstep (se 1 (by rfl) ⟨10948919, by rfl⟩ : syracuseStep 14598559 = 21897839) B21897839
theorem B6316541 : Blo 1246441 6316541 := bstep (se 3 (by rfl) ⟨1184351, by rfl⟩ : syracuseStep 6316541 = 2368703) B2368703
theorem B102351599 : Blo 1246441 102351599 := bstep (se 1 (by rfl) ⟨76763699, by rfl⟩ : syracuseStep 102351599 = 153527399) B153527399
theorem B10257479 : Blo 1246441 10257479 := bstep (se 1 (by rfl) ⟨7693109, by rfl⟩ : syracuseStep 10257479 = 15386219) B15386219
theorem B23970977 : Blo 1246441 23970977 := bstep (se 2 (by rfl) ⟨8989116, by rfl⟩ : syracuseStep 23970977 = 17978233) B17978233
theorem B2106607 : Blo 1246441 2106607 := bstep (se 1 (by rfl) ⟨1579955, by rfl⟩ : syracuseStep 2106607 = 3159911) B3159911
theorem B5326235 : Blo 1246441 5326235 := bstep (se 1 (by rfl) ⟨3994676, by rfl⟩ : syracuseStep 5326235 = 7989353) B7989353
theorem B3155699 : Blo 1246441 3155699 := bstep (se 1 (by rfl) ⟨2366774, by rfl⟩ : syracuseStep 3155699 = 4733549) B4733549
theorem B1246975 : Blo 1246441 1246975 := bstep (se 1 (by rfl) ⟨935231, by rfl⟩ : syracuseStep 1246975 = 1870463) B1870463
theorem B20227973 : Blo 1246441 20227973 := bstep (se 4 (by rfl) ⟨1896372, by rfl⟩ : syracuseStep 20227973 = 3792745) B3792745
theorem B1247343 : Blo 1246441 1247343 := bstep (se 1 (by rfl) ⟨935507, by rfl⟩ : syracuseStep 1247343 = 1871015) B1871015
theorem B1247391 : Blo 1246441 1247391 := bstep (se 1 (by rfl) ⟨935543, by rfl⟩ : syracuseStep 1247391 = 1871087) B1871087
theorem B1403239 : Blo 1246441 1403239 := bstep (se 1 (by rfl) ⟨1052429, by rfl⟩ : syracuseStep 1403239 = 2104859) B2104859
theorem B1870271 : Blo 1246441 1870271 := bstep (se 1 (by rfl) ⟨1402703, by rfl⟩ : syracuseStep 1870271 = 2805407) B2805407
theorem B3156833 : Blo 1246441 3156833 := bstep (se 2 (by rfl) ⟨1183812, by rfl⟩ : syracuseStep 3156833 = 2367625) B2367625
theorem B25611227 : Blo 1246441 25611227 := bstep (se 1 (by rfl) ⟨19208420, by rfl⟩ : syracuseStep 25611227 = 38416841) B38416841
theorem B1248411 : Blo 1246441 1248411 := bstep (se 1 (by rfl) ⟨936308, by rfl⟩ : syracuseStep 1248411 = 1872617) B1872617
theorem B6319295 : Blo 1246441 6319295 := bstep (se 1 (by rfl) ⟨4739471, by rfl⟩ : syracuseStep 6319295 = 9478943) B9478943
theorem B7105745 : Blo 1246441 7105745 := bstep (se 2 (by rfl) ⟨2664654, by rfl⟩ : syracuseStep 7105745 = 5329309) B5329309
theorem B2804975 : Blo 1246441 2804975 := bstep (se 1 (by rfl) ⟨2103731, by rfl⟩ : syracuseStep 2804975 = 4207463) B4207463
theorem B1871099 : Blo 1246441 1871099 := bstep (se 1 (by rfl) ⟨1403324, by rfl⟩ : syracuseStep 1871099 = 2806649) B2806649
theorem B32402987 : Blo 1246441 32402987 := bstep (se 1 (by rfl) ⟨24302240, by rfl⟩ : syracuseStep 32402987 = 48604481) B48604481
theorem B4738607 : Blo 1246441 4738607 := bstep (se 1 (by rfl) ⟨3553955, by rfl⟩ : syracuseStep 4738607 = 7107911) B7107911
theorem B11374519 : Blo 1246441 11374519 := bstep (se 1 (by rfl) ⟨8530889, by rfl⟩ : syracuseStep 11374519 = 17061779) B17061779
theorem B2134127 : Blo 1246441 2134127 := bstep (se 1 (by rfl) ⟨1600595, by rfl⟩ : syracuseStep 2134127 = 3201191) B3201191
theorem B4739411 : Blo 1246441 4739411 := bstep (se 1 (by rfl) ⟨3554558, by rfl⟩ : syracuseStep 4739411 = 7109117) B7109117
theorem B1872551 : Blo 1246441 1872551 := bstep (se 1 (by rfl) ⟨1404413, by rfl⟩ : syracuseStep 1872551 = 2808827) B2808827
theorem B1872623 : Blo 1246441 1872623 := bstep (se 1 (by rfl) ⟨1404467, by rfl⟩ : syracuseStep 1872623 = 2808935) B2808935
theorem B4207355 : Blo 1246441 4207355 := bstep (se 1 (by rfl) ⟨3155516, by rfl⟩ : syracuseStep 4207355 = 6311033) B6311033
theorem B7099163 : Blo 1246441 7099163 := bstep (se 1 (by rfl) ⟨5324372, by rfl⟩ : syracuseStep 7099163 = 10648745) B10648745
theorem B6402887 : Blo 1246441 6402887 := bstep (se 1 (by rfl) ⟨4802165, by rfl⟩ : syracuseStep 6402887 = 9604331) B9604331
theorem B22754141 : Blo 1246441 22754141 := bstep (se 3 (by rfl) ⟨4266401, by rfl⟩ : syracuseStep 22754141 = 8532803) B8532803
theorem B2806739 : Blo 1246441 2806739 := bstep (se 1 (by rfl) ⟨2105054, by rfl⟩ : syracuseStep 2806739 = 4210109) B4210109
theorem B5993459 : Blo 1246441 5993459 := bstep (se 1 (by rfl) ⟨4495094, by rfl⟩ : syracuseStep 5993459 = 8990189) B8990189
theorem B2807009 : Blo 1246441 2807009 := bstep (se 2 (by rfl) ⟨1052628, by rfl⟩ : syracuseStep 2807009 = 2105257) B2105257
theorem B2807315 : Blo 1246441 2807315 := bstep (se 1 (by rfl) ⟨2105486, by rfl⟩ : syracuseStep 2807315 = 4210973) B4210973
theorem B5330539 : Blo 1246441 5330539 := bstep (se 1 (by rfl) ⟨3997904, by rfl⟩ : syracuseStep 5330539 = 7995809) B7995809
theorem B49256059 : Blo 1246441 49256059 := bstep (se 1 (by rfl) ⟨36942044, by rfl⟩ : syracuseStep 49256059 = 73884089) B73884089
theorem B4732607 : Blo 1246441 4732607 := bstep (se 1 (by rfl) ⟨3549455, by rfl⟩ : syracuseStep 4732607 = 7098911) B7098911
theorem B2996065 : Blo 1246441 2996065 := bstep (se 2 (by rfl) ⟨1123524, by rfl⟩ : syracuseStep 2996065 = 2247049) B2247049
theorem B20502395 : Blo 1246441 20502395 := bstep (se 1 (by rfl) ⟨15376796, by rfl⟩ : syracuseStep 20502395 = 30753593) B30753593
theorem B2996345 : Blo 1246441 2996345 := bstep (se 2 (by rfl) ⟨1123629, by rfl⟩ : syracuseStep 2996345 = 2247259) B2247259
theorem B2808143 : Blo 1246441 2808143 := bstep (se 1 (by rfl) ⟨2106107, by rfl⟩ : syracuseStep 2808143 = 4212215) B4212215
theorem B2808233 : Blo 1246441 2808233 := bstep (se 2 (by rfl) ⟨1053087, by rfl⟩ : syracuseStep 2808233 = 2106175) B2106175
theorem B2808287 : Blo 1246441 2808287 := bstep (se 1 (by rfl) ⟨2106215, by rfl⟩ : syracuseStep 2808287 = 4212431) B4212431
theorem B2808431 : Blo 1246441 2808431 := bstep (se 1 (by rfl) ⟨2106323, by rfl⟩ : syracuseStep 2808431 = 4212647) B4212647
theorem B2104103 : Blo 1246441 2104103 := bstep (se 1 (by rfl) ⟨1578077, by rfl⟩ : syracuseStep 2104103 = 3156155) B3156155
theorem B12802981 : Blo 1246441 12802981 := bstep (se 4 (by rfl) ⟨1200279, by rfl⟩ : syracuseStep 12802981 = 2400559) B2400559
theorem B10664905 : Blo 1246441 10664905 := bstep (se 2 (by rfl) ⟨3999339, by rfl⟩ : syracuseStep 10664905 = 7998679) B7998679
theorem B5332027 : Blo 1246441 5332027 := bstep (se 1 (by rfl) ⟨3999020, by rfl⟩ : syracuseStep 5332027 = 7998041) B7998041
theorem B5692625 : Blo 1246441 5692625 := bstep (se 2 (by rfl) ⟨2134734, by rfl⟩ : syracuseStep 5692625 = 4269469) B4269469
theorem B12148717 : Blo 1246441 12148717 := bstep (se 3 (by rfl) ⟨2277884, by rfl⟩ : syracuseStep 12148717 = 4555769) B4555769
theorem B12976249 : Blo 1246441 12976249 := bstep (se 2 (by rfl) ⟨4866093, by rfl⟩ : syracuseStep 12976249 = 9732187) B9732187
theorem B4211027 : Blo 1246441 4211027 := bstep (se 1 (by rfl) ⟨3158270, by rfl⟩ : syracuseStep 4211027 = 6316541) B6316541
theorem B19464745 : Blo 1246441 19464745 := bstep (se 2 (by rfl) ⟨7299279, by rfl⟩ : syracuseStep 19464745 = 14598559) B14598559
theorem B4268591 : Blo 1246441 4268591 := bstep (se 1 (by rfl) ⟨3201443, by rfl⟩ : syracuseStep 4268591 = 6402887) B6402887
theorem B3155071 : Blo 1246441 3155071 := bstep (se 1 (by rfl) ⟨2366303, by rfl⟩ : syracuseStep 3155071 = 4732607) B4732607
theorem B1246847 : Blo 1246441 1246847 := bstep (se 1 (by rfl) ⟨935135, by rfl⟩ : syracuseStep 1246847 = 1870271) B1870271
theorem B1402735 : Blo 1246441 1402735 := bstep (se 1 (by rfl) ⟨1052051, by rfl⟩ : syracuseStep 1402735 = 2104103) B2104103
theorem B17074151 : Blo 1246441 17074151 := bstep (se 1 (by rfl) ⟨12805613, by rfl⟩ : syracuseStep 17074151 = 25611227) B25611227
theorem B4212863 : Blo 1246441 4212863 := bstep (se 1 (by rfl) ⟨3159647, by rfl⟩ : syracuseStep 4212863 = 6319295) B6319295
theorem B4737163 : Blo 1246441 4737163 := bstep (se 1 (by rfl) ⟨3552872, by rfl⟩ : syracuseStep 4737163 = 7105745) B7105745
theorem B3795083 : Blo 1246441 3795083 := bstep (se 1 (by rfl) ⟨2846312, by rfl⟩ : syracuseStep 3795083 = 5692625) B5692625
theorem B1869983 : Blo 1246441 1869983 := bstep (se 1 (by rfl) ⟨1402487, by rfl⟩ : syracuseStep 1869983 = 2804975) B2804975
theorem B1247399 : Blo 1246441 1247399 := bstep (se 1 (by rfl) ⟨935549, by rfl⟩ : syracuseStep 1247399 = 1871099) B1871099
theorem B15166025 : Blo 1246441 15166025 := bstep (se 2 (by rfl) ⟨5687259, by rfl⟩ : syracuseStep 15166025 = 11374519) B11374519
theorem B16198289 : Blo 1246441 16198289 := bstep (se 2 (by rfl) ⟨6074358, by rfl⟩ : syracuseStep 16198289 = 12148717) B12148717
theorem B1248367 : Blo 1246441 1248367 := bstep (se 1 (by rfl) ⟨936275, by rfl⟩ : syracuseStep 1248367 = 1872551) B1872551
theorem B1870985 : Blo 1246441 1870985 := bstep (se 2 (by rfl) ⟨701619, by rfl⟩ : syracuseStep 1870985 = 1403239) B1403239
theorem B68234399 : Blo 1246441 68234399 := bstep (se 1 (by rfl) ⟨51175799, by rfl⟩ : syracuseStep 68234399 = 102351599) B102351599
theorem B1248415 : Blo 1246441 1248415 := bstep (se 1 (by rfl) ⟨936311, by rfl⟩ : syracuseStep 1248415 = 1872623) B1872623
theorem B2804903 : Blo 1246441 2804903 := bstep (se 1 (by rfl) ⟨2103677, by rfl⟩ : syracuseStep 2804903 = 4207355) B4207355
theorem B1871159 : Blo 1246441 1871159 := bstep (se 1 (by rfl) ⟨1403369, by rfl⟩ : syracuseStep 1871159 = 2806739) B2806739
theorem B1871339 : Blo 1246441 1871339 := bstep (se 1 (by rfl) ⟨1403504, by rfl⟩ : syracuseStep 1871339 = 2807009) B2807009
theorem B3550823 : Blo 1246441 3550823 := bstep (se 1 (by rfl) ⟨2663117, by rfl⟩ : syracuseStep 3550823 = 5326235) B5326235
theorem B1871543 : Blo 1246441 1871543 := bstep (se 1 (by rfl) ⟨1403657, by rfl⟩ : syracuseStep 1871543 = 2807315) B2807315
theorem B13668263 : Blo 1246441 13668263 := bstep (se 1 (by rfl) ⟨10251197, by rfl⟩ : syracuseStep 13668263 = 20502395) B20502395
theorem B1872095 : Blo 1246441 1872095 := bstep (se 1 (by rfl) ⟨1404071, by rfl⟩ : syracuseStep 1872095 = 2808143) B2808143
theorem B1872155 : Blo 1246441 1872155 := bstep (se 1 (by rfl) ⟨1404116, by rfl⟩ : syracuseStep 1872155 = 2808233) B2808233
theorem B1872191 : Blo 1246441 1872191 := bstep (se 1 (by rfl) ⟨1404143, by rfl⟩ : syracuseStep 1872191 = 2808287) B2808287
theorem B1872287 : Blo 1246441 1872287 := bstep (se 1 (by rfl) ⟨1404215, by rfl⟩ : syracuseStep 1872287 = 2808431) B2808431
theorem B7107385 : Blo 1246441 7107385 := bstep (se 2 (by rfl) ⟨2665269, by rfl⟩ : syracuseStep 7107385 = 5330539) B5330539
theorem B53941261 : Blo 1246441 53941261 := bstep (se 3 (by rfl) ⟨10113986, by rfl⟩ : syracuseStep 53941261 = 20227973) B20227973
theorem B3159071 : Blo 1246441 3159071 := bstep (se 1 (by rfl) ⟨2369303, by rfl⟩ : syracuseStep 3159071 = 4738607) B4738607
theorem B3994753 : Blo 1246441 3994753 := bstep (se 2 (by rfl) ⟨1498032, by rfl⟩ : syracuseStep 3994753 = 2996065) B2996065
theorem B1422751 : Blo 1246441 1422751 := bstep (se 1 (by rfl) ⟨1067063, by rfl⟩ : syracuseStep 1422751 = 2134127) B2134127
theorem B3159607 : Blo 1246441 3159607 := bstep (se 1 (by rfl) ⟨2369705, by rfl⟩ : syracuseStep 3159607 = 4739411) B4739411
theorem B4732775 : Blo 1246441 4732775 := bstep (se 1 (by rfl) ⟨3549581, by rfl⟩ : syracuseStep 4732775 = 7099163) B7099163
theorem B15169427 : Blo 1246441 15169427 := bstep (se 1 (by rfl) ⟨11377070, by rfl⟩ : syracuseStep 15169427 = 22754141) B22754141
theorem B3995639 : Blo 1246441 3995639 := bstep (se 1 (by rfl) ⟨2996729, by rfl⟩ : syracuseStep 3995639 = 5993459) B5993459
theorem B6838319 : Blo 1246441 6838319 := bstep (se 1 (by rfl) ⟨5128739, by rfl⟩ : syracuseStep 6838319 = 10257479) B10257479
theorem B15980651 : Blo 1246441 15980651 := bstep (se 1 (by rfl) ⟨11985488, by rfl⟩ : syracuseStep 15980651 = 23970977) B23970977
theorem B2103799 : Blo 1246441 2103799 := bstep (se 1 (by rfl) ⟨1577849, by rfl⟩ : syracuseStep 2103799 = 3155699) B3155699
theorem B17070641 : Blo 1246441 17070641 := bstep (se 2 (by rfl) ⟨6401490, by rfl⟩ : syracuseStep 17070641 = 12802981) B12802981
theorem B14219873 : Blo 1246441 14219873 := bstep (se 2 (by rfl) ⟨5332452, by rfl⟩ : syracuseStep 14219873 = 10664905) B10664905
theorem B7109369 : Blo 1246441 7109369 := bstep (se 2 (by rfl) ⟨2666013, by rfl⟩ : syracuseStep 7109369 = 5332027) B5332027
theorem B1997563 : Blo 1246441 1997563 := bstep (se 1 (by rfl) ⟨1498172, by rfl⟩ : syracuseStep 1997563 = 2996345) B2996345
theorem B2808809 : Blo 1246441 2808809 := bstep (se 2 (by rfl) ⟨1053303, by rfl⟩ : syracuseStep 2808809 = 2106607) B2106607
theorem B2104555 : Blo 1246441 2104555 := bstep (se 1 (by rfl) ⟨1578416, by rfl⟩ : syracuseStep 2104555 = 3156833) B3156833
theorem B65674745 : Blo 1246441 65674745 := bstep (se 2 (by rfl) ⟨24628029, by rfl⟩ : syracuseStep 65674745 = 49256059) B49256059
theorem B21601991 : Blo 1246441 21601991 := bstep (se 1 (by rfl) ⟨16201493, by rfl⟩ : syracuseStep 21601991 = 32402987) B32402987
theorem B2277371 : Blo 1246441 2277371 := bstep (se 1 (by rfl) ⟨1708028, by rfl⟩ : syracuseStep 2277371 = 3416057) B3416057
theorem B17301665 : Blo 1246441 17301665 := bstep (se 2 (by rfl) ⟨6488124, by rfl⟩ : syracuseStep 17301665 = 12976249) B12976249
theorem B6316217 : Blo 1246441 6316217 := bstep (se 2 (by rfl) ⟨2368581, by rfl⟩ : syracuseStep 6316217 = 4737163) B4737163
theorem B2106047 : Blo 1246441 2106047 := bstep (se 1 (by rfl) ⟨1579535, by rfl⟩ : syracuseStep 2106047 = 3159071) B3159071
theorem B25952993 : Blo 1246441 25952993 := bstep (se 2 (by rfl) ⟨9732372, by rfl⟩ : syracuseStep 25952993 = 19464745) B19464745
theorem B2663417 : Blo 1246441 2663417 := bstep (se 2 (by rfl) ⟨998781, by rfl⟩ : syracuseStep 2663417 = 1997563) B1997563
theorem B3155183 : Blo 1246441 3155183 := bstep (se 1 (by rfl) ⟨2366387, by rfl⟩ : syracuseStep 3155183 = 4732775) B4732775
theorem B2663759 : Blo 1246441 2663759 := bstep (se 1 (by rfl) ⟨1997819, by rfl⟩ : syracuseStep 2663759 = 3995639) B3995639
theorem B1246655 : Blo 1246441 1246655 := bstep (se 1 (by rfl) ⟨934991, by rfl⟩ : syracuseStep 1246655 = 1869983) B1869983
theorem B5326337 : Blo 1246441 5326337 := bstep (se 2 (by rfl) ⟨1997376, by rfl⟩ : syracuseStep 5326337 = 3994753) B3994753
theorem B11380427 : Blo 1246441 11380427 := bstep (se 1 (by rfl) ⟨8535320, by rfl⟩ : syracuseStep 11380427 = 17070641) B17070641
theorem B10110683 : Blo 1246441 10110683 := bstep (se 1 (by rfl) ⟨7583012, by rfl⟩ : syracuseStep 10110683 = 15166025) B15166025
theorem B9479915 : Blo 1246441 9479915 := bstep (se 1 (by rfl) ⟨7109936, by rfl⟩ : syracuseStep 9479915 = 14219873) B14219873
theorem B10798859 : Blo 1246441 10798859 := bstep (se 1 (by rfl) ⟨8099144, by rfl⟩ : syracuseStep 10798859 = 16198289) B16198289
theorem B4212809 : Blo 1246441 4212809 := bstep (se 2 (by rfl) ⟨1579803, by rfl⟩ : syracuseStep 4212809 = 3159607) B3159607
theorem B1247323 : Blo 1246441 1247323 := bstep (se 1 (by rfl) ⟨935492, by rfl⟩ : syracuseStep 1247323 = 1870985) B1870985
theorem B1869935 : Blo 1246441 1869935 := bstep (se 1 (by rfl) ⟨1402451, by rfl⟩ : syracuseStep 1869935 = 2804903) B2804903
theorem B1247439 : Blo 1246441 1247439 := bstep (se 1 (by rfl) ⟨935579, by rfl⟩ : syracuseStep 1247439 = 1871159) B1871159
theorem B1247559 : Blo 1246441 1247559 := bstep (se 1 (by rfl) ⟨935669, by rfl⟩ : syracuseStep 1247559 = 1871339) B1871339
theorem B1247695 : Blo 1246441 1247695 := bstep (se 1 (by rfl) ⟨935771, by rfl⟩ : syracuseStep 1247695 = 1871543) B1871543
theorem B1870313 : Blo 1246441 1870313 := bstep (se 2 (by rfl) ⟨701367, by rfl⟩ : syracuseStep 1870313 = 1402735) B1402735
theorem B9112175 : Blo 1246441 9112175 := bstep (se 1 (by rfl) ⟨6834131, by rfl⟩ : syracuseStep 9112175 = 13668263) B13668263
theorem B1518247 : Blo 1246441 1518247 := bstep (se 1 (by rfl) ⟨1138685, by rfl⟩ : syracuseStep 1518247 = 2277371) B2277371
theorem B1248063 : Blo 1246441 1248063 := bstep (se 1 (by rfl) ⟨936047, by rfl⟩ : syracuseStep 1248063 = 1872095) B1872095
theorem B1248103 : Blo 1246441 1248103 := bstep (se 1 (by rfl) ⟨936077, by rfl⟩ : syracuseStep 1248103 = 1872155) B1872155
theorem B1248127 : Blo 1246441 1248127 := bstep (se 1 (by rfl) ⟨936095, by rfl⟩ : syracuseStep 1248127 = 1872191) B1872191
theorem B1248191 : Blo 1246441 1248191 := bstep (se 1 (by rfl) ⟨936143, by rfl⟩ : syracuseStep 1248191 = 1872287) B1872287
theorem B2845727 : Blo 1246441 2845727 := bstep (se 1 (by rfl) ⟨2134295, by rfl⟩ : syracuseStep 2845727 = 4268591) B4268591
theorem B2805065 : Blo 1246441 2805065 := bstep (se 2 (by rfl) ⟨1051899, by rfl⟩ : syracuseStep 2805065 = 2103799) B2103799
theorem B10112951 : Blo 1246441 10112951 := bstep (se 1 (by rfl) ⟨7584713, by rfl⟩ : syracuseStep 10112951 = 15169427) B15169427
theorem B11382767 : Blo 1246441 11382767 := bstep (se 1 (by rfl) ⟨8537075, by rfl⟩ : syracuseStep 11382767 = 17074151) B17074151
theorem B71921681 : Blo 1246441 71921681 := bstep (se 2 (by rfl) ⟨26970630, by rfl⟩ : syracuseStep 71921681 = 53941261) B53941261
theorem B4558879 : Blo 1246441 4558879 := bstep (se 1 (by rfl) ⟨3419159, by rfl⟩ : syracuseStep 4558879 = 6838319) B6838319
theorem B10653767 : Blo 1246441 10653767 := bstep (se 1 (by rfl) ⟨7990325, by rfl⟩ : syracuseStep 10653767 = 15980651) B15980651
theorem B4206761 : Blo 1246441 4206761 := bstep (se 2 (by rfl) ⟨1577535, by rfl⟩ : syracuseStep 4206761 = 3155071) B3155071
theorem B2806073 : Blo 1246441 2806073 := bstep (se 2 (by rfl) ⟨1052277, by rfl⟩ : syracuseStep 2806073 = 2104555) B2104555
theorem B4739579 : Blo 1246441 4739579 := bstep (se 1 (by rfl) ⟨3554684, by rfl⟩ : syracuseStep 4739579 = 7109369) B7109369
theorem B1897001 : Blo 1246441 1897001 := bstep (se 2 (by rfl) ⟨711375, by rfl⟩ : syracuseStep 1897001 = 1422751) B1422751
theorem B1872539 : Blo 1246441 1872539 := bstep (se 1 (by rfl) ⟨1404404, by rfl⟩ : syracuseStep 1872539 = 2808809) B2808809
theorem B43783163 : Blo 1246441 43783163 := bstep (se 1 (by rfl) ⟨32837372, by rfl⟩ : syracuseStep 43783163 = 65674745) B65674745
theorem B2807351 : Blo 1246441 2807351 := bstep (se 1 (by rfl) ⟨2105513, by rfl⟩ : syracuseStep 2807351 = 4211027) B4211027
theorem B9476513 : Blo 1246441 9476513 := bstep (se 2 (by rfl) ⟨3553692, by rfl⟩ : syracuseStep 9476513 = 7107385) B7107385
theorem B2808575 : Blo 1246441 2808575 := bstep (se 1 (by rfl) ⟨2106431, by rfl⟩ : syracuseStep 2808575 = 4212863) B4212863
theorem B2530055 : Blo 1246441 2530055 := bstep (se 1 (by rfl) ⟨1897541, by rfl⟩ : syracuseStep 2530055 = 3795083) B3795083
theorem B45489599 : Blo 1246441 45489599 := bstep (se 1 (by rfl) ⟨34117199, by rfl⟩ : syracuseStep 45489599 = 68234399) B68234399
theorem B2367215 : Blo 1246441 2367215 := bstep (se 1 (by rfl) ⟨1775411, by rfl⟩ : syracuseStep 2367215 = 3550823) B3550823
theorem B14401327 : Blo 1246441 14401327 := bstep (se 1 (by rfl) ⟨10800995, by rfl⟩ : syracuseStep 14401327 = 21601991) B21601991
theorem B47947787 : Blo 1246441 47947787 := bstep (se 1 (by rfl) ⟨35960840, by rfl⟩ : syracuseStep 47947787 = 71921681) B71921681
theorem B6078505 : Blo 1246441 6078505 := bstep (se 2 (by rfl) ⟨2279439, by rfl⟩ : syracuseStep 6078505 = 4558879) B4558879
theorem B7102511 : Blo 1246441 7102511 := bstep (se 1 (by rfl) ⟨5326883, by rfl⟩ : syracuseStep 7102511 = 10653767) B10653767
theorem B11534443 : Blo 1246441 11534443 := bstep (se 1 (by rfl) ⟨8650832, by rfl⟩ : syracuseStep 11534443 = 17301665) B17301665
theorem B4210811 : Blo 1246441 4210811 := bstep (se 1 (by rfl) ⟨3158108, by rfl⟩ : syracuseStep 4210811 = 6316217) B6316217
theorem B17301995 : Blo 1246441 17301995 := bstep (se 1 (by rfl) ⟨12976496, by rfl⟩ : syracuseStep 17301995 = 25952993) B25952993
theorem B29188775 : Blo 1246441 29188775 := bstep (se 1 (by rfl) ⟨21891581, by rfl⟩ : syracuseStep 29188775 = 43783163) B43783163
theorem B7586951 : Blo 1246441 7586951 := bstep (se 1 (by rfl) ⟨5690213, by rfl⟩ : syracuseStep 7586951 = 11380427) B11380427
theorem B1246623 : Blo 1246441 1246623 := bstep (se 1 (by rfl) ⟨934967, by rfl⟩ : syracuseStep 1246623 = 1869935) B1869935
theorem B6317675 : Blo 1246441 6317675 := bstep (se 1 (by rfl) ⟨4738256, by rfl⟩ : syracuseStep 6317675 = 9476513) B9476513
theorem B1246875 : Blo 1246441 1246875 := bstep (se 1 (by rfl) ⟨935156, by rfl⟩ : syracuseStep 1246875 = 1870313) B1870313
theorem B1870043 : Blo 1246441 1870043 := bstep (se 1 (by rfl) ⟨1402532, by rfl⟩ : syracuseStep 1870043 = 2805065) B2805065
theorem B7588511 : Blo 1246441 7588511 := bstep (se 1 (by rfl) ⟨5691383, by rfl⟩ : syracuseStep 7588511 = 11382767) B11382767
theorem B2804507 : Blo 1246441 2804507 := bstep (se 1 (by rfl) ⟨2103380, by rfl⟩ : syracuseStep 2804507 = 4206761) B4206761
theorem B1870715 : Blo 1246441 1870715 := bstep (se 1 (by rfl) ⟨1403036, by rfl⟩ : syracuseStep 1870715 = 2806073) B2806073
theorem B1264667 : Blo 1246441 1264667 := bstep (se 1 (by rfl) ⟨948500, by rfl⟩ : syracuseStep 1264667 = 1897001) B1897001
theorem B1248359 : Blo 1246441 1248359 := bstep (se 1 (by rfl) ⟨936269, by rfl⟩ : syracuseStep 1248359 = 1872539) B1872539
theorem B1404031 : Blo 1246441 1404031 := bstep (se 1 (by rfl) ⟨1053023, by rfl⟩ : syracuseStep 1404031 = 2106047) B2106047
theorem B8097317 : Blo 1246441 8097317 := bstep (se 4 (by rfl) ⟨759123, by rfl⟩ : syracuseStep 8097317 = 1518247) B1518247
theorem B3550891 : Blo 1246441 3550891 := bstep (se 1 (by rfl) ⟨2663168, by rfl⟩ : syracuseStep 3550891 = 5326337) B5326337
theorem B1871567 : Blo 1246441 1871567 := bstep (se 1 (by rfl) ⟨1403675, by rfl⟩ : syracuseStep 1871567 = 2807351) B2807351
theorem B6319943 : Blo 1246441 6319943 := bstep (se 1 (by rfl) ⟨4739957, by rfl⟩ : syracuseStep 6319943 = 9479915) B9479915
theorem B6074783 : Blo 1246441 6074783 := bstep (se 1 (by rfl) ⟨4556087, by rfl⟩ : syracuseStep 6074783 = 9112175) B9112175
theorem B1872383 : Blo 1246441 1872383 := bstep (se 1 (by rfl) ⟨1404287, by rfl⟩ : syracuseStep 1872383 = 2808575) B2808575
theorem B1897151 : Blo 1246441 1897151 := bstep (se 1 (by rfl) ⟨1422863, by rfl⟩ : syracuseStep 1897151 = 2845727) B2845727
theorem B1578143 : Blo 1246441 1578143 := bstep (se 1 (by rfl) ⟨1183607, by rfl⟩ : syracuseStep 1578143 = 2367215) B2367215
theorem B3159719 : Blo 1246441 3159719 := bstep (se 1 (by rfl) ⟨2369789, by rfl⟩ : syracuseStep 3159719 = 4739579) B4739579
theorem B1775611 : Blo 1246441 1775611 := bstep (se 1 (by rfl) ⟨1331708, by rfl⟩ : syracuseStep 1775611 = 2663417) B2663417
theorem B2103455 : Blo 1246441 2103455 := bstep (se 1 (by rfl) ⟨1577591, by rfl⟩ : syracuseStep 2103455 = 3155183) B3155183
theorem B1775839 : Blo 1246441 1775839 := bstep (se 1 (by rfl) ⟨1331879, by rfl⟩ : syracuseStep 1775839 = 2663759) B2663759
theorem B6740455 : Blo 1246441 6740455 := bstep (se 1 (by rfl) ⟨5055341, by rfl⟩ : syracuseStep 6740455 = 10110683) B10110683
theorem B7199239 : Blo 1246441 7199239 := bstep (se 1 (by rfl) ⟨5399429, by rfl⟩ : syracuseStep 7199239 = 10798859) B10798859
theorem B2808539 : Blo 1246441 2808539 := bstep (se 1 (by rfl) ⟨2106404, by rfl⟩ : syracuseStep 2808539 = 4212809) B4212809
theorem B1686703 : Blo 1246441 1686703 := bstep (se 1 (by rfl) ⟨1265027, by rfl⟩ : syracuseStep 1686703 = 2530055) B2530055
theorem B30326399 : Blo 1246441 30326399 := bstep (se 1 (by rfl) ⟨22744799, by rfl⟩ : syracuseStep 30326399 = 45489599) B45489599
theorem B19201769 : Blo 1246441 19201769 := bstep (se 2 (by rfl) ⟨7200663, by rfl⟩ : syracuseStep 19201769 = 14401327) B14401327
theorem B6741967 : Blo 1246441 6741967 := bstep (se 1 (by rfl) ⟨5056475, by rfl⟩ : syracuseStep 6741967 = 10112951) B10112951
theorem B31965191 : Blo 1246441 31965191 := bstep (se 1 (by rfl) ⟨23973893, by rfl⟩ : syracuseStep 31965191 = 47947787) B47947787
theorem B4735007 : Blo 1246441 4735007 := bstep (se 1 (by rfl) ⟨3551255, by rfl⟩ : syracuseStep 4735007 = 7102511) B7102511
theorem B2367785 : Blo 1246441 2367785 := bstep (se 2 (by rfl) ⟨887919, by rfl⟩ : syracuseStep 2367785 = 1775839) B1775839
theorem B11534663 : Blo 1246441 11534663 := bstep (se 1 (by rfl) ⟨8650997, by rfl⟩ : syracuseStep 11534663 = 17301995) B17301995
theorem B8987273 : Blo 1246441 8987273 := bstep (se 2 (by rfl) ⟨3370227, by rfl⟩ : syracuseStep 8987273 = 6740455) B6740455
theorem B4211783 : Blo 1246441 4211783 := bstep (se 1 (by rfl) ⟨3158837, by rfl⟩ : syracuseStep 4211783 = 6317675) B6317675
theorem B2106479 : Blo 1246441 2106479 := bstep (se 1 (by rfl) ⟨1579859, by rfl⟩ : syracuseStep 2106479 = 3159719) B3159719
theorem B1402303 : Blo 1246441 1402303 := bstep (se 1 (by rfl) ⟨1051727, by rfl⟩ : syracuseStep 1402303 = 2103455) B2103455
theorem B1246695 : Blo 1246441 1246695 := bstep (se 1 (by rfl) ⟨935021, by rfl⟩ : syracuseStep 1246695 = 1870043) B1870043
theorem B1869671 : Blo 1246441 1869671 := bstep (se 1 (by rfl) ⟨1402253, by rfl⟩ : syracuseStep 1869671 = 2804507) B2804507
theorem B1247143 : Blo 1246441 1247143 := bstep (se 1 (by rfl) ⟨935357, by rfl⟩ : syracuseStep 1247143 = 1870715) B1870715
theorem B20236277 : Blo 1246441 20236277 := bstep (se 5 (by rfl) ⟨948575, by rfl⟩ : syracuseStep 20236277 = 1897151) B1897151
theorem B1247711 : Blo 1246441 1247711 := bstep (se 1 (by rfl) ⟨935783, by rfl⟩ : syracuseStep 1247711 = 1871567) B1871567
theorem B4213295 : Blo 1246441 4213295 := bstep (se 1 (by rfl) ⟨3159971, by rfl⟩ : syracuseStep 4213295 = 6319943) B6319943
theorem B8989289 : Blo 1246441 8989289 := bstep (se 2 (by rfl) ⟨3370983, by rfl⟩ : syracuseStep 8989289 = 6741967) B6741967
theorem B8104673 : Blo 1246441 8104673 := bstep (se 2 (by rfl) ⟨3039252, by rfl⟩ : syracuseStep 8104673 = 6078505) B6078505
theorem B4049855 : Blo 1246441 4049855 := bstep (se 1 (by rfl) ⟨3037391, by rfl⟩ : syracuseStep 4049855 = 6074783) B6074783
theorem B1248255 : Blo 1246441 1248255 := bstep (se 1 (by rfl) ⟨936191, by rfl⟩ : syracuseStep 1248255 = 1872383) B1872383
theorem B19459183 : Blo 1246441 19459183 := bstep (se 1 (by rfl) ⟨14594387, by rfl⟩ : syracuseStep 19459183 = 29188775) B29188775
theorem B61517029 : Blo 1246441 61517029 := bstep (se 4 (by rfl) ⟨5767221, by rfl⟩ : syracuseStep 61517029 = 11534443) B11534443
theorem B1872041 : Blo 1246441 1872041 := bstep (se 2 (by rfl) ⟨702015, by rfl⟩ : syracuseStep 1872041 = 1404031) B1404031
theorem B2248937 : Blo 1246441 2248937 := bstep (se 2 (by rfl) ⟨843351, by rfl⟩ : syracuseStep 2248937 = 1686703) B1686703
theorem B5059007 : Blo 1246441 5059007 := bstep (se 1 (by rfl) ⟨3794255, by rfl⟩ : syracuseStep 5059007 = 7588511) B7588511
theorem B1872359 : Blo 1246441 1872359 := bstep (se 1 (by rfl) ⟨1404269, by rfl⟩ : syracuseStep 1872359 = 2808539) B2808539
theorem B12801179 : Blo 1246441 12801179 := bstep (se 1 (by rfl) ⟨9600884, by rfl⟩ : syracuseStep 12801179 = 19201769) B19201769
theorem B3372445 : Blo 1246441 3372445 := bstep (se 3 (by rfl) ⟨632333, by rfl⟩ : syracuseStep 3372445 = 1264667) B1264667
theorem B2807207 : Blo 1246441 2807207 := bstep (se 1 (by rfl) ⟨2105405, by rfl⟩ : syracuseStep 2807207 = 4210811) B4210811
theorem B20231869 : Blo 1246441 20231869 := bstep (se 3 (by rfl) ⟨3793475, by rfl⟩ : syracuseStep 20231869 = 7586951) B7586951
theorem B4208381 : Blo 1246441 4208381 := bstep (se 3 (by rfl) ⟨789071, by rfl⟩ : syracuseStep 4208381 = 1578143) B1578143
theorem B9598985 : Blo 1246441 9598985 := bstep (se 2 (by rfl) ⟨3599619, by rfl⟩ : syracuseStep 9598985 = 7199239) B7199239
theorem B4734521 : Blo 1246441 4734521 := bstep (se 2 (by rfl) ⟨1775445, by rfl⟩ : syracuseStep 4734521 = 3550891) B3550891
theorem B5398211 : Blo 1246441 5398211 := bstep (se 1 (by rfl) ⟨4048658, by rfl⟩ : syracuseStep 5398211 = 8097317) B8097317
theorem B20217599 : Blo 1246441 20217599 := bstep (se 1 (by rfl) ⟨15163199, by rfl⟩ : syracuseStep 20217599 = 30326399) B30326399
theorem B2367481 : Blo 1246441 2367481 := bstep (se 2 (by rfl) ⟨887805, by rfl⟩ : syracuseStep 2367481 = 1775611) B1775611
theorem B1499291 : Blo 1246441 1499291 := bstep (se 1 (by rfl) ⟨1124468, by rfl⟩ : syracuseStep 1499291 = 2248937) B2248937
theorem B1246447 : Blo 1246441 1246447 := bstep (se 1 (by rfl) ⟨934835, by rfl⟩ : syracuseStep 1246447 = 1869671) B1869671
theorem B6399323 : Blo 1246441 6399323 := bstep (se 1 (by rfl) ⟨4799492, by rfl⟩ : syracuseStep 6399323 = 9598985) B9598985
theorem B25945577 : Blo 1246441 25945577 := bstep (se 2 (by rfl) ⟨9729591, by rfl⟩ : syracuseStep 25945577 = 19459183) B19459183
theorem B1869737 : Blo 1246441 1869737 := bstep (se 2 (by rfl) ⟨701151, by rfl⟩ : syracuseStep 1869737 = 1402303) B1402303
theorem B3156347 : Blo 1246441 3156347 := bstep (se 1 (by rfl) ⟨2367260, by rfl⟩ : syracuseStep 3156347 = 4734521) B4734521
theorem B3598807 : Blo 1246441 3598807 := bstep (se 1 (by rfl) ⟨2699105, by rfl⟩ : syracuseStep 3598807 = 5398211) B5398211
theorem B13478399 : Blo 1246441 13478399 := bstep (se 1 (by rfl) ⟨10108799, by rfl⟩ : syracuseStep 13478399 = 20217599) B20217599
theorem B53963405 : Blo 1246441 53963405 := bstep (se 3 (by rfl) ⟨10118138, by rfl⟩ : syracuseStep 53963405 = 20236277) B20236277
theorem B3156641 : Blo 1246441 3156641 := bstep (se 2 (by rfl) ⟨1183740, by rfl⟩ : syracuseStep 3156641 = 2367481) B2367481
theorem B21310127 : Blo 1246441 21310127 := bstep (se 1 (by rfl) ⟨15982595, by rfl⟩ : syracuseStep 21310127 = 31965191) B31965191
theorem B3156671 : Blo 1246441 3156671 := bstep (se 1 (by rfl) ⟨2367503, by rfl⟩ : syracuseStep 3156671 = 4735007) B4735007
theorem B1248027 : Blo 1246441 1248027 := bstep (se 1 (by rfl) ⟨936020, by rfl⟩ : syracuseStep 1248027 = 1872041) B1872041
theorem B1248239 : Blo 1246441 1248239 := bstep (se 1 (by rfl) ⟨936179, by rfl⟩ : syracuseStep 1248239 = 1872359) B1872359
theorem B5991515 : Blo 1246441 5991515 := bstep (se 1 (by rfl) ⟨4493636, by rfl⟩ : syracuseStep 5991515 = 8987273) B8987273
theorem B1404319 : Blo 1246441 1404319 := bstep (se 1 (by rfl) ⟨1053239, by rfl⟩ : syracuseStep 1404319 = 2106479) B2106479
theorem B1871471 : Blo 1246441 1871471 := bstep (se 1 (by rfl) ⟨1403603, by rfl⟩ : syracuseStep 1871471 = 2807207) B2807207
theorem B2805587 : Blo 1246441 2805587 := bstep (se 1 (by rfl) ⟨2104190, by rfl⟩ : syracuseStep 2805587 = 4208381) B4208381
theorem B82022705 : Blo 1246441 82022705 := bstep (se 2 (by rfl) ⟨30758514, by rfl⟩ : syracuseStep 82022705 = 61517029) B61517029
theorem B5992859 : Blo 1246441 5992859 := bstep (se 1 (by rfl) ⟨4494644, by rfl⟩ : syracuseStep 5992859 = 8989289) B8989289
theorem B5403115 : Blo 1246441 5403115 := bstep (se 1 (by rfl) ⟨4052336, by rfl⟩ : syracuseStep 5403115 = 8104673) B8104673
theorem B2699903 : Blo 1246441 2699903 := bstep (se 1 (by rfl) ⟨2024927, by rfl⟩ : syracuseStep 2699903 = 4049855) B4049855
theorem B1578523 : Blo 1246441 1578523 := bstep (se 1 (by rfl) ⟨1183892, by rfl⟩ : syracuseStep 1578523 = 2367785) B2367785
theorem B7689775 : Blo 1246441 7689775 := bstep (se 1 (by rfl) ⟨5767331, by rfl⟩ : syracuseStep 7689775 = 11534663) B11534663
theorem B3372671 : Blo 1246441 3372671 := bstep (se 1 (by rfl) ⟨2529503, by rfl⟩ : syracuseStep 3372671 = 5059007) B5059007
theorem B2807855 : Blo 1246441 2807855 := bstep (se 1 (by rfl) ⟨2105891, by rfl⟩ : syracuseStep 2807855 = 4211783) B4211783
theorem B8534119 : Blo 1246441 8534119 := bstep (se 1 (by rfl) ⟨6400589, by rfl⟩ : syracuseStep 8534119 = 12801179) B12801179
theorem B2808863 : Blo 1246441 2808863 := bstep (se 1 (by rfl) ⟨2106647, by rfl⟩ : syracuseStep 2808863 = 4213295) B4213295
theorem B4496593 : Blo 1246441 4496593 := bstep (se 2 (by rfl) ⟨1686222, by rfl⟩ : syracuseStep 4496593 = 3372445) B3372445
theorem B26975825 : Blo 1246441 26975825 := bstep (se 2 (by rfl) ⟨10115934, by rfl⟩ : syracuseStep 26975825 = 20231869) B20231869
theorem B11378825 : Blo 1246441 11378825 := bstep (se 2 (by rfl) ⟨4267059, by rfl⟩ : syracuseStep 11378825 = 8534119) B8534119
theorem B54681803 : Blo 1246441 54681803 := bstep (se 1 (by rfl) ⟨41011352, by rfl⟩ : syracuseStep 54681803 = 82022705) B82022705
theorem B1246491 : Blo 1246441 1246491 := bstep (se 1 (by rfl) ⟨934868, by rfl⟩ : syracuseStep 1246491 = 1869737) B1869737
theorem B15992437 : Blo 1246441 15992437 := bstep (se 5 (by rfl) ⟨749645, by rfl⟩ : syracuseStep 15992437 = 1499291) B1499291
theorem B14206751 : Blo 1246441 14206751 := bstep (se 1 (by rfl) ⟨10655063, by rfl⟩ : syracuseStep 14206751 = 21310127) B21310127
theorem B17983883 : Blo 1246441 17983883 := bstep (se 1 (by rfl) ⟨13487912, by rfl⟩ : syracuseStep 17983883 = 26975825) B26975825
theorem B1247647 : Blo 1246441 1247647 := bstep (se 1 (by rfl) ⟨935735, by rfl⟩ : syracuseStep 1247647 = 1871471) B1871471
theorem B276752821 : Blo 1246441 276752821 := bstep (se 5 (by rfl) ⟨12972788, by rfl⟩ : syracuseStep 276752821 = 25945577) B25945577
theorem B1870391 : Blo 1246441 1870391 := bstep (se 1 (by rfl) ⟨1402793, by rfl⟩ : syracuseStep 1870391 = 2805587) B2805587
theorem B7204153 : Blo 1246441 7204153 := bstep (se 2 (by rfl) ⟨2701557, by rfl⟩ : syracuseStep 7204153 = 5403115) B5403115
theorem B2248447 : Blo 1246441 2248447 := bstep (se 1 (by rfl) ⟨1686335, by rfl⟩ : syracuseStep 2248447 = 3372671) B3372671
theorem B1871903 : Blo 1246441 1871903 := bstep (se 1 (by rfl) ⟨1403927, by rfl⟩ : syracuseStep 1871903 = 2807855) B2807855
theorem B35975603 : Blo 1246441 35975603 := bstep (se 1 (by rfl) ⟨26981702, by rfl⟩ : syracuseStep 35975603 = 53963405) B53963405
theorem B1872425 : Blo 1246441 1872425 := bstep (se 2 (by rfl) ⟨702159, by rfl⟩ : syracuseStep 1872425 = 1404319) B1404319
theorem B1872575 : Blo 1246441 1872575 := bstep (se 1 (by rfl) ⟨1404431, by rfl⟩ : syracuseStep 1872575 = 2808863) B2808863
theorem B3994343 : Blo 1246441 3994343 := bstep (se 1 (by rfl) ⟨2995757, by rfl⟩ : syracuseStep 3994343 = 5991515) B5991515
theorem B10253033 : Blo 1246441 10253033 := bstep (se 2 (by rfl) ⟨3844887, by rfl⟩ : syracuseStep 10253033 = 7689775) B7689775
theorem B3995239 : Blo 1246441 3995239 := bstep (se 1 (by rfl) ⟨2996429, by rfl⟩ : syracuseStep 3995239 = 5992859) B5992859
theorem B4798409 : Blo 1246441 4798409 := bstep (se 2 (by rfl) ⟨1799403, by rfl⟩ : syracuseStep 4798409 = 3598807) B3598807
theorem B4266215 : Blo 1246441 4266215 := bstep (se 1 (by rfl) ⟨3199661, by rfl⟩ : syracuseStep 4266215 = 6399323) B6399323
theorem B2104231 : Blo 1246441 2104231 := bstep (se 1 (by rfl) ⟨1578173, by rfl⟩ : syracuseStep 2104231 = 3156347) B3156347
theorem B5995457 : Blo 1246441 5995457 := bstep (se 2 (by rfl) ⟨2248296, by rfl⟩ : syracuseStep 5995457 = 4496593) B4496593
theorem B7199741 : Blo 1246441 7199741 := bstep (se 3 (by rfl) ⟨1349951, by rfl⟩ : syracuseStep 7199741 = 2699903) B2699903
theorem B8985599 : Blo 1246441 8985599 := bstep (se 1 (by rfl) ⟨6739199, by rfl⟩ : syracuseStep 8985599 = 13478399) B13478399
theorem B2104427 : Blo 1246441 2104427 := bstep (se 1 (by rfl) ⟨1578320, by rfl⟩ : syracuseStep 2104427 = 3156641) B3156641
theorem B2104447 : Blo 1246441 2104447 := bstep (se 1 (by rfl) ⟨1578335, by rfl⟩ : syracuseStep 2104447 = 3156671) B3156671
theorem B2104697 : Blo 1246441 2104697 := bstep (se 2 (by rfl) ⟨789261, by rfl⟩ : syracuseStep 2104697 = 1578523) B1578523
theorem B7585883 : Blo 1246441 7585883 := bstep (se 1 (by rfl) ⟨5689412, by rfl⟩ : syracuseStep 7585883 = 11378825) B11378825
theorem B36454535 : Blo 1246441 36454535 := bstep (se 1 (by rfl) ⟨27340901, by rfl⟩ : syracuseStep 36454535 = 54681803) B54681803
theorem B2662895 : Blo 1246441 2662895 := bstep (se 1 (by rfl) ⟨1997171, by rfl⟩ : syracuseStep 2662895 = 3994343) B3994343
theorem B9471167 : Blo 1246441 9471167 := bstep (se 1 (by rfl) ⟨7103375, by rfl⟩ : syracuseStep 9471167 = 14206751) B14206751
theorem B2844143 : Blo 1246441 2844143 := bstep (se 1 (by rfl) ⟨2133107, by rfl⟩ : syracuseStep 2844143 = 4266215) B4266215
theorem B1246927 : Blo 1246441 1246927 := bstep (se 1 (by rfl) ⟨935195, by rfl⟩ : syracuseStep 1246927 = 1870391) B1870391
theorem B5990399 : Blo 1246441 5990399 := bstep (se 1 (by rfl) ⟨4492799, by rfl⟩ : syracuseStep 5990399 = 8985599) B8985599
theorem B1402951 : Blo 1246441 1402951 := bstep (se 1 (by rfl) ⟨1052213, by rfl⟩ : syracuseStep 1402951 = 2104427) B2104427
theorem B5326985 : Blo 1246441 5326985 := bstep (se 2 (by rfl) ⟨1997619, by rfl⟩ : syracuseStep 5326985 = 3995239) B3995239
theorem B1403131 : Blo 1246441 1403131 := bstep (se 1 (by rfl) ⟨1052348, by rfl⟩ : syracuseStep 1403131 = 2104697) B2104697
theorem B1247935 : Blo 1246441 1247935 := bstep (se 1 (by rfl) ⟨935951, by rfl⟩ : syracuseStep 1247935 = 1871903) B1871903
theorem B1248283 : Blo 1246441 1248283 := bstep (se 1 (by rfl) ⟨936212, by rfl⟩ : syracuseStep 1248283 = 1872425) B1872425
theorem B1248383 : Blo 1246441 1248383 := bstep (se 1 (by rfl) ⟨936287, by rfl⟩ : syracuseStep 1248383 = 1872575) B1872575
theorem B6835355 : Blo 1246441 6835355 := bstep (se 1 (by rfl) ⟨5126516, by rfl⟩ : syracuseStep 6835355 = 10253033) B10253033
theorem B369003761 : Blo 1246441 369003761 := bstep (se 2 (by rfl) ⟨138376410, by rfl⟩ : syracuseStep 369003761 = 276752821) B276752821
theorem B2805641 : Blo 1246441 2805641 := bstep (se 2 (by rfl) ⟨1052115, by rfl⟩ : syracuseStep 2805641 = 2104231) B2104231
theorem B2805929 : Blo 1246441 2805929 := bstep (se 2 (by rfl) ⟨1052223, by rfl⟩ : syracuseStep 2805929 = 2104447) B2104447
theorem B11989255 : Blo 1246441 11989255 := bstep (se 1 (by rfl) ⟨8991941, by rfl⟩ : syracuseStep 11989255 = 17983883) B17983883
theorem B9605537 : Blo 1246441 9605537 := bstep (se 2 (by rfl) ⟨3602076, by rfl⟩ : syracuseStep 9605537 = 7204153) B7204153
theorem B23983735 : Blo 1246441 23983735 := bstep (se 1 (by rfl) ⟨17987801, by rfl⟩ : syracuseStep 23983735 = 35975603) B35975603
theorem B3996971 : Blo 1246441 3996971 := bstep (se 1 (by rfl) ⟨2997728, by rfl⟩ : syracuseStep 3996971 = 5995457) B5995457
theorem B4799827 : Blo 1246441 4799827 := bstep (se 1 (by rfl) ⟨3599870, by rfl⟩ : syracuseStep 4799827 = 7199741) B7199741
theorem B51183029 : Blo 1246441 51183029 := bstep (se 5 (by rfl) ⟨2399204, by rfl⟩ : syracuseStep 51183029 = 4798409) B4798409
theorem B21323249 : Blo 1246441 21323249 := bstep (se 2 (by rfl) ⟨7996218, by rfl⟩ : syracuseStep 21323249 = 15992437) B15992437
theorem B2997929 : Blo 1246441 2997929 := bstep (se 2 (by rfl) ⟨1124223, by rfl⟩ : syracuseStep 2997929 = 2248447) B2248447
theorem B14205293 : Blo 1246441 14205293 := bstep (se 3 (by rfl) ⟨2663492, by rfl⟩ : syracuseStep 14205293 = 5326985) B5326985
theorem B4556903 : Blo 1246441 4556903 := bstep (se 1 (by rfl) ⟨3417677, by rfl⟩ : syracuseStep 4556903 = 6835355) B6835355
theorem B2664647 : Blo 1246441 2664647 := bstep (se 1 (by rfl) ⟨1998485, by rfl⟩ : syracuseStep 2664647 = 3996971) B3996971
theorem B34122019 : Blo 1246441 34122019 := bstep (se 1 (by rfl) ⟨25591514, by rfl⟩ : syracuseStep 34122019 = 51183029) B51183029
theorem B14215499 : Blo 1246441 14215499 := bstep (se 1 (by rfl) ⟨10661624, by rfl⟩ : syracuseStep 14215499 = 21323249) B21323249
theorem B1870427 : Blo 1246441 1870427 := bstep (se 1 (by rfl) ⟨1402820, by rfl⟩ : syracuseStep 1870427 = 2805641) B2805641
theorem B5057255 : Blo 1246441 5057255 := bstep (se 1 (by rfl) ⟨3792941, by rfl⟩ : syracuseStep 5057255 = 7585883) B7585883
theorem B1870601 : Blo 1246441 1870601 := bstep (se 2 (by rfl) ⟨701475, by rfl⟩ : syracuseStep 1870601 = 1402951) B1402951
theorem B1870619 : Blo 1246441 1870619 := bstep (se 1 (by rfl) ⟨1402964, by rfl⟩ : syracuseStep 1870619 = 2805929) B2805929
theorem B1870841 : Blo 1246441 1870841 := bstep (se 2 (by rfl) ⟨701565, by rfl⟩ : syracuseStep 1870841 = 1403131) B1403131
theorem B15985673 : Blo 1246441 15985673 := bstep (se 2 (by rfl) ⟨5994627, by rfl⟩ : syracuseStep 15985673 = 11989255) B11989255
theorem B1896095 : Blo 1246441 1896095 := bstep (se 1 (by rfl) ⟨1422071, by rfl⟩ : syracuseStep 1896095 = 2844143) B2844143
theorem B3993599 : Blo 1246441 3993599 := bstep (se 1 (by rfl) ⟨2995199, by rfl⟩ : syracuseStep 3993599 = 5990399) B5990399
theorem B31978313 : Blo 1246441 31978313 := bstep (se 2 (by rfl) ⟨11991867, by rfl⟩ : syracuseStep 31978313 = 23983735) B23983735
theorem B246002507 : Blo 1246441 246002507 := bstep (se 1 (by rfl) ⟨184501880, by rfl⟩ : syracuseStep 246002507 = 369003761) B369003761
theorem B24303023 : Blo 1246441 24303023 := bstep (se 1 (by rfl) ⟨18227267, by rfl⟩ : syracuseStep 24303023 = 36454535) B36454535
theorem B6403691 : Blo 1246441 6403691 := bstep (se 1 (by rfl) ⟨4802768, by rfl⟩ : syracuseStep 6403691 = 9605537) B9605537
theorem B6314111 : Blo 1246441 6314111 := bstep (se 1 (by rfl) ⟨4735583, by rfl⟩ : syracuseStep 6314111 = 9471167) B9471167
theorem B7101053 : Blo 1246441 7101053 := bstep (se 3 (by rfl) ⟨1331447, by rfl⟩ : syracuseStep 7101053 = 2662895) B2662895
theorem B25599077 : Blo 1246441 25599077 := bstep (se 4 (by rfl) ⟨2399913, by rfl⟩ : syracuseStep 25599077 = 4799827) B4799827
theorem B7994477 : Blo 1246441 7994477 := bstep (se 3 (by rfl) ⟨1498964, by rfl⟩ : syracuseStep 7994477 = 2997929) B2997929
theorem B9470195 : Blo 1246441 9470195 := bstep (se 1 (by rfl) ⟨7102646, by rfl⟩ : syracuseStep 9470195 = 14205293) B14205293
theorem B4269127 : Blo 1246441 4269127 := bstep (se 1 (by rfl) ⟨3201845, by rfl⟩ : syracuseStep 4269127 = 6403691) B6403691
theorem B1246951 : Blo 1246441 1246951 := bstep (se 1 (by rfl) ⟨935213, by rfl⟩ : syracuseStep 1246951 = 1870427) B1870427
theorem B5056253 : Blo 1246441 5056253 := bstep (se 3 (by rfl) ⟨948047, by rfl⟩ : syracuseStep 5056253 = 1896095) B1896095
theorem B1247067 : Blo 1246441 1247067 := bstep (se 1 (by rfl) ⟨935300, by rfl⟩ : syracuseStep 1247067 = 1870601) B1870601
theorem B1247079 : Blo 1246441 1247079 := bstep (se 1 (by rfl) ⟨935309, by rfl⟩ : syracuseStep 1247079 = 1870619) B1870619
theorem B13486013 : Blo 1246441 13486013 := bstep (se 3 (by rfl) ⟨2528627, by rfl⟩ : syracuseStep 13486013 = 5057255) B5057255
theorem B1247227 : Blo 1246441 1247227 := bstep (se 1 (by rfl) ⟨935420, by rfl⟩ : syracuseStep 1247227 = 1870841) B1870841
theorem B17066051 : Blo 1246441 17066051 := bstep (se 1 (by rfl) ⟨12799538, by rfl⟩ : syracuseStep 17066051 = 25599077) B25599077
theorem B21318875 : Blo 1246441 21318875 := bstep (se 1 (by rfl) ⟨15989156, by rfl⟩ : syracuseStep 21318875 = 31978313) B31978313
theorem B48606965 : Blo 1246441 48606965 := bstep (se 5 (by rfl) ⟨2278451, by rfl⟩ : syracuseStep 48606965 = 4556903) B4556903
theorem B5329651 : Blo 1246441 5329651 := bstep (se 1 (by rfl) ⟨3997238, by rfl⟩ : syracuseStep 5329651 = 7994477) B7994477
theorem B45496025 : Blo 1246441 45496025 := bstep (se 2 (by rfl) ⟨17061009, by rfl⟩ : syracuseStep 45496025 = 34122019) B34122019
theorem B164001671 : Blo 1246441 164001671 := bstep (se 1 (by rfl) ⟨123001253, by rfl⟩ : syracuseStep 164001671 = 246002507) B246002507
theorem B16202015 : Blo 1246441 16202015 := bstep (se 1 (by rfl) ⟨12151511, by rfl⟩ : syracuseStep 16202015 = 24303023) B24303023
theorem B4209407 : Blo 1246441 4209407 := bstep (se 1 (by rfl) ⟨3157055, by rfl⟩ : syracuseStep 4209407 = 6314111) B6314111
theorem B1776431 : Blo 1246441 1776431 := bstep (se 1 (by rfl) ⟨1332323, by rfl⟩ : syracuseStep 1776431 = 2664647) B2664647
theorem B9476999 : Blo 1246441 9476999 := bstep (se 1 (by rfl) ⟨7107749, by rfl⟩ : syracuseStep 9476999 = 14215499) B14215499
theorem B4734035 : Blo 1246441 4734035 := bstep (se 1 (by rfl) ⟨3550526, by rfl⟩ : syracuseStep 4734035 = 7101053) B7101053
theorem B10657115 : Blo 1246441 10657115 := bstep (se 1 (by rfl) ⟨7992836, by rfl⟩ : syracuseStep 10657115 = 15985673) B15985673
theorem B2662399 : Blo 1246441 2662399 := bstep (se 1 (by rfl) ⟨1996799, by rfl⟩ : syracuseStep 2662399 = 3993599) B3993599
theorem B6317999 : Blo 1246441 6317999 := bstep (se 1 (by rfl) ⟨4738499, by rfl⟩ : syracuseStep 6317999 = 9476999) B9476999
theorem B3156023 : Blo 1246441 3156023 := bstep (se 1 (by rfl) ⟨2367017, by rfl⟩ : syracuseStep 3156023 = 4734035) B4734035
theorem B4737149 : Blo 1246441 4737149 := bstep (se 3 (by rfl) ⟨888215, by rfl⟩ : syracuseStep 4737149 = 1776431) B1776431
theorem B7104743 : Blo 1246441 7104743 := bstep (se 1 (by rfl) ⟨5328557, by rfl⟩ : syracuseStep 7104743 = 10657115) B10657115
theorem B14199461 : Blo 1246441 14199461 := bstep (se 4 (by rfl) ⟨1331199, by rfl⟩ : syracuseStep 14199461 = 2662399) B2662399
theorem B7106201 : Blo 1246441 7106201 := bstep (se 2 (by rfl) ⟨2664825, by rfl⟩ : syracuseStep 7106201 = 5329651) B5329651
theorem B30330683 : Blo 1246441 30330683 := bstep (se 1 (by rfl) ⟨22748012, by rfl⟩ : syracuseStep 30330683 = 45496025) B45496025
theorem B3370835 : Blo 1246441 3370835 := bstep (se 1 (by rfl) ⟨2528126, by rfl⟩ : syracuseStep 3370835 = 5056253) B5056253
theorem B109334447 : Blo 1246441 109334447 := bstep (se 1 (by rfl) ⟨82000835, by rfl⟩ : syracuseStep 109334447 = 164001671) B164001671
theorem B8990675 : Blo 1246441 8990675 := bstep (se 1 (by rfl) ⟨6743006, by rfl⟩ : syracuseStep 8990675 = 13486013) B13486013
theorem B10801343 : Blo 1246441 10801343 := bstep (se 1 (by rfl) ⟨8101007, by rfl⟩ : syracuseStep 10801343 = 16202015) B16202015
theorem B2806271 : Blo 1246441 2806271 := bstep (se 1 (by rfl) ⟨2104703, by rfl⟩ : syracuseStep 2806271 = 4209407) B4209407
theorem B32404643 : Blo 1246441 32404643 := bstep (se 1 (by rfl) ⟨24303482, by rfl⟩ : syracuseStep 32404643 = 48606965) B48606965
theorem B6313463 : Blo 1246441 6313463 := bstep (se 1 (by rfl) ⟨4735097, by rfl⟩ : syracuseStep 6313463 = 9470195) B9470195
theorem B11377367 : Blo 1246441 11377367 := bstep (se 1 (by rfl) ⟨8533025, by rfl⟩ : syracuseStep 11377367 = 17066051) B17066051
theorem B5692169 : Blo 1246441 5692169 := bstep (se 2 (by rfl) ⟨2134563, by rfl⟩ : syracuseStep 5692169 = 4269127) B4269127
theorem B14212583 : Blo 1246441 14212583 := bstep (se 1 (by rfl) ⟨10659437, by rfl⟩ : syracuseStep 14212583 = 21318875) B21318875
theorem B7200895 : Blo 1246441 7200895 := bstep (se 1 (by rfl) ⟨5400671, by rfl⟩ : syracuseStep 7200895 = 10801343) B10801343
theorem B21603095 : Blo 1246441 21603095 := bstep (se 1 (by rfl) ⟨16202321, by rfl⟩ : syracuseStep 21603095 = 32404643) B32404643
theorem B4211999 : Blo 1246441 4211999 := bstep (se 1 (by rfl) ⟨3158999, by rfl⟩ : syracuseStep 4211999 = 6317999) B6317999
theorem B4736495 : Blo 1246441 4736495 := bstep (se 1 (by rfl) ⟨3552371, by rfl⟩ : syracuseStep 4736495 = 7104743) B7104743
theorem B3794779 : Blo 1246441 3794779 := bstep (se 1 (by rfl) ⟨2846084, by rfl⟩ : syracuseStep 3794779 = 5692169) B5692169
theorem B4737467 : Blo 1246441 4737467 := bstep (se 1 (by rfl) ⟨3553100, by rfl⟩ : syracuseStep 4737467 = 7106201) B7106201
theorem B20220455 : Blo 1246441 20220455 := bstep (se 1 (by rfl) ⟨15165341, by rfl⟩ : syracuseStep 20220455 = 30330683) B30330683
theorem B2247223 : Blo 1246441 2247223 := bstep (se 1 (by rfl) ⟨1685417, by rfl⟩ : syracuseStep 2247223 = 3370835) B3370835
theorem B1870847 : Blo 1246441 1870847 := bstep (se 1 (by rfl) ⟨1403135, by rfl⟩ : syracuseStep 1870847 = 2806271) B2806271
theorem B3158099 : Blo 1246441 3158099 := bstep (se 1 (by rfl) ⟨2368574, by rfl⟩ : syracuseStep 3158099 = 4737149) B4737149
theorem B9466307 : Blo 1246441 9466307 := bstep (se 1 (by rfl) ⟨7099730, by rfl⟩ : syracuseStep 9466307 = 14199461) B14199461
theorem B9475055 : Blo 1246441 9475055 := bstep (se 1 (by rfl) ⟨7106291, by rfl⟩ : syracuseStep 9475055 = 14212583) B14212583
theorem B72889631 : Blo 1246441 72889631 := bstep (se 1 (by rfl) ⟨54667223, by rfl⟩ : syracuseStep 72889631 = 109334447) B109334447
theorem B5993783 : Blo 1246441 5993783 := bstep (se 1 (by rfl) ⟨4495337, by rfl⟩ : syracuseStep 5993783 = 8990675) B8990675
theorem B4208975 : Blo 1246441 4208975 := bstep (se 1 (by rfl) ⟨3156731, by rfl⟩ : syracuseStep 4208975 = 6313463) B6313463
theorem B2104015 : Blo 1246441 2104015 := bstep (se 1 (by rfl) ⟨1578011, by rfl⟩ : syracuseStep 2104015 = 3156023) B3156023
theorem B7584911 : Blo 1246441 7584911 := bstep (se 1 (by rfl) ⟨5688683, by rfl⟩ : syracuseStep 7584911 = 11377367) B11377367
theorem B2105399 : Blo 1246441 2105399 := bstep (se 1 (by rfl) ⟨1579049, by rfl⟩ : syracuseStep 2105399 = 3158099) B3158099
theorem B9601193 : Blo 1246441 9601193 := bstep (se 2 (by rfl) ⟨3600447, by rfl⟩ : syracuseStep 9601193 = 7200895) B7200895
theorem B14402063 : Blo 1246441 14402063 := bstep (se 1 (by rfl) ⟨10801547, by rfl⟩ : syracuseStep 14402063 = 21603095) B21603095
theorem B6316703 : Blo 1246441 6316703 := bstep (se 1 (by rfl) ⟨4737527, by rfl⟩ : syracuseStep 6316703 = 9475055) B9475055
theorem B1247231 : Blo 1246441 1247231 := bstep (se 1 (by rfl) ⟨935423, by rfl⟩ : syracuseStep 1247231 = 1870847) B1870847
theorem B5056607 : Blo 1246441 5056607 := bstep (se 1 (by rfl) ⟨3792455, by rfl⟩ : syracuseStep 5056607 = 7584911) B7584911
theorem B6310871 : Blo 1246441 6310871 := bstep (se 1 (by rfl) ⟨4733153, by rfl⟩ : syracuseStep 6310871 = 9466307) B9466307
theorem B2805353 : Blo 1246441 2805353 := bstep (se 2 (by rfl) ⟨1052007, by rfl⟩ : syracuseStep 2805353 = 2104015) B2104015
theorem B3157663 : Blo 1246441 3157663 := bstep (se 1 (by rfl) ⟨2368247, by rfl⟩ : syracuseStep 3157663 = 4736495) B4736495
theorem B2805983 : Blo 1246441 2805983 := bstep (se 1 (by rfl) ⟨2104487, by rfl⟩ : syracuseStep 2805983 = 4208975) B4208975
theorem B3158311 : Blo 1246441 3158311 := bstep (se 1 (by rfl) ⟨2368733, by rfl⟩ : syracuseStep 3158311 = 4737467) B4737467
theorem B13480303 : Blo 1246441 13480303 := bstep (se 1 (by rfl) ⟨10110227, by rfl⟩ : syracuseStep 13480303 = 20220455) B20220455
theorem B5059705 : Blo 1246441 5059705 := bstep (se 2 (by rfl) ⟨1897389, by rfl⟩ : syracuseStep 5059705 = 3794779) B3794779
theorem B2996297 : Blo 1246441 2996297 := bstep (se 2 (by rfl) ⟨1123611, by rfl⟩ : syracuseStep 2996297 = 2247223) B2247223
theorem B48593087 : Blo 1246441 48593087 := bstep (se 1 (by rfl) ⟨36444815, by rfl⟩ : syracuseStep 48593087 = 72889631) B72889631
theorem B2807999 : Blo 1246441 2807999 := bstep (se 1 (by rfl) ⟨2105999, by rfl⟩ : syracuseStep 2807999 = 4211999) B4211999
theorem B3995855 : Blo 1246441 3995855 := bstep (se 1 (by rfl) ⟨2996891, by rfl⟩ : syracuseStep 3995855 = 5993783) B5993783
theorem B9601375 : Blo 1246441 9601375 := bstep (se 1 (by rfl) ⟨7201031, by rfl⟩ : syracuseStep 9601375 = 14402063) B14402063
theorem B4211081 : Blo 1246441 4211081 := bstep (se 2 (by rfl) ⟨1579155, by rfl⟩ : syracuseStep 4211081 = 3158311) B3158311
theorem B4211135 : Blo 1246441 4211135 := bstep (se 1 (by rfl) ⟨3158351, by rfl⟩ : syracuseStep 4211135 = 6316703) B6316703
theorem B17973737 : Blo 1246441 17973737 := bstep (se 2 (by rfl) ⟨6740151, by rfl⟩ : syracuseStep 17973737 = 13480303) B13480303
theorem B2663903 : Blo 1246441 2663903 := bstep (se 1 (by rfl) ⟨1997927, by rfl⟩ : syracuseStep 2663903 = 3995855) B3995855
theorem B1870235 : Blo 1246441 1870235 := bstep (se 1 (by rfl) ⟨1402676, by rfl⟩ : syracuseStep 1870235 = 2805353) B2805353
theorem B1403599 : Blo 1246441 1403599 := bstep (se 1 (by rfl) ⟨1052699, by rfl⟩ : syracuseStep 1403599 = 2105399) B2105399
theorem B6400795 : Blo 1246441 6400795 := bstep (se 1 (by rfl) ⟨4800596, by rfl⟩ : syracuseStep 6400795 = 9601193) B9601193
theorem B1870655 : Blo 1246441 1870655 := bstep (se 1 (by rfl) ⟨1402991, by rfl⟩ : syracuseStep 1870655 = 2805983) B2805983
theorem B3371071 : Blo 1246441 3371071 := bstep (se 1 (by rfl) ⟨2528303, by rfl⟩ : syracuseStep 3371071 = 5056607) B5056607
theorem B32395391 : Blo 1246441 32395391 := bstep (se 1 (by rfl) ⟨24296543, by rfl⟩ : syracuseStep 32395391 = 48593087) B48593087
theorem B1871999 : Blo 1246441 1871999 := bstep (se 1 (by rfl) ⟨1403999, by rfl⟩ : syracuseStep 1871999 = 2807999) B2807999
theorem B6746273 : Blo 1246441 6746273 := bstep (se 2 (by rfl) ⟨2529852, by rfl⟩ : syracuseStep 6746273 = 5059705) B5059705
theorem B4207247 : Blo 1246441 4207247 := bstep (se 1 (by rfl) ⟨3155435, by rfl⟩ : syracuseStep 4207247 = 6310871) B6310871
theorem B1997531 : Blo 1246441 1997531 := bstep (se 1 (by rfl) ⟨1498148, by rfl⟩ : syracuseStep 1997531 = 2996297) B2996297
theorem B4210217 : Blo 1246441 4210217 := bstep (se 2 (by rfl) ⟨1578831, by rfl⟩ : syracuseStep 4210217 = 3157663) B3157663
theorem B4497515 : Blo 1246441 4497515 := bstep (se 1 (by rfl) ⟨3373136, by rfl⟩ : syracuseStep 4497515 = 6746273) B6746273
theorem B1246823 : Blo 1246441 1246823 := bstep (se 1 (by rfl) ⟨935117, by rfl⟩ : syracuseStep 1246823 = 1870235) B1870235
theorem B1247103 : Blo 1246441 1247103 := bstep (se 1 (by rfl) ⟨935327, by rfl⟩ : syracuseStep 1247103 = 1870655) B1870655
theorem B21596927 : Blo 1246441 21596927 := bstep (se 1 (by rfl) ⟨16197695, by rfl⟩ : syracuseStep 21596927 = 32395391) B32395391
theorem B1247999 : Blo 1246441 1247999 := bstep (se 1 (by rfl) ⟨935999, by rfl⟩ : syracuseStep 1247999 = 1871999) B1871999
theorem B2804831 : Blo 1246441 2804831 := bstep (se 1 (by rfl) ⟨2103623, by rfl⟩ : syracuseStep 2804831 = 4207247) B4207247
theorem B1871465 : Blo 1246441 1871465 := bstep (se 2 (by rfl) ⟨701799, by rfl⟩ : syracuseStep 1871465 = 1403599) B1403599
theorem B1331687 : Blo 1246441 1331687 := bstep (se 1 (by rfl) ⟨998765, by rfl⟩ : syracuseStep 1331687 = 1997531) B1997531
theorem B2806811 : Blo 1246441 2806811 := bstep (se 1 (by rfl) ⟨2105108, by rfl⟩ : syracuseStep 2806811 = 4210217) B4210217
theorem B4494761 : Blo 1246441 4494761 := bstep (se 2 (by rfl) ⟨1685535, by rfl⟩ : syracuseStep 4494761 = 3371071) B3371071
theorem B2807387 : Blo 1246441 2807387 := bstep (se 1 (by rfl) ⟨2105540, by rfl⟩ : syracuseStep 2807387 = 4211081) B4211081
theorem B2807423 : Blo 1246441 2807423 := bstep (se 1 (by rfl) ⟨2105567, by rfl⟩ : syracuseStep 2807423 = 4211135) B4211135
theorem B11982491 : Blo 1246441 11982491 := bstep (se 1 (by rfl) ⟨8986868, by rfl⟩ : syracuseStep 11982491 = 17973737) B17973737
theorem B12801833 : Blo 1246441 12801833 := bstep (se 2 (by rfl) ⟨4800687, by rfl⟩ : syracuseStep 12801833 = 9601375) B9601375
theorem B1775935 : Blo 1246441 1775935 := bstep (se 1 (by rfl) ⟨1331951, by rfl⟩ : syracuseStep 1775935 = 2663903) B2663903
theorem B8534393 : Blo 1246441 8534393 := bstep (se 2 (by rfl) ⟨3200397, by rfl⟩ : syracuseStep 8534393 = 6400795) B6400795
theorem B2998343 : Blo 1246441 2998343 := bstep (se 1 (by rfl) ⟨2248757, by rfl⟩ : syracuseStep 2998343 = 4497515) B4497515
theorem B7988327 : Blo 1246441 7988327 := bstep (se 1 (by rfl) ⟨5991245, by rfl⟩ : syracuseStep 7988327 = 11982491) B11982491
theorem B9471653 : Blo 1246441 9471653 := bstep (se 4 (by rfl) ⟨887967, by rfl⟩ : syracuseStep 9471653 = 1775935) B1775935
theorem B57591805 : Blo 1246441 57591805 := bstep (se 3 (by rfl) ⟨10798463, by rfl⟩ : syracuseStep 57591805 = 21596927) B21596927
theorem B1869887 : Blo 1246441 1869887 := bstep (se 1 (by rfl) ⟨1402415, by rfl⟩ : syracuseStep 1869887 = 2804831) B2804831
theorem B1247643 : Blo 1246441 1247643 := bstep (se 1 (by rfl) ⟨935732, by rfl⟩ : syracuseStep 1247643 = 1871465) B1871465
theorem B1871207 : Blo 1246441 1871207 := bstep (se 1 (by rfl) ⟨1403405, by rfl⟩ : syracuseStep 1871207 = 2806811) B2806811
theorem B1871591 : Blo 1246441 1871591 := bstep (se 1 (by rfl) ⟨1403693, by rfl⟩ : syracuseStep 1871591 = 2807387) B2807387
theorem B1871615 : Blo 1246441 1871615 := bstep (se 1 (by rfl) ⟨1403711, by rfl⟩ : syracuseStep 1871615 = 2807423) B2807423
theorem B3551165 : Blo 1246441 3551165 := bstep (se 3 (by rfl) ⟨665843, by rfl⟩ : syracuseStep 3551165 = 1331687) B1331687
theorem B5689595 : Blo 1246441 5689595 := bstep (se 1 (by rfl) ⟨4267196, by rfl⟩ : syracuseStep 5689595 = 8534393) B8534393
theorem B2996507 : Blo 1246441 2996507 := bstep (se 1 (by rfl) ⟨2247380, by rfl⟩ : syracuseStep 2996507 = 4494761) B4494761
theorem B8534555 : Blo 1246441 8534555 := bstep (se 1 (by rfl) ⟨6400916, by rfl⟩ : syracuseStep 8534555 = 12801833) B12801833
theorem B3793063 : Blo 1246441 3793063 := bstep (se 1 (by rfl) ⟨2844797, by rfl⟩ : syracuseStep 3793063 = 5689595) B5689595
theorem B7995581 : Blo 1246441 7995581 := bstep (se 3 (by rfl) ⟨1499171, by rfl⟩ : syracuseStep 7995581 = 2998343) B2998343
theorem B5325551 : Blo 1246441 5325551 := bstep (se 1 (by rfl) ⟨3994163, by rfl⟩ : syracuseStep 5325551 = 7988327) B7988327
theorem B1246591 : Blo 1246441 1246591 := bstep (se 1 (by rfl) ⟨934943, by rfl⟩ : syracuseStep 1246591 = 1869887) B1869887
theorem B1247471 : Blo 1246441 1247471 := bstep (se 1 (by rfl) ⟨935603, by rfl⟩ : syracuseStep 1247471 = 1871207) B1871207
theorem B1247727 : Blo 1246441 1247727 := bstep (se 1 (by rfl) ⟨935795, by rfl⟩ : syracuseStep 1247727 = 1871591) B1871591
theorem B1247743 : Blo 1246441 1247743 := bstep (se 1 (by rfl) ⟨935807, by rfl⟩ : syracuseStep 1247743 = 1871615) B1871615
theorem B5689703 : Blo 1246441 5689703 := bstep (se 1 (by rfl) ⟨4267277, by rfl⟩ : syracuseStep 5689703 = 8534555) B8534555
theorem B76789073 : Blo 1246441 76789073 := bstep (se 2 (by rfl) ⟨28795902, by rfl⟩ : syracuseStep 76789073 = 57591805) B57591805
theorem B6314435 : Blo 1246441 6314435 := bstep (se 1 (by rfl) ⟨4735826, by rfl⟩ : syracuseStep 6314435 = 9471653) B9471653
theorem B1997671 : Blo 1246441 1997671 := bstep (se 1 (by rfl) ⟨1498253, by rfl⟩ : syracuseStep 1997671 = 2996507) B2996507
theorem B2367443 : Blo 1246441 2367443 := bstep (se 1 (by rfl) ⟨1775582, by rfl⟩ : syracuseStep 2367443 = 3551165) B3551165
theorem B15172541 : Blo 1246441 15172541 := bstep (se 3 (by rfl) ⟨2844851, by rfl⟩ : syracuseStep 15172541 = 5689703) B5689703
theorem B2663561 : Blo 1246441 2663561 := bstep (se 2 (by rfl) ⟨998835, by rfl⟩ : syracuseStep 2663561 = 1997671) B1997671
theorem B5057417 : Blo 1246441 5057417 := bstep (se 2 (by rfl) ⟨1896531, by rfl⟩ : syracuseStep 5057417 = 3793063) B3793063
theorem B3550367 : Blo 1246441 3550367 := bstep (se 1 (by rfl) ⟨2662775, by rfl⟩ : syracuseStep 3550367 = 5325551) B5325551
theorem B204770861 : Blo 1246441 204770861 := bstep (se 3 (by rfl) ⟨38394536, by rfl⟩ : syracuseStep 204770861 = 76789073) B76789073
theorem B1578295 : Blo 1246441 1578295 := bstep (se 1 (by rfl) ⟨1183721, by rfl⟩ : syracuseStep 1578295 = 2367443) B2367443
theorem B5330387 : Blo 1246441 5330387 := bstep (se 1 (by rfl) ⟨3997790, by rfl⟩ : syracuseStep 5330387 = 7995581) B7995581
theorem B4209623 : Blo 1246441 4209623 := bstep (se 1 (by rfl) ⟨3157217, by rfl⟩ : syracuseStep 4209623 = 6314435) B6314435
theorem B7102829 : Blo 1246441 7102829 := bstep (se 3 (by rfl) ⟨1331780, by rfl⟩ : syracuseStep 7102829 = 2663561) B2663561
theorem B13486445 : Blo 1246441 13486445 := bstep (se 3 (by rfl) ⟨2528708, by rfl⟩ : syracuseStep 13486445 = 5057417) B5057417
theorem B136513907 : Blo 1246441 136513907 := bstep (se 1 (by rfl) ⟨102385430, by rfl⟩ : syracuseStep 136513907 = 204770861) B204770861
theorem B2806415 : Blo 1246441 2806415 := bstep (se 1 (by rfl) ⟨2104811, by rfl⟩ : syracuseStep 2806415 = 4209623) B4209623
theorem B10115027 : Blo 1246441 10115027 := bstep (se 1 (by rfl) ⟨7586270, by rfl⟩ : syracuseStep 10115027 = 15172541) B15172541
theorem B3553591 : Blo 1246441 3553591 := bstep (se 1 (by rfl) ⟨2665193, by rfl⟩ : syracuseStep 3553591 = 5330387) B5330387
theorem B2104393 : Blo 1246441 2104393 := bstep (se 2 (by rfl) ⟨789147, by rfl⟩ : syracuseStep 2104393 = 1578295) B1578295
theorem B2366911 : Blo 1246441 2366911 := bstep (se 1 (by rfl) ⟨1775183, by rfl⟩ : syracuseStep 2366911 = 3550367) B3550367
theorem B4735219 : Blo 1246441 4735219 := bstep (se 1 (by rfl) ⟨3551414, by rfl⟩ : syracuseStep 4735219 = 7102829) B7102829
theorem B6743351 : Blo 1246441 6743351 := bstep (se 1 (by rfl) ⟨5057513, by rfl⟩ : syracuseStep 6743351 = 10115027) B10115027
theorem B3155881 : Blo 1246441 3155881 := bstep (se 2 (by rfl) ⟨1183455, by rfl⟩ : syracuseStep 3155881 = 2366911) B2366911
theorem B4738121 : Blo 1246441 4738121 := bstep (se 2 (by rfl) ⟨1776795, by rfl⟩ : syracuseStep 4738121 = 3553591) B3553591
theorem B1870943 : Blo 1246441 1870943 := bstep (se 1 (by rfl) ⟨1403207, by rfl⟩ : syracuseStep 1870943 = 2806415) B2806415
theorem B2805857 : Blo 1246441 2805857 := bstep (se 2 (by rfl) ⟨1052196, by rfl⟩ : syracuseStep 2805857 = 2104393) B2104393
theorem B8990963 : Blo 1246441 8990963 := bstep (se 1 (by rfl) ⟨6743222, by rfl⟩ : syracuseStep 8990963 = 13486445) B13486445
theorem B91009271 : Blo 1246441 91009271 := bstep (se 1 (by rfl) ⟨68256953, by rfl⟩ : syracuseStep 91009271 = 136513907) B136513907
theorem B1247295 : Blo 1246441 1247295 := bstep (se 1 (by rfl) ⟨935471, by rfl⟩ : syracuseStep 1247295 = 1870943) B1870943
theorem B1870571 : Blo 1246441 1870571 := bstep (se 1 (by rfl) ⟨1402928, by rfl⟩ : syracuseStep 1870571 = 2805857) B2805857
theorem B60672847 : Blo 1246441 60672847 := bstep (se 1 (by rfl) ⟨45504635, by rfl⟩ : syracuseStep 60672847 = 91009271) B91009271
theorem B3158747 : Blo 1246441 3158747 := bstep (se 1 (by rfl) ⟨2369060, by rfl⟩ : syracuseStep 3158747 = 4738121) B4738121
theorem B4207841 : Blo 1246441 4207841 := bstep (se 2 (by rfl) ⟨1577940, by rfl⟩ : syracuseStep 4207841 = 3155881) B3155881
theorem B5993975 : Blo 1246441 5993975 := bstep (se 1 (by rfl) ⟨4495481, by rfl⟩ : syracuseStep 5993975 = 8990963) B8990963
theorem B6313625 : Blo 1246441 6313625 := bstep (se 2 (by rfl) ⟨2367609, by rfl⟩ : syracuseStep 6313625 = 4735219) B4735219
theorem B4495567 : Blo 1246441 4495567 := bstep (se 1 (by rfl) ⟨3371675, by rfl⟩ : syracuseStep 4495567 = 6743351) B6743351
theorem B2105831 : Blo 1246441 2105831 := bstep (se 1 (by rfl) ⟨1579373, by rfl⟩ : syracuseStep 2105831 = 3158747) B3158747
theorem B80897129 : Blo 1246441 80897129 := bstep (se 2 (by rfl) ⟨30336423, by rfl⟩ : syracuseStep 80897129 = 60672847) B60672847
theorem B1247047 : Blo 1246441 1247047 := bstep (se 1 (by rfl) ⟨935285, by rfl⟩ : syracuseStep 1247047 = 1870571) B1870571
theorem B2805227 : Blo 1246441 2805227 := bstep (se 1 (by rfl) ⟨2103920, by rfl⟩ : syracuseStep 2805227 = 4207841) B4207841
theorem B5994089 : Blo 1246441 5994089 := bstep (se 2 (by rfl) ⟨2247783, by rfl⟩ : syracuseStep 5994089 = 4495567) B4495567
theorem B3995983 : Blo 1246441 3995983 := bstep (se 1 (by rfl) ⟨2996987, by rfl⟩ : syracuseStep 3995983 = 5993975) B5993975
theorem B4209083 : Blo 1246441 4209083 := bstep (se 1 (by rfl) ⟨3156812, by rfl⟩ : syracuseStep 4209083 = 6313625) B6313625
theorem B1870151 : Blo 1246441 1870151 := bstep (se 1 (by rfl) ⟨1402613, by rfl⟩ : syracuseStep 1870151 = 2805227) B2805227
theorem B1403887 : Blo 1246441 1403887 := bstep (se 1 (by rfl) ⟨1052915, by rfl⟩ : syracuseStep 1403887 = 2105831) B2105831
theorem B5327977 : Blo 1246441 5327977 := bstep (se 2 (by rfl) ⟨1997991, by rfl⟩ : syracuseStep 5327977 = 3995983) B3995983
theorem B53931419 : Blo 1246441 53931419 := bstep (se 1 (by rfl) ⟨40448564, by rfl⟩ : syracuseStep 53931419 = 80897129) B80897129
theorem B2806055 : Blo 1246441 2806055 := bstep (se 1 (by rfl) ⟨2104541, by rfl⟩ : syracuseStep 2806055 = 4209083) B4209083
theorem B3996059 : Blo 1246441 3996059 := bstep (se 1 (by rfl) ⟨2997044, by rfl⟩ : syracuseStep 3996059 = 5994089) B5994089
theorem B7103969 : Blo 1246441 7103969 := bstep (se 2 (by rfl) ⟨2663988, by rfl⟩ : syracuseStep 7103969 = 5327977) B5327977
theorem B1246767 : Blo 1246441 1246767 := bstep (se 1 (by rfl) ⟨935075, by rfl⟩ : syracuseStep 1246767 = 1870151) B1870151
theorem B1870703 : Blo 1246441 1870703 := bstep (se 1 (by rfl) ⟨1403027, by rfl⟩ : syracuseStep 1870703 = 2806055) B2806055
theorem B1871849 : Blo 1246441 1871849 := bstep (se 2 (by rfl) ⟨701943, by rfl⟩ : syracuseStep 1871849 = 1403887) B1403887
theorem B10656157 : Blo 1246441 10656157 := bstep (se 3 (by rfl) ⟨1998029, by rfl⟩ : syracuseStep 10656157 = 3996059) B3996059
theorem B35954279 : Blo 1246441 35954279 := bstep (se 1 (by rfl) ⟨26965709, by rfl⟩ : syracuseStep 35954279 = 53931419) B53931419
theorem B4735979 : Blo 1246441 4735979 := bstep (se 1 (by rfl) ⟨3551984, by rfl⟩ : syracuseStep 4735979 = 7103969) B7103969
theorem B1247135 : Blo 1246441 1247135 := bstep (se 1 (by rfl) ⟨935351, by rfl⟩ : syracuseStep 1247135 = 1870703) B1870703
theorem B1247899 : Blo 1246441 1247899 := bstep (se 1 (by rfl) ⟨935924, by rfl⟩ : syracuseStep 1247899 = 1871849) B1871849
theorem B14208209 : Blo 1246441 14208209 := bstep (se 2 (by rfl) ⟨5328078, by rfl⟩ : syracuseStep 14208209 = 10656157) B10656157
theorem B23969519 : Blo 1246441 23969519 := bstep (se 1 (by rfl) ⟨17977139, by rfl⟩ : syracuseStep 23969519 = 35954279) B35954279
theorem B9472139 : Blo 1246441 9472139 := bstep (se 1 (by rfl) ⟨7104104, by rfl⟩ : syracuseStep 9472139 = 14208209) B14208209
theorem B3157319 : Blo 1246441 3157319 := bstep (se 1 (by rfl) ⟨2367989, by rfl⟩ : syracuseStep 3157319 = 4735979) B4735979
theorem B15979679 : Blo 1246441 15979679 := bstep (se 1 (by rfl) ⟨11984759, by rfl⟩ : syracuseStep 15979679 = 23969519) B23969519
theorem B10653119 : Blo 1246441 10653119 := bstep (se 1 (by rfl) ⟨7989839, by rfl⟩ : syracuseStep 10653119 = 15979679) B15979679
theorem B6314759 : Blo 1246441 6314759 := bstep (se 1 (by rfl) ⟨4736069, by rfl⟩ : syracuseStep 6314759 = 9472139) B9472139
theorem B2104879 : Blo 1246441 2104879 := bstep (se 1 (by rfl) ⟨1578659, by rfl⟩ : syracuseStep 2104879 = 3157319) B3157319
theorem B2806505 : Blo 1246441 2806505 := bstep (se 2 (by rfl) ⟨1052439, by rfl⟩ : syracuseStep 2806505 = 2104879) B2104879
theorem B4209839 : Blo 1246441 4209839 := bstep (se 1 (by rfl) ⟨3157379, by rfl⟩ : syracuseStep 4209839 = 6314759) B6314759
theorem B7102079 : Blo 1246441 7102079 := bstep (se 1 (by rfl) ⟨5326559, by rfl⟩ : syracuseStep 7102079 = 10653119) B10653119
theorem B1871003 : Blo 1246441 1871003 := bstep (se 1 (by rfl) ⟨1403252, by rfl⟩ : syracuseStep 1871003 = 2806505) B2806505
theorem B2806559 : Blo 1246441 2806559 := bstep (se 1 (by rfl) ⟨2104919, by rfl⟩ : syracuseStep 2806559 = 4209839) B4209839
theorem B4734719 : Blo 1246441 4734719 := bstep (se 1 (by rfl) ⟨3551039, by rfl⟩ : syracuseStep 4734719 = 7102079) B7102079
theorem B1247335 : Blo 1246441 1247335 := bstep (se 1 (by rfl) ⟨935501, by rfl⟩ : syracuseStep 1247335 = 1871003) B1871003
theorem B3156479 : Blo 1246441 3156479 := bstep (se 1 (by rfl) ⟨2367359, by rfl⟩ : syracuseStep 3156479 = 4734719) B4734719
theorem B1871039 : Blo 1246441 1871039 := bstep (se 1 (by rfl) ⟨1403279, by rfl⟩ : syracuseStep 1871039 = 2806559) B2806559
theorem B1247359 : Blo 1246441 1247359 := bstep (se 1 (by rfl) ⟨935519, by rfl⟩ : syracuseStep 1247359 = 1871039) B1871039
theorem B2104319 : Blo 1246441 2104319 := bstep (se 1 (by rfl) ⟨1578239, by rfl⟩ : syracuseStep 2104319 = 3156479) B3156479
theorem B1402879 : Blo 1246441 1402879 := bstep (se 1 (by rfl) ⟨1052159, by rfl⟩ : syracuseStep 1402879 = 2104319) B2104319
theorem B1870505 : Blo 1246441 1870505 := bstep (se 2 (by rfl) ⟨701439, by rfl⟩ : syracuseStep 1870505 = 1402879) B1402879
theorem B1247003 : Blo 1246441 1247003 := bstep (se 1 (by rfl) ⟨935252, by rfl⟩ : syracuseStep 1247003 = 1870505) B1870505

theorem C0 (j : ℕ) (h1 : 311610 ≤ j) (h2 : j ≤ 312109) : Blo 1246441 (4 * j + 3) := by
  interval_cases j
  · exact B1246443
  · exact B1246447
  · exact B1246451
  · exact B1246455
  · exact B1246459
  · exact B1246463
  · exact B1246467
  · exact B1246471
  · exact B1246475
  · exact B1246479
  · exact B1246483
  · exact B1246487
  · exact B1246491
  · exact B1246495
  · exact B1246499
  · exact B1246503
  · exact B1246507
  · exact B1246511
  · exact B1246515
  · exact B1246519
  · exact B1246523
  · exact B1246527
  · exact B1246531
  · exact B1246535
  · exact B1246539
  · exact B1246543
  · exact B1246547
  · exact B1246551
  · exact B1246555
  · exact B1246559
  · exact B1246563
  · exact B1246567
  · exact B1246571
  · exact B1246575
  · exact B1246579
  · exact B1246583
  · exact B1246587
  · exact B1246591
  · exact B1246595
  · exact B1246599
  · exact B1246603
  · exact B1246607
  · exact B1246611
  · exact B1246615
  · exact B1246619
  · exact B1246623
  · exact B1246627
  · exact B1246631
  · exact B1246635
  · exact B1246639
  · exact B1246643
  · exact B1246647
  · exact B1246651
  · exact B1246655
  · exact B1246659
  · exact B1246663
  · exact B1246667
  · exact B1246671
  · exact B1246675
  · exact B1246679
  · exact B1246683
  · exact B1246687
  · exact B1246691
  · exact B1246695
  · exact B1246699
  · exact B1246703
  · exact B1246707
  · exact B1246711
  · exact B1246715
  · exact B1246719
  · exact B1246723
  · exact B1246727
  · exact B1246731
  · exact B1246735
  · exact B1246739
  · exact B1246743
  · exact B1246747
  · exact B1246751
  · exact B1246755
  · exact B1246759
  · exact B1246763
  · exact B1246767
  · exact B1246771
  · exact B1246775
  · exact B1246779
  · exact B1246783
  · exact B1246787
  · exact B1246791
  · exact B1246795
  · exact B1246799
  · exact B1246803
  · exact B1246807
  · exact B1246811
  · exact B1246815
  · exact B1246819
  · exact B1246823
  · exact B1246827
  · exact B1246831
  · exact B1246835
  · exact B1246839
  · exact B1246843
  · exact B1246847
  · exact B1246851
  · exact B1246855
  · exact B1246859
  · exact B1246863
  · exact B1246867
  · exact B1246871
  · exact B1246875
  · exact B1246879
  · exact B1246883
  · exact B1246887
  · exact B1246891
  · exact B1246895
  · exact B1246899
  · exact B1246903
  · exact B1246907
  · exact B1246911
  · exact B1246915
  · exact B1246919
  · exact B1246923
  · exact B1246927
  · exact B1246931
  · exact B1246935
  · exact B1246939
  · exact B1246943
  · exact B1246947
  · exact B1246951
  · exact B1246955
  · exact B1246959
  · exact B1246963
  · exact B1246967
  · exact B1246971
  · exact B1246975
  · exact B1246979
  · exact B1246983
  · exact B1246987
  · exact B1246991
  · exact B1246995
  · exact B1246999
  · exact B1247003
  · exact B1247007
  · exact B1247011
  · exact B1247015
  · exact B1247019
  · exact B1247023
  · exact B1247027
  · exact B1247031
  · exact B1247035
  · exact B1247039
  · exact B1247043
  · exact B1247047
  · exact B1247051
  · exact B1247055
  · exact B1247059
  · exact B1247063
  · exact B1247067
  · exact B1247071
  · exact B1247075
  · exact B1247079
  · exact B1247083
  · exact B1247087
  · exact B1247091
  · exact B1247095
  · exact B1247099
  · exact B1247103
  · exact B1247107
  · exact B1247111
  · exact B1247115
  · exact B1247119
  · exact B1247123
  · exact B1247127
  · exact B1247131
  · exact B1247135
  · exact B1247139
  · exact B1247143
  · exact B1247147
  · exact B1247151
  · exact B1247155
  · exact B1247159
  · exact B1247163
  · exact B1247167
  · exact B1247171
  · exact B1247175
  · exact B1247179
  · exact B1247183
  · exact B1247187
  · exact B1247191
  · exact B1247195
  · exact B1247199
  · exact B1247203
  · exact B1247207
  · exact B1247211
  · exact B1247215
  · exact B1247219
  · exact B1247223
  · exact B1247227
  · exact B1247231
  · exact B1247235
  · exact B1247239
  · exact B1247243
  · exact B1247247
  · exact B1247251
  · exact B1247255
  · exact B1247259
  · exact B1247263
  · exact B1247267
  · exact B1247271
  · exact B1247275
  · exact B1247279
  · exact B1247283
  · exact B1247287
  · exact B1247291
  · exact B1247295
  · exact B1247299
  · exact B1247303
  · exact B1247307
  · exact B1247311
  · exact B1247315
  · exact B1247319
  · exact B1247323
  · exact B1247327
  · exact B1247331
  · exact B1247335
  · exact B1247339
  · exact B1247343
  · exact B1247347
  · exact B1247351
  · exact B1247355
  · exact B1247359
  · exact B1247363
  · exact B1247367
  · exact B1247371
  · exact B1247375
  · exact B1247379
  · exact B1247383
  · exact B1247387
  · exact B1247391
  · exact B1247395
  · exact B1247399
  · exact B1247403
  · exact B1247407
  · exact B1247411
  · exact B1247415
  · exact B1247419
  · exact B1247423
  · exact B1247427
  · exact B1247431
  · exact B1247435
  · exact B1247439
  · exact B1247443
  · exact B1247447
  · exact B1247451
  · exact B1247455
  · exact B1247459
  · exact B1247463
  · exact B1247467
  · exact B1247471
  · exact B1247475
  · exact B1247479
  · exact B1247483
  · exact B1247487
  · exact B1247491
  · exact B1247495
  · exact B1247499
  · exact B1247503
  · exact B1247507
  · exact B1247511
  · exact B1247515
  · exact B1247519
  · exact B1247523
  · exact B1247527
  · exact B1247531
  · exact B1247535
  · exact B1247539
  · exact B1247543
  · exact B1247547
  · exact B1247551
  · exact B1247555
  · exact B1247559
  · exact B1247563
  · exact B1247567
  · exact B1247571
  · exact B1247575
  · exact B1247579
  · exact B1247583
  · exact B1247587
  · exact B1247591
  · exact B1247595
  · exact B1247599
  · exact B1247603
  · exact B1247607
  · exact B1247611
  · exact B1247615
  · exact B1247619
  · exact B1247623
  · exact B1247627
  · exact B1247631
  · exact B1247635
  · exact B1247639
  · exact B1247643
  · exact B1247647
  · exact B1247651
  · exact B1247655
  · exact B1247659
  · exact B1247663
  · exact B1247667
  · exact B1247671
  · exact B1247675
  · exact B1247679
  · exact B1247683
  · exact B1247687
  · exact B1247691
  · exact B1247695
  · exact B1247699
  · exact B1247703
  · exact B1247707
  · exact B1247711
  · exact B1247715
  · exact B1247719
  · exact B1247723
  · exact B1247727
  · exact B1247731
  · exact B1247735
  · exact B1247739
  · exact B1247743
  · exact B1247747
  · exact B1247751
  · exact B1247755
  · exact B1247759
  · exact B1247763
  · exact B1247767
  · exact B1247771
  · exact B1247775
  · exact B1247779
  · exact B1247783
  · exact B1247787
  · exact B1247791
  · exact B1247795
  · exact B1247799
  · exact B1247803
  · exact B1247807
  · exact B1247811
  · exact B1247815
  · exact B1247819
  · exact B1247823
  · exact B1247827
  · exact B1247831
  · exact B1247835
  · exact B1247839
  · exact B1247843
  · exact B1247847
  · exact B1247851
  · exact B1247855
  · exact B1247859
  · exact B1247863
  · exact B1247867
  · exact B1247871
  · exact B1247875
  · exact B1247879
  · exact B1247883
  · exact B1247887
  · exact B1247891
  · exact B1247895
  · exact B1247899
  · exact B1247903
  · exact B1247907
  · exact B1247911
  · exact B1247915
  · exact B1247919
  · exact B1247923
  · exact B1247927
  · exact B1247931
  · exact B1247935
  · exact B1247939
  · exact B1247943
  · exact B1247947
  · exact B1247951
  · exact B1247955
  · exact B1247959
  · exact B1247963
  · exact B1247967
  · exact B1247971
  · exact B1247975
  · exact B1247979
  · exact B1247983
  · exact B1247987
  · exact B1247991
  · exact B1247995
  · exact B1247999
  · exact B1248003
  · exact B1248007
  · exact B1248011
  · exact B1248015
  · exact B1248019
  · exact B1248023
  · exact B1248027
  · exact B1248031
  · exact B1248035
  · exact B1248039
  · exact B1248043
  · exact B1248047
  · exact B1248051
  · exact B1248055
  · exact B1248059
  · exact B1248063
  · exact B1248067
  · exact B1248071
  · exact B1248075
  · exact B1248079
  · exact B1248083
  · exact B1248087
  · exact B1248091
  · exact B1248095
  · exact B1248099
  · exact B1248103
  · exact B1248107
  · exact B1248111
  · exact B1248115
  · exact B1248119
  · exact B1248123
  · exact B1248127
  · exact B1248131
  · exact B1248135
  · exact B1248139
  · exact B1248143
  · exact B1248147
  · exact B1248151
  · exact B1248155
  · exact B1248159
  · exact B1248163
  · exact B1248167
  · exact B1248171
  · exact B1248175
  · exact B1248179
  · exact B1248183
  · exact B1248187
  · exact B1248191
  · exact B1248195
  · exact B1248199
  · exact B1248203
  · exact B1248207
  · exact B1248211
  · exact B1248215
  · exact B1248219
  · exact B1248223
  · exact B1248227
  · exact B1248231
  · exact B1248235
  · exact B1248239
  · exact B1248243
  · exact B1248247
  · exact B1248251
  · exact B1248255
  · exact B1248259
  · exact B1248263
  · exact B1248267
  · exact B1248271
  · exact B1248275
  · exact B1248279
  · exact B1248283
  · exact B1248287
  · exact B1248291
  · exact B1248295
  · exact B1248299
  · exact B1248303
  · exact B1248307
  · exact B1248311
  · exact B1248315
  · exact B1248319
  · exact B1248323
  · exact B1248327
  · exact B1248331
  · exact B1248335
  · exact B1248339
  · exact B1248343
  · exact B1248347
  · exact B1248351
  · exact B1248355
  · exact B1248359
  · exact B1248363
  · exact B1248367
  · exact B1248371
  · exact B1248375
  · exact B1248379
  · exact B1248383
  · exact B1248387
  · exact B1248391
  · exact B1248395
  · exact B1248399
  · exact B1248403
  · exact B1248407
  · exact B1248411
  · exact B1248415
  · exact B1248419
  · exact B1248423
  · exact B1248427
  · exact B1248431
  · exact B1248435
  · exact B1248439

theorem solution (m : ℕ) (hlo : 1246441 ≤ m) (hhi : m ≤ 1248441) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 311610 ≤ j := by omega
    have hj2 : j ≤ 312109 := by omega
    have hb : Blo 1246441 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
