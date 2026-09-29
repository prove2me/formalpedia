-- Prove2me | solution 1 for syracuse_descends_range_1572484_1574484
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:07:11.306381+00:00
-- url     : https://prove2.me/submissions/eb574cf5-a14b-4bd8-a61f-46ae7bdf40d4

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


theorem B2359301 : Blo 1572484 2359301 := bbase (se 4 (by rfl) ⟨221184, by rfl⟩ : syracuseStep 2359301 = 442369) (by norm_num)
theorem B2654221 : Blo 1572484 2654221 := bbase (se 3 (by rfl) ⟨497666, by rfl⟩ : syracuseStep 2654221 = 995333) (by norm_num)
theorem B1769485 : Blo 1572484 1769485 := bbase (se 3 (by rfl) ⟨331778, by rfl⟩ : syracuseStep 1769485 = 663557) (by norm_num)
theorem B1679377 : Blo 1572484 1679377 := bbase (se 2 (by rfl) ⟨629766, by rfl⟩ : syracuseStep 1679377 = 1259533) (by norm_num)
theorem B2359325 : Blo 1572484 2359325 := bbase (se 3 (by rfl) ⟨442373, by rfl⟩ : syracuseStep 2359325 = 884747) (by norm_num)
theorem B1769521 : Blo 1572484 1769521 := bbase (se 2 (by rfl) ⟨663570, by rfl⟩ : syracuseStep 1769521 = 1327141) (by norm_num)
theorem B5308469 : Blo 1572484 5308469 := bbase (se 5 (by rfl) ⟨248834, by rfl⟩ : syracuseStep 5308469 = 497669) (by norm_num)
theorem B3538997 : Blo 1572484 3538997 := bbase (se 5 (by rfl) ⟨165890, by rfl⟩ : syracuseStep 3538997 = 331781) (by norm_num)
theorem B2359349 : Blo 1572484 2359349 := bbase (se 5 (by rfl) ⟨110594, by rfl⟩ : syracuseStep 2359349 = 221189) (by norm_num)
theorem B2359373 : Blo 1572484 2359373 := bbase (se 3 (by rfl) ⟨442382, by rfl⟩ : syracuseStep 2359373 = 884765) (by norm_num)
theorem B1769557 : Blo 1572484 1769557 := bbase (se 8 (by rfl) ⟨10368, by rfl⟩ : syracuseStep 1769557 = 20737) (by norm_num)
theorem B3981413 : Blo 1572484 3981413 := bbase (se 4 (by rfl) ⟨373257, by rfl⟩ : syracuseStep 3981413 = 746515) (by norm_num)
theorem B2654309 : Blo 1572484 2654309 := bbase (se 4 (by rfl) ⟨248841, by rfl⟩ : syracuseStep 2654309 = 497683) (by norm_num)
theorem B2359397 : Blo 1572484 2359397 := bbase (se 4 (by rfl) ⟨221193, by rfl⟩ : syracuseStep 2359397 = 442387) (by norm_num)
theorem B1769593 : Blo 1572484 1769593 := bbase (se 2 (by rfl) ⟨663597, by rfl⟩ : syracuseStep 1769593 = 1327195) (by norm_num)
theorem B3539069 : Blo 1572484 3539069 := bbase (se 3 (by rfl) ⟨663575, by rfl⟩ : syracuseStep 3539069 = 1327151) (by norm_num)
theorem B2359421 : Blo 1572484 2359421 := bbase (se 3 (by rfl) ⟨442391, by rfl⟩ : syracuseStep 2359421 = 884783) (by norm_num)
theorem B2359445 : Blo 1572484 2359445 := bbase (se 6 (by rfl) ⟨55299, by rfl⟩ : syracuseStep 2359445 = 110599) (by norm_num)
theorem B1769629 : Blo 1572484 1769629 := bbase (se 3 (by rfl) ⟨331805, by rfl⟩ : syracuseStep 1769629 = 663611) (by norm_num)
theorem B2392229 : Blo 1572484 2392229 := bbase (se 4 (by rfl) ⟨224271, by rfl⟩ : syracuseStep 2392229 = 448543) (by norm_num)
theorem B2359469 : Blo 1572484 2359469 := bbase (se 3 (by rfl) ⟨442400, by rfl⟩ : syracuseStep 2359469 = 884801) (by norm_num)
theorem B1941689 : Blo 1572484 1941689 := bbase (se 2 (by rfl) ⟨728133, by rfl⟩ : syracuseStep 1941689 = 1456267) (by norm_num)
theorem B1769665 : Blo 1572484 1769665 := bbase (se 2 (by rfl) ⟨663624, by rfl⟩ : syracuseStep 1769665 = 1327249) (by norm_num)
theorem B3539141 : Blo 1572484 3539141 := bbase (se 4 (by rfl) ⟨331794, by rfl⟩ : syracuseStep 3539141 = 663589) (by norm_num)
theorem B2359493 : Blo 1572484 2359493 := bbase (se 4 (by rfl) ⟨221202, by rfl⟩ : syracuseStep 2359493 = 442405) (by norm_num)
theorem B3358925 : Blo 1572484 3358925 := bbase (se 3 (by rfl) ⟨629798, by rfl⟩ : syracuseStep 3358925 = 1259597) (by norm_num)
theorem B2359517 : Blo 1572484 2359517 := bbase (se 3 (by rfl) ⟨442409, by rfl⟩ : syracuseStep 2359517 = 884819) (by norm_num)
theorem B2654437 : Blo 1572484 2654437 := bbase (se 4 (by rfl) ⟨248853, by rfl⟩ : syracuseStep 2654437 = 497707) (by norm_num)
theorem B1769701 : Blo 1572484 1769701 := bbase (se 4 (by rfl) ⟨165909, by rfl⟩ : syracuseStep 1769701 = 331819) (by norm_num)
theorem B5038325 : Blo 1572484 5038325 := bbase (se 5 (by rfl) ⟨236171, by rfl⟩ : syracuseStep 5038325 = 472343) (by norm_num)
theorem B2359541 : Blo 1572484 2359541 := bbase (se 5 (by rfl) ⟨110603, by rfl⟩ : syracuseStep 2359541 = 221207) (by norm_num)
theorem B1990909 : Blo 1572484 1990909 := bbase (se 3 (by rfl) ⟨373295, by rfl⟩ : syracuseStep 1990909 = 746591) (by norm_num)
theorem B1769737 : Blo 1572484 1769737 := bbase (se 2 (by rfl) ⟨663651, by rfl⟩ : syracuseStep 1769737 = 1327303) (by norm_num)
theorem B3539213 : Blo 1572484 3539213 := bbase (se 3 (by rfl) ⟨663602, by rfl⟩ : syracuseStep 3539213 = 1327205) (by norm_num)
theorem B2359565 : Blo 1572484 2359565 := bbase (se 3 (by rfl) ⟨442418, by rfl⟩ : syracuseStep 2359565 = 884837) (by norm_num)
theorem B26878229 : Blo 1572484 26878229 := bbase (se 6 (by rfl) ⟨629958, by rfl⟩ : syracuseStep 26878229 = 1259917) (by norm_num)
theorem B2359589 : Blo 1572484 2359589 := bbase (se 4 (by rfl) ⟨221211, by rfl⟩ : syracuseStep 2359589 = 442423) (by norm_num)
theorem B1769773 : Blo 1572484 1769773 := bbase (se 3 (by rfl) ⟨331832, by rfl⟩ : syracuseStep 1769773 = 663665) (by norm_num)
theorem B2654525 : Blo 1572484 2654525 := bbase (se 3 (by rfl) ⟨497723, by rfl⟩ : syracuseStep 2654525 = 995447) (by norm_num)
theorem B2359613 : Blo 1572484 2359613 := bbase (se 3 (by rfl) ⟨442427, by rfl⟩ : syracuseStep 2359613 = 884855) (by norm_num)
theorem B3359045 : Blo 1572484 3359045 := bbase (se 4 (by rfl) ⟨314910, by rfl⟩ : syracuseStep 3359045 = 629821) (by norm_num)
theorem B1769809 : Blo 1572484 1769809 := bbase (se 2 (by rfl) ⟨663678, by rfl⟩ : syracuseStep 1769809 = 1327357) (by norm_num)
theorem B3539285 : Blo 1572484 3539285 := bbase (se 10 (by rfl) ⟨5184, by rfl⟩ : syracuseStep 3539285 = 10369) (by norm_num)
theorem B2359637 : Blo 1572484 2359637 := bbase (se 10 (by rfl) ⟨3456, by rfl⟩ : syracuseStep 2359637 = 6913) (by norm_num)
theorem B2359661 : Blo 1572484 2359661 := bbase (se 3 (by rfl) ⟨442436, by rfl⟩ : syracuseStep 2359661 = 884873) (by norm_num)
theorem B1769845 : Blo 1572484 1769845 := bbase (se 5 (by rfl) ⟨82961, by rfl⟩ : syracuseStep 1769845 = 165923) (by norm_num)
theorem B2359685 : Blo 1572484 2359685 := bbase (se 4 (by rfl) ⟨221220, by rfl⟩ : syracuseStep 2359685 = 442441) (by norm_num)
theorem B1769881 : Blo 1572484 1769881 := bbase (se 2 (by rfl) ⟨663705, by rfl⟩ : syracuseStep 1769881 = 1327411) (by norm_num)
theorem B3539357 : Blo 1572484 3539357 := bbase (se 3 (by rfl) ⟨663629, by rfl⟩ : syracuseStep 3539357 = 1327259) (by norm_num)
theorem B2359709 : Blo 1572484 2359709 := bbase (se 3 (by rfl) ⟨442445, by rfl⟩ : syracuseStep 2359709 = 884891) (by norm_num)
theorem B1991081 : Blo 1572484 1991081 := bbase (se 2 (by rfl) ⟨746655, by rfl⟩ : syracuseStep 1991081 = 1493311) (by norm_num)
theorem B2359733 : Blo 1572484 2359733 := bbase (se 5 (by rfl) ⟨110612, by rfl⟩ : syracuseStep 2359733 = 221225) (by norm_num)
theorem B3981757 : Blo 1572484 3981757 := bbase (se 3 (by rfl) ⟨746579, by rfl⟩ : syracuseStep 3981757 = 1493159) (by norm_num)
theorem B2654653 : Blo 1572484 2654653 := bbase (se 3 (by rfl) ⟨497747, by rfl⟩ : syracuseStep 2654653 = 995495) (by norm_num)
theorem B1769917 : Blo 1572484 1769917 := bbase (se 3 (by rfl) ⟨331859, by rfl⟩ : syracuseStep 1769917 = 663719) (by norm_num)
theorem B1679821 : Blo 1572484 1679821 := bbase (se 3 (by rfl) ⟨314966, by rfl⟩ : syracuseStep 1679821 = 629933) (by norm_num)
theorem B2359757 : Blo 1572484 2359757 := bbase (se 3 (by rfl) ⟨442454, by rfl⟩ : syracuseStep 2359757 = 884909) (by norm_num)
theorem B1819093 : Blo 1572484 1819093 := bbase (se 7 (by rfl) ⟨21317, by rfl⟩ : syracuseStep 1819093 = 42635) (by norm_num)
theorem B1991137 : Blo 1572484 1991137 := bbase (se 2 (by rfl) ⟨746676, by rfl⟩ : syracuseStep 1991137 = 1493353) (by norm_num)
theorem B1769953 : Blo 1572484 1769953 := bbase (se 2 (by rfl) ⟨663732, by rfl⟩ : syracuseStep 1769953 = 1327465) (by norm_num)
theorem B2359781 : Blo 1572484 2359781 := bbase (se 4 (by rfl) ⟨221229, by rfl⟩ : syracuseStep 2359781 = 442459) (by norm_num)
theorem B7963109 : Blo 1572484 7963109 := bbase (se 4 (by rfl) ⟨746541, by rfl⟩ : syracuseStep 7963109 = 1493083) (by norm_num)
theorem B5308901 : Blo 1572484 5308901 := bbase (se 4 (by rfl) ⟨497709, by rfl⟩ : syracuseStep 5308901 = 995419) (by norm_num)
theorem B3539429 : Blo 1572484 3539429 := bbase (se 4 (by rfl) ⟨331821, by rfl⟩ : syracuseStep 3539429 = 663643) (by norm_num)
theorem B2359805 : Blo 1572484 2359805 := bbase (se 3 (by rfl) ⟨442463, by rfl⟩ : syracuseStep 2359805 = 884927) (by norm_num)
theorem B1769989 : Blo 1572484 1769989 := bbase (se 4 (by rfl) ⟨165936, by rfl⟩ : syracuseStep 1769989 = 331873) (by norm_num)
theorem B2654741 : Blo 1572484 2654741 := bbase (se 6 (by rfl) ⟨62220, by rfl⟩ : syracuseStep 2654741 = 124441) (by norm_num)
theorem B2359829 : Blo 1572484 2359829 := bbase (se 6 (by rfl) ⟨55308, by rfl⟩ : syracuseStep 2359829 = 110617) (by norm_num)
theorem B1770025 : Blo 1572484 1770025 := bbase (se 2 (by rfl) ⟨663759, by rfl⟩ : syracuseStep 1770025 = 1327519) (by norm_num)
theorem B3981869 : Blo 1572484 3981869 := bbase (se 3 (by rfl) ⟨746600, by rfl⟩ : syracuseStep 3981869 = 1493201) (by norm_num)
theorem B3539501 : Blo 1572484 3539501 := bbase (se 3 (by rfl) ⟨663656, by rfl⟩ : syracuseStep 3539501 = 1327313) (by norm_num)
theorem B2359853 : Blo 1572484 2359853 := bbase (se 3 (by rfl) ⟨442472, by rfl⟩ : syracuseStep 2359853 = 884945) (by norm_num)
theorem B1991233 : Blo 1572484 1991233 := bbase (se 2 (by rfl) ⟨746712, by rfl⟩ : syracuseStep 1991233 = 1493425) (by norm_num)
theorem B3883589 : Blo 1572484 3883589 := bbase (se 4 (by rfl) ⟨364086, by rfl⟩ : syracuseStep 3883589 = 728173) (by norm_num)
theorem B1679941 : Blo 1572484 1679941 := bbase (se 4 (by rfl) ⟨157494, by rfl⟩ : syracuseStep 1679941 = 314989) (by norm_num)
theorem B2359877 : Blo 1572484 2359877 := bbase (se 4 (by rfl) ⟨221238, by rfl⟩ : syracuseStep 2359877 = 442477) (by norm_num)
theorem B1770061 : Blo 1572484 1770061 := bbase (se 3 (by rfl) ⟨331886, by rfl⟩ : syracuseStep 1770061 = 663773) (by norm_num)
theorem B2359901 : Blo 1572484 2359901 := bbase (se 3 (by rfl) ⟨442481, by rfl⟩ : syracuseStep 2359901 = 884963) (by norm_num)
theorem B1770097 : Blo 1572484 1770097 := bbase (se 2 (by rfl) ⟨663786, by rfl⟩ : syracuseStep 1770097 = 1327573) (by norm_num)
theorem B1794673 : Blo 1572484 1794673 := bbase (se 2 (by rfl) ⟨673002, by rfl⟩ : syracuseStep 1794673 = 1346005) (by norm_num)
theorem B3539573 : Blo 1572484 3539573 := bbase (se 5 (by rfl) ⟨165917, by rfl⟩ : syracuseStep 3539573 = 331835) (by norm_num)
theorem B2359925 : Blo 1572484 2359925 := bbase (se 5 (by rfl) ⟨110621, by rfl⟩ : syracuseStep 2359925 = 221243) (by norm_num)
theorem B2359949 : Blo 1572484 2359949 := bbase (se 3 (by rfl) ⟨442490, by rfl⟩ : syracuseStep 2359949 = 884981) (by norm_num)
theorem B2654869 : Blo 1572484 2654869 := bbase (se 6 (by rfl) ⟨62223, by rfl⟩ : syracuseStep 2654869 = 124447) (by norm_num)
theorem B1770133 : Blo 1572484 1770133 := bbase (se 6 (by rfl) ⟨41487, by rfl⟩ : syracuseStep 1770133 = 82975) (by norm_num)
theorem B2359973 : Blo 1572484 2359973 := bbase (se 4 (by rfl) ⟨221247, by rfl⟩ : syracuseStep 2359973 = 442495) (by norm_num)
theorem B1770169 : Blo 1572484 1770169 := bbase (se 2 (by rfl) ⟨663813, by rfl⟩ : syracuseStep 1770169 = 1327627) (by norm_num)
theorem B3539645 : Blo 1572484 3539645 := bbase (se 3 (by rfl) ⟨663683, by rfl⟩ : syracuseStep 3539645 = 1327367) (by norm_num)
theorem B2359997 : Blo 1572484 2359997 := bbase (se 3 (by rfl) ⟨442499, by rfl⟩ : syracuseStep 2359997 = 884999) (by norm_num)
theorem B30646997 : Blo 1572484 30646997 := bbase (se 7 (by rfl) ⟨359144, by rfl⟩ : syracuseStep 30646997 = 718289) (by norm_num)
theorem B2360021 : Blo 1572484 2360021 := bbase (se 7 (by rfl) ⟨27656, by rfl⟩ : syracuseStep 2360021 = 55313) (by norm_num)
theorem B10085077 : Blo 1572484 10085077 := bbase (se 7 (by rfl) ⟨118184, by rfl⟩ : syracuseStep 10085077 = 236369) (by norm_num)
theorem B1770205 : Blo 1572484 1770205 := bbase (se 3 (by rfl) ⟨331913, by rfl⟩ : syracuseStep 1770205 = 663827) (by norm_num)
theorem B3982061 : Blo 1572484 3982061 := bbase (se 3 (by rfl) ⟨746636, by rfl⟩ : syracuseStep 3982061 = 1493273) (by norm_num)
theorem B2654957 : Blo 1572484 2654957 := bbase (se 3 (by rfl) ⟨497804, by rfl⟩ : syracuseStep 2654957 = 995609) (by norm_num)
theorem B2360045 : Blo 1572484 2360045 := bbase (se 3 (by rfl) ⟨442508, by rfl⟩ : syracuseStep 2360045 = 885017) (by norm_num)
theorem B1991405 : Blo 1572484 1991405 := bbase (se 3 (by rfl) ⟨373388, by rfl⟩ : syracuseStep 1991405 = 746777) (by norm_num)
theorem B1770241 : Blo 1572484 1770241 := bbase (se 2 (by rfl) ⟨663840, by rfl⟩ : syracuseStep 1770241 = 1327681) (by norm_num)
theorem B3539717 : Blo 1572484 3539717 := bbase (se 4 (by rfl) ⟨331848, by rfl⟩ : syracuseStep 3539717 = 663697) (by norm_num)
theorem B2360069 : Blo 1572484 2360069 := bbase (se 4 (by rfl) ⟨221256, by rfl⟩ : syracuseStep 2360069 = 442513) (by norm_num)
theorem B15319829 : Blo 1572484 15319829 := bbase (se 6 (by rfl) ⟨359058, by rfl⟩ : syracuseStep 15319829 = 718117) (by norm_num)
theorem B2360093 : Blo 1572484 2360093 := bbase (se 3 (by rfl) ⟨442517, by rfl⟩ : syracuseStep 2360093 = 885035) (by norm_num)
theorem B1991461 : Blo 1572484 1991461 := bbase (se 4 (by rfl) ⟨186699, by rfl⟩ : syracuseStep 1991461 = 373399) (by norm_num)
theorem B1770277 : Blo 1572484 1770277 := bbase (se 4 (by rfl) ⟨165963, by rfl⟩ : syracuseStep 1770277 = 331927) (by norm_num)
theorem B2360117 : Blo 1572484 2360117 := bbase (se 5 (by rfl) ⟨110630, by rfl⟩ : syracuseStep 2360117 = 221261) (by norm_num)
theorem B1680193 : Blo 1572484 1680193 := bbase (se 2 (by rfl) ⟨630072, by rfl⟩ : syracuseStep 1680193 = 1260145) (by norm_num)
theorem B1680197 : Blo 1572484 1680197 := bbase (se 4 (by rfl) ⟨157518, by rfl⟩ : syracuseStep 1680197 = 315037) (by norm_num)
theorem B1770313 : Blo 1572484 1770313 := bbase (se 2 (by rfl) ⟨663867, by rfl⟩ : syracuseStep 1770313 = 1327735) (by norm_num)
theorem B3539789 : Blo 1572484 3539789 := bbase (se 3 (by rfl) ⟨663710, by rfl⟩ : syracuseStep 3539789 = 1327421) (by norm_num)
theorem B2360141 : Blo 1572484 2360141 := bbase (se 3 (by rfl) ⟨442526, by rfl⟩ : syracuseStep 2360141 = 885053) (by norm_num)
theorem B121160533 : Blo 1572484 121160533 := bbase (se 9 (by rfl) ⟨354962, by rfl⟩ : syracuseStep 121160533 = 709925) (by norm_num)
theorem B1794901 : Blo 1572484 1794901 := bbase (se 9 (by rfl) ⟨5258, by rfl⟩ : syracuseStep 1794901 = 10517) (by norm_num)
theorem B2360165 : Blo 1572484 2360165 := bbase (se 4 (by rfl) ⟨221265, by rfl⟩ : syracuseStep 2360165 = 442531) (by norm_num)
theorem B2655085 : Blo 1572484 2655085 := bbase (se 3 (by rfl) ⟨497828, by rfl⟩ : syracuseStep 2655085 = 995657) (by norm_num)
theorem B1770349 : Blo 1572484 1770349 := bbase (se 3 (by rfl) ⟨331940, by rfl⟩ : syracuseStep 1770349 = 663881) (by norm_num)
theorem B2360189 : Blo 1572484 2360189 := bbase (se 3 (by rfl) ⟨442535, by rfl⟩ : syracuseStep 2360189 = 885071) (by norm_num)
theorem B1991557 : Blo 1572484 1991557 := bbase (se 4 (by rfl) ⟨186708, by rfl⟩ : syracuseStep 1991557 = 373417) (by norm_num)
theorem B1770385 : Blo 1572484 1770385 := bbase (se 2 (by rfl) ⟨663894, by rfl⟩ : syracuseStep 1770385 = 1327789) (by norm_num)
theorem B5309333 : Blo 1572484 5309333 := bbase (se 6 (by rfl) ⟨124437, by rfl⟩ : syracuseStep 5309333 = 248875) (by norm_num)
theorem B3539861 : Blo 1572484 3539861 := bbase (se 6 (by rfl) ⟨82965, by rfl⟩ : syracuseStep 3539861 = 165931) (by norm_num)
theorem B2360213 : Blo 1572484 2360213 := bbase (se 6 (by rfl) ⟨55317, by rfl⟩ : syracuseStep 2360213 = 110635) (by norm_num)
theorem B2360237 : Blo 1572484 2360237 := bbase (se 3 (by rfl) ⟨442544, by rfl⟩ : syracuseStep 2360237 = 885089) (by norm_num)
theorem B1770421 : Blo 1572484 1770421 := bbase (se 5 (by rfl) ⟨82988, by rfl⟩ : syracuseStep 1770421 = 165977) (by norm_num)
theorem B3359677 : Blo 1572484 3359677 := bbase (se 3 (by rfl) ⟨629939, by rfl⟩ : syracuseStep 3359677 = 1259879) (by norm_num)
theorem B2655173 : Blo 1572484 2655173 := bbase (se 4 (by rfl) ⟨248922, by rfl⟩ : syracuseStep 2655173 = 497845) (by norm_num)
theorem B2360261 : Blo 1572484 2360261 := bbase (se 4 (by rfl) ⟨221274, by rfl⟩ : syracuseStep 2360261 = 442549) (by norm_num)
theorem B1770457 : Blo 1572484 1770457 := bbase (se 2 (by rfl) ⟨663921, by rfl⟩ : syracuseStep 1770457 = 1327843) (by norm_num)
theorem B3539933 : Blo 1572484 3539933 := bbase (se 3 (by rfl) ⟨663737, by rfl⟩ : syracuseStep 3539933 = 1327475) (by norm_num)
theorem B2360285 : Blo 1572484 2360285 := bbase (se 3 (by rfl) ⟨442553, by rfl⟩ : syracuseStep 2360285 = 885107) (by norm_num)
theorem B2360309 : Blo 1572484 2360309 := bbase (se 5 (by rfl) ⟨110639, by rfl⟩ : syracuseStep 2360309 = 221279) (by norm_num)
theorem B1770493 : Blo 1572484 1770493 := bbase (se 3 (by rfl) ⟨331967, by rfl⟩ : syracuseStep 1770493 = 663935) (by norm_num)
theorem B2360333 : Blo 1572484 2360333 := bbase (se 3 (by rfl) ⟨442562, by rfl⟩ : syracuseStep 2360333 = 885125) (by norm_num)
theorem B1770529 : Blo 1572484 1770529 := bbase (se 2 (by rfl) ⟨663948, by rfl⟩ : syracuseStep 1770529 = 1327897) (by norm_num)
theorem B3540005 : Blo 1572484 3540005 := bbase (se 4 (by rfl) ⟨331875, by rfl⟩ : syracuseStep 3540005 = 663751) (by norm_num)
theorem B2360357 : Blo 1572484 2360357 := bbase (se 4 (by rfl) ⟨221283, by rfl⟩ : syracuseStep 2360357 = 442567) (by norm_num)
theorem B1991729 : Blo 1572484 1991729 := bbase (se 2 (by rfl) ⟨746898, by rfl⟩ : syracuseStep 1991729 = 1493797) (by norm_num)
theorem B2360381 : Blo 1572484 2360381 := bbase (se 3 (by rfl) ⟨442571, by rfl⟩ : syracuseStep 2360381 = 885143) (by norm_num)
theorem B5973061 : Blo 1572484 5973061 := bbase (se 4 (by rfl) ⟨559974, by rfl⟩ : syracuseStep 5973061 = 1119949) (by norm_num)
theorem B3982405 : Blo 1572484 3982405 := bbase (se 4 (by rfl) ⟨373350, by rfl⟩ : syracuseStep 3982405 = 746701) (by norm_num)
theorem B2655301 : Blo 1572484 2655301 := bbase (se 4 (by rfl) ⟨248934, by rfl⟩ : syracuseStep 2655301 = 497869) (by norm_num)
theorem B1770565 : Blo 1572484 1770565 := bbase (se 4 (by rfl) ⟨165990, by rfl⟩ : syracuseStep 1770565 = 331981) (by norm_num)
theorem B2360405 : Blo 1572484 2360405 := bbase (se 8 (by rfl) ⟨13830, by rfl⟩ : syracuseStep 2360405 = 27661) (by norm_num)
theorem B1991785 : Blo 1572484 1991785 := bbase (se 2 (by rfl) ⟨746919, by rfl⟩ : syracuseStep 1991785 = 1493839) (by norm_num)
theorem B3540077 : Blo 1572484 3540077 := bbase (se 3 (by rfl) ⟨663764, by rfl⟩ : syracuseStep 3540077 = 1327529) (by norm_num)
theorem B2360429 : Blo 1572484 2360429 := bbase (se 3 (by rfl) ⟨442580, by rfl⟩ : syracuseStep 2360429 = 885161) (by norm_num)
theorem B1770601 : Blo 1572484 1770601 := bbase (se 2 (by rfl) ⟨663975, by rfl⟩ : syracuseStep 1770601 = 1327951) (by norm_num)
theorem B2360453 : Blo 1572484 2360453 := bbase (se 4 (by rfl) ⟨221292, by rfl⟩ : syracuseStep 2360453 = 442585) (by norm_num)
theorem B1770637 : Blo 1572484 1770637 := bbase (se 3 (by rfl) ⟨331994, by rfl⟩ : syracuseStep 1770637 = 663989) (by norm_num)
theorem B2655389 : Blo 1572484 2655389 := bbase (se 3 (by rfl) ⟨497885, by rfl⟩ : syracuseStep 2655389 = 995771) (by norm_num)
theorem B2360477 : Blo 1572484 2360477 := bbase (se 3 (by rfl) ⟨442589, by rfl⟩ : syracuseStep 2360477 = 885179) (by norm_num)
theorem B1770673 : Blo 1572484 1770673 := bbase (se 2 (by rfl) ⟨664002, by rfl⟩ : syracuseStep 1770673 = 1328005) (by norm_num)
theorem B3982517 : Blo 1572484 3982517 := bbase (se 5 (by rfl) ⟨186680, by rfl⟩ : syracuseStep 3982517 = 373361) (by norm_num)
theorem B3540149 : Blo 1572484 3540149 := bbase (se 5 (by rfl) ⟨165944, by rfl⟩ : syracuseStep 3540149 = 331889) (by norm_num)
theorem B2360501 : Blo 1572484 2360501 := bbase (se 5 (by rfl) ⟨110648, by rfl⟩ : syracuseStep 2360501 = 221297) (by norm_num)
theorem B1991881 : Blo 1572484 1991881 := bbase (se 2 (by rfl) ⟨746955, by rfl⟩ : syracuseStep 1991881 = 1493911) (by norm_num)
theorem B2360525 : Blo 1572484 2360525 := bbase (se 3 (by rfl) ⟨442598, by rfl⟩ : syracuseStep 2360525 = 885197) (by norm_num)
theorem B1770709 : Blo 1572484 1770709 := bbase (se 7 (by rfl) ⟨20750, by rfl⟩ : syracuseStep 1770709 = 41501) (by norm_num)
theorem B2360549 : Blo 1572484 2360549 := bbase (se 4 (by rfl) ⟨221301, by rfl⟩ : syracuseStep 2360549 = 442603) (by norm_num)
theorem B1770745 : Blo 1572484 1770745 := bbase (se 2 (by rfl) ⟨664029, by rfl⟩ : syracuseStep 1770745 = 1328059) (by norm_num)
theorem B3540221 : Blo 1572484 3540221 := bbase (se 3 (by rfl) ⟨663791, by rfl⟩ : syracuseStep 3540221 = 1327583) (by norm_num)
theorem B2360573 : Blo 1572484 2360573 := bbase (se 3 (by rfl) ⟨442607, by rfl⟩ : syracuseStep 2360573 = 885215) (by norm_num)
theorem B2360597 : Blo 1572484 2360597 := bbase (se 6 (by rfl) ⟨55326, by rfl⟩ : syracuseStep 2360597 = 110653) (by norm_num)
theorem B2655517 : Blo 1572484 2655517 := bbase (se 3 (by rfl) ⟨497909, by rfl⟩ : syracuseStep 2655517 = 995819) (by norm_num)
theorem B1770781 : Blo 1572484 1770781 := bbase (se 3 (by rfl) ⟨332021, by rfl⟩ : syracuseStep 1770781 = 664043) (by norm_num)
theorem B2360621 : Blo 1572484 2360621 := bbase (se 3 (by rfl) ⟨442616, by rfl⟩ : syracuseStep 2360621 = 885233) (by norm_num)
theorem B1770817 : Blo 1572484 1770817 := bbase (se 2 (by rfl) ⟨664056, by rfl⟩ : syracuseStep 1770817 = 1328113) (by norm_num)
theorem B5309765 : Blo 1572484 5309765 := bbase (se 4 (by rfl) ⟨497790, by rfl⟩ : syracuseStep 5309765 = 995581) (by norm_num)
theorem B3540293 : Blo 1572484 3540293 := bbase (se 4 (by rfl) ⟨331902, by rfl⟩ : syracuseStep 3540293 = 663805) (by norm_num)
theorem B2360645 : Blo 1572484 2360645 := bbase (se 4 (by rfl) ⟨221310, by rfl⟩ : syracuseStep 2360645 = 442621) (by norm_num)
theorem B2360669 : Blo 1572484 2360669 := bbase (se 3 (by rfl) ⟨442625, by rfl⟩ : syracuseStep 2360669 = 885251) (by norm_num)
theorem B1770853 : Blo 1572484 1770853 := bbase (se 4 (by rfl) ⟨166017, by rfl⟩ : syracuseStep 1770853 = 332035) (by norm_num)
theorem B5973365 : Blo 1572484 5973365 := bbase (se 5 (by rfl) ⟨280001, by rfl⟩ : syracuseStep 5973365 = 560003) (by norm_num)
theorem B3982709 : Blo 1572484 3982709 := bbase (se 5 (by rfl) ⟨186689, by rfl⟩ : syracuseStep 3982709 = 373379) (by norm_num)
theorem B2655605 : Blo 1572484 2655605 := bbase (se 5 (by rfl) ⟨124481, by rfl⟩ : syracuseStep 2655605 = 248963) (by norm_num)
theorem B2360693 : Blo 1572484 2360693 := bbase (se 5 (by rfl) ⟨110657, by rfl⟩ : syracuseStep 2360693 = 221315) (by norm_num)
theorem B1680761 : Blo 1572484 1680761 := bbase (se 2 (by rfl) ⟨630285, by rfl⟩ : syracuseStep 1680761 = 1260571) (by norm_num)
theorem B1992053 : Blo 1572484 1992053 := bbase (se 5 (by rfl) ⟨93377, by rfl⟩ : syracuseStep 1992053 = 186755) (by norm_num)
theorem B1770889 : Blo 1572484 1770889 := bbase (se 2 (by rfl) ⟨664083, by rfl⟩ : syracuseStep 1770889 = 1328167) (by norm_num)
theorem B3540365 : Blo 1572484 3540365 := bbase (se 3 (by rfl) ⟨663818, by rfl⟩ : syracuseStep 3540365 = 1327637) (by norm_num)
theorem B2360717 : Blo 1572484 2360717 := bbase (se 3 (by rfl) ⟨442634, by rfl⟩ : syracuseStep 2360717 = 885269) (by norm_num)
theorem B4310437 : Blo 1572484 4310437 := bbase (se 4 (by rfl) ⟨404103, by rfl⟩ : syracuseStep 4310437 = 808207) (by norm_num)
theorem B2360741 : Blo 1572484 2360741 := bbase (se 4 (by rfl) ⟨221319, by rfl⟩ : syracuseStep 2360741 = 442639) (by norm_num)
theorem B1992109 : Blo 1572484 1992109 := bbase (se 3 (by rfl) ⟨373520, by rfl⟩ : syracuseStep 1992109 = 747041) (by norm_num)
theorem B1770925 : Blo 1572484 1770925 := bbase (se 3 (by rfl) ⟨332048, by rfl⟩ : syracuseStep 1770925 = 664097) (by norm_num)
theorem B4482485 : Blo 1572484 4482485 := bbase (se 5 (by rfl) ⟨210116, by rfl⟩ : syracuseStep 4482485 = 420233) (by norm_num)
theorem B2360765 : Blo 1572484 2360765 := bbase (se 3 (by rfl) ⟨442643, by rfl⟩ : syracuseStep 2360765 = 885287) (by norm_num)
theorem B1770961 : Blo 1572484 1770961 := bbase (se 2 (by rfl) ⟨664110, by rfl⟩ : syracuseStep 1770961 = 1328221) (by norm_num)
theorem B3540437 : Blo 1572484 3540437 := bbase (se 7 (by rfl) ⟨41489, by rfl⟩ : syracuseStep 3540437 = 82979) (by norm_num)
theorem B15123925 : Blo 1572484 15123925 := bbase (se 7 (by rfl) ⟨177233, by rfl⟩ : syracuseStep 15123925 = 354467) (by norm_num)
theorem B2360789 : Blo 1572484 2360789 := bbase (se 7 (by rfl) ⟨27665, by rfl⟩ : syracuseStep 2360789 = 55331) (by norm_num)
theorem B2360813 : Blo 1572484 2360813 := bbase (se 3 (by rfl) ⟨442652, by rfl⟩ : syracuseStep 2360813 = 885305) (by norm_num)
theorem B2655733 : Blo 1572484 2655733 := bbase (se 5 (by rfl) ⟨124487, by rfl⟩ : syracuseStep 2655733 = 248975) (by norm_num)
theorem B1770997 : Blo 1572484 1770997 := bbase (se 5 (by rfl) ⟨83015, by rfl⟩ : syracuseStep 1770997 = 166031) (by norm_num)
theorem B2360837 : Blo 1572484 2360837 := bbase (se 4 (by rfl) ⟨221328, by rfl⟩ : syracuseStep 2360837 = 442657) (by norm_num)
theorem B1992205 : Blo 1572484 1992205 := bbase (se 3 (by rfl) ⟨373538, by rfl⟩ : syracuseStep 1992205 = 747077) (by norm_num)
theorem B1771033 : Blo 1572484 1771033 := bbase (se 2 (by rfl) ⟨664137, by rfl⟩ : syracuseStep 1771033 = 1328275) (by norm_num)
theorem B3540509 : Blo 1572484 3540509 := bbase (se 3 (by rfl) ⟨663845, by rfl⟩ : syracuseStep 3540509 = 1327691) (by norm_num)
theorem B2360861 : Blo 1572484 2360861 := bbase (se 3 (by rfl) ⟨442661, by rfl⟩ : syracuseStep 2360861 = 885323) (by norm_num)
theorem B6809141 : Blo 1572484 6809141 := bbase (se 5 (by rfl) ⟨319178, by rfl⟩ : syracuseStep 6809141 = 638357) (by norm_num)
theorem B2360885 : Blo 1572484 2360885 := bbase (se 5 (by rfl) ⟨110666, by rfl⟩ : syracuseStep 2360885 = 221333) (by norm_num)
theorem B1680949 : Blo 1572484 1680949 := bbase (se 5 (by rfl) ⟨78794, by rfl⟩ : syracuseStep 1680949 = 157589) (by norm_num)
theorem B1771069 : Blo 1572484 1771069 := bbase (se 3 (by rfl) ⟨332075, by rfl⟩ : syracuseStep 1771069 = 664151) (by norm_num)
theorem B2655821 : Blo 1572484 2655821 := bbase (se 3 (by rfl) ⟨497966, by rfl⟩ : syracuseStep 2655821 = 995933) (by norm_num)
theorem B2360909 : Blo 1572484 2360909 := bbase (se 3 (by rfl) ⟨442670, by rfl⟩ : syracuseStep 2360909 = 885341) (by norm_num)
theorem B23004757 : Blo 1572484 23004757 := bbase (se 8 (by rfl) ⟨134793, by rfl⟩ : syracuseStep 23004757 = 269587) (by norm_num)
theorem B1771105 : Blo 1572484 1771105 := bbase (se 2 (by rfl) ⟨664164, by rfl⟩ : syracuseStep 1771105 = 1328329) (by norm_num)
theorem B3540581 : Blo 1572484 3540581 := bbase (se 4 (by rfl) ⟨331929, by rfl⟩ : syracuseStep 3540581 = 663859) (by norm_num)
theorem B2360933 : Blo 1572484 2360933 := bbase (se 4 (by rfl) ⟨221337, by rfl⟩ : syracuseStep 2360933 = 442675) (by norm_num)
theorem B2360957 : Blo 1572484 2360957 := bbase (se 3 (by rfl) ⟨442679, by rfl⟩ : syracuseStep 2360957 = 885359) (by norm_num)
theorem B1771141 : Blo 1572484 1771141 := bbase (se 4 (by rfl) ⟨166044, by rfl⟩ : syracuseStep 1771141 = 332089) (by norm_num)
theorem B2360981 : Blo 1572484 2360981 := bbase (se 6 (by rfl) ⟨55335, by rfl⟩ : syracuseStep 2360981 = 110671) (by norm_num)
theorem B2393749 : Blo 1572484 2393749 := bbase (se 6 (by rfl) ⟨56103, by rfl⟩ : syracuseStep 2393749 = 112207) (by norm_num)
theorem B1771177 : Blo 1572484 1771177 := bbase (se 2 (by rfl) ⟨664191, by rfl⟩ : syracuseStep 1771177 = 1328383) (by norm_num)
theorem B3540653 : Blo 1572484 3540653 := bbase (se 3 (by rfl) ⟨663872, by rfl⟩ : syracuseStep 3540653 = 1327745) (by norm_num)
theorem B2361005 : Blo 1572484 2361005 := bbase (se 3 (by rfl) ⟨442688, by rfl⟩ : syracuseStep 2361005 = 885377) (by norm_num)
theorem B1992377 : Blo 1572484 1992377 := bbase (se 2 (by rfl) ⟨747141, by rfl⟩ : syracuseStep 1992377 = 1494283) (by norm_num)
theorem B2361029 : Blo 1572484 2361029 := bbase (se 4 (by rfl) ⟨221346, by rfl⟩ : syracuseStep 2361029 = 442693) (by norm_num)
theorem B3983053 : Blo 1572484 3983053 := bbase (se 3 (by rfl) ⟨746822, by rfl⟩ : syracuseStep 3983053 = 1493645) (by norm_num)
theorem B2655949 : Blo 1572484 2655949 := bbase (se 3 (by rfl) ⟨497990, by rfl⟩ : syracuseStep 2655949 = 995981) (by norm_num)
theorem B1771213 : Blo 1572484 1771213 := bbase (se 3 (by rfl) ⟨332102, by rfl⟩ : syracuseStep 1771213 = 664205) (by norm_num)
theorem B9570005 : Blo 1572484 9570005 := bbase (se 7 (by rfl) ⟨112148, by rfl⟩ : syracuseStep 9570005 = 224297) (by norm_num)
theorem B2361053 : Blo 1572484 2361053 := bbase (se 3 (by rfl) ⟨442697, by rfl⟩ : syracuseStep 2361053 = 885395) (by norm_num)
theorem B1992433 : Blo 1572484 1992433 := bbase (se 2 (by rfl) ⟨747162, by rfl⟩ : syracuseStep 1992433 = 1494325) (by norm_num)
theorem B1771249 : Blo 1572484 1771249 := bbase (se 2 (by rfl) ⟨664218, by rfl⟩ : syracuseStep 1771249 = 1328437) (by norm_num)
theorem B7964405 : Blo 1572484 7964405 := bbase (se 5 (by rfl) ⟨373331, by rfl⟩ : syracuseStep 7964405 = 746663) (by norm_num)
theorem B5310197 : Blo 1572484 5310197 := bbase (se 5 (by rfl) ⟨248915, by rfl⟩ : syracuseStep 5310197 = 497831) (by norm_num)
theorem B3540725 : Blo 1572484 3540725 := bbase (se 5 (by rfl) ⟨165971, by rfl⟩ : syracuseStep 3540725 = 331943) (by norm_num)
theorem B2361077 : Blo 1572484 2361077 := bbase (se 5 (by rfl) ⟨110675, by rfl⟩ : syracuseStep 2361077 = 221351) (by norm_num)
theorem B2361101 : Blo 1572484 2361101 := bbase (se 3 (by rfl) ⟨442706, by rfl⟩ : syracuseStep 2361101 = 885413) (by norm_num)
theorem B1771285 : Blo 1572484 1771285 := bbase (se 6 (by rfl) ⟨41514, by rfl⟩ : syracuseStep 1771285 = 83029) (by norm_num)
theorem B2656037 : Blo 1572484 2656037 := bbase (se 4 (by rfl) ⟨249003, by rfl⟩ : syracuseStep 2656037 = 498007) (by norm_num)
theorem B2361125 : Blo 1572484 2361125 := bbase (se 4 (by rfl) ⟨221355, by rfl⟩ : syracuseStep 2361125 = 442711) (by norm_num)
theorem B3360565 : Blo 1572484 3360565 := bbase (se 5 (by rfl) ⟨157526, by rfl⟩ : syracuseStep 3360565 = 315053) (by norm_num)
theorem B3983165 : Blo 1572484 3983165 := bbase (se 3 (by rfl) ⟨746843, by rfl⟩ : syracuseStep 3983165 = 1493687) (by norm_num)
theorem B3540797 : Blo 1572484 3540797 := bbase (se 3 (by rfl) ⟨663899, by rfl⟩ : syracuseStep 3540797 = 1327799) (by norm_num)
theorem B2361149 : Blo 1572484 2361149 := bbase (se 3 (by rfl) ⟨442715, by rfl⟩ : syracuseStep 2361149 = 885431) (by norm_num)
theorem B1992529 : Blo 1572484 1992529 := bbase (se 2 (by rfl) ⟨747198, by rfl⟩ : syracuseStep 1992529 = 1494397) (by norm_num)
theorem B2361173 : Blo 1572484 2361173 := bbase (se 9 (by rfl) ⟨6917, by rfl⟩ : syracuseStep 2361173 = 13835) (by norm_num)
theorem B2361197 : Blo 1572484 2361197 := bbase (se 3 (by rfl) ⟨442724, by rfl⟩ : syracuseStep 2361197 = 885449) (by norm_num)
theorem B4786037 : Blo 1572484 4786037 := bbase (se 5 (by rfl) ⟨224345, by rfl⟩ : syracuseStep 4786037 = 448691) (by norm_num)
theorem B3540869 : Blo 1572484 3540869 := bbase (se 4 (by rfl) ⟨331956, by rfl⟩ : syracuseStep 3540869 = 663913) (by norm_num)
theorem B2361221 : Blo 1572484 2361221 := bbase (se 4 (by rfl) ⟨221364, by rfl⟩ : syracuseStep 2361221 = 442729) (by norm_num)
theorem B2361245 : Blo 1572484 2361245 := bbase (se 3 (by rfl) ⟨442733, by rfl⟩ : syracuseStep 2361245 = 885467) (by norm_num)
theorem B2656165 : Blo 1572484 2656165 := bbase (se 4 (by rfl) ⟨249015, by rfl⟩ : syracuseStep 2656165 = 498031) (by norm_num)
theorem B3360685 : Blo 1572484 3360685 := bbase (se 3 (by rfl) ⟨630128, by rfl⟩ : syracuseStep 3360685 = 1260257) (by norm_num)
theorem B2361269 : Blo 1572484 2361269 := bbase (se 5 (by rfl) ⟨110684, by rfl⟩ : syracuseStep 2361269 = 221369) (by norm_num)
theorem B3540941 : Blo 1572484 3540941 := bbase (se 3 (by rfl) ⟨663926, by rfl⟩ : syracuseStep 3540941 = 1327853) (by norm_num)
theorem B2361293 : Blo 1572484 2361293 := bbase (se 3 (by rfl) ⟨442742, by rfl⟩ : syracuseStep 2361293 = 885485) (by norm_num)
theorem B2361317 : Blo 1572484 2361317 := bbase (se 4 (by rfl) ⟨221373, by rfl⟩ : syracuseStep 2361317 = 442747) (by norm_num)
theorem B3983357 : Blo 1572484 3983357 := bbase (se 3 (by rfl) ⟨746879, by rfl⟩ : syracuseStep 3983357 = 1493759) (by norm_num)
theorem B2656253 : Blo 1572484 2656253 := bbase (se 3 (by rfl) ⟨498047, by rfl⟩ : syracuseStep 2656253 = 996095) (by norm_num)
theorem B2361341 : Blo 1572484 2361341 := bbase (se 3 (by rfl) ⟨442751, by rfl⟩ : syracuseStep 2361341 = 885503) (by norm_num)
theorem B1992701 : Blo 1572484 1992701 := bbase (se 3 (by rfl) ⟨373631, by rfl⟩ : syracuseStep 1992701 = 747263) (by norm_num)
theorem B3541013 : Blo 1572484 3541013 := bbase (se 6 (by rfl) ⟨82992, by rfl⟩ : syracuseStep 3541013 = 165985) (by norm_num)
theorem B2361365 : Blo 1572484 2361365 := bbase (se 6 (by rfl) ⟨55344, by rfl⟩ : syracuseStep 2361365 = 110689) (by norm_num)
theorem B2361389 : Blo 1572484 2361389 := bbase (se 3 (by rfl) ⟨442760, by rfl⟩ : syracuseStep 2361389 = 885521) (by norm_num)
theorem B5040181 : Blo 1572484 5040181 := bbase (se 5 (by rfl) ⟨236258, by rfl⟩ : syracuseStep 5040181 = 472517) (by norm_num)
theorem B2361413 : Blo 1572484 2361413 := bbase (se 4 (by rfl) ⟨221382, by rfl⟩ : syracuseStep 2361413 = 442765) (by norm_num)
theorem B3541085 : Blo 1572484 3541085 := bbase (se 3 (by rfl) ⟨663953, by rfl⟩ : syracuseStep 3541085 = 1327907) (by norm_num)
theorem B2361437 : Blo 1572484 2361437 := bbase (se 3 (by rfl) ⟨442769, by rfl⟩ : syracuseStep 2361437 = 885539) (by norm_num)
theorem B2361461 : Blo 1572484 2361461 := bbase (se 5 (by rfl) ⟨110693, by rfl⟩ : syracuseStep 2361461 = 221387) (by norm_num)
theorem B2656381 : Blo 1572484 2656381 := bbase (se 3 (by rfl) ⟨498071, by rfl⟩ : syracuseStep 2656381 = 996143) (by norm_num)
theorem B4540549 : Blo 1572484 4540549 := bbase (se 4 (by rfl) ⟨425676, by rfl⟩ : syracuseStep 4540549 = 851353) (by norm_num)
theorem B2361485 : Blo 1572484 2361485 := bbase (se 3 (by rfl) ⟨442778, by rfl⟩ : syracuseStep 2361485 = 885557) (by norm_num)
theorem B5310629 : Blo 1572484 5310629 := bbase (se 4 (by rfl) ⟨497871, by rfl⟩ : syracuseStep 5310629 = 995743) (by norm_num)
theorem B3541157 : Blo 1572484 3541157 := bbase (se 4 (by rfl) ⟨331983, by rfl⟩ : syracuseStep 3541157 = 663967) (by norm_num)
theorem B2361509 : Blo 1572484 2361509 := bbase (se 4 (by rfl) ⟨221391, by rfl⟩ : syracuseStep 2361509 = 442783) (by norm_num)
theorem B3360941 : Blo 1572484 3360941 := bbase (se 3 (by rfl) ⟨630176, by rfl⟩ : syracuseStep 3360941 = 1260353) (by norm_num)
theorem B2361533 : Blo 1572484 2361533 := bbase (se 3 (by rfl) ⟨442787, by rfl⟩ : syracuseStep 2361533 = 885575) (by norm_num)
theorem B2656469 : Blo 1572484 2656469 := bbase (se 7 (by rfl) ⟨31130, by rfl⟩ : syracuseStep 2656469 = 62261) (by norm_num)
theorem B2361557 : Blo 1572484 2361557 := bbase (se 7 (by rfl) ⟨27674, by rfl⟩ : syracuseStep 2361557 = 55349) (by norm_num)
theorem B3188965 : Blo 1572484 3188965 := bbase (se 4 (by rfl) ⟨298965, by rfl⟩ : syracuseStep 3188965 = 597931) (by norm_num)
theorem B3541229 : Blo 1572484 3541229 := bbase (se 3 (by rfl) ⟨663980, by rfl⟩ : syracuseStep 3541229 = 1327961) (by norm_num)
theorem B2361581 : Blo 1572484 2361581 := bbase (se 3 (by rfl) ⟨442796, by rfl⟩ : syracuseStep 2361581 = 885593) (by norm_num)
theorem B2361605 : Blo 1572484 2361605 := bbase (se 4 (by rfl) ⟨221400, by rfl⟩ : syracuseStep 2361605 = 442801) (by norm_num)
theorem B3778829 : Blo 1572484 3778829 := bbase (se 3 (by rfl) ⟨708530, by rfl⟩ : syracuseStep 3778829 = 1417061) (by norm_num)
theorem B2361629 : Blo 1572484 2361629 := bbase (se 3 (by rfl) ⟨442805, by rfl⟩ : syracuseStep 2361629 = 885611) (by norm_num)
theorem B3688741 : Blo 1572484 3688741 := bbase (se 4 (by rfl) ⟨345819, by rfl⟩ : syracuseStep 3688741 = 691639) (by norm_num)
theorem B3541301 : Blo 1572484 3541301 := bbase (se 5 (by rfl) ⟨165998, by rfl⟩ : syracuseStep 3541301 = 331997) (by norm_num)
theorem B2361653 : Blo 1572484 2361653 := bbase (se 5 (by rfl) ⟨110702, by rfl⟩ : syracuseStep 2361653 = 221405) (by norm_num)
theorem B2361677 : Blo 1572484 2361677 := bbase (se 3 (by rfl) ⟨442814, by rfl⟩ : syracuseStep 2361677 = 885629) (by norm_num)
theorem B3983701 : Blo 1572484 3983701 := bbase (se 10 (by rfl) ⟨5835, by rfl⟩ : syracuseStep 3983701 = 11671) (by norm_num)
theorem B2656597 : Blo 1572484 2656597 := bbase (se 10 (by rfl) ⟨3891, by rfl⟩ : syracuseStep 2656597 = 7783) (by norm_num)
theorem B2361701 : Blo 1572484 2361701 := bbase (se 4 (by rfl) ⟨221409, by rfl⟩ : syracuseStep 2361701 = 442819) (by norm_num)
theorem B3541373 : Blo 1572484 3541373 := bbase (se 3 (by rfl) ⟨664007, by rfl⟩ : syracuseStep 3541373 = 1328015) (by norm_num)
theorem B2361725 : Blo 1572484 2361725 := bbase (se 3 (by rfl) ⟨442823, by rfl⟩ : syracuseStep 2361725 = 885647) (by norm_num)
theorem B2656685 : Blo 1572484 2656685 := bbase (se 3 (by rfl) ⟨498128, by rfl⟩ : syracuseStep 2656685 = 996257) (by norm_num)
theorem B3983813 : Blo 1572484 3983813 := bbase (se 4 (by rfl) ⟨373482, by rfl⟩ : syracuseStep 3983813 = 746965) (by norm_num)
theorem B3541445 : Blo 1572484 3541445 := bbase (se 4 (by rfl) ⟨332010, by rfl⟩ : syracuseStep 3541445 = 664021) (by norm_num)
theorem B3541517 : Blo 1572484 3541517 := bbase (se 3 (by rfl) ⟨664034, by rfl⟩ : syracuseStep 3541517 = 1328069) (by norm_num)
theorem B2017813 : Blo 1572484 2017813 := bbase (se 6 (by rfl) ⟨47292, by rfl⟩ : syracuseStep 2017813 = 94585) (by norm_num)
theorem B2656813 : Blo 1572484 2656813 := bbase (se 3 (by rfl) ⟨498152, by rfl⟩ : syracuseStep 2656813 = 996305) (by norm_num)
theorem B5311061 : Blo 1572484 5311061 := bbase (se 8 (by rfl) ⟨31119, by rfl⟩ : syracuseStep 5311061 = 62239) (by norm_num)
theorem B3541589 : Blo 1572484 3541589 := bbase (se 8 (by rfl) ⟨20751, by rfl⟩ : syracuseStep 3541589 = 41503) (by norm_num)
theorem B3984005 : Blo 1572484 3984005 := bbase (se 4 (by rfl) ⟨373500, by rfl⟩ : syracuseStep 3984005 = 747001) (by norm_num)
theorem B2656901 : Blo 1572484 2656901 := bbase (se 4 (by rfl) ⟨249084, by rfl⟩ : syracuseStep 2656901 = 498169) (by norm_num)
theorem B3541661 : Blo 1572484 3541661 := bbase (se 3 (by rfl) ⟨664061, by rfl⟩ : syracuseStep 3541661 = 1328123) (by norm_num)
theorem B4254373 : Blo 1572484 4254373 := bbase (se 4 (by rfl) ⟨398847, by rfl⟩ : syracuseStep 4254373 = 797695) (by norm_num)
theorem B7277221 : Blo 1572484 7277221 := bbase (se 4 (by rfl) ⟨682239, by rfl⟩ : syracuseStep 7277221 = 1364479) (by norm_num)
theorem B21523157 : Blo 1572484 21523157 := bbase (se 7 (by rfl) ⟨252224, by rfl⟩ : syracuseStep 21523157 = 504449) (by norm_num)
theorem B3541733 : Blo 1572484 3541733 := bbase (se 4 (by rfl) ⟨332037, by rfl⟩ : syracuseStep 3541733 = 664075) (by norm_num)
theorem B3541805 : Blo 1572484 3541805 := bbase (se 3 (by rfl) ⟨664088, by rfl⟩ : syracuseStep 3541805 = 1328177) (by norm_num)
theorem B2018125 : Blo 1572484 2018125 := bbase (se 3 (by rfl) ⟨378398, by rfl⟩ : syracuseStep 2018125 = 756797) (by norm_num)
theorem B3541877 : Blo 1572484 3541877 := bbase (se 5 (by rfl) ⟨166025, by rfl⟩ : syracuseStep 3541877 = 332051) (by norm_num)
theorem B3541949 : Blo 1572484 3541949 := bbase (se 3 (by rfl) ⟨664115, by rfl⟩ : syracuseStep 3541949 = 1328231) (by norm_num)
theorem B3984349 : Blo 1572484 3984349 := bbase (se 3 (by rfl) ⟨747065, by rfl⟩ : syracuseStep 3984349 = 1494131) (by norm_num)
theorem B4090861 : Blo 1572484 4090861 := bbase (se 3 (by rfl) ⟨767036, by rfl⟩ : syracuseStep 4090861 = 1534073) (by norm_num)
theorem B7965701 : Blo 1572484 7965701 := bbase (se 4 (by rfl) ⟨746784, by rfl⟩ : syracuseStep 7965701 = 1493569) (by norm_num)
theorem B5311493 : Blo 1572484 5311493 := bbase (se 4 (by rfl) ⟨497952, by rfl⟩ : syracuseStep 5311493 = 995905) (by norm_num)
theorem B5385221 : Blo 1572484 5385221 := bbase (se 4 (by rfl) ⟨504864, by rfl⟩ : syracuseStep 5385221 = 1009729) (by norm_num)
theorem B3542021 : Blo 1572484 3542021 := bbase (se 4 (by rfl) ⟨332064, by rfl⟩ : syracuseStep 3542021 = 664129) (by norm_num)
theorem B3361829 : Blo 1572484 3361829 := bbase (se 4 (by rfl) ⟨315171, by rfl⟩ : syracuseStep 3361829 = 630343) (by norm_num)
theorem B3984461 : Blo 1572484 3984461 := bbase (se 3 (by rfl) ⟨747086, by rfl⟩ : syracuseStep 3984461 = 1494173) (by norm_num)
theorem B3542093 : Blo 1572484 3542093 := bbase (se 3 (by rfl) ⟨664142, by rfl⟩ : syracuseStep 3542093 = 1328285) (by norm_num)
theorem B3542165 : Blo 1572484 3542165 := bbase (se 6 (by rfl) ⟨83019, by rfl⟩ : syracuseStep 3542165 = 166039) (by norm_num)
theorem B3542237 : Blo 1572484 3542237 := bbase (se 3 (by rfl) ⟨664169, by rfl⟩ : syracuseStep 3542237 = 1328339) (by norm_num)
theorem B14355701 : Blo 1572484 14355701 := bbase (se 5 (by rfl) ⟨672923, by rfl⟩ : syracuseStep 14355701 = 1345847) (by norm_num)
theorem B3984653 : Blo 1572484 3984653 := bbase (se 3 (by rfl) ⟨747122, by rfl⟩ : syracuseStep 3984653 = 1494245) (by norm_num)
theorem B3362069 : Blo 1572484 3362069 := bbase (se 6 (by rfl) ⟨78798, by rfl⟩ : syracuseStep 3362069 = 157597) (by norm_num)
theorem B3542309 : Blo 1572484 3542309 := bbase (se 4 (by rfl) ⟨332091, by rfl⟩ : syracuseStep 3542309 = 664183) (by norm_num)
theorem B3935557 : Blo 1572484 3935557 := bbase (se 4 (by rfl) ⟨368958, by rfl⟩ : syracuseStep 3935557 = 737917) (by norm_num)
theorem B3542381 : Blo 1572484 3542381 := bbase (se 3 (by rfl) ⟨664196, by rfl⟩ : syracuseStep 3542381 = 1328393) (by norm_num)
theorem B5041541 : Blo 1572484 5041541 := bbase (se 4 (by rfl) ⟨472644, by rfl⟩ : syracuseStep 5041541 = 945289) (by norm_num)
theorem B5975477 : Blo 1572484 5975477 := bbase (se 5 (by rfl) ⟨280100, by rfl⟩ : syracuseStep 5975477 = 560201) (by norm_num)
theorem B5311925 : Blo 1572484 5311925 := bbase (se 5 (by rfl) ⟨248996, by rfl⟩ : syracuseStep 5311925 = 497993) (by norm_num)
theorem B3542453 : Blo 1572484 3542453 := bbase (se 5 (by rfl) ⟨166052, by rfl⟩ : syracuseStep 3542453 = 332105) (by norm_num)
theorem B2985437 : Blo 1572484 2985437 := bbase (se 3 (by rfl) ⟨559769, by rfl⟩ : syracuseStep 2985437 = 1119539) (by norm_num)
theorem B7556581 : Blo 1572484 7556581 := bbase (se 4 (by rfl) ⟨708429, by rfl⟩ : syracuseStep 7556581 = 1416859) (by norm_num)
theorem B3190261 : Blo 1572484 3190261 := bbase (se 5 (by rfl) ⟨149543, by rfl⟩ : syracuseStep 3190261 = 299087) (by norm_num)
theorem B3542525 : Blo 1572484 3542525 := bbase (se 3 (by rfl) ⟨664223, by rfl⟩ : syracuseStep 3542525 = 1328447) (by norm_num)
theorem B4312597 : Blo 1572484 4312597 := bbase (se 6 (by rfl) ⟨101076, by rfl⟩ : syracuseStep 4312597 = 202153) (by norm_num)
theorem B2125397 : Blo 1572484 2125397 := bbase (se 8 (by rfl) ⟨12453, by rfl⟩ : syracuseStep 2125397 = 24907) (by norm_num)
theorem B3984997 : Blo 1572484 3984997 := bbase (se 4 (by rfl) ⟨373593, by rfl⟩ : syracuseStep 3984997 = 747187) (by norm_num)
theorem B2985589 : Blo 1572484 2985589 := bbase (se 5 (by rfl) ⟨139949, by rfl⟩ : syracuseStep 2985589 = 279899) (by norm_num)
theorem B2240149 : Blo 1572484 2240149 := bbase (se 6 (by rfl) ⟨52503, by rfl⟩ : syracuseStep 2240149 = 105007) (by norm_num)
theorem B5975765 : Blo 1572484 5975765 := bbase (se 7 (by rfl) ⟨70028, by rfl⟩ : syracuseStep 5975765 = 140057) (by norm_num)
theorem B3985109 : Blo 1572484 3985109 := bbase (se 7 (by rfl) ⟨46700, by rfl⟩ : syracuseStep 3985109 = 93401) (by norm_num)
theorem B5385989 : Blo 1572484 5385989 := bbase (se 4 (by rfl) ⟨504936, by rfl⟩ : syracuseStep 5385989 = 1009873) (by norm_num)
theorem B3362573 : Blo 1572484 3362573 := bbase (se 3 (by rfl) ⟨630482, by rfl⟩ : syracuseStep 3362573 = 1260965) (by norm_num)
theorem B3362581 : Blo 1572484 3362581 := bbase (se 6 (by rfl) ⟨78810, by rfl⟩ : syracuseStep 3362581 = 157621) (by norm_num)
theorem B5312357 : Blo 1572484 5312357 := bbase (se 4 (by rfl) ⟨498033, by rfl⟩ : syracuseStep 5312357 = 996067) (by norm_num)
theorem B11956085 : Blo 1572484 11956085 := bbase (se 5 (by rfl) ⟨560441, by rfl⟩ : syracuseStep 11956085 = 1120883) (by norm_num)
theorem B3985301 : Blo 1572484 3985301 := bbase (se 6 (by rfl) ⟨93405, by rfl⟩ : syracuseStep 3985301 = 186811) (by norm_num)
theorem B2985893 : Blo 1572484 2985893 := bbase (se 4 (by rfl) ⟨279927, by rfl⟩ : syracuseStep 2985893 = 559855) (by norm_num)
theorem B3780589 : Blo 1572484 3780589 := bbase (se 3 (by rfl) ⟨708860, by rfl⟩ : syracuseStep 3780589 = 1417721) (by norm_num)
theorem B6721541 : Blo 1572484 6721541 := bbase (se 4 (by rfl) ⟨630144, by rfl⟩ : syracuseStep 6721541 = 1260289) (by norm_num)
theorem B5386261 : Blo 1572484 5386261 := bbase (se 6 (by rfl) ⟨126240, by rfl⟩ : syracuseStep 5386261 = 252481) (by norm_num)
theorem B2519117 : Blo 1572484 2519117 := bbase (se 3 (by rfl) ⟨472334, by rfl⟩ : syracuseStep 2519117 = 944669) (by norm_num)
theorem B6377669 : Blo 1572484 6377669 := bbase (se 4 (by rfl) ⟨597906, by rfl⟩ : syracuseStep 6377669 = 1195813) (by norm_num)
theorem B2019541 : Blo 1572484 2019541 := bbase (se 7 (by rfl) ⟨23666, by rfl⟩ : syracuseStep 2019541 = 47333) (by norm_num)
theorem B2240741 : Blo 1572484 2240741 := bbase (se 4 (by rfl) ⟨210069, by rfl⟩ : syracuseStep 2240741 = 420139) (by norm_num)
theorem B6377717 : Blo 1572484 6377717 := bbase (se 5 (by rfl) ⟨298955, by rfl⟩ : syracuseStep 6377717 = 597911) (by norm_num)
theorem B17920277 : Blo 1572484 17920277 := bbase (se 6 (by rfl) ⟨420006, by rfl⟩ : syracuseStep 17920277 = 840013) (by norm_num)
theorem B11948309 : Blo 1572484 11948309 := bbase (se 6 (by rfl) ⟨280038, by rfl⟩ : syracuseStep 11948309 = 560077) (by norm_num)
theorem B7966997 : Blo 1572484 7966997 := bbase (se 6 (by rfl) ⟨186726, by rfl⟩ : syracuseStep 7966997 = 373453) (by norm_num)
theorem B5312789 : Blo 1572484 5312789 := bbase (se 6 (by rfl) ⟨124518, by rfl⟩ : syracuseStep 5312789 = 249037) (by norm_num)
theorem B2240821 : Blo 1572484 2240821 := bbase (se 5 (by rfl) ⟨105038, by rfl⟩ : syracuseStep 2240821 = 210077) (by norm_num)
theorem B7565653 : Blo 1572484 7565653 := bbase (se 10 (by rfl) ⟨11082, by rfl⟩ : syracuseStep 7565653 = 22165) (by norm_num)
theorem B2126197 : Blo 1572484 2126197 := bbase (se 5 (by rfl) ⟨99665, by rfl⟩ : syracuseStep 2126197 = 199331) (by norm_num)
theorem B2240941 : Blo 1572484 2240941 := bbase (se 3 (by rfl) ⟨420176, by rfl⟩ : syracuseStep 2240941 = 840353) (by norm_num)
theorem B1749433 : Blo 1572484 1749433 := bbase (se 2 (by rfl) ⟨656037, by rfl⟩ : syracuseStep 1749433 = 1312075) (by norm_num)
theorem B2241037 : Blo 1572484 2241037 := bbase (se 3 (by rfl) ⟨420194, by rfl⟩ : syracuseStep 2241037 = 840389) (by norm_num)
theorem B2519629 : Blo 1572484 2519629 := bbase (se 3 (by rfl) ⟨472430, by rfl⟩ : syracuseStep 2519629 = 944861) (by norm_num)
theorem B3781205 : Blo 1572484 3781205 := bbase (se 8 (by rfl) ⟨22155, by rfl⟩ : syracuseStep 3781205 = 44311) (by norm_num)
theorem B2986645 : Blo 1572484 2986645 := bbase (se 6 (by rfl) ⟨69999, by rfl⟩ : syracuseStep 2986645 = 139999) (by norm_num)
theorem B5313221 : Blo 1572484 5313221 := bbase (se 4 (by rfl) ⟨498114, by rfl⟩ : syracuseStep 5313221 = 996229) (by norm_num)
theorem B2986789 : Blo 1572484 2986789 := bbase (se 4 (by rfl) ⟨280011, by rfl⟩ : syracuseStep 2986789 = 560023) (by norm_num)
theorem B3232613 : Blo 1572484 3232613 := bbase (se 4 (by rfl) ⟨303057, by rfl⟩ : syracuseStep 3232613 = 606115) (by norm_num)
theorem B1889141 : Blo 1572484 1889141 := bbase (se 5 (by rfl) ⟨88553, by rfl⟩ : syracuseStep 1889141 = 177107) (by norm_num)
theorem B5976949 : Blo 1572484 5976949 := bbase (se 5 (by rfl) ⟨280169, by rfl⟩ : syracuseStep 5976949 = 560339) (by norm_num)
theorem B2986949 : Blo 1572484 2986949 := bbase (se 4 (by rfl) ⟨280026, by rfl⟩ : syracuseStep 2986949 = 560053) (by norm_num)
theorem B1889257 : Blo 1572484 1889257 := bbase (se 2 (by rfl) ⟨708471, by rfl⟩ : syracuseStep 1889257 = 1416943) (by norm_num)
theorem B2241533 : Blo 1572484 2241533 := bbase (se 3 (by rfl) ⟨420287, by rfl⟩ : syracuseStep 2241533 = 840575) (by norm_num)
theorem B2520085 : Blo 1572484 2520085 := bbase (se 6 (by rfl) ⟨59064, by rfl⟩ : syracuseStep 2520085 = 118129) (by norm_num)
theorem B2987093 : Blo 1572484 2987093 := bbase (se 8 (by rfl) ⟨17502, by rfl⟩ : syracuseStep 2987093 = 35005) (by norm_num)
theorem B5313653 : Blo 1572484 5313653 := bbase (se 5 (by rfl) ⟨249077, by rfl⟩ : syracuseStep 5313653 = 498155) (by norm_num)
theorem B5747861 : Blo 1572484 5747861 := bbase (se 6 (by rfl) ⟨134715, by rfl⟩ : syracuseStep 5747861 = 269431) (by norm_num)
theorem B5977253 : Blo 1572484 5977253 := bbase (se 4 (by rfl) ⟨560367, by rfl⟩ : syracuseStep 5977253 = 1120735) (by norm_num)
theorem B1889453 : Blo 1572484 1889453 := bbase (se 3 (by rfl) ⟨354272, by rfl⟩ : syracuseStep 1889453 = 708545) (by norm_num)
theorem B1990757 : Blo 1572484 1990757 := bbase (se 4 (by rfl) ⟨186633, by rfl⟩ : syracuseStep 1990757 = 373267) (by norm_num)
theorem B3781973 : Blo 1572484 3781973 := bbase (se 13 (by rfl) ⟨692, by rfl⟩ : syracuseStep 3781973 = 1385) (by norm_num)
theorem B3781981 : Blo 1572484 3781981 := bbase (se 3 (by rfl) ⟨709121, by rfl⟩ : syracuseStep 3781981 = 1418243) (by norm_num)
theorem B2987381 : Blo 1572484 2987381 := bbase (se 5 (by rfl) ⟨140033, by rfl⟩ : syracuseStep 2987381 = 280067) (by norm_num)
theorem B2045345 : Blo 1572484 2045345 := bbase (se 2 (by rfl) ⟨767004, by rfl⟩ : syracuseStep 2045345 = 1534009) (by norm_num)
theorem B10221013 : Blo 1572484 10221013 := bbase (se 7 (by rfl) ⟨119777, by rfl⟩ : syracuseStep 10221013 = 239555) (by norm_num)
theorem B18175445 : Blo 1572484 18175445 := bbase (se 7 (by rfl) ⟨212993, by rfl⟩ : syracuseStep 18175445 = 425987) (by norm_num)
theorem B4478453 : Blo 1572484 4478453 := bbase (se 5 (by rfl) ⟨209927, by rfl⟩ : syracuseStep 4478453 = 419855) (by norm_num)
theorem B2987533 : Blo 1572484 2987533 := bbase (se 3 (by rfl) ⟨560162, by rfl⟩ : syracuseStep 2987533 = 1120325) (by norm_num)
theorem B1990813 : Blo 1572484 1990813 := bbase (se 3 (by rfl) ⟨373277, by rfl⟩ : syracuseStep 1990813 = 746555) (by norm_num)
theorem B7968293 : Blo 1572484 7968293 := bbase (se 4 (by rfl) ⟨747027, by rfl⟩ : syracuseStep 7968293 = 1494055) (by norm_num)
theorem B2520757 : Blo 1572484 2520757 := bbase (se 5 (by rfl) ⟨118160, by rfl⟩ : syracuseStep 2520757 = 236321) (by norm_num)
theorem B1890001 : Blo 1572484 1890001 := bbase (se 2 (by rfl) ⟨708750, by rfl⟩ : syracuseStep 1890001 = 1417501) (by norm_num)
theorem B6723317 : Blo 1572484 6723317 := bbase (se 5 (by rfl) ⟨315155, by rfl⟩ : syracuseStep 6723317 = 630311) (by norm_num)
theorem B2692885 : Blo 1572484 2692885 := bbase (se 6 (by rfl) ⟨63114, by rfl⟩ : syracuseStep 2692885 = 126229) (by norm_num)
theorem B2987837 : Blo 1572484 2987837 := bbase (se 3 (by rfl) ⟨560219, by rfl⟩ : syracuseStep 2987837 = 1120439) (by norm_num)
theorem B1890145 : Blo 1572484 1890145 := bbase (se 2 (by rfl) ⟨708804, by rfl⟩ : syracuseStep 1890145 = 1417609) (by norm_num)
theorem B4478885 : Blo 1572484 4478885 := bbase (se 4 (by rfl) ⟨419895, by rfl⟩ : syracuseStep 4478885 = 839791) (by norm_num)
theorem B6723557 : Blo 1572484 6723557 := bbase (se 4 (by rfl) ⟨630333, by rfl⟩ : syracuseStep 6723557 = 1260667) (by norm_num)
theorem B2521181 : Blo 1572484 2521181 := bbase (se 3 (by rfl) ⟨472721, by rfl⟩ : syracuseStep 2521181 = 945443) (by norm_num)
theorem B3782789 : Blo 1572484 3782789 := bbase (se 4 (by rfl) ⟨354636, by rfl⟩ : syracuseStep 3782789 = 709273) (by norm_num)
theorem B4036781 : Blo 1572484 4036781 := bbase (se 3 (by rfl) ⟨756896, by rfl⟩ : syracuseStep 4036781 = 1513793) (by norm_num)
theorem B1595597 : Blo 1572484 1595597 := bbase (se 3 (by rfl) ⟨299174, by rfl⟩ : syracuseStep 1595597 = 598349) (by norm_num)
theorem B3234125 : Blo 1572484 3234125 := bbase (se 3 (by rfl) ⟨606398, by rfl⟩ : syracuseStep 3234125 = 1212797) (by norm_num)
theorem B2521469 : Blo 1572484 2521469 := bbase (se 3 (by rfl) ⟨472775, by rfl⟩ : syracuseStep 2521469 = 945551) (by norm_num)
theorem B1595857 : Blo 1572484 1595857 := bbase (se 2 (by rfl) ⟨598446, by rfl⟩ : syracuseStep 1595857 = 1196893) (by norm_num)
theorem B2988589 : Blo 1572484 2988589 := bbase (se 3 (by rfl) ⟨560360, by rfl⟩ : syracuseStep 2988589 = 1120721) (by norm_num)
theorem B22682197 : Blo 1572484 22682197 := bbase (se 8 (by rfl) ⟨132903, by rfl⟩ : syracuseStep 22682197 = 265807) (by norm_num)
theorem B4479637 : Blo 1572484 4479637 := bbase (se 6 (by rfl) ⟨104991, by rfl⟩ : syracuseStep 4479637 = 209983) (by norm_num)
theorem B2988733 : Blo 1572484 2988733 := bbase (se 3 (by rfl) ⟨560387, by rfl⟩ : syracuseStep 2988733 = 1120775) (by norm_num)
theorem B4848325 : Blo 1572484 4848325 := bbase (se 4 (by rfl) ⟨454530, by rfl⟩ : syracuseStep 4848325 = 909061) (by norm_num)
theorem B10771157 : Blo 1572484 10771157 := bbase (se 7 (by rfl) ⟨126224, by rfl⟩ : syracuseStep 10771157 = 252449) (by norm_num)
theorem B4037357 : Blo 1572484 4037357 := bbase (se 3 (by rfl) ⟨757004, by rfl⟩ : syracuseStep 4037357 = 1514009) (by norm_num)
theorem B5307173 : Blo 1572484 5307173 := bbase (se 4 (by rfl) ⟨497547, by rfl⟩ : syracuseStep 5307173 = 995095) (by norm_num)
theorem B7969589 : Blo 1572484 7969589 := bbase (se 5 (by rfl) ⟨373574, by rfl⟩ : syracuseStep 7969589 = 747149) (by norm_num)
theorem B4037437 : Blo 1572484 4037437 := bbase (se 3 (by rfl) ⟨757019, by rfl⟩ : syracuseStep 4037437 = 1514039) (by norm_num)
theorem B2988893 : Blo 1572484 2988893 := bbase (se 3 (by rfl) ⟨560417, by rfl⟩ : syracuseStep 2988893 = 1120835) (by norm_num)
theorem B3406693 : Blo 1572484 3406693 := bbase (se 4 (by rfl) ⟨319377, by rfl⟩ : syracuseStep 3406693 = 638755) (by norm_num)
theorem B1891193 : Blo 1572484 1891193 := bbase (se 2 (by rfl) ⟨709197, by rfl⟩ : syracuseStep 1891193 = 1418395) (by norm_num)
theorem B11344789 : Blo 1572484 11344789 := bbase (se 6 (by rfl) ⟨265893, by rfl⟩ : syracuseStep 11344789 = 531787) (by norm_num)
theorem B4037597 : Blo 1572484 4037597 := bbase (se 3 (by rfl) ⟨757049, by rfl⟩ : syracuseStep 4037597 = 1514099) (by norm_num)
theorem B2989037 : Blo 1572484 2989037 := bbase (se 3 (by rfl) ⟨560444, by rfl⟩ : syracuseStep 2989037 = 1120889) (by norm_num)
theorem B3980461 : Blo 1572484 3980461 := bbase (se 3 (by rfl) ⟨746336, by rfl⟩ : syracuseStep 3980461 = 1492673) (by norm_num)
theorem B3538133 : Blo 1572484 3538133 := bbase (se 7 (by rfl) ⟨41462, by rfl⟩ : syracuseStep 3538133 = 82925) (by norm_num)
theorem B5307605 : Blo 1572484 5307605 := bbase (se 7 (by rfl) ⟨62198, by rfl⟩ : syracuseStep 5307605 = 124397) (by norm_num)
theorem B7961813 : Blo 1572484 7961813 := bbase (se 7 (by rfl) ⟨93302, by rfl⟩ : syracuseStep 7961813 = 186605) (by norm_num)
theorem B3538205 : Blo 1572484 3538205 := bbase (se 3 (by rfl) ⟨663413, by rfl⟩ : syracuseStep 3538205 = 1326827) (by norm_num)
theorem B3980573 : Blo 1572484 3980573 := bbase (se 3 (by rfl) ⟨746357, by rfl⟩ : syracuseStep 3980573 = 1492715) (by norm_num)
theorem B3538277 : Blo 1572484 3538277 := bbase (se 4 (by rfl) ⟨331713, by rfl⟩ : syracuseStep 3538277 = 663427) (by norm_num)
theorem B2653573 : Blo 1572484 2653573 := bbase (se 4 (by rfl) ⟨248772, by rfl⟩ : syracuseStep 2653573 = 497545) (by norm_num)
theorem B3538349 : Blo 1572484 3538349 := bbase (se 3 (by rfl) ⟨663440, by rfl⟩ : syracuseStep 3538349 = 1326881) (by norm_num)
theorem B8961461 : Blo 1572484 8961461 := bbase (se 5 (by rfl) ⟨420068, by rfl⟩ : syracuseStep 8961461 = 840137) (by norm_num)
theorem B2358749 : Blo 1572484 2358749 := bbase (se 3 (by rfl) ⟨442265, by rfl⟩ : syracuseStep 2358749 = 884531) (by norm_num)
theorem B2653661 : Blo 1572484 2653661 := bbase (se 3 (by rfl) ⟨497561, by rfl⟩ : syracuseStep 2653661 = 995123) (by norm_num)
theorem B3980765 : Blo 1572484 3980765 := bbase (se 3 (by rfl) ⟨746393, by rfl⟩ : syracuseStep 3980765 = 1492787) (by norm_num)
theorem B2358773 : Blo 1572484 2358773 := bbase (se 5 (by rfl) ⟨110567, by rfl⟩ : syracuseStep 2358773 = 221135) (by norm_num)
theorem B3538421 : Blo 1572484 3538421 := bbase (se 5 (by rfl) ⟨165863, by rfl⟩ : syracuseStep 3538421 = 331727) (by norm_num)
theorem B2358797 : Blo 1572484 2358797 := bbase (se 3 (by rfl) ⟨442274, by rfl⟩ : syracuseStep 2358797 = 884549) (by norm_num)
theorem B2358821 : Blo 1572484 2358821 := bbase (se 4 (by rfl) ⟨221139, by rfl⟩ : syracuseStep 2358821 = 442279) (by norm_num)
theorem B2358845 : Blo 1572484 2358845 := bbase (se 3 (by rfl) ⟨442283, by rfl⟩ : syracuseStep 2358845 = 884567) (by norm_num)
theorem B3538493 : Blo 1572484 3538493 := bbase (se 3 (by rfl) ⟨663467, by rfl⟩ : syracuseStep 3538493 = 1326935) (by norm_num)
theorem B2358869 : Blo 1572484 2358869 := bbase (se 8 (by rfl) ⟨13821, by rfl⟩ : syracuseStep 2358869 = 27643) (by norm_num)
theorem B1769053 : Blo 1572484 1769053 := bbase (se 3 (by rfl) ⟨331697, by rfl⟩ : syracuseStep 1769053 = 663395) (by norm_num)
theorem B2653789 : Blo 1572484 2653789 := bbase (se 3 (by rfl) ⟨497585, by rfl⟩ : syracuseStep 2653789 = 995171) (by norm_num)
theorem B3636829 : Blo 1572484 3636829 := bbase (se 3 (by rfl) ⟨681905, by rfl⟩ : syracuseStep 3636829 = 1363811) (by norm_num)
theorem B2358893 : Blo 1572484 2358893 := bbase (se 3 (by rfl) ⟨442292, by rfl⟩ : syracuseStep 2358893 = 884585) (by norm_num)
theorem B1990261 : Blo 1572484 1990261 := bbase (se 5 (by rfl) ⟨93293, by rfl⟩ : syracuseStep 1990261 = 186587) (by norm_num)
theorem B1769089 : Blo 1572484 1769089 := bbase (se 2 (by rfl) ⟨663408, by rfl⟩ : syracuseStep 1769089 = 1326817) (by norm_num)
theorem B2358917 : Blo 1572484 2358917 := bbase (se 4 (by rfl) ⟨221148, by rfl⟩ : syracuseStep 2358917 = 442297) (by norm_num)
theorem B3538565 : Blo 1572484 3538565 := bbase (se 4 (by rfl) ⟨331740, by rfl⟩ : syracuseStep 3538565 = 663481) (by norm_num)
theorem B5308037 : Blo 1572484 5308037 := bbase (se 4 (by rfl) ⟨497628, by rfl⟩ : syracuseStep 5308037 = 995257) (by norm_num)
theorem B5971589 : Blo 1572484 5971589 := bbase (se 4 (by rfl) ⟨559836, by rfl⟩ : syracuseStep 5971589 = 1119673) (by norm_num)
theorem B1793669 : Blo 1572484 1793669 := bbase (se 4 (by rfl) ⟨168156, by rfl⟩ : syracuseStep 1793669 = 336313) (by norm_num)
theorem B2358941 : Blo 1572484 2358941 := bbase (se 3 (by rfl) ⟨442301, by rfl⟩ : syracuseStep 2358941 = 884603) (by norm_num)
theorem B1769125 : Blo 1572484 1769125 := bbase (se 4 (by rfl) ⟨165855, by rfl⟩ : syracuseStep 1769125 = 331711) (by norm_num)
theorem B6053557 : Blo 1572484 6053557 := bbase (se 5 (by rfl) ⟨283760, by rfl⟩ : syracuseStep 6053557 = 567521) (by norm_num)
theorem B2358965 : Blo 1572484 2358965 := bbase (se 5 (by rfl) ⟨110576, by rfl⟩ : syracuseStep 2358965 = 221153) (by norm_num)
theorem B2653877 : Blo 1572484 2653877 := bbase (se 5 (by rfl) ⟨124400, by rfl⟩ : syracuseStep 2653877 = 248801) (by norm_num)
theorem B1769161 : Blo 1572484 1769161 := bbase (se 2 (by rfl) ⟨663435, by rfl⟩ : syracuseStep 1769161 = 1326871) (by norm_num)
theorem B2358989 : Blo 1572484 2358989 := bbase (se 3 (by rfl) ⟨442310, by rfl⟩ : syracuseStep 2358989 = 884621) (by norm_num)
theorem B3538637 : Blo 1572484 3538637 := bbase (se 3 (by rfl) ⟨663494, by rfl⟩ : syracuseStep 3538637 = 1326989) (by norm_num)
theorem B2359013 : Blo 1572484 2359013 := bbase (se 4 (by rfl) ⟨221157, by rfl⟩ : syracuseStep 2359013 = 442315) (by norm_num)
theorem B1769197 : Blo 1572484 1769197 := bbase (se 3 (by rfl) ⟨331724, by rfl⟩ : syracuseStep 1769197 = 663449) (by norm_num)
theorem B2359037 : Blo 1572484 2359037 := bbase (se 3 (by rfl) ⟨442319, by rfl⟩ : syracuseStep 2359037 = 884639) (by norm_num)
theorem B7560965 : Blo 1572484 7560965 := bbase (se 4 (by rfl) ⟨708840, by rfl⟩ : syracuseStep 7560965 = 1417681) (by norm_num)
theorem B6381317 : Blo 1572484 6381317 := bbase (se 4 (by rfl) ⟨598248, by rfl⟩ : syracuseStep 6381317 = 1196497) (by norm_num)
theorem B1769233 : Blo 1572484 1769233 := bbase (se 2 (by rfl) ⟨663462, by rfl⟩ : syracuseStep 1769233 = 1326925) (by norm_num)
theorem B6463253 : Blo 1572484 6463253 := bbase (se 6 (by rfl) ⟨151482, by rfl⟩ : syracuseStep 6463253 = 302965) (by norm_num)
theorem B2359061 : Blo 1572484 2359061 := bbase (se 6 (by rfl) ⟨55290, by rfl⟩ : syracuseStep 2359061 = 110581) (by norm_num)
theorem B3538709 : Blo 1572484 3538709 := bbase (se 6 (by rfl) ⟨82938, by rfl⟩ : syracuseStep 3538709 = 165877) (by norm_num)
theorem B1990433 : Blo 1572484 1990433 := bbase (se 2 (by rfl) ⟨746412, by rfl⟩ : syracuseStep 1990433 = 1492825) (by norm_num)
theorem B2359085 : Blo 1572484 2359085 := bbase (se 3 (by rfl) ⟨442328, by rfl⟩ : syracuseStep 2359085 = 884657) (by norm_num)
theorem B1769269 : Blo 1572484 1769269 := bbase (se 5 (by rfl) ⟨82934, by rfl⟩ : syracuseStep 1769269 = 165869) (by norm_num)
theorem B2654005 : Blo 1572484 2654005 := bbase (se 5 (by rfl) ⟨124406, by rfl⟩ : syracuseStep 2654005 = 248813) (by norm_num)
theorem B3981109 : Blo 1572484 3981109 := bbase (se 5 (by rfl) ⟨186614, by rfl⟩ : syracuseStep 3981109 = 373229) (by norm_num)
theorem B2834237 : Blo 1572484 2834237 := bbase (se 3 (by rfl) ⟨531419, by rfl⟩ : syracuseStep 2834237 = 1062839) (by norm_num)
theorem B2359109 : Blo 1572484 2359109 := bbase (se 4 (by rfl) ⟨221166, by rfl⟩ : syracuseStep 2359109 = 442333) (by norm_num)
theorem B6717269 : Blo 1572484 6717269 := bbase (se 9 (by rfl) ⟨19679, by rfl⟩ : syracuseStep 6717269 = 39359) (by norm_num)
theorem B3112789 : Blo 1572484 3112789 := bbase (se 9 (by rfl) ⟨9119, by rfl⟩ : syracuseStep 3112789 = 18239) (by norm_num)
theorem B1769305 : Blo 1572484 1769305 := bbase (se 2 (by rfl) ⟨663489, by rfl⟩ : syracuseStep 1769305 = 1326979) (by norm_num)
theorem B1990489 : Blo 1572484 1990489 := bbase (se 2 (by rfl) ⟨746433, by rfl⟩ : syracuseStep 1990489 = 1492867) (by norm_num)
theorem B2359133 : Blo 1572484 2359133 := bbase (se 3 (by rfl) ⟨442337, by rfl⟩ : syracuseStep 2359133 = 884675) (by norm_num)
theorem B3538781 : Blo 1572484 3538781 := bbase (se 3 (by rfl) ⟨663521, by rfl⟩ : syracuseStep 3538781 = 1327043) (by norm_num)
theorem B2359157 : Blo 1572484 2359157 := bbase (se 5 (by rfl) ⟨110585, by rfl⟩ : syracuseStep 2359157 = 221171) (by norm_num)
theorem B1769341 : Blo 1572484 1769341 := bbase (se 3 (by rfl) ⟨331751, by rfl⟩ : syracuseStep 1769341 = 663503) (by norm_num)
theorem B2359181 : Blo 1572484 2359181 := bbase (se 3 (by rfl) ⟨442346, by rfl⟩ : syracuseStep 2359181 = 884693) (by norm_num)
theorem B2654093 : Blo 1572484 2654093 := bbase (se 3 (by rfl) ⟨497642, by rfl⟩ : syracuseStep 2654093 = 995285) (by norm_num)
theorem B1679249 : Blo 1572484 1679249 := bbase (se 2 (by rfl) ⟨629718, by rfl⟩ : syracuseStep 1679249 = 1259437) (by norm_num)
theorem B24223637 : Blo 1572484 24223637 := bbase (se 6 (by rfl) ⟨567741, by rfl⟩ : syracuseStep 24223637 = 1135483) (by norm_num)
theorem B1769377 : Blo 1572484 1769377 := bbase (se 2 (by rfl) ⟨663516, by rfl⟩ : syracuseStep 1769377 = 1327033) (by norm_num)
theorem B5971877 : Blo 1572484 5971877 := bbase (se 4 (by rfl) ⟨559863, by rfl⟩ : syracuseStep 5971877 = 1119727) (by norm_num)
theorem B2359205 : Blo 1572484 2359205 := bbase (se 4 (by rfl) ⟨221175, by rfl⟩ : syracuseStep 2359205 = 442351) (by norm_num)
theorem B3538853 : Blo 1572484 3538853 := bbase (se 4 (by rfl) ⟨331767, by rfl⟩ : syracuseStep 3538853 = 663535) (by norm_num)
theorem B3981221 : Blo 1572484 3981221 := bbase (se 4 (by rfl) ⟨373239, by rfl⟩ : syracuseStep 3981221 = 746479) (by norm_num)
theorem B1990585 : Blo 1572484 1990585 := bbase (se 2 (by rfl) ⟨746469, by rfl⟩ : syracuseStep 1990585 = 1492939) (by norm_num)
theorem B2359229 : Blo 1572484 2359229 := bbase (se 3 (by rfl) ⟨442355, by rfl⟩ : syracuseStep 2359229 = 884711) (by norm_num)
theorem B1769413 : Blo 1572484 1769413 := bbase (se 4 (by rfl) ⟨165882, by rfl⟩ : syracuseStep 1769413 = 331765) (by norm_num)
theorem B2359253 : Blo 1572484 2359253 := bbase (se 7 (by rfl) ⟨27647, by rfl⟩ : syracuseStep 2359253 = 55295) (by norm_num)
theorem B1769449 : Blo 1572484 1769449 := bbase (se 2 (by rfl) ⟨663543, by rfl⟩ : syracuseStep 1769449 = 1327087) (by norm_num)
theorem B2359277 : Blo 1572484 2359277 := bbase (se 3 (by rfl) ⟨442364, by rfl⟩ : syracuseStep 2359277 = 884729) (by norm_num)
theorem B3538925 : Blo 1572484 3538925 := bbase (se 3 (by rfl) ⟨663548, by rfl⟩ : syracuseStep 3538925 = 1327097) (by norm_num)
theorem B1572867 : Blo 1572484 1572867 := bstep (se 1 (by rfl) ⟨1179650, by rfl⟩ : syracuseStep 1572867 = 2359301) B2359301
theorem B4481027 : Blo 1572484 4481027 := bstep (se 1 (by rfl) ⟨3360770, by rfl⟩ : syracuseStep 4481027 = 6721541) B6721541
theorem B3538961 : Blo 1572484 3538961 := bstep (se 2 (by rfl) ⟨1327110, by rfl⟩ : syracuseStep 3538961 = 2654221) B2654221
theorem B2359313 : Blo 1572484 2359313 := bstep (se 2 (by rfl) ⟨884742, by rfl⟩ : syracuseStep 2359313 = 1769485) B1769485
theorem B1572883 : Blo 1572484 1572883 := bstep (se 1 (by rfl) ⟨1179662, by rfl⟩ : syracuseStep 1572883 = 2359325) B2359325
theorem B3538979 : Blo 1572484 3538979 := bstep (se 1 (by rfl) ⟨2654234, by rfl⟩ : syracuseStep 3538979 = 5308469) B5308469
theorem B2359331 : Blo 1572484 2359331 := bstep (se 1 (by rfl) ⟨1769498, by rfl⟩ : syracuseStep 2359331 = 3538997) B3538997
theorem B1572899 : Blo 1572484 1572899 := bstep (se 1 (by rfl) ⟨1179674, by rfl⟩ : syracuseStep 1572899 = 2359349) B2359349
theorem B1679411 : Blo 1572484 1679411 := bstep (se 1 (by rfl) ⟨1259558, by rfl⟩ : syracuseStep 1679411 = 2519117) B2519117
theorem B1572915 : Blo 1572484 1572915 := bstep (se 1 (by rfl) ⟨1179686, by rfl⟩ : syracuseStep 1572915 = 2359373) B2359373
theorem B2359361 : Blo 1572484 2359361 := bstep (se 2 (by rfl) ⟨884760, by rfl⟩ : syracuseStep 2359361 = 1769521) B1769521
theorem B2654275 : Blo 1572484 2654275 := bstep (se 1 (by rfl) ⟨1990706, by rfl⟩ : syracuseStep 2654275 = 3981413) B3981413
theorem B1769539 : Blo 1572484 1769539 := bstep (se 1 (by rfl) ⟨1327154, by rfl⟩ : syracuseStep 1769539 = 2654309) B2654309
theorem B1572931 : Blo 1572484 1572931 := bstep (se 1 (by rfl) ⟨1179698, by rfl⟩ : syracuseStep 1572931 = 2359397) B2359397
theorem B11952197 : Blo 1572484 11952197 := bstep (se 4 (by rfl) ⟨1120518, by rfl⟩ : syracuseStep 11952197 = 2241037) B2241037
theorem B2359379 : Blo 1572484 2359379 := bstep (se 1 (by rfl) ⟨1769534, by rfl⟩ : syracuseStep 2359379 = 3539069) B3539069
theorem B1572947 : Blo 1572484 1572947 := bstep (se 1 (by rfl) ⟨1179710, by rfl⟩ : syracuseStep 1572947 = 2359421) B2359421
theorem B1572963 : Blo 1572484 1572963 := bstep (se 1 (by rfl) ⟨1179722, by rfl⟩ : syracuseStep 1572963 = 2359445) B2359445
theorem B2359409 : Blo 1572484 2359409 := bstep (se 2 (by rfl) ⟨884778, by rfl⟩ : syracuseStep 2359409 = 1769557) B1769557
theorem B1572979 : Blo 1572484 1572979 := bstep (se 1 (by rfl) ⟨1179734, by rfl⟩ : syracuseStep 1572979 = 2359469) B2359469
theorem B2359427 : Blo 1572484 2359427 := bstep (se 1 (by rfl) ⟨1769570, by rfl⟩ : syracuseStep 2359427 = 3539141) B3539141
theorem B4251779 : Blo 1572484 4251779 := bstep (se 1 (by rfl) ⟨3188834, by rfl⟩ : syracuseStep 4251779 = 6377669) B6377669
theorem B1572995 : Blo 1572484 1572995 := bstep (se 1 (by rfl) ⟨1179746, by rfl⟩ : syracuseStep 1572995 = 2359493) B2359493
theorem B1573011 : Blo 1572484 1573011 := bstep (se 1 (by rfl) ⟨1179758, by rfl⟩ : syracuseStep 1573011 = 2359517) B2359517
theorem B3358883 : Blo 1572484 3358883 := bstep (se 1 (by rfl) ⟨2519162, by rfl⟩ : syracuseStep 3358883 = 5038325) B5038325
theorem B4251811 : Blo 1572484 4251811 := bstep (se 1 (by rfl) ⟨3188858, by rfl⟩ : syracuseStep 4251811 = 6377717) B6377717
theorem B2359457 : Blo 1572484 2359457 := bstep (se 2 (by rfl) ⟨884796, by rfl⟩ : syracuseStep 2359457 = 1769593) B1769593
theorem B1573027 : Blo 1572484 1573027 := bstep (se 1 (by rfl) ⟨1179770, by rfl⟩ : syracuseStep 1573027 = 2359541) B2359541
theorem B6054065 : Blo 1572484 6054065 := bstep (se 2 (by rfl) ⟨2270274, by rfl⟩ : syracuseStep 6054065 = 4540549) B4540549
theorem B2359475 : Blo 1572484 2359475 := bstep (se 1 (by rfl) ⟨1769606, by rfl⟩ : syracuseStep 2359475 = 3539213) B3539213
theorem B1573043 : Blo 1572484 1573043 := bstep (se 1 (by rfl) ⟨1179782, by rfl⟩ : syracuseStep 1573043 = 2359565) B2359565
theorem B1573059 : Blo 1572484 1573059 := bstep (se 1 (by rfl) ⟨1179794, by rfl⟩ : syracuseStep 1573059 = 2359589) B2359589
theorem B2654417 : Blo 1572484 2654417 := bstep (se 2 (by rfl) ⟨995406, by rfl⟩ : syracuseStep 2654417 = 1990813) B1990813
theorem B2359505 : Blo 1572484 2359505 := bstep (se 2 (by rfl) ⟨884814, by rfl⟩ : syracuseStep 2359505 = 1769629) B1769629
theorem B1769683 : Blo 1572484 1769683 := bstep (se 1 (by rfl) ⟨1327262, by rfl⟩ : syracuseStep 1769683 = 2654525) B2654525
theorem B1573075 : Blo 1572484 1573075 := bstep (se 1 (by rfl) ⟨1179806, by rfl⟩ : syracuseStep 1573075 = 2359613) B2359613
theorem B4480913 : Blo 1572484 4480913 := bstep (se 2 (by rfl) ⟨1680342, by rfl⟩ : syracuseStep 4480913 = 3360685) B3360685
theorem B2359523 : Blo 1572484 2359523 := bstep (se 1 (by rfl) ⟨1769642, by rfl⟩ : syracuseStep 2359523 = 3539285) B3539285
theorem B1573091 : Blo 1572484 1573091 := bstep (se 1 (by rfl) ⟨1179818, by rfl⟩ : syracuseStep 1573091 = 2359637) B2359637
theorem B1573107 : Blo 1572484 1573107 := bstep (se 1 (by rfl) ⟨1179830, by rfl⟩ : syracuseStep 1573107 = 2359661) B2359661
theorem B2359553 : Blo 1572484 2359553 := bstep (se 2 (by rfl) ⟨884832, by rfl⟩ : syracuseStep 2359553 = 1769665) B1769665
theorem B1573123 : Blo 1572484 1573123 := bstep (se 1 (by rfl) ⟨1179842, by rfl⟩ : syracuseStep 1573123 = 2359685) B2359685
theorem B5308685 : Blo 1572484 5308685 := bstep (se 3 (by rfl) ⟨995378, by rfl⟩ : syracuseStep 5308685 = 1990757) B1990757
theorem B2359571 : Blo 1572484 2359571 := bstep (se 1 (by rfl) ⟨1769678, by rfl⟩ : syracuseStep 2359571 = 3539357) B3539357
theorem B1573139 : Blo 1572484 1573139 := bstep (se 1 (by rfl) ⟨1179854, by rfl⟩ : syracuseStep 1573139 = 2359709) B2359709
theorem B1573155 : Blo 1572484 1573155 := bstep (se 1 (by rfl) ⟨1179866, by rfl⟩ : syracuseStep 1573155 = 2359733) B2359733
theorem B3539249 : Blo 1572484 3539249 := bstep (se 2 (by rfl) ⟨1327218, by rfl⟩ : syracuseStep 3539249 = 2654437) B2654437
theorem B4251953 : Blo 1572484 4251953 := bstep (se 2 (by rfl) ⟨1594482, by rfl⟩ : syracuseStep 4251953 = 3188965) B3188965
theorem B2359601 : Blo 1572484 2359601 := bstep (se 2 (by rfl) ⟨884850, by rfl⟩ : syracuseStep 2359601 = 1769701) B1769701
theorem B1573171 : Blo 1572484 1573171 := bstep (se 1 (by rfl) ⟨1179878, by rfl⟩ : syracuseStep 1573171 = 2359757) B2359757
theorem B5308739 : Blo 1572484 5308739 := bstep (se 1 (by rfl) ⟨3981554, by rfl⟩ : syracuseStep 5308739 = 7963109) B7963109
theorem B3539267 : Blo 1572484 3539267 := bstep (se 1 (by rfl) ⟨2654450, by rfl⟩ : syracuseStep 3539267 = 5308901) B5308901
theorem B2359619 : Blo 1572484 2359619 := bstep (se 1 (by rfl) ⟨1769714, by rfl⟩ : syracuseStep 2359619 = 3539429) B3539429
theorem B1573187 : Blo 1572484 1573187 := bstep (se 1 (by rfl) ⟨1179890, by rfl⟩ : syracuseStep 1573187 = 2359781) B2359781
theorem B2654545 : Blo 1572484 2654545 := bstep (se 2 (by rfl) ⟨995454, by rfl⟩ : syracuseStep 2654545 = 1990909) B1990909
theorem B1573203 : Blo 1572484 1573203 := bstep (se 1 (by rfl) ⟨1179902, by rfl⟩ : syracuseStep 1573203 = 2359805) B2359805
theorem B2359649 : Blo 1572484 2359649 := bstep (se 2 (by rfl) ⟨884868, by rfl⟩ : syracuseStep 2359649 = 1769737) B1769737
theorem B1769827 : Blo 1572484 1769827 := bstep (se 1 (by rfl) ⟨1327370, by rfl⟩ : syracuseStep 1769827 = 2654741) B2654741
theorem B1573219 : Blo 1572484 1573219 := bstep (se 1 (by rfl) ⟨1179914, by rfl⟩ : syracuseStep 1573219 = 2359829) B2359829
theorem B2654579 : Blo 1572484 2654579 := bstep (se 1 (by rfl) ⟨1990934, by rfl⟩ : syracuseStep 2654579 = 3981869) B3981869
theorem B2359667 : Blo 1572484 2359667 := bstep (se 1 (by rfl) ⟨1769750, by rfl⟩ : syracuseStep 2359667 = 3539501) B3539501
theorem B1573235 : Blo 1572484 1573235 := bstep (se 1 (by rfl) ⟨1179926, by rfl⟩ : syracuseStep 1573235 = 2359853) B2359853
theorem B2589059 : Blo 1572484 2589059 := bstep (se 1 (by rfl) ⟨1941794, by rfl⟩ : syracuseStep 2589059 = 3883589) B3883589
theorem B1573251 : Blo 1572484 1573251 := bstep (se 1 (by rfl) ⟨1179938, by rfl⟩ : syracuseStep 1573251 = 2359877) B2359877
theorem B2359697 : Blo 1572484 2359697 := bstep (se 2 (by rfl) ⟨884886, by rfl⟩ : syracuseStep 2359697 = 1769773) B1769773
theorem B1573267 : Blo 1572484 1573267 := bstep (se 1 (by rfl) ⟨1179950, by rfl⟩ : syracuseStep 1573267 = 2359901) B2359901
theorem B2359715 : Blo 1572484 2359715 := bstep (se 1 (by rfl) ⟨1769786, by rfl⟩ : syracuseStep 2359715 = 3539573) B3539573
theorem B1573283 : Blo 1572484 1573283 := bstep (se 1 (by rfl) ⟨1179962, by rfl⟩ : syracuseStep 1573283 = 2359925) B2359925
theorem B1573299 : Blo 1572484 1573299 := bstep (se 1 (by rfl) ⟨1179974, by rfl⟩ : syracuseStep 1573299 = 2359949) B2359949
theorem B2359745 : Blo 1572484 2359745 := bstep (se 2 (by rfl) ⟨884904, by rfl⟩ : syracuseStep 2359745 = 1769809) B1769809
theorem B1573315 : Blo 1572484 1573315 := bstep (se 1 (by rfl) ⟨1179986, by rfl⟩ : syracuseStep 1573315 = 2359973) B2359973
theorem B5038541 : Blo 1572484 5038541 := bstep (se 3 (by rfl) ⟨944726, by rfl⟩ : syracuseStep 5038541 = 1889453) B1889453
theorem B2359763 : Blo 1572484 2359763 := bstep (se 1 (by rfl) ⟨1769822, by rfl⟩ : syracuseStep 2359763 = 3539645) B3539645
theorem B1573331 : Blo 1572484 1573331 := bstep (se 1 (by rfl) ⟨1179998, by rfl⟩ : syracuseStep 1573331 = 2359997) B2359997
theorem B20431331 : Blo 1572484 20431331 := bstep (se 1 (by rfl) ⟨15323498, by rfl⟩ : syracuseStep 20431331 = 30646997) B30646997
theorem B1573347 : Blo 1572484 1573347 := bstep (se 1 (by rfl) ⟨1180010, by rfl⟩ : syracuseStep 1573347 = 2360021) B2360021
theorem B5177837 : Blo 1572484 5177837 := bstep (se 3 (by rfl) ⟨970844, by rfl⟩ : syracuseStep 5177837 = 1941689) B1941689
theorem B2834929 : Blo 1572484 2834929 := bstep (se 2 (by rfl) ⟨1063098, by rfl⟩ : syracuseStep 2834929 = 2126197) B2126197
theorem B2359793 : Blo 1572484 2359793 := bstep (se 2 (by rfl) ⟨884922, by rfl⟩ : syracuseStep 2359793 = 1769845) B1769845
theorem B2654707 : Blo 1572484 2654707 := bstep (se 1 (by rfl) ⟨1991030, by rfl⟩ : syracuseStep 2654707 = 3982061) B3982061
theorem B1769971 : Blo 1572484 1769971 := bstep (se 1 (by rfl) ⟨1327478, by rfl⟩ : syracuseStep 1769971 = 2654957) B2654957
theorem B1573363 : Blo 1572484 1573363 := bstep (se 1 (by rfl) ⟨1180022, by rfl⟩ : syracuseStep 1573363 = 2360045) B2360045
theorem B2359811 : Blo 1572484 2359811 := bstep (se 1 (by rfl) ⟨1769858, by rfl⟩ : syracuseStep 2359811 = 3539717) B3539717
theorem B1573379 : Blo 1572484 1573379 := bstep (se 1 (by rfl) ⟨1180034, by rfl⟩ : syracuseStep 1573379 = 2360069) B2360069
theorem B1573395 : Blo 1572484 1573395 := bstep (se 1 (by rfl) ⟨1180046, by rfl⟩ : syracuseStep 1573395 = 2360093) B2360093
theorem B2359841 : Blo 1572484 2359841 := bstep (se 2 (by rfl) ⟨884940, by rfl⟩ : syracuseStep 2359841 = 1769881) B1769881
theorem B1573411 : Blo 1572484 1573411 := bstep (se 1 (by rfl) ⟨1180058, by rfl⟩ : syracuseStep 1573411 = 2360117) B2360117
theorem B2359859 : Blo 1572484 2359859 := bstep (se 1 (by rfl) ⟨1769894, by rfl⟩ : syracuseStep 2359859 = 3539789) B3539789
theorem B1573427 : Blo 1572484 1573427 := bstep (se 1 (by rfl) ⟨1180070, by rfl⟩ : syracuseStep 1573427 = 2360141) B2360141
theorem B2155075 : Blo 1572484 2155075 := bstep (se 1 (by rfl) ⟨1616306, by rfl⟩ : syracuseStep 2155075 = 3232613) B3232613
theorem B1573443 : Blo 1572484 1573443 := bstep (se 1 (by rfl) ⟨1180082, by rfl⟩ : syracuseStep 1573443 = 2360165) B2360165
theorem B5309009 : Blo 1572484 5309009 := bstep (se 2 (by rfl) ⟨1990878, by rfl⟩ : syracuseStep 5309009 = 3981757) B3981757
theorem B3539537 : Blo 1572484 3539537 := bstep (se 2 (by rfl) ⟨1327326, by rfl⟩ : syracuseStep 3539537 = 2654653) B2654653
theorem B2359889 : Blo 1572484 2359889 := bstep (se 2 (by rfl) ⟨884958, by rfl⟩ : syracuseStep 2359889 = 1769917) B1769917
theorem B1573459 : Blo 1572484 1573459 := bstep (se 1 (by rfl) ⟨1180094, by rfl⟩ : syracuseStep 1573459 = 2360189) B2360189
theorem B3539555 : Blo 1572484 3539555 := bstep (se 1 (by rfl) ⟨2654666, by rfl⟩ : syracuseStep 3539555 = 5309333) B5309333
theorem B2359907 : Blo 1572484 2359907 := bstep (se 1 (by rfl) ⟨1769930, by rfl⟩ : syracuseStep 2359907 = 3539861) B3539861
theorem B1573475 : Blo 1572484 1573475 := bstep (se 1 (by rfl) ⟨1180106, by rfl⟩ : syracuseStep 1573475 = 2360213) B2360213
theorem B2425457 : Blo 1572484 2425457 := bstep (se 2 (by rfl) ⟨909546, by rfl⟩ : syracuseStep 2425457 = 1819093) B1819093
theorem B1573491 : Blo 1572484 1573491 := bstep (se 1 (by rfl) ⟨1180118, by rfl⟩ : syracuseStep 1573491 = 2360237) B2360237
theorem B2654849 : Blo 1572484 2654849 := bstep (se 2 (by rfl) ⟨995568, by rfl⟩ : syracuseStep 2654849 = 1991137) B1991137
theorem B2359937 : Blo 1572484 2359937 := bstep (se 2 (by rfl) ⟨884976, by rfl⟩ : syracuseStep 2359937 = 1769953) B1769953
theorem B1991299 : Blo 1572484 1991299 := bstep (se 1 (by rfl) ⟨1493474, by rfl⟩ : syracuseStep 1991299 = 2986949) B2986949
theorem B1770115 : Blo 1572484 1770115 := bstep (se 1 (by rfl) ⟨1327586, by rfl⟩ : syracuseStep 1770115 = 2655173) B2655173
theorem B1573507 : Blo 1572484 1573507 := bstep (se 1 (by rfl) ⟨1180130, by rfl⟩ : syracuseStep 1573507 = 2360261) B2360261
theorem B2359955 : Blo 1572484 2359955 := bstep (se 1 (by rfl) ⟨1769966, by rfl⟩ : syracuseStep 2359955 = 3539933) B3539933
theorem B1573523 : Blo 1572484 1573523 := bstep (se 1 (by rfl) ⟨1180142, by rfl⟩ : syracuseStep 1573523 = 2360285) B2360285
theorem B1573539 : Blo 1572484 1573539 := bstep (se 1 (by rfl) ⟨1180154, by rfl⟩ : syracuseStep 1573539 = 2360309) B2360309
theorem B2359985 : Blo 1572484 2359985 := bstep (se 2 (by rfl) ⟨884994, by rfl⟩ : syracuseStep 2359985 = 1769989) B1769989
theorem B1573555 : Blo 1572484 1573555 := bstep (se 1 (by rfl) ⟨1180166, by rfl⟩ : syracuseStep 1573555 = 2360333) B2360333
theorem B2360003 : Blo 1572484 2360003 := bstep (se 1 (by rfl) ⟨1770002, by rfl⟩ : syracuseStep 2360003 = 3540005) B3540005
theorem B1573571 : Blo 1572484 1573571 := bstep (se 1 (by rfl) ⟨1180178, by rfl⟩ : syracuseStep 1573571 = 2360357) B2360357
theorem B1573587 : Blo 1572484 1573587 := bstep (se 1 (by rfl) ⟨1180190, by rfl⟩ : syracuseStep 1573587 = 2360381) B2360381
theorem B2360033 : Blo 1572484 2360033 := bstep (se 2 (by rfl) ⟨885012, by rfl⟩ : syracuseStep 2360033 = 1770025) B1770025
theorem B1991395 : Blo 1572484 1991395 := bstep (se 1 (by rfl) ⟨1493546, by rfl⟩ : syracuseStep 1991395 = 2987093) B2987093
theorem B1573603 : Blo 1572484 1573603 := bstep (se 1 (by rfl) ⟨1180202, by rfl⟩ : syracuseStep 1573603 = 2360405) B2360405
theorem B2360051 : Blo 1572484 2360051 := bstep (se 1 (by rfl) ⟨1770038, by rfl⟩ : syracuseStep 2360051 = 3540077) B3540077
theorem B1573619 : Blo 1572484 1573619 := bstep (se 1 (by rfl) ⟨1180214, by rfl⟩ : syracuseStep 1573619 = 2360429) B2360429
theorem B2654977 : Blo 1572484 2654977 := bstep (se 2 (by rfl) ⟨995616, by rfl⟩ : syracuseStep 2654977 = 1991233) B1991233
theorem B1573635 : Blo 1572484 1573635 := bstep (se 1 (by rfl) ⟨1180226, by rfl⟩ : syracuseStep 1573635 = 2360453) B2360453
theorem B2360081 : Blo 1572484 2360081 := bstep (se 2 (by rfl) ⟨885030, by rfl⟩ : syracuseStep 2360081 = 1770061) B1770061
theorem B1770259 : Blo 1572484 1770259 := bstep (se 1 (by rfl) ⟨1327694, by rfl⟩ : syracuseStep 1770259 = 2655389) B2655389
theorem B1573651 : Blo 1572484 1573651 := bstep (se 1 (by rfl) ⟨1180238, by rfl⟩ : syracuseStep 1573651 = 2360477) B2360477
theorem B2655011 : Blo 1572484 2655011 := bstep (se 1 (by rfl) ⟨1991258, by rfl⟩ : syracuseStep 2655011 = 3982517) B3982517
theorem B2360099 : Blo 1572484 2360099 := bstep (se 1 (by rfl) ⟨1770074, by rfl⟩ : syracuseStep 2360099 = 3540149) B3540149
theorem B1573667 : Blo 1572484 1573667 := bstep (se 1 (by rfl) ⟨1180250, by rfl⟩ : syracuseStep 1573667 = 2360501) B2360501
theorem B1573683 : Blo 1572484 1573683 := bstep (se 1 (by rfl) ⟨1180262, by rfl⟩ : syracuseStep 1573683 = 2360525) B2360525
theorem B2360129 : Blo 1572484 2360129 := bstep (se 2 (by rfl) ⟨885048, by rfl⟩ : syracuseStep 2360129 = 1770097) B1770097
theorem B1573699 : Blo 1572484 1573699 := bstep (se 1 (by rfl) ⟨1180274, by rfl⟩ : syracuseStep 1573699 = 2360549) B2360549
theorem B2392897 : Blo 1572484 2392897 := bstep (se 2 (by rfl) ⟨897336, by rfl⟩ : syracuseStep 2392897 = 1794673) B1794673
theorem B2360147 : Blo 1572484 2360147 := bstep (se 1 (by rfl) ⟨1770110, by rfl⟩ : syracuseStep 2360147 = 3540221) B3540221
theorem B1573715 : Blo 1572484 1573715 := bstep (se 1 (by rfl) ⟨1180286, by rfl⟩ : syracuseStep 1573715 = 2360573) B2360573
theorem B1573731 : Blo 1572484 1573731 := bstep (se 1 (by rfl) ⟨1180298, by rfl⟩ : syracuseStep 1573731 = 2360597) B2360597
theorem B5972849 : Blo 1572484 5972849 := bstep (se 2 (by rfl) ⟨2239818, by rfl⟩ : syracuseStep 5972849 = 4479637) B4479637
theorem B3982193 : Blo 1572484 3982193 := bstep (se 2 (by rfl) ⟨1493322, by rfl⟩ : syracuseStep 3982193 = 2986645) B2986645
theorem B3539825 : Blo 1572484 3539825 := bstep (se 2 (by rfl) ⟨1327434, by rfl⟩ : syracuseStep 3539825 = 2654869) B2654869
theorem B2360177 : Blo 1572484 2360177 := bstep (se 2 (by rfl) ⟨885066, by rfl⟩ : syracuseStep 2360177 = 1770133) B1770133
theorem B1573747 : Blo 1572484 1573747 := bstep (se 1 (by rfl) ⟨1180310, by rfl⟩ : syracuseStep 1573747 = 2360621) B2360621
theorem B3539843 : Blo 1572484 3539843 := bstep (se 1 (by rfl) ⟨2654882, by rfl⟩ : syracuseStep 3539843 = 5309765) B5309765
theorem B2360195 : Blo 1572484 2360195 := bstep (se 1 (by rfl) ⟨1770146, by rfl⟩ : syracuseStep 2360195 = 3540293) B3540293
theorem B1573763 : Blo 1572484 1573763 := bstep (se 1 (by rfl) ⟨1180322, by rfl⟩ : syracuseStep 1573763 = 2360645) B2360645
theorem B1573779 : Blo 1572484 1573779 := bstep (se 1 (by rfl) ⟨1180334, by rfl⟩ : syracuseStep 1573779 = 2360669) B2360669
theorem B2360225 : Blo 1572484 2360225 := bstep (se 2 (by rfl) ⟨885084, by rfl⟩ : syracuseStep 2360225 = 1770169) B1770169
theorem B3982243 : Blo 1572484 3982243 := bstep (se 1 (by rfl) ⟨2986682, by rfl⟩ : syracuseStep 3982243 = 5973365) B5973365
theorem B2655139 : Blo 1572484 2655139 := bstep (se 1 (by rfl) ⟨1991354, by rfl⟩ : syracuseStep 2655139 = 3982709) B3982709
theorem B1770403 : Blo 1572484 1770403 := bstep (se 1 (by rfl) ⟨1327802, by rfl⟩ : syracuseStep 1770403 = 2655605) B2655605
theorem B1573795 : Blo 1572484 1573795 := bstep (se 1 (by rfl) ⟨1180346, by rfl⟩ : syracuseStep 1573795 = 2360693) B2360693
theorem B2360243 : Blo 1572484 2360243 := bstep (se 1 (by rfl) ⟨1770182, by rfl⟩ : syracuseStep 2360243 = 3540365) B3540365
theorem B1573811 : Blo 1572484 1573811 := bstep (se 1 (by rfl) ⟨1180358, by rfl⟩ : syracuseStep 1573811 = 2360717) B2360717
theorem B1573827 : Blo 1572484 1573827 := bstep (se 1 (by rfl) ⟨1180370, by rfl⟩ : syracuseStep 1573827 = 2360741) B2360741
theorem B2360273 : Blo 1572484 2360273 := bstep (se 2 (by rfl) ⟨885102, by rfl⟩ : syracuseStep 2360273 = 1770205) B1770205
theorem B1573843 : Blo 1572484 1573843 := bstep (se 1 (by rfl) ⟨1180382, by rfl⟩ : syracuseStep 1573843 = 2360765) B2360765
theorem B2360291 : Blo 1572484 2360291 := bstep (se 1 (by rfl) ⟨1770218, by rfl⟩ : syracuseStep 2360291 = 3540437) B3540437
theorem B1573859 : Blo 1572484 1573859 := bstep (se 1 (by rfl) ⟨1180394, by rfl⟩ : syracuseStep 1573859 = 2360789) B2360789
theorem B12116963 : Blo 1572484 12116963 := bstep (se 1 (by rfl) ⟨9087722, by rfl⟩ : syracuseStep 12116963 = 18175445) B18175445
theorem B4482029 : Blo 1572484 4482029 := bstep (se 3 (by rfl) ⟨840380, by rfl⟩ : syracuseStep 4482029 = 1680761) B1680761
theorem B1573875 : Blo 1572484 1573875 := bstep (se 1 (by rfl) ⟨1180406, by rfl⟩ : syracuseStep 1573875 = 2360813) B2360813
theorem B2360321 : Blo 1572484 2360321 := bstep (se 2 (by rfl) ⟨885120, by rfl⟩ : syracuseStep 2360321 = 1770241) B1770241
theorem B1573891 : Blo 1572484 1573891 := bstep (se 1 (by rfl) ⟨1180418, by rfl⟩ : syracuseStep 1573891 = 2360837) B2360837
theorem B2360339 : Blo 1572484 2360339 := bstep (se 1 (by rfl) ⟨1770254, by rfl⟩ : syracuseStep 2360339 = 3540509) B3540509
theorem B1573907 : Blo 1572484 1573907 := bstep (se 1 (by rfl) ⟨1180430, by rfl⟩ : syracuseStep 1573907 = 2360861) B2360861
theorem B1573923 : Blo 1572484 1573923 := bstep (se 1 (by rfl) ⟨1180442, by rfl⟩ : syracuseStep 1573923 = 2360885) B2360885
theorem B3982385 : Blo 1572484 3982385 := bstep (se 2 (by rfl) ⟨1493394, by rfl⟩ : syracuseStep 3982385 = 2986789) B2986789
theorem B2655281 : Blo 1572484 2655281 := bstep (se 2 (by rfl) ⟨995730, by rfl⟩ : syracuseStep 2655281 = 1991461) B1991461
theorem B2360369 : Blo 1572484 2360369 := bstep (se 2 (by rfl) ⟨885138, by rfl⟩ : syracuseStep 2360369 = 1770277) B1770277
theorem B1770547 : Blo 1572484 1770547 := bstep (se 1 (by rfl) ⟨1327910, by rfl⟩ : syracuseStep 1770547 = 2655821) B2655821
theorem B1573939 : Blo 1572484 1573939 := bstep (se 1 (by rfl) ⟨1180454, by rfl⟩ : syracuseStep 1573939 = 2360909) B2360909
theorem B2360387 : Blo 1572484 2360387 := bstep (se 1 (by rfl) ⟨1770290, by rfl⟩ : syracuseStep 2360387 = 3540581) B3540581
theorem B1573955 : Blo 1572484 1573955 := bstep (se 1 (by rfl) ⟨1180466, by rfl⟩ : syracuseStep 1573955 = 2360933) B2360933
theorem B1573971 : Blo 1572484 1573971 := bstep (se 1 (by rfl) ⟨1180478, by rfl⟩ : syracuseStep 1573971 = 2360957) B2360957
theorem B2360417 : Blo 1572484 2360417 := bstep (se 2 (by rfl) ⟨885156, by rfl⟩ : syracuseStep 2360417 = 1770313) B1770313
theorem B1573987 : Blo 1572484 1573987 := bstep (se 1 (by rfl) ⟨1180490, by rfl⟩ : syracuseStep 1573987 = 2360981) B2360981
theorem B5309549 : Blo 1572484 5309549 := bstep (se 3 (by rfl) ⟨995540, by rfl⟩ : syracuseStep 5309549 = 1991081) B1991081
theorem B161547377 : Blo 1572484 161547377 := bstep (se 2 (by rfl) ⟨60580266, by rfl⟩ : syracuseStep 161547377 = 121160533) B121160533
theorem B2360435 : Blo 1572484 2360435 := bstep (se 1 (by rfl) ⟨1770326, by rfl⟩ : syracuseStep 2360435 = 3540653) B3540653
theorem B2393201 : Blo 1572484 2393201 := bstep (se 2 (by rfl) ⟨897450, by rfl⟩ : syracuseStep 2393201 = 1794901) B1794901
theorem B1574003 : Blo 1572484 1574003 := bstep (se 1 (by rfl) ⟨1180502, by rfl⟩ : syracuseStep 1574003 = 2361005) B2361005
theorem B1574019 : Blo 1572484 1574019 := bstep (se 1 (by rfl) ⟨1180514, by rfl⟩ : syracuseStep 1574019 = 2361029) B2361029
theorem B3540113 : Blo 1572484 3540113 := bstep (se 2 (by rfl) ⟨1327542, by rfl⟩ : syracuseStep 3540113 = 2655085) B2655085
theorem B2360465 : Blo 1572484 2360465 := bstep (se 2 (by rfl) ⟨885174, by rfl⟩ : syracuseStep 2360465 = 1770349) B1770349
theorem B1574035 : Blo 1572484 1574035 := bstep (se 1 (by rfl) ⟨1180526, by rfl⟩ : syracuseStep 1574035 = 2361053) B2361053
theorem B5309603 : Blo 1572484 5309603 := bstep (se 1 (by rfl) ⟨3982202, by rfl⟩ : syracuseStep 5309603 = 7964405) B7964405
theorem B3540131 : Blo 1572484 3540131 := bstep (se 1 (by rfl) ⟨2655098, by rfl⟩ : syracuseStep 3540131 = 5310197) B5310197
theorem B2360483 : Blo 1572484 2360483 := bstep (se 1 (by rfl) ⟨1770362, by rfl⟩ : syracuseStep 2360483 = 3540725) B3540725
theorem B4482211 : Blo 1572484 4482211 := bstep (se 1 (by rfl) ⟨3361658, by rfl⟩ : syracuseStep 4482211 = 6723317) B6723317
theorem B1574051 : Blo 1572484 1574051 := bstep (se 1 (by rfl) ⟨1180538, by rfl⟩ : syracuseStep 1574051 = 2361077) B2361077
theorem B2655409 : Blo 1572484 2655409 := bstep (se 2 (by rfl) ⟨995778, by rfl⟩ : syracuseStep 2655409 = 1991557) B1991557
theorem B1574067 : Blo 1572484 1574067 := bstep (se 1 (by rfl) ⟨1180550, by rfl⟩ : syracuseStep 1574067 = 2361101) B2361101
theorem B2360513 : Blo 1572484 2360513 := bstep (se 2 (by rfl) ⟨885192, by rfl⟩ : syracuseStep 2360513 = 1770385) B1770385
theorem B1770691 : Blo 1572484 1770691 := bstep (se 1 (by rfl) ⟨1328018, by rfl⟩ : syracuseStep 1770691 = 2656037) B2656037
theorem B1574083 : Blo 1572484 1574083 := bstep (se 1 (by rfl) ⟨1180562, by rfl⟩ : syracuseStep 1574083 = 2361125) B2361125
theorem B2655443 : Blo 1572484 2655443 := bstep (se 1 (by rfl) ⟨1991582, by rfl⟩ : syracuseStep 2655443 = 3983165) B3983165
theorem B2360531 : Blo 1572484 2360531 := bstep (se 1 (by rfl) ⟨1770398, by rfl⟩ : syracuseStep 2360531 = 3540797) B3540797
theorem B1991891 : Blo 1572484 1991891 := bstep (se 1 (by rfl) ⟨1493918, by rfl⟩ : syracuseStep 1991891 = 2987837) B2987837
theorem B1574099 : Blo 1572484 1574099 := bstep (se 1 (by rfl) ⟨1180574, by rfl⟩ : syracuseStep 1574099 = 2361149) B2361149
theorem B1574115 : Blo 1572484 1574115 := bstep (se 1 (by rfl) ⟨1180586, by rfl⟩ : syracuseStep 1574115 = 2361173) B2361173
theorem B2360561 : Blo 1572484 2360561 := bstep (se 2 (by rfl) ⟨885210, by rfl⟩ : syracuseStep 2360561 = 1770421) B1770421
theorem B1574131 : Blo 1572484 1574131 := bstep (se 1 (by rfl) ⟨1180598, by rfl⟩ : syracuseStep 1574131 = 2361197) B2361197
theorem B2360579 : Blo 1572484 2360579 := bstep (se 1 (by rfl) ⟨1770434, by rfl⟩ : syracuseStep 2360579 = 3540869) B3540869
theorem B1574147 : Blo 1572484 1574147 := bstep (se 1 (by rfl) ⟨1180610, by rfl⟩ : syracuseStep 1574147 = 2361221) B2361221
theorem B1574163 : Blo 1572484 1574163 := bstep (se 1 (by rfl) ⟨1180622, by rfl⟩ : syracuseStep 1574163 = 2361245) B2361245
theorem B2360609 : Blo 1572484 2360609 := bstep (se 2 (by rfl) ⟨885228, by rfl⟩ : syracuseStep 2360609 = 1770457) B1770457
theorem B1574179 : Blo 1572484 1574179 := bstep (se 1 (by rfl) ⟨1180634, by rfl⟩ : syracuseStep 1574179 = 2361269) B2361269
theorem B2360627 : Blo 1572484 2360627 := bstep (se 1 (by rfl) ⟨1770470, by rfl⟩ : syracuseStep 2360627 = 3540941) B3540941
theorem B1574195 : Blo 1572484 1574195 := bstep (se 1 (by rfl) ⟨1180646, by rfl⟩ : syracuseStep 1574195 = 2361293) B2361293
theorem B4482371 : Blo 1572484 4482371 := bstep (se 1 (by rfl) ⟨3361778, by rfl⟩ : syracuseStep 4482371 = 6723557) B6723557
theorem B1574211 : Blo 1572484 1574211 := bstep (se 1 (by rfl) ⟨1180658, by rfl⟩ : syracuseStep 1574211 = 2361317) B2361317
theorem B2360657 : Blo 1572484 2360657 := bstep (se 2 (by rfl) ⟨885246, by rfl⟩ : syracuseStep 2360657 = 1770493) B1770493
theorem B2655571 : Blo 1572484 2655571 := bstep (se 1 (by rfl) ⟨1991678, by rfl⟩ : syracuseStep 2655571 = 3983357) B3983357
theorem B1770835 : Blo 1572484 1770835 := bstep (se 1 (by rfl) ⟨1328126, by rfl⟩ : syracuseStep 1770835 = 2656253) B2656253
theorem B1574227 : Blo 1572484 1574227 := bstep (se 1 (by rfl) ⟨1180670, by rfl⟩ : syracuseStep 1574227 = 2361341) B2361341
theorem B2360675 : Blo 1572484 2360675 := bstep (se 1 (by rfl) ⟨1770506, by rfl⟩ : syracuseStep 2360675 = 3541013) B3541013
theorem B1574243 : Blo 1572484 1574243 := bstep (se 1 (by rfl) ⟨1180682, by rfl⟩ : syracuseStep 1574243 = 2361365) B2361365
theorem B3360113 : Blo 1572484 3360113 := bstep (se 2 (by rfl) ⟨1260042, by rfl⟩ : syracuseStep 3360113 = 2520085) B2520085
theorem B1574259 : Blo 1572484 1574259 := bstep (se 1 (by rfl) ⟨1180694, by rfl⟩ : syracuseStep 1574259 = 2361389) B2361389
theorem B2360705 : Blo 1572484 2360705 := bstep (se 2 (by rfl) ⟨885264, by rfl⟩ : syracuseStep 2360705 = 1770529) B1770529
theorem B1574275 : Blo 1572484 1574275 := bstep (se 1 (by rfl) ⟨1180706, by rfl⟩ : syracuseStep 1574275 = 2361413) B2361413
theorem B2360723 : Blo 1572484 2360723 := bstep (se 1 (by rfl) ⟨1770542, by rfl⟩ : syracuseStep 2360723 = 3541085) B3541085
theorem B1680787 : Blo 1572484 1680787 := bstep (se 1 (by rfl) ⟨1260590, by rfl⟩ : syracuseStep 1680787 = 2521181) B2521181
theorem B1574291 : Blo 1572484 1574291 := bstep (se 1 (by rfl) ⟨1180718, by rfl⟩ : syracuseStep 1574291 = 2361437) B2361437
theorem B1574307 : Blo 1572484 1574307 := bstep (se 1 (by rfl) ⟨1180730, by rfl⟩ : syracuseStep 1574307 = 2361461) B2361461
theorem B7964081 : Blo 1572484 7964081 := bstep (se 2 (by rfl) ⟨2986530, by rfl⟩ : syracuseStep 7964081 = 5973061) B5973061
theorem B5309873 : Blo 1572484 5309873 := bstep (se 2 (by rfl) ⟨1991202, by rfl⟩ : syracuseStep 5309873 = 3982405) B3982405
theorem B3540401 : Blo 1572484 3540401 := bstep (se 2 (by rfl) ⟨1327650, by rfl⟩ : syracuseStep 3540401 = 2655301) B2655301
theorem B2360753 : Blo 1572484 2360753 := bstep (se 2 (by rfl) ⟨885282, by rfl⟩ : syracuseStep 2360753 = 1770565) B1770565
theorem B1574323 : Blo 1572484 1574323 := bstep (se 1 (by rfl) ⟨1180742, by rfl⟩ : syracuseStep 1574323 = 2361485) B2361485
theorem B3540419 : Blo 1572484 3540419 := bstep (se 1 (by rfl) ⟨2655314, by rfl⟩ : syracuseStep 3540419 = 5310629) B5310629
theorem B2360771 : Blo 1572484 2360771 := bstep (se 1 (by rfl) ⟨1770578, by rfl⟩ : syracuseStep 2360771 = 3541157) B3541157
theorem B1574339 : Blo 1572484 1574339 := bstep (se 1 (by rfl) ⟨1180754, by rfl⟩ : syracuseStep 1574339 = 2361509) B2361509
theorem B1574355 : Blo 1572484 1574355 := bstep (se 1 (by rfl) ⟨1180766, by rfl⟩ : syracuseStep 1574355 = 2361533) B2361533
theorem B2655713 : Blo 1572484 2655713 := bstep (se 2 (by rfl) ⟨995892, by rfl⟩ : syracuseStep 2655713 = 1991785) B1991785
theorem B2360801 : Blo 1572484 2360801 := bstep (se 2 (by rfl) ⟨885300, by rfl⟩ : syracuseStep 2360801 = 1770601) B1770601
theorem B1770979 : Blo 1572484 1770979 := bstep (se 1 (by rfl) ⟨1328234, by rfl⟩ : syracuseStep 1770979 = 2656469) B2656469
theorem B1574371 : Blo 1572484 1574371 := bstep (se 1 (by rfl) ⟨1180778, by rfl⟩ : syracuseStep 1574371 = 2361557) B2361557
theorem B2360819 : Blo 1572484 2360819 := bstep (se 1 (by rfl) ⟨1770614, by rfl⟩ : syracuseStep 2360819 = 3541229) B3541229
theorem B1574387 : Blo 1572484 1574387 := bstep (se 1 (by rfl) ⟨1180790, by rfl⟩ : syracuseStep 1574387 = 2361581) B2361581
theorem B1574403 : Blo 1572484 1574403 := bstep (se 1 (by rfl) ⟨1180802, by rfl⟩ : syracuseStep 1574403 = 2361605) B2361605
theorem B2360849 : Blo 1572484 2360849 := bstep (se 2 (by rfl) ⟨885318, by rfl⟩ : syracuseStep 2360849 = 1770637) B1770637
theorem B1574419 : Blo 1572484 1574419 := bstep (se 1 (by rfl) ⟨1180814, by rfl⟩ : syracuseStep 1574419 = 2361629) B2361629
theorem B2360867 : Blo 1572484 2360867 := bstep (se 1 (by rfl) ⟨1770650, by rfl⟩ : syracuseStep 2360867 = 3541301) B3541301
theorem B1574435 : Blo 1572484 1574435 := bstep (se 1 (by rfl) ⟨1180826, by rfl⟩ : syracuseStep 1574435 = 2361653) B2361653
theorem B1574451 : Blo 1572484 1574451 := bstep (se 1 (by rfl) ⟨1180838, by rfl⟩ : syracuseStep 1574451 = 2361677) B2361677
theorem B2360897 : Blo 1572484 2360897 := bstep (se 2 (by rfl) ⟨885336, by rfl⟩ : syracuseStep 2360897 = 1770673) B1770673
theorem B1574467 : Blo 1572484 1574467 := bstep (se 1 (by rfl) ⟨1180850, by rfl⟩ : syracuseStep 1574467 = 2361701) B2361701
theorem B2360915 : Blo 1572484 2360915 := bstep (se 1 (by rfl) ⟨1770686, by rfl⟩ : syracuseStep 2360915 = 3541373) B3541373
theorem B1574483 : Blo 1572484 1574483 := bstep (se 1 (by rfl) ⟨1180862, by rfl⟩ : syracuseStep 1574483 = 2361725) B2361725
theorem B2655841 : Blo 1572484 2655841 := bstep (se 2 (by rfl) ⟨995940, by rfl⟩ : syracuseStep 2655841 = 1991881) B1991881
theorem B2360945 : Blo 1572484 2360945 := bstep (se 2 (by rfl) ⟨885354, by rfl⟩ : syracuseStep 2360945 = 1770709) B1770709
theorem B1771123 : Blo 1572484 1771123 := bstep (se 1 (by rfl) ⟨1328342, by rfl⟩ : syracuseStep 1771123 = 2656685) B2656685
theorem B2655875 : Blo 1572484 2655875 := bstep (se 1 (by rfl) ⟨1991906, by rfl⟩ : syracuseStep 2655875 = 3983813) B3983813
theorem B2360963 : Blo 1572484 2360963 := bstep (se 1 (by rfl) ⟨1770722, by rfl⟩ : syracuseStep 2360963 = 3541445) B3541445
theorem B2360993 : Blo 1572484 2360993 := bstep (se 2 (by rfl) ⟨885372, by rfl⟩ : syracuseStep 2360993 = 1770745) B1770745
theorem B2361011 : Blo 1572484 2361011 := bstep (se 1 (by rfl) ⟨1770758, by rfl⟩ : syracuseStep 2361011 = 3541517) B3541517
theorem B3540689 : Blo 1572484 3540689 := bstep (se 2 (by rfl) ⟨1327758, by rfl⟩ : syracuseStep 3540689 = 2655517) B2655517
theorem B2361041 : Blo 1572484 2361041 := bstep (se 2 (by rfl) ⟨885390, by rfl⟩ : syracuseStep 2361041 = 1770781) B1770781
theorem B3540707 : Blo 1572484 3540707 := bstep (se 1 (by rfl) ⟨2655530, by rfl⟩ : syracuseStep 3540707 = 5311061) B5311061
theorem B2361059 : Blo 1572484 2361059 := bstep (se 1 (by rfl) ⟨1770794, by rfl⟩ : syracuseStep 2361059 = 3541589) B3541589
theorem B2361089 : Blo 1572484 2361089 := bstep (se 2 (by rfl) ⟨885408, by rfl⟩ : syracuseStep 2361089 = 1770817) B1770817
theorem B2656003 : Blo 1572484 2656003 := bstep (se 1 (by rfl) ⟨1992002, by rfl⟩ : syracuseStep 2656003 = 3984005) B3984005
theorem B1771267 : Blo 1572484 1771267 := bstep (se 1 (by rfl) ⟨1328450, by rfl⟩ : syracuseStep 1771267 = 2656901) B2656901
theorem B2361107 : Blo 1572484 2361107 := bstep (se 1 (by rfl) ⟨1770830, by rfl⟩ : syracuseStep 2361107 = 3541661) B3541661
theorem B2361137 : Blo 1572484 2361137 := bstep (se 2 (by rfl) ⟨885426, by rfl⟩ : syracuseStep 2361137 = 1770853) B1770853
theorem B2361155 : Blo 1572484 2361155 := bstep (se 1 (by rfl) ⟨1770866, by rfl⟩ : syracuseStep 2361155 = 3541733) B3541733
theorem B20170565 : Blo 1572484 20170565 := bstep (se 4 (by rfl) ⟨1890990, by rfl⟩ : syracuseStep 20170565 = 3781981) B3781981
theorem B2361185 : Blo 1572484 2361185 := bstep (se 2 (by rfl) ⟨885444, by rfl⟩ : syracuseStep 2361185 = 1770889) B1770889
theorem B2361203 : Blo 1572484 2361203 := bstep (se 1 (by rfl) ⟨1770902, by rfl⟩ : syracuseStep 2361203 = 3541805) B3541805
theorem B2656145 : Blo 1572484 2656145 := bstep (se 2 (by rfl) ⟨996054, by rfl⟩ : syracuseStep 2656145 = 1992109) B1992109
theorem B2361233 : Blo 1572484 2361233 := bstep (se 2 (by rfl) ⟨885462, by rfl⟩ : syracuseStep 2361233 = 1770925) B1770925
theorem B1992595 : Blo 1572484 1992595 := bstep (se 1 (by rfl) ⟨1494446, by rfl⟩ : syracuseStep 1992595 = 2988893) B2988893
theorem B2361251 : Blo 1572484 2361251 := bstep (se 1 (by rfl) ⟨1770938, by rfl⟩ : syracuseStep 2361251 = 3541877) B3541877
theorem B2361281 : Blo 1572484 2361281 := bstep (se 2 (by rfl) ⟨885480, by rfl⟩ : syracuseStep 2361281 = 1770961) B1770961
theorem B5310413 : Blo 1572484 5310413 := bstep (se 3 (by rfl) ⟨995702, by rfl⟩ : syracuseStep 5310413 = 1991405) B1991405
theorem B2361299 : Blo 1572484 2361299 := bstep (se 1 (by rfl) ⟨1770974, by rfl⟩ : syracuseStep 2361299 = 3541949) B3541949
theorem B4253681 : Blo 1572484 4253681 := bstep (se 2 (by rfl) ⟨1595130, by rfl⟩ : syracuseStep 4253681 = 3190261) B3190261
theorem B3540977 : Blo 1572484 3540977 := bstep (se 2 (by rfl) ⟨1327866, by rfl⟩ : syracuseStep 3540977 = 2655733) B2655733
theorem B2361329 : Blo 1572484 2361329 := bstep (se 2 (by rfl) ⟨885498, by rfl⟩ : syracuseStep 2361329 = 1770997) B1770997
theorem B1992691 : Blo 1572484 1992691 := bstep (se 1 (by rfl) ⟨1494518, by rfl⟩ : syracuseStep 1992691 = 2989037) B2989037
theorem B5310467 : Blo 1572484 5310467 := bstep (se 1 (by rfl) ⟨3982850, by rfl⟩ : syracuseStep 5310467 = 7965701) B7965701
theorem B3540995 : Blo 1572484 3540995 := bstep (se 1 (by rfl) ⟨2655746, by rfl⟩ : syracuseStep 3540995 = 5311493) B5311493
theorem B3590147 : Blo 1572484 3590147 := bstep (se 1 (by rfl) ⟨2692610, by rfl⟩ : syracuseStep 3590147 = 5385221) B5385221
theorem B2361347 : Blo 1572484 2361347 := bstep (se 1 (by rfl) ⟨1771010, by rfl⟩ : syracuseStep 2361347 = 3542021) B3542021
theorem B3983377 : Blo 1572484 3983377 := bstep (se 2 (by rfl) ⟨1493766, by rfl⟩ : syracuseStep 3983377 = 2987533) B2987533
theorem B2656273 : Blo 1572484 2656273 := bstep (se 2 (by rfl) ⟨996102, by rfl⟩ : syracuseStep 2656273 = 1992205) B1992205
theorem B2361377 : Blo 1572484 2361377 := bstep (se 2 (by rfl) ⟨885516, by rfl⟩ : syracuseStep 2361377 = 1771033) B1771033
theorem B2656307 : Blo 1572484 2656307 := bstep (se 1 (by rfl) ⟨1992230, by rfl⟩ : syracuseStep 2656307 = 3984461) B3984461
theorem B2361395 : Blo 1572484 2361395 := bstep (se 1 (by rfl) ⟨1771046, by rfl⟩ : syracuseStep 2361395 = 3542093) B3542093
theorem B2361425 : Blo 1572484 2361425 := bstep (se 2 (by rfl) ⟨885534, by rfl⟩ : syracuseStep 2361425 = 1771069) B1771069
theorem B2361443 : Blo 1572484 2361443 := bstep (se 1 (by rfl) ⟨1771082, by rfl⟩ : syracuseStep 2361443 = 3542165) B3542165
theorem B30673009 : Blo 1572484 30673009 := bstep (se 2 (by rfl) ⟨11502378, by rfl⟩ : syracuseStep 30673009 = 23004757) B23004757
theorem B2361473 : Blo 1572484 2361473 := bstep (se 2 (by rfl) ⟨885552, by rfl⟩ : syracuseStep 2361473 = 1771105) B1771105
theorem B2361491 : Blo 1572484 2361491 := bstep (se 1 (by rfl) ⟨1771118, by rfl⟩ : syracuseStep 2361491 = 3542237) B3542237
theorem B9570467 : Blo 1572484 9570467 := bstep (se 1 (by rfl) ⟨7177850, by rfl⟩ : syracuseStep 9570467 = 14355701) B14355701
theorem B2361521 : Blo 1572484 2361521 := bstep (se 2 (by rfl) ⟨885570, by rfl⟩ : syracuseStep 2361521 = 1771141) B1771141
theorem B2656435 : Blo 1572484 2656435 := bstep (se 1 (by rfl) ⟨1992326, by rfl⟩ : syracuseStep 2656435 = 3984653) B3984653
theorem B2361539 : Blo 1572484 2361539 := bstep (se 1 (by rfl) ⟨1771154, by rfl⟩ : syracuseStep 2361539 = 3542309) B3542309
theorem B2361569 : Blo 1572484 2361569 := bstep (se 2 (by rfl) ⟨885588, by rfl⟩ : syracuseStep 2361569 = 1771177) B1771177
theorem B8071409 : Blo 1572484 8071409 := bstep (se 2 (by rfl) ⟨3026778, by rfl⟩ : syracuseStep 8071409 = 6053557) B6053557
theorem B3361009 : Blo 1572484 3361009 := bstep (se 2 (by rfl) ⟨1260378, by rfl⟩ : syracuseStep 3361009 = 2520757) B2520757
theorem B2361587 : Blo 1572484 2361587 := bstep (se 1 (by rfl) ⟨1771190, by rfl⟩ : syracuseStep 2361587 = 3542381) B3542381
theorem B3361027 : Blo 1572484 3361027 := bstep (se 1 (by rfl) ⟨2520770, by rfl⟩ : syracuseStep 3361027 = 5041541) B5041541
theorem B5310737 : Blo 1572484 5310737 := bstep (se 2 (by rfl) ⟨1991526, by rfl⟩ : syracuseStep 5310737 = 3983053) B3983053
theorem B3541265 : Blo 1572484 3541265 := bstep (se 2 (by rfl) ⟨1327974, by rfl⟩ : syracuseStep 3541265 = 2655949) B2655949
theorem B2361617 : Blo 1572484 2361617 := bstep (se 2 (by rfl) ⟨885606, by rfl⟩ : syracuseStep 2361617 = 1771213) B1771213
theorem B5974307 : Blo 1572484 5974307 := bstep (se 1 (by rfl) ⟨4480730, by rfl⟩ : syracuseStep 5974307 = 8961461) B8961461
theorem B3983651 : Blo 1572484 3983651 := bstep (se 1 (by rfl) ⟨2987738, by rfl⟩ : syracuseStep 3983651 = 5975477) B5975477
theorem B3541283 : Blo 1572484 3541283 := bstep (se 1 (by rfl) ⟨2655962, by rfl⟩ : syracuseStep 3541283 = 5311925) B5311925
theorem B2361635 : Blo 1572484 2361635 := bstep (se 1 (by rfl) ⟨1771226, by rfl⟩ : syracuseStep 2361635 = 3542453) B3542453
theorem B2656577 : Blo 1572484 2656577 := bstep (se 2 (by rfl) ⟨996216, by rfl⟩ : syracuseStep 2656577 = 1992433) B1992433
theorem B2361665 : Blo 1572484 2361665 := bstep (se 2 (by rfl) ⟨885624, by rfl⟩ : syracuseStep 2361665 = 1771249) B1771249
theorem B2361683 : Blo 1572484 2361683 := bstep (se 1 (by rfl) ⟨1771262, by rfl⟩ : syracuseStep 2361683 = 3542525) B3542525
theorem B3590513 : Blo 1572484 3590513 := bstep (se 2 (by rfl) ⟨1346442, by rfl⟩ : syracuseStep 3590513 = 2692885) B2692885
theorem B4483441 : Blo 1572484 4483441 := bstep (se 2 (by rfl) ⟨1681290, by rfl⟩ : syracuseStep 4483441 = 3362581) B3362581
theorem B2361713 : Blo 1572484 2361713 := bstep (se 2 (by rfl) ⟨885642, by rfl⟩ : syracuseStep 2361713 = 1771285) B1771285
theorem B2656705 : Blo 1572484 2656705 := bstep (se 2 (by rfl) ⟨996264, by rfl⟩ : syracuseStep 2656705 = 1992529) B1992529
theorem B3983843 : Blo 1572484 3983843 := bstep (se 1 (by rfl) ⟨2987882, by rfl⟩ : syracuseStep 3983843 = 5975765) B5975765
theorem B2656739 : Blo 1572484 2656739 := bstep (se 1 (by rfl) ⟨1992554, by rfl⟩ : syracuseStep 2656739 = 3985109) B3985109
theorem B5040643 : Blo 1572484 5040643 := bstep (se 1 (by rfl) ⟨3780482, by rfl⟩ : syracuseStep 5040643 = 7560965) B7560965
theorem B4254211 : Blo 1572484 4254211 := bstep (se 1 (by rfl) ⟨3190658, by rfl⟩ : syracuseStep 4254211 = 6381317) B6381317
theorem B3590659 : Blo 1572484 3590659 := bstep (se 1 (by rfl) ⟨2692994, by rfl⟩ : syracuseStep 3590659 = 5385989) B5385989
theorem B3541553 : Blo 1572484 3541553 := bstep (se 2 (by rfl) ⟨1328082, by rfl⟩ : syracuseStep 3541553 = 2656165) B2656165
theorem B3541571 : Blo 1572484 3541571 := bstep (se 1 (by rfl) ⟨2656178, by rfl⟩ : syracuseStep 3541571 = 5312357) B5312357
theorem B16149091 : Blo 1572484 16149091 := bstep (se 1 (by rfl) ⟨12111818, by rfl⟩ : syracuseStep 16149091 = 24223637) B24223637
theorem B2656867 : Blo 1572484 2656867 := bstep (se 1 (by rfl) ⟨1992650, by rfl⟩ : syracuseStep 2656867 = 3985301) B3985301
theorem B5040785 : Blo 1572484 5040785 := bstep (se 2 (by rfl) ⟨1890294, by rfl⟩ : syracuseStep 5040785 = 3780589) B3780589
theorem B2239169 : Blo 1572484 2239169 := bstep (se 2 (by rfl) ⟨839688, by rfl⟩ : syracuseStep 2239169 = 1679377) B1679377
theorem B6720241 : Blo 1572484 6720241 := bstep (se 2 (by rfl) ⟨2520090, by rfl⟩ : syracuseStep 6720241 = 5040181) B5040181
theorem B8964877 : Blo 1572484 8964877 := bstep (se 3 (by rfl) ⟨1680914, by rfl⟩ : syracuseStep 8964877 = 3361829) B3361829
theorem B5311277 : Blo 1572484 5311277 := bstep (se 3 (by rfl) ⟨995864, by rfl⟩ : syracuseStep 5311277 = 1991729) B1991729
theorem B7970723 : Blo 1572484 7970723 := bstep (se 1 (by rfl) ⟨5978042, by rfl⟩ : syracuseStep 7970723 = 11956085) B11956085
theorem B2239283 : Blo 1572484 2239283 := bstep (se 1 (by rfl) ⟨1679462, by rfl⟩ : syracuseStep 2239283 = 3358925) B3358925
theorem B3541841 : Blo 1572484 3541841 := bstep (se 2 (by rfl) ⟨1328190, by rfl⟩ : syracuseStep 3541841 = 2656381) B2656381
theorem B17918819 : Blo 1572484 17918819 := bstep (se 1 (by rfl) ⟨13439114, by rfl⟩ : syracuseStep 17918819 = 26878229) B26878229
theorem B11946851 : Blo 1572484 11946851 := bstep (se 1 (by rfl) ⟨8960138, by rfl⟩ : syracuseStep 11946851 = 17920277) B17920277
theorem B7965539 : Blo 1572484 7965539 := bstep (se 1 (by rfl) ⟨5974154, by rfl⟩ : syracuseStep 7965539 = 11948309) B11948309
theorem B5311331 : Blo 1572484 5311331 := bstep (se 1 (by rfl) ⟨3983498, by rfl⟩ : syracuseStep 5311331 = 7966997) B7966997
theorem B3541859 : Blo 1572484 3541859 := bstep (se 1 (by rfl) ⟨2656394, by rfl⟩ : syracuseStep 3541859 = 5312789) B5312789
theorem B2239363 : Blo 1572484 2239363 := bstep (se 1 (by rfl) ⟨1679522, by rfl⟩ : syracuseStep 2239363 = 3359045) B3359045
theorem B4918321 : Blo 1572484 4918321 := bstep (se 2 (by rfl) ⟨1844370, by rfl⟩ : syracuseStep 4918321 = 3688741) B3688741
theorem B13438021 : Blo 1572484 13438021 := bstep (se 4 (by rfl) ⟨1259814, by rfl⟩ : syracuseStep 13438021 = 2519629) B2519629
theorem B5311601 : Blo 1572484 5311601 := bstep (se 2 (by rfl) ⟨1991850, by rfl⟩ : syracuseStep 5311601 = 3983701) B3983701
theorem B3542129 : Blo 1572484 3542129 := bstep (se 2 (by rfl) ⟨1328298, by rfl⟩ : syracuseStep 3542129 = 2656597) B2656597
theorem B3542147 : Blo 1572484 3542147 := bstep (se 1 (by rfl) ⟨2656610, by rfl⟩ : syracuseStep 3542147 = 5313221) B5313221
theorem B4254925 : Blo 1572484 4254925 := bstep (se 3 (by rfl) ⟨797798, by rfl⟩ : syracuseStep 4254925 = 1595597) B1595597
theorem B5975309 : Blo 1572484 5975309 := bstep (se 3 (by rfl) ⟨1120370, by rfl⟩ : syracuseStep 5975309 = 2240741) B2240741
theorem B2690417 : Blo 1572484 2690417 := bstep (se 2 (by rfl) ⟨1008906, by rfl⟩ : syracuseStep 2690417 = 2017813) B2017813
theorem B3984785 : Blo 1572484 3984785 := bstep (se 2 (by rfl) ⟨1494294, by rfl⟩ : syracuseStep 3984785 = 2988589) B2988589
theorem B3542417 : Blo 1572484 3542417 := bstep (se 2 (by rfl) ⟨1328406, by rfl⟩ : syracuseStep 3542417 = 2656813) B2656813
theorem B3542435 : Blo 1572484 3542435 := bstep (se 1 (by rfl) ⟨2656826, by rfl⟩ : syracuseStep 3542435 = 5313653) B5313653
theorem B2239921 : Blo 1572484 2239921 := bstep (se 2 (by rfl) ⟨839970, by rfl⟩ : syracuseStep 2239921 = 1679941) B1679941
theorem B3984835 : Blo 1572484 3984835 := bstep (se 1 (by rfl) ⟨2988626, by rfl⟩ : syracuseStep 3984835 = 5977253) B5977253
theorem B3984977 : Blo 1572484 3984977 := bstep (se 2 (by rfl) ⟨1494366, by rfl⟩ : syracuseStep 3984977 = 2988733) B2988733
theorem B13446769 : Blo 1572484 13446769 := bstep (se 2 (by rfl) ⟨5042538, by rfl⟩ : syracuseStep 13446769 = 10085077) B10085077
theorem B7966349 : Blo 1572484 7966349 := bstep (se 3 (by rfl) ⟨1493690, by rfl⟩ : syracuseStep 7966349 = 2987381) B2987381
theorem B5312141 : Blo 1572484 5312141 := bstep (se 3 (by rfl) ⟨996026, by rfl⟩ : syracuseStep 5312141 = 1992053) B1992053
theorem B2985635 : Blo 1572484 2985635 := bstep (se 1 (by rfl) ⟨2239226, by rfl⟩ : syracuseStep 2985635 = 4478453) B4478453
theorem B5312195 : Blo 1572484 5312195 := bstep (se 1 (by rfl) ⟨3984146, by rfl⟩ : syracuseStep 5312195 = 7968293) B7968293
theorem B25857733 : Blo 1572484 25857733 := bstep (se 4 (by rfl) ⟨2424162, by rfl⟩ : syracuseStep 25857733 = 4848325) B4848325
theorem B2690833 : Blo 1572484 2690833 := bstep (se 2 (by rfl) ⟨1009062, by rfl⟩ : syracuseStep 2690833 = 2018125) B2018125
theorem B4542257 : Blo 1572484 4542257 := bstep (se 2 (by rfl) ⟨1703346, by rfl⟩ : syracuseStep 4542257 = 3406693) B3406693
theorem B3190691 : Blo 1572484 3190691 := bstep (se 1 (by rfl) ⟨2393018, by rfl⟩ : syracuseStep 3190691 = 4786037) B4786037
theorem B2985923 : Blo 1572484 2985923 := bstep (se 1 (by rfl) ⟨2239442, by rfl⟩ : syracuseStep 2985923 = 4478885) B4478885
theorem B5312465 : Blo 1572484 5312465 := bstep (se 2 (by rfl) ⟨1992174, by rfl⟩ : syracuseStep 5312465 = 3984349) B3984349
theorem B2519009 : Blo 1572484 2519009 := bstep (se 2 (by rfl) ⟨944628, by rfl⟩ : syracuseStep 2519009 = 1889257) B1889257
theorem B19132469 : Blo 1572484 19132469 := bstep (se 5 (by rfl) ⟨896834, by rfl⟩ : syracuseStep 19132469 = 1793669) B1793669
theorem B2691187 : Blo 1572484 2691187 := bstep (se 1 (by rfl) ⟨2018390, by rfl⟩ : syracuseStep 2691187 = 4036781) B4036781
theorem B2240627 : Blo 1572484 2240627 := bstep (se 1 (by rfl) ⟨1680470, by rfl⟩ : syracuseStep 2240627 = 3360941) B3360941
theorem B18157709 : Blo 1572484 18157709 := bstep (se 3 (by rfl) ⟨3404570, by rfl⟩ : syracuseStep 18157709 = 6809141) B6809141
theorem B2519219 : Blo 1572484 2519219 := bstep (se 1 (by rfl) ⟨1889414, by rfl⟩ : syracuseStep 2519219 = 3778829) B3778829
theorem B21532997 : Blo 1572484 21532997 := bstep (se 4 (by rfl) ⟨2018718, by rfl⟩ : syracuseStep 21532997 = 4037437) B4037437
theorem B5247409 : Blo 1572484 5247409 := bstep (se 2 (by rfl) ⟨1967778, by rfl⟩ : syracuseStep 5247409 = 3935557) B3935557
theorem B40350149 : Blo 1572484 40350149 := bstep (se 4 (by rfl) ⟨3782826, by rfl⟩ : syracuseStep 40350149 = 7565653) B7565653
theorem B14348771 : Blo 1572484 14348771 := bstep (se 1 (by rfl) ⟨10761578, by rfl⟩ : syracuseStep 14348771 = 21523157) B21523157
theorem B7180771 : Blo 1572484 7180771 := bstep (se 1 (by rfl) ⟨5385578, by rfl⟩ : syracuseStep 7180771 = 10771157) B10771157
theorem B5313005 : Blo 1572484 5313005 := bstep (se 3 (by rfl) ⟨996188, by rfl⟩ : syracuseStep 5313005 = 1992377) B1992377
theorem B2691571 : Blo 1572484 2691571 := bstep (se 1 (by rfl) ⟨2018678, by rfl⟩ : syracuseStep 2691571 = 4037357) B4037357
theorem B10080773 : Blo 1572484 10080773 := bstep (se 4 (by rfl) ⟨945072, by rfl⟩ : syracuseStep 10080773 = 1890145) B1890145
theorem B5313059 : Blo 1572484 5313059 := bstep (se 1 (by rfl) ⟨3984794, by rfl⟩ : syracuseStep 5313059 = 7969589) B7969589
theorem B5747249 : Blo 1572484 5747249 := bstep (se 2 (by rfl) ⟨2155218, by rfl⟩ : syracuseStep 5747249 = 4310437) B4310437
theorem B20165233 : Blo 1572484 20165233 := bstep (se 2 (by rfl) ⟨7561962, by rfl⟩ : syracuseStep 20165233 = 15123925) B15123925
theorem B13628017 : Blo 1572484 13628017 := bstep (se 2 (by rfl) ⟨5110506, by rfl⟩ : syracuseStep 13628017 = 10221013) B10221013
theorem B2691731 : Blo 1572484 2691731 := bstep (se 1 (by rfl) ⟨2018798, by rfl⟩ : syracuseStep 2691731 = 4037597) B4037597
theorem B8966861 : Blo 1572484 8966861 := bstep (se 3 (by rfl) ⟨1681286, by rfl⟩ : syracuseStep 8966861 = 3362573) B3362573
theorem B2241265 : Blo 1572484 2241265 := bstep (se 2 (by rfl) ⟨840474, by rfl⟩ : syracuseStep 2241265 = 1680949) B1680949
theorem B5313329 : Blo 1572484 5313329 := bstep (se 2 (by rfl) ⟨1992498, by rfl⟩ : syracuseStep 5313329 = 3984997) B3984997
theorem B7557965 : Blo 1572484 7557965 := bstep (se 3 (by rfl) ⟨1417118, by rfl⟩ : syracuseStep 7557965 = 2834237) B2834237
theorem B2241379 : Blo 1572484 2241379 := bstep (se 1 (by rfl) ⟨1681034, by rfl⟩ : syracuseStep 2241379 = 3362069) B3362069
theorem B2986865 : Blo 1572484 2986865 := bstep (se 2 (by rfl) ⟨1120074, by rfl⟩ : syracuseStep 2986865 = 2240149) B2240149
theorem B3191665 : Blo 1572484 3191665 := bstep (se 2 (by rfl) ⟨1196874, by rfl⟩ : syracuseStep 3191665 = 2393749) B2393749
theorem B2520001 : Blo 1572484 2520001 := bstep (se 2 (by rfl) ⟨945000, by rfl⟩ : syracuseStep 2520001 = 1890001) B1890001
theorem B5043181 : Blo 1572484 5043181 := bstep (se 3 (by rfl) ⟨945596, by rfl⟩ : syracuseStep 5043181 = 1891193) B1891193
theorem B4477997 : Blo 1572484 4477997 := bstep (se 3 (by rfl) ⟨839624, by rfl⟩ : syracuseStep 4477997 = 1679249) B1679249
theorem B8959045 : Blo 1572484 8959045 := bstep (se 4 (by rfl) ⟨839910, by rfl⟩ : syracuseStep 8959045 = 1679821) B1679821
theorem B4150385 : Blo 1572484 4150385 := bstep (se 2 (by rfl) ⟨1556394, by rfl⟩ : syracuseStep 4150385 = 3112789) B3112789
theorem B4478179 : Blo 1572484 4478179 := bstep (se 1 (by rfl) ⟨3358634, by rfl⟩ : syracuseStep 4478179 = 6717269) B6717269
theorem B5977421 : Blo 1572484 5977421 := bstep (se 3 (by rfl) ⟨1120766, by rfl⟩ : syracuseStep 5977421 = 2241533) B2241533
theorem B5313869 : Blo 1572484 5313869 := bstep (se 3 (by rfl) ⟨996350, by rfl⟩ : syracuseStep 5313869 = 1992701) B1992701
theorem B7181681 : Blo 1572484 7181681 := bstep (se 2 (by rfl) ⟨2693130, by rfl⟩ : syracuseStep 7181681 = 5386261) B5386261
theorem B1594819 : Blo 1572484 1594819 := bstep (se 1 (by rfl) ⟨1196114, by rfl⟩ : syracuseStep 1594819 = 2392229) B2392229
theorem B2692721 : Blo 1572484 2692721 := bstep (se 2 (by rfl) ⟨1009770, by rfl⟩ : syracuseStep 2692721 = 2019541) B2019541
theorem B2520803 : Blo 1572484 2520803 := bstep (se 1 (by rfl) ⟨1890602, by rfl⟩ : syracuseStep 2520803 = 3781205) B3781205
theorem B2987761 : Blo 1572484 2987761 := bstep (se 2 (by rfl) ⟨1120410, by rfl⟩ : syracuseStep 2987761 = 2240821) B2240821
theorem B19396421 : Blo 1572484 19396421 := bstep (se 4 (by rfl) ⟨1818414, by rfl⟩ : syracuseStep 19396421 = 3636829) B3636829
theorem B10213219 : Blo 1572484 10213219 := bstep (se 1 (by rfl) ⟨7659914, by rfl⟩ : syracuseStep 10213219 = 15319829) B15319829
theorem B2987921 : Blo 1572484 2987921 := bstep (se 2 (by rfl) ⟨1120470, by rfl⟩ : syracuseStep 2987921 = 2240941) B2240941
theorem B2332577 : Blo 1572484 2332577 := bstep (se 2 (by rfl) ⟨874716, by rfl⟩ : syracuseStep 2332577 = 1749433) B1749433
theorem B2127809 : Blo 1572484 2127809 := bstep (se 2 (by rfl) ⟨797928, by rfl⟩ : syracuseStep 2127809 = 1595857) B1595857
theorem B3831907 : Blo 1572484 3831907 := bstep (se 1 (by rfl) ⟨2873930, by rfl⟩ : syracuseStep 3831907 = 5747861) B5747861
theorem B30242929 : Blo 1572484 30242929 := bstep (se 2 (by rfl) ⟨11341098, by rfl⟩ : syracuseStep 30242929 = 22682197) B22682197
theorem B22689989 : Blo 1572484 22689989 := bstep (se 4 (by rfl) ⟨2127186, by rfl⟩ : syracuseStep 22689989 = 4254373) B4254373
theorem B38811845 : Blo 1572484 38811845 := bstep (se 4 (by rfl) ⟨3638610, by rfl⟩ : syracuseStep 38811845 = 7277221) B7277221
theorem B8624333 : Blo 1572484 8624333 := bstep (se 3 (by rfl) ⟨1617062, by rfl⟩ : syracuseStep 8624333 = 3234125) B3234125
theorem B2521315 : Blo 1572484 2521315 := bstep (se 1 (by rfl) ⟨1890986, by rfl⟩ : syracuseStep 2521315 = 3781973) B3781973
theorem B2988323 : Blo 1572484 2988323 := bstep (se 1 (by rfl) ⟨2241242, by rfl⟩ : syracuseStep 2988323 = 4482485) B4482485
theorem B6723917 : Blo 1572484 6723917 := bstep (se 3 (by rfl) ⟨1260734, by rfl⟩ : syracuseStep 6723917 = 2521469) B2521469
theorem B5454253 : Blo 1572484 5454253 := bstep (se 3 (by rfl) ⟨1022672, by rfl⟩ : syracuseStep 5454253 = 2045345) B2045345
theorem B6380003 : Blo 1572484 6380003 := bstep (se 1 (by rfl) ⟨4785002, by rfl⟩ : syracuseStep 6380003 = 9570005) B9570005
theorem B7969265 : Blo 1572484 7969265 := bstep (se 2 (by rfl) ⟨2988474, by rfl⟩ : syracuseStep 7969265 = 5976949) B5976949
theorem B7961165 : Blo 1572484 7961165 := bstep (se 3 (by rfl) ⟨1492718, by rfl⟩ : syracuseStep 7961165 = 2985437) B2985437
theorem B4479569 : Blo 1572484 4479569 := bstep (se 2 (by rfl) ⟨1679838, by rfl⟩ : syracuseStep 4479569 = 3359677) B3359677
theorem B5454481 : Blo 1572484 5454481 := bstep (se 2 (by rfl) ⟨2045430, by rfl⟩ : syracuseStep 5454481 = 4090861) B4090861
theorem B2521859 : Blo 1572484 2521859 := bstep (se 1 (by rfl) ⟨1891394, by rfl⟩ : syracuseStep 2521859 = 3782789) B3782789
theorem B5667725 : Blo 1572484 5667725 := bstep (se 3 (by rfl) ⟨1062698, by rfl⟩ : syracuseStep 5667725 = 2125397) B2125397
theorem B5307281 : Blo 1572484 5307281 := bstep (se 2 (by rfl) ⟨1990230, by rfl⟩ : syracuseStep 5307281 = 3980461) B3980461
theorem B8961029 : Blo 1572484 8961029 := bstep (se 4 (by rfl) ⟨840096, by rfl⟩ : syracuseStep 8961029 = 1680193) B1680193
theorem B3538097 : Blo 1572484 3538097 := bstep (se 2 (by rfl) ⟨1326786, by rfl⟩ : syracuseStep 3538097 = 2653573) B2653573
theorem B3538115 : Blo 1572484 3538115 := bstep (se 1 (by rfl) ⟨2653586, by rfl⟩ : syracuseStep 3538115 = 5307173) B5307173
theorem B10075441 : Blo 1572484 10075441 := bstep (se 2 (by rfl) ⟨3778290, by rfl⟩ : syracuseStep 10075441 = 7556581) B7556581
theorem B5750129 : Blo 1572484 5750129 := bstep (se 2 (by rfl) ⟨2156298, by rfl⟩ : syracuseStep 5750129 = 4312597) B4312597
theorem B5307821 : Blo 1572484 5307821 := bstep (se 3 (by rfl) ⟨995216, by rfl⟩ : syracuseStep 5307821 = 1990433) B1990433
theorem B60505541 : Blo 1572484 60505541 := bstep (se 4 (by rfl) ⟨5672394, by rfl⟩ : syracuseStep 60505541 = 11344789) B11344789
theorem B2358737 : Blo 1572484 2358737 := bstep (se 2 (by rfl) ⟨884526, by rfl⟩ : syracuseStep 2358737 = 1769053) B1769053
theorem B3538385 : Blo 1572484 3538385 := bstep (se 2 (by rfl) ⟨1326894, by rfl⟩ : syracuseStep 3538385 = 2653789) B2653789
theorem B2358755 : Blo 1572484 2358755 := bstep (se 1 (by rfl) ⟨1769066, by rfl⟩ : syracuseStep 2358755 = 3538133) B3538133
theorem B3538403 : Blo 1572484 3538403 := bstep (se 1 (by rfl) ⟨2653802, by rfl⟩ : syracuseStep 3538403 = 5307605) B5307605
theorem B5307875 : Blo 1572484 5307875 := bstep (se 1 (by rfl) ⟨3980906, by rfl⟩ : syracuseStep 5307875 = 7961813) B7961813
theorem B2653681 : Blo 1572484 2653681 := bstep (se 2 (by rfl) ⟨995130, by rfl⟩ : syracuseStep 2653681 = 1990261) B1990261
theorem B3980785 : Blo 1572484 3980785 := bstep (se 2 (by rfl) ⟨1492794, by rfl⟩ : syracuseStep 3980785 = 2985589) B2985589
theorem B2358785 : Blo 1572484 2358785 := bstep (se 2 (by rfl) ⟨884544, by rfl⟩ : syracuseStep 2358785 = 1769089) B1769089
theorem B4480525 : Blo 1572484 4480525 := bstep (se 3 (by rfl) ⟨840098, by rfl⟩ : syracuseStep 4480525 = 1680197) B1680197
theorem B2358803 : Blo 1572484 2358803 := bstep (se 1 (by rfl) ⟨1769102, by rfl⟩ : syracuseStep 2358803 = 3538205) B3538205
theorem B2653715 : Blo 1572484 2653715 := bstep (se 1 (by rfl) ⟨1990286, by rfl⟩ : syracuseStep 2653715 = 3980573) B3980573
theorem B2358833 : Blo 1572484 2358833 := bstep (se 2 (by rfl) ⟨884562, by rfl⟩ : syracuseStep 2358833 = 1769125) B1769125
theorem B2358851 : Blo 1572484 2358851 := bstep (se 1 (by rfl) ⟨1769138, by rfl⟩ : syracuseStep 2358851 = 3538277) B3538277
theorem B2358881 : Blo 1572484 2358881 := bstep (se 2 (by rfl) ⟨884580, by rfl⟩ : syracuseStep 2358881 = 1769161) B1769161
theorem B2358899 : Blo 1572484 2358899 := bstep (se 1 (by rfl) ⟨1769174, by rfl⟩ : syracuseStep 2358899 = 3538349) B3538349
theorem B5037709 : Blo 1572484 5037709 := bstep (se 3 (by rfl) ⟨944570, by rfl⟩ : syracuseStep 5037709 = 1889141) B1889141
theorem B2358929 : Blo 1572484 2358929 := bstep (se 2 (by rfl) ⟨884598, by rfl⟩ : syracuseStep 2358929 = 1769197) B1769197
theorem B1572499 : Blo 1572484 1572499 := bstep (se 1 (by rfl) ⟨1179374, by rfl⟩ : syracuseStep 1572499 = 2358749) B2358749
theorem B1769107 : Blo 1572484 1769107 := bstep (se 1 (by rfl) ⟨1326830, by rfl⟩ : syracuseStep 1769107 = 2653661) B2653661
theorem B2653843 : Blo 1572484 2653843 := bstep (se 1 (by rfl) ⟨1990382, by rfl⟩ : syracuseStep 2653843 = 3980765) B3980765
theorem B1572515 : Blo 1572484 1572515 := bstep (se 1 (by rfl) ⟨1179386, by rfl⟩ : syracuseStep 1572515 = 2358773) B2358773
theorem B2358947 : Blo 1572484 2358947 := bstep (se 1 (by rfl) ⟨1769210, by rfl⟩ : syracuseStep 2358947 = 3538421) B3538421
theorem B1572531 : Blo 1572484 1572531 := bstep (se 1 (by rfl) ⟨1179398, by rfl⟩ : syracuseStep 1572531 = 2358797) B2358797
theorem B2358977 : Blo 1572484 2358977 := bstep (se 2 (by rfl) ⟨884616, by rfl⟩ : syracuseStep 2358977 = 1769233) B1769233
theorem B1572547 : Blo 1572484 1572547 := bstep (se 1 (by rfl) ⟨1179410, by rfl⟩ : syracuseStep 1572547 = 2358821) B2358821
theorem B1572563 : Blo 1572484 1572563 := bstep (se 1 (by rfl) ⟨1179422, by rfl⟩ : syracuseStep 1572563 = 2358845) B2358845
theorem B2358995 : Blo 1572484 2358995 := bstep (se 1 (by rfl) ⟨1769246, by rfl⟩ : syracuseStep 2358995 = 3538493) B3538493
theorem B1572579 : Blo 1572484 1572579 := bstep (se 1 (by rfl) ⟨1179434, by rfl⟩ : syracuseStep 1572579 = 2358869) B2358869
theorem B2359025 : Blo 1572484 2359025 := bstep (se 2 (by rfl) ⟨884634, by rfl⟩ : syracuseStep 2359025 = 1769269) B1769269
theorem B1572595 : Blo 1572484 1572595 := bstep (se 1 (by rfl) ⟨1179446, by rfl⟩ : syracuseStep 1572595 = 2358893) B2358893
theorem B3538673 : Blo 1572484 3538673 := bstep (se 2 (by rfl) ⟨1327002, by rfl⟩ : syracuseStep 3538673 = 2654005) B2654005
theorem B5308145 : Blo 1572484 5308145 := bstep (se 2 (by rfl) ⟨1990554, by rfl⟩ : syracuseStep 5308145 = 3981109) B3981109
theorem B4480753 : Blo 1572484 4480753 := bstep (se 2 (by rfl) ⟨1680282, by rfl⟩ : syracuseStep 4480753 = 3360565) B3360565
theorem B1572611 : Blo 1572484 1572611 := bstep (se 1 (by rfl) ⟨1179458, by rfl⟩ : syracuseStep 1572611 = 2358917) B2358917
theorem B2359043 : Blo 1572484 2359043 := bstep (se 1 (by rfl) ⟨1769282, by rfl⟩ : syracuseStep 2359043 = 3538565) B3538565
theorem B3538691 : Blo 1572484 3538691 := bstep (se 1 (by rfl) ⟨2654018, by rfl⟩ : syracuseStep 3538691 = 5308037) B5308037
theorem B3981059 : Blo 1572484 3981059 := bstep (se 1 (by rfl) ⟨2985794, by rfl⟩ : syracuseStep 3981059 = 5971589) B5971589
theorem B1572627 : Blo 1572484 1572627 := bstep (se 1 (by rfl) ⟨1179470, by rfl⟩ : syracuseStep 1572627 = 2358941) B2358941
theorem B2359073 : Blo 1572484 2359073 := bstep (se 2 (by rfl) ⟨884652, by rfl⟩ : syracuseStep 2359073 = 1769305) B1769305
theorem B1572643 : Blo 1572484 1572643 := bstep (se 1 (by rfl) ⟨1179482, by rfl⟩ : syracuseStep 1572643 = 2358965) B2358965
theorem B1769251 : Blo 1572484 1769251 := bstep (se 1 (by rfl) ⟨1326938, by rfl⟩ : syracuseStep 1769251 = 2653877) B2653877
theorem B2653985 : Blo 1572484 2653985 := bstep (se 2 (by rfl) ⟨995244, by rfl⟩ : syracuseStep 2653985 = 1990489) B1990489
theorem B1572659 : Blo 1572484 1572659 := bstep (se 1 (by rfl) ⟨1179494, by rfl⟩ : syracuseStep 1572659 = 2358989) B2358989
theorem B2359091 : Blo 1572484 2359091 := bstep (se 1 (by rfl) ⟨1769318, by rfl⟩ : syracuseStep 2359091 = 3538637) B3538637
theorem B1572675 : Blo 1572484 1572675 := bstep (se 1 (by rfl) ⟨1179506, by rfl⟩ : syracuseStep 1572675 = 2359013) B2359013
theorem B2359121 : Blo 1572484 2359121 := bstep (se 2 (by rfl) ⟨884670, by rfl⟩ : syracuseStep 2359121 = 1769341) B1769341
theorem B1572691 : Blo 1572484 1572691 := bstep (se 1 (by rfl) ⟨1179518, by rfl⟩ : syracuseStep 1572691 = 2359037) B2359037
theorem B4308835 : Blo 1572484 4308835 := bstep (se 1 (by rfl) ⟨3231626, by rfl⟩ : syracuseStep 4308835 = 6463253) B6463253
theorem B1572707 : Blo 1572484 1572707 := bstep (se 1 (by rfl) ⟨1179530, by rfl⟩ : syracuseStep 1572707 = 2359061) B2359061
theorem B2359139 : Blo 1572484 2359139 := bstep (se 1 (by rfl) ⟨1769354, by rfl⟩ : syracuseStep 2359139 = 3538709) B3538709
theorem B1572723 : Blo 1572484 1572723 := bstep (se 1 (by rfl) ⟨1179542, by rfl⟩ : syracuseStep 1572723 = 2359085) B2359085
theorem B2359169 : Blo 1572484 2359169 := bstep (se 2 (by rfl) ⟨884688, by rfl⟩ : syracuseStep 2359169 = 1769377) B1769377
theorem B1572739 : Blo 1572484 1572739 := bstep (se 1 (by rfl) ⟨1179554, by rfl⟩ : syracuseStep 1572739 = 2359109) B2359109
theorem B1572755 : Blo 1572484 1572755 := bstep (se 1 (by rfl) ⟨1179566, by rfl⟩ : syracuseStep 1572755 = 2359133) B2359133
theorem B2359187 : Blo 1572484 2359187 := bstep (se 1 (by rfl) ⟨1769390, by rfl⟩ : syracuseStep 2359187 = 3538781) B3538781
theorem B1572771 : Blo 1572484 1572771 := bstep (se 1 (by rfl) ⟨1179578, by rfl⟩ : syracuseStep 1572771 = 2359157) B2359157
theorem B2654113 : Blo 1572484 2654113 := bstep (se 2 (by rfl) ⟨995292, by rfl⟩ : syracuseStep 2654113 = 1990585) B1990585
theorem B2359217 : Blo 1572484 2359217 := bstep (se 2 (by rfl) ⟨884706, by rfl⟩ : syracuseStep 2359217 = 1769413) B1769413
theorem B1572787 : Blo 1572484 1572787 := bstep (se 1 (by rfl) ⟨1179590, by rfl⟩ : syracuseStep 1572787 = 2359181) B2359181
theorem B1769395 : Blo 1572484 1769395 := bstep (se 1 (by rfl) ⟨1327046, by rfl⟩ : syracuseStep 1769395 = 2654093) B2654093
theorem B3981251 : Blo 1572484 3981251 := bstep (se 1 (by rfl) ⟨2985938, by rfl⟩ : syracuseStep 3981251 = 5971877) B5971877
theorem B1572803 : Blo 1572484 1572803 := bstep (se 1 (by rfl) ⟨1179602, by rfl⟩ : syracuseStep 1572803 = 2359205) B2359205
theorem B1990595 : Blo 1572484 1990595 := bstep (se 1 (by rfl) ⟨1492946, by rfl⟩ : syracuseStep 1990595 = 2985893) B2985893
theorem B2359235 : Blo 1572484 2359235 := bstep (se 1 (by rfl) ⟨1769426, by rfl⟩ : syracuseStep 2359235 = 3538853) B3538853
theorem B2654147 : Blo 1572484 2654147 := bstep (se 1 (by rfl) ⟨1990610, by rfl⟩ : syracuseStep 2654147 = 3981221) B3981221
theorem B1572819 : Blo 1572484 1572819 := bstep (se 1 (by rfl) ⟨1179614, by rfl⟩ : syracuseStep 1572819 = 2359229) B2359229
theorem B2359265 : Blo 1572484 2359265 := bstep (se 2 (by rfl) ⟨884724, by rfl⟩ : syracuseStep 2359265 = 1769449) B1769449
theorem B1572835 : Blo 1572484 1572835 := bstep (se 1 (by rfl) ⟨1179626, by rfl⟩ : syracuseStep 1572835 = 2359253) B2359253
theorem B1572851 : Blo 1572484 1572851 := bstep (se 1 (by rfl) ⟨1179638, by rfl⟩ : syracuseStep 1572851 = 2359277) B2359277
theorem B2359283 : Blo 1572484 2359283 := bstep (se 1 (by rfl) ⟨1769462, by rfl⟩ : syracuseStep 2359283 = 3538925) B3538925
theorem B2359307 : Blo 1572484 2359307 := bstep (se 1 (by rfl) ⟨1769480, by rfl⟩ : syracuseStep 2359307 = 3538961) B3538961
theorem B1572875 : Blo 1572484 1572875 := bstep (se 1 (by rfl) ⟨1179656, by rfl⟩ : syracuseStep 1572875 = 2359313) B2359313
theorem B2359319 : Blo 1572484 2359319 := bstep (se 1 (by rfl) ⟨1769489, by rfl⟩ : syracuseStep 2359319 = 3538979) B3538979
theorem B1572887 : Blo 1572484 1572887 := bstep (se 1 (by rfl) ⟨1179665, by rfl⟩ : syracuseStep 1572887 = 2359331) B2359331
theorem B12754979 : Blo 1572484 12754979 := bstep (se 1 (by rfl) ⟨9566234, by rfl⟩ : syracuseStep 12754979 = 19132469) B19132469
theorem B1572907 : Blo 1572484 1572907 := bstep (se 1 (by rfl) ⟨1179680, by rfl⟩ : syracuseStep 1572907 = 2359361) B2359361
theorem B1572919 : Blo 1572484 1572919 := bstep (se 1 (by rfl) ⟨1179689, by rfl⟩ : syracuseStep 1572919 = 2359379) B2359379
theorem B1572939 : Blo 1572484 1572939 := bstep (se 1 (by rfl) ⟨1179704, by rfl⟩ : syracuseStep 1572939 = 2359409) B2359409
theorem B1572951 : Blo 1572484 1572951 := bstep (se 1 (by rfl) ⟨1179713, by rfl⟩ : syracuseStep 1572951 = 2359427) B2359427
theorem B2834519 : Blo 1572484 2834519 := bstep (se 1 (by rfl) ⟨2125889, by rfl⟩ : syracuseStep 2834519 = 4251779) B4251779
theorem B3539033 : Blo 1572484 3539033 := bstep (se 2 (by rfl) ⟨1327137, by rfl⟩ : syracuseStep 3539033 = 2654275) B2654275
theorem B2359385 : Blo 1572484 2359385 := bstep (se 2 (by rfl) ⟨884769, by rfl⟩ : syracuseStep 2359385 = 1769539) B1769539
theorem B1572971 : Blo 1572484 1572971 := bstep (se 1 (by rfl) ⟨1179728, by rfl⟩ : syracuseStep 1572971 = 2359457) B2359457
theorem B1572983 : Blo 1572484 1572983 := bstep (se 1 (by rfl) ⟨1179737, by rfl⟩ : syracuseStep 1572983 = 2359475) B2359475
theorem B1769611 : Blo 1572484 1769611 := bstep (se 1 (by rfl) ⟨1327208, by rfl⟩ : syracuseStep 1769611 = 2654417) B2654417
theorem B1573003 : Blo 1572484 1573003 := bstep (se 1 (by rfl) ⟨1179752, by rfl⟩ : syracuseStep 1573003 = 2359505) B2359505
theorem B1573015 : Blo 1572484 1573015 := bstep (se 1 (by rfl) ⟨1179761, by rfl⟩ : syracuseStep 1573015 = 2359523) B2359523
theorem B1573035 : Blo 1572484 1573035 := bstep (se 1 (by rfl) ⟨1179776, by rfl⟩ : syracuseStep 1573035 = 2359553) B2359553
theorem B3539123 : Blo 1572484 3539123 := bstep (se 1 (by rfl) ⟨2654342, by rfl⟩ : syracuseStep 3539123 = 5308685) B5308685
theorem B1573047 : Blo 1572484 1573047 := bstep (se 1 (by rfl) ⟨1179785, by rfl⟩ : syracuseStep 1573047 = 2359571) B2359571
theorem B2359499 : Blo 1572484 2359499 := bstep (se 1 (by rfl) ⟨1769624, by rfl⟩ : syracuseStep 2359499 = 3539249) B3539249
theorem B2834635 : Blo 1572484 2834635 := bstep (se 1 (by rfl) ⟨2125976, by rfl⟩ : syracuseStep 2834635 = 4251953) B4251953
theorem B1573067 : Blo 1572484 1573067 := bstep (se 1 (by rfl) ⟨1179800, by rfl⟩ : syracuseStep 1573067 = 2359601) B2359601
theorem B3539159 : Blo 1572484 3539159 := bstep (se 1 (by rfl) ⟨2654369, by rfl⟩ : syracuseStep 3539159 = 5308739) B5308739
theorem B5669081 : Blo 1572484 5669081 := bstep (se 2 (by rfl) ⟨2125905, by rfl⟩ : syracuseStep 5669081 = 4251811) B4251811
theorem B2359511 : Blo 1572484 2359511 := bstep (se 1 (by rfl) ⟨1769633, by rfl⟩ : syracuseStep 2359511 = 3539267) B3539267
theorem B1573079 : Blo 1572484 1573079 := bstep (se 1 (by rfl) ⟨1179809, by rfl⟩ : syracuseStep 1573079 = 2359619) B2359619
theorem B1573099 : Blo 1572484 1573099 := bstep (se 1 (by rfl) ⟨1179824, by rfl⟩ : syracuseStep 1573099 = 2359649) B2359649
theorem B1769719 : Blo 1572484 1769719 := bstep (se 1 (by rfl) ⟨1327289, by rfl⟩ : syracuseStep 1769719 = 2654579) B2654579
theorem B1573111 : Blo 1572484 1573111 := bstep (se 1 (by rfl) ⟨1179833, by rfl⟩ : syracuseStep 1573111 = 2359667) B2359667
theorem B1573131 : Blo 1572484 1573131 := bstep (se 1 (by rfl) ⟨1179848, by rfl⟩ : syracuseStep 1573131 = 2359697) B2359697
theorem B1573143 : Blo 1572484 1573143 := bstep (se 1 (by rfl) ⟨1179857, by rfl⟩ : syracuseStep 1573143 = 2359715) B2359715
theorem B2359577 : Blo 1572484 2359577 := bstep (se 2 (by rfl) ⟨884841, by rfl⟩ : syracuseStep 2359577 = 1769683) B1769683
theorem B1573163 : Blo 1572484 1573163 := bstep (se 1 (by rfl) ⟨1179872, by rfl⟩ : syracuseStep 1573163 = 2359745) B2359745
theorem B430793005 : Blo 1572484 430793005 := bstep (se 3 (by rfl) ⟨80773688, by rfl⟩ : syracuseStep 430793005 = 161547377) B161547377
theorem B3359027 : Blo 1572484 3359027 := bstep (se 1 (by rfl) ⟨2519270, by rfl⟩ : syracuseStep 3359027 = 5038541) B5038541
theorem B1573175 : Blo 1572484 1573175 := bstep (se 1 (by rfl) ⟨1179881, by rfl⟩ : syracuseStep 1573175 = 2359763) B2359763
theorem B4481345 : Blo 1572484 4481345 := bstep (se 2 (by rfl) ⟨1680504, by rfl⟩ : syracuseStep 4481345 = 3361009) B3361009
theorem B1573195 : Blo 1572484 1573195 := bstep (se 1 (by rfl) ⟨1179896, by rfl⟩ : syracuseStep 1573195 = 2359793) B2359793
theorem B1573207 : Blo 1572484 1573207 := bstep (se 1 (by rfl) ⟨1179905, by rfl⟩ : syracuseStep 1573207 = 2359811) B2359811
theorem B4481369 : Blo 1572484 4481369 := bstep (se 2 (by rfl) ⟨1680513, by rfl⟩ : syracuseStep 4481369 = 3361027) B3361027
theorem B11493733 : Blo 1572484 11493733 := bstep (se 4 (by rfl) ⟨1077537, by rfl⟩ : syracuseStep 11493733 = 2155075) B2155075
theorem B1573227 : Blo 1572484 1573227 := bstep (se 1 (by rfl) ⟨1179920, by rfl⟩ : syracuseStep 1573227 = 2359841) B2359841
theorem B1573239 : Blo 1572484 1573239 := bstep (se 1 (by rfl) ⟨1179929, by rfl⟩ : syracuseStep 1573239 = 2359859) B2359859
theorem B3539339 : Blo 1572484 3539339 := bstep (se 1 (by rfl) ⟨2654504, by rfl⟩ : syracuseStep 3539339 = 5309009) B5309009
theorem B2359691 : Blo 1572484 2359691 := bstep (se 1 (by rfl) ⟨1769768, by rfl⟩ : syracuseStep 2359691 = 3539537) B3539537
theorem B1573259 : Blo 1572484 1573259 := bstep (se 1 (by rfl) ⟨1179944, by rfl⟩ : syracuseStep 1573259 = 2359889) B2359889
theorem B2359703 : Blo 1572484 2359703 := bstep (se 1 (by rfl) ⟨1769777, by rfl⟩ : syracuseStep 2359703 = 3539555) B3539555
theorem B1573271 : Blo 1572484 1573271 := bstep (se 1 (by rfl) ⟨1179953, by rfl⟩ : syracuseStep 1573271 = 2359907) B2359907
theorem B1769899 : Blo 1572484 1769899 := bstep (se 1 (by rfl) ⟨1327424, by rfl⟩ : syracuseStep 1769899 = 2654849) B2654849
theorem B1573291 : Blo 1572484 1573291 := bstep (se 1 (by rfl) ⟨1179968, by rfl⟩ : syracuseStep 1573291 = 2359937) B2359937
theorem B1573303 : Blo 1572484 1573303 := bstep (se 1 (by rfl) ⟨1179977, by rfl⟩ : syracuseStep 1573303 = 2359955) B2359955
theorem B1794487 : Blo 1572484 1794487 := bstep (se 1 (by rfl) ⟨1345865, by rfl⟩ : syracuseStep 1794487 = 2691731) B2691731
theorem B3539393 : Blo 1572484 3539393 := bstep (se 2 (by rfl) ⟨1327272, by rfl⟩ : syracuseStep 3539393 = 2654545) B2654545
theorem B1573323 : Blo 1572484 1573323 := bstep (se 1 (by rfl) ⟨1179992, by rfl⟩ : syracuseStep 1573323 = 2359985) B2359985
theorem B1573335 : Blo 1572484 1573335 := bstep (se 1 (by rfl) ⟨1180001, by rfl⟩ : syracuseStep 1573335 = 2360003) B2360003
theorem B2359769 : Blo 1572484 2359769 := bstep (se 2 (by rfl) ⟨884913, by rfl⟩ : syracuseStep 2359769 = 1769827) B1769827
theorem B6717917 : Blo 1572484 6717917 := bstep (se 3 (by rfl) ⟨1259609, by rfl⟩ : syracuseStep 6717917 = 2519219) B2519219
theorem B1573355 : Blo 1572484 1573355 := bstep (se 1 (by rfl) ⟨1180016, by rfl⟩ : syracuseStep 1573355 = 2360033) B2360033
theorem B1573367 : Blo 1572484 1573367 := bstep (se 1 (by rfl) ⟨1180025, by rfl⟩ : syracuseStep 1573367 = 2360051) B2360051
theorem B1573387 : Blo 1572484 1573387 := bstep (se 1 (by rfl) ⟨1180040, by rfl⟩ : syracuseStep 1573387 = 2360081) B2360081
theorem B1770007 : Blo 1572484 1770007 := bstep (se 1 (by rfl) ⟨1327505, by rfl⟩ : syracuseStep 1770007 = 2655011) B2655011
theorem B1573399 : Blo 1572484 1573399 := bstep (se 1 (by rfl) ⟨1180049, by rfl⟩ : syracuseStep 1573399 = 2360099) B2360099
theorem B1573419 : Blo 1572484 1573419 := bstep (se 1 (by rfl) ⟨1180064, by rfl⟩ : syracuseStep 1573419 = 2360129) B2360129
theorem B5038643 : Blo 1572484 5038643 := bstep (se 1 (by rfl) ⟨3778982, by rfl⟩ : syracuseStep 5038643 = 7557965) B7557965
theorem B1573431 : Blo 1572484 1573431 := bstep (se 1 (by rfl) ⟨1180073, by rfl⟩ : syracuseStep 1573431 = 2360147) B2360147
theorem B6996545 : Blo 1572484 6996545 := bstep (se 2 (by rfl) ⟨2623704, by rfl⟩ : syracuseStep 6996545 = 5247409) B5247409
theorem B3981899 : Blo 1572484 3981899 := bstep (se 1 (by rfl) ⟨2986424, by rfl⟩ : syracuseStep 3981899 = 5972849) B5972849
theorem B2654795 : Blo 1572484 2654795 := bstep (se 1 (by rfl) ⟨1991096, by rfl⟩ : syracuseStep 2654795 = 3982193) B3982193
theorem B2359883 : Blo 1572484 2359883 := bstep (se 1 (by rfl) ⟨1769912, by rfl⟩ : syracuseStep 2359883 = 3539825) B3539825
theorem B1991243 : Blo 1572484 1991243 := bstep (se 1 (by rfl) ⟨1493432, by rfl⟩ : syracuseStep 1991243 = 2986865) B2986865
theorem B1573451 : Blo 1572484 1573451 := bstep (se 1 (by rfl) ⟨1180088, by rfl⟩ : syracuseStep 1573451 = 2360177) B2360177
theorem B2359895 : Blo 1572484 2359895 := bstep (se 1 (by rfl) ⟨1769921, by rfl⟩ : syracuseStep 2359895 = 3539843) B3539843
theorem B1573463 : Blo 1572484 1573463 := bstep (se 1 (by rfl) ⟨1180097, by rfl⟩ : syracuseStep 1573463 = 2360195) B2360195
theorem B14352997 : Blo 1572484 14352997 := bstep (se 4 (by rfl) ⟨1345593, by rfl⟩ : syracuseStep 14352997 = 2691187) B2691187
theorem B1573483 : Blo 1572484 1573483 := bstep (se 1 (by rfl) ⟨1180112, by rfl⟩ : syracuseStep 1573483 = 2360225) B2360225
theorem B1573495 : Blo 1572484 1573495 := bstep (se 1 (by rfl) ⟨1180121, by rfl⟩ : syracuseStep 1573495 = 2360243) B2360243
theorem B1573515 : Blo 1572484 1573515 := bstep (se 1 (by rfl) ⟨1180136, by rfl⟩ : syracuseStep 1573515 = 2360273) B2360273
theorem B1573527 : Blo 1572484 1573527 := bstep (se 1 (by rfl) ⟨1180145, by rfl⟩ : syracuseStep 1573527 = 2360291) B2360291
theorem B3539609 : Blo 1572484 3539609 := bstep (se 2 (by rfl) ⟨1327353, by rfl⟩ : syracuseStep 3539609 = 2654707) B2654707
theorem B2359961 : Blo 1572484 2359961 := bstep (se 2 (by rfl) ⟨884985, by rfl⟩ : syracuseStep 2359961 = 1769971) B1769971
theorem B3588761 : Blo 1572484 3588761 := bstep (se 2 (by rfl) ⟨1345785, by rfl⟩ : syracuseStep 3588761 = 2691571) B2691571
theorem B8077975 : Blo 1572484 8077975 := bstep (se 1 (by rfl) ⟨6058481, by rfl⟩ : syracuseStep 8077975 = 12116963) B12116963
theorem B1573547 : Blo 1572484 1573547 := bstep (se 1 (by rfl) ⟨1180160, by rfl⟩ : syracuseStep 1573547 = 2360321) B2360321
theorem B1573559 : Blo 1572484 1573559 := bstep (se 1 (by rfl) ⟨1180169, by rfl⟩ : syracuseStep 1573559 = 2360339) B2360339
theorem B2654923 : Blo 1572484 2654923 := bstep (se 1 (by rfl) ⟨1991192, by rfl⟩ : syracuseStep 2654923 = 3982385) B3982385
theorem B1770187 : Blo 1572484 1770187 := bstep (se 1 (by rfl) ⟨1327640, by rfl⟩ : syracuseStep 1770187 = 2655281) B2655281
theorem B1573579 : Blo 1572484 1573579 := bstep (se 1 (by rfl) ⟨1180184, by rfl⟩ : syracuseStep 1573579 = 2360369) B2360369
theorem B1573591 : Blo 1572484 1573591 := bstep (se 1 (by rfl) ⟨1180193, by rfl⟩ : syracuseStep 1573591 = 2360387) B2360387
theorem B1573611 : Blo 1572484 1573611 := bstep (se 1 (by rfl) ⟨1180208, by rfl⟩ : syracuseStep 1573611 = 2360417) B2360417
theorem B3539699 : Blo 1572484 3539699 := bstep (se 1 (by rfl) ⟨2654774, by rfl⟩ : syracuseStep 3539699 = 5309549) B5309549
theorem B1573623 : Blo 1572484 1573623 := bstep (se 1 (by rfl) ⟨1180217, by rfl⟩ : syracuseStep 1573623 = 2360435) B2360435
theorem B2360075 : Blo 1572484 2360075 := bstep (se 1 (by rfl) ⟨1770056, by rfl⟩ : syracuseStep 2360075 = 3540113) B3540113
theorem B1573643 : Blo 1572484 1573643 := bstep (se 1 (by rfl) ⟨1180232, by rfl⟩ : syracuseStep 1573643 = 2360465) B2360465
theorem B3539735 : Blo 1572484 3539735 := bstep (se 1 (by rfl) ⟨2654801, by rfl⟩ : syracuseStep 3539735 = 5309603) B5309603
theorem B2360087 : Blo 1572484 2360087 := bstep (se 1 (by rfl) ⟨1770065, by rfl⟩ : syracuseStep 2360087 = 3540131) B3540131
theorem B1573655 : Blo 1572484 1573655 := bstep (se 1 (by rfl) ⟨1180241, by rfl⟩ : syracuseStep 1573655 = 2360483) B2360483
theorem B1573675 : Blo 1572484 1573675 := bstep (se 1 (by rfl) ⟨1180256, by rfl⟩ : syracuseStep 1573675 = 2360513) B2360513
theorem B1770295 : Blo 1572484 1770295 := bstep (se 1 (by rfl) ⟨1327721, by rfl⟩ : syracuseStep 1770295 = 2655443) B2655443
theorem B1573687 : Blo 1572484 1573687 := bstep (se 1 (by rfl) ⟨1180265, by rfl⟩ : syracuseStep 1573687 = 2360531) B2360531
theorem B26886977 : Blo 1572484 26886977 := bstep (se 2 (by rfl) ⟨10082616, by rfl⟩ : syracuseStep 26886977 = 20165233) B20165233
theorem B1573707 : Blo 1572484 1573707 := bstep (se 1 (by rfl) ⟨1180280, by rfl⟩ : syracuseStep 1573707 = 2360561) B2360561
theorem B1573719 : Blo 1572484 1573719 := bstep (se 1 (by rfl) ⟨1180289, by rfl⟩ : syracuseStep 1573719 = 2360579) B2360579
theorem B2655065 : Blo 1572484 2655065 := bstep (se 2 (by rfl) ⟨995649, by rfl⟩ : syracuseStep 2655065 = 1991299) B1991299
theorem B2360153 : Blo 1572484 2360153 := bstep (se 2 (by rfl) ⟨885057, by rfl⟩ : syracuseStep 2360153 = 1770115) B1770115
theorem B1573739 : Blo 1572484 1573739 := bstep (se 1 (by rfl) ⟨1180304, by rfl⟩ : syracuseStep 1573739 = 2360609) B2360609
theorem B1573751 : Blo 1572484 1573751 := bstep (se 1 (by rfl) ⟨1180313, by rfl⟩ : syracuseStep 1573751 = 2360627) B2360627
theorem B1573771 : Blo 1572484 1573771 := bstep (se 1 (by rfl) ⟨1180328, by rfl⟩ : syracuseStep 1573771 = 2360657) B2360657
theorem B1573783 : Blo 1572484 1573783 := bstep (se 1 (by rfl) ⟨1180337, by rfl⟩ : syracuseStep 1573783 = 2360675) B2360675
theorem B1573803 : Blo 1572484 1573803 := bstep (se 1 (by rfl) ⟨1180352, by rfl⟩ : syracuseStep 1573803 = 2360705) B2360705
theorem B1573815 : Blo 1572484 1573815 := bstep (se 1 (by rfl) ⟨1180361, by rfl⟩ : syracuseStep 1573815 = 2360723) B2360723
theorem B5309387 : Blo 1572484 5309387 := bstep (se 1 (by rfl) ⟨3982040, by rfl⟩ : syracuseStep 5309387 = 7964081) B7964081
theorem B3539915 : Blo 1572484 3539915 := bstep (se 1 (by rfl) ⟨2654936, by rfl⟩ : syracuseStep 3539915 = 5309873) B5309873
theorem B2360267 : Blo 1572484 2360267 := bstep (se 1 (by rfl) ⟨1770200, by rfl⟩ : syracuseStep 2360267 = 3540401) B3540401
theorem B1573835 : Blo 1572484 1573835 := bstep (se 1 (by rfl) ⟨1180376, by rfl⟩ : syracuseStep 1573835 = 2360753) B2360753
theorem B2360279 : Blo 1572484 2360279 := bstep (se 1 (by rfl) ⟨1770209, by rfl⟩ : syracuseStep 2360279 = 3540419) B3540419
theorem B1573847 : Blo 1572484 1573847 := bstep (se 1 (by rfl) ⟨1180385, by rfl⟩ : syracuseStep 1573847 = 2360771) B2360771
theorem B2655193 : Blo 1572484 2655193 := bstep (se 2 (by rfl) ⟨995697, by rfl⟩ : syracuseStep 2655193 = 1991395) B1991395
theorem B1770475 : Blo 1572484 1770475 := bstep (se 1 (by rfl) ⟨1327856, by rfl⟩ : syracuseStep 1770475 = 2655713) B2655713
theorem B1573867 : Blo 1572484 1573867 := bstep (se 1 (by rfl) ⟨1180400, by rfl⟩ : syracuseStep 1573867 = 2360801) B2360801
theorem B1573879 : Blo 1572484 1573879 := bstep (se 1 (by rfl) ⟨1180409, by rfl⟩ : syracuseStep 1573879 = 2360819) B2360819
theorem B3539969 : Blo 1572484 3539969 := bstep (se 2 (by rfl) ⟨1327488, by rfl⟩ : syracuseStep 3539969 = 2654977) B2654977
theorem B1573899 : Blo 1572484 1573899 := bstep (se 1 (by rfl) ⟨1180424, by rfl⟩ : syracuseStep 1573899 = 2360849) B2360849
theorem B11953169 : Blo 1572484 11953169 := bstep (se 2 (by rfl) ⟨4482438, by rfl⟩ : syracuseStep 11953169 = 8964877) B8964877
theorem B1573911 : Blo 1572484 1573911 := bstep (se 1 (by rfl) ⟨1180433, by rfl⟩ : syracuseStep 1573911 = 2360867) B2360867
theorem B2360345 : Blo 1572484 2360345 := bstep (se 2 (by rfl) ⟨885129, by rfl⟩ : syracuseStep 2360345 = 1770259) B1770259
theorem B1573931 : Blo 1572484 1573931 := bstep (se 1 (by rfl) ⟨1180448, by rfl⟩ : syracuseStep 1573931 = 2360897) B2360897
theorem B1573943 : Blo 1572484 1573943 := bstep (se 1 (by rfl) ⟨1180457, by rfl⟩ : syracuseStep 1573943 = 2360915) B2360915
theorem B1573963 : Blo 1572484 1573963 := bstep (se 1 (by rfl) ⟨1180472, by rfl⟩ : syracuseStep 1573963 = 2360945) B2360945
theorem B1770583 : Blo 1572484 1770583 := bstep (se 1 (by rfl) ⟨1327937, by rfl⟩ : syracuseStep 1770583 = 2655875) B2655875
theorem B1573975 : Blo 1572484 1573975 := bstep (se 1 (by rfl) ⟨1180481, by rfl⟩ : syracuseStep 1573975 = 2360963) B2360963
theorem B1574007 : Blo 1572484 1574007 := bstep (se 1 (by rfl) ⟨1180505, by rfl⟩ : syracuseStep 1574007 = 2361011) B2361011
theorem B2360459 : Blo 1572484 2360459 := bstep (se 1 (by rfl) ⟨1770344, by rfl⟩ : syracuseStep 2360459 = 3540689) B3540689
theorem B1574027 : Blo 1572484 1574027 := bstep (se 1 (by rfl) ⟨1180520, by rfl⟩ : syracuseStep 1574027 = 2361041) B2361041
theorem B2360471 : Blo 1572484 2360471 := bstep (se 1 (by rfl) ⟨1770353, by rfl⟩ : syracuseStep 2360471 = 3540707) B3540707
theorem B1680535 : Blo 1572484 1680535 := bstep (se 1 (by rfl) ⟨1260401, by rfl⟩ : syracuseStep 1680535 = 2520803) B2520803
theorem B1574039 : Blo 1572484 1574039 := bstep (se 1 (by rfl) ⟨1180529, by rfl⟩ : syracuseStep 1574039 = 2361059) B2361059
theorem B1574059 : Blo 1572484 1574059 := bstep (se 1 (by rfl) ⟨1180544, by rfl⟩ : syracuseStep 1574059 = 2361089) B2361089
theorem B1574071 : Blo 1572484 1574071 := bstep (se 1 (by rfl) ⟨1180553, by rfl⟩ : syracuseStep 1574071 = 2361107) B2361107
theorem B1574091 : Blo 1572484 1574091 := bstep (se 1 (by rfl) ⟨1180568, by rfl⟩ : syracuseStep 1574091 = 2361137) B2361137
theorem B5309657 : Blo 1572484 5309657 := bstep (se 2 (by rfl) ⟨1991121, by rfl⟩ : syracuseStep 5309657 = 3982243) B3982243
theorem B3540185 : Blo 1572484 3540185 := bstep (se 2 (by rfl) ⟨1327569, by rfl⟩ : syracuseStep 3540185 = 2655139) B2655139
theorem B2360537 : Blo 1572484 2360537 := bstep (se 2 (by rfl) ⟨885201, by rfl⟩ : syracuseStep 2360537 = 1770403) B1770403
theorem B1574103 : Blo 1572484 1574103 := bstep (se 1 (by rfl) ⟨1180577, by rfl⟩ : syracuseStep 1574103 = 2361155) B2361155
theorem B1574123 : Blo 1572484 1574123 := bstep (se 1 (by rfl) ⟨1180592, by rfl⟩ : syracuseStep 1574123 = 2361185) B2361185
theorem B1574135 : Blo 1572484 1574135 := bstep (se 1 (by rfl) ⟨1180601, by rfl⟩ : syracuseStep 1574135 = 2361203) B2361203
theorem B1991947 : Blo 1572484 1991947 := bstep (se 1 (by rfl) ⟨1493960, by rfl⟩ : syracuseStep 1991947 = 2987921) B2987921
theorem B1770763 : Blo 1572484 1770763 := bstep (se 1 (by rfl) ⟨1328072, by rfl⟩ : syracuseStep 1770763 = 2656145) B2656145
theorem B1574155 : Blo 1572484 1574155 := bstep (se 1 (by rfl) ⟨1180616, by rfl⟩ : syracuseStep 1574155 = 2361233) B2361233
theorem B1574167 : Blo 1572484 1574167 := bstep (se 1 (by rfl) ⟨1180625, by rfl⟩ : syracuseStep 1574167 = 2361251) B2361251
theorem B1574187 : Blo 1572484 1574187 := bstep (se 1 (by rfl) ⟨1180640, by rfl⟩ : syracuseStep 1574187 = 2361281) B2361281
theorem B3540275 : Blo 1572484 3540275 := bstep (se 1 (by rfl) ⟨2655206, by rfl⟩ : syracuseStep 3540275 = 5310413) B5310413
theorem B1574199 : Blo 1572484 1574199 := bstep (se 1 (by rfl) ⟨1180649, by rfl⟩ : syracuseStep 1574199 = 2361299) B2361299
theorem B2360651 : Blo 1572484 2360651 := bstep (se 1 (by rfl) ⟨1770488, by rfl⟩ : syracuseStep 2360651 = 3540977) B3540977
theorem B1574219 : Blo 1572484 1574219 := bstep (se 1 (by rfl) ⟨1180664, by rfl⟩ : syracuseStep 1574219 = 2361329) B2361329
theorem B3540311 : Blo 1572484 3540311 := bstep (se 1 (by rfl) ⟨2655233, by rfl⟩ : syracuseStep 3540311 = 5310467) B5310467
theorem B2360663 : Blo 1572484 2360663 := bstep (se 1 (by rfl) ⟨1770497, by rfl⟩ : syracuseStep 2360663 = 3540995) B3540995
theorem B2393431 : Blo 1572484 2393431 := bstep (se 1 (by rfl) ⟨1795073, by rfl⟩ : syracuseStep 2393431 = 3590147) B3590147
theorem B1574231 : Blo 1572484 1574231 := bstep (se 1 (by rfl) ⟨1180673, by rfl⟩ : syracuseStep 1574231 = 2361347) B2361347
theorem B1574251 : Blo 1572484 1574251 := bstep (se 1 (by rfl) ⟨1180688, by rfl⟩ : syracuseStep 1574251 = 2361377) B2361377
theorem B1770871 : Blo 1572484 1770871 := bstep (se 1 (by rfl) ⟨1328153, by rfl⟩ : syracuseStep 1770871 = 2656307) B2656307
theorem B1574263 : Blo 1572484 1574263 := bstep (se 1 (by rfl) ⟨1180697, by rfl⟩ : syracuseStep 1574263 = 2361395) B2361395
theorem B1574283 : Blo 1572484 1574283 := bstep (se 1 (by rfl) ⟨1180712, by rfl⟩ : syracuseStep 1574283 = 2361425) B2361425
theorem B1574295 : Blo 1572484 1574295 := bstep (se 1 (by rfl) ⟨1180721, by rfl⟩ : syracuseStep 1574295 = 2361443) B2361443
theorem B2360729 : Blo 1572484 2360729 := bstep (se 2 (by rfl) ⟨885273, by rfl⟩ : syracuseStep 2360729 = 1770547) B1770547
theorem B1574315 : Blo 1572484 1574315 := bstep (se 1 (by rfl) ⟨1180736, by rfl⟩ : syracuseStep 1574315 = 2361473) B2361473
theorem B17917361 : Blo 1572484 17917361 := bstep (se 2 (by rfl) ⟨6719010, by rfl⟩ : syracuseStep 17917361 = 13438021) B13438021
theorem B11945393 : Blo 1572484 11945393 := bstep (se 2 (by rfl) ⟨4479522, by rfl⟩ : syracuseStep 11945393 = 8959045) B8959045
theorem B1574327 : Blo 1572484 1574327 := bstep (se 1 (by rfl) ⟨1180745, by rfl⟩ : syracuseStep 1574327 = 2361491) B2361491
theorem B1574347 : Blo 1572484 1574347 := bstep (se 1 (by rfl) ⟨1180760, by rfl⟩ : syracuseStep 1574347 = 2361521) B2361521
theorem B1574359 : Blo 1572484 1574359 := bstep (se 1 (by rfl) ⟨1180769, by rfl⟩ : syracuseStep 1574359 = 2361539) B2361539
theorem B1574379 : Blo 1572484 1574379 := bstep (se 1 (by rfl) ⟨1180784, by rfl⟩ : syracuseStep 1574379 = 2361569) B2361569
theorem B1574391 : Blo 1572484 1574391 := bstep (se 1 (by rfl) ⟨1180793, by rfl⟩ : syracuseStep 1574391 = 2361587) B2361587
theorem B3540491 : Blo 1572484 3540491 := bstep (se 1 (by rfl) ⟨2655368, by rfl⟩ : syracuseStep 3540491 = 5310737) B5310737
theorem B2360843 : Blo 1572484 2360843 := bstep (se 1 (by rfl) ⟨1770632, by rfl⟩ : syracuseStep 2360843 = 3541265) B3541265
theorem B1574411 : Blo 1572484 1574411 := bstep (se 1 (by rfl) ⟨1180808, by rfl⟩ : syracuseStep 1574411 = 2361617) B2361617
theorem B3982871 : Blo 1572484 3982871 := bstep (se 1 (by rfl) ⟨2987153, by rfl⟩ : syracuseStep 3982871 = 5974307) B5974307
theorem B2655767 : Blo 1572484 2655767 := bstep (se 1 (by rfl) ⟨1991825, by rfl⟩ : syracuseStep 2655767 = 3983651) B3983651
theorem B2360855 : Blo 1572484 2360855 := bstep (se 1 (by rfl) ⟨1770641, by rfl⟩ : syracuseStep 2360855 = 3541283) B3541283
theorem B1992215 : Blo 1572484 1992215 := bstep (se 1 (by rfl) ⟨1494161, by rfl⟩ : syracuseStep 1992215 = 2988323) B2988323
theorem B1574423 : Blo 1572484 1574423 := bstep (se 1 (by rfl) ⟨1180817, by rfl⟩ : syracuseStep 1574423 = 2361635) B2361635
theorem B1771051 : Blo 1572484 1771051 := bstep (se 1 (by rfl) ⟨1328288, by rfl⟩ : syracuseStep 1771051 = 2656577) B2656577
theorem B1574443 : Blo 1572484 1574443 := bstep (se 1 (by rfl) ⟨1180832, by rfl⟩ : syracuseStep 1574443 = 2361665) B2361665
theorem B4482611 : Blo 1572484 4482611 := bstep (se 1 (by rfl) ⟨3361958, by rfl⟩ : syracuseStep 4482611 = 6723917) B6723917
theorem B1574455 : Blo 1572484 1574455 := bstep (se 1 (by rfl) ⟨1180841, by rfl⟩ : syracuseStep 1574455 = 2361683) B2361683
theorem B3540545 : Blo 1572484 3540545 := bstep (se 2 (by rfl) ⟨1327704, by rfl⟩ : syracuseStep 3540545 = 2655409) B2655409
theorem B2393675 : Blo 1572484 2393675 := bstep (se 1 (by rfl) ⟨1795256, by rfl⟩ : syracuseStep 2393675 = 3590513) B3590513
theorem B1574475 : Blo 1572484 1574475 := bstep (se 1 (by rfl) ⟨1180856, by rfl⟩ : syracuseStep 1574475 = 2361713) B2361713
theorem B2360921 : Blo 1572484 2360921 := bstep (se 2 (by rfl) ⟨885345, by rfl⟩ : syracuseStep 2360921 = 1770691) B1770691
theorem B2655895 : Blo 1572484 2655895 := bstep (se 1 (by rfl) ⟨1991921, by rfl⟩ : syracuseStep 2655895 = 3983843) B3983843
theorem B1771159 : Blo 1572484 1771159 := bstep (se 1 (by rfl) ⟨1328369, by rfl⟩ : syracuseStep 1771159 = 2656739) B2656739
theorem B2361035 : Blo 1572484 2361035 := bstep (se 1 (by rfl) ⟨1770776, by rfl⟩ : syracuseStep 2361035 = 3541553) B3541553
theorem B2361047 : Blo 1572484 2361047 := bstep (se 1 (by rfl) ⟨1770785, by rfl⟩ : syracuseStep 2361047 = 3541571) B3541571
theorem B3360523 : Blo 1572484 3360523 := bstep (se 1 (by rfl) ⟨2520392, by rfl⟩ : syracuseStep 3360523 = 5040785) B5040785
theorem B3540761 : Blo 1572484 3540761 := bstep (se 2 (by rfl) ⟨1327785, by rfl⟩ : syracuseStep 3540761 = 2655571) B2655571
theorem B2361113 : Blo 1572484 2361113 := bstep (se 2 (by rfl) ⟨885417, by rfl⟩ : syracuseStep 2361113 = 1770835) B1770835
theorem B54470501 : Blo 1572484 54470501 := bstep (se 4 (by rfl) ⟨5106609, by rfl⟩ : syracuseStep 54470501 = 10213219) B10213219
theorem B3540851 : Blo 1572484 3540851 := bstep (se 1 (by rfl) ⟨2655638, by rfl⟩ : syracuseStep 3540851 = 5311277) B5311277
theorem B2361227 : Blo 1572484 2361227 := bstep (se 1 (by rfl) ⟨1770920, by rfl⟩ : syracuseStep 2361227 = 3541841) B3541841
theorem B11945879 : Blo 1572484 11945879 := bstep (se 1 (by rfl) ⟨8959409, by rfl⟩ : syracuseStep 11945879 = 17918819) B17918819
theorem B7964567 : Blo 1572484 7964567 := bstep (se 1 (by rfl) ⟨5973425, by rfl⟩ : syracuseStep 7964567 = 11946851) B11946851
theorem B5310359 : Blo 1572484 5310359 := bstep (se 1 (by rfl) ⟨3982769, by rfl⟩ : syracuseStep 5310359 = 7965539) B7965539
theorem B3540887 : Blo 1572484 3540887 := bstep (se 1 (by rfl) ⟨2655665, by rfl⟩ : syracuseStep 3540887 = 5311331) B5311331
theorem B2361239 : Blo 1572484 2361239 := bstep (se 1 (by rfl) ⟨1770929, by rfl⟩ : syracuseStep 2361239 = 3541859) B3541859
theorem B3778483 : Blo 1572484 3778483 := bstep (se 1 (by rfl) ⟨2833862, by rfl⟩ : syracuseStep 3778483 = 5667725) B5667725
theorem B2361305 : Blo 1572484 2361305 := bstep (se 2 (by rfl) ⟨885489, by rfl⟩ : syracuseStep 2361305 = 1770979) B1770979
theorem B5974019 : Blo 1572484 5974019 := bstep (se 1 (by rfl) ⟨4480514, by rfl⟩ : syracuseStep 5974019 = 8961029) B8961029
theorem B5974033 : Blo 1572484 5974033 := bstep (se 2 (by rfl) ⟨2240262, by rfl⟩ : syracuseStep 5974033 = 4480525) B4480525
theorem B3541067 : Blo 1572484 3541067 := bstep (se 1 (by rfl) ⟨2655800, by rfl⟩ : syracuseStep 3541067 = 5311601) B5311601
theorem B2361419 : Blo 1572484 2361419 := bstep (se 1 (by rfl) ⟨1771064, by rfl⟩ : syracuseStep 2361419 = 3542129) B3542129
theorem B2361431 : Blo 1572484 2361431 := bstep (se 1 (by rfl) ⟨1771073, by rfl⟩ : syracuseStep 2361431 = 3542147) B3542147
theorem B3541121 : Blo 1572484 3541121 := bstep (se 2 (by rfl) ⟨1327920, by rfl⟩ : syracuseStep 3541121 = 2655841) B2655841
theorem B2361497 : Blo 1572484 2361497 := bstep (se 2 (by rfl) ⟨885561, by rfl⟩ : syracuseStep 2361497 = 1771123) B1771123
theorem B3983539 : Blo 1572484 3983539 := bstep (se 1 (by rfl) ⟨2987654, by rfl⟩ : syracuseStep 3983539 = 5975309) B5975309
theorem B2656523 : Blo 1572484 2656523 := bstep (se 1 (by rfl) ⟨1992392, by rfl⟩ : syracuseStep 2656523 = 3984785) B3984785
theorem B2361611 : Blo 1572484 2361611 := bstep (se 1 (by rfl) ⟨1771208, by rfl⟩ : syracuseStep 2361611 = 3542417) B3542417
theorem B2361623 : Blo 1572484 2361623 := bstep (se 1 (by rfl) ⟨1771217, by rfl⟩ : syracuseStep 2361623 = 3542435) B3542435
theorem B5974337 : Blo 1572484 5974337 := bstep (se 2 (by rfl) ⟨2240376, by rfl⟩ : syracuseStep 5974337 = 4480753) B4480753
theorem B3983681 : Blo 1572484 3983681 := bstep (se 2 (by rfl) ⟨1493880, by rfl⟩ : syracuseStep 3983681 = 2987761) B2987761
theorem B3541337 : Blo 1572484 3541337 := bstep (se 2 (by rfl) ⟨1328001, by rfl⟩ : syracuseStep 3541337 = 2656003) B2656003
theorem B2361689 : Blo 1572484 2361689 := bstep (se 2 (by rfl) ⟨885633, by rfl⟩ : syracuseStep 2361689 = 1771267) B1771267
theorem B2656651 : Blo 1572484 2656651 := bstep (se 1 (by rfl) ⟨1992488, by rfl⟩ : syracuseStep 2656651 = 3984977) B3984977
theorem B6220205 : Blo 1572484 6220205 := bstep (se 3 (by rfl) ⟨1166288, by rfl⟩ : syracuseStep 6220205 = 2332577) B2332577
theorem B5310899 : Blo 1572484 5310899 := bstep (se 1 (by rfl) ⟨3983174, by rfl⟩ : syracuseStep 5310899 = 7966349) B7966349
theorem B3541427 : Blo 1572484 3541427 := bstep (se 1 (by rfl) ⟨2656070, by rfl⟩ : syracuseStep 3541427 = 5312141) B5312141
theorem B3541463 : Blo 1572484 3541463 := bstep (se 1 (by rfl) ⟨2656097, by rfl⟩ : syracuseStep 3541463 = 5312195) B5312195
theorem B5745113 : Blo 1572484 5745113 := bstep (se 2 (by rfl) ⟨2154417, by rfl⟩ : syracuseStep 5745113 = 4308835) B4308835
theorem B2656793 : Blo 1572484 2656793 := bstep (se 2 (by rfl) ⟨996297, by rfl⟩ : syracuseStep 2656793 = 1992595) B1992595
theorem B3541643 : Blo 1572484 3541643 := bstep (se 1 (by rfl) ⟨2656232, by rfl⟩ : syracuseStep 3541643 = 5312465) B5312465
theorem B2656921 : Blo 1572484 2656921 := bstep (se 2 (by rfl) ⟨996345, by rfl⟩ : syracuseStep 2656921 = 1992691) B1992691
theorem B5311169 : Blo 1572484 5311169 := bstep (se 2 (by rfl) ⟨1991688, by rfl⟩ : syracuseStep 5311169 = 3983377) B3983377
theorem B3541697 : Blo 1572484 3541697 := bstep (se 2 (by rfl) ⟨1328136, by rfl⟩ : syracuseStep 3541697 = 2656273) B2656273
theorem B2239255 : Blo 1572484 2239255 := bstep (se 1 (by rfl) ⟨1679441, by rfl⟩ : syracuseStep 2239255 = 3358883) B3358883
theorem B40323905 : Blo 1572484 40323905 := bstep (se 2 (by rfl) ⟨15121464, by rfl⟩ : syracuseStep 40323905 = 30242929) B30242929
theorem B40897345 : Blo 1572484 40897345 := bstep (se 2 (by rfl) ⟨15336504, by rfl⟩ : syracuseStep 40897345 = 30673009) B30673009
theorem B3541913 : Blo 1572484 3541913 := bstep (se 2 (by rfl) ⟨1328217, by rfl⟩ : syracuseStep 3541913 = 2656435) B2656435
theorem B3361753 : Blo 1572484 3361753 := bstep (se 2 (by rfl) ⟨1260657, by rfl⟩ : syracuseStep 3361753 = 2521315) B2521315
theorem B5975005 : Blo 1572484 5975005 := bstep (se 3 (by rfl) ⟨1120313, by rfl⟩ : syracuseStep 5975005 = 2240627) B2240627
theorem B3451891 : Blo 1572484 3451891 := bstep (se 1 (by rfl) ⟨2588918, by rfl⟩ : syracuseStep 3451891 = 5177837) B5177837
theorem B3542003 : Blo 1572484 3542003 := bstep (se 1 (by rfl) ⟨2656502, by rfl⟩ : syracuseStep 3542003 = 5313005) B5313005
theorem B6720515 : Blo 1572484 6720515 := bstep (se 1 (by rfl) ⟨5040386, by rfl⟩ : syracuseStep 6720515 = 10080773) B10080773
theorem B3542039 : Blo 1572484 3542039 := bstep (se 1 (by rfl) ⟨2656529, by rfl⟩ : syracuseStep 3542039 = 5313059) B5313059
theorem B3542219 : Blo 1572484 3542219 := bstep (se 1 (by rfl) ⟨2656664, by rfl⟩ : syracuseStep 3542219 = 5313329) B5313329
theorem B5311709 : Blo 1572484 5311709 := bstep (se 3 (by rfl) ⟨995945, by rfl⟩ : syracuseStep 5311709 = 1991891) B1991891
theorem B3542273 : Blo 1572484 3542273 := bstep (se 2 (by rfl) ⟨1328352, by rfl⟩ : syracuseStep 3542273 = 2656705) B2656705
theorem B72682757 : Blo 1572484 72682757 := bstep (se 4 (by rfl) ⟨6814008, by rfl⟩ : syracuseStep 72682757 = 13628017) B13628017
theorem B6720857 : Blo 1572484 6720857 := bstep (se 2 (by rfl) ⟨2520321, by rfl⟩ : syracuseStep 6720857 = 5040643) B5040643
theorem B5672281 : Blo 1572484 5672281 := bstep (se 2 (by rfl) ⟨2127105, by rfl⟩ : syracuseStep 5672281 = 4254211) B4254211
theorem B4787545 : Blo 1572484 4787545 := bstep (se 2 (by rfl) ⟨1795329, by rfl⟩ : syracuseStep 4787545 = 3590659) B3590659
theorem B2985331 : Blo 1572484 2985331 := bstep (se 1 (by rfl) ⟨2238998, by rfl⟩ : syracuseStep 2985331 = 4477997) B4477997
theorem B21532121 : Blo 1572484 21532121 := bstep (se 2 (by rfl) ⟨8074545, by rfl⟩ : syracuseStep 21532121 = 16149091) B16149091
theorem B3542489 : Blo 1572484 3542489 := bstep (se 2 (by rfl) ⟨1328433, by rfl⟩ : syracuseStep 3542489 = 2656867) B2656867
theorem B57421325 : Blo 1572484 57421325 := bstep (se 3 (by rfl) ⟨10766498, by rfl⟩ : syracuseStep 57421325 = 21532997) B21532997
theorem B3984947 : Blo 1572484 3984947 := bstep (se 1 (by rfl) ⟨2988710, by rfl⟩ : syracuseStep 3984947 = 5977421) B5977421
theorem B3542579 : Blo 1572484 3542579 := bstep (se 1 (by rfl) ⟨2656934, by rfl⟩ : syracuseStep 3542579 = 5313869) B5313869
theorem B2240075 : Blo 1572484 2240075 := bstep (se 1 (by rfl) ⟨1680056, by rfl⟩ : syracuseStep 2240075 = 3360113) B3360113
theorem B3190529 : Blo 1572484 3190529 := bstep (se 2 (by rfl) ⟨1196448, by rfl⟩ : syracuseStep 3190529 = 2392897) B2392897
theorem B4255553 : Blo 1572484 4255553 := bstep (se 2 (by rfl) ⟨1595832, by rfl⟩ : syracuseStep 4255553 = 3191665) B3191665
theorem B2985817 : Blo 1572484 2985817 := bstep (se 2 (by rfl) ⟨1119681, by rfl⟩ : syracuseStep 2985817 = 2239363) B2239363
theorem B12930947 : Blo 1572484 12930947 := bstep (se 1 (by rfl) ⟨9698210, by rfl⟩ : syracuseStep 12930947 = 19396421) B19396421
theorem B13447043 : Blo 1572484 13447043 := bstep (se 1 (by rfl) ⟨10085282, by rfl⟩ : syracuseStep 13447043 = 20170565) B20170565
theorem B6557761 : Blo 1572484 6557761 := bstep (se 2 (by rfl) ⟨2459160, by rfl⟩ : syracuseStep 6557761 = 4918321) B4918321
theorem B15126659 : Blo 1572484 15126659 := bstep (se 1 (by rfl) ⟨11344994, by rfl⟩ : syracuseStep 15126659 = 22689989) B22689989
theorem B25874563 : Blo 1572484 25874563 := bstep (se 1 (by rfl) ⟨19405922, by rfl⟩ : syracuseStep 25874563 = 38811845) B38811845
theorem B5976281 : Blo 1572484 5976281 := bstep (se 2 (by rfl) ⟨2241105, by rfl⟩ : syracuseStep 5976281 = 4482211) B4482211
theorem B5673233 : Blo 1572484 5673233 := bstep (se 2 (by rfl) ⟨2127462, by rfl⟩ : syracuseStep 5673233 = 4254925) B4254925
theorem B6467885 : Blo 1572484 6467885 := bstep (se 3 (by rfl) ⟨1212728, by rfl⟩ : syracuseStep 6467885 = 2425457) B2425457
theorem B7180589 : Blo 1572484 7180589 := bstep (se 3 (by rfl) ⟨1346360, by rfl⟩ : syracuseStep 7180589 = 2692721) B2692721
theorem B5312843 : Blo 1572484 5312843 := bstep (se 1 (by rfl) ⟨3984632, by rfl⟩ : syracuseStep 5312843 = 7969265) B7969265
theorem B2986379 : Blo 1572484 2986379 := bstep (se 1 (by rfl) ⟨2239784, by rfl⟩ : syracuseStep 2986379 = 4479569) B4479569
theorem B2241049 : Blo 1572484 2241049 := bstep (se 2 (by rfl) ⟨840393, by rfl⟩ : syracuseStep 2241049 = 1680787) B1680787
theorem B2986561 : Blo 1572484 2986561 := bstep (se 2 (by rfl) ⟨1119960, by rfl⟩ : syracuseStep 2986561 = 2239921) B2239921
theorem B2126425 : Blo 1572484 2126425 := bstep (se 2 (by rfl) ⟨797409, by rfl⟩ : syracuseStep 2126425 = 1594819) B1594819
theorem B5313113 : Blo 1572484 5313113 := bstep (se 2 (by rfl) ⟨1992417, by rfl⟩ : syracuseStep 5313113 = 3984835) B3984835
theorem B12112685 : Blo 1572484 12112685 := bstep (se 3 (by rfl) ⟨2271128, by rfl⟩ : syracuseStep 12112685 = 4542257) B4542257
theorem B17929025 : Blo 1572484 17929025 := bstep (se 2 (by rfl) ⟨6723384, by rfl⟩ : syracuseStep 17929025 = 13446769) B13446769
theorem B34476977 : Blo 1572484 34476977 := bstep (se 2 (by rfl) ⟨12928866, by rfl⟩ : syracuseStep 34476977 = 25857733) B25857733
theorem B13440005 : Blo 1572484 13440005 := bstep (se 4 (by rfl) ⟨1260000, by rfl⟩ : syracuseStep 13440005 = 2520001) B2520001
theorem B8508509 : Blo 1572484 8508509 := bstep (se 3 (by rfl) ⟨1595345, by rfl⟩ : syracuseStep 8508509 = 3190691) B3190691
theorem B40337027 : Blo 1572484 40337027 := bstep (se 1 (by rfl) ⟨30252770, by rfl⟩ : syracuseStep 40337027 = 60505541) B60505541
theorem B5674157 : Blo 1572484 5674157 := bstep (se 3 (by rfl) ⟨1063904, by rfl⟩ : syracuseStep 5674157 = 2127809) B2127809
theorem B15119621 : Blo 1572484 15119621 := bstep (se 4 (by rfl) ⟨1417464, by rfl⟩ : syracuseStep 15119621 = 2834929) B2834929
theorem B2987275 : Blo 1572484 2987275 := bstep (se 1 (by rfl) ⟨2240456, by rfl⟩ : syracuseStep 2987275 = 4480913) B4480913
theorem B5313815 : Blo 1572484 5313815 := bstep (se 1 (by rfl) ⟨3985361, by rfl⟩ : syracuseStep 5313815 = 7970723) B7970723
theorem B11343149 : Blo 1572484 11343149 := bstep (se 3 (by rfl) ⟨2126840, by rfl⟩ : syracuseStep 11343149 = 4253681) B4253681
theorem B2987351 : Blo 1572484 2987351 := bstep (se 1 (by rfl) ⟨2240513, by rfl⟩ : syracuseStep 2987351 = 4481027) B4481027
theorem B7968131 : Blo 1572484 7968131 := bstep (se 1 (by rfl) ⟨5976098, by rfl⟩ : syracuseStep 7968131 = 11952197) B11952197
theorem B4036043 : Blo 1572484 4036043 := bstep (se 1 (by rfl) ⟨3027032, by rfl⟩ : syracuseStep 4036043 = 6054065) B6054065
theorem B5109209 : Blo 1572484 5109209 := bstep (se 2 (by rfl) ⟨1915953, by rfl⟩ : syracuseStep 5109209 = 3831907) B3831907
theorem B4478429 : Blo 1572484 4478429 := bstep (se 3 (by rfl) ⟨839705, by rfl⟩ : syracuseStep 4478429 = 1679411) B1679411
theorem B1573995 : Blo 1572484 1573995 := bstep (se 1 (by rfl) ⟨1180496, by rfl⟩ : syracuseStep 1573995 = 2360993) B2360993
theorem B1726039 : Blo 1572484 1726039 := bstep (se 1 (by rfl) ⟨1294529, by rfl⟩ : syracuseStep 1726039 = 2589059) B2589059
theorem B26900099 : Blo 1572484 26900099 := bstep (se 1 (by rfl) ⟨20175074, by rfl⟩ : syracuseStep 26900099 = 40350149) B40350149
theorem B9565847 : Blo 1572484 9565847 := bstep (se 1 (by rfl) ⟨7174385, by rfl⟩ : syracuseStep 9565847 = 14348771) B14348771
theorem B13620887 : Blo 1572484 13620887 := bstep (se 1 (by rfl) ⟨10215665, by rfl⟩ : syracuseStep 13620887 = 20431331) B20431331
theorem B3831499 : Blo 1572484 3831499 := bstep (se 1 (by rfl) ⟨2873624, by rfl⟩ : syracuseStep 3831499 = 5747249) B5747249
theorem B48420557 : Blo 1572484 48420557 := bstep (se 3 (by rfl) ⟨9078854, by rfl⟩ : syracuseStep 48420557 = 18157709) B18157709
theorem B5977907 : Blo 1572484 5977907 := bstep (se 1 (by rfl) ⟨4483430, by rfl⟩ : syracuseStep 5977907 = 8966861) B8966861
theorem B5977921 : Blo 1572484 5977921 := bstep (se 2 (by rfl) ⟨2241720, by rfl⟩ : syracuseStep 5977921 = 4483441) B4483441
theorem B7272337 : Blo 1572484 7272337 := bstep (se 2 (by rfl) ⟨2727126, by rfl⟩ : syracuseStep 7272337 = 5454253) B5454253
theorem B9574361 : Blo 1572484 9574361 := bstep (se 2 (by rfl) ⟨3590385, by rfl⟩ : syracuseStep 9574361 = 7180771) B7180771
theorem B2988019 : Blo 1572484 2988019 := bstep (se 1 (by rfl) ⟨2241014, by rfl⟩ : syracuseStep 2988019 = 4482029) B4482029
theorem B1595467 : Blo 1572484 1595467 := bstep (se 1 (by rfl) ⟨1196600, by rfl⟩ : syracuseStep 1595467 = 2393201) B2393201
theorem B2766923 : Blo 1572484 2766923 := bstep (se 1 (by rfl) ⟨2075192, by rfl⟩ : syracuseStep 2766923 = 4150385) B4150385
theorem B7272641 : Blo 1572484 7272641 := bstep (se 2 (by rfl) ⟨2727240, by rfl⟩ : syracuseStep 7272641 = 5454481) B5454481
theorem B2988247 : Blo 1572484 2988247 := bstep (se 1 (by rfl) ⟨2241185, by rfl⟩ : syracuseStep 2988247 = 4482371) B4482371
theorem B19151149 : Blo 1572484 19151149 := bstep (se 3 (by rfl) ⟨3590840, by rfl⟩ : syracuseStep 19151149 = 7181681) B7181681
theorem B8960321 : Blo 1572484 8960321 := bstep (se 2 (by rfl) ⟨3360120, by rfl⟩ : syracuseStep 8960321 = 6720241) B6720241
theorem B2988353 : Blo 1572484 2988353 := bstep (se 2 (by rfl) ⟨1120632, by rfl⟩ : syracuseStep 2988353 = 2241265) B2241265
theorem B2988505 : Blo 1572484 2988505 := bstep (se 2 (by rfl) ⟨1120689, by rfl⟩ : syracuseStep 2988505 = 2241379) B2241379
theorem B17013341 : Blo 1572484 17013341 := bstep (se 3 (by rfl) ⟨3190001, by rfl⟩ : syracuseStep 17013341 = 6380003) B6380003
theorem B6724241 : Blo 1572484 6724241 := bstep (se 2 (by rfl) ⟨2521590, by rfl⟩ : syracuseStep 6724241 = 5043181) B5043181
theorem B6380311 : Blo 1572484 6380311 := bstep (se 1 (by rfl) ⟨4785233, by rfl⟩ : syracuseStep 6380311 = 9570467) B9570467
theorem B5749555 : Blo 1572484 5749555 := bstep (se 1 (by rfl) ⟨4312166, by rfl⟩ : syracuseStep 5749555 = 8624333) B8624333
theorem B5380939 : Blo 1572484 5380939 := bstep (se 1 (by rfl) ⟨4035704, by rfl⟩ : syracuseStep 5380939 = 8071409) B8071409
theorem B5970905 : Blo 1572484 5970905 := bstep (se 2 (by rfl) ⟨2239089, by rfl⟩ : syracuseStep 5970905 = 4478179) B4478179
theorem B5307443 : Blo 1572484 5307443 := bstep (se 1 (by rfl) ⟨3980582, by rfl⟩ : syracuseStep 5307443 = 7961165) B7961165
theorem B13433921 : Blo 1572484 13433921 := bstep (se 2 (by rfl) ⟨5037720, by rfl⟩ : syracuseStep 13433921 = 10075441) B10075441
theorem B5971117 : Blo 1572484 5971117 := bstep (se 3 (by rfl) ⟨1119584, by rfl⟩ : syracuseStep 5971117 = 2239169) B2239169
theorem B3538187 : Blo 1572484 3538187 := bstep (se 1 (by rfl) ⟨2653640, by rfl⟩ : syracuseStep 3538187 = 5307281) B5307281
theorem B3538241 : Blo 1572484 3538241 := bstep (se 2 (by rfl) ⟨1326840, by rfl⟩ : syracuseStep 3538241 = 2653681) B2653681
theorem B5307713 : Blo 1572484 5307713 := bstep (se 2 (by rfl) ⟨1990392, by rfl⟩ : syracuseStep 5307713 = 3980785) B3980785
theorem B6724957 : Blo 1572484 6724957 := bstep (se 3 (by rfl) ⟨1260929, by rfl⟩ : syracuseStep 6724957 = 2521859) B2521859
theorem B2358731 : Blo 1572484 2358731 := bstep (se 1 (by rfl) ⟨1769048, by rfl⟩ : syracuseStep 2358731 = 3538097) B3538097
theorem B2358743 : Blo 1572484 2358743 := bstep (se 1 (by rfl) ⟨1769057, by rfl⟩ : syracuseStep 2358743 = 3538115) B3538115
theorem B5971421 : Blo 1572484 5971421 := bstep (se 3 (by rfl) ⟨1119641, by rfl⟩ : syracuseStep 5971421 = 2239283) B2239283
theorem B6716945 : Blo 1572484 6716945 := bstep (se 2 (by rfl) ⟨2518854, by rfl⟩ : syracuseStep 6716945 = 5037709) B5037709
theorem B2358809 : Blo 1572484 2358809 := bstep (se 2 (by rfl) ⟨884553, by rfl⟩ : syracuseStep 2358809 = 1769107) B1769107
theorem B3538457 : Blo 1572484 3538457 := bstep (se 2 (by rfl) ⟨1326921, by rfl⟩ : syracuseStep 3538457 = 2653843) B2653843
theorem B1793611 : Blo 1572484 1793611 := bstep (se 1 (by rfl) ⟨1345208, by rfl⟩ : syracuseStep 1793611 = 2690417) B2690417
theorem B3833419 : Blo 1572484 3833419 := bstep (se 1 (by rfl) ⟨2875064, by rfl⟩ : syracuseStep 3833419 = 5750129) B5750129
theorem B3538547 : Blo 1572484 3538547 := bstep (se 1 (by rfl) ⟨2653910, by rfl⟩ : syracuseStep 3538547 = 5307821) B5307821
theorem B1572491 : Blo 1572484 1572491 := bstep (se 1 (by rfl) ⟨1179368, by rfl⟩ : syracuseStep 1572491 = 2358737) B2358737
theorem B2358923 : Blo 1572484 2358923 := bstep (se 1 (by rfl) ⟨1769192, by rfl⟩ : syracuseStep 2358923 = 3538385) B3538385
theorem B1572503 : Blo 1572484 1572503 := bstep (se 1 (by rfl) ⟨1179377, by rfl⟩ : syracuseStep 1572503 = 2358755) B2358755
theorem B2358935 : Blo 1572484 2358935 := bstep (se 1 (by rfl) ⟨1769201, by rfl⟩ : syracuseStep 2358935 = 3538403) B3538403
theorem B3538583 : Blo 1572484 3538583 := bstep (se 1 (by rfl) ⟨2653937, by rfl⟩ : syracuseStep 3538583 = 5307875) B5307875
theorem B1572523 : Blo 1572484 1572523 := bstep (se 1 (by rfl) ⟨1179392, by rfl⟩ : syracuseStep 1572523 = 2358785) B2358785
theorem B1572535 : Blo 1572484 1572535 := bstep (se 1 (by rfl) ⟨1179401, by rfl⟩ : syracuseStep 1572535 = 2358803) B2358803
theorem B1769143 : Blo 1572484 1769143 := bstep (se 1 (by rfl) ⟨1326857, by rfl⟩ : syracuseStep 1769143 = 2653715) B2653715
theorem B3587777 : Blo 1572484 3587777 := bstep (se 2 (by rfl) ⟨1345416, by rfl⟩ : syracuseStep 3587777 = 2690833) B2690833
theorem B1572555 : Blo 1572484 1572555 := bstep (se 1 (by rfl) ⟨1179416, by rfl⟩ : syracuseStep 1572555 = 2358833) B2358833
theorem B1572567 : Blo 1572484 1572567 := bstep (se 1 (by rfl) ⟨1179425, by rfl⟩ : syracuseStep 1572567 = 2358851) B2358851
theorem B2359001 : Blo 1572484 2359001 := bstep (se 2 (by rfl) ⟨884625, by rfl⟩ : syracuseStep 2359001 = 1769251) B1769251
theorem B1572587 : Blo 1572484 1572587 := bstep (se 1 (by rfl) ⟨1179440, by rfl⟩ : syracuseStep 1572587 = 2358881) B2358881
theorem B1572599 : Blo 1572484 1572599 := bstep (se 1 (by rfl) ⟨1179449, by rfl⟩ : syracuseStep 1572599 = 2358899) B2358899
theorem B1572619 : Blo 1572484 1572619 := bstep (se 1 (by rfl) ⟨1179464, by rfl⟩ : syracuseStep 1572619 = 2358929) B2358929
theorem B1572631 : Blo 1572484 1572631 := bstep (se 1 (by rfl) ⟨1179473, by rfl⟩ : syracuseStep 1572631 = 2358947) B2358947
theorem B1990423 : Blo 1572484 1990423 := bstep (se 1 (by rfl) ⟨1492817, by rfl⟩ : syracuseStep 1990423 = 2985635) B2985635
theorem B1572651 : Blo 1572484 1572651 := bstep (se 1 (by rfl) ⟨1179488, by rfl⟩ : syracuseStep 1572651 = 2358977) B2358977
theorem B1572663 : Blo 1572484 1572663 := bstep (se 1 (by rfl) ⟨1179497, by rfl⟩ : syracuseStep 1572663 = 2358995) B2358995
theorem B1572683 : Blo 1572484 1572683 := bstep (se 1 (by rfl) ⟨1179512, by rfl⟩ : syracuseStep 1572683 = 2359025) B2359025
theorem B2359115 : Blo 1572484 2359115 := bstep (se 1 (by rfl) ⟨1769336, by rfl⟩ : syracuseStep 2359115 = 3538673) B3538673
theorem B3538763 : Blo 1572484 3538763 := bstep (se 1 (by rfl) ⟨2654072, by rfl⟩ : syracuseStep 3538763 = 5308145) B5308145
theorem B1572695 : Blo 1572484 1572695 := bstep (se 1 (by rfl) ⟨1179521, by rfl⟩ : syracuseStep 1572695 = 2359043) B2359043
theorem B2359127 : Blo 1572484 2359127 := bstep (se 1 (by rfl) ⟨1769345, by rfl⟩ : syracuseStep 2359127 = 3538691) B3538691
theorem B2654039 : Blo 1572484 2654039 := bstep (se 1 (by rfl) ⟨1990529, by rfl⟩ : syracuseStep 2654039 = 3981059) B3981059
theorem B5308253 : Blo 1572484 5308253 := bstep (se 3 (by rfl) ⟨995297, by rfl⟩ : syracuseStep 5308253 = 1990595) B1990595
theorem B7962461 : Blo 1572484 7962461 := bstep (se 3 (by rfl) ⟨1492961, by rfl⟩ : syracuseStep 7962461 = 2985923) B2985923
theorem B1572715 : Blo 1572484 1572715 := bstep (se 1 (by rfl) ⟨1179536, by rfl⟩ : syracuseStep 1572715 = 2359073) B2359073
theorem B1769323 : Blo 1572484 1769323 := bstep (se 1 (by rfl) ⟨1326992, by rfl⟩ : syracuseStep 1769323 = 2653985) B2653985
theorem B1572727 : Blo 1572484 1572727 := bstep (se 1 (by rfl) ⟨1179545, by rfl⟩ : syracuseStep 1572727 = 2359091) B2359091
theorem B3538817 : Blo 1572484 3538817 := bstep (se 2 (by rfl) ⟨1327056, by rfl⟩ : syracuseStep 3538817 = 2654113) B2654113
theorem B1572747 : Blo 1572484 1572747 := bstep (se 1 (by rfl) ⟨1179560, by rfl⟩ : syracuseStep 1572747 = 2359121) B2359121
theorem B1572759 : Blo 1572484 1572759 := bstep (se 1 (by rfl) ⟨1179569, by rfl⟩ : syracuseStep 1572759 = 2359139) B2359139
theorem B2359193 : Blo 1572484 2359193 := bstep (se 2 (by rfl) ⟨884697, by rfl⟩ : syracuseStep 2359193 = 1769395) B1769395
theorem B1572779 : Blo 1572484 1572779 := bstep (se 1 (by rfl) ⟨1179584, by rfl⟩ : syracuseStep 1572779 = 2359169) B2359169
theorem B1572791 : Blo 1572484 1572791 := bstep (se 1 (by rfl) ⟨1179593, by rfl⟩ : syracuseStep 1572791 = 2359187) B2359187
theorem B1572811 : Blo 1572484 1572811 := bstep (se 1 (by rfl) ⟨1179608, by rfl⟩ : syracuseStep 1572811 = 2359217) B2359217
theorem B1572823 : Blo 1572484 1572823 := bstep (se 1 (by rfl) ⟨1179617, by rfl⟩ : syracuseStep 1572823 = 2359235) B2359235
theorem B1769431 : Blo 1572484 1769431 := bstep (se 1 (by rfl) ⟨1327073, by rfl⟩ : syracuseStep 1769431 = 2654147) B2654147
theorem B2654167 : Blo 1572484 2654167 := bstep (se 1 (by rfl) ⟨1990625, by rfl⟩ : syracuseStep 2654167 = 3981251) B3981251
theorem B1679339 : Blo 1572484 1679339 := bstep (se 1 (by rfl) ⟨1259504, by rfl⟩ : syracuseStep 1679339 = 2519009) B2519009
theorem B1572843 : Blo 1572484 1572843 := bstep (se 1 (by rfl) ⟨1179632, by rfl⟩ : syracuseStep 1572843 = 2359265) B2359265
theorem B1572855 : Blo 1572484 1572855 := bstep (se 1 (by rfl) ⟨1179641, by rfl⟩ : syracuseStep 1572855 = 2359283) B2359283
theorem B1572871 : Blo 1572484 1572871 := bstep (se 1 (by rfl) ⟨1179653, by rfl⟩ : syracuseStep 1572871 = 2359307) B2359307
theorem B1572879 : Blo 1572484 1572879 := bstep (se 1 (by rfl) ⟨1179659, by rfl⟩ : syracuseStep 1572879 = 2359319) B2359319
theorem B8503319 : Blo 1572484 8503319 := bstep (se 1 (by rfl) ⟨6377489, by rfl⟩ : syracuseStep 8503319 = 12754979) B12754979
theorem B2359355 : Blo 1572484 2359355 := bstep (se 1 (by rfl) ⟨1769516, by rfl⟩ : syracuseStep 2359355 = 3539033) B3539033
theorem B1572923 : Blo 1572484 1572923 := bstep (se 1 (by rfl) ⟨1179692, by rfl⟩ : syracuseStep 1572923 = 2359385) B2359385
theorem B10084439 : Blo 1572484 10084439 := bstep (se 1 (by rfl) ⟨7563329, by rfl⟩ : syracuseStep 10084439 = 15126659) B15126659
theorem B2359415 : Blo 1572484 2359415 := bstep (se 1 (by rfl) ⟨1769561, by rfl⟩ : syracuseStep 2359415 = 3539123) B3539123
theorem B1572999 : Blo 1572484 1572999 := bstep (se 1 (by rfl) ⟨1179749, by rfl⟩ : syracuseStep 1572999 = 2359499) B2359499
theorem B2359439 : Blo 1572484 2359439 := bstep (se 1 (by rfl) ⟨1769579, by rfl⟩ : syracuseStep 2359439 = 3539159) B3539159
theorem B1573007 : Blo 1572484 1573007 := bstep (se 1 (by rfl) ⟨1179755, by rfl⟩ : syracuseStep 1573007 = 2359511) B2359511
theorem B2359481 : Blo 1572484 2359481 := bstep (se 2 (by rfl) ⟨884805, by rfl⟩ : syracuseStep 2359481 = 1769611) B1769611
theorem B1573051 : Blo 1572484 1573051 := bstep (se 1 (by rfl) ⟨1179788, by rfl⟩ : syracuseStep 1573051 = 2359577) B2359577
theorem B1990919 : Blo 1572484 1990919 := bstep (se 1 (by rfl) ⟨1493189, by rfl⟩ : syracuseStep 1990919 = 2986379) B2986379
theorem B1573135 : Blo 1572484 1573135 := bstep (se 1 (by rfl) ⟨1179851, by rfl⟩ : syracuseStep 1573135 = 2359703) B2359703
theorem B2359595 : Blo 1572484 2359595 := bstep (se 1 (by rfl) ⟨1769696, by rfl⟩ : syracuseStep 2359595 = 3539393) B3539393
theorem B1573179 : Blo 1572484 1573179 := bstep (se 1 (by rfl) ⟨1179884, by rfl⟩ : syracuseStep 1573179 = 2359769) B2359769
theorem B2359625 : Blo 1572484 2359625 := bstep (se 2 (by rfl) ⟨884859, by rfl⟩ : syracuseStep 2359625 = 1769719) B1769719
theorem B2654599 : Blo 1572484 2654599 := bstep (se 1 (by rfl) ⟨1990949, by rfl⟩ : syracuseStep 2654599 = 3981899) B3981899
theorem B1769863 : Blo 1572484 1769863 := bstep (se 1 (by rfl) ⟨1327397, by rfl⟩ : syracuseStep 1769863 = 2654795) B2654795
theorem B1573255 : Blo 1572484 1573255 := bstep (se 1 (by rfl) ⟨1179941, by rfl⟩ : syracuseStep 1573255 = 2359883) B2359883
theorem B1573263 : Blo 1572484 1573263 := bstep (se 1 (by rfl) ⟨1179947, by rfl⟩ : syracuseStep 1573263 = 2359895) B2359895
theorem B574390673 : Blo 1572484 574390673 := bstep (se 2 (by rfl) ⟨215396502, by rfl⟩ : syracuseStep 574390673 = 430793005) B430793005
theorem B25534865 : Blo 1572484 25534865 := bstep (se 2 (by rfl) ⟨9575574, by rfl⟩ : syracuseStep 25534865 = 19151149) B19151149
theorem B2359739 : Blo 1572484 2359739 := bstep (se 1 (by rfl) ⟨1769804, by rfl⟩ : syracuseStep 2359739 = 3539609) B3539609
theorem B1573307 : Blo 1572484 1573307 := bstep (se 1 (by rfl) ⟨1179980, by rfl⟩ : syracuseStep 1573307 = 2359961) B2359961
theorem B2392507 : Blo 1572484 2392507 := bstep (se 1 (by rfl) ⟨1794380, by rfl⟩ : syracuseStep 2392507 = 3588761) B3588761
theorem B2359799 : Blo 1572484 2359799 := bstep (se 1 (by rfl) ⟨1769849, by rfl⟩ : syracuseStep 2359799 = 3539699) B3539699
theorem B1573383 : Blo 1572484 1573383 := bstep (se 1 (by rfl) ⟨1180037, by rfl⟩ : syracuseStep 1573383 = 2360075) B2360075
theorem B2359823 : Blo 1572484 2359823 := bstep (se 1 (by rfl) ⟨1769867, by rfl⟩ : syracuseStep 2359823 = 3539735) B3539735
theorem B1573391 : Blo 1572484 1573391 := bstep (se 1 (by rfl) ⟨1180043, by rfl⟩ : syracuseStep 1573391 = 2360087) B2360087
theorem B17924651 : Blo 1572484 17924651 := bstep (se 1 (by rfl) ⟨13443488, by rfl⟩ : syracuseStep 17924651 = 26886977) B26886977
theorem B2359865 : Blo 1572484 2359865 := bstep (se 2 (by rfl) ⟨884949, by rfl⟩ : syracuseStep 2359865 = 1769899) B1769899
theorem B1770043 : Blo 1572484 1770043 := bstep (se 1 (by rfl) ⟨1327532, by rfl⟩ : syracuseStep 1770043 = 2655065) B2655065
theorem B1573435 : Blo 1572484 1573435 := bstep (se 1 (by rfl) ⟨1180076, by rfl⟩ : syracuseStep 1573435 = 2360153) B2360153
theorem B2392649 : Blo 1572484 2392649 := bstep (se 2 (by rfl) ⟨897243, by rfl⟩ : syracuseStep 2392649 = 1794487) B1794487
theorem B3539591 : Blo 1572484 3539591 := bstep (se 1 (by rfl) ⟨2654693, by rfl⟩ : syracuseStep 3539591 = 5309387) B5309387
theorem B2359943 : Blo 1572484 2359943 := bstep (se 1 (by rfl) ⟨1769957, by rfl⟩ : syracuseStep 2359943 = 3539915) B3539915
theorem B1573511 : Blo 1572484 1573511 := bstep (se 1 (by rfl) ⟨1180133, by rfl⟩ : syracuseStep 1573511 = 2360267) B2360267
theorem B1573519 : Blo 1572484 1573519 := bstep (se 1 (by rfl) ⟨1180139, by rfl⟩ : syracuseStep 1573519 = 2360279) B2360279
theorem B2359979 : Blo 1572484 2359979 := bstep (se 1 (by rfl) ⟨1769984, by rfl⟩ : syracuseStep 2359979 = 3539969) B3539969
theorem B1573563 : Blo 1572484 1573563 := bstep (se 1 (by rfl) ⟨1180172, by rfl⟩ : syracuseStep 1573563 = 2360345) B2360345
theorem B2360009 : Blo 1572484 2360009 := bstep (se 2 (by rfl) ⟨885003, by rfl⟩ : syracuseStep 2360009 = 1770007) B1770007
theorem B3982081 : Blo 1572484 3982081 := bstep (se 2 (by rfl) ⟨1493280, by rfl⟩ : syracuseStep 3982081 = 2986561) B2986561
theorem B1573639 : Blo 1572484 1573639 := bstep (se 1 (by rfl) ⟨1180229, by rfl⟩ : syracuseStep 1573639 = 2360459) B2360459
theorem B1573647 : Blo 1572484 1573647 := bstep (se 1 (by rfl) ⟨1180235, by rfl⟩ : syracuseStep 1573647 = 2360471) B2360471
theorem B2835233 : Blo 1572484 2835233 := bstep (se 2 (by rfl) ⟨1063212, by rfl⟩ : syracuseStep 2835233 = 2126425) B2126425
theorem B19137329 : Blo 1572484 19137329 := bstep (se 2 (by rfl) ⟨7176498, by rfl⟩ : syracuseStep 19137329 = 14352997) B14352997
theorem B3539771 : Blo 1572484 3539771 := bstep (se 1 (by rfl) ⟨2654828, by rfl⟩ : syracuseStep 3539771 = 5309657) B5309657
theorem B2360123 : Blo 1572484 2360123 := bstep (se 1 (by rfl) ⟨1770092, by rfl⟩ : syracuseStep 2360123 = 3540185) B3540185
theorem B1573691 : Blo 1572484 1573691 := bstep (se 1 (by rfl) ⟨1180268, by rfl⟩ : syracuseStep 1573691 = 2360537) B2360537
theorem B7562099 : Blo 1572484 7562099 := bstep (se 1 (by rfl) ⟨5671574, by rfl⟩ : syracuseStep 7562099 = 11343149) B11343149
theorem B2360183 : Blo 1572484 2360183 := bstep (se 1 (by rfl) ⟨1770137, by rfl⟩ : syracuseStep 2360183 = 3540275) B3540275
theorem B1573767 : Blo 1572484 1573767 := bstep (se 1 (by rfl) ⟨1180325, by rfl⟩ : syracuseStep 1573767 = 2360651) B2360651
theorem B2360207 : Blo 1572484 2360207 := bstep (se 1 (by rfl) ⟨1770155, by rfl⟩ : syracuseStep 2360207 = 3540311) B3540311
theorem B1991567 : Blo 1572484 1991567 := bstep (se 1 (by rfl) ⟨1493675, by rfl⟩ : syracuseStep 1991567 = 2987351) B2987351
theorem B1573775 : Blo 1572484 1573775 := bstep (se 1 (by rfl) ⟨1180331, by rfl⟩ : syracuseStep 1573775 = 2360663) B2360663
theorem B3539897 : Blo 1572484 3539897 := bstep (se 2 (by rfl) ⟨1327461, by rfl⟩ : syracuseStep 3539897 = 2654923) B2654923
theorem B2360249 : Blo 1572484 2360249 := bstep (se 2 (by rfl) ⟨885093, by rfl⟩ : syracuseStep 2360249 = 1770187) B1770187
theorem B1573819 : Blo 1572484 1573819 := bstep (se 1 (by rfl) ⟨1180364, by rfl⟩ : syracuseStep 1573819 = 2360729) B2360729
theorem B11944907 : Blo 1572484 11944907 := bstep (se 1 (by rfl) ⟨8958680, by rfl⟩ : syracuseStep 11944907 = 17917361) B17917361
theorem B7963595 : Blo 1572484 7963595 := bstep (se 1 (by rfl) ⟨5972696, by rfl⟩ : syracuseStep 7963595 = 11945393) B11945393
theorem B2360327 : Blo 1572484 2360327 := bstep (se 1 (by rfl) ⟨1770245, by rfl⟩ : syracuseStep 2360327 = 3540491) B3540491
theorem B1573895 : Blo 1572484 1573895 := bstep (se 1 (by rfl) ⟨1180421, by rfl⟩ : syracuseStep 1573895 = 2360843) B2360843
theorem B2655247 : Blo 1572484 2655247 := bstep (se 1 (by rfl) ⟨1991435, by rfl⟩ : syracuseStep 2655247 = 3982871) B3982871
theorem B1770511 : Blo 1572484 1770511 := bstep (se 1 (by rfl) ⟨1327883, by rfl⟩ : syracuseStep 1770511 = 2655767) B2655767
theorem B1573903 : Blo 1572484 1573903 := bstep (se 1 (by rfl) ⟨1180427, by rfl⟩ : syracuseStep 1573903 = 2360855) B2360855
theorem B2360363 : Blo 1572484 2360363 := bstep (se 1 (by rfl) ⟨1770272, by rfl⟩ : syracuseStep 2360363 = 3540545) B3540545
theorem B1573947 : Blo 1572484 1573947 := bstep (se 1 (by rfl) ⟨1180460, by rfl⟩ : syracuseStep 1573947 = 2360921) B2360921
theorem B2360393 : Blo 1572484 2360393 := bstep (se 2 (by rfl) ⟨885147, by rfl⟩ : syracuseStep 2360393 = 1770295) B1770295
theorem B17933399 : Blo 1572484 17933399 := bstep (se 1 (by rfl) ⟨13450049, by rfl⟩ : syracuseStep 17933399 = 26900099) B26900099
theorem B1574023 : Blo 1572484 1574023 := bstep (se 1 (by rfl) ⟨1180517, by rfl⟩ : syracuseStep 1574023 = 2361035) B2361035
theorem B1574031 : Blo 1572484 1574031 := bstep (se 1 (by rfl) ⟨1180523, by rfl⟩ : syracuseStep 1574031 = 2361047) B2361047
theorem B2360507 : Blo 1572484 2360507 := bstep (se 1 (by rfl) ⟨1770380, by rfl⟩ : syracuseStep 2360507 = 3540761) B3540761
theorem B1574075 : Blo 1572484 1574075 := bstep (se 1 (by rfl) ⟨1180556, by rfl⟩ : syracuseStep 1574075 = 2361113) B2361113
theorem B2360567 : Blo 1572484 2360567 := bstep (se 1 (by rfl) ⟨1770425, by rfl⟩ : syracuseStep 2360567 = 3540851) B3540851
theorem B1574151 : Blo 1572484 1574151 := bstep (se 1 (by rfl) ⟨1180613, by rfl⟩ : syracuseStep 1574151 = 2361227) B2361227
theorem B7963919 : Blo 1572484 7963919 := bstep (se 1 (by rfl) ⟨5972939, by rfl⟩ : syracuseStep 7963919 = 11945879) B11945879
theorem B5309711 : Blo 1572484 5309711 := bstep (se 1 (by rfl) ⟨3982283, by rfl⟩ : syracuseStep 5309711 = 7964567) B7964567
theorem B3540239 : Blo 1572484 3540239 := bstep (se 1 (by rfl) ⟨2655179, by rfl⟩ : syracuseStep 3540239 = 5310359) B5310359
theorem B2360591 : Blo 1572484 2360591 := bstep (se 1 (by rfl) ⟨1770443, by rfl⟩ : syracuseStep 2360591 = 3540887) B3540887
theorem B1574159 : Blo 1572484 1574159 := bstep (se 1 (by rfl) ⟨1180619, by rfl⟩ : syracuseStep 1574159 = 2361239) B2361239
theorem B3540257 : Blo 1572484 3540257 := bstep (se 2 (by rfl) ⟨1327596, by rfl⟩ : syracuseStep 3540257 = 2655193) B2655193
theorem B4482337 : Blo 1572484 4482337 := bstep (se 2 (by rfl) ⟨1680876, by rfl⟩ : syracuseStep 4482337 = 3361753) B3361753
theorem B2359559 : Blo 1572484 2359559 := bstep (se 1 (by rfl) ⟨1769669, by rfl⟩ : syracuseStep 2359559 = 3539339) B3539339
theorem B1573127 : Blo 1572484 1573127 := bstep (se 1 (by rfl) ⟨1179845, by rfl⟩ : syracuseStep 1573127 = 2359691) B2359691
theorem B2360633 : Blo 1572484 2360633 := bstep (se 2 (by rfl) ⟨885237, by rfl⟩ : syracuseStep 2360633 = 1770475) B1770475
theorem B1574203 : Blo 1572484 1574203 := bstep (se 1 (by rfl) ⟨1180652, by rfl⟩ : syracuseStep 1574203 = 2361305) B2361305
theorem B6382907 : Blo 1572484 6382907 := bstep (se 1 (by rfl) ⟨4787180, by rfl⟩ : syracuseStep 6382907 = 9574361) B9574361
theorem B3982679 : Blo 1572484 3982679 := bstep (se 1 (by rfl) ⟨2987009, by rfl⟩ : syracuseStep 3982679 = 5974019) B5974019
theorem B2360711 : Blo 1572484 2360711 := bstep (se 1 (by rfl) ⟨1770533, by rfl⟩ : syracuseStep 2360711 = 3541067) B3541067
theorem B1574279 : Blo 1572484 1574279 := bstep (se 1 (by rfl) ⟨1180709, by rfl⟩ : syracuseStep 1574279 = 2361419) B2361419
theorem B1574287 : Blo 1572484 1574287 := bstep (se 1 (by rfl) ⟨1180715, by rfl⟩ : syracuseStep 1574287 = 2361431) B2361431
theorem B2360747 : Blo 1572484 2360747 := bstep (se 1 (by rfl) ⟨1770560, by rfl⟩ : syracuseStep 2360747 = 3541121) B3541121
theorem B1574331 : Blo 1572484 1574331 := bstep (se 1 (by rfl) ⟨1180748, by rfl⟩ : syracuseStep 1574331 = 2361497) B2361497
theorem B2360777 : Blo 1572484 2360777 := bstep (se 2 (by rfl) ⟨885291, by rfl⟩ : syracuseStep 2360777 = 1770583) B1770583
theorem B13436381 : Blo 1572484 13436381 := bstep (se 3 (by rfl) ⟨2519321, by rfl⟩ : syracuseStep 13436381 = 5038643) B5038643
theorem B1771015 : Blo 1572484 1771015 := bstep (se 1 (by rfl) ⟨1328261, by rfl⟩ : syracuseStep 1771015 = 2656523) B2656523
theorem B1574407 : Blo 1572484 1574407 := bstep (se 1 (by rfl) ⟨1180805, by rfl⟩ : syracuseStep 1574407 = 2361611) B2361611
theorem B1574415 : Blo 1572484 1574415 := bstep (se 1 (by rfl) ⟨1180811, by rfl⟩ : syracuseStep 1574415 = 2361623) B2361623
theorem B5973533 : Blo 1572484 5973533 := bstep (se 3 (by rfl) ⟨1120037, by rfl⟩ : syracuseStep 5973533 = 2240075) B2240075
theorem B5309981 : Blo 1572484 5309981 := bstep (se 3 (by rfl) ⟨995621, by rfl⟩ : syracuseStep 5309981 = 1991243) B1991243
theorem B5973547 : Blo 1572484 5973547 := bstep (se 1 (by rfl) ⟨4480160, by rfl⟩ : syracuseStep 5973547 = 8960321) B8960321
theorem B3982891 : Blo 1572484 3982891 := bstep (se 1 (by rfl) ⟨2987168, by rfl⟩ : syracuseStep 3982891 = 5974337) B5974337
theorem B2655787 : Blo 1572484 2655787 := bstep (se 1 (by rfl) ⟨1991840, by rfl⟩ : syracuseStep 2655787 = 3983681) B3983681
theorem B2360891 : Blo 1572484 2360891 := bstep (se 1 (by rfl) ⟨1770668, by rfl⟩ : syracuseStep 2360891 = 3541337) B3541337
theorem B1574459 : Blo 1572484 1574459 := bstep (se 1 (by rfl) ⟨1180844, by rfl⟩ : syracuseStep 1574459 = 2361689) B2361689
theorem B4146803 : Blo 1572484 4146803 := bstep (se 1 (by rfl) ⟨3110102, by rfl⟩ : syracuseStep 4146803 = 6220205) B6220205
theorem B3540599 : Blo 1572484 3540599 := bstep (se 1 (by rfl) ⟨2655449, by rfl⟩ : syracuseStep 3540599 = 5310899) B5310899
theorem B2360951 : Blo 1572484 2360951 := bstep (se 1 (by rfl) ⟨1770713, by rfl⟩ : syracuseStep 2360951 = 3541427) B3541427
theorem B2360975 : Blo 1572484 2360975 := bstep (se 1 (by rfl) ⟨1770731, by rfl⟩ : syracuseStep 2360975 = 3541463) B3541463
theorem B3983033 : Blo 1572484 3983033 := bstep (se 2 (by rfl) ⟨1493637, by rfl⟩ : syracuseStep 3983033 = 2987275) B2987275
theorem B2655929 : Blo 1572484 2655929 := bstep (se 2 (by rfl) ⟨995973, by rfl⟩ : syracuseStep 2655929 = 1991947) B1991947
theorem B2361017 : Blo 1572484 2361017 := bstep (se 2 (by rfl) ⟨885381, by rfl⟩ : syracuseStep 2361017 = 1770763) B1770763
theorem B1771195 : Blo 1572484 1771195 := bstep (se 1 (by rfl) ⟨1328396, by rfl⟩ : syracuseStep 1771195 = 2656793) B2656793
theorem B2361095 : Blo 1572484 2361095 := bstep (se 1 (by rfl) ⟨1770821, by rfl⟩ : syracuseStep 2361095 = 3541643) B3541643
theorem B4482827 : Blo 1572484 4482827 := bstep (se 1 (by rfl) ⟨3362120, by rfl⟩ : syracuseStep 4482827 = 6724241) B6724241
theorem B7563041 : Blo 1572484 7563041 := bstep (se 2 (by rfl) ⟨2836140, by rfl⟩ : syracuseStep 7563041 = 5672281) B5672281
theorem B6383393 : Blo 1572484 6383393 := bstep (se 2 (by rfl) ⟨2393772, by rfl⟩ : syracuseStep 6383393 = 4787545) B4787545
theorem B12764965 : Blo 1572484 12764965 := bstep (se 4 (by rfl) ⟨1196715, by rfl⟩ : syracuseStep 12764965 = 2393431) B2393431
theorem B3540779 : Blo 1572484 3540779 := bstep (se 1 (by rfl) ⟨2655584, by rfl⟩ : syracuseStep 3540779 = 5311169) B5311169
theorem B2361131 : Blo 1572484 2361131 := bstep (se 1 (by rfl) ⟨1770848, by rfl⟩ : syracuseStep 2361131 = 3541697) B3541697
theorem B2361161 : Blo 1572484 2361161 := bstep (se 2 (by rfl) ⟨885435, by rfl⟩ : syracuseStep 2361161 = 1770871) B1770871
theorem B2361275 : Blo 1572484 2361275 := bstep (se 1 (by rfl) ⟨1770956, by rfl⟩ : syracuseStep 2361275 = 3541913) B3541913
theorem B2361335 : Blo 1572484 2361335 := bstep (se 1 (by rfl) ⟨1771001, by rfl⟩ : syracuseStep 2361335 = 3542003) B3542003
theorem B7970561 : Blo 1572484 7970561 := bstep (se 2 (by rfl) ⟨2988960, by rfl⟩ : syracuseStep 7970561 = 5977921) B5977921
theorem B2361359 : Blo 1572484 2361359 := bstep (se 1 (by rfl) ⟨1771019, by rfl⟩ : syracuseStep 2361359 = 3542039) B3542039
theorem B8955947 : Blo 1572484 8955947 := bstep (se 1 (by rfl) ⟨6716960, by rfl⟩ : syracuseStep 8955947 = 13433921) B13433921
theorem B2361401 : Blo 1572484 2361401 := bstep (se 2 (by rfl) ⟨885525, by rfl⟩ : syracuseStep 2361401 = 1771051) B1771051
theorem B2361479 : Blo 1572484 2361479 := bstep (se 1 (by rfl) ⟨1771109, by rfl⟩ : syracuseStep 2361479 = 3542219) B3542219
theorem B3541139 : Blo 1572484 3541139 := bstep (se 1 (by rfl) ⟨2655854, by rfl⟩ : syracuseStep 3541139 = 5311709) B5311709
theorem B2361515 : Blo 1572484 2361515 := bstep (se 1 (by rfl) ⟨1771136, by rfl⟩ : syracuseStep 2361515 = 3542273) B3542273
theorem B3541193 : Blo 1572484 3541193 := bstep (se 2 (by rfl) ⟨1327947, by rfl⟩ : syracuseStep 3541193 = 2655895) B2655895
theorem B2361545 : Blo 1572484 2361545 := bstep (se 2 (by rfl) ⟨885579, by rfl⟩ : syracuseStep 2361545 = 1771159) B1771159
theorem B14354747 : Blo 1572484 14354747 := bstep (se 1 (by rfl) ⟨10766060, by rfl⟩ : syracuseStep 14354747 = 21532121) B21532121
theorem B2361659 : Blo 1572484 2361659 := bstep (se 1 (by rfl) ⟨1771244, by rfl⟩ : syracuseStep 2361659 = 3542489) B3542489
theorem B2656631 : Blo 1572484 2656631 := bstep (se 1 (by rfl) ⟨1992473, by rfl⟩ : syracuseStep 2656631 = 3984947) B3984947
theorem B2361719 : Blo 1572484 2361719 := bstep (se 1 (by rfl) ⟨1771289, by rfl⟩ : syracuseStep 2361719 = 3542579) B3542579
theorem B2837035 : Blo 1572484 2837035 := bstep (se 1 (by rfl) ⟨2127776, by rfl⟩ : syracuseStep 2837035 = 4255553) B4255553
theorem B8620631 : Blo 1572484 8620631 := bstep (se 1 (by rfl) ⟨6465473, by rfl⟩ : syracuseStep 8620631 = 12930947) B12930947
theorem B8964695 : Blo 1572484 8964695 := bstep (se 1 (by rfl) ⟨6723521, by rfl⟩ : syracuseStep 8964695 = 13447043) B13447043
theorem B3984025 : Blo 1572484 3984025 := bstep (se 2 (by rfl) ⟨1494009, by rfl⟩ : syracuseStep 3984025 = 2988019) B2988019
theorem B7965377 : Blo 1572484 7965377 := bstep (se 2 (by rfl) ⟨2987016, by rfl⟩ : syracuseStep 7965377 = 5974033) B5974033
theorem B8743681 : Blo 1572484 8743681 := bstep (se 2 (by rfl) ⟨3278880, by rfl⟩ : syracuseStep 8743681 = 6557761) B6557761
theorem B3779387 : Blo 1572484 3779387 := bstep (se 1 (by rfl) ⟨2834540, by rfl⟩ : syracuseStep 3779387 = 5669081) B5669081
theorem B3984187 : Blo 1572484 3984187 := bstep (se 1 (by rfl) ⟨2988140, by rfl⟩ : syracuseStep 3984187 = 5976281) B5976281
theorem B34499417 : Blo 1572484 34499417 := bstep (se 2 (by rfl) ⟨12937281, by rfl⟩ : syracuseStep 34499417 = 25874563) B25874563
theorem B4311923 : Blo 1572484 4311923 := bstep (se 1 (by rfl) ⟨3233942, by rfl⟩ : syracuseStep 4311923 = 6467885) B6467885
theorem B4787059 : Blo 1572484 4787059 := bstep (se 1 (by rfl) ⟨3590294, by rfl⟩ : syracuseStep 4787059 = 7180589) B7180589
theorem B3541895 : Blo 1572484 3541895 := bstep (se 1 (by rfl) ⟨2656421, by rfl⟩ : syracuseStep 3541895 = 5312843) B5312843
theorem B5311385 : Blo 1572484 5311385 := bstep (se 2 (by rfl) ⟨1991769, by rfl⟩ : syracuseStep 5311385 = 3983539) B3983539
theorem B3779513 : Blo 1572484 3779513 := bstep (se 2 (by rfl) ⟨1417317, by rfl⟩ : syracuseStep 3779513 = 2834635) B2834635
theorem B3984329 : Blo 1572484 3984329 := bstep (se 2 (by rfl) ⟨1494123, by rfl⟩ : syracuseStep 3984329 = 2988247) B2988247
theorem B4664363 : Blo 1572484 4664363 := bstep (se 1 (by rfl) ⟨3498272, by rfl⟩ : syracuseStep 4664363 = 6996545) B6996545
theorem B3542075 : Blo 1572484 3542075 := bstep (se 1 (by rfl) ⟨2656556, by rfl⟩ : syracuseStep 3542075 = 5313113) B5313113
theorem B3542201 : Blo 1572484 3542201 := bstep (se 2 (by rfl) ⟨1328325, by rfl⟩ : syracuseStep 3542201 = 2656651) B2656651
theorem B3984673 : Blo 1572484 3984673 := bstep (se 2 (by rfl) ⟨1494252, by rfl⟩ : syracuseStep 3984673 = 2988505) B2988505
theorem B5672339 : Blo 1572484 5672339 := bstep (se 1 (by rfl) ⟨4254254, by rfl⟩ : syracuseStep 5672339 = 8508509) B8508509
theorem B8957405 : Blo 1572484 8957405 := bstep (se 3 (by rfl) ⟨1679513, by rfl⟩ : syracuseStep 8957405 = 3359027) B3359027
theorem B10079747 : Blo 1572484 10079747 := bstep (se 1 (by rfl) ⟨7559810, by rfl⟩ : syracuseStep 10079747 = 15119621) B15119621
theorem B3542543 : Blo 1572484 3542543 := bstep (se 1 (by rfl) ⟨2656907, by rfl⟩ : syracuseStep 3542543 = 5313815) B5313815
theorem B3542561 : Blo 1572484 3542561 := bstep (se 2 (by rfl) ⟨1328460, by rfl⟩ : syracuseStep 3542561 = 2656921) B2656921
theorem B5312087 : Blo 1572484 5312087 := bstep (se 1 (by rfl) ⟨3984065, by rfl⟩ : syracuseStep 5312087 = 7968131) B7968131
theorem B2690695 : Blo 1572484 2690695 := bstep (se 1 (by rfl) ⟨2018021, by rfl⟩ : syracuseStep 2690695 = 4036043) B4036043
theorem B2985673 : Blo 1572484 2985673 := bstep (se 2 (by rfl) ⟨1119627, by rfl⟩ : syracuseStep 2985673 = 2239255) B2239255
theorem B8507081 : Blo 1572484 8507081 := bstep (se 2 (by rfl) ⟨3190155, by rfl⟩ : syracuseStep 8507081 = 6380311) B6380311
theorem B54529793 : Blo 1572484 54529793 := bstep (se 2 (by rfl) ⟨20448672, by rfl⟩ : syracuseStep 54529793 = 40897345) B40897345
theorem B6377231 : Blo 1572484 6377231 := bstep (se 1 (by rfl) ⟨4782923, by rfl⟩ : syracuseStep 6377231 = 9565847) B9565847
theorem B9080591 : Blo 1572484 9080591 := bstep (se 1 (by rfl) ⟨6810443, by rfl⟩ : syracuseStep 9080591 = 13620887) B13620887
theorem B32280371 : Blo 1572484 32280371 := bstep (se 1 (by rfl) ⟨24210278, by rfl⟩ : syracuseStep 32280371 = 48420557) B48420557
theorem B3985271 : Blo 1572484 3985271 := bstep (se 1 (by rfl) ⟨2988953, by rfl⟩ : syracuseStep 3985271 = 5977907) B5977907
theorem B7966673 : Blo 1572484 7966673 := bstep (se 2 (by rfl) ⟨2987502, by rfl⟩ : syracuseStep 7966673 = 5975005) B5975005
theorem B5312573 : Blo 1572484 5312573 := bstep (se 3 (by rfl) ⟨996107, by rfl⟩ : syracuseStep 5312573 = 1992215) B1992215
theorem B2240713 : Blo 1572484 2240713 := bstep (se 2 (by rfl) ⟨840267, by rfl⟩ : syracuseStep 2240713 = 1680535) B1680535
theorem B3830075 : Blo 1572484 3830075 := bstep (se 1 (by rfl) ⟨2872556, by rfl⟩ : syracuseStep 3830075 = 5745113) B5745113
theorem B11342227 : Blo 1572484 11342227 := bstep (se 1 (by rfl) ⟨8506670, by rfl⟩ : syracuseStep 11342227 = 17013341) B17013341
theorem B8966609 : Blo 1572484 8966609 := bstep (se 2 (by rfl) ⟨3362478, by rfl⟩ : syracuseStep 8966609 = 6724957) B6724957
theorem B26882603 : Blo 1572484 26882603 := bstep (se 1 (by rfl) ⟨20161952, by rfl⟩ : syracuseStep 26882603 = 40323905) B40323905
theorem B8508077 : Blo 1572484 8508077 := bstep (se 3 (by rfl) ⟨1595264, by rfl⟩ : syracuseStep 8508077 = 3190529) B3190529
theorem B5108665 : Blo 1572484 5108665 := bstep (se 2 (by rfl) ⟨1915749, by rfl⟩ : syracuseStep 5108665 = 3831499) B3831499
theorem B4477963 : Blo 1572484 4477963 := bstep (se 1 (by rfl) ⟨3358472, by rfl⟩ : syracuseStep 4477963 = 6716945) B6716945
theorem B26891351 : Blo 1572484 26891351 := bstep (se 1 (by rfl) ⟨20168513, by rfl⟩ : syracuseStep 26891351 = 40337027) B40337027
theorem B9696449 : Blo 1572484 9696449 := bstep (se 2 (by rfl) ⟨3636168, by rfl⟩ : syracuseStep 9696449 = 7272337) B7272337
theorem B4478237 : Blo 1572484 4478237 := bstep (se 3 (by rfl) ⟨839669, by rfl⟩ : syracuseStep 4478237 = 1679339) B1679339
theorem B3782155 : Blo 1572484 3782155 := bstep (se 1 (by rfl) ⟨2836616, by rfl⟩ : syracuseStep 3782155 = 5673233) B5673233
theorem B2987579 : Blo 1572484 2987579 := bstep (se 1 (by rfl) ⟨2240684, by rfl⟩ : syracuseStep 2987579 = 4481369) B4481369
theorem B7558717 : Blo 1572484 7558717 := bstep (se 3 (by rfl) ⟨1417259, by rfl⟩ : syracuseStep 7558717 = 2834519) B2834519
theorem B8509157 : Blo 1572484 8509157 := bstep (se 4 (by rfl) ⟨797733, by rfl⟩ : syracuseStep 8509157 = 1595467) B1595467
theorem B15324977 : Blo 1572484 15324977 := bstep (se 2 (by rfl) ⟨5746866, by rfl⟩ : syracuseStep 15324977 = 11493733) B11493733
theorem B8075123 : Blo 1572484 8075123 := bstep (se 1 (by rfl) ⟨6056342, by rfl⟩ : syracuseStep 8075123 = 12112685) B12112685
theorem B22984651 : Blo 1572484 22984651 := bstep (se 1 (by rfl) ⟨17238488, by rfl⟩ : syracuseStep 22984651 = 34476977) B34476977
theorem B8960003 : Blo 1572484 8960003 := bstep (se 1 (by rfl) ⟨6720002, by rfl⟩ : syracuseStep 8960003 = 13440005) B13440005
theorem B7968779 : Blo 1572484 7968779 := bstep (se 1 (by rfl) ⟨5976584, by rfl⟩ : syracuseStep 7968779 = 11953169) B11953169
theorem B2988065 : Blo 1572484 2988065 := bstep (se 2 (by rfl) ⟨1120524, by rfl⟩ : syracuseStep 2988065 = 2241049) B2241049
theorem B3782771 : Blo 1572484 3782771 := bstep (se 1 (by rfl) ⟨2837078, by rfl⟩ : syracuseStep 3782771 = 5674157) B5674157
theorem B11950253 : Blo 1572484 11950253 := bstep (se 3 (by rfl) ⟨2240672, by rfl⟩ : syracuseStep 11950253 = 4481345) B4481345
theorem B7968941 : Blo 1572484 7968941 := bstep (se 3 (by rfl) ⟨1494176, by rfl⟩ : syracuseStep 7968941 = 2988353) B2988353
theorem B3406139 : Blo 1572484 3406139 := bstep (se 1 (by rfl) ⟨2554604, by rfl⟩ : syracuseStep 3406139 = 5109209) B5109209
theorem B2988407 : Blo 1572484 2988407 := bstep (se 1 (by rfl) ⟨2241305, by rfl⟩ : syracuseStep 2988407 = 4482611) B4482611
theorem B1595783 : Blo 1572484 1595783 := bstep (se 1 (by rfl) ⟨1196837, by rfl⟩ : syracuseStep 1595783 = 2393675) B2393675
theorem B7666073 : Blo 1572484 7666073 := bstep (se 2 (by rfl) ⟨2874777, by rfl⟩ : syracuseStep 7666073 = 5749555) B5749555
theorem B7174585 : Blo 1572484 7174585 := bstep (se 2 (by rfl) ⟨2690469, by rfl⟩ : syracuseStep 7174585 = 5380939) B5380939
theorem B36313667 : Blo 1572484 36313667 := bstep (se 1 (by rfl) ⟨27235250, by rfl⟩ : syracuseStep 36313667 = 54470501) B54470501
theorem B11942477 : Blo 1572484 11942477 := bstep (se 3 (by rfl) ⟨2239214, by rfl⟩ : syracuseStep 11942477 = 4478429) B4478429
theorem B17914445 : Blo 1572484 17914445 := bstep (se 3 (by rfl) ⟨3358958, by rfl⟩ : syracuseStep 17914445 = 6717917) B6717917
theorem B4602521 : Blo 1572484 4602521 := bstep (se 2 (by rfl) ⟨1725945, by rfl⟩ : syracuseStep 4602521 = 3451891) B3451891
theorem B43082533 : Blo 1572484 43082533 := bstep (se 4 (by rfl) ⟨4038987, by rfl⟩ : syracuseStep 43082533 = 8077975) B8077975
theorem B4848427 : Blo 1572484 4848427 := bstep (se 1 (by rfl) ⟨3636320, by rfl⟩ : syracuseStep 4848427 = 7272641) B7272641
theorem B7961489 : Blo 1572484 7961489 := bstep (se 2 (by rfl) ⟨2985558, by rfl⟩ : syracuseStep 7961489 = 5971117) B5971117
theorem B4480697 : Blo 1572484 4480697 := bstep (se 2 (by rfl) ⟨1680261, by rfl⟩ : syracuseStep 4480697 = 3360523) B3360523
theorem B3980441 : Blo 1572484 3980441 := bstep (se 2 (by rfl) ⟨1492665, by rfl⟩ : syracuseStep 3980441 = 2985331) B2985331
theorem B1844615 : Blo 1572484 1844615 := bstep (se 1 (by rfl) ⟨1383461, by rfl⟩ : syracuseStep 1844615 = 2766923) B2766923
theorem B3980603 : Blo 1572484 3980603 := bstep (se 1 (by rfl) ⟨2985452, by rfl⟩ : syracuseStep 3980603 = 5970905) B5970905
theorem B4480343 : Blo 1572484 4480343 := bstep (se 1 (by rfl) ⟨3360257, by rfl⟩ : syracuseStep 4480343 = 6720515) B6720515
theorem B3538295 : Blo 1572484 3538295 := bstep (se 1 (by rfl) ⟨2653721, by rfl⟩ : syracuseStep 3538295 = 5307443) B5307443
theorem B2391481 : Blo 1572484 2391481 := bstep (se 2 (by rfl) ⟨896805, by rfl⟩ : syracuseStep 2391481 = 1793611) B1793611
theorem B5111225 : Blo 1572484 5111225 := bstep (se 2 (by rfl) ⟨1916709, by rfl⟩ : syracuseStep 5111225 = 3833419) B3833419
theorem B2301385 : Blo 1572484 2301385 := bstep (se 2 (by rfl) ⟨863019, by rfl⟩ : syracuseStep 2301385 = 1726039) B1726039
theorem B11952683 : Blo 1572484 11952683 := bstep (se 1 (by rfl) ⟨8964512, by rfl⟩ : syracuseStep 11952683 = 17929025) B17929025
theorem B48455171 : Blo 1572484 48455171 := bstep (se 1 (by rfl) ⟨36341378, by rfl⟩ : syracuseStep 48455171 = 72682757) B72682757
theorem B2358791 : Blo 1572484 2358791 := bstep (se 1 (by rfl) ⟨1769093, by rfl⟩ : syracuseStep 2358791 = 3538187) B3538187
theorem B2358827 : Blo 1572484 2358827 := bstep (se 1 (by rfl) ⟨1769120, by rfl⟩ : syracuseStep 2358827 = 3538241) B3538241
theorem B3538475 : Blo 1572484 3538475 := bstep (se 1 (by rfl) ⟨2653856, by rfl⟩ : syracuseStep 3538475 = 5307713) B5307713
theorem B4480571 : Blo 1572484 4480571 := bstep (se 1 (by rfl) ⟨3360428, by rfl⟩ : syracuseStep 4480571 = 6720857) B6720857
theorem B2358857 : Blo 1572484 2358857 := bstep (se 2 (by rfl) ⟨884571, by rfl⟩ : syracuseStep 2358857 = 1769143) B1769143
theorem B1572487 : Blo 1572484 1572487 := bstep (se 1 (by rfl) ⟨1179365, by rfl⟩ : syracuseStep 1572487 = 2358731) B2358731
theorem B1572495 : Blo 1572484 1572495 := bstep (se 1 (by rfl) ⟨1179371, by rfl⟩ : syracuseStep 1572495 = 2358743) B2358743
theorem B3980947 : Blo 1572484 3980947 := bstep (se 1 (by rfl) ⟨2985710, by rfl⟩ : syracuseStep 3980947 = 5971421) B5971421
theorem B38280883 : Blo 1572484 38280883 := bstep (se 1 (by rfl) ⟨28710662, by rfl⟩ : syracuseStep 38280883 = 57421325) B57421325
theorem B1572539 : Blo 1572484 1572539 := bstep (se 1 (by rfl) ⟨1179404, by rfl⟩ : syracuseStep 1572539 = 2358809) B2358809
theorem B2358971 : Blo 1572484 2358971 := bstep (se 1 (by rfl) ⟨1769228, by rfl⟩ : syracuseStep 2358971 = 3538457) B3538457
theorem B2653897 : Blo 1572484 2653897 := bstep (se 2 (by rfl) ⟨995211, by rfl⟩ : syracuseStep 2653897 = 1990423) B1990423
theorem B2359031 : Blo 1572484 2359031 := bstep (se 1 (by rfl) ⟨1769273, by rfl⟩ : syracuseStep 2359031 = 3538547) B3538547
theorem B1572615 : Blo 1572484 1572615 := bstep (se 1 (by rfl) ⟨1179461, by rfl⟩ : syracuseStep 1572615 = 2358923) B2358923
theorem B1572623 : Blo 1572484 1572623 := bstep (se 1 (by rfl) ⟨1179467, by rfl⟩ : syracuseStep 1572623 = 2358935) B2358935
theorem B2359055 : Blo 1572484 2359055 := bstep (se 1 (by rfl) ⟨1769291, by rfl⟩ : syracuseStep 2359055 = 3538583) B3538583
theorem B3981089 : Blo 1572484 3981089 := bstep (se 2 (by rfl) ⟨1492908, by rfl⟩ : syracuseStep 3981089 = 2985817) B2985817
theorem B2391851 : Blo 1572484 2391851 := bstep (se 1 (by rfl) ⟨1793888, by rfl⟩ : syracuseStep 2391851 = 3587777) B3587777
theorem B2359097 : Blo 1572484 2359097 := bstep (se 2 (by rfl) ⟨884661, by rfl⟩ : syracuseStep 2359097 = 1769323) B1769323
theorem B1572667 : Blo 1572484 1572667 := bstep (se 1 (by rfl) ⟨1179500, by rfl⟩ : syracuseStep 1572667 = 2359001) B2359001
theorem B1572743 : Blo 1572484 1572743 := bstep (se 1 (by rfl) ⟨1179557, by rfl⟩ : syracuseStep 1572743 = 2359115) B2359115
theorem B2359175 : Blo 1572484 2359175 := bstep (se 1 (by rfl) ⟨1769381, by rfl⟩ : syracuseStep 2359175 = 3538763) B3538763
theorem B1572751 : Blo 1572484 1572751 := bstep (se 1 (by rfl) ⟨1179563, by rfl⟩ : syracuseStep 1572751 = 2359127) B2359127
theorem B1769359 : Blo 1572484 1769359 := bstep (se 1 (by rfl) ⟨1327019, by rfl⟩ : syracuseStep 1769359 = 2654039) B2654039
theorem B3538835 : Blo 1572484 3538835 := bstep (se 1 (by rfl) ⟨2654126, by rfl⟩ : syracuseStep 3538835 = 5308253) B5308253
theorem B5308307 : Blo 1572484 5308307 := bstep (se 1 (by rfl) ⟨3981230, by rfl⟩ : syracuseStep 5308307 = 7962461) B7962461
theorem B5037977 : Blo 1572484 5037977 := bstep (se 2 (by rfl) ⟨1889241, by rfl⟩ : syracuseStep 5037977 = 3778483) B3778483
theorem B2359211 : Blo 1572484 2359211 := bstep (se 1 (by rfl) ⟨1769408, by rfl⟩ : syracuseStep 2359211 = 3538817) B3538817
theorem B1572795 : Blo 1572484 1572795 := bstep (se 1 (by rfl) ⟨1179596, by rfl⟩ : syracuseStep 1572795 = 2359193) B2359193
theorem B2359241 : Blo 1572484 2359241 := bstep (se 2 (by rfl) ⟨884715, by rfl⟩ : syracuseStep 2359241 = 1769431) B1769431
theorem B3538889 : Blo 1572484 3538889 := bstep (se 2 (by rfl) ⟨1327083, by rfl⟩ : syracuseStep 3538889 = 2654167) B2654167
theorem B5668879 : Blo 1572484 5668879 := bstep (se 1 (by rfl) ⟨4251659, by rfl⟩ : syracuseStep 5668879 = 8503319) B8503319
theorem B1572903 : Blo 1572484 1572903 := bstep (se 1 (by rfl) ⟨1179677, by rfl⟩ : syracuseStep 1572903 = 2359355) B2359355
theorem B1572943 : Blo 1572484 1572943 := bstep (se 1 (by rfl) ⟨1179707, by rfl⟩ : syracuseStep 1572943 = 2359415) B2359415
theorem B1572959 : Blo 1572484 1572959 := bstep (se 1 (by rfl) ⟨1179719, by rfl⟩ : syracuseStep 1572959 = 2359439) B2359439
theorem B1572987 : Blo 1572484 1572987 := bstep (se 1 (by rfl) ⟨1179740, by rfl⟩ : syracuseStep 1572987 = 2359481) B2359481
theorem B1573039 : Blo 1572484 1573039 := bstep (se 1 (by rfl) ⟨1179779, by rfl⟩ : syracuseStep 1573039 = 2359559) B2359559
theorem B1573063 : Blo 1572484 1573063 := bstep (se 1 (by rfl) ⟨1179797, by rfl⟩ : syracuseStep 1573063 = 2359595) B2359595
theorem B1573083 : Blo 1572484 1573083 := bstep (se 1 (by rfl) ⟨1179812, by rfl⟩ : syracuseStep 1573083 = 2359625) B2359625
theorem B382927115 : Blo 1572484 382927115 := bstep (se 1 (by rfl) ⟨287195336, by rfl⟩ : syracuseStep 382927115 = 574390673) B574390673
theorem B17023243 : Blo 1572484 17023243 := bstep (se 1 (by rfl) ⟨12767432, by rfl⟩ : syracuseStep 17023243 = 25534865) B25534865
theorem B1573159 : Blo 1572484 1573159 := bstep (se 1 (by rfl) ⟨1179869, by rfl⟩ : syracuseStep 1573159 = 2359739) B2359739
theorem B1573199 : Blo 1572484 1573199 := bstep (se 1 (by rfl) ⟨1179899, by rfl⟩ : syracuseStep 1573199 = 2359799) B2359799
theorem B1573215 : Blo 1572484 1573215 := bstep (se 1 (by rfl) ⟨1179911, by rfl⟩ : syracuseStep 1573215 = 2359823) B2359823
theorem B1573243 : Blo 1572484 1573243 := bstep (se 1 (by rfl) ⟨1179932, by rfl⟩ : syracuseStep 1573243 = 2359865) B2359865
theorem B2359727 : Blo 1572484 2359727 := bstep (se 1 (by rfl) ⟨1769795, by rfl⟩ : syracuseStep 2359727 = 3539591) B3539591
theorem B1573295 : Blo 1572484 1573295 := bstep (se 1 (by rfl) ⟨1179971, by rfl⟩ : syracuseStep 1573295 = 2359943) B2359943
theorem B1573319 : Blo 1572484 1573319 := bstep (se 1 (by rfl) ⟨1179989, by rfl⟩ : syracuseStep 1573319 = 2359979) B2359979
theorem B1573339 : Blo 1572484 1573339 := bstep (se 1 (by rfl) ⟨1180004, by rfl⟩ : syracuseStep 1573339 = 2360009) B2360009
theorem B3539465 : Blo 1572484 3539465 := bstep (se 2 (by rfl) ⟨1327299, by rfl⟩ : syracuseStep 3539465 = 2654599) B2654599
theorem B2359817 : Blo 1572484 2359817 := bstep (se 2 (by rfl) ⟨884931, by rfl⟩ : syracuseStep 2359817 = 1769863) B1769863
theorem B15122969 : Blo 1572484 15122969 := bstep (se 2 (by rfl) ⟨5671113, by rfl⟩ : syracuseStep 15122969 = 11342227) B11342227
theorem B2359847 : Blo 1572484 2359847 := bstep (se 1 (by rfl) ⟨1769885, by rfl⟩ : syracuseStep 2359847 = 3539771) B3539771
theorem B1573415 : Blo 1572484 1573415 := bstep (se 1 (by rfl) ⟨1180061, by rfl⟩ : syracuseStep 1573415 = 2360123) B2360123
theorem B1573455 : Blo 1572484 1573455 := bstep (se 1 (by rfl) ⟨1180091, by rfl⟩ : syracuseStep 1573455 = 2360183) B2360183
theorem B1573471 : Blo 1572484 1573471 := bstep (se 1 (by rfl) ⟨1180103, by rfl⟩ : syracuseStep 1573471 = 2360207) B2360207
theorem B2359931 : Blo 1572484 2359931 := bstep (se 1 (by rfl) ⟨1769948, by rfl⟩ : syracuseStep 2359931 = 3539897) B3539897
theorem B1573499 : Blo 1572484 1573499 := bstep (se 1 (by rfl) ⟨1180124, by rfl⟩ : syracuseStep 1573499 = 2360249) B2360249
theorem B7963271 : Blo 1572484 7963271 := bstep (se 1 (by rfl) ⟨5972453, by rfl⟩ : syracuseStep 7963271 = 11944907) B11944907
theorem B5309063 : Blo 1572484 5309063 := bstep (se 1 (by rfl) ⟨3981797, by rfl⟩ : syracuseStep 5309063 = 7963595) B7963595
theorem B1573551 : Blo 1572484 1573551 := bstep (se 1 (by rfl) ⟨1180163, by rfl⟩ : syracuseStep 1573551 = 2360327) B2360327
theorem B5309117 : Blo 1572484 5309117 := bstep (se 3 (by rfl) ⟨995459, by rfl⟩ : syracuseStep 5309117 = 1990919) B1990919
theorem B1573575 : Blo 1572484 1573575 := bstep (se 1 (by rfl) ⟨1180181, by rfl⟩ : syracuseStep 1573575 = 2360363) B2360363
theorem B1573595 : Blo 1572484 1573595 := bstep (se 1 (by rfl) ⟨1180196, by rfl⟩ : syracuseStep 1573595 = 2360393) B2360393
theorem B2360057 : Blo 1572484 2360057 := bstep (se 2 (by rfl) ⟨885021, by rfl⟩ : syracuseStep 2360057 = 1770043) B1770043
theorem B1573671 : Blo 1572484 1573671 := bstep (se 1 (by rfl) ⟨1180253, by rfl⟩ : syracuseStep 1573671 = 2360507) B2360507
theorem B1573711 : Blo 1572484 1573711 := bstep (se 1 (by rfl) ⟨1180283, by rfl⟩ : syracuseStep 1573711 = 2360567) B2360567
theorem B5309279 : Blo 1572484 5309279 := bstep (se 1 (by rfl) ⟨3981959, by rfl⟩ : syracuseStep 5309279 = 7963919) B7963919
theorem B3539807 : Blo 1572484 3539807 := bstep (se 1 (by rfl) ⟨2654855, by rfl⟩ : syracuseStep 3539807 = 5309711) B5309711
theorem B2360159 : Blo 1572484 2360159 := bstep (se 1 (by rfl) ⟨1770119, by rfl⟩ : syracuseStep 2360159 = 3540239) B3540239
theorem B1573727 : Blo 1572484 1573727 := bstep (se 1 (by rfl) ⟨1180295, by rfl⟩ : syracuseStep 1573727 = 2360591) B2360591
theorem B2360171 : Blo 1572484 2360171 := bstep (se 1 (by rfl) ⟨1770128, by rfl⟩ : syracuseStep 2360171 = 3540257) B3540257
theorem B1573755 : Blo 1572484 1573755 := bstep (se 1 (by rfl) ⟨1180316, by rfl⟩ : syracuseStep 1573755 = 2360633) B2360633
theorem B2655119 : Blo 1572484 2655119 := bstep (se 1 (by rfl) ⟨1991339, by rfl⟩ : syracuseStep 2655119 = 3982679) B3982679
theorem B1573807 : Blo 1572484 1573807 := bstep (se 1 (by rfl) ⟨1180355, by rfl⟩ : syracuseStep 1573807 = 2360711) B2360711
theorem B1573831 : Blo 1572484 1573831 := bstep (se 1 (by rfl) ⟨1180373, by rfl⟩ : syracuseStep 1573831 = 2360747) B2360747
theorem B1573851 : Blo 1572484 1573851 := bstep (se 1 (by rfl) ⟨1180388, by rfl⟩ : syracuseStep 1573851 = 2360777) B2360777
theorem B5309441 : Blo 1572484 5309441 := bstep (se 2 (by rfl) ⟨1991040, by rfl⟩ : syracuseStep 5309441 = 3982081) B3982081
theorem B11658241 : Blo 1572484 11658241 := bstep (se 2 (by rfl) ⟨4371840, by rfl⟩ : syracuseStep 11658241 = 8743681) B8743681
theorem B3982355 : Blo 1572484 3982355 := bstep (se 1 (by rfl) ⟨2986766, by rfl⟩ : syracuseStep 3982355 = 5973533) B5973533
theorem B3539987 : Blo 1572484 3539987 := bstep (se 1 (by rfl) ⟨2654990, by rfl⟩ : syracuseStep 3539987 = 5309981) B5309981
theorem B1991719 : Blo 1572484 1991719 := bstep (se 1 (by rfl) ⟨1493789, by rfl⟩ : syracuseStep 1991719 = 2987579) B2987579
theorem B1573927 : Blo 1572484 1573927 := bstep (se 1 (by rfl) ⟨1180445, by rfl⟩ : syracuseStep 1573927 = 2360891) B2360891
theorem B2360399 : Blo 1572484 2360399 := bstep (se 1 (by rfl) ⟨1770299, by rfl⟩ : syracuseStep 2360399 = 3540599) B3540599
theorem B1573967 : Blo 1572484 1573967 := bstep (se 1 (by rfl) ⟨1180475, by rfl⟩ : syracuseStep 1573967 = 2360951) B2360951
theorem B1573983 : Blo 1572484 1573983 := bstep (se 1 (by rfl) ⟨1180487, by rfl⟩ : syracuseStep 1573983 = 2360975) B2360975
theorem B2655355 : Blo 1572484 2655355 := bstep (se 1 (by rfl) ⟨1991516, by rfl⟩ : syracuseStep 2655355 = 3983033) B3983033
theorem B1770619 : Blo 1572484 1770619 := bstep (se 1 (by rfl) ⟨1327964, by rfl⟩ : syracuseStep 1770619 = 2655929) B2655929
theorem B1574011 : Blo 1572484 1574011 := bstep (se 1 (by rfl) ⟨1180508, by rfl⟩ : syracuseStep 1574011 = 2361017) B2361017
theorem B6382745 : Blo 1572484 6382745 := bstep (se 2 (by rfl) ⟨2393529, by rfl⟩ : syracuseStep 6382745 = 4787059) B4787059
theorem B1574063 : Blo 1572484 1574063 := bstep (se 1 (by rfl) ⟨1180547, by rfl⟩ : syracuseStep 1574063 = 2361095) B2361095
theorem B2360519 : Blo 1572484 2360519 := bstep (se 1 (by rfl) ⟨1770389, by rfl⟩ : syracuseStep 2360519 = 3540779) B3540779
theorem B1574087 : Blo 1572484 1574087 := bstep (se 1 (by rfl) ⟨1180565, by rfl⟩ : syracuseStep 1574087 = 2361131) B2361131
theorem B10216651 : Blo 1572484 10216651 := bstep (se 1 (by rfl) ⟨7662488, by rfl⟩ : syracuseStep 10216651 = 15324977) B15324977
theorem B1574107 : Blo 1572484 1574107 := bstep (se 1 (by rfl) ⟨1180580, by rfl⟩ : syracuseStep 1574107 = 2361161) B2361161
theorem B5383415 : Blo 1572484 5383415 := bstep (se 1 (by rfl) ⟨4037561, by rfl⟩ : syracuseStep 5383415 = 8075123) B8075123
theorem B1574183 : Blo 1572484 1574183 := bstep (se 1 (by rfl) ⟨1180637, by rfl⟩ : syracuseStep 1574183 = 2361275) B2361275
theorem B1574223 : Blo 1572484 1574223 := bstep (se 1 (by rfl) ⟨1180667, by rfl⟩ : syracuseStep 1574223 = 2361335) B2361335
theorem B5973335 : Blo 1572484 5973335 := bstep (se 1 (by rfl) ⟨4480001, by rfl⟩ : syracuseStep 5973335 = 8960003) B8960003
theorem B1574239 : Blo 1572484 1574239 := bstep (se 1 (by rfl) ⟨1180679, by rfl⟩ : syracuseStep 1574239 = 2361359) B2361359
theorem B3540329 : Blo 1572484 3540329 := bstep (se 2 (by rfl) ⟨1327623, by rfl⟩ : syracuseStep 3540329 = 2655247) B2655247
theorem B2360681 : Blo 1572484 2360681 := bstep (se 2 (by rfl) ⟨885255, by rfl⟩ : syracuseStep 2360681 = 1770511) B1770511
theorem B1992043 : Blo 1572484 1992043 := bstep (se 1 (by rfl) ⟨1494032, by rfl⟩ : syracuseStep 1992043 = 2988065) B2988065
theorem B1574267 : Blo 1572484 1574267 := bstep (se 1 (by rfl) ⟨1180700, by rfl⟩ : syracuseStep 1574267 = 2361401) B2361401
theorem B2360759 : Blo 1572484 2360759 := bstep (se 1 (by rfl) ⟨1770569, by rfl⟩ : syracuseStep 2360759 = 3541139) B3541139
theorem B1574343 : Blo 1572484 1574343 := bstep (se 1 (by rfl) ⟨1180757, by rfl⟩ : syracuseStep 1574343 = 2361515) B2361515
theorem B2360795 : Blo 1572484 2360795 := bstep (se 1 (by rfl) ⟨1770596, by rfl⟩ : syracuseStep 2360795 = 3541193) B3541193
theorem B1574363 : Blo 1572484 1574363 := bstep (se 1 (by rfl) ⟨1180772, by rfl⟩ : syracuseStep 1574363 = 2361545) B2361545
theorem B2270759 : Blo 1572484 2270759 := bstep (se 1 (by rfl) ⟨1703069, by rfl⟩ : syracuseStep 2270759 = 3406139) B3406139
theorem B9569831 : Blo 1572484 9569831 := bstep (se 1 (by rfl) ⟨7177373, by rfl⟩ : syracuseStep 9569831 = 14354747) B14354747
theorem B1574439 : Blo 1572484 1574439 := bstep (se 1 (by rfl) ⟨1180829, by rfl⟩ : syracuseStep 1574439 = 2361659) B2361659
theorem B1992271 : Blo 1572484 1992271 := bstep (se 1 (by rfl) ⟨1494203, by rfl⟩ : syracuseStep 1992271 = 2988407) B2988407
theorem B1771087 : Blo 1572484 1771087 := bstep (se 1 (by rfl) ⟨1328315, by rfl⟩ : syracuseStep 1771087 = 2656631) B2656631
theorem B1574479 : Blo 1572484 1574479 := bstep (se 1 (by rfl) ⟨1180859, by rfl⟩ : syracuseStep 1574479 = 2361719) B2361719
theorem B24209111 : Blo 1572484 24209111 := bstep (se 1 (by rfl) ⟨18156833, by rfl⟩ : syracuseStep 24209111 = 36313667) B36313667
theorem B12273389 : Blo 1572484 12273389 := bstep (se 3 (by rfl) ⟨2301260, by rfl⟩ : syracuseStep 12273389 = 4602521) B4602521
theorem B5310251 : Blo 1572484 5310251 := bstep (se 1 (by rfl) ⟨3982688, by rfl⟩ : syracuseStep 5310251 = 7965377) B7965377
theorem B3188641 : Blo 1572484 3188641 := bstep (se 2 (by rfl) ⟨1195740, by rfl⟩ : syracuseStep 3188641 = 2391481) B2391481
theorem B2361263 : Blo 1572484 2361263 := bstep (se 1 (by rfl) ⟨1770947, by rfl⟩ : syracuseStep 2361263 = 3541895) B3541895
theorem B3540923 : Blo 1572484 3540923 := bstep (se 1 (by rfl) ⟨2655692, by rfl⟩ : syracuseStep 3540923 = 5311385) B5311385
theorem B2656219 : Blo 1572484 2656219 := bstep (se 1 (by rfl) ⟨1992164, by rfl⟩ : syracuseStep 2656219 = 3984329) B3984329
theorem B2361353 : Blo 1572484 2361353 := bstep (se 2 (by rfl) ⟨885507, by rfl⟩ : syracuseStep 2361353 = 1771015) B1771015
theorem B2361383 : Blo 1572484 2361383 := bstep (se 1 (by rfl) ⟨1771037, by rfl⟩ : syracuseStep 2361383 = 3542075) B3542075
theorem B7964729 : Blo 1572484 7964729 := bstep (se 2 (by rfl) ⟨2986773, by rfl⟩ : syracuseStep 7964729 = 5973547) B5973547
theorem B5310521 : Blo 1572484 5310521 := bstep (se 2 (by rfl) ⟨1991445, by rfl⟩ : syracuseStep 5310521 = 3982891) B3982891
theorem B3541049 : Blo 1572484 3541049 := bstep (se 2 (by rfl) ⟨1327893, by rfl⟩ : syracuseStep 3541049 = 2655787) B2655787
theorem B10078289 : Blo 1572484 10078289 := bstep (se 2 (by rfl) ⟨3779358, by rfl⟩ : syracuseStep 10078289 = 7558717) B7558717
theorem B2361467 : Blo 1572484 2361467 := bstep (se 1 (by rfl) ⟨1771100, by rfl⟩ : syracuseStep 2361467 = 3542201) B3542201
theorem B91998445 : Blo 1572484 91998445 := bstep (se 3 (by rfl) ⟨17249708, by rfl⟩ : syracuseStep 91998445 = 34499417) B34499417
theorem B2361593 : Blo 1572484 2361593 := bstep (se 2 (by rfl) ⟨885597, by rfl⟩ : syracuseStep 2361593 = 1771195) B1771195
theorem B6719831 : Blo 1572484 6719831 := bstep (se 1 (by rfl) ⟨5039873, by rfl⟩ : syracuseStep 6719831 = 10079747) B10079747
theorem B32303447 : Blo 1572484 32303447 := bstep (se 1 (by rfl) ⟨24227585, by rfl⟩ : syracuseStep 32303447 = 48455171) B48455171
theorem B2361695 : Blo 1572484 2361695 := bstep (se 1 (by rfl) ⟨1771271, by rfl⟩ : syracuseStep 2361695 = 3542543) B3542543
theorem B2361707 : Blo 1572484 2361707 := bstep (se 1 (by rfl) ⟨1771280, by rfl⟩ : syracuseStep 2361707 = 3542561) B3542561
theorem B5310845 : Blo 1572484 5310845 := bstep (se 3 (by rfl) ⟨995783, by rfl⟩ : syracuseStep 5310845 = 1991567) B1991567
theorem B3541391 : Blo 1572484 3541391 := bstep (se 1 (by rfl) ⟨2656043, by rfl⟩ : syracuseStep 3541391 = 5312087) B5312087
theorem B5671387 : Blo 1572484 5671387 := bstep (se 1 (by rfl) ⟨4253540, by rfl⟩ : syracuseStep 5671387 = 8507081) B8507081
theorem B2656847 : Blo 1572484 2656847 := bstep (se 1 (by rfl) ⟨1992635, by rfl⟩ : syracuseStep 2656847 = 3985271) B3985271
theorem B5311115 : Blo 1572484 5311115 := bstep (se 1 (by rfl) ⟨3983336, by rfl⟩ : syracuseStep 5311115 = 7966673) B7966673
theorem B3541715 : Blo 1572484 3541715 := bstep (se 1 (by rfl) ⟨2656286, by rfl⟩ : syracuseStep 3541715 = 5312573) B5312573
theorem B12438301 : Blo 1572484 12438301 := bstep (se 3 (by rfl) ⟨2332181, by rfl⟩ : syracuseStep 12438301 = 4664363) B4664363
theorem B5672051 : Blo 1572484 5672051 := bstep (se 1 (by rfl) ⟨4254038, by rfl⟩ : syracuseStep 5672051 = 8508077) B8508077
theorem B25857197 : Blo 1572484 25857197 := bstep (se 3 (by rfl) ⟨4848224, by rfl⟩ : syracuseStep 25857197 = 9696449) B9696449
theorem B12758219 : Blo 1572484 12758219 := bstep (se 1 (by rfl) ⟨9568664, by rfl⟩ : syracuseStep 12758219 = 19137329) B19137329
theorem B17927567 : Blo 1572484 17927567 := bstep (se 1 (by rfl) ⟨13445675, by rfl⟩ : syracuseStep 17927567 = 26891351) B26891351
theorem B11955599 : Blo 1572484 11955599 := bstep (se 1 (by rfl) ⟨8966699, by rfl⟩ : syracuseStep 11955599 = 17933399) B17933399
theorem B2985491 : Blo 1572484 2985491 := bstep (se 1 (by rfl) ⟨2239118, by rfl⟩ : syracuseStep 2985491 = 4478237) B4478237
theorem B5312033 : Blo 1572484 5312033 := bstep (se 2 (by rfl) ⟨1992012, by rfl⟩ : syracuseStep 5312033 = 3984025) B3984025
theorem B4255271 : Blo 1572484 4255271 := bstep (se 1 (by rfl) ⟨3191453, by rfl⟩ : syracuseStep 4255271 = 6382907) B6382907
theorem B8957587 : Blo 1572484 8957587 := bstep (se 1 (by rfl) ⟨6718190, by rfl⟩ : syracuseStep 8957587 = 13436381) B13436381
theorem B4255421 : Blo 1572484 4255421 := bstep (se 3 (by rfl) ⟨797891, by rfl⟩ : syracuseStep 4255421 = 1595783) B1595783
theorem B4918973 : Blo 1572484 4918973 := bstep (se 3 (by rfl) ⟨922307, by rfl⟩ : syracuseStep 4918973 = 1844615) B1844615
theorem B2764535 : Blo 1572484 2764535 := bstep (se 1 (by rfl) ⟨2073401, by rfl⟩ : syracuseStep 2764535 = 4146803) B4146803
theorem B5312249 : Blo 1572484 5312249 := bstep (se 2 (by rfl) ⟨1992093, by rfl⟩ : syracuseStep 5312249 = 3984187) B3984187
theorem B5672771 : Blo 1572484 5672771 := bstep (se 1 (by rfl) ⟨4254578, by rfl⟩ : syracuseStep 5672771 = 8509157) B8509157
theorem B5042027 : Blo 1572484 5042027 := bstep (se 1 (by rfl) ⟨3781520, by rfl⟩ : syracuseStep 5042027 = 7563041) B7563041
theorem B4255595 : Blo 1572484 4255595 := bstep (se 1 (by rfl) ⟨3191696, by rfl⟩ : syracuseStep 4255595 = 6383393) B6383393
theorem B45993845 : Blo 1572484 45993845 := bstep (se 5 (by rfl) ⟨2155961, by rfl⟩ : syracuseStep 45993845 = 4311923) B4311923
theorem B6811553 : Blo 1572484 6811553 := bstep (se 2 (by rfl) ⟨2554332, by rfl⟩ : syracuseStep 6811553 = 5108665) B5108665
theorem B5312519 : Blo 1572484 5312519 := bstep (se 1 (by rfl) ⟨3984389, by rfl⟩ : syracuseStep 5312519 = 7968779) B7968779
theorem B7966835 : Blo 1572484 7966835 := bstep (se 1 (by rfl) ⟨5975126, by rfl⟩ : syracuseStep 7966835 = 11950253) B11950253
theorem B5312627 : Blo 1572484 5312627 := bstep (se 1 (by rfl) ⟨3984470, by rfl⟩ : syracuseStep 5312627 = 7968941) B7968941
theorem B25858277 : Blo 1572484 25858277 := bstep (se 4 (by rfl) ⟨2424213, by rfl⟩ : syracuseStep 25858277 = 4848427) B4848427
theorem B5976449 : Blo 1572484 5976449 := bstep (se 2 (by rfl) ⟨2241168, by rfl⟩ : syracuseStep 5976449 = 4482337) B4482337
theorem B5312897 : Blo 1572484 5312897 := bstep (se 2 (by rfl) ⟨1992336, by rfl⟩ : syracuseStep 5312897 = 3984673) B3984673
theorem B5747087 : Blo 1572484 5747087 := bstep (se 1 (by rfl) ⟨4310315, by rfl⟩ : syracuseStep 5747087 = 8620631) B8620631
theorem B5976463 : Blo 1572484 5976463 := bstep (se 1 (by rfl) ⟨4482347, by rfl⟩ : syracuseStep 5976463 = 8964695) B8964695
theorem B2519591 : Blo 1572484 2519591 := bstep (se 1 (by rfl) ⟨1889693, by rfl⟩ : syracuseStep 2519591 = 3779387) B3779387
theorem B3068513 : Blo 1572484 3068513 := bstep (se 2 (by rfl) ⟨1150692, by rfl⟩ : syracuseStep 3068513 = 2301385) B2301385
theorem B2519675 : Blo 1572484 2519675 := bstep (se 1 (by rfl) ⟨1889756, by rfl⟩ : syracuseStep 2519675 = 3779513) B3779513
theorem B5042873 : Blo 1572484 5042873 := bstep (se 2 (by rfl) ⟨1891077, by rfl⟩ : syracuseStep 5042873 = 3782155) B3782155
theorem B2986895 : Blo 1572484 2986895 := bstep (se 1 (by rfl) ⟨2240171, by rfl⟩ : syracuseStep 2986895 = 4480343) B4480343
theorem B51041177 : Blo 1572484 51041177 := bstep (se 2 (by rfl) ⟨19140441, by rfl⟩ : syracuseStep 51041177 = 38280883) B38280883
theorem B3781559 : Blo 1572484 3781559 := bstep (se 1 (by rfl) ⟨2836169, by rfl⟩ : syracuseStep 3781559 = 5672339) B5672339
theorem B20165597 : Blo 1572484 20165597 := bstep (se 3 (by rfl) ⟨3781049, by rfl⟩ : syracuseStep 20165597 = 7562099) B7562099
theorem B12760037 : Blo 1572484 12760037 := bstep (se 4 (by rfl) ⟨1196253, by rfl⟩ : syracuseStep 12760037 = 2392507) B2392507
theorem B2987047 : Blo 1572484 2987047 := bstep (se 1 (by rfl) ⟨2240285, by rfl⟩ : syracuseStep 2987047 = 4480571) B4480571
theorem B17019953 : Blo 1572484 17019953 := bstep (se 2 (by rfl) ⟨6382482, by rfl⟩ : syracuseStep 17019953 = 12764965) B12764965
theorem B2987131 : Blo 1572484 2987131 := bstep (se 1 (by rfl) ⟨2240348, by rfl⟩ : syracuseStep 2987131 = 4480697) B4480697
theorem B36353195 : Blo 1572484 36353195 := bstep (se 1 (by rfl) ⟨27264896, by rfl⟩ : syracuseStep 36353195 = 54529793) B54529793
theorem B5313707 : Blo 1572484 5313707 := bstep (se 1 (by rfl) ⟨3985280, by rfl⟩ : syracuseStep 5313707 = 7970561) B7970561
theorem B1594567 : Blo 1572484 1594567 := bstep (se 1 (by rfl) ⟨1195925, by rfl⟩ : syracuseStep 1594567 = 2391851) B2391851
theorem B6722959 : Blo 1572484 6722959 := bstep (se 1 (by rfl) ⟨5042219, by rfl⟩ : syracuseStep 6722959 = 10084439) B10084439
theorem B2553383 : Blo 1572484 2553383 := bstep (se 1 (by rfl) ⟨1915037, by rfl⟩ : syracuseStep 2553383 = 3830075) B3830075
theorem B2987617 : Blo 1572484 2987617 := bstep (se 2 (by rfl) ⟨1120356, by rfl⟩ : syracuseStep 2987617 = 2240713) B2240713
theorem B5977739 : Blo 1572484 5977739 := bstep (se 1 (by rfl) ⟨4483304, by rfl⟩ : syracuseStep 5977739 = 8966609) B8966609
theorem B17921735 : Blo 1572484 17921735 := bstep (se 1 (by rfl) ⟨13441301, by rfl⟩ : syracuseStep 17921735 = 26882603) B26882603
theorem B11949767 : Blo 1572484 11949767 := bstep (se 1 (by rfl) ⟨8962325, by rfl⟩ : syracuseStep 11949767 = 17924651) B17924651
theorem B7968455 : Blo 1572484 7968455 := bstep (se 1 (by rfl) ⟨5976341, by rfl⟩ : syracuseStep 7968455 = 11952683) B11952683
theorem B1595099 : Blo 1572484 1595099 := bstep (se 1 (by rfl) ⟨1196324, by rfl⟩ : syracuseStep 1595099 = 2392649) B2392649
theorem B1890155 : Blo 1572484 1890155 := bstep (se 1 (by rfl) ⟨1417616, by rfl⟩ : syracuseStep 1890155 = 2835233) B2835233
theorem B9566113 : Blo 1572484 9566113 := bstep (se 2 (by rfl) ⟨3587292, by rfl⟩ : syracuseStep 9566113 = 7174585) B7174585
theorem B3782713 : Blo 1572484 3782713 := bstep (se 2 (by rfl) ⟨1418517, by rfl⟩ : syracuseStep 3782713 = 2837035) B2837035
theorem B57443377 : Blo 1572484 57443377 := bstep (se 2 (by rfl) ⟨21541266, by rfl⟩ : syracuseStep 57443377 = 43082533) B43082533
theorem B2988551 : Blo 1572484 2988551 := bstep (se 1 (by rfl) ⟨2241413, by rfl⟩ : syracuseStep 2988551 = 4482827) B4482827
theorem B5970617 : Blo 1572484 5970617 := bstep (se 2 (by rfl) ⟨2238981, by rfl⟩ : syracuseStep 5970617 = 4477963) B4477963
theorem B5970631 : Blo 1572484 5970631 := bstep (se 1 (by rfl) ⟨4477973, by rfl⟩ : syracuseStep 5970631 = 8955947) B8955947
theorem B2521847 : Blo 1572484 2521847 := bstep (se 1 (by rfl) ⟨1891385, by rfl⟩ : syracuseStep 2521847 = 3782771) B3782771
theorem B5110715 : Blo 1572484 5110715 := bstep (se 1 (by rfl) ⟨3833036, by rfl⟩ : syracuseStep 5110715 = 7666073) B7666073
theorem B7961651 : Blo 1572484 7961651 := bstep (se 1 (by rfl) ⟨5971238, by rfl⟩ : syracuseStep 7961651 = 11942477) B11942477
theorem B11942963 : Blo 1572484 11942963 := bstep (se 1 (by rfl) ⟨8957222, by rfl⟩ : syracuseStep 11942963 = 17914445) B17914445
theorem B1574319 : Blo 1572484 1574319 := bstep (se 1 (by rfl) ⟨1180739, by rfl⟩ : syracuseStep 1574319 = 2361479) B2361479
theorem B5307659 : Blo 1572484 5307659 := bstep (se 1 (by rfl) ⟨3980744, by rfl⟩ : syracuseStep 5307659 = 7961489) B7961489
theorem B24214909 : Blo 1572484 24214909 := bstep (se 3 (by rfl) ⟨4540295, by rfl⟩ : syracuseStep 24214909 = 9080591) B9080591
theorem B2653627 : Blo 1572484 2653627 := bstep (se 1 (by rfl) ⟨1990220, by rfl⟩ : syracuseStep 2653627 = 3980441) B3980441
theorem B3587593 : Blo 1572484 3587593 := bstep (se 2 (by rfl) ⟨1345347, by rfl⟩ : syracuseStep 3587593 = 2690695) B2690695
theorem B5307929 : Blo 1572484 5307929 := bstep (se 2 (by rfl) ⟨1990473, by rfl⟩ : syracuseStep 5307929 = 3980947) B3980947
theorem B2653735 : Blo 1572484 2653735 := bstep (se 1 (by rfl) ⟨1990301, by rfl⟩ : syracuseStep 2653735 = 3980603) B3980603
theorem B2358863 : Blo 1572484 2358863 := bstep (se 1 (by rfl) ⟨1769147, by rfl⟩ : syracuseStep 2358863 = 3538295) B3538295
theorem B3538529 : Blo 1572484 3538529 := bstep (se 2 (by rfl) ⟨1326948, by rfl⟩ : syracuseStep 3538529 = 2653897) B2653897
theorem B3980897 : Blo 1572484 3980897 := bstep (se 2 (by rfl) ⟨1492836, by rfl⟩ : syracuseStep 3980897 = 2985673) B2985673
theorem B3407483 : Blo 1572484 3407483 := bstep (se 1 (by rfl) ⟨2555612, by rfl⟩ : syracuseStep 3407483 = 5111225) B5111225
theorem B5971603 : Blo 1572484 5971603 := bstep (se 1 (by rfl) ⟨4478702, by rfl⟩ : syracuseStep 5971603 = 8957405) B8957405
theorem B1572527 : Blo 1572484 1572527 := bstep (se 1 (by rfl) ⟨1179395, by rfl⟩ : syracuseStep 1572527 = 2358791) B2358791
theorem B1572551 : Blo 1572484 1572551 := bstep (se 1 (by rfl) ⟨1179413, by rfl⟩ : syracuseStep 1572551 = 2358827) B2358827
theorem B2358983 : Blo 1572484 2358983 := bstep (se 1 (by rfl) ⟨1769237, by rfl⟩ : syracuseStep 2358983 = 3538475) B3538475
theorem B1572571 : Blo 1572484 1572571 := bstep (se 1 (by rfl) ⟨1179428, by rfl⟩ : syracuseStep 1572571 = 2358857) B2358857
theorem B13434605 : Blo 1572484 13434605 := bstep (se 3 (by rfl) ⟨2518988, by rfl⟩ : syracuseStep 13434605 = 5037977) B5037977
theorem B1572647 : Blo 1572484 1572647 := bstep (se 1 (by rfl) ⟨1179485, by rfl⟩ : syracuseStep 1572647 = 2358971) B2358971
theorem B1572687 : Blo 1572484 1572687 := bstep (se 1 (by rfl) ⟨1179515, by rfl⟩ : syracuseStep 1572687 = 2359031) B2359031
theorem B4251487 : Blo 1572484 4251487 := bstep (se 1 (by rfl) ⟨3188615, by rfl⟩ : syracuseStep 4251487 = 6377231) B6377231
theorem B1572703 : Blo 1572484 1572703 := bstep (se 1 (by rfl) ⟨1179527, by rfl⟩ : syracuseStep 1572703 = 2359055) B2359055
theorem B2359145 : Blo 1572484 2359145 := bstep (se 2 (by rfl) ⟨884679, by rfl⟩ : syracuseStep 2359145 = 1769359) B1769359
theorem B2654059 : Blo 1572484 2654059 := bstep (se 1 (by rfl) ⟨1990544, by rfl⟩ : syracuseStep 2654059 = 3981089) B3981089
theorem B21520247 : Blo 1572484 21520247 := bstep (se 1 (by rfl) ⟨16140185, by rfl⟩ : syracuseStep 21520247 = 32280371) B32280371
theorem B1572731 : Blo 1572484 1572731 := bstep (se 1 (by rfl) ⟨1179548, by rfl⟩ : syracuseStep 1572731 = 2359097) B2359097
theorem B1572783 : Blo 1572484 1572783 := bstep (se 1 (by rfl) ⟨1179587, by rfl⟩ : syracuseStep 1572783 = 2359175) B2359175
theorem B2359223 : Blo 1572484 2359223 := bstep (se 1 (by rfl) ⟨1769417, by rfl⟩ : syracuseStep 2359223 = 3538835) B3538835
theorem B3538871 : Blo 1572484 3538871 := bstep (se 1 (by rfl) ⟨2654153, by rfl⟩ : syracuseStep 3538871 = 5308307) B5308307
theorem B30646201 : Blo 1572484 30646201 := bstep (se 2 (by rfl) ⟨11492325, by rfl⟩ : syracuseStep 30646201 = 22984651) B22984651
theorem B1572807 : Blo 1572484 1572807 := bstep (se 1 (by rfl) ⟨1179605, by rfl⟩ : syracuseStep 1572807 = 2359211) B2359211
theorem B1572827 : Blo 1572484 1572827 := bstep (se 1 (by rfl) ⟨1179620, by rfl⟩ : syracuseStep 1572827 = 2359241) B2359241
theorem B2359259 : Blo 1572484 2359259 := bstep (se 1 (by rfl) ⟨1769444, by rfl⟩ : syracuseStep 2359259 = 3538889) B3538889
theorem B1573151 : Blo 1572484 1573151 := bstep (se 1 (by rfl) ⟨1179863, by rfl⟩ : syracuseStep 1573151 = 2359727) B2359727
theorem B2359643 : Blo 1572484 2359643 := bstep (se 1 (by rfl) ⟨1769732, by rfl⟩ : syracuseStep 2359643 = 3539465) B3539465
theorem B1573211 : Blo 1572484 1573211 := bstep (se 1 (by rfl) ⟨1179908, by rfl⟩ : syracuseStep 1573211 = 2359817) B2359817
theorem B1573231 : Blo 1572484 1573231 := bstep (se 1 (by rfl) ⟨1179923, by rfl⟩ : syracuseStep 1573231 = 2359847) B2359847
theorem B1679783 : Blo 1572484 1679783 := bstep (se 1 (by rfl) ⟨1259837, by rfl⟩ : syracuseStep 1679783 = 2519675) B2519675
theorem B5308847 : Blo 1572484 5308847 := bstep (se 1 (by rfl) ⟨3981635, by rfl⟩ : syracuseStep 5308847 = 7963271) B7963271
theorem B3539375 : Blo 1572484 3539375 := bstep (se 1 (by rfl) ⟨2654531, by rfl⟩ : syracuseStep 3539375 = 5309063) B5309063
theorem B3539411 : Blo 1572484 3539411 := bstep (se 1 (by rfl) ⟨2654558, by rfl⟩ : syracuseStep 3539411 = 5309117) B5309117
theorem B1573371 : Blo 1572484 1573371 := bstep (se 1 (by rfl) ⟨1180028, by rfl⟩ : syracuseStep 1573371 = 2360057) B2360057
theorem B3539519 : Blo 1572484 3539519 := bstep (se 1 (by rfl) ⟨2654639, by rfl⟩ : syracuseStep 3539519 = 5309279) B5309279
theorem B2359871 : Blo 1572484 2359871 := bstep (se 1 (by rfl) ⟨1769903, by rfl⟩ : syracuseStep 2359871 = 3539807) B3539807
theorem B1573439 : Blo 1572484 1573439 := bstep (se 1 (by rfl) ⟨1180079, by rfl⟩ : syracuseStep 1573439 = 2360159) B2360159
theorem B1573447 : Blo 1572484 1573447 := bstep (se 1 (by rfl) ⟨1180085, by rfl⟩ : syracuseStep 1573447 = 2360171) B2360171
theorem B1770079 : Blo 1572484 1770079 := bstep (se 1 (by rfl) ⟨1327559, by rfl⟩ : syracuseStep 1770079 = 2655119) B2655119
theorem B7561849 : Blo 1572484 7561849 := bstep (se 2 (by rfl) ⟨2835693, by rfl⟩ : syracuseStep 7561849 = 5671387) B5671387
theorem B13443731 : Blo 1572484 13443731 := bstep (se 1 (by rfl) ⟨10082798, by rfl⟩ : syracuseStep 13443731 = 20165597) B20165597
theorem B3539627 : Blo 1572484 3539627 := bstep (se 1 (by rfl) ⟨2654720, by rfl⟩ : syracuseStep 3539627 = 5309441) B5309441
theorem B2654903 : Blo 1572484 2654903 := bstep (se 1 (by rfl) ⟨1991177, by rfl⟩ : syracuseStep 2654903 = 3982355) B3982355
theorem B2359991 : Blo 1572484 2359991 := bstep (se 1 (by rfl) ⟨1769993, by rfl⟩ : syracuseStep 2359991 = 3539987) B3539987
theorem B11346635 : Blo 1572484 11346635 := bstep (se 1 (by rfl) ⟨8509976, by rfl⟩ : syracuseStep 11346635 = 17019953) B17019953
theorem B1573599 : Blo 1572484 1573599 := bstep (se 1 (by rfl) ⟨1180199, by rfl⟩ : syracuseStep 1573599 = 2360399) B2360399
theorem B1573679 : Blo 1572484 1573679 := bstep (se 1 (by rfl) ⟨1180259, by rfl⟩ : syracuseStep 1573679 = 2360519) B2360519
theorem B3588943 : Blo 1572484 3588943 := bstep (se 1 (by rfl) ⟨2691707, by rfl⟩ : syracuseStep 3588943 = 5383415) B5383415
theorem B3982223 : Blo 1572484 3982223 := bstep (se 1 (by rfl) ⟨2986667, by rfl⟩ : syracuseStep 3982223 = 5973335) B5973335
theorem B2360219 : Blo 1572484 2360219 := bstep (se 1 (by rfl) ⟨1770164, by rfl⟩ : syracuseStep 2360219 = 3540329) B3540329
theorem B1573787 : Blo 1572484 1573787 := bstep (se 1 (by rfl) ⟨1180340, by rfl⟩ : syracuseStep 1573787 = 2360681) B2360681
theorem B1573839 : Blo 1572484 1573839 := bstep (se 1 (by rfl) ⟨1180379, by rfl⟩ : syracuseStep 1573839 = 2360759) B2360759
theorem B1573863 : Blo 1572484 1573863 := bstep (se 1 (by rfl) ⟨1180397, by rfl⟩ : syracuseStep 1573863 = 2360795) B2360795
theorem B16139407 : Blo 1572484 16139407 := bstep (se 1 (by rfl) ⟨12104555, by rfl⟩ : syracuseStep 16139407 = 24209111) B24209111
theorem B3540167 : Blo 1572484 3540167 := bstep (se 1 (by rfl) ⟨2655125, by rfl⟩ : syracuseStep 3540167 = 5310251) B5310251
theorem B1574175 : Blo 1572484 1574175 := bstep (se 1 (by rfl) ⟨1180631, by rfl⟩ : syracuseStep 1574175 = 2361263) B2361263
theorem B2360615 : Blo 1572484 2360615 := bstep (se 1 (by rfl) ⟨1770461, by rfl⟩ : syracuseStep 2360615 = 3540923) B3540923
theorem B1574235 : Blo 1572484 1574235 := bstep (se 1 (by rfl) ⟨1180676, by rfl⟩ : syracuseStep 1574235 = 2361353) B2361353
theorem B1574255 : Blo 1572484 1574255 := bstep (se 1 (by rfl) ⟨1180691, by rfl⟩ : syracuseStep 1574255 = 2361383) B2361383
theorem B5309819 : Blo 1572484 5309819 := bstep (se 1 (by rfl) ⟨3982364, by rfl⟩ : syracuseStep 5309819 = 7964729) B7964729
theorem B3540347 : Blo 1572484 3540347 := bstep (se 1 (by rfl) ⟨2655260, by rfl⟩ : syracuseStep 3540347 = 5310521) B5310521
theorem B2360699 : Blo 1572484 2360699 := bstep (se 1 (by rfl) ⟨1770524, by rfl⟩ : syracuseStep 2360699 = 3541049) B3541049
theorem B3982729 : Blo 1572484 3982729 := bstep (se 2 (by rfl) ⟨1493523, by rfl⟩ : syracuseStep 3982729 = 2987047) B2987047
theorem B2655625 : Blo 1572484 2655625 := bstep (se 2 (by rfl) ⟨995859, by rfl⟩ : syracuseStep 2655625 = 1991719) B1991719
theorem B6718859 : Blo 1572484 6718859 := bstep (se 1 (by rfl) ⟨5039144, by rfl⟩ : syracuseStep 6718859 = 10078289) B10078289
theorem B1574311 : Blo 1572484 1574311 := bstep (se 1 (by rfl) ⟨1180733, by rfl⟩ : syracuseStep 1574311 = 2361467) B2361467
theorem B6809021 : Blo 1572484 6809021 := bstep (se 3 (by rfl) ⟨1276691, by rfl⟩ : syracuseStep 6809021 = 2553383) B2553383
theorem B6718909 : Blo 1572484 6718909 := bstep (se 3 (by rfl) ⟨1259795, by rfl⟩ : syracuseStep 6718909 = 2519591) B2519591
theorem B6055357 : Blo 1572484 6055357 := bstep (se 3 (by rfl) ⟨1135379, by rfl⟩ : syracuseStep 6055357 = 2270759) B2270759
theorem B25519549 : Blo 1572484 25519549 := bstep (se 3 (by rfl) ⟨4784915, by rfl⟩ : syracuseStep 25519549 = 9569831) B9569831
theorem B3982841 : Blo 1572484 3982841 := bstep (se 2 (by rfl) ⟨1493565, by rfl⟩ : syracuseStep 3982841 = 2987131) B2987131
theorem B3540473 : Blo 1572484 3540473 := bstep (se 2 (by rfl) ⟨1327677, by rfl⟩ : syracuseStep 3540473 = 2655355) B2655355
theorem B2360825 : Blo 1572484 2360825 := bstep (se 2 (by rfl) ⟨885309, by rfl⟩ : syracuseStep 2360825 = 1770619) B1770619
theorem B1574395 : Blo 1572484 1574395 := bstep (se 1 (by rfl) ⟨1180796, by rfl⟩ : syracuseStep 1574395 = 2361593) B2361593
theorem B1574463 : Blo 1572484 1574463 := bstep (se 1 (by rfl) ⟨1180847, by rfl⟩ : syracuseStep 1574463 = 2361695) B2361695
theorem B1574471 : Blo 1572484 1574471 := bstep (se 1 (by rfl) ⟨1180853, by rfl⟩ : syracuseStep 1574471 = 2361707) B2361707
theorem B3540563 : Blo 1572484 3540563 := bstep (se 1 (by rfl) ⟨2655422, by rfl⟩ : syracuseStep 3540563 = 5310845) B5310845
theorem B2360927 : Blo 1572484 2360927 := bstep (se 1 (by rfl) ⟨1770695, by rfl⟩ : syracuseStep 2360927 = 3541391) B3541391
theorem B1992367 : Blo 1572484 1992367 := bstep (se 1 (by rfl) ⟨1494275, by rfl⟩ : syracuseStep 1992367 = 2988551) B2988551
theorem B1771231 : Blo 1572484 1771231 := bstep (se 1 (by rfl) ⟨1328423, by rfl⟩ : syracuseStep 1771231 = 2656847) B2656847
theorem B3540743 : Blo 1572484 3540743 := bstep (se 1 (by rfl) ⟨2655557, by rfl⟩ : syracuseStep 3540743 = 5311115) B5311115
theorem B2361143 : Blo 1572484 2361143 := bstep (se 1 (by rfl) ⟨1770857, by rfl⟩ : syracuseStep 2361143 = 3541715) B3541715
theorem B2656057 : Blo 1572484 2656057 := bstep (se 2 (by rfl) ⟨996021, by rfl⟩ : syracuseStep 2656057 = 1992043) B1992043
theorem B11347789 : Blo 1572484 11347789 := bstep (se 3 (by rfl) ⟨2127710, by rfl⟩ : syracuseStep 11347789 = 4255421) B4255421
theorem B13117261 : Blo 1572484 13117261 := bstep (se 3 (by rfl) ⟨2459486, by rfl⟩ : syracuseStep 13117261 = 4918973) B4918973
theorem B32286545 : Blo 1572484 32286545 := bstep (se 2 (by rfl) ⟨12107454, by rfl⟩ : syracuseStep 32286545 = 24214909) B24214909
theorem B1681231 : Blo 1572484 1681231 := bstep (se 1 (by rfl) ⟨1260923, by rfl⟩ : syracuseStep 1681231 = 2521847) B2521847
theorem B8963945 : Blo 1572484 8963945 := bstep (se 2 (by rfl) ⟨3361479, by rfl⟩ : syracuseStep 8963945 = 6722959) B6722959
theorem B4253597 : Blo 1572484 4253597 := bstep (se 3 (by rfl) ⟨797549, by rfl⟩ : syracuseStep 4253597 = 1595099) B1595099
theorem B1573287 : Blo 1572484 1573287 := bstep (se 1 (by rfl) ⟨1179965, by rfl⟩ : syracuseStep 1573287 = 2359931) B2359931
theorem B2656361 : Blo 1572484 2656361 := bstep (se 2 (by rfl) ⟨996135, by rfl⟩ : syracuseStep 2656361 = 1992271) B1992271
theorem B2361449 : Blo 1572484 2361449 := bstep (se 2 (by rfl) ⟨885543, by rfl⟩ : syracuseStep 2361449 = 1771087) B1771087
theorem B17238131 : Blo 1572484 17238131 := bstep (se 1 (by rfl) ⟨12928598, by rfl⟩ : syracuseStep 17238131 = 25857197) B25857197
theorem B3983489 : Blo 1572484 3983489 := bstep (se 2 (by rfl) ⟨1493808, by rfl⟩ : syracuseStep 3983489 = 2987617) B2987617
theorem B8505479 : Blo 1572484 8505479 := bstep (se 1 (by rfl) ⟨6379109, by rfl⟩ : syracuseStep 8505479 = 12758219) B12758219
theorem B5040413 : Blo 1572484 5040413 := bstep (se 3 (by rfl) ⟨945077, by rfl⟩ : syracuseStep 5040413 = 1890155) B1890155
theorem B57387325 : Blo 1572484 57387325 := bstep (se 3 (by rfl) ⟨10760123, by rfl⟩ : syracuseStep 57387325 = 21520247) B21520247
theorem B3541355 : Blo 1572484 3541355 := bstep (se 1 (by rfl) ⟨2656016, by rfl⟩ : syracuseStep 3541355 = 5312033) B5312033
theorem B2836847 : Blo 1572484 2836847 := bstep (se 1 (by rfl) ⟨2127635, by rfl⟩ : syracuseStep 2836847 = 4255271) B4255271
theorem B7965053 : Blo 1572484 7965053 := bstep (se 3 (by rfl) ⟨1493447, by rfl⟩ : syracuseStep 7965053 = 2986895) B2986895
theorem B2271655 : Blo 1572484 2271655 := bstep (se 1 (by rfl) ⟨1703741, by rfl⟩ : syracuseStep 2271655 = 3407483) B3407483
theorem B8956403 : Blo 1572484 8956403 := bstep (se 1 (by rfl) ⟨6717302, by rfl⟩ : syracuseStep 8956403 = 13434605) B13434605
theorem B3541499 : Blo 1572484 3541499 := bstep (se 1 (by rfl) ⟨2656124, by rfl⟩ : syracuseStep 3541499 = 5312249) B5312249
theorem B3361351 : Blo 1572484 3361351 := bstep (se 1 (by rfl) ⟨2521013, by rfl⟩ : syracuseStep 3361351 = 5042027) B5042027
theorem B2837063 : Blo 1572484 2837063 := bstep (se 1 (by rfl) ⟨2127797, by rfl⟩ : syracuseStep 2837063 = 4255595) B4255595
theorem B4541035 : Blo 1572484 4541035 := bstep (se 1 (by rfl) ⟨3405776, by rfl⟩ : syracuseStep 4541035 = 6811553) B6811553
theorem B3541625 : Blo 1572484 3541625 := bstep (se 2 (by rfl) ⟨1328109, by rfl⟩ : syracuseStep 3541625 = 2656219) B2656219
theorem B3541679 : Blo 1572484 3541679 := bstep (se 1 (by rfl) ⟨2656259, by rfl⟩ : syracuseStep 3541679 = 5312519) B5312519
theorem B5311223 : Blo 1572484 5311223 := bstep (se 1 (by rfl) ⟨3983417, by rfl⟩ : syracuseStep 5311223 = 7966835) B7966835
theorem B3541751 : Blo 1572484 3541751 := bstep (se 1 (by rfl) ⟨2656313, by rfl⟩ : syracuseStep 3541751 = 5312627) B5312627
theorem B17238851 : Blo 1572484 17238851 := bstep (se 1 (by rfl) ⟨12929138, by rfl⟩ : syracuseStep 17238851 = 25858277) B25858277
theorem B3984299 : Blo 1572484 3984299 := bstep (se 1 (by rfl) ⟨2988224, by rfl⟩ : syracuseStep 3984299 = 5976449) B5976449
theorem B3541931 : Blo 1572484 3541931 := bstep (se 1 (by rfl) ⟨2656448, by rfl⟩ : syracuseStep 3541931 = 5312897) B5312897
theorem B3361915 : Blo 1572484 3361915 := bstep (se 1 (by rfl) ⟨2521436, by rfl⟩ : syracuseStep 3361915 = 5042873) B5042873
theorem B8506691 : Blo 1572484 8506691 := bstep (se 1 (by rfl) ⟨6380018, by rfl⟩ : syracuseStep 8506691 = 12760037) B12760037
theorem B4255163 : Blo 1572484 4255163 := bstep (se 1 (by rfl) ⟨3191372, by rfl⟩ : syracuseStep 4255163 = 6382745) B6382745
theorem B24235463 : Blo 1572484 24235463 := bstep (se 1 (by rfl) ⟨18176597, by rfl⟩ : syracuseStep 24235463 = 36353195) B36353195
theorem B3542471 : Blo 1572484 3542471 := bstep (se 1 (by rfl) ⟨2656853, by rfl⟩ : syracuseStep 3542471 = 5313707) B5313707
theorem B16584401 : Blo 1572484 16584401 := bstep (se 2 (by rfl) ⟨6219150, by rfl⟩ : syracuseStep 16584401 = 12438301) B12438301
theorem B3985159 : Blo 1572484 3985159 := bstep (se 1 (by rfl) ⟨2988869, by rfl⟩ : syracuseStep 3985159 = 5977739) B5977739
theorem B11947823 : Blo 1572484 11947823 := bstep (se 1 (by rfl) ⟨8960867, by rfl⟩ : syracuseStep 11947823 = 17921735) B17921735
theorem B7966511 : Blo 1572484 7966511 := bstep (se 1 (by rfl) ⟨5974883, by rfl⟩ : syracuseStep 7966511 = 11949767) B11949767
theorem B5312303 : Blo 1572484 5312303 := bstep (se 1 (by rfl) ⟨3984227, by rfl⟩ : syracuseStep 5312303 = 7968455) B7968455
theorem B15544321 : Blo 1572484 15544321 := bstep (se 2 (by rfl) ⟨5829120, by rfl⟩ : syracuseStep 15544321 = 11658241) B11658241
theorem B76591169 : Blo 1572484 76591169 := bstep (se 2 (by rfl) ⟨28721688, by rfl⟩ : syracuseStep 76591169 = 57443377) B57443377
theorem B2126089 : Blo 1572484 2126089 := bstep (se 2 (by rfl) ⟨797283, by rfl⟩ : syracuseStep 2126089 = 1594567) B1594567
theorem B3781367 : Blo 1572484 3781367 := bstep (se 1 (by rfl) ⟨2836025, by rfl⟩ : syracuseStep 3781367 = 5672051) B5672051
theorem B13628573 : Blo 1572484 13628573 := bstep (se 3 (by rfl) ⟨2555357, by rfl⟩ : syracuseStep 13628573 = 5110715) B5110715
theorem B3781847 : Blo 1572484 3781847 := bstep (se 1 (by rfl) ⟨2836385, by rfl⟩ : syracuseStep 3781847 = 5672771) B5672771
theorem B7558505 : Blo 1572484 7558505 := bstep (se 2 (by rfl) ⟨2834439, by rfl⟩ : syracuseStep 7558505 = 5668879) B5668879
theorem B5043617 : Blo 1572484 5043617 := bstep (se 2 (by rfl) ⟨1891356, by rfl⟩ : syracuseStep 5043617 = 3782713) B3782713
theorem B3831391 : Blo 1572484 3831391 := bstep (se 1 (by rfl) ⟨2873543, by rfl⟩ : syracuseStep 3831391 = 5747087) B5747087
theorem B122664593 : Blo 1572484 122664593 := bstep (se 2 (by rfl) ⟨45999222, by rfl⟩ : syracuseStep 122664593 = 91998445) B91998445
theorem B22697657 : Blo 1572484 22697657 := bstep (se 2 (by rfl) ⟨8511621, by rfl⟩ : syracuseStep 22697657 = 17023243) B17023243
theorem B10081979 : Blo 1572484 10081979 := bstep (se 1 (by rfl) ⟨7561484, by rfl⟩ : syracuseStep 10081979 = 15122969) B15122969
theorem B2045675 : Blo 1572484 2045675 := bstep (se 1 (by rfl) ⟨1534256, by rfl⟩ : syracuseStep 2045675 = 3068513) B3068513
theorem B7968617 : Blo 1572484 7968617 := bstep (se 2 (by rfl) ⟨2988231, by rfl⟩ : syracuseStep 7968617 = 5976463) B5976463
theorem B34027451 : Blo 1572484 34027451 := bstep (se 1 (by rfl) ⟨25520588, by rfl⟩ : syracuseStep 34027451 = 51041177) B51041177
theorem B2521039 : Blo 1572484 2521039 := bstep (se 1 (by rfl) ⟨1890779, by rfl⟩ : syracuseStep 2521039 = 3781559) B3781559
theorem B1021138973 : Blo 1572484 1021138973 := bstep (se 3 (by rfl) ⟨191463557, by rfl⟩ : syracuseStep 1021138973 = 382927115) B382927115
theorem B7960841 : Blo 1572484 7960841 := bstep (se 2 (by rfl) ⟨2985315, by rfl⟩ : syracuseStep 7960841 = 5970631) B5970631
theorem B8182259 : Blo 1572484 8182259 := bstep (se 1 (by rfl) ⟨6136694, by rfl⟩ : syracuseStep 8182259 = 12273389) B12273389
theorem B4479887 : Blo 1572484 4479887 := bstep (se 1 (by rfl) ⟨3359915, by rfl⟩ : syracuseStep 4479887 = 6719831) B6719831
theorem B21535631 : Blo 1572484 21535631 := bstep (se 1 (by rfl) ⟨16151723, by rfl⟩ : syracuseStep 21535631 = 32303447) B32303447
theorem B13622201 : Blo 1572484 13622201 := bstep (se 2 (by rfl) ⟨5108325, by rfl⟩ : syracuseStep 13622201 = 10216651) B10216651
theorem B3980411 : Blo 1572484 3980411 := bstep (se 1 (by rfl) ⟨2985308, by rfl⟩ : syracuseStep 3980411 = 5970617) B5970617
theorem B3538169 : Blo 1572484 3538169 := bstep (se 2 (by rfl) ⟨1326813, by rfl⟩ : syracuseStep 3538169 = 2653627) B2653627
theorem B7372093 : Blo 1572484 7372093 := bstep (se 3 (by rfl) ⟨1382267, by rfl⟩ : syracuseStep 7372093 = 2764535) B2764535
theorem B4783457 : Blo 1572484 4783457 := bstep (se 2 (by rfl) ⟨1793796, by rfl⟩ : syracuseStep 4783457 = 3587593) B3587593
theorem B5307767 : Blo 1572484 5307767 := bstep (se 1 (by rfl) ⟨3980825, by rfl⟩ : syracuseStep 5307767 = 7961651) B7961651
theorem B7961975 : Blo 1572484 7961975 := bstep (se 1 (by rfl) ⟨5971481, by rfl⟩ : syracuseStep 7961975 = 11942963) B11942963
theorem B3538313 : Blo 1572484 3538313 := bstep (se 2 (by rfl) ⟨1326867, by rfl⟩ : syracuseStep 3538313 = 2653735) B2653735
theorem B3538439 : Blo 1572484 3538439 := bstep (se 1 (by rfl) ⟨2653829, by rfl⟩ : syracuseStep 3538439 = 5307659) B5307659
theorem B7962137 : Blo 1572484 7962137 := bstep (se 2 (by rfl) ⟨2985801, by rfl⟩ : syracuseStep 7962137 = 5971603) B5971603
theorem B11943449 : Blo 1572484 11943449 := bstep (se 2 (by rfl) ⟨4478793, by rfl⟩ : syracuseStep 11943449 = 8957587) B8957587
theorem B11951711 : Blo 1572484 11951711 := bstep (se 1 (by rfl) ⟨8963783, by rfl⟩ : syracuseStep 11951711 = 17927567) B17927567
theorem B7970399 : Blo 1572484 7970399 := bstep (se 1 (by rfl) ⟨5977799, by rfl⟩ : syracuseStep 7970399 = 11955599) B11955599
theorem B122650253 : Blo 1572484 122650253 := bstep (se 3 (by rfl) ⟨22996922, by rfl⟩ : syracuseStep 122650253 = 45993845) B45993845
theorem B1990327 : Blo 1572484 1990327 := bstep (se 1 (by rfl) ⟨1492745, by rfl⟩ : syracuseStep 1990327 = 2985491) B2985491
theorem B3538619 : Blo 1572484 3538619 := bstep (se 1 (by rfl) ⟨2653964, by rfl⟩ : syracuseStep 3538619 = 5307929) B5307929
theorem B1572575 : Blo 1572484 1572575 := bstep (se 1 (by rfl) ⟨1179431, by rfl⟩ : syracuseStep 1572575 = 2358863) B2358863
theorem B2359019 : Blo 1572484 2359019 := bstep (se 1 (by rfl) ⟨1769264, by rfl⟩ : syracuseStep 2359019 = 3538529) B3538529
theorem B2653931 : Blo 1572484 2653931 := bstep (se 1 (by rfl) ⟨1990448, by rfl⟩ : syracuseStep 2653931 = 3980897) B3980897
theorem B5668649 : Blo 1572484 5668649 := bstep (se 2 (by rfl) ⟨2125743, by rfl⟩ : syracuseStep 5668649 = 4251487) B4251487
theorem B1572655 : Blo 1572484 1572655 := bstep (se 1 (by rfl) ⟨1179491, by rfl⟩ : syracuseStep 1572655 = 2358983) B2358983
theorem B3538745 : Blo 1572484 3538745 := bstep (se 2 (by rfl) ⟨1327029, by rfl⟩ : syracuseStep 3538745 = 2654059) B2654059
theorem B4251521 : Blo 1572484 4251521 := bstep (se 2 (by rfl) ⟨1594320, by rfl⟩ : syracuseStep 4251521 = 3188641) B3188641
theorem B12754817 : Blo 1572484 12754817 := bstep (se 2 (by rfl) ⟨4783056, by rfl⟩ : syracuseStep 12754817 = 9566113) B9566113
theorem B1572763 : Blo 1572484 1572763 := bstep (se 1 (by rfl) ⟨1179572, by rfl⟩ : syracuseStep 1572763 = 2359145) B2359145
theorem B40861601 : Blo 1572484 40861601 := bstep (se 2 (by rfl) ⟨15323100, by rfl⟩ : syracuseStep 40861601 = 30646201) B30646201
theorem B1572815 : Blo 1572484 1572815 := bstep (se 1 (by rfl) ⟨1179611, by rfl⟩ : syracuseStep 1572815 = 2359223) B2359223
theorem B2359247 : Blo 1572484 2359247 := bstep (se 1 (by rfl) ⟨1769435, by rfl⟩ : syracuseStep 2359247 = 3538871) B3538871
theorem B1572839 : Blo 1572484 1572839 := bstep (se 1 (by rfl) ⟨1179629, by rfl⟩ : syracuseStep 1572839 = 2359259) B2359259
theorem B82903045 : Blo 1572484 82903045 := bstep (se 4 (by rfl) ⟨7772160, by rfl⟩ : syracuseStep 82903045 = 15544321) B15544321
theorem B51060779 : Blo 1572484 51060779 := bstep (se 1 (by rfl) ⟨38295584, by rfl⟩ : syracuseStep 51060779 = 76591169) B76591169
theorem B1573095 : Blo 1572484 1573095 := bstep (se 1 (by rfl) ⟨1179821, by rfl⟩ : syracuseStep 1573095 = 2359643) B2359643
theorem B3539231 : Blo 1572484 3539231 := bstep (se 1 (by rfl) ⟨2654423, by rfl⟩ : syracuseStep 3539231 = 5308847) B5308847
theorem B2359583 : Blo 1572484 2359583 := bstep (se 1 (by rfl) ⟨1769687, by rfl⟩ : syracuseStep 2359583 = 3539375) B3539375
theorem B2359607 : Blo 1572484 2359607 := bstep (se 1 (by rfl) ⟨1769705, by rfl⟩ : syracuseStep 2359607 = 3539411) B3539411
theorem B2834785 : Blo 1572484 2834785 := bstep (se 2 (by rfl) ⟨1063044, by rfl⟩ : syracuseStep 2834785 = 2126089) B2126089
theorem B2359679 : Blo 1572484 2359679 := bstep (se 1 (by rfl) ⟨1769759, by rfl⟩ : syracuseStep 2359679 = 3539519) B3539519
theorem B1573247 : Blo 1572484 1573247 := bstep (se 1 (by rfl) ⟨1179935, by rfl⟩ : syracuseStep 1573247 = 2359871) B2359871
theorem B8962487 : Blo 1572484 8962487 := bstep (se 1 (by rfl) ⟨6721865, by rfl⟩ : syracuseStep 8962487 = 13443731) B13443731
theorem B2359751 : Blo 1572484 2359751 := bstep (se 1 (by rfl) ⟨1769813, by rfl⟩ : syracuseStep 2359751 = 3539627) B3539627
theorem B1769935 : Blo 1572484 1769935 := bstep (se 1 (by rfl) ⟨1327451, by rfl⟩ : syracuseStep 1769935 = 2654903) B2654903
theorem B1573327 : Blo 1572484 1573327 := bstep (se 1 (by rfl) ⟨1179995, by rfl⟩ : syracuseStep 1573327 = 2359991) B2359991
theorem B10084925 : Blo 1572484 10084925 := bstep (se 3 (by rfl) ⟨1890923, by rfl⟩ : syracuseStep 10084925 = 3781847) B3781847
theorem B2654815 : Blo 1572484 2654815 := bstep (se 1 (by rfl) ⟨1991111, by rfl⟩ : syracuseStep 2654815 = 3982223) B3982223
theorem B1573479 : Blo 1572484 1573479 := bstep (se 1 (by rfl) ⟨1180109, by rfl⟩ : syracuseStep 1573479 = 2360219) B2360219
theorem B4481801 : Blo 1572484 4481801 := bstep (se 2 (by rfl) ⟨1680675, by rfl⟩ : syracuseStep 4481801 = 3361351) B3361351
theorem B9085715 : Blo 1572484 9085715 := bstep (se 1 (by rfl) ⟨6814286, by rfl⟩ : syracuseStep 9085715 = 13628573) B13628573
theorem B2360105 : Blo 1572484 2360105 := bstep (se 2 (by rfl) ⟨885039, by rfl⟩ : syracuseStep 2360105 = 1770079) B1770079
theorem B2360111 : Blo 1572484 2360111 := bstep (se 1 (by rfl) ⟨1770083, by rfl⟩ : syracuseStep 2360111 = 3540167) B3540167
theorem B6054713 : Blo 1572484 6054713 := bstep (se 2 (by rfl) ⟨2270517, by rfl⟩ : syracuseStep 6054713 = 4541035) B4541035
theorem B1573743 : Blo 1572484 1573743 := bstep (se 1 (by rfl) ⟨1180307, by rfl⟩ : syracuseStep 1573743 = 2360615) B2360615
theorem B5039003 : Blo 1572484 5039003 := bstep (se 1 (by rfl) ⟨3779252, by rfl⟩ : syracuseStep 5039003 = 7558505) B7558505
theorem B3539879 : Blo 1572484 3539879 := bstep (se 1 (by rfl) ⟨2654909, by rfl⟩ : syracuseStep 3539879 = 5309819) B5309819
theorem B2360231 : Blo 1572484 2360231 := bstep (se 1 (by rfl) ⟨1770173, by rfl⟩ : syracuseStep 2360231 = 3540347) B3540347
theorem B1573799 : Blo 1572484 1573799 := bstep (se 1 (by rfl) ⟨1180349, by rfl⟩ : syracuseStep 1573799 = 2360699) B2360699
theorem B4539347 : Blo 1572484 4539347 := bstep (se 1 (by rfl) ⟨3404510, by rfl⟩ : syracuseStep 4539347 = 6809021) B6809021
theorem B2655227 : Blo 1572484 2655227 := bstep (se 1 (by rfl) ⟨1991420, by rfl⟩ : syracuseStep 2655227 = 3982841) B3982841
theorem B2360315 : Blo 1572484 2360315 := bstep (se 1 (by rfl) ⟨1770236, by rfl⟩ : syracuseStep 2360315 = 3540473) B3540473
theorem B1573883 : Blo 1572484 1573883 := bstep (se 1 (by rfl) ⟨1180412, by rfl⟩ : syracuseStep 1573883 = 2360825) B2360825
theorem B2360375 : Blo 1572484 2360375 := bstep (se 1 (by rfl) ⟨1770281, by rfl⟩ : syracuseStep 2360375 = 3540563) B3540563
theorem B1573951 : Blo 1572484 1573951 := bstep (se 1 (by rfl) ⟨1180463, by rfl⟩ : syracuseStep 1573951 = 2360927) B2360927
theorem B4785257 : Blo 1572484 4785257 := bstep (se 2 (by rfl) ⟨1794471, by rfl⟩ : syracuseStep 4785257 = 3588943) B3588943
theorem B15131771 : Blo 1572484 15131771 := bstep (se 1 (by rfl) ⟨11348828, by rfl⟩ : syracuseStep 15131771 = 22697657) B22697657
theorem B2360495 : Blo 1572484 2360495 := bstep (se 1 (by rfl) ⟨1770371, by rfl⟩ : syracuseStep 2360495 = 3540743) B3540743
theorem B64627901 : Blo 1572484 64627901 := bstep (se 3 (by rfl) ⟨12117731, by rfl⟩ : syracuseStep 64627901 = 24235463) B24235463
theorem B1574095 : Blo 1572484 1574095 := bstep (se 1 (by rfl) ⟨1180571, by rfl⟩ : syracuseStep 1574095 = 2361143) B2361143
theorem B2835731 : Blo 1572484 2835731 := bstep (se 1 (by rfl) ⟨2126798, by rfl⟩ : syracuseStep 2835731 = 4253597) B4253597
theorem B22684967 : Blo 1572484 22684967 := bstep (se 1 (by rfl) ⟨17013725, by rfl⟩ : syracuseStep 22684967 = 34027451) B34027451
theorem B1770907 : Blo 1572484 1770907 := bstep (se 1 (by rfl) ⟨1328180, by rfl⟩ : syracuseStep 1770907 = 2656361) B2656361
theorem B1574299 : Blo 1572484 1574299 := bstep (se 1 (by rfl) ⟨1180724, by rfl⟩ : syracuseStep 1574299 = 2361449) B2361449
theorem B2655659 : Blo 1572484 2655659 := bstep (se 1 (by rfl) ⟨1991744, by rfl⟩ : syracuseStep 2655659 = 3983489) B3983489
theorem B5670319 : Blo 1572484 5670319 := bstep (se 1 (by rfl) ⟨4252739, by rfl⟩ : syracuseStep 5670319 = 8505479) B8505479
theorem B4482553 : Blo 1572484 4482553 := bstep (se 2 (by rfl) ⟨1680957, by rfl⟩ : syracuseStep 4482553 = 3361915) B3361915
theorem B3360275 : Blo 1572484 3360275 := bstep (se 1 (by rfl) ⟨2520206, by rfl⟩ : syracuseStep 3360275 = 5040413) B5040413
theorem B2360903 : Blo 1572484 2360903 := bstep (se 1 (by rfl) ⟨1770677, by rfl⟩ : syracuseStep 2360903 = 3541355) B3541355
theorem B5310035 : Blo 1572484 5310035 := bstep (se 1 (by rfl) ⟨3982526, by rfl⟩ : syracuseStep 5310035 = 7965053) B7965053
theorem B2360999 : Blo 1572484 2360999 := bstep (se 1 (by rfl) ⟨1770749, by rfl⟩ : syracuseStep 2360999 = 3541499) B3541499
theorem B2361083 : Blo 1572484 2361083 := bstep (se 1 (by rfl) ⟨1770812, by rfl⟩ : syracuseStep 2361083 = 3541625) B3541625
theorem B2361119 : Blo 1572484 2361119 := bstep (se 1 (by rfl) ⟨1770839, by rfl⟩ : syracuseStep 2361119 = 3541679) B3541679
theorem B3540815 : Blo 1572484 3540815 := bstep (se 1 (by rfl) ⟨2655611, by rfl⟩ : syracuseStep 3540815 = 5311223) B5311223
theorem B2361167 : Blo 1572484 2361167 := bstep (se 1 (by rfl) ⟨1770875, by rfl⟩ : syracuseStep 2361167 = 3541751) B3541751
theorem B5310305 : Blo 1572484 5310305 := bstep (se 2 (by rfl) ⟨1991364, by rfl⟩ : syracuseStep 5310305 = 3982729) B3982729
theorem B3540833 : Blo 1572484 3540833 := bstep (se 2 (by rfl) ⟨1327812, by rfl⟩ : syracuseStep 3540833 = 2655625) B2655625
theorem B2656199 : Blo 1572484 2656199 := bstep (se 1 (by rfl) ⟨1992149, by rfl⟩ : syracuseStep 2656199 = 3984299) B3984299
theorem B2361287 : Blo 1572484 2361287 := bstep (se 1 (by rfl) ⟨1770965, by rfl⟩ : syracuseStep 2361287 = 3541931) B3541931
theorem B5671127 : Blo 1572484 5671127 := bstep (se 1 (by rfl) ⟨4253345, by rfl⟩ : syracuseStep 5671127 = 8506691) B8506691
theorem B2656489 : Blo 1572484 2656489 := bstep (se 2 (by rfl) ⟨996183, by rfl⟩ : syracuseStep 2656489 = 1992367) B1992367
theorem B3188971 : Blo 1572484 3188971 := bstep (se 1 (by rfl) ⟨2391728, by rfl⟩ : syracuseStep 3188971 = 4783457) B4783457
theorem B2836775 : Blo 1572484 2836775 := bstep (se 1 (by rfl) ⟨2127581, by rfl⟩ : syracuseStep 2836775 = 4255163) B4255163
theorem B2361641 : Blo 1572484 2361641 := bstep (se 2 (by rfl) ⟨885615, by rfl⟩ : syracuseStep 2361641 = 1771231) B1771231
theorem B2361647 : Blo 1572484 2361647 := bstep (se 1 (by rfl) ⟨1771235, by rfl⟩ : syracuseStep 2361647 = 3542471) B3542471
theorem B11946365 : Blo 1572484 11946365 := bstep (se 3 (by rfl) ⟨2239943, by rfl⟩ : syracuseStep 11946365 = 4479887) B4479887
theorem B3541409 : Blo 1572484 3541409 := bstep (se 2 (by rfl) ⟨1328028, by rfl⟩ : syracuseStep 3541409 = 2656057) B2656057
theorem B81766835 : Blo 1572484 81766835 := bstep (se 1 (by rfl) ⟨61325126, by rfl⟩ : syracuseStep 81766835 = 122650253) B122650253
theorem B3779099 : Blo 1572484 3779099 := bstep (se 1 (by rfl) ⟨2834324, by rfl⟩ : syracuseStep 3779099 = 5668649) B5668649
theorem B7965215 : Blo 1572484 7965215 := bstep (se 1 (by rfl) ⟨5973911, by rfl⟩ : syracuseStep 7965215 = 11947823) B11947823
theorem B5311007 : Blo 1572484 5311007 := bstep (se 1 (by rfl) ⟨3983255, by rfl⟩ : syracuseStep 5311007 = 7966511) B7966511
theorem B3541535 : Blo 1572484 3541535 := bstep (se 1 (by rfl) ⟨2656151, by rfl⟩ : syracuseStep 3541535 = 5312303) B5312303
theorem B3361385 : Blo 1572484 3361385 := bstep (se 2 (by rfl) ⟨1260519, by rfl⟩ : syracuseStep 3361385 = 2521039) B2521039
theorem B27241067 : Blo 1572484 27241067 := bstep (se 1 (by rfl) ⟨20430800, by rfl⟩ : syracuseStep 27241067 = 40861601) B40861601
theorem B76516433 : Blo 1572484 76516433 := bstep (se 2 (by rfl) ⟨28693662, by rfl⟩ : syracuseStep 76516433 = 57387325) B57387325
theorem B7564423 : Blo 1572484 7564423 := bstep (se 1 (by rfl) ⟨5673317, by rfl⟩ : syracuseStep 7564423 = 11346635) B11346635
theorem B3362411 : Blo 1572484 3362411 := bstep (se 1 (by rfl) ⟨2521808, by rfl⟩ : syracuseStep 3362411 = 5043617) B5043617
theorem B81776395 : Blo 1572484 81776395 := bstep (se 1 (by rfl) ⟨61332296, by rfl⟩ : syracuseStep 81776395 = 122664593) B122664593
theorem B6721319 : Blo 1572484 6721319 := bstep (se 1 (by rfl) ⟨5040989, by rfl⟩ : syracuseStep 6721319 = 10081979) B10081979
theorem B183873397 : Blo 1572484 183873397 := bstep (se 5 (by rfl) ⟨8619065, by rfl⟩ : syracuseStep 183873397 = 17238131) B17238131
theorem B21524363 : Blo 1572484 21524363 := bstep (se 1 (by rfl) ⟨16143272, by rfl⟩ : syracuseStep 21524363 = 32286545) B32286545
theorem B5975963 : Blo 1572484 5975963 := bstep (se 1 (by rfl) ⟨4481972, by rfl⟩ : syracuseStep 5975963 = 8963945) B8963945
theorem B5312411 : Blo 1572484 5312411 := bstep (se 1 (by rfl) ⟨3984308, by rfl⟩ : syracuseStep 5312411 = 7968617) B7968617
theorem B680759315 : Blo 1572484 680759315 := bstep (se 1 (by rfl) ⟨510569486, by rfl⟩ : syracuseStep 680759315 = 1021138973) B1021138973
theorem B7565501 : Blo 1572484 7565501 := bstep (se 3 (by rfl) ⟨1418531, by rfl⟩ : syracuseStep 7565501 = 2837063) B2837063
theorem B8958545 : Blo 1572484 8958545 := bstep (se 2 (by rfl) ⟨3359454, by rfl⟩ : syracuseStep 8958545 = 6718909) B6718909
theorem B8073809 : Blo 1572484 8073809 := bstep (se 2 (by rfl) ⟨3027678, by rfl⟩ : syracuseStep 8073809 = 6055357) B6055357
theorem B34026065 : Blo 1572484 34026065 := bstep (se 2 (by rfl) ⟨12759774, by rfl⟩ : syracuseStep 34026065 = 25519549) B25519549
theorem B14357087 : Blo 1572484 14357087 := bstep (se 1 (by rfl) ⟨10767815, by rfl⟩ : syracuseStep 14357087 = 21535631) B21535631
theorem B9081467 : Blo 1572484 9081467 := bstep (se 1 (by rfl) ⟨6811100, by rfl⟩ : syracuseStep 9081467 = 13622201) B13622201
theorem B5108521 : Blo 1572484 5108521 := bstep (se 2 (by rfl) ⟨1915695, by rfl⟩ : syracuseStep 5108521 = 3831391) B3831391
theorem B5313545 : Blo 1572484 5313545 := bstep (se 2 (by rfl) ⟨1992579, by rfl⟩ : syracuseStep 5313545 = 3985159) B3985159
theorem B7967807 : Blo 1572484 7967807 := bstep (se 1 (by rfl) ⟨5975855, by rfl⟩ : syracuseStep 7967807 = 11951711) B11951711
theorem B5313599 : Blo 1572484 5313599 := bstep (se 1 (by rfl) ⟨3985199, by rfl⟩ : syracuseStep 5313599 = 7970399) B7970399
theorem B2241641 : Blo 1572484 2241641 := bstep (se 2 (by rfl) ⟨840615, by rfl⟩ : syracuseStep 2241641 = 1681231) B1681231
theorem B11056267 : Blo 1572484 11056267 := bstep (se 1 (by rfl) ⟨8292200, by rfl⟩ : syracuseStep 11056267 = 16584401) B16584401
theorem B2520911 : Blo 1572484 2520911 := bstep (se 1 (by rfl) ⟨1890683, by rfl⟩ : syracuseStep 2520911 = 3781367) B3781367
theorem B10082465 : Blo 1572484 10082465 := bstep (se 2 (by rfl) ⟨3780924, by rfl⟩ : syracuseStep 10082465 = 7561849) B7561849
theorem B4479239 : Blo 1572484 4479239 := bstep (se 1 (by rfl) ⟨3359429, by rfl⟩ : syracuseStep 4479239 = 6718859) B6718859
theorem B4479421 : Blo 1572484 4479421 := bstep (se 3 (by rfl) ⟨839891, by rfl⟩ : syracuseStep 4479421 = 1679783) B1679783
theorem B5307227 : Blo 1572484 5307227 := bstep (se 1 (by rfl) ⟨3980420, by rfl⟩ : syracuseStep 5307227 = 7960841) B7960841
theorem B21519209 : Blo 1572484 21519209 := bstep (se 2 (by rfl) ⟨8069703, by rfl⟩ : syracuseStep 21519209 = 16139407) B16139407
theorem B1891231 : Blo 1572484 1891231 := bstep (se 1 (by rfl) ⟨1418423, by rfl⟩ : syracuseStep 1891231 = 2836847) B2836847
theorem B5970935 : Blo 1572484 5970935 := bstep (se 1 (by rfl) ⟨4478201, by rfl⟩ : syracuseStep 5970935 = 8956403) B8956403
theorem B5454839 : Blo 1572484 5454839 := bstep (se 1 (by rfl) ⟨4091129, by rfl⟩ : syracuseStep 5454839 = 8182259) B8182259
theorem B9829457 : Blo 1572484 9829457 := bstep (se 2 (by rfl) ⟨3686046, by rfl⟩ : syracuseStep 9829457 = 7372093) B7372093
theorem B11492567 : Blo 1572484 11492567 := bstep (se 1 (by rfl) ⟨8619425, by rfl⟩ : syracuseStep 11492567 = 17238851) B17238851
theorem B5455133 : Blo 1572484 5455133 := bstep (se 3 (by rfl) ⟨1022837, by rfl⟩ : syracuseStep 5455133 = 2045675) B2045675
theorem B2653607 : Blo 1572484 2653607 := bstep (se 1 (by rfl) ⟨1990205, by rfl⟩ : syracuseStep 2653607 = 3980411) B3980411
theorem B2358779 : Blo 1572484 2358779 := bstep (se 1 (by rfl) ⟨1769084, by rfl⟩ : syracuseStep 2358779 = 3538169) B3538169
theorem B12115493 : Blo 1572484 12115493 := bstep (se 4 (by rfl) ⟨1135827, by rfl⟩ : syracuseStep 12115493 = 2271655) B2271655
theorem B2653769 : Blo 1572484 2653769 := bstep (se 2 (by rfl) ⟨995163, by rfl⟩ : syracuseStep 2653769 = 1990327) B1990327
theorem B3538511 : Blo 1572484 3538511 := bstep (se 1 (by rfl) ⟨2653883, by rfl⟩ : syracuseStep 3538511 = 5307767) B5307767
theorem B5307983 : Blo 1572484 5307983 := bstep (se 1 (by rfl) ⟨3980987, by rfl⟩ : syracuseStep 5307983 = 7961975) B7961975
theorem B2358875 : Blo 1572484 2358875 := bstep (se 1 (by rfl) ⟨1769156, by rfl⟩ : syracuseStep 2358875 = 3538313) B3538313
theorem B2358959 : Blo 1572484 2358959 := bstep (se 1 (by rfl) ⟨1769219, by rfl⟩ : syracuseStep 2358959 = 3538439) B3538439
theorem B5308091 : Blo 1572484 5308091 := bstep (se 1 (by rfl) ⟨3981068, by rfl⟩ : syracuseStep 5308091 = 7962137) B7962137
theorem B7962299 : Blo 1572484 7962299 := bstep (se 1 (by rfl) ⟨5971724, by rfl⟩ : syracuseStep 7962299 = 11943449) B11943449
theorem B15130385 : Blo 1572484 15130385 := bstep (se 2 (by rfl) ⟨5673894, by rfl⟩ : syracuseStep 15130385 = 11347789) B11347789
theorem B17489681 : Blo 1572484 17489681 := bstep (se 2 (by rfl) ⟨6558630, by rfl⟩ : syracuseStep 17489681 = 13117261) B13117261
theorem B2359079 : Blo 1572484 2359079 := bstep (se 1 (by rfl) ⟨1769309, by rfl⟩ : syracuseStep 2359079 = 3538619) B3538619
theorem B1572679 : Blo 1572484 1572679 := bstep (se 1 (by rfl) ⟨1179509, by rfl⟩ : syracuseStep 1572679 = 2359019) B2359019
theorem B1769287 : Blo 1572484 1769287 := bstep (se 1 (by rfl) ⟨1326965, by rfl⟩ : syracuseStep 1769287 = 2653931) B2653931
theorem B2359163 : Blo 1572484 2359163 := bstep (se 1 (by rfl) ⟨1769372, by rfl⟩ : syracuseStep 2359163 = 3538745) B3538745
theorem B2834347 : Blo 1572484 2834347 := bstep (se 1 (by rfl) ⟨2125760, by rfl⟩ : syracuseStep 2834347 = 4251521) B4251521
theorem B8503211 : Blo 1572484 8503211 := bstep (se 1 (by rfl) ⟨6377408, by rfl⟩ : syracuseStep 8503211 = 12754817) B12754817
theorem B1572831 : Blo 1572484 1572831 := bstep (se 1 (by rfl) ⟨1179623, by rfl⟩ : syracuseStep 1572831 = 2359247) B2359247
theorem B2359487 : Blo 1572484 2359487 := bstep (se 1 (by rfl) ⟨1769615, by rfl⟩ : syracuseStep 2359487 = 3539231) B3539231
theorem B1573055 : Blo 1572484 1573055 := bstep (se 1 (by rfl) ⟨1179791, by rfl⟩ : syracuseStep 1573055 = 2359583) B2359583
theorem B1573071 : Blo 1572484 1573071 := bstep (se 1 (by rfl) ⟨1179803, by rfl⟩ : syracuseStep 1573071 = 2359607) B2359607
theorem B1573119 : Blo 1572484 1573119 := bstep (se 1 (by rfl) ⟨1179839, by rfl⟩ : syracuseStep 1573119 = 2359679) B2359679
theorem B1573167 : Blo 1572484 1573167 := bstep (se 1 (by rfl) ⟨1179875, by rfl⟩ : syracuseStep 1573167 = 2359751) B2359751
theorem B4251961 : Blo 1572484 4251961 := bstep (se 2 (by rfl) ⟨1594485, by rfl⟩ : syracuseStep 4251961 = 3188971) B3188971
theorem B5972363 : Blo 1572484 5972363 := bstep (se 1 (by rfl) ⟨4479272, by rfl⟩ : syracuseStep 5972363 = 8958545) B8958545
theorem B5382539 : Blo 1572484 5382539 := bstep (se 1 (by rfl) ⟨4036904, by rfl⟩ : syracuseStep 5382539 = 8073809) B8073809
theorem B6054311 : Blo 1572484 6054311 := bstep (se 1 (by rfl) ⟨4540733, by rfl⟩ : syracuseStep 6054311 = 9081467) B9081467
theorem B1573403 : Blo 1572484 1573403 := bstep (se 1 (by rfl) ⟨1180052, by rfl⟩ : syracuseStep 1573403 = 2360105) B2360105
theorem B1573407 : Blo 1572484 1573407 := bstep (se 1 (by rfl) ⟨1180055, by rfl⟩ : syracuseStep 1573407 = 2360111) B2360111
theorem B5972561 : Blo 1572484 5972561 := bstep (se 2 (by rfl) ⟨2239710, by rfl⟩ : syracuseStep 5972561 = 4479421) B4479421
theorem B3359335 : Blo 1572484 3359335 := bstep (se 1 (by rfl) ⟨2519501, by rfl⟩ : syracuseStep 3359335 = 5039003) B5039003
theorem B2359913 : Blo 1572484 2359913 := bstep (se 2 (by rfl) ⟨884967, by rfl⟩ : syracuseStep 2359913 = 1769935) B1769935
theorem B2359919 : Blo 1572484 2359919 := bstep (se 1 (by rfl) ⟨1769939, by rfl⟩ : syracuseStep 2359919 = 3539879) B3539879
theorem B1573487 : Blo 1572484 1573487 := bstep (se 1 (by rfl) ⟨1180115, by rfl⟩ : syracuseStep 1573487 = 2360231) B2360231
theorem B1770151 : Blo 1572484 1770151 := bstep (se 1 (by rfl) ⟨1327613, by rfl⟩ : syracuseStep 1770151 = 2655227) B2655227
theorem B1573543 : Blo 1572484 1573543 := bstep (se 1 (by rfl) ⟨1180157, by rfl⟩ : syracuseStep 1573543 = 2360315) B2360315
theorem B1573583 : Blo 1572484 1573583 := bstep (se 1 (by rfl) ⟨1180187, by rfl⟩ : syracuseStep 1573583 = 2360375) B2360375
theorem B1573663 : Blo 1572484 1573663 := bstep (se 1 (by rfl) ⟨1180247, by rfl⟩ : syracuseStep 1573663 = 2360495) B2360495
theorem B3539753 : Blo 1572484 3539753 := bstep (se 2 (by rfl) ⟨1327407, by rfl⟩ : syracuseStep 3539753 = 2654815) B2654815
theorem B15123311 : Blo 1572484 15123311 := bstep (se 1 (by rfl) ⟨11342483, by rfl⟩ : syracuseStep 15123311 = 22684967) B22684967
theorem B1770439 : Blo 1572484 1770439 := bstep (se 1 (by rfl) ⟨1327829, by rfl⟩ : syracuseStep 1770439 = 2655659) B2655659
theorem B1573935 : Blo 1572484 1573935 := bstep (se 1 (by rfl) ⟨1180451, by rfl⟩ : syracuseStep 1573935 = 2360903) B2360903
theorem B3540023 : Blo 1572484 3540023 := bstep (se 1 (by rfl) ⟨2655017, by rfl⟩ : syracuseStep 3540023 = 5310035) B5310035
theorem B1573999 : Blo 1572484 1573999 := bstep (se 1 (by rfl) ⟨1180499, by rfl⟩ : syracuseStep 1573999 = 2360999) B2360999
theorem B1574055 : Blo 1572484 1574055 := bstep (se 1 (by rfl) ⟨1180541, by rfl⟩ : syracuseStep 1574055 = 2361083) B2361083
theorem B1574079 : Blo 1572484 1574079 := bstep (se 1 (by rfl) ⟨1180559, by rfl⟩ : syracuseStep 1574079 = 2361119) B2361119
theorem B2360543 : Blo 1572484 2360543 := bstep (se 1 (by rfl) ⟨1770407, by rfl⟩ : syracuseStep 2360543 = 3540815) B3540815
theorem B1680607 : Blo 1572484 1680607 := bstep (se 1 (by rfl) ⟨1260455, by rfl⟩ : syracuseStep 1680607 = 2520911) B2520911
theorem B1574111 : Blo 1572484 1574111 := bstep (se 1 (by rfl) ⟨1180583, by rfl⟩ : syracuseStep 1574111 = 2361167) B2361167
theorem B3540203 : Blo 1572484 3540203 := bstep (se 1 (by rfl) ⟨2655152, by rfl⟩ : syracuseStep 3540203 = 5310305) B5310305
theorem B2360555 : Blo 1572484 2360555 := bstep (se 1 (by rfl) ⟨1770416, by rfl⟩ : syracuseStep 2360555 = 3540833) B3540833
theorem B1770799 : Blo 1572484 1770799 := bstep (se 1 (by rfl) ⟨1328099, by rfl⟩ : syracuseStep 1770799 = 2656199) B2656199
theorem B1574191 : Blo 1572484 1574191 := bstep (se 1 (by rfl) ⟨1180643, by rfl⟩ : syracuseStep 1574191 = 2361287) B2361287
theorem B10085897 : Blo 1572484 10085897 := bstep (se 2 (by rfl) ⟨3782211, by rfl⟩ : syracuseStep 10085897 = 7564423) B7564423
theorem B1574427 : Blo 1572484 1574427 := bstep (se 1 (by rfl) ⟨1180820, by rfl⟩ : syracuseStep 1574427 = 2361641) B2361641
theorem B1574431 : Blo 1572484 1574431 := bstep (se 1 (by rfl) ⟨1180823, by rfl⟩ : syracuseStep 1574431 = 2361647) B2361647
theorem B7964243 : Blo 1572484 7964243 := bstep (se 1 (by rfl) ⟨5973182, by rfl⟩ : syracuseStep 7964243 = 11946365) B11946365
theorem B2360939 : Blo 1572484 2360939 := bstep (se 1 (by rfl) ⟨1770704, by rfl⟩ : syracuseStep 2360939 = 3541409) B3541409
theorem B8963693 : Blo 1572484 8963693 := bstep (se 3 (by rfl) ⟨1680692, by rfl⟩ : syracuseStep 8963693 = 3361385) B3361385
theorem B54511223 : Blo 1572484 54511223 := bstep (se 1 (by rfl) ⟨40883417, by rfl⟩ : syracuseStep 54511223 = 81766835) B81766835
theorem B5310143 : Blo 1572484 5310143 := bstep (se 1 (by rfl) ⟨3982607, by rfl⟩ : syracuseStep 5310143 = 7965215) B7965215
theorem B3540671 : Blo 1572484 3540671 := bstep (se 1 (by rfl) ⟨2655503, by rfl⟩ : syracuseStep 3540671 = 5311007) B5311007
theorem B2361023 : Blo 1572484 2361023 := bstep (se 1 (by rfl) ⟨1770767, by rfl⟩ : syracuseStep 2361023 = 3541535) B3541535
theorem B2361209 : Blo 1572484 2361209 := bstep (se 2 (by rfl) ⟨885453, by rfl⟩ : syracuseStep 2361209 = 1770907) B1770907
theorem B7661711 : Blo 1572484 7661711 := bstep (se 1 (by rfl) ⟨5746283, by rfl⟩ : syracuseStep 7661711 = 11492567) B11492567
theorem B10086565 : Blo 1572484 10086565 := bstep (se 4 (by rfl) ⟨945615, by rfl⟩ : syracuseStep 10086565 = 1891231) B1891231
theorem B245164529 : Blo 1572484 245164529 := bstep (se 2 (by rfl) ⟨91936698, by rfl⟩ : syracuseStep 245164529 = 183873397) B183873397
theorem B10086923 : Blo 1572484 10086923 := bstep (se 1 (by rfl) ⟨7565192, by rfl⟩ : syracuseStep 10086923 = 15130385) B15130385
theorem B11659787 : Blo 1572484 11659787 := bstep (se 1 (by rfl) ⟨8744840, by rfl⟩ : syracuseStep 11659787 = 17489681) B17489681
theorem B3779129 : Blo 1572484 3779129 := bstep (se 2 (by rfl) ⟨1417173, by rfl⟩ : syracuseStep 3779129 = 2834347) B2834347
theorem B3983975 : Blo 1572484 3983975 := bstep (se 1 (by rfl) ⟨2987981, by rfl⟩ : syracuseStep 3983975 = 5975963) B5975963
theorem B3541607 : Blo 1572484 3541607 := bstep (se 1 (by rfl) ⟨2656205, by rfl⟩ : syracuseStep 3541607 = 5312411) B5312411
theorem B110537393 : Blo 1572484 110537393 := bstep (se 2 (by rfl) ⟨41451522, by rfl⟩ : syracuseStep 110537393 = 82903045) B82903045
theorem B453839543 : Blo 1572484 453839543 := bstep (se 1 (by rfl) ⟨340379657, by rfl⟩ : syracuseStep 453839543 = 680759315) B680759315
theorem B34040519 : Blo 1572484 34040519 := bstep (se 1 (by rfl) ⟨25530389, by rfl⟩ : syracuseStep 34040519 = 51060779) B51060779
theorem B5974991 : Blo 1572484 5974991 := bstep (se 1 (by rfl) ⟨4481243, by rfl⟩ : syracuseStep 5974991 = 8962487) B8962487
theorem B3541985 : Blo 1572484 3541985 := bstep (se 2 (by rfl) ⟨1328244, by rfl⟩ : syracuseStep 3541985 = 2656489) B2656489
theorem B9571391 : Blo 1572484 9571391 := bstep (se 1 (by rfl) ⟨7178543, by rfl⟩ : syracuseStep 9571391 = 14357087) B14357087
theorem B3779713 : Blo 1572484 3779713 := bstep (se 2 (by rfl) ⟨1417392, by rfl⟩ : syracuseStep 3779713 = 2834785) B2834785
theorem B6057143 : Blo 1572484 6057143 := bstep (se 1 (by rfl) ⟨4542857, by rfl⟩ : syracuseStep 6057143 = 9085715) B9085715
theorem B3026231 : Blo 1572484 3026231 := bstep (se 1 (by rfl) ⟨2269673, by rfl⟩ : syracuseStep 3026231 = 4539347) B4539347
theorem B3542363 : Blo 1572484 3542363 := bstep (se 1 (by rfl) ⟨2656772, by rfl⟩ : syracuseStep 3542363 = 5313545) B5313545
theorem B5311871 : Blo 1572484 5311871 := bstep (se 1 (by rfl) ⟨3983903, by rfl⟩ : syracuseStep 5311871 = 7967807) B7967807
theorem B3542399 : Blo 1572484 3542399 := bstep (se 1 (by rfl) ⟨2656799, by rfl⟩ : syracuseStep 3542399 = 5313599) B5313599
theorem B10087847 : Blo 1572484 10087847 := bstep (se 1 (by rfl) ⟨7565885, by rfl⟩ : syracuseStep 10087847 = 15131771) B15131771
theorem B43085267 : Blo 1572484 43085267 := bstep (se 1 (by rfl) ⟨32313950, by rfl⟩ : syracuseStep 43085267 = 64627901) B64627901
theorem B2240183 : Blo 1572484 2240183 := bstep (se 1 (by rfl) ⟨1680137, by rfl⟩ : syracuseStep 2240183 = 3360275) B3360275
theorem B6811361 : Blo 1572484 6811361 := bstep (se 2 (by rfl) ⟨2554260, by rfl⟩ : syracuseStep 6811361 = 5108521) B5108521
theorem B6721643 : Blo 1572484 6721643 := bstep (se 1 (by rfl) ⟨5041232, by rfl⟩ : syracuseStep 6721643 = 10082465) B10082465
theorem B3780751 : Blo 1572484 3780751 := bstep (se 1 (by rfl) ⟨2835563, by rfl⟩ : syracuseStep 3780751 = 5671127) B5671127
theorem B2986159 : Blo 1572484 2986159 := bstep (se 1 (by rfl) ⟨2239619, by rfl⟩ : syracuseStep 2986159 = 4479239) B4479239
theorem B14741689 : Blo 1572484 14741689 := bstep (se 2 (by rfl) ⟨5528133, by rfl⟩ : syracuseStep 14741689 = 11056267) B11056267
theorem B72642845 : Blo 1572484 72642845 := bstep (se 3 (by rfl) ⟨13620533, by rfl⟩ : syracuseStep 72642845 = 27241067) B27241067
theorem B2519399 : Blo 1572484 2519399 := bstep (se 1 (by rfl) ⟨1889549, by rfl⟩ : syracuseStep 2519399 = 3779099) B3779099
theorem B5976737 : Blo 1572484 5976737 := bstep (se 2 (by rfl) ⟨2241276, by rfl⟩ : syracuseStep 5976737 = 4482553) B4482553
theorem B2241607 : Blo 1572484 2241607 := bstep (se 1 (by rfl) ⟨1681205, by rfl⟩ : syracuseStep 2241607 = 3362411) B3362411
theorem B14349575 : Blo 1572484 14349575 := bstep (se 1 (by rfl) ⟨10762181, by rfl⟩ : syracuseStep 14349575 = 21524363) B21524363
theorem B5043667 : Blo 1572484 5043667 := bstep (se 1 (by rfl) ⟨3782750, by rfl⟩ : syracuseStep 5043667 = 7565501) B7565501
theorem B12760685 : Blo 1572484 12760685 := bstep (se 3 (by rfl) ⟨2392628, by rfl⟩ : syracuseStep 12760685 = 4785257) B4785257
theorem B5977709 : Blo 1572484 5977709 := bstep (se 3 (by rfl) ⟨1120820, by rfl⟩ : syracuseStep 5977709 = 2241641) B2241641
theorem B6723283 : Blo 1572484 6723283 := bstep (se 1 (by rfl) ⟨5042462, by rfl⟩ : syracuseStep 6723283 = 10084925) B10084925
theorem B2987867 : Blo 1572484 2987867 := bstep (se 1 (by rfl) ⟨2240900, by rfl⟩ : syracuseStep 2987867 = 4481801) B4481801
theorem B4036475 : Blo 1572484 4036475 := bstep (se 1 (by rfl) ⟨3027356, by rfl⟩ : syracuseStep 4036475 = 6054713) B6054713
theorem B109035193 : Blo 1572484 109035193 := bstep (se 2 (by rfl) ⟨40888197, by rfl⟩ : syracuseStep 109035193 = 81776395) B81776395
theorem B1890487 : Blo 1572484 1890487 := bstep (se 1 (by rfl) ⟨1417865, by rfl⟩ : syracuseStep 1890487 = 2835731) B2835731
theorem B22684043 : Blo 1572484 22684043 := bstep (se 1 (by rfl) ⟨17013032, by rfl⟩ : syracuseStep 22684043 = 34026065) B34026065
theorem B1891183 : Blo 1572484 1891183 := bstep (se 1 (by rfl) ⟨1418387, by rfl⟩ : syracuseStep 1891183 = 2836775) B2836775
theorem B3538151 : Blo 1572484 3538151 := bstep (se 1 (by rfl) ⟨2653613, by rfl⟩ : syracuseStep 3538151 = 5307227) B5307227
theorem B7560425 : Blo 1572484 7560425 := bstep (se 2 (by rfl) ⟨2835159, by rfl⟩ : syracuseStep 7560425 = 5670319) B5670319
theorem B3980623 : Blo 1572484 3980623 := bstep (se 1 (by rfl) ⟨2985467, by rfl⟩ : syracuseStep 3980623 = 5970935) B5970935
theorem B3636559 : Blo 1572484 3636559 := bstep (se 1 (by rfl) ⟨2727419, by rfl⟩ : syracuseStep 3636559 = 5454839) B5454839
theorem B51010955 : Blo 1572484 51010955 := bstep (se 1 (by rfl) ⟨38258216, by rfl⟩ : syracuseStep 51010955 = 76516433) B76516433
theorem B6552971 : Blo 1572484 6552971 := bstep (se 1 (by rfl) ⟨4914728, by rfl⟩ : syracuseStep 6552971 = 9829457) B9829457
theorem B3636755 : Blo 1572484 3636755 := bstep (se 1 (by rfl) ⟨2727566, by rfl⟩ : syracuseStep 3636755 = 5455133) B5455133
theorem B57384557 : Blo 1572484 57384557 := bstep (se 3 (by rfl) ⟨10759604, by rfl⟩ : syracuseStep 57384557 = 21519209) B21519209
theorem B1769071 : Blo 1572484 1769071 := bstep (se 1 (by rfl) ⟨1326803, by rfl⟩ : syracuseStep 1769071 = 2653607) B2653607
theorem B1572519 : Blo 1572484 1572519 := bstep (se 1 (by rfl) ⟨1179389, by rfl⟩ : syracuseStep 1572519 = 2358779) B2358779
theorem B8076995 : Blo 1572484 8076995 := bstep (se 1 (by rfl) ⟨6057746, by rfl⟩ : syracuseStep 8076995 = 12115493) B12115493
theorem B1769179 : Blo 1572484 1769179 := bstep (se 1 (by rfl) ⟨1326884, by rfl⟩ : syracuseStep 1769179 = 2653769) B2653769
theorem B2359007 : Blo 1572484 2359007 := bstep (se 1 (by rfl) ⟨1769255, by rfl⟩ : syracuseStep 2359007 = 3538511) B3538511
theorem B3538655 : Blo 1572484 3538655 := bstep (se 1 (by rfl) ⟨2653991, by rfl⟩ : syracuseStep 3538655 = 5307983) B5307983
theorem B1572583 : Blo 1572484 1572583 := bstep (se 1 (by rfl) ⟨1179437, by rfl⟩ : syracuseStep 1572583 = 2358875) B2358875
theorem B2359049 : Blo 1572484 2359049 := bstep (se 2 (by rfl) ⟨884643, by rfl⟩ : syracuseStep 2359049 = 1769287) B1769287
theorem B1572639 : Blo 1572484 1572639 := bstep (se 1 (by rfl) ⟨1179479, by rfl⟩ : syracuseStep 1572639 = 2358959) B2358959
theorem B3538727 : Blo 1572484 3538727 := bstep (se 1 (by rfl) ⟨2654045, by rfl⟩ : syracuseStep 3538727 = 5308091) B5308091
theorem B5308199 : Blo 1572484 5308199 := bstep (se 1 (by rfl) ⟨3981149, by rfl⟩ : syracuseStep 5308199 = 7962299) B7962299
theorem B1572719 : Blo 1572484 1572719 := bstep (se 1 (by rfl) ⟨1179539, by rfl⟩ : syracuseStep 1572719 = 2359079) B2359079
theorem B4480879 : Blo 1572484 4480879 := bstep (se 1 (by rfl) ⟨3360659, by rfl⟩ : syracuseStep 4480879 = 6721319) B6721319
theorem B1572775 : Blo 1572484 1572775 := bstep (se 1 (by rfl) ⟨1179581, by rfl⟩ : syracuseStep 1572775 = 2359163) B2359163
theorem B5668807 : Blo 1572484 5668807 := bstep (se 1 (by rfl) ⟨4251605, by rfl⟩ : syracuseStep 5668807 = 8503211) B8503211
theorem B4481095 : Blo 1572484 4481095 := bstep (se 1 (by rfl) ⟨3360821, by rfl⟩ : syracuseStep 4481095 = 6721643) B6721643
theorem B1572991 : Blo 1572484 1572991 := bstep (se 1 (by rfl) ⟨1179743, by rfl⟩ : syracuseStep 1572991 = 2359487) B2359487
theorem B3981545 : Blo 1572484 3981545 := bstep (se 2 (by rfl) ⟨1493079, by rfl⟩ : syracuseStep 3981545 = 2986159) B2986159
theorem B1679599 : Blo 1572484 1679599 := bstep (se 1 (by rfl) ⟨1259699, by rfl⟩ : syracuseStep 1679599 = 2519399) B2519399
theorem B3981575 : Blo 1572484 3981575 := bstep (se 1 (by rfl) ⟨2986181, by rfl⟩ : syracuseStep 3981575 = 5972363) B5972363
theorem B3981707 : Blo 1572484 3981707 := bstep (se 1 (by rfl) ⟨2986280, by rfl⟩ : syracuseStep 3981707 = 5972561) B5972561
theorem B1573275 : Blo 1572484 1573275 := bstep (se 1 (by rfl) ⟨1179956, by rfl⟩ : syracuseStep 1573275 = 2359913) B2359913
theorem B1573279 : Blo 1572484 1573279 := bstep (se 1 (by rfl) ⟨1179959, by rfl⟩ : syracuseStep 1573279 = 2359919) B2359919
theorem B5669281 : Blo 1572484 5669281 := bstep (se 2 (by rfl) ⟨2125980, by rfl⟩ : syracuseStep 5669281 = 4251961) B4251961
theorem B2359835 : Blo 1572484 2359835 := bstep (se 1 (by rfl) ⟨1769876, by rfl⟩ : syracuseStep 2359835 = 3539753) B3539753
theorem B20161133 : Blo 1572484 20161133 := bstep (se 3 (by rfl) ⟨3780212, by rfl⟩ : syracuseStep 20161133 = 7560425) B7560425
theorem B2360015 : Blo 1572484 2360015 := bstep (se 1 (by rfl) ⟨1770011, by rfl⟩ : syracuseStep 2360015 = 3540023) B3540023
theorem B1573695 : Blo 1572484 1573695 := bstep (se 1 (by rfl) ⟨1180271, by rfl⟩ : syracuseStep 1573695 = 2360543) B2360543
theorem B2360135 : Blo 1572484 2360135 := bstep (se 1 (by rfl) ⟨1770101, by rfl⟩ : syracuseStep 2360135 = 3540203) B3540203
theorem B1573703 : Blo 1572484 1573703 := bstep (se 1 (by rfl) ⟨1180277, by rfl⟩ : syracuseStep 1573703 = 2360555) B2360555
theorem B2360201 : Blo 1572484 2360201 := bstep (se 2 (by rfl) ⟨885075, by rfl⟩ : syracuseStep 2360201 = 1770151) B1770151
theorem B5309495 : Blo 1572484 5309495 := bstep (se 1 (by rfl) ⟨3982121, by rfl⟩ : syracuseStep 5309495 = 7964243) B7964243
theorem B1573959 : Blo 1572484 1573959 := bstep (se 1 (by rfl) ⟨1180469, by rfl⟩ : syracuseStep 1573959 = 2360939) B2360939
theorem B3540095 : Blo 1572484 3540095 := bstep (se 1 (by rfl) ⟨2655071, by rfl⟩ : syracuseStep 3540095 = 5310143) B5310143
theorem B2360447 : Blo 1572484 2360447 := bstep (se 1 (by rfl) ⟨1770335, by rfl⟩ : syracuseStep 2360447 = 3540671) B3540671
theorem B1574015 : Blo 1572484 1574015 := bstep (se 1 (by rfl) ⟨1180511, by rfl⟩ : syracuseStep 1574015 = 2361023) B2361023
theorem B8963237 : Blo 1572484 8963237 := bstep (se 4 (by rfl) ⟨840303, by rfl⟩ : syracuseStep 8963237 = 1680607) B1680607
theorem B1574139 : Blo 1572484 1574139 := bstep (se 1 (by rfl) ⟨1180604, by rfl⟩ : syracuseStep 1574139 = 2361209) B2361209
theorem B2360585 : Blo 1572484 2360585 := bstep (se 2 (by rfl) ⟨885219, by rfl⟩ : syracuseStep 2360585 = 1770439) B1770439
theorem B26895725 : Blo 1572484 26895725 := bstep (se 3 (by rfl) ⟨5042948, by rfl⟩ : syracuseStep 26895725 = 10085897) B10085897
theorem B2361065 : Blo 1572484 2361065 := bstep (se 2 (by rfl) ⟨885399, by rfl⟩ : syracuseStep 2361065 = 1770799) B1770799
theorem B2655983 : Blo 1572484 2655983 := bstep (se 1 (by rfl) ⟨1991987, by rfl⟩ : syracuseStep 2655983 = 3983975) B3983975
theorem B2361071 : Blo 1572484 2361071 := bstep (se 1 (by rfl) ⟨1770803, by rfl⟩ : syracuseStep 2361071 = 3541607) B3541607
theorem B294766381 : Blo 1572484 294766381 := bstep (se 3 (by rfl) ⟨55268696, by rfl⟩ : syracuseStep 294766381 = 110537393) B110537393
theorem B22693679 : Blo 1572484 22693679 := bstep (se 1 (by rfl) ⟨17020259, by rfl⟩ : syracuseStep 22693679 = 34040519) B34040519
theorem B5973821 : Blo 1572484 5973821 := bstep (se 3 (by rfl) ⟨1120091, by rfl⟩ : syracuseStep 5973821 = 2240183) B2240183
theorem B3983327 : Blo 1572484 3983327 := bstep (se 1 (by rfl) ⟨2987495, by rfl⟩ : syracuseStep 3983327 = 5974991) B5974991
theorem B2361323 : Blo 1572484 2361323 := bstep (se 1 (by rfl) ⟨1770992, by rfl⟩ : syracuseStep 2361323 = 3541985) B3541985
theorem B2017487 : Blo 1572484 2017487 := bstep (se 1 (by rfl) ⟨1513115, by rfl⟩ : syracuseStep 2017487 = 3026231) B3026231
theorem B2361575 : Blo 1572484 2361575 := bstep (se 1 (by rfl) ⟨1771181, by rfl⟩ : syracuseStep 2361575 = 3542363) B3542363
theorem B3541247 : Blo 1572484 3541247 := bstep (se 1 (by rfl) ⟨2655935, by rfl⟩ : syracuseStep 3541247 = 5311871) B5311871
theorem B2361599 : Blo 1572484 2361599 := bstep (se 1 (by rfl) ⟨1771199, by rfl⟩ : syracuseStep 2361599 = 3542399) B3542399
theorem B34007303 : Blo 1572484 34007303 := bstep (se 1 (by rfl) ⟨25505477, by rfl⟩ : syracuseStep 34007303 = 51010955) B51010955
theorem B4368647 : Blo 1572484 4368647 := bstep (se 1 (by rfl) ⟨3276485, by rfl⟩ : syracuseStep 4368647 = 6552971) B6552971
theorem B8964377 : Blo 1572484 8964377 := bstep (se 2 (by rfl) ⟨3361641, by rfl⟩ : syracuseStep 8964377 = 6723283) B6723283
theorem B28723511 : Blo 1572484 28723511 := bstep (se 1 (by rfl) ⟨21542633, by rfl⟩ : syracuseStep 28723511 = 43085267) B43085267
theorem B5384663 : Blo 1572484 5384663 := bstep (se 1 (by rfl) ⟨4038497, by rfl⟩ : syracuseStep 5384663 = 8076995) B8076995
theorem B5974505 : Blo 1572484 5974505 := bstep (se 2 (by rfl) ⟨2240439, by rfl⟩ : syracuseStep 5974505 = 4480879) B4480879
theorem B4540907 : Blo 1572484 4540907 := bstep (se 1 (by rfl) ⟨3405680, by rfl⟩ : syracuseStep 4540907 = 6811361) B6811361
theorem B5041001 : Blo 1572484 5041001 := bstep (se 2 (by rfl) ⟨1890375, by rfl⟩ : syracuseStep 5041001 = 3780751) B3780751
theorem B19655585 : Blo 1572484 19655585 := bstep (se 2 (by rfl) ⟨7370844, by rfl⟩ : syracuseStep 19655585 = 14741689) B14741689
theorem B3984491 : Blo 1572484 3984491 := bstep (se 1 (by rfl) ⟨2988368, by rfl⟩ : syracuseStep 3984491 = 5976737) B5976737
theorem B8507123 : Blo 1572484 8507123 := bstep (se 1 (by rfl) ⟨6380342, by rfl⟩ : syracuseStep 8507123 = 12760685) B12760685
theorem B5975795 : Blo 1572484 5975795 := bstep (se 1 (by rfl) ⟨4481846, by rfl⟩ : syracuseStep 5975795 = 8963693) B8963693
theorem B3985139 : Blo 1572484 3985139 := bstep (se 1 (by rfl) ⟨2988854, by rfl⟩ : syracuseStep 3985139 = 5977709) B5977709
theorem B2690983 : Blo 1572484 2690983 := bstep (se 1 (by rfl) ⟨2018237, by rfl⟩ : syracuseStep 2690983 = 4036475) B4036475
theorem B5107807 : Blo 1572484 5107807 := bstep (se 1 (by rfl) ⟨3830855, by rfl⟩ : syracuseStep 5107807 = 7661711) B7661711
theorem B145363261 : Blo 1572484 145363261 := bstep (se 3 (by rfl) ⟨27255611, by rfl⟩ : syracuseStep 145363261 = 54511223) B54511223
theorem B163443019 : Blo 1572484 163443019 := bstep (se 1 (by rfl) ⟨122582264, by rfl⟩ : syracuseStep 163443019 = 245164529) B245164529
theorem B2519419 : Blo 1572484 2519419 := bstep (se 1 (by rfl) ⟨1889564, by rfl⟩ : syracuseStep 2519419 = 3779129) B3779129
theorem B302559695 : Blo 1572484 302559695 := bstep (se 1 (by rfl) ⟨226919771, by rfl⟩ : syracuseStep 302559695 = 453839543) B453839543
theorem B7967645 : Blo 1572484 7967645 := bstep (se 3 (by rfl) ⟨1493933, by rfl⟩ : syracuseStep 7967645 = 2987867) B2987867
theorem B145380257 : Blo 1572484 145380257 := bstep (se 2 (by rfl) ⟨54517596, by rfl⟩ : syracuseStep 145380257 = 109035193) B109035193
theorem B7558409 : Blo 1572484 7558409 := bstep (se 2 (by rfl) ⟨2834403, by rfl⟩ : syracuseStep 7558409 = 5668807) B5668807
theorem B48428563 : Blo 1572484 48428563 := bstep (se 1 (by rfl) ⟨36321422, by rfl⟩ : syracuseStep 48428563 = 72642845) B72642845
theorem B13448753 : Blo 1572484 13448753 := bstep (se 2 (by rfl) ⟨5043282, by rfl⟩ : syracuseStep 13448753 = 10086565) B10086565
theorem B2520649 : Blo 1572484 2520649 := bstep (se 2 (by rfl) ⟨945243, by rfl⟩ : syracuseStep 2520649 = 1890487) B1890487
theorem B10082207 : Blo 1572484 10082207 := bstep (se 1 (by rfl) ⟨7561655, by rfl⟩ : syracuseStep 10082207 = 15123311) B15123311
theorem B20158469 : Blo 1572484 20158469 := bstep (se 4 (by rfl) ⟨1889856, by rfl⟩ : syracuseStep 20158469 = 3779713) B3779713
theorem B4479113 : Blo 1572484 4479113 := bstep (se 2 (by rfl) ⟨1679667, by rfl⟩ : syracuseStep 4479113 = 3359335) B3359335
theorem B9566383 : Blo 1572484 9566383 := bstep (se 1 (by rfl) ⟨7174787, by rfl⟩ : syracuseStep 9566383 = 14349575) B14349575
theorem B16144829 : Blo 1572484 16144829 := bstep (se 3 (by rfl) ⟨3027155, by rfl⟩ : syracuseStep 16144829 = 6054311) B6054311
theorem B2521577 : Blo 1572484 2521577 := bstep (se 2 (by rfl) ⟨945591, by rfl⟩ : syracuseStep 2521577 = 1891183) B1891183
theorem B2988809 : Blo 1572484 2988809 := bstep (se 2 (by rfl) ⟨1120803, by rfl⟩ : syracuseStep 2988809 = 2241607) B2241607
theorem B3588359 : Blo 1572484 3588359 := bstep (se 1 (by rfl) ⟨2691269, by rfl⟩ : syracuseStep 3588359 = 5382539) B5382539
theorem B15122695 : Blo 1572484 15122695 := bstep (se 1 (by rfl) ⟨11342021, by rfl⟩ : syracuseStep 15122695 = 22684043) B22684043
theorem B6724615 : Blo 1572484 6724615 := bstep (se 1 (by rfl) ⟨5043461, by rfl⟩ : syracuseStep 6724615 = 10086923) B10086923
theorem B7773191 : Blo 1572484 7773191 := bstep (se 1 (by rfl) ⟨5829893, by rfl⟩ : syracuseStep 7773191 = 11659787) B11659787
theorem B5307497 : Blo 1572484 5307497 := bstep (se 2 (by rfl) ⟨1990311, by rfl⟩ : syracuseStep 5307497 = 3980623) B3980623
theorem B4848745 : Blo 1572484 4848745 := bstep (se 2 (by rfl) ⟨1818279, by rfl⟩ : syracuseStep 4848745 = 3636559) B3636559
theorem B6724889 : Blo 1572484 6724889 := bstep (se 2 (by rfl) ⟨2521833, by rfl⟩ : syracuseStep 6724889 = 5043667) B5043667
theorem B6380927 : Blo 1572484 6380927 := bstep (se 1 (by rfl) ⟨4785695, by rfl⟩ : syracuseStep 6380927 = 9571391) B9571391
theorem B4038095 : Blo 1572484 4038095 := bstep (se 1 (by rfl) ⟨3028571, by rfl⟩ : syracuseStep 4038095 = 6057143) B6057143
theorem B2358761 : Blo 1572484 2358761 := bstep (se 2 (by rfl) ⟨884535, by rfl⟩ : syracuseStep 2358761 = 1769071) B1769071
theorem B2358767 : Blo 1572484 2358767 := bstep (se 1 (by rfl) ⟨1769075, by rfl⟩ : syracuseStep 2358767 = 3538151) B3538151
theorem B6725231 : Blo 1572484 6725231 := bstep (se 1 (by rfl) ⟨5043923, by rfl⟩ : syracuseStep 6725231 = 10087847) B10087847
theorem B2358905 : Blo 1572484 2358905 := bstep (se 2 (by rfl) ⟨884589, by rfl⟩ : syracuseStep 2358905 = 1769179) B1769179
theorem B2424503 : Blo 1572484 2424503 := bstep (se 1 (by rfl) ⟨1818377, by rfl⟩ : syracuseStep 2424503 = 3636755) B3636755
theorem B38256371 : Blo 1572484 38256371 := bstep (se 1 (by rfl) ⟨28692278, by rfl⟩ : syracuseStep 38256371 = 57384557) B57384557
theorem B1572671 : Blo 1572484 1572671 := bstep (se 1 (by rfl) ⟨1179503, by rfl⟩ : syracuseStep 1572671 = 2359007) B2359007
theorem B2359103 : Blo 1572484 2359103 := bstep (se 1 (by rfl) ⟨1769327, by rfl⟩ : syracuseStep 2359103 = 3538655) B3538655
theorem B1572699 : Blo 1572484 1572699 := bstep (se 1 (by rfl) ⟨1179524, by rfl⟩ : syracuseStep 1572699 = 2359049) B2359049
theorem B2359151 : Blo 1572484 2359151 := bstep (se 1 (by rfl) ⟨1769363, by rfl⟩ : syracuseStep 2359151 = 3538727) B3538727
theorem B3538799 : Blo 1572484 3538799 := bstep (se 1 (by rfl) ⟨2654099, by rfl⟩ : syracuseStep 3538799 = 5308199) B5308199
theorem B2654363 : Blo 1572484 2654363 := bstep (se 1 (by rfl) ⟨1990772, by rfl⟩ : syracuseStep 2654363 = 3981545) B3981545
theorem B2654383 : Blo 1572484 2654383 := bstep (se 1 (by rfl) ⟨1990787, by rfl⟩ : syracuseStep 2654383 = 3981575) B3981575
theorem B12755177 : Blo 1572484 12755177 := bstep (se 2 (by rfl) ⟨4783191, by rfl⟩ : syracuseStep 12755177 = 9566383) B9566383
theorem B2654471 : Blo 1572484 2654471 := bstep (se 1 (by rfl) ⟨1990853, by rfl⟩ : syracuseStep 2654471 = 3981707) B3981707
theorem B1573223 : Blo 1572484 1573223 := bstep (se 1 (by rfl) ⟨1179917, by rfl⟩ : syracuseStep 1573223 = 2359835) B2359835
theorem B217924025 : Blo 1572484 217924025 := bstep (se 2 (by rfl) ⟨81721509, by rfl⟩ : syracuseStep 217924025 = 163443019) B163443019
theorem B1573343 : Blo 1572484 1573343 := bstep (se 1 (by rfl) ⟨1180007, by rfl⟩ : syracuseStep 1573343 = 2360015) B2360015
theorem B3359225 : Blo 1572484 3359225 := bstep (se 2 (by rfl) ⟨1259709, by rfl⟩ : syracuseStep 3359225 = 2519419) B2519419
theorem B1573423 : Blo 1572484 1573423 := bstep (se 1 (by rfl) ⟨1180067, by rfl⟩ : syracuseStep 1573423 = 2360135) B2360135
theorem B1573467 : Blo 1572484 1573467 := bstep (se 1 (by rfl) ⟨1180100, by rfl⟩ : syracuseStep 1573467 = 2360201) B2360201
theorem B96920171 : Blo 1572484 96920171 := bstep (se 1 (by rfl) ⟨72690128, by rfl⟩ : syracuseStep 96920171 = 145380257) B145380257
theorem B9568957 : Blo 1572484 9568957 := bstep (se 3 (by rfl) ⟨1794179, by rfl⟩ : syracuseStep 9568957 = 3588359) B3588359
theorem B3539663 : Blo 1572484 3539663 := bstep (se 1 (by rfl) ⟨2654747, by rfl⟩ : syracuseStep 3539663 = 5309495) B5309495
theorem B2360063 : Blo 1572484 2360063 := bstep (se 1 (by rfl) ⟨1770047, by rfl⟩ : syracuseStep 2360063 = 3540095) B3540095
theorem B1573631 : Blo 1572484 1573631 := bstep (se 1 (by rfl) ⟨1180223, by rfl⟩ : syracuseStep 1573631 = 2360447) B2360447
theorem B5038939 : Blo 1572484 5038939 := bstep (se 1 (by rfl) ⟨3779204, by rfl⟩ : syracuseStep 5038939 = 7558409) B7558409
theorem B1573723 : Blo 1572484 1573723 := bstep (se 1 (by rfl) ⟨1180292, by rfl⟩ : syracuseStep 1573723 = 2360585) B2360585
theorem B1574043 : Blo 1572484 1574043 := bstep (se 1 (by rfl) ⟨1180532, by rfl⟩ : syracuseStep 1574043 = 2361065) B2361065
theorem B1770655 : Blo 1572484 1770655 := bstep (se 1 (by rfl) ⟨1327991, by rfl⟩ : syracuseStep 1770655 = 2655983) B2655983
theorem B1574047 : Blo 1572484 1574047 := bstep (se 1 (by rfl) ⟨1180535, by rfl⟩ : syracuseStep 1574047 = 2361071) B2361071
theorem B3982547 : Blo 1572484 3982547 := bstep (se 1 (by rfl) ⟨2986910, by rfl⟩ : syracuseStep 3982547 = 5973821) B5973821
theorem B12109085 : Blo 1572484 12109085 := bstep (se 3 (by rfl) ⟨2270453, by rfl⟩ : syracuseStep 12109085 = 4540907) B4540907
theorem B2655551 : Blo 1572484 2655551 := bstep (se 1 (by rfl) ⟨1991663, by rfl⟩ : syracuseStep 2655551 = 3983327) B3983327
theorem B1574215 : Blo 1572484 1574215 := bstep (se 1 (by rfl) ⟨1180661, by rfl⟩ : syracuseStep 1574215 = 2361323) B2361323
theorem B6464993 : Blo 1572484 6464993 := bstep (se 2 (by rfl) ⟨2424372, by rfl⟩ : syracuseStep 6464993 = 4848745) B4848745
theorem B1574383 : Blo 1572484 1574383 := bstep (se 1 (by rfl) ⟨1180787, by rfl⟩ : syracuseStep 1574383 = 2361575) B2361575
theorem B2360831 : Blo 1572484 2360831 := bstep (se 1 (by rfl) ⟨1770623, by rfl⟩ : syracuseStep 2360831 = 3541247) B3541247
theorem B1574399 : Blo 1572484 1574399 := bstep (se 1 (by rfl) ⟨1180799, by rfl⟩ : syracuseStep 1574399 = 2361599) B2361599
theorem B3589775 : Blo 1572484 3589775 := bstep (se 1 (by rfl) ⟨2692331, by rfl⟩ : syracuseStep 3589775 = 5384663) B5384663
theorem B3983003 : Blo 1572484 3983003 := bstep (se 1 (by rfl) ⟨2987252, by rfl⟩ : syracuseStep 3983003 = 5974505) B5974505
theorem B209659573 : Blo 1572484 209659573 := bstep (se 5 (by rfl) ⟨9827792, by rfl⟩ : syracuseStep 209659573 = 19655585) B19655585
theorem B1992539 : Blo 1572484 1992539 := bstep (se 1 (by rfl) ⟨1494404, by rfl⟩ : syracuseStep 1992539 = 2988809) B2988809
theorem B64571417 : Blo 1572484 64571417 := bstep (se 2 (by rfl) ⟨24214281, by rfl⟩ : syracuseStep 64571417 = 48428563) B48428563
theorem B2656327 : Blo 1572484 2656327 := bstep (se 1 (by rfl) ⟨1992245, by rfl⟩ : syracuseStep 2656327 = 3984491) B3984491
theorem B3360865 : Blo 1572484 3360865 := bstep (se 2 (by rfl) ⟨1260324, by rfl⟩ : syracuseStep 3360865 = 2520649) B2520649
theorem B4483259 : Blo 1572484 4483259 := bstep (se 1 (by rfl) ⟨3362444, by rfl⟩ : syracuseStep 4483259 = 6724889) B6724889
theorem B4253951 : Blo 1572484 4253951 := bstep (se 1 (by rfl) ⟨3190463, by rfl⟩ : syracuseStep 4253951 = 6380927) B6380927
theorem B393021841 : Blo 1572484 393021841 := bstep (se 2 (by rfl) ⟨147383190, by rfl⟩ : syracuseStep 393021841 = 294766381) B294766381
theorem B4483487 : Blo 1572484 4483487 := bstep (se 1 (by rfl) ⟨3362615, by rfl⟩ : syracuseStep 4483487 = 6725231) B6725231
theorem B1616335 : Blo 1572484 1616335 := bstep (se 1 (by rfl) ⟨1212251, by rfl⟩ : syracuseStep 1616335 = 2424503) B2424503
theorem B25504247 : Blo 1572484 25504247 := bstep (se 1 (by rfl) ⟨19128185, by rfl⟩ : syracuseStep 25504247 = 38256371) B38256371
theorem B5671415 : Blo 1572484 5671415 := bstep (se 1 (by rfl) ⟨4253561, by rfl⟩ : syracuseStep 5671415 = 8507123) B8507123
theorem B3983863 : Blo 1572484 3983863 := bstep (se 1 (by rfl) ⟨2987897, by rfl⟩ : syracuseStep 3983863 = 5975795) B5975795
theorem B2656759 : Blo 1572484 2656759 := bstep (se 1 (by rfl) ⟨1992569, by rfl⟩ : syracuseStep 2656759 = 3985139) B3985139
theorem B5974793 : Blo 1572484 5974793 := bstep (se 2 (by rfl) ⟨2240547, by rfl⟩ : syracuseStep 5974793 = 4481095) B4481095
theorem B6810409 : Blo 1572484 6810409 := bstep (se 2 (by rfl) ⟨2553903, by rfl⟩ : syracuseStep 6810409 = 5107807) B5107807
theorem B201706463 : Blo 1572484 201706463 := bstep (se 1 (by rfl) ⟨151279847, by rfl⟩ : syracuseStep 201706463 = 302559695) B302559695
theorem B20163593 : Blo 1572484 20163593 := bstep (se 2 (by rfl) ⟨7561347, by rfl⟩ : syracuseStep 20163593 = 15122695) B15122695
theorem B193817681 : Blo 1572484 193817681 := bstep (se 2 (by rfl) ⟨72681630, by rfl⟩ : syracuseStep 193817681 = 145363261) B145363261
theorem B5311763 : Blo 1572484 5311763 := bstep (se 1 (by rfl) ⟨3983822, by rfl⟩ : syracuseStep 5311763 = 7967645) B7967645
theorem B5975491 : Blo 1572484 5975491 := bstep (se 1 (by rfl) ⟨4481618, by rfl⟩ : syracuseStep 5975491 = 8963237) B8963237
theorem B8965835 : Blo 1572484 8965835 := bstep (se 1 (by rfl) ⟨6724376, by rfl⟩ : syracuseStep 8965835 = 13448753) B13448753
theorem B8957861 : Blo 1572484 8957861 := bstep (se 4 (by rfl) ⟨839799, by rfl⟩ : syracuseStep 8957861 = 1679599) B1679599
theorem B6721471 : Blo 1572484 6721471 := bstep (se 1 (by rfl) ⟨5041103, by rfl⟩ : syracuseStep 6721471 = 10082207) B10082207
theorem B13438979 : Blo 1572484 13438979 := bstep (se 1 (by rfl) ⟨10079234, by rfl⟩ : syracuseStep 13438979 = 20158469) B20158469
theorem B8966153 : Blo 1572484 8966153 := bstep (se 2 (by rfl) ⟨3362307, by rfl⟩ : syracuseStep 8966153 = 6724615) B6724615
theorem B2986075 : Blo 1572484 2986075 := bstep (se 1 (by rfl) ⟨2239556, by rfl⟩ : syracuseStep 2986075 = 4479113) B4479113
theorem B22671535 : Blo 1572484 22671535 := bstep (se 1 (by rfl) ⟨17003651, by rfl⟩ : syracuseStep 22671535 = 34007303) B34007303
theorem B2912431 : Blo 1572484 2912431 := bstep (se 1 (by rfl) ⟨2184323, by rfl⟩ : syracuseStep 2912431 = 4368647) B4368647
theorem B5976251 : Blo 1572484 5976251 := bstep (se 1 (by rfl) ⟨4482188, by rfl⟩ : syracuseStep 5976251 = 8964377) B8964377
theorem B19149007 : Blo 1572484 19149007 := bstep (se 1 (by rfl) ⟨14361755, by rfl⟩ : syracuseStep 19149007 = 28723511) B28723511
theorem B5182127 : Blo 1572484 5182127 := bstep (se 1 (by rfl) ⟨3886595, by rfl⟩ : syracuseStep 5182127 = 7773191) B7773191
theorem B2692063 : Blo 1572484 2692063 := bstep (se 1 (by rfl) ⟨2019047, by rfl⟩ : syracuseStep 2692063 = 4038095) B4038095
theorem B13440755 : Blo 1572484 13440755 := bstep (se 1 (by rfl) ⟨10080566, by rfl⟩ : syracuseStep 13440755 = 20161133) B20161133
theorem B5379965 : Blo 1572484 5379965 := bstep (se 3 (by rfl) ⟨1008743, by rfl⟩ : syracuseStep 5379965 = 2017487) B2017487
theorem B17930483 : Blo 1572484 17930483 := bstep (se 1 (by rfl) ⟨13447862, by rfl⟩ : syracuseStep 17930483 = 26895725) B26895725
theorem B15129119 : Blo 1572484 15129119 := bstep (se 1 (by rfl) ⟨11346839, by rfl⟩ : syracuseStep 15129119 = 22693679) B22693679
theorem B6724205 : Blo 1572484 6724205 := bstep (se 3 (by rfl) ⟨1260788, by rfl⟩ : syracuseStep 6724205 = 2521577) B2521577
theorem B10763219 : Blo 1572484 10763219 := bstep (se 1 (by rfl) ⟨8072414, by rfl⟩ : syracuseStep 10763219 = 16144829) B16144829
theorem B3538331 : Blo 1572484 3538331 := bstep (se 1 (by rfl) ⟨2653748, by rfl⟩ : syracuseStep 3538331 = 5307497) B5307497
theorem B30236165 : Blo 1572484 30236165 := bstep (se 4 (by rfl) ⟨2834640, by rfl⟩ : syracuseStep 30236165 = 5669281) B5669281
theorem B13442669 : Blo 1572484 13442669 := bstep (se 3 (by rfl) ⟨2520500, by rfl⟩ : syracuseStep 13442669 = 5041001) B5041001
theorem B1572507 : Blo 1572484 1572507 := bstep (se 1 (by rfl) ⟨1179380, by rfl⟩ : syracuseStep 1572507 = 2358761) B2358761
theorem B1572511 : Blo 1572484 1572511 := bstep (se 1 (by rfl) ⟨1179383, by rfl⟩ : syracuseStep 1572511 = 2358767) B2358767
theorem B1572603 : Blo 1572484 1572603 := bstep (se 1 (by rfl) ⟨1179452, by rfl⟩ : syracuseStep 1572603 = 2358905) B2358905
theorem B1572735 : Blo 1572484 1572735 := bstep (se 1 (by rfl) ⟨1179551, by rfl⟩ : syracuseStep 1572735 = 2359103) B2359103
theorem B3587977 : Blo 1572484 3587977 := bstep (se 2 (by rfl) ⟨1345491, by rfl⟩ : syracuseStep 3587977 = 2690983) B2690983
theorem B1572767 : Blo 1572484 1572767 := bstep (se 1 (by rfl) ⟨1179575, by rfl⟩ : syracuseStep 1572767 = 2359151) B2359151
theorem B2359199 : Blo 1572484 2359199 := bstep (se 1 (by rfl) ⟨1769399, by rfl⟩ : syracuseStep 2359199 = 3538799) B3538799
theorem B1769575 : Blo 1572484 1769575 := bstep (se 1 (by rfl) ⟨1327181, by rfl⟩ : syracuseStep 1769575 = 2654363) B2654363
theorem B3981433 : Blo 1572484 3981433 := bstep (se 2 (by rfl) ⟨1493037, by rfl⟩ : syracuseStep 3981433 = 2986075) B2986075
theorem B4481153 : Blo 1572484 4481153 := bstep (se 2 (by rfl) ⟨1680432, by rfl⟩ : syracuseStep 4481153 = 3360865) B3360865
theorem B8503451 : Blo 1572484 8503451 := bstep (se 1 (by rfl) ⟨6377588, by rfl⟩ : syracuseStep 8503451 = 12755177) B12755177
theorem B1769647 : Blo 1572484 1769647 := bstep (se 1 (by rfl) ⟨1327235, by rfl⟩ : syracuseStep 1769647 = 2654471) B2654471
theorem B30228713 : Blo 1572484 30228713 := bstep (se 2 (by rfl) ⟨11335767, by rfl⟩ : syracuseStep 30228713 = 22671535) B22671535
theorem B3539177 : Blo 1572484 3539177 := bstep (se 2 (by rfl) ⟨1327191, by rfl⟩ : syracuseStep 3539177 = 2654383) B2654383
theorem B3883241 : Blo 1572484 3883241 := bstep (se 2 (by rfl) ⟨1456215, by rfl⟩ : syracuseStep 3883241 = 2912431) B2912431
theorem B2359775 : Blo 1572484 2359775 := bstep (se 1 (by rfl) ⟨1769831, by rfl⟩ : syracuseStep 2359775 = 3539663) B3539663
theorem B1573375 : Blo 1572484 1573375 := bstep (se 1 (by rfl) ⟨1180031, by rfl⟩ : syracuseStep 1573375 = 2360063) B2360063
theorem B2655031 : Blo 1572484 2655031 := bstep (se 1 (by rfl) ⟨1991273, by rfl⟩ : syracuseStep 2655031 = 3982547) B3982547
theorem B1770367 : Blo 1572484 1770367 := bstep (se 1 (by rfl) ⟨1327775, by rfl⟩ : syracuseStep 1770367 = 2655551) B2655551
theorem B1118184389 : Blo 1572484 1118184389 := bstep (se 4 (by rfl) ⟨104829786, by rfl⟩ : syracuseStep 1118184389 = 209659573) B209659573
theorem B1573887 : Blo 1572484 1573887 := bstep (se 1 (by rfl) ⟨1180415, by rfl⟩ : syracuseStep 1573887 = 2360831) B2360831
theorem B2393183 : Blo 1572484 2393183 := bstep (se 1 (by rfl) ⟨1794887, by rfl⟩ : syracuseStep 2393183 = 3589775) B3589775
theorem B2655335 : Blo 1572484 2655335 := bstep (se 1 (by rfl) ⟨1991501, by rfl⟩ : syracuseStep 2655335 = 3983003) B3983003
theorem B6718585 : Blo 1572484 6718585 := bstep (se 2 (by rfl) ⟨2519469, by rfl⟩ : syracuseStep 6718585 = 5038939) B5038939
theorem B3589417 : Blo 1572484 3589417 := bstep (se 2 (by rfl) ⟨1346031, by rfl⟩ : syracuseStep 3589417 = 2692063) B2692063
theorem B15123773 : Blo 1572484 15123773 := bstep (se 3 (by rfl) ⟨2835707, by rfl⟩ : syracuseStep 15123773 = 5671415) B5671415
theorem B11953655 : Blo 1572484 11953655 := bstep (se 1 (by rfl) ⟨8965241, by rfl⟩ : syracuseStep 11953655 = 17930483) B17930483
theorem B2835967 : Blo 1572484 2835967 := bstep (se 1 (by rfl) ⟨2126975, by rfl⟩ : syracuseStep 2835967 = 4253951) B4253951
theorem B2360873 : Blo 1572484 2360873 := bstep (se 2 (by rfl) ⟨885327, by rfl⟩ : syracuseStep 2360873 = 1770655) B1770655
theorem B10086079 : Blo 1572484 10086079 := bstep (se 1 (by rfl) ⟨7564559, by rfl⟩ : syracuseStep 10086079 = 15129119) B15129119
theorem B4482803 : Blo 1572484 4482803 := bstep (se 1 (by rfl) ⟨3362102, by rfl⟩ : syracuseStep 4482803 = 6724205) B6724205
theorem B3983195 : Blo 1572484 3983195 := bstep (se 1 (by rfl) ⟨2987396, by rfl⟩ : syracuseStep 3983195 = 5974793) B5974793
theorem B2324522933 : Blo 1572484 2324522933 := bstep (se 5 (by rfl) ⟨108962012, by rfl⟩ : syracuseStep 2324522933 = 217924025) B217924025
theorem B3541175 : Blo 1572484 3541175 := bstep (se 1 (by rfl) ⟨2655881, by rfl⟩ : syracuseStep 3541175 = 5311763) B5311763
theorem B8620453 : Blo 1572484 8620453 := bstep (se 4 (by rfl) ⟨808167, by rfl⟩ : syracuseStep 8620453 = 1616335) B1616335
theorem B3541769 : Blo 1572484 3541769 := bstep (se 2 (by rfl) ⟨1328163, by rfl⟩ : syracuseStep 3541769 = 2656327) B2656327
theorem B3984167 : Blo 1572484 3984167 := bstep (se 1 (by rfl) ⟨2988125, by rfl⟩ : syracuseStep 3984167 = 5976251) B5976251
theorem B2239483 : Blo 1572484 2239483 := bstep (se 1 (by rfl) ⟨1679612, by rfl⟩ : syracuseStep 2239483 = 3359225) B3359225
theorem B64613447 : Blo 1572484 64613447 := bstep (se 1 (by rfl) ⟨48460085, by rfl⟩ : syracuseStep 64613447 = 96920171) B96920171
theorem B524029121 : Blo 1572484 524029121 := bstep (se 2 (by rfl) ⟨196510920, by rfl⟩ : syracuseStep 524029121 = 393021841) B393021841
theorem B5311817 : Blo 1572484 5311817 := bstep (se 2 (by rfl) ⟨1991931, by rfl⟩ : syracuseStep 5311817 = 3983863) B3983863
theorem B3542345 : Blo 1572484 3542345 := bstep (se 2 (by rfl) ⟨1328379, by rfl⟩ : syracuseStep 3542345 = 2656759) B2656759
theorem B8072723 : Blo 1572484 8072723 := bstep (se 1 (by rfl) ⟨6054542, by rfl⟩ : syracuseStep 8072723 = 12109085) B12109085
theorem B12758609 : Blo 1572484 12758609 := bstep (se 2 (by rfl) ⟨4784478, by rfl⟩ : syracuseStep 12758609 = 9568957) B9568957
theorem B9080545 : Blo 1572484 9080545 := bstep (se 2 (by rfl) ⟨3405204, by rfl⟩ : syracuseStep 9080545 = 6810409) B6810409
theorem B17239981 : Blo 1572484 17239981 := bstep (se 3 (by rfl) ⟨3232496, by rfl⟩ : syracuseStep 17239981 = 6464993) B6464993
theorem B17002831 : Blo 1572484 17002831 := bstep (se 1 (by rfl) ⟨12752123, by rfl⟩ : syracuseStep 17002831 = 25504247) B25504247
theorem B7967321 : Blo 1572484 7967321 := bstep (se 2 (by rfl) ⟨2987745, by rfl⟩ : syracuseStep 7967321 = 5975491) B5975491
theorem B5313437 : Blo 1572484 5313437 := bstep (se 3 (by rfl) ⟨996269, by rfl⟩ : syracuseStep 5313437 = 1992539) B1992539
theorem B20157443 : Blo 1572484 20157443 := bstep (se 1 (by rfl) ⟨15118082, by rfl⟩ : syracuseStep 20157443 = 30236165) B30236165
theorem B5977223 : Blo 1572484 5977223 := bstep (se 1 (by rfl) ⟨4482917, by rfl⟩ : syracuseStep 5977223 = 8965835) B8965835
theorem B8959319 : Blo 1572484 8959319 := bstep (se 1 (by rfl) ⟨6719489, by rfl⟩ : syracuseStep 8959319 = 13438979) B13438979
theorem B5977435 : Blo 1572484 5977435 := bstep (se 1 (by rfl) ⟨4483076, by rfl⟩ : syracuseStep 5977435 = 8966153) B8966153
theorem B25532009 : Blo 1572484 25532009 := bstep (se 2 (by rfl) ⟨9574503, by rfl⟩ : syracuseStep 25532009 = 19149007) B19149007
theorem B3454751 : Blo 1572484 3454751 := bstep (se 1 (by rfl) ⟨2591063, by rfl⟩ : syracuseStep 3454751 = 5182127) B5182127
theorem B5971907 : Blo 1572484 5971907 := bstep (se 1 (by rfl) ⟨4478930, by rfl⟩ : syracuseStep 5971907 = 8957861) B8957861
theorem B8960503 : Blo 1572484 8960503 := bstep (se 1 (by rfl) ⟨6720377, by rfl⟩ : syracuseStep 8960503 = 13440755) B13440755
theorem B3586643 : Blo 1572484 3586643 := bstep (se 1 (by rfl) ⟨2689982, by rfl⟩ : syracuseStep 3586643 = 5379965) B5379965
theorem B43047611 : Blo 1572484 43047611 := bstep (se 1 (by rfl) ⟨32285708, by rfl⟩ : syracuseStep 43047611 = 64571417) B64571417
theorem B2988839 : Blo 1572484 2988839 := bstep (se 1 (by rfl) ⟨2241629, by rfl⟩ : syracuseStep 2988839 = 4483259) B4483259
theorem B2988991 : Blo 1572484 2988991 := bstep (se 1 (by rfl) ⟨2241743, by rfl⟩ : syracuseStep 2988991 = 4483487) B4483487
theorem B7175479 : Blo 1572484 7175479 := bstep (se 1 (by rfl) ⟨5381609, by rfl⟩ : syracuseStep 7175479 = 10763219) B10763219
theorem B134470975 : Blo 1572484 134470975 := bstep (se 1 (by rfl) ⟨100853231, by rfl⟩ : syracuseStep 134470975 = 201706463) B201706463
theorem B13442395 : Blo 1572484 13442395 := bstep (se 1 (by rfl) ⟨10081796, by rfl⟩ : syracuseStep 13442395 = 20163593) B20163593
theorem B129211787 : Blo 1572484 129211787 := bstep (se 1 (by rfl) ⟨96908840, by rfl⟩ : syracuseStep 129211787 = 193817681) B193817681
theorem B2358887 : Blo 1572484 2358887 := bstep (se 1 (by rfl) ⟨1769165, by rfl⟩ : syracuseStep 2358887 = 3538331) B3538331
theorem B8961779 : Blo 1572484 8961779 := bstep (se 1 (by rfl) ⟨6721334, by rfl⟩ : syracuseStep 8961779 = 13442669) B13442669
theorem B4783969 : Blo 1572484 4783969 := bstep (se 2 (by rfl) ⟨1793988, by rfl⟩ : syracuseStep 4783969 = 3587977) B3587977
theorem B8961961 : Blo 1572484 8961961 := bstep (se 2 (by rfl) ⟨3360735, by rfl⟩ : syracuseStep 8961961 = 6721471) B6721471
theorem B1572799 : Blo 1572484 1572799 := bstep (se 1 (by rfl) ⟨1179599, by rfl⟩ : syracuseStep 1572799 = 2359199) B2359199
theorem B5668967 : Blo 1572484 5668967 := bstep (se 1 (by rfl) ⟨4251725, by rfl⟩ : syracuseStep 5668967 = 8503451) B8503451
theorem B2359433 : Blo 1572484 2359433 := bstep (se 2 (by rfl) ⟨884787, by rfl⟩ : syracuseStep 2359433 = 1769575) B1769575
theorem B20152475 : Blo 1572484 20152475 := bstep (se 1 (by rfl) ⟨15114356, by rfl⟩ : syracuseStep 20152475 = 30228713) B30228713
theorem B2359451 : Blo 1572484 2359451 := bstep (se 1 (by rfl) ⟨1769588, by rfl⟩ : syracuseStep 2359451 = 3539177) B3539177
theorem B5308577 : Blo 1572484 5308577 := bstep (se 2 (by rfl) ⟨1990716, by rfl⟩ : syracuseStep 5308577 = 3981433) B3981433
theorem B2359529 : Blo 1572484 2359529 := bstep (se 2 (by rfl) ⟨884823, by rfl⟩ : syracuseStep 2359529 = 1769647) B1769647
theorem B6381821 : Blo 1572484 6381821 := bstep (se 3 (by rfl) ⟨1196591, by rfl⟩ : syracuseStep 6381821 = 2393183) B2393183
theorem B1573183 : Blo 1572484 1573183 := bstep (se 1 (by rfl) ⟨1179887, by rfl⟩ : syracuseStep 1573183 = 2359775) B2359775
theorem B11493937 : Blo 1572484 11493937 := bstep (se 2 (by rfl) ⟨4310226, by rfl⟩ : syracuseStep 11493937 = 8620453) B8620453
theorem B10355309 : Blo 1572484 10355309 := bstep (se 3 (by rfl) ⟨1941620, by rfl⟩ : syracuseStep 10355309 = 3883241) B3883241
theorem B745456259 : Blo 1572484 745456259 := bstep (se 1 (by rfl) ⟨559092194, by rfl⟩ : syracuseStep 745456259 = 1118184389) B1118184389
theorem B1770223 : Blo 1572484 1770223 := bstep (se 1 (by rfl) ⟨1327667, by rfl⟩ : syracuseStep 1770223 = 2655335) B2655335
theorem B38257525 : Blo 1572484 38257525 := bstep (se 5 (by rfl) ⟨1793321, by rfl⟩ : syracuseStep 38257525 = 3586643) B3586643
theorem B5972879 : Blo 1572484 5972879 := bstep (se 1 (by rfl) ⟨4479659, by rfl⟩ : syracuseStep 5972879 = 8959319) B8959319
theorem B1573915 : Blo 1572484 1573915 := bstep (se 1 (by rfl) ⟨1180436, by rfl⟩ : syracuseStep 1573915 = 2360873) B2360873
theorem B3540041 : Blo 1572484 3540041 := bstep (se 2 (by rfl) ⟨1327515, by rfl⟩ : syracuseStep 3540041 = 2655031) B2655031
theorem B2360489 : Blo 1572484 2360489 := bstep (se 2 (by rfl) ⟨885183, by rfl⟩ : syracuseStep 2360489 = 1770367) B1770367
theorem B2655463 : Blo 1572484 2655463 := bstep (se 1 (by rfl) ⟨1991597, by rfl⟩ : syracuseStep 2655463 = 3983195) B3983195
theorem B1549681955 : Blo 1572484 1549681955 := bstep (se 1 (by rfl) ⟨1162261466, by rfl⟩ : syracuseStep 1549681955 = 2324522933) B2324522933
theorem B2360783 : Blo 1572484 2360783 := bstep (se 1 (by rfl) ⟨1770587, by rfl⟩ : syracuseStep 2360783 = 3541175) B3541175
theorem B4785889 : Blo 1572484 4785889 := bstep (se 2 (by rfl) ⟨1794708, by rfl⟩ : syracuseStep 4785889 = 3589417) B3589417
theorem B28698407 : Blo 1572484 28698407 := bstep (se 1 (by rfl) ⟨21523805, by rfl⟩ : syracuseStep 28698407 = 43047611) B43047611
theorem B2361179 : Blo 1572484 2361179 := bstep (se 1 (by rfl) ⟨1770884, by rfl⟩ : syracuseStep 2361179 = 3541769) B3541769
theorem B2656111 : Blo 1572484 2656111 := bstep (se 1 (by rfl) ⟨1992083, by rfl⟩ : syracuseStep 2656111 = 3984167) B3984167
theorem B11954141 : Blo 1572484 11954141 := bstep (se 3 (by rfl) ⟨2241401, by rfl⟩ : syracuseStep 11954141 = 4482803) B4482803
theorem B43075631 : Blo 1572484 43075631 := bstep (se 1 (by rfl) ⟨32306723, by rfl⟩ : syracuseStep 43075631 = 64613447) B64613447
theorem B3541211 : Blo 1572484 3541211 := bstep (se 1 (by rfl) ⟨2655908, by rfl⟩ : syracuseStep 3541211 = 5311817) B5311817
theorem B2361563 : Blo 1572484 2361563 := bstep (se 1 (by rfl) ⟨1771172, by rfl⟩ : syracuseStep 2361563 = 3542345) B3542345
theorem B86141191 : Blo 1572484 86141191 := bstep (se 1 (by rfl) ⟨64605893, by rfl⟩ : syracuseStep 86141191 = 129211787) B129211787
theorem B8505739 : Blo 1572484 8505739 := bstep (se 1 (by rfl) ⟨6379304, by rfl⟩ : syracuseStep 8505739 = 12758609) B12758609
theorem B5974519 : Blo 1572484 5974519 := bstep (se 1 (by rfl) ⟨4480889, by rfl⟩ : syracuseStep 5974519 = 8961779) B8961779
theorem B5311547 : Blo 1572484 5311547 := bstep (se 1 (by rfl) ⟨3983660, by rfl⟩ : syracuseStep 5311547 = 7967321) B7967321
theorem B22670441 : Blo 1572484 22670441 := bstep (se 2 (by rfl) ⟨8501415, by rfl⟩ : syracuseStep 22670441 = 17002831) B17002831
theorem B3542291 : Blo 1572484 3542291 := bstep (se 1 (by rfl) ⟨2656718, by rfl⟩ : syracuseStep 3542291 = 5313437) B5313437
theorem B11947337 : Blo 1572484 11947337 := bstep (se 2 (by rfl) ⟨4480251, by rfl⟩ : syracuseStep 11947337 = 8960503) B8960503
theorem B13438295 : Blo 1572484 13438295 := bstep (se 1 (by rfl) ⟨10078721, by rfl⟩ : syracuseStep 13438295 = 20157443) B20157443
theorem B3984815 : Blo 1572484 3984815 := bstep (se 1 (by rfl) ⟨2988611, by rfl⟩ : syracuseStep 3984815 = 5977223) B5977223
theorem B3985321 : Blo 1572484 3985321 := bstep (se 2 (by rfl) ⟨1494495, by rfl⟩ : syracuseStep 3985321 = 2988991) B2988991
theorem B2985977 : Blo 1572484 2985977 := bstep (se 2 (by rfl) ⟨1119741, by rfl⟩ : syracuseStep 2985977 = 2239483) B2239483
theorem B8958113 : Blo 1572484 8958113 := bstep (se 2 (by rfl) ⟨3359292, by rfl⟩ : syracuseStep 8958113 = 6718585) B6718585
theorem B179294633 : Blo 1572484 179294633 := bstep (se 2 (by rfl) ⟨67235487, by rfl⟩ : syracuseStep 179294633 = 134470975) B134470975
theorem B3781289 : Blo 1572484 3781289 := bstep (se 2 (by rfl) ⟨1417983, by rfl⟩ : syracuseStep 3781289 = 2835967) B2835967
theorem B9212669 : Blo 1572484 9212669 := bstep (se 3 (by rfl) ⟨1727375, by rfl⟩ : syracuseStep 9212669 = 3454751) B3454751
theorem B349352747 : Blo 1572484 349352747 := bstep (se 1 (by rfl) ⟨262014560, by rfl⟩ : syracuseStep 349352747 = 524029121) B524029121
theorem B13448105 : Blo 1572484 13448105 := bstep (se 2 (by rfl) ⟨5043039, by rfl⟩ : syracuseStep 13448105 = 10086079) B10086079
theorem B6378625 : Blo 1572484 6378625 := bstep (se 2 (by rfl) ⟨2391984, by rfl⟩ : syracuseStep 6378625 = 4783969) B4783969
theorem B11949281 : Blo 1572484 11949281 := bstep (se 2 (by rfl) ⟨4480980, by rfl⟩ : syracuseStep 11949281 = 8961961) B8961961
theorem B2987435 : Blo 1572484 2987435 := bstep (se 1 (by rfl) ⟨2240576, by rfl⟩ : syracuseStep 2987435 = 4481153) B4481153
theorem B10082515 : Blo 1572484 10082515 := bstep (se 1 (by rfl) ⟨7561886, by rfl⟩ : syracuseStep 10082515 = 15123773) B15123773
theorem B7969103 : Blo 1572484 7969103 := bstep (se 1 (by rfl) ⟨5976827, by rfl⟩ : syracuseStep 7969103 = 11953655) B11953655
theorem B17021339 : Blo 1572484 17021339 := bstep (se 1 (by rfl) ⟨12766004, by rfl⟩ : syracuseStep 17021339 = 25532009) B25532009
theorem B9567305 : Blo 1572484 9567305 := bstep (se 2 (by rfl) ⟨3587739, by rfl⟩ : syracuseStep 9567305 = 7175479) B7175479
theorem B17923193 : Blo 1572484 17923193 := bstep (se 2 (by rfl) ⟨6721197, by rfl⟩ : syracuseStep 17923193 = 13442395) B13442395
theorem B7969913 : Blo 1572484 7969913 := bstep (se 2 (by rfl) ⟨2988717, by rfl⟩ : syracuseStep 7969913 = 5977435) B5977435
theorem B7970237 : Blo 1572484 7970237 := bstep (se 3 (by rfl) ⟨1494419, by rfl⟩ : syracuseStep 7970237 = 2988839) B2988839
theorem B12107393 : Blo 1572484 12107393 := bstep (se 2 (by rfl) ⟨4540272, by rfl⟩ : syracuseStep 12107393 = 9080545) B9080545
theorem B5381815 : Blo 1572484 5381815 := bstep (se 1 (by rfl) ⟨4036361, by rfl⟩ : syracuseStep 5381815 = 8072723) B8072723
theorem B1572591 : Blo 1572484 1572591 := bstep (se 1 (by rfl) ⟨1179443, by rfl⟩ : syracuseStep 1572591 = 2358887) B2358887
theorem B22986641 : Blo 1572484 22986641 := bstep (se 2 (by rfl) ⟨8619990, by rfl⟩ : syracuseStep 22986641 = 17239981) B17239981
theorem B3981271 : Blo 1572484 3981271 := bstep (se 1 (by rfl) ⟨2985953, by rfl⟩ : syracuseStep 3981271 = 5971907) B5971907
theorem B1572955 : Blo 1572484 1572955 := bstep (se 1 (by rfl) ⟨1179716, by rfl⟩ : syracuseStep 1572955 = 2359433) B2359433
theorem B13434983 : Blo 1572484 13434983 := bstep (se 1 (by rfl) ⟨10076237, by rfl⟩ : syracuseStep 13434983 = 20152475) B20152475
theorem B5972075 : Blo 1572484 5972075 := bstep (se 1 (by rfl) ⟨4479056, by rfl⟩ : syracuseStep 5972075 = 8958113) B8958113
theorem B3539051 : Blo 1572484 3539051 := bstep (se 1 (by rfl) ⟨2654288, by rfl⟩ : syracuseStep 3539051 = 5308577) B5308577
theorem B1573019 : Blo 1572484 1573019 := bstep (se 1 (by rfl) ⟨1179764, by rfl⟩ : syracuseStep 1573019 = 2359529) B2359529
theorem B13443353 : Blo 1572484 13443353 := bstep (se 2 (by rfl) ⟨5041257, by rfl⟩ : syracuseStep 13443353 = 10082515) B10082515
theorem B119529755 : Blo 1572484 119529755 := bstep (se 1 (by rfl) ⟨89647316, by rfl⟩ : syracuseStep 119529755 = 179294633) B179294633
theorem B1572967 : Blo 1572484 1572967 := bstep (se 1 (by rfl) ⟨1179725, by rfl⟩ : syracuseStep 1572967 = 2359451) B2359451
theorem B3981919 : Blo 1572484 3981919 := bstep (se 1 (by rfl) ⟨2986439, by rfl⟩ : syracuseStep 3981919 = 5972879) B5972879
theorem B2360027 : Blo 1572484 2360027 := bstep (se 1 (by rfl) ⟨1770020, by rfl⟩ : syracuseStep 2360027 = 3540041) B3540041
theorem B1573659 : Blo 1572484 1573659 := bstep (se 1 (by rfl) ⟨1180244, by rfl⟩ : syracuseStep 1573659 = 2360489) B2360489
theorem B6381185 : Blo 1572484 6381185 := bstep (se 2 (by rfl) ⟨2392944, by rfl⟩ : syracuseStep 6381185 = 4785889) B4785889
theorem B1991623 : Blo 1572484 1991623 := bstep (se 1 (by rfl) ⟨1493717, by rfl⟩ : syracuseStep 1991623 = 2987435) B2987435
theorem B1573855 : Blo 1572484 1573855 := bstep (se 1 (by rfl) ⟨1180391, by rfl⟩ : syracuseStep 1573855 = 2360783) B2360783
theorem B2360297 : Blo 1572484 2360297 := bstep (se 2 (by rfl) ⟨885111, by rfl⟩ : syracuseStep 2360297 = 1770223) B1770223
theorem B1574119 : Blo 1572484 1574119 := bstep (se 1 (by rfl) ⟨1180589, by rfl⟩ : syracuseStep 1574119 = 2361179) B2361179
theorem B2360807 : Blo 1572484 2360807 := bstep (se 1 (by rfl) ⟨1770605, by rfl⟩ : syracuseStep 2360807 = 3541211) B3541211
theorem B1574375 : Blo 1572484 1574375 := bstep (se 1 (by rfl) ⟨1180781, by rfl⟩ : syracuseStep 1574375 = 2361563) B2361563
theorem B8504833 : Blo 1572484 8504833 := bstep (se 2 (by rfl) ⟨3189312, by rfl⟩ : syracuseStep 8504833 = 6378625) B6378625
theorem B11347559 : Blo 1572484 11347559 := bstep (se 1 (by rfl) ⟨8510669, by rfl⟩ : syracuseStep 11347559 = 17021339) B17021339
theorem B3540617 : Blo 1572484 3540617 := bstep (se 2 (by rfl) ⟨1327731, by rfl⟩ : syracuseStep 3540617 = 2655463) B2655463
theorem B3541031 : Blo 1572484 3541031 := bstep (se 1 (by rfl) ⟨2655773, by rfl⟩ : syracuseStep 3541031 = 5311547) B5311547
theorem B2361527 : Blo 1572484 2361527 := bstep (se 1 (by rfl) ⟨1771145, by rfl⟩ : syracuseStep 2361527 = 3542291) B3542291
theorem B7964891 : Blo 1572484 7964891 := bstep (se 1 (by rfl) ⟨5973668, by rfl⟩ : syracuseStep 7964891 = 11947337) B11947337
theorem B2656543 : Blo 1572484 2656543 := bstep (se 1 (by rfl) ⟨1992407, by rfl⟩ : syracuseStep 2656543 = 3984815) B3984815
theorem B8071595 : Blo 1572484 8071595 := bstep (se 1 (by rfl) ⟨6053696, by rfl⟩ : syracuseStep 8071595 = 12107393) B12107393
theorem B3541481 : Blo 1572484 3541481 := bstep (se 2 (by rfl) ⟨1328055, by rfl⟩ : syracuseStep 3541481 = 2656111) B2656111
theorem B3779311 : Blo 1572484 3779311 := bstep (se 1 (by rfl) ⟨2834483, by rfl⟩ : syracuseStep 3779311 = 5668967) B5668967
theorem B4254547 : Blo 1572484 4254547 := bstep (se 1 (by rfl) ⟨3190910, by rfl⟩ : syracuseStep 4254547 = 6381821) B6381821
theorem B114854921 : Blo 1572484 114854921 := bstep (se 2 (by rfl) ⟨43070595, by rfl⟩ : syracuseStep 114854921 = 86141191) B86141191
theorem B496970839 : Blo 1572484 496970839 := bstep (se 1 (by rfl) ⟨372728129, by rfl⟩ : syracuseStep 496970839 = 745456259) B745456259
theorem B11340985 : Blo 1572484 11340985 := bstep (se 2 (by rfl) ⟨4252869, by rfl⟩ : syracuseStep 11340985 = 8505739) B8505739
theorem B232901831 : Blo 1572484 232901831 := bstep (se 1 (by rfl) ⟨174676373, by rfl⟩ : syracuseStep 232901831 = 349352747) B349352747
theorem B8965403 : Blo 1572484 8965403 := bstep (se 1 (by rfl) ⟨6724052, by rfl⟩ : syracuseStep 8965403 = 13448105) B13448105
theorem B7966025 : Blo 1572484 7966025 := bstep (se 2 (by rfl) ⟨2987259, by rfl⟩ : syracuseStep 7966025 = 5974519) B5974519
theorem B7966187 : Blo 1572484 7966187 := bstep (se 1 (by rfl) ⟨5974640, by rfl⟩ : syracuseStep 7966187 = 11949281) B11949281
theorem B1033121303 : Blo 1572484 1033121303 := bstep (se 1 (by rfl) ⟨774840977, by rfl⟩ : syracuseStep 1033121303 = 1549681955) B1549681955
theorem B19132271 : Blo 1572484 19132271 := bstep (se 1 (by rfl) ⟨14349203, by rfl⟩ : syracuseStep 19132271 = 28698407) B28698407
theorem B28717087 : Blo 1572484 28717087 := bstep (se 1 (by rfl) ⟨21537815, by rfl⟩ : syracuseStep 28717087 = 43075631) B43075631
theorem B5312735 : Blo 1572484 5312735 := bstep (se 1 (by rfl) ⟨3984551, by rfl⟩ : syracuseStep 5312735 = 7969103) B7969103
theorem B6378203 : Blo 1572484 6378203 := bstep (se 1 (by rfl) ⟨4783652, by rfl⟩ : syracuseStep 6378203 = 9567305) B9567305
theorem B11948795 : Blo 1572484 11948795 := bstep (se 1 (by rfl) ⟨8961596, by rfl⟩ : syracuseStep 11948795 = 17923193) B17923193
theorem B5313275 : Blo 1572484 5313275 := bstep (se 1 (by rfl) ⟨3984956, by rfl⟩ : syracuseStep 5313275 = 7969913) B7969913
theorem B8958863 : Blo 1572484 8958863 := bstep (se 1 (by rfl) ⟨6719147, by rfl⟩ : syracuseStep 8958863 = 13438295) B13438295
theorem B5313491 : Blo 1572484 5313491 := bstep (se 1 (by rfl) ⟨3985118, by rfl⟩ : syracuseStep 5313491 = 7970237) B7970237
theorem B5313761 : Blo 1572484 5313761 := bstep (se 2 (by rfl) ⟨1992660, by rfl⟩ : syracuseStep 5313761 = 3985321) B3985321
theorem B15324427 : Blo 1572484 15324427 := bstep (se 1 (by rfl) ⟨11493320, by rfl⟩ : syracuseStep 15324427 = 22986641) B22986641
theorem B6903539 : Blo 1572484 6903539 := bstep (se 1 (by rfl) ⟨5177654, by rfl⟩ : syracuseStep 6903539 = 10355309) B10355309
theorem B6141779 : Blo 1572484 6141779 := bstep (se 1 (by rfl) ⟨4606334, by rfl⟩ : syracuseStep 6141779 = 9212669) B9212669
theorem B15325249 : Blo 1572484 15325249 := bstep (se 2 (by rfl) ⟨5746968, by rfl⟩ : syracuseStep 15325249 = 11493937) B11493937
theorem B51010033 : Blo 1572484 51010033 := bstep (se 2 (by rfl) ⟨19128762, by rfl⟩ : syracuseStep 51010033 = 38257525) B38257525
theorem B7969427 : Blo 1572484 7969427 := bstep (se 1 (by rfl) ⟨5977070, by rfl⟩ : syracuseStep 7969427 = 11954141) B11954141
theorem B10083437 : Blo 1572484 10083437 := bstep (se 3 (by rfl) ⟨1890644, by rfl⟩ : syracuseStep 10083437 = 3781289) B3781289
theorem B15113627 : Blo 1572484 15113627 := bstep (se 1 (by rfl) ⟨11335220, by rfl⟩ : syracuseStep 15113627 = 22670441) B22670441
theorem B7175753 : Blo 1572484 7175753 := bstep (se 2 (by rfl) ⟨2690907, by rfl⟩ : syracuseStep 7175753 = 5381815) B5381815
theorem B5308361 : Blo 1572484 5308361 := bstep (se 2 (by rfl) ⟨1990635, by rfl⟩ : syracuseStep 5308361 = 3981271) B3981271
theorem B1990651 : Blo 1572484 1990651 := bstep (se 1 (by rfl) ⟨1492988, by rfl⟩ : syracuseStep 1990651 = 2985977) B2985977
theorem B38289449 : Blo 1572484 38289449 := bstep (se 2 (by rfl) ⟨14358543, by rfl⟩ : syracuseStep 38289449 = 28717087) B28717087
theorem B3981383 : Blo 1572484 3981383 := bstep (se 1 (by rfl) ⟨2986037, by rfl⟩ : syracuseStep 3981383 = 5972075) B5972075
theorem B2359367 : Blo 1572484 2359367 := bstep (se 1 (by rfl) ⟨1769525, by rfl⟩ : syracuseStep 2359367 = 3539051) B3539051
theorem B8962235 : Blo 1572484 8962235 := bstep (se 1 (by rfl) ⟨6721676, by rfl⟩ : syracuseStep 8962235 = 13443353) B13443353
theorem B1573351 : Blo 1572484 1573351 := bstep (se 1 (by rfl) ⟨1180013, by rfl⟩ : syracuseStep 1573351 = 2360027) B2360027
theorem B5972575 : Blo 1572484 5972575 := bstep (se 1 (by rfl) ⟨4479431, by rfl⟩ : syracuseStep 5972575 = 8958863) B8958863
theorem B1573531 : Blo 1572484 1573531 := bstep (se 1 (by rfl) ⟨1180148, by rfl⟩ : syracuseStep 1573531 = 2360297) B2360297
theorem B5309225 : Blo 1572484 5309225 := bstep (se 2 (by rfl) ⟨1990959, by rfl⟩ : syracuseStep 5309225 = 3981919) B3981919
theorem B5039081 : Blo 1572484 5039081 := bstep (se 2 (by rfl) ⟨1889655, by rfl⟩ : syracuseStep 5039081 = 3779311) B3779311
theorem B1573871 : Blo 1572484 1573871 := bstep (se 1 (by rfl) ⟨1180403, by rfl⟩ : syracuseStep 1573871 = 2360807) B2360807
theorem B2360411 : Blo 1572484 2360411 := bstep (se 1 (by rfl) ⟨1770308, by rfl⟩ : syracuseStep 2360411 = 3540617) B3540617
theorem B2655497 : Blo 1572484 2655497 := bstep (se 2 (by rfl) ⟨995811, by rfl⟩ : syracuseStep 2655497 = 1991623) B1991623
theorem B2360687 : Blo 1572484 2360687 := bstep (se 1 (by rfl) ⟨1770515, by rfl⟩ : syracuseStep 2360687 = 3541031) B3541031
theorem B662627785 : Blo 1572484 662627785 := bstep (se 2 (by rfl) ⟨248485419, by rfl⟩ : syracuseStep 662627785 = 496970839) B496970839
theorem B1574351 : Blo 1572484 1574351 := bstep (se 1 (by rfl) ⟨1180763, by rfl⟩ : syracuseStep 1574351 = 2361527) B2361527
theorem B5309927 : Blo 1572484 5309927 := bstep (se 1 (by rfl) ⟨3982445, by rfl⟩ : syracuseStep 5309927 = 7964891) B7964891
theorem B2360987 : Blo 1572484 2360987 := bstep (se 1 (by rfl) ⟨1770740, by rfl⟩ : syracuseStep 2360987 = 3541481) B3541481
theorem B17016493 : Blo 1572484 17016493 := bstep (se 3 (by rfl) ⟨3190592, by rfl⟩ : syracuseStep 17016493 = 6381185) B6381185
theorem B20432569 : Blo 1572484 20432569 := bstep (se 2 (by rfl) ⟨7662213, by rfl⟩ : syracuseStep 20432569 = 15324427) B15324427
theorem B17008541 : Blo 1572484 17008541 := bstep (se 3 (by rfl) ⟨3189101, by rfl⟩ : syracuseStep 17008541 = 6378203) B6378203
theorem B11339777 : Blo 1572484 11339777 := bstep (se 2 (by rfl) ⟨4252416, by rfl⟩ : syracuseStep 11339777 = 8504833) B8504833
theorem B5310683 : Blo 1572484 5310683 := bstep (se 1 (by rfl) ⟨3983012, by rfl⟩ : syracuseStep 5310683 = 7966025) B7966025
theorem B5310791 : Blo 1572484 5310791 := bstep (se 1 (by rfl) ⟨3983093, by rfl⟩ : syracuseStep 5310791 = 7966187) B7966187
theorem B8956655 : Blo 1572484 8956655 := bstep (se 1 (by rfl) ⟨6717491, by rfl⟩ : syracuseStep 8956655 = 13434983) B13434983
theorem B20433665 : Blo 1572484 20433665 := bstep (se 2 (by rfl) ⟨7662624, by rfl⟩ : syracuseStep 20433665 = 15325249) B15325249
theorem B3541823 : Blo 1572484 3541823 := bstep (se 1 (by rfl) ⟨2656367, by rfl⟩ : syracuseStep 3541823 = 5312735) B5312735
theorem B79686503 : Blo 1572484 79686503 := bstep (se 1 (by rfl) ⟨59764877, by rfl⟩ : syracuseStep 79686503 = 119529755) B119529755
theorem B3542057 : Blo 1572484 3542057 := bstep (se 2 (by rfl) ⟨1328271, by rfl⟩ : syracuseStep 3542057 = 2656543) B2656543
theorem B7965863 : Blo 1572484 7965863 := bstep (se 1 (by rfl) ⟨5974397, by rfl⟩ : syracuseStep 7965863 = 11948795) B11948795
theorem B3542183 : Blo 1572484 3542183 := bstep (se 1 (by rfl) ⟨2656637, by rfl⟩ : syracuseStep 3542183 = 5313275) B5313275
theorem B3542327 : Blo 1572484 3542327 := bstep (se 1 (by rfl) ⟨2656745, by rfl⟩ : syracuseStep 3542327 = 5313491) B5313491
theorem B68013377 : Blo 1572484 68013377 := bstep (se 2 (by rfl) ⟨25505016, by rfl⟩ : syracuseStep 68013377 = 51010033) B51010033
theorem B3542507 : Blo 1572484 3542507 := bstep (se 1 (by rfl) ⟨2656880, by rfl⟩ : syracuseStep 3542507 = 5313761) B5313761
theorem B7565039 : Blo 1572484 7565039 := bstep (se 1 (by rfl) ⟨5673779, by rfl⟩ : syracuseStep 7565039 = 11347559) B11347559
theorem B5672729 : Blo 1572484 5672729 := bstep (se 2 (by rfl) ⟨2127273, by rfl⟩ : syracuseStep 5672729 = 4254547) B4254547
theorem B5312951 : Blo 1572484 5312951 := bstep (se 1 (by rfl) ⟨3984713, by rfl⟩ : syracuseStep 5312951 = 7969427) B7969427
theorem B6722291 : Blo 1572484 6722291 := bstep (se 1 (by rfl) ⟨5041718, by rfl⟩ : syracuseStep 6722291 = 10083437) B10083437
theorem B155267887 : Blo 1572484 155267887 := bstep (se 1 (by rfl) ⟨116450915, by rfl⟩ : syracuseStep 155267887 = 232901831) B232901831
theorem B5976935 : Blo 1572484 5976935 := bstep (se 1 (by rfl) ⟨4482701, by rfl⟩ : syracuseStep 5976935 = 8965403) B8965403
theorem B688747535 : Blo 1572484 688747535 := bstep (se 1 (by rfl) ⟨516560651, by rfl⟩ : syracuseStep 688747535 = 1033121303) B1033121303
theorem B4602359 : Blo 1572484 4602359 := bstep (se 1 (by rfl) ⟨3451769, by rfl⟩ : syracuseStep 4602359 = 6903539) B6903539
theorem B4094519 : Blo 1572484 4094519 := bstep (se 1 (by rfl) ⟨3070889, by rfl⟩ : syracuseStep 4094519 = 6141779) B6141779
theorem B15121313 : Blo 1572484 15121313 := bstep (se 2 (by rfl) ⟨5670492, by rfl⟩ : syracuseStep 15121313 = 11340985) B11340985
theorem B5381063 : Blo 1572484 5381063 := bstep (se 1 (by rfl) ⟨4035797, by rfl⟩ : syracuseStep 5381063 = 8071595) B8071595
theorem B76569947 : Blo 1572484 76569947 := bstep (se 1 (by rfl) ⟨57427460, by rfl⟩ : syracuseStep 76569947 = 114854921) B114854921
theorem B10075751 : Blo 1572484 10075751 := bstep (se 1 (by rfl) ⟨7556813, by rfl⟩ : syracuseStep 10075751 = 15113627) B15113627
theorem B4783835 : Blo 1572484 4783835 := bstep (se 1 (by rfl) ⟨3587876, by rfl⟩ : syracuseStep 4783835 = 7175753) B7175753
theorem B12754847 : Blo 1572484 12754847 := bstep (se 1 (by rfl) ⟨9566135, by rfl⟩ : syracuseStep 12754847 = 19132271) B19132271
theorem B3538907 : Blo 1572484 3538907 := bstep (se 1 (by rfl) ⟨2654180, by rfl⟩ : syracuseStep 3538907 = 5308361) B5308361
theorem B2654201 : Blo 1572484 2654201 := bstep (se 2 (by rfl) ⟨995325, by rfl⟩ : syracuseStep 2654201 = 1990651) B1990651
theorem B25526299 : Blo 1572484 25526299 := bstep (se 1 (by rfl) ⟨19144724, by rfl⟩ : syracuseStep 25526299 = 38289449) B38289449
theorem B2654255 : Blo 1572484 2654255 := bstep (se 1 (by rfl) ⟨1990691, by rfl⟩ : syracuseStep 2654255 = 3981383) B3981383
theorem B1572911 : Blo 1572484 1572911 := bstep (se 1 (by rfl) ⟨1179683, by rfl⟩ : syracuseStep 1572911 = 2359367) B2359367
theorem B3539483 : Blo 1572484 3539483 := bstep (se 1 (by rfl) ⟨2654612, by rfl⟩ : syracuseStep 3539483 = 5309225) B5309225
theorem B3359387 : Blo 1572484 3359387 := bstep (se 1 (by rfl) ⟨2519540, by rfl⟩ : syracuseStep 3359387 = 5039081) B5039081
theorem B1573607 : Blo 1572484 1573607 := bstep (se 1 (by rfl) ⟨1180205, by rfl⟩ : syracuseStep 1573607 = 2360411) B2360411
theorem B7963433 : Blo 1572484 7963433 := bstep (se 2 (by rfl) ⟨2986287, by rfl⟩ : syracuseStep 7963433 = 5972575) B5972575
theorem B1770331 : Blo 1572484 1770331 := bstep (se 1 (by rfl) ⟨1327748, by rfl⟩ : syracuseStep 1770331 = 2655497) B2655497
theorem B1573791 : Blo 1572484 1573791 := bstep (se 1 (by rfl) ⟨1180343, by rfl⟩ : syracuseStep 1573791 = 2360687) B2360687
theorem B3539951 : Blo 1572484 3539951 := bstep (se 1 (by rfl) ⟨2654963, by rfl⟩ : syracuseStep 3539951 = 5309927) B5309927
theorem B11339027 : Blo 1572484 11339027 := bstep (se 1 (by rfl) ⟨8504270, by rfl⟩ : syracuseStep 11339027 = 17008541) B17008541
theorem B12272957 : Blo 1572484 12272957 := bstep (se 3 (by rfl) ⟨2301179, by rfl⟩ : syracuseStep 12272957 = 4602359) B4602359
theorem B3540455 : Blo 1572484 3540455 := bstep (se 1 (by rfl) ⟨2655341, by rfl⟩ : syracuseStep 3540455 = 5310683) B5310683
theorem B3540527 : Blo 1572484 3540527 := bstep (se 1 (by rfl) ⟨2655395, by rfl⟩ : syracuseStep 3540527 = 5310791) B5310791
theorem B2361215 : Blo 1572484 2361215 := bstep (se 1 (by rfl) ⟨1770911, by rfl⟩ : syracuseStep 2361215 = 3541823) B3541823
theorem B17926109 : Blo 1572484 17926109 := bstep (se 3 (by rfl) ⟨3361145, by rfl⟩ : syracuseStep 17926109 = 6722291) B6722291
theorem B2361371 : Blo 1572484 2361371 := bstep (se 1 (by rfl) ⟨1771028, by rfl⟩ : syracuseStep 2361371 = 3542057) B3542057
theorem B5310575 : Blo 1572484 5310575 := bstep (se 1 (by rfl) ⟨3982931, by rfl⟩ : syracuseStep 5310575 = 7965863) B7965863
theorem B2361455 : Blo 1572484 2361455 := bstep (se 1 (by rfl) ⟨1771091, by rfl⟩ : syracuseStep 2361455 = 3542183) B3542183
theorem B2361551 : Blo 1572484 2361551 := bstep (se 1 (by rfl) ⟨1771163, by rfl⟩ : syracuseStep 2361551 = 3542327) B3542327
theorem B51046631 : Blo 1572484 51046631 := bstep (se 1 (by rfl) ⟨38284973, by rfl⟩ : syracuseStep 51046631 = 76569947) B76569947
theorem B2361671 : Blo 1572484 2361671 := bstep (se 1 (by rfl) ⟨1771253, by rfl⟩ : syracuseStep 2361671 = 3542507) B3542507
theorem B3189223 : Blo 1572484 3189223 := bstep (se 1 (by rfl) ⟨2391917, by rfl⟩ : syracuseStep 3189223 = 4783835) B4783835
theorem B5974823 : Blo 1572484 5974823 := bstep (se 1 (by rfl) ⟨4481117, by rfl⟩ : syracuseStep 5974823 = 8962235) B8962235
theorem B3541967 : Blo 1572484 3541967 := bstep (se 1 (by rfl) ⟨2656475, by rfl⟩ : syracuseStep 3541967 = 5312951) B5312951
theorem B3984623 : Blo 1572484 3984623 := bstep (se 1 (by rfl) ⟨2988467, by rfl⟩ : syracuseStep 3984623 = 5976935) B5976935
theorem B43674869 : Blo 1572484 43674869 := bstep (se 5 (by rfl) ⟨2047259, by rfl⟩ : syracuseStep 43674869 = 4094519) B4094519
theorem B459165023 : Blo 1572484 459165023 := bstep (se 1 (by rfl) ⟨344373767, by rfl⟩ : syracuseStep 459165023 = 688747535) B688747535
theorem B207023849 : Blo 1572484 207023849 := bstep (se 2 (by rfl) ⟨77633943, by rfl⟩ : syracuseStep 207023849 = 155267887) B155267887
theorem B883503713 : Blo 1572484 883503713 := bstep (se 2 (by rfl) ⟨331313892, by rfl⟩ : syracuseStep 883503713 = 662627785) B662627785
theorem B10080875 : Blo 1572484 10080875 := bstep (se 1 (by rfl) ⟨7560656, by rfl⟩ : syracuseStep 10080875 = 15121313) B15121313
theorem B54489773 : Blo 1572484 54489773 := bstep (se 3 (by rfl) ⟨10216832, by rfl⟩ : syracuseStep 54489773 = 20433665) B20433665
theorem B22688657 : Blo 1572484 22688657 := bstep (se 2 (by rfl) ⟨8508246, by rfl⟩ : syracuseStep 22688657 = 17016493) B17016493
theorem B27243425 : Blo 1572484 27243425 := bstep (se 2 (by rfl) ⟨10216284, by rfl⟩ : syracuseStep 27243425 = 20432569) B20432569
theorem B5043359 : Blo 1572484 5043359 := bstep (se 1 (by rfl) ⟨3782519, by rfl⟩ : syracuseStep 5043359 = 7565039) B7565039
theorem B3781819 : Blo 1572484 3781819 := bstep (se 1 (by rfl) ⟨2836364, by rfl⟩ : syracuseStep 3781819 = 5672729) B5672729
theorem B1573991 : Blo 1572484 1573991 := bstep (se 1 (by rfl) ⟨1180493, by rfl⟩ : syracuseStep 1573991 = 2360987) B2360987
theorem B1769467 : Blo 1572484 1769467 := bstep (se 1 (by rfl) ⟨1327100, by rfl⟩ : syracuseStep 1769467 = 2654201) B2654201
theorem B7559851 : Blo 1572484 7559851 := bstep (se 1 (by rfl) ⟨5669888, by rfl⟩ : syracuseStep 7559851 = 11339777) B11339777
theorem B5971103 : Blo 1572484 5971103 := bstep (se 1 (by rfl) ⟨4478327, by rfl⟩ : syracuseStep 5971103 = 8956655) B8956655
theorem B53124335 : Blo 1572484 53124335 := bstep (se 1 (by rfl) ⟨39843251, by rfl⟩ : syracuseStep 53124335 = 79686503) B79686503
theorem B3587375 : Blo 1572484 3587375 := bstep (se 1 (by rfl) ⟨2690531, by rfl⟩ : syracuseStep 3587375 = 5381063) B5381063
theorem B45342251 : Blo 1572484 45342251 := bstep (se 1 (by rfl) ⟨34006688, by rfl⟩ : syracuseStep 45342251 = 68013377) B68013377
theorem B6717167 : Blo 1572484 6717167 := bstep (se 1 (by rfl) ⟨5037875, by rfl⟩ : syracuseStep 6717167 = 10075751) B10075751
theorem B8503231 : Blo 1572484 8503231 := bstep (se 1 (by rfl) ⟨6377423, by rfl⟩ : syracuseStep 8503231 = 12754847) B12754847
theorem B2359271 : Blo 1572484 2359271 := bstep (se 1 (by rfl) ⟨1769453, by rfl⟩ : syracuseStep 2359271 = 3538907) B3538907
theorem B1769503 : Blo 1572484 1769503 := bstep (se 1 (by rfl) ⟨1327127, by rfl⟩ : syracuseStep 1769503 = 2654255) B2654255
theorem B2359655 : Blo 1572484 2359655 := bstep (se 1 (by rfl) ⟨1769741, by rfl⟩ : syracuseStep 2359655 = 3539483) B3539483
theorem B5308955 : Blo 1572484 5308955 := bstep (se 1 (by rfl) ⟨3981716, by rfl⟩ : syracuseStep 5308955 = 7963433) B7963433
theorem B2359967 : Blo 1572484 2359967 := bstep (se 1 (by rfl) ⟨1769975, by rfl⟩ : syracuseStep 2359967 = 3539951) B3539951
theorem B2360303 : Blo 1572484 2360303 := bstep (se 1 (by rfl) ⟨1770227, by rfl⟩ : syracuseStep 2360303 = 3540455) B3540455
theorem B2360351 : Blo 1572484 2360351 := bstep (se 1 (by rfl) ⟨1770263, by rfl⟩ : syracuseStep 2360351 = 3540527) B3540527
theorem B2360441 : Blo 1572484 2360441 := bstep (se 2 (by rfl) ⟨885165, by rfl⟩ : syracuseStep 2360441 = 1770331) B1770331
theorem B1574143 : Blo 1572484 1574143 := bstep (se 1 (by rfl) ⟨1180607, by rfl⟩ : syracuseStep 1574143 = 2361215) B2361215
theorem B1574247 : Blo 1572484 1574247 := bstep (se 1 (by rfl) ⟨1180685, by rfl⟩ : syracuseStep 1574247 = 2361371) B2361371
theorem B3540383 : Blo 1572484 3540383 := bstep (se 1 (by rfl) ⟨2655287, by rfl⟩ : syracuseStep 3540383 = 5310575) B5310575
theorem B1574303 : Blo 1572484 1574303 := bstep (se 1 (by rfl) ⟨1180727, by rfl⟩ : syracuseStep 1574303 = 2361455) B2361455
theorem B1574367 : Blo 1572484 1574367 := bstep (se 1 (by rfl) ⟨1180775, by rfl⟩ : syracuseStep 1574367 = 2361551) B2361551
theorem B34031087 : Blo 1572484 34031087 := bstep (se 1 (by rfl) ⟨25523315, by rfl⟩ : syracuseStep 34031087 = 51046631) B51046631
theorem B1574447 : Blo 1572484 1574447 := bstep (se 1 (by rfl) ⟨1180835, by rfl⟩ : syracuseStep 1574447 = 2361671) B2361671
theorem B3983215 : Blo 1572484 3983215 := bstep (se 1 (by rfl) ⟨2987411, by rfl⟩ : syracuseStep 3983215 = 5974823) B5974823
theorem B2361311 : Blo 1572484 2361311 := bstep (se 1 (by rfl) ⟨1770983, by rfl⟩ : syracuseStep 2361311 = 3541967) B3541967
theorem B35416223 : Blo 1572484 35416223 := bstep (se 1 (by rfl) ⟨26562167, by rfl⟩ : syracuseStep 35416223 = 53124335) B53124335
theorem B2656415 : Blo 1572484 2656415 := bstep (se 1 (by rfl) ⟨1992311, by rfl⟩ : syracuseStep 2656415 = 3984623) B3984623
theorem B29116579 : Blo 1572484 29116579 := bstep (se 1 (by rfl) ⟨21837434, by rfl⟩ : syracuseStep 29116579 = 43674869) B43674869
theorem B72649133 : Blo 1572484 72649133 := bstep (se 3 (by rfl) ⟨13621712, by rfl⟩ : syracuseStep 72649133 = 27243425) B27243425
theorem B17009189 : Blo 1572484 17009189 := bstep (se 4 (by rfl) ⟨1594611, by rfl⟩ : syracuseStep 17009189 = 3189223) B3189223
theorem B6720583 : Blo 1572484 6720583 := bstep (se 1 (by rfl) ⟨5040437, by rfl⟩ : syracuseStep 6720583 = 10080875) B10080875
theorem B2239591 : Blo 1572484 2239591 := bstep (se 1 (by rfl) ⟨1679693, by rfl⟩ : syracuseStep 2239591 = 3359387) B3359387
theorem B36326515 : Blo 1572484 36326515 := bstep (se 1 (by rfl) ⟨27244886, by rfl⟩ : syracuseStep 36326515 = 54489773) B54489773
theorem B15125771 : Blo 1572484 15125771 := bstep (se 1 (by rfl) ⟨11344328, by rfl⟩ : syracuseStep 15125771 = 22688657) B22688657
theorem B3362239 : Blo 1572484 3362239 := bstep (se 1 (by rfl) ⟨2521679, by rfl⟩ : syracuseStep 3362239 = 5043359) B5043359
theorem B10079801 : Blo 1572484 10079801 := bstep (se 2 (by rfl) ⟨3779925, by rfl⟩ : syracuseStep 10079801 = 7559851) B7559851
theorem B5042425 : Blo 1572484 5042425 := bstep (se 2 (by rfl) ⟨1890909, by rfl⟩ : syracuseStep 5042425 = 3781819) B3781819
theorem B138015899 : Blo 1572484 138015899 := bstep (se 1 (by rfl) ⟨103511924, by rfl⟩ : syracuseStep 138015899 = 207023849) B207023849
theorem B4478111 : Blo 1572484 4478111 := bstep (se 1 (by rfl) ⟨3358583, by rfl⟩ : syracuseStep 4478111 = 6717167) B6717167
theorem B34035065 : Blo 1572484 34035065 := bstep (se 2 (by rfl) ⟨12763149, by rfl⟩ : syracuseStep 34035065 = 25526299) B25526299
theorem B589002475 : Blo 1572484 589002475 := bstep (se 1 (by rfl) ⟨441751856, by rfl⟩ : syracuseStep 589002475 = 883503713) B883503713
theorem B9566333 : Blo 1572484 9566333 := bstep (se 3 (by rfl) ⟨1793687, by rfl⟩ : syracuseStep 9566333 = 3587375) B3587375
theorem B7559351 : Blo 1572484 7559351 := bstep (se 1 (by rfl) ⟨5669513, by rfl⟩ : syracuseStep 7559351 = 11339027) B11339027
theorem B8181971 : Blo 1572484 8181971 := bstep (se 1 (by rfl) ⟨6136478, by rfl⟩ : syracuseStep 8181971 = 12272957) B12272957
theorem B11950739 : Blo 1572484 11950739 := bstep (se 1 (by rfl) ⟨8963054, by rfl⟩ : syracuseStep 11950739 = 17926109) B17926109
theorem B3980735 : Blo 1572484 3980735 := bstep (se 1 (by rfl) ⟨2985551, by rfl⟩ : syracuseStep 3980735 = 5971103) B5971103
theorem B306110015 : Blo 1572484 306110015 := bstep (se 1 (by rfl) ⟨229582511, by rfl⟩ : syracuseStep 306110015 = 459165023) B459165023
theorem B30228167 : Blo 1572484 30228167 := bstep (se 1 (by rfl) ⟨22671125, by rfl⟩ : syracuseStep 30228167 = 45342251) B45342251
theorem B11337641 : Blo 1572484 11337641 := bstep (se 2 (by rfl) ⟨4251615, by rfl⟩ : syracuseStep 11337641 = 8503231) B8503231
theorem B2359289 : Blo 1572484 2359289 := bstep (se 2 (by rfl) ⟨884733, by rfl⟩ : syracuseStep 2359289 = 1769467) B1769467
theorem B1572847 : Blo 1572484 1572847 := bstep (se 1 (by rfl) ⟨1179635, by rfl⟩ : syracuseStep 1572847 = 2359271) B2359271
theorem B2359337 : Blo 1572484 2359337 := bstep (se 2 (by rfl) ⟨884751, by rfl⟩ : syracuseStep 2359337 = 1769503) B1769503
theorem B38822105 : Blo 1572484 38822105 := bstep (se 2 (by rfl) ⟨14558289, by rfl⟩ : syracuseStep 38822105 = 29116579) B29116579
theorem B1573103 : Blo 1572484 1573103 := bstep (se 1 (by rfl) ⟨1179827, by rfl⟩ : syracuseStep 1573103 = 2359655) B2359655
theorem B3539303 : Blo 1572484 3539303 := bstep (se 1 (by rfl) ⟨2654477, by rfl⟩ : syracuseStep 3539303 = 5308955) B5308955
theorem B1573311 : Blo 1572484 1573311 := bstep (se 1 (by rfl) ⟨1179983, by rfl⟩ : syracuseStep 1573311 = 2359967) B2359967
theorem B1573535 : Blo 1572484 1573535 := bstep (se 1 (by rfl) ⟨1180151, by rfl⟩ : syracuseStep 1573535 = 2360303) B2360303
theorem B1573567 : Blo 1572484 1573567 := bstep (se 1 (by rfl) ⟨1180175, by rfl⟩ : syracuseStep 1573567 = 2360351) B2360351
theorem B1573627 : Blo 1572484 1573627 := bstep (se 1 (by rfl) ⟨1180220, by rfl⟩ : syracuseStep 1573627 = 2360441) B2360441
theorem B2360255 : Blo 1572484 2360255 := bstep (se 1 (by rfl) ⟨1770191, by rfl⟩ : syracuseStep 2360255 = 3540383) B3540383
theorem B1574207 : Blo 1572484 1574207 := bstep (se 1 (by rfl) ⟨1180655, by rfl⟩ : syracuseStep 1574207 = 2361311) B2361311
theorem B23610815 : Blo 1572484 23610815 := bstep (se 1 (by rfl) ⟨17708111, by rfl⟩ : syracuseStep 23610815 = 35416223) B35416223
theorem B1770943 : Blo 1572484 1770943 := bstep (se 1 (by rfl) ⟨1328207, by rfl⟩ : syracuseStep 1770943 = 2656415) B2656415
theorem B5039567 : Blo 1572484 5039567 := bstep (se 1 (by rfl) ⟨3779675, by rfl⟩ : syracuseStep 5039567 = 7559351) B7559351
theorem B48432755 : Blo 1572484 48432755 := bstep (se 1 (by rfl) ⟨36324566, by rfl⟩ : syracuseStep 48432755 = 72649133) B72649133
theorem B11339459 : Blo 1572484 11339459 := bstep (se 1 (by rfl) ⟨8504594, by rfl⟩ : syracuseStep 11339459 = 17009189) B17009189
theorem B785336633 : Blo 1572484 785336633 := bstep (se 2 (by rfl) ⟨294501237, by rfl⟩ : syracuseStep 785336633 = 589002475) B589002475
theorem B6719867 : Blo 1572484 6719867 := bstep (se 1 (by rfl) ⟨5039900, by rfl⟩ : syracuseStep 6719867 = 10079801) B10079801
theorem B204073343 : Blo 1572484 204073343 := bstep (se 1 (by rfl) ⟨153055007, by rfl⟩ : syracuseStep 204073343 = 306110015) B306110015
theorem B5310953 : Blo 1572484 5310953 := bstep (se 2 (by rfl) ⟨1991607, by rfl⟩ : syracuseStep 5310953 = 3983215) B3983215
theorem B2985407 : Blo 1572484 2985407 := bstep (se 1 (by rfl) ⟨2239055, by rfl⟩ : syracuseStep 2985407 = 4478111) B4478111
theorem B22687391 : Blo 1572484 22687391 := bstep (se 1 (by rfl) ⟨17015543, by rfl⟩ : syracuseStep 22687391 = 34031087) B34031087
theorem B6377555 : Blo 1572484 6377555 := bstep (se 1 (by rfl) ⟨4783166, by rfl⟩ : syracuseStep 6377555 = 9566333) B9566333
theorem B2986121 : Blo 1572484 2986121 := bstep (se 2 (by rfl) ⟨1119795, by rfl⟩ : syracuseStep 2986121 = 2239591) B2239591
theorem B48435353 : Blo 1572484 48435353 := bstep (se 2 (by rfl) ⟨18163257, by rfl⟩ : syracuseStep 48435353 = 36326515) B36326515
theorem B7967159 : Blo 1572484 7967159 := bstep (se 1 (by rfl) ⟨5975369, by rfl⟩ : syracuseStep 7967159 = 11950739) B11950739
theorem B7558427 : Blo 1572484 7558427 := bstep (se 1 (by rfl) ⟨5668820, by rfl⟩ : syracuseStep 7558427 = 11337641) B11337641
theorem B6723233 : Blo 1572484 6723233 := bstep (se 2 (by rfl) ⟨2521212, by rfl⟩ : syracuseStep 6723233 = 5042425) B5042425
theorem B92010599 : Blo 1572484 92010599 := bstep (se 1 (by rfl) ⟨69007949, by rfl⟩ : syracuseStep 92010599 = 138015899) B138015899
theorem B22690043 : Blo 1572484 22690043 := bstep (se 1 (by rfl) ⟨17017532, by rfl⟩ : syracuseStep 22690043 = 34035065) B34035065
theorem B8960777 : Blo 1572484 8960777 := bstep (se 2 (by rfl) ⟨3360291, by rfl⟩ : syracuseStep 8960777 = 6720583) B6720583
theorem B5454647 : Blo 1572484 5454647 := bstep (se 1 (by rfl) ⟨4090985, by rfl⟩ : syracuseStep 5454647 = 8181971) B8181971
theorem B10083847 : Blo 1572484 10083847 := bstep (se 1 (by rfl) ⟨7562885, by rfl⟩ : syracuseStep 10083847 = 15125771) B15125771
theorem B2653823 : Blo 1572484 2653823 := bstep (se 1 (by rfl) ⟨1990367, by rfl⟩ : syracuseStep 2653823 = 3980735) B3980735
theorem B17931941 : Blo 1572484 17931941 := bstep (se 4 (by rfl) ⟨1681119, by rfl⟩ : syracuseStep 17931941 = 3362239) B3362239
theorem B20152111 : Blo 1572484 20152111 := bstep (se 1 (by rfl) ⟨15114083, by rfl⟩ : syracuseStep 20152111 = 30228167) B30228167
theorem B1572859 : Blo 1572484 1572859 := bstep (se 1 (by rfl) ⟨1179644, by rfl⟩ : syracuseStep 1572859 = 2359289) B2359289
theorem B1572891 : Blo 1572484 1572891 := bstep (se 1 (by rfl) ⟨1179668, by rfl⟩ : syracuseStep 1572891 = 2359337) B2359337
theorem B4251703 : Blo 1572484 4251703 := bstep (se 1 (by rfl) ⟨3188777, by rfl⟩ : syracuseStep 4251703 = 6377555) B6377555
theorem B1990747 : Blo 1572484 1990747 := bstep (se 1 (by rfl) ⟨1493060, by rfl⟩ : syracuseStep 1990747 = 2986121) B2986121
theorem B2359535 : Blo 1572484 2359535 := bstep (se 1 (by rfl) ⟨1769651, by rfl⟩ : syracuseStep 2359535 = 3539303) B3539303
theorem B1573503 : Blo 1572484 1573503 := bstep (se 1 (by rfl) ⟨1180127, by rfl⟩ : syracuseStep 1573503 = 2360255) B2360255
theorem B5038951 : Blo 1572484 5038951 := bstep (se 1 (by rfl) ⟨3779213, by rfl⟩ : syracuseStep 5038951 = 7558427) B7558427
theorem B3359711 : Blo 1572484 3359711 := bstep (se 1 (by rfl) ⟨2519783, by rfl⟩ : syracuseStep 3359711 = 5039567) B5039567
theorem B4482155 : Blo 1572484 4482155 := bstep (se 1 (by rfl) ⟨3361616, by rfl⟩ : syracuseStep 4482155 = 6723233) B6723233
theorem B3540635 : Blo 1572484 3540635 := bstep (se 1 (by rfl) ⟨2655476, by rfl⟩ : syracuseStep 3540635 = 5310953) B5310953
theorem B5973851 : Blo 1572484 5973851 := bstep (se 1 (by rfl) ⟨4480388, by rfl⟩ : syracuseStep 5973851 = 8960777) B8960777
theorem B2361257 : Blo 1572484 2361257 := bstep (se 2 (by rfl) ⟨885471, by rfl⟩ : syracuseStep 2361257 = 1770943) B1770943
theorem B13445129 : Blo 1572484 13445129 := bstep (se 2 (by rfl) ⟨5041923, by rfl⟩ : syracuseStep 13445129 = 10083847) B10083847
theorem B15124927 : Blo 1572484 15124927 := bstep (se 1 (by rfl) ⟨11343695, by rfl⟩ : syracuseStep 15124927 = 22687391) B22687391
theorem B11954627 : Blo 1572484 11954627 := bstep (se 1 (by rfl) ⟨8965970, by rfl⟩ : syracuseStep 11954627 = 17931941) B17931941
theorem B25881403 : Blo 1572484 25881403 := bstep (se 1 (by rfl) ⟨19411052, by rfl⟩ : syracuseStep 25881403 = 38822105) B38822105
theorem B5311439 : Blo 1572484 5311439 := bstep (se 1 (by rfl) ⟨3983579, by rfl⟩ : syracuseStep 5311439 = 7967159) B7967159
theorem B15740543 : Blo 1572484 15740543 := bstep (se 1 (by rfl) ⟨11805407, by rfl⟩ : syracuseStep 15740543 = 23610815) B23610815
theorem B32288503 : Blo 1572484 32288503 := bstep (se 1 (by rfl) ⟨24216377, by rfl⟩ : syracuseStep 32288503 = 48432755) B48432755
theorem B15126695 : Blo 1572484 15126695 := bstep (se 1 (by rfl) ⟨11345021, by rfl⟩ : syracuseStep 15126695 = 22690043) B22690043
theorem B136048895 : Blo 1572484 136048895 := bstep (se 1 (by rfl) ⟨102036671, by rfl⟩ : syracuseStep 136048895 = 204073343) B204073343
theorem B32290235 : Blo 1572484 32290235 := bstep (se 1 (by rfl) ⟨24217676, by rfl⟩ : syracuseStep 32290235 = 48435353) B48435353
theorem B7559639 : Blo 1572484 7559639 := bstep (se 1 (by rfl) ⟨5669729, by rfl⟩ : syracuseStep 7559639 = 11339459) B11339459
theorem B61340399 : Blo 1572484 61340399 := bstep (se 1 (by rfl) ⟨46005299, by rfl⟩ : syracuseStep 61340399 = 92010599) B92010599
theorem B523557755 : Blo 1572484 523557755 := bstep (se 1 (by rfl) ⟨392668316, by rfl⟩ : syracuseStep 523557755 = 785336633) B785336633
theorem B4479911 : Blo 1572484 4479911 := bstep (se 1 (by rfl) ⟨3359933, by rfl⟩ : syracuseStep 4479911 = 6719867) B6719867
theorem B3636431 : Blo 1572484 3636431 := bstep (se 1 (by rfl) ⟨2727323, by rfl⟩ : syracuseStep 3636431 = 5454647) B5454647
theorem B1990271 : Blo 1572484 1990271 := bstep (se 1 (by rfl) ⟨1492703, by rfl⟩ : syracuseStep 1990271 = 2985407) B2985407
theorem B26869481 : Blo 1572484 26869481 := bstep (se 2 (by rfl) ⟨10076055, by rfl⟩ : syracuseStep 26869481 = 20152111) B20152111
theorem B1769215 : Blo 1572484 1769215 := bstep (se 1 (by rfl) ⟨1326911, by rfl⟩ : syracuseStep 1769215 = 2653823) B2653823
theorem B5668937 : Blo 1572484 5668937 := bstep (se 2 (by rfl) ⟨2125851, by rfl⟩ : syracuseStep 5668937 = 4251703) B4251703
theorem B10084463 : Blo 1572484 10084463 := bstep (se 1 (by rfl) ⟨7563347, by rfl⟩ : syracuseStep 10084463 = 15126695) B15126695
theorem B2654329 : Blo 1572484 2654329 := bstep (se 2 (by rfl) ⟨995373, by rfl⟩ : syracuseStep 2654329 = 1990747) B1990747
theorem B1573023 : Blo 1572484 1573023 := bstep (se 1 (by rfl) ⟨1179767, by rfl⟩ : syracuseStep 1573023 = 2359535) B2359535
theorem B2360423 : Blo 1572484 2360423 := bstep (se 1 (by rfl) ⟨1770317, by rfl⟩ : syracuseStep 2360423 = 3540635) B3540635
theorem B6718601 : Blo 1572484 6718601 := bstep (se 2 (by rfl) ⟨2519475, by rfl⟩ : syracuseStep 6718601 = 5038951) B5038951
theorem B3982567 : Blo 1572484 3982567 := bstep (se 1 (by rfl) ⟨2986925, by rfl⟩ : syracuseStep 3982567 = 5973851) B5973851
theorem B1574171 : Blo 1572484 1574171 := bstep (se 1 (by rfl) ⟨1180628, by rfl⟩ : syracuseStep 1574171 = 2361257) B2361257
theorem B8963419 : Blo 1572484 8963419 := bstep (se 1 (by rfl) ⟨6722564, by rfl⟩ : syracuseStep 8963419 = 13445129) B13445129
theorem B5039759 : Blo 1572484 5039759 := bstep (se 1 (by rfl) ⟨3779819, by rfl⟩ : syracuseStep 5039759 = 7559639) B7559639
theorem B349038503 : Blo 1572484 349038503 := bstep (se 1 (by rfl) ⟨261778877, by rfl⟩ : syracuseStep 349038503 = 523557755) B523557755
theorem B3540959 : Blo 1572484 3540959 := bstep (se 1 (by rfl) ⟨2655719, by rfl⟩ : syracuseStep 3540959 = 5311439) B5311439
theorem B43051337 : Blo 1572484 43051337 := bstep (se 2 (by rfl) ⟨16144251, by rfl⟩ : syracuseStep 43051337 = 32288503) B32288503
theorem B2239807 : Blo 1572484 2239807 := bstep (se 1 (by rfl) ⟨1679855, by rfl⟩ : syracuseStep 2239807 = 3359711) B3359711
theorem B34508537 : Blo 1572484 34508537 := bstep (se 2 (by rfl) ⟨12940701, by rfl⟩ : syracuseStep 34508537 = 25881403) B25881403
theorem B2986607 : Blo 1572484 2986607 := bstep (se 1 (by rfl) ⟨2239955, by rfl⟩ : syracuseStep 2986607 = 4479911) B4479911
theorem B17912987 : Blo 1572484 17912987 := bstep (se 1 (by rfl) ⟨13434740, by rfl⟩ : syracuseStep 17912987 = 26869481) B26869481
theorem B90699263 : Blo 1572484 90699263 := bstep (se 1 (by rfl) ⟨68024447, by rfl⟩ : syracuseStep 90699263 = 136048895) B136048895
theorem B20166569 : Blo 1572484 20166569 := bstep (se 2 (by rfl) ⟨7562463, by rfl⟩ : syracuseStep 20166569 = 15124927) B15124927
theorem B2988103 : Blo 1572484 2988103 := bstep (se 1 (by rfl) ⟨2241077, by rfl⟩ : syracuseStep 2988103 = 4482155) B4482155
theorem B21526823 : Blo 1572484 21526823 := bstep (se 1 (by rfl) ⟨16145117, by rfl⟩ : syracuseStep 21526823 = 32290235) B32290235
theorem B7969751 : Blo 1572484 7969751 := bstep (se 1 (by rfl) ⟨5977313, by rfl⟩ : syracuseStep 7969751 = 11954627) B11954627
theorem B5307389 : Blo 1572484 5307389 := bstep (se 3 (by rfl) ⟨995135, by rfl⟩ : syracuseStep 5307389 = 1990271) B1990271
theorem B40893599 : Blo 1572484 40893599 := bstep (se 1 (by rfl) ⟨30670199, by rfl⟩ : syracuseStep 40893599 = 61340399) B61340399
theorem B2424287 : Blo 1572484 2424287 := bstep (se 1 (by rfl) ⟨1818215, by rfl⟩ : syracuseStep 2424287 = 3636431) B3636431
theorem B2358953 : Blo 1572484 2358953 := bstep (se 2 (by rfl) ⟨884607, by rfl⟩ : syracuseStep 2358953 = 1769215) B1769215
theorem B10493695 : Blo 1572484 10493695 := bstep (se 1 (by rfl) ⟨7870271, by rfl⟩ : syracuseStep 10493695 = 15740543) B15740543
theorem B3539105 : Blo 1572484 3539105 := bstep (se 2 (by rfl) ⟨1327164, by rfl⟩ : syracuseStep 3539105 = 2654329) B2654329
theorem B1991071 : Blo 1572484 1991071 := bstep (se 1 (by rfl) ⟨1493303, by rfl⟩ : syracuseStep 1991071 = 2986607) B2986607
theorem B1573615 : Blo 1572484 1573615 := bstep (se 1 (by rfl) ⟨1180211, by rfl⟩ : syracuseStep 1573615 = 2360423) B2360423
theorem B60466175 : Blo 1572484 60466175 := bstep (se 1 (by rfl) ⟨45349631, by rfl⟩ : syracuseStep 60466175 = 90699263) B90699263
theorem B6464765 : Blo 1572484 6464765 := bstep (se 3 (by rfl) ⟨1212143, by rfl⟩ : syracuseStep 6464765 = 2424287) B2424287
theorem B13444379 : Blo 1572484 13444379 := bstep (se 1 (by rfl) ⟨10083284, by rfl⟩ : syracuseStep 13444379 = 20166569) B20166569
theorem B2360639 : Blo 1572484 2360639 := bstep (se 1 (by rfl) ⟨1770479, by rfl⟩ : syracuseStep 2360639 = 3540959) B3540959
theorem B5310089 : Blo 1572484 5310089 := bstep (se 2 (by rfl) ⟨1991283, by rfl⟩ : syracuseStep 5310089 = 3982567) B3982567
theorem B23005691 : Blo 1572484 23005691 := bstep (se 1 (by rfl) ⟨17254268, by rfl⟩ : syracuseStep 23005691 = 34508537) B34508537
theorem B3779291 : Blo 1572484 3779291 := bstep (se 1 (by rfl) ⟨2834468, by rfl⟩ : syracuseStep 3779291 = 5668937) B5668937
theorem B3984137 : Blo 1572484 3984137 := bstep (se 2 (by rfl) ⟨1494051, by rfl⟩ : syracuseStep 3984137 = 2988103) B2988103
theorem B28700891 : Blo 1572484 28700891 := bstep (se 1 (by rfl) ⟨21525668, by rfl⟩ : syracuseStep 28700891 = 43051337) B43051337
theorem B13439357 : Blo 1572484 13439357 := bstep (se 3 (by rfl) ⟨2519879, by rfl⟩ : syracuseStep 13439357 = 5039759) B5039759
theorem B2986409 : Blo 1572484 2986409 := bstep (se 2 (by rfl) ⟨1119903, by rfl⟩ : syracuseStep 2986409 = 2239807) B2239807
theorem B5313167 : Blo 1572484 5313167 := bstep (se 1 (by rfl) ⟨3984875, by rfl⟩ : syracuseStep 5313167 = 7969751) B7969751
theorem B6722975 : Blo 1572484 6722975 := bstep (se 1 (by rfl) ⟨5042231, by rfl⟩ : syracuseStep 6722975 = 10084463) B10084463
theorem B109049597 : Blo 1572484 109049597 := bstep (se 3 (by rfl) ⟨20446799, by rfl⟩ : syracuseStep 109049597 = 40893599) B40893599
theorem B4479067 : Blo 1572484 4479067 := bstep (se 1 (by rfl) ⟨3359300, by rfl⟩ : syracuseStep 4479067 = 6718601) B6718601
theorem B11941991 : Blo 1572484 11941991 := bstep (se 1 (by rfl) ⟨8956493, by rfl⟩ : syracuseStep 11941991 = 17912987) B17912987
theorem B232692335 : Blo 1572484 232692335 := bstep (se 1 (by rfl) ⟨174519251, by rfl⟩ : syracuseStep 232692335 = 349038503) B349038503
theorem B55966373 : Blo 1572484 55966373 := bstep (se 4 (by rfl) ⟨5246847, by rfl⟩ : syracuseStep 55966373 = 10493695) B10493695
theorem B14351215 : Blo 1572484 14351215 := bstep (se 1 (by rfl) ⟨10763411, by rfl⟩ : syracuseStep 14351215 = 21526823) B21526823
theorem B11951225 : Blo 1572484 11951225 := bstep (se 2 (by rfl) ⟨4481709, by rfl⟩ : syracuseStep 11951225 = 8963419) B8963419
theorem B3538259 : Blo 1572484 3538259 := bstep (se 1 (by rfl) ⟨2653694, by rfl⟩ : syracuseStep 3538259 = 5307389) B5307389
theorem B1572635 : Blo 1572484 1572635 := bstep (se 1 (by rfl) ⟨1179476, by rfl⟩ : syracuseStep 1572635 = 2358953) B2358953
theorem B2359403 : Blo 1572484 2359403 := bstep (se 1 (by rfl) ⟨1769552, by rfl⟩ : syracuseStep 2359403 = 3539105) B3539105
theorem B5972089 : Blo 1572484 5972089 := bstep (se 2 (by rfl) ⟨2239533, by rfl⟩ : syracuseStep 5972089 = 4479067) B4479067
theorem B2654761 : Blo 1572484 2654761 := bstep (se 2 (by rfl) ⟨995535, by rfl⟩ : syracuseStep 2654761 = 1991071) B1991071
theorem B4309843 : Blo 1572484 4309843 := bstep (se 1 (by rfl) ⟨3232382, by rfl⟩ : syracuseStep 4309843 = 6464765) B6464765
theorem B8962919 : Blo 1572484 8962919 := bstep (se 1 (by rfl) ⟨6722189, by rfl⟩ : syracuseStep 8962919 = 13444379) B13444379
theorem B1573759 : Blo 1572484 1573759 := bstep (se 1 (by rfl) ⟨1180319, by rfl⟩ : syracuseStep 1573759 = 2360639) B2360639
theorem B4481983 : Blo 1572484 4481983 := bstep (se 1 (by rfl) ⟨3361487, by rfl⟩ : syracuseStep 4481983 = 6722975) B6722975
theorem B3540059 : Blo 1572484 3540059 := bstep (se 1 (by rfl) ⟨2655044, by rfl⟩ : syracuseStep 3540059 = 5310089) B5310089
theorem B7963757 : Blo 1572484 7963757 := bstep (se 3 (by rfl) ⟨1493204, by rfl⟩ : syracuseStep 7963757 = 2986409) B2986409
theorem B15337127 : Blo 1572484 15337127 := bstep (se 1 (by rfl) ⟨11502845, by rfl⟩ : syracuseStep 15337127 = 23005691) B23005691
theorem B2656091 : Blo 1572484 2656091 := bstep (se 1 (by rfl) ⟨1992068, by rfl⟩ : syracuseStep 2656091 = 3984137) B3984137
theorem B3542111 : Blo 1572484 3542111 := bstep (se 1 (by rfl) ⟨2656583, by rfl⟩ : syracuseStep 3542111 = 5313167) B5313167
theorem B72699731 : Blo 1572484 72699731 := bstep (se 1 (by rfl) ⟨54524798, by rfl⟩ : syracuseStep 72699731 = 109049597) B109049597
theorem B155128223 : Blo 1572484 155128223 := bstep (se 1 (by rfl) ⟨116346167, by rfl⟩ : syracuseStep 155128223 = 232692335) B232692335
theorem B37310915 : Blo 1572484 37310915 := bstep (se 1 (by rfl) ⟨27983186, by rfl⟩ : syracuseStep 37310915 = 55966373) B55966373
theorem B2519527 : Blo 1572484 2519527 := bstep (se 1 (by rfl) ⟨1889645, by rfl⟩ : syracuseStep 2519527 = 3779291) B3779291
theorem B7967483 : Blo 1572484 7967483 := bstep (se 1 (by rfl) ⟨5975612, by rfl⟩ : syracuseStep 7967483 = 11951225) B11951225
theorem B19133927 : Blo 1572484 19133927 := bstep (se 1 (by rfl) ⟨14350445, by rfl⟩ : syracuseStep 19133927 = 28700891) B28700891
theorem B8959571 : Blo 1572484 8959571 := bstep (se 1 (by rfl) ⟨6719678, by rfl⟩ : syracuseStep 8959571 = 13439357) B13439357
theorem B40310783 : Blo 1572484 40310783 := bstep (se 1 (by rfl) ⟨30233087, by rfl⟩ : syracuseStep 40310783 = 60466175) B60466175
theorem B19134953 : Blo 1572484 19134953 := bstep (se 2 (by rfl) ⟨7175607, by rfl⟩ : syracuseStep 19134953 = 14351215) B14351215
theorem B7961327 : Blo 1572484 7961327 := bstep (se 1 (by rfl) ⟨5970995, by rfl⟩ : syracuseStep 7961327 = 11941991) B11941991
theorem B2358839 : Blo 1572484 2358839 := bstep (se 1 (by rfl) ⟨1769129, by rfl⟩ : syracuseStep 2358839 = 3538259) B3538259
theorem B1572935 : Blo 1572484 1572935 := bstep (se 1 (by rfl) ⟨1179701, by rfl⟩ : syracuseStep 1572935 = 2359403) B2359403
theorem B7962785 : Blo 1572484 7962785 := bstep (se 2 (by rfl) ⟨2986044, by rfl⟩ : syracuseStep 7962785 = 5972089) B5972089
theorem B3359369 : Blo 1572484 3359369 := bstep (se 2 (by rfl) ⟨1259763, by rfl⟩ : syracuseStep 3359369 = 2519527) B2519527
theorem B3539681 : Blo 1572484 3539681 := bstep (se 2 (by rfl) ⟨1327380, by rfl⟩ : syracuseStep 3539681 = 2654761) B2654761
theorem B2360039 : Blo 1572484 2360039 := bstep (se 1 (by rfl) ⟨1770029, by rfl⟩ : syracuseStep 2360039 = 3540059) B3540059
theorem B5309171 : Blo 1572484 5309171 := bstep (se 1 (by rfl) ⟨3981878, by rfl⟩ : syracuseStep 5309171 = 7963757) B7963757
theorem B12755951 : Blo 1572484 12755951 := bstep (se 1 (by rfl) ⟨9566963, by rfl⟩ : syracuseStep 12755951 = 19133927) B19133927
theorem B5973047 : Blo 1572484 5973047 := bstep (se 1 (by rfl) ⟨4479785, by rfl⟩ : syracuseStep 5973047 = 8959571) B8959571
theorem B1770727 : Blo 1572484 1770727 := bstep (se 1 (by rfl) ⟨1328045, by rfl⟩ : syracuseStep 1770727 = 2656091) B2656091
theorem B12756635 : Blo 1572484 12756635 := bstep (se 1 (by rfl) ⟨9567476, by rfl⟩ : syracuseStep 12756635 = 19134953) B19134953
theorem B2361407 : Blo 1572484 2361407 := bstep (se 1 (by rfl) ⟨1771055, by rfl⟩ : syracuseStep 2361407 = 3542111) B3542111
theorem B48466487 : Blo 1572484 48466487 := bstep (se 1 (by rfl) ⟨36349865, by rfl⟩ : syracuseStep 48466487 = 72699731) B72699731
theorem B103418815 : Blo 1572484 103418815 := bstep (se 1 (by rfl) ⟨77564111, by rfl⟩ : syracuseStep 103418815 = 155128223) B155128223
theorem B24873943 : Blo 1572484 24873943 := bstep (se 1 (by rfl) ⟨18655457, by rfl⟩ : syracuseStep 24873943 = 37310915) B37310915
theorem B5311655 : Blo 1572484 5311655 := bstep (se 1 (by rfl) ⟨3983741, by rfl⟩ : syracuseStep 5311655 = 7967483) B7967483
theorem B5975279 : Blo 1572484 5975279 := bstep (se 1 (by rfl) ⟨4481459, by rfl⟩ : syracuseStep 5975279 = 8962919) B8962919
theorem B5746457 : Blo 1572484 5746457 := bstep (se 2 (by rfl) ⟨2154921, by rfl⟩ : syracuseStep 5746457 = 4309843) B4309843
theorem B5975977 : Blo 1572484 5975977 := bstep (se 2 (by rfl) ⟨2240991, by rfl⟩ : syracuseStep 5975977 = 4481983) B4481983
theorem B26873855 : Blo 1572484 26873855 := bstep (se 1 (by rfl) ⟨20155391, by rfl⟩ : syracuseStep 26873855 = 40310783) B40310783
theorem B40899005 : Blo 1572484 40899005 := bstep (se 3 (by rfl) ⟨7668563, by rfl⟩ : syracuseStep 40899005 = 15337127) B15337127
theorem B5307551 : Blo 1572484 5307551 := bstep (se 1 (by rfl) ⟨3980663, by rfl⟩ : syracuseStep 5307551 = 7961327) B7961327
theorem B1572559 : Blo 1572484 1572559 := bstep (se 1 (by rfl) ⟨1179419, by rfl⟩ : syracuseStep 1572559 = 2358839) B2358839
theorem B5308523 : Blo 1572484 5308523 := bstep (se 1 (by rfl) ⟨3981392, by rfl⟩ : syracuseStep 5308523 = 7962785) B7962785
theorem B2359787 : Blo 1572484 2359787 := bstep (se 1 (by rfl) ⟨1769840, by rfl⟩ : syracuseStep 2359787 = 3539681) B3539681
theorem B1573359 : Blo 1572484 1573359 := bstep (se 1 (by rfl) ⟨1180019, by rfl⟩ : syracuseStep 1573359 = 2360039) B2360039
theorem B3539447 : Blo 1572484 3539447 := bstep (se 1 (by rfl) ⟨2654585, by rfl⟩ : syracuseStep 3539447 = 5309171) B5309171
theorem B8503967 : Blo 1572484 8503967 := bstep (se 1 (by rfl) ⟨6377975, by rfl⟩ : syracuseStep 8503967 = 12755951) B12755951
theorem B3982031 : Blo 1572484 3982031 := bstep (se 1 (by rfl) ⟨2986523, by rfl⟩ : syracuseStep 3982031 = 5973047) B5973047
theorem B8504423 : Blo 1572484 8504423 := bstep (se 1 (by rfl) ⟨6378317, by rfl⟩ : syracuseStep 8504423 = 12756635) B12756635
theorem B1574271 : Blo 1572484 1574271 := bstep (se 1 (by rfl) ⟨1180703, by rfl⟩ : syracuseStep 1574271 = 2361407) B2361407
theorem B2360969 : Blo 1572484 2360969 := bstep (se 2 (by rfl) ⟨885363, by rfl⟩ : syracuseStep 2360969 = 1770727) B1770727
theorem B32310991 : Blo 1572484 32310991 := bstep (se 1 (by rfl) ⟨24233243, by rfl⟩ : syracuseStep 32310991 = 48466487) B48466487
theorem B3541103 : Blo 1572484 3541103 := bstep (se 1 (by rfl) ⟨2655827, by rfl⟩ : syracuseStep 3541103 = 5311655) B5311655
theorem B3983519 : Blo 1572484 3983519 := bstep (se 1 (by rfl) ⟨2987639, by rfl⟩ : syracuseStep 3983519 = 5975279) B5975279
theorem B17915903 : Blo 1572484 17915903 := bstep (se 1 (by rfl) ⟨13436927, by rfl⟩ : syracuseStep 17915903 = 26873855) B26873855
theorem B27266003 : Blo 1572484 27266003 := bstep (se 1 (by rfl) ⟨20449502, by rfl⟩ : syracuseStep 27266003 = 40899005) B40899005
theorem B2239579 : Blo 1572484 2239579 := bstep (se 1 (by rfl) ⟨1679684, by rfl⟩ : syracuseStep 2239579 = 3359369) B3359369
theorem B137891753 : Blo 1572484 137891753 := bstep (se 2 (by rfl) ⟨51709407, by rfl⟩ : syracuseStep 137891753 = 103418815) B103418815
theorem B33165257 : Blo 1572484 33165257 := bstep (se 2 (by rfl) ⟨12436971, by rfl⟩ : syracuseStep 33165257 = 24873943) B24873943
theorem B3830971 : Blo 1572484 3830971 := bstep (se 1 (by rfl) ⟨2873228, by rfl⟩ : syracuseStep 3830971 = 5746457) B5746457
theorem B7967969 : Blo 1572484 7967969 := bstep (se 2 (by rfl) ⟨2987988, by rfl⟩ : syracuseStep 7967969 = 5975977) B5975977
theorem B3538367 : Blo 1572484 3538367 := bstep (se 1 (by rfl) ⟨2653775, by rfl⟩ : syracuseStep 3538367 = 5307551) B5307551
theorem B3539015 : Blo 1572484 3539015 := bstep (se 1 (by rfl) ⟨2654261, by rfl⟩ : syracuseStep 3539015 = 5308523) B5308523
theorem B1573191 : Blo 1572484 1573191 := bstep (se 1 (by rfl) ⟨1179893, by rfl⟩ : syracuseStep 1573191 = 2359787) B2359787
theorem B2359631 : Blo 1572484 2359631 := bstep (se 1 (by rfl) ⟨1769723, by rfl⟩ : syracuseStep 2359631 = 3539447) B3539447
theorem B2654687 : Blo 1572484 2654687 := bstep (se 1 (by rfl) ⟨1991015, by rfl⟩ : syracuseStep 2654687 = 3982031) B3982031
theorem B11944421 : Blo 1572484 11944421 := bstep (se 4 (by rfl) ⟨1119789, by rfl⟩ : syracuseStep 11944421 = 2239579) B2239579
theorem B5669615 : Blo 1572484 5669615 := bstep (se 1 (by rfl) ⟨4252211, by rfl⟩ : syracuseStep 5669615 = 8504423) B8504423
theorem B1573979 : Blo 1572484 1573979 := bstep (se 1 (by rfl) ⟨1180484, by rfl⟩ : syracuseStep 1573979 = 2360969) B2360969
theorem B2360735 : Blo 1572484 2360735 := bstep (se 1 (by rfl) ⟨1770551, by rfl⟩ : syracuseStep 2360735 = 3541103) B3541103
theorem B2655679 : Blo 1572484 2655679 := bstep (se 1 (by rfl) ⟨1991759, by rfl⟩ : syracuseStep 2655679 = 3983519) B3983519
theorem B22677245 : Blo 1572484 22677245 := bstep (se 3 (by rfl) ⟨4251983, by rfl⟩ : syracuseStep 22677245 = 8503967) B8503967
theorem B5311979 : Blo 1572484 5311979 := bstep (se 1 (by rfl) ⟨3983984, by rfl⟩ : syracuseStep 5311979 = 7967969) B7967969
theorem B5107961 : Blo 1572484 5107961 := bstep (se 2 (by rfl) ⟨1915485, by rfl⟩ : syracuseStep 5107961 = 3830971) B3830971
theorem B11943935 : Blo 1572484 11943935 := bstep (se 1 (by rfl) ⟨8957951, by rfl⟩ : syracuseStep 11943935 = 17915903) B17915903
theorem B91927835 : Blo 1572484 91927835 := bstep (se 1 (by rfl) ⟨68945876, by rfl⟩ : syracuseStep 91927835 = 137891753) B137891753
theorem B18177335 : Blo 1572484 18177335 := bstep (se 1 (by rfl) ⟨13633001, by rfl⟩ : syracuseStep 18177335 = 27266003) B27266003
theorem B353762741 : Blo 1572484 353762741 := bstep (se 5 (by rfl) ⟨16582628, by rfl⟩ : syracuseStep 353762741 = 33165257) B33165257
theorem B43081321 : Blo 1572484 43081321 := bstep (se 2 (by rfl) ⟨16155495, by rfl⟩ : syracuseStep 43081321 = 32310991) B32310991
theorem B2358911 : Blo 1572484 2358911 := bstep (se 1 (by rfl) ⟨1769183, by rfl⟩ : syracuseStep 2358911 = 3538367) B3538367
theorem B2359343 : Blo 1572484 2359343 := bstep (se 1 (by rfl) ⟨1769507, by rfl⟩ : syracuseStep 2359343 = 3539015) B3539015
theorem B1573087 : Blo 1572484 1573087 := bstep (se 1 (by rfl) ⟨1179815, by rfl⟩ : syracuseStep 1573087 = 2359631) B2359631
theorem B1769791 : Blo 1572484 1769791 := bstep (se 1 (by rfl) ⟨1327343, by rfl⟩ : syracuseStep 1769791 = 2654687) B2654687
theorem B7962947 : Blo 1572484 7962947 := bstep (se 1 (by rfl) ⟨5972210, by rfl⟩ : syracuseStep 7962947 = 11944421) B11944421
theorem B61285223 : Blo 1572484 61285223 := bstep (se 1 (by rfl) ⟨45963917, by rfl⟩ : syracuseStep 61285223 = 91927835) B91927835
theorem B1573823 : Blo 1572484 1573823 := bstep (se 1 (by rfl) ⟨1180367, by rfl⟩ : syracuseStep 1573823 = 2360735) B2360735
theorem B3540905 : Blo 1572484 3540905 := bstep (se 2 (by rfl) ⟨1327839, by rfl⟩ : syracuseStep 3540905 = 2655679) B2655679
theorem B12118223 : Blo 1572484 12118223 := bstep (se 1 (by rfl) ⟨9088667, by rfl⟩ : syracuseStep 12118223 = 18177335) B18177335
theorem B235841827 : Blo 1572484 235841827 := bstep (se 1 (by rfl) ⟨176881370, by rfl⟩ : syracuseStep 235841827 = 353762741) B353762741
theorem B3541319 : Blo 1572484 3541319 := bstep (se 1 (by rfl) ⟨2655989, by rfl⟩ : syracuseStep 3541319 = 5311979) B5311979
theorem B7962623 : Blo 1572484 7962623 := bstep (se 1 (by rfl) ⟨5971967, by rfl⟩ : syracuseStep 7962623 = 11943935) B11943935
theorem B15118163 : Blo 1572484 15118163 := bstep (se 1 (by rfl) ⟨11338622, by rfl⟩ : syracuseStep 15118163 = 22677245) B22677245
theorem B15118973 : Blo 1572484 15118973 := bstep (se 3 (by rfl) ⟨2834807, by rfl⟩ : syracuseStep 15118973 = 5669615) B5669615
theorem B3405307 : Blo 1572484 3405307 := bstep (se 1 (by rfl) ⟨2553980, by rfl⟩ : syracuseStep 3405307 = 5107961) B5107961
theorem B57441761 : Blo 1572484 57441761 := bstep (se 2 (by rfl) ⟨21540660, by rfl⟩ : syracuseStep 57441761 = 43081321) B43081321
theorem B1572607 : Blo 1572484 1572607 := bstep (se 1 (by rfl) ⟨1179455, by rfl⟩ : syracuseStep 1572607 = 2358911) B2358911
theorem B1572895 : Blo 1572484 1572895 := bstep (se 1 (by rfl) ⟨1179671, by rfl⟩ : syracuseStep 1572895 = 2359343) B2359343
theorem B5308631 : Blo 1572484 5308631 := bstep (se 1 (by rfl) ⟨3981473, by rfl⟩ : syracuseStep 5308631 = 7962947) B7962947
theorem B2359721 : Blo 1572484 2359721 := bstep (se 2 (by rfl) ⟨884895, by rfl⟩ : syracuseStep 2359721 = 1769791) B1769791
theorem B2360603 : Blo 1572484 2360603 := bstep (se 1 (by rfl) ⟨1770452, by rfl⟩ : syracuseStep 2360603 = 3540905) B3540905
theorem B8078815 : Blo 1572484 8078815 := bstep (se 1 (by rfl) ⟨6059111, by rfl⟩ : syracuseStep 8078815 = 12118223) B12118223
theorem B2360879 : Blo 1572484 2360879 := bstep (se 1 (by rfl) ⟨1770659, by rfl⟩ : syracuseStep 2360879 = 3541319) B3541319
theorem B4540409 : Blo 1572484 4540409 := bstep (se 2 (by rfl) ⟨1702653, by rfl⟩ : syracuseStep 4540409 = 3405307) B3405307
theorem B5308415 : Blo 1572484 5308415 := bstep (se 1 (by rfl) ⟨3981311, by rfl⟩ : syracuseStep 5308415 = 7962623) B7962623
theorem B10078775 : Blo 1572484 10078775 := bstep (se 1 (by rfl) ⟨7559081, by rfl⟩ : syracuseStep 10078775 = 15118163) B15118163
theorem B10079315 : Blo 1572484 10079315 := bstep (se 1 (by rfl) ⟨7559486, by rfl⟩ : syracuseStep 10079315 = 15118973) B15118973
theorem B40856815 : Blo 1572484 40856815 := bstep (se 1 (by rfl) ⟨30642611, by rfl⟩ : syracuseStep 40856815 = 61285223) B61285223
theorem B38294507 : Blo 1572484 38294507 := bstep (se 1 (by rfl) ⟨28720880, by rfl⟩ : syracuseStep 38294507 = 57441761) B57441761
theorem B314455769 : Blo 1572484 314455769 := bstep (se 2 (by rfl) ⟨117920913, by rfl⟩ : syracuseStep 314455769 = 235841827) B235841827
theorem B3539087 : Blo 1572484 3539087 := bstep (se 1 (by rfl) ⟨2654315, by rfl⟩ : syracuseStep 3539087 = 5308631) B5308631
theorem B1573147 : Blo 1572484 1573147 := bstep (se 1 (by rfl) ⟨1179860, by rfl⟩ : syracuseStep 1573147 = 2359721) B2359721
theorem B1573735 : Blo 1572484 1573735 := bstep (se 1 (by rfl) ⟨1180301, by rfl⟩ : syracuseStep 1573735 = 2360603) B2360603
theorem B1573919 : Blo 1572484 1573919 := bstep (se 1 (by rfl) ⟨1180439, by rfl⟩ : syracuseStep 1573919 = 2360879) B2360879
theorem B6719183 : Blo 1572484 6719183 := bstep (se 1 (by rfl) ⟨5039387, by rfl⟩ : syracuseStep 6719183 = 10078775) B10078775
theorem B6719543 : Blo 1572484 6719543 := bstep (se 1 (by rfl) ⟨5039657, by rfl⟩ : syracuseStep 6719543 = 10079315) B10079315
theorem B25529671 : Blo 1572484 25529671 := bstep (se 1 (by rfl) ⟨19147253, by rfl⟩ : syracuseStep 25529671 = 38294507) B38294507
theorem B209637179 : Blo 1572484 209637179 := bstep (se 1 (by rfl) ⟨157227884, by rfl⟩ : syracuseStep 209637179 = 314455769) B314455769
theorem B3026939 : Blo 1572484 3026939 := bstep (se 1 (by rfl) ⟨2270204, by rfl⟩ : syracuseStep 3026939 = 4540409) B4540409
theorem B3538943 : Blo 1572484 3538943 := bstep (se 1 (by rfl) ⟨2654207, by rfl⟩ : syracuseStep 3538943 = 5308415) B5308415
theorem B54475753 : Blo 1572484 54475753 := bstep (se 2 (by rfl) ⟨20428407, by rfl⟩ : syracuseStep 54475753 = 40856815) B40856815
theorem B10771753 : Blo 1572484 10771753 := bstep (se 2 (by rfl) ⟨4039407, by rfl⟩ : syracuseStep 10771753 = 8078815) B8078815
theorem B2359391 : Blo 1572484 2359391 := bstep (se 1 (by rfl) ⟨1769543, by rfl⟩ : syracuseStep 2359391 = 3539087) B3539087
theorem B14362337 : Blo 1572484 14362337 := bstep (se 2 (by rfl) ⟨5385876, by rfl⟩ : syracuseStep 14362337 = 10771753) B10771753
theorem B34039561 : Blo 1572484 34039561 := bstep (se 2 (by rfl) ⟨12764835, by rfl⟩ : syracuseStep 34039561 = 25529671) B25529671
theorem B139758119 : Blo 1572484 139758119 := bstep (se 1 (by rfl) ⟨104818589, by rfl⟩ : syracuseStep 139758119 = 209637179) B209637179
theorem B32287349 : Blo 1572484 32287349 := bstep (se 5 (by rfl) ⟨1513469, by rfl⟩ : syracuseStep 32287349 = 3026939) B3026939
theorem B72634337 : Blo 1572484 72634337 := bstep (se 2 (by rfl) ⟨27237876, by rfl⟩ : syracuseStep 72634337 = 54475753) B54475753
theorem B4479455 : Blo 1572484 4479455 := bstep (se 1 (by rfl) ⟨3359591, by rfl⟩ : syracuseStep 4479455 = 6719183) B6719183
theorem B4479695 : Blo 1572484 4479695 := bstep (se 1 (by rfl) ⟨3359771, by rfl⟩ : syracuseStep 4479695 = 6719543) B6719543
theorem B2359295 : Blo 1572484 2359295 := bstep (se 1 (by rfl) ⟨1769471, by rfl⟩ : syracuseStep 2359295 = 3538943) B3538943
theorem B1572927 : Blo 1572484 1572927 := bstep (se 1 (by rfl) ⟨1179695, by rfl⟩ : syracuseStep 1572927 = 2359391) B2359391
theorem B1572863 : Blo 1572484 1572863 := bstep (se 1 (by rfl) ⟨1179647, by rfl⟩ : syracuseStep 1572863 = 2359295) B2359295
theorem B45386081 : Blo 1572484 45386081 := bstep (se 2 (by rfl) ⟨17019780, by rfl⟩ : syracuseStep 45386081 = 34039561) B34039561
theorem B2986303 : Blo 1572484 2986303 := bstep (se 1 (by rfl) ⟨2239727, by rfl⟩ : syracuseStep 2986303 = 4479455) B4479455
theorem B93172079 : Blo 1572484 93172079 := bstep (se 1 (by rfl) ⟨69879059, by rfl⟩ : syracuseStep 93172079 = 139758119) B139758119
theorem B21524899 : Blo 1572484 21524899 := bstep (se 1 (by rfl) ⟨16143674, by rfl⟩ : syracuseStep 21524899 = 32287349) B32287349
theorem B2986463 : Blo 1572484 2986463 := bstep (se 1 (by rfl) ⟨2239847, by rfl⟩ : syracuseStep 2986463 = 4479695) B4479695
theorem B9574891 : Blo 1572484 9574891 := bstep (se 1 (by rfl) ⟨7181168, by rfl⟩ : syracuseStep 9574891 = 14362337) B14362337
theorem B48422891 : Blo 1572484 48422891 := bstep (se 1 (by rfl) ⟨36317168, by rfl⟩ : syracuseStep 48422891 = 72634337) B72634337
theorem B1990975 : Blo 1572484 1990975 := bstep (se 1 (by rfl) ⟨1493231, by rfl⟩ : syracuseStep 1990975 = 2986463) B2986463
theorem B3981737 : Blo 1572484 3981737 := bstep (se 2 (by rfl) ⟨1493151, by rfl⟩ : syracuseStep 3981737 = 2986303) B2986303
theorem B62114719 : Blo 1572484 62114719 := bstep (se 1 (by rfl) ⟨46586039, by rfl⟩ : syracuseStep 62114719 = 93172079) B93172079
theorem B28699865 : Blo 1572484 28699865 := bstep (se 2 (by rfl) ⟨10762449, by rfl⟩ : syracuseStep 28699865 = 21524899) B21524899
theorem B30257387 : Blo 1572484 30257387 := bstep (se 1 (by rfl) ⟨22693040, by rfl⟩ : syracuseStep 30257387 = 45386081) B45386081
theorem B51066085 : Blo 1572484 51066085 := bstep (se 4 (by rfl) ⟨4787445, by rfl⟩ : syracuseStep 51066085 = 9574891) B9574891
theorem B129127709 : Blo 1572484 129127709 := bstep (se 3 (by rfl) ⟨24211445, by rfl⟩ : syracuseStep 129127709 = 48422891) B48422891
theorem B2654491 : Blo 1572484 2654491 := bstep (se 1 (by rfl) ⟨1990868, by rfl⟩ : syracuseStep 2654491 = 3981737) B3981737
theorem B2654633 : Blo 1572484 2654633 := bstep (se 2 (by rfl) ⟨995487, by rfl⟩ : syracuseStep 2654633 = 1990975) B1990975
theorem B20171591 : Blo 1572484 20171591 := bstep (se 1 (by rfl) ⟨15128693, by rfl⟩ : syracuseStep 20171591 = 30257387) B30257387
theorem B86085139 : Blo 1572484 86085139 := bstep (se 1 (by rfl) ⟨64563854, by rfl⟩ : syracuseStep 86085139 = 129127709) B129127709
theorem B68088113 : Blo 1572484 68088113 := bstep (se 2 (by rfl) ⟨25533042, by rfl⟩ : syracuseStep 68088113 = 51066085) B51066085
theorem B19133243 : Blo 1572484 19133243 := bstep (se 1 (by rfl) ⟨14349932, by rfl⟩ : syracuseStep 19133243 = 28699865) B28699865
theorem B82819625 : Blo 1572484 82819625 := bstep (se 2 (by rfl) ⟨31057359, by rfl⟩ : syracuseStep 82819625 = 62114719) B62114719
theorem B45392075 : Blo 1572484 45392075 := bstep (se 1 (by rfl) ⟨34044056, by rfl⟩ : syracuseStep 45392075 = 68088113) B68088113
theorem B1769755 : Blo 1572484 1769755 := bstep (se 1 (by rfl) ⟨1327316, by rfl⟩ : syracuseStep 1769755 = 2654633) B2654633
theorem B3539321 : Blo 1572484 3539321 := bstep (se 2 (by rfl) ⟨1327245, by rfl⟩ : syracuseStep 3539321 = 2654491) B2654491
theorem B12755495 : Blo 1572484 12755495 := bstep (se 1 (by rfl) ⟨9566621, by rfl⟩ : syracuseStep 12755495 = 19133243) B19133243
theorem B114780185 : Blo 1572484 114780185 := bstep (se 2 (by rfl) ⟨43042569, by rfl⟩ : syracuseStep 114780185 = 86085139) B86085139
theorem B220852333 : Blo 1572484 220852333 := bstep (se 3 (by rfl) ⟨41409812, by rfl⟩ : syracuseStep 220852333 = 82819625) B82819625
theorem B13447727 : Blo 1572484 13447727 := bstep (se 1 (by rfl) ⟨10085795, by rfl⟩ : syracuseStep 13447727 = 20171591) B20171591
theorem B30261383 : Blo 1572484 30261383 := bstep (se 1 (by rfl) ⟨22696037, by rfl⟩ : syracuseStep 30261383 = 45392075) B45392075
theorem B294469777 : Blo 1572484 294469777 := bstep (se 2 (by rfl) ⟨110426166, by rfl⟩ : syracuseStep 294469777 = 220852333) B220852333
theorem B2359547 : Blo 1572484 2359547 := bstep (se 1 (by rfl) ⟨1769660, by rfl⟩ : syracuseStep 2359547 = 3539321) B3539321
theorem B2359673 : Blo 1572484 2359673 := bstep (se 2 (by rfl) ⟨884877, by rfl⟩ : syracuseStep 2359673 = 1769755) B1769755
theorem B34014653 : Blo 1572484 34014653 := bstep (se 3 (by rfl) ⟨6377747, by rfl⟩ : syracuseStep 34014653 = 12755495) B12755495
theorem B8965151 : Blo 1572484 8965151 := bstep (se 1 (by rfl) ⟨6723863, by rfl⟩ : syracuseStep 8965151 = 13447727) B13447727
theorem B76520123 : Blo 1572484 76520123 := bstep (se 1 (by rfl) ⟨57390092, by rfl⟩ : syracuseStep 76520123 = 114780185) B114780185
theorem B1573031 : Blo 1572484 1573031 := bstep (se 1 (by rfl) ⟨1179773, by rfl⟩ : syracuseStep 1573031 = 2359547) B2359547
theorem B392626369 : Blo 1572484 392626369 := bstep (se 2 (by rfl) ⟨147234888, by rfl⟩ : syracuseStep 392626369 = 294469777) B294469777
theorem B1573115 : Blo 1572484 1573115 := bstep (se 1 (by rfl) ⟨1179836, by rfl⟩ : syracuseStep 1573115 = 2359673) B2359673
theorem B22676435 : Blo 1572484 22676435 := bstep (se 1 (by rfl) ⟨17007326, by rfl⟩ : syracuseStep 22676435 = 34014653) B34014653
theorem B51013415 : Blo 1572484 51013415 := bstep (se 1 (by rfl) ⟨38260061, by rfl⟩ : syracuseStep 51013415 = 76520123) B76520123
theorem B5976767 : Blo 1572484 5976767 := bstep (se 1 (by rfl) ⟨4482575, by rfl⟩ : syracuseStep 5976767 = 8965151) B8965151
theorem B20174255 : Blo 1572484 20174255 := bstep (se 1 (by rfl) ⟨15130691, by rfl⟩ : syracuseStep 20174255 = 30261383) B30261383
theorem B523501825 : Blo 1572484 523501825 := bstep (se 2 (by rfl) ⟨196313184, by rfl⟩ : syracuseStep 523501825 = 392626369) B392626369
theorem B3984511 : Blo 1572484 3984511 := bstep (se 1 (by rfl) ⟨2988383, by rfl⟩ : syracuseStep 3984511 = 5976767) B5976767
theorem B15117623 : Blo 1572484 15117623 := bstep (se 1 (by rfl) ⟨11338217, by rfl⟩ : syracuseStep 15117623 = 22676435) B22676435
theorem B34008943 : Blo 1572484 34008943 := bstep (se 1 (by rfl) ⟨25506707, by rfl⟩ : syracuseStep 34008943 = 51013415) B51013415
theorem B13449503 : Blo 1572484 13449503 := bstep (se 1 (by rfl) ⟨10087127, by rfl⟩ : syracuseStep 13449503 = 20174255) B20174255
theorem B10078415 : Blo 1572484 10078415 := bstep (se 1 (by rfl) ⟨7558811, by rfl⟩ : syracuseStep 10078415 = 15117623) B15117623
theorem B45345257 : Blo 1572484 45345257 := bstep (se 2 (by rfl) ⟨17004471, by rfl⟩ : syracuseStep 45345257 = 34008943) B34008943
theorem B698002433 : Blo 1572484 698002433 := bstep (se 2 (by rfl) ⟨261750912, by rfl⟩ : syracuseStep 698002433 = 523501825) B523501825
theorem B5312681 : Blo 1572484 5312681 := bstep (se 2 (by rfl) ⟨1992255, by rfl⟩ : syracuseStep 5312681 = 3984511) B3984511
theorem B8966335 : Blo 1572484 8966335 := bstep (se 1 (by rfl) ⟨6724751, by rfl⟩ : syracuseStep 8966335 = 13449503) B13449503
theorem B6718943 : Blo 1572484 6718943 := bstep (se 1 (by rfl) ⟨5039207, by rfl⟩ : syracuseStep 6718943 = 10078415) B10078415
theorem B30230171 : Blo 1572484 30230171 := bstep (se 1 (by rfl) ⟨22672628, by rfl⟩ : syracuseStep 30230171 = 45345257) B45345257
theorem B3541787 : Blo 1572484 3541787 := bstep (se 1 (by rfl) ⟨2656340, by rfl⟩ : syracuseStep 3541787 = 5312681) B5312681
theorem B11955113 : Blo 1572484 11955113 := bstep (se 2 (by rfl) ⟨4483167, by rfl⟩ : syracuseStep 11955113 = 8966335) B8966335
theorem B465334955 : Blo 1572484 465334955 := bstep (se 1 (by rfl) ⟨349001216, by rfl⟩ : syracuseStep 465334955 = 698002433) B698002433
theorem B310223303 : Blo 1572484 310223303 := bstep (se 1 (by rfl) ⟨232667477, by rfl⟩ : syracuseStep 310223303 = 465334955) B465334955
theorem B20153447 : Blo 1572484 20153447 := bstep (se 1 (by rfl) ⟨15115085, by rfl⟩ : syracuseStep 20153447 = 30230171) B30230171
theorem B2361191 : Blo 1572484 2361191 := bstep (se 1 (by rfl) ⟨1770893, by rfl⟩ : syracuseStep 2361191 = 3541787) B3541787
theorem B4479295 : Blo 1572484 4479295 := bstep (se 1 (by rfl) ⟨3359471, by rfl⟩ : syracuseStep 4479295 = 6718943) B6718943
theorem B7970075 : Blo 1572484 7970075 := bstep (se 1 (by rfl) ⟨5977556, by rfl⟩ : syracuseStep 7970075 = 11955113) B11955113
theorem B206815535 : Blo 1572484 206815535 := bstep (se 1 (by rfl) ⟨155111651, by rfl⟩ : syracuseStep 206815535 = 310223303) B310223303
theorem B5972393 : Blo 1572484 5972393 := bstep (se 2 (by rfl) ⟨2239647, by rfl⟩ : syracuseStep 5972393 = 4479295) B4479295
theorem B13435631 : Blo 1572484 13435631 := bstep (se 1 (by rfl) ⟨10076723, by rfl⟩ : syracuseStep 13435631 = 20153447) B20153447
theorem B1574127 : Blo 1572484 1574127 := bstep (se 1 (by rfl) ⟨1180595, by rfl⟩ : syracuseStep 1574127 = 2361191) B2361191
theorem B5313383 : Blo 1572484 5313383 := bstep (se 1 (by rfl) ⟨3985037, by rfl⟩ : syracuseStep 5313383 = 7970075) B7970075
theorem B3981595 : Blo 1572484 3981595 := bstep (se 1 (by rfl) ⟨2986196, by rfl⟩ : syracuseStep 3981595 = 5972393) B5972393
theorem B8957087 : Blo 1572484 8957087 := bstep (se 1 (by rfl) ⟨6717815, by rfl⟩ : syracuseStep 8957087 = 13435631) B13435631
theorem B3542255 : Blo 1572484 3542255 := bstep (se 1 (by rfl) ⟨2656691, by rfl⟩ : syracuseStep 3542255 = 5313383) B5313383
theorem B137877023 : Blo 1572484 137877023 := bstep (se 1 (by rfl) ⟨103407767, by rfl⟩ : syracuseStep 137877023 = 206815535) B206815535
theorem B5308793 : Blo 1572484 5308793 := bstep (se 2 (by rfl) ⟨1990797, by rfl⟩ : syracuseStep 5308793 = 3981595) B3981595
theorem B2361503 : Blo 1572484 2361503 := bstep (se 1 (by rfl) ⟨1771127, by rfl⟩ : syracuseStep 2361503 = 3542255) B3542255
theorem B367672061 : Blo 1572484 367672061 := bstep (se 3 (by rfl) ⟨68938511, by rfl⟩ : syracuseStep 367672061 = 137877023) B137877023
theorem B5971391 : Blo 1572484 5971391 := bstep (se 1 (by rfl) ⟨4478543, by rfl⟩ : syracuseStep 5971391 = 8957087) B8957087
theorem B3539195 : Blo 1572484 3539195 := bstep (se 1 (by rfl) ⟨2654396, by rfl⟩ : syracuseStep 3539195 = 5308793) B5308793
theorem B1574335 : Blo 1572484 1574335 := bstep (se 1 (by rfl) ⟨1180751, by rfl⟩ : syracuseStep 1574335 = 2361503) B2361503
theorem B245114707 : Blo 1572484 245114707 := bstep (se 1 (by rfl) ⟨183836030, by rfl⟩ : syracuseStep 245114707 = 367672061) B367672061
theorem B3980927 : Blo 1572484 3980927 := bstep (se 1 (by rfl) ⟨2985695, by rfl⟩ : syracuseStep 3980927 = 5971391) B5971391
theorem B2359463 : Blo 1572484 2359463 := bstep (se 1 (by rfl) ⟨1769597, by rfl⟩ : syracuseStep 2359463 = 3539195) B3539195
theorem B2653951 : Blo 1572484 2653951 := bstep (se 1 (by rfl) ⟨1990463, by rfl⟩ : syracuseStep 2653951 = 3980927) B3980927
theorem B326819609 : Blo 1572484 326819609 := bstep (se 2 (by rfl) ⟨122557353, by rfl⟩ : syracuseStep 326819609 = 245114707) B245114707
theorem B1572975 : Blo 1572484 1572975 := bstep (se 1 (by rfl) ⟨1179731, by rfl⟩ : syracuseStep 1572975 = 2359463) B2359463
theorem B217879739 : Blo 1572484 217879739 := bstep (se 1 (by rfl) ⟨163409804, by rfl⟩ : syracuseStep 217879739 = 326819609) B326819609
theorem B3538601 : Blo 1572484 3538601 := bstep (se 2 (by rfl) ⟨1326975, by rfl⟩ : syracuseStep 3538601 = 2653951) B2653951
theorem B145253159 : Blo 1572484 145253159 := bstep (se 1 (by rfl) ⟨108939869, by rfl⟩ : syracuseStep 145253159 = 217879739) B217879739
theorem B2359067 : Blo 1572484 2359067 := bstep (se 1 (by rfl) ⟨1769300, by rfl⟩ : syracuseStep 2359067 = 3538601) B3538601
theorem B96835439 : Blo 1572484 96835439 := bstep (se 1 (by rfl) ⟨72626579, by rfl⟩ : syracuseStep 96835439 = 145253159) B145253159
theorem B1572711 : Blo 1572484 1572711 := bstep (se 1 (by rfl) ⟨1179533, by rfl⟩ : syracuseStep 1572711 = 2359067) B2359067
theorem B64556959 : Blo 1572484 64556959 := bstep (se 1 (by rfl) ⟨48417719, by rfl⟩ : syracuseStep 64556959 = 96835439) B96835439
theorem B86075945 : Blo 1572484 86075945 := bstep (se 2 (by rfl) ⟨32278479, by rfl⟩ : syracuseStep 86075945 = 64556959) B64556959
theorem B57383963 : Blo 1572484 57383963 := bstep (se 1 (by rfl) ⟨43037972, by rfl⟩ : syracuseStep 57383963 = 86075945) B86075945
theorem B38255975 : Blo 1572484 38255975 := bstep (se 1 (by rfl) ⟨28691981, by rfl⟩ : syracuseStep 38255975 = 57383963) B57383963
theorem B25503983 : Blo 1572484 25503983 := bstep (se 1 (by rfl) ⟨19127987, by rfl⟩ : syracuseStep 25503983 = 38255975) B38255975
theorem B17002655 : Blo 1572484 17002655 := bstep (se 1 (by rfl) ⟨12751991, by rfl⟩ : syracuseStep 17002655 = 25503983) B25503983
theorem B11335103 : Blo 1572484 11335103 := bstep (se 1 (by rfl) ⟨8501327, by rfl⟩ : syracuseStep 11335103 = 17002655) B17002655
theorem B7556735 : Blo 1572484 7556735 := bstep (se 1 (by rfl) ⟨5667551, by rfl⟩ : syracuseStep 7556735 = 11335103) B11335103
theorem B5037823 : Blo 1572484 5037823 := bstep (se 1 (by rfl) ⟨3778367, by rfl⟩ : syracuseStep 5037823 = 7556735) B7556735
theorem B6717097 : Blo 1572484 6717097 := bstep (se 2 (by rfl) ⟨2518911, by rfl⟩ : syracuseStep 6717097 = 5037823) B5037823
theorem B8956129 : Blo 1572484 8956129 := bstep (se 2 (by rfl) ⟨3358548, by rfl⟩ : syracuseStep 8956129 = 6717097) B6717097
theorem B11941505 : Blo 1572484 11941505 := bstep (se 2 (by rfl) ⟨4478064, by rfl⟩ : syracuseStep 11941505 = 8956129) B8956129
theorem B7961003 : Blo 1572484 7961003 := bstep (se 1 (by rfl) ⟨5970752, by rfl⟩ : syracuseStep 7961003 = 11941505) B11941505
theorem B5307335 : Blo 1572484 5307335 := bstep (se 1 (by rfl) ⟨3980501, by rfl⟩ : syracuseStep 5307335 = 7961003) B7961003
theorem B3538223 : Blo 1572484 3538223 := bstep (se 1 (by rfl) ⟨2653667, by rfl⟩ : syracuseStep 3538223 = 5307335) B5307335
theorem B2358815 : Blo 1572484 2358815 := bstep (se 1 (by rfl) ⟨1769111, by rfl⟩ : syracuseStep 2358815 = 3538223) B3538223
theorem B1572543 : Blo 1572484 1572543 := bstep (se 1 (by rfl) ⟨1179407, by rfl⟩ : syracuseStep 1572543 = 2358815) B2358815

theorem C0 (j : ℕ) (h1 : 393121 ≤ j) (h2 : j ≤ 393620) : Blo 1572484 (4 * j + 3) := by
  interval_cases j
  · exact B1572487
  · exact B1572491
  · exact B1572495
  · exact B1572499
  · exact B1572503
  · exact B1572507
  · exact B1572511
  · exact B1572515
  · exact B1572519
  · exact B1572523
  · exact B1572527
  · exact B1572531
  · exact B1572535
  · exact B1572539
  · exact B1572543
  · exact B1572547
  · exact B1572551
  · exact B1572555
  · exact B1572559
  · exact B1572563
  · exact B1572567
  · exact B1572571
  · exact B1572575
  · exact B1572579
  · exact B1572583
  · exact B1572587
  · exact B1572591
  · exact B1572595
  · exact B1572599
  · exact B1572603
  · exact B1572607
  · exact B1572611
  · exact B1572615
  · exact B1572619
  · exact B1572623
  · exact B1572627
  · exact B1572631
  · exact B1572635
  · exact B1572639
  · exact B1572643
  · exact B1572647
  · exact B1572651
  · exact B1572655
  · exact B1572659
  · exact B1572663
  · exact B1572667
  · exact B1572671
  · exact B1572675
  · exact B1572679
  · exact B1572683
  · exact B1572687
  · exact B1572691
  · exact B1572695
  · exact B1572699
  · exact B1572703
  · exact B1572707
  · exact B1572711
  · exact B1572715
  · exact B1572719
  · exact B1572723
  · exact B1572727
  · exact B1572731
  · exact B1572735
  · exact B1572739
  · exact B1572743
  · exact B1572747
  · exact B1572751
  · exact B1572755
  · exact B1572759
  · exact B1572763
  · exact B1572767
  · exact B1572771
  · exact B1572775
  · exact B1572779
  · exact B1572783
  · exact B1572787
  · exact B1572791
  · exact B1572795
  · exact B1572799
  · exact B1572803
  · exact B1572807
  · exact B1572811
  · exact B1572815
  · exact B1572819
  · exact B1572823
  · exact B1572827
  · exact B1572831
  · exact B1572835
  · exact B1572839
  · exact B1572843
  · exact B1572847
  · exact B1572851
  · exact B1572855
  · exact B1572859
  · exact B1572863
  · exact B1572867
  · exact B1572871
  · exact B1572875
  · exact B1572879
  · exact B1572883
  · exact B1572887
  · exact B1572891
  · exact B1572895
  · exact B1572899
  · exact B1572903
  · exact B1572907
  · exact B1572911
  · exact B1572915
  · exact B1572919
  · exact B1572923
  · exact B1572927
  · exact B1572931
  · exact B1572935
  · exact B1572939
  · exact B1572943
  · exact B1572947
  · exact B1572951
  · exact B1572955
  · exact B1572959
  · exact B1572963
  · exact B1572967
  · exact B1572971
  · exact B1572975
  · exact B1572979
  · exact B1572983
  · exact B1572987
  · exact B1572991
  · exact B1572995
  · exact B1572999
  · exact B1573003
  · exact B1573007
  · exact B1573011
  · exact B1573015
  · exact B1573019
  · exact B1573023
  · exact B1573027
  · exact B1573031
  · exact B1573035
  · exact B1573039
  · exact B1573043
  · exact B1573047
  · exact B1573051
  · exact B1573055
  · exact B1573059
  · exact B1573063
  · exact B1573067
  · exact B1573071
  · exact B1573075
  · exact B1573079
  · exact B1573083
  · exact B1573087
  · exact B1573091
  · exact B1573095
  · exact B1573099
  · exact B1573103
  · exact B1573107
  · exact B1573111
  · exact B1573115
  · exact B1573119
  · exact B1573123
  · exact B1573127
  · exact B1573131
  · exact B1573135
  · exact B1573139
  · exact B1573143
  · exact B1573147
  · exact B1573151
  · exact B1573155
  · exact B1573159
  · exact B1573163
  · exact B1573167
  · exact B1573171
  · exact B1573175
  · exact B1573179
  · exact B1573183
  · exact B1573187
  · exact B1573191
  · exact B1573195
  · exact B1573199
  · exact B1573203
  · exact B1573207
  · exact B1573211
  · exact B1573215
  · exact B1573219
  · exact B1573223
  · exact B1573227
  · exact B1573231
  · exact B1573235
  · exact B1573239
  · exact B1573243
  · exact B1573247
  · exact B1573251
  · exact B1573255
  · exact B1573259
  · exact B1573263
  · exact B1573267
  · exact B1573271
  · exact B1573275
  · exact B1573279
  · exact B1573283
  · exact B1573287
  · exact B1573291
  · exact B1573295
  · exact B1573299
  · exact B1573303
  · exact B1573307
  · exact B1573311
  · exact B1573315
  · exact B1573319
  · exact B1573323
  · exact B1573327
  · exact B1573331
  · exact B1573335
  · exact B1573339
  · exact B1573343
  · exact B1573347
  · exact B1573351
  · exact B1573355
  · exact B1573359
  · exact B1573363
  · exact B1573367
  · exact B1573371
  · exact B1573375
  · exact B1573379
  · exact B1573383
  · exact B1573387
  · exact B1573391
  · exact B1573395
  · exact B1573399
  · exact B1573403
  · exact B1573407
  · exact B1573411
  · exact B1573415
  · exact B1573419
  · exact B1573423
  · exact B1573427
  · exact B1573431
  · exact B1573435
  · exact B1573439
  · exact B1573443
  · exact B1573447
  · exact B1573451
  · exact B1573455
  · exact B1573459
  · exact B1573463
  · exact B1573467
  · exact B1573471
  · exact B1573475
  · exact B1573479
  · exact B1573483
  · exact B1573487
  · exact B1573491
  · exact B1573495
  · exact B1573499
  · exact B1573503
  · exact B1573507
  · exact B1573511
  · exact B1573515
  · exact B1573519
  · exact B1573523
  · exact B1573527
  · exact B1573531
  · exact B1573535
  · exact B1573539
  · exact B1573543
  · exact B1573547
  · exact B1573551
  · exact B1573555
  · exact B1573559
  · exact B1573563
  · exact B1573567
  · exact B1573571
  · exact B1573575
  · exact B1573579
  · exact B1573583
  · exact B1573587
  · exact B1573591
  · exact B1573595
  · exact B1573599
  · exact B1573603
  · exact B1573607
  · exact B1573611
  · exact B1573615
  · exact B1573619
  · exact B1573623
  · exact B1573627
  · exact B1573631
  · exact B1573635
  · exact B1573639
  · exact B1573643
  · exact B1573647
  · exact B1573651
  · exact B1573655
  · exact B1573659
  · exact B1573663
  · exact B1573667
  · exact B1573671
  · exact B1573675
  · exact B1573679
  · exact B1573683
  · exact B1573687
  · exact B1573691
  · exact B1573695
  · exact B1573699
  · exact B1573703
  · exact B1573707
  · exact B1573711
  · exact B1573715
  · exact B1573719
  · exact B1573723
  · exact B1573727
  · exact B1573731
  · exact B1573735
  · exact B1573739
  · exact B1573743
  · exact B1573747
  · exact B1573751
  · exact B1573755
  · exact B1573759
  · exact B1573763
  · exact B1573767
  · exact B1573771
  · exact B1573775
  · exact B1573779
  · exact B1573783
  · exact B1573787
  · exact B1573791
  · exact B1573795
  · exact B1573799
  · exact B1573803
  · exact B1573807
  · exact B1573811
  · exact B1573815
  · exact B1573819
  · exact B1573823
  · exact B1573827
  · exact B1573831
  · exact B1573835
  · exact B1573839
  · exact B1573843
  · exact B1573847
  · exact B1573851
  · exact B1573855
  · exact B1573859
  · exact B1573863
  · exact B1573867
  · exact B1573871
  · exact B1573875
  · exact B1573879
  · exact B1573883
  · exact B1573887
  · exact B1573891
  · exact B1573895
  · exact B1573899
  · exact B1573903
  · exact B1573907
  · exact B1573911
  · exact B1573915
  · exact B1573919
  · exact B1573923
  · exact B1573927
  · exact B1573931
  · exact B1573935
  · exact B1573939
  · exact B1573943
  · exact B1573947
  · exact B1573951
  · exact B1573955
  · exact B1573959
  · exact B1573963
  · exact B1573967
  · exact B1573971
  · exact B1573975
  · exact B1573979
  · exact B1573983
  · exact B1573987
  · exact B1573991
  · exact B1573995
  · exact B1573999
  · exact B1574003
  · exact B1574007
  · exact B1574011
  · exact B1574015
  · exact B1574019
  · exact B1574023
  · exact B1574027
  · exact B1574031
  · exact B1574035
  · exact B1574039
  · exact B1574043
  · exact B1574047
  · exact B1574051
  · exact B1574055
  · exact B1574059
  · exact B1574063
  · exact B1574067
  · exact B1574071
  · exact B1574075
  · exact B1574079
  · exact B1574083
  · exact B1574087
  · exact B1574091
  · exact B1574095
  · exact B1574099
  · exact B1574103
  · exact B1574107
  · exact B1574111
  · exact B1574115
  · exact B1574119
  · exact B1574123
  · exact B1574127
  · exact B1574131
  · exact B1574135
  · exact B1574139
  · exact B1574143
  · exact B1574147
  · exact B1574151
  · exact B1574155
  · exact B1574159
  · exact B1574163
  · exact B1574167
  · exact B1574171
  · exact B1574175
  · exact B1574179
  · exact B1574183
  · exact B1574187
  · exact B1574191
  · exact B1574195
  · exact B1574199
  · exact B1574203
  · exact B1574207
  · exact B1574211
  · exact B1574215
  · exact B1574219
  · exact B1574223
  · exact B1574227
  · exact B1574231
  · exact B1574235
  · exact B1574239
  · exact B1574243
  · exact B1574247
  · exact B1574251
  · exact B1574255
  · exact B1574259
  · exact B1574263
  · exact B1574267
  · exact B1574271
  · exact B1574275
  · exact B1574279
  · exact B1574283
  · exact B1574287
  · exact B1574291
  · exact B1574295
  · exact B1574299
  · exact B1574303
  · exact B1574307
  · exact B1574311
  · exact B1574315
  · exact B1574319
  · exact B1574323
  · exact B1574327
  · exact B1574331
  · exact B1574335
  · exact B1574339
  · exact B1574343
  · exact B1574347
  · exact B1574351
  · exact B1574355
  · exact B1574359
  · exact B1574363
  · exact B1574367
  · exact B1574371
  · exact B1574375
  · exact B1574379
  · exact B1574383
  · exact B1574387
  · exact B1574391
  · exact B1574395
  · exact B1574399
  · exact B1574403
  · exact B1574407
  · exact B1574411
  · exact B1574415
  · exact B1574419
  · exact B1574423
  · exact B1574427
  · exact B1574431
  · exact B1574435
  · exact B1574439
  · exact B1574443
  · exact B1574447
  · exact B1574451
  · exact B1574455
  · exact B1574459
  · exact B1574463
  · exact B1574467
  · exact B1574471
  · exact B1574475
  · exact B1574479
  · exact B1574483

theorem solution (m : ℕ) (hlo : 1572484 ≤ m) (hhi : m ≤ 1574484) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 393121 ≤ j := by omega
    have hj2 : j ≤ 393620 := by omega
    have hb : Blo 1572484 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
