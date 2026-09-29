-- Prove2me | solution 1 for syracuse_descends_range_1303970_1305970
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:12:28.466921+00:00
-- url     : https://prove2.me/submissions/3077ec42-8a68-42c9-b22c-3ecd4f10ec00

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


theorem B1957901 : Blo 1303970 1957901 := bbase (se 3 (by rfl) ⟨367106, by rfl⟩ : syracuseStep 1957901 = 734213) (by norm_num)
theorem B4407317 : Blo 1303970 4407317 := bbase (se 6 (by rfl) ⟨103296, by rfl⟩ : syracuseStep 4407317 = 206593) (by norm_num)
theorem B1957925 : Blo 1303970 1957925 := bbase (se 4 (by rfl) ⟨183555, by rfl⟩ : syracuseStep 1957925 = 367111) (by norm_num)
theorem B4767797 : Blo 1303970 4767797 := bbase (se 5 (by rfl) ⟨223490, by rfl⟩ : syracuseStep 4767797 = 446981) (by norm_num)
theorem B1957949 : Blo 1303970 1957949 := bbase (se 3 (by rfl) ⟨367115, by rfl⟩ : syracuseStep 1957949 = 734231) (by norm_num)
theorem B1957973 : Blo 1303970 1957973 := bbase (se 8 (by rfl) ⟨11472, by rfl⟩ : syracuseStep 1957973 = 22945) (by norm_num)
theorem B2203733 : Blo 1303970 2203733 := bbase (se 8 (by rfl) ⟨12912, by rfl⟩ : syracuseStep 2203733 = 25825) (by norm_num)
theorem B3301469 : Blo 1303970 3301469 := bbase (se 3 (by rfl) ⟨619025, by rfl⟩ : syracuseStep 3301469 = 1238051) (by norm_num)
theorem B1957997 : Blo 1303970 1957997 := bbase (se 3 (by rfl) ⟨367124, by rfl⟩ : syracuseStep 1957997 = 734249) (by norm_num)
theorem B1958021 : Blo 1303970 1958021 := bbase (se 4 (by rfl) ⟨183564, by rfl⟩ : syracuseStep 1958021 = 367129) (by norm_num)
theorem B2089109 : Blo 1303970 2089109 := bbase (se 6 (by rfl) ⟨48963, by rfl⟩ : syracuseStep 2089109 = 97927) (by norm_num)
theorem B9412757 : Blo 1303970 9412757 := bbase (se 6 (by rfl) ⟨220611, by rfl⟩ : syracuseStep 9412757 = 441223) (by norm_num)
theorem B1958045 : Blo 1303970 1958045 := bbase (se 3 (by rfl) ⟨367133, by rfl⟩ : syracuseStep 1958045 = 734267) (by norm_num)
theorem B1958069 : Blo 1303970 1958069 := bbase (se 5 (by rfl) ⟨91784, by rfl⟩ : syracuseStep 1958069 = 183569) (by norm_num)
theorem B6267077 : Blo 1303970 6267077 := bbase (se 4 (by rfl) ⟨587538, by rfl⟩ : syracuseStep 6267077 = 1175077) (by norm_num)
theorem B1958093 : Blo 1303970 1958093 := bbase (se 3 (by rfl) ⟨367142, by rfl⟩ : syracuseStep 1958093 = 734285) (by norm_num)
theorem B1958117 : Blo 1303970 1958117 := bbase (se 4 (by rfl) ⟨183573, by rfl⟩ : syracuseStep 1958117 = 367147) (by norm_num)
theorem B1958141 : Blo 1303970 1958141 := bbase (se 3 (by rfl) ⟨367151, by rfl⟩ : syracuseStep 1958141 = 734303) (by norm_num)
theorem B1958165 : Blo 1303970 1958165 := bbase (se 6 (by rfl) ⟨45894, by rfl⟩ : syracuseStep 1958165 = 91789) (by norm_num)
theorem B3301661 : Blo 1303970 3301661 := bbase (se 3 (by rfl) ⟨619061, by rfl⟩ : syracuseStep 3301661 = 1238123) (by norm_num)
theorem B3350813 : Blo 1303970 3350813 := bbase (se 3 (by rfl) ⟨628277, by rfl⟩ : syracuseStep 3350813 = 1256555) (by norm_num)
theorem B1958189 : Blo 1303970 1958189 := bbase (se 3 (by rfl) ⟨367160, by rfl⟩ : syracuseStep 1958189 = 734321) (by norm_num)
theorem B1958213 : Blo 1303970 1958213 := bbase (se 4 (by rfl) ⟨183582, by rfl⟩ : syracuseStep 1958213 = 367165) (by norm_num)
theorem B1958237 : Blo 1303970 1958237 := bbase (se 3 (by rfl) ⟨367169, by rfl⟩ : syracuseStep 1958237 = 734339) (by norm_num)
theorem B2646373 : Blo 1303970 2646373 := bbase (se 4 (by rfl) ⟨248097, by rfl⟩ : syracuseStep 2646373 = 496195) (by norm_num)
theorem B1958261 : Blo 1303970 1958261 := bbase (se 5 (by rfl) ⟨91793, by rfl⟩ : syracuseStep 1958261 = 183587) (by norm_num)
theorem B1958285 : Blo 1303970 1958285 := bbase (se 3 (by rfl) ⟨367178, by rfl⟩ : syracuseStep 1958285 = 734357) (by norm_num)
theorem B2646437 : Blo 1303970 2646437 := bbase (se 4 (by rfl) ⟨248103, by rfl⟩ : syracuseStep 2646437 = 496207) (by norm_num)
theorem B1958309 : Blo 1303970 1958309 := bbase (se 4 (by rfl) ⟨183591, by rfl⟩ : syracuseStep 1958309 = 367183) (by norm_num)
theorem B6611381 : Blo 1303970 6611381 := bbase (se 5 (by rfl) ⟨309908, by rfl⟩ : syracuseStep 6611381 = 619817) (by norm_num)
theorem B1393085 : Blo 1303970 1393085 := bbase (se 3 (by rfl) ⟨261203, by rfl⟩ : syracuseStep 1393085 = 522407) (by norm_num)
theorem B1958333 : Blo 1303970 1958333 := bbase (se 3 (by rfl) ⟨367187, by rfl⟩ : syracuseStep 1958333 = 734375) (by norm_num)
theorem B1958357 : Blo 1303970 1958357 := bbase (se 7 (by rfl) ⟨22949, by rfl⟩ : syracuseStep 1958357 = 45899) (by norm_num)
theorem B1958381 : Blo 1303970 1958381 := bbase (se 3 (by rfl) ⟨367196, by rfl⟩ : syracuseStep 1958381 = 734393) (by norm_num)
theorem B1958405 : Blo 1303970 1958405 := bbase (se 4 (by rfl) ⟨183600, by rfl⟩ : syracuseStep 1958405 = 367201) (by norm_num)
theorem B1958429 : Blo 1303970 1958429 := bbase (se 3 (by rfl) ⟨367205, by rfl⟩ : syracuseStep 1958429 = 734411) (by norm_num)
theorem B5571109 : Blo 1303970 5571109 := bbase (se 4 (by rfl) ⟨522291, by rfl⟩ : syracuseStep 5571109 = 1044583) (by norm_num)
theorem B2089525 : Blo 1303970 2089525 := bbase (se 5 (by rfl) ⟨97946, by rfl⟩ : syracuseStep 2089525 = 195893) (by norm_num)
theorem B1958453 : Blo 1303970 1958453 := bbase (se 5 (by rfl) ⟨91802, by rfl⟩ : syracuseStep 1958453 = 183605) (by norm_num)
theorem B1958477 : Blo 1303970 1958477 := bbase (se 3 (by rfl) ⟨367214, by rfl⟩ : syracuseStep 1958477 = 734429) (by norm_num)
theorem B1466977 : Blo 1303970 1466977 := bbase (se 2 (by rfl) ⟨550116, by rfl⟩ : syracuseStep 1466977 = 1100233) (by norm_num)
theorem B1958501 : Blo 1303970 1958501 := bbase (se 4 (by rfl) ⟨183609, by rfl⟩ : syracuseStep 1958501 = 367219) (by norm_num)
theorem B9044597 : Blo 1303970 9044597 := bbase (se 5 (by rfl) ⟨423965, by rfl⟩ : syracuseStep 9044597 = 847931) (by norm_num)
theorem B3302005 : Blo 1303970 3302005 := bbase (se 5 (by rfl) ⟨154781, by rfl⟩ : syracuseStep 3302005 = 309563) (by norm_num)
theorem B1983101 : Blo 1303970 1983101 := bbase (se 3 (by rfl) ⟨371831, by rfl⟩ : syracuseStep 1983101 = 743663) (by norm_num)
theorem B1958525 : Blo 1303970 1958525 := bbase (se 3 (by rfl) ⟨367223, by rfl⟩ : syracuseStep 1958525 = 734447) (by norm_num)
theorem B1467013 : Blo 1303970 1467013 := bbase (se 4 (by rfl) ⟨137532, by rfl⟩ : syracuseStep 1467013 = 275065) (by norm_num)
theorem B4956821 : Blo 1303970 4956821 := bbase (se 6 (by rfl) ⟨116175, by rfl⟩ : syracuseStep 4956821 = 232351) (by norm_num)
theorem B1958549 : Blo 1303970 1958549 := bbase (se 6 (by rfl) ⟨45903, by rfl⟩ : syracuseStep 1958549 = 91807) (by norm_num)
theorem B1467049 : Blo 1303970 1467049 := bbase (se 2 (by rfl) ⟨550143, by rfl⟩ : syracuseStep 1467049 = 1100287) (by norm_num)
theorem B1958573 : Blo 1303970 1958573 := bbase (se 3 (by rfl) ⟨367232, by rfl⟩ : syracuseStep 1958573 = 734465) (by norm_num)
theorem B6357685 : Blo 1303970 6357685 := bbase (se 5 (by rfl) ⟨298016, by rfl⟩ : syracuseStep 6357685 = 596033) (by norm_num)
theorem B1958597 : Blo 1303970 1958597 := bbase (se 4 (by rfl) ⟨183618, by rfl⟩ : syracuseStep 1958597 = 367237) (by norm_num)
theorem B1467085 : Blo 1303970 1467085 := bbase (se 3 (by rfl) ⟨275078, by rfl⟩ : syracuseStep 1467085 = 550157) (by norm_num)
theorem B1696465 : Blo 1303970 1696465 := bbase (se 2 (by rfl) ⟨636174, by rfl⟩ : syracuseStep 1696465 = 1272349) (by norm_num)
theorem B1958621 : Blo 1303970 1958621 := bbase (se 3 (by rfl) ⟨367241, by rfl⟩ : syracuseStep 1958621 = 734483) (by norm_num)
theorem B3302117 : Blo 1303970 3302117 := bbase (se 4 (by rfl) ⟨309573, by rfl⟩ : syracuseStep 3302117 = 619147) (by norm_num)
theorem B1467121 : Blo 1303970 1467121 := bbase (se 2 (by rfl) ⟨550170, by rfl⟩ : syracuseStep 1467121 = 1100341) (by norm_num)
theorem B1958645 : Blo 1303970 1958645 := bbase (se 5 (by rfl) ⟨91811, by rfl⟩ : syracuseStep 1958645 = 183623) (by norm_num)
theorem B1958669 : Blo 1303970 1958669 := bbase (se 3 (by rfl) ⟨367250, by rfl⟩ : syracuseStep 1958669 = 734501) (by norm_num)
theorem B1467157 : Blo 1303970 1467157 := bbase (se 6 (by rfl) ⟨34386, by rfl⟩ : syracuseStep 1467157 = 68773) (by norm_num)
theorem B1958693 : Blo 1303970 1958693 := bbase (se 4 (by rfl) ⟨183627, by rfl⟩ : syracuseStep 1958693 = 367255) (by norm_num)
theorem B1467193 : Blo 1303970 1467193 := bbase (se 2 (by rfl) ⟨550197, by rfl⟩ : syracuseStep 1467193 = 1100395) (by norm_num)
theorem B1958717 : Blo 1303970 1958717 := bbase (se 3 (by rfl) ⟨367259, by rfl⟩ : syracuseStep 1958717 = 734519) (by norm_num)
theorem B2974541 : Blo 1303970 2974541 := bbase (se 3 (by rfl) ⟨557726, by rfl⟩ : syracuseStep 2974541 = 1115453) (by norm_num)
theorem B6603605 : Blo 1303970 6603605 := bbase (se 9 (by rfl) ⟨19346, by rfl⟩ : syracuseStep 6603605 = 38693) (by norm_num)
theorem B7938901 : Blo 1303970 7938901 := bbase (se 9 (by rfl) ⟨23258, by rfl⟩ : syracuseStep 7938901 = 46517) (by norm_num)
theorem B1958741 : Blo 1303970 1958741 := bbase (se 9 (by rfl) ⟨5738, by rfl⟩ : syracuseStep 1958741 = 11477) (by norm_num)
theorem B1467229 : Blo 1303970 1467229 := bbase (se 3 (by rfl) ⟨275105, by rfl⟩ : syracuseStep 1467229 = 550211) (by norm_num)
theorem B5808997 : Blo 1303970 5808997 := bbase (se 4 (by rfl) ⟨544593, by rfl⟩ : syracuseStep 5808997 = 1089187) (by norm_num)
theorem B5956453 : Blo 1303970 5956453 := bbase (se 4 (by rfl) ⟨558417, by rfl⟩ : syracuseStep 5956453 = 1116835) (by norm_num)
theorem B1958765 : Blo 1303970 1958765 := bbase (se 3 (by rfl) ⟨367268, by rfl⟩ : syracuseStep 1958765 = 734537) (by norm_num)
theorem B1393529 : Blo 1303970 1393529 := bbase (se 2 (by rfl) ⟨522573, by rfl⟩ : syracuseStep 1393529 = 1045147) (by norm_num)
theorem B1467265 : Blo 1303970 1467265 := bbase (se 2 (by rfl) ⟨550224, by rfl⟩ : syracuseStep 1467265 = 1100449) (by norm_num)
theorem B1958789 : Blo 1303970 1958789 := bbase (se 4 (by rfl) ⟨183636, by rfl⟩ : syracuseStep 1958789 = 367273) (by norm_num)
theorem B7431061 : Blo 1303970 7431061 := bbase (se 6 (by rfl) ⟨174165, by rfl⟩ : syracuseStep 7431061 = 348331) (by norm_num)
theorem B1958813 : Blo 1303970 1958813 := bbase (se 3 (by rfl) ⟨367277, by rfl⟩ : syracuseStep 1958813 = 734555) (by norm_num)
theorem B1467301 : Blo 1303970 1467301 := bbase (se 4 (by rfl) ⟨137559, by rfl⟩ : syracuseStep 1467301 = 275119) (by norm_num)
theorem B3302309 : Blo 1303970 3302309 := bbase (se 4 (by rfl) ⟨309591, by rfl⟩ : syracuseStep 3302309 = 619183) (by norm_num)
theorem B4957109 : Blo 1303970 4957109 := bbase (se 5 (by rfl) ⟨232364, by rfl⟩ : syracuseStep 4957109 = 464729) (by norm_num)
theorem B1958837 : Blo 1303970 1958837 := bbase (se 5 (by rfl) ⟨91820, by rfl⟩ : syracuseStep 1958837 = 183641) (by norm_num)
theorem B1467337 : Blo 1303970 1467337 := bbase (se 2 (by rfl) ⟨550251, by rfl⟩ : syracuseStep 1467337 = 1100503) (by norm_num)
theorem B1958861 : Blo 1303970 1958861 := bbase (se 3 (by rfl) ⟨367286, by rfl⟩ : syracuseStep 1958861 = 734573) (by norm_num)
theorem B1958885 : Blo 1303970 1958885 := bbase (se 4 (by rfl) ⟨183645, by rfl⟩ : syracuseStep 1958885 = 367291) (by norm_num)
theorem B1467373 : Blo 1303970 1467373 := bbase (se 3 (by rfl) ⟨275132, by rfl⟩ : syracuseStep 1467373 = 550265) (by norm_num)
theorem B2647037 : Blo 1303970 2647037 := bbase (se 3 (by rfl) ⟨496319, by rfl⟩ : syracuseStep 2647037 = 992639) (by norm_num)
theorem B1958909 : Blo 1303970 1958909 := bbase (se 3 (by rfl) ⟨367295, by rfl⟩ : syracuseStep 1958909 = 734591) (by norm_num)
theorem B3965957 : Blo 1303970 3965957 := bbase (se 4 (by rfl) ⟨371808, by rfl⟩ : syracuseStep 3965957 = 743617) (by norm_num)
theorem B1467409 : Blo 1303970 1467409 := bbase (se 2 (by rfl) ⟨550278, by rfl⟩ : syracuseStep 1467409 = 1100557) (by norm_num)
theorem B8471573 : Blo 1303970 8471573 := bbase (se 6 (by rfl) ⟨198552, by rfl⟩ : syracuseStep 8471573 = 397105) (by norm_num)
theorem B7939093 : Blo 1303970 7939093 := bbase (se 6 (by rfl) ⟨186072, by rfl⟩ : syracuseStep 7939093 = 372145) (by norm_num)
theorem B1958933 : Blo 1303970 1958933 := bbase (se 6 (by rfl) ⟨45912, by rfl⟩ : syracuseStep 1958933 = 91825) (by norm_num)
theorem B2786341 : Blo 1303970 2786341 := bbase (se 4 (by rfl) ⟨261219, by rfl⟩ : syracuseStep 2786341 = 522439) (by norm_num)
theorem B2647085 : Blo 1303970 2647085 := bbase (se 3 (by rfl) ⟨496328, by rfl⟩ : syracuseStep 2647085 = 992657) (by norm_num)
theorem B1467445 : Blo 1303970 1467445 := bbase (se 5 (by rfl) ⟨68786, by rfl⟩ : syracuseStep 1467445 = 137573) (by norm_num)
theorem B5022805 : Blo 1303970 5022805 := bbase (se 8 (by rfl) ⟨29430, by rfl⟩ : syracuseStep 5022805 = 58861) (by norm_num)
theorem B1467481 : Blo 1303970 1467481 := bbase (se 2 (by rfl) ⟨550305, by rfl⟩ : syracuseStep 1467481 = 1100611) (by norm_num)
theorem B1393777 : Blo 1303970 1393777 := bbase (se 2 (by rfl) ⟨522666, by rfl⟩ : syracuseStep 1393777 = 1045333) (by norm_num)
theorem B1467517 : Blo 1303970 1467517 := bbase (se 3 (by rfl) ⟨275159, by rfl⟩ : syracuseStep 1467517 = 550319) (by norm_num)
theorem B4179077 : Blo 1303970 4179077 := bbase (se 4 (by rfl) ⟨391788, by rfl⟩ : syracuseStep 4179077 = 783577) (by norm_num)
theorem B1467553 : Blo 1303970 1467553 := bbase (se 2 (by rfl) ⟨550332, by rfl⟩ : syracuseStep 1467553 = 1100665) (by norm_num)
theorem B1467589 : Blo 1303970 1467589 := bbase (se 4 (by rfl) ⟨137586, by rfl⟩ : syracuseStep 1467589 = 275173) (by norm_num)
theorem B2933981 : Blo 1303970 2933981 := bbase (se 3 (by rfl) ⟨550121, by rfl⟩ : syracuseStep 2933981 = 1100243) (by norm_num)
theorem B1467625 : Blo 1303970 1467625 := bbase (se 2 (by rfl) ⟨550359, by rfl⟩ : syracuseStep 1467625 = 1100719) (by norm_num)
theorem B1983733 : Blo 1303970 1983733 := bbase (se 5 (by rfl) ⟨92987, by rfl⟩ : syracuseStep 1983733 = 185975) (by norm_num)
theorem B3302653 : Blo 1303970 3302653 := bbase (se 3 (by rfl) ⟨619247, by rfl⟩ : syracuseStep 3302653 = 1238495) (by norm_num)
theorem B1467661 : Blo 1303970 1467661 := bbase (se 3 (by rfl) ⟨275186, by rfl⟩ : syracuseStep 1467661 = 550373) (by norm_num)
theorem B2934053 : Blo 1303970 2934053 := bbase (se 4 (by rfl) ⟨275067, by rfl⟩ : syracuseStep 2934053 = 550135) (by norm_num)
theorem B1467697 : Blo 1303970 1467697 := bbase (se 2 (by rfl) ⟨550386, by rfl⟩ : syracuseStep 1467697 = 1100773) (by norm_num)
theorem B56411477 : Blo 1303970 56411477 := bbase (se 12 (by rfl) ⟨20658, by rfl⟩ : syracuseStep 56411477 = 41317) (by norm_num)
theorem B1467733 : Blo 1303970 1467733 := bbase (se 12 (by rfl) ⟨537, by rfl⟩ : syracuseStep 1467733 = 1075) (by norm_num)
theorem B2934125 : Blo 1303970 2934125 := bbase (se 3 (by rfl) ⟨550148, by rfl⟩ : syracuseStep 2934125 = 1100297) (by norm_num)
theorem B3302765 : Blo 1303970 3302765 := bbase (se 3 (by rfl) ⟨619268, by rfl⟩ : syracuseStep 3302765 = 1238537) (by norm_num)
theorem B1467769 : Blo 1303970 1467769 := bbase (se 2 (by rfl) ⟨550413, by rfl⟩ : syracuseStep 1467769 = 1100827) (by norm_num)
theorem B1467805 : Blo 1303970 1467805 := bbase (se 3 (by rfl) ⟨275213, by rfl⟩ : syracuseStep 1467805 = 550427) (by norm_num)
theorem B2786717 : Blo 1303970 2786717 := bbase (se 3 (by rfl) ⟨522509, by rfl⟩ : syracuseStep 2786717 = 1045019) (by norm_num)
theorem B2934197 : Blo 1303970 2934197 := bbase (se 5 (by rfl) ⟨137540, by rfl⟩ : syracuseStep 2934197 = 275081) (by norm_num)
theorem B1467841 : Blo 1303970 1467841 := bbase (se 2 (by rfl) ⟨550440, by rfl⟩ : syracuseStep 1467841 = 1100881) (by norm_num)
theorem B2090461 : Blo 1303970 2090461 := bbase (se 3 (by rfl) ⟨391961, by rfl⟩ : syracuseStep 2090461 = 783923) (by norm_num)
theorem B1762789 : Blo 1303970 1762789 := bbase (se 4 (by rfl) ⟨165261, by rfl⟩ : syracuseStep 1762789 = 330523) (by norm_num)
theorem B1467877 : Blo 1303970 1467877 := bbase (se 4 (by rfl) ⟨137613, by rfl⟩ : syracuseStep 1467877 = 275227) (by norm_num)
theorem B2934269 : Blo 1303970 2934269 := bbase (se 3 (by rfl) ⟨550175, by rfl⟩ : syracuseStep 2934269 = 1100351) (by norm_num)
theorem B2475517 : Blo 1303970 2475517 := bbase (se 3 (by rfl) ⟨464159, by rfl⟩ : syracuseStep 2475517 = 928319) (by norm_num)
theorem B6268421 : Blo 1303970 6268421 := bbase (se 4 (by rfl) ⟨587664, by rfl⟩ : syracuseStep 6268421 = 1175329) (by norm_num)
theorem B1467913 : Blo 1303970 1467913 := bbase (se 2 (by rfl) ⟨550467, by rfl⟩ : syracuseStep 1467913 = 1100935) (by norm_num)
theorem B1394209 : Blo 1303970 1394209 := bbase (se 2 (by rfl) ⟨522828, by rfl⟩ : syracuseStep 1394209 = 1045657) (by norm_num)
theorem B1467949 : Blo 1303970 1467949 := bbase (se 3 (by rfl) ⟨275240, by rfl⟩ : syracuseStep 1467949 = 550481) (by norm_num)
theorem B3302957 : Blo 1303970 3302957 := bbase (se 3 (by rfl) ⟨619304, by rfl⟩ : syracuseStep 3302957 = 1238609) (by norm_num)
theorem B2934341 : Blo 1303970 2934341 := bbase (se 4 (by rfl) ⟨275094, by rfl⟩ : syracuseStep 2934341 = 550189) (by norm_num)
theorem B1467985 : Blo 1303970 1467985 := bbase (se 2 (by rfl) ⟨550494, by rfl⟩ : syracuseStep 1467985 = 1100989) (by norm_num)
theorem B1394281 : Blo 1303970 1394281 := bbase (se 2 (by rfl) ⟨522855, by rfl⟩ : syracuseStep 1394281 = 1045711) (by norm_num)
theorem B1468021 : Blo 1303970 1468021 := bbase (se 5 (by rfl) ⟨68813, by rfl⟩ : syracuseStep 1468021 = 137627) (by norm_num)
theorem B2934413 : Blo 1303970 2934413 := bbase (se 3 (by rfl) ⟨550202, by rfl⟩ : syracuseStep 2934413 = 1100405) (by norm_num)
theorem B11904661 : Blo 1303970 11904661 := bbase (se 6 (by rfl) ⟨279015, by rfl⟩ : syracuseStep 11904661 = 558031) (by norm_num)
theorem B1468057 : Blo 1303970 1468057 := bbase (se 2 (by rfl) ⟨550521, by rfl⟩ : syracuseStep 1468057 = 1101043) (by norm_num)
theorem B2475677 : Blo 1303970 2475677 := bbase (se 3 (by rfl) ⟨464189, by rfl⟩ : syracuseStep 2475677 = 928379) (by norm_num)
theorem B1468093 : Blo 1303970 1468093 := bbase (se 3 (by rfl) ⟨275267, by rfl⟩ : syracuseStep 1468093 = 550535) (by norm_num)
theorem B2934485 : Blo 1303970 2934485 := bbase (se 7 (by rfl) ⟨34388, by rfl⟩ : syracuseStep 2934485 = 68777) (by norm_num)
theorem B4703957 : Blo 1303970 4703957 := bbase (se 7 (by rfl) ⟨55124, by rfl⟩ : syracuseStep 4703957 = 110249) (by norm_num)
theorem B1468129 : Blo 1303970 1468129 := bbase (se 2 (by rfl) ⟨550548, by rfl⟩ : syracuseStep 1468129 = 1101097) (by norm_num)
theorem B1468165 : Blo 1303970 1468165 := bbase (se 4 (by rfl) ⟨137640, by rfl⟩ : syracuseStep 1468165 = 275281) (by norm_num)
theorem B2352901 : Blo 1303970 2352901 := bbase (se 4 (by rfl) ⟨220584, by rfl⟩ : syracuseStep 2352901 = 441169) (by norm_num)
theorem B2934557 : Blo 1303970 2934557 := bbase (se 3 (by rfl) ⟨550229, by rfl⟩ : syracuseStep 2934557 = 1100459) (by norm_num)
theorem B1468201 : Blo 1303970 1468201 := bbase (se 2 (by rfl) ⟨550575, by rfl⟩ : syracuseStep 1468201 = 1101151) (by norm_num)
theorem B2475821 : Blo 1303970 2475821 := bbase (se 3 (by rfl) ⟨464216, by rfl⟩ : syracuseStep 2475821 = 928433) (by norm_num)
theorem B1468237 : Blo 1303970 1468237 := bbase (se 3 (by rfl) ⟨275294, by rfl⟩ : syracuseStep 1468237 = 550589) (by norm_num)
theorem B2934629 : Blo 1303970 2934629 := bbase (se 4 (by rfl) ⟨275121, by rfl⟩ : syracuseStep 2934629 = 550243) (by norm_num)
theorem B1468273 : Blo 1303970 1468273 := bbase (se 2 (by rfl) ⟨550602, by rfl⟩ : syracuseStep 1468273 = 1101205) (by norm_num)
theorem B3303301 : Blo 1303970 3303301 := bbase (se 4 (by rfl) ⟨309684, by rfl⟩ : syracuseStep 3303301 = 619369) (by norm_num)
theorem B1468309 : Blo 1303970 1468309 := bbase (se 6 (by rfl) ⟨34413, by rfl⟩ : syracuseStep 1468309 = 68827) (by norm_num)
theorem B21170069 : Blo 1303970 21170069 := bbase (se 6 (by rfl) ⟨496173, by rfl⟩ : syracuseStep 21170069 = 992347) (by norm_num)
theorem B1566625 : Blo 1303970 1566625 := bbase (se 2 (by rfl) ⟨587484, by rfl⟩ : syracuseStep 1566625 = 1174969) (by norm_num)
theorem B2934701 : Blo 1303970 2934701 := bbase (se 3 (by rfl) ⟨550256, by rfl⟩ : syracuseStep 2934701 = 1100513) (by norm_num)
theorem B1468345 : Blo 1303970 1468345 := bbase (se 2 (by rfl) ⟨550629, by rfl⟩ : syracuseStep 1468345 = 1101259) (by norm_num)
theorem B1468381 : Blo 1303970 1468381 := bbase (se 3 (by rfl) ⟨275321, by rfl⟩ : syracuseStep 1468381 = 550643) (by norm_num)
theorem B2934773 : Blo 1303970 2934773 := bbase (se 5 (by rfl) ⟨137567, by rfl⟩ : syracuseStep 2934773 = 275135) (by norm_num)
theorem B5572597 : Blo 1303970 5572597 := bbase (se 5 (by rfl) ⟨261215, by rfl⟩ : syracuseStep 5572597 = 522431) (by norm_num)
theorem B3303413 : Blo 1303970 3303413 := bbase (se 5 (by rfl) ⟨154847, by rfl⟩ : syracuseStep 3303413 = 309695) (by norm_num)
theorem B1468417 : Blo 1303970 1468417 := bbase (se 2 (by rfl) ⟨550656, by rfl⟩ : syracuseStep 1468417 = 1101313) (by norm_num)
theorem B5572613 : Blo 1303970 5572613 := bbase (se 4 (by rfl) ⟨522432, by rfl⟩ : syracuseStep 5572613 = 1044865) (by norm_num)
theorem B1468453 : Blo 1303970 1468453 := bbase (se 4 (by rfl) ⟨137667, by rfl⟩ : syracuseStep 1468453 = 275335) (by norm_num)
theorem B2934845 : Blo 1303970 2934845 := bbase (se 3 (by rfl) ⟨550283, by rfl⟩ : syracuseStep 2934845 = 1100567) (by norm_num)
theorem B1468489 : Blo 1303970 1468489 := bbase (se 2 (by rfl) ⟨550683, by rfl⟩ : syracuseStep 1468489 = 1101367) (by norm_num)
theorem B2476109 : Blo 1303970 2476109 := bbase (se 3 (by rfl) ⟨464270, by rfl⟩ : syracuseStep 2476109 = 928541) (by norm_num)
theorem B4958293 : Blo 1303970 4958293 := bbase (se 8 (by rfl) ⟨29052, by rfl⟩ : syracuseStep 4958293 = 58105) (by norm_num)
theorem B6604901 : Blo 1303970 6604901 := bbase (se 4 (by rfl) ⟨619209, by rfl⟩ : syracuseStep 6604901 = 1238419) (by norm_num)
theorem B1468525 : Blo 1303970 1468525 := bbase (se 3 (by rfl) ⟨275348, by rfl⟩ : syracuseStep 1468525 = 550697) (by norm_num)
theorem B4401269 : Blo 1303970 4401269 := bbase (se 5 (by rfl) ⟨206309, by rfl⟩ : syracuseStep 4401269 = 412619) (by norm_num)
theorem B2934917 : Blo 1303970 2934917 := bbase (se 4 (by rfl) ⟨275148, by rfl⟩ : syracuseStep 2934917 = 550297) (by norm_num)
theorem B1468561 : Blo 1303970 1468561 := bbase (se 2 (by rfl) ⟨550710, by rfl⟩ : syracuseStep 1468561 = 1101421) (by norm_num)
theorem B3303605 : Blo 1303970 3303605 := bbase (se 5 (by rfl) ⟨154856, by rfl⟩ : syracuseStep 3303605 = 309713) (by norm_num)
theorem B1468597 : Blo 1303970 1468597 := bbase (se 5 (by rfl) ⟨68840, by rfl⟩ : syracuseStep 1468597 = 137681) (by norm_num)
theorem B2934989 : Blo 1303970 2934989 := bbase (se 3 (by rfl) ⟨550310, by rfl⟩ : syracuseStep 2934989 = 1100621) (by norm_num)
theorem B1468633 : Blo 1303970 1468633 := bbase (se 2 (by rfl) ⟨550737, by rfl⟩ : syracuseStep 1468633 = 1101475) (by norm_num)
theorem B2476261 : Blo 1303970 2476261 := bbase (se 4 (by rfl) ⟨232149, by rfl⟩ : syracuseStep 2476261 = 464299) (by norm_num)
theorem B1468669 : Blo 1303970 1468669 := bbase (se 3 (by rfl) ⟨275375, by rfl⟩ : syracuseStep 1468669 = 550751) (by norm_num)
theorem B2935061 : Blo 1303970 2935061 := bbase (se 6 (by rfl) ⟨68790, by rfl⟩ : syracuseStep 2935061 = 137581) (by norm_num)
theorem B1468705 : Blo 1303970 1468705 := bbase (se 2 (by rfl) ⟨550764, by rfl⟩ : syracuseStep 1468705 = 1101529) (by norm_num)
theorem B1468741 : Blo 1303970 1468741 := bbase (se 4 (by rfl) ⟨137694, by rfl⟩ : syracuseStep 1468741 = 275389) (by norm_num)
theorem B2935133 : Blo 1303970 2935133 := bbase (se 3 (by rfl) ⟨550337, by rfl⟩ : syracuseStep 2935133 = 1100675) (by norm_num)
theorem B1468777 : Blo 1303970 1468777 := bbase (se 2 (by rfl) ⟨550791, by rfl⟩ : syracuseStep 1468777 = 1101583) (by norm_num)
theorem B4958597 : Blo 1303970 4958597 := bbase (se 4 (by rfl) ⟨464868, by rfl⟩ : syracuseStep 4958597 = 929737) (by norm_num)
theorem B1468813 : Blo 1303970 1468813 := bbase (se 3 (by rfl) ⟨275402, by rfl⟩ : syracuseStep 1468813 = 550805) (by norm_num)
theorem B2935205 : Blo 1303970 2935205 := bbase (se 4 (by rfl) ⟨275175, by rfl⟩ : syracuseStep 2935205 = 550351) (by norm_num)
theorem B1468849 : Blo 1303970 1468849 := bbase (se 2 (by rfl) ⟨550818, by rfl⟩ : syracuseStep 1468849 = 1101637) (by norm_num)
theorem B1468885 : Blo 1303970 1468885 := bbase (se 7 (by rfl) ⟨17213, by rfl⟩ : syracuseStep 1468885 = 34427) (by norm_num)
theorem B2935277 : Blo 1303970 2935277 := bbase (se 3 (by rfl) ⟨550364, by rfl⟩ : syracuseStep 2935277 = 1100729) (by norm_num)
theorem B1468921 : Blo 1303970 1468921 := bbase (se 2 (by rfl) ⟨550845, by rfl⟩ : syracuseStep 1468921 = 1101691) (by norm_num)
theorem B3303949 : Blo 1303970 3303949 := bbase (se 3 (by rfl) ⟨619490, by rfl⟩ : syracuseStep 3303949 = 1238981) (by norm_num)
theorem B2476565 : Blo 1303970 2476565 := bbase (se 6 (by rfl) ⟨58044, by rfl⟩ : syracuseStep 2476565 = 116089) (by norm_num)
theorem B1468957 : Blo 1303970 1468957 := bbase (se 3 (by rfl) ⟨275429, by rfl⟩ : syracuseStep 1468957 = 550859) (by norm_num)
theorem B4401701 : Blo 1303970 4401701 := bbase (se 4 (by rfl) ⟨412659, by rfl⟩ : syracuseStep 4401701 = 825319) (by norm_num)
theorem B2935349 : Blo 1303970 2935349 := bbase (se 5 (by rfl) ⟨137594, by rfl⟩ : syracuseStep 2935349 = 275189) (by norm_num)
theorem B2509373 : Blo 1303970 2509373 := bbase (se 3 (by rfl) ⟨470507, by rfl⟩ : syracuseStep 2509373 = 941015) (by norm_num)
theorem B1468993 : Blo 1303970 1468993 := bbase (se 2 (by rfl) ⟨550872, by rfl⟩ : syracuseStep 1468993 = 1101745) (by norm_num)
theorem B1411673 : Blo 1303970 1411673 := bbase (se 2 (by rfl) ⟨529377, by rfl⟩ : syracuseStep 1411673 = 1058755) (by norm_num)
theorem B1469029 : Blo 1303970 1469029 := bbase (se 4 (by rfl) ⟨137721, by rfl⟩ : syracuseStep 1469029 = 275443) (by norm_num)
theorem B2935421 : Blo 1303970 2935421 := bbase (se 3 (by rfl) ⟨550391, by rfl⟩ : syracuseStep 2935421 = 1100783) (by norm_num)
theorem B3304061 : Blo 1303970 3304061 := bbase (se 3 (by rfl) ⟨619511, by rfl⟩ : syracuseStep 3304061 = 1239023) (by norm_num)
theorem B2091653 : Blo 1303970 2091653 := bbase (se 4 (by rfl) ⟨196092, by rfl⟩ : syracuseStep 2091653 = 392185) (by norm_num)
theorem B1469065 : Blo 1303970 1469065 := bbase (se 2 (by rfl) ⟨550899, by rfl⟩ : syracuseStep 1469065 = 1101799) (by norm_num)
theorem B1469101 : Blo 1303970 1469101 := bbase (se 3 (by rfl) ⟨275456, by rfl⟩ : syracuseStep 1469101 = 550913) (by norm_num)
theorem B2935493 : Blo 1303970 2935493 := bbase (se 4 (by rfl) ⟨275202, by rfl⟩ : syracuseStep 2935493 = 550405) (by norm_num)
theorem B1469137 : Blo 1303970 1469137 := bbase (se 2 (by rfl) ⟨550926, by rfl⟩ : syracuseStep 1469137 = 1101853) (by norm_num)
theorem B1469173 : Blo 1303970 1469173 := bbase (se 5 (by rfl) ⟨68867, by rfl⟩ : syracuseStep 1469173 = 137735) (by norm_num)
theorem B2935565 : Blo 1303970 2935565 := bbase (se 3 (by rfl) ⟨550418, by rfl⟩ : syracuseStep 2935565 = 1100837) (by norm_num)
theorem B1469209 : Blo 1303970 1469209 := bbase (se 2 (by rfl) ⟨550953, by rfl⟩ : syracuseStep 1469209 = 1101907) (by norm_num)
theorem B3713845 : Blo 1303970 3713845 := bbase (se 5 (by rfl) ⟨174086, by rfl⟩ : syracuseStep 3713845 = 348173) (by norm_num)
theorem B10734389 : Blo 1303970 10734389 := bbase (se 5 (by rfl) ⟨503174, by rfl⟩ : syracuseStep 10734389 = 1006349) (by norm_num)
theorem B3304253 : Blo 1303970 3304253 := bbase (se 3 (by rfl) ⟨619547, by rfl⟩ : syracuseStep 3304253 = 1239095) (by norm_num)
theorem B2091845 : Blo 1303970 2091845 := bbase (se 4 (by rfl) ⟨196110, by rfl⟩ : syracuseStep 2091845 = 392221) (by norm_num)
theorem B2935637 : Blo 1303970 2935637 := bbase (se 9 (by rfl) ⟨8600, by rfl⟩ : syracuseStep 2935637 = 17201) (by norm_num)
theorem B7433045 : Blo 1303970 7433045 := bbase (se 9 (by rfl) ⟨21776, by rfl⟩ : syracuseStep 7433045 = 43553) (by norm_num)
theorem B6269845 : Blo 1303970 6269845 := bbase (se 6 (by rfl) ⟨146949, by rfl⟩ : syracuseStep 6269845 = 293899) (by norm_num)
theorem B2935709 : Blo 1303970 2935709 := bbase (se 3 (by rfl) ⟨550445, by rfl⟩ : syracuseStep 2935709 = 1100891) (by norm_num)
theorem B4025285 : Blo 1303970 4025285 := bbase (se 4 (by rfl) ⟨377370, by rfl⟩ : syracuseStep 4025285 = 754741) (by norm_num)
theorem B3714005 : Blo 1303970 3714005 := bbase (se 7 (by rfl) ⟨43523, by rfl⟩ : syracuseStep 3714005 = 87047) (by norm_num)
theorem B4402133 : Blo 1303970 4402133 := bbase (se 7 (by rfl) ⟨51587, by rfl⟩ : syracuseStep 4402133 = 103175) (by norm_num)
theorem B4705237 : Blo 1303970 4705237 := bbase (se 7 (by rfl) ⟨55139, by rfl⟩ : syracuseStep 4705237 = 110279) (by norm_num)
theorem B2935781 : Blo 1303970 2935781 := bbase (se 4 (by rfl) ⟨275229, by rfl⟩ : syracuseStep 2935781 = 550459) (by norm_num)
theorem B1985509 : Blo 1303970 1985509 := bbase (se 4 (by rfl) ⟨186141, by rfl⟩ : syracuseStep 1985509 = 372283) (by norm_num)
theorem B7154677 : Blo 1303970 7154677 := bbase (se 5 (by rfl) ⟨335375, by rfl⟩ : syracuseStep 7154677 = 670751) (by norm_num)
theorem B2788357 : Blo 1303970 2788357 := bbase (se 4 (by rfl) ⟨261408, by rfl⟩ : syracuseStep 2788357 = 522817) (by norm_num)
theorem B2935853 : Blo 1303970 2935853 := bbase (se 3 (by rfl) ⟨550472, by rfl⟩ : syracuseStep 2935853 = 1100945) (by norm_num)
theorem B2935925 : Blo 1303970 2935925 := bbase (se 5 (by rfl) ⟨137621, by rfl⟩ : syracuseStep 2935925 = 275243) (by norm_num)
theorem B3304597 : Blo 1303970 3304597 := bbase (se 6 (by rfl) ⟨77451, by rfl⟩ : syracuseStep 3304597 = 154903) (by norm_num)
theorem B2935997 : Blo 1303970 2935997 := bbase (se 3 (by rfl) ⟨550499, by rfl⟩ : syracuseStep 2935997 = 1100999) (by norm_num)
theorem B3714245 : Blo 1303970 3714245 := bbase (se 4 (by rfl) ⟨348210, by rfl⟩ : syracuseStep 3714245 = 696421) (by norm_num)
theorem B11144405 : Blo 1303970 11144405 := bbase (se 7 (by rfl) ⟨130598, by rfl⟩ : syracuseStep 11144405 = 261197) (by norm_num)
theorem B1764589 : Blo 1303970 1764589 := bbase (se 3 (by rfl) ⟨330860, by rfl⟩ : syracuseStep 1764589 = 661721) (by norm_num)
theorem B3525893 : Blo 1303970 3525893 := bbase (se 4 (by rfl) ⟨330552, by rfl⟩ : syracuseStep 3525893 = 661105) (by norm_num)
theorem B2936069 : Blo 1303970 2936069 := bbase (se 4 (by rfl) ⟨275256, by rfl⟩ : syracuseStep 2936069 = 550513) (by norm_num)
theorem B2477317 : Blo 1303970 2477317 := bbase (se 4 (by rfl) ⟨232248, by rfl⟩ : syracuseStep 2477317 = 464497) (by norm_num)
theorem B1568009 : Blo 1303970 1568009 := bbase (se 2 (by rfl) ⟨588003, by rfl⟩ : syracuseStep 1568009 = 1176007) (by norm_num)
theorem B3304709 : Blo 1303970 3304709 := bbase (se 4 (by rfl) ⟨309816, by rfl⟩ : syracuseStep 3304709 = 619633) (by norm_num)
theorem B2936141 : Blo 1303970 2936141 := bbase (se 3 (by rfl) ⟨550526, by rfl⟩ : syracuseStep 2936141 = 1101053) (by norm_num)
theorem B6606197 : Blo 1303970 6606197 := bbase (se 5 (by rfl) ⟨309665, by rfl⟩ : syracuseStep 6606197 = 619331) (by norm_num)
theorem B3714437 : Blo 1303970 3714437 := bbase (se 4 (by rfl) ⟨348228, by rfl⟩ : syracuseStep 3714437 = 696457) (by norm_num)
theorem B4402565 : Blo 1303970 4402565 := bbase (se 4 (by rfl) ⟨412740, by rfl⟩ : syracuseStep 4402565 = 825481) (by norm_num)
theorem B2936213 : Blo 1303970 2936213 := bbase (se 6 (by rfl) ⟨68817, by rfl⟩ : syracuseStep 2936213 = 137635) (by norm_num)
theorem B2477461 : Blo 1303970 2477461 := bbase (se 6 (by rfl) ⟨58065, by rfl⟩ : syracuseStep 2477461 = 116131) (by norm_num)
theorem B3304901 : Blo 1303970 3304901 := bbase (se 4 (by rfl) ⟨309834, by rfl⟩ : syracuseStep 3304901 = 619669) (by norm_num)
theorem B2936285 : Blo 1303970 2936285 := bbase (se 3 (by rfl) ⟨550553, by rfl⟩ : syracuseStep 2936285 = 1101107) (by norm_num)
theorem B1568269 : Blo 1303970 1568269 := bbase (se 3 (by rfl) ⟨294050, by rfl⟩ : syracuseStep 1568269 = 588101) (by norm_num)
theorem B2936357 : Blo 1303970 2936357 := bbase (se 4 (by rfl) ⟨275283, by rfl⟩ : syracuseStep 2936357 = 550567) (by norm_num)
theorem B1322537 : Blo 1303970 1322537 := bbase (se 2 (by rfl) ⟨495951, by rfl⟩ : syracuseStep 1322537 = 991903) (by norm_num)
theorem B2477621 : Blo 1303970 2477621 := bbase (se 5 (by rfl) ⟨116138, by rfl⟩ : syracuseStep 2477621 = 232277) (by norm_num)
theorem B1568317 : Blo 1303970 1568317 := bbase (se 3 (by rfl) ⟨294059, by rfl⟩ : syracuseStep 1568317 = 588119) (by norm_num)
theorem B2936429 : Blo 1303970 2936429 := bbase (se 3 (by rfl) ⟨550580, by rfl⟩ : syracuseStep 2936429 = 1101161) (by norm_num)
theorem B3526325 : Blo 1303970 3526325 := bbase (se 5 (by rfl) ⟨165296, by rfl⟩ : syracuseStep 3526325 = 330593) (by norm_num)
theorem B2936501 : Blo 1303970 2936501 := bbase (se 5 (by rfl) ⟨137648, by rfl⟩ : syracuseStep 2936501 = 275297) (by norm_num)
theorem B2477765 : Blo 1303970 2477765 := bbase (se 4 (by rfl) ⟨232290, by rfl⟩ : syracuseStep 2477765 = 464581) (by norm_num)
theorem B1650385 : Blo 1303970 1650385 := bbase (se 2 (by rfl) ⟨618894, by rfl⟩ : syracuseStep 1650385 = 1237789) (by norm_num)
theorem B2936573 : Blo 1303970 2936573 := bbase (se 3 (by rfl) ⟨550607, by rfl⟩ : syracuseStep 2936573 = 1101215) (by norm_num)
theorem B3305245 : Blo 1303970 3305245 := bbase (se 3 (by rfl) ⟨619733, by rfl⟩ : syracuseStep 3305245 = 1239467) (by norm_num)
theorem B4402997 : Blo 1303970 4402997 := bbase (se 5 (by rfl) ⟨206390, by rfl⟩ : syracuseStep 4402997 = 412781) (by norm_num)
theorem B2936645 : Blo 1303970 2936645 := bbase (se 4 (by rfl) ⟨275310, by rfl⟩ : syracuseStep 2936645 = 550621) (by norm_num)
theorem B1650557 : Blo 1303970 1650557 := bbase (se 3 (by rfl) ⟨309479, by rfl⟩ : syracuseStep 1650557 = 618959) (by norm_num)
theorem B2936717 : Blo 1303970 2936717 := bbase (se 3 (by rfl) ⟨550634, by rfl⟩ : syracuseStep 2936717 = 1101269) (by norm_num)
theorem B3305357 : Blo 1303970 3305357 := bbase (se 3 (by rfl) ⟨619754, by rfl⟩ : syracuseStep 3305357 = 1239509) (by norm_num)
theorem B1650613 : Blo 1303970 1650613 := bbase (se 5 (by rfl) ⟨77372, by rfl⟩ : syracuseStep 1650613 = 154745) (by norm_num)
theorem B2936789 : Blo 1303970 2936789 := bbase (se 7 (by rfl) ⟨34415, by rfl⟩ : syracuseStep 2936789 = 68831) (by norm_num)
theorem B2478053 : Blo 1303970 2478053 := bbase (se 4 (by rfl) ⟨232317, by rfl⟩ : syracuseStep 2478053 = 464635) (by norm_num)
theorem B1650709 : Blo 1303970 1650709 := bbase (se 6 (by rfl) ⟨38688, by rfl⟩ : syracuseStep 1650709 = 77377) (by norm_num)
theorem B2936861 : Blo 1303970 2936861 := bbase (se 3 (by rfl) ⟨550661, by rfl⟩ : syracuseStep 2936861 = 1101323) (by norm_num)
theorem B1323065 : Blo 1303970 1323065 := bbase (se 2 (by rfl) ⟨496149, by rfl⟩ : syracuseStep 1323065 = 992299) (by norm_num)
theorem B2510909 : Blo 1303970 2510909 := bbase (se 3 (by rfl) ⟨470795, by rfl⟩ : syracuseStep 2510909 = 941591) (by norm_num)
theorem B3305549 : Blo 1303970 3305549 := bbase (se 3 (by rfl) ⟨619790, by rfl⟩ : syracuseStep 3305549 = 1239581) (by norm_num)
theorem B2936933 : Blo 1303970 2936933 := bbase (se 4 (by rfl) ⟨275337, by rfl⟩ : syracuseStep 2936933 = 550675) (by norm_num)
theorem B2117749 : Blo 1303970 2117749 := bbase (se 5 (by rfl) ⟨99269, by rfl⟩ : syracuseStep 2117749 = 198539) (by norm_num)
theorem B9408629 : Blo 1303970 9408629 := bbase (se 5 (by rfl) ⟨441029, by rfl⟩ : syracuseStep 9408629 = 882059) (by norm_num)
theorem B2478205 : Blo 1303970 2478205 := bbase (se 3 (by rfl) ⟨464663, by rfl⟩ : syracuseStep 2478205 = 929327) (by norm_num)
theorem B2937005 : Blo 1303970 2937005 := bbase (se 3 (by rfl) ⟨550688, by rfl⟩ : syracuseStep 2937005 = 1101377) (by norm_num)
theorem B1650881 : Blo 1303970 1650881 := bbase (se 2 (by rfl) ⟨619080, by rfl⟩ : syracuseStep 1650881 = 1238161) (by norm_num)
theorem B5574869 : Blo 1303970 5574869 := bbase (se 7 (by rfl) ⟨65330, by rfl⟩ : syracuseStep 5574869 = 130661) (by norm_num)
theorem B4403429 : Blo 1303970 4403429 := bbase (se 4 (by rfl) ⟨412821, by rfl⟩ : syracuseStep 4403429 = 825643) (by norm_num)
theorem B2937077 : Blo 1303970 2937077 := bbase (se 5 (by rfl) ⟨137675, by rfl⟩ : syracuseStep 2937077 = 275351) (by norm_num)
theorem B1650937 : Blo 1303970 1650937 := bbase (se 2 (by rfl) ⟨619101, by rfl⟩ : syracuseStep 1650937 = 1238203) (by norm_num)
theorem B2978045 : Blo 1303970 2978045 := bbase (se 3 (by rfl) ⟨558383, by rfl⟩ : syracuseStep 2978045 = 1116767) (by norm_num)
theorem B3969317 : Blo 1303970 3969317 := bbase (se 4 (by rfl) ⟨372123, by rfl⟩ : syracuseStep 3969317 = 744247) (by norm_num)
theorem B2937149 : Blo 1303970 2937149 := bbase (se 3 (by rfl) ⟨550715, by rfl⟩ : syracuseStep 2937149 = 1101431) (by norm_num)
theorem B1323325 : Blo 1303970 1323325 := bbase (se 3 (by rfl) ⟨248123, by rfl⟩ : syracuseStep 1323325 = 496247) (by norm_num)
theorem B1651033 : Blo 1303970 1651033 := bbase (se 2 (by rfl) ⟨619137, by rfl⟩ : syracuseStep 1651033 = 1238275) (by norm_num)
theorem B3715429 : Blo 1303970 3715429 := bbase (se 4 (by rfl) ⟨348321, by rfl⟩ : syracuseStep 3715429 = 696643) (by norm_num)
theorem B2937221 : Blo 1303970 2937221 := bbase (se 4 (by rfl) ⟨275364, by rfl⟩ : syracuseStep 2937221 = 550729) (by norm_num)
theorem B1323397 : Blo 1303970 1323397 := bbase (se 4 (by rfl) ⟨124068, by rfl⟩ : syracuseStep 1323397 = 248137) (by norm_num)
theorem B2478509 : Blo 1303970 2478509 := bbase (se 3 (by rfl) ⟨464720, by rfl⟩ : syracuseStep 2478509 = 929441) (by norm_num)
theorem B3969461 : Blo 1303970 3969461 := bbase (se 5 (by rfl) ⟨186068, by rfl⟩ : syracuseStep 3969461 = 372137) (by norm_num)
theorem B2937293 : Blo 1303970 2937293 := bbase (se 3 (by rfl) ⟨550742, by rfl⟩ : syracuseStep 2937293 = 1101485) (by norm_num)
theorem B1651205 : Blo 1303970 1651205 := bbase (se 4 (by rfl) ⟨154800, by rfl⟩ : syracuseStep 1651205 = 309601) (by norm_num)
theorem B2937365 : Blo 1303970 2937365 := bbase (se 6 (by rfl) ⟨68844, by rfl⟩ : syracuseStep 2937365 = 137689) (by norm_num)
theorem B3527221 : Blo 1303970 3527221 := bbase (se 5 (by rfl) ⟨165338, by rfl⟩ : syracuseStep 3527221 = 330677) (by norm_num)
theorem B1651261 : Blo 1303970 1651261 := bbase (se 3 (by rfl) ⟨309611, by rfl⟩ : syracuseStep 1651261 = 619223) (by norm_num)
theorem B2937437 : Blo 1303970 2937437 := bbase (se 3 (by rfl) ⟨550769, by rfl⟩ : syracuseStep 2937437 = 1101539) (by norm_num)
theorem B1323649 : Blo 1303970 1323649 := bbase (se 2 (by rfl) ⟨496368, by rfl⟩ : syracuseStep 1323649 = 992737) (by norm_num)
theorem B6607493 : Blo 1303970 6607493 := bbase (se 4 (by rfl) ⟨619452, by rfl⟩ : syracuseStep 6607493 = 1238905) (by norm_num)
theorem B4403861 : Blo 1303970 4403861 := bbase (se 6 (by rfl) ⟨103215, by rfl⟩ : syracuseStep 4403861 = 206431) (by norm_num)
theorem B5952149 : Blo 1303970 5952149 := bbase (se 6 (by rfl) ⟨139503, by rfl⟩ : syracuseStep 5952149 = 279007) (by norm_num)
theorem B1651357 : Blo 1303970 1651357 := bbase (se 3 (by rfl) ⟨309629, by rfl⟩ : syracuseStep 1651357 = 619259) (by norm_num)
theorem B2937509 : Blo 1303970 2937509 := bbase (se 4 (by rfl) ⟨275391, by rfl⟩ : syracuseStep 2937509 = 550783) (by norm_num)
theorem B3764933 : Blo 1303970 3764933 := bbase (se 4 (by rfl) ⟨352962, by rfl⟩ : syracuseStep 3764933 = 705925) (by norm_num)
theorem B3134173 : Blo 1303970 3134173 := bbase (se 3 (by rfl) ⟨587657, by rfl⟩ : syracuseStep 3134173 = 1175315) (by norm_num)
theorem B2937581 : Blo 1303970 2937581 := bbase (se 3 (by rfl) ⟨550796, by rfl⟩ : syracuseStep 2937581 = 1101593) (by norm_num)
theorem B2937653 : Blo 1303970 2937653 := bbase (se 5 (by rfl) ⟨137702, by rfl⟩ : syracuseStep 2937653 = 275405) (by norm_num)
theorem B1651529 : Blo 1303970 1651529 := bbase (se 2 (by rfl) ⟨619323, by rfl⟩ : syracuseStep 1651529 = 1238647) (by norm_num)
theorem B2823005 : Blo 1303970 2823005 := bbase (se 3 (by rfl) ⟨529313, by rfl⟩ : syracuseStep 2823005 = 1058627) (by norm_num)
theorem B4952933 : Blo 1303970 4952933 := bbase (se 4 (by rfl) ⟨464337, by rfl⟩ : syracuseStep 4952933 = 928675) (by norm_num)
theorem B2937725 : Blo 1303970 2937725 := bbase (se 3 (by rfl) ⟨550823, by rfl⟩ : syracuseStep 2937725 = 1101647) (by norm_num)
theorem B1651585 : Blo 1303970 1651585 := bbase (se 2 (by rfl) ⟨619344, by rfl⟩ : syracuseStep 1651585 = 1238689) (by norm_num)
theorem B2200493 : Blo 1303970 2200493 := bbase (se 3 (by rfl) ⟨412592, by rfl⟩ : syracuseStep 2200493 = 825185) (by norm_num)
theorem B2937797 : Blo 1303970 2937797 := bbase (se 4 (by rfl) ⟨275418, by rfl⟩ : syracuseStep 2937797 = 550837) (by norm_num)
theorem B4182997 : Blo 1303970 4182997 := bbase (se 7 (by rfl) ⟨49019, by rfl⟩ : syracuseStep 4182997 = 98039) (by norm_num)
theorem B1651681 : Blo 1303970 1651681 := bbase (se 2 (by rfl) ⟨619380, by rfl⟩ : syracuseStep 1651681 = 1238761) (by norm_num)
theorem B7435253 : Blo 1303970 7435253 := bbase (se 5 (by rfl) ⟨348527, by rfl⟩ : syracuseStep 7435253 = 697055) (by norm_num)
theorem B2937869 : Blo 1303970 2937869 := bbase (se 3 (by rfl) ⟨550850, by rfl⟩ : syracuseStep 2937869 = 1101701) (by norm_num)
theorem B2200621 : Blo 1303970 2200621 := bbase (se 3 (by rfl) ⟨412616, by rfl⟩ : syracuseStep 2200621 = 825233) (by norm_num)
theorem B7935029 : Blo 1303970 7935029 := bbase (se 5 (by rfl) ⟨371954, by rfl⟩ : syracuseStep 7935029 = 743909) (by norm_num)
theorem B4404293 : Blo 1303970 4404293 := bbase (se 4 (by rfl) ⟨412902, by rfl⟩ : syracuseStep 4404293 = 825805) (by norm_num)
theorem B2937941 : Blo 1303970 2937941 := bbase (se 8 (by rfl) ⟨17214, by rfl⟩ : syracuseStep 2937941 = 34429) (by norm_num)
theorem B2200709 : Blo 1303970 2200709 := bbase (se 4 (by rfl) ⟨206316, by rfl⟩ : syracuseStep 2200709 = 412633) (by norm_num)
theorem B4953221 : Blo 1303970 4953221 := bbase (se 4 (by rfl) ⟨464364, by rfl⟩ : syracuseStep 4953221 = 928729) (by norm_num)
theorem B1651853 : Blo 1303970 1651853 := bbase (se 3 (by rfl) ⟨309722, by rfl⟩ : syracuseStep 1651853 = 619445) (by norm_num)
theorem B2938013 : Blo 1303970 2938013 := bbase (se 3 (by rfl) ⟨550877, by rfl⟩ : syracuseStep 2938013 = 1101755) (by norm_num)
theorem B2479261 : Blo 1303970 2479261 := bbase (se 3 (by rfl) ⟨464861, by rfl⟩ : syracuseStep 2479261 = 929723) (by norm_num)
theorem B1651909 : Blo 1303970 1651909 := bbase (se 4 (by rfl) ⟨154866, by rfl⟩ : syracuseStep 1651909 = 309733) (by norm_num)
theorem B4183253 : Blo 1303970 4183253 := bbase (se 7 (by rfl) ⟨49022, by rfl⟩ : syracuseStep 4183253 = 98045) (by norm_num)
theorem B3134693 : Blo 1303970 3134693 := bbase (se 4 (by rfl) ⟨293877, by rfl⟩ : syracuseStep 3134693 = 587755) (by norm_num)
theorem B2938085 : Blo 1303970 2938085 := bbase (se 4 (by rfl) ⟨275445, by rfl⟩ : syracuseStep 2938085 = 550891) (by norm_num)
theorem B2200837 : Blo 1303970 2200837 := bbase (se 4 (by rfl) ⟨206328, by rfl⟩ : syracuseStep 2200837 = 412657) (by norm_num)
theorem B1652005 : Blo 1303970 1652005 := bbase (se 4 (by rfl) ⟨154875, by rfl⟩ : syracuseStep 1652005 = 309751) (by norm_num)
theorem B2938157 : Blo 1303970 2938157 := bbase (se 3 (by rfl) ⟨550904, by rfl⟩ : syracuseStep 2938157 = 1101809) (by norm_num)
theorem B2200925 : Blo 1303970 2200925 := bbase (se 3 (by rfl) ⟨412673, by rfl⟩ : syracuseStep 2200925 = 825347) (by norm_num)
theorem B2938229 : Blo 1303970 2938229 := bbase (se 5 (by rfl) ⟨137729, by rfl⟩ : syracuseStep 2938229 = 275459) (by norm_num)
theorem B2717093 : Blo 1303970 2717093 := bbase (se 4 (by rfl) ⟨254727, by rfl⟩ : syracuseStep 2717093 = 509455) (by norm_num)
theorem B3716533 : Blo 1303970 3716533 := bbase (se 5 (by rfl) ⟨174212, by rfl⟩ : syracuseStep 3716533 = 348425) (by norm_num)
theorem B2938301 : Blo 1303970 2938301 := bbase (se 3 (by rfl) ⟨550931, by rfl⟩ : syracuseStep 2938301 = 1101863) (by norm_num)
theorem B1652177 : Blo 1303970 1652177 := bbase (se 2 (by rfl) ⟨619566, by rfl⟩ : syracuseStep 1652177 = 1239133) (by norm_num)
theorem B2201053 : Blo 1303970 2201053 := bbase (se 3 (by rfl) ⟨412697, by rfl⟩ : syracuseStep 2201053 = 825395) (by norm_num)
theorem B4404725 : Blo 1303970 4404725 := bbase (se 5 (by rfl) ⟨206471, by rfl⟩ : syracuseStep 4404725 = 412943) (by norm_num)
theorem B2938373 : Blo 1303970 2938373 := bbase (se 4 (by rfl) ⟨275472, by rfl⟩ : syracuseStep 2938373 = 550945) (by norm_num)
theorem B1652233 : Blo 1303970 1652233 := bbase (se 2 (by rfl) ⟨619587, by rfl⟩ : syracuseStep 1652233 = 1239175) (by norm_num)
theorem B2201141 : Blo 1303970 2201141 := bbase (se 5 (by rfl) ⟨103178, by rfl⟩ : syracuseStep 2201141 = 206357) (by norm_num)
theorem B3135077 : Blo 1303970 3135077 := bbase (se 4 (by rfl) ⟨293913, by rfl⟩ : syracuseStep 3135077 = 587827) (by norm_num)
theorem B1652329 : Blo 1303970 1652329 := bbase (se 2 (by rfl) ⟨619623, by rfl⟩ : syracuseStep 1652329 = 1239247) (by norm_num)
theorem B1857173 : Blo 1303970 1857173 := bbase (se 6 (by rfl) ⟨43527, by rfl⟩ : syracuseStep 1857173 = 87055) (by norm_num)
theorem B3135125 : Blo 1303970 3135125 := bbase (se 6 (by rfl) ⟨73479, by rfl⟩ : syracuseStep 3135125 = 146959) (by norm_num)
theorem B3135133 : Blo 1303970 3135133 := bbase (se 3 (by rfl) ⟨587837, by rfl⟩ : syracuseStep 3135133 = 1175675) (by norm_num)
theorem B2201269 : Blo 1303970 2201269 := bbase (se 5 (by rfl) ⟨103184, by rfl⟩ : syracuseStep 2201269 = 206369) (by norm_num)
theorem B3765973 : Blo 1303970 3765973 := bbase (se 7 (by rfl) ⟨44132, by rfl⟩ : syracuseStep 3765973 = 88265) (by norm_num)
theorem B2201357 : Blo 1303970 2201357 := bbase (se 3 (by rfl) ⟨412754, by rfl⟩ : syracuseStep 2201357 = 825509) (by norm_num)
theorem B1652501 : Blo 1303970 1652501 := bbase (se 6 (by rfl) ⟨38730, by rfl⟩ : syracuseStep 1652501 = 77461) (by norm_num)
theorem B1652557 : Blo 1303970 1652557 := bbase (se 3 (by rfl) ⟨309854, by rfl⟩ : syracuseStep 1652557 = 619709) (by norm_num)
theorem B2201485 : Blo 1303970 2201485 := bbase (se 3 (by rfl) ⟨412778, by rfl⟩ : syracuseStep 2201485 = 825557) (by norm_num)
theorem B6608789 : Blo 1303970 6608789 := bbase (se 6 (by rfl) ⟨154893, by rfl⟩ : syracuseStep 6608789 = 309787) (by norm_num)
theorem B4405157 : Blo 1303970 4405157 := bbase (se 4 (by rfl) ⟨412983, by rfl⟩ : syracuseStep 4405157 = 825967) (by norm_num)
theorem B1652653 : Blo 1303970 1652653 := bbase (se 3 (by rfl) ⟨309872, by rfl⟩ : syracuseStep 1652653 = 619745) (by norm_num)
theorem B2119645 : Blo 1303970 2119645 := bbase (se 3 (by rfl) ⟨397433, by rfl⟩ : syracuseStep 2119645 = 794867) (by norm_num)
theorem B2578405 : Blo 1303970 2578405 := bbase (se 4 (by rfl) ⟨241725, by rfl⟩ : syracuseStep 2578405 = 483451) (by norm_num)
theorem B2201573 : Blo 1303970 2201573 := bbase (se 4 (by rfl) ⟨206397, by rfl⟩ : syracuseStep 2201573 = 412795) (by norm_num)
theorem B1652825 : Blo 1303970 1652825 := bbase (se 2 (by rfl) ⟨619809, by rfl⟩ : syracuseStep 1652825 = 1239619) (by norm_num)
theorem B2201701 : Blo 1303970 2201701 := bbase (se 4 (by rfl) ⟨206409, by rfl⟩ : syracuseStep 2201701 = 412819) (by norm_num)
theorem B1955957 : Blo 1303970 1955957 := bbase (se 5 (by rfl) ⟨91685, by rfl⟩ : syracuseStep 1955957 = 183371) (by norm_num)
theorem B11147381 : Blo 1303970 11147381 := bbase (se 5 (by rfl) ⟨522533, by rfl⟩ : syracuseStep 11147381 = 1045067) (by norm_num)
theorem B1955981 : Blo 1303970 1955981 := bbase (se 3 (by rfl) ⟨366746, by rfl⟩ : syracuseStep 1955981 = 733493) (by norm_num)
theorem B1956005 : Blo 1303970 1956005 := bbase (se 4 (by rfl) ⟨183375, by rfl⟩ : syracuseStep 1956005 = 366751) (by norm_num)
theorem B2119853 : Blo 1303970 2119853 := bbase (se 3 (by rfl) ⟨397472, by rfl⟩ : syracuseStep 2119853 = 794945) (by norm_num)
theorem B1956029 : Blo 1303970 1956029 := bbase (se 3 (by rfl) ⟨366755, by rfl⟩ : syracuseStep 1956029 = 733511) (by norm_num)
theorem B2201789 : Blo 1303970 2201789 := bbase (se 3 (by rfl) ⟨412835, by rfl⟩ : syracuseStep 2201789 = 825671) (by norm_num)
theorem B1956053 : Blo 1303970 1956053 := bbase (se 7 (by rfl) ⟨22922, by rfl⟩ : syracuseStep 1956053 = 45845) (by norm_num)
theorem B1956077 : Blo 1303970 1956077 := bbase (se 3 (by rfl) ⟨366764, by rfl⟩ : syracuseStep 1956077 = 733529) (by norm_num)
theorem B1956101 : Blo 1303970 1956101 := bbase (se 4 (by rfl) ⟨183384, by rfl⟩ : syracuseStep 1956101 = 366769) (by norm_num)
theorem B1956125 : Blo 1303970 1956125 := bbase (se 3 (by rfl) ⟨366773, by rfl⟩ : syracuseStep 1956125 = 733547) (by norm_num)
theorem B4954405 : Blo 1303970 4954405 := bbase (se 4 (by rfl) ⟨464475, by rfl⟩ : syracuseStep 4954405 = 928951) (by norm_num)
theorem B1956149 : Blo 1303970 1956149 := bbase (se 5 (by rfl) ⟨91694, by rfl⟩ : syracuseStep 1956149 = 183389) (by norm_num)
theorem B2201917 : Blo 1303970 2201917 := bbase (se 3 (by rfl) ⟨412859, by rfl⟩ : syracuseStep 2201917 = 825719) (by norm_num)
theorem B1956173 : Blo 1303970 1956173 := bbase (se 3 (by rfl) ⟨366782, by rfl⟩ : syracuseStep 1956173 = 733565) (by norm_num)
theorem B4405589 : Blo 1303970 4405589 := bbase (se 10 (by rfl) ⟨6453, by rfl⟩ : syracuseStep 4405589 = 12907) (by norm_num)
theorem B1956197 : Blo 1303970 1956197 := bbase (se 4 (by rfl) ⟨183393, by rfl⟩ : syracuseStep 1956197 = 366787) (by norm_num)
theorem B1956221 : Blo 1303970 1956221 := bbase (se 3 (by rfl) ⟨366791, by rfl⟩ : syracuseStep 1956221 = 733583) (by norm_num)
theorem B1857925 : Blo 1303970 1857925 := bbase (se 4 (by rfl) ⟨174180, by rfl⟩ : syracuseStep 1857925 = 348361) (by norm_num)
theorem B1956245 : Blo 1303970 1956245 := bbase (se 6 (by rfl) ⟨45849, by rfl⟩ : syracuseStep 1956245 = 91699) (by norm_num)
theorem B2202005 : Blo 1303970 2202005 := bbase (se 6 (by rfl) ⟨51609, by rfl⟩ : syracuseStep 2202005 = 103219) (by norm_num)
theorem B1956269 : Blo 1303970 1956269 := bbase (se 3 (by rfl) ⟨366800, by rfl⟩ : syracuseStep 1956269 = 733601) (by norm_num)
theorem B1956293 : Blo 1303970 1956293 := bbase (se 4 (by rfl) ⟨183402, by rfl⟩ : syracuseStep 1956293 = 366805) (by norm_num)
theorem B1956317 : Blo 1303970 1956317 := bbase (se 3 (by rfl) ⟨366809, by rfl⟩ : syracuseStep 1956317 = 733619) (by norm_num)
theorem B1956341 : Blo 1303970 1956341 := bbase (se 5 (by rfl) ⟨91703, by rfl⟩ : syracuseStep 1956341 = 183407) (by norm_num)
theorem B1956365 : Blo 1303970 1956365 := bbase (se 3 (by rfl) ⟨366818, by rfl⟩ : syracuseStep 1956365 = 733637) (by norm_num)
theorem B2202133 : Blo 1303970 2202133 := bbase (se 6 (by rfl) ⟨51612, by rfl⟩ : syracuseStep 2202133 = 103225) (by norm_num)
theorem B1956389 : Blo 1303970 1956389 := bbase (se 4 (by rfl) ⟨183411, by rfl⟩ : syracuseStep 1956389 = 366823) (by norm_num)
theorem B1956413 : Blo 1303970 1956413 := bbase (se 3 (by rfl) ⟨366827, by rfl⟩ : syracuseStep 1956413 = 733655) (by norm_num)
theorem B1956437 : Blo 1303970 1956437 := bbase (se 8 (by rfl) ⟨11463, by rfl⟩ : syracuseStep 1956437 = 22927) (by norm_num)
theorem B4954709 : Blo 1303970 4954709 := bbase (se 8 (by rfl) ⟨29031, by rfl⟩ : syracuseStep 4954709 = 58063) (by norm_num)
theorem B1956461 : Blo 1303970 1956461 := bbase (se 3 (by rfl) ⟨366836, by rfl⟩ : syracuseStep 1956461 = 733673) (by norm_num)
theorem B2202221 : Blo 1303970 2202221 := bbase (se 3 (by rfl) ⟨412916, by rfl⟩ : syracuseStep 2202221 = 825833) (by norm_num)
theorem B1956485 : Blo 1303970 1956485 := bbase (se 4 (by rfl) ⟨183420, by rfl⟩ : syracuseStep 1956485 = 366841) (by norm_num)
theorem B4463237 : Blo 1303970 4463237 := bbase (se 4 (by rfl) ⟨418428, by rfl⟩ : syracuseStep 4463237 = 836857) (by norm_num)
theorem B3136133 : Blo 1303970 3136133 := bbase (se 4 (by rfl) ⟨294012, by rfl⟩ : syracuseStep 3136133 = 588025) (by norm_num)
theorem B1956509 : Blo 1303970 1956509 := bbase (se 3 (by rfl) ⟨366845, by rfl⟩ : syracuseStep 1956509 = 733691) (by norm_num)
theorem B1956533 : Blo 1303970 1956533 := bbase (se 5 (by rfl) ⟨91712, by rfl⟩ : syracuseStep 1956533 = 183425) (by norm_num)
theorem B1956557 : Blo 1303970 1956557 := bbase (se 3 (by rfl) ⟨366854, by rfl⟩ : syracuseStep 1956557 = 733709) (by norm_num)
theorem B9910997 : Blo 1303970 9910997 := bbase (se 7 (by rfl) ⟨116144, by rfl⟩ : syracuseStep 9910997 = 232289) (by norm_num)
theorem B1956581 : Blo 1303970 1956581 := bbase (se 4 (by rfl) ⟨183429, by rfl⟩ : syracuseStep 1956581 = 366859) (by norm_num)
theorem B4463333 : Blo 1303970 4463333 := bbase (se 4 (by rfl) ⟨418437, by rfl⟩ : syracuseStep 4463333 = 836875) (by norm_num)
theorem B2202349 : Blo 1303970 2202349 := bbase (se 3 (by rfl) ⟨412940, by rfl⟩ : syracuseStep 2202349 = 825881) (by norm_num)
theorem B1956605 : Blo 1303970 1956605 := bbase (se 3 (by rfl) ⟨366863, by rfl⟩ : syracuseStep 1956605 = 733727) (by norm_num)
theorem B4406021 : Blo 1303970 4406021 := bbase (se 4 (by rfl) ⟨413064, by rfl⟩ : syracuseStep 4406021 = 826129) (by norm_num)
theorem B1956629 : Blo 1303970 1956629 := bbase (se 6 (by rfl) ⟨45858, by rfl⟩ : syracuseStep 1956629 = 91717) (by norm_num)
theorem B1956653 : Blo 1303970 1956653 := bbase (se 3 (by rfl) ⟨366872, by rfl⟩ : syracuseStep 1956653 = 733745) (by norm_num)
theorem B1956677 : Blo 1303970 1956677 := bbase (se 4 (by rfl) ⟨183438, by rfl⟩ : syracuseStep 1956677 = 366877) (by norm_num)
theorem B2202437 : Blo 1303970 2202437 := bbase (se 4 (by rfl) ⟨206478, by rfl⟩ : syracuseStep 2202437 = 412957) (by norm_num)
theorem B3136325 : Blo 1303970 3136325 := bbase (se 4 (by rfl) ⟨294030, by rfl⟩ : syracuseStep 3136325 = 588061) (by norm_num)
theorem B1956701 : Blo 1303970 1956701 := bbase (se 3 (by rfl) ⟨366881, by rfl⟩ : syracuseStep 1956701 = 733763) (by norm_num)
theorem B1956725 : Blo 1303970 1956725 := bbase (se 5 (by rfl) ⟨91721, by rfl⟩ : syracuseStep 1956725 = 183443) (by norm_num)
theorem B1956749 : Blo 1303970 1956749 := bbase (se 3 (by rfl) ⟨366890, by rfl⟩ : syracuseStep 1956749 = 733781) (by norm_num)
theorem B3718037 : Blo 1303970 3718037 := bbase (se 6 (by rfl) ⟨87141, by rfl⟩ : syracuseStep 3718037 = 174283) (by norm_num)
theorem B1956773 : Blo 1303970 1956773 := bbase (se 4 (by rfl) ⟨183447, by rfl⟩ : syracuseStep 1956773 = 366895) (by norm_num)
theorem B1956797 : Blo 1303970 1956797 := bbase (se 3 (by rfl) ⟨366899, by rfl⟩ : syracuseStep 1956797 = 733799) (by norm_num)
theorem B2202565 : Blo 1303970 2202565 := bbase (se 4 (by rfl) ⟨206490, by rfl⟩ : syracuseStep 2202565 = 412981) (by norm_num)
theorem B1956821 : Blo 1303970 1956821 := bbase (se 7 (by rfl) ⟨22931, by rfl⟩ : syracuseStep 1956821 = 45863) (by norm_num)
theorem B1956845 : Blo 1303970 1956845 := bbase (se 3 (by rfl) ⟨366908, by rfl⟩ : syracuseStep 1956845 = 733817) (by norm_num)
theorem B8362997 : Blo 1303970 8362997 := bbase (se 5 (by rfl) ⟨392015, by rfl⟩ : syracuseStep 8362997 = 784031) (by norm_num)
theorem B1956869 : Blo 1303970 1956869 := bbase (se 4 (by rfl) ⟨183456, by rfl⟩ : syracuseStep 1956869 = 366913) (by norm_num)
theorem B1956893 : Blo 1303970 1956893 := bbase (se 3 (by rfl) ⟨366917, by rfl⟩ : syracuseStep 1956893 = 733835) (by norm_num)
theorem B2202653 : Blo 1303970 2202653 := bbase (se 3 (by rfl) ⟨412997, by rfl⟩ : syracuseStep 2202653 = 825995) (by norm_num)
theorem B1956917 : Blo 1303970 1956917 := bbase (se 5 (by rfl) ⟨91730, by rfl⟩ : syracuseStep 1956917 = 183461) (by norm_num)
theorem B1956941 : Blo 1303970 1956941 := bbase (se 3 (by rfl) ⟨366926, by rfl⟩ : syracuseStep 1956941 = 733853) (by norm_num)
theorem B2825293 : Blo 1303970 2825293 := bbase (se 3 (by rfl) ⟨529742, by rfl⟩ : syracuseStep 2825293 = 1059485) (by norm_num)
theorem B1956965 : Blo 1303970 1956965 := bbase (se 4 (by rfl) ⟨183465, by rfl⟩ : syracuseStep 1956965 = 366931) (by norm_num)
theorem B9903221 : Blo 1303970 9903221 := bbase (se 5 (by rfl) ⟨464213, by rfl⟩ : syracuseStep 9903221 = 928427) (by norm_num)
theorem B1956989 : Blo 1303970 1956989 := bbase (se 3 (by rfl) ⟨366935, by rfl⟩ : syracuseStep 1956989 = 733871) (by norm_num)
theorem B1957013 : Blo 1303970 1957013 := bbase (se 6 (by rfl) ⟨45867, by rfl⟩ : syracuseStep 1957013 = 91735) (by norm_num)
theorem B2202781 : Blo 1303970 2202781 := bbase (se 3 (by rfl) ⟨413021, by rfl⟩ : syracuseStep 2202781 = 826043) (by norm_num)
theorem B1858717 : Blo 1303970 1858717 := bbase (se 3 (by rfl) ⟨348509, by rfl⟩ : syracuseStep 1858717 = 697019) (by norm_num)
theorem B5291173 : Blo 1303970 5291173 := bbase (se 4 (by rfl) ⟨496047, by rfl⟩ : syracuseStep 5291173 = 992095) (by norm_num)
theorem B6610085 : Blo 1303970 6610085 := bbase (se 4 (by rfl) ⟨619695, by rfl⟩ : syracuseStep 6610085 = 1239391) (by norm_num)
theorem B1957037 : Blo 1303970 1957037 := bbase (se 3 (by rfl) ⟨366944, by rfl⟩ : syracuseStep 1957037 = 733889) (by norm_num)
theorem B2645173 : Blo 1303970 2645173 := bbase (se 5 (by rfl) ⟨123992, by rfl⟩ : syracuseStep 2645173 = 247985) (by norm_num)
theorem B5291189 : Blo 1303970 5291189 := bbase (se 5 (by rfl) ⟨248024, by rfl⟩ : syracuseStep 5291189 = 496049) (by norm_num)
theorem B4406453 : Blo 1303970 4406453 := bbase (se 5 (by rfl) ⟨206552, by rfl⟩ : syracuseStep 4406453 = 413105) (by norm_num)
theorem B1957061 : Blo 1303970 1957061 := bbase (se 4 (by rfl) ⟨183474, by rfl⟩ : syracuseStep 1957061 = 366949) (by norm_num)
theorem B3529925 : Blo 1303970 3529925 := bbase (se 4 (by rfl) ⟨330930, by rfl⟩ : syracuseStep 3529925 = 661861) (by norm_num)
theorem B1957085 : Blo 1303970 1957085 := bbase (se 3 (by rfl) ⟨366953, by rfl⟩ : syracuseStep 1957085 = 733907) (by norm_num)
theorem B1957109 : Blo 1303970 1957109 := bbase (se 5 (by rfl) ⟨91739, by rfl⟩ : syracuseStep 1957109 = 183479) (by norm_num)
theorem B2202869 : Blo 1303970 2202869 := bbase (se 5 (by rfl) ⟨103259, by rfl⟩ : syracuseStep 2202869 = 206519) (by norm_num)
theorem B6790405 : Blo 1303970 6790405 := bbase (se 4 (by rfl) ⟨636600, by rfl⟩ : syracuseStep 6790405 = 1273201) (by norm_num)
theorem B1957133 : Blo 1303970 1957133 := bbase (se 3 (by rfl) ⟨366962, by rfl⟩ : syracuseStep 1957133 = 733925) (by norm_num)
theorem B1957157 : Blo 1303970 1957157 := bbase (se 4 (by rfl) ⟨183483, by rfl⟩ : syracuseStep 1957157 = 366967) (by norm_num)
theorem B1957181 : Blo 1303970 1957181 := bbase (se 3 (by rfl) ⟨366971, by rfl⟩ : syracuseStep 1957181 = 733943) (by norm_num)
theorem B1957205 : Blo 1303970 1957205 := bbase (se 11 (by rfl) ⟨1433, by rfl⟩ : syracuseStep 1957205 = 2867) (by norm_num)
theorem B3300709 : Blo 1303970 3300709 := bbase (se 4 (by rfl) ⟨309441, by rfl⟩ : syracuseStep 3300709 = 618883) (by norm_num)
theorem B1957229 : Blo 1303970 1957229 := bbase (se 3 (by rfl) ⟨366980, by rfl⟩ : syracuseStep 1957229 = 733961) (by norm_num)
theorem B4234613 : Blo 1303970 4234613 := bbase (se 5 (by rfl) ⟨198497, by rfl⟩ : syracuseStep 4234613 = 396995) (by norm_num)
theorem B2202997 : Blo 1303970 2202997 := bbase (se 5 (by rfl) ⟨103265, by rfl⟩ : syracuseStep 2202997 = 206531) (by norm_num)
theorem B1957253 : Blo 1303970 1957253 := bbase (se 4 (by rfl) ⟨183492, by rfl⟩ : syracuseStep 1957253 = 366985) (by norm_num)
theorem B1957277 : Blo 1303970 1957277 := bbase (se 3 (by rfl) ⟨366989, by rfl⟩ : syracuseStep 1957277 = 733979) (by norm_num)
theorem B1957301 : Blo 1303970 1957301 := bbase (se 5 (by rfl) ⟨91748, by rfl⟩ : syracuseStep 1957301 = 183497) (by norm_num)
theorem B1957325 : Blo 1303970 1957325 := bbase (se 3 (by rfl) ⟨366998, by rfl⟩ : syracuseStep 1957325 = 733997) (by norm_num)
theorem B2203085 : Blo 1303970 2203085 := bbase (se 3 (by rfl) ⟨413078, by rfl⟩ : syracuseStep 2203085 = 826157) (by norm_num)
theorem B3300821 : Blo 1303970 3300821 := bbase (se 7 (by rfl) ⟨38681, by rfl⟩ : syracuseStep 3300821 = 77363) (by norm_num)
theorem B1957349 : Blo 1303970 1957349 := bbase (se 4 (by rfl) ⟨183501, by rfl⟩ : syracuseStep 1957349 = 367003) (by norm_num)
theorem B1859053 : Blo 1303970 1859053 := bbase (se 3 (by rfl) ⟨348572, by rfl⟩ : syracuseStep 1859053 = 697145) (by norm_num)
theorem B1957373 : Blo 1303970 1957373 := bbase (se 3 (by rfl) ⟨367007, by rfl⟩ : syracuseStep 1957373 = 734015) (by norm_num)
theorem B1957397 : Blo 1303970 1957397 := bbase (se 6 (by rfl) ⟨45876, by rfl⟩ : syracuseStep 1957397 = 91753) (by norm_num)
theorem B1957421 : Blo 1303970 1957421 := bbase (se 3 (by rfl) ⟨367016, by rfl⟩ : syracuseStep 1957421 = 734033) (by norm_num)
theorem B6602309 : Blo 1303970 6602309 := bbase (se 4 (by rfl) ⟨618966, by rfl⟩ : syracuseStep 6602309 = 1237933) (by norm_num)
theorem B1957445 : Blo 1303970 1957445 := bbase (se 4 (by rfl) ⟨183510, by rfl⟩ : syracuseStep 1957445 = 367021) (by norm_num)
theorem B2203213 : Blo 1303970 2203213 := bbase (se 3 (by rfl) ⟨413102, by rfl⟩ : syracuseStep 2203213 = 826205) (by norm_num)
theorem B1957469 : Blo 1303970 1957469 := bbase (se 3 (by rfl) ⟨367025, by rfl⟩ : syracuseStep 1957469 = 734051) (by norm_num)
theorem B4406885 : Blo 1303970 4406885 := bbase (se 4 (by rfl) ⟨413145, by rfl⟩ : syracuseStep 4406885 = 826291) (by norm_num)
theorem B1957493 : Blo 1303970 1957493 := bbase (se 5 (by rfl) ⟨91757, by rfl⟩ : syracuseStep 1957493 = 183515) (by norm_num)
theorem B1957517 : Blo 1303970 1957517 := bbase (se 3 (by rfl) ⟨367034, by rfl⟩ : syracuseStep 1957517 = 734069) (by norm_num)
theorem B3301013 : Blo 1303970 3301013 := bbase (se 6 (by rfl) ⟨77367, by rfl⟩ : syracuseStep 3301013 = 154735) (by norm_num)
theorem B6274709 : Blo 1303970 6274709 := bbase (se 6 (by rfl) ⟨147063, by rfl⟩ : syracuseStep 6274709 = 294127) (by norm_num)
theorem B1957541 : Blo 1303970 1957541 := bbase (se 4 (by rfl) ⟨183519, by rfl⟩ : syracuseStep 1957541 = 367039) (by norm_num)
theorem B2203301 : Blo 1303970 2203301 := bbase (se 4 (by rfl) ⟨206559, by rfl⟩ : syracuseStep 2203301 = 413119) (by norm_num)
theorem B2645693 : Blo 1303970 2645693 := bbase (se 3 (by rfl) ⟨496067, by rfl⟩ : syracuseStep 2645693 = 992135) (by norm_num)
theorem B1957565 : Blo 1303970 1957565 := bbase (se 3 (by rfl) ⟨367043, by rfl⟩ : syracuseStep 1957565 = 734087) (by norm_num)
theorem B1859269 : Blo 1303970 1859269 := bbase (se 4 (by rfl) ⟨174306, by rfl⟩ : syracuseStep 1859269 = 348613) (by norm_num)
theorem B1957589 : Blo 1303970 1957589 := bbase (se 7 (by rfl) ⟨22940, by rfl⟩ : syracuseStep 1957589 = 45881) (by norm_num)
theorem B1957613 : Blo 1303970 1957613 := bbase (se 3 (by rfl) ⟨367052, by rfl⟩ : syracuseStep 1957613 = 734105) (by norm_num)
theorem B7429877 : Blo 1303970 7429877 := bbase (se 5 (by rfl) ⟨348275, by rfl⟩ : syracuseStep 7429877 = 696551) (by norm_num)
theorem B1957637 : Blo 1303970 1957637 := bbase (se 4 (by rfl) ⟨183528, by rfl⟩ : syracuseStep 1957637 = 367057) (by norm_num)
theorem B1957661 : Blo 1303970 1957661 := bbase (se 3 (by rfl) ⟨367061, by rfl⟩ : syracuseStep 1957661 = 734123) (by norm_num)
theorem B2203429 : Blo 1303970 2203429 := bbase (se 4 (by rfl) ⟨206571, by rfl⟩ : syracuseStep 2203429 = 413143) (by norm_num)
theorem B1957685 : Blo 1303970 1957685 := bbase (se 5 (by rfl) ⟨91766, by rfl⟩ : syracuseStep 1957685 = 183533) (by norm_num)
theorem B1957709 : Blo 1303970 1957709 := bbase (se 3 (by rfl) ⟨367070, by rfl⟩ : syracuseStep 1957709 = 734141) (by norm_num)
theorem B1957733 : Blo 1303970 1957733 := bbase (se 4 (by rfl) ⟨183537, by rfl⟩ : syracuseStep 1957733 = 367075) (by norm_num)
theorem B2088821 : Blo 1303970 2088821 := bbase (se 5 (by rfl) ⟨97913, by rfl⟩ : syracuseStep 2088821 = 195827) (by norm_num)
theorem B1957757 : Blo 1303970 1957757 := bbase (se 3 (by rfl) ⟨367079, by rfl⟩ : syracuseStep 1957757 = 734159) (by norm_num)
theorem B2203517 : Blo 1303970 2203517 := bbase (se 3 (by rfl) ⟨413159, by rfl⟩ : syracuseStep 2203517 = 826319) (by norm_num)
theorem B1957781 : Blo 1303970 1957781 := bbase (se 6 (by rfl) ⟨45885, by rfl⟩ : syracuseStep 1957781 = 91771) (by norm_num)
theorem B2383781 : Blo 1303970 2383781 := bbase (se 4 (by rfl) ⟨223479, by rfl⟩ : syracuseStep 2383781 = 446959) (by norm_num)
theorem B1957805 : Blo 1303970 1957805 := bbase (se 3 (by rfl) ⟨367088, by rfl⟩ : syracuseStep 1957805 = 734177) (by norm_num)
theorem B2785205 : Blo 1303970 2785205 := bbase (se 5 (by rfl) ⟨130556, by rfl⟩ : syracuseStep 2785205 = 261113) (by norm_num)
theorem B2785213 : Blo 1303970 2785213 := bbase (se 3 (by rfl) ⟨522227, by rfl⟩ : syracuseStep 2785213 = 1044455) (by norm_num)
theorem B1957829 : Blo 1303970 1957829 := bbase (se 4 (by rfl) ⟨183546, by rfl⟩ : syracuseStep 1957829 = 367093) (by norm_num)
theorem B1957853 : Blo 1303970 1957853 := bbase (se 3 (by rfl) ⟨367097, by rfl⟩ : syracuseStep 1957853 = 734195) (by norm_num)
theorem B3301357 : Blo 1303970 3301357 := bbase (se 3 (by rfl) ⟨619004, by rfl⟩ : syracuseStep 3301357 = 1238009) (by norm_num)
theorem B1957877 : Blo 1303970 1957877 := bbase (se 5 (by rfl) ⟨91775, by rfl⟩ : syracuseStep 1957877 = 183551) (by norm_num)
theorem B2203645 : Blo 1303970 2203645 := bbase (se 3 (by rfl) ⟨413183, by rfl⟩ : syracuseStep 2203645 = 826367) (by norm_num)
theorem B1957889 : Blo 1303970 1957889 := bstep (se 2 (by rfl) ⟨734208, by rfl⟩ : syracuseStep 1957889 = 1468417) B1468417
theorem B1957907 : Blo 1303970 1957907 := bstep (se 1 (by rfl) ⟨1468430, by rfl⟩ : syracuseStep 1957907 = 2936861) B2936861
theorem B3178531 : Blo 1303970 3178531 := bstep (se 1 (by rfl) ⟨2383898, by rfl⟩ : syracuseStep 3178531 = 4767797) B4767797
theorem B1957937 : Blo 1303970 1957937 := bstep (se 2 (by rfl) ⟨734226, by rfl⟩ : syracuseStep 1957937 = 1468453) B1468453
theorem B2203699 : Blo 1303970 2203699 := bstep (se 1 (by rfl) ⟨1652774, by rfl⟩ : syracuseStep 2203699 = 3305549) B3305549
theorem B1957955 : Blo 1303970 1957955 := bstep (se 1 (by rfl) ⟨1468466, by rfl⟩ : syracuseStep 1957955 = 2936933) B2936933
theorem B1957985 : Blo 1303970 1957985 := bstep (se 2 (by rfl) ⟨734244, by rfl⟩ : syracuseStep 1957985 = 1468489) B1468489
theorem B6275171 : Blo 1303970 6275171 := bstep (se 1 (by rfl) ⟨4706378, by rfl⟩ : syracuseStep 6275171 = 9412757) B9412757
theorem B6611057 : Blo 1303970 6611057 := bstep (se 2 (by rfl) ⟨2479146, by rfl⟩ : syracuseStep 6611057 = 4958293) B4958293
theorem B1958003 : Blo 1303970 1958003 := bstep (se 1 (by rfl) ⟨1468502, by rfl⟩ : syracuseStep 1958003 = 2937005) B2937005
theorem B4178051 : Blo 1303970 4178051 := bstep (se 1 (by rfl) ⟨3133538, by rfl⟩ : syracuseStep 4178051 = 6267077) B6267077
theorem B1958033 : Blo 1303970 1958033 := bstep (se 2 (by rfl) ⟨734262, by rfl⟩ : syracuseStep 1958033 = 1468525) B1468525
theorem B1958051 : Blo 1303970 1958051 := bstep (se 1 (by rfl) ⟨1468538, by rfl⟩ : syracuseStep 1958051 = 2937077) B2937077
theorem B1958081 : Blo 1303970 1958081 := bstep (se 2 (by rfl) ⟨734280, by rfl⟩ : syracuseStep 1958081 = 1468561) B1468561
theorem B2646211 : Blo 1303970 2646211 := bstep (se 1 (by rfl) ⟨1984658, by rfl⟩ : syracuseStep 2646211 = 3969317) B3969317
theorem B6602957 : Blo 1303970 6602957 := bstep (se 3 (by rfl) ⟨1238054, by rfl⟩ : syracuseStep 6602957 = 2476109) B2476109
theorem B1958099 : Blo 1303970 1958099 := bstep (se 1 (by rfl) ⟨1468574, by rfl⟩ : syracuseStep 1958099 = 2937149) B2937149
theorem B4407533 : Blo 1303970 4407533 := bstep (se 3 (by rfl) ⟨826412, by rfl⟩ : syracuseStep 4407533 = 1652825) B1652825
theorem B1958129 : Blo 1303970 1958129 := bstep (se 2 (by rfl) ⟨734298, by rfl⟩ : syracuseStep 1958129 = 1468597) B1468597
theorem B1958147 : Blo 1303970 1958147 := bstep (se 1 (by rfl) ⟨1468610, by rfl⟩ : syracuseStep 1958147 = 2937221) B2937221
theorem B1958177 : Blo 1303970 1958177 := bstep (se 2 (by rfl) ⟨734316, by rfl⟩ : syracuseStep 1958177 = 1468633) B1468633
theorem B2646307 : Blo 1303970 2646307 := bstep (se 1 (by rfl) ⟨1984730, by rfl⟩ : syracuseStep 2646307 = 3969461) B3969461
theorem B4407587 : Blo 1303970 4407587 := bstep (se 1 (by rfl) ⟨3305690, by rfl⟩ : syracuseStep 4407587 = 6611381) B6611381
theorem B3301681 : Blo 1303970 3301681 := bstep (se 2 (by rfl) ⟨1238130, by rfl⟩ : syracuseStep 3301681 = 2476261) B2476261
theorem B1958195 : Blo 1303970 1958195 := bstep (se 1 (by rfl) ⟨1468646, by rfl⟩ : syracuseStep 1958195 = 2937293) B2937293
theorem B35742005 : Blo 1303970 35742005 := bstep (se 5 (by rfl) ⟨1675406, by rfl⟩ : syracuseStep 35742005 = 3350813) B3350813
theorem B1958225 : Blo 1303970 1958225 := bstep (se 2 (by rfl) ⟨734334, by rfl⟩ : syracuseStep 1958225 = 1468669) B1468669
theorem B1958243 : Blo 1303970 1958243 := bstep (se 1 (by rfl) ⟨1468682, by rfl⟩ : syracuseStep 1958243 = 2937365) B2937365
theorem B1958273 : Blo 1303970 1958273 := bstep (se 2 (by rfl) ⟨734352, by rfl⟩ : syracuseStep 1958273 = 1468705) B1468705
theorem B5570957 : Blo 1303970 5570957 := bstep (se 3 (by rfl) ⟨1044554, by rfl⟩ : syracuseStep 5570957 = 2089109) B2089109
theorem B1958291 : Blo 1303970 1958291 := bstep (se 1 (by rfl) ⟨1468718, by rfl⟩ : syracuseStep 1958291 = 2937437) B2937437
theorem B6029731 : Blo 1303970 6029731 := bstep (se 1 (by rfl) ⟨4522298, by rfl⟩ : syracuseStep 6029731 = 9044597) B9044597
theorem B1958321 : Blo 1303970 1958321 := bstep (se 2 (by rfl) ⟨734370, by rfl⟩ : syracuseStep 1958321 = 1468741) B1468741
theorem B14107061 : Blo 1303970 14107061 := bstep (se 5 (by rfl) ⟨661268, by rfl⟩ : syracuseStep 14107061 = 1322537) B1322537
theorem B1958339 : Blo 1303970 1958339 := bstep (se 1 (by rfl) ⟨1468754, by rfl⟩ : syracuseStep 1958339 = 2937509) B2937509
theorem B1958369 : Blo 1303970 1958369 := bstep (se 2 (by rfl) ⟨734388, by rfl⟩ : syracuseStep 1958369 = 1468777) B1468777
theorem B1958387 : Blo 1303970 1958387 := bstep (se 1 (by rfl) ⟨1468790, by rfl⟩ : syracuseStep 1958387 = 2937581) B2937581
theorem B1958417 : Blo 1303970 1958417 := bstep (se 2 (by rfl) ⟨734406, by rfl⟩ : syracuseStep 1958417 = 1468813) B1468813
theorem B1958435 : Blo 1303970 1958435 := bstep (se 1 (by rfl) ⟨1468826, by rfl⟩ : syracuseStep 1958435 = 2937653) B2937653
theorem B1958465 : Blo 1303970 1958465 := bstep (se 2 (by rfl) ⟨734424, by rfl⟩ : syracuseStep 1958465 = 1468849) B1468849
theorem B3301955 : Blo 1303970 3301955 := bstep (se 1 (by rfl) ⟨2476466, by rfl⟩ : syracuseStep 3301955 = 4952933) B4952933
theorem B1958483 : Blo 1303970 1958483 := bstep (se 1 (by rfl) ⟨1468862, by rfl⟩ : syracuseStep 1958483 = 2937725) B2937725
theorem B1958513 : Blo 1303970 1958513 := bstep (se 2 (by rfl) ⟨734442, by rfl⟩ : syracuseStep 1958513 = 1468885) B1468885
theorem B1466995 : Blo 1303970 1466995 := bstep (se 1 (by rfl) ⟨1100246, by rfl⟩ : syracuseStep 1466995 = 2200493) B2200493
theorem B1958531 : Blo 1303970 1958531 := bstep (se 1 (by rfl) ⟨1468898, by rfl⟩ : syracuseStep 1958531 = 2937797) B2937797
theorem B1958561 : Blo 1303970 1958561 := bstep (se 2 (by rfl) ⟨734460, by rfl⟩ : syracuseStep 1958561 = 1468921) B1468921
theorem B4956835 : Blo 1303970 4956835 := bstep (se 1 (by rfl) ⟨3717626, by rfl⟩ : syracuseStep 4956835 = 7435253) B7435253
theorem B1958579 : Blo 1303970 1958579 := bstep (se 1 (by rfl) ⟨1468934, by rfl⟩ : syracuseStep 1958579 = 2937869) B2937869
theorem B1958609 : Blo 1303970 1958609 := bstep (se 2 (by rfl) ⟨734478, by rfl⟩ : syracuseStep 1958609 = 1468957) B1468957
theorem B1958627 : Blo 1303970 1958627 := bstep (se 1 (by rfl) ⟨1468970, by rfl⟩ : syracuseStep 1958627 = 2937941) B2937941
theorem B2786033 : Blo 1303970 2786033 := bstep (se 2 (by rfl) ⟨1044762, by rfl⟩ : syracuseStep 2786033 = 2089525) B2089525
theorem B4702961 : Blo 1303970 4702961 := bstep (se 2 (by rfl) ⟨1763610, by rfl⟩ : syracuseStep 4702961 = 3527221) B3527221
theorem B1958657 : Blo 1303970 1958657 := bstep (se 2 (by rfl) ⟨734496, by rfl⟩ : syracuseStep 1958657 = 1468993) B1468993
theorem B1467139 : Blo 1303970 1467139 := bstep (se 1 (by rfl) ⟨1100354, by rfl⟩ : syracuseStep 1467139 = 2200709) B2200709
theorem B2786051 : Blo 1303970 2786051 := bstep (se 1 (by rfl) ⟨2089538, by rfl⟩ : syracuseStep 2786051 = 4179077) B4179077
theorem B3302147 : Blo 1303970 3302147 := bstep (se 1 (by rfl) ⟨2476610, by rfl⟩ : syracuseStep 3302147 = 4953221) B4953221
theorem B1958675 : Blo 1303970 1958675 := bstep (se 1 (by rfl) ⟨1469006, by rfl⟩ : syracuseStep 1958675 = 2938013) B2938013
theorem B1958705 : Blo 1303970 1958705 := bstep (se 2 (by rfl) ⟨734514, by rfl⟩ : syracuseStep 1958705 = 1469029) B1469029
theorem B2089795 : Blo 1303970 2089795 := bstep (se 1 (by rfl) ⟨1567346, by rfl⟩ : syracuseStep 2089795 = 3134693) B3134693
theorem B1958723 : Blo 1303970 1958723 := bstep (se 1 (by rfl) ⟨1469042, by rfl⟩ : syracuseStep 1958723 = 2938085) B2938085
theorem B1958753 : Blo 1303970 1958753 := bstep (se 2 (by rfl) ⟨734532, by rfl⟩ : syracuseStep 1958753 = 1469065) B1469065
theorem B1958771 : Blo 1303970 1958771 := bstep (se 1 (by rfl) ⟨1469078, by rfl⟩ : syracuseStep 1958771 = 2938157) B2938157
theorem B1958801 : Blo 1303970 1958801 := bstep (se 2 (by rfl) ⟨734550, by rfl⟩ : syracuseStep 1958801 = 1469101) B1469101
theorem B1467283 : Blo 1303970 1467283 := bstep (se 1 (by rfl) ⟨1100462, by rfl⟩ : syracuseStep 1467283 = 2200925) B2200925
theorem B1958819 : Blo 1303970 1958819 := bstep (se 1 (by rfl) ⟨1469114, by rfl⟩ : syracuseStep 1958819 = 2938229) B2938229
theorem B15057845 : Blo 1303970 15057845 := bstep (se 5 (by rfl) ⟨705836, by rfl⟩ : syracuseStep 15057845 = 1411673) B1411673
theorem B2261953 : Blo 1303970 2261953 := bstep (se 2 (by rfl) ⟨848232, by rfl⟩ : syracuseStep 2261953 = 1696465) B1696465
theorem B1958849 : Blo 1303970 1958849 := bstep (se 2 (by rfl) ⟨734568, by rfl⟩ : syracuseStep 1958849 = 1469137) B1469137
theorem B1811395 : Blo 1303970 1811395 := bstep (se 1 (by rfl) ⟨1358546, by rfl⟩ : syracuseStep 1811395 = 2717093) B2717093
theorem B4178897 : Blo 1303970 4178897 := bstep (se 2 (by rfl) ⟨1567086, by rfl⟩ : syracuseStep 4178897 = 3134173) B3134173
theorem B1958867 : Blo 1303970 1958867 := bstep (se 1 (by rfl) ⟨1469150, by rfl⟩ : syracuseStep 1958867 = 2938301) B2938301
theorem B1958897 : Blo 1303970 1958897 := bstep (se 2 (by rfl) ⟨734586, by rfl⟩ : syracuseStep 1958897 = 1469173) B1469173
theorem B4178947 : Blo 1303970 4178947 := bstep (se 1 (by rfl) ⟨3134210, by rfl⟩ : syracuseStep 4178947 = 6268421) B6268421
theorem B1958915 : Blo 1303970 1958915 := bstep (se 1 (by rfl) ⟨1469186, by rfl⟩ : syracuseStep 1958915 = 2938373) B2938373
theorem B9905165 : Blo 1303970 9905165 := bstep (se 3 (by rfl) ⟨1857218, by rfl⟩ : syracuseStep 9905165 = 3714437) B3714437
theorem B1958945 : Blo 1303970 1958945 := bstep (se 2 (by rfl) ⟨734604, by rfl⟩ : syracuseStep 1958945 = 1469209) B1469209
theorem B1467427 : Blo 1303970 1467427 := bstep (se 1 (by rfl) ⟨1100570, by rfl⟩ : syracuseStep 1467427 = 2201141) B2201141
theorem B2090051 : Blo 1303970 2090051 := bstep (se 1 (by rfl) ⟨1567538, by rfl⟩ : syracuseStep 2090051 = 3135077) B3135077
theorem B10585201 : Blo 1303970 10585201 := bstep (se 2 (by rfl) ⟨3969450, by rfl⟩ : syracuseStep 10585201 = 7938901) B7938901
theorem B1467571 : Blo 1303970 1467571 := bstep (se 1 (by rfl) ⟨1100678, by rfl⟩ : syracuseStep 1467571 = 2201357) B2201357
theorem B2647345 : Blo 1303970 2647345 := bstep (se 2 (by rfl) ⟨992754, by rfl⟩ : syracuseStep 2647345 = 1985509) B1985509
theorem B1467715 : Blo 1303970 1467715 := bstep (se 1 (by rfl) ⟨1100786, by rfl⟩ : syracuseStep 1467715 = 2201573) B2201573
theorem B10585457 : Blo 1303970 10585457 := bstep (se 2 (by rfl) ⟨3969546, by rfl⟩ : syracuseStep 10585457 = 7939093) B7939093
theorem B2934161 : Blo 1303970 2934161 := bstep (se 2 (by rfl) ⟨1100310, by rfl⟩ : syracuseStep 2934161 = 2200621) B2200621
theorem B1303971 : Blo 1303970 1303971 := bstep (se 1 (by rfl) ⟨977978, by rfl⟩ : syracuseStep 1303971 = 1955957) B1955957
theorem B2934179 : Blo 1303970 2934179 := bstep (se 1 (by rfl) ⟨2200634, by rfl⟩ : syracuseStep 2934179 = 4401269) B4401269
theorem B7431587 : Blo 1303970 7431587 := bstep (se 1 (by rfl) ⟨5573690, by rfl⟩ : syracuseStep 7431587 = 11147381) B11147381
theorem B1303987 : Blo 1303970 1303987 := bstep (se 1 (by rfl) ⟨977990, by rfl⟩ : syracuseStep 1303987 = 1955981) B1955981
theorem B1304003 : Blo 1303970 1304003 := bstep (se 1 (by rfl) ⟨978002, by rfl⟩ : syracuseStep 1304003 = 1956005) B1956005
theorem B1304019 : Blo 1303970 1304019 := bstep (se 1 (by rfl) ⟨978014, by rfl⟩ : syracuseStep 1304019 = 1956029) B1956029
theorem B1467859 : Blo 1303970 1467859 := bstep (se 1 (by rfl) ⟨1100894, by rfl⟩ : syracuseStep 1467859 = 2201789) B2201789
theorem B1304035 : Blo 1303970 1304035 := bstep (se 1 (by rfl) ⟨978026, by rfl⟩ : syracuseStep 1304035 = 1956053) B1956053
theorem B1304051 : Blo 1303970 1304051 := bstep (se 1 (by rfl) ⟨978038, by rfl⟩ : syracuseStep 1304051 = 1956077) B1956077
theorem B1304067 : Blo 1303970 1304067 := bstep (se 1 (by rfl) ⟨978050, by rfl⟩ : syracuseStep 1304067 = 1956101) B1956101
theorem B1304083 : Blo 1303970 1304083 := bstep (se 1 (by rfl) ⟨978062, by rfl⟩ : syracuseStep 1304083 = 1956125) B1956125
theorem B1304099 : Blo 1303970 1304099 := bstep (se 1 (by rfl) ⟨978074, by rfl⟩ : syracuseStep 1304099 = 1956149) B1956149
theorem B7054897 : Blo 1303970 7054897 := bstep (se 2 (by rfl) ⟨2645586, by rfl⟩ : syracuseStep 7054897 = 5291173) B5291173
theorem B1304115 : Blo 1303970 1304115 := bstep (se 1 (by rfl) ⟨978086, by rfl⟩ : syracuseStep 1304115 = 1956173) B1956173
theorem B1304131 : Blo 1303970 1304131 := bstep (se 1 (by rfl) ⟨978098, by rfl⟩ : syracuseStep 1304131 = 1956197) B1956197
theorem B1304147 : Blo 1303970 1304147 := bstep (se 1 (by rfl) ⟨978110, by rfl⟩ : syracuseStep 1304147 = 1956221) B1956221
theorem B1304163 : Blo 1303970 1304163 := bstep (se 1 (by rfl) ⟨978122, by rfl⟩ : syracuseStep 1304163 = 1956245) B1956245
theorem B1468003 : Blo 1303970 1468003 := bstep (se 1 (by rfl) ⟨1101002, by rfl⟩ : syracuseStep 1468003 = 2202005) B2202005
theorem B1304179 : Blo 1303970 1304179 := bstep (se 1 (by rfl) ⟨978134, by rfl⟩ : syracuseStep 1304179 = 1956269) B1956269
theorem B1304195 : Blo 1303970 1304195 := bstep (se 1 (by rfl) ⟨978146, by rfl⟩ : syracuseStep 1304195 = 1956293) B1956293
theorem B2352785 : Blo 1303970 2352785 := bstep (se 2 (by rfl) ⟨882294, by rfl⟩ : syracuseStep 2352785 = 1764589) B1764589
theorem B1304211 : Blo 1303970 1304211 := bstep (se 1 (by rfl) ⟨978158, by rfl⟩ : syracuseStep 1304211 = 1956317) B1956317
theorem B1304227 : Blo 1303970 1304227 := bstep (se 1 (by rfl) ⟨978170, by rfl⟩ : syracuseStep 1304227 = 1956341) B1956341
theorem B2934449 : Blo 1303970 2934449 := bstep (se 2 (by rfl) ⟨1100418, by rfl⟩ : syracuseStep 2934449 = 2200837) B2200837
theorem B3303089 : Blo 1303970 3303089 := bstep (se 2 (by rfl) ⟨1238658, by rfl⟩ : syracuseStep 3303089 = 2477317) B2477317
theorem B1304243 : Blo 1303970 1304243 := bstep (se 1 (by rfl) ⟨978182, by rfl⟩ : syracuseStep 1304243 = 1956365) B1956365
theorem B9053873 : Blo 1303970 9053873 := bstep (se 2 (by rfl) ⟨3395202, by rfl⟩ : syracuseStep 9053873 = 6790405) B6790405
theorem B2934467 : Blo 1303970 2934467 := bstep (se 1 (by rfl) ⟨2200850, by rfl⟩ : syracuseStep 2934467 = 4401701) B4401701
theorem B1304259 : Blo 1303970 1304259 := bstep (se 1 (by rfl) ⟨978194, by rfl⟩ : syracuseStep 1304259 = 1956389) B1956389
theorem B1672915 : Blo 1303970 1672915 := bstep (se 1 (by rfl) ⟨1254686, by rfl⟩ : syracuseStep 1672915 = 2509373) B2509373
theorem B1304275 : Blo 1303970 1304275 := bstep (se 1 (by rfl) ⟨978206, by rfl⟩ : syracuseStep 1304275 = 1956413) B1956413
theorem B1304291 : Blo 1303970 1304291 := bstep (se 1 (by rfl) ⟨978218, by rfl⟩ : syracuseStep 1304291 = 1956437) B1956437
theorem B3303139 : Blo 1303970 3303139 := bstep (se 1 (by rfl) ⟨2477354, by rfl⟩ : syracuseStep 3303139 = 4954709) B4954709
theorem B1304307 : Blo 1303970 1304307 := bstep (se 1 (by rfl) ⟨978230, by rfl⟩ : syracuseStep 1304307 = 1956461) B1956461
theorem B1468147 : Blo 1303970 1468147 := bstep (se 1 (by rfl) ⟨1101110, by rfl⟩ : syracuseStep 1468147 = 2202221) B2202221
theorem B1304323 : Blo 1303970 1304323 := bstep (se 1 (by rfl) ⟨978242, by rfl⟩ : syracuseStep 1304323 = 1956485) B1956485
theorem B2975491 : Blo 1303970 2975491 := bstep (se 1 (by rfl) ⟨2231618, by rfl⟩ : syracuseStep 2975491 = 4463237) B4463237
theorem B2090755 : Blo 1303970 2090755 := bstep (se 1 (by rfl) ⟨1568066, by rfl⟩ : syracuseStep 2090755 = 3136133) B3136133
theorem B1394435 : Blo 1303970 1394435 := bstep (se 1 (by rfl) ⟨1045826, by rfl⟩ : syracuseStep 1394435 = 2091653) B2091653
theorem B1304339 : Blo 1303970 1304339 := bstep (se 1 (by rfl) ⟨978254, by rfl⟩ : syracuseStep 1304339 = 1956509) B1956509
theorem B1304355 : Blo 1303970 1304355 := bstep (se 1 (by rfl) ⟨978266, by rfl⟩ : syracuseStep 1304355 = 1956533) B1956533
theorem B4400945 : Blo 1303970 4400945 := bstep (se 2 (by rfl) ⟨1650354, by rfl⟩ : syracuseStep 4400945 = 3300709) B3300709
theorem B1304371 : Blo 1303970 1304371 := bstep (se 1 (by rfl) ⟨978278, by rfl⟩ : syracuseStep 1304371 = 1956557) B1956557
theorem B1304387 : Blo 1303970 1304387 := bstep (se 1 (by rfl) ⟨978290, by rfl⟩ : syracuseStep 1304387 = 1956581) B1956581
theorem B2975555 : Blo 1303970 2975555 := bstep (se 1 (by rfl) ⟨2231666, by rfl⟩ : syracuseStep 2975555 = 4463333) B4463333
theorem B1304403 : Blo 1303970 1304403 := bstep (se 1 (by rfl) ⟨978302, by rfl⟩ : syracuseStep 1304403 = 1956605) B1956605
theorem B1304419 : Blo 1303970 1304419 := bstep (se 1 (by rfl) ⟨978314, by rfl⟩ : syracuseStep 1304419 = 1956629) B1956629
theorem B3303281 : Blo 1303970 3303281 := bstep (se 2 (by rfl) ⟨1238730, by rfl⟩ : syracuseStep 3303281 = 2477461) B2477461
theorem B1304435 : Blo 1303970 1304435 := bstep (se 1 (by rfl) ⟨978326, by rfl⟩ : syracuseStep 1304435 = 1956653) B1956653
theorem B1304451 : Blo 1303970 1304451 := bstep (se 1 (by rfl) ⟨978338, by rfl⟩ : syracuseStep 1304451 = 1956677) B1956677
theorem B1468291 : Blo 1303970 1468291 := bstep (se 1 (by rfl) ⟨1101218, by rfl⟩ : syracuseStep 1468291 = 2202437) B2202437
theorem B1304467 : Blo 1303970 1304467 := bstep (se 1 (by rfl) ⟨978350, by rfl⟩ : syracuseStep 1304467 = 1956701) B1956701
theorem B1304483 : Blo 1303970 1304483 := bstep (se 1 (by rfl) ⟨978362, by rfl⟩ : syracuseStep 1304483 = 1956725) B1956725
theorem B1304499 : Blo 1303970 1304499 := bstep (se 1 (by rfl) ⟨978374, by rfl⟩ : syracuseStep 1304499 = 1956749) B1956749
theorem B1304515 : Blo 1303970 1304515 := bstep (se 1 (by rfl) ⟨978386, by rfl⟩ : syracuseStep 1304515 = 1956773) B1956773
theorem B2934737 : Blo 1303970 2934737 := bstep (se 2 (by rfl) ⟨1100526, by rfl⟩ : syracuseStep 2934737 = 2201053) B2201053
theorem B2787281 : Blo 1303970 2787281 := bstep (se 2 (by rfl) ⟨1045230, by rfl⟩ : syracuseStep 2787281 = 2090461) B2090461
theorem B1304531 : Blo 1303970 1304531 := bstep (se 1 (by rfl) ⟨978398, by rfl⟩ : syracuseStep 1304531 = 1956797) B1956797
theorem B2476003 : Blo 1303970 2476003 := bstep (se 1 (by rfl) ⟨1857002, by rfl⟩ : syracuseStep 2476003 = 3714005) B3714005
theorem B2934755 : Blo 1303970 2934755 := bstep (se 1 (by rfl) ⟨2201066, by rfl⟩ : syracuseStep 2934755 = 4402133) B4402133
theorem B1304547 : Blo 1303970 1304547 := bstep (se 1 (by rfl) ⟨978410, by rfl⟩ : syracuseStep 1304547 = 1956821) B1956821
theorem B1304563 : Blo 1303970 1304563 := bstep (se 1 (by rfl) ⟨978422, by rfl⟩ : syracuseStep 1304563 = 1956845) B1956845
theorem B1304579 : Blo 1303970 1304579 := bstep (se 1 (by rfl) ⟨978434, by rfl⟩ : syracuseStep 1304579 = 1956869) B1956869
theorem B2091025 : Blo 1303970 2091025 := bstep (se 2 (by rfl) ⟨784134, by rfl⟩ : syracuseStep 2091025 = 1568269) B1568269
theorem B1304595 : Blo 1303970 1304595 := bstep (se 1 (by rfl) ⟨978446, by rfl⟩ : syracuseStep 1304595 = 1956893) B1956893
theorem B1468435 : Blo 1303970 1468435 := bstep (se 1 (by rfl) ⟨1101326, by rfl⟩ : syracuseStep 1468435 = 2202653) B2202653
theorem B1304611 : Blo 1303970 1304611 := bstep (se 1 (by rfl) ⟨978458, by rfl⟩ : syracuseStep 1304611 = 1956917) B1956917
theorem B1304627 : Blo 1303970 1304627 := bstep (se 1 (by rfl) ⟨978470, by rfl⟩ : syracuseStep 1304627 = 1956941) B1956941
theorem B1304643 : Blo 1303970 1304643 := bstep (se 1 (by rfl) ⟨978482, by rfl⟩ : syracuseStep 1304643 = 1956965) B1956965
theorem B2091089 : Blo 1303970 2091089 := bstep (se 2 (by rfl) ⟨784158, by rfl⟩ : syracuseStep 2091089 = 1568317) B1568317
theorem B1304659 : Blo 1303970 1304659 := bstep (se 1 (by rfl) ⟨978494, by rfl⟩ : syracuseStep 1304659 = 1956989) B1956989
theorem B1304675 : Blo 1303970 1304675 := bstep (se 1 (by rfl) ⟨978506, by rfl⟩ : syracuseStep 1304675 = 1957013) B1957013
theorem B1304691 : Blo 1303970 1304691 := bstep (se 1 (by rfl) ⟨978518, by rfl⟩ : syracuseStep 1304691 = 1957037) B1957037
theorem B2476163 : Blo 1303970 2476163 := bstep (se 1 (by rfl) ⟨1857122, by rfl⟩ : syracuseStep 2476163 = 3714245) B3714245
theorem B1304707 : Blo 1303970 1304707 := bstep (se 1 (by rfl) ⟨978530, by rfl⟩ : syracuseStep 1304707 = 1957061) B1957061
theorem B2353283 : Blo 1303970 2353283 := bstep (se 1 (by rfl) ⟨1764962, by rfl⟩ : syracuseStep 2353283 = 3529925) B3529925
theorem B1304723 : Blo 1303970 1304723 := bstep (se 1 (by rfl) ⟨978542, by rfl⟩ : syracuseStep 1304723 = 1957085) B1957085
theorem B1304739 : Blo 1303970 1304739 := bstep (se 1 (by rfl) ⟨978554, by rfl⟩ : syracuseStep 1304739 = 1957109) B1957109
theorem B1468579 : Blo 1303970 1468579 := bstep (se 1 (by rfl) ⟨1101434, by rfl⟩ : syracuseStep 1468579 = 2202869) B2202869
theorem B1304755 : Blo 1303970 1304755 := bstep (se 1 (by rfl) ⟨978566, by rfl⟩ : syracuseStep 1304755 = 1957133) B1957133
theorem B1304771 : Blo 1303970 1304771 := bstep (se 1 (by rfl) ⟨978578, by rfl⟩ : syracuseStep 1304771 = 1957157) B1957157
theorem B7932109 : Blo 1303970 7932109 := bstep (se 3 (by rfl) ⟨1487270, by rfl⟩ : syracuseStep 7932109 = 2974541) B2974541
theorem B4180177 : Blo 1303970 4180177 := bstep (se 2 (by rfl) ⟨1567566, by rfl⟩ : syracuseStep 4180177 = 3135133) B3135133
theorem B1304787 : Blo 1303970 1304787 := bstep (se 1 (by rfl) ⟨978590, by rfl⟩ : syracuseStep 1304787 = 1957181) B1957181
theorem B1304803 : Blo 1303970 1304803 := bstep (se 1 (by rfl) ⟨978602, by rfl⟩ : syracuseStep 1304803 = 1957205) B1957205
theorem B2935025 : Blo 1303970 2935025 := bstep (se 2 (by rfl) ⟨1100634, by rfl⟩ : syracuseStep 2935025 = 2201269) B2201269
theorem B1304819 : Blo 1303970 1304819 := bstep (se 1 (by rfl) ⟨978614, by rfl⟩ : syracuseStep 1304819 = 1957229) B1957229
theorem B2935043 : Blo 1303970 2935043 := bstep (se 1 (by rfl) ⟨2201282, by rfl⟩ : syracuseStep 2935043 = 4402565) B4402565
theorem B1304835 : Blo 1303970 1304835 := bstep (se 1 (by rfl) ⟨978626, by rfl⟩ : syracuseStep 1304835 = 1957253) B1957253
theorem B1304851 : Blo 1303970 1304851 := bstep (se 1 (by rfl) ⟨978638, by rfl⟩ : syracuseStep 1304851 = 1957277) B1957277
theorem B1304867 : Blo 1303970 1304867 := bstep (se 1 (by rfl) ⟨978650, by rfl⟩ : syracuseStep 1304867 = 1957301) B1957301
theorem B1304883 : Blo 1303970 1304883 := bstep (se 1 (by rfl) ⟨978662, by rfl⟩ : syracuseStep 1304883 = 1957325) B1957325
theorem B1468723 : Blo 1303970 1468723 := bstep (se 1 (by rfl) ⟨1101542, by rfl⟩ : syracuseStep 1468723 = 2203085) B2203085
theorem B1304899 : Blo 1303970 1304899 := bstep (se 1 (by rfl) ⟨978674, by rfl⟩ : syracuseStep 1304899 = 1957349) B1957349
theorem B4401485 : Blo 1303970 4401485 := bstep (se 3 (by rfl) ⟨825278, by rfl⟩ : syracuseStep 4401485 = 1650557) B1650557
theorem B1304915 : Blo 1303970 1304915 := bstep (se 1 (by rfl) ⟨978686, by rfl⟩ : syracuseStep 1304915 = 1957373) B1957373
theorem B1304931 : Blo 1303970 1304931 := bstep (se 1 (by rfl) ⟨978698, by rfl⟩ : syracuseStep 1304931 = 1957397) B1957397
theorem B1304947 : Blo 1303970 1304947 := bstep (se 1 (by rfl) ⟨978710, by rfl⟩ : syracuseStep 1304947 = 1957421) B1957421
theorem B4401539 : Blo 1303970 4401539 := bstep (se 1 (by rfl) ⟨3301154, by rfl⟩ : syracuseStep 4401539 = 6602309) B6602309
theorem B1304963 : Blo 1303970 1304963 := bstep (se 1 (by rfl) ⟨978722, by rfl⟩ : syracuseStep 1304963 = 1957445) B1957445
theorem B1304979 : Blo 1303970 1304979 := bstep (se 1 (by rfl) ⟨978734, by rfl⟩ : syracuseStep 1304979 = 1957469) B1957469
theorem B1304995 : Blo 1303970 1304995 := bstep (se 1 (by rfl) ⟨978746, by rfl⟩ : syracuseStep 1304995 = 1957493) B1957493
theorem B1305011 : Blo 1303970 1305011 := bstep (se 1 (by rfl) ⟨978758, by rfl⟩ : syracuseStep 1305011 = 1957517) B1957517
theorem B1305027 : Blo 1303970 1305027 := bstep (se 1 (by rfl) ⟨978770, by rfl⟩ : syracuseStep 1305027 = 1957541) B1957541
theorem B1468867 : Blo 1303970 1468867 := bstep (se 1 (by rfl) ⟨1101650, by rfl⟩ : syracuseStep 1468867 = 2203301) B2203301
theorem B1763795 : Blo 1303970 1763795 := bstep (se 1 (by rfl) ⟨1322846, by rfl⟩ : syracuseStep 1763795 = 2645693) B2645693
theorem B1305043 : Blo 1303970 1305043 := bstep (se 1 (by rfl) ⟨978782, by rfl⟩ : syracuseStep 1305043 = 1957565) B1957565
theorem B1305059 : Blo 1303970 1305059 := bstep (se 1 (by rfl) ⟨978794, by rfl⟩ : syracuseStep 1305059 = 1957589) B1957589
theorem B1305075 : Blo 1303970 1305075 := bstep (se 1 (by rfl) ⟨978806, by rfl⟩ : syracuseStep 1305075 = 1957613) B1957613
theorem B1305091 : Blo 1303970 1305091 := bstep (se 1 (by rfl) ⟨978818, by rfl⟩ : syracuseStep 1305091 = 1957637) B1957637
theorem B2935313 : Blo 1303970 2935313 := bstep (se 2 (by rfl) ⟨1100742, by rfl⟩ : syracuseStep 2935313 = 2201485) B2201485
theorem B1305107 : Blo 1303970 1305107 := bstep (se 1 (by rfl) ⟨978830, by rfl⟩ : syracuseStep 1305107 = 1957661) B1957661
theorem B2935331 : Blo 1303970 2935331 := bstep (se 1 (by rfl) ⟨2201498, by rfl⟩ : syracuseStep 2935331 = 4402997) B4402997
theorem B1305123 : Blo 1303970 1305123 := bstep (se 1 (by rfl) ⟨978842, by rfl⟩ : syracuseStep 1305123 = 1957685) B1957685
theorem B1305139 : Blo 1303970 1305139 := bstep (se 1 (by rfl) ⟨978854, by rfl⟩ : syracuseStep 1305139 = 1957709) B1957709
theorem B1305155 : Blo 1303970 1305155 := bstep (se 1 (by rfl) ⟨978866, by rfl⟩ : syracuseStep 1305155 = 1957733) B1957733
theorem B3713617 : Blo 1303970 3713617 := bstep (se 2 (by rfl) ⟨1392606, by rfl⟩ : syracuseStep 3713617 = 2785213) B2785213
theorem B1305171 : Blo 1303970 1305171 := bstep (se 1 (by rfl) ⟨978878, by rfl⟩ : syracuseStep 1305171 = 1957757) B1957757
theorem B1469011 : Blo 1303970 1469011 := bstep (se 1 (by rfl) ⟨1101758, by rfl⟩ : syracuseStep 1469011 = 2203517) B2203517
theorem B1305187 : Blo 1303970 1305187 := bstep (se 1 (by rfl) ⟨978890, by rfl⟩ : syracuseStep 1305187 = 1957781) B1957781
theorem B1305203 : Blo 1303970 1305203 := bstep (se 1 (by rfl) ⟨978902, by rfl⟩ : syracuseStep 1305203 = 1957805) B1957805
theorem B1305219 : Blo 1303970 1305219 := bstep (se 1 (by rfl) ⟨978914, by rfl⟩ : syracuseStep 1305219 = 1957829) B1957829
theorem B4401809 : Blo 1303970 4401809 := bstep (se 2 (by rfl) ⟨1650678, by rfl⟩ : syracuseStep 4401809 = 3301357) B3301357
theorem B1305235 : Blo 1303970 1305235 := bstep (se 1 (by rfl) ⟨978926, by rfl⟩ : syracuseStep 1305235 = 1957853) B1957853
theorem B1305251 : Blo 1303970 1305251 := bstep (se 1 (by rfl) ⟨978938, by rfl⟩ : syracuseStep 1305251 = 1957877) B1957877
theorem B1305267 : Blo 1303970 1305267 := bstep (se 1 (by rfl) ⟨978950, by rfl⟩ : syracuseStep 1305267 = 1957901) B1957901
theorem B1305283 : Blo 1303970 1305283 := bstep (se 1 (by rfl) ⟨978962, by rfl⟩ : syracuseStep 1305283 = 1957925) B1957925
theorem B1673939 : Blo 1303970 1673939 := bstep (se 1 (by rfl) ⟨1255454, by rfl⟩ : syracuseStep 1673939 = 2510909) B2510909
theorem B1305299 : Blo 1303970 1305299 := bstep (se 1 (by rfl) ⟨978974, by rfl⟩ : syracuseStep 1305299 = 1957949) B1957949
theorem B1305315 : Blo 1303970 1305315 := bstep (se 1 (by rfl) ⟨978986, by rfl⟩ : syracuseStep 1305315 = 1957973) B1957973
theorem B1469155 : Blo 1303970 1469155 := bstep (se 1 (by rfl) ⟨1101866, by rfl⟩ : syracuseStep 1469155 = 2203733) B2203733
theorem B1305331 : Blo 1303970 1305331 := bstep (se 1 (by rfl) ⟨978998, by rfl⟩ : syracuseStep 1305331 = 1957997) B1957997
theorem B1305347 : Blo 1303970 1305347 := bstep (se 1 (by rfl) ⟨979010, by rfl⟩ : syracuseStep 1305347 = 1958021) B1958021
theorem B1305363 : Blo 1303970 1305363 := bstep (se 1 (by rfl) ⟨979022, by rfl⟩ : syracuseStep 1305363 = 1958045) B1958045
theorem B1305379 : Blo 1303970 1305379 := bstep (se 1 (by rfl) ⟨979034, by rfl⟩ : syracuseStep 1305379 = 1958069) B1958069
theorem B2935601 : Blo 1303970 2935601 := bstep (se 2 (by rfl) ⟨1100850, by rfl⟩ : syracuseStep 2935601 = 2201701) B2201701
theorem B1305395 : Blo 1303970 1305395 := bstep (se 1 (by rfl) ⟨979046, by rfl⟩ : syracuseStep 1305395 = 1958093) B1958093
theorem B2935619 : Blo 1303970 2935619 := bstep (se 1 (by rfl) ⟨2201714, by rfl⟩ : syracuseStep 2935619 = 4403429) B4403429
theorem B1305411 : Blo 1303970 1305411 := bstep (se 1 (by rfl) ⟨979058, by rfl⟩ : syracuseStep 1305411 = 1958117) B1958117
theorem B3304273 : Blo 1303970 3304273 := bstep (se 2 (by rfl) ⟨1239102, by rfl⟩ : syracuseStep 3304273 = 2478205) B2478205
theorem B1305427 : Blo 1303970 1305427 := bstep (se 1 (by rfl) ⟨979070, by rfl⟩ : syracuseStep 1305427 = 1958141) B1958141
theorem B1985363 : Blo 1303970 1985363 := bstep (se 1 (by rfl) ⟨1489022, by rfl⟩ : syracuseStep 1985363 = 2978045) B2978045
theorem B1305443 : Blo 1303970 1305443 := bstep (se 1 (by rfl) ⟨979082, by rfl⟩ : syracuseStep 1305443 = 1958165) B1958165
theorem B1305459 : Blo 1303970 1305459 := bstep (se 1 (by rfl) ⟨979094, by rfl⟩ : syracuseStep 1305459 = 1958189) B1958189
theorem B1305475 : Blo 1303970 1305475 := bstep (se 1 (by rfl) ⟨979106, by rfl⟩ : syracuseStep 1305475 = 1958213) B1958213
theorem B1305491 : Blo 1303970 1305491 := bstep (se 1 (by rfl) ⟨979118, by rfl⟩ : syracuseStep 1305491 = 1958237) B1958237
theorem B1305507 : Blo 1303970 1305507 := bstep (se 1 (by rfl) ⟨979130, by rfl⟩ : syracuseStep 1305507 = 1958261) B1958261
theorem B1305523 : Blo 1303970 1305523 := bstep (se 1 (by rfl) ⟨979142, by rfl⟩ : syracuseStep 1305523 = 1958285) B1958285
theorem B1305539 : Blo 1303970 1305539 := bstep (se 1 (by rfl) ⟨979154, by rfl⟩ : syracuseStep 1305539 = 1958309) B1958309
theorem B1305555 : Blo 1303970 1305555 := bstep (se 1 (by rfl) ⟨979166, by rfl⟩ : syracuseStep 1305555 = 1958333) B1958333
theorem B1305571 : Blo 1303970 1305571 := bstep (se 1 (by rfl) ⟨979178, by rfl⟩ : syracuseStep 1305571 = 1958357) B1958357
theorem B1305587 : Blo 1303970 1305587 := bstep (se 1 (by rfl) ⟨979190, by rfl⟩ : syracuseStep 1305587 = 1958381) B1958381
theorem B1305603 : Blo 1303970 1305603 := bstep (se 1 (by rfl) ⟨979202, by rfl⟩ : syracuseStep 1305603 = 1958405) B1958405
theorem B1305619 : Blo 1303970 1305619 := bstep (se 1 (by rfl) ⟨979214, by rfl⟩ : syracuseStep 1305619 = 1958429) B1958429
theorem B1305635 : Blo 1303970 1305635 := bstep (se 1 (by rfl) ⟨979226, by rfl⟩ : syracuseStep 1305635 = 1958453) B1958453
theorem B6605873 : Blo 1303970 6605873 := bstep (se 2 (by rfl) ⟨2477202, by rfl⟩ : syracuseStep 6605873 = 4954405) B4954405
theorem B1305651 : Blo 1303970 1305651 := bstep (se 1 (by rfl) ⟨979238, by rfl⟩ : syracuseStep 1305651 = 1958477) B1958477
theorem B1305667 : Blo 1303970 1305667 := bstep (se 1 (by rfl) ⟨979250, by rfl⟩ : syracuseStep 1305667 = 1958501) B1958501
theorem B2935889 : Blo 1303970 2935889 := bstep (se 2 (by rfl) ⟨1100958, by rfl⟩ : syracuseStep 2935889 = 2201917) B2201917
theorem B1764433 : Blo 1303970 1764433 := bstep (se 2 (by rfl) ⟨661662, by rfl⟩ : syracuseStep 1764433 = 1323325) B1323325
theorem B1305683 : Blo 1303970 1305683 := bstep (se 1 (by rfl) ⟨979262, by rfl⟩ : syracuseStep 1305683 = 1958525) B1958525
theorem B2935907 : Blo 1303970 2935907 := bstep (se 1 (by rfl) ⟨2201930, by rfl⟩ : syracuseStep 2935907 = 4403861) B4403861
theorem B3968099 : Blo 1303970 3968099 := bstep (se 1 (by rfl) ⟨2976074, by rfl⟩ : syracuseStep 3968099 = 5952149) B5952149
theorem B3304547 : Blo 1303970 3304547 := bstep (se 1 (by rfl) ⟨2478410, by rfl⟩ : syracuseStep 3304547 = 4956821) B4956821
theorem B1305699 : Blo 1303970 1305699 := bstep (se 1 (by rfl) ⟨979274, by rfl⟩ : syracuseStep 1305699 = 1958549) B1958549
theorem B1305715 : Blo 1303970 1305715 := bstep (se 1 (by rfl) ⟨979286, by rfl⟩ : syracuseStep 1305715 = 1958573) B1958573
theorem B2509955 : Blo 1303970 2509955 := bstep (se 1 (by rfl) ⟨1882466, by rfl⟩ : syracuseStep 2509955 = 3764933) B3764933
theorem B1305731 : Blo 1303970 1305731 := bstep (se 1 (by rfl) ⟨979298, by rfl⟩ : syracuseStep 1305731 = 1958597) B1958597
theorem B1305747 : Blo 1303970 1305747 := bstep (se 1 (by rfl) ⟨979310, by rfl⟩ : syracuseStep 1305747 = 1958621) B1958621
theorem B1305763 : Blo 1303970 1305763 := bstep (se 1 (by rfl) ⟨979322, by rfl⟩ : syracuseStep 1305763 = 1958645) B1958645
theorem B4402349 : Blo 1303970 4402349 := bstep (se 3 (by rfl) ⟨825440, by rfl⟩ : syracuseStep 4402349 = 1650881) B1650881
theorem B2477233 : Blo 1303970 2477233 := bstep (se 2 (by rfl) ⟨928962, by rfl⟩ : syracuseStep 2477233 = 1857925) B1857925
theorem B1305779 : Blo 1303970 1305779 := bstep (se 1 (by rfl) ⟨979334, by rfl⟩ : syracuseStep 1305779 = 1958669) B1958669
theorem B1305795 : Blo 1303970 1305795 := bstep (se 1 (by rfl) ⟨979346, by rfl⟩ : syracuseStep 1305795 = 1958693) B1958693
theorem B1305811 : Blo 1303970 1305811 := bstep (se 1 (by rfl) ⟨979358, by rfl⟩ : syracuseStep 1305811 = 1958717) B1958717
theorem B4402403 : Blo 1303970 4402403 := bstep (se 1 (by rfl) ⟨3301802, by rfl⟩ : syracuseStep 4402403 = 6603605) B6603605
theorem B1305827 : Blo 1303970 1305827 := bstep (se 1 (by rfl) ⟨979370, by rfl⟩ : syracuseStep 1305827 = 1958741) B1958741
theorem B1305843 : Blo 1303970 1305843 := bstep (se 1 (by rfl) ⟨979382, by rfl⟩ : syracuseStep 1305843 = 1958765) B1958765
theorem B1305859 : Blo 1303970 1305859 := bstep (se 1 (by rfl) ⟨979394, by rfl⟩ : syracuseStep 1305859 = 1958789) B1958789
theorem B7433477 : Blo 1303970 7433477 := bstep (se 4 (by rfl) ⟨696888, by rfl⟩ : syracuseStep 7433477 = 1393777) B1393777
theorem B1305875 : Blo 1303970 1305875 := bstep (se 1 (by rfl) ⟨979406, by rfl⟩ : syracuseStep 1305875 = 1958813) B1958813
theorem B3304739 : Blo 1303970 3304739 := bstep (se 1 (by rfl) ⟨2478554, by rfl⟩ : syracuseStep 3304739 = 4957109) B4957109
theorem B1305891 : Blo 1303970 1305891 := bstep (se 1 (by rfl) ⟨979418, by rfl⟩ : syracuseStep 1305891 = 1958837) B1958837
theorem B1305907 : Blo 1303970 1305907 := bstep (se 1 (by rfl) ⟨979430, by rfl⟩ : syracuseStep 1305907 = 1958861) B1958861
theorem B1305923 : Blo 1303970 1305923 := bstep (se 1 (by rfl) ⟨979442, by rfl⟩ : syracuseStep 1305923 = 1958885) B1958885
theorem B1305939 : Blo 1303970 1305939 := bstep (se 1 (by rfl) ⟨979454, by rfl⟩ : syracuseStep 1305939 = 1958909) B1958909
theorem B5647715 : Blo 1303970 5647715 := bstep (se 1 (by rfl) ⟨4235786, by rfl⟩ : syracuseStep 5647715 = 8471573) B8471573
theorem B1305955 : Blo 1303970 1305955 := bstep (se 1 (by rfl) ⟨979466, by rfl⟩ : syracuseStep 1305955 = 1958933) B1958933
theorem B4181357 : Blo 1303970 4181357 := bstep (se 3 (by rfl) ⟨784004, by rfl⟩ : syracuseStep 4181357 = 1568009) B1568009
theorem B2936177 : Blo 1303970 2936177 := bstep (se 2 (by rfl) ⟨1101066, by rfl⟩ : syracuseStep 2936177 = 2202133) B2202133
theorem B2936195 : Blo 1303970 2936195 := bstep (se 1 (by rfl) ⟨2202146, by rfl⟩ : syracuseStep 2936195 = 4404293) B4404293
theorem B2788835 : Blo 1303970 2788835 := bstep (se 1 (by rfl) ⟨2091626, by rfl⟩ : syracuseStep 2788835 = 4183253) B4183253
theorem B4402673 : Blo 1303970 4402673 := bstep (se 2 (by rfl) ⟨1651002, by rfl⟩ : syracuseStep 4402673 = 3302005) B3302005
theorem B1764865 : Blo 1303970 1764865 := bstep (se 2 (by rfl) ⟨661824, by rfl⟩ : syracuseStep 1764865 = 1323649) B1323649
theorem B11292301 : Blo 1303970 11292301 := bstep (se 3 (by rfl) ⟨2117306, by rfl⟩ : syracuseStep 11292301 = 4234613) B4234613
theorem B2936465 : Blo 1303970 2936465 := bstep (se 2 (by rfl) ⟨1101174, by rfl⟩ : syracuseStep 2936465 = 2202349) B2202349
theorem B2936483 : Blo 1303970 2936483 := bstep (se 1 (by rfl) ⟨2202362, by rfl⟩ : syracuseStep 2936483 = 4404725) B4404725
theorem B4951793 : Blo 1303970 4951793 := bstep (se 2 (by rfl) ⟨1856922, by rfl⟩ : syracuseStep 4951793 = 3713845) B3713845
theorem B7057165 : Blo 1303970 7057165 := bstep (se 3 (by rfl) ⟨1323218, by rfl⟩ : syracuseStep 7057165 = 2646437) B2646437
theorem B1650451 : Blo 1303970 1650451 := bstep (se 1 (by rfl) ⟨1237838, by rfl⟩ : syracuseStep 1650451 = 2475677) B2475677
theorem B7745329 : Blo 1303970 7745329 := bstep (se 2 (by rfl) ⟨2904498, by rfl⟩ : syracuseStep 7745329 = 5808997) B5808997
theorem B7941937 : Blo 1303970 7941937 := bstep (se 2 (by rfl) ⟨2978226, by rfl⟩ : syracuseStep 7941937 = 5956453) B5956453
theorem B3714893 : Blo 1303970 3714893 := bstep (se 3 (by rfl) ⟨696542, by rfl⟩ : syracuseStep 3714893 = 1393085) B1393085
theorem B8359793 : Blo 1303970 8359793 := bstep (se 2 (by rfl) ⟨3134922, by rfl⟩ : syracuseStep 8359793 = 6269845) B6269845
theorem B9908081 : Blo 1303970 9908081 := bstep (se 2 (by rfl) ⟨3715530, by rfl⟩ : syracuseStep 9908081 = 7431061) B7431061
theorem B1650547 : Blo 1303970 1650547 := bstep (se 1 (by rfl) ⟨1237910, by rfl⟩ : syracuseStep 1650547 = 2475821) B2475821
theorem B2936753 : Blo 1303970 2936753 := bstep (se 2 (by rfl) ⟨1101282, by rfl⟩ : syracuseStep 2936753 = 2202565) B2202565
theorem B14864309 : Blo 1303970 14864309 := bstep (se 5 (by rfl) ⟨696764, by rfl⟩ : syracuseStep 14864309 = 1393529) B1393529
theorem B2936771 : Blo 1303970 2936771 := bstep (se 1 (by rfl) ⟨2202578, by rfl⟩ : syracuseStep 2936771 = 4405157) B4405157
theorem B10579909 : Blo 1303970 10579909 := bstep (se 4 (by rfl) ⟨991866, by rfl⟩ : syracuseStep 10579909 = 1983733) B1983733
theorem B9539569 : Blo 1303970 9539569 := bstep (se 2 (by rfl) ⟨3577338, by rfl⟩ : syracuseStep 9539569 = 7154677) B7154677
theorem B3715075 : Blo 1303970 3715075 := bstep (se 1 (by rfl) ⟨2786306, by rfl⟩ : syracuseStep 3715075 = 5572613) B5572613
theorem B4403213 : Blo 1303970 4403213 := bstep (se 3 (by rfl) ⟨825602, by rfl⟩ : syracuseStep 4403213 = 1651205) B1651205
theorem B3715121 : Blo 1303970 3715121 := bstep (se 2 (by rfl) ⟨1393170, by rfl⟩ : syracuseStep 3715121 = 2786341) B2786341
theorem B4403267 : Blo 1303970 4403267 := bstep (se 1 (by rfl) ⟨3302450, by rfl⟩ : syracuseStep 4403267 = 6604901) B6604901
theorem B6697073 : Blo 1303970 6697073 := bstep (se 2 (by rfl) ⟨2511402, by rfl⟩ : syracuseStep 6697073 = 5022805) B5022805
theorem B1413235 : Blo 1303970 1413235 := bstep (se 1 (by rfl) ⟨1059926, by rfl⟩ : syracuseStep 1413235 = 2119853) B2119853
theorem B2937041 : Blo 1303970 2937041 := bstep (se 2 (by rfl) ⟨1101390, by rfl⟩ : syracuseStep 2937041 = 2202781) B2202781
theorem B2478289 : Blo 1303970 2478289 := bstep (se 2 (by rfl) ⟨929358, by rfl⟩ : syracuseStep 2478289 = 1858717) B1858717
theorem B3305681 : Blo 1303970 3305681 := bstep (se 2 (by rfl) ⟨1239630, by rfl⟩ : syracuseStep 3305681 = 2479261) B2479261
theorem B2937059 : Blo 1303970 2937059 := bstep (se 1 (by rfl) ⟨2202794, by rfl⟩ : syracuseStep 2937059 = 4405589) B4405589
theorem B3526897 : Blo 1303970 3526897 := bstep (se 2 (by rfl) ⟨1322586, by rfl⟩ : syracuseStep 3526897 = 2645173) B2645173
theorem B3305731 : Blo 1303970 3305731 := bstep (se 1 (by rfl) ⟨2479298, by rfl⟩ : syracuseStep 3305731 = 4958597) B4958597
theorem B5288269 : Blo 1303970 5288269 := bstep (se 3 (by rfl) ⟨991550, by rfl⟩ : syracuseStep 5288269 = 1983101) B1983101
theorem B4403537 : Blo 1303970 4403537 := bstep (se 2 (by rfl) ⟨1651326, by rfl⟩ : syracuseStep 4403537 = 3302653) B3302653
theorem B1651043 : Blo 1303970 1651043 := bstep (se 1 (by rfl) ⟨1238282, by rfl⟩ : syracuseStep 1651043 = 2476565) B2476565
theorem B4952461 : Blo 1303970 4952461 := bstep (se 3 (by rfl) ⟨928586, by rfl⟩ : syracuseStep 4952461 = 1857173) B1857173
theorem B8360333 : Blo 1303970 8360333 := bstep (se 3 (by rfl) ⟨1567562, by rfl⟩ : syracuseStep 8360333 = 3135125) B3135125
theorem B6607331 : Blo 1303970 6607331 := bstep (se 1 (by rfl) ⟨4955498, by rfl⟩ : syracuseStep 6607331 = 9910997) B9910997
theorem B2937329 : Blo 1303970 2937329 := bstep (se 2 (by rfl) ⟨1101498, by rfl⟩ : syracuseStep 2937329 = 2202997) B2202997
theorem B2937347 : Blo 1303970 2937347 := bstep (se 1 (by rfl) ⟨2203010, by rfl⟩ : syracuseStep 2937347 = 4406021) B4406021
theorem B7156259 : Blo 1303970 7156259 := bstep (se 1 (by rfl) ⟨5367194, by rfl⟩ : syracuseStep 7156259 = 10734389) B10734389
theorem B2478691 : Blo 1303970 2478691 := bstep (se 1 (by rfl) ⟨1859018, by rfl⟩ : syracuseStep 2478691 = 3718037) B3718037
theorem B2683523 : Blo 1303970 2683523 := bstep (se 1 (by rfl) ⟨2012642, by rfl⟩ : syracuseStep 2683523 = 4025285) B4025285
theorem B2478737 : Blo 1303970 2478737 := bstep (se 2 (by rfl) ⟨929526, by rfl⟩ : syracuseStep 2478737 = 1859053) B1859053
theorem B5575331 : Blo 1303970 5575331 := bstep (se 1 (by rfl) ⟨4181498, by rfl⟩ : syracuseStep 5575331 = 8362997) B8362997
theorem B7058117 : Blo 1303970 7058117 := bstep (se 4 (by rfl) ⟨661698, by rfl⟩ : syracuseStep 7058117 = 1323397) B1323397
theorem B2937617 : Blo 1303970 2937617 := bstep (se 2 (by rfl) ⟨1101606, by rfl⟩ : syracuseStep 2937617 = 2203213) B2203213
theorem B3527459 : Blo 1303970 3527459 := bstep (se 1 (by rfl) ⟨2645594, by rfl⟩ : syracuseStep 3527459 = 5291189) B5291189
theorem B2937635 : Blo 1303970 2937635 := bstep (se 1 (by rfl) ⟨2203226, by rfl⟩ : syracuseStep 2937635 = 4406453) B4406453
theorem B4404077 : Blo 1303970 4404077 := bstep (se 3 (by rfl) ⟨825764, by rfl⟩ : syracuseStep 4404077 = 1651529) B1651529
theorem B15872881 : Blo 1303970 15872881 := bstep (se 2 (by rfl) ⟨5952330, by rfl⟩ : syracuseStep 15872881 = 11904661) B11904661
theorem B4404131 : Blo 1303970 4404131 := bstep (se 1 (by rfl) ⟨3303098, by rfl⟩ : syracuseStep 4404131 = 6606197) B6606197
theorem B2479025 : Blo 1303970 2479025 := bstep (se 2 (by rfl) ⟨929634, by rfl⟩ : syracuseStep 2479025 = 1859269) B1859269
theorem B2200513 : Blo 1303970 2200513 := bstep (se 2 (by rfl) ⟨825192, by rfl⟩ : syracuseStep 2200513 = 1650385) B1650385
theorem B2200547 : Blo 1303970 2200547 := bstep (se 1 (by rfl) ⟨1650410, by rfl⟩ : syracuseStep 2200547 = 3300821) B3300821
theorem B1651747 : Blo 1303970 1651747 := bstep (se 1 (by rfl) ⟨1238810, by rfl⟩ : syracuseStep 1651747 = 2477621) B2477621
theorem B2937905 : Blo 1303970 2937905 := bstep (se 2 (by rfl) ⟨1101714, by rfl⟩ : syracuseStep 2937905 = 2203429) B2203429
theorem B2937923 : Blo 1303970 2937923 := bstep (se 1 (by rfl) ⟨2203442, by rfl⟩ : syracuseStep 2937923 = 4406885) B4406885
theorem B2200675 : Blo 1303970 2200675 := bstep (se 1 (by rfl) ⟨1650506, by rfl⟩ : syracuseStep 2200675 = 3301013) B3301013
theorem B4183139 : Blo 1303970 4183139 := bstep (se 1 (by rfl) ⟨3137354, by rfl⟩ : syracuseStep 4183139 = 6274709) B6274709
theorem B1651843 : Blo 1303970 1651843 := bstep (se 1 (by rfl) ⟨1238882, by rfl⟩ : syracuseStep 1651843 = 2477765) B2477765
theorem B7427213 : Blo 1303970 7427213 := bstep (se 3 (by rfl) ⟨1392602, by rfl⟩ : syracuseStep 7427213 = 2785205) B2785205
theorem B4953251 : Blo 1303970 4953251 := bstep (se 1 (by rfl) ⟨3714938, by rfl⟩ : syracuseStep 4953251 = 7429877) B7429877
theorem B4404401 : Blo 1303970 4404401 := bstep (se 2 (by rfl) ⟨1651650, by rfl⟩ : syracuseStep 4404401 = 3303301) B3303301
theorem B2200817 : Blo 1303970 2200817 := bstep (se 2 (by rfl) ⟨825306, by rfl⟩ : syracuseStep 2200817 = 1650613) B1650613
theorem B6608141 : Blo 1303970 6608141 := bstep (se 3 (by rfl) ⟨1239026, by rfl⟩ : syracuseStep 6608141 = 2478053) B2478053
theorem B3437873 : Blo 1303970 3437873 := bstep (se 2 (by rfl) ⟨1289202, by rfl⟩ : syracuseStep 3437873 = 2578405) B2578405
theorem B7058765 : Blo 1303970 7058765 := bstep (se 3 (by rfl) ⟨1323518, by rfl⟩ : syracuseStep 7058765 = 2647037) B2647037
theorem B2938193 : Blo 1303970 2938193 := bstep (se 2 (by rfl) ⟨1101822, by rfl⟩ : syracuseStep 2938193 = 2203645) B2203645
theorem B2938211 : Blo 1303970 2938211 := bstep (se 1 (by rfl) ⟨2203658, by rfl⟩ : syracuseStep 2938211 = 4407317) B4407317
theorem B2200945 : Blo 1303970 2200945 := bstep (se 2 (by rfl) ⟨825354, by rfl⟩ : syracuseStep 2200945 = 1650709) B1650709
theorem B2200979 : Blo 1303970 2200979 := bstep (se 1 (by rfl) ⟨1650734, by rfl⟩ : syracuseStep 2200979 = 3301469) B3301469
theorem B6272419 : Blo 1303970 6272419 := bstep (se 1 (by rfl) ⟨4704314, by rfl⟩ : syracuseStep 6272419 = 9408629) B9408629
theorem B3716579 : Blo 1303970 3716579 := bstep (se 1 (by rfl) ⟨2787434, by rfl⟩ : syracuseStep 3716579 = 5574869) B5574869
theorem B3528173 : Blo 1303970 3528173 := bstep (se 3 (by rfl) ⟨661532, by rfl⟩ : syracuseStep 3528173 = 1323065) B1323065
theorem B2823665 : Blo 1303970 2823665 := bstep (se 2 (by rfl) ⟨1058874, by rfl⟩ : syracuseStep 2823665 = 2117749) B2117749
theorem B2201107 : Blo 1303970 2201107 := bstep (se 1 (by rfl) ⟨1650830, by rfl⟩ : syracuseStep 2201107 = 3301661) B3301661
theorem B1652339 : Blo 1303970 1652339 := bstep (se 1 (by rfl) ⟨1239254, by rfl⟩ : syracuseStep 1652339 = 2478509) B2478509
theorem B2201249 : Blo 1303970 2201249 := bstep (se 2 (by rfl) ⟨825468, by rfl⟩ : syracuseStep 2201249 = 1650937) B1650937
theorem B4404941 : Blo 1303970 4404941 := bstep (se 3 (by rfl) ⟨825926, by rfl⟩ : syracuseStep 4404941 = 1651853) B1651853
theorem B4404995 : Blo 1303970 4404995 := bstep (se 1 (by rfl) ⟨3303746, by rfl⟩ : syracuseStep 4404995 = 6607493) B6607493
theorem B2201377 : Blo 1303970 2201377 := bstep (se 2 (by rfl) ⟨825516, by rfl⟩ : syracuseStep 2201377 = 1651033) B1651033
theorem B4953905 : Blo 1303970 4953905 := bstep (se 2 (by rfl) ⟨1857714, by rfl⟩ : syracuseStep 4953905 = 3715429) B3715429
theorem B3528497 : Blo 1303970 3528497 := bstep (se 2 (by rfl) ⟨1323186, by rfl⟩ : syracuseStep 3528497 = 2646373) B2646373
theorem B28235573 : Blo 1303970 28235573 := bstep (se 5 (by rfl) ⟨1323542, by rfl⟩ : syracuseStep 28235573 = 2647085) B2647085
theorem B2201411 : Blo 1303970 2201411 := bstep (se 1 (by rfl) ⟨1651058, by rfl⟩ : syracuseStep 2201411 = 3302117) B3302117
theorem B2201539 : Blo 1303970 2201539 := bstep (se 1 (by rfl) ⟨1651154, by rfl⟩ : syracuseStep 2201539 = 3302309) B3302309
theorem B2643971 : Blo 1303970 2643971 := bstep (se 1 (by rfl) ⟨1982978, by rfl⟩ : syracuseStep 2643971 = 3965957) B3965957
theorem B4405265 : Blo 1303970 4405265 := bstep (se 2 (by rfl) ⟨1651974, by rfl⟩ : syracuseStep 4405265 = 3303949) B3303949
theorem B5290019 : Blo 1303970 5290019 := bstep (se 1 (by rfl) ⟨3967514, by rfl⟩ : syracuseStep 5290019 = 7935029) B7935029
theorem B7428145 : Blo 1303970 7428145 := bstep (se 2 (by rfl) ⟨2785554, by rfl⟩ : syracuseStep 7428145 = 5571109) B5571109
theorem B2201681 : Blo 1303970 2201681 := bstep (se 2 (by rfl) ⟨825630, by rfl⟩ : syracuseStep 2201681 = 1651261) B1651261
theorem B1955969 : Blo 1303970 1955969 := bstep (se 2 (by rfl) ⟨733488, by rfl⟩ : syracuseStep 1955969 = 1466977) B1466977
theorem B1955987 : Blo 1303970 1955987 := bstep (se 1 (by rfl) ⟨1466990, by rfl⟩ : syracuseStep 1955987 = 2933981) B2933981
theorem B1956017 : Blo 1303970 1956017 := bstep (se 2 (by rfl) ⟨733506, by rfl⟩ : syracuseStep 1956017 = 1467013) B1467013
theorem B1956035 : Blo 1303970 1956035 := bstep (se 1 (by rfl) ⟨1467026, by rfl⟩ : syracuseStep 1956035 = 2934053) B2934053
theorem B2201809 : Blo 1303970 2201809 := bstep (se 2 (by rfl) ⟨825678, by rfl⟩ : syracuseStep 2201809 = 1651357) B1651357
theorem B1956065 : Blo 1303970 1956065 := bstep (se 2 (by rfl) ⟨733524, by rfl⟩ : syracuseStep 1956065 = 1467049) B1467049
theorem B37607651 : Blo 1303970 37607651 := bstep (se 1 (by rfl) ⟨28205738, by rfl⟩ : syracuseStep 37607651 = 56411477) B56411477
theorem B8476913 : Blo 1303970 8476913 := bstep (se 2 (by rfl) ⟨3178842, by rfl⟩ : syracuseStep 8476913 = 6357685) B6357685
theorem B1956083 : Blo 1303970 1956083 := bstep (se 1 (by rfl) ⟨1467062, by rfl⟩ : syracuseStep 1956083 = 2934125) B2934125
theorem B2201843 : Blo 1303970 2201843 := bstep (se 1 (by rfl) ⟨1651382, by rfl⟩ : syracuseStep 2201843 = 3302765) B3302765
theorem B1956113 : Blo 1303970 1956113 := bstep (se 2 (by rfl) ⟨733542, by rfl⟩ : syracuseStep 1956113 = 1467085) B1467085
theorem B1857811 : Blo 1303970 1857811 := bstep (se 1 (by rfl) ⟨1393358, by rfl⟩ : syracuseStep 1857811 = 2786717) B2786717
theorem B1956131 : Blo 1303970 1956131 := bstep (se 1 (by rfl) ⟨1467098, by rfl⟩ : syracuseStep 1956131 = 2934197) B2934197
theorem B1956161 : Blo 1303970 1956161 := bstep (se 2 (by rfl) ⟨733560, by rfl⟩ : syracuseStep 1956161 = 1467121) B1467121
theorem B1956179 : Blo 1303970 1956179 := bstep (se 1 (by rfl) ⟨1467134, by rfl⟩ : syracuseStep 1956179 = 2934269) B2934269
theorem B1956209 : Blo 1303970 1956209 := bstep (se 2 (by rfl) ⟨733578, by rfl⟩ : syracuseStep 1956209 = 1467157) B1467157
theorem B2201971 : Blo 1303970 2201971 := bstep (se 1 (by rfl) ⟨1651478, by rfl⟩ : syracuseStep 2201971 = 3302957) B3302957
theorem B1956227 : Blo 1303970 1956227 := bstep (se 1 (by rfl) ⟨1467170, by rfl⟩ : syracuseStep 1956227 = 2934341) B2934341
theorem B1956257 : Blo 1303970 1956257 := bstep (se 2 (by rfl) ⟨733596, by rfl⟩ : syracuseStep 1956257 = 1467193) B1467193
theorem B1956275 : Blo 1303970 1956275 := bstep (se 1 (by rfl) ⟨1467206, by rfl⟩ : syracuseStep 1956275 = 2934413) B2934413
theorem B1956305 : Blo 1303970 1956305 := bstep (se 2 (by rfl) ⟨733614, by rfl⟩ : syracuseStep 1956305 = 1467229) B1467229
theorem B1956323 : Blo 1303970 1956323 := bstep (se 1 (by rfl) ⟨1467242, by rfl⟩ : syracuseStep 1956323 = 2934485) B2934485
theorem B3135971 : Blo 1303970 3135971 := bstep (se 1 (by rfl) ⟨2351978, by rfl⟩ : syracuseStep 3135971 = 4703957) B4703957
theorem B1956353 : Blo 1303970 1956353 := bstep (se 2 (by rfl) ⟨733632, by rfl⟩ : syracuseStep 1956353 = 1467265) B1467265
theorem B2202113 : Blo 1303970 2202113 := bstep (se 2 (by rfl) ⟨825792, by rfl⟩ : syracuseStep 2202113 = 1651585) B1651585
theorem B1956371 : Blo 1303970 1956371 := bstep (se 1 (by rfl) ⟨1467278, by rfl⟩ : syracuseStep 1956371 = 2934557) B2934557
theorem B4405805 : Blo 1303970 4405805 := bstep (se 3 (by rfl) ⟨826088, by rfl⟩ : syracuseStep 4405805 = 1652177) B1652177
theorem B1956401 : Blo 1303970 1956401 := bstep (se 2 (by rfl) ⟨733650, by rfl⟩ : syracuseStep 1956401 = 1467301) B1467301
theorem B1956419 : Blo 1303970 1956419 := bstep (se 1 (by rfl) ⟨1467314, by rfl⟩ : syracuseStep 1956419 = 2934629) B2934629
theorem B1956449 : Blo 1303970 1956449 := bstep (se 2 (by rfl) ⟨733668, by rfl⟩ : syracuseStep 1956449 = 1467337) B1467337
theorem B14113379 : Blo 1303970 14113379 := bstep (se 1 (by rfl) ⟨10585034, by rfl⟩ : syracuseStep 14113379 = 21170069) B21170069
theorem B4405859 : Blo 1303970 4405859 := bstep (se 1 (by rfl) ⟨3304394, by rfl⟩ : syracuseStep 4405859 = 6608789) B6608789
theorem B6273649 : Blo 1303970 6273649 := bstep (se 2 (by rfl) ⟨2352618, by rfl⟩ : syracuseStep 6273649 = 4705237) B4705237
theorem B5577329 : Blo 1303970 5577329 := bstep (se 2 (by rfl) ⟨2091498, by rfl⟩ : syracuseStep 5577329 = 4182997) B4182997
theorem B1956467 : Blo 1303970 1956467 := bstep (se 1 (by rfl) ⟨1467350, by rfl⟩ : syracuseStep 1956467 = 2934701) B2934701
theorem B2202241 : Blo 1303970 2202241 := bstep (se 2 (by rfl) ⟨825840, by rfl⟩ : syracuseStep 2202241 = 1651681) B1651681
theorem B1956497 : Blo 1303970 1956497 := bstep (se 2 (by rfl) ⟨733686, by rfl⟩ : syracuseStep 1956497 = 1467373) B1467373
theorem B1956515 : Blo 1303970 1956515 := bstep (se 1 (by rfl) ⟨1467386, by rfl⟩ : syracuseStep 1956515 = 2934773) B2934773
theorem B2202275 : Blo 1303970 2202275 := bstep (se 1 (by rfl) ⟨1651706, by rfl⟩ : syracuseStep 2202275 = 3303413) B3303413
theorem B3717809 : Blo 1303970 3717809 := bstep (se 2 (by rfl) ⟨1394178, by rfl⟩ : syracuseStep 3717809 = 2788357) B2788357
theorem B1956545 : Blo 1303970 1956545 := bstep (se 2 (by rfl) ⟨733704, by rfl⟩ : syracuseStep 1956545 = 1467409) B1467409
theorem B1956563 : Blo 1303970 1956563 := bstep (se 1 (by rfl) ⟨1467422, by rfl⟩ : syracuseStep 1956563 = 2934845) B2934845
theorem B1956593 : Blo 1303970 1956593 := bstep (se 2 (by rfl) ⟨733722, by rfl⟩ : syracuseStep 1956593 = 1467445) B1467445
theorem B1956611 : Blo 1303970 1956611 := bstep (se 1 (by rfl) ⟨1467458, by rfl⟩ : syracuseStep 1956611 = 2934917) B2934917
theorem B3767057 : Blo 1303970 3767057 := bstep (se 2 (by rfl) ⟨1412646, by rfl⟩ : syracuseStep 3767057 = 2825293) B2825293
theorem B1956641 : Blo 1303970 1956641 := bstep (se 2 (by rfl) ⟨733740, by rfl⟩ : syracuseStep 1956641 = 1467481) B1467481
theorem B2202403 : Blo 1303970 2202403 := bstep (se 1 (by rfl) ⟨1651802, by rfl⟩ : syracuseStep 2202403 = 3303605) B3303605
theorem B1956659 : Blo 1303970 1956659 := bstep (se 1 (by rfl) ⟨1467494, by rfl⟩ : syracuseStep 1956659 = 2934989) B2934989
theorem B1956689 : Blo 1303970 1956689 := bstep (se 2 (by rfl) ⟨733758, by rfl⟩ : syracuseStep 1956689 = 1467517) B1467517
theorem B1956707 : Blo 1303970 1956707 := bstep (se 1 (by rfl) ⟨1467530, by rfl⟩ : syracuseStep 1956707 = 2935061) B2935061
theorem B4406129 : Blo 1303970 4406129 := bstep (se 2 (by rfl) ⟨1652298, by rfl⟩ : syracuseStep 4406129 = 3304597) B3304597
theorem B1956737 : Blo 1303970 1956737 := bstep (se 2 (by rfl) ⟨733776, by rfl⟩ : syracuseStep 1956737 = 1467553) B1467553
theorem B1956755 : Blo 1303970 1956755 := bstep (se 1 (by rfl) ⟨1467566, by rfl⟩ : syracuseStep 1956755 = 2935133) B2935133
theorem B1956785 : Blo 1303970 1956785 := bstep (se 2 (by rfl) ⟨733794, by rfl⟩ : syracuseStep 1956785 = 1467589) B1467589
theorem B2202545 : Blo 1303970 2202545 := bstep (se 2 (by rfl) ⟨825954, by rfl⟩ : syracuseStep 2202545 = 1651909) B1651909
theorem B1956803 : Blo 1303970 1956803 := bstep (se 1 (by rfl) ⟨1467602, by rfl⟩ : syracuseStep 1956803 = 2935205) B2935205
theorem B1956833 : Blo 1303970 1956833 := bstep (se 2 (by rfl) ⟨733812, by rfl⟩ : syracuseStep 1956833 = 1467625) B1467625
theorem B1956851 : Blo 1303970 1956851 := bstep (se 1 (by rfl) ⟨1467638, by rfl⟩ : syracuseStep 1956851 = 2935277) B2935277
theorem B1956881 : Blo 1303970 1956881 := bstep (se 2 (by rfl) ⟨733830, by rfl⟩ : syracuseStep 1956881 = 1467661) B1467661
theorem B1956899 : Blo 1303970 1956899 := bstep (se 1 (by rfl) ⟨1467674, by rfl⟩ : syracuseStep 1956899 = 2935349) B2935349
theorem B2202673 : Blo 1303970 2202673 := bstep (se 2 (by rfl) ⟨826002, by rfl⟩ : syracuseStep 2202673 = 1652005) B1652005
theorem B25426997 : Blo 1303970 25426997 := bstep (se 5 (by rfl) ⟨1191890, by rfl⟩ : syracuseStep 25426997 = 2383781) B2383781
theorem B1956929 : Blo 1303970 1956929 := bstep (se 2 (by rfl) ⟨733848, by rfl⟩ : syracuseStep 1956929 = 1467697) B1467697
theorem B1956947 : Blo 1303970 1956947 := bstep (se 1 (by rfl) ⟨1467710, by rfl⟩ : syracuseStep 1956947 = 2935421) B2935421
theorem B2202707 : Blo 1303970 2202707 := bstep (se 1 (by rfl) ⟨1652030, by rfl⟩ : syracuseStep 2202707 = 3304061) B3304061
theorem B1956977 : Blo 1303970 1956977 := bstep (se 2 (by rfl) ⟨733866, by rfl⟩ : syracuseStep 1956977 = 1467733) B1467733
theorem B1956995 : Blo 1303970 1956995 := bstep (se 1 (by rfl) ⟨1467746, by rfl⟩ : syracuseStep 1956995 = 2935493) B2935493
theorem B1957025 : Blo 1303970 1957025 := bstep (se 2 (by rfl) ⟨733884, by rfl⟩ : syracuseStep 1957025 = 1467769) B1467769
theorem B1957043 : Blo 1303970 1957043 := bstep (se 1 (by rfl) ⟨1467782, by rfl⟩ : syracuseStep 1957043 = 2935565) B2935565
theorem B1957073 : Blo 1303970 1957073 := bstep (se 2 (by rfl) ⟨733902, by rfl⟩ : syracuseStep 1957073 = 1467805) B1467805
theorem B2202835 : Blo 1303970 2202835 := bstep (se 1 (by rfl) ⟨1652126, by rfl⟩ : syracuseStep 2202835 = 3304253) B3304253
theorem B1957091 : Blo 1303970 1957091 := bstep (se 1 (by rfl) ⟨1467818, by rfl⟩ : syracuseStep 1957091 = 2935637) B2935637
theorem B4955363 : Blo 1303970 4955363 := bstep (se 1 (by rfl) ⟨3716522, by rfl⟩ : syracuseStep 4955363 = 7433045) B7433045
theorem B4955377 : Blo 1303970 4955377 := bstep (se 2 (by rfl) ⟨1858266, by rfl⟩ : syracuseStep 4955377 = 3716533) B3716533
theorem B1957121 : Blo 1303970 1957121 := bstep (se 2 (by rfl) ⟨733920, by rfl⟩ : syracuseStep 1957121 = 1467841) B1467841
theorem B1957139 : Blo 1303970 1957139 := bstep (se 1 (by rfl) ⟨1467854, by rfl⟩ : syracuseStep 1957139 = 2935709) B2935709
theorem B2350385 : Blo 1303970 2350385 := bstep (se 2 (by rfl) ⟨881394, by rfl⟩ : syracuseStep 2350385 = 1762789) B1762789
theorem B1957169 : Blo 1303970 1957169 := bstep (se 2 (by rfl) ⟨733938, by rfl⟩ : syracuseStep 1957169 = 1467877) B1467877
theorem B1957187 : Blo 1303970 1957187 := bstep (se 1 (by rfl) ⟨1467890, by rfl⟩ : syracuseStep 1957187 = 2935781) B2935781
theorem B3300689 : Blo 1303970 3300689 := bstep (se 2 (by rfl) ⟨1237758, by rfl⟩ : syracuseStep 3300689 = 2475517) B2475517
theorem B1957217 : Blo 1303970 1957217 := bstep (se 2 (by rfl) ⟨733956, by rfl⟩ : syracuseStep 1957217 = 1467913) B1467913
theorem B2202977 : Blo 1303970 2202977 := bstep (se 2 (by rfl) ⟨826116, by rfl⟩ : syracuseStep 2202977 = 1652233) B1652233
theorem B1957235 : Blo 1303970 1957235 := bstep (se 1 (by rfl) ⟨1467926, by rfl⟩ : syracuseStep 1957235 = 2935853) B2935853
theorem B1858945 : Blo 1303970 1858945 := bstep (se 2 (by rfl) ⟨697104, by rfl⟩ : syracuseStep 1858945 = 1394209) B1394209
theorem B4406669 : Blo 1303970 4406669 := bstep (se 3 (by rfl) ⟨826250, by rfl⟩ : syracuseStep 4406669 = 1652501) B1652501
theorem B1957265 : Blo 1303970 1957265 := bstep (se 2 (by rfl) ⟨733974, by rfl⟩ : syracuseStep 1957265 = 1467949) B1467949
theorem B6602147 : Blo 1303970 6602147 := bstep (se 1 (by rfl) ⟨4951610, by rfl⟩ : syracuseStep 6602147 = 9903221) B9903221
theorem B1957283 : Blo 1303970 1957283 := bstep (se 1 (by rfl) ⟨1467962, by rfl⟩ : syracuseStep 1957283 = 2935925) B2935925
theorem B1957313 : Blo 1303970 1957313 := bstep (se 2 (by rfl) ⟨733992, by rfl⟩ : syracuseStep 1957313 = 1467985) B1467985
theorem B4406723 : Blo 1303970 4406723 := bstep (se 1 (by rfl) ⟨3305042, by rfl⟩ : syracuseStep 4406723 = 6610085) B6610085
theorem B1957331 : Blo 1303970 1957331 := bstep (se 1 (by rfl) ⟨1467998, by rfl⟩ : syracuseStep 1957331 = 2935997) B2935997
theorem B2203105 : Blo 1303970 2203105 := bstep (se 2 (by rfl) ⟨826164, by rfl⟩ : syracuseStep 2203105 = 1652329) B1652329
theorem B1859041 : Blo 1303970 1859041 := bstep (se 2 (by rfl) ⟨697140, by rfl⟩ : syracuseStep 1859041 = 1394281) B1394281
theorem B7429603 : Blo 1303970 7429603 := bstep (se 1 (by rfl) ⟨5572202, by rfl⟩ : syracuseStep 7429603 = 11144405) B11144405
theorem B1957361 : Blo 1303970 1957361 := bstep (se 2 (by rfl) ⟨734010, by rfl⟩ : syracuseStep 1957361 = 1468021) B1468021
theorem B2350595 : Blo 1303970 2350595 := bstep (se 1 (by rfl) ⟨1762946, by rfl⟩ : syracuseStep 2350595 = 3525893) B3525893
theorem B1957379 : Blo 1303970 1957379 := bstep (se 1 (by rfl) ⟨1468034, by rfl⟩ : syracuseStep 1957379 = 2936069) B2936069
theorem B2203139 : Blo 1303970 2203139 := bstep (se 1 (by rfl) ⟨1652354, by rfl⟩ : syracuseStep 2203139 = 3304709) B3304709
theorem B8363533 : Blo 1303970 8363533 := bstep (se 3 (by rfl) ⟨1568162, by rfl⟩ : syracuseStep 8363533 = 3136325) B3136325
theorem B5578253 : Blo 1303970 5578253 := bstep (se 3 (by rfl) ⟨1045922, by rfl⟩ : syracuseStep 5578253 = 2091845) B2091845
theorem B1957409 : Blo 1303970 1957409 := bstep (se 2 (by rfl) ⟨734028, by rfl⟩ : syracuseStep 1957409 = 1468057) B1468057
theorem B1957427 : Blo 1303970 1957427 := bstep (se 1 (by rfl) ⟨1468070, by rfl⟩ : syracuseStep 1957427 = 2936141) B2936141
theorem B7528013 : Blo 1303970 7528013 := bstep (se 3 (by rfl) ⟨1411502, by rfl⟩ : syracuseStep 7528013 = 2823005) B2823005
theorem B1957457 : Blo 1303970 1957457 := bstep (se 2 (by rfl) ⟨734046, by rfl⟩ : syracuseStep 1957457 = 1468093) B1468093
theorem B1957475 : Blo 1303970 1957475 := bstep (se 1 (by rfl) ⟨1468106, by rfl⟩ : syracuseStep 1957475 = 2936213) B2936213
theorem B5021297 : Blo 1303970 5021297 := bstep (se 2 (by rfl) ⟨1882986, by rfl⟩ : syracuseStep 5021297 = 3765973) B3765973
theorem B1957505 : Blo 1303970 1957505 := bstep (se 2 (by rfl) ⟨734064, by rfl⟩ : syracuseStep 1957505 = 1468129) B1468129
theorem B2203267 : Blo 1303970 2203267 := bstep (se 1 (by rfl) ⟨1652450, by rfl⟩ : syracuseStep 2203267 = 3304901) B3304901
theorem B1957523 : Blo 1303970 1957523 := bstep (se 1 (by rfl) ⟨1468142, by rfl⟩ : syracuseStep 1957523 = 2936285) B2936285
theorem B1957553 : Blo 1303970 1957553 := bstep (se 2 (by rfl) ⟨734082, by rfl⟩ : syracuseStep 1957553 = 1468165) B1468165
theorem B3137201 : Blo 1303970 3137201 := bstep (se 2 (by rfl) ⟨1176450, by rfl⟩ : syracuseStep 3137201 = 2352901) B2352901
theorem B1957571 : Blo 1303970 1957571 := bstep (se 1 (by rfl) ⟨1468178, by rfl⟩ : syracuseStep 1957571 = 2936357) B2936357
theorem B4406993 : Blo 1303970 4406993 := bstep (se 2 (by rfl) ⟨1652622, by rfl⟩ : syracuseStep 4406993 = 3305245) B3305245
theorem B1957601 : Blo 1303970 1957601 := bstep (se 2 (by rfl) ⟨734100, by rfl⟩ : syracuseStep 1957601 = 1468201) B1468201
theorem B1957619 : Blo 1303970 1957619 := bstep (se 1 (by rfl) ⟨1468214, by rfl⟩ : syracuseStep 1957619 = 2936429) B2936429
theorem B1957649 : Blo 1303970 1957649 := bstep (se 2 (by rfl) ⟨734118, by rfl⟩ : syracuseStep 1957649 = 1468237) B1468237
theorem B2203409 : Blo 1303970 2203409 := bstep (se 2 (by rfl) ⟨826278, by rfl⟩ : syracuseStep 2203409 = 1652557) B1652557
theorem B2350883 : Blo 1303970 2350883 := bstep (se 1 (by rfl) ⟨1763162, by rfl⟩ : syracuseStep 2350883 = 3526325) B3526325
theorem B1957667 : Blo 1303970 1957667 := bstep (se 1 (by rfl) ⟨1468250, by rfl⟩ : syracuseStep 1957667 = 2936501) B2936501
theorem B1957697 : Blo 1303970 1957697 := bstep (se 2 (by rfl) ⟨734136, by rfl⟩ : syracuseStep 1957697 = 1468273) B1468273
theorem B1957715 : Blo 1303970 1957715 := bstep (se 1 (by rfl) ⟨1468286, by rfl⟩ : syracuseStep 1957715 = 2936573) B2936573
theorem B1957745 : Blo 1303970 1957745 := bstep (se 2 (by rfl) ⟨734154, by rfl⟩ : syracuseStep 1957745 = 1468309) B1468309
theorem B2088833 : Blo 1303970 2088833 := bstep (se 2 (by rfl) ⟨783312, by rfl⟩ : syracuseStep 2088833 = 1566625) B1566625
theorem B1957763 : Blo 1303970 1957763 := bstep (se 1 (by rfl) ⟨1468322, by rfl⟩ : syracuseStep 1957763 = 2936645) B2936645
theorem B2203537 : Blo 1303970 2203537 := bstep (se 2 (by rfl) ⟨826326, by rfl⟩ : syracuseStep 2203537 = 1652653) B1652653
theorem B1957793 : Blo 1303970 1957793 := bstep (se 2 (by rfl) ⟨734172, by rfl⟩ : syracuseStep 1957793 = 1468345) B1468345
theorem B1392547 : Blo 1303970 1392547 := bstep (se 1 (by rfl) ⟨1044410, by rfl⟩ : syracuseStep 1392547 = 2088821) B2088821
theorem B1957811 : Blo 1303970 1957811 := bstep (se 1 (by rfl) ⟨1468358, by rfl⟩ : syracuseStep 1957811 = 2936717) B2936717
theorem B2203571 : Blo 1303970 2203571 := bstep (se 1 (by rfl) ⟨1652678, by rfl⟩ : syracuseStep 2203571 = 3305357) B3305357
theorem B1957841 : Blo 1303970 1957841 := bstep (se 2 (by rfl) ⟨734190, by rfl⟩ : syracuseStep 1957841 = 1468381) B1468381
theorem B2826193 : Blo 1303970 2826193 := bstep (se 2 (by rfl) ⟨1059822, by rfl⟩ : syracuseStep 2826193 = 2119645) B2119645
theorem B1957859 : Blo 1303970 1957859 := bstep (se 1 (by rfl) ⟨1468394, by rfl⟩ : syracuseStep 1957859 = 2936789) B2936789
theorem B7430129 : Blo 1303970 7430129 := bstep (se 2 (by rfl) ⟨2786298, by rfl⟩ : syracuseStep 7430129 = 5572597) B5572597
theorem B1957913 : Blo 1303970 1957913 := bstep (se 2 (by rfl) ⟨734217, by rfl⟩ : syracuseStep 1957913 = 1468435) B1468435
theorem B9904193 : Blo 1303970 9904193 := bstep (se 2 (by rfl) ⟨3714072, by rfl⟩ : syracuseStep 9904193 = 7428145) B7428145
theorem B4464715 : Blo 1303970 4464715 := bstep (se 1 (by rfl) ⟨3348536, by rfl⟩ : syracuseStep 4464715 = 6697073) B6697073
theorem B4407371 : Blo 1303970 4407371 := bstep (se 1 (by rfl) ⟨3305528, by rfl⟩ : syracuseStep 4407371 = 6611057) B6611057
theorem B2785367 : Blo 1303970 2785367 := bstep (se 1 (by rfl) ⟨2089025, by rfl⟩ : syracuseStep 2785367 = 4178051) B4178051
theorem B1958027 : Blo 1303970 1958027 := bstep (se 1 (by rfl) ⟨1468520, by rfl⟩ : syracuseStep 1958027 = 2937041) B2937041
theorem B2203787 : Blo 1303970 2203787 := bstep (se 1 (by rfl) ⟨1652840, by rfl⟩ : syracuseStep 2203787 = 3305681) B3305681
theorem B1958039 : Blo 1303970 1958039 := bstep (se 1 (by rfl) ⟨1468529, by rfl⟩ : syracuseStep 1958039 = 2937059) B2937059
theorem B1884313 : Blo 1303970 1884313 := bstep (se 2 (by rfl) ⟨706617, by rfl⟩ : syracuseStep 1884313 = 1413235) B1413235
theorem B1958105 : Blo 1303970 1958105 := bstep (se 2 (by rfl) ⟨734289, by rfl⟩ : syracuseStep 1958105 = 1468579) B1468579
theorem B10576145 : Blo 1303970 10576145 := bstep (se 2 (by rfl) ⟨3966054, by rfl⟩ : syracuseStep 10576145 = 7932109) B7932109
theorem B4702529 : Blo 1303970 4702529 := bstep (se 2 (by rfl) ⟨1763448, by rfl⟩ : syracuseStep 4702529 = 3526897) B3526897
theorem B1958219 : Blo 1303970 1958219 := bstep (se 1 (by rfl) ⟨1468664, by rfl⟩ : syracuseStep 1958219 = 2937329) B2937329
theorem B1958231 : Blo 1303970 1958231 := bstep (se 1 (by rfl) ⟨1468673, by rfl⟩ : syracuseStep 1958231 = 2937347) B2937347
theorem B4407641 : Blo 1303970 4407641 := bstep (se 2 (by rfl) ⟨1652865, by rfl⟩ : syracuseStep 4407641 = 3305731) B3305731
theorem B1958297 : Blo 1303970 1958297 := bstep (se 2 (by rfl) ⟨734361, by rfl⟩ : syracuseStep 1958297 = 1468723) B1468723
theorem B1958411 : Blo 1303970 1958411 := bstep (se 1 (by rfl) ⟨1468808, by rfl⟩ : syracuseStep 1958411 = 2937617) B2937617
theorem B6603281 : Blo 1303970 6603281 := bstep (se 2 (by rfl) ⟨2476230, by rfl⟩ : syracuseStep 6603281 = 4952461) B4952461
theorem B2351639 : Blo 1303970 2351639 := bstep (se 1 (by rfl) ⟨1763729, by rfl⟩ : syracuseStep 2351639 = 3527459) B3527459
theorem B1958423 : Blo 1303970 1958423 := bstep (se 1 (by rfl) ⟨1468817, by rfl⟩ : syracuseStep 1958423 = 2937635) B2937635
theorem B1958489 : Blo 1303970 1958489 := bstep (se 2 (by rfl) ⟨734433, by rfl⟩ : syracuseStep 1958489 = 1468867) B1468867
theorem B2785931 : Blo 1303970 2785931 := bstep (se 1 (by rfl) ⟨2089448, by rfl⟩ : syracuseStep 2785931 = 4178897) B4178897
theorem B1467031 : Blo 1303970 1467031 := bstep (se 1 (by rfl) ⟨1100273, by rfl⟩ : syracuseStep 1467031 = 2200547) B2200547
theorem B6603443 : Blo 1303970 6603443 := bstep (se 1 (by rfl) ⟨4952582, by rfl⟩ : syracuseStep 6603443 = 9905165) B9905165
theorem B1958603 : Blo 1303970 1958603 := bstep (se 1 (by rfl) ⟨1468952, by rfl⟩ : syracuseStep 1958603 = 2937905) B2937905
theorem B1393367 : Blo 1303970 1393367 := bstep (se 1 (by rfl) ⟨1045025, by rfl⟩ : syracuseStep 1393367 = 2090051) B2090051
theorem B1958615 : Blo 1303970 1958615 := bstep (se 1 (by rfl) ⟨1468961, by rfl⟩ : syracuseStep 1958615 = 2937923) B2937923
theorem B3302167 : Blo 1303970 3302167 := bstep (se 1 (by rfl) ⟨2476625, by rfl⟩ : syracuseStep 3302167 = 4953251) B4953251
theorem B1958681 : Blo 1303970 1958681 := bstep (se 2 (by rfl) ⟨734505, by rfl⟩ : syracuseStep 1958681 = 1469011) B1469011
theorem B8364865 : Blo 1303970 8364865 := bstep (se 2 (by rfl) ⟨3136824, by rfl⟩ : syracuseStep 8364865 = 6273649) B6273649
theorem B1467211 : Blo 1303970 1467211 := bstep (se 1 (by rfl) ⟨1100408, by rfl⟩ : syracuseStep 1467211 = 2200817) B2200817
theorem B1958795 : Blo 1303970 1958795 := bstep (se 1 (by rfl) ⟨1469096, by rfl⟩ : syracuseStep 1958795 = 2938193) B2938193
theorem B1958807 : Blo 1303970 1958807 := bstep (se 1 (by rfl) ⟨1469105, by rfl⟩ : syracuseStep 1958807 = 2938211) B2938211
theorem B1467319 : Blo 1303970 1467319 := bstep (se 1 (by rfl) ⟨1100489, by rfl⟩ : syracuseStep 1467319 = 2200979) B2200979
theorem B1958873 : Blo 1303970 1958873 := bstep (se 2 (by rfl) ⟨734577, by rfl⟩ : syracuseStep 1958873 = 1469155) B1469155
theorem B2352115 : Blo 1303970 2352115 := bstep (se 1 (by rfl) ⟨1764086, by rfl⟩ : syracuseStep 2352115 = 3528173) B3528173
theorem B2786393 : Blo 1303970 2786393 := bstep (se 2 (by rfl) ⟨1044897, by rfl⟩ : syracuseStep 2786393 = 2089795) B2089795
theorem B1467499 : Blo 1303970 1467499 := bstep (se 1 (by rfl) ⟨1100624, by rfl⟩ : syracuseStep 1467499 = 2201249) B2201249
theorem B37618829 : Blo 1303970 37618829 := bstep (se 3 (by rfl) ⟨7053530, by rfl⟩ : syracuseStep 37618829 = 14107061) B14107061
theorem B2933963 : Blo 1303970 2933963 := bstep (se 1 (by rfl) ⟨2200472, by rfl⟩ : syracuseStep 2933963 = 4400945) B4400945
theorem B3302603 : Blo 1303970 3302603 := bstep (se 1 (by rfl) ⟨2476952, by rfl⟩ : syracuseStep 3302603 = 4953905) B4953905
theorem B2352331 : Blo 1303970 2352331 := bstep (se 1 (by rfl) ⟨1764248, by rfl⟩ : syracuseStep 2352331 = 3528497) B3528497
theorem B1467607 : Blo 1303970 1467607 := bstep (se 1 (by rfl) ⟨1100705, by rfl⟩ : syracuseStep 1467607 = 2201411) B2201411
theorem B4703453 : Blo 1303970 4703453 := bstep (se 3 (by rfl) ⟨881897, by rfl⟩ : syracuseStep 4703453 = 1763795) B1763795
theorem B2934017 : Blo 1303970 2934017 := bstep (se 2 (by rfl) ⟨1100256, by rfl⟩ : syracuseStep 2934017 = 2200513) B2200513
theorem B3015937 : Blo 1303970 3015937 := bstep (se 2 (by rfl) ⟨1130976, by rfl⟩ : syracuseStep 3015937 = 2261953) B2261953
theorem B7529773 : Blo 1303970 7529773 := bstep (se 3 (by rfl) ⟨1411832, by rfl⟩ : syracuseStep 7529773 = 2823665) B2823665
theorem B5571929 : Blo 1303970 5571929 := bstep (se 2 (by rfl) ⟨2089473, by rfl⟩ : syracuseStep 5571929 = 4178947) B4178947
theorem B11150693 : Blo 1303970 11150693 := bstep (se 4 (by rfl) ⟨1045377, by rfl⟩ : syracuseStep 11150693 = 2090755) B2090755
theorem B1467787 : Blo 1303970 1467787 := bstep (se 1 (by rfl) ⟨1100840, by rfl⟩ : syracuseStep 1467787 = 2201681) B2201681
theorem B1394059 : Blo 1303970 1394059 := bstep (se 1 (by rfl) ⟨1045544, by rfl⟩ : syracuseStep 1394059 = 2091089) B2091089
theorem B1303979 : Blo 1303970 1303979 := bstep (se 1 (by rfl) ⟨977984, by rfl⟩ : syracuseStep 1303979 = 1955969) B1955969
theorem B1303991 : Blo 1303970 1303991 := bstep (se 1 (by rfl) ⟨977993, by rfl⟩ : syracuseStep 1303991 = 1955987) B1955987
theorem B2352577 : Blo 1303970 2352577 := bstep (se 2 (by rfl) ⟨882216, by rfl⟩ : syracuseStep 2352577 = 1764433) B1764433
theorem B1304011 : Blo 1303970 1304011 := bstep (se 1 (by rfl) ⟨978008, by rfl⟩ : syracuseStep 1304011 = 1956017) B1956017
theorem B1304023 : Blo 1303970 1304023 := bstep (se 1 (by rfl) ⟨978017, by rfl⟩ : syracuseStep 1304023 = 1956035) B1956035
theorem B2934233 : Blo 1303970 2934233 := bstep (se 2 (by rfl) ⟨1100337, by rfl⟩ : syracuseStep 2934233 = 2200675) B2200675
theorem B1304043 : Blo 1303970 1304043 := bstep (se 1 (by rfl) ⟨978032, by rfl⟩ : syracuseStep 1304043 = 1956065) B1956065
theorem B1304055 : Blo 1303970 1304055 := bstep (se 1 (by rfl) ⟨978041, by rfl⟩ : syracuseStep 1304055 = 1956083) B1956083
theorem B1467895 : Blo 1303970 1467895 := bstep (se 1 (by rfl) ⟨1100921, by rfl⟩ : syracuseStep 1467895 = 2201843) B2201843
theorem B1304075 : Blo 1303970 1304075 := bstep (se 1 (by rfl) ⟨978056, by rfl⟩ : syracuseStep 1304075 = 1956113) B1956113
theorem B1304087 : Blo 1303970 1304087 := bstep (se 1 (by rfl) ⟨978065, by rfl⟩ : syracuseStep 1304087 = 1956131) B1956131
theorem B1304107 : Blo 1303970 1304107 := bstep (se 1 (by rfl) ⟨978080, by rfl⟩ : syracuseStep 1304107 = 1956161) B1956161
theorem B2934323 : Blo 1303970 2934323 := bstep (se 1 (by rfl) ⟨2200742, by rfl⟩ : syracuseStep 2934323 = 4401485) B4401485
theorem B1304119 : Blo 1303970 1304119 := bstep (se 1 (by rfl) ⟨978089, by rfl⟩ : syracuseStep 1304119 = 1956179) B1956179
theorem B3302977 : Blo 1303970 3302977 := bstep (se 2 (by rfl) ⟨1238616, by rfl⟩ : syracuseStep 3302977 = 2477233) B2477233
theorem B1304139 : Blo 1303970 1304139 := bstep (se 1 (by rfl) ⟨978104, by rfl⟩ : syracuseStep 1304139 = 1956209) B1956209
theorem B1304151 : Blo 1303970 1304151 := bstep (se 1 (by rfl) ⟨978113, by rfl⟩ : syracuseStep 1304151 = 1956227) B1956227
theorem B2934359 : Blo 1303970 2934359 := bstep (se 1 (by rfl) ⟨2200769, by rfl⟩ : syracuseStep 2934359 = 4401539) B4401539
theorem B1304171 : Blo 1303970 1304171 := bstep (se 1 (by rfl) ⟨978128, by rfl⟩ : syracuseStep 1304171 = 1956257) B1956257
theorem B1304183 : Blo 1303970 1304183 := bstep (se 1 (by rfl) ⟨978137, by rfl⟩ : syracuseStep 1304183 = 1956275) B1956275
theorem B1304203 : Blo 1303970 1304203 := bstep (se 1 (by rfl) ⟨978152, by rfl⟩ : syracuseStep 1304203 = 1956305) B1956305
theorem B1304215 : Blo 1303970 1304215 := bstep (se 1 (by rfl) ⟨978161, by rfl⟩ : syracuseStep 1304215 = 1956323) B1956323
theorem B2090647 : Blo 1303970 2090647 := bstep (se 1 (by rfl) ⟨1567985, by rfl⟩ : syracuseStep 2090647 = 3135971) B3135971
theorem B1304235 : Blo 1303970 1304235 := bstep (se 1 (by rfl) ⟨978176, by rfl⟩ : syracuseStep 1304235 = 1956353) B1956353
theorem B1468075 : Blo 1303970 1468075 := bstep (se 1 (by rfl) ⟨1101056, by rfl⟩ : syracuseStep 1468075 = 2202113) B2202113
theorem B1304247 : Blo 1303970 1304247 := bstep (se 1 (by rfl) ⟨978185, by rfl⟩ : syracuseStep 1304247 = 1956371) B1956371
theorem B1304267 : Blo 1303970 1304267 := bstep (se 1 (by rfl) ⟨978200, by rfl⟩ : syracuseStep 1304267 = 1956401) B1956401
theorem B1304279 : Blo 1303970 1304279 := bstep (se 1 (by rfl) ⟨978209, by rfl⟩ : syracuseStep 1304279 = 1956419) B1956419
theorem B1304299 : Blo 1303970 1304299 := bstep (se 1 (by rfl) ⟨978224, by rfl⟩ : syracuseStep 1304299 = 1956449) B1956449
theorem B1304311 : Blo 1303970 1304311 := bstep (se 1 (by rfl) ⟨978233, by rfl⟩ : syracuseStep 1304311 = 1956467) B1956467
theorem B2934539 : Blo 1303970 2934539 := bstep (se 1 (by rfl) ⟨2200904, by rfl⟩ : syracuseStep 2934539 = 4401809) B4401809
theorem B1304331 : Blo 1303970 1304331 := bstep (se 1 (by rfl) ⟨978248, by rfl⟩ : syracuseStep 1304331 = 1956497) B1956497
theorem B1304343 : Blo 1303970 1304343 := bstep (se 1 (by rfl) ⟨978257, by rfl⟩ : syracuseStep 1304343 = 1956515) B1956515
theorem B1468183 : Blo 1303970 1468183 := bstep (se 1 (by rfl) ⟨1101137, by rfl⟩ : syracuseStep 1468183 = 2202275) B2202275
theorem B1304363 : Blo 1303970 1304363 := bstep (se 1 (by rfl) ⟨978272, by rfl⟩ : syracuseStep 1304363 = 1956545) B1956545
theorem B1304375 : Blo 1303970 1304375 := bstep (se 1 (by rfl) ⟨978281, by rfl⟩ : syracuseStep 1304375 = 1956563) B1956563
theorem B2934593 : Blo 1303970 2934593 := bstep (se 2 (by rfl) ⟨1100472, by rfl⟩ : syracuseStep 2934593 = 2200945) B2200945
theorem B1304395 : Blo 1303970 1304395 := bstep (se 1 (by rfl) ⟨978296, by rfl⟩ : syracuseStep 1304395 = 1956593) B1956593
theorem B1304407 : Blo 1303970 1304407 := bstep (se 1 (by rfl) ⟨978305, by rfl⟩ : syracuseStep 1304407 = 1956611) B1956611
theorem B1304427 : Blo 1303970 1304427 := bstep (se 1 (by rfl) ⟨978320, by rfl⟩ : syracuseStep 1304427 = 1956641) B1956641
theorem B1304439 : Blo 1303970 1304439 := bstep (se 1 (by rfl) ⟨978329, by rfl⟩ : syracuseStep 1304439 = 1956659) B1956659
theorem B1304459 : Blo 1303970 1304459 := bstep (se 1 (by rfl) ⟨978344, by rfl⟩ : syracuseStep 1304459 = 1956689) B1956689
theorem B1304471 : Blo 1303970 1304471 := bstep (se 1 (by rfl) ⟨978353, by rfl⟩ : syracuseStep 1304471 = 1956707) B1956707
theorem B1304491 : Blo 1303970 1304491 := bstep (se 1 (by rfl) ⟨978368, by rfl⟩ : syracuseStep 1304491 = 1956737) B1956737
theorem B1304503 : Blo 1303970 1304503 := bstep (se 1 (by rfl) ⟨978377, by rfl⟩ : syracuseStep 1304503 = 1956755) B1956755
theorem B1304523 : Blo 1303970 1304523 := bstep (se 1 (by rfl) ⟨978392, by rfl⟩ : syracuseStep 1304523 = 1956785) B1956785
theorem B1468363 : Blo 1303970 1468363 := bstep (se 1 (by rfl) ⟨1101272, by rfl⟩ : syracuseStep 1468363 = 2202545) B2202545
theorem B1304535 : Blo 1303970 1304535 := bstep (se 1 (by rfl) ⟨978401, by rfl⟩ : syracuseStep 1304535 = 1956803) B1956803
theorem B9906137 : Blo 1303970 9906137 := bstep (se 2 (by rfl) ⟨3714801, by rfl⟩ : syracuseStep 9906137 = 7429603) B7429603
theorem B1304555 : Blo 1303970 1304555 := bstep (se 1 (by rfl) ⟨978416, by rfl⟩ : syracuseStep 1304555 = 1956833) B1956833
theorem B1304567 : Blo 1303970 1304567 := bstep (se 1 (by rfl) ⟨978425, by rfl⟩ : syracuseStep 1304567 = 1956851) B1956851
theorem B2353153 : Blo 1303970 2353153 := bstep (se 2 (by rfl) ⟨882432, by rfl⟩ : syracuseStep 2353153 = 1764865) B1764865
theorem B1304587 : Blo 1303970 1304587 := bstep (se 1 (by rfl) ⟨978440, by rfl⟩ : syracuseStep 1304587 = 1956881) B1956881
theorem B11151377 : Blo 1303970 11151377 := bstep (se 2 (by rfl) ⟨4181766, by rfl⟩ : syracuseStep 11151377 = 8363533) B8363533
theorem B1304599 : Blo 1303970 1304599 := bstep (se 1 (by rfl) ⟨978449, by rfl⟩ : syracuseStep 1304599 = 1956899) B1956899
theorem B2934809 : Blo 1303970 2934809 := bstep (se 2 (by rfl) ⟨1100553, by rfl⟩ : syracuseStep 2934809 = 2201107) B2201107
theorem B16951331 : Blo 1303970 16951331 := bstep (se 1 (by rfl) ⟨12713498, by rfl⟩ : syracuseStep 16951331 = 25426997) B25426997
theorem B1304619 : Blo 1303970 1304619 := bstep (se 1 (by rfl) ⟨978464, by rfl⟩ : syracuseStep 1304619 = 1956929) B1956929
theorem B1304631 : Blo 1303970 1304631 := bstep (se 1 (by rfl) ⟨978473, by rfl⟩ : syracuseStep 1304631 = 1956947) B1956947
theorem B1468471 : Blo 1303970 1468471 := bstep (se 1 (by rfl) ⟨1101353, by rfl⟩ : syracuseStep 1468471 = 2202707) B2202707
theorem B9406529 : Blo 1303970 9406529 := bstep (se 2 (by rfl) ⟨3527448, by rfl⟩ : syracuseStep 9406529 = 7054897) B7054897
theorem B1304651 : Blo 1303970 1304651 := bstep (se 1 (by rfl) ⟨978488, by rfl⟩ : syracuseStep 1304651 = 1956977) B1956977
theorem B1673303 : Blo 1303970 1673303 := bstep (se 1 (by rfl) ⟨1254977, by rfl⟩ : syracuseStep 1673303 = 2509955) B2509955
theorem B1304663 : Blo 1303970 1304663 := bstep (se 1 (by rfl) ⟨978497, by rfl⟩ : syracuseStep 1304663 = 1956995) B1956995
theorem B6269021 : Blo 1303970 6269021 := bstep (se 3 (by rfl) ⟨1175441, by rfl⟩ : syracuseStep 6269021 = 2350883) B2350883
theorem B1304683 : Blo 1303970 1304683 := bstep (se 1 (by rfl) ⟨978512, by rfl⟩ : syracuseStep 1304683 = 1957025) B1957025
theorem B2934899 : Blo 1303970 2934899 := bstep (se 1 (by rfl) ⟨2201174, by rfl⟩ : syracuseStep 2934899 = 4402349) B4402349
theorem B1304695 : Blo 1303970 1304695 := bstep (se 1 (by rfl) ⟨978521, by rfl⟩ : syracuseStep 1304695 = 1957043) B1957043
theorem B1304715 : Blo 1303970 1304715 := bstep (se 1 (by rfl) ⟨978536, by rfl⟩ : syracuseStep 1304715 = 1957073) B1957073
theorem B2934935 : Blo 1303970 2934935 := bstep (se 1 (by rfl) ⟨2201201, by rfl⟩ : syracuseStep 2934935 = 4402403) B4402403
theorem B1304727 : Blo 1303970 1304727 := bstep (se 1 (by rfl) ⟨978545, by rfl⟩ : syracuseStep 1304727 = 1957091) B1957091
theorem B3303575 : Blo 1303970 3303575 := bstep (se 1 (by rfl) ⟨2477681, by rfl⟩ : syracuseStep 3303575 = 4955363) B4955363
theorem B1304747 : Blo 1303970 1304747 := bstep (se 1 (by rfl) ⟨978560, by rfl⟩ : syracuseStep 1304747 = 1957121) B1957121
theorem B1304759 : Blo 1303970 1304759 := bstep (se 1 (by rfl) ⟨978569, by rfl⟩ : syracuseStep 1304759 = 1957139) B1957139
theorem B1566923 : Blo 1303970 1566923 := bstep (se 1 (by rfl) ⟨1175192, by rfl⟩ : syracuseStep 1566923 = 2350385) B2350385
theorem B1304779 : Blo 1303970 1304779 := bstep (se 1 (by rfl) ⟨978584, by rfl⟩ : syracuseStep 1304779 = 1957169) B1957169
theorem B1304791 : Blo 1303970 1304791 := bstep (se 1 (by rfl) ⟨978593, by rfl⟩ : syracuseStep 1304791 = 1957187) B1957187
theorem B1304811 : Blo 1303970 1304811 := bstep (se 1 (by rfl) ⟨978608, by rfl⟩ : syracuseStep 1304811 = 1957217) B1957217
theorem B1468651 : Blo 1303970 1468651 := bstep (se 1 (by rfl) ⟨1101488, by rfl⟩ : syracuseStep 1468651 = 2202977) B2202977
theorem B2787571 : Blo 1303970 2787571 := bstep (se 1 (by rfl) ⟨2090678, by rfl⟩ : syracuseStep 2787571 = 4181357) B4181357
theorem B1304823 : Blo 1303970 1304823 := bstep (se 1 (by rfl) ⟨978617, by rfl⟩ : syracuseStep 1304823 = 1957235) B1957235
theorem B1304843 : Blo 1303970 1304843 := bstep (se 1 (by rfl) ⟨978632, by rfl⟩ : syracuseStep 1304843 = 1957265) B1957265
theorem B4401431 : Blo 1303970 4401431 := bstep (se 1 (by rfl) ⟨3301073, by rfl⟩ : syracuseStep 4401431 = 6602147) B6602147
theorem B1304855 : Blo 1303970 1304855 := bstep (se 1 (by rfl) ⟨978641, by rfl⟩ : syracuseStep 1304855 = 1957283) B1957283
theorem B2230553 : Blo 1303970 2230553 := bstep (se 2 (by rfl) ⟨836457, by rfl⟩ : syracuseStep 2230553 = 1672915) B1672915
theorem B1304875 : Blo 1303970 1304875 := bstep (se 1 (by rfl) ⟨978656, by rfl⟩ : syracuseStep 1304875 = 1957313) B1957313
theorem B1304887 : Blo 1303970 1304887 := bstep (se 1 (by rfl) ⟨978665, by rfl⟩ : syracuseStep 1304887 = 1957331) B1957331
theorem B2935115 : Blo 1303970 2935115 := bstep (se 1 (by rfl) ⟨2201336, by rfl⟩ : syracuseStep 2935115 = 4402673) B4402673
theorem B1304907 : Blo 1303970 1304907 := bstep (se 1 (by rfl) ⟨978680, by rfl⟩ : syracuseStep 1304907 = 1957361) B1957361
theorem B1567063 : Blo 1303970 1567063 := bstep (se 1 (by rfl) ⟨1175297, by rfl⟩ : syracuseStep 1567063 = 2350595) B2350595
theorem B1304919 : Blo 1303970 1304919 := bstep (se 1 (by rfl) ⟨978689, by rfl⟩ : syracuseStep 1304919 = 1957379) B1957379
theorem B3967321 : Blo 1303970 3967321 := bstep (se 2 (by rfl) ⟨1487745, by rfl⟩ : syracuseStep 3967321 = 2975491) B2975491
theorem B1468759 : Blo 1303970 1468759 := bstep (se 1 (by rfl) ⟨1101569, by rfl⟩ : syracuseStep 1468759 = 2203139) B2203139
theorem B1304939 : Blo 1303970 1304939 := bstep (se 1 (by rfl) ⟨978704, by rfl⟩ : syracuseStep 1304939 = 1957409) B1957409
theorem B1304951 : Blo 1303970 1304951 := bstep (se 1 (by rfl) ⟨978713, by rfl⟩ : syracuseStep 1304951 = 1957427) B1957427
theorem B2935169 : Blo 1303970 2935169 := bstep (se 2 (by rfl) ⟨1100688, by rfl⟩ : syracuseStep 2935169 = 2201377) B2201377
theorem B1304971 : Blo 1303970 1304971 := bstep (se 1 (by rfl) ⟨978728, by rfl⟩ : syracuseStep 1304971 = 1957457) B1957457
theorem B1304983 : Blo 1303970 1304983 := bstep (se 1 (by rfl) ⟨978737, by rfl⟩ : syracuseStep 1304983 = 1957475) B1957475
theorem B1305003 : Blo 1303970 1305003 := bstep (se 1 (by rfl) ⟨978752, by rfl⟩ : syracuseStep 1305003 = 1957505) B1957505
theorem B1305015 : Blo 1303970 1305015 := bstep (se 1 (by rfl) ⟨978761, by rfl⟩ : syracuseStep 1305015 = 1957523) B1957523
theorem B1305035 : Blo 1303970 1305035 := bstep (se 1 (by rfl) ⟨978776, by rfl⟩ : syracuseStep 1305035 = 1957553) B1957553
theorem B2091467 : Blo 1303970 2091467 := bstep (se 1 (by rfl) ⟨1568600, by rfl⟩ : syracuseStep 2091467 = 3137201) B3137201
theorem B1305047 : Blo 1303970 1305047 := bstep (se 1 (by rfl) ⟨978785, by rfl⟩ : syracuseStep 1305047 = 1957571) B1957571
theorem B1305067 : Blo 1303970 1305067 := bstep (se 1 (by rfl) ⟨978800, by rfl⟩ : syracuseStep 1305067 = 1957601) B1957601
theorem B1305079 : Blo 1303970 1305079 := bstep (se 1 (by rfl) ⟨978809, by rfl⟩ : syracuseStep 1305079 = 1957619) B1957619
theorem B9914885 : Blo 1303970 9914885 := bstep (se 4 (by rfl) ⟨929520, by rfl⟩ : syracuseStep 9914885 = 1859041) B1859041
theorem B1305099 : Blo 1303970 1305099 := bstep (se 1 (by rfl) ⟨978824, by rfl⟩ : syracuseStep 1305099 = 1957649) B1957649
theorem B1468939 : Blo 1303970 1468939 := bstep (se 1 (by rfl) ⟨1101704, by rfl⟩ : syracuseStep 1468939 = 2203409) B2203409
theorem B1305111 : Blo 1303970 1305111 := bstep (se 1 (by rfl) ⟨978833, by rfl⟩ : syracuseStep 1305111 = 1957667) B1957667
theorem B1305131 : Blo 1303970 1305131 := bstep (se 1 (by rfl) ⟨978848, by rfl⟩ : syracuseStep 1305131 = 1957697) B1957697
theorem B2476595 : Blo 1303970 2476595 := bstep (se 1 (by rfl) ⟨1857446, by rfl⟩ : syracuseStep 2476595 = 3714893) B3714893
theorem B1305143 : Blo 1303970 1305143 := bstep (se 1 (by rfl) ⟨978857, by rfl⟩ : syracuseStep 1305143 = 1957715) B1957715
theorem B5573195 : Blo 1303970 5573195 := bstep (se 1 (by rfl) ⟨4179896, by rfl⟩ : syracuseStep 5573195 = 8359793) B8359793
theorem B6605387 : Blo 1303970 6605387 := bstep (se 1 (by rfl) ⟨4954040, by rfl⟩ : syracuseStep 6605387 = 9908081) B9908081
theorem B1305163 : Blo 1303970 1305163 := bstep (se 1 (by rfl) ⟨978872, by rfl⟩ : syracuseStep 1305163 = 1957745) B1957745
theorem B1305175 : Blo 1303970 1305175 := bstep (se 1 (by rfl) ⟨978881, by rfl⟩ : syracuseStep 1305175 = 1957763) B1957763
theorem B2935385 : Blo 1303970 2935385 := bstep (se 2 (by rfl) ⟨1100769, by rfl⟩ : syracuseStep 2935385 = 2201539) B2201539
theorem B1305195 : Blo 1303970 1305195 := bstep (se 1 (by rfl) ⟨978896, by rfl⟩ : syracuseStep 1305195 = 1957793) B1957793
theorem B1305207 : Blo 1303970 1305207 := bstep (se 1 (by rfl) ⟨978905, by rfl⟩ : syracuseStep 1305207 = 1957811) B1957811
theorem B1469047 : Blo 1303970 1469047 := bstep (se 1 (by rfl) ⟨1101785, by rfl⟩ : syracuseStep 1469047 = 2203571) B2203571
theorem B1305227 : Blo 1303970 1305227 := bstep (se 1 (by rfl) ⟨978920, by rfl⟩ : syracuseStep 1305227 = 1957841) B1957841
theorem B1305239 : Blo 1303970 1305239 := bstep (se 1 (by rfl) ⟨978929, by rfl⟩ : syracuseStep 1305239 = 1957859) B1957859
theorem B1305259 : Blo 1303970 1305259 := bstep (se 1 (by rfl) ⟨978944, by rfl⟩ : syracuseStep 1305259 = 1957889) B1957889
theorem B2935475 : Blo 1303970 2935475 := bstep (se 1 (by rfl) ⟨2201606, by rfl⟩ : syracuseStep 2935475 = 4403213) B4403213
theorem B1305271 : Blo 1303970 1305271 := bstep (se 1 (by rfl) ⟨978953, by rfl⟩ : syracuseStep 1305271 = 1957907) B1957907
theorem B2788033 : Blo 1303970 2788033 := bstep (se 2 (by rfl) ⟨1045512, by rfl⟩ : syracuseStep 2788033 = 2091025) B2091025
theorem B2476747 : Blo 1303970 2476747 := bstep (se 1 (by rfl) ⟨1857560, by rfl⟩ : syracuseStep 2476747 = 3715121) B3715121
theorem B1305291 : Blo 1303970 1305291 := bstep (se 1 (by rfl) ⟨978968, by rfl⟩ : syracuseStep 1305291 = 1957937) B1957937
theorem B2935511 : Blo 1303970 2935511 := bstep (se 1 (by rfl) ⟨2201633, by rfl⟩ : syracuseStep 2935511 = 4403267) B4403267
theorem B1305303 : Blo 1303970 1305303 := bstep (se 1 (by rfl) ⟨978977, by rfl⟩ : syracuseStep 1305303 = 1957955) B1957955
theorem B4238041 : Blo 1303970 4238041 := bstep (se 2 (by rfl) ⟨1589265, by rfl⟩ : syracuseStep 4238041 = 3178531) B3178531
theorem B1305323 : Blo 1303970 1305323 := bstep (se 1 (by rfl) ⟨978992, by rfl⟩ : syracuseStep 1305323 = 1957985) B1957985
theorem B1305335 : Blo 1303970 1305335 := bstep (se 1 (by rfl) ⟨979001, by rfl⟩ : syracuseStep 1305335 = 1958003) B1958003
theorem B1305355 : Blo 1303970 1305355 := bstep (se 1 (by rfl) ⟨979016, by rfl⟩ : syracuseStep 1305355 = 1958033) B1958033
theorem B1305367 : Blo 1303970 1305367 := bstep (se 1 (by rfl) ⟨979025, by rfl⟩ : syracuseStep 1305367 = 1958051) B1958051
theorem B1305387 : Blo 1303970 1305387 := bstep (se 1 (by rfl) ⟨979040, by rfl⟩ : syracuseStep 1305387 = 1958081) B1958081
theorem B4401971 : Blo 1303970 4401971 := bstep (se 1 (by rfl) ⟨3301478, by rfl⟩ : syracuseStep 4401971 = 6602957) B6602957
theorem B1305399 : Blo 1303970 1305399 := bstep (se 1 (by rfl) ⟨979049, by rfl⟩ : syracuseStep 1305399 = 1958099) B1958099
theorem B1305419 : Blo 1303970 1305419 := bstep (se 1 (by rfl) ⟨979064, by rfl⟩ : syracuseStep 1305419 = 1958129) B1958129
theorem B1305431 : Blo 1303970 1305431 := bstep (se 1 (by rfl) ⟨979073, by rfl⟩ : syracuseStep 1305431 = 1958147) B1958147
theorem B1305451 : Blo 1303970 1305451 := bstep (se 1 (by rfl) ⟨979088, by rfl⟩ : syracuseStep 1305451 = 1958177) B1958177
theorem B1305463 : Blo 1303970 1305463 := bstep (se 1 (by rfl) ⟨979097, by rfl⟩ : syracuseStep 1305463 = 1958195) B1958195
theorem B2935691 : Blo 1303970 2935691 := bstep (se 1 (by rfl) ⟨2201768, by rfl⟩ : syracuseStep 2935691 = 4403537) B4403537
theorem B1305483 : Blo 1303970 1305483 := bstep (se 1 (by rfl) ⟨979112, by rfl⟩ : syracuseStep 1305483 = 1958225) B1958225
theorem B1305495 : Blo 1303970 1305495 := bstep (se 1 (by rfl) ⟨979121, by rfl⟩ : syracuseStep 1305495 = 1958243) B1958243
theorem B1305515 : Blo 1303970 1305515 := bstep (se 1 (by rfl) ⟨979136, by rfl⟩ : syracuseStep 1305515 = 1958273) B1958273
theorem B3713971 : Blo 1303970 3713971 := bstep (se 1 (by rfl) ⟨2785478, by rfl⟩ : syracuseStep 3713971 = 5570957) B5570957
theorem B5573555 : Blo 1303970 5573555 := bstep (se 1 (by rfl) ⟨4180166, by rfl⟩ : syracuseStep 5573555 = 8360333) B8360333
theorem B1305527 : Blo 1303970 1305527 := bstep (se 1 (by rfl) ⟨979145, by rfl⟩ : syracuseStep 1305527 = 1958291) B1958291
theorem B2935745 : Blo 1303970 2935745 := bstep (se 2 (by rfl) ⟨1100904, by rfl⟩ : syracuseStep 2935745 = 2201809) B2201809
theorem B3304385 : Blo 1303970 3304385 := bstep (se 2 (by rfl) ⟨1239144, by rfl⟩ : syracuseStep 3304385 = 2478289) B2478289
theorem B1305547 : Blo 1303970 1305547 := bstep (se 1 (by rfl) ⟨979160, by rfl⟩ : syracuseStep 1305547 = 1958321) B1958321
theorem B1305559 : Blo 1303970 1305559 := bstep (se 1 (by rfl) ⟨979169, by rfl⟩ : syracuseStep 1305559 = 1958339) B1958339
theorem B1305579 : Blo 1303970 1305579 := bstep (se 1 (by rfl) ⟨979184, by rfl⟩ : syracuseStep 1305579 = 1958369) B1958369
theorem B1305591 : Blo 1303970 1305591 := bstep (se 1 (by rfl) ⟨979193, by rfl⟩ : syracuseStep 1305591 = 1958387) B1958387
theorem B1305611 : Blo 1303970 1305611 := bstep (se 1 (by rfl) ⟨979208, by rfl⟩ : syracuseStep 1305611 = 1958417) B1958417
theorem B1305623 : Blo 1303970 1305623 := bstep (se 1 (by rfl) ⟨979217, by rfl⟩ : syracuseStep 1305623 = 1958435) B1958435
theorem B4770839 : Blo 1303970 4770839 := bstep (se 1 (by rfl) ⟨3578129, by rfl⟩ : syracuseStep 4770839 = 7156259) B7156259
theorem B2477081 : Blo 1303970 2477081 := bstep (se 2 (by rfl) ⟨928905, by rfl⟩ : syracuseStep 2477081 = 1857811) B1857811
theorem B1305643 : Blo 1303970 1305643 := bstep (se 1 (by rfl) ⟨979232, by rfl⟩ : syracuseStep 1305643 = 1958465) B1958465
theorem B1305655 : Blo 1303970 1305655 := bstep (se 1 (by rfl) ⟨979241, by rfl⟩ : syracuseStep 1305655 = 1958483) B1958483
theorem B4402241 : Blo 1303970 4402241 := bstep (se 2 (by rfl) ⟨1650840, by rfl⟩ : syracuseStep 4402241 = 3301681) B3301681
theorem B1305675 : Blo 1303970 1305675 := bstep (se 1 (by rfl) ⟨979256, by rfl⟩ : syracuseStep 1305675 = 1958513) B1958513
theorem B1305687 : Blo 1303970 1305687 := bstep (se 1 (by rfl) ⟨979265, by rfl⟩ : syracuseStep 1305687 = 1958531) B1958531
theorem B1789015 : Blo 1303970 1789015 := bstep (se 1 (by rfl) ⟨1341761, by rfl⟩ : syracuseStep 1789015 = 2683523) B2683523
theorem B1305707 : Blo 1303970 1305707 := bstep (se 1 (by rfl) ⟨979280, by rfl⟩ : syracuseStep 1305707 = 1958561) B1958561
theorem B1305719 : Blo 1303970 1305719 := bstep (se 1 (by rfl) ⟨979289, by rfl⟩ : syracuseStep 1305719 = 1958579) B1958579
theorem B4705411 : Blo 1303970 4705411 := bstep (se 1 (by rfl) ⟨3529058, by rfl⟩ : syracuseStep 4705411 = 7058117) B7058117
theorem B1305739 : Blo 1303970 1305739 := bstep (se 1 (by rfl) ⟨979304, by rfl⟩ : syracuseStep 1305739 = 1958609) B1958609
theorem B1305751 : Blo 1303970 1305751 := bstep (se 1 (by rfl) ⟨979313, by rfl⟩ : syracuseStep 1305751 = 1958627) B1958627
theorem B2935961 : Blo 1303970 2935961 := bstep (se 2 (by rfl) ⟨1100985, by rfl⟩ : syracuseStep 2935961 = 2201971) B2201971
theorem B1305771 : Blo 1303970 1305771 := bstep (se 1 (by rfl) ⟨979328, by rfl⟩ : syracuseStep 1305771 = 1958657) B1958657
theorem B1305783 : Blo 1303970 1305783 := bstep (se 1 (by rfl) ⟨979337, by rfl⟩ : syracuseStep 1305783 = 1958675) B1958675
theorem B1305803 : Blo 1303970 1305803 := bstep (se 1 (by rfl) ⟨979352, by rfl⟩ : syracuseStep 1305803 = 1958705) B1958705
theorem B1305815 : Blo 1303970 1305815 := bstep (se 1 (by rfl) ⟨979361, by rfl⟩ : syracuseStep 1305815 = 1958723) B1958723
theorem B1305835 : Blo 1303970 1305835 := bstep (se 1 (by rfl) ⟨979376, by rfl⟩ : syracuseStep 1305835 = 1958753) B1958753
theorem B2936051 : Blo 1303970 2936051 := bstep (se 1 (by rfl) ⟨2202038, by rfl⟩ : syracuseStep 2936051 = 4404077) B4404077
theorem B1305847 : Blo 1303970 1305847 := bstep (se 1 (by rfl) ⟨979385, by rfl⟩ : syracuseStep 1305847 = 1958771) B1958771
theorem B1305867 : Blo 1303970 1305867 := bstep (se 1 (by rfl) ⟨979400, by rfl⟩ : syracuseStep 1305867 = 1958801) B1958801
theorem B2936087 : Blo 1303970 2936087 := bstep (se 1 (by rfl) ⟨2202065, by rfl⟩ : syracuseStep 2936087 = 4404131) B4404131
theorem B1305879 : Blo 1303970 1305879 := bstep (se 1 (by rfl) ⟨979409, by rfl⟩ : syracuseStep 1305879 = 1958819) B1958819
theorem B10038563 : Blo 1303970 10038563 := bstep (se 1 (by rfl) ⟨7528922, by rfl⟩ : syracuseStep 10038563 = 15057845) B15057845
theorem B1305899 : Blo 1303970 1305899 := bstep (se 1 (by rfl) ⟨979424, by rfl⟩ : syracuseStep 1305899 = 1958849) B1958849
theorem B22605101 : Blo 1303970 22605101 := bstep (se 3 (by rfl) ⟨4238456, by rfl⟩ : syracuseStep 22605101 = 8476913) B8476913
theorem B1305911 : Blo 1303970 1305911 := bstep (se 1 (by rfl) ⟨979433, by rfl⟩ : syracuseStep 1305911 = 1958867) B1958867
theorem B1305931 : Blo 1303970 1305931 := bstep (se 1 (by rfl) ⟨979448, by rfl⟩ : syracuseStep 1305931 = 1958897) B1958897
theorem B1305943 : Blo 1303970 1305943 := bstep (se 1 (by rfl) ⟨979457, by rfl⟩ : syracuseStep 1305943 = 1958915) B1958915
theorem B1305963 : Blo 1303970 1305963 := bstep (se 1 (by rfl) ⟨979472, by rfl⟩ : syracuseStep 1305963 = 1958945) B1958945
theorem B2788759 : Blo 1303970 2788759 := bstep (se 1 (by rfl) ⟨2091569, by rfl⟩ : syracuseStep 2788759 = 4183139) B4183139
theorem B4951475 : Blo 1303970 4951475 := bstep (se 1 (by rfl) ⟨3713606, by rfl⟩ : syracuseStep 4951475 = 7427213) B7427213
theorem B4951489 : Blo 1303970 4951489 := bstep (se 2 (by rfl) ⟨1856808, by rfl⟩ : syracuseStep 4951489 = 3713617) B3713617
theorem B2936267 : Blo 1303970 2936267 := bstep (se 1 (by rfl) ⟨2202200, by rfl⟩ : syracuseStep 2936267 = 4404401) B4404401
theorem B3304921 : Blo 1303970 3304921 := bstep (se 2 (by rfl) ⟨1239345, by rfl⟩ : syracuseStep 3304921 = 2478691) B2478691
theorem B2936321 : Blo 1303970 2936321 := bstep (se 2 (by rfl) ⟨1101120, by rfl⟩ : syracuseStep 2936321 = 2202241) B2202241
theorem B7056971 : Blo 1303970 7056971 := bstep (se 1 (by rfl) ⟨5292728, by rfl⟩ : syracuseStep 7056971 = 10585457) B10585457
theorem B4402781 : Blo 1303970 4402781 := bstep (se 3 (by rfl) ⟨825521, by rfl⟩ : syracuseStep 4402781 = 1651043) B1651043
theorem B2477719 : Blo 1303970 2477719 := bstep (se 1 (by rfl) ⟨1858289, by rfl⟩ : syracuseStep 2477719 = 3716579) B3716579
theorem B2936537 : Blo 1303970 2936537 := bstep (se 2 (by rfl) ⟨1101201, by rfl⟩ : syracuseStep 2936537 = 2202403) B2202403
theorem B22294277 : Blo 1303970 22294277 := bstep (se 4 (by rfl) ⟨2090088, by rfl⟩ : syracuseStep 22294277 = 4180177) B4180177
theorem B2936627 : Blo 1303970 2936627 := bstep (se 1 (by rfl) ⟨2202470, by rfl⟩ : syracuseStep 2936627 = 4404941) B4404941
theorem B21163841 : Blo 1303970 21163841 := bstep (se 2 (by rfl) ⟨7936440, by rfl⟩ : syracuseStep 21163841 = 15872881) B15872881
theorem B2936663 : Blo 1303970 2936663 := bstep (se 1 (by rfl) ⟨2202497, by rfl⟩ : syracuseStep 2936663 = 4404995) B4404995
theorem B2936843 : Blo 1303970 2936843 := bstep (se 1 (by rfl) ⟨2202632, by rfl⟩ : syracuseStep 2936843 = 4405265) B4405265
theorem B3526679 : Blo 1303970 3526679 := bstep (se 1 (by rfl) ⟨2645009, by rfl⟩ : syracuseStep 3526679 = 5290019) B5290019
theorem B2936897 : Blo 1303970 2936897 := bstep (se 2 (by rfl) ⟨1101336, by rfl⟩ : syracuseStep 2936897 = 2202673) B2202673
theorem B1650775 : Blo 1303970 1650775 := bstep (se 1 (by rfl) ⟨1238081, by rfl⟩ : syracuseStep 1650775 = 2476163) B2476163
theorem B1568855 : Blo 1303970 1568855 := bstep (se 1 (by rfl) ⟨1176641, by rfl⟩ : syracuseStep 1568855 = 2353283) B2353283
theorem B25071767 : Blo 1303970 25071767 := bstep (se 1 (by rfl) ⟨18803825, by rfl⟩ : syracuseStep 25071767 = 37607651) B37607651
theorem B2937113 : Blo 1303970 2937113 := bstep (se 2 (by rfl) ⟨1101417, by rfl⟩ : syracuseStep 2937113 = 2202835) B2202835
theorem B6607169 : Blo 1303970 6607169 := bstep (se 2 (by rfl) ⟨2477688, by rfl⟩ : syracuseStep 6607169 = 4955377) B4955377
theorem B2937203 : Blo 1303970 2937203 := bstep (se 1 (by rfl) ⟨2202902, by rfl⟩ : syracuseStep 2937203 = 4405805) B4405805
theorem B9408919 : Blo 1303970 9408919 := bstep (se 1 (by rfl) ⟨7056689, by rfl⟩ : syracuseStep 9408919 = 14113379) B14113379
theorem B2937239 : Blo 1303970 2937239 := bstep (se 1 (by rfl) ⟨2202929, by rfl⟩ : syracuseStep 2937239 = 4405859) B4405859
theorem B2478539 : Blo 1303970 2478539 := bstep (se 1 (by rfl) ⟨1858904, by rfl⟩ : syracuseStep 2478539 = 3717809) B3717809
theorem B2478593 : Blo 1303970 2478593 := bstep (se 2 (by rfl) ⟨929472, by rfl⟩ : syracuseStep 2478593 = 1858945) B1858945
theorem B2511371 : Blo 1303970 2511371 := bstep (se 1 (by rfl) ⟨1883528, by rfl⟩ : syracuseStep 2511371 = 3767057) B3767057
theorem B1323575 : Blo 1303970 1323575 := bstep (se 1 (by rfl) ⟨992681, by rfl⟩ : syracuseStep 1323575 = 1985363) B1985363
theorem B2937419 : Blo 1303970 2937419 := bstep (se 1 (by rfl) ⟨2203064, by rfl⟩ : syracuseStep 2937419 = 4406129) B4406129
theorem B2937473 : Blo 1303970 2937473 := bstep (se 2 (by rfl) ⟨1101552, by rfl⟩ : syracuseStep 2937473 = 2203105) B2203105
theorem B4403915 : Blo 1303970 4403915 := bstep (se 1 (by rfl) ⟨3302936, by rfl⟩ : syracuseStep 4403915 = 6605873) B6605873
theorem B2937689 : Blo 1303970 2937689 := bstep (se 2 (by rfl) ⟨1101633, by rfl⟩ : syracuseStep 2937689 = 2203267) B2203267
theorem B7934813 : Blo 1303970 7934813 := bstep (se 3 (by rfl) ⟨1487777, by rfl⟩ : syracuseStep 7934813 = 2975555) B2975555
theorem B32158565 : Blo 1303970 32158565 := bstep (se 4 (by rfl) ⟨3014865, by rfl⟩ : syracuseStep 32158565 = 6029731) B6029731
theorem B2200459 : Blo 1303970 2200459 := bstep (se 1 (by rfl) ⟨1650344, by rfl⟩ : syracuseStep 2200459 = 3300689) B3300689
theorem B3765143 : Blo 1303970 3765143 := bstep (se 1 (by rfl) ⟨2823857, by rfl⟩ : syracuseStep 3765143 = 5647715) B5647715
theorem B2937779 : Blo 1303970 2937779 := bstep (se 1 (by rfl) ⟨2203334, by rfl⟩ : syracuseStep 2937779 = 4406669) B4406669
theorem B2937815 : Blo 1303970 2937815 := bstep (se 1 (by rfl) ⟨2203361, by rfl⟩ : syracuseStep 2937815 = 4406723) B4406723
theorem B4404185 : Blo 1303970 4404185 := bstep (se 2 (by rfl) ⟨1651569, by rfl⟩ : syracuseStep 4404185 = 3303139) B3303139
theorem B9409553 : Blo 1303970 9409553 := bstep (se 2 (by rfl) ⟨3528582, by rfl⟩ : syracuseStep 9409553 = 7057165) B7057165
theorem B2200601 : Blo 1303970 2200601 := bstep (se 2 (by rfl) ⟨825225, by rfl⟩ : syracuseStep 2200601 = 1650451) B1650451
theorem B5018675 : Blo 1303970 5018675 := bstep (se 1 (by rfl) ⟨3764006, by rfl⟩ : syracuseStep 5018675 = 7528013) B7528013
theorem B10327105 : Blo 1303970 10327105 := bstep (se 2 (by rfl) ⟨3872664, by rfl⟩ : syracuseStep 10327105 = 7745329) B7745329
theorem B10589249 : Blo 1303970 10589249 := bstep (se 2 (by rfl) ⟨3970968, by rfl⟩ : syracuseStep 10589249 = 7941937) B7941937
theorem B3347531 : Blo 1303970 3347531 := bstep (se 1 (by rfl) ⟨2510648, by rfl⟩ : syracuseStep 3347531 = 5021297) B5021297
theorem B2937995 : Blo 1303970 2937995 := bstep (se 1 (by rfl) ⟨2203496, by rfl⟩ : syracuseStep 2937995 = 4406993) B4406993
theorem B2200729 : Blo 1303970 2200729 := bstep (se 2 (by rfl) ⟨825273, by rfl⟩ : syracuseStep 2200729 = 1650547) B1650547
theorem B2938049 : Blo 1303970 2938049 := bstep (se 2 (by rfl) ⟨1101768, by rfl⟩ : syracuseStep 2938049 = 2203537) B2203537
theorem B1856729 : Blo 1303970 1856729 := bstep (se 2 (by rfl) ⟨696273, by rfl⟩ : syracuseStep 1856729 = 1392547) B1392547
theorem B9909539 : Blo 1303970 9909539 := bstep (se 1 (by rfl) ⟨7432154, by rfl⟩ : syracuseStep 9909539 = 14864309) B14864309
theorem B12719425 : Blo 1303970 12719425 := bstep (se 2 (by rfl) ⟨4769784, by rfl⟩ : syracuseStep 12719425 = 9539569) B9539569
theorem B4953419 : Blo 1303970 4953419 := bstep (se 1 (by rfl) ⟨3715064, by rfl⟩ : syracuseStep 4953419 = 7430129) B7430129
theorem B4953433 : Blo 1303970 4953433 := bstep (se 2 (by rfl) ⟨1857537, by rfl⟩ : syracuseStep 4953433 = 3715075) B3715075
theorem B28202357 : Blo 1303970 28202357 := bstep (se 5 (by rfl) ⟨1321985, by rfl⟩ : syracuseStep 28202357 = 2643971) B2643971
theorem B4183447 : Blo 1303970 4183447 := bstep (se 1 (by rfl) ⟨3137585, by rfl⟩ : syracuseStep 4183447 = 6275171) B6275171
theorem B2938265 : Blo 1303970 2938265 := bstep (se 2 (by rfl) ⟨1101849, by rfl⟩ : syracuseStep 2938265 = 2203699) B2203699
theorem B2938355 : Blo 1303970 2938355 := bstep (se 1 (by rfl) ⟨2203766, by rfl⟩ : syracuseStep 2938355 = 4407533) B4407533
theorem B2938391 : Blo 1303970 2938391 := bstep (se 1 (by rfl) ⟨2203793, by rfl⟩ : syracuseStep 2938391 = 4407587) B4407587
theorem B23828003 : Blo 1303970 23828003 := bstep (se 1 (by rfl) ⟨17871002, by rfl⟩ : syracuseStep 23828003 = 35742005) B35742005
theorem B3528281 : Blo 1303970 3528281 := bstep (se 2 (by rfl) ⟨1323105, by rfl⟩ : syracuseStep 3528281 = 2646211) B2646211
theorem B4404887 : Blo 1303970 4404887 := bstep (se 1 (by rfl) ⟨3303665, by rfl⟩ : syracuseStep 4404887 = 6607331) B6607331
theorem B2201303 : Blo 1303970 2201303 := bstep (se 1 (by rfl) ⟨1650977, by rfl⟩ : syracuseStep 2201303 = 3301955) B3301955
theorem B3528409 : Blo 1303970 3528409 := bstep (se 2 (by rfl) ⟨1323153, by rfl⟩ : syracuseStep 3528409 = 2646307) B2646307
theorem B1652491 : Blo 1303970 1652491 := bstep (se 1 (by rfl) ⟨1239368, by rfl⟩ : syracuseStep 1652491 = 2478737) B2478737
theorem B7051025 : Blo 1303970 7051025 := bstep (se 2 (by rfl) ⟨2644134, by rfl⟩ : syracuseStep 7051025 = 5288269) B5288269
theorem B3716887 : Blo 1303970 3716887 := bstep (se 1 (by rfl) ⟨2787665, by rfl⟩ : syracuseStep 3716887 = 5575331) B5575331
theorem B1857367 : Blo 1303970 1857367 := bstep (se 1 (by rfl) ⟨1393025, by rfl⟩ : syracuseStep 1857367 = 2786051) B2786051
theorem B2201431 : Blo 1303970 2201431 := bstep (se 1 (by rfl) ⟨1651073, by rfl⟩ : syracuseStep 2201431 = 3302147) B3302147
theorem B60225605 : Blo 1303970 60225605 := bstep (se 4 (by rfl) ⟨5646150, by rfl⟩ : syracuseStep 60225605 = 11292301) B11292301
theorem B1955993 : Blo 1303970 1955993 := bstep (se 2 (by rfl) ⟨733497, by rfl⟩ : syracuseStep 1955993 = 1466995) B1466995
theorem B4405427 : Blo 1303970 4405427 := bstep (se 1 (by rfl) ⟨3304070, by rfl⟩ : syracuseStep 4405427 = 6608141) B6608141
theorem B2291915 : Blo 1303970 2291915 := bstep (se 1 (by rfl) ⟨1718936, by rfl⟩ : syracuseStep 2291915 = 3437873) B3437873
theorem B18823373 : Blo 1303970 18823373 := bstep (se 3 (by rfl) ⟨3529382, by rfl⟩ : syracuseStep 18823373 = 7058765) B7058765
theorem B6609113 : Blo 1303970 6609113 := bstep (se 2 (by rfl) ⟨2478417, by rfl⟩ : syracuseStep 6609113 = 4956835) B4956835
theorem B1956107 : Blo 1303970 1956107 := bstep (se 1 (by rfl) ⟨1467080, by rfl⟩ : syracuseStep 1956107 = 2934161) B2934161
theorem B1956119 : Blo 1303970 1956119 := bstep (se 1 (by rfl) ⟨1467089, by rfl⟩ : syracuseStep 1956119 = 2934179) B2934179
theorem B4954391 : Blo 1303970 4954391 := bstep (se 1 (by rfl) ⟨3715793, by rfl⟩ : syracuseStep 4954391 = 7431587) B7431587
theorem B1956185 : Blo 1303970 1956185 := bstep (se 2 (by rfl) ⟨733569, by rfl⟩ : syracuseStep 1956185 = 1467139) B1467139
theorem B4405697 : Blo 1303970 4405697 := bstep (se 2 (by rfl) ⟨1652136, by rfl⟩ : syracuseStep 4405697 = 3304273) B3304273
theorem B1956299 : Blo 1303970 1956299 := bstep (se 1 (by rfl) ⟨1467224, by rfl⟩ : syracuseStep 1956299 = 2934449) B2934449
theorem B2202059 : Blo 1303970 2202059 := bstep (se 1 (by rfl) ⟨1651544, by rfl⟩ : syracuseStep 2202059 = 3303089) B3303089
theorem B6035915 : Blo 1303970 6035915 := bstep (se 1 (by rfl) ⟨4526936, by rfl⟩ : syracuseStep 6035915 = 9053873) B9053873
theorem B1956311 : Blo 1303970 1956311 := bstep (se 1 (by rfl) ⟨1467233, by rfl⟩ : syracuseStep 1956311 = 2934467) B2934467
theorem B1956377 : Blo 1303970 1956377 := bstep (se 2 (by rfl) ⟨733641, by rfl⟩ : syracuseStep 1956377 = 1467283) B1467283
theorem B18823715 : Blo 1303970 18823715 := bstep (se 1 (by rfl) ⟨14117786, by rfl⟩ : syracuseStep 18823715 = 28235573) B28235573
theorem B2202187 : Blo 1303970 2202187 := bstep (se 1 (by rfl) ⟨1651640, by rfl⟩ : syracuseStep 2202187 = 3303281) B3303281
theorem B2415193 : Blo 1303970 2415193 := bstep (se 2 (by rfl) ⟨905697, by rfl⟩ : syracuseStep 2415193 = 1811395) B1811395
theorem B7436893 : Blo 1303970 7436893 := bstep (se 3 (by rfl) ⟨1394417, by rfl⟩ : syracuseStep 7436893 = 2788835) B2788835
theorem B1956491 : Blo 1303970 1956491 := bstep (se 1 (by rfl) ⟨1467368, by rfl⟩ : syracuseStep 1956491 = 2934737) B2934737
theorem B1858187 : Blo 1303970 1858187 := bstep (se 1 (by rfl) ⟨1393640, by rfl⟩ : syracuseStep 1858187 = 2787281) B2787281
theorem B1956503 : Blo 1303970 1956503 := bstep (se 1 (by rfl) ⟨1467377, by rfl⟩ : syracuseStep 1956503 = 2934755) B2934755
theorem B1956569 : Blo 1303970 1956569 := bstep (se 2 (by rfl) ⟨733713, by rfl⟩ : syracuseStep 1956569 = 1467427) B1467427
theorem B2202329 : Blo 1303970 2202329 := bstep (se 2 (by rfl) ⟨825873, by rfl⟩ : syracuseStep 2202329 = 1651747) B1651747
theorem B14113601 : Blo 1303970 14113601 := bstep (se 2 (by rfl) ⟨5292600, by rfl⟩ : syracuseStep 14113601 = 10585201) B10585201
theorem B1956683 : Blo 1303970 1956683 := bstep (se 1 (by rfl) ⟨1467512, by rfl⟩ : syracuseStep 1956683 = 2935025) B2935025
theorem B1956695 : Blo 1303970 1956695 := bstep (se 1 (by rfl) ⟨1467521, by rfl⟩ : syracuseStep 1956695 = 2935043) B2935043
theorem B2202457 : Blo 1303970 2202457 := bstep (se 2 (by rfl) ⟨825921, by rfl⟩ : syracuseStep 2202457 = 1651843) B1651843
theorem B1956761 : Blo 1303970 1956761 := bstep (se 2 (by rfl) ⟨733785, by rfl⟩ : syracuseStep 1956761 = 1467571) B1467571
theorem B4406237 : Blo 1303970 4406237 := bstep (se 3 (by rfl) ⟨826169, by rfl⟩ : syracuseStep 4406237 = 1652339) B1652339
theorem B1956875 : Blo 1303970 1956875 := bstep (se 1 (by rfl) ⟨1467656, by rfl⟩ : syracuseStep 1956875 = 2935313) B2935313
theorem B1956887 : Blo 1303970 1956887 := bstep (se 1 (by rfl) ⟨1467665, by rfl⟩ : syracuseStep 1956887 = 2935331) B2935331
theorem B6274093 : Blo 1303970 6274093 := bstep (se 3 (by rfl) ⟨1176392, by rfl⟩ : syracuseStep 6274093 = 2352785) B2352785
theorem B3529793 : Blo 1303970 3529793 := bstep (se 2 (by rfl) ⟨1323672, by rfl⟩ : syracuseStep 3529793 = 2647345) B2647345
theorem B3718219 : Blo 1303970 3718219 := bstep (se 1 (by rfl) ⟨2788664, by rfl⟩ : syracuseStep 3718219 = 5577329) B5577329
theorem B1956953 : Blo 1303970 1956953 := bstep (se 2 (by rfl) ⟨733857, by rfl⟩ : syracuseStep 1956953 = 1467715) B1467715
theorem B1957067 : Blo 1303970 1957067 := bstep (se 1 (by rfl) ⟨1467800, by rfl⟩ : syracuseStep 1957067 = 2935601) B2935601
theorem B1957079 : Blo 1303970 1957079 := bstep (se 1 (by rfl) ⟨1467809, by rfl⟩ : syracuseStep 1957079 = 2935619) B2935619
theorem B8363225 : Blo 1303970 8363225 := bstep (se 2 (by rfl) ⟨3136209, by rfl⟩ : syracuseStep 8363225 = 6272419) B6272419
theorem B4463837 : Blo 1303970 4463837 := bstep (se 3 (by rfl) ⟨836969, by rfl⟩ : syracuseStep 4463837 = 1673939) B1673939
theorem B1957145 : Blo 1303970 1957145 := bstep (se 2 (by rfl) ⟨733929, by rfl⟩ : syracuseStep 1957145 = 1467859) B1467859
theorem B7429421 : Blo 1303970 7429421 := bstep (se 3 (by rfl) ⟨1393016, by rfl⟩ : syracuseStep 7429421 = 2786033) B2786033
theorem B12541229 : Blo 1303970 12541229 := bstep (se 3 (by rfl) ⟨2351480, by rfl⟩ : syracuseStep 12541229 = 4702961) B4702961
theorem B3718493 : Blo 1303970 3718493 := bstep (se 3 (by rfl) ⟨697217, by rfl⟩ : syracuseStep 3718493 = 1394435) B1394435
theorem B1957259 : Blo 1303970 1957259 := bstep (se 1 (by rfl) ⟨1467944, by rfl⟩ : syracuseStep 1957259 = 2935889) B2935889
theorem B1957271 : Blo 1303970 1957271 := bstep (se 1 (by rfl) ⟨1467953, by rfl⟩ : syracuseStep 1957271 = 2935907) B2935907
theorem B2645399 : Blo 1303970 2645399 := bstep (se 1 (by rfl) ⟨1984049, by rfl⟩ : syracuseStep 2645399 = 3968099) B3968099
theorem B2203031 : Blo 1303970 2203031 := bstep (se 1 (by rfl) ⟨1652273, by rfl⟩ : syracuseStep 2203031 = 3304547) B3304547
theorem B1957337 : Blo 1303970 1957337 := bstep (se 2 (by rfl) ⟨734001, by rfl⟩ : syracuseStep 1957337 = 1468003) B1468003
theorem B4955651 : Blo 1303970 4955651 := bstep (se 1 (by rfl) ⟨3716738, by rfl⟩ : syracuseStep 4955651 = 7433477) B7433477
theorem B2203159 : Blo 1303970 2203159 := bstep (se 1 (by rfl) ⟨1652369, by rfl⟩ : syracuseStep 2203159 = 3304739) B3304739
theorem B1957451 : Blo 1303970 1957451 := bstep (se 1 (by rfl) ⟨1468088, by rfl⟩ : syracuseStep 1957451 = 2936177) B2936177
theorem B1957463 : Blo 1303970 1957463 := bstep (se 1 (by rfl) ⟨1468097, by rfl⟩ : syracuseStep 1957463 = 2936195) B2936195
theorem B1957529 : Blo 1303970 1957529 := bstep (se 2 (by rfl) ⟨734073, by rfl⟩ : syracuseStep 1957529 = 1468147) B1468147
theorem B5570221 : Blo 1303970 5570221 := bstep (se 3 (by rfl) ⟨1044416, by rfl⟩ : syracuseStep 5570221 = 2088833) B2088833
theorem B3718835 : Blo 1303970 3718835 := bstep (se 1 (by rfl) ⟨2789126, by rfl⟩ : syracuseStep 3718835 = 5578253) B5578253
theorem B1957643 : Blo 1303970 1957643 := bstep (se 1 (by rfl) ⟨1468232, by rfl⟩ : syracuseStep 1957643 = 2936465) B2936465
theorem B1957655 : Blo 1303970 1957655 := bstep (se 1 (by rfl) ⟨1468241, by rfl⟩ : syracuseStep 1957655 = 2936483) B2936483
theorem B6610733 : Blo 1303970 6610733 := bstep (se 3 (by rfl) ⟨1239512, by rfl⟩ : syracuseStep 6610733 = 2479025) B2479025
theorem B3301195 : Blo 1303970 3301195 := bstep (se 1 (by rfl) ⟨2475896, by rfl⟩ : syracuseStep 3301195 = 4951793) B4951793
theorem B1957721 : Blo 1303970 1957721 := bstep (se 2 (by rfl) ⟨734145, by rfl⟩ : syracuseStep 1957721 = 1468291) B1468291
theorem B14106545 : Blo 1303970 14106545 := bstep (se 2 (by rfl) ⟨5289954, by rfl⟩ : syracuseStep 14106545 = 10579909) B10579909
theorem B3768257 : Blo 1303970 3768257 := bstep (se 2 (by rfl) ⟨1413096, by rfl⟩ : syracuseStep 3768257 = 2826193) B2826193
theorem B1957835 : Blo 1303970 1957835 := bstep (se 1 (by rfl) ⟨1468376, by rfl⟩ : syracuseStep 1957835 = 2936753) B2936753
theorem B1957847 : Blo 1303970 1957847 := bstep (se 1 (by rfl) ⟨1468385, by rfl⟩ : syracuseStep 1957847 = 2936771) B2936771
theorem B3301337 : Blo 1303970 3301337 := bstep (se 2 (by rfl) ⟨1238001, by rfl⟩ : syracuseStep 3301337 = 2476003) B2476003
theorem B3137537 : Blo 1303970 3137537 := bstep (se 2 (by rfl) ⟨1176576, by rfl⟩ : syracuseStep 3137537 = 2353153) B2353153
theorem B1957895 : Blo 1303970 1957895 := bstep (se 1 (by rfl) ⟨1468421, by rfl⟩ : syracuseStep 1957895 = 2936843) B2936843
theorem B6602795 : Blo 1303970 6602795 := bstep (se 1 (by rfl) ⟨4952096, by rfl⟩ : syracuseStep 6602795 = 9904193) B9904193
theorem B1957931 : Blo 1303970 1957931 := bstep (se 1 (by rfl) ⟨1468448, by rfl⟩ : syracuseStep 1957931 = 2936897) B2936897
theorem B9404477 : Blo 1303970 9404477 := bstep (se 3 (by rfl) ⟨1763339, by rfl⟩ : syracuseStep 9404477 = 3526679) B3526679
theorem B1957961 : Blo 1303970 1957961 := bstep (se 2 (by rfl) ⟨734235, by rfl⟩ : syracuseStep 1957961 = 1468471) B1468471
theorem B28237997 : Blo 1303970 28237997 := bstep (se 3 (by rfl) ⟨5294624, by rfl⟩ : syracuseStep 28237997 = 10589249) B10589249
theorem B1958075 : Blo 1303970 1958075 := bstep (se 1 (by rfl) ⟨1468556, by rfl⟩ : syracuseStep 1958075 = 2937113) B2937113
theorem B1958135 : Blo 1303970 1958135 := bstep (se 1 (by rfl) ⟨1468601, by rfl⟩ : syracuseStep 1958135 = 2937203) B2937203
theorem B1958159 : Blo 1303970 1958159 := bstep (se 1 (by rfl) ⟨1468619, by rfl⟩ : syracuseStep 1958159 = 2937239) B2937239
theorem B1958201 : Blo 1303970 1958201 := bstep (se 2 (by rfl) ⟨734325, by rfl⟩ : syracuseStep 1958201 = 1468651) B1468651
theorem B1958279 : Blo 1303970 1958279 := bstep (se 1 (by rfl) ⟨1468709, by rfl⟩ : syracuseStep 1958279 = 2937419) B2937419
theorem B1958315 : Blo 1303970 1958315 := bstep (se 1 (by rfl) ⟨1468736, by rfl⟩ : syracuseStep 1958315 = 2937473) B2937473
theorem B2089417 : Blo 1303970 2089417 := bstep (se 2 (by rfl) ⟨783531, by rfl⟩ : syracuseStep 2089417 = 1567063) B1567063
theorem B1958345 : Blo 1303970 1958345 := bstep (se 2 (by rfl) ⟨734379, by rfl⟩ : syracuseStep 1958345 = 1468759) B1468759
theorem B6111773 : Blo 1303970 6111773 := bstep (se 3 (by rfl) ⟨1145957, by rfl⟩ : syracuseStep 6111773 = 2291915) B2291915
theorem B4178461 : Blo 1303970 4178461 := bstep (se 3 (by rfl) ⟨783461, by rfl⟩ : syracuseStep 4178461 = 1566923) B1566923
theorem B1958459 : Blo 1303970 1958459 := bstep (se 1 (by rfl) ⟨1468844, by rfl⟩ : syracuseStep 1958459 = 2937689) B2937689
theorem B21439043 : Blo 1303970 21439043 := bstep (se 1 (by rfl) ⟨16079282, by rfl⟩ : syracuseStep 21439043 = 32158565) B32158565
theorem B1958519 : Blo 1303970 1958519 := bstep (se 1 (by rfl) ⟨1468889, by rfl⟩ : syracuseStep 1958519 = 2937779) B2937779
theorem B1958543 : Blo 1303970 1958543 := bstep (se 1 (by rfl) ⟨1468907, by rfl⟩ : syracuseStep 1958543 = 2937815) B2937815
theorem B1958585 : Blo 1303970 1958585 := bstep (se 2 (by rfl) ⟨734469, by rfl⟩ : syracuseStep 1958585 = 1468939) B1468939
theorem B1467067 : Blo 1303970 1467067 := bstep (se 1 (by rfl) ⟨1100300, by rfl⟩ : syracuseStep 1467067 = 2200601) B2200601
theorem B1958663 : Blo 1303970 1958663 := bstep (se 1 (by rfl) ⟨1468997, by rfl⟩ : syracuseStep 1958663 = 2937995) B2937995
theorem B1958699 : Blo 1303970 1958699 := bstep (se 1 (by rfl) ⟨1469024, by rfl⟩ : syracuseStep 1958699 = 2938049) B2938049
theorem B1958729 : Blo 1303970 1958729 := bstep (se 2 (by rfl) ⟨734523, by rfl⟩ : syracuseStep 1958729 = 1469047) B1469047
theorem B3302279 : Blo 1303970 3302279 := bstep (se 1 (by rfl) ⟨2476709, by rfl⟩ : syracuseStep 3302279 = 4953419) B4953419
theorem B18801571 : Blo 1303970 18801571 := bstep (se 1 (by rfl) ⟨14101178, by rfl⟩ : syracuseStep 18801571 = 28202357) B28202357
theorem B3302329 : Blo 1303970 3302329 := bstep (se 2 (by rfl) ⟨1238373, by rfl⟩ : syracuseStep 3302329 = 2476747) B2476747
theorem B1958843 : Blo 1303970 1958843 := bstep (se 1 (by rfl) ⟨1469132, by rfl⟩ : syracuseStep 1958843 = 2938265) B2938265
theorem B1958903 : Blo 1303970 1958903 := bstep (se 1 (by rfl) ⟨1469177, by rfl⟩ : syracuseStep 1958903 = 2938355) B2938355
theorem B1958927 : Blo 1303970 1958927 := bstep (se 1 (by rfl) ⟨1469195, by rfl⟩ : syracuseStep 1958927 = 2938391) B2938391
theorem B15885335 : Blo 1303970 15885335 := bstep (se 1 (by rfl) ⟨11914001, by rfl⟩ : syracuseStep 15885335 = 23828003) B23828003
theorem B2352187 : Blo 1303970 2352187 := bstep (se 1 (by rfl) ⟨1764140, by rfl⟩ : syracuseStep 2352187 = 3528281) B3528281
theorem B7054397 : Blo 1303970 7054397 := bstep (se 3 (by rfl) ⟨1322699, by rfl⟩ : syracuseStep 7054397 = 2645399) B2645399
theorem B1467535 : Blo 1303970 1467535 := bstep (se 1 (by rfl) ⟨1100651, by rfl⟩ : syracuseStep 1467535 = 2201303) B2201303
theorem B2933945 : Blo 1303970 2933945 := bstep (se 2 (by rfl) ⟨1100229, by rfl⟩ : syracuseStep 2933945 = 2200459) B2200459
theorem B6604091 : Blo 1303970 6604091 := bstep (se 1 (by rfl) ⟨4953068, by rfl⟩ : syracuseStep 6604091 = 9906137) B9906137
theorem B40150403 : Blo 1303970 40150403 := bstep (se 1 (by rfl) ⟨30112802, by rfl⟩ : syracuseStep 40150403 = 60225605) B60225605
theorem B8365457 : Blo 1303970 8365457 := bstep (se 2 (by rfl) ⟨3137046, by rfl⟩ : syracuseStep 8365457 = 6274093) B6274093
theorem B4179347 : Blo 1303970 4179347 := bstep (se 1 (by rfl) ⟨3134510, by rfl⟩ : syracuseStep 4179347 = 6269021) B6269021
theorem B4957625 : Blo 1303970 4957625 := bstep (se 2 (by rfl) ⟨1859109, by rfl⟩ : syracuseStep 4957625 = 3718219) B3718219
theorem B1303995 : Blo 1303970 1303995 := bstep (se 1 (by rfl) ⟨977996, by rfl⟩ : syracuseStep 1303995 = 1955993) B1955993
theorem B2385353 : Blo 1303970 2385353 := bstep (se 2 (by rfl) ⟨894507, by rfl⟩ : syracuseStep 2385353 = 1789015) B1789015
theorem B6604253 : Blo 1303970 6604253 := bstep (se 3 (by rfl) ⟨1238297, by rfl⟩ : syracuseStep 6604253 = 2476595) B2476595
theorem B1304071 : Blo 1303970 1304071 := bstep (se 1 (by rfl) ⟨978053, by rfl⟩ : syracuseStep 1304071 = 1956107) B1956107
theorem B1304079 : Blo 1303970 1304079 := bstep (se 1 (by rfl) ⟨978059, by rfl⟩ : syracuseStep 1304079 = 1956119) B1956119
theorem B2934287 : Blo 1303970 2934287 := bstep (se 1 (by rfl) ⟨2200715, by rfl⟩ : syracuseStep 2934287 = 4401431) B4401431
theorem B3302927 : Blo 1303970 3302927 := bstep (se 1 (by rfl) ⟨2477195, by rfl⟩ : syracuseStep 3302927 = 4954391) B4954391
theorem B2934305 : Blo 1303970 2934305 := bstep (se 2 (by rfl) ⟨1100364, by rfl⟩ : syracuseStep 2934305 = 2200729) B2200729
theorem B1304123 : Blo 1303970 1304123 := bstep (se 1 (by rfl) ⟨978092, by rfl⟩ : syracuseStep 1304123 = 1956185) B1956185
theorem B1304199 : Blo 1303970 1304199 := bstep (se 1 (by rfl) ⟨978149, by rfl⟩ : syracuseStep 1304199 = 1956299) B1956299
theorem B1468039 : Blo 1303970 1468039 := bstep (se 1 (by rfl) ⟨1101029, by rfl⟩ : syracuseStep 1468039 = 2202059) B2202059
theorem B1304207 : Blo 1303970 1304207 := bstep (se 1 (by rfl) ⟨978155, by rfl⟩ : syracuseStep 1304207 = 1956311) B1956311
theorem B1304251 : Blo 1303970 1304251 := bstep (se 1 (by rfl) ⟨978188, by rfl⟩ : syracuseStep 1304251 = 1956377) B1956377
theorem B16959233 : Blo 1303970 16959233 := bstep (se 2 (by rfl) ⟨6359712, by rfl⟩ : syracuseStep 16959233 = 12719425) B12719425
theorem B1304327 : Blo 1303970 1304327 := bstep (se 1 (by rfl) ⟨978245, by rfl⟩ : syracuseStep 1304327 = 1956491) B1956491
theorem B1304335 : Blo 1303970 1304335 := bstep (se 1 (by rfl) ⟨978251, by rfl⟩ : syracuseStep 1304335 = 1956503) B1956503
theorem B6604577 : Blo 1303970 6604577 := bstep (se 2 (by rfl) ⟨2476716, by rfl⟩ : syracuseStep 6604577 = 4953433) B4953433
theorem B1304379 : Blo 1303970 1304379 := bstep (se 1 (by rfl) ⟨978284, by rfl⟩ : syracuseStep 1304379 = 1956569) B1956569
theorem B1468219 : Blo 1303970 1468219 := bstep (se 1 (by rfl) ⟨1101164, by rfl⟩ : syracuseStep 1468219 = 2202329) B2202329
theorem B2934647 : Blo 1303970 2934647 := bstep (se 1 (by rfl) ⟨2200985, by rfl⟩ : syracuseStep 2934647 = 4401971) B4401971
theorem B1304455 : Blo 1303970 1304455 := bstep (se 1 (by rfl) ⟨978341, by rfl⟩ : syracuseStep 1304455 = 1956683) B1956683
theorem B1304463 : Blo 1303970 1304463 := bstep (se 1 (by rfl) ⟨978347, by rfl⟩ : syracuseStep 1304463 = 1956695) B1956695
theorem B1304507 : Blo 1303970 1304507 := bstep (se 1 (by rfl) ⟨978380, by rfl⟩ : syracuseStep 1304507 = 1956761) B1956761
theorem B1304583 : Blo 1303970 1304583 := bstep (se 1 (by rfl) ⟨978437, by rfl⟩ : syracuseStep 1304583 = 1956875) B1956875
theorem B1304591 : Blo 1303970 1304591 := bstep (se 1 (by rfl) ⟨978443, by rfl⟩ : syracuseStep 1304591 = 1956887) B1956887
theorem B3180559 : Blo 1303970 3180559 := bstep (se 1 (by rfl) ⟨2385419, by rfl⟩ : syracuseStep 3180559 = 4770839) B4770839
theorem B2934827 : Blo 1303970 2934827 := bstep (se 1 (by rfl) ⟨2201120, by rfl⟩ : syracuseStep 2934827 = 4402241) B4402241
theorem B2353195 : Blo 1303970 2353195 := bstep (se 1 (by rfl) ⟨1764896, by rfl⟩ : syracuseStep 2353195 = 3529793) B3529793
theorem B1304635 : Blo 1303970 1304635 := bstep (se 1 (by rfl) ⟨978476, by rfl⟩ : syracuseStep 1304635 = 1956953) B1956953
theorem B1304711 : Blo 1303970 1304711 := bstep (se 1 (by rfl) ⟨978533, by rfl⟩ : syracuseStep 1304711 = 1957067) B1957067
theorem B1304719 : Blo 1303970 1304719 := bstep (se 1 (by rfl) ⟨978539, by rfl⟩ : syracuseStep 1304719 = 1957079) B1957079
theorem B2975891 : Blo 1303970 2975891 := bstep (se 1 (by rfl) ⟨2231918, by rfl⟩ : syracuseStep 2975891 = 4463837) B4463837
theorem B1304763 : Blo 1303970 1304763 := bstep (se 1 (by rfl) ⟨978572, by rfl⟩ : syracuseStep 1304763 = 1957145) B1957145
theorem B3303625 : Blo 1303970 3303625 := bstep (se 2 (by rfl) ⟨1238859, by rfl⟩ : syracuseStep 3303625 = 2477719) B2477719
theorem B2787529 : Blo 1303970 2787529 := bstep (se 2 (by rfl) ⟨1045323, by rfl⟩ : syracuseStep 2787529 = 2090647) B2090647
theorem B1304839 : Blo 1303970 1304839 := bstep (se 1 (by rfl) ⟨978629, by rfl⟩ : syracuseStep 1304839 = 1957259) B1957259
theorem B1304847 : Blo 1303970 1304847 := bstep (se 1 (by rfl) ⟨978635, by rfl⟩ : syracuseStep 1304847 = 1957271) B1957271
theorem B1468687 : Blo 1303970 1468687 := bstep (se 1 (by rfl) ⟨1101515, by rfl⟩ : syracuseStep 1468687 = 2203031) B2203031
theorem B4704545 : Blo 1303970 4704545 := bstep (se 2 (by rfl) ⟨1764204, by rfl⟩ : syracuseStep 4704545 = 3528409) B3528409
theorem B1304891 : Blo 1303970 1304891 := bstep (se 1 (by rfl) ⟨978668, by rfl⟩ : syracuseStep 1304891 = 1957337) B1957337
theorem B3303767 : Blo 1303970 3303767 := bstep (se 1 (by rfl) ⟨2477825, by rfl⟩ : syracuseStep 3303767 = 4955651) B4955651
theorem B1304967 : Blo 1303970 1304967 := bstep (se 1 (by rfl) ⟨978725, by rfl⟩ : syracuseStep 1304967 = 1957451) B1957451
theorem B4704647 : Blo 1303970 4704647 := bstep (se 1 (by rfl) ⟨3528485, by rfl⟩ : syracuseStep 4704647 = 7056971) B7056971
theorem B1304975 : Blo 1303970 1304975 := bstep (se 1 (by rfl) ⟨978731, by rfl⟩ : syracuseStep 1304975 = 1957463) B1957463
theorem B2935187 : Blo 1303970 2935187 := bstep (se 1 (by rfl) ⟨2201390, by rfl⟩ : syracuseStep 2935187 = 4402781) B4402781
theorem B4401593 : Blo 1303970 4401593 := bstep (se 2 (by rfl) ⟨1650597, by rfl⟩ : syracuseStep 4401593 = 3301195) B3301195
theorem B1305019 : Blo 1303970 1305019 := bstep (se 1 (by rfl) ⟨978764, by rfl⟩ : syracuseStep 1305019 = 1957529) B1957529
theorem B2476489 : Blo 1303970 2476489 := bstep (se 2 (by rfl) ⟨928683, by rfl⟩ : syracuseStep 2476489 = 1857367) B1857367
theorem B2935241 : Blo 1303970 2935241 := bstep (se 2 (by rfl) ⟨1100715, by rfl⟩ : syracuseStep 2935241 = 2201431) B2201431
theorem B14862851 : Blo 1303970 14862851 := bstep (se 1 (by rfl) ⟨11147138, by rfl⟩ : syracuseStep 14862851 = 22294277) B22294277
theorem B1305095 : Blo 1303970 1305095 := bstep (se 1 (by rfl) ⟨978821, by rfl⟩ : syracuseStep 1305095 = 1957643) B1957643
theorem B1305103 : Blo 1303970 1305103 := bstep (se 1 (by rfl) ⟨978827, by rfl⟩ : syracuseStep 1305103 = 1957655) B1957655
theorem B14109227 : Blo 1303970 14109227 := bstep (se 1 (by rfl) ⟨10581920, by rfl⟩ : syracuseStep 14109227 = 21163841) B21163841
theorem B1305147 : Blo 1303970 1305147 := bstep (se 1 (by rfl) ⟨978860, by rfl⟩ : syracuseStep 1305147 = 1957721) B1957721
theorem B1305223 : Blo 1303970 1305223 := bstep (se 1 (by rfl) ⟨978917, by rfl⟩ : syracuseStep 1305223 = 1957835) B1957835
theorem B1305231 : Blo 1303970 1305231 := bstep (se 1 (by rfl) ⟨978923, by rfl⟩ : syracuseStep 1305231 = 1957847) B1957847
theorem B1305275 : Blo 1303970 1305275 := bstep (se 1 (by rfl) ⟨978956, by rfl⟩ : syracuseStep 1305275 = 1957913) B1957913
theorem B6605549 : Blo 1303970 6605549 := bstep (se 3 (by rfl) ⟨1238540, by rfl⟩ : syracuseStep 6605549 = 2477081) B2477081
theorem B1305351 : Blo 1303970 1305351 := bstep (se 1 (by rfl) ⟨979013, by rfl⟩ : syracuseStep 1305351 = 1958027) B1958027
theorem B1469191 : Blo 1303970 1469191 := bstep (se 1 (by rfl) ⟨1101893, by rfl⟩ : syracuseStep 1469191 = 2203787) B2203787
theorem B16714511 : Blo 1303970 16714511 := bstep (se 1 (by rfl) ⟨12535883, by rfl⟩ : syracuseStep 16714511 = 25071767) B25071767
theorem B1305359 : Blo 1303970 1305359 := bstep (se 1 (by rfl) ⟨979019, by rfl⟩ : syracuseStep 1305359 = 1958039) B1958039
theorem B1305403 : Blo 1303970 1305403 := bstep (se 1 (by rfl) ⟨979052, by rfl⟩ : syracuseStep 1305403 = 1958105) B1958105
theorem B1305479 : Blo 1303970 1305479 := bstep (se 1 (by rfl) ⟨979109, by rfl⟩ : syracuseStep 1305479 = 1958219) B1958219
theorem B1305487 : Blo 1303970 1305487 := bstep (se 1 (by rfl) ⟨979115, by rfl⟩ : syracuseStep 1305487 = 1958231) B1958231
theorem B1305531 : Blo 1303970 1305531 := bstep (se 1 (by rfl) ⟨979148, by rfl⟩ : syracuseStep 1305531 = 1958297) B1958297
theorem B1674247 : Blo 1303970 1674247 := bstep (se 1 (by rfl) ⟨1255685, by rfl⟩ : syracuseStep 1674247 = 2511371) B2511371
theorem B1305607 : Blo 1303970 1305607 := bstep (se 1 (by rfl) ⟨979205, by rfl⟩ : syracuseStep 1305607 = 1958411) B1958411
theorem B4402187 : Blo 1303970 4402187 := bstep (se 1 (by rfl) ⟨3301640, by rfl⟩ : syracuseStep 4402187 = 6603281) B6603281
theorem B1567759 : Blo 1303970 1567759 := bstep (se 1 (by rfl) ⟨1175819, by rfl⟩ : syracuseStep 1567759 = 2351639) B2351639
theorem B1305615 : Blo 1303970 1305615 := bstep (se 1 (by rfl) ⟨979211, by rfl⟩ : syracuseStep 1305615 = 1958423) B1958423
theorem B1305659 : Blo 1303970 1305659 := bstep (se 1 (by rfl) ⟨979244, by rfl⟩ : syracuseStep 1305659 = 1958489) B1958489
theorem B4402295 : Blo 1303970 4402295 := bstep (se 1 (by rfl) ⟨3301721, by rfl⟩ : syracuseStep 4402295 = 6603443) B6603443
theorem B12881029 : Blo 1303970 12881029 := bstep (se 4 (by rfl) ⟨1207596, by rfl⟩ : syracuseStep 12881029 = 2415193) B2415193
theorem B2935943 : Blo 1303970 2935943 := bstep (se 1 (by rfl) ⟨2201957, by rfl⟩ : syracuseStep 2935943 = 4403915) B4403915
theorem B1305735 : Blo 1303970 1305735 := bstep (se 1 (by rfl) ⟨979301, by rfl⟩ : syracuseStep 1305735 = 1958603) B1958603
theorem B1305743 : Blo 1303970 1305743 := bstep (se 1 (by rfl) ⟨979307, by rfl⟩ : syracuseStep 1305743 = 1958615) B1958615
theorem B1305787 : Blo 1303970 1305787 := bstep (se 1 (by rfl) ⟨979340, by rfl⟩ : syracuseStep 1305787 = 1958681) B1958681
theorem B12545225 : Blo 1303970 12545225 := bstep (se 2 (by rfl) ⟨4704459, by rfl⟩ : syracuseStep 12545225 = 9408919) B9408919
theorem B4951277 : Blo 1303970 4951277 := bstep (se 3 (by rfl) ⟨928364, by rfl⟩ : syracuseStep 4951277 = 1856729) B1856729
theorem B14118133 : Blo 1303970 14118133 := bstep (se 5 (by rfl) ⟨661787, by rfl⟩ : syracuseStep 14118133 = 1323575) B1323575
theorem B1305863 : Blo 1303970 1305863 := bstep (se 1 (by rfl) ⟨979397, by rfl⟩ : syracuseStep 1305863 = 1958795) B1958795
theorem B1305871 : Blo 1303970 1305871 := bstep (se 1 (by rfl) ⟨979403, by rfl⟩ : syracuseStep 1305871 = 1958807) B1958807
theorem B2936123 : Blo 1303970 2936123 := bstep (se 1 (by rfl) ⟨2202092, by rfl⟩ : syracuseStep 2936123 = 4404185) B4404185
theorem B1305915 : Blo 1303970 1305915 := bstep (se 1 (by rfl) ⟨979436, by rfl⟩ : syracuseStep 1305915 = 1958873) B1958873
theorem B2231687 : Blo 1303970 2231687 := bstep (se 1 (by rfl) ⟨1673765, by rfl⟩ : syracuseStep 2231687 = 3347531) B3347531
theorem B25079219 : Blo 1303970 25079219 := bstep (se 1 (by rfl) ⟨18809414, by rfl⟩ : syracuseStep 25079219 = 37618829) B37618829
theorem B2936249 : Blo 1303970 2936249 := bstep (se 2 (by rfl) ⟨1101093, by rfl⟩ : syracuseStep 2936249 = 2202187) B2202187
theorem B9915857 : Blo 1303970 9915857 := bstep (se 2 (by rfl) ⟨3718446, by rfl⟩ : syracuseStep 9915857 = 7436893) B7436893
theorem B6606359 : Blo 1303970 6606359 := bstep (se 1 (by rfl) ⟨4954769, by rfl⟩ : syracuseStep 6606359 = 9909539) B9909539
theorem B7433795 : Blo 1303970 7433795 := bstep (se 1 (by rfl) ⟨5575346, by rfl⟩ : syracuseStep 7433795 = 11150693) B11150693
theorem B4402889 : Blo 1303970 4402889 := bstep (se 2 (by rfl) ⟨1651083, by rfl⟩ : syracuseStep 4402889 = 3302167) B3302167
theorem B11153153 : Blo 1303970 11153153 := bstep (se 2 (by rfl) ⟨4182432, by rfl⟩ : syracuseStep 11153153 = 8364865) B8364865
theorem B2936591 : Blo 1303970 2936591 := bstep (se 1 (by rfl) ⟨2202443, by rfl⟩ : syracuseStep 2936591 = 4404887) B4404887
theorem B2936609 : Blo 1303970 2936609 := bstep (se 2 (by rfl) ⟨1101228, by rfl⟩ : syracuseStep 2936609 = 2202457) B2202457
theorem B4951961 : Blo 1303970 4951961 := bstep (se 2 (by rfl) ⟨1856985, by rfl⟩ : syracuseStep 4951961 = 3713971) B3713971
theorem B7434251 : Blo 1303970 7434251 := bstep (se 1 (by rfl) ⟨5575688, by rfl⟩ : syracuseStep 7434251 = 11151377) B11151377
theorem B11300887 : Blo 1303970 11300887 := bstep (se 1 (by rfl) ⟨8475665, by rfl⟩ : syracuseStep 11300887 = 16951331) B16951331
theorem B6271019 : Blo 1303970 6271019 := bstep (se 1 (by rfl) ⟨4703264, by rfl⟩ : syracuseStep 6271019 = 9406529) B9406529
theorem B2936951 : Blo 1303970 2936951 := bstep (se 1 (by rfl) ⟨2202713, by rfl⟩ : syracuseStep 2936951 = 4405427) B4405427
theorem B1487035 : Blo 1303970 1487035 := bstep (se 1 (by rfl) ⟨1115276, by rfl⟩ : syracuseStep 1487035 = 2230553) B2230553
theorem B2937131 : Blo 1303970 2937131 := bstep (se 1 (by rfl) ⟨2202848, by rfl⟩ : syracuseStep 2937131 = 4405697) B4405697
theorem B3715463 : Blo 1303970 3715463 := bstep (se 1 (by rfl) ⟨2786597, by rfl⟩ : syracuseStep 3715463 = 5573195) B5573195
theorem B4403591 : Blo 1303970 4403591 := bstep (se 1 (by rfl) ⟨3302693, by rfl⟩ : syracuseStep 4403591 = 6605387) B6605387
theorem B10039697 : Blo 1303970 10039697 := bstep (se 2 (by rfl) ⟨3764886, by rfl⟩ : syracuseStep 10039697 = 7529773) B7529773
theorem B9409067 : Blo 1303970 9409067 := bstep (se 1 (by rfl) ⟨7056800, by rfl⟩ : syracuseStep 9409067 = 14113601) B14113601
theorem B3715645 : Blo 1303970 3715645 := bstep (se 3 (by rfl) ⟨696683, by rfl⟩ : syracuseStep 3715645 = 1393367) B1393367
theorem B3715703 : Blo 1303970 3715703 := bstep (se 1 (by rfl) ⟨2786777, by rfl⟩ : syracuseStep 3715703 = 5573555) B5573555
theorem B2937491 : Blo 1303970 2937491 := bstep (se 1 (by rfl) ⟨2203118, by rfl⟩ : syracuseStep 2937491 = 4406237) B4406237
theorem B2937545 : Blo 1303970 2937545 := bstep (se 2 (by rfl) ⟨1101579, by rfl⟩ : syracuseStep 2937545 = 2203159) B2203159
theorem B4403969 : Blo 1303970 4403969 := bstep (se 2 (by rfl) ⟨1651488, by rfl⟩ : syracuseStep 4403969 = 3302977) B3302977
theorem B5575483 : Blo 1303970 5575483 := bstep (se 1 (by rfl) ⟨4181612, by rfl⟩ : syracuseStep 5575483 = 8363225) B8363225
theorem B4952947 : Blo 1303970 4952947 := bstep (se 1 (by rfl) ⟨3714710, by rfl⟩ : syracuseStep 4952947 = 7429421) B7429421
theorem B8360819 : Blo 1303970 8360819 := bstep (se 1 (by rfl) ⟨6270614, by rfl⟩ : syracuseStep 8360819 = 12541229) B12541229
theorem B15070067 : Blo 1303970 15070067 := bstep (se 1 (by rfl) ⟨11302550, by rfl⟩ : syracuseStep 15070067 = 22605101) B22605101
theorem B7426961 : Blo 1303970 7426961 := bstep (se 2 (by rfl) ⟨2785110, by rfl⟩ : syracuseStep 7426961 = 5570221) B5570221
theorem B2478995 : Blo 1303970 2478995 := bstep (se 1 (by rfl) ⟨1859246, by rfl⟩ : syracuseStep 2478995 = 3718493) B3718493
theorem B10040381 : Blo 1303970 10040381 := bstep (se 3 (by rfl) ⟨1882571, by rfl⟩ : syracuseStep 10040381 = 3765143) B3765143
theorem B2479223 : Blo 1303970 2479223 := bstep (se 1 (by rfl) ⟨1859417, by rfl⟩ : syracuseStep 2479223 = 3718835) B3718835
theorem B2512171 : Blo 1303970 2512171 := bstep (se 1 (by rfl) ⟨1884128, by rfl⟩ : syracuseStep 2512171 = 3768257) B3768257
theorem B2200891 : Blo 1303970 2200891 := bstep (se 1 (by rfl) ⟨1650668, by rfl⟩ : syracuseStep 2200891 = 3301337) B3301337
theorem B2938247 : Blo 1303970 2938247 := bstep (se 1 (by rfl) ⟨2203685, by rfl⟩ : syracuseStep 2938247 = 4407371) B4407371
theorem B5952953 : Blo 1303970 5952953 := bstep (se 2 (by rfl) ⟨2232357, by rfl⟩ : syracuseStep 5952953 = 4464715) B4464715
theorem B2201033 : Blo 1303970 2201033 := bstep (se 2 (by rfl) ⟨825387, by rfl⟩ : syracuseStep 2201033 = 1650775) B1650775
theorem B13383133 : Blo 1303970 13383133 := bstep (se 3 (by rfl) ⟨2509337, by rfl⟩ : syracuseStep 13383133 = 5018675) B5018675
theorem B7050763 : Blo 1303970 7050763 := bstep (se 1 (by rfl) ⟨5288072, by rfl⟩ : syracuseStep 7050763 = 10576145) B10576145
theorem B3135019 : Blo 1303970 3135019 := bstep (se 1 (by rfl) ⟨2351264, by rfl⟩ : syracuseStep 3135019 = 4702529) B4702529
theorem B4404779 : Blo 1303970 4404779 := bstep (se 1 (by rfl) ⟨3303584, by rfl⟩ : syracuseStep 4404779 = 6607169) B6607169
theorem B2938427 : Blo 1303970 2938427 := bstep (se 1 (by rfl) ⟨2203820, by rfl⟩ : syracuseStep 2938427 = 4407641) B4407641
theorem B7427645 : Blo 1303970 7427645 := bstep (se 3 (by rfl) ⟨1392683, by rfl⟩ : syracuseStep 7427645 = 2785367) B2785367
theorem B4462141 : Blo 1303970 4462141 := bstep (se 3 (by rfl) ⟨836651, by rfl⟩ : syracuseStep 4462141 = 1673303) B1673303
theorem B4183613 : Blo 1303970 4183613 := bstep (se 3 (by rfl) ⟨784427, by rfl⟩ : syracuseStep 4183613 = 1568855) B1568855
theorem B3716761 : Blo 1303970 3716761 := bstep (se 2 (by rfl) ⟨1393785, by rfl⟩ : syracuseStep 3716761 = 2787571) B2787571
theorem B1652395 : Blo 1303970 1652395 := bstep (se 1 (by rfl) ⟨1239296, by rfl⟩ : syracuseStep 1652395 = 2478593) B2478593
theorem B1857287 : Blo 1303970 1857287 := bstep (se 1 (by rfl) ⟨1392965, by rfl⟩ : syracuseStep 1857287 = 2785931) B2785931
theorem B5289761 : Blo 1303970 5289761 := bstep (se 2 (by rfl) ⟨1983660, by rfl⟩ : syracuseStep 5289761 = 3967321) B3967321
theorem B5289875 : Blo 1303970 5289875 := bstep (se 1 (by rfl) ⟨3967406, by rfl⟩ : syracuseStep 5289875 = 7934813) B7934813
theorem B6273035 : Blo 1303970 6273035 := bstep (se 1 (by rfl) ⟨4704776, by rfl⟩ : syracuseStep 6273035 = 9409553) B9409553
theorem B1857595 : Blo 1303970 1857595 := bstep (se 1 (by rfl) ⟨1393196, by rfl⟩ : syracuseStep 1857595 = 2786393) B2786393
theorem B10049669 : Blo 1303970 10049669 := bstep (se 4 (by rfl) ⟨942156, by rfl⟩ : syracuseStep 10049669 = 1884313) B1884313
theorem B1955975 : Blo 1303970 1955975 := bstep (se 1 (by rfl) ⟨1466981, by rfl⟩ : syracuseStep 1955975 = 2933963) B2933963
theorem B2201735 : Blo 1303970 2201735 := bstep (se 1 (by rfl) ⟨1651301, by rfl⟩ : syracuseStep 2201735 = 3302603) B3302603
theorem B3135635 : Blo 1303970 3135635 := bstep (se 1 (by rfl) ⟨2351726, by rfl⟩ : syracuseStep 3135635 = 4703453) B4703453
theorem B1956011 : Blo 1303970 1956011 := bstep (se 1 (by rfl) ⟨1467008, by rfl⟩ : syracuseStep 1956011 = 2934017) B2934017
theorem B1956041 : Blo 1303970 1956041 := bstep (se 2 (by rfl) ⟨733515, by rfl⟩ : syracuseStep 1956041 = 1467031) B1467031
theorem B14858477 : Blo 1303970 14858477 := bstep (se 3 (by rfl) ⟨2785964, by rfl⟩ : syracuseStep 14858477 = 5571929) B5571929
theorem B3717377 : Blo 1303970 3717377 := bstep (se 2 (by rfl) ⟨1394016, by rfl⟩ : syracuseStep 3717377 = 2788033) B2788033
theorem B5650721 : Blo 1303970 5650721 := bstep (se 2 (by rfl) ⟨2119020, by rfl⟩ : syracuseStep 5650721 = 4238041) B4238041
theorem B1956155 : Blo 1303970 1956155 := bstep (se 1 (by rfl) ⟨1467116, by rfl⟩ : syracuseStep 1956155 = 2934233) B2934233
theorem B1956215 : Blo 1303970 1956215 := bstep (se 1 (by rfl) ⟨1467161, by rfl⟩ : syracuseStep 1956215 = 2934323) B2934323
theorem B1956239 : Blo 1303970 1956239 := bstep (se 1 (by rfl) ⟨1467179, by rfl⟩ : syracuseStep 1956239 = 2934359) B2934359
theorem B1956281 : Blo 1303970 1956281 := bstep (se 2 (by rfl) ⟨733605, by rfl⟩ : syracuseStep 1956281 = 1467211) B1467211
theorem B1956359 : Blo 1303970 1956359 := bstep (se 1 (by rfl) ⟨1467269, by rfl⟩ : syracuseStep 1956359 = 2934539) B2934539
theorem B4700683 : Blo 1303970 4700683 := bstep (se 1 (by rfl) ⟨3525512, by rfl⟩ : syracuseStep 4700683 = 7051025) B7051025
theorem B16095773 : Blo 1303970 16095773 := bstep (se 3 (by rfl) ⟨3017957, by rfl⟩ : syracuseStep 16095773 = 6035915) B6035915
theorem B6609437 : Blo 1303970 6609437 := bstep (se 3 (by rfl) ⟨1239269, by rfl⟩ : syracuseStep 6609437 = 2478539) B2478539
theorem B5577245 : Blo 1303970 5577245 := bstep (se 3 (by rfl) ⟨1045733, by rfl⟩ : syracuseStep 5577245 = 2091467) B2091467
theorem B1956395 : Blo 1303970 1956395 := bstep (se 1 (by rfl) ⟨1467296, by rfl⟩ : syracuseStep 1956395 = 2934593) B2934593
theorem B1956425 : Blo 1303970 1956425 := bstep (se 2 (by rfl) ⟨733659, by rfl⟩ : syracuseStep 1956425 = 1467319) B1467319
theorem B3136153 : Blo 1303970 3136153 := bstep (se 2 (by rfl) ⟨1176057, by rfl⟩ : syracuseStep 3136153 = 2352115) B2352115
theorem B1956539 : Blo 1303970 1956539 := bstep (se 1 (by rfl) ⟨1467404, by rfl⟩ : syracuseStep 1956539 = 2934809) B2934809
theorem B1956599 : Blo 1303970 1956599 := bstep (se 1 (by rfl) ⟨1467449, by rfl⟩ : syracuseStep 1956599 = 2934899) B2934899
theorem B13769473 : Blo 1303970 13769473 := bstep (se 2 (by rfl) ⟨5163552, by rfl⟩ : syracuseStep 13769473 = 10327105) B10327105
theorem B1956623 : Blo 1303970 1956623 := bstep (se 1 (by rfl) ⟨1467467, by rfl⟩ : syracuseStep 1956623 = 2934935) B2934935
theorem B2202383 : Blo 1303970 2202383 := bstep (se 1 (by rfl) ⟨1651787, by rfl⟩ : syracuseStep 2202383 = 3303575) B3303575
theorem B12548915 : Blo 1303970 12548915 := bstep (se 1 (by rfl) ⟨9411686, by rfl⟩ : syracuseStep 12548915 = 18823373) B18823373
theorem B1956665 : Blo 1303970 1956665 := bstep (se 2 (by rfl) ⟨733749, by rfl⟩ : syracuseStep 1956665 = 1467499) B1467499
theorem B4406075 : Blo 1303970 4406075 := bstep (se 1 (by rfl) ⟨3304556, by rfl⟩ : syracuseStep 4406075 = 6609113) B6609113
theorem B6273881 : Blo 1303970 6273881 := bstep (se 2 (by rfl) ⟨2352705, by rfl⟩ : syracuseStep 6273881 = 4705411) B4705411
theorem B1956743 : Blo 1303970 1956743 := bstep (se 1 (by rfl) ⟨1467557, by rfl⟩ : syracuseStep 1956743 = 2935115) B2935115
theorem B1956779 : Blo 1303970 1956779 := bstep (se 1 (by rfl) ⟨1467584, by rfl⟩ : syracuseStep 1956779 = 2935169) B2935169
theorem B3136441 : Blo 1303970 3136441 := bstep (se 2 (by rfl) ⟨1176165, by rfl⟩ : syracuseStep 3136441 = 2352331) B2352331
theorem B1956809 : Blo 1303970 1956809 := bstep (se 2 (by rfl) ⟨733803, by rfl⟩ : syracuseStep 1956809 = 1467607) B1467607
theorem B4021249 : Blo 1303970 4021249 := bstep (se 2 (by rfl) ⟨1507968, by rfl⟩ : syracuseStep 4021249 = 3015937) B3015937
theorem B6609923 : Blo 1303970 6609923 := bstep (se 1 (by rfl) ⟨4957442, by rfl⟩ : syracuseStep 6609923 = 9914885) B9914885
theorem B12549143 : Blo 1303970 12549143 := bstep (se 1 (by rfl) ⟨9411857, by rfl⟩ : syracuseStep 12549143 = 18823715) B18823715
theorem B4955165 : Blo 1303970 4955165 := bstep (se 3 (by rfl) ⟨929093, by rfl⟩ : syracuseStep 4955165 = 1858187) B1858187
theorem B1956923 : Blo 1303970 1956923 := bstep (se 1 (by rfl) ⟨1467692, by rfl⟩ : syracuseStep 1956923 = 2935385) B2935385
theorem B1956983 : Blo 1303970 1956983 := bstep (se 1 (by rfl) ⟨1467737, by rfl⟩ : syracuseStep 1956983 = 2935475) B2935475
theorem B1957007 : Blo 1303970 1957007 := bstep (se 1 (by rfl) ⟨1467755, by rfl⟩ : syracuseStep 1957007 = 2935511) B2935511
theorem B1957049 : Blo 1303970 1957049 := bstep (se 2 (by rfl) ⟨733893, by rfl⟩ : syracuseStep 1957049 = 1467787) B1467787
theorem B1858745 : Blo 1303970 1858745 := bstep (se 2 (by rfl) ⟨697029, by rfl⟩ : syracuseStep 1858745 = 1394059) B1394059
theorem B3718345 : Blo 1303970 3718345 := bstep (se 2 (by rfl) ⟨1394379, by rfl⟩ : syracuseStep 3718345 = 2788759) B2788759
theorem B5577929 : Blo 1303970 5577929 := bstep (se 2 (by rfl) ⟨2091723, by rfl⟩ : syracuseStep 5577929 = 4183447) B4183447
theorem B6601985 : Blo 1303970 6601985 := bstep (se 2 (by rfl) ⟨2475744, by rfl⟩ : syracuseStep 6601985 = 4951489) B4951489
theorem B3136769 : Blo 1303970 3136769 := bstep (se 2 (by rfl) ⟨1176288, by rfl⟩ : syracuseStep 3136769 = 2352577) B2352577
theorem B1957127 : Blo 1303970 1957127 := bstep (se 1 (by rfl) ⟨1467845, by rfl⟩ : syracuseStep 1957127 = 2935691) B2935691
theorem B4406561 : Blo 1303970 4406561 := bstep (se 2 (by rfl) ⟨1652460, by rfl⟩ : syracuseStep 4406561 = 3304921) B3304921
theorem B1957163 : Blo 1303970 1957163 := bstep (se 1 (by rfl) ⟨1467872, by rfl⟩ : syracuseStep 1957163 = 2935745) B2935745
theorem B2202923 : Blo 1303970 2202923 := bstep (se 1 (by rfl) ⟨1652192, by rfl⟩ : syracuseStep 2202923 = 3304385) B3304385
theorem B1957193 : Blo 1303970 1957193 := bstep (se 2 (by rfl) ⟨733947, by rfl⟩ : syracuseStep 1957193 = 1467895) B1467895
theorem B1957307 : Blo 1303970 1957307 := bstep (se 1 (by rfl) ⟨1467980, by rfl⟩ : syracuseStep 1957307 = 2935961) B2935961
theorem B1957367 : Blo 1303970 1957367 := bstep (se 1 (by rfl) ⟨1468025, by rfl⟩ : syracuseStep 1957367 = 2936051) B2936051
theorem B1957391 : Blo 1303970 1957391 := bstep (se 1 (by rfl) ⟨1468043, by rfl⟩ : syracuseStep 1957391 = 2936087) B2936087
theorem B6692375 : Blo 1303970 6692375 := bstep (se 1 (by rfl) ⟨5019281, by rfl⟩ : syracuseStep 6692375 = 10038563) B10038563
theorem B1957433 : Blo 1303970 1957433 := bstep (se 2 (by rfl) ⟨734037, by rfl⟩ : syracuseStep 1957433 = 1468075) B1468075
theorem B3300983 : Blo 1303970 3300983 := bstep (se 1 (by rfl) ⟨2475737, by rfl⟩ : syracuseStep 3300983 = 4951475) B4951475
theorem B1957511 : Blo 1303970 1957511 := bstep (se 1 (by rfl) ⟨1468133, by rfl⟩ : syracuseStep 1957511 = 2936267) B2936267
theorem B1957547 : Blo 1303970 1957547 := bstep (se 1 (by rfl) ⟨1468160, by rfl⟩ : syracuseStep 1957547 = 2936321) B2936321
theorem B2203321 : Blo 1303970 2203321 := bstep (se 2 (by rfl) ⟨826245, by rfl⟩ : syracuseStep 2203321 = 1652491) B1652491
theorem B1957577 : Blo 1303970 1957577 := bstep (se 2 (by rfl) ⟨734091, by rfl⟩ : syracuseStep 1957577 = 1468183) B1468183
theorem B4955849 : Blo 1303970 4955849 := bstep (se 2 (by rfl) ⟨1858443, by rfl⟩ : syracuseStep 4955849 = 3716887) B3716887
theorem B1957691 : Blo 1303970 1957691 := bstep (se 1 (by rfl) ⟨1468268, by rfl⟩ : syracuseStep 1957691 = 2936537) B2936537
theorem B4407155 : Blo 1303970 4407155 := bstep (se 1 (by rfl) ⟨3305366, by rfl⟩ : syracuseStep 4407155 = 6610733) B6610733
theorem B1957751 : Blo 1303970 1957751 := bstep (se 1 (by rfl) ⟨1468313, by rfl⟩ : syracuseStep 1957751 = 2936627) B2936627
theorem B1957775 : Blo 1303970 1957775 := bstep (se 1 (by rfl) ⟨1468331, by rfl⟩ : syracuseStep 1957775 = 2936663) B2936663
theorem B1957817 : Blo 1303970 1957817 := bstep (se 2 (by rfl) ⟨734181, by rfl⟩ : syracuseStep 1957817 = 1468363) B1468363
theorem B9404363 : Blo 1303970 9404363 := bstep (se 1 (by rfl) ⟨7053272, by rfl⟩ : syracuseStep 9404363 = 14106545) B14106545
theorem B4956167 : Blo 1303970 4956167 := bstep (se 1 (by rfl) ⟨3717125, by rfl⟩ : syracuseStep 4956167 = 7434251) B7434251
theorem B42360893 : Blo 1303970 42360893 := bstep (se 3 (by rfl) ⟨7942667, by rfl⟩ : syracuseStep 42360893 = 15885335) B15885335
theorem B1957967 : Blo 1303970 1957967 := bstep (se 1 (by rfl) ⟨1468475, by rfl⟩ : syracuseStep 1957967 = 2936951) B2936951
theorem B18825331 : Blo 1303970 18825331 := bstep (se 1 (by rfl) ⟨14118998, by rfl⟩ : syracuseStep 18825331 = 28237997) B28237997
theorem B1958087 : Blo 1303970 1958087 := bstep (se 1 (by rfl) ⟨1468565, by rfl⟩ : syracuseStep 1958087 = 2937131) B2937131
theorem B12550373 : Blo 1303970 12550373 := bstep (se 4 (by rfl) ⟨1176597, by rfl⟩ : syracuseStep 12550373 = 2353195) B2353195
theorem B1982713 : Blo 1303970 1982713 := bstep (se 2 (by rfl) ⟨743517, by rfl⟩ : syracuseStep 1982713 = 1487035) B1487035
theorem B6693131 : Blo 1303970 6693131 := bstep (se 1 (by rfl) ⟨5019848, by rfl⟩ : syracuseStep 6693131 = 10039697) B10039697
theorem B1958249 : Blo 1303970 1958249 := bstep (se 2 (by rfl) ⟨734343, by rfl⟩ : syracuseStep 1958249 = 1468687) B1468687
theorem B1958327 : Blo 1303970 1958327 := bstep (se 1 (by rfl) ⟨1468745, by rfl⟩ : syracuseStep 1958327 = 2937491) B2937491
theorem B1958363 : Blo 1303970 1958363 := bstep (se 1 (by rfl) ⟨1468772, by rfl⟩ : syracuseStep 1958363 = 2937545) B2937545
theorem B4956653 : Blo 1303970 4956653 := bstep (se 3 (by rfl) ⟨929372, by rfl⟩ : syracuseStep 4956653 = 1858745) B1858745
theorem B2785889 : Blo 1303970 2785889 := bstep (se 2 (by rfl) ⟨1044708, by rfl⟩ : syracuseStep 2785889 = 2089417) B2089417
theorem B3301985 : Blo 1303970 3301985 := bstep (se 2 (by rfl) ⟨1238244, by rfl⟩ : syracuseStep 3301985 = 2476489) B2476489
theorem B6267577 : Blo 1303970 6267577 := bstep (se 2 (by rfl) ⟨2350341, by rfl⟩ : syracuseStep 6267577 = 4700683) B4700683
theorem B5571281 : Blo 1303970 5571281 := bstep (se 2 (by rfl) ⟨2089230, by rfl⟩ : syracuseStep 5571281 = 4178461) B4178461
theorem B6693587 : Blo 1303970 6693587 := bstep (se 1 (by rfl) ⟨5020190, by rfl⟩ : syracuseStep 6693587 = 10040381) B10040381
theorem B4702931 : Blo 1303970 4702931 := bstep (se 1 (by rfl) ⟨3527198, by rfl⟩ : syracuseStep 4702931 = 7054397) B7054397
theorem B1958831 : Blo 1303970 1958831 := bstep (se 1 (by rfl) ⟨1469123, by rfl⟩ : syracuseStep 1958831 = 2938247) B2938247
theorem B2786231 : Blo 1303970 2786231 := bstep (se 1 (by rfl) ⟨2089673, by rfl⟩ : syracuseStep 2786231 = 4179347) B4179347
theorem B1467355 : Blo 1303970 1467355 := bstep (se 1 (by rfl) ⟨1100516, by rfl⟩ : syracuseStep 1467355 = 2201033) B2201033
theorem B18359297 : Blo 1303970 18359297 := bstep (se 2 (by rfl) ⟨6884736, by rfl⟩ : syracuseStep 18359297 = 13769473) B13769473
theorem B1958921 : Blo 1303970 1958921 := bstep (se 2 (by rfl) ⟨734595, by rfl⟩ : syracuseStep 1958921 = 1469191) B1469191
theorem B1958951 : Blo 1303970 1958951 := bstep (se 1 (by rfl) ⟨1469213, by rfl⟩ : syracuseStep 1958951 = 2938427) B2938427
theorem B6603929 : Blo 1303970 6603929 := bstep (se 2 (by rfl) ⟨2476473, by rfl⟩ : syracuseStep 6603929 = 4952947) B4952947
theorem B11306155 : Blo 1303970 11306155 := bstep (se 1 (by rfl) ⟨8479616, by rfl⟩ : syracuseStep 11306155 = 16959233) B16959233
theorem B25068761 : Blo 1303970 25068761 := bstep (se 2 (by rfl) ⟨9400785, by rfl⟩ : syracuseStep 25068761 = 18801571) B18801571
theorem B2090345 : Blo 1303970 2090345 := bstep (se 2 (by rfl) ⟨783879, by rfl⟩ : syracuseStep 2090345 = 1567759) B1567759
theorem B1303983 : Blo 1303970 1303983 := bstep (se 1 (by rfl) ⟨977987, by rfl⟩ : syracuseStep 1303983 = 1955975) B1955975
theorem B1467823 : Blo 1303970 1467823 := bstep (se 1 (by rfl) ⟨1100867, by rfl⟩ : syracuseStep 1467823 = 2201735) B2201735
theorem B2090423 : Blo 1303970 2090423 := bstep (se 1 (by rfl) ⟨1567817, by rfl⟩ : syracuseStep 2090423 = 3135635) B3135635
theorem B1304007 : Blo 1303970 1304007 := bstep (se 1 (by rfl) ⟨978005, by rfl⟩ : syracuseStep 1304007 = 1956011) B1956011
theorem B1304027 : Blo 1303970 1304027 := bstep (se 1 (by rfl) ⟨978020, by rfl⟩ : syracuseStep 1304027 = 1956041) B1956041
theorem B9905651 : Blo 1303970 9905651 := bstep (se 1 (by rfl) ⟨7429238, by rfl⟩ : syracuseStep 9905651 = 14858477) B14858477
theorem B1304103 : Blo 1303970 1304103 := bstep (se 1 (by rfl) ⟨978077, by rfl⟩ : syracuseStep 1304103 = 1956155) B1956155
theorem B1304143 : Blo 1303970 1304143 := bstep (se 1 (by rfl) ⟨978107, by rfl⟩ : syracuseStep 1304143 = 1956215) B1956215
theorem B1304159 : Blo 1303970 1304159 := bstep (se 1 (by rfl) ⟨978119, by rfl⟩ : syracuseStep 1304159 = 1956239) B1956239
theorem B4957793 : Blo 1303970 4957793 := bstep (se 2 (by rfl) ⟨1859172, by rfl⟩ : syracuseStep 4957793 = 3718345) B3718345
theorem B2934395 : Blo 1303970 2934395 := bstep (se 1 (by rfl) ⟨2200796, by rfl⟩ : syracuseStep 2934395 = 4401593) B4401593
theorem B1304187 : Blo 1303970 1304187 := bstep (se 1 (by rfl) ⟨978140, by rfl⟩ : syracuseStep 1304187 = 1956281) B1956281
theorem B1304239 : Blo 1303970 1304239 := bstep (se 1 (by rfl) ⟨978179, by rfl⟩ : syracuseStep 1304239 = 1956359) B1956359
theorem B1304263 : Blo 1303970 1304263 := bstep (se 1 (by rfl) ⟨978197, by rfl⟩ : syracuseStep 1304263 = 1956395) B1956395
theorem B9406151 : Blo 1303970 9406151 := bstep (se 1 (by rfl) ⟨7054613, by rfl⟩ : syracuseStep 9406151 = 14109227) B14109227
theorem B1304283 : Blo 1303970 1304283 := bstep (se 1 (by rfl) ⟨978212, by rfl⟩ : syracuseStep 1304283 = 1956425) B1956425
theorem B2934521 : Blo 1303970 2934521 := bstep (se 2 (by rfl) ⟨1100445, by rfl⟩ : syracuseStep 2934521 = 2200891) B2200891
theorem B1304359 : Blo 1303970 1304359 := bstep (se 1 (by rfl) ⟨978269, by rfl⟩ : syracuseStep 1304359 = 1956539) B1956539
theorem B1304399 : Blo 1303970 1304399 := bstep (se 1 (by rfl) ⟨978299, by rfl⟩ : syracuseStep 1304399 = 1956599) B1956599
theorem B11143007 : Blo 1303970 11143007 := bstep (se 1 (by rfl) ⟨8357255, by rfl⟩ : syracuseStep 11143007 = 16714511) B16714511
theorem B1304415 : Blo 1303970 1304415 := bstep (se 1 (by rfl) ⟨978311, by rfl⟩ : syracuseStep 1304415 = 1956623) B1956623
theorem B1468255 : Blo 1303970 1468255 := bstep (se 1 (by rfl) ⟨1101191, by rfl⟩ : syracuseStep 1468255 = 2202383) B2202383
theorem B8365943 : Blo 1303970 8365943 := bstep (se 1 (by rfl) ⟨6274457, by rfl⟩ : syracuseStep 8365943 = 12548915) B12548915
theorem B1304443 : Blo 1303970 1304443 := bstep (se 1 (by rfl) ⟨978332, by rfl⟩ : syracuseStep 1304443 = 1956665) B1956665
theorem B1304495 : Blo 1303970 1304495 := bstep (se 1 (by rfl) ⟨978371, by rfl⟩ : syracuseStep 1304495 = 1956743) B1956743
theorem B1304519 : Blo 1303970 1304519 := bstep (se 1 (by rfl) ⟨978389, by rfl⟩ : syracuseStep 1304519 = 1956779) B1956779
theorem B1304539 : Blo 1303970 1304539 := bstep (se 1 (by rfl) ⟨978404, by rfl⟩ : syracuseStep 1304539 = 1956809) B1956809
theorem B2934791 : Blo 1303970 2934791 := bstep (se 1 (by rfl) ⟨2201093, by rfl⟩ : syracuseStep 2934791 = 4402187) B4402187
theorem B8366095 : Blo 1303970 8366095 := bstep (se 1 (by rfl) ⟨6274571, by rfl⟩ : syracuseStep 8366095 = 12549143) B12549143
theorem B3303443 : Blo 1303970 3303443 := bstep (se 1 (by rfl) ⟨2477582, by rfl⟩ : syracuseStep 3303443 = 4955165) B4955165
theorem B1304615 : Blo 1303970 1304615 := bstep (se 1 (by rfl) ⟨978461, by rfl⟩ : syracuseStep 1304615 = 1956923) B1956923
theorem B4180025 : Blo 1303970 4180025 := bstep (se 2 (by rfl) ⟨1567509, by rfl⟩ : syracuseStep 4180025 = 3135019) B3135019
theorem B2934863 : Blo 1303970 2934863 := bstep (se 1 (by rfl) ⟨2201147, by rfl⟩ : syracuseStep 2934863 = 4402295) B4402295
theorem B1304655 : Blo 1303970 1304655 := bstep (se 1 (by rfl) ⟨978491, by rfl⟩ : syracuseStep 1304655 = 1956983) B1956983
theorem B5949521 : Blo 1303970 5949521 := bstep (se 2 (by rfl) ⟨2231070, by rfl⟩ : syracuseStep 5949521 = 4462141) B4462141
theorem B1304671 : Blo 1303970 1304671 := bstep (se 1 (by rfl) ⟨978503, by rfl⟩ : syracuseStep 1304671 = 1957007) B1957007
theorem B1304699 : Blo 1303970 1304699 := bstep (se 1 (by rfl) ⟨978524, by rfl⟩ : syracuseStep 1304699 = 1957049) B1957049
theorem B4401323 : Blo 1303970 4401323 := bstep (se 1 (by rfl) ⟨3300992, by rfl⟩ : syracuseStep 4401323 = 6601985) B6601985
theorem B2091179 : Blo 1303970 2091179 := bstep (se 1 (by rfl) ⟨1568384, by rfl⟩ : syracuseStep 2091179 = 3136769) B3136769
theorem B1304751 : Blo 1303970 1304751 := bstep (se 1 (by rfl) ⟨978563, by rfl⟩ : syracuseStep 1304751 = 1957127) B1957127
theorem B1304775 : Blo 1303970 1304775 := bstep (se 1 (by rfl) ⟨978581, by rfl⟩ : syracuseStep 1304775 = 1957163) B1957163
theorem B1468615 : Blo 1303970 1468615 := bstep (se 1 (by rfl) ⟨1101461, by rfl⟩ : syracuseStep 1468615 = 2202923) B2202923
theorem B1304795 : Blo 1303970 1304795 := bstep (se 1 (by rfl) ⟨978596, by rfl⟩ : syracuseStep 1304795 = 1957193) B1957193
theorem B1304871 : Blo 1303970 1304871 := bstep (se 1 (by rfl) ⟨978653, by rfl⟩ : syracuseStep 1304871 = 1957307) B1957307
theorem B1304911 : Blo 1303970 1304911 := bstep (se 1 (by rfl) ⟨978683, by rfl⟩ : syracuseStep 1304911 = 1957367) B1957367
theorem B1304927 : Blo 1303970 1304927 := bstep (se 1 (by rfl) ⟨978695, by rfl⟩ : syracuseStep 1304927 = 1957391) B1957391
theorem B1304955 : Blo 1303970 1304955 := bstep (se 1 (by rfl) ⟨978716, by rfl⟩ : syracuseStep 1304955 = 1957433) B1957433
theorem B1305007 : Blo 1303970 1305007 := bstep (se 1 (by rfl) ⟨978755, by rfl⟩ : syracuseStep 1305007 = 1957511) B1957511
theorem B1305031 : Blo 1303970 1305031 := bstep (se 1 (by rfl) ⟨978773, by rfl⟩ : syracuseStep 1305031 = 1957547) B1957547
theorem B2935259 : Blo 1303970 2935259 := bstep (se 1 (by rfl) ⟨2201444, by rfl⟩ : syracuseStep 2935259 = 4402889) B4402889
theorem B1305051 : Blo 1303970 1305051 := bstep (se 1 (by rfl) ⟨978788, by rfl⟩ : syracuseStep 1305051 = 1957577) B1957577
theorem B3303899 : Blo 1303970 3303899 := bstep (se 1 (by rfl) ⟨2477924, by rfl⟩ : syracuseStep 3303899 = 4955849) B4955849
theorem B1305127 : Blo 1303970 1305127 := bstep (se 1 (by rfl) ⟨978845, by rfl⟩ : syracuseStep 1305127 = 1957691) B1957691
theorem B1305167 : Blo 1303970 1305167 := bstep (se 1 (by rfl) ⟨978875, by rfl⟩ : syracuseStep 1305167 = 1957751) B1957751
theorem B1305183 : Blo 1303970 1305183 := bstep (se 1 (by rfl) ⟨978887, by rfl⟩ : syracuseStep 1305183 = 1957775) B1957775
theorem B1305211 : Blo 1303970 1305211 := bstep (se 1 (by rfl) ⟨978908, by rfl⟩ : syracuseStep 1305211 = 1957817) B1957817
theorem B6269575 : Blo 1303970 6269575 := bstep (se 1 (by rfl) ⟨4702181, by rfl⟩ : syracuseStep 6269575 = 9404363) B9404363
theorem B2091691 : Blo 1303970 2091691 := bstep (se 1 (by rfl) ⟨1568768, by rfl⟩ : syracuseStep 2091691 = 3137537) B3137537
theorem B1305263 : Blo 1303970 1305263 := bstep (se 1 (by rfl) ⟨978947, by rfl⟩ : syracuseStep 1305263 = 1957895) B1957895
theorem B4401863 : Blo 1303970 4401863 := bstep (se 1 (by rfl) ⟨3301397, by rfl⟩ : syracuseStep 4401863 = 6602795) B6602795
theorem B4180679 : Blo 1303970 4180679 := bstep (se 1 (by rfl) ⟨3135509, by rfl⟩ : syracuseStep 4180679 = 6271019) B6271019
theorem B1305287 : Blo 1303970 1305287 := bstep (se 1 (by rfl) ⟨978965, by rfl⟩ : syracuseStep 1305287 = 1957931) B1957931
theorem B6269651 : Blo 1303970 6269651 := bstep (se 1 (by rfl) ⟨4702238, by rfl⟩ : syracuseStep 6269651 = 9404477) B9404477
theorem B1305307 : Blo 1303970 1305307 := bstep (se 1 (by rfl) ⟨978980, by rfl⟩ : syracuseStep 1305307 = 1957961) B1957961
theorem B2476793 : Blo 1303970 2476793 := bstep (se 2 (by rfl) ⟨928797, by rfl⟩ : syracuseStep 2476793 = 1857595) B1857595
theorem B60271397 : Blo 1303970 60271397 := bstep (se 4 (by rfl) ⟨5650443, by rfl⟩ : syracuseStep 60271397 = 11300887) B11300887
theorem B1305383 : Blo 1303970 1305383 := bstep (se 1 (by rfl) ⟨979037, by rfl⟩ : syracuseStep 1305383 = 1958075) B1958075
theorem B1305423 : Blo 1303970 1305423 := bstep (se 1 (by rfl) ⟨979067, by rfl⟩ : syracuseStep 1305423 = 1958135) B1958135
theorem B1305439 : Blo 1303970 1305439 := bstep (se 1 (by rfl) ⟨979079, by rfl⟩ : syracuseStep 1305439 = 1958159) B1958159
theorem B1305467 : Blo 1303970 1305467 := bstep (se 1 (by rfl) ⟨979100, by rfl⟩ : syracuseStep 1305467 = 1958201) B1958201
theorem B2476975 : Blo 1303970 2476975 := bstep (se 1 (by rfl) ⟨1857731, by rfl⟩ : syracuseStep 2476975 = 3715463) B3715463
theorem B2935727 : Blo 1303970 2935727 := bstep (se 1 (by rfl) ⟨2201795, by rfl⟩ : syracuseStep 2935727 = 4403591) B4403591
theorem B1305519 : Blo 1303970 1305519 := bstep (se 1 (by rfl) ⟨979139, by rfl⟩ : syracuseStep 1305519 = 1958279) B1958279
theorem B1305543 : Blo 1303970 1305543 := bstep (se 1 (by rfl) ⟨979157, by rfl⟩ : syracuseStep 1305543 = 1958315) B1958315
theorem B1305563 : Blo 1303970 1305563 := bstep (se 1 (by rfl) ⟨979172, by rfl⟩ : syracuseStep 1305563 = 1958345) B1958345
theorem B4074515 : Blo 1303970 4074515 := bstep (se 1 (by rfl) ⟨3055886, by rfl⟩ : syracuseStep 4074515 = 6111773) B6111773
theorem B1305639 : Blo 1303970 1305639 := bstep (se 1 (by rfl) ⟨979229, by rfl⟩ : syracuseStep 1305639 = 1958459) B1958459
theorem B2477135 : Blo 1303970 2477135 := bstep (se 1 (by rfl) ⟨1857851, by rfl⟩ : syracuseStep 2477135 = 3715703) B3715703
theorem B1305679 : Blo 1303970 1305679 := bstep (se 1 (by rfl) ⟨979259, by rfl⟩ : syracuseStep 1305679 = 1958519) B1958519
theorem B1305695 : Blo 1303970 1305695 := bstep (se 1 (by rfl) ⟨979271, by rfl⟩ : syracuseStep 1305695 = 1958543) B1958543
theorem B1305723 : Blo 1303970 1305723 := bstep (se 1 (by rfl) ⟨979292, by rfl⟩ : syracuseStep 1305723 = 1958585) B1958585
theorem B2935979 : Blo 1303970 2935979 := bstep (se 1 (by rfl) ⟨2201984, by rfl⟩ : syracuseStep 2935979 = 4403969) B4403969
theorem B1305775 : Blo 1303970 1305775 := bstep (se 1 (by rfl) ⟨979331, by rfl⟩ : syracuseStep 1305775 = 1958663) B1958663
theorem B1305799 : Blo 1303970 1305799 := bstep (se 1 (by rfl) ⟨979349, by rfl⟩ : syracuseStep 1305799 = 1958699) B1958699
theorem B1305819 : Blo 1303970 1305819 := bstep (se 1 (by rfl) ⟨979364, by rfl⟩ : syracuseStep 1305819 = 1958729) B1958729
theorem B5573879 : Blo 1303970 5573879 := bstep (se 1 (by rfl) ⟨4180409, by rfl⟩ : syracuseStep 5573879 = 8360819) B8360819
theorem B10046711 : Blo 1303970 10046711 := bstep (se 1 (by rfl) ⟨7535033, by rfl⟩ : syracuseStep 10046711 = 15070067) B15070067
theorem B4951307 : Blo 1303970 4951307 := bstep (se 1 (by rfl) ⟨3713480, by rfl⟩ : syracuseStep 4951307 = 7426961) B7426961
theorem B1305895 : Blo 1303970 1305895 := bstep (se 1 (by rfl) ⟨979421, by rfl⟩ : syracuseStep 1305895 = 1958843) B1958843
theorem B1305935 : Blo 1303970 1305935 := bstep (se 1 (by rfl) ⟨979451, by rfl⟩ : syracuseStep 1305935 = 1958903) B1958903
theorem B1305951 : Blo 1303970 1305951 := bstep (se 1 (by rfl) ⟨979463, by rfl⟩ : syracuseStep 1305951 = 1958927) B1958927
theorem B4181537 : Blo 1303970 4181537 := bstep (se 2 (by rfl) ⟨1568076, by rfl⟩ : syracuseStep 4181537 = 3136153) B3136153
theorem B4402727 : Blo 1303970 4402727 := bstep (se 1 (by rfl) ⟨3302045, by rfl⟩ : syracuseStep 4402727 = 6604091) B6604091
theorem B26766935 : Blo 1303970 26766935 := bstep (se 1 (by rfl) ⟨20075201, by rfl⟩ : syracuseStep 26766935 = 40150403) B40150403
theorem B3968635 : Blo 1303970 3968635 := bstep (se 1 (by rfl) ⟨2976476, by rfl⟩ : syracuseStep 3968635 = 5952953) B5952953
theorem B3305083 : Blo 1303970 3305083 := bstep (se 1 (by rfl) ⟨2478812, by rfl⟩ : syracuseStep 3305083 = 4957625) B4957625
theorem B4402835 : Blo 1303970 4402835 := bstep (se 1 (by rfl) ⟨3302126, by rfl⟩ : syracuseStep 4402835 = 6604253) B6604253
theorem B12545725 : Blo 1303970 12545725 := bstep (se 3 (by rfl) ⟨2352323, by rfl⟩ : syracuseStep 12545725 = 4704647) B4704647
theorem B2936519 : Blo 1303970 2936519 := bstep (se 1 (by rfl) ⟨2202389, by rfl⟩ : syracuseStep 2936519 = 4404779) B4404779
theorem B4951763 : Blo 1303970 4951763 := bstep (se 1 (by rfl) ⟨3713822, by rfl⟩ : syracuseStep 4951763 = 7427645) B7427645
theorem B2789075 : Blo 1303970 2789075 := bstep (se 1 (by rfl) ⟨2091806, by rfl⟩ : syracuseStep 2789075 = 4183613) B4183613
theorem B7433977 : Blo 1303970 7433977 := bstep (se 2 (by rfl) ⟨2787741, by rfl⟩ : syracuseStep 7433977 = 5575483) B5575483
theorem B4403051 : Blo 1303970 4403051 := bstep (se 1 (by rfl) ⟨3302288, by rfl⟩ : syracuseStep 4403051 = 6604577) B6604577
theorem B3526507 : Blo 1303970 3526507 := bstep (se 1 (by rfl) ⟨2644880, by rfl⟩ : syracuseStep 3526507 = 5289761) B5289761
theorem B6360941 : Blo 1303970 6360941 := bstep (se 3 (by rfl) ⟨1192676, by rfl⟩ : syracuseStep 6360941 = 2385353) B2385353
theorem B4403105 : Blo 1303970 4403105 := bstep (se 2 (by rfl) ⟨1651164, by rfl⟩ : syracuseStep 4403105 = 3302329) B3302329
theorem B4181921 : Blo 1303970 4181921 := bstep (se 2 (by rfl) ⟨1568220, by rfl⟩ : syracuseStep 4181921 = 3136441) B3136441
theorem B3526583 : Blo 1303970 3526583 := bstep (se 1 (by rfl) ⟨2644937, by rfl⟩ : syracuseStep 3526583 = 5289875) B5289875
theorem B5361665 : Blo 1303970 5361665 := bstep (se 2 (by rfl) ⟨2010624, by rfl⟩ : syracuseStep 5361665 = 4021249) B4021249
theorem B4182023 : Blo 1303970 4182023 := bstep (se 1 (by rfl) ⟨3136517, by rfl⟩ : syracuseStep 4182023 = 6273035) B6273035
theorem B2232329 : Blo 1303970 2232329 := bstep (se 2 (by rfl) ⟨837123, by rfl⟩ : syracuseStep 2232329 = 1674247) B1674247
theorem B42922061 : Blo 1303970 42922061 := bstep (se 3 (by rfl) ⟨8047886, by rfl⟩ : syracuseStep 42922061 = 16095773) B16095773
theorem B2478251 : Blo 1303970 2478251 := bstep (se 1 (by rfl) ⟨1858688, by rfl⟩ : syracuseStep 2478251 = 3717377) B3717377
theorem B17174705 : Blo 1303970 17174705 := bstep (se 2 (by rfl) ⟨6440514, by rfl⟩ : syracuseStep 17174705 = 12881029) B12881029
theorem B9908567 : Blo 1303970 9908567 := bstep (se 1 (by rfl) ⟨7431425, by rfl⟩ : syracuseStep 9908567 = 14862851) B14862851
theorem B4403699 : Blo 1303970 4403699 := bstep (se 1 (by rfl) ⟨3302774, by rfl⟩ : syracuseStep 4403699 = 6605549) B6605549
theorem B2937383 : Blo 1303970 2937383 := bstep (se 1 (by rfl) ⟨2203037, by rfl⟩ : syracuseStep 2937383 = 4406075) B4406075
theorem B4182587 : Blo 1303970 4182587 := bstep (se 1 (by rfl) ⟨3136940, by rfl⟩ : syracuseStep 4182587 = 6273881) B6273881
theorem B9401017 : Blo 1303970 9401017 := bstep (se 2 (by rfl) ⟨3525381, by rfl⟩ : syracuseStep 9401017 = 7050763) B7050763
theorem B4952765 : Blo 1303970 4952765 := bstep (se 3 (by rfl) ⟨928643, by rfl⟩ : syracuseStep 4952765 = 1857287) B1857287
theorem B2937707 : Blo 1303970 2937707 := bstep (se 1 (by rfl) ⟨2203280, by rfl⟩ : syracuseStep 2937707 = 4406561) B4406561
theorem B2937761 : Blo 1303970 2937761 := bstep (se 2 (by rfl) ⟨1101660, by rfl⟩ : syracuseStep 2937761 = 2203321) B2203321
theorem B1487791 : Blo 1303970 1487791 := bstep (se 1 (by rfl) ⟨1115843, by rfl⟩ : syracuseStep 1487791 = 2231687) B2231687
theorem B4461583 : Blo 1303970 4461583 := bstep (se 1 (by rfl) ⟨3346187, by rfl⟩ : syracuseStep 4461583 = 6692375) B6692375
theorem B4404239 : Blo 1303970 4404239 := bstep (se 1 (by rfl) ⟨3303179, by rfl⟩ : syracuseStep 4404239 = 6606359) B6606359
theorem B2200655 : Blo 1303970 2200655 := bstep (se 1 (by rfl) ⟨1650491, by rfl⟩ : syracuseStep 2200655 = 3300983) B3300983
theorem B7435435 : Blo 1303970 7435435 := bstep (se 1 (by rfl) ⟨5576576, by rfl⟩ : syracuseStep 7435435 = 11153153) B11153153
theorem B2938103 : Blo 1303970 2938103 := bstep (se 1 (by rfl) ⟨2203577, by rfl⟩ : syracuseStep 2938103 = 4407155) B4407155
theorem B4240745 : Blo 1303970 4240745 := bstep (se 2 (by rfl) ⟨1590279, by rfl⟩ : syracuseStep 4240745 = 3180559) B3180559
theorem B4404833 : Blo 1303970 4404833 := bstep (se 2 (by rfl) ⟨1651812, by rfl⟩ : syracuseStep 4404833 = 3303625) B3303625
theorem B3716705 : Blo 1303970 3716705 := bstep (se 2 (by rfl) ⟨1393764, by rfl⟩ : syracuseStep 3716705 = 2787529) B2787529
theorem B6272711 : Blo 1303970 6272711 := bstep (se 1 (by rfl) ⟨4704533, by rfl⟩ : syracuseStep 6272711 = 9409067) B9409067
theorem B14292695 : Blo 1303970 14292695 := bstep (se 1 (by rfl) ⟨10719521, by rfl⟩ : syracuseStep 14292695 = 21439043) B21439043
theorem B2201519 : Blo 1303970 2201519 := bstep (se 1 (by rfl) ⟨1651139, by rfl⟩ : syracuseStep 2201519 = 3302279) B3302279
theorem B1652663 : Blo 1303970 1652663 := bstep (se 1 (by rfl) ⟨1239497, by rfl⟩ : syracuseStep 1652663 = 2478995) B2478995
theorem B1652815 : Blo 1303970 1652815 := bstep (se 1 (by rfl) ⟨1239611, by rfl⟩ : syracuseStep 1652815 = 2479223) B2479223
theorem B4954193 : Blo 1303970 4954193 := bstep (se 2 (by rfl) ⟨1857822, by rfl⟩ : syracuseStep 4954193 = 3715645) B3715645
theorem B1955963 : Blo 1303970 1955963 := bstep (se 1 (by rfl) ⟨1466972, by rfl⟩ : syracuseStep 1955963 = 2933945) B2933945
theorem B1956089 : Blo 1303970 1956089 := bstep (se 2 (by rfl) ⟨733533, by rfl⟩ : syracuseStep 1956089 = 1467067) B1467067
theorem B5576971 : Blo 1303970 5576971 := bstep (se 1 (by rfl) ⟨4182728, by rfl⟩ : syracuseStep 5576971 = 8365457) B8365457
theorem B1956191 : Blo 1303970 1956191 := bstep (se 1 (by rfl) ⟨1467143, by rfl⟩ : syracuseStep 1956191 = 2934287) B2934287
theorem B2201951 : Blo 1303970 2201951 := bstep (se 1 (by rfl) ⟨1651463, by rfl⟩ : syracuseStep 2201951 = 3302927) B3302927
theorem B1956203 : Blo 1303970 1956203 := bstep (se 1 (by rfl) ⟨1467152, by rfl⟩ : syracuseStep 1956203 = 2934305) B2934305
theorem B1956431 : Blo 1303970 1956431 := bstep (se 1 (by rfl) ⟨1467323, by rfl⟩ : syracuseStep 1956431 = 2934647) B2934647
theorem B1956551 : Blo 1303970 1956551 := bstep (se 1 (by rfl) ⟨1467413, by rfl⟩ : syracuseStep 1956551 = 2934827) B2934827
theorem B3136249 : Blo 1303970 3136249 := bstep (se 2 (by rfl) ⟨1176093, by rfl⟩ : syracuseStep 3136249 = 2352187) B2352187
theorem B6699779 : Blo 1303970 6699779 := bstep (se 1 (by rfl) ⟨5024834, by rfl⟩ : syracuseStep 6699779 = 10049669) B10049669
theorem B1956713 : Blo 1303970 1956713 := bstep (se 2 (by rfl) ⟨733767, by rfl⟩ : syracuseStep 1956713 = 1467535) B1467535
theorem B3767147 : Blo 1303970 3767147 := bstep (se 1 (by rfl) ⟨2825360, by rfl⟩ : syracuseStep 3767147 = 5650721) B5650721
theorem B3136363 : Blo 1303970 3136363 := bstep (se 1 (by rfl) ⟨2352272, by rfl⟩ : syracuseStep 3136363 = 4704545) B4704545
theorem B31742837 : Blo 1303970 31742837 := bstep (se 5 (by rfl) ⟨1487945, by rfl⟩ : syracuseStep 31742837 = 2975891) B2975891
theorem B2202511 : Blo 1303970 2202511 := bstep (se 1 (by rfl) ⟨1651883, by rfl⟩ : syracuseStep 2202511 = 3303767) B3303767
theorem B1956791 : Blo 1303970 1956791 := bstep (se 1 (by rfl) ⟨1467593, by rfl⟩ : syracuseStep 1956791 = 2935187) B2935187
theorem B1956827 : Blo 1303970 1956827 := bstep (se 1 (by rfl) ⟨1467620, by rfl⟩ : syracuseStep 1956827 = 2935241) B2935241
theorem B18824177 : Blo 1303970 18824177 := bstep (se 2 (by rfl) ⟨7059066, by rfl⟩ : syracuseStep 18824177 = 14118133) B14118133
theorem B4406291 : Blo 1303970 4406291 := bstep (se 1 (by rfl) ⟨3304718, by rfl⟩ : syracuseStep 4406291 = 6609437) B6609437
theorem B3718163 : Blo 1303970 3718163 := bstep (se 1 (by rfl) ⟨2788622, by rfl⟩ : syracuseStep 3718163 = 5577245) B5577245
theorem B3349561 : Blo 1303970 3349561 := bstep (se 2 (by rfl) ⟨1256085, by rfl⟩ : syracuseStep 3349561 = 2512171) B2512171
theorem B4406615 : Blo 1303970 4406615 := bstep (se 1 (by rfl) ⟨3304961, by rfl⟩ : syracuseStep 4406615 = 6609923) B6609923
theorem B1957295 : Blo 1303970 1957295 := bstep (se 1 (by rfl) ⟨1467971, by rfl⟩ : syracuseStep 1957295 = 2935943) B2935943
theorem B8363483 : Blo 1303970 8363483 := bstep (se 1 (by rfl) ⟨6272612, by rfl⟩ : syracuseStep 8363483 = 12545225) B12545225
theorem B3718619 : Blo 1303970 3718619 := bstep (se 1 (by rfl) ⟨2788964, by rfl⟩ : syracuseStep 3718619 = 5577929) B5577929
theorem B3300851 : Blo 1303970 3300851 := bstep (se 1 (by rfl) ⟨2475638, by rfl⟩ : syracuseStep 3300851 = 4951277) B4951277
theorem B1957385 : Blo 1303970 1957385 := bstep (se 2 (by rfl) ⟨734019, by rfl⟩ : syracuseStep 1957385 = 1468039) B1468039
theorem B4955681 : Blo 1303970 4955681 := bstep (se 2 (by rfl) ⟨1858380, by rfl⟩ : syracuseStep 4955681 = 3716761) B3716761
theorem B1957415 : Blo 1303970 1957415 := bstep (se 1 (by rfl) ⟨1468061, by rfl⟩ : syracuseStep 1957415 = 2936123) B2936123
theorem B2203193 : Blo 1303970 2203193 := bstep (se 2 (by rfl) ⟨826197, by rfl⟩ : syracuseStep 2203193 = 1652395) B1652395
theorem B16719479 : Blo 1303970 16719479 := bstep (se 1 (by rfl) ⟨12539609, by rfl⟩ : syracuseStep 16719479 = 25079219) B25079219
theorem B1957499 : Blo 1303970 1957499 := bstep (se 1 (by rfl) ⟨1468124, by rfl⟩ : syracuseStep 1957499 = 2936249) B2936249
theorem B6610571 : Blo 1303970 6610571 := bstep (se 1 (by rfl) ⟨4957928, by rfl⟩ : syracuseStep 6610571 = 9915857) B9915857
theorem B4955863 : Blo 1303970 4955863 := bstep (se 1 (by rfl) ⟨3716897, by rfl⟩ : syracuseStep 4955863 = 7433795) B7433795
theorem B1957625 : Blo 1303970 1957625 := bstep (se 2 (by rfl) ⟨734109, by rfl⟩ : syracuseStep 1957625 = 1468219) B1468219
theorem B71376709 : Blo 1303970 71376709 := bstep (se 4 (by rfl) ⟨6691566, by rfl⟩ : syracuseStep 71376709 = 13383133) B13383133
theorem B1957727 : Blo 1303970 1957727 := bstep (se 1 (by rfl) ⟨1468295, by rfl⟩ : syracuseStep 1957727 = 2936591) B2936591
theorem B1957739 : Blo 1303970 1957739 := bstep (se 1 (by rfl) ⟨1468304, by rfl⟩ : syracuseStep 1957739 = 2936609) B2936609
theorem B3301307 : Blo 1303970 3301307 := bstep (se 1 (by rfl) ⟨2475980, by rfl⟩ : syracuseStep 3301307 = 4951961) B4951961
theorem B28614707 : Blo 1303970 28614707 := bstep (se 1 (by rfl) ⟨21461030, by rfl⟩ : syracuseStep 28614707 = 42922061) B42922061
theorem B2203753 : Blo 1303970 2203753 := bstep (se 2 (by rfl) ⟨826407, by rfl⟩ : syracuseStep 2203753 = 1652815) B1652815
theorem B25100441 : Blo 1303970 25100441 := bstep (se 2 (by rfl) ⟨9412665, by rfl⟩ : syracuseStep 25100441 = 18825331) B18825331
theorem B1958153 : Blo 1303970 1958153 := bstep (se 2 (by rfl) ⟨734307, by rfl⟩ : syracuseStep 1958153 = 1468615) B1468615
theorem B1958255 : Blo 1303970 1958255 := bstep (se 1 (by rfl) ⟨1468691, by rfl⟩ : syracuseStep 1958255 = 2937383) B2937383
theorem B3301843 : Blo 1303970 3301843 := bstep (se 1 (by rfl) ⟨2476382, by rfl⟩ : syracuseStep 3301843 = 4952765) B4952765
theorem B1958471 : Blo 1303970 1958471 := bstep (se 1 (by rfl) ⟨1468853, by rfl⟩ : syracuseStep 1958471 = 2937707) B2937707
theorem B1958507 : Blo 1303970 1958507 := bstep (se 1 (by rfl) ⟨1468880, by rfl⟩ : syracuseStep 1958507 = 2937761) B2937761
theorem B12239531 : Blo 1303970 12239531 := bstep (se 1 (by rfl) ⟨9179648, by rfl⟩ : syracuseStep 12239531 = 18359297) B18359297
theorem B1467103 : Blo 1303970 1467103 := bstep (se 1 (by rfl) ⟨1100327, by rfl⟩ : syracuseStep 1467103 = 2200655) B2200655
theorem B16712507 : Blo 1303970 16712507 := bstep (se 1 (by rfl) ⟨12534380, by rfl⟩ : syracuseStep 16712507 = 25068761) B25068761
theorem B1958735 : Blo 1303970 1958735 := bstep (se 1 (by rfl) ⟨1469051, by rfl⟩ : syracuseStep 1958735 = 2938103) B2938103
theorem B2827163 : Blo 1303970 2827163 := bstep (se 1 (by rfl) ⟨2120372, by rfl⟩ : syracuseStep 2827163 = 4240745) B4240745
theorem B12534689 : Blo 1303970 12534689 := bstep (se 2 (by rfl) ⟨4700508, by rfl⟩ : syracuseStep 12534689 = 9401017) B9401017
theorem B8356769 : Blo 1303970 8356769 := bstep (se 2 (by rfl) ⟨3133788, by rfl⟩ : syracuseStep 8356769 = 6267577) B6267577
theorem B1393615 : Blo 1303970 1393615 := bstep (se 1 (by rfl) ⟨1045211, by rfl⟩ : syracuseStep 1393615 = 2090423) B2090423
theorem B6603767 : Blo 1303970 6603767 := bstep (se 1 (by rfl) ⟨4952825, by rfl⟩ : syracuseStep 6603767 = 9905651) B9905651
theorem B9528463 : Blo 1303970 9528463 := bstep (se 1 (by rfl) ⟨7146347, by rfl⟩ : syracuseStep 9528463 = 14292695) B14292695
theorem B3302633 : Blo 1303970 3302633 := bstep (se 2 (by rfl) ⟨1238487, by rfl⟩ : syracuseStep 3302633 = 2476975) B2476975
theorem B1467679 : Blo 1303970 1467679 := bstep (se 1 (by rfl) ⟨1100759, by rfl⟩ : syracuseStep 1467679 = 2201519) B2201519
theorem B5948777 : Blo 1303970 5948777 := bstep (se 2 (by rfl) ⟨2230791, by rfl⟩ : syracuseStep 5948777 = 4461583) B4461583
theorem B2786683 : Blo 1303970 2786683 := bstep (se 1 (by rfl) ⟨2090012, by rfl⟩ : syracuseStep 2786683 = 4180025) B4180025
theorem B3966347 : Blo 1303970 3966347 := bstep (se 1 (by rfl) ⟨2974760, by rfl⟩ : syracuseStep 3966347 = 5949521) B5949521
theorem B3302795 : Blo 1303970 3302795 := bstep (se 1 (by rfl) ⟨2477096, by rfl⟩ : syracuseStep 3302795 = 4954193) B4954193
theorem B4466081 : Blo 1303970 4466081 := bstep (se 2 (by rfl) ⟨1674780, by rfl⟩ : syracuseStep 4466081 = 3349561) B3349561
theorem B1303975 : Blo 1303970 1303975 := bstep (se 1 (by rfl) ⟨977981, by rfl⟩ : syracuseStep 1303975 = 1955963) B1955963
theorem B2934215 : Blo 1303970 2934215 := bstep (se 1 (by rfl) ⟨2200661, by rfl⟩ : syracuseStep 2934215 = 4401323) B4401323
theorem B1394119 : Blo 1303970 1394119 := bstep (se 1 (by rfl) ⟨1045589, by rfl⟩ : syracuseStep 1394119 = 2091179) B2091179
theorem B1304059 : Blo 1303970 1304059 := bstep (se 1 (by rfl) ⟨978044, by rfl⟩ : syracuseStep 1304059 = 1956089) B1956089
theorem B9913913 : Blo 1303970 9913913 := bstep (se 2 (by rfl) ⟨3717717, by rfl⟩ : syracuseStep 9913913 = 7435435) B7435435
theorem B15074873 : Blo 1303970 15074873 := bstep (se 2 (by rfl) ⟨5653077, by rfl⟩ : syracuseStep 15074873 = 11306155) B11306155
theorem B1304127 : Blo 1303970 1304127 := bstep (se 1 (by rfl) ⟨978095, by rfl⟩ : syracuseStep 1304127 = 1956191) B1956191
theorem B1467967 : Blo 1303970 1467967 := bstep (se 1 (by rfl) ⟨1100975, by rfl⟩ : syracuseStep 1467967 = 2201951) B2201951
theorem B1304135 : Blo 1303970 1304135 := bstep (se 1 (by rfl) ⟨978101, by rfl⟩ : syracuseStep 1304135 = 1956203) B1956203
theorem B1304287 : Blo 1303970 1304287 := bstep (se 1 (by rfl) ⟨978215, by rfl⟩ : syracuseStep 1304287 = 1956431) B1956431
theorem B2934575 : Blo 1303970 2934575 := bstep (se 1 (by rfl) ⟨2200931, by rfl⟩ : syracuseStep 2934575 = 4401863) B4401863
theorem B1304367 : Blo 1303970 1304367 := bstep (se 1 (by rfl) ⟨978275, by rfl⟩ : syracuseStep 1304367 = 1956551) B1956551
theorem B2787119 : Blo 1303970 2787119 := bstep (se 1 (by rfl) ⟨2090339, by rfl⟩ : syracuseStep 2787119 = 4180679) B4180679
theorem B4179767 : Blo 1303970 4179767 := bstep (se 1 (by rfl) ⟨3134825, by rfl⟩ : syracuseStep 4179767 = 6269651) B6269651
theorem B4466519 : Blo 1303970 4466519 := bstep (se 1 (by rfl) ⟨3349889, by rfl⟩ : syracuseStep 4466519 = 6699779) B6699779
theorem B1304475 : Blo 1303970 1304475 := bstep (se 1 (by rfl) ⟨978356, by rfl⟩ : syracuseStep 1304475 = 1956713) B1956713
theorem B21161891 : Blo 1303970 21161891 := bstep (se 1 (by rfl) ⟨15871418, by rfl⟩ : syracuseStep 21161891 = 31742837) B31742837
theorem B1304527 : Blo 1303970 1304527 := bstep (se 1 (by rfl) ⟨978395, by rfl⟩ : syracuseStep 1304527 = 1956791) B1956791
theorem B1304551 : Blo 1303970 1304551 := bstep (se 1 (by rfl) ⟨978413, by rfl⟩ : syracuseStep 1304551 = 1956827) B1956827
theorem B1304863 : Blo 1303970 1304863 := bstep (se 1 (by rfl) ⟨978647, by rfl⟩ : syracuseStep 1304863 = 1957295) B1957295
theorem B1304923 : Blo 1303970 1304923 := bstep (se 1 (by rfl) ⟨978692, by rfl⟩ : syracuseStep 1304923 = 1957385) B1957385
theorem B3303787 : Blo 1303970 3303787 := bstep (se 1 (by rfl) ⟨2477840, by rfl⟩ : syracuseStep 3303787 = 4955681) B4955681
theorem B2787691 : Blo 1303970 2787691 := bstep (se 1 (by rfl) ⟨2090768, by rfl⟩ : syracuseStep 2787691 = 4181537) B4181537
theorem B2935151 : Blo 1303970 2935151 := bstep (se 1 (by rfl) ⟨2201363, by rfl⟩ : syracuseStep 2935151 = 4402727) B4402727
theorem B1304943 : Blo 1303970 1304943 := bstep (se 1 (by rfl) ⟨978707, by rfl⟩ : syracuseStep 1304943 = 1957415) B1957415
theorem B1468795 : Blo 1303970 1468795 := bstep (se 1 (by rfl) ⟨1101596, by rfl⟩ : syracuseStep 1468795 = 2203193) B2203193
theorem B17844623 : Blo 1303970 17844623 := bstep (se 1 (by rfl) ⟨13383467, by rfl⟩ : syracuseStep 17844623 = 26766935) B26766935
theorem B1304999 : Blo 1303970 1304999 := bstep (se 1 (by rfl) ⟨978749, by rfl⟩ : syracuseStep 1304999 = 1957499) B1957499
theorem B95168945 : Blo 1303970 95168945 := bstep (se 2 (by rfl) ⟨35688354, by rfl⟩ : syracuseStep 95168945 = 71376709) B71376709
theorem B2935223 : Blo 1303970 2935223 := bstep (se 1 (by rfl) ⟨2201417, by rfl⟩ : syracuseStep 2935223 = 4402835) B4402835
theorem B1305083 : Blo 1303970 1305083 := bstep (se 1 (by rfl) ⟨978812, by rfl⟩ : syracuseStep 1305083 = 1957625) B1957625
theorem B1305151 : Blo 1303970 1305151 := bstep (se 1 (by rfl) ⟨978863, by rfl⟩ : syracuseStep 1305151 = 1957727) B1957727
theorem B2935367 : Blo 1303970 2935367 := bstep (se 1 (by rfl) ⟨2201525, by rfl⟩ : syracuseStep 2935367 = 4403051) B4403051
theorem B1305159 : Blo 1303970 1305159 := bstep (se 1 (by rfl) ⟨978869, by rfl⟩ : syracuseStep 1305159 = 1957739) B1957739
theorem B2935403 : Blo 1303970 2935403 := bstep (se 1 (by rfl) ⟨2201552, by rfl⟩ : syracuseStep 2935403 = 4403105) B4403105
theorem B2787947 : Blo 1303970 2787947 := bstep (se 1 (by rfl) ⟨2090960, by rfl⟩ : syracuseStep 2787947 = 4181921) B4181921
theorem B3304111 : Blo 1303970 3304111 := bstep (se 1 (by rfl) ⟨2478083, by rfl⟩ : syracuseStep 3304111 = 4956167) B4956167
theorem B2788015 : Blo 1303970 2788015 := bstep (se 1 (by rfl) ⟨2091011, by rfl⟩ : syracuseStep 2788015 = 4182023) B4182023
theorem B57191093 : Blo 1303970 57191093 := bstep (se 5 (by rfl) ⟨2680832, by rfl⟩ : syracuseStep 57191093 = 5361665) B5361665
theorem B28240595 : Blo 1303970 28240595 := bstep (se 1 (by rfl) ⟨21180446, by rfl⟩ : syracuseStep 28240595 = 42360893) B42360893
theorem B1305311 : Blo 1303970 1305311 := bstep (se 1 (by rfl) ⟨978983, by rfl⟩ : syracuseStep 1305311 = 1957967) B1957967
theorem B1305391 : Blo 1303970 1305391 := bstep (se 1 (by rfl) ⟨979043, by rfl⟩ : syracuseStep 1305391 = 1958087) B1958087
theorem B8366915 : Blo 1303970 8366915 := bstep (se 1 (by rfl) ⟨6275186, by rfl⟩ : syracuseStep 8366915 = 12550373) B12550373
theorem B6605711 : Blo 1303970 6605711 := bstep (se 1 (by rfl) ⟨4954283, by rfl⟩ : syracuseStep 6605711 = 9908567) B9908567
theorem B1305499 : Blo 1303970 1305499 := bstep (se 1 (by rfl) ⟨979124, by rfl⟩ : syracuseStep 1305499 = 1958249) B1958249
theorem B1305551 : Blo 1303970 1305551 := bstep (se 1 (by rfl) ⟨979163, by rfl⟩ : syracuseStep 1305551 = 1958327) B1958327
theorem B1305575 : Blo 1303970 1305575 := bstep (se 1 (by rfl) ⟨979181, by rfl⟩ : syracuseStep 1305575 = 1958363) B1958363
theorem B3304435 : Blo 1303970 3304435 := bstep (se 1 (by rfl) ⟨2478326, by rfl⟩ : syracuseStep 3304435 = 4956653) B4956653
theorem B2935799 : Blo 1303970 2935799 := bstep (se 1 (by rfl) ⟨2201849, by rfl⟩ : syracuseStep 2935799 = 4403699) B4403699
theorem B2788391 : Blo 1303970 2788391 := bstep (se 1 (by rfl) ⟨2091293, by rfl⟩ : syracuseStep 2788391 = 4182587) B4182587
theorem B3714187 : Blo 1303970 3714187 := bstep (se 1 (by rfl) ⟨2785640, by rfl⟩ : syracuseStep 3714187 = 5571281) B5571281
theorem B1305887 : Blo 1303970 1305887 := bstep (se 1 (by rfl) ⟨979415, by rfl⟩ : syracuseStep 1305887 = 1958831) B1958831
theorem B26791229 : Blo 1303970 26791229 := bstep (se 3 (by rfl) ⟨5023355, by rfl⟩ : syracuseStep 26791229 = 10046711) B10046711
theorem B1305947 : Blo 1303970 1305947 := bstep (se 1 (by rfl) ⟨979460, by rfl⟩ : syracuseStep 1305947 = 1958921) B1958921
theorem B2936159 : Blo 1303970 2936159 := bstep (se 1 (by rfl) ⟨2202119, by rfl⟩ : syracuseStep 2936159 = 4404239) B4404239
theorem B1305967 : Blo 1303970 1305967 := bstep (se 1 (by rfl) ⟨979475, by rfl⟩ : syracuseStep 1305967 = 1958951) B1958951
theorem B4402619 : Blo 1303970 4402619 := bstep (se 1 (by rfl) ⟨3301964, by rfl⟩ : syracuseStep 4402619 = 6603929) B6603929
theorem B8359433 : Blo 1303970 8359433 := bstep (se 2 (by rfl) ⟨3134787, by rfl⟩ : syracuseStep 8359433 = 6269575) B6269575
theorem B2788921 : Blo 1303970 2788921 := bstep (se 2 (by rfl) ⟨1045845, by rfl⟩ : syracuseStep 2788921 = 2091691) B2091691
theorem B5574253 : Blo 1303970 5574253 := bstep (se 3 (by rfl) ⟨1045172, by rfl⟩ : syracuseStep 5574253 = 2090345) B2090345
theorem B4181665 : Blo 1303970 4181665 := bstep (se 2 (by rfl) ⟨1568124, by rfl⟩ : syracuseStep 4181665 = 3136249) B3136249
theorem B2936555 : Blo 1303970 2936555 := bstep (se 1 (by rfl) ⟨2202416, by rfl⟩ : syracuseStep 2936555 = 4404833) B4404833
theorem B2477803 : Blo 1303970 2477803 := bstep (se 1 (by rfl) ⟨1858352, by rfl⟩ : syracuseStep 2477803 = 3716705) B3716705
theorem B3305195 : Blo 1303970 3305195 := bstep (se 1 (by rfl) ⟨2478896, by rfl⟩ : syracuseStep 3305195 = 4957793) B4957793
theorem B6270767 : Blo 1303970 6270767 := bstep (se 1 (by rfl) ⟨4703075, by rfl⟩ : syracuseStep 6270767 = 9406151) B9406151
theorem B4181807 : Blo 1303970 4181807 := bstep (se 1 (by rfl) ⟨3136355, by rfl⟩ : syracuseStep 4181807 = 6272711) B6272711
theorem B2936681 : Blo 1303970 2936681 := bstep (se 2 (by rfl) ⟨1101255, by rfl⟩ : syracuseStep 2936681 = 2202511) B2202511
theorem B1651195 : Blo 1303970 1651195 := bstep (se 1 (by rfl) ⟨1238396, by rfl⟩ : syracuseStep 1651195 = 2476793) B2476793
theorem B2511431 : Blo 1303970 2511431 := bstep (se 1 (by rfl) ⟨1883573, by rfl⟩ : syracuseStep 2511431 = 3767147) B3767147
theorem B2716343 : Blo 1303970 2716343 := bstep (se 1 (by rfl) ⟨2037257, by rfl⟩ : syracuseStep 2716343 = 4074515) B4074515
theorem B2937527 : Blo 1303970 2937527 := bstep (se 1 (by rfl) ⟨2203145, by rfl⟩ : syracuseStep 2937527 = 4406291) B4406291
theorem B2478775 : Blo 1303970 2478775 := bstep (se 1 (by rfl) ⟨1859081, by rfl⟩ : syracuseStep 2478775 = 3718163) B3718163
theorem B1651423 : Blo 1303970 1651423 := bstep (se 1 (by rfl) ⟨1238567, by rfl⟩ : syracuseStep 1651423 = 2477135) B2477135
theorem B3715919 : Blo 1303970 3715919 := bstep (se 1 (by rfl) ⟨2786939, by rfl⟩ : syracuseStep 3715919 = 5573879) B5573879
theorem B2937743 : Blo 1303970 2937743 := bstep (se 1 (by rfl) ⟨2203307, by rfl⟩ : syracuseStep 2937743 = 4406615) B4406615
theorem B7934885 : Blo 1303970 7934885 := bstep (se 4 (by rfl) ⟨743895, by rfl⟩ : syracuseStep 7934885 = 1487791) B1487791
theorem B6607817 : Blo 1303970 6607817 := bstep (se 2 (by rfl) ⟨2477931, by rfl⟩ : syracuseStep 6607817 = 4955863) B4955863
theorem B16962509 : Blo 1303970 16962509 := bstep (se 3 (by rfl) ⟨3180470, by rfl⟩ : syracuseStep 16962509 = 6360941) B6360941
theorem B5575655 : Blo 1303970 5575655 := bstep (se 1 (by rfl) ⟨4181741, by rfl⟩ : syracuseStep 5575655 = 8363483) B8363483
theorem B2479079 : Blo 1303970 2479079 := bstep (se 1 (by rfl) ⟨1859309, by rfl⟩ : syracuseStep 2479079 = 3718619) B3718619
theorem B2200567 : Blo 1303970 2200567 := bstep (se 1 (by rfl) ⟨1650425, by rfl⟩ : syracuseStep 2200567 = 3300851) B3300851
theorem B11146319 : Blo 1303970 11146319 := bstep (se 1 (by rfl) ⟨8359739, by rfl⟩ : syracuseStep 11146319 = 16719479) B16719479
theorem B2200871 : Blo 1303970 2200871 := bstep (se 1 (by rfl) ⟨1650653, by rfl⟩ : syracuseStep 2200871 = 3301307) B3301307
theorem B11154793 : Blo 1303970 11154793 := bstep (se 2 (by rfl) ⟨4183047, by rfl⟩ : syracuseStep 11154793 = 8366095) B8366095
theorem B23811509 : Blo 1303970 23811509 := bstep (se 5 (by rfl) ⟨1116164, by rfl⟩ : syracuseStep 23811509 = 2232329) B2232329
theorem B1652167 : Blo 1303970 1652167 := bstep (se 1 (by rfl) ⟨1239125, by rfl⟩ : syracuseStep 1652167 = 2478251) B2478251
theorem B2643617 : Blo 1303970 2643617 := bstep (se 2 (by rfl) ⟨991356, by rfl⟩ : syracuseStep 2643617 = 1982713) B1982713
theorem B7435961 : Blo 1303970 7435961 := bstep (se 2 (by rfl) ⟨2788485, by rfl⟩ : syracuseStep 7435961 = 5576971) B5576971
theorem B1857259 : Blo 1303970 1857259 := bstep (se 1 (by rfl) ⟨1392944, by rfl⟩ : syracuseStep 1857259 = 2785889) B2785889
theorem B2201323 : Blo 1303970 2201323 := bstep (se 1 (by rfl) ⟨1650992, by rfl⟩ : syracuseStep 2201323 = 3301985) B3301985
theorem B4462391 : Blo 1303970 4462391 := bstep (se 1 (by rfl) ⟨3346793, by rfl⟩ : syracuseStep 4462391 = 6693587) B6693587
theorem B3135287 : Blo 1303970 3135287 := bstep (se 1 (by rfl) ⟨2351465, by rfl⟩ : syracuseStep 3135287 = 4702931) B4702931
theorem B1857487 : Blo 1303970 1857487 := bstep (se 1 (by rfl) ⟨1393115, by rfl⟩ : syracuseStep 1857487 = 2786231) B2786231
theorem B17848349 : Blo 1303970 17848349 := bstep (se 3 (by rfl) ⟨3346565, by rfl⟩ : syracuseStep 17848349 = 6693131) B6693131
theorem B1956263 : Blo 1303970 1956263 := bstep (se 1 (by rfl) ⟨1467197, by rfl⟩ : syracuseStep 1956263 = 2934395) B2934395
theorem B1956347 : Blo 1303970 1956347 := bstep (se 1 (by rfl) ⟨1467260, by rfl⟩ : syracuseStep 1956347 = 2934521) B2934521
theorem B7428671 : Blo 1303970 7428671 := bstep (se 1 (by rfl) ⟨5571503, by rfl⟩ : syracuseStep 7428671 = 11143007) B11143007
theorem B5577295 : Blo 1303970 5577295 := bstep (se 1 (by rfl) ⟨4182971, by rfl⟩ : syracuseStep 5577295 = 8365943) B8365943
theorem B1956473 : Blo 1303970 1956473 := bstep (se 2 (by rfl) ⟨733677, by rfl⟩ : syracuseStep 1956473 = 1467355) B1467355
theorem B1956527 : Blo 1303970 1956527 := bstep (se 1 (by rfl) ⟨1467395, by rfl⟩ : syracuseStep 1956527 = 2934791) B2934791
theorem B2202295 : Blo 1303970 2202295 := bstep (se 1 (by rfl) ⟨1651721, by rfl⟩ : syracuseStep 2202295 = 3303443) B3303443
theorem B1956575 : Blo 1303970 1956575 := bstep (se 1 (by rfl) ⟨1467431, by rfl⟩ : syracuseStep 1956575 = 2934863) B2934863
theorem B1956839 : Blo 1303970 1956839 := bstep (se 1 (by rfl) ⟨1467629, by rfl⟩ : syracuseStep 1956839 = 2935259) B2935259
theorem B2202599 : Blo 1303970 2202599 := bstep (se 1 (by rfl) ⟨1651949, by rfl⟩ : syracuseStep 2202599 = 3303899) B3303899
theorem B183196853 : Blo 1303970 183196853 := bstep (se 5 (by rfl) ⟨8587352, by rfl⟩ : syracuseStep 183196853 = 17174705) B17174705
theorem B40180931 : Blo 1303970 40180931 := bstep (se 1 (by rfl) ⟨30135698, by rfl⟩ : syracuseStep 40180931 = 60271397) B60271397
theorem B16727269 : Blo 1303970 16727269 := bstep (se 4 (by rfl) ⟨1568181, by rfl⟩ : syracuseStep 16727269 = 3136363) B3136363
theorem B1957097 : Blo 1303970 1957097 := bstep (se 2 (by rfl) ⟨733911, by rfl⟩ : syracuseStep 1957097 = 1467823) B1467823
theorem B1957151 : Blo 1303970 1957151 := bstep (se 1 (by rfl) ⟨1467863, by rfl⟩ : syracuseStep 1957151 = 2935727) B2935727
theorem B12549451 : Blo 1303970 12549451 := bstep (se 1 (by rfl) ⟨9412088, by rfl⟩ : syracuseStep 12549451 = 18824177) B18824177
theorem B1957319 : Blo 1303970 1957319 := bstep (se 1 (by rfl) ⟨1467989, by rfl⟩ : syracuseStep 1957319 = 2935979) B2935979
theorem B5291513 : Blo 1303970 5291513 := bstep (se 2 (by rfl) ⟨1984317, by rfl⟩ : syracuseStep 5291513 = 3968635) B3968635
theorem B4406777 : Blo 1303970 4406777 := bstep (se 2 (by rfl) ⟨1652541, by rfl⟩ : syracuseStep 4406777 = 3305083) B3305083
theorem B3300871 : Blo 1303970 3300871 := bstep (se 1 (by rfl) ⟨2475653, by rfl⟩ : syracuseStep 3300871 = 4951307) B4951307
theorem B16727633 : Blo 1303970 16727633 := bstep (se 2 (by rfl) ⟨6272862, by rfl⟩ : syracuseStep 16727633 = 12545725) B12545725
theorem B9911969 : Blo 1303970 9911969 := bstep (se 2 (by rfl) ⟨3716988, by rfl⟩ : syracuseStep 9911969 = 7433977) B7433977
theorem B4407047 : Blo 1303970 4407047 := bstep (se 1 (by rfl) ⟨3305285, by rfl⟩ : syracuseStep 4407047 = 6610571) B6610571
theorem B1957673 : Blo 1303970 1957673 := bstep (se 2 (by rfl) ⟨734127, by rfl⟩ : syracuseStep 1957673 = 1468255) B1468255
theorem B1957679 : Blo 1303970 1957679 := bstep (se 1 (by rfl) ⟨1468259, by rfl⟩ : syracuseStep 1957679 = 2936519) B2936519
theorem B3301175 : Blo 1303970 3301175 := bstep (se 1 (by rfl) ⟨2475881, by rfl⟩ : syracuseStep 3301175 = 4951763) B4951763
theorem B1859383 : Blo 1303970 1859383 := bstep (se 1 (by rfl) ⟨1394537, by rfl⟩ : syracuseStep 1859383 = 2789075) B2789075
theorem B4702009 : Blo 1303970 4702009 := bstep (se 2 (by rfl) ⟨1763253, by rfl⟩ : syracuseStep 4702009 = 3526507) B3526507
theorem B9404221 : Blo 1303970 9404221 := bstep (se 3 (by rfl) ⟨1763291, by rfl⟩ : syracuseStep 9404221 = 3526583) B3526583
theorem B4407101 : Blo 1303970 4407101 := bstep (se 3 (by rfl) ⟨826331, by rfl⟩ : syracuseStep 4407101 = 1652663) B1652663
theorem B8159687 : Blo 1303970 8159687 := bstep (se 1 (by rfl) ⟨6119765, by rfl⟩ : syracuseStep 8159687 = 12239531) B12239531
theorem B1810895 : Blo 1303970 1810895 := bstep (se 1 (by rfl) ⟨1358171, by rfl⟩ : syracuseStep 1810895 = 2716343) B2716343
theorem B1958351 : Blo 1303970 1958351 := bstep (se 1 (by rfl) ⟨1468763, by rfl⟩ : syracuseStep 1958351 = 2937527) B2937527
theorem B1958393 : Blo 1303970 1958393 := bstep (se 2 (by rfl) ⟨734397, by rfl⟩ : syracuseStep 1958393 = 1468795) B1468795
theorem B11141671 : Blo 1303970 11141671 := bstep (se 1 (by rfl) ⟨8356253, by rfl⟩ : syracuseStep 11141671 = 16712507) B16712507
theorem B1958495 : Blo 1303970 1958495 := bstep (se 1 (by rfl) ⟨1468871, by rfl⟩ : syracuseStep 1958495 = 2937743) B2937743
theorem B8356459 : Blo 1303970 8356459 := bstep (se 1 (by rfl) ⟨6267344, by rfl⟩ : syracuseStep 8356459 = 12534689) B12534689
theorem B5571179 : Blo 1303970 5571179 := bstep (se 1 (by rfl) ⟨4178384, by rfl⟩ : syracuseStep 5571179 = 8356769) B8356769
theorem B7430879 : Blo 1303970 7430879 := bstep (se 1 (by rfl) ⟨5573159, by rfl⟩ : syracuseStep 7430879 = 11146319) B11146319
theorem B1467247 : Blo 1303970 1467247 := bstep (se 1 (by rfl) ⟨1100435, by rfl⟩ : syracuseStep 1467247 = 2200871) B2200871
theorem B3965851 : Blo 1303970 3965851 := bstep (se 1 (by rfl) ⟨2974388, by rfl⟩ : syracuseStep 3965851 = 5948777) B5948777
theorem B1762411 : Blo 1303970 1762411 := bstep (se 1 (by rfl) ⟨1321808, by rfl⟩ : syracuseStep 1762411 = 2643617) B2643617
theorem B4957307 : Blo 1303970 4957307 := bstep (se 1 (by rfl) ⟨3717980, by rfl⟩ : syracuseStep 4957307 = 7435961) B7435961
theorem B63497357 : Blo 1303970 63497357 := bstep (se 3 (by rfl) ⟨11905754, by rfl⟩ : syracuseStep 63497357 = 23811509) B23811509
theorem B14107927 : Blo 1303970 14107927 := bstep (se 1 (by rfl) ⟨10580945, by rfl⟩ : syracuseStep 14107927 = 21161891) B21161891
theorem B2934089 : Blo 1303970 2934089 := bstep (se 2 (by rfl) ⟨1100283, by rfl⟩ : syracuseStep 2934089 = 2200567) B2200567
theorem B11896415 : Blo 1303970 11896415 := bstep (se 1 (by rfl) ⟨8922311, by rfl⟩ : syracuseStep 11896415 = 17844623) B17844623
theorem B1304175 : Blo 1303970 1304175 := bstep (se 1 (by rfl) ⟨978131, by rfl⟩ : syracuseStep 1304175 = 1956263) B1956263
theorem B1304231 : Blo 1303970 1304231 := bstep (se 1 (by rfl) ⟨978173, by rfl⟩ : syracuseStep 1304231 = 1956347) B1956347
theorem B1304315 : Blo 1303970 1304315 := bstep (se 1 (by rfl) ⟨978236, by rfl⟩ : syracuseStep 1304315 = 1956473) B1956473
theorem B1304351 : Blo 1303970 1304351 := bstep (se 1 (by rfl) ⟨978263, by rfl⟩ : syracuseStep 1304351 = 1956527) B1956527
theorem B38127395 : Blo 1303970 38127395 := bstep (se 1 (by rfl) ⟨28595546, by rfl⟩ : syracuseStep 38127395 = 57191093) B57191093
theorem B18827063 : Blo 1303970 18827063 := bstep (se 1 (by rfl) ⟨14120297, by rfl⟩ : syracuseStep 18827063 = 28240595) B28240595
theorem B1304383 : Blo 1303970 1304383 := bstep (se 1 (by rfl) ⟨978287, by rfl⟩ : syracuseStep 1304383 = 1956575) B1956575
theorem B1304559 : Blo 1303970 1304559 := bstep (se 1 (by rfl) ⟨978419, by rfl⟩ : syracuseStep 1304559 = 1956839) B1956839
theorem B1468399 : Blo 1303970 1468399 := bstep (se 1 (by rfl) ⟨1101299, by rfl⟩ : syracuseStep 1468399 = 2202599) B2202599
theorem B4401161 : Blo 1303970 4401161 := bstep (se 2 (by rfl) ⟨1650435, by rfl⟩ : syracuseStep 4401161 = 3300871) B3300871
theorem B7432337 : Blo 1303970 7432337 := bstep (se 2 (by rfl) ⟨2787126, by rfl⟩ : syracuseStep 7432337 = 5574253) B5574253
theorem B1304731 : Blo 1303970 1304731 := bstep (se 1 (by rfl) ⟨978548, by rfl⟩ : syracuseStep 1304731 = 1957097) B1957097
theorem B1304767 : Blo 1303970 1304767 := bstep (se 1 (by rfl) ⟨978575, by rfl⟩ : syracuseStep 1304767 = 1957151) B1957151
theorem B17860819 : Blo 1303970 17860819 := bstep (se 1 (by rfl) ⟨13395614, by rfl⟩ : syracuseStep 17860819 = 26791229) B26791229
theorem B2935079 : Blo 1303970 2935079 := bstep (se 1 (by rfl) ⟨2201309, by rfl⟩ : syracuseStep 2935079 = 4402619) B4402619
theorem B1304879 : Blo 1303970 1304879 := bstep (se 1 (by rfl) ⟨978659, by rfl⟩ : syracuseStep 1304879 = 1957319) B1957319
theorem B2476345 : Blo 1303970 2476345 := bstep (se 2 (by rfl) ⟨928629, by rfl⟩ : syracuseStep 2476345 = 1857259) B1857259
theorem B2935097 : Blo 1303970 2935097 := bstep (se 2 (by rfl) ⟨1100661, by rfl⟩ : syracuseStep 2935097 = 2201323) B2201323
theorem B3303737 : Blo 1303970 3303737 := bstep (se 2 (by rfl) ⟨1238901, by rfl⟩ : syracuseStep 3303737 = 2477803) B2477803
theorem B5572955 : Blo 1303970 5572955 := bstep (se 1 (by rfl) ⟨4179716, by rfl⟩ : syracuseStep 5572955 = 8359433) B8359433
theorem B11151755 : Blo 1303970 11151755 := bstep (se 1 (by rfl) ⟨8363816, by rfl⟩ : syracuseStep 11151755 = 16727633) B16727633
theorem B7539101 : Blo 1303970 7539101 := bstep (se 3 (by rfl) ⟨1413581, by rfl⟩ : syracuseStep 7539101 = 2827163) B2827163
theorem B6269345 : Blo 1303970 6269345 := bstep (se 2 (by rfl) ⟨2351004, by rfl⟩ : syracuseStep 6269345 = 4702009) B4702009
theorem B1305115 : Blo 1303970 1305115 := bstep (se 1 (by rfl) ⟨978836, by rfl⟩ : syracuseStep 1305115 = 1957673) B1957673
theorem B4180511 : Blo 1303970 4180511 := bstep (se 1 (by rfl) ⟨3135383, by rfl⟩ : syracuseStep 4180511 = 6270767) B6270767
theorem B1305119 : Blo 1303970 1305119 := bstep (se 1 (by rfl) ⟨978839, by rfl⟩ : syracuseStep 1305119 = 1957679) B1957679
theorem B2787871 : Blo 1303970 2787871 := bstep (se 1 (by rfl) ⟨2090903, by rfl⟩ : syracuseStep 2787871 = 4181807) B4181807
theorem B2476649 : Blo 1303970 2476649 := bstep (se 2 (by rfl) ⟨928743, by rfl⟩ : syracuseStep 2476649 = 1857487) B1857487
theorem B1305435 : Blo 1303970 1305435 := bstep (se 1 (by rfl) ⟨979076, by rfl⟩ : syracuseStep 1305435 = 1958153) B1958153
theorem B1305503 : Blo 1303970 1305503 := bstep (se 1 (by rfl) ⟨979127, by rfl⟩ : syracuseStep 1305503 = 1958255) B1958255
theorem B107154389 : Blo 1303970 107154389 := bstep (se 7 (by rfl) ⟨1255715, by rfl⟩ : syracuseStep 107154389 = 2511431) B2511431
theorem B1305647 : Blo 1303970 1305647 := bstep (se 1 (by rfl) ⟨979235, by rfl⟩ : syracuseStep 1305647 = 1958471) B1958471
theorem B1305671 : Blo 1303970 1305671 := bstep (se 1 (by rfl) ⟨979253, by rfl⟩ : syracuseStep 1305671 = 1958507) B1958507
theorem B2477279 : Blo 1303970 2477279 := bstep (se 1 (by rfl) ⟨1857959, by rfl⟩ : syracuseStep 2477279 = 3715919) B3715919
theorem B1305823 : Blo 1303970 1305823 := bstep (se 1 (by rfl) ⟨979367, by rfl⟩ : syracuseStep 1305823 = 1958735) B1958735
theorem B4402457 : Blo 1303970 4402457 := bstep (se 2 (by rfl) ⟨1650921, by rfl⟩ : syracuseStep 4402457 = 3301843) B3301843
theorem B11308339 : Blo 1303970 11308339 := bstep (se 1 (by rfl) ⟨8481254, by rfl⟩ : syracuseStep 11308339 = 16962509) B16962509
theorem B4402511 : Blo 1303970 4402511 := bstep (se 1 (by rfl) ⟨3301883, by rfl⟩ : syracuseStep 4402511 = 6603767) B6603767
theorem B2936393 : Blo 1303970 2936393 := bstep (se 2 (by rfl) ⟨1101147, by rfl⟩ : syracuseStep 2936393 = 2202295) B2202295
theorem B3305033 : Blo 1303970 3305033 := bstep (se 2 (by rfl) ⟨1239387, by rfl⟩ : syracuseStep 3305033 = 2478775) B2478775
theorem B2977387 : Blo 1303970 2977387 := bstep (se 1 (by rfl) ⟨2233040, by rfl⟩ : syracuseStep 2977387 = 4466081) B4466081
theorem B2977679 : Blo 1303970 2977679 := bstep (se 1 (by rfl) ⟨2233259, by rfl⟩ : syracuseStep 2977679 = 4466519) B4466519
theorem B11898899 : Blo 1303970 11898899 := bstep (se 1 (by rfl) ⟨8924174, by rfl⟩ : syracuseStep 11898899 = 17848349) B17848349
theorem B4952249 : Blo 1303970 4952249 := bstep (se 2 (by rfl) ⟨1857093, by rfl⟩ : syracuseStep 4952249 = 3714187) B3714187
theorem B22303025 : Blo 1303970 22303025 := bstep (se 2 (by rfl) ⟨8363634, by rfl⟩ : syracuseStep 22303025 = 16727269) B16727269
theorem B4952447 : Blo 1303970 4952447 := bstep (se 1 (by rfl) ⟨3714335, by rfl⟩ : syracuseStep 4952447 = 7428671) B7428671
theorem B16732601 : Blo 1303970 16732601 := bstep (se 2 (by rfl) ⟨6274725, by rfl⟩ : syracuseStep 16732601 = 12549451) B12549451
theorem B14873057 : Blo 1303970 14873057 := bstep (se 2 (by rfl) ⟨5577396, by rfl⟩ : syracuseStep 14873057 = 11154793) B11154793
theorem B3715577 : Blo 1303970 3715577 := bstep (se 2 (by rfl) ⟨1393341, by rfl⟩ : syracuseStep 3715577 = 2786683) B2786683
theorem B4403807 : Blo 1303970 4403807 := bstep (se 1 (by rfl) ⟨3302855, by rfl⟩ : syracuseStep 4403807 = 6605711) B6605711
theorem B122131235 : Blo 1303970 122131235 := bstep (se 1 (by rfl) ⟨91598426, by rfl⟩ : syracuseStep 122131235 = 183196853) B183196853
theorem B11899709 : Blo 1303970 11899709 := bstep (se 3 (by rfl) ⟨2231195, by rfl⟩ : syracuseStep 11899709 = 4462391) B4462391
theorem B11146045 : Blo 1303970 11146045 := bstep (se 3 (by rfl) ⟨2089883, by rfl⟩ : syracuseStep 11146045 = 4179767) B4179767
theorem B8360765 : Blo 1303970 8360765 := bstep (se 3 (by rfl) ⟨1567643, by rfl⟩ : syracuseStep 8360765 = 3135287) B3135287
theorem B22311773 : Blo 1303970 22311773 := bstep (se 3 (by rfl) ⟨4183457, by rfl⟩ : syracuseStep 22311773 = 8366915) B8366915
theorem B5575553 : Blo 1303970 5575553 := bstep (se 2 (by rfl) ⟨2090832, by rfl⟩ : syracuseStep 5575553 = 4181665) B4181665
theorem B3527675 : Blo 1303970 3527675 := bstep (se 1 (by rfl) ⟨2645756, by rfl⟩ : syracuseStep 3527675 = 5291513) B5291513
theorem B2937851 : Blo 1303970 2937851 := bstep (se 1 (by rfl) ⟨2203388, by rfl⟩ : syracuseStep 2937851 = 4406777) B4406777
theorem B2479177 : Blo 1303970 2479177 := bstep (se 2 (by rfl) ⟨929691, by rfl⟩ : syracuseStep 2479177 = 1859383) B1859383
theorem B12538961 : Blo 1303970 12538961 := bstep (se 2 (by rfl) ⟨4702110, by rfl⟩ : syracuseStep 12538961 = 9404221) B9404221
theorem B6607979 : Blo 1303970 6607979 := bstep (se 1 (by rfl) ⟨4955984, by rfl⟩ : syracuseStep 6607979 = 9911969) B9911969
theorem B2938031 : Blo 1303970 2938031 := bstep (se 1 (by rfl) ⟨2203523, by rfl⟩ : syracuseStep 2938031 = 4407047) B4407047
theorem B2200783 : Blo 1303970 2200783 := bstep (se 1 (by rfl) ⟨1650587, by rfl⟩ : syracuseStep 2200783 = 3301175) B3301175
theorem B2938067 : Blo 1303970 2938067 := bstep (se 1 (by rfl) ⟨2203550, by rfl⟩ : syracuseStep 2938067 = 4407101) B4407101
theorem B19076471 : Blo 1303970 19076471 := bstep (se 1 (by rfl) ⟨14307353, by rfl⟩ : syracuseStep 19076471 = 28614707) B28614707
theorem B16733627 : Blo 1303970 16733627 := bstep (se 1 (by rfl) ⟨12550220, by rfl⟩ : syracuseStep 16733627 = 25100441) B25100441
theorem B7435709 : Blo 1303970 7435709 := bstep (se 3 (by rfl) ⟨1394195, by rfl⟩ : syracuseStep 7435709 = 2788391) B2788391
theorem B2938337 : Blo 1303970 2938337 := bstep (se 2 (by rfl) ⟨1101876, by rfl⟩ : syracuseStep 2938337 = 2203753) B2203753
theorem B4405049 : Blo 1303970 4405049 := bstep (se 2 (by rfl) ⟨1651893, by rfl⟩ : syracuseStep 4405049 = 3303787) B3303787
theorem B3716921 : Blo 1303970 3716921 := bstep (se 2 (by rfl) ⟨1393845, by rfl⟩ : syracuseStep 3716921 = 2787691) B2787691
theorem B5289923 : Blo 1303970 5289923 := bstep (se 1 (by rfl) ⟨3967442, by rfl⟩ : syracuseStep 5289923 = 7934885) B7934885
theorem B4405211 : Blo 1303970 4405211 := bstep (se 1 (by rfl) ⟨3303908, by rfl⟩ : syracuseStep 4405211 = 6607817) B6607817
theorem B3717103 : Blo 1303970 3717103 := bstep (se 1 (by rfl) ⟨2787827, by rfl⟩ : syracuseStep 3717103 = 5575655) B5575655
theorem B1652719 : Blo 1303970 1652719 := bstep (se 1 (by rfl) ⟨1239539, by rfl⟩ : syracuseStep 1652719 = 2479079) B2479079
theorem B2201593 : Blo 1303970 2201593 := bstep (se 2 (by rfl) ⟨825597, by rfl⟩ : syracuseStep 2201593 = 1651195) B1651195
theorem B7436393 : Blo 1303970 7436393 := bstep (se 2 (by rfl) ⟨2788647, by rfl⟩ : syracuseStep 7436393 = 5577295) B5577295
theorem B2201755 : Blo 1303970 2201755 := bstep (se 1 (by rfl) ⟨1651316, by rfl⟩ : syracuseStep 2201755 = 3302633) B3302633
theorem B4405481 : Blo 1303970 4405481 := bstep (se 2 (by rfl) ⟨1652055, by rfl⟩ : syracuseStep 4405481 = 3304111) B3304111
theorem B3717353 : Blo 1303970 3717353 := bstep (se 2 (by rfl) ⟨1394007, by rfl⟩ : syracuseStep 3717353 = 2788015) B2788015
theorem B2644231 : Blo 1303970 2644231 := bstep (se 1 (by rfl) ⟨1983173, by rfl⟩ : syracuseStep 2644231 = 3966347) B3966347
theorem B2201863 : Blo 1303970 2201863 := bstep (se 1 (by rfl) ⟨1651397, by rfl⟩ : syracuseStep 2201863 = 3302795) B3302795
theorem B1956137 : Blo 1303970 1956137 := bstep (se 2 (by rfl) ⟨733551, by rfl⟩ : syracuseStep 1956137 = 1467103) B1467103
theorem B2201897 : Blo 1303970 2201897 := bstep (se 2 (by rfl) ⟨825711, by rfl⟩ : syracuseStep 2201897 = 1651423) B1651423
theorem B1956143 : Blo 1303970 1956143 := bstep (se 1 (by rfl) ⟨1467107, by rfl⟩ : syracuseStep 1956143 = 2934215) B2934215
theorem B6609275 : Blo 1303970 6609275 := bstep (se 1 (by rfl) ⟨4956956, by rfl⟩ : syracuseStep 6609275 = 9913913) B9913913
theorem B10049915 : Blo 1303970 10049915 := bstep (se 1 (by rfl) ⟨7537436, by rfl⟩ : syracuseStep 10049915 = 15074873) B15074873
theorem B1956383 : Blo 1303970 1956383 := bstep (se 1 (by rfl) ⟨1467287, by rfl⟩ : syracuseStep 1956383 = 2934575) B2934575
theorem B1858079 : Blo 1303970 1858079 := bstep (se 1 (by rfl) ⟨1393559, by rfl⟩ : syracuseStep 1858079 = 2787119) B2787119
theorem B1858153 : Blo 1303970 1858153 := bstep (se 2 (by rfl) ⟨696807, by rfl⟩ : syracuseStep 1858153 = 1393615) B1393615
theorem B4405913 : Blo 1303970 4405913 := bstep (se 2 (by rfl) ⟨1652217, by rfl⟩ : syracuseStep 4405913 = 3304435) B3304435
theorem B12704617 : Blo 1303970 12704617 := bstep (se 2 (by rfl) ⟨4764231, by rfl⟩ : syracuseStep 12704617 = 9528463) B9528463
theorem B1956767 : Blo 1303970 1956767 := bstep (se 1 (by rfl) ⟨1467575, by rfl⟩ : syracuseStep 1956767 = 2935151) B2935151
theorem B63445963 : Blo 1303970 63445963 := bstep (se 1 (by rfl) ⟨47584472, by rfl⟩ : syracuseStep 63445963 = 95168945) B95168945
theorem B1956815 : Blo 1303970 1956815 := bstep (se 1 (by rfl) ⟨1467611, by rfl⟩ : syracuseStep 1956815 = 2935223) B2935223
theorem B1956905 : Blo 1303970 1956905 := bstep (se 2 (by rfl) ⟨733839, by rfl⟩ : syracuseStep 1956905 = 1467679) B1467679
theorem B1956911 : Blo 1303970 1956911 := bstep (se 1 (by rfl) ⟨1467683, by rfl⟩ : syracuseStep 1956911 = 2935367) B2935367
theorem B1956935 : Blo 1303970 1956935 := bstep (se 1 (by rfl) ⟨1467701, by rfl⟩ : syracuseStep 1956935 = 2935403) B2935403
theorem B1858631 : Blo 1303970 1858631 := bstep (se 1 (by rfl) ⟨1393973, by rfl⟩ : syracuseStep 1858631 = 2787947) B2787947
theorem B2202889 : Blo 1303970 2202889 := bstep (se 2 (by rfl) ⟨826083, by rfl⟩ : syracuseStep 2202889 = 1652167) B1652167
theorem B1858825 : Blo 1303970 1858825 := bstep (se 2 (by rfl) ⟨697059, by rfl⟩ : syracuseStep 1858825 = 1394119) B1394119
theorem B1957199 : Blo 1303970 1957199 := bstep (se 1 (by rfl) ⟨1467899, by rfl⟩ : syracuseStep 1957199 = 2935799) B2935799
theorem B3718561 : Blo 1303970 3718561 := bstep (se 2 (by rfl) ⟨1394460, by rfl⟩ : syracuseStep 3718561 = 2788921) B2788921
theorem B1957289 : Blo 1303970 1957289 := bstep (se 2 (by rfl) ⟨733983, by rfl⟩ : syracuseStep 1957289 = 1467967) B1467967
theorem B26787287 : Blo 1303970 26787287 := bstep (se 1 (by rfl) ⟨20090465, by rfl⟩ : syracuseStep 26787287 = 40180931) B40180931
theorem B1957439 : Blo 1303970 1957439 := bstep (se 1 (by rfl) ⟨1468079, by rfl⟩ : syracuseStep 1957439 = 2936159) B2936159
theorem B1957703 : Blo 1303970 1957703 := bstep (se 1 (by rfl) ⟨1468277, by rfl⟩ : syracuseStep 1957703 = 2936555) B2936555
theorem B2203463 : Blo 1303970 2203463 := bstep (se 1 (by rfl) ⟨1652597, by rfl⟩ : syracuseStep 2203463 = 3305195) B3305195
theorem B1957787 : Blo 1303970 1957787 := bstep (se 1 (by rfl) ⟨1468340, by rfl⟩ : syracuseStep 1957787 = 2936681) B2936681
theorem B3301499 : Blo 1303970 3301499 := bstep (se 1 (by rfl) ⟨2476124, by rfl⟩ : syracuseStep 3301499 = 4952249) B4952249
theorem B4956349 : Blo 1303970 4956349 := bstep (se 3 (by rfl) ⟨929315, by rfl⟩ : syracuseStep 4956349 = 1858631) B1858631
theorem B14868683 : Blo 1303970 14868683 := bstep (se 1 (by rfl) ⟨11151512, by rfl⟩ : syracuseStep 14868683 = 22303025) B22303025
theorem B3301631 : Blo 1303970 3301631 := bstep (se 1 (by rfl) ⟨2476223, by rfl⟩ : syracuseStep 3301631 = 4952447) B4952447
theorem B23814425 : Blo 1303970 23814425 := bstep (se 2 (by rfl) ⟨8930409, by rfl⟩ : syracuseStep 23814425 = 17860819) B17860819
theorem B5439791 : Blo 1303970 5439791 := bstep (se 1 (by rfl) ⟨4079843, by rfl⟩ : syracuseStep 5439791 = 8159687) B8159687
theorem B3301793 : Blo 1303970 3301793 := bstep (se 2 (by rfl) ⟨1238172, by rfl⟩ : syracuseStep 3301793 = 2476345) B2476345
theorem B81420823 : Blo 1303970 81420823 := bstep (se 1 (by rfl) ⟨61065617, by rfl⟩ : syracuseStep 81420823 = 122131235) B122131235
theorem B9912941 : Blo 1303970 9912941 := bstep (se 3 (by rfl) ⟨1858676, by rfl⟩ : syracuseStep 9912941 = 3717353) B3717353
theorem B2351783 : Blo 1303970 2351783 := bstep (se 1 (by rfl) ⟨1763837, by rfl⟩ : syracuseStep 2351783 = 3527675) B3527675
theorem B1958567 : Blo 1303970 1958567 := bstep (se 1 (by rfl) ⟨1468925, by rfl⟩ : syracuseStep 1958567 = 2937851) B2937851
theorem B1958687 : Blo 1303970 1958687 := bstep (se 1 (by rfl) ⟨1469015, by rfl⟩ : syracuseStep 1958687 = 2938031) B2938031
theorem B1958711 : Blo 1303970 1958711 := bstep (se 1 (by rfl) ⟨1469033, by rfl⟩ : syracuseStep 1958711 = 2938067) B2938067
theorem B11141945 : Blo 1303970 11141945 := bstep (se 2 (by rfl) ⟨4178229, by rfl⟩ : syracuseStep 11141945 = 8356459) B8356459
theorem B4957139 : Blo 1303970 4957139 := bstep (se 1 (by rfl) ⟨3717854, by rfl⟩ : syracuseStep 4957139 = 7435709) B7435709
theorem B1958891 : Blo 1303970 1958891 := bstep (se 1 (by rfl) ⟨1469168, by rfl⟩ : syracuseStep 1958891 = 2938337) B2938337
theorem B7930943 : Blo 1303970 7930943 := bstep (se 1 (by rfl) ⟨5948207, by rfl⟩ : syracuseStep 7930943 = 11896415) B11896415
theorem B14861393 : Blo 1303970 14861393 := bstep (se 2 (by rfl) ⟨5573022, by rfl⟩ : syracuseStep 14861393 = 11146045) B11146045
theorem B12551375 : Blo 1303970 12551375 := bstep (se 1 (by rfl) ⟨9413531, by rfl⟩ : syracuseStep 12551375 = 18827063) B18827063
theorem B2934107 : Blo 1303970 2934107 := bstep (se 1 (by rfl) ⟨2200580, by rfl⟩ : syracuseStep 2934107 = 4401161) B4401161
theorem B4957595 : Blo 1303970 4957595 := bstep (se 1 (by rfl) ⟨3718196, by rfl⟩ : syracuseStep 4957595 = 7436393) B7436393
theorem B1304091 : Blo 1303970 1304091 := bstep (se 1 (by rfl) ⟨978068, by rfl⟩ : syracuseStep 1304091 = 1956137) B1956137
theorem B1467931 : Blo 1303970 1467931 := bstep (se 1 (by rfl) ⟨1100948, by rfl⟩ : syracuseStep 1467931 = 2201897) B2201897
theorem B1304095 : Blo 1303970 1304095 := bstep (se 1 (by rfl) ⟨978071, by rfl⟩ : syracuseStep 1304095 = 1956143) B1956143
theorem B60311141 : Blo 1303970 60311141 := bstep (se 4 (by rfl) ⟨5654169, by rfl⟩ : syracuseStep 60311141 = 11308339) B11308339
theorem B2934377 : Blo 1303970 2934377 := bstep (se 2 (by rfl) ⟨1100391, by rfl⟩ : syracuseStep 2934377 = 2200783) B2200783
theorem B4179563 : Blo 1303970 4179563 := bstep (se 1 (by rfl) ⟨3134672, by rfl⟩ : syracuseStep 4179563 = 6269345) B6269345
theorem B1304255 : Blo 1303970 1304255 := bstep (se 1 (by rfl) ⟨978191, by rfl⟩ : syracuseStep 1304255 = 1956383) B1956383
theorem B18810569 : Blo 1303970 18810569 := bstep (se 2 (by rfl) ⟨7053963, by rfl⟩ : syracuseStep 18810569 = 14107927) B14107927
theorem B4958081 : Blo 1303970 4958081 := bstep (se 2 (by rfl) ⟨1859280, by rfl⟩ : syracuseStep 4958081 = 3718561) B3718561
theorem B1304511 : Blo 1303970 1304511 := bstep (se 1 (by rfl) ⟨978383, by rfl⟩ : syracuseStep 1304511 = 1956767) B1956767
theorem B1304543 : Blo 1303970 1304543 := bstep (se 1 (by rfl) ⟨978407, by rfl⟩ : syracuseStep 1304543 = 1956815) B1956815
theorem B71436259 : Blo 1303970 71436259 := bstep (se 1 (by rfl) ⟨53577194, by rfl⟩ : syracuseStep 71436259 = 107154389) B107154389
theorem B1304603 : Blo 1303970 1304603 := bstep (se 1 (by rfl) ⟨978452, by rfl⟩ : syracuseStep 1304603 = 1956905) B1956905
theorem B1304607 : Blo 1303970 1304607 := bstep (se 1 (by rfl) ⟨978455, by rfl⟩ : syracuseStep 1304607 = 1956911) B1956911
theorem B1304623 : Blo 1303970 1304623 := bstep (se 1 (by rfl) ⟨978467, by rfl⟩ : syracuseStep 1304623 = 1956935) B1956935
theorem B101673053 : Blo 1303970 101673053 := bstep (se 3 (by rfl) ⟨19063697, by rfl⟩ : syracuseStep 101673053 = 38127395) B38127395
theorem B2934971 : Blo 1303970 2934971 := bstep (se 1 (by rfl) ⟨2201228, by rfl⟩ : syracuseStep 2934971 = 4402457) B4402457
theorem B2935007 : Blo 1303970 2935007 := bstep (se 1 (by rfl) ⟨2201255, by rfl⟩ : syracuseStep 2935007 = 4402511) B4402511
theorem B1304799 : Blo 1303970 1304799 := bstep (se 1 (by rfl) ⟨978599, by rfl⟩ : syracuseStep 1304799 = 1957199) B1957199
theorem B1304859 : Blo 1303970 1304859 := bstep (se 1 (by rfl) ⟨978644, by rfl⟩ : syracuseStep 1304859 = 1957289) B1957289
theorem B1304959 : Blo 1303970 1304959 := bstep (se 1 (by rfl) ⟨978719, by rfl⟩ : syracuseStep 1304959 = 1957439) B1957439
theorem B1305135 : Blo 1303970 1305135 := bstep (se 1 (by rfl) ⟨978851, by rfl⟩ : syracuseStep 1305135 = 1957703) B1957703
theorem B1468975 : Blo 1303970 1468975 := bstep (se 1 (by rfl) ⟨1101731, by rfl⟩ : syracuseStep 1468975 = 2203463) B2203463
theorem B1985119 : Blo 1303970 1985119 := bstep (se 1 (by rfl) ⟨1488839, by rfl⟩ : syracuseStep 1985119 = 2977679) B2977679
theorem B1305191 : Blo 1303970 1305191 := bstep (se 1 (by rfl) ⟨978893, by rfl⟩ : syracuseStep 1305191 = 1957787) B1957787
theorem B2935457 : Blo 1303970 2935457 := bstep (se 2 (by rfl) ⟨1100796, by rfl⟩ : syracuseStep 2935457 = 2201593) B2201593
theorem B7932599 : Blo 1303970 7932599 := bstep (se 1 (by rfl) ⟨5949449, by rfl⟩ : syracuseStep 7932599 = 11898899) B11898899
theorem B2935673 : Blo 1303970 2935673 := bstep (se 2 (by rfl) ⟨1100877, by rfl⟩ : syracuseStep 2935673 = 2201755) B2201755
theorem B1305567 : Blo 1303970 1305567 := bstep (se 1 (by rfl) ⟨979175, by rfl⟩ : syracuseStep 1305567 = 1958351) B1958351
theorem B9915371 : Blo 1303970 9915371 := bstep (se 1 (by rfl) ⟨7436528, by rfl⟩ : syracuseStep 9915371 = 14873057) B14873057
theorem B2477051 : Blo 1303970 2477051 := bstep (se 1 (by rfl) ⟨1857788, by rfl⟩ : syracuseStep 2477051 = 3715577) B3715577
theorem B1305595 : Blo 1303970 1305595 := bstep (se 1 (by rfl) ⟨979196, by rfl⟩ : syracuseStep 1305595 = 1958393) B1958393
theorem B3525641 : Blo 1303970 3525641 := bstep (se 2 (by rfl) ⟨1322115, by rfl⟩ : syracuseStep 3525641 = 2644231) B2644231
theorem B2935817 : Blo 1303970 2935817 := bstep (se 2 (by rfl) ⟨1100931, by rfl⟩ : syracuseStep 2935817 = 2201863) B2201863
theorem B2935871 : Blo 1303970 2935871 := bstep (se 1 (by rfl) ⟨2201903, by rfl⟩ : syracuseStep 2935871 = 4403807) B4403807
theorem B1305663 : Blo 1303970 1305663 := bstep (se 1 (by rfl) ⟨979247, by rfl⟩ : syracuseStep 1305663 = 1958495) B1958495
theorem B3714119 : Blo 1303970 3714119 := bstep (se 1 (by rfl) ⟨2785589, by rfl⟩ : syracuseStep 3714119 = 5571179) B5571179
theorem B7933139 : Blo 1303970 7933139 := bstep (se 1 (by rfl) ⟨5949854, by rfl⟩ : syracuseStep 7933139 = 11899709) B11899709
theorem B5573843 : Blo 1303970 5573843 := bstep (se 1 (by rfl) ⟨4180382, by rfl⟩ : syracuseStep 5573843 = 8360765) B8360765
theorem B15879397 : Blo 1303970 15879397 := bstep (se 4 (by rfl) ⟨1488693, by rfl⟩ : syracuseStep 15879397 = 2977387) B2977387
theorem B14855561 : Blo 1303970 14855561 := bstep (se 2 (by rfl) ⟨5570835, by rfl⟩ : syracuseStep 14855561 = 11141671) B11141671
theorem B8359307 : Blo 1303970 8359307 := bstep (se 1 (by rfl) ⟨6269480, by rfl⟩ : syracuseStep 8359307 = 12538961) B12538961
theorem B3304871 : Blo 1303970 3304871 := bstep (se 1 (by rfl) ⟨2478653, by rfl⟩ : syracuseStep 3304871 = 4957307) B4957307
theorem B42331571 : Blo 1303970 42331571 := bstep (se 1 (by rfl) ⟨31748678, by rfl⟩ : syracuseStep 42331571 = 63497357) B63497357
theorem B2477537 : Blo 1303970 2477537 := bstep (se 2 (by rfl) ⟨929076, by rfl⟩ : syracuseStep 2477537 = 1858153) B1858153
theorem B12717647 : Blo 1303970 12717647 := bstep (se 1 (by rfl) ⟨9538235, by rfl⟩ : syracuseStep 12717647 = 19076471) B19076471
theorem B5287801 : Blo 1303970 5287801 := bstep (se 2 (by rfl) ⟨1982925, by rfl⟩ : syracuseStep 5287801 = 3965851) B3965851
theorem B2936699 : Blo 1303970 2936699 := bstep (se 1 (by rfl) ⟨2202524, by rfl⟩ : syracuseStep 2936699 = 4405049) B4405049
theorem B2477947 : Blo 1303970 2477947 := bstep (se 1 (by rfl) ⟨1858460, by rfl⟩ : syracuseStep 2477947 = 3716921) B3716921
theorem B4829053 : Blo 1303970 4829053 := bstep (se 3 (by rfl) ⟨905447, by rfl⟩ : syracuseStep 4829053 = 1810895) B1810895
theorem B84594617 : Blo 1303970 84594617 := bstep (se 2 (by rfl) ⟨31722981, by rfl⟩ : syracuseStep 84594617 = 63445963) B63445963
theorem B3526615 : Blo 1303970 3526615 := bstep (se 1 (by rfl) ⟨2644961, by rfl⟩ : syracuseStep 3526615 = 5289923) B5289923
theorem B2936807 : Blo 1303970 2936807 := bstep (se 1 (by rfl) ⟨2202605, by rfl⟩ : syracuseStep 2936807 = 4405211) B4405211
theorem B3305569 : Blo 1303970 3305569 := bstep (se 2 (by rfl) ⟨1239588, by rfl⟩ : syracuseStep 3305569 = 2479177) B2479177
theorem B2936987 : Blo 1303970 2936987 := bstep (se 1 (by rfl) ⟨2202740, by rfl⟩ : syracuseStep 2936987 = 4405481) B4405481
theorem B3715303 : Blo 1303970 3715303 := bstep (se 1 (by rfl) ⟨2786477, by rfl⟩ : syracuseStep 3715303 = 5572955) B5572955
theorem B7434503 : Blo 1303970 7434503 := bstep (se 1 (by rfl) ⟨5575877, by rfl⟩ : syracuseStep 7434503 = 11151755) B11151755
theorem B5026067 : Blo 1303970 5026067 := bstep (se 1 (by rfl) ⟨3769550, by rfl⟩ : syracuseStep 5026067 = 7539101) B7539101
theorem B2937185 : Blo 1303970 2937185 := bstep (se 2 (by rfl) ⟨1101444, by rfl⟩ : syracuseStep 2937185 = 2202889) B2202889
theorem B2478433 : Blo 1303970 2478433 := bstep (se 2 (by rfl) ⟨929412, by rfl⟩ : syracuseStep 2478433 = 1858825) B1858825
theorem B1651099 : Blo 1303970 1651099 := bstep (se 1 (by rfl) ⟨1238324, by rfl⟩ : syracuseStep 1651099 = 2476649) B2476649
theorem B2937275 : Blo 1303970 2937275 := bstep (se 1 (by rfl) ⟨2202956, by rfl⟩ : syracuseStep 2937275 = 4405913) B4405913
theorem B1651519 : Blo 1303970 1651519 := bstep (se 1 (by rfl) ⟨1238639, by rfl⟩ : syracuseStep 1651519 = 2477279) B2477279
theorem B11155067 : Blo 1303970 11155067 := bstep (se 1 (by rfl) ⟨8366300, by rfl⟩ : syracuseStep 11155067 = 16732601) B16732601
theorem B4953919 : Blo 1303970 4953919 := bstep (se 1 (by rfl) ⟨3715439, by rfl⟩ : syracuseStep 4953919 = 7430879) B7430879
theorem B14874515 : Blo 1303970 14874515 := bstep (se 1 (by rfl) ⟨11155886, by rfl⟩ : syracuseStep 14874515 = 22311773) B22311773
theorem B3717035 : Blo 1303970 3717035 := bstep (se 1 (by rfl) ⟨2787776, by rfl⟩ : syracuseStep 3717035 = 5575553) B5575553
theorem B3717161 : Blo 1303970 3717161 := bstep (se 2 (by rfl) ⟨1393935, by rfl⟩ : syracuseStep 3717161 = 2787871) B2787871
theorem B4405319 : Blo 1303970 4405319 := bstep (se 1 (by rfl) ⟨3303989, by rfl⟩ : syracuseStep 4405319 = 6607979) B6607979
theorem B1956059 : Blo 1303970 1956059 := bstep (se 1 (by rfl) ⟨1467044, by rfl⟩ : syracuseStep 1956059 = 2934089) B2934089
theorem B11155751 : Blo 1303970 11155751 := bstep (se 1 (by rfl) ⟨8366813, by rfl⟩ : syracuseStep 11155751 = 16733627) B16733627
theorem B16939489 : Blo 1303970 16939489 := bstep (se 2 (by rfl) ⟨6352308, by rfl⟩ : syracuseStep 16939489 = 12704617) B12704617
theorem B1956329 : Blo 1303970 1956329 := bstep (se 2 (by rfl) ⟨733623, by rfl⟩ : syracuseStep 1956329 = 1467247) B1467247
theorem B71432765 : Blo 1303970 71432765 := bstep (se 3 (by rfl) ⟨13393643, by rfl⟩ : syracuseStep 71432765 = 26787287) B26787287
theorem B11148029 : Blo 1303970 11148029 := bstep (se 3 (by rfl) ⟨2090255, by rfl⟩ : syracuseStep 11148029 = 4180511) B4180511
theorem B4954877 : Blo 1303970 4954877 := bstep (se 3 (by rfl) ⟨929039, by rfl⟩ : syracuseStep 4954877 = 1858079) B1858079
theorem B4954891 : Blo 1303970 4954891 := bstep (se 1 (by rfl) ⟨3716168, by rfl⟩ : syracuseStep 4954891 = 7432337) B7432337
theorem B2349881 : Blo 1303970 2349881 := bstep (se 2 (by rfl) ⟨881205, by rfl⟩ : syracuseStep 2349881 = 1762411) B1762411
theorem B1956719 : Blo 1303970 1956719 := bstep (se 1 (by rfl) ⟨1467539, by rfl⟩ : syracuseStep 1956719 = 2935079) B2935079
theorem B1956731 : Blo 1303970 1956731 := bstep (se 1 (by rfl) ⟨1467548, by rfl⟩ : syracuseStep 1956731 = 2935097) B2935097
theorem B2202491 : Blo 1303970 2202491 := bstep (se 1 (by rfl) ⟨1651868, by rfl⟩ : syracuseStep 2202491 = 3303737) B3303737
theorem B4406183 : Blo 1303970 4406183 := bstep (se 1 (by rfl) ⟨3304637, by rfl⟩ : syracuseStep 4406183 = 6609275) B6609275
theorem B6699943 : Blo 1303970 6699943 := bstep (se 1 (by rfl) ⟨5024957, by rfl⟩ : syracuseStep 6699943 = 10049915) B10049915
theorem B1957595 : Blo 1303970 1957595 := bstep (se 1 (by rfl) ⟨1468196, by rfl⟩ : syracuseStep 1957595 = 2936393) B2936393
theorem B2203355 : Blo 1303970 2203355 := bstep (se 1 (by rfl) ⟨1652516, by rfl⟩ : syracuseStep 2203355 = 3305033) B3305033
theorem B1957865 : Blo 1303970 1957865 := bstep (se 2 (by rfl) ⟨734199, by rfl⟩ : syracuseStep 1957865 = 1468399) B1468399
theorem B4956137 : Blo 1303970 4956137 := bstep (se 2 (by rfl) ⟨1858551, by rfl⟩ : syracuseStep 4956137 = 3717103) B3717103
theorem B2203625 : Blo 1303970 2203625 := bstep (se 2 (by rfl) ⟨826359, by rfl⟩ : syracuseStep 2203625 = 1652719) B1652719
theorem B1957991 : Blo 1303970 1957991 := bstep (se 1 (by rfl) ⟨1468493, by rfl⟩ : syracuseStep 1957991 = 2936987) B2936987
theorem B4407425 : Blo 1303970 4407425 := bstep (se 2 (by rfl) ⟨1652784, by rfl⟩ : syracuseStep 4407425 = 3305569) B3305569
theorem B9912455 : Blo 1303970 9912455 := bstep (se 1 (by rfl) ⟨7434341, by rfl⟩ : syracuseStep 9912455 = 14868683) B14868683
theorem B4956335 : Blo 1303970 4956335 := bstep (se 1 (by rfl) ⟨3717251, by rfl⟩ : syracuseStep 4956335 = 7434503) B7434503
theorem B3350711 : Blo 1303970 3350711 := bstep (se 1 (by rfl) ⟨2513033, by rfl⟩ : syracuseStep 3350711 = 5026067) B5026067
theorem B15876283 : Blo 1303970 15876283 := bstep (se 1 (by rfl) ⟨11907212, by rfl⟩ : syracuseStep 15876283 = 23814425) B23814425
theorem B1958123 : Blo 1303970 1958123 := bstep (se 1 (by rfl) ⟨1468592, by rfl⟩ : syracuseStep 1958123 = 2937185) B2937185
theorem B1958183 : Blo 1303970 1958183 := bstep (se 1 (by rfl) ⟨1468637, by rfl⟩ : syracuseStep 1958183 = 2937275) B2937275
theorem B22585985 : Blo 1303970 22585985 := bstep (se 2 (by rfl) ⟨8469744, by rfl⟩ : syracuseStep 22585985 = 16939489) B16939489
theorem B108561097 : Blo 1303970 108561097 := bstep (se 2 (by rfl) ⟨40710411, by rfl⟩ : syracuseStep 108561097 = 81420823) B81420823
theorem B1958633 : Blo 1303970 1958633 := bstep (se 2 (by rfl) ⟨734487, by rfl⟩ : syracuseStep 1958633 = 1468975) B1468975
theorem B40207427 : Blo 1303970 40207427 := bstep (se 1 (by rfl) ⟨30155570, by rfl⟩ : syracuseStep 40207427 = 60311141) B60311141
theorem B2786375 : Blo 1303970 2786375 := bstep (se 1 (by rfl) ⟨2089781, by rfl⟩ : syracuseStep 2786375 = 4179563) B4179563
theorem B67782035 : Blo 1303970 67782035 := bstep (se 1 (by rfl) ⟨50836526, by rfl⟩ : syracuseStep 67782035 = 101673053) B101673053
theorem B1304039 : Blo 1303970 1304039 := bstep (se 1 (by rfl) ⟨978029, by rfl⟩ : syracuseStep 1304039 = 1956059) B1956059
theorem B1304219 : Blo 1303970 1304219 := bstep (se 1 (by rfl) ⟨978164, by rfl⟩ : syracuseStep 1304219 = 1956329) B1956329
theorem B47621843 : Blo 1303970 47621843 := bstep (se 1 (by rfl) ⟨35716382, by rfl⟩ : syracuseStep 47621843 = 71432765) B71432765
theorem B7432019 : Blo 1303970 7432019 := bstep (se 1 (by rfl) ⟨5574014, by rfl⟩ : syracuseStep 7432019 = 11148029) B11148029
theorem B3303251 : Blo 1303970 3303251 := bstep (se 1 (by rfl) ⟨2477438, by rfl⟩ : syracuseStep 3303251 = 4954877) B4954877
theorem B1566587 : Blo 1303970 1566587 := bstep (se 1 (by rfl) ⟨1174940, by rfl⟩ : syracuseStep 1566587 = 2349881) B2349881
theorem B1304479 : Blo 1303970 1304479 := bstep (se 1 (by rfl) ⟨978359, by rfl⟩ : syracuseStep 1304479 = 1956719) B1956719
theorem B1304487 : Blo 1303970 1304487 := bstep (se 1 (by rfl) ⟨978365, by rfl⟩ : syracuseStep 1304487 = 1956731) B1956731
theorem B1468327 : Blo 1303970 1468327 := bstep (se 1 (by rfl) ⟨1101245, by rfl⟩ : syracuseStep 1468327 = 2202491) B2202491
theorem B2476079 : Blo 1303970 2476079 := bstep (se 1 (by rfl) ⟨1857059, by rfl⟩ : syracuseStep 2476079 = 3714119) B3714119
theorem B5572871 : Blo 1303970 5572871 := bstep (se 1 (by rfl) ⟨4179653, by rfl⟩ : syracuseStep 5572871 = 8359307) B8359307
theorem B6605225 : Blo 1303970 6605225 := bstep (se 2 (by rfl) ⟨2476959, by rfl⟩ : syracuseStep 6605225 = 4953919) B4953919
theorem B1305063 : Blo 1303970 1305063 := bstep (se 1 (by rfl) ⟨978797, by rfl⟩ : syracuseStep 1305063 = 1957595) B1957595
theorem B1468903 : Blo 1303970 1468903 := bstep (se 1 (by rfl) ⟨1101677, by rfl⟩ : syracuseStep 1468903 = 2203355) B2203355
theorem B3303929 : Blo 1303970 3303929 := bstep (se 2 (by rfl) ⟨1238973, by rfl⟩ : syracuseStep 3303929 = 2477947) B2477947
theorem B56396411 : Blo 1303970 56396411 := bstep (se 1 (by rfl) ⟨42297308, by rfl⟩ : syracuseStep 56396411 = 84594617) B84594617
theorem B1305243 : Blo 1303970 1305243 := bstep (se 1 (by rfl) ⟨978932, by rfl⟩ : syracuseStep 1305243 = 1957865) B1957865
theorem B3304091 : Blo 1303970 3304091 := bstep (se 1 (by rfl) ⟨2478068, by rfl⟩ : syracuseStep 3304091 = 4956137) B4956137
theorem B1469083 : Blo 1303970 1469083 := bstep (se 1 (by rfl) ⟨1101812, by rfl⟩ : syracuseStep 1469083 = 2203625) B2203625
theorem B1567855 : Blo 1303970 1567855 := bstep (se 1 (by rfl) ⟨1175891, by rfl⟩ : syracuseStep 1567855 = 2351783) B2351783
theorem B1305711 : Blo 1303970 1305711 := bstep (se 1 (by rfl) ⟨979283, by rfl⟩ : syracuseStep 1305711 = 1958567) B1958567
theorem B3304577 : Blo 1303970 3304577 := bstep (se 2 (by rfl) ⟨1239216, by rfl⟩ : syracuseStep 3304577 = 2478433) B2478433
theorem B1305791 : Blo 1303970 1305791 := bstep (se 1 (by rfl) ⟨979343, by rfl⟩ : syracuseStep 1305791 = 1958687) B1958687
theorem B1305807 : Blo 1303970 1305807 := bstep (se 1 (by rfl) ⟨979355, by rfl⟩ : syracuseStep 1305807 = 1958711) B1958711
theorem B3304759 : Blo 1303970 3304759 := bstep (se 1 (by rfl) ⟨2478569, by rfl⟩ : syracuseStep 3304759 = 4957139) B4957139
theorem B1305927 : Blo 1303970 1305927 := bstep (se 1 (by rfl) ⟨979445, by rfl⟩ : syracuseStep 1305927 = 1958891) B1958891
theorem B5287295 : Blo 1303970 5287295 := bstep (se 1 (by rfl) ⟨3965471, by rfl⟩ : syracuseStep 5287295 = 7930943) B7930943
theorem B9907595 : Blo 1303970 9907595 := bstep (se 1 (by rfl) ⟨7430696, by rfl⟩ : syracuseStep 9907595 = 14861393) B14861393
theorem B8367583 : Blo 1303970 8367583 := bstep (se 1 (by rfl) ⟨6275687, by rfl⟩ : syracuseStep 8367583 = 12551375) B12551375
theorem B3305063 : Blo 1303970 3305063 := bstep (se 1 (by rfl) ⟨2478797, by rfl⟩ : syracuseStep 3305063 = 4957595) B4957595
theorem B6606521 : Blo 1303970 6606521 := bstep (se 2 (by rfl) ⟨2477445, by rfl⟩ : syracuseStep 6606521 = 4954891) B4954891
theorem B8933257 : Blo 1303970 8933257 := bstep (se 2 (by rfl) ⟨3349971, by rfl⟩ : syracuseStep 8933257 = 6699943) B6699943
theorem B3305387 : Blo 1303970 3305387 := bstep (se 1 (by rfl) ⟨2479040, by rfl⟩ : syracuseStep 3305387 = 4958081) B4958081
theorem B9916343 : Blo 1303970 9916343 := bstep (se 1 (by rfl) ⟨7437257, by rfl⟩ : syracuseStep 9916343 = 14874515) B14874515
theorem B2478023 : Blo 1303970 2478023 := bstep (se 1 (by rfl) ⟨1858517, by rfl⟩ : syracuseStep 2478023 = 3717035) B3717035
theorem B2478107 : Blo 1303970 2478107 := bstep (se 1 (by rfl) ⟨1858580, by rfl⟩ : syracuseStep 2478107 = 3717161) B3717161
theorem B2936879 : Blo 1303970 2936879 := bstep (se 1 (by rfl) ⟨2202659, by rfl⟩ : syracuseStep 2936879 = 4405319) B4405319
theorem B21172529 : Blo 1303970 21172529 := bstep (se 2 (by rfl) ⟨7939698, by rfl⟩ : syracuseStep 21172529 = 15879397) B15879397
theorem B5288399 : Blo 1303970 5288399 := bstep (se 1 (by rfl) ⟨3966299, by rfl⟩ : syracuseStep 5288399 = 7932599) B7932599
theorem B2937455 : Blo 1303970 2937455 := bstep (se 1 (by rfl) ⟨2203091, by rfl⟩ : syracuseStep 2937455 = 4406183) B4406183
theorem B42349205 : Blo 1303970 42349205 := bstep (se 6 (by rfl) ⟨992559, by rfl⟩ : syracuseStep 42349205 = 1985119) B1985119
theorem B1651367 : Blo 1303970 1651367 := bstep (se 1 (by rfl) ⟨1238525, by rfl⟩ : syracuseStep 1651367 = 2477051) B2477051
theorem B5288759 : Blo 1303970 5288759 := bstep (se 1 (by rfl) ⟨3966569, by rfl⟩ : syracuseStep 5288759 = 7933139) B7933139
theorem B3715895 : Blo 1303970 3715895 := bstep (se 1 (by rfl) ⟨2786921, by rfl⟩ : syracuseStep 3715895 = 5573843) B5573843
theorem B1651691 : Blo 1303970 1651691 := bstep (se 1 (by rfl) ⟨1238768, by rfl⟩ : syracuseStep 1651691 = 2477537) B2477537
theorem B7050401 : Blo 1303970 7050401 := bstep (se 2 (by rfl) ⟨2643900, by rfl⟩ : syracuseStep 7050401 = 5287801) B5287801
theorem B2200999 : Blo 1303970 2200999 := bstep (se 1 (by rfl) ⟨1650749, by rfl⟩ : syracuseStep 2200999 = 3301499) B3301499
theorem B2201087 : Blo 1303970 2201087 := bstep (se 1 (by rfl) ⟨1650815, by rfl⟩ : syracuseStep 2201087 = 3301631) B3301631
theorem B3626527 : Blo 1303970 3626527 := bstep (se 1 (by rfl) ⟨2719895, by rfl⟩ : syracuseStep 3626527 = 5439791) B5439791
theorem B6608465 : Blo 1303970 6608465 := bstep (se 2 (by rfl) ⟨2478174, by rfl⟩ : syracuseStep 6608465 = 4956349) B4956349
theorem B2201195 : Blo 1303970 2201195 := bstep (se 1 (by rfl) ⟨1650896, by rfl⟩ : syracuseStep 2201195 = 3301793) B3301793
theorem B4953737 : Blo 1303970 4953737 := bstep (se 2 (by rfl) ⟨1857651, by rfl⟩ : syracuseStep 4953737 = 3715303) B3715303
theorem B6608627 : Blo 1303970 6608627 := bstep (se 1 (by rfl) ⟨4956470, by rfl⟩ : syracuseStep 6608627 = 9912941) B9912941
theorem B2201465 : Blo 1303970 2201465 := bstep (se 2 (by rfl) ⟨825549, by rfl⟩ : syracuseStep 2201465 = 1651099) B1651099
theorem B7427963 : Blo 1303970 7427963 := bstep (se 1 (by rfl) ⟨5570972, by rfl⟩ : syracuseStep 7427963 = 11141945) B11141945
theorem B1956071 : Blo 1303970 1956071 := bstep (se 1 (by rfl) ⟨1467053, by rfl⟩ : syracuseStep 1956071 = 2934107) B2934107
theorem B1956251 : Blo 1303970 1956251 := bstep (se 1 (by rfl) ⟨1467188, by rfl⟩ : syracuseStep 1956251 = 2934377) B2934377
theorem B7436711 : Blo 1303970 7436711 := bstep (se 1 (by rfl) ⟨5577533, by rfl⟩ : syracuseStep 7436711 = 11155067) B11155067
theorem B2202025 : Blo 1303970 2202025 := bstep (se 2 (by rfl) ⟨825759, by rfl⟩ : syracuseStep 2202025 = 1651519) B1651519
theorem B12540379 : Blo 1303970 12540379 := bstep (se 1 (by rfl) ⟨9405284, by rfl⟩ : syracuseStep 12540379 = 18810569) B18810569
theorem B1956647 : Blo 1303970 1956647 := bstep (se 1 (by rfl) ⟨1467485, by rfl⟩ : syracuseStep 1956647 = 2934971) B2934971
theorem B1956671 : Blo 1303970 1956671 := bstep (se 1 (by rfl) ⟨1467503, by rfl⟩ : syracuseStep 1956671 = 2935007) B2935007
theorem B7437167 : Blo 1303970 7437167 := bstep (se 1 (by rfl) ⟨5577875, by rfl⟩ : syracuseStep 7437167 = 11155751) B11155751
theorem B1956971 : Blo 1303970 1956971 := bstep (se 1 (by rfl) ⟨1467728, by rfl⟩ : syracuseStep 1956971 = 2935457) B2935457
theorem B1957115 : Blo 1303970 1957115 := bstep (se 1 (by rfl) ⟨1467836, by rfl⟩ : syracuseStep 1957115 = 2935673) B2935673
theorem B6610247 : Blo 1303970 6610247 := bstep (se 1 (by rfl) ⟨4957685, by rfl⟩ : syracuseStep 6610247 = 9915371) B9915371
theorem B2350427 : Blo 1303970 2350427 := bstep (se 1 (by rfl) ⟨1762820, by rfl⟩ : syracuseStep 2350427 = 3525641) B3525641
theorem B1957211 : Blo 1303970 1957211 := bstep (se 1 (by rfl) ⟨1467908, by rfl⟩ : syracuseStep 1957211 = 2935817) B2935817
theorem B1957241 : Blo 1303970 1957241 := bstep (se 2 (by rfl) ⟨733965, by rfl⟩ : syracuseStep 1957241 = 1467931) B1467931
theorem B1957247 : Blo 1303970 1957247 := bstep (se 1 (by rfl) ⟨1467935, by rfl⟩ : syracuseStep 1957247 = 2935871) B2935871
theorem B9903707 : Blo 1303970 9903707 := bstep (se 1 (by rfl) ⟨7427780, by rfl⟩ : syracuseStep 9903707 = 14855561) B14855561
theorem B2203247 : Blo 1303970 2203247 := bstep (se 1 (by rfl) ⟨1652435, by rfl⟩ : syracuseStep 2203247 = 3304871) B3304871
theorem B28221047 : Blo 1303970 28221047 := bstep (se 1 (by rfl) ⟨21165785, by rfl⟩ : syracuseStep 28221047 = 42331571) B42331571
theorem B8478431 : Blo 1303970 8478431 := bstep (se 1 (by rfl) ⟨6358823, by rfl⟩ : syracuseStep 8478431 = 12717647) B12717647
theorem B6438737 : Blo 1303970 6438737 := bstep (se 2 (by rfl) ⟨2414526, by rfl⟩ : syracuseStep 6438737 = 4829053) B4829053
theorem B1957799 : Blo 1303970 1957799 := bstep (se 1 (by rfl) ⟨1468349, by rfl⟩ : syracuseStep 1957799 = 2936699) B2936699
theorem B4702153 : Blo 1303970 4702153 := bstep (se 2 (by rfl) ⟨1763307, by rfl⟩ : syracuseStep 4702153 = 3526615) B3526615
theorem B95248345 : Blo 1303970 95248345 := bstep (se 2 (by rfl) ⟨35718129, by rfl⟩ : syracuseStep 95248345 = 71436259) B71436259
theorem B1957871 : Blo 1303970 1957871 := bstep (se 1 (by rfl) ⟨1468403, by rfl⟩ : syracuseStep 1957871 = 2936807) B2936807
theorem B1957919 : Blo 1303970 1957919 := bstep (se 1 (by rfl) ⟨1468439, by rfl⟩ : syracuseStep 1957919 = 2936879) B2936879
theorem B14115019 : Blo 1303970 14115019 := bstep (se 1 (by rfl) ⟨10586264, by rfl⟩ : syracuseStep 14115019 = 21172529) B21172529
theorem B21168377 : Blo 1303970 21168377 := bstep (se 2 (by rfl) ⟨7938141, by rfl⟩ : syracuseStep 21168377 = 15876283) B15876283
theorem B1958303 : Blo 1303970 1958303 := bstep (se 1 (by rfl) ⟨1468727, by rfl⟩ : syracuseStep 1958303 = 2937455) B2937455
theorem B15057323 : Blo 1303970 15057323 := bstep (se 1 (by rfl) ⟨11292992, by rfl⟩ : syracuseStep 15057323 = 22585985) B22585985
theorem B16720505 : Blo 1303970 16720505 := bstep (se 2 (by rfl) ⟨6270189, by rfl⟩ : syracuseStep 16720505 = 12540379) B12540379
theorem B1958537 : Blo 1303970 1958537 := bstep (se 2 (by rfl) ⟨734451, by rfl⟩ : syracuseStep 1958537 = 1468903) B1468903
theorem B26804951 : Blo 1303970 26804951 := bstep (se 1 (by rfl) ⟨20103713, by rfl⟩ : syracuseStep 26804951 = 40207427) B40207427
theorem B1958777 : Blo 1303970 1958777 := bstep (se 2 (by rfl) ⟨734541, by rfl⟩ : syracuseStep 1958777 = 1469083) B1469083
theorem B14099453 : Blo 1303970 14099453 := bstep (se 3 (by rfl) ⟨2643647, by rfl⟩ : syracuseStep 14099453 = 5287295) B5287295
theorem B1467391 : Blo 1303970 1467391 := bstep (se 1 (by rfl) ⟨1100543, by rfl⟩ : syracuseStep 1467391 = 2201087) B2201087
theorem B1467463 : Blo 1303970 1467463 := bstep (se 1 (by rfl) ⟨1100597, by rfl⟩ : syracuseStep 1467463 = 2201195) B2201195
theorem B3302491 : Blo 1303970 3302491 := bstep (se 1 (by rfl) ⟨2476868, by rfl⟩ : syracuseStep 3302491 = 4953737) B4953737
theorem B1467643 : Blo 1303970 1467643 := bstep (se 1 (by rfl) ⟨1100732, by rfl⟩ : syracuseStep 1467643 = 2201465) B2201465
theorem B1304047 : Blo 1303970 1304047 := bstep (se 1 (by rfl) ⟨978035, by rfl⟩ : syracuseStep 1304047 = 1956071) B1956071
theorem B1304167 : Blo 1303970 1304167 := bstep (se 1 (by rfl) ⟨978125, by rfl⟩ : syracuseStep 1304167 = 1956251) B1956251
theorem B4957807 : Blo 1303970 4957807 := bstep (se 1 (by rfl) ⟨3718355, by rfl⟩ : syracuseStep 4957807 = 7436711) B7436711
theorem B1304431 : Blo 1303970 1304431 := bstep (se 1 (by rfl) ⟨978323, by rfl⟩ : syracuseStep 1304431 = 1956647) B1956647
theorem B1304447 : Blo 1303970 1304447 := bstep (se 1 (by rfl) ⟨978335, by rfl⟩ : syracuseStep 1304447 = 1956671) B1956671
theorem B2934665 : Blo 1303970 2934665 := bstep (se 2 (by rfl) ⟨1100499, by rfl⟩ : syracuseStep 2934665 = 2200999) B2200999
theorem B4958111 : Blo 1303970 4958111 := bstep (se 1 (by rfl) ⟨3718583, by rfl⟩ : syracuseStep 4958111 = 7437167) B7437167
theorem B4835369 : Blo 1303970 4835369 := bstep (se 2 (by rfl) ⟨1813263, by rfl⟩ : syracuseStep 4835369 = 3626527) B3626527
theorem B1304647 : Blo 1303970 1304647 := bstep (se 1 (by rfl) ⟨978485, by rfl⟩ : syracuseStep 1304647 = 1956971) B1956971
theorem B1304743 : Blo 1303970 1304743 := bstep (se 1 (by rfl) ⟨978557, by rfl⟩ : syracuseStep 1304743 = 1957115) B1957115
theorem B1304807 : Blo 1303970 1304807 := bstep (se 1 (by rfl) ⟨978605, by rfl⟩ : syracuseStep 1304807 = 1957211) B1957211
theorem B1304827 : Blo 1303970 1304827 := bstep (se 1 (by rfl) ⟨978620, by rfl⟩ : syracuseStep 1304827 = 1957241) B1957241
theorem B1304831 : Blo 1303970 1304831 := bstep (se 1 (by rfl) ⟨978623, by rfl⟩ : syracuseStep 1304831 = 1957247) B1957247
theorem B6605063 : Blo 1303970 6605063 := bstep (se 1 (by rfl) ⟨4953797, by rfl⟩ : syracuseStep 6605063 = 9907595) B9907595
theorem B1468831 : Blo 1303970 1468831 := bstep (se 1 (by rfl) ⟨1101623, by rfl⟩ : syracuseStep 1468831 = 2203247) B2203247
theorem B6269537 : Blo 1303970 6269537 := bstep (se 2 (by rfl) ⟨2351076, by rfl⟩ : syracuseStep 6269537 = 4702153) B4702153
theorem B1305199 : Blo 1303970 1305199 := bstep (se 1 (by rfl) ⟨978899, by rfl⟩ : syracuseStep 1305199 = 1957799) B1957799
theorem B1305247 : Blo 1303970 1305247 := bstep (se 1 (by rfl) ⟨978935, by rfl⟩ : syracuseStep 1305247 = 1957871) B1957871
theorem B1305327 : Blo 1303970 1305327 := bstep (se 1 (by rfl) ⟨978995, by rfl⟩ : syracuseStep 1305327 = 1957991) B1957991
theorem B3304223 : Blo 1303970 3304223 := bstep (se 1 (by rfl) ⟨2478167, by rfl⟩ : syracuseStep 3304223 = 4956335) B4956335
theorem B1305415 : Blo 1303970 1305415 := bstep (se 1 (by rfl) ⟨979061, by rfl⟩ : syracuseStep 1305415 = 1958123) B1958123
theorem B1305455 : Blo 1303970 1305455 := bstep (se 1 (by rfl) ⟨979091, by rfl⟩ : syracuseStep 1305455 = 1958183) B1958183
theorem B3525599 : Blo 1303970 3525599 := bstep (se 1 (by rfl) ⟨2644199, by rfl⟩ : syracuseStep 3525599 = 5288399) B5288399
theorem B28232803 : Blo 1303970 28232803 := bstep (se 1 (by rfl) ⟨21174602, by rfl⟩ : syracuseStep 28232803 = 42349205) B42349205
theorem B1305755 : Blo 1303970 1305755 := bstep (se 1 (by rfl) ⟨979316, by rfl⟩ : syracuseStep 1305755 = 1958633) B1958633
theorem B3525839 : Blo 1303970 3525839 := bstep (se 1 (by rfl) ⟨2644379, by rfl⟩ : syracuseStep 3525839 = 5288759) B5288759
theorem B2936033 : Blo 1303970 2936033 := bstep (se 2 (by rfl) ⟨1101012, by rfl⟩ : syracuseStep 2936033 = 2202025) B2202025
theorem B144748129 : Blo 1303970 144748129 := bstep (se 2 (by rfl) ⟨54280548, by rfl⟩ : syracuseStep 144748129 = 108561097) B108561097
theorem B25071221 : Blo 1303970 25071221 := bstep (se 5 (by rfl) ⟨1175213, by rfl⟩ : syracuseStep 25071221 = 2350427) B2350427
theorem B180752093 : Blo 1303970 180752093 := bstep (se 3 (by rfl) ⟨33891017, by rfl⟩ : syracuseStep 180752093 = 67782035) B67782035
theorem B31747895 : Blo 1303970 31747895 := bstep (se 1 (by rfl) ⟨23810921, by rfl⟩ : syracuseStep 31747895 = 47621843) B47621843
theorem B4951975 : Blo 1303970 4951975 := bstep (se 1 (by rfl) ⟨3713981, by rfl⟩ : syracuseStep 4951975 = 7427963) B7427963
theorem B1650719 : Blo 1303970 1650719 := bstep (se 1 (by rfl) ⟨1238039, by rfl⟩ : syracuseStep 1650719 = 2476079) B2476079
theorem B3715247 : Blo 1303970 3715247 := bstep (se 1 (by rfl) ⟨2786435, by rfl⟩ : syracuseStep 3715247 = 5572871) B5572871
theorem B4403483 : Blo 1303970 4403483 := bstep (se 1 (by rfl) ⟨3302612, by rfl⟩ : syracuseStep 4403483 = 6605225) B6605225
theorem B37597607 : Blo 1303970 37597607 := bstep (se 1 (by rfl) ⟨28198205, by rfl⟩ : syracuseStep 37597607 = 56396411) B56396411
theorem B4403645 : Blo 1303970 4403645 := bstep (se 3 (by rfl) ⟨825683, by rfl⟩ : syracuseStep 4403645 = 1651367) B1651367
theorem B9909053 : Blo 1303970 9909053 := bstep (se 3 (by rfl) ⟨1857947, by rfl⟩ : syracuseStep 9909053 = 3715895) B3715895
theorem B18814031 : Blo 1303970 18814031 := bstep (se 1 (by rfl) ⟨14110523, by rfl⟩ : syracuseStep 18814031 = 28221047) B28221047
theorem B4404347 : Blo 1303970 4404347 := bstep (se 1 (by rfl) ⟨3303260, by rfl⟩ : syracuseStep 4404347 = 6606521) B6606521
theorem B4404509 : Blo 1303970 4404509 := bstep (se 3 (by rfl) ⟨825845, by rfl⟩ : syracuseStep 4404509 = 1651691) B1651691
theorem B126997793 : Blo 1303970 126997793 := bstep (se 2 (by rfl) ⟨47624172, by rfl⟩ : syracuseStep 126997793 = 95248345) B95248345
theorem B1652015 : Blo 1303970 1652015 := bstep (se 1 (by rfl) ⟨1239011, by rfl⟩ : syracuseStep 1652015 = 2478023) B2478023
theorem B1652071 : Blo 1303970 1652071 := bstep (se 1 (by rfl) ⟨1239053, by rfl⟩ : syracuseStep 1652071 = 2478107) B2478107
theorem B2938283 : Blo 1303970 2938283 := bstep (se 1 (by rfl) ⟨2203712, by rfl⟩ : syracuseStep 2938283 = 4407425) B4407425
theorem B6608303 : Blo 1303970 6608303 := bstep (se 1 (by rfl) ⟨4956227, by rfl⟩ : syracuseStep 6608303 = 9912455) B9912455
theorem B2233807 : Blo 1303970 2233807 := bstep (se 1 (by rfl) ⟨1675355, by rfl⟩ : syracuseStep 2233807 = 3350711) B3350711
theorem B8361893 : Blo 1303970 8361893 := bstep (se 4 (by rfl) ⟨783927, by rfl⟩ : syracuseStep 8361893 = 1567855) B1567855
theorem B1857583 : Blo 1303970 1857583 := bstep (se 1 (by rfl) ⟨1393187, by rfl⟩ : syracuseStep 1857583 = 2786375) B2786375
theorem B4700267 : Blo 1303970 4700267 := bstep (se 1 (by rfl) ⟨3525200, by rfl⟩ : syracuseStep 4700267 = 7050401) B7050401
theorem B4405643 : Blo 1303970 4405643 := bstep (se 1 (by rfl) ⟨3304232, by rfl⟩ : syracuseStep 4405643 = 6608465) B6608465
theorem B4405751 : Blo 1303970 4405751 := bstep (se 1 (by rfl) ⟨3304313, by rfl⟩ : syracuseStep 4405751 = 6608627) B6608627
theorem B4954679 : Blo 1303970 4954679 := bstep (se 1 (by rfl) ⟨3716009, by rfl⟩ : syracuseStep 4954679 = 7432019) B7432019
theorem B2202167 : Blo 1303970 2202167 := bstep (se 1 (by rfl) ⟨1651625, by rfl⟩ : syracuseStep 2202167 = 3303251) B3303251
theorem B2202619 : Blo 1303970 2202619 := bstep (se 1 (by rfl) ⟨1651964, by rfl⟩ : syracuseStep 2202619 = 3303929) B3303929
theorem B4406345 : Blo 1303970 4406345 := bstep (se 2 (by rfl) ⟨1652379, by rfl⟩ : syracuseStep 4406345 = 3304759) B3304759
theorem B2202727 : Blo 1303970 2202727 := bstep (se 1 (by rfl) ⟨1652045, by rfl⟩ : syracuseStep 2202727 = 3304091) B3304091
theorem B11156777 : Blo 1303970 11156777 := bstep (se 2 (by rfl) ⟨4183791, by rfl⟩ : syracuseStep 11156777 = 8367583) B8367583
theorem B47644037 : Blo 1303970 47644037 := bstep (se 4 (by rfl) ⟨4466628, by rfl⟩ : syracuseStep 47644037 = 8933257) B8933257
theorem B2203051 : Blo 1303970 2203051 := bstep (se 1 (by rfl) ⟨1652288, by rfl⟩ : syracuseStep 2203051 = 3304577) B3304577
theorem B17169965 : Blo 1303970 17169965 := bstep (se 3 (by rfl) ⟨3219368, by rfl⟩ : syracuseStep 17169965 = 6438737) B6438737
theorem B4406831 : Blo 1303970 4406831 := bstep (se 1 (by rfl) ⟨3305123, by rfl⟩ : syracuseStep 4406831 = 6610247) B6610247
theorem B4177565 : Blo 1303970 4177565 := bstep (se 3 (by rfl) ⟨783293, by rfl⟩ : syracuseStep 4177565 = 1566587) B1566587
theorem B6602471 : Blo 1303970 6602471 := bstep (se 1 (by rfl) ⟨4951853, by rfl⟩ : syracuseStep 6602471 = 9903707) B9903707
theorem B2203375 : Blo 1303970 2203375 := bstep (se 1 (by rfl) ⟨1652531, by rfl⟩ : syracuseStep 2203375 = 3305063) B3305063
theorem B5652287 : Blo 1303970 5652287 := bstep (se 1 (by rfl) ⟨4239215, by rfl⟩ : syracuseStep 5652287 = 8478431) B8478431
theorem B1957769 : Blo 1303970 1957769 := bstep (se 2 (by rfl) ⟨734163, by rfl⟩ : syracuseStep 1957769 = 1468327) B1468327
theorem B2203591 : Blo 1303970 2203591 := bstep (se 1 (by rfl) ⟨1652693, by rfl⟩ : syracuseStep 2203591 = 3305387) B3305387
theorem B6610895 : Blo 1303970 6610895 := bstep (se 1 (by rfl) ⟨4958171, by rfl⟩ : syracuseStep 6610895 = 9916343) B9916343
theorem B1958441 : Blo 1303970 1958441 := bstep (se 2 (by rfl) ⟨734415, by rfl⟩ : syracuseStep 1958441 = 1468831) B1468831
theorem B12542687 : Blo 1303970 12542687 := bstep (se 1 (by rfl) ⟨9407015, by rfl⟩ : syracuseStep 12542687 = 18814031) B18814031
theorem B84665195 : Blo 1303970 84665195 := bstep (se 1 (by rfl) ⟨63498896, by rfl⟩ : syracuseStep 84665195 = 126997793) B126997793
theorem B1958855 : Blo 1303970 1958855 := bstep (se 1 (by rfl) ⟨1469141, by rfl⟩ : syracuseStep 1958855 = 2938283) B2938283
theorem B37643737 : Blo 1303970 37643737 := bstep (se 2 (by rfl) ⟨14116401, by rfl⟩ : syracuseStep 37643737 = 28232803) B28232803
theorem B3303119 : Blo 1303970 3303119 := bstep (se 1 (by rfl) ⟨2477339, by rfl⟩ : syracuseStep 3303119 = 4954679) B4954679
theorem B1468111 : Blo 1303970 1468111 := bstep (se 1 (by rfl) ⟨1101083, by rfl⟩ : syracuseStep 1468111 = 2202167) B2202167
theorem B4179691 : Blo 1303970 4179691 := bstep (se 1 (by rfl) ⟨3134768, by rfl⟩ : syracuseStep 4179691 = 6269537) B6269537
theorem B192997505 : Blo 1303970 192997505 := bstep (se 2 (by rfl) ⟨72374064, by rfl⟩ : syracuseStep 192997505 = 144748129) B144748129
theorem B31762691 : Blo 1303970 31762691 := bstep (se 1 (by rfl) ⟨23822018, by rfl⟩ : syracuseStep 31762691 = 47644037) B47644037
theorem B11446643 : Blo 1303970 11446643 := bstep (se 1 (by rfl) ⟨8584982, by rfl⟩ : syracuseStep 11446643 = 17169965) B17169965
theorem B16714147 : Blo 1303970 16714147 := bstep (se 1 (by rfl) ⟨12535610, by rfl⟩ : syracuseStep 16714147 = 25071221) B25071221
theorem B11913637 : Blo 1303970 11913637 := bstep (se 4 (by rfl) ⟨1116903, by rfl⟩ : syracuseStep 11913637 = 2233807) B2233807
theorem B4401647 : Blo 1303970 4401647 := bstep (se 1 (by rfl) ⟨3301235, by rfl⟩ : syracuseStep 4401647 = 6602471) B6602471
theorem B1305179 : Blo 1303970 1305179 := bstep (se 1 (by rfl) ⟨978884, by rfl⟩ : syracuseStep 1305179 = 1957769) B1957769
theorem B1305279 : Blo 1303970 1305279 := bstep (se 1 (by rfl) ⟨978959, by rfl⟩ : syracuseStep 1305279 = 1957919) B1957919
theorem B4401917 : Blo 1303970 4401917 := bstep (se 3 (by rfl) ⟨825359, by rfl⟩ : syracuseStep 4401917 = 1650719) B1650719
theorem B2476831 : Blo 1303970 2476831 := bstep (se 1 (by rfl) ⟨1857623, by rfl⟩ : syracuseStep 2476831 = 3715247) B3715247
theorem B2935655 : Blo 1303970 2935655 := bstep (se 1 (by rfl) ⟨2201741, by rfl⟩ : syracuseStep 2935655 = 4403483) B4403483
theorem B9907109 : Blo 1303970 9907109 := bstep (se 4 (by rfl) ⟨928791, by rfl⟩ : syracuseStep 9907109 = 1857583) B1857583
theorem B18820025 : Blo 1303970 18820025 := bstep (se 2 (by rfl) ⟨7057509, by rfl⟩ : syracuseStep 18820025 = 14115019) B14115019
theorem B1305535 : Blo 1303970 1305535 := bstep (se 1 (by rfl) ⟨979151, by rfl⟩ : syracuseStep 1305535 = 1958303) B1958303
theorem B10038215 : Blo 1303970 10038215 := bstep (se 1 (by rfl) ⟨7528661, by rfl⟩ : syracuseStep 10038215 = 15057323) B15057323
theorem B2935763 : Blo 1303970 2935763 := bstep (se 1 (by rfl) ⟨2201822, by rfl⟩ : syracuseStep 2935763 = 4403645) B4403645
theorem B1305691 : Blo 1303970 1305691 := bstep (se 1 (by rfl) ⟨979268, by rfl⟩ : syracuseStep 1305691 = 1958537) B1958537
theorem B17869967 : Blo 1303970 17869967 := bstep (se 1 (by rfl) ⟨13402475, by rfl⟩ : syracuseStep 17869967 = 26804951) B26804951
theorem B6606035 : Blo 1303970 6606035 := bstep (se 1 (by rfl) ⟨4954526, by rfl⟩ : syracuseStep 6606035 = 9909053) B9909053
theorem B1305851 : Blo 1303970 1305851 := bstep (se 1 (by rfl) ⟨979388, by rfl⟩ : syracuseStep 1305851 = 1958777) B1958777
theorem B9399635 : Blo 1303970 9399635 := bstep (se 1 (by rfl) ⟨7049726, by rfl⟩ : syracuseStep 9399635 = 14099453) B14099453
theorem B2936231 : Blo 1303970 2936231 := bstep (se 1 (by rfl) ⟨2202173, by rfl⟩ : syracuseStep 2936231 = 4404347) B4404347
theorem B2936339 : Blo 1303970 2936339 := bstep (se 1 (by rfl) ⟨2202254, by rfl⟩ : syracuseStep 2936339 = 4404509) B4404509
theorem B3305407 : Blo 1303970 3305407 := bstep (se 1 (by rfl) ⟨2479055, by rfl⟩ : syracuseStep 3305407 = 4958111) B4958111
theorem B5574595 : Blo 1303970 5574595 := bstep (se 1 (by rfl) ⟨4180946, by rfl⟩ : syracuseStep 5574595 = 8361893) B8361893
theorem B2936825 : Blo 1303970 2936825 := bstep (se 2 (by rfl) ⟨1101309, by rfl⟩ : syracuseStep 2936825 = 2202619) B2202619
theorem B3223579 : Blo 1303970 3223579 := bstep (se 1 (by rfl) ⟨2417684, by rfl⟩ : syracuseStep 3223579 = 4835369) B4835369
theorem B3133511 : Blo 1303970 3133511 := bstep (se 1 (by rfl) ⟨2350133, by rfl⟩ : syracuseStep 3133511 = 4700267) B4700267
theorem B4403321 : Blo 1303970 4403321 := bstep (se 2 (by rfl) ⟨1651245, by rfl⟩ : syracuseStep 4403321 = 3302491) B3302491
theorem B2936969 : Blo 1303970 2936969 := bstep (se 2 (by rfl) ⟨1101363, by rfl⟩ : syracuseStep 2936969 = 2202727) B2202727
theorem B4403375 : Blo 1303970 4403375 := bstep (se 1 (by rfl) ⟨3302531, by rfl⟩ : syracuseStep 4403375 = 6605063) B6605063
theorem B2937095 : Blo 1303970 2937095 := bstep (se 1 (by rfl) ⟨2202821, by rfl⟩ : syracuseStep 2937095 = 4405643) B4405643
theorem B2937167 : Blo 1303970 2937167 := bstep (se 1 (by rfl) ⟨2202875, by rfl⟩ : syracuseStep 2937167 = 4405751) B4405751
theorem B2937401 : Blo 1303970 2937401 := bstep (se 2 (by rfl) ⟨1101525, by rfl⟩ : syracuseStep 2937401 = 2203051) B2203051
theorem B2937563 : Blo 1303970 2937563 := bstep (se 1 (by rfl) ⟨2203172, by rfl⟩ : syracuseStep 2937563 = 4406345) B4406345
theorem B2937833 : Blo 1303970 2937833 := bstep (se 2 (by rfl) ⟨1101687, by rfl⟩ : syracuseStep 2937833 = 2203375) B2203375
theorem B2937887 : Blo 1303970 2937887 := bstep (se 1 (by rfl) ⟨2203415, by rfl⟩ : syracuseStep 2937887 = 4406831) B4406831
theorem B120501395 : Blo 1303970 120501395 := bstep (se 1 (by rfl) ⟨90376046, by rfl⟩ : syracuseStep 120501395 = 180752093) B180752093
theorem B21165263 : Blo 1303970 21165263 := bstep (se 1 (by rfl) ⟨15873947, by rfl⟩ : syracuseStep 21165263 = 31747895) B31747895
theorem B2938121 : Blo 1303970 2938121 := bstep (se 2 (by rfl) ⟨1101795, by rfl⟩ : syracuseStep 2938121 = 2203591) B2203591
theorem B14112251 : Blo 1303970 14112251 := bstep (se 1 (by rfl) ⟨10584188, by rfl⟩ : syracuseStep 14112251 = 21168377) B21168377
theorem B25065071 : Blo 1303970 25065071 := bstep (se 1 (by rfl) ⟨18798803, by rfl⟩ : syracuseStep 25065071 = 37597607) B37597607
theorem B11147003 : Blo 1303970 11147003 := bstep (se 1 (by rfl) ⟨8360252, by rfl⟩ : syracuseStep 11147003 = 16720505) B16720505
theorem B4405373 : Blo 1303970 4405373 := bstep (se 3 (by rfl) ⟨826007, by rfl⟩ : syracuseStep 4405373 = 1652015) B1652015
theorem B4405535 : Blo 1303970 4405535 := bstep (se 1 (by rfl) ⟨3304151, by rfl⟩ : syracuseStep 4405535 = 6608303) B6608303
theorem B1956443 : Blo 1303970 1956443 := bstep (se 1 (by rfl) ⟨1467332, by rfl⟩ : syracuseStep 1956443 = 2934665) B2934665
theorem B1956521 : Blo 1303970 1956521 := bstep (se 2 (by rfl) ⟨733695, by rfl⟩ : syracuseStep 1956521 = 1467391) B1467391
theorem B1956617 : Blo 1303970 1956617 := bstep (se 2 (by rfl) ⟨733731, by rfl⟩ : syracuseStep 1956617 = 1467463) B1467463
theorem B1956857 : Blo 1303970 1956857 := bstep (se 2 (by rfl) ⟨733821, by rfl⟩ : syracuseStep 1956857 = 1467643) B1467643
theorem B2202761 : Blo 1303970 2202761 := bstep (se 2 (by rfl) ⟨826035, by rfl⟩ : syracuseStep 2202761 = 1652071) B1652071
theorem B2202815 : Blo 1303970 2202815 := bstep (se 1 (by rfl) ⟨1652111, by rfl⟩ : syracuseStep 2202815 = 3304223) B3304223
theorem B2350399 : Blo 1303970 2350399 := bstep (se 1 (by rfl) ⟨1762799, by rfl⟩ : syracuseStep 2350399 = 3525599) B3525599
theorem B2350559 : Blo 1303970 2350559 := bstep (se 1 (by rfl) ⟨1762919, by rfl⟩ : syracuseStep 2350559 = 3525839) B3525839
theorem B6610409 : Blo 1303970 6610409 := bstep (se 2 (by rfl) ⟨2478903, by rfl⟩ : syracuseStep 6610409 = 4957807) B4957807
theorem B1957355 : Blo 1303970 1957355 := bstep (se 1 (by rfl) ⟨1468016, by rfl⟩ : syracuseStep 1957355 = 2936033) B2936033
theorem B7437851 : Blo 1303970 7437851 := bstep (se 1 (by rfl) ⟨5578388, by rfl⟩ : syracuseStep 7437851 = 11156777) B11156777
theorem B2785043 : Blo 1303970 2785043 := bstep (se 1 (by rfl) ⟨2088782, by rfl⟩ : syracuseStep 2785043 = 4177565) B4177565
theorem B3768191 : Blo 1303970 3768191 := bstep (se 1 (by rfl) ⟨2826143, by rfl⟩ : syracuseStep 3768191 = 5652287) B5652287
theorem B6602633 : Blo 1303970 6602633 := bstep (se 2 (by rfl) ⟨2475987, by rfl⟩ : syracuseStep 6602633 = 4951975) B4951975
theorem B4407263 : Blo 1303970 4407263 := bstep (se 1 (by rfl) ⟨3305447, by rfl⟩ : syracuseStep 4407263 = 6610895) B6610895
theorem B2089007 : Blo 1303970 2089007 := bstep (se 1 (by rfl) ⟨1566755, by rfl⟩ : syracuseStep 2089007 = 3133511) B3133511
theorem B1957979 : Blo 1303970 1957979 := bstep (se 1 (by rfl) ⟨1468484, by rfl⟩ : syracuseStep 1957979 = 2936969) B2936969
theorem B1958063 : Blo 1303970 1958063 := bstep (se 1 (by rfl) ⟨1468547, by rfl⟩ : syracuseStep 1958063 = 2937095) B2937095
theorem B1958111 : Blo 1303970 1958111 := bstep (se 1 (by rfl) ⟨1468583, by rfl⟩ : syracuseStep 1958111 = 2937167) B2937167
theorem B1958267 : Blo 1303970 1958267 := bstep (se 1 (by rfl) ⟨1468700, by rfl⟩ : syracuseStep 1958267 = 2937401) B2937401
theorem B1958375 : Blo 1303970 1958375 := bstep (se 1 (by rfl) ⟨1468781, by rfl⟩ : syracuseStep 1958375 = 2937563) B2937563
theorem B15884849 : Blo 1303970 15884849 := bstep (se 2 (by rfl) ⟨5956818, by rfl⟩ : syracuseStep 15884849 = 11913637) B11913637
theorem B56443463 : Blo 1303970 56443463 := bstep (se 1 (by rfl) ⟨42332597, by rfl⟩ : syracuseStep 56443463 = 84665195) B84665195
theorem B1958555 : Blo 1303970 1958555 := bstep (se 1 (by rfl) ⟨1468916, by rfl⟩ : syracuseStep 1958555 = 2937833) B2937833
theorem B1958591 : Blo 1303970 1958591 := bstep (se 1 (by rfl) ⟨1468943, by rfl⟩ : syracuseStep 1958591 = 2937887) B2937887
theorem B1958747 : Blo 1303970 1958747 := bstep (se 1 (by rfl) ⟨1469060, by rfl⟩ : syracuseStep 1958747 = 2938121) B2938121
theorem B30524381 : Blo 1303970 30524381 := bstep (se 3 (by rfl) ⟨5723321, by rfl⟩ : syracuseStep 30524381 = 11446643) B11446643
theorem B3302441 : Blo 1303970 3302441 := bstep (se 2 (by rfl) ⟨1238415, by rfl⟩ : syracuseStep 3302441 = 2476831) B2476831
theorem B7431335 : Blo 1303970 7431335 := bstep (se 1 (by rfl) ⟨5573501, by rfl⟩ : syracuseStep 7431335 = 11147003) B11147003
theorem B2934431 : Blo 1303970 2934431 := bstep (se 1 (by rfl) ⟨2200823, by rfl⟩ : syracuseStep 2934431 = 4401647) B4401647
theorem B1304295 : Blo 1303970 1304295 := bstep (se 1 (by rfl) ⟨978221, by rfl⟩ : syracuseStep 1304295 = 1956443) B1956443
theorem B1304347 : Blo 1303970 1304347 := bstep (se 1 (by rfl) ⟨978260, by rfl⟩ : syracuseStep 1304347 = 1956521) B1956521
theorem B2934611 : Blo 1303970 2934611 := bstep (se 1 (by rfl) ⟨2200958, by rfl⟩ : syracuseStep 2934611 = 4401917) B4401917
theorem B1304411 : Blo 1303970 1304411 := bstep (se 1 (by rfl) ⟨978308, by rfl⟩ : syracuseStep 1304411 = 1956617) B1956617
theorem B6604739 : Blo 1303970 6604739 := bstep (se 1 (by rfl) ⟨4953554, by rfl⟩ : syracuseStep 6604739 = 9907109) B9907109
theorem B1304571 : Blo 1303970 1304571 := bstep (se 1 (by rfl) ⟨978428, by rfl⟩ : syracuseStep 1304571 = 1956857) B1956857
theorem B1468507 : Blo 1303970 1468507 := bstep (se 1 (by rfl) ⟨1101380, by rfl⟩ : syracuseStep 1468507 = 2202761) B2202761
theorem B11913311 : Blo 1303970 11913311 := bstep (se 1 (by rfl) ⟨8934983, by rfl⟩ : syracuseStep 11913311 = 17869967) B17869967
theorem B1468543 : Blo 1303970 1468543 := bstep (se 1 (by rfl) ⟨1101407, by rfl⟩ : syracuseStep 1468543 = 2202815) B2202815
theorem B5572921 : Blo 1303970 5572921 := bstep (se 2 (by rfl) ⟨2089845, by rfl⟩ : syracuseStep 5572921 = 4179691) B4179691
theorem B1567039 : Blo 1303970 1567039 := bstep (se 1 (by rfl) ⟨1175279, by rfl⟩ : syracuseStep 1567039 = 2350559) B2350559
theorem B1304903 : Blo 1303970 1304903 := bstep (se 1 (by rfl) ⟨978677, by rfl⟩ : syracuseStep 1304903 = 1957355) B1957355
theorem B4958567 : Blo 1303970 4958567 := bstep (se 1 (by rfl) ⟨3718925, by rfl⟩ : syracuseStep 4958567 = 7437851) B7437851
theorem B4401755 : Blo 1303970 4401755 := bstep (se 1 (by rfl) ⟨3301316, by rfl⟩ : syracuseStep 4401755 = 6602633) B6602633
theorem B7432793 : Blo 1303970 7432793 := bstep (se 2 (by rfl) ⟨2787297, by rfl⟩ : syracuseStep 7432793 = 5574595) B5574595
theorem B2935547 : Blo 1303970 2935547 := bstep (se 1 (by rfl) ⟨2201660, by rfl⟩ : syracuseStep 2935547 = 4403321) B4403321
theorem B2935583 : Blo 1303970 2935583 := bstep (se 1 (by rfl) ⟨2201687, by rfl⟩ : syracuseStep 2935583 = 4403375) B4403375
theorem B1305627 : Blo 1303970 1305627 := bstep (se 1 (by rfl) ⟨979220, by rfl⟩ : syracuseStep 1305627 = 1958441) B1958441
theorem B22285529 : Blo 1303970 22285529 := bstep (se 2 (by rfl) ⟨8357073, by rfl⟩ : syracuseStep 22285529 = 16714147) B16714147
theorem B1305903 : Blo 1303970 1305903 := bstep (se 1 (by rfl) ⟨979427, by rfl⟩ : syracuseStep 1305903 = 1958855) B1958855
theorem B80334263 : Blo 1303970 80334263 := bstep (se 1 (by rfl) ⟨60250697, by rfl⟩ : syracuseStep 80334263 = 120501395) B120501395
theorem B14110175 : Blo 1303970 14110175 := bstep (se 1 (by rfl) ⟨10582631, by rfl⟩ : syracuseStep 14110175 = 21165263) B21165263
theorem B9408167 : Blo 1303970 9408167 := bstep (se 1 (by rfl) ⟨7056125, by rfl⟩ : syracuseStep 9408167 = 14112251) B14112251
theorem B2936915 : Blo 1303970 2936915 := bstep (se 1 (by rfl) ⟨2202686, by rfl⟩ : syracuseStep 2936915 = 4405373) B4405373
theorem B2937023 : Blo 1303970 2937023 := bstep (se 1 (by rfl) ⟨2202767, by rfl⟩ : syracuseStep 2937023 = 4405535) B4405535
theorem B3133865 : Blo 1303970 3133865 := bstep (se 2 (by rfl) ⟨1175199, by rfl⟩ : syracuseStep 3133865 = 2350399) B2350399
theorem B12546683 : Blo 1303970 12546683 := bstep (se 1 (by rfl) ⟨9410012, by rfl⟩ : syracuseStep 12546683 = 18820025) B18820025
theorem B4404023 : Blo 1303970 4404023 := bstep (se 1 (by rfl) ⟨3303017, by rfl⟩ : syracuseStep 4404023 = 6606035) B6606035
theorem B1856695 : Blo 1303970 1856695 := bstep (se 1 (by rfl) ⟨1392521, by rfl⟩ : syracuseStep 1856695 = 2785043) B2785043
theorem B26768573 : Blo 1303970 26768573 := bstep (se 3 (by rfl) ⟨5019107, by rfl⟩ : syracuseStep 26768573 = 10038215) B10038215
theorem B2512127 : Blo 1303970 2512127 := bstep (se 1 (by rfl) ⟨1884095, by rfl⟩ : syracuseStep 2512127 = 3768191) B3768191
theorem B2938175 : Blo 1303970 2938175 := bstep (se 1 (by rfl) ⟨2203631, by rfl⟩ : syracuseStep 2938175 = 4407263) B4407263
theorem B4298105 : Blo 1303970 4298105 := bstep (se 2 (by rfl) ⟨1611789, by rfl⟩ : syracuseStep 4298105 = 3223579) B3223579
theorem B514660013 : Blo 1303970 514660013 := bstep (se 3 (by rfl) ⟨96498752, by rfl⟩ : syracuseStep 514660013 = 192997505) B192997505
theorem B8361791 : Blo 1303970 8361791 := bstep (se 1 (by rfl) ⟨6271343, by rfl⟩ : syracuseStep 8361791 = 12542687) B12542687
theorem B16710047 : Blo 1303970 16710047 := bstep (se 1 (by rfl) ⟨12532535, by rfl⟩ : syracuseStep 16710047 = 25065071) B25065071
theorem B2202079 : Blo 1303970 2202079 := bstep (se 1 (by rfl) ⟨1651559, by rfl⟩ : syracuseStep 2202079 = 3303119) B3303119
theorem B21175127 : Blo 1303970 21175127 := bstep (se 1 (by rfl) ⟨15881345, by rfl⟩ : syracuseStep 21175127 = 31762691) B31762691
theorem B1957103 : Blo 1303970 1957103 := bstep (se 1 (by rfl) ⟨1467827, by rfl⟩ : syracuseStep 1957103 = 2935655) B2935655
theorem B50191649 : Blo 1303970 50191649 := bstep (se 2 (by rfl) ⟨18821868, by rfl⟩ : syracuseStep 50191649 = 37643737) B37643737
theorem B1957175 : Blo 1303970 1957175 := bstep (se 1 (by rfl) ⟨1467881, by rfl⟩ : syracuseStep 1957175 = 2935763) B2935763
theorem B6266423 : Blo 1303970 6266423 := bstep (se 1 (by rfl) ⟨4699817, by rfl⟩ : syracuseStep 6266423 = 9399635) B9399635
theorem B1957481 : Blo 1303970 1957481 := bstep (se 2 (by rfl) ⟨734055, by rfl⟩ : syracuseStep 1957481 = 1468111) B1468111
theorem B1957487 : Blo 1303970 1957487 := bstep (se 1 (by rfl) ⟨1468115, by rfl⟩ : syracuseStep 1957487 = 2936231) B2936231
theorem B4406939 : Blo 1303970 4406939 := bstep (se 1 (by rfl) ⟨3305204, by rfl⟩ : syracuseStep 4406939 = 6610409) B6610409
theorem B1957559 : Blo 1303970 1957559 := bstep (se 1 (by rfl) ⟨1468169, by rfl⟩ : syracuseStep 1957559 = 2936339) B2936339
theorem B4407209 : Blo 1303970 4407209 := bstep (se 2 (by rfl) ⟨1652703, by rfl⟩ : syracuseStep 4407209 = 3305407) B3305407
theorem B1957883 : Blo 1303970 1957883 := bstep (se 1 (by rfl) ⟨1468412, by rfl⟩ : syracuseStep 1957883 = 2936825) B2936825
theorem B1392671 : Blo 1303970 1392671 := bstep (se 1 (by rfl) ⟨1044503, by rfl⟩ : syracuseStep 1392671 = 2089007) B2089007
theorem B1957943 : Blo 1303970 1957943 := bstep (se 1 (by rfl) ⟨1468457, by rfl⟩ : syracuseStep 1957943 = 2936915) B2936915
theorem B1958009 : Blo 1303970 1958009 := bstep (se 2 (by rfl) ⟨734253, by rfl⟩ : syracuseStep 1958009 = 1468507) B1468507
theorem B1958015 : Blo 1303970 1958015 := bstep (se 1 (by rfl) ⟨1468511, by rfl⟩ : syracuseStep 1958015 = 2937023) B2937023
theorem B1958057 : Blo 1303970 1958057 := bstep (se 2 (by rfl) ⟨734271, by rfl⟩ : syracuseStep 1958057 = 1468543) B1468543
theorem B2089243 : Blo 1303970 2089243 := bstep (se 1 (by rfl) ⟨1566932, by rfl⟩ : syracuseStep 2089243 = 3133865) B3133865
theorem B7430561 : Blo 1303970 7430561 := bstep (se 2 (by rfl) ⟨2786460, by rfl⟩ : syracuseStep 7430561 = 5572921) B5572921
theorem B8364455 : Blo 1303970 8364455 := bstep (se 1 (by rfl) ⟨6273341, by rfl⟩ : syracuseStep 8364455 = 12546683) B12546683
theorem B2089385 : Blo 1303970 2089385 := bstep (se 2 (by rfl) ⟨783519, by rfl⟩ : syracuseStep 2089385 = 1567039) B1567039
theorem B20349587 : Blo 1303970 20349587 := bstep (se 1 (by rfl) ⟨15262190, by rfl⟩ : syracuseStep 20349587 = 30524381) B30524381
theorem B1958783 : Blo 1303970 1958783 := bstep (se 1 (by rfl) ⟨1469087, by rfl⟩ : syracuseStep 1958783 = 2938175) B2938175
theorem B343106675 : Blo 1303970 343106675 := bstep (se 1 (by rfl) ⟨257330006, by rfl⟩ : syracuseStep 343106675 = 514660013) B514660013
theorem B2475593 : Blo 1303970 2475593 := bstep (se 2 (by rfl) ⟨928347, by rfl⟩ : syracuseStep 2475593 = 1856695) B1856695
theorem B2934503 : Blo 1303970 2934503 := bstep (se 1 (by rfl) ⟨2200877, by rfl⟩ : syracuseStep 2934503 = 4401755) B4401755
theorem B14116751 : Blo 1303970 14116751 := bstep (se 1 (by rfl) ⟨10587563, by rfl⟩ : syracuseStep 14116751 = 21175127) B21175127
theorem B1304735 : Blo 1303970 1304735 := bstep (se 1 (by rfl) ⟨978551, by rfl⟩ : syracuseStep 1304735 = 1957103) B1957103
theorem B1304783 : Blo 1303970 1304783 := bstep (se 1 (by rfl) ⟨978587, by rfl⟩ : syracuseStep 1304783 = 1957175) B1957175
theorem B9406783 : Blo 1303970 9406783 := bstep (se 1 (by rfl) ⟨7055087, by rfl⟩ : syracuseStep 9406783 = 14110175) B14110175
theorem B1304987 : Blo 1303970 1304987 := bstep (se 1 (by rfl) ⟨978740, by rfl⟩ : syracuseStep 1304987 = 1957481) B1957481
theorem B1304991 : Blo 1303970 1304991 := bstep (se 1 (by rfl) ⟨978743, by rfl⟩ : syracuseStep 1304991 = 1957487) B1957487
theorem B1305039 : Blo 1303970 1305039 := bstep (se 1 (by rfl) ⟨978779, by rfl⟩ : syracuseStep 1305039 = 1957559) B1957559
theorem B1305255 : Blo 1303970 1305255 := bstep (se 1 (by rfl) ⟨978941, by rfl⟩ : syracuseStep 1305255 = 1957883) B1957883
theorem B1305319 : Blo 1303970 1305319 := bstep (se 1 (by rfl) ⟨978989, by rfl⟩ : syracuseStep 1305319 = 1957979) B1957979
theorem B1305375 : Blo 1303970 1305375 := bstep (se 1 (by rfl) ⟨979031, by rfl⟩ : syracuseStep 1305375 = 1958063) B1958063
theorem B1305407 : Blo 1303970 1305407 := bstep (se 1 (by rfl) ⟨979055, by rfl⟩ : syracuseStep 1305407 = 1958111) B1958111
theorem B1305511 : Blo 1303970 1305511 := bstep (se 1 (by rfl) ⟨979133, by rfl⟩ : syracuseStep 1305511 = 1958267) B1958267
theorem B1305583 : Blo 1303970 1305583 := bstep (se 1 (by rfl) ⟨979187, by rfl⟩ : syracuseStep 1305583 = 1958375) B1958375
theorem B37628975 : Blo 1303970 37628975 := bstep (se 1 (by rfl) ⟨28221731, by rfl⟩ : syracuseStep 37628975 = 56443463) B56443463
theorem B1305703 : Blo 1303970 1305703 := bstep (se 1 (by rfl) ⟨979277, by rfl⟩ : syracuseStep 1305703 = 1958555) B1958555
theorem B1305727 : Blo 1303970 1305727 := bstep (se 1 (by rfl) ⟨979295, by rfl⟩ : syracuseStep 1305727 = 1958591) B1958591
theorem B2936015 : Blo 1303970 2936015 := bstep (se 1 (by rfl) ⟨2202011, by rfl⟩ : syracuseStep 2936015 = 4404023) B4404023
theorem B1305831 : Blo 1303970 1305831 := bstep (se 1 (by rfl) ⟨979373, by rfl⟩ : syracuseStep 1305831 = 1958747) B1958747
theorem B2936105 : Blo 1303970 2936105 := bstep (se 2 (by rfl) ⟨1101039, by rfl⟩ : syracuseStep 2936105 = 2202079) B2202079
theorem B17845715 : Blo 1303970 17845715 := bstep (se 1 (by rfl) ⟨13384286, by rfl⟩ : syracuseStep 17845715 = 26768573) B26768573
theorem B1674751 : Blo 1303970 1674751 := bstep (se 1 (by rfl) ⟨1256063, by rfl⟩ : syracuseStep 1674751 = 2512127) B2512127
theorem B5574527 : Blo 1303970 5574527 := bstep (se 1 (by rfl) ⟨4180895, by rfl⟩ : syracuseStep 5574527 = 8361791) B8361791
theorem B4403159 : Blo 1303970 4403159 := bstep (se 1 (by rfl) ⟨3302369, by rfl⟩ : syracuseStep 4403159 = 6604739) B6604739
theorem B7942207 : Blo 1303970 7942207 := bstep (se 1 (by rfl) ⟨5956655, by rfl⟩ : syracuseStep 7942207 = 11913311) B11913311
theorem B3305711 : Blo 1303970 3305711 := bstep (se 1 (by rfl) ⟨2479283, by rfl⟩ : syracuseStep 3305711 = 4958567) B4958567
theorem B14857019 : Blo 1303970 14857019 := bstep (se 1 (by rfl) ⟨11142764, by rfl⟩ : syracuseStep 14857019 = 22285529) B22285529
theorem B33461099 : Blo 1303970 33461099 := bstep (se 1 (by rfl) ⟨25095824, by rfl⟩ : syracuseStep 33461099 = 50191649) B50191649
theorem B53556175 : Blo 1303970 53556175 := bstep (se 1 (by rfl) ⟨40167131, by rfl⟩ : syracuseStep 53556175 = 80334263) B80334263
theorem B2937959 : Blo 1303970 2937959 := bstep (se 1 (by rfl) ⟨2203469, by rfl⟩ : syracuseStep 2937959 = 4406939) B4406939
theorem B6272111 : Blo 1303970 6272111 := bstep (se 1 (by rfl) ⟨4704083, by rfl⟩ : syracuseStep 6272111 = 9408167) B9408167
theorem B2938139 : Blo 1303970 2938139 := bstep (se 1 (by rfl) ⟨2203604, by rfl⟩ : syracuseStep 2938139 = 4407209) B4407209
theorem B10589899 : Blo 1303970 10589899 := bstep (se 1 (by rfl) ⟨7942424, by rfl⟩ : syracuseStep 10589899 = 15884849) B15884849
theorem B2201627 : Blo 1303970 2201627 := bstep (se 1 (by rfl) ⟨1651220, by rfl⟩ : syracuseStep 2201627 = 3302441) B3302441
theorem B4954223 : Blo 1303970 4954223 := bstep (se 1 (by rfl) ⟨3715667, by rfl⟩ : syracuseStep 4954223 = 7431335) B7431335
theorem B2865403 : Blo 1303970 2865403 := bstep (se 1 (by rfl) ⟨2149052, by rfl⟩ : syracuseStep 2865403 = 4298105) B4298105
theorem B1956287 : Blo 1303970 1956287 := bstep (se 1 (by rfl) ⟨1467215, by rfl⟩ : syracuseStep 1956287 = 2934431) B2934431
theorem B1956407 : Blo 1303970 1956407 := bstep (se 1 (by rfl) ⟨1467305, by rfl⟩ : syracuseStep 1956407 = 2934611) B2934611
theorem B11140031 : Blo 1303970 11140031 := bstep (se 1 (by rfl) ⟨8355023, by rfl⟩ : syracuseStep 11140031 = 16710047) B16710047
theorem B4955195 : Blo 1303970 4955195 := bstep (se 1 (by rfl) ⟨3716396, by rfl⟩ : syracuseStep 4955195 = 7432793) B7432793
theorem B1957031 : Blo 1303970 1957031 := bstep (se 1 (by rfl) ⟨1467773, by rfl⟩ : syracuseStep 1957031 = 2935547) B2935547
theorem B1957055 : Blo 1303970 1957055 := bstep (se 1 (by rfl) ⟨1467791, by rfl⟩ : syracuseStep 1957055 = 2935583) B2935583
theorem B4177615 : Blo 1303970 4177615 := bstep (se 1 (by rfl) ⟨3133211, by rfl⟩ : syracuseStep 4177615 = 6266423) B6266423
theorem B2203807 : Blo 1303970 2203807 := bstep (se 1 (by rfl) ⟨1652855, by rfl⟩ : syracuseStep 2203807 = 3305711) B3305711
theorem B1392923 : Blo 1303970 1392923 := bstep (se 1 (by rfl) ⟨1044692, by rfl⟩ : syracuseStep 1392923 = 2089385) B2089385
theorem B12542377 : Blo 1303970 12542377 := bstep (se 2 (by rfl) ⟨4703391, by rfl⟩ : syracuseStep 12542377 = 9406783) B9406783
theorem B9904679 : Blo 1303970 9904679 := bstep (se 1 (by rfl) ⟨7428509, by rfl⟩ : syracuseStep 9904679 = 14857019) B14857019
theorem B22307399 : Blo 1303970 22307399 := bstep (se 1 (by rfl) ⟨16730549, by rfl⟩ : syracuseStep 22307399 = 33461099) B33461099
theorem B1958639 : Blo 1303970 1958639 := bstep (se 1 (by rfl) ⟨1468979, by rfl⟩ : syracuseStep 1958639 = 2937959) B2937959
theorem B228737783 : Blo 1303970 228737783 := bstep (se 1 (by rfl) ⟨171553337, by rfl⟩ : syracuseStep 228737783 = 343106675) B343106675
theorem B1958759 : Blo 1303970 1958759 := bstep (se 1 (by rfl) ⟨1469069, by rfl⟩ : syracuseStep 1958759 = 2938139) B2938139
theorem B47588573 : Blo 1303970 47588573 := bstep (se 3 (by rfl) ⟨8922857, by rfl⟩ : syracuseStep 47588573 = 17845715) B17845715
theorem B1467751 : Blo 1303970 1467751 := bstep (se 1 (by rfl) ⟨1100813, by rfl⟩ : syracuseStep 1467751 = 2201627) B2201627
theorem B3302815 : Blo 1303970 3302815 := bstep (se 1 (by rfl) ⟨2477111, by rfl⟩ : syracuseStep 3302815 = 4954223) B4954223
theorem B11142629 : Blo 1303970 11142629 := bstep (se 4 (by rfl) ⟨1044621, by rfl⟩ : syracuseStep 11142629 = 2089243) B2089243
theorem B1304191 : Blo 1303970 1304191 := bstep (se 1 (by rfl) ⟨978143, by rfl⟩ : syracuseStep 1304191 = 1956287) B1956287
theorem B1304271 : Blo 1303970 1304271 := bstep (se 1 (by rfl) ⟨978203, by rfl⟩ : syracuseStep 1304271 = 1956407) B1956407
theorem B54265565 : Blo 1303970 54265565 := bstep (se 3 (by rfl) ⟨10174793, by rfl⟩ : syracuseStep 54265565 = 20349587) B20349587
theorem B25085983 : Blo 1303970 25085983 := bstep (se 1 (by rfl) ⟨18814487, by rfl⟩ : syracuseStep 25085983 = 37628975) B37628975
theorem B3303463 : Blo 1303970 3303463 := bstep (se 1 (by rfl) ⟨2477597, by rfl⟩ : syracuseStep 3303463 = 4955195) B4955195
theorem B1304687 : Blo 1303970 1304687 := bstep (se 1 (by rfl) ⟨978515, by rfl⟩ : syracuseStep 1304687 = 1957031) B1957031
theorem B1304703 : Blo 1303970 1304703 := bstep (se 1 (by rfl) ⟨978527, by rfl⟩ : syracuseStep 1304703 = 1957055) B1957055
theorem B2935439 : Blo 1303970 2935439 := bstep (se 1 (by rfl) ⟨2201579, by rfl⟩ : syracuseStep 2935439 = 4403159) B4403159
theorem B1305295 : Blo 1303970 1305295 := bstep (se 1 (by rfl) ⟨978971, by rfl⟩ : syracuseStep 1305295 = 1957943) B1957943
theorem B1305339 : Blo 1303970 1305339 := bstep (se 1 (by rfl) ⟨979004, by rfl⟩ : syracuseStep 1305339 = 1958009) B1958009
theorem B3713789 : Blo 1303970 3713789 := bstep (se 3 (by rfl) ⟨696335, by rfl⟩ : syracuseStep 3713789 = 1392671) B1392671
theorem B1305343 : Blo 1303970 1305343 := bstep (se 1 (by rfl) ⟨979007, by rfl⟩ : syracuseStep 1305343 = 1958015) B1958015
theorem B1305371 : Blo 1303970 1305371 := bstep (se 1 (by rfl) ⟨979028, by rfl⟩ : syracuseStep 1305371 = 1958057) B1958057
theorem B3820537 : Blo 1303970 3820537 := bstep (se 2 (by rfl) ⟨1432701, by rfl⟩ : syracuseStep 3820537 = 2865403) B2865403
theorem B1305855 : Blo 1303970 1305855 := bstep (se 1 (by rfl) ⟨979391, by rfl⟩ : syracuseStep 1305855 = 1958783) B1958783
theorem B1650395 : Blo 1303970 1650395 := bstep (se 1 (by rfl) ⟨1237796, by rfl⟩ : syracuseStep 1650395 = 2475593) B2475593
theorem B7426687 : Blo 1303970 7426687 := bstep (se 1 (by rfl) ⟨5570015, by rfl⟩ : syracuseStep 7426687 = 11140031) B11140031
theorem B2233001 : Blo 1303970 2233001 := bstep (se 2 (by rfl) ⟨837375, by rfl⟩ : syracuseStep 2233001 = 1674751) B1674751
theorem B14119865 : Blo 1303970 14119865 := bstep (se 2 (by rfl) ⟨5294949, by rfl⟩ : syracuseStep 14119865 = 10589899) B10589899
theorem B3716351 : Blo 1303970 3716351 := bstep (se 1 (by rfl) ⟨2787263, by rfl⟩ : syracuseStep 3716351 = 5574527) B5574527
theorem B10589609 : Blo 1303970 10589609 := bstep (se 2 (by rfl) ⟨3971103, by rfl⟩ : syracuseStep 10589609 = 7942207) B7942207
theorem B4953707 : Blo 1303970 4953707 := bstep (se 1 (by rfl) ⟨3715280, by rfl⟩ : syracuseStep 4953707 = 7430561) B7430561
theorem B5576303 : Blo 1303970 5576303 := bstep (se 1 (by rfl) ⟨4182227, by rfl⟩ : syracuseStep 5576303 = 8364455) B8364455
theorem B16725629 : Blo 1303970 16725629 := bstep (se 3 (by rfl) ⟨3136055, by rfl⟩ : syracuseStep 16725629 = 6272111) B6272111
theorem B1956335 : Blo 1303970 1956335 := bstep (se 1 (by rfl) ⟨1467251, by rfl⟩ : syracuseStep 1956335 = 2934503) B2934503
theorem B9411167 : Blo 1303970 9411167 := bstep (se 1 (by rfl) ⟨7058375, by rfl⟩ : syracuseStep 9411167 = 14116751) B14116751
theorem B71408233 : Blo 1303970 71408233 := bstep (se 2 (by rfl) ⟨26778087, by rfl⟩ : syracuseStep 71408233 = 53556175) B53556175
theorem B1957343 : Blo 1303970 1957343 := bstep (se 1 (by rfl) ⟨1468007, by rfl⟩ : syracuseStep 1957343 = 2936015) B2936015
theorem B1957403 : Blo 1303970 1957403 := bstep (se 1 (by rfl) ⟨1468052, by rfl⟩ : syracuseStep 1957403 = 2936105) B2936105
theorem B5570153 : Blo 1303970 5570153 := bstep (se 2 (by rfl) ⟨2088807, by rfl⟩ : syracuseStep 5570153 = 4177615) B4177615
theorem B33447977 : Blo 1303970 33447977 := bstep (se 2 (by rfl) ⟨12542991, by rfl⟩ : syracuseStep 33447977 = 25085983) B25085983
theorem B6603119 : Blo 1303970 6603119 := bstep (se 1 (by rfl) ⟨4952339, by rfl⟩ : syracuseStep 6603119 = 9904679) B9904679
theorem B9413243 : Blo 1303970 9413243 := bstep (se 1 (by rfl) ⟨7059932, by rfl⟩ : syracuseStep 9413243 = 14119865) B14119865
theorem B3302471 : Blo 1303970 3302471 := bstep (se 1 (by rfl) ⟨2476853, by rfl⟩ : syracuseStep 3302471 = 4953707) B4953707
theorem B11150419 : Blo 1303970 11150419 := bstep (se 1 (by rfl) ⟨8362814, by rfl⟩ : syracuseStep 11150419 = 16725629) B16725629
theorem B36177043 : Blo 1303970 36177043 := bstep (se 1 (by rfl) ⟨27132782, by rfl⟩ : syracuseStep 36177043 = 54265565) B54265565
theorem B14870141 : Blo 1303970 14870141 := bstep (se 3 (by rfl) ⟨2788151, by rfl⟩ : syracuseStep 14870141 = 5576303) B5576303
theorem B1304223 : Blo 1303970 1304223 := bstep (se 1 (by rfl) ⟨978167, by rfl⟩ : syracuseStep 1304223 = 1956335) B1956335
theorem B2475859 : Blo 1303970 2475859 := bstep (se 1 (by rfl) ⟨1856894, by rfl⟩ : syracuseStep 2475859 = 3713789) B3713789
theorem B4401053 : Blo 1303970 4401053 := bstep (se 3 (by rfl) ⟨825197, by rfl⟩ : syracuseStep 4401053 = 1650395) B1650395
theorem B1304895 : Blo 1303970 1304895 := bstep (se 1 (by rfl) ⟨978671, by rfl⟩ : syracuseStep 1304895 = 1957343) B1957343
theorem B1304935 : Blo 1303970 1304935 := bstep (se 1 (by rfl) ⟨978701, by rfl⟩ : syracuseStep 1304935 = 1957403) B1957403
theorem B3713435 : Blo 1303970 3713435 := bstep (se 1 (by rfl) ⟨2785076, by rfl⟩ : syracuseStep 3713435 = 5570153) B5570153
theorem B20376197 : Blo 1303970 20376197 := bstep (se 4 (by rfl) ⟨1910268, by rfl⟩ : syracuseStep 20376197 = 3820537) B3820537
theorem B14871599 : Blo 1303970 14871599 := bstep (se 1 (by rfl) ⟨11153699, by rfl⟩ : syracuseStep 14871599 = 22307399) B22307399
theorem B1305759 : Blo 1303970 1305759 := bstep (se 1 (by rfl) ⟨979319, by rfl⟩ : syracuseStep 1305759 = 1958639) B1958639
theorem B16723169 : Blo 1303970 16723169 := bstep (se 2 (by rfl) ⟨6271188, by rfl⟩ : syracuseStep 16723169 = 12542377) B12542377
theorem B1305839 : Blo 1303970 1305839 := bstep (se 1 (by rfl) ⟨979379, by rfl⟩ : syracuseStep 1305839 = 1958759) B1958759
theorem B3714461 : Blo 1303970 3714461 := bstep (se 3 (by rfl) ⟨696461, by rfl⟩ : syracuseStep 3714461 = 1392923) B1392923
theorem B95210977 : Blo 1303970 95210977 := bstep (se 2 (by rfl) ⟨35704116, by rfl⟩ : syracuseStep 95210977 = 71408233) B71408233
theorem B2477567 : Blo 1303970 2477567 := bstep (se 1 (by rfl) ⟨1858175, by rfl⟩ : syracuseStep 2477567 = 3716351) B3716351
theorem B4403753 : Blo 1303970 4403753 := bstep (se 2 (by rfl) ⟨1651407, by rfl⟩ : syracuseStep 4403753 = 3302815) B3302815
theorem B4404617 : Blo 1303970 4404617 := bstep (se 2 (by rfl) ⟨1651731, by rfl⟩ : syracuseStep 4404617 = 3303463) B3303463
theorem B2938409 : Blo 1303970 2938409 := bstep (se 2 (by rfl) ⟨1101903, by rfl⟩ : syracuseStep 2938409 = 2203807) B2203807
theorem B1488667 : Blo 1303970 1488667 := bstep (se 1 (by rfl) ⟨1116500, by rfl⟩ : syracuseStep 1488667 = 2233001) B2233001
theorem B152491855 : Blo 1303970 152491855 := bstep (se 1 (by rfl) ⟨114368891, by rfl⟩ : syracuseStep 152491855 = 228737783) B228737783
theorem B31725715 : Blo 1303970 31725715 := bstep (se 1 (by rfl) ⟨23794286, by rfl⟩ : syracuseStep 31725715 = 47588573) B47588573
theorem B9902249 : Blo 1303970 9902249 := bstep (se 2 (by rfl) ⟨3713343, by rfl⟩ : syracuseStep 9902249 = 7426687) B7426687
theorem B7059739 : Blo 1303970 7059739 := bstep (se 1 (by rfl) ⟨5294804, by rfl⟩ : syracuseStep 7059739 = 10589609) B10589609
theorem B7428419 : Blo 1303970 7428419 := bstep (se 1 (by rfl) ⟨5571314, by rfl⟩ : syracuseStep 7428419 = 11142629) B11142629
theorem B6274111 : Blo 1303970 6274111 := bstep (se 1 (by rfl) ⟨4705583, by rfl⟩ : syracuseStep 6274111 = 9411167) B9411167
theorem B1956959 : Blo 1303970 1956959 := bstep (se 1 (by rfl) ⟨1467719, by rfl⟩ : syracuseStep 1956959 = 2935439) B2935439
theorem B1957001 : Blo 1303970 1957001 := bstep (se 2 (by rfl) ⟨733875, by rfl⟩ : syracuseStep 1957001 = 1467751) B1467751
theorem B22298651 : Blo 1303970 22298651 := bstep (se 1 (by rfl) ⟨16723988, by rfl⟩ : syracuseStep 22298651 = 33447977) B33447977
theorem B9412985 : Blo 1303970 9412985 := bstep (se 2 (by rfl) ⟨3529869, by rfl⟩ : syracuseStep 9412985 = 7059739) B7059739
theorem B6275495 : Blo 1303970 6275495 := bstep (se 1 (by rfl) ⟨4706621, by rfl⟩ : syracuseStep 6275495 = 9413243) B9413243
theorem B1958939 : Blo 1303970 1958939 := bstep (se 1 (by rfl) ⟨1469204, by rfl⟩ : syracuseStep 1958939 = 2938409) B2938409
theorem B9913427 : Blo 1303970 9913427 := bstep (se 1 (by rfl) ⟨7435070, by rfl⟩ : syracuseStep 9913427 = 14870141) B14870141
theorem B2934035 : Blo 1303970 2934035 := bstep (se 1 (by rfl) ⟨2200526, by rfl⟩ : syracuseStep 2934035 = 4401053) B4401053
theorem B8365481 : Blo 1303970 8365481 := bstep (se 2 (by rfl) ⟨3137055, by rfl⟩ : syracuseStep 8365481 = 6274111) B6274111
theorem B48236057 : Blo 1303970 48236057 := bstep (se 2 (by rfl) ⟨18088521, by rfl⟩ : syracuseStep 48236057 = 36177043) B36177043
theorem B2475623 : Blo 1303970 2475623 := bstep (se 1 (by rfl) ⟨1856717, by rfl⟩ : syracuseStep 2475623 = 3713435) B3713435
theorem B13584131 : Blo 1303970 13584131 := bstep (se 1 (by rfl) ⟨10188098, by rfl⟩ : syracuseStep 13584131 = 20376197) B20376197
theorem B9914399 : Blo 1303970 9914399 := bstep (se 1 (by rfl) ⟨7435799, by rfl⟩ : syracuseStep 9914399 = 14871599) B14871599
theorem B1304639 : Blo 1303970 1304639 := bstep (se 1 (by rfl) ⟨978479, by rfl⟩ : syracuseStep 1304639 = 1956959) B1956959
theorem B1304667 : Blo 1303970 1304667 := bstep (se 1 (by rfl) ⟨978500, by rfl⟩ : syracuseStep 1304667 = 1957001) B1957001
theorem B2476307 : Blo 1303970 2476307 := bstep (se 1 (by rfl) ⟨1857230, by rfl⟩ : syracuseStep 2476307 = 3714461) B3714461
theorem B1984889 : Blo 1303970 1984889 := bstep (se 2 (by rfl) ⟨744333, by rfl⟩ : syracuseStep 1984889 = 1488667) B1488667
theorem B4402079 : Blo 1303970 4402079 := bstep (se 1 (by rfl) ⟨3301559, by rfl⟩ : syracuseStep 4402079 = 6603119) B6603119
theorem B2935835 : Blo 1303970 2935835 := bstep (se 1 (by rfl) ⟨2201876, by rfl⟩ : syracuseStep 2935835 = 4403753) B4403753
theorem B2936411 : Blo 1303970 2936411 := bstep (se 1 (by rfl) ⟨2202308, by rfl⟩ : syracuseStep 2936411 = 4404617) B4404617
theorem B6606845 : Blo 1303970 6606845 := bstep (se 3 (by rfl) ⟨1238783, by rfl⟩ : syracuseStep 6606845 = 2477567) B2477567
theorem B4952279 : Blo 1303970 4952279 := bstep (se 1 (by rfl) ⟨3714209, by rfl⟩ : syracuseStep 4952279 = 7428419) B7428419
theorem B126947969 : Blo 1303970 126947969 := bstep (se 2 (by rfl) ⟨47605488, by rfl⟩ : syracuseStep 126947969 = 95210977) B95210977
theorem B203322473 : Blo 1303970 203322473 := bstep (se 2 (by rfl) ⟨76245927, by rfl⟩ : syracuseStep 203322473 = 152491855) B152491855
theorem B42300953 : Blo 1303970 42300953 := bstep (se 2 (by rfl) ⟨15862857, by rfl⟩ : syracuseStep 42300953 = 31725715) B31725715
theorem B2201647 : Blo 1303970 2201647 := bstep (se 1 (by rfl) ⟨1651235, by rfl⟩ : syracuseStep 2201647 = 3302471) B3302471
theorem B14867225 : Blo 1303970 14867225 := bstep (se 2 (by rfl) ⟨5575209, by rfl⟩ : syracuseStep 14867225 = 11150419) B11150419
theorem B6601499 : Blo 1303970 6601499 := bstep (se 1 (by rfl) ⟨4951124, by rfl⟩ : syracuseStep 6601499 = 9902249) B9902249
theorem B11148779 : Blo 1303970 11148779 := bstep (se 1 (by rfl) ⟨8361584, by rfl⟩ : syracuseStep 11148779 = 16723169) B16723169
theorem B3301145 : Blo 1303970 3301145 := bstep (se 2 (by rfl) ⟨1237929, by rfl⟩ : syracuseStep 3301145 = 2475859) B2475859
theorem B3301519 : Blo 1303970 3301519 := bstep (se 1 (by rfl) ⟨2476139, by rfl⟩ : syracuseStep 3301519 = 4952279) B4952279
theorem B6275323 : Blo 1303970 6275323 := bstep (se 1 (by rfl) ⟨4706492, by rfl⟩ : syracuseStep 6275323 = 9412985) B9412985
theorem B84631979 : Blo 1303970 84631979 := bstep (se 1 (by rfl) ⟨63473984, by rfl⟩ : syracuseStep 84631979 = 126947969) B126947969
theorem B4400999 : Blo 1303970 4400999 := bstep (se 1 (by rfl) ⟨3300749, by rfl⟩ : syracuseStep 4400999 = 6601499) B6601499
theorem B2934719 : Blo 1303970 2934719 := bstep (se 1 (by rfl) ⟨2201039, by rfl⟩ : syracuseStep 2934719 = 4402079) B4402079
theorem B7432519 : Blo 1303970 7432519 := bstep (se 1 (by rfl) ⟨5574389, by rfl⟩ : syracuseStep 7432519 = 11148779) B11148779
theorem B2935529 : Blo 1303970 2935529 := bstep (se 2 (by rfl) ⟨1100823, by rfl⟩ : syracuseStep 2935529 = 2201647) B2201647
theorem B1305959 : Blo 1303970 1305959 := bstep (se 1 (by rfl) ⟨979469, by rfl⟩ : syracuseStep 1305959 = 1958939) B1958939
theorem B135548315 : Blo 1303970 135548315 := bstep (se 1 (by rfl) ⟨101661236, by rfl⟩ : syracuseStep 135548315 = 203322473) B203322473
theorem B32157371 : Blo 1303970 32157371 := bstep (se 1 (by rfl) ⟨24118028, by rfl⟩ : syracuseStep 32157371 = 48236057) B48236057
theorem B28200635 : Blo 1303970 28200635 := bstep (se 1 (by rfl) ⟨21150476, by rfl⟩ : syracuseStep 28200635 = 42300953) B42300953
theorem B9056087 : Blo 1303970 9056087 := bstep (se 1 (by rfl) ⟨6792065, by rfl⟩ : syracuseStep 9056087 = 13584131) B13584131
theorem B1650871 : Blo 1303970 1650871 := bstep (se 1 (by rfl) ⟨1238153, by rfl⟩ : syracuseStep 1650871 = 2476307) B2476307
theorem B1323259 : Blo 1303970 1323259 := bstep (se 1 (by rfl) ⟨992444, by rfl⟩ : syracuseStep 1323259 = 1984889) B1984889
theorem B2200763 : Blo 1303970 2200763 := bstep (se 1 (by rfl) ⟨1650572, by rfl⟩ : syracuseStep 2200763 = 3301145) B3301145
theorem B4404563 : Blo 1303970 4404563 := bstep (se 1 (by rfl) ⟨3303422, by rfl⟩ : syracuseStep 4404563 = 6606845) B6606845
theorem B14865767 : Blo 1303970 14865767 := bstep (se 1 (by rfl) ⟨11149325, by rfl⟩ : syracuseStep 14865767 = 22298651) B22298651
theorem B4183663 : Blo 1303970 4183663 := bstep (se 1 (by rfl) ⟨3137747, by rfl⟩ : syracuseStep 4183663 = 6275495) B6275495
theorem B6608951 : Blo 1303970 6608951 := bstep (se 1 (by rfl) ⟨4956713, by rfl⟩ : syracuseStep 6608951 = 9913427) B9913427
theorem B1956023 : Blo 1303970 1956023 := bstep (se 1 (by rfl) ⟨1467017, by rfl⟩ : syracuseStep 1956023 = 2934035) B2934035
theorem B5576987 : Blo 1303970 5576987 := bstep (se 1 (by rfl) ⟨4182740, by rfl⟩ : syracuseStep 5576987 = 8365481) B8365481
theorem B6609599 : Blo 1303970 6609599 := bstep (se 1 (by rfl) ⟨4957199, by rfl⟩ : syracuseStep 6609599 = 9914399) B9914399
theorem B6601661 : Blo 1303970 6601661 := bstep (se 3 (by rfl) ⟨1237811, by rfl⟩ : syracuseStep 6601661 = 2475623) B2475623
theorem B9911483 : Blo 1303970 9911483 := bstep (se 1 (by rfl) ⟨7433612, by rfl⟩ : syracuseStep 9911483 = 14867225) B14867225
theorem B1957223 : Blo 1303970 1957223 := bstep (se 1 (by rfl) ⟨1467917, by rfl⟩ : syracuseStep 1957223 = 2935835) B2935835
theorem B1957607 : Blo 1303970 1957607 := bstep (se 1 (by rfl) ⟨1468205, by rfl⟩ : syracuseStep 1957607 = 2936411) B2936411
theorem B1467175 : Blo 1303970 1467175 := bstep (se 1 (by rfl) ⟨1100381, by rfl⟩ : syracuseStep 1467175 = 2200763) B2200763
theorem B2933999 : Blo 1303970 2933999 := bstep (se 1 (by rfl) ⟨2200499, by rfl⟩ : syracuseStep 2933999 = 4400999) B4400999
theorem B1304015 : Blo 1303970 1304015 := bstep (se 1 (by rfl) ⟨978011, by rfl⟩ : syracuseStep 1304015 = 1956023) B1956023
theorem B4401107 : Blo 1303970 4401107 := bstep (se 1 (by rfl) ⟨3300830, by rfl⟩ : syracuseStep 4401107 = 6601661) B6601661
theorem B1304815 : Blo 1303970 1304815 := bstep (se 1 (by rfl) ⟨978611, by rfl⟩ : syracuseStep 1304815 = 1957223) B1957223
theorem B1305071 : Blo 1303970 1305071 := bstep (se 1 (by rfl) ⟨978803, by rfl⟩ : syracuseStep 1305071 = 1957607) B1957607
theorem B4402025 : Blo 1303970 4402025 := bstep (se 2 (by rfl) ⟨1650759, by rfl⟩ : syracuseStep 4402025 = 3301519) B3301519
theorem B56421319 : Blo 1303970 56421319 := bstep (se 1 (by rfl) ⟨42315989, by rfl⟩ : syracuseStep 56421319 = 84631979) B84631979
theorem B8367097 : Blo 1303970 8367097 := bstep (se 2 (by rfl) ⟨3137661, by rfl⟩ : syracuseStep 8367097 = 6275323) B6275323
theorem B2936375 : Blo 1303970 2936375 := bstep (se 1 (by rfl) ⟨2202281, by rfl⟩ : syracuseStep 2936375 = 4404563) B4404563
theorem B7057381 : Blo 1303970 7057381 := bstep (se 4 (by rfl) ⟨661629, by rfl⟩ : syracuseStep 7057381 = 1323259) B1323259
theorem B6607655 : Blo 1303970 6607655 := bstep (se 1 (by rfl) ⟨4955741, by rfl⟩ : syracuseStep 6607655 = 9911483) B9911483
theorem B2201161 : Blo 1303970 2201161 := bstep (se 2 (by rfl) ⟨825435, by rfl⟩ : syracuseStep 2201161 = 1650871) B1650871
theorem B9910025 : Blo 1303970 9910025 := bstep (se 2 (by rfl) ⟨3716259, by rfl⟩ : syracuseStep 9910025 = 7432519) B7432519
theorem B9910511 : Blo 1303970 9910511 := bstep (se 1 (by rfl) ⟨7432883, by rfl⟩ : syracuseStep 9910511 = 14865767) B14865767
theorem B1956479 : Blo 1303970 1956479 := bstep (se 1 (by rfl) ⟨1467359, by rfl⟩ : syracuseStep 1956479 = 2934719) B2934719
theorem B4405967 : Blo 1303970 4405967 := bstep (se 1 (by rfl) ⟨3304475, by rfl⟩ : syracuseStep 4405967 = 6608951) B6608951
theorem B3717991 : Blo 1303970 3717991 := bstep (se 1 (by rfl) ⟨2788493, by rfl⟩ : syracuseStep 3717991 = 5576987) B5576987
theorem B4406399 : Blo 1303970 4406399 := bstep (se 1 (by rfl) ⟨3304799, by rfl⟩ : syracuseStep 4406399 = 6609599) B6609599
theorem B1957019 : Blo 1303970 1957019 := bstep (se 1 (by rfl) ⟨1467764, by rfl⟩ : syracuseStep 1957019 = 2935529) B2935529
theorem B85752989 : Blo 1303970 85752989 := bstep (se 3 (by rfl) ⟨16078685, by rfl⟩ : syracuseStep 85752989 = 32157371) B32157371
theorem B5578217 : Blo 1303970 5578217 := bstep (se 2 (by rfl) ⟨2091831, by rfl⟩ : syracuseStep 5578217 = 4183663) B4183663
theorem B90365543 : Blo 1303970 90365543 := bstep (se 1 (by rfl) ⟨67774157, by rfl⟩ : syracuseStep 90365543 = 135548315) B135548315
theorem B18800423 : Blo 1303970 18800423 := bstep (se 1 (by rfl) ⟨14100317, by rfl⟩ : syracuseStep 18800423 = 28200635) B28200635
theorem B6037391 : Blo 1303970 6037391 := bstep (se 1 (by rfl) ⟨4528043, by rfl⟩ : syracuseStep 6037391 = 9056087) B9056087
theorem B4957321 : Blo 1303970 4957321 := bstep (se 2 (by rfl) ⟨1858995, by rfl⟩ : syracuseStep 4957321 = 3717991) B3717991
theorem B75228425 : Blo 1303970 75228425 := bstep (se 2 (by rfl) ⟨28210659, by rfl⟩ : syracuseStep 75228425 = 56421319) B56421319
theorem B2934071 : Blo 1303970 2934071 := bstep (se 1 (by rfl) ⟨2200553, by rfl⟩ : syracuseStep 2934071 = 4401107) B4401107
theorem B1304319 : Blo 1303970 1304319 := bstep (se 1 (by rfl) ⟨978239, by rfl⟩ : syracuseStep 1304319 = 1956479) B1956479
theorem B2934683 : Blo 1303970 2934683 := bstep (se 1 (by rfl) ⟨2201012, by rfl⟩ : syracuseStep 2934683 = 4402025) B4402025
theorem B2934881 : Blo 1303970 2934881 := bstep (se 2 (by rfl) ⟨1100580, by rfl⟩ : syracuseStep 2934881 = 2201161) B2201161
theorem B1304679 : Blo 1303970 1304679 := bstep (se 1 (by rfl) ⟨978509, by rfl⟩ : syracuseStep 1304679 = 1957019) B1957019
theorem B4024927 : Blo 1303970 4024927 := bstep (se 1 (by rfl) ⟨3018695, by rfl⟩ : syracuseStep 4024927 = 6037391) B6037391
theorem B6606683 : Blo 1303970 6606683 := bstep (se 1 (by rfl) ⟨4955012, by rfl⟩ : syracuseStep 6606683 = 9910025) B9910025
theorem B6607007 : Blo 1303970 6607007 := bstep (se 1 (by rfl) ⟨4955255, by rfl⟩ : syracuseStep 6607007 = 9910511) B9910511
theorem B2937311 : Blo 1303970 2937311 := bstep (se 1 (by rfl) ⟨2202983, by rfl⟩ : syracuseStep 2937311 = 4405967) B4405967
theorem B2937599 : Blo 1303970 2937599 := bstep (se 1 (by rfl) ⟨2203199, by rfl⟩ : syracuseStep 2937599 = 4406399) B4406399
theorem B57168659 : Blo 1303970 57168659 := bstep (se 1 (by rfl) ⟨42876494, by rfl⟩ : syracuseStep 57168659 = 85752989) B85752989
theorem B9409841 : Blo 1303970 9409841 := bstep (se 2 (by rfl) ⟨3528690, by rfl⟩ : syracuseStep 9409841 = 7057381) B7057381
theorem B4405103 : Blo 1303970 4405103 := bstep (se 1 (by rfl) ⟨3303827, by rfl⟩ : syracuseStep 4405103 = 6607655) B6607655
theorem B1955999 : Blo 1303970 1955999 := bstep (se 1 (by rfl) ⟨1466999, by rfl⟩ : syracuseStep 1955999 = 2933999) B2933999
theorem B1956233 : Blo 1303970 1956233 := bstep (se 2 (by rfl) ⟨733587, by rfl⟩ : syracuseStep 1956233 = 1467175) B1467175
theorem B11156129 : Blo 1303970 11156129 := bstep (se 2 (by rfl) ⟨4183548, by rfl⟩ : syracuseStep 11156129 = 8367097) B8367097
theorem B3718811 : Blo 1303970 3718811 := bstep (se 1 (by rfl) ⟨2789108, by rfl⟩ : syracuseStep 3718811 = 5578217) B5578217
theorem B1957583 : Blo 1303970 1957583 := bstep (se 1 (by rfl) ⟨1468187, by rfl⟩ : syracuseStep 1957583 = 2936375) B2936375
theorem B60243695 : Blo 1303970 60243695 := bstep (se 1 (by rfl) ⟨45182771, by rfl⟩ : syracuseStep 60243695 = 90365543) B90365543
theorem B12533615 : Blo 1303970 12533615 := bstep (se 1 (by rfl) ⟨9400211, by rfl⟩ : syracuseStep 12533615 = 18800423) B18800423
theorem B1958207 : Blo 1303970 1958207 := bstep (se 1 (by rfl) ⟨1468655, by rfl⟩ : syracuseStep 1958207 = 2937311) B2937311
theorem B1958399 : Blo 1303970 1958399 := bstep (se 1 (by rfl) ⟨1468799, by rfl⟩ : syracuseStep 1958399 = 2937599) B2937599
theorem B5366569 : Blo 1303970 5366569 := bstep (se 2 (by rfl) ⟨2012463, by rfl⟩ : syracuseStep 5366569 = 4024927) B4024927
theorem B50152283 : Blo 1303970 50152283 := bstep (se 1 (by rfl) ⟨37614212, by rfl⟩ : syracuseStep 50152283 = 75228425) B75228425
theorem B1303999 : Blo 1303970 1303999 := bstep (se 1 (by rfl) ⟨977999, by rfl⟩ : syracuseStep 1303999 = 1955999) B1955999
theorem B1304155 : Blo 1303970 1304155 := bstep (se 1 (by rfl) ⟨978116, by rfl⟩ : syracuseStep 1304155 = 1956233) B1956233
theorem B1305055 : Blo 1303970 1305055 := bstep (se 1 (by rfl) ⟨978791, by rfl⟩ : syracuseStep 1305055 = 1957583) B1957583
theorem B38112439 : Blo 1303970 38112439 := bstep (se 1 (by rfl) ⟨28584329, by rfl⟩ : syracuseStep 38112439 = 57168659) B57168659
theorem B2936735 : Blo 1303970 2936735 := bstep (se 1 (by rfl) ⟨2202551, by rfl⟩ : syracuseStep 2936735 = 4405103) B4405103
theorem B9916829 : Blo 1303970 9916829 := bstep (se 3 (by rfl) ⟨1859405, by rfl⟩ : syracuseStep 9916829 = 3718811) B3718811
theorem B40162463 : Blo 1303970 40162463 := bstep (se 1 (by rfl) ⟨30121847, by rfl⟩ : syracuseStep 40162463 = 60243695) B60243695
theorem B4404455 : Blo 1303970 4404455 := bstep (se 1 (by rfl) ⟨3303341, by rfl⟩ : syracuseStep 4404455 = 6606683) B6606683
theorem B4404671 : Blo 1303970 4404671 := bstep (se 1 (by rfl) ⟨3303503, by rfl⟩ : syracuseStep 4404671 = 6607007) B6607007
theorem B6273227 : Blo 1303970 6273227 := bstep (se 1 (by rfl) ⟨4704920, by rfl⟩ : syracuseStep 6273227 = 9409841) B9409841
theorem B1956047 : Blo 1303970 1956047 := bstep (se 1 (by rfl) ⟨1467035, by rfl⟩ : syracuseStep 1956047 = 2934071) B2934071
theorem B1956455 : Blo 1303970 1956455 := bstep (se 1 (by rfl) ⟨1467341, by rfl⟩ : syracuseStep 1956455 = 2934683) B2934683
theorem B1956587 : Blo 1303970 1956587 := bstep (se 1 (by rfl) ⟨1467440, by rfl⟩ : syracuseStep 1956587 = 2934881) B2934881
theorem B6609761 : Blo 1303970 6609761 := bstep (se 2 (by rfl) ⟨2478660, by rfl⟩ : syracuseStep 6609761 = 4957321) B4957321
theorem B7437419 : Blo 1303970 7437419 := bstep (se 1 (by rfl) ⟨5578064, by rfl⟩ : syracuseStep 7437419 = 11156129) B11156129
theorem B8355743 : Blo 1303970 8355743 := bstep (se 1 (by rfl) ⟨6266807, by rfl⟩ : syracuseStep 8355743 = 12533615) B12533615
theorem B6611219 : Blo 1303970 6611219 := bstep (se 1 (by rfl) ⟨4958414, by rfl⟩ : syracuseStep 6611219 = 9916829) B9916829
theorem B16728605 : Blo 1303970 16728605 := bstep (se 3 (by rfl) ⟨3136613, by rfl⟩ : syracuseStep 16728605 = 6273227) B6273227
theorem B1304031 : Blo 1303970 1304031 := bstep (se 1 (by rfl) ⟨978023, by rfl⟩ : syracuseStep 1304031 = 1956047) B1956047
theorem B50816585 : Blo 1303970 50816585 := bstep (se 2 (by rfl) ⟨19056219, by rfl⟩ : syracuseStep 50816585 = 38112439) B38112439
theorem B1304303 : Blo 1303970 1304303 := bstep (se 1 (by rfl) ⟨978227, by rfl⟩ : syracuseStep 1304303 = 1956455) B1956455
theorem B1304391 : Blo 1303970 1304391 := bstep (se 1 (by rfl) ⟨978293, by rfl⟩ : syracuseStep 1304391 = 1956587) B1956587
theorem B4958279 : Blo 1303970 4958279 := bstep (se 1 (by rfl) ⟨3718709, by rfl⟩ : syracuseStep 4958279 = 7437419) B7437419
theorem B1305471 : Blo 1303970 1305471 := bstep (se 1 (by rfl) ⟨979103, by rfl⟩ : syracuseStep 1305471 = 1958207) B1958207
theorem B1305599 : Blo 1303970 1305599 := bstep (se 1 (by rfl) ⟨979199, by rfl⟩ : syracuseStep 1305599 = 1958399) B1958399
theorem B33434855 : Blo 1303970 33434855 := bstep (se 1 (by rfl) ⟨25076141, by rfl⟩ : syracuseStep 33434855 = 50152283) B50152283
theorem B26774975 : Blo 1303970 26774975 := bstep (se 1 (by rfl) ⟨20081231, by rfl⟩ : syracuseStep 26774975 = 40162463) B40162463
theorem B2936303 : Blo 1303970 2936303 := bstep (se 1 (by rfl) ⟨2202227, by rfl⟩ : syracuseStep 2936303 = 4404455) B4404455
theorem B2936447 : Blo 1303970 2936447 := bstep (se 1 (by rfl) ⟨2202335, by rfl⟩ : syracuseStep 2936447 = 4404671) B4404671
theorem B7155425 : Blo 1303970 7155425 := bstep (se 2 (by rfl) ⟨2683284, by rfl⟩ : syracuseStep 7155425 = 5366569) B5366569
theorem B4406507 : Blo 1303970 4406507 := bstep (se 1 (by rfl) ⟨3304880, by rfl⟩ : syracuseStep 4406507 = 6609761) B6609761
theorem B5570495 : Blo 1303970 5570495 := bstep (se 1 (by rfl) ⟨4177871, by rfl⟩ : syracuseStep 5570495 = 8355743) B8355743
theorem B1957823 : Blo 1303970 1957823 := bstep (se 1 (by rfl) ⟨1468367, by rfl⟩ : syracuseStep 1957823 = 2936735) B2936735
theorem B4407479 : Blo 1303970 4407479 := bstep (se 1 (by rfl) ⟨3305609, by rfl⟩ : syracuseStep 4407479 = 6611219) B6611219
theorem B4770283 : Blo 1303970 4770283 := bstep (se 1 (by rfl) ⟨3577712, by rfl⟩ : syracuseStep 4770283 = 7155425) B7155425
theorem B3713663 : Blo 1303970 3713663 := bstep (se 1 (by rfl) ⟨2785247, by rfl⟩ : syracuseStep 3713663 = 5570495) B5570495
theorem B1305215 : Blo 1303970 1305215 := bstep (se 1 (by rfl) ⟨978911, by rfl⟩ : syracuseStep 1305215 = 1957823) B1957823
theorem B11152403 : Blo 1303970 11152403 := bstep (se 1 (by rfl) ⟨8364302, by rfl⟩ : syracuseStep 11152403 = 16728605) B16728605
theorem B3305519 : Blo 1303970 3305519 := bstep (se 1 (by rfl) ⟨2479139, by rfl⟩ : syracuseStep 3305519 = 4958279) B4958279
theorem B2937671 : Blo 1303970 2937671 := bstep (se 1 (by rfl) ⟨2203253, by rfl⟩ : syracuseStep 2937671 = 4406507) B4406507
theorem B135510893 : Blo 1303970 135510893 := bstep (se 3 (by rfl) ⟨25408292, by rfl⟩ : syracuseStep 135510893 = 50816585) B50816585
theorem B22289903 : Blo 1303970 22289903 := bstep (se 1 (by rfl) ⟨16717427, by rfl⟩ : syracuseStep 22289903 = 33434855) B33434855
theorem B17849983 : Blo 1303970 17849983 := bstep (se 1 (by rfl) ⟨13387487, by rfl⟩ : syracuseStep 17849983 = 26774975) B26774975
theorem B1957535 : Blo 1303970 1957535 := bstep (se 1 (by rfl) ⟨1468151, by rfl⟩ : syracuseStep 1957535 = 2936303) B2936303
theorem B1957631 : Blo 1303970 1957631 := bstep (se 1 (by rfl) ⟨1468223, by rfl⟩ : syracuseStep 1957631 = 2936447) B2936447
theorem B2203679 : Blo 1303970 2203679 := bstep (se 1 (by rfl) ⟨1652759, by rfl⟩ : syracuseStep 2203679 = 3305519) B3305519
theorem B1958447 : Blo 1303970 1958447 := bstep (se 1 (by rfl) ⟨1468835, by rfl⟩ : syracuseStep 1958447 = 2937671) B2937671
theorem B2475775 : Blo 1303970 2475775 := bstep (se 1 (by rfl) ⟨1856831, by rfl⟩ : syracuseStep 2475775 = 3713663) B3713663
theorem B23799977 : Blo 1303970 23799977 := bstep (se 2 (by rfl) ⟨8924991, by rfl⟩ : syracuseStep 23799977 = 17849983) B17849983
theorem B1305023 : Blo 1303970 1305023 := bstep (se 1 (by rfl) ⟨978767, by rfl⟩ : syracuseStep 1305023 = 1957535) B1957535
theorem B1305087 : Blo 1303970 1305087 := bstep (se 1 (by rfl) ⟨978815, by rfl⟩ : syracuseStep 1305087 = 1957631) B1957631
theorem B6360377 : Blo 1303970 6360377 := bstep (se 2 (by rfl) ⟨2385141, by rfl⟩ : syracuseStep 6360377 = 4770283) B4770283
theorem B7434935 : Blo 1303970 7434935 := bstep (se 1 (by rfl) ⟨5576201, by rfl⟩ : syracuseStep 7434935 = 11152403) B11152403
theorem B2938319 : Blo 1303970 2938319 := bstep (se 1 (by rfl) ⟨2203739, by rfl⟩ : syracuseStep 2938319 = 4407479) B4407479
theorem B90340595 : Blo 1303970 90340595 := bstep (se 1 (by rfl) ⟨67755446, by rfl⟩ : syracuseStep 90340595 = 135510893) B135510893
theorem B14859935 : Blo 1303970 14859935 := bstep (se 1 (by rfl) ⟨11144951, by rfl⟩ : syracuseStep 14859935 = 22289903) B22289903
theorem B4956623 : Blo 1303970 4956623 := bstep (se 1 (by rfl) ⟨3717467, by rfl⟩ : syracuseStep 4956623 = 7434935) B7434935
theorem B1958879 : Blo 1303970 1958879 := bstep (se 1 (by rfl) ⟨1469159, by rfl⟩ : syracuseStep 1958879 = 2938319) B2938319
theorem B9906623 : Blo 1303970 9906623 := bstep (se 1 (by rfl) ⟨7429967, by rfl⟩ : syracuseStep 9906623 = 14859935) B14859935
theorem B1469119 : Blo 1303970 1469119 := bstep (se 1 (by rfl) ⟨1101839, by rfl⟩ : syracuseStep 1469119 = 2203679) B2203679
theorem B1305631 : Blo 1303970 1305631 := bstep (se 1 (by rfl) ⟨979223, by rfl⟩ : syracuseStep 1305631 = 1958447) B1958447
theorem B16961005 : Blo 1303970 16961005 := bstep (se 3 (by rfl) ⟨3180188, by rfl⟩ : syracuseStep 16961005 = 6360377) B6360377
theorem B15866651 : Blo 1303970 15866651 := bstep (se 1 (by rfl) ⟨11899988, by rfl⟩ : syracuseStep 15866651 = 23799977) B23799977
theorem B60227063 : Blo 1303970 60227063 := bstep (se 1 (by rfl) ⟨45170297, by rfl⟩ : syracuseStep 60227063 = 90340595) B90340595
theorem B3301033 : Blo 1303970 3301033 := bstep (se 2 (by rfl) ⟨1237887, by rfl⟩ : syracuseStep 3301033 = 2475775) B2475775
theorem B1958825 : Blo 1303970 1958825 := bstep (se 2 (by rfl) ⟨734559, by rfl⟩ : syracuseStep 1958825 = 1469119) B1469119
theorem B6604415 : Blo 1303970 6604415 := bstep (se 1 (by rfl) ⟨4953311, by rfl⟩ : syracuseStep 6604415 = 9906623) B9906623
theorem B4401377 : Blo 1303970 4401377 := bstep (se 2 (by rfl) ⟨1650516, by rfl⟩ : syracuseStep 4401377 = 3301033) B3301033
theorem B40151375 : Blo 1303970 40151375 := bstep (se 1 (by rfl) ⟨30113531, by rfl⟩ : syracuseStep 40151375 = 60227063) B60227063
theorem B90458693 : Blo 1303970 90458693 := bstep (se 4 (by rfl) ⟨8480502, by rfl⟩ : syracuseStep 90458693 = 16961005) B16961005
theorem B3304415 : Blo 1303970 3304415 := bstep (se 1 (by rfl) ⟨2478311, by rfl⟩ : syracuseStep 3304415 = 4956623) B4956623
theorem B1305919 : Blo 1303970 1305919 := bstep (se 1 (by rfl) ⟨979439, by rfl⟩ : syracuseStep 1305919 = 1958879) B1958879
theorem B42311069 : Blo 1303970 42311069 := bstep (se 3 (by rfl) ⟨7933325, by rfl⟩ : syracuseStep 42311069 = 15866651) B15866651
theorem B2934251 : Blo 1303970 2934251 := bstep (se 1 (by rfl) ⟨2200688, by rfl⟩ : syracuseStep 2934251 = 4401377) B4401377
theorem B28207379 : Blo 1303970 28207379 := bstep (se 1 (by rfl) ⟨21155534, by rfl⟩ : syracuseStep 28207379 = 42311069) B42311069
theorem B1305883 : Blo 1303970 1305883 := bstep (se 1 (by rfl) ⟨979412, by rfl⟩ : syracuseStep 1305883 = 1958825) B1958825
theorem B4402943 : Blo 1303970 4402943 := bstep (se 1 (by rfl) ⟨3302207, by rfl⟩ : syracuseStep 4402943 = 6604415) B6604415
theorem B26767583 : Blo 1303970 26767583 := bstep (se 1 (by rfl) ⟨20075687, by rfl⟩ : syracuseStep 26767583 = 40151375) B40151375
theorem B60305795 : Blo 1303970 60305795 := bstep (se 1 (by rfl) ⟨45229346, by rfl⟩ : syracuseStep 60305795 = 90458693) B90458693
theorem B2202943 : Blo 1303970 2202943 := bstep (se 1 (by rfl) ⟨1652207, by rfl⟩ : syracuseStep 2202943 = 3304415) B3304415
theorem B2935295 : Blo 1303970 2935295 := bstep (se 1 (by rfl) ⟨2201471, by rfl⟩ : syracuseStep 2935295 = 4402943) B4402943
theorem B17845055 : Blo 1303970 17845055 := bstep (se 1 (by rfl) ⟨13383791, by rfl⟩ : syracuseStep 17845055 = 26767583) B26767583
theorem B18804919 : Blo 1303970 18804919 := bstep (se 1 (by rfl) ⟨14103689, by rfl⟩ : syracuseStep 18804919 = 28207379) B28207379
theorem B2937257 : Blo 1303970 2937257 := bstep (se 2 (by rfl) ⟨1101471, by rfl⟩ : syracuseStep 2937257 = 2202943) B2202943
theorem B40203863 : Blo 1303970 40203863 := bstep (se 1 (by rfl) ⟨30152897, by rfl⟩ : syracuseStep 40203863 = 60305795) B60305795
theorem B1956167 : Blo 1303970 1956167 := bstep (se 1 (by rfl) ⟨1467125, by rfl⟩ : syracuseStep 1956167 = 2934251) B2934251
theorem B1958171 : Blo 1303970 1958171 := bstep (se 1 (by rfl) ⟨1468628, by rfl⟩ : syracuseStep 1958171 = 2937257) B2937257
theorem B1304111 : Blo 1303970 1304111 := bstep (se 1 (by rfl) ⟨978083, by rfl⟩ : syracuseStep 1304111 = 1956167) B1956167
theorem B11896703 : Blo 1303970 11896703 := bstep (se 1 (by rfl) ⟨8922527, by rfl⟩ : syracuseStep 11896703 = 17845055) B17845055
theorem B25073225 : Blo 1303970 25073225 := bstep (se 2 (by rfl) ⟨9402459, by rfl⟩ : syracuseStep 25073225 = 18804919) B18804919
theorem B26802575 : Blo 1303970 26802575 := bstep (se 1 (by rfl) ⟨20101931, by rfl⟩ : syracuseStep 26802575 = 40203863) B40203863
theorem B1956863 : Blo 1303970 1956863 := bstep (se 1 (by rfl) ⟨1467647, by rfl⟩ : syracuseStep 1956863 = 2935295) B2935295
theorem B7931135 : Blo 1303970 7931135 := bstep (se 1 (by rfl) ⟨5948351, by rfl⟩ : syracuseStep 7931135 = 11896703) B11896703
theorem B17868383 : Blo 1303970 17868383 := bstep (se 1 (by rfl) ⟨13401287, by rfl⟩ : syracuseStep 17868383 = 26802575) B26802575
theorem B1304575 : Blo 1303970 1304575 := bstep (se 1 (by rfl) ⟨978431, by rfl⟩ : syracuseStep 1304575 = 1956863) B1956863
theorem B1305447 : Blo 1303970 1305447 := bstep (se 1 (by rfl) ⟨979085, by rfl⟩ : syracuseStep 1305447 = 1958171) B1958171
theorem B16715483 : Blo 1303970 16715483 := bstep (se 1 (by rfl) ⟨12536612, by rfl⟩ : syracuseStep 16715483 = 25073225) B25073225
theorem B11912255 : Blo 1303970 11912255 := bstep (se 1 (by rfl) ⟨8934191, by rfl⟩ : syracuseStep 11912255 = 17868383) B17868383
theorem B11143655 : Blo 1303970 11143655 := bstep (se 1 (by rfl) ⟨8357741, by rfl⟩ : syracuseStep 11143655 = 16715483) B16715483
theorem B21149693 : Blo 1303970 21149693 := bstep (se 3 (by rfl) ⟨3965567, by rfl⟩ : syracuseStep 21149693 = 7931135) B7931135
theorem B14099795 : Blo 1303970 14099795 := bstep (se 1 (by rfl) ⟨10574846, by rfl⟩ : syracuseStep 14099795 = 21149693) B21149693
theorem B7941503 : Blo 1303970 7941503 := bstep (se 1 (by rfl) ⟨5956127, by rfl⟩ : syracuseStep 7941503 = 11912255) B11912255
theorem B7429103 : Blo 1303970 7429103 := bstep (se 1 (by rfl) ⟨5571827, by rfl⟩ : syracuseStep 7429103 = 11143655) B11143655
theorem B5294335 : Blo 1303970 5294335 := bstep (se 1 (by rfl) ⟨3970751, by rfl⟩ : syracuseStep 5294335 = 7941503) B7941503
theorem B9399863 : Blo 1303970 9399863 := bstep (se 1 (by rfl) ⟨7049897, by rfl⟩ : syracuseStep 9399863 = 14099795) B14099795
theorem B4952735 : Blo 1303970 4952735 := bstep (se 1 (by rfl) ⟨3714551, by rfl⟩ : syracuseStep 4952735 = 7429103) B7429103
theorem B3301823 : Blo 1303970 3301823 := bstep (se 1 (by rfl) ⟨2476367, by rfl⟩ : syracuseStep 3301823 = 4952735) B4952735
theorem B7059113 : Blo 1303970 7059113 := bstep (se 2 (by rfl) ⟨2647167, by rfl⟩ : syracuseStep 7059113 = 5294335) B5294335
theorem B6266575 : Blo 1303970 6266575 := bstep (se 1 (by rfl) ⟨4699931, by rfl⟩ : syracuseStep 6266575 = 9399863) B9399863
theorem B4706075 : Blo 1303970 4706075 := bstep (se 1 (by rfl) ⟨3529556, by rfl⟩ : syracuseStep 4706075 = 7059113) B7059113
theorem B2201215 : Blo 1303970 2201215 := bstep (se 1 (by rfl) ⟨1650911, by rfl⟩ : syracuseStep 2201215 = 3301823) B3301823
theorem B33421733 : Blo 1303970 33421733 := bstep (se 4 (by rfl) ⟨3133287, by rfl⟩ : syracuseStep 33421733 = 6266575) B6266575
theorem B2934953 : Blo 1303970 2934953 := bstep (se 2 (by rfl) ⟨1100607, by rfl⟩ : syracuseStep 2934953 = 2201215) B2201215
theorem B22281155 : Blo 1303970 22281155 := bstep (se 1 (by rfl) ⟨16710866, by rfl⟩ : syracuseStep 22281155 = 33421733) B33421733
theorem B3137383 : Blo 1303970 3137383 := bstep (se 1 (by rfl) ⟨2353037, by rfl⟩ : syracuseStep 3137383 = 4706075) B4706075
theorem B14854103 : Blo 1303970 14854103 := bstep (se 1 (by rfl) ⟨11140577, by rfl⟩ : syracuseStep 14854103 = 22281155) B22281155
theorem B4183177 : Blo 1303970 4183177 := bstep (se 2 (by rfl) ⟨1568691, by rfl⟩ : syracuseStep 4183177 = 3137383) B3137383
theorem B1956635 : Blo 1303970 1956635 := bstep (se 1 (by rfl) ⟨1467476, by rfl⟩ : syracuseStep 1956635 = 2934953) B2934953
theorem B1304423 : Blo 1303970 1304423 := bstep (se 1 (by rfl) ⟨978317, by rfl⟩ : syracuseStep 1304423 = 1956635) B1956635
theorem B9902735 : Blo 1303970 9902735 := bstep (se 1 (by rfl) ⟨7427051, by rfl⟩ : syracuseStep 9902735 = 14854103) B14854103
theorem B5577569 : Blo 1303970 5577569 := bstep (se 2 (by rfl) ⟨2091588, by rfl⟩ : syracuseStep 5577569 = 4183177) B4183177
theorem B6601823 : Blo 1303970 6601823 := bstep (se 1 (by rfl) ⟨4951367, by rfl⟩ : syracuseStep 6601823 = 9902735) B9902735
theorem B3718379 : Blo 1303970 3718379 := bstep (se 1 (by rfl) ⟨2788784, by rfl⟩ : syracuseStep 3718379 = 5577569) B5577569
theorem B4401215 : Blo 1303970 4401215 := bstep (se 1 (by rfl) ⟨3300911, by rfl⟩ : syracuseStep 4401215 = 6601823) B6601823
theorem B2478919 : Blo 1303970 2478919 := bstep (se 1 (by rfl) ⟨1859189, by rfl⟩ : syracuseStep 2478919 = 3718379) B3718379
theorem B2934143 : Blo 1303970 2934143 := bstep (se 1 (by rfl) ⟨2200607, by rfl⟩ : syracuseStep 2934143 = 4401215) B4401215
theorem B3305225 : Blo 1303970 3305225 := bstep (se 2 (by rfl) ⟨1239459, by rfl⟩ : syracuseStep 3305225 = 2478919) B2478919
theorem B1956095 : Blo 1303970 1956095 := bstep (se 1 (by rfl) ⟨1467071, by rfl⟩ : syracuseStep 1956095 = 2934143) B2934143
theorem B2203483 : Blo 1303970 2203483 := bstep (se 1 (by rfl) ⟨1652612, by rfl⟩ : syracuseStep 2203483 = 3305225) B3305225
theorem B1304063 : Blo 1303970 1304063 := bstep (se 1 (by rfl) ⟨978047, by rfl⟩ : syracuseStep 1304063 = 1956095) B1956095
theorem B2937977 : Blo 1303970 2937977 := bstep (se 2 (by rfl) ⟨1101741, by rfl⟩ : syracuseStep 2937977 = 2203483) B2203483
theorem B1958651 : Blo 1303970 1958651 := bstep (se 1 (by rfl) ⟨1468988, by rfl⟩ : syracuseStep 1958651 = 2937977) B2937977
theorem B1305767 : Blo 1303970 1305767 := bstep (se 1 (by rfl) ⟨979325, by rfl⟩ : syracuseStep 1305767 = 1958651) B1958651

theorem C0 (j : ℕ) (h1 : 325992 ≤ j) (h2 : j ≤ 326491) : Blo 1303970 (4 * j + 3) := by
  interval_cases j
  · exact B1303971
  · exact B1303975
  · exact B1303979
  · exact B1303983
  · exact B1303987
  · exact B1303991
  · exact B1303995
  · exact B1303999
  · exact B1304003
  · exact B1304007
  · exact B1304011
  · exact B1304015
  · exact B1304019
  · exact B1304023
  · exact B1304027
  · exact B1304031
  · exact B1304035
  · exact B1304039
  · exact B1304043
  · exact B1304047
  · exact B1304051
  · exact B1304055
  · exact B1304059
  · exact B1304063
  · exact B1304067
  · exact B1304071
  · exact B1304075
  · exact B1304079
  · exact B1304083
  · exact B1304087
  · exact B1304091
  · exact B1304095
  · exact B1304099
  · exact B1304103
  · exact B1304107
  · exact B1304111
  · exact B1304115
  · exact B1304119
  · exact B1304123
  · exact B1304127
  · exact B1304131
  · exact B1304135
  · exact B1304139
  · exact B1304143
  · exact B1304147
  · exact B1304151
  · exact B1304155
  · exact B1304159
  · exact B1304163
  · exact B1304167
  · exact B1304171
  · exact B1304175
  · exact B1304179
  · exact B1304183
  · exact B1304187
  · exact B1304191
  · exact B1304195
  · exact B1304199
  · exact B1304203
  · exact B1304207
  · exact B1304211
  · exact B1304215
  · exact B1304219
  · exact B1304223
  · exact B1304227
  · exact B1304231
  · exact B1304235
  · exact B1304239
  · exact B1304243
  · exact B1304247
  · exact B1304251
  · exact B1304255
  · exact B1304259
  · exact B1304263
  · exact B1304267
  · exact B1304271
  · exact B1304275
  · exact B1304279
  · exact B1304283
  · exact B1304287
  · exact B1304291
  · exact B1304295
  · exact B1304299
  · exact B1304303
  · exact B1304307
  · exact B1304311
  · exact B1304315
  · exact B1304319
  · exact B1304323
  · exact B1304327
  · exact B1304331
  · exact B1304335
  · exact B1304339
  · exact B1304343
  · exact B1304347
  · exact B1304351
  · exact B1304355
  · exact B1304359
  · exact B1304363
  · exact B1304367
  · exact B1304371
  · exact B1304375
  · exact B1304379
  · exact B1304383
  · exact B1304387
  · exact B1304391
  · exact B1304395
  · exact B1304399
  · exact B1304403
  · exact B1304407
  · exact B1304411
  · exact B1304415
  · exact B1304419
  · exact B1304423
  · exact B1304427
  · exact B1304431
  · exact B1304435
  · exact B1304439
  · exact B1304443
  · exact B1304447
  · exact B1304451
  · exact B1304455
  · exact B1304459
  · exact B1304463
  · exact B1304467
  · exact B1304471
  · exact B1304475
  · exact B1304479
  · exact B1304483
  · exact B1304487
  · exact B1304491
  · exact B1304495
  · exact B1304499
  · exact B1304503
  · exact B1304507
  · exact B1304511
  · exact B1304515
  · exact B1304519
  · exact B1304523
  · exact B1304527
  · exact B1304531
  · exact B1304535
  · exact B1304539
  · exact B1304543
  · exact B1304547
  · exact B1304551
  · exact B1304555
  · exact B1304559
  · exact B1304563
  · exact B1304567
  · exact B1304571
  · exact B1304575
  · exact B1304579
  · exact B1304583
  · exact B1304587
  · exact B1304591
  · exact B1304595
  · exact B1304599
  · exact B1304603
  · exact B1304607
  · exact B1304611
  · exact B1304615
  · exact B1304619
  · exact B1304623
  · exact B1304627
  · exact B1304631
  · exact B1304635
  · exact B1304639
  · exact B1304643
  · exact B1304647
  · exact B1304651
  · exact B1304655
  · exact B1304659
  · exact B1304663
  · exact B1304667
  · exact B1304671
  · exact B1304675
  · exact B1304679
  · exact B1304683
  · exact B1304687
  · exact B1304691
  · exact B1304695
  · exact B1304699
  · exact B1304703
  · exact B1304707
  · exact B1304711
  · exact B1304715
  · exact B1304719
  · exact B1304723
  · exact B1304727
  · exact B1304731
  · exact B1304735
  · exact B1304739
  · exact B1304743
  · exact B1304747
  · exact B1304751
  · exact B1304755
  · exact B1304759
  · exact B1304763
  · exact B1304767
  · exact B1304771
  · exact B1304775
  · exact B1304779
  · exact B1304783
  · exact B1304787
  · exact B1304791
  · exact B1304795
  · exact B1304799
  · exact B1304803
  · exact B1304807
  · exact B1304811
  · exact B1304815
  · exact B1304819
  · exact B1304823
  · exact B1304827
  · exact B1304831
  · exact B1304835
  · exact B1304839
  · exact B1304843
  · exact B1304847
  · exact B1304851
  · exact B1304855
  · exact B1304859
  · exact B1304863
  · exact B1304867
  · exact B1304871
  · exact B1304875
  · exact B1304879
  · exact B1304883
  · exact B1304887
  · exact B1304891
  · exact B1304895
  · exact B1304899
  · exact B1304903
  · exact B1304907
  · exact B1304911
  · exact B1304915
  · exact B1304919
  · exact B1304923
  · exact B1304927
  · exact B1304931
  · exact B1304935
  · exact B1304939
  · exact B1304943
  · exact B1304947
  · exact B1304951
  · exact B1304955
  · exact B1304959
  · exact B1304963
  · exact B1304967
  · exact B1304971
  · exact B1304975
  · exact B1304979
  · exact B1304983
  · exact B1304987
  · exact B1304991
  · exact B1304995
  · exact B1304999
  · exact B1305003
  · exact B1305007
  · exact B1305011
  · exact B1305015
  · exact B1305019
  · exact B1305023
  · exact B1305027
  · exact B1305031
  · exact B1305035
  · exact B1305039
  · exact B1305043
  · exact B1305047
  · exact B1305051
  · exact B1305055
  · exact B1305059
  · exact B1305063
  · exact B1305067
  · exact B1305071
  · exact B1305075
  · exact B1305079
  · exact B1305083
  · exact B1305087
  · exact B1305091
  · exact B1305095
  · exact B1305099
  · exact B1305103
  · exact B1305107
  · exact B1305111
  · exact B1305115
  · exact B1305119
  · exact B1305123
  · exact B1305127
  · exact B1305131
  · exact B1305135
  · exact B1305139
  · exact B1305143
  · exact B1305147
  · exact B1305151
  · exact B1305155
  · exact B1305159
  · exact B1305163
  · exact B1305167
  · exact B1305171
  · exact B1305175
  · exact B1305179
  · exact B1305183
  · exact B1305187
  · exact B1305191
  · exact B1305195
  · exact B1305199
  · exact B1305203
  · exact B1305207
  · exact B1305211
  · exact B1305215
  · exact B1305219
  · exact B1305223
  · exact B1305227
  · exact B1305231
  · exact B1305235
  · exact B1305239
  · exact B1305243
  · exact B1305247
  · exact B1305251
  · exact B1305255
  · exact B1305259
  · exact B1305263
  · exact B1305267
  · exact B1305271
  · exact B1305275
  · exact B1305279
  · exact B1305283
  · exact B1305287
  · exact B1305291
  · exact B1305295
  · exact B1305299
  · exact B1305303
  · exact B1305307
  · exact B1305311
  · exact B1305315
  · exact B1305319
  · exact B1305323
  · exact B1305327
  · exact B1305331
  · exact B1305335
  · exact B1305339
  · exact B1305343
  · exact B1305347
  · exact B1305351
  · exact B1305355
  · exact B1305359
  · exact B1305363
  · exact B1305367
  · exact B1305371
  · exact B1305375
  · exact B1305379
  · exact B1305383
  · exact B1305387
  · exact B1305391
  · exact B1305395
  · exact B1305399
  · exact B1305403
  · exact B1305407
  · exact B1305411
  · exact B1305415
  · exact B1305419
  · exact B1305423
  · exact B1305427
  · exact B1305431
  · exact B1305435
  · exact B1305439
  · exact B1305443
  · exact B1305447
  · exact B1305451
  · exact B1305455
  · exact B1305459
  · exact B1305463
  · exact B1305467
  · exact B1305471
  · exact B1305475
  · exact B1305479
  · exact B1305483
  · exact B1305487
  · exact B1305491
  · exact B1305495
  · exact B1305499
  · exact B1305503
  · exact B1305507
  · exact B1305511
  · exact B1305515
  · exact B1305519
  · exact B1305523
  · exact B1305527
  · exact B1305531
  · exact B1305535
  · exact B1305539
  · exact B1305543
  · exact B1305547
  · exact B1305551
  · exact B1305555
  · exact B1305559
  · exact B1305563
  · exact B1305567
  · exact B1305571
  · exact B1305575
  · exact B1305579
  · exact B1305583
  · exact B1305587
  · exact B1305591
  · exact B1305595
  · exact B1305599
  · exact B1305603
  · exact B1305607
  · exact B1305611
  · exact B1305615
  · exact B1305619
  · exact B1305623
  · exact B1305627
  · exact B1305631
  · exact B1305635
  · exact B1305639
  · exact B1305643
  · exact B1305647
  · exact B1305651
  · exact B1305655
  · exact B1305659
  · exact B1305663
  · exact B1305667
  · exact B1305671
  · exact B1305675
  · exact B1305679
  · exact B1305683
  · exact B1305687
  · exact B1305691
  · exact B1305695
  · exact B1305699
  · exact B1305703
  · exact B1305707
  · exact B1305711
  · exact B1305715
  · exact B1305719
  · exact B1305723
  · exact B1305727
  · exact B1305731
  · exact B1305735
  · exact B1305739
  · exact B1305743
  · exact B1305747
  · exact B1305751
  · exact B1305755
  · exact B1305759
  · exact B1305763
  · exact B1305767
  · exact B1305771
  · exact B1305775
  · exact B1305779
  · exact B1305783
  · exact B1305787
  · exact B1305791
  · exact B1305795
  · exact B1305799
  · exact B1305803
  · exact B1305807
  · exact B1305811
  · exact B1305815
  · exact B1305819
  · exact B1305823
  · exact B1305827
  · exact B1305831
  · exact B1305835
  · exact B1305839
  · exact B1305843
  · exact B1305847
  · exact B1305851
  · exact B1305855
  · exact B1305859
  · exact B1305863
  · exact B1305867
  · exact B1305871
  · exact B1305875
  · exact B1305879
  · exact B1305883
  · exact B1305887
  · exact B1305891
  · exact B1305895
  · exact B1305899
  · exact B1305903
  · exact B1305907
  · exact B1305911
  · exact B1305915
  · exact B1305919
  · exact B1305923
  · exact B1305927
  · exact B1305931
  · exact B1305935
  · exact B1305939
  · exact B1305943
  · exact B1305947
  · exact B1305951
  · exact B1305955
  · exact B1305959
  · exact B1305963
  · exact B1305967

theorem solution (m : ℕ) (hlo : 1303970 ≤ m) (hhi : m ≤ 1305970) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 325992 ≤ j := by omega
    have hj2 : j ≤ 326491 := by omega
    have hb : Blo 1303970 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
