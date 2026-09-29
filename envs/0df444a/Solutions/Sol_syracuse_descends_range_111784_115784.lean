-- Prove2me | solution 1 for syracuse_descends_range_111784_115784
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T16:43:29.804492+00:00
-- url     : https://prove2.me/submissions/4fb0a2af-5e84-444a-a432-fbd1289679e6

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


theorem B1310741 : Blo 111784 1310741 := bbase (se 6 (by rfl) ⟨30720, by rfl⟩ : syracuseStep 1310741 = 61441) (by norm_num)
theorem B163957 : Blo 111784 163957 := bbase (se 5 (by rfl) ⟨7685, by rfl⟩ : syracuseStep 163957 = 15371) (by norm_num)
theorem B361061 : Blo 111784 361061 := bbase (se 4 (by rfl) ⟨33849, by rfl⟩ : syracuseStep 361061 = 67699) (by norm_num)
theorem B623285 : Blo 111784 623285 := bbase (se 5 (by rfl) ⟨29216, by rfl⟩ : syracuseStep 623285 = 58433) (by norm_num)
theorem B164549 : Blo 111784 164549 := bbase (se 4 (by rfl) ⟨15426, by rfl⟩ : syracuseStep 164549 = 30853) (by norm_num)
theorem B361189 : Blo 111784 361189 := bbase (se 4 (by rfl) ⟨33861, by rfl⟩ : syracuseStep 361189 = 67723) (by norm_num)
theorem B164629 : Blo 111784 164629 := bbase (se 6 (by rfl) ⟨3858, by rfl⟩ : syracuseStep 164629 = 7717) (by norm_num)
theorem B164749 : Blo 111784 164749 := bbase (se 3 (by rfl) ⟨30890, by rfl⟩ : syracuseStep 164749 = 61781) (by norm_num)
theorem B164845 : Blo 111784 164845 := bbase (se 3 (by rfl) ⟨30908, by rfl⟩ : syracuseStep 164845 = 61817) (by norm_num)
theorem B591077 : Blo 111784 591077 := bbase (se 4 (by rfl) ⟨55413, by rfl⟩ : syracuseStep 591077 = 110827) (by norm_num)
theorem B427301 : Blo 111784 427301 := bbase (se 4 (by rfl) ⟨40059, by rfl⟩ : syracuseStep 427301 = 80119) (by norm_num)
theorem B656693 : Blo 111784 656693 := bbase (se 5 (by rfl) ⟨30782, by rfl⟩ : syracuseStep 656693 = 61565) (by norm_num)
theorem B296309 : Blo 111784 296309 := bbase (se 5 (by rfl) ⟨13889, by rfl⟩ : syracuseStep 296309 = 27779) (by norm_num)
theorem B492965 : Blo 111784 492965 := bbase (se 4 (by rfl) ⟨46215, by rfl⟩ : syracuseStep 492965 = 92431) (by norm_num)
theorem B165341 : Blo 111784 165341 := bbase (se 3 (by rfl) ⟨31001, by rfl⟩ : syracuseStep 165341 = 62003) (by norm_num)
theorem B230917 : Blo 111784 230917 := bbase (se 4 (by rfl) ⟨21648, by rfl⟩ : syracuseStep 230917 = 43297) (by norm_num)
theorem B427589 : Blo 111784 427589 := bbase (se 4 (by rfl) ⟨40086, by rfl⟩ : syracuseStep 427589 = 80173) (by norm_num)
theorem B231005 : Blo 111784 231005 := bbase (se 3 (by rfl) ⟨43313, by rfl⟩ : syracuseStep 231005 = 86627) (by norm_num)
theorem B132949 : Blo 111784 132949 := bbase (se 9 (by rfl) ⟨389, by rfl⟩ : syracuseStep 132949 = 779) (by norm_num)
theorem B296893 : Blo 111784 296893 := bbase (se 3 (by rfl) ⟨55667, by rfl⟩ : syracuseStep 296893 = 111335) (by norm_num)
theorem B264173 : Blo 111784 264173 := bbase (se 3 (by rfl) ⟨49532, by rfl⟩ : syracuseStep 264173 = 99065) (by norm_num)
theorem B231437 : Blo 111784 231437 := bbase (se 3 (by rfl) ⟨43394, by rfl⟩ : syracuseStep 231437 = 86789) (by norm_num)
theorem B625205 : Blo 111784 625205 := bbase (se 5 (by rfl) ⟨29306, by rfl⟩ : syracuseStep 625205 = 58613) (by norm_num)
theorem B658037 : Blo 111784 658037 := bbase (se 5 (by rfl) ⟨30845, by rfl⟩ : syracuseStep 658037 = 61691) (by norm_num)
theorem B428773 : Blo 111784 428773 := bbase (se 4 (by rfl) ⟨40197, by rfl⟩ : syracuseStep 428773 = 80395) (by norm_num)
theorem B429077 : Blo 111784 429077 := bbase (se 6 (by rfl) ⟨10056, by rfl⟩ : syracuseStep 429077 = 20113) (by norm_num)
theorem B2067605 : Blo 111784 2067605 := bbase (se 6 (by rfl) ⟨48459, by rfl⟩ : syracuseStep 2067605 = 96919) (by norm_num)
theorem B1379861 : Blo 111784 1379861 := bbase (se 6 (by rfl) ⟨32340, by rfl⟩ : syracuseStep 1379861 = 64681) (by norm_num)
theorem B364085 : Blo 111784 364085 := bbase (se 5 (by rfl) ⟨17066, by rfl⟩ : syracuseStep 364085 = 34133) (by norm_num)
theorem B167693 : Blo 111784 167693 := bbase (se 3 (by rfl) ⟨31442, by rfl⟩ : syracuseStep 167693 = 62885) (by norm_num)
theorem B167717 : Blo 111784 167717 := bbase (se 4 (by rfl) ⟨15723, by rfl⟩ : syracuseStep 167717 = 31447) (by norm_num)
theorem B167741 : Blo 111784 167741 := bbase (se 3 (by rfl) ⟨31451, by rfl⟩ : syracuseStep 167741 = 62903) (by norm_num)
theorem B167765 : Blo 111784 167765 := bbase (se 9 (by rfl) ⟨491, by rfl⟩ : syracuseStep 167765 = 983) (by norm_num)
theorem B167789 : Blo 111784 167789 := bbase (se 3 (by rfl) ⟨31460, by rfl⟩ : syracuseStep 167789 = 62921) (by norm_num)
theorem B167813 : Blo 111784 167813 := bbase (se 4 (by rfl) ⟨15732, by rfl⟩ : syracuseStep 167813 = 31465) (by norm_num)
theorem B167837 : Blo 111784 167837 := bbase (se 3 (by rfl) ⟨31469, by rfl⟩ : syracuseStep 167837 = 62939) (by norm_num)
theorem B167861 : Blo 111784 167861 := bbase (se 5 (by rfl) ⟨7868, by rfl⟩ : syracuseStep 167861 = 15737) (by norm_num)
theorem B167885 : Blo 111784 167885 := bbase (se 3 (by rfl) ⟨31478, by rfl⟩ : syracuseStep 167885 = 62957) (by norm_num)
theorem B2625493 : Blo 111784 2625493 := bbase (se 7 (by rfl) ⟨30767, by rfl⟩ : syracuseStep 2625493 = 61535) (by norm_num)
theorem B167909 : Blo 111784 167909 := bbase (se 4 (by rfl) ⟨15741, by rfl⟩ : syracuseStep 167909 = 31483) (by norm_num)
theorem B167933 : Blo 111784 167933 := bbase (se 3 (by rfl) ⟨31487, by rfl⟩ : syracuseStep 167933 = 62975) (by norm_num)
theorem B167957 : Blo 111784 167957 := bbase (se 6 (by rfl) ⟨3936, by rfl⟩ : syracuseStep 167957 = 7873) (by norm_num)
theorem B167981 : Blo 111784 167981 := bbase (se 3 (by rfl) ⟨31496, by rfl⟩ : syracuseStep 167981 = 62993) (by norm_num)
theorem B168005 : Blo 111784 168005 := bbase (se 4 (by rfl) ⟨15750, by rfl⟩ : syracuseStep 168005 = 31501) (by norm_num)
theorem B168029 : Blo 111784 168029 := bbase (se 3 (by rfl) ⟨31505, by rfl⟩ : syracuseStep 168029 = 63011) (by norm_num)
theorem B168053 : Blo 111784 168053 := bbase (se 5 (by rfl) ⟨7877, by rfl⟩ : syracuseStep 168053 = 15755) (by norm_num)
theorem B168077 : Blo 111784 168077 := bbase (se 3 (by rfl) ⟨31514, by rfl⟩ : syracuseStep 168077 = 63029) (by norm_num)
theorem B135317 : Blo 111784 135317 := bbase (se 6 (by rfl) ⟨3171, by rfl⟩ : syracuseStep 135317 = 6343) (by norm_num)
theorem B168101 : Blo 111784 168101 := bbase (se 4 (by rfl) ⟨15759, by rfl⟩ : syracuseStep 168101 = 31519) (by norm_num)
theorem B168125 : Blo 111784 168125 := bbase (se 3 (by rfl) ⟨31523, by rfl⟩ : syracuseStep 168125 = 63047) (by norm_num)
theorem B168149 : Blo 111784 168149 := bbase (se 7 (by rfl) ⟨1970, by rfl⟩ : syracuseStep 168149 = 3941) (by norm_num)
theorem B168173 : Blo 111784 168173 := bbase (se 3 (by rfl) ⟨31532, by rfl⟩ : syracuseStep 168173 = 63065) (by norm_num)
theorem B168197 : Blo 111784 168197 := bbase (se 4 (by rfl) ⟨15768, by rfl⟩ : syracuseStep 168197 = 31537) (by norm_num)
theorem B168221 : Blo 111784 168221 := bbase (se 3 (by rfl) ⟨31541, by rfl⟩ : syracuseStep 168221 = 63083) (by norm_num)
theorem B168245 : Blo 111784 168245 := bbase (se 5 (by rfl) ⟨7886, by rfl⟩ : syracuseStep 168245 = 15773) (by norm_num)
theorem B168269 : Blo 111784 168269 := bbase (se 3 (by rfl) ⟨31550, by rfl⟩ : syracuseStep 168269 = 63101) (by norm_num)
theorem B1118549 : Blo 111784 1118549 := bbase (se 10 (by rfl) ⟨1638, by rfl⟩ : syracuseStep 1118549 = 3277) (by norm_num)
theorem B168293 : Blo 111784 168293 := bbase (se 4 (by rfl) ⟨15777, by rfl⟩ : syracuseStep 168293 = 31555) (by norm_num)
theorem B168317 : Blo 111784 168317 := bbase (se 3 (by rfl) ⟨31559, by rfl⟩ : syracuseStep 168317 = 63119) (by norm_num)
theorem B233861 : Blo 111784 233861 := bbase (se 4 (by rfl) ⟨21924, by rfl⟩ : syracuseStep 233861 = 43849) (by norm_num)
theorem B233869 : Blo 111784 233869 := bbase (se 3 (by rfl) ⟨43850, by rfl⟩ : syracuseStep 233869 = 87701) (by norm_num)
theorem B168341 : Blo 111784 168341 := bbase (se 6 (by rfl) ⟨3945, by rfl⟩ : syracuseStep 168341 = 7891) (by norm_num)
theorem B168365 : Blo 111784 168365 := bbase (se 3 (by rfl) ⟨31568, by rfl⟩ : syracuseStep 168365 = 63137) (by norm_num)
theorem B168389 : Blo 111784 168389 := bbase (se 4 (by rfl) ⟨15786, by rfl⟩ : syracuseStep 168389 = 31573) (by norm_num)
theorem B233933 : Blo 111784 233933 := bbase (se 3 (by rfl) ⟨43862, by rfl⟩ : syracuseStep 233933 = 87725) (by norm_num)
theorem B168413 : Blo 111784 168413 := bbase (se 3 (by rfl) ⟨31577, by rfl⟩ : syracuseStep 168413 = 63155) (by norm_num)
theorem B168437 : Blo 111784 168437 := bbase (se 5 (by rfl) ⟨7895, by rfl⟩ : syracuseStep 168437 = 15791) (by norm_num)
theorem B168461 : Blo 111784 168461 := bbase (se 3 (by rfl) ⟨31586, by rfl⟩ : syracuseStep 168461 = 63173) (by norm_num)
theorem B168485 : Blo 111784 168485 := bbase (se 4 (by rfl) ⟨15795, by rfl⟩ : syracuseStep 168485 = 31591) (by norm_num)
theorem B168509 : Blo 111784 168509 := bbase (se 3 (by rfl) ⟨31595, by rfl⟩ : syracuseStep 168509 = 63191) (by norm_num)
theorem B168533 : Blo 111784 168533 := bbase (se 8 (by rfl) ⟨987, by rfl⟩ : syracuseStep 168533 = 1975) (by norm_num)
theorem B168557 : Blo 111784 168557 := bbase (se 3 (by rfl) ⟨31604, by rfl⟩ : syracuseStep 168557 = 63209) (by norm_num)
theorem B168581 : Blo 111784 168581 := bbase (se 4 (by rfl) ⟨15804, by rfl⟩ : syracuseStep 168581 = 31609) (by norm_num)
theorem B168605 : Blo 111784 168605 := bbase (se 3 (by rfl) ⟨31613, by rfl⟩ : syracuseStep 168605 = 63227) (by norm_num)
theorem B168629 : Blo 111784 168629 := bbase (se 5 (by rfl) ⟨7904, by rfl⟩ : syracuseStep 168629 = 15809) (by norm_num)
theorem B168653 : Blo 111784 168653 := bbase (se 3 (by rfl) ⟨31622, by rfl⟩ : syracuseStep 168653 = 63245) (by norm_num)
theorem B168677 : Blo 111784 168677 := bbase (se 4 (by rfl) ⟨15813, by rfl⟩ : syracuseStep 168677 = 31627) (by norm_num)
theorem B168701 : Blo 111784 168701 := bbase (se 3 (by rfl) ⟨31631, by rfl⟩ : syracuseStep 168701 = 63263) (by norm_num)
theorem B135941 : Blo 111784 135941 := bbase (se 4 (by rfl) ⟨12744, by rfl⟩ : syracuseStep 135941 = 25489) (by norm_num)
theorem B168725 : Blo 111784 168725 := bbase (se 6 (by rfl) ⟨3954, by rfl⟩ : syracuseStep 168725 = 7909) (by norm_num)
theorem B168749 : Blo 111784 168749 := bbase (se 3 (by rfl) ⟨31640, by rfl⟩ : syracuseStep 168749 = 63281) (by norm_num)
theorem B201541 : Blo 111784 201541 := bbase (se 4 (by rfl) ⟨18894, by rfl⟩ : syracuseStep 201541 = 37789) (by norm_num)
theorem B168773 : Blo 111784 168773 := bbase (se 4 (by rfl) ⟨15822, by rfl⟩ : syracuseStep 168773 = 31645) (by norm_num)
theorem B168797 : Blo 111784 168797 := bbase (se 3 (by rfl) ⟨31649, by rfl⟩ : syracuseStep 168797 = 63299) (by norm_num)
theorem B168821 : Blo 111784 168821 := bbase (se 5 (by rfl) ⟨7913, by rfl⟩ : syracuseStep 168821 = 15827) (by norm_num)
theorem B168845 : Blo 111784 168845 := bbase (se 3 (by rfl) ⟨31658, by rfl⟩ : syracuseStep 168845 = 63317) (by norm_num)
theorem B234389 : Blo 111784 234389 := bbase (se 6 (by rfl) ⟨5493, by rfl⟩ : syracuseStep 234389 = 10987) (by norm_num)
theorem B168869 : Blo 111784 168869 := bbase (se 4 (by rfl) ⟨15831, by rfl⟩ : syracuseStep 168869 = 31663) (by norm_num)
theorem B463781 : Blo 111784 463781 := bbase (se 4 (by rfl) ⟨43479, by rfl⟩ : syracuseStep 463781 = 86959) (by norm_num)
theorem B168893 : Blo 111784 168893 := bbase (se 3 (by rfl) ⟨31667, by rfl⟩ : syracuseStep 168893 = 63335) (by norm_num)
theorem B201685 : Blo 111784 201685 := bbase (se 7 (by rfl) ⟨2363, by rfl⟩ : syracuseStep 201685 = 4727) (by norm_num)
theorem B168917 : Blo 111784 168917 := bbase (se 7 (by rfl) ⟨1979, by rfl⟩ : syracuseStep 168917 = 3959) (by norm_num)
theorem B168941 : Blo 111784 168941 := bbase (se 3 (by rfl) ⟨31676, by rfl⟩ : syracuseStep 168941 = 63353) (by norm_num)
theorem B168965 : Blo 111784 168965 := bbase (se 4 (by rfl) ⟨15840, by rfl⟩ : syracuseStep 168965 = 31681) (by norm_num)
theorem B168989 : Blo 111784 168989 := bbase (se 3 (by rfl) ⟨31685, by rfl⟩ : syracuseStep 168989 = 63371) (by norm_num)
theorem B169013 : Blo 111784 169013 := bbase (se 5 (by rfl) ⟨7922, by rfl⟩ : syracuseStep 169013 = 15845) (by norm_num)
theorem B169037 : Blo 111784 169037 := bbase (se 3 (by rfl) ⟨31694, by rfl⟩ : syracuseStep 169037 = 63389) (by norm_num)
theorem B431189 : Blo 111784 431189 := bbase (se 8 (by rfl) ⟨2526, by rfl⟩ : syracuseStep 431189 = 5053) (by norm_num)
theorem B169061 : Blo 111784 169061 := bbase (se 4 (by rfl) ⟨15849, by rfl⟩ : syracuseStep 169061 = 31699) (by norm_num)
theorem B463973 : Blo 111784 463973 := bbase (se 4 (by rfl) ⟨43497, by rfl⟩ : syracuseStep 463973 = 86995) (by norm_num)
theorem B169085 : Blo 111784 169085 := bbase (se 3 (by rfl) ⟨31703, by rfl⟩ : syracuseStep 169085 = 63407) (by norm_num)
theorem B169109 : Blo 111784 169109 := bbase (se 6 (by rfl) ⟨3963, by rfl⟩ : syracuseStep 169109 = 7927) (by norm_num)
theorem B169133 : Blo 111784 169133 := bbase (se 3 (by rfl) ⟨31712, by rfl⟩ : syracuseStep 169133 = 63425) (by norm_num)
theorem B169157 : Blo 111784 169157 := bbase (se 4 (by rfl) ⟨15858, by rfl⟩ : syracuseStep 169157 = 31717) (by norm_num)
theorem B169181 : Blo 111784 169181 := bbase (se 3 (by rfl) ⟨31721, by rfl⟩ : syracuseStep 169181 = 63443) (by norm_num)
theorem B169205 : Blo 111784 169205 := bbase (se 5 (by rfl) ⟨7931, by rfl⟩ : syracuseStep 169205 = 15863) (by norm_num)
theorem B169229 : Blo 111784 169229 := bbase (se 3 (by rfl) ⟨31730, by rfl⟩ : syracuseStep 169229 = 63461) (by norm_num)
theorem B169253 : Blo 111784 169253 := bbase (se 4 (by rfl) ⟨15867, by rfl⟩ : syracuseStep 169253 = 31735) (by norm_num)
theorem B169277 : Blo 111784 169277 := bbase (se 3 (by rfl) ⟨31739, by rfl⟩ : syracuseStep 169277 = 63479) (by norm_num)
theorem B136513 : Blo 111784 136513 := bbase (se 2 (by rfl) ⟨51192, by rfl⟩ : syracuseStep 136513 = 102385) (by norm_num)
theorem B169301 : Blo 111784 169301 := bbase (se 14 (by rfl) ⟨15, by rfl⟩ : syracuseStep 169301 = 31) (by norm_num)
theorem B169325 : Blo 111784 169325 := bbase (se 3 (by rfl) ⟨31748, by rfl⟩ : syracuseStep 169325 = 63497) (by norm_num)
theorem B431477 : Blo 111784 431477 := bbase (se 5 (by rfl) ⟨20225, by rfl⟩ : syracuseStep 431477 = 40451) (by norm_num)
theorem B202117 : Blo 111784 202117 := bbase (se 4 (by rfl) ⟨18948, by rfl⟩ : syracuseStep 202117 = 37897) (by norm_num)
theorem B169349 : Blo 111784 169349 := bbase (se 4 (by rfl) ⟨15876, by rfl⟩ : syracuseStep 169349 = 31753) (by norm_num)
theorem B136585 : Blo 111784 136585 := bbase (se 2 (by rfl) ⟨51219, by rfl⟩ : syracuseStep 136585 = 102439) (by norm_num)
theorem B169373 : Blo 111784 169373 := bbase (se 3 (by rfl) ⟨31757, by rfl⟩ : syracuseStep 169373 = 63515) (by norm_num)
theorem B169397 : Blo 111784 169397 := bbase (se 5 (by rfl) ⟨7940, by rfl⟩ : syracuseStep 169397 = 15881) (by norm_num)
theorem B169421 : Blo 111784 169421 := bbase (se 3 (by rfl) ⟨31766, by rfl⟩ : syracuseStep 169421 = 63533) (by norm_num)
theorem B169445 : Blo 111784 169445 := bbase (se 4 (by rfl) ⟨15885, by rfl⟩ : syracuseStep 169445 = 31771) (by norm_num)
theorem B169469 : Blo 111784 169469 := bbase (se 3 (by rfl) ⟨31775, by rfl⟩ : syracuseStep 169469 = 63551) (by norm_num)
theorem B169493 : Blo 111784 169493 := bbase (se 6 (by rfl) ⟨3972, by rfl⟩ : syracuseStep 169493 = 7945) (by norm_num)
theorem B169517 : Blo 111784 169517 := bbase (se 3 (by rfl) ⟨31784, by rfl⟩ : syracuseStep 169517 = 63569) (by norm_num)
theorem B169541 : Blo 111784 169541 := bbase (se 4 (by rfl) ⟨15894, by rfl⟩ : syracuseStep 169541 = 31789) (by norm_num)
theorem B169565 : Blo 111784 169565 := bbase (se 3 (by rfl) ⟨31793, by rfl⟩ : syracuseStep 169565 = 63587) (by norm_num)
theorem B169589 : Blo 111784 169589 := bbase (se 5 (by rfl) ⟨7949, by rfl⟩ : syracuseStep 169589 = 15899) (by norm_num)
theorem B169613 : Blo 111784 169613 := bbase (se 3 (by rfl) ⟨31802, by rfl⟩ : syracuseStep 169613 = 63605) (by norm_num)
theorem B202405 : Blo 111784 202405 := bbase (se 4 (by rfl) ⟨18975, by rfl⟩ : syracuseStep 202405 = 37951) (by norm_num)
theorem B169637 : Blo 111784 169637 := bbase (se 4 (by rfl) ⟨15903, by rfl⟩ : syracuseStep 169637 = 31807) (by norm_num)
theorem B169661 : Blo 111784 169661 := bbase (se 3 (by rfl) ⟨31811, by rfl⟩ : syracuseStep 169661 = 63623) (by norm_num)
theorem B366277 : Blo 111784 366277 := bbase (se 4 (by rfl) ⟨34338, by rfl⟩ : syracuseStep 366277 = 68677) (by norm_num)
theorem B169685 : Blo 111784 169685 := bbase (se 7 (by rfl) ⟨1988, by rfl⟩ : syracuseStep 169685 = 3977) (by norm_num)
theorem B169709 : Blo 111784 169709 := bbase (se 3 (by rfl) ⟨31820, by rfl⟩ : syracuseStep 169709 = 63641) (by norm_num)
theorem B169733 : Blo 111784 169733 := bbase (se 4 (by rfl) ⟨15912, by rfl⟩ : syracuseStep 169733 = 31825) (by norm_num)
theorem B169757 : Blo 111784 169757 := bbase (se 3 (by rfl) ⟨31829, by rfl⟩ : syracuseStep 169757 = 63659) (by norm_num)
theorem B169781 : Blo 111784 169781 := bbase (se 5 (by rfl) ⟨7958, by rfl⟩ : syracuseStep 169781 = 15917) (by norm_num)
theorem B169805 : Blo 111784 169805 := bbase (se 3 (by rfl) ⟨31838, by rfl⟩ : syracuseStep 169805 = 63677) (by norm_num)
theorem B169829 : Blo 111784 169829 := bbase (se 4 (by rfl) ⟨15921, by rfl⟩ : syracuseStep 169829 = 31843) (by norm_num)
theorem B169853 : Blo 111784 169853 := bbase (se 3 (by rfl) ⟨31847, by rfl⟩ : syracuseStep 169853 = 63695) (by norm_num)
theorem B169877 : Blo 111784 169877 := bbase (se 6 (by rfl) ⟨3981, by rfl⟩ : syracuseStep 169877 = 7963) (by norm_num)
theorem B169901 : Blo 111784 169901 := bbase (se 3 (by rfl) ⟨31856, by rfl⟩ : syracuseStep 169901 = 63713) (by norm_num)
theorem B169925 : Blo 111784 169925 := bbase (se 4 (by rfl) ⟨15930, by rfl⟩ : syracuseStep 169925 = 31861) (by norm_num)
theorem B169949 : Blo 111784 169949 := bbase (se 3 (by rfl) ⟨31865, by rfl⟩ : syracuseStep 169949 = 63731) (by norm_num)
theorem B169973 : Blo 111784 169973 := bbase (se 5 (by rfl) ⟨7967, by rfl⟩ : syracuseStep 169973 = 15935) (by norm_num)
theorem B169997 : Blo 111784 169997 := bbase (se 3 (by rfl) ⟨31874, by rfl⟩ : syracuseStep 169997 = 63749) (by norm_num)
theorem B170021 : Blo 111784 170021 := bbase (se 4 (by rfl) ⟨15939, by rfl⟩ : syracuseStep 170021 = 31879) (by norm_num)
theorem B170045 : Blo 111784 170045 := bbase (se 3 (by rfl) ⟨31883, by rfl⟩ : syracuseStep 170045 = 63767) (by norm_num)
theorem B170069 : Blo 111784 170069 := bbase (se 8 (by rfl) ⟨996, by rfl⟩ : syracuseStep 170069 = 1993) (by norm_num)
theorem B170093 : Blo 111784 170093 := bbase (se 3 (by rfl) ⟨31892, by rfl⟩ : syracuseStep 170093 = 63785) (by norm_num)
theorem B170117 : Blo 111784 170117 := bbase (se 4 (by rfl) ⟨15948, by rfl⟩ : syracuseStep 170117 = 31897) (by norm_num)
theorem B170141 : Blo 111784 170141 := bbase (se 3 (by rfl) ⟨31901, by rfl⟩ : syracuseStep 170141 = 63803) (by norm_num)
theorem B202925 : Blo 111784 202925 := bbase (se 3 (by rfl) ⟨38048, by rfl⟩ : syracuseStep 202925 = 76097) (by norm_num)
theorem B170165 : Blo 111784 170165 := bbase (se 5 (by rfl) ⟨7976, by rfl⟩ : syracuseStep 170165 = 15953) (by norm_num)
theorem B170189 : Blo 111784 170189 := bbase (se 3 (by rfl) ⟨31910, by rfl⟩ : syracuseStep 170189 = 63821) (by norm_num)
theorem B170213 : Blo 111784 170213 := bbase (se 4 (by rfl) ⟨15957, by rfl⟩ : syracuseStep 170213 = 31915) (by norm_num)
theorem B170237 : Blo 111784 170237 := bbase (se 3 (by rfl) ⟨31919, by rfl⟩ : syracuseStep 170237 = 63839) (by norm_num)
theorem B235781 : Blo 111784 235781 := bbase (se 4 (by rfl) ⟨22104, by rfl⟩ : syracuseStep 235781 = 44209) (by norm_num)
theorem B170261 : Blo 111784 170261 := bbase (se 6 (by rfl) ⟨3990, by rfl⟩ : syracuseStep 170261 = 7981) (by norm_num)
theorem B170285 : Blo 111784 170285 := bbase (se 3 (by rfl) ⟨31928, by rfl⟩ : syracuseStep 170285 = 63857) (by norm_num)
theorem B203069 : Blo 111784 203069 := bbase (se 3 (by rfl) ⟨38075, by rfl⟩ : syracuseStep 203069 = 76151) (by norm_num)
theorem B170309 : Blo 111784 170309 := bbase (se 4 (by rfl) ⟨15966, by rfl⟩ : syracuseStep 170309 = 31933) (by norm_num)
theorem B170333 : Blo 111784 170333 := bbase (se 3 (by rfl) ⟨31937, by rfl⟩ : syracuseStep 170333 = 63875) (by norm_num)
theorem B137585 : Blo 111784 137585 := bbase (se 2 (by rfl) ⟨51594, by rfl⟩ : syracuseStep 137585 = 103189) (by norm_num)
theorem B170357 : Blo 111784 170357 := bbase (se 5 (by rfl) ⟨7985, by rfl⟩ : syracuseStep 170357 = 15971) (by norm_num)
theorem B170381 : Blo 111784 170381 := bbase (se 3 (by rfl) ⟨31946, by rfl⟩ : syracuseStep 170381 = 63893) (by norm_num)
theorem B170405 : Blo 111784 170405 := bbase (se 4 (by rfl) ⟨15975, by rfl⟩ : syracuseStep 170405 = 31951) (by norm_num)
theorem B170429 : Blo 111784 170429 := bbase (se 3 (by rfl) ⟨31955, by rfl⟩ : syracuseStep 170429 = 63911) (by norm_num)
theorem B170453 : Blo 111784 170453 := bbase (se 7 (by rfl) ⟨1997, by rfl⟩ : syracuseStep 170453 = 3995) (by norm_num)
theorem B170477 : Blo 111784 170477 := bbase (se 3 (by rfl) ⟨31964, by rfl⟩ : syracuseStep 170477 = 63929) (by norm_num)
theorem B170501 : Blo 111784 170501 := bbase (se 4 (by rfl) ⟨15984, by rfl⟩ : syracuseStep 170501 = 31969) (by norm_num)
theorem B367109 : Blo 111784 367109 := bbase (se 4 (by rfl) ⟨34416, by rfl⟩ : syracuseStep 367109 = 68833) (by norm_num)
theorem B203285 : Blo 111784 203285 := bbase (se 6 (by rfl) ⟨4764, by rfl⟩ : syracuseStep 203285 = 9529) (by norm_num)
theorem B432661 : Blo 111784 432661 := bbase (se 6 (by rfl) ⟨10140, by rfl⟩ : syracuseStep 432661 = 20281) (by norm_num)
theorem B170525 : Blo 111784 170525 := bbase (se 3 (by rfl) ⟨31973, by rfl⟩ : syracuseStep 170525 = 63947) (by norm_num)
theorem B170549 : Blo 111784 170549 := bbase (se 5 (by rfl) ⟨7994, by rfl⟩ : syracuseStep 170549 = 15989) (by norm_num)
theorem B170573 : Blo 111784 170573 := bbase (se 3 (by rfl) ⟨31982, by rfl⟩ : syracuseStep 170573 = 63965) (by norm_num)
theorem B203357 : Blo 111784 203357 := bbase (se 3 (by rfl) ⟨38129, by rfl⟩ : syracuseStep 203357 = 76259) (by norm_num)
theorem B170597 : Blo 111784 170597 := bbase (se 4 (by rfl) ⟨15993, by rfl⟩ : syracuseStep 170597 = 31987) (by norm_num)
theorem B170621 : Blo 111784 170621 := bbase (se 3 (by rfl) ⟨31991, by rfl⟩ : syracuseStep 170621 = 63983) (by norm_num)
theorem B170645 : Blo 111784 170645 := bbase (se 6 (by rfl) ⟨3999, by rfl⟩ : syracuseStep 170645 = 7999) (by norm_num)
theorem B170669 : Blo 111784 170669 := bbase (se 3 (by rfl) ⟨32000, by rfl⟩ : syracuseStep 170669 = 64001) (by norm_num)
theorem B170693 : Blo 111784 170693 := bbase (se 4 (by rfl) ⟨16002, by rfl⟩ : syracuseStep 170693 = 32005) (by norm_num)
theorem B170717 : Blo 111784 170717 := bbase (se 3 (by rfl) ⟨32009, by rfl⟩ : syracuseStep 170717 = 64019) (by norm_num)
theorem B269045 : Blo 111784 269045 := bbase (se 5 (by rfl) ⟨12611, by rfl⟩ : syracuseStep 269045 = 25223) (by norm_num)
theorem B170741 : Blo 111784 170741 := bbase (se 5 (by rfl) ⟨8003, by rfl⟩ : syracuseStep 170741 = 16007) (by norm_num)
theorem B170765 : Blo 111784 170765 := bbase (se 3 (by rfl) ⟨32018, by rfl⟩ : syracuseStep 170765 = 64037) (by norm_num)
theorem B170789 : Blo 111784 170789 := bbase (se 4 (by rfl) ⟨16011, by rfl⟩ : syracuseStep 170789 = 32023) (by norm_num)
theorem B727861 : Blo 111784 727861 := bbase (se 5 (by rfl) ⟨34118, by rfl⟩ : syracuseStep 727861 = 68237) (by norm_num)
theorem B170813 : Blo 111784 170813 := bbase (se 3 (by rfl) ⟨32027, by rfl⟩ : syracuseStep 170813 = 64055) (by norm_num)
theorem B432965 : Blo 111784 432965 := bbase (se 4 (by rfl) ⟨40590, by rfl⟩ : syracuseStep 432965 = 81181) (by norm_num)
theorem B170837 : Blo 111784 170837 := bbase (se 9 (by rfl) ⟨500, by rfl⟩ : syracuseStep 170837 = 1001) (by norm_num)
theorem B170861 : Blo 111784 170861 := bbase (se 3 (by rfl) ⟨32036, by rfl⟩ : syracuseStep 170861 = 64073) (by norm_num)
theorem B170885 : Blo 111784 170885 := bbase (se 4 (by rfl) ⟨16020, by rfl⟩ : syracuseStep 170885 = 32041) (by norm_num)
theorem B1579925 : Blo 111784 1579925 := bbase (se 6 (by rfl) ⟨37029, by rfl⟩ : syracuseStep 1579925 = 74059) (by norm_num)
theorem B170909 : Blo 111784 170909 := bbase (se 3 (by rfl) ⟨32045, by rfl⟩ : syracuseStep 170909 = 64091) (by norm_num)
theorem B170933 : Blo 111784 170933 := bbase (se 5 (by rfl) ⟨8012, by rfl⟩ : syracuseStep 170933 = 16025) (by norm_num)
theorem B203725 : Blo 111784 203725 := bbase (se 3 (by rfl) ⟨38198, by rfl⟩ : syracuseStep 203725 = 76397) (by norm_num)
theorem B170957 : Blo 111784 170957 := bbase (se 3 (by rfl) ⟨32054, by rfl⟩ : syracuseStep 170957 = 64109) (by norm_num)
theorem B170981 : Blo 111784 170981 := bbase (se 4 (by rfl) ⟨16029, by rfl⟩ : syracuseStep 170981 = 32059) (by norm_num)
theorem B171005 : Blo 111784 171005 := bbase (se 3 (by rfl) ⟨32063, by rfl⟩ : syracuseStep 171005 = 64127) (by norm_num)
theorem B171029 : Blo 111784 171029 := bbase (se 6 (by rfl) ⟨4008, by rfl⟩ : syracuseStep 171029 = 8017) (by norm_num)
theorem B138277 : Blo 111784 138277 := bbase (se 4 (by rfl) ⟨12963, by rfl⟩ : syracuseStep 138277 = 25927) (by norm_num)
theorem B138281 : Blo 111784 138281 := bbase (se 2 (by rfl) ⟨51855, by rfl⟩ : syracuseStep 138281 = 103711) (by norm_num)
theorem B171053 : Blo 111784 171053 := bbase (se 3 (by rfl) ⟨32072, by rfl⟩ : syracuseStep 171053 = 64145) (by norm_num)
theorem B171077 : Blo 111784 171077 := bbase (se 4 (by rfl) ⟨16038, by rfl⟩ : syracuseStep 171077 = 32077) (by norm_num)
theorem B171101 : Blo 111784 171101 := bbase (se 3 (by rfl) ⟨32081, by rfl⟩ : syracuseStep 171101 = 64163) (by norm_num)
theorem B466037 : Blo 111784 466037 := bbase (se 5 (by rfl) ⟨21845, by rfl⟩ : syracuseStep 466037 = 43691) (by norm_num)
theorem B171125 : Blo 111784 171125 := bbase (se 5 (by rfl) ⟨8021, by rfl⟩ : syracuseStep 171125 = 16043) (by norm_num)
theorem B171149 : Blo 111784 171149 := bbase (se 3 (by rfl) ⟨32090, by rfl⟩ : syracuseStep 171149 = 64181) (by norm_num)
theorem B171173 : Blo 111784 171173 := bbase (se 4 (by rfl) ⟨16047, by rfl⟩ : syracuseStep 171173 = 32095) (by norm_num)
theorem B171197 : Blo 111784 171197 := bbase (se 3 (by rfl) ⟨32099, by rfl⟩ : syracuseStep 171197 = 64199) (by norm_num)
theorem B171221 : Blo 111784 171221 := bbase (se 7 (by rfl) ⟨2006, by rfl⟩ : syracuseStep 171221 = 4013) (by norm_num)
theorem B171245 : Blo 111784 171245 := bbase (se 3 (by rfl) ⟨32108, by rfl⟩ : syracuseStep 171245 = 64217) (by norm_num)
theorem B466165 : Blo 111784 466165 := bbase (se 5 (by rfl) ⟨21851, by rfl⟩ : syracuseStep 466165 = 43703) (by norm_num)
theorem B171269 : Blo 111784 171269 := bbase (se 4 (by rfl) ⟨16056, by rfl⟩ : syracuseStep 171269 = 32113) (by norm_num)
theorem B695573 : Blo 111784 695573 := bbase (se 6 (by rfl) ⟨16302, by rfl⟩ : syracuseStep 695573 = 32605) (by norm_num)
theorem B171293 : Blo 111784 171293 := bbase (se 3 (by rfl) ⟨32117, by rfl⟩ : syracuseStep 171293 = 64235) (by norm_num)
theorem B171317 : Blo 111784 171317 := bbase (se 5 (by rfl) ⟨8030, by rfl⟩ : syracuseStep 171317 = 16061) (by norm_num)
theorem B171341 : Blo 111784 171341 := bbase (se 3 (by rfl) ⟨32126, by rfl⟩ : syracuseStep 171341 = 64253) (by norm_num)
theorem B171365 : Blo 111784 171365 := bbase (se 4 (by rfl) ⟨16065, by rfl⟩ : syracuseStep 171365 = 32131) (by norm_num)
theorem B171389 : Blo 111784 171389 := bbase (se 3 (by rfl) ⟨32135, by rfl⟩ : syracuseStep 171389 = 64271) (by norm_num)
theorem B171413 : Blo 111784 171413 := bbase (se 6 (by rfl) ⟨4017, by rfl⟩ : syracuseStep 171413 = 8035) (by norm_num)
theorem B171437 : Blo 111784 171437 := bbase (se 3 (by rfl) ⟨32144, by rfl⟩ : syracuseStep 171437 = 64289) (by norm_num)
theorem B171461 : Blo 111784 171461 := bbase (se 4 (by rfl) ⟨16074, by rfl⟩ : syracuseStep 171461 = 32149) (by norm_num)
theorem B171485 : Blo 111784 171485 := bbase (se 3 (by rfl) ⟨32153, by rfl⟩ : syracuseStep 171485 = 64307) (by norm_num)
theorem B171509 : Blo 111784 171509 := bbase (se 5 (by rfl) ⟨8039, by rfl⟩ : syracuseStep 171509 = 16079) (by norm_num)
theorem B171533 : Blo 111784 171533 := bbase (se 3 (by rfl) ⟨32162, by rfl⟩ : syracuseStep 171533 = 64325) (by norm_num)
theorem B138781 : Blo 111784 138781 := bbase (se 3 (by rfl) ⟨26021, by rfl⟩ : syracuseStep 138781 = 52043) (by norm_num)
theorem B171557 : Blo 111784 171557 := bbase (se 4 (by rfl) ⟨16083, by rfl⟩ : syracuseStep 171557 = 32167) (by norm_num)
theorem B171581 : Blo 111784 171581 := bbase (se 3 (by rfl) ⟨32171, by rfl⟩ : syracuseStep 171581 = 64343) (by norm_num)
theorem B204365 : Blo 111784 204365 := bbase (se 3 (by rfl) ⟨38318, by rfl⟩ : syracuseStep 204365 = 76637) (by norm_num)
theorem B859733 : Blo 111784 859733 := bbase (se 8 (by rfl) ⟨5037, by rfl⟩ : syracuseStep 859733 = 10075) (by norm_num)
theorem B171605 : Blo 111784 171605 := bbase (se 8 (by rfl) ⟨1005, by rfl⟩ : syracuseStep 171605 = 2011) (by norm_num)
theorem B171629 : Blo 111784 171629 := bbase (se 3 (by rfl) ⟨32180, by rfl⟩ : syracuseStep 171629 = 64361) (by norm_num)
theorem B171653 : Blo 111784 171653 := bbase (se 4 (by rfl) ⟨16092, by rfl⟩ : syracuseStep 171653 = 32185) (by norm_num)
theorem B171677 : Blo 111784 171677 := bbase (se 3 (by rfl) ⟨32189, by rfl⟩ : syracuseStep 171677 = 64379) (by norm_num)
theorem B171701 : Blo 111784 171701 := bbase (se 5 (by rfl) ⟨8048, by rfl⟩ : syracuseStep 171701 = 16097) (by norm_num)
theorem B171725 : Blo 111784 171725 := bbase (se 3 (by rfl) ⟨32198, by rfl⟩ : syracuseStep 171725 = 64397) (by norm_num)
theorem B171749 : Blo 111784 171749 := bbase (se 4 (by rfl) ⟨16101, by rfl⟩ : syracuseStep 171749 = 32203) (by norm_num)
theorem B171773 : Blo 111784 171773 := bbase (se 3 (by rfl) ⟨32207, by rfl⟩ : syracuseStep 171773 = 64415) (by norm_num)
theorem B171797 : Blo 111784 171797 := bbase (se 6 (by rfl) ⟨4026, by rfl⟩ : syracuseStep 171797 = 8053) (by norm_num)
theorem B171821 : Blo 111784 171821 := bbase (se 3 (by rfl) ⟨32216, by rfl⟩ : syracuseStep 171821 = 64433) (by norm_num)
theorem B171845 : Blo 111784 171845 := bbase (se 4 (by rfl) ⟨16110, by rfl⟩ : syracuseStep 171845 = 32221) (by norm_num)
theorem B171869 : Blo 111784 171869 := bbase (se 3 (by rfl) ⟨32225, by rfl⟩ : syracuseStep 171869 = 64451) (by norm_num)
theorem B171893 : Blo 111784 171893 := bbase (se 5 (by rfl) ⟨8057, by rfl⟩ : syracuseStep 171893 = 16115) (by norm_num)
theorem B171917 : Blo 111784 171917 := bbase (se 3 (by rfl) ⟨32234, by rfl⟩ : syracuseStep 171917 = 64469) (by norm_num)
theorem B171941 : Blo 111784 171941 := bbase (se 4 (by rfl) ⟨16119, by rfl⟩ : syracuseStep 171941 = 32239) (by norm_num)
theorem B171965 : Blo 111784 171965 := bbase (se 3 (by rfl) ⟨32243, by rfl⟩ : syracuseStep 171965 = 64487) (by norm_num)
theorem B171989 : Blo 111784 171989 := bbase (se 7 (by rfl) ⟨2015, by rfl⟩ : syracuseStep 171989 = 4031) (by norm_num)
theorem B172013 : Blo 111784 172013 := bbase (se 3 (by rfl) ⟨32252, by rfl⟩ : syracuseStep 172013 = 64505) (by norm_num)
theorem B172037 : Blo 111784 172037 := bbase (se 4 (by rfl) ⟨16128, by rfl⟩ : syracuseStep 172037 = 32257) (by norm_num)
theorem B172061 : Blo 111784 172061 := bbase (se 3 (by rfl) ⟨32261, by rfl⟩ : syracuseStep 172061 = 64523) (by norm_num)
theorem B172085 : Blo 111784 172085 := bbase (se 5 (by rfl) ⟨8066, by rfl⟩ : syracuseStep 172085 = 16133) (by norm_num)
theorem B172109 : Blo 111784 172109 := bbase (se 3 (by rfl) ⟨32270, by rfl⟩ : syracuseStep 172109 = 64541) (by norm_num)
theorem B172133 : Blo 111784 172133 := bbase (se 4 (by rfl) ⟨16137, by rfl⟩ : syracuseStep 172133 = 32275) (by norm_num)
theorem B172157 : Blo 111784 172157 := bbase (se 3 (by rfl) ⟨32279, by rfl⟩ : syracuseStep 172157 = 64559) (by norm_num)
theorem B172181 : Blo 111784 172181 := bbase (se 6 (by rfl) ⟨4035, by rfl⟩ : syracuseStep 172181 = 8071) (by norm_num)
theorem B172205 : Blo 111784 172205 := bbase (se 3 (by rfl) ⟨32288, by rfl⟩ : syracuseStep 172205 = 64577) (by norm_num)
theorem B172229 : Blo 111784 172229 := bbase (se 4 (by rfl) ⟨16146, by rfl⟩ : syracuseStep 172229 = 32293) (by norm_num)
theorem B172253 : Blo 111784 172253 := bbase (se 3 (by rfl) ⟨32297, by rfl⟩ : syracuseStep 172253 = 64595) (by norm_num)
theorem B172277 : Blo 111784 172277 := bbase (se 5 (by rfl) ⟨8075, by rfl⟩ : syracuseStep 172277 = 16151) (by norm_num)
theorem B172301 : Blo 111784 172301 := bbase (se 3 (by rfl) ⟨32306, by rfl⟩ : syracuseStep 172301 = 64613) (by norm_num)
theorem B172325 : Blo 111784 172325 := bbase (se 4 (by rfl) ⟨16155, by rfl⟩ : syracuseStep 172325 = 32311) (by norm_num)
theorem B205109 : Blo 111784 205109 := bbase (se 5 (by rfl) ⟨9614, by rfl⟩ : syracuseStep 205109 = 19229) (by norm_num)
theorem B172349 : Blo 111784 172349 := bbase (se 3 (by rfl) ⟨32315, by rfl⟩ : syracuseStep 172349 = 64631) (by norm_num)
theorem B172373 : Blo 111784 172373 := bbase (se 10 (by rfl) ⟨252, by rfl⟩ : syracuseStep 172373 = 505) (by norm_num)
theorem B368981 : Blo 111784 368981 := bbase (se 10 (by rfl) ⟨540, by rfl⟩ : syracuseStep 368981 = 1081) (by norm_num)
theorem B172397 : Blo 111784 172397 := bbase (se 3 (by rfl) ⟨32324, by rfl⟩ : syracuseStep 172397 = 64649) (by norm_num)
theorem B172421 : Blo 111784 172421 := bbase (se 4 (by rfl) ⟨16164, by rfl⟩ : syracuseStep 172421 = 32329) (by norm_num)
theorem B172445 : Blo 111784 172445 := bbase (se 3 (by rfl) ⟨32333, by rfl⟩ : syracuseStep 172445 = 64667) (by norm_num)
theorem B172469 : Blo 111784 172469 := bbase (se 5 (by rfl) ⟨8084, by rfl⟩ : syracuseStep 172469 = 16169) (by norm_num)
theorem B172493 : Blo 111784 172493 := bbase (se 3 (by rfl) ⟨32342, by rfl⟩ : syracuseStep 172493 = 64685) (by norm_num)
theorem B172517 : Blo 111784 172517 := bbase (se 4 (by rfl) ⟨16173, by rfl⟩ : syracuseStep 172517 = 32347) (by norm_num)
theorem B172541 : Blo 111784 172541 := bbase (se 3 (by rfl) ⟨32351, by rfl⟩ : syracuseStep 172541 = 64703) (by norm_num)
theorem B172565 : Blo 111784 172565 := bbase (se 6 (by rfl) ⟨4044, by rfl⟩ : syracuseStep 172565 = 8089) (by norm_num)
theorem B172589 : Blo 111784 172589 := bbase (se 3 (by rfl) ⟨32360, by rfl⟩ : syracuseStep 172589 = 64721) (by norm_num)
theorem B172613 : Blo 111784 172613 := bbase (se 4 (by rfl) ⟨16182, by rfl⟩ : syracuseStep 172613 = 32365) (by norm_num)
theorem B172637 : Blo 111784 172637 := bbase (se 3 (by rfl) ⟨32369, by rfl⟩ : syracuseStep 172637 = 64739) (by norm_num)
theorem B270949 : Blo 111784 270949 := bbase (se 4 (by rfl) ⟨25401, by rfl⟩ : syracuseStep 270949 = 50803) (by norm_num)
theorem B172661 : Blo 111784 172661 := bbase (se 5 (by rfl) ⟨8093, by rfl⟩ : syracuseStep 172661 = 16187) (by norm_num)
theorem B172685 : Blo 111784 172685 := bbase (se 3 (by rfl) ⟨32378, by rfl⟩ : syracuseStep 172685 = 64757) (by norm_num)
theorem B172709 : Blo 111784 172709 := bbase (se 4 (by rfl) ⟨16191, by rfl⟩ : syracuseStep 172709 = 32383) (by norm_num)
theorem B172733 : Blo 111784 172733 := bbase (se 3 (by rfl) ⟨32387, by rfl⟩ : syracuseStep 172733 = 64775) (by norm_num)
theorem B172757 : Blo 111784 172757 := bbase (se 7 (by rfl) ⟨2024, by rfl⟩ : syracuseStep 172757 = 4049) (by norm_num)
theorem B172781 : Blo 111784 172781 := bbase (se 3 (by rfl) ⟨32396, by rfl⟩ : syracuseStep 172781 = 64793) (by norm_num)
theorem B172805 : Blo 111784 172805 := bbase (se 4 (by rfl) ⟨16200, by rfl⟩ : syracuseStep 172805 = 32401) (by norm_num)
theorem B795413 : Blo 111784 795413 := bbase (se 6 (by rfl) ⟨18642, by rfl⟩ : syracuseStep 795413 = 37285) (by norm_num)
theorem B172829 : Blo 111784 172829 := bbase (se 3 (by rfl) ⟨32405, by rfl⟩ : syracuseStep 172829 = 64811) (by norm_num)
theorem B172853 : Blo 111784 172853 := bbase (se 5 (by rfl) ⟨8102, by rfl⟩ : syracuseStep 172853 = 16205) (by norm_num)
theorem B271181 : Blo 111784 271181 := bbase (se 3 (by rfl) ⟨50846, by rfl⟩ : syracuseStep 271181 = 101693) (by norm_num)
theorem B172877 : Blo 111784 172877 := bbase (se 3 (by rfl) ⟨32414, by rfl⟩ : syracuseStep 172877 = 64829) (by norm_num)
theorem B172901 : Blo 111784 172901 := bbase (se 4 (by rfl) ⟨16209, by rfl⟩ : syracuseStep 172901 = 32419) (by norm_num)
theorem B172925 : Blo 111784 172925 := bbase (se 3 (by rfl) ⟨32423, by rfl⟩ : syracuseStep 172925 = 64847) (by norm_num)
theorem B435077 : Blo 111784 435077 := bbase (se 4 (by rfl) ⟨40788, by rfl⟩ : syracuseStep 435077 = 81577) (by norm_num)
theorem B172949 : Blo 111784 172949 := bbase (se 6 (by rfl) ⟨4053, by rfl⟩ : syracuseStep 172949 = 8107) (by norm_num)
theorem B172973 : Blo 111784 172973 := bbase (se 3 (by rfl) ⟨32432, by rfl⟩ : syracuseStep 172973 = 64865) (by norm_num)
theorem B172981 : Blo 111784 172981 := bbase (se 5 (by rfl) ⟨8108, by rfl⟩ : syracuseStep 172981 = 16217) (by norm_num)
theorem B172997 : Blo 111784 172997 := bbase (se 4 (by rfl) ⟨16218, by rfl⟩ : syracuseStep 172997 = 32437) (by norm_num)
theorem B271325 : Blo 111784 271325 := bbase (se 3 (by rfl) ⟨50873, by rfl⟩ : syracuseStep 271325 = 101747) (by norm_num)
theorem B173021 : Blo 111784 173021 := bbase (se 3 (by rfl) ⟨32441, by rfl⟩ : syracuseStep 173021 = 64883) (by norm_num)
theorem B173045 : Blo 111784 173045 := bbase (se 5 (by rfl) ⟨8111, by rfl⟩ : syracuseStep 173045 = 16223) (by norm_num)
theorem B173069 : Blo 111784 173069 := bbase (se 3 (by rfl) ⟨32450, by rfl⟩ : syracuseStep 173069 = 64901) (by norm_num)
theorem B173093 : Blo 111784 173093 := bbase (se 4 (by rfl) ⟨16227, by rfl⟩ : syracuseStep 173093 = 32455) (by norm_num)
theorem B173117 : Blo 111784 173117 := bbase (se 3 (by rfl) ⟨32459, by rfl⟩ : syracuseStep 173117 = 64919) (by norm_num)
theorem B173141 : Blo 111784 173141 := bbase (se 8 (by rfl) ⟨1014, by rfl⟩ : syracuseStep 173141 = 2029) (by norm_num)
theorem B173165 : Blo 111784 173165 := bbase (se 3 (by rfl) ⟨32468, by rfl⟩ : syracuseStep 173165 = 64937) (by norm_num)
theorem B173189 : Blo 111784 173189 := bbase (se 4 (by rfl) ⟨16236, by rfl⟩ : syracuseStep 173189 = 32473) (by norm_num)
theorem B173213 : Blo 111784 173213 := bbase (se 3 (by rfl) ⟨32477, by rfl⟩ : syracuseStep 173213 = 64955) (by norm_num)
theorem B435365 : Blo 111784 435365 := bbase (se 4 (by rfl) ⟨40815, by rfl⟩ : syracuseStep 435365 = 81631) (by norm_num)
theorem B173237 : Blo 111784 173237 := bbase (se 5 (by rfl) ⟨8120, by rfl⟩ : syracuseStep 173237 = 16241) (by norm_num)
theorem B271565 : Blo 111784 271565 := bbase (se 3 (by rfl) ⟨50918, by rfl⟩ : syracuseStep 271565 = 101837) (by norm_num)
theorem B173261 : Blo 111784 173261 := bbase (se 3 (by rfl) ⟨32486, by rfl⟩ : syracuseStep 173261 = 64973) (by norm_num)
theorem B173285 : Blo 111784 173285 := bbase (se 4 (by rfl) ⟨16245, by rfl⟩ : syracuseStep 173285 = 32491) (by norm_num)
theorem B173309 : Blo 111784 173309 := bbase (se 3 (by rfl) ⟨32495, by rfl⟩ : syracuseStep 173309 = 64991) (by norm_num)
theorem B173333 : Blo 111784 173333 := bbase (se 6 (by rfl) ⟨4062, by rfl⟩ : syracuseStep 173333 = 8125) (by norm_num)
theorem B173357 : Blo 111784 173357 := bbase (se 3 (by rfl) ⟨32504, by rfl⟩ : syracuseStep 173357 = 65009) (by norm_num)
theorem B173381 : Blo 111784 173381 := bbase (se 4 (by rfl) ⟨16254, by rfl⟩ : syracuseStep 173381 = 32509) (by norm_num)
theorem B173405 : Blo 111784 173405 := bbase (se 3 (by rfl) ⟨32513, by rfl⟩ : syracuseStep 173405 = 65027) (by norm_num)
theorem B173429 : Blo 111784 173429 := bbase (se 5 (by rfl) ⟨8129, by rfl⟩ : syracuseStep 173429 = 16259) (by norm_num)
theorem B173453 : Blo 111784 173453 := bbase (se 3 (by rfl) ⟨32522, by rfl⟩ : syracuseStep 173453 = 65045) (by norm_num)
theorem B173477 : Blo 111784 173477 := bbase (se 4 (by rfl) ⟨16263, by rfl⟩ : syracuseStep 173477 = 32527) (by norm_num)
theorem B173501 : Blo 111784 173501 := bbase (se 3 (by rfl) ⟨32531, by rfl⟩ : syracuseStep 173501 = 65063) (by norm_num)
theorem B959957 : Blo 111784 959957 := bbase (se 7 (by rfl) ⟨11249, by rfl⟩ : syracuseStep 959957 = 22499) (by norm_num)
theorem B173525 : Blo 111784 173525 := bbase (se 7 (by rfl) ⟨2033, by rfl⟩ : syracuseStep 173525 = 4067) (by norm_num)
theorem B173549 : Blo 111784 173549 := bbase (se 3 (by rfl) ⟨32540, by rfl⟩ : syracuseStep 173549 = 65081) (by norm_num)
theorem B173573 : Blo 111784 173573 := bbase (se 4 (by rfl) ⟨16272, by rfl⟩ : syracuseStep 173573 = 32545) (by norm_num)
theorem B402965 : Blo 111784 402965 := bbase (se 6 (by rfl) ⟨9444, by rfl⟩ : syracuseStep 402965 = 18889) (by norm_num)
theorem B173597 : Blo 111784 173597 := bbase (se 3 (by rfl) ⟨32549, by rfl⟩ : syracuseStep 173597 = 65099) (by norm_num)
theorem B566837 : Blo 111784 566837 := bbase (se 5 (by rfl) ⟨26570, by rfl⟩ : syracuseStep 566837 = 53141) (by norm_num)
theorem B173621 : Blo 111784 173621 := bbase (se 5 (by rfl) ⟨8138, by rfl⟩ : syracuseStep 173621 = 16277) (by norm_num)
theorem B173645 : Blo 111784 173645 := bbase (se 3 (by rfl) ⟨32558, by rfl⟩ : syracuseStep 173645 = 65117) (by norm_num)
theorem B173669 : Blo 111784 173669 := bbase (se 4 (by rfl) ⟨16281, by rfl⟩ : syracuseStep 173669 = 32563) (by norm_num)
theorem B468629 : Blo 111784 468629 := bbase (se 6 (by rfl) ⟨10983, by rfl⟩ : syracuseStep 468629 = 21967) (by norm_num)
theorem B272333 : Blo 111784 272333 := bbase (se 3 (by rfl) ⟨51062, by rfl⟩ : syracuseStep 272333 = 102125) (by norm_num)
theorem B141517 : Blo 111784 141517 := bbase (se 3 (by rfl) ⟨26534, by rfl⟩ : syracuseStep 141517 = 53069) (by norm_num)
theorem B436549 : Blo 111784 436549 := bbase (se 4 (by rfl) ⟨40926, by rfl⟩ : syracuseStep 436549 = 81853) (by norm_num)
theorem B141689 : Blo 111784 141689 := bbase (se 2 (by rfl) ⟨53133, by rfl⟩ : syracuseStep 141689 = 106267) (by norm_num)
theorem B141745 : Blo 111784 141745 := bbase (se 2 (by rfl) ⟨53154, by rfl⟩ : syracuseStep 141745 = 106309) (by norm_num)
theorem B141841 : Blo 111784 141841 := bbase (se 2 (by rfl) ⟨53190, by rfl⟩ : syracuseStep 141841 = 106381) (by norm_num)
theorem B240221 : Blo 111784 240221 := bbase (se 3 (by rfl) ⟨45041, by rfl⟩ : syracuseStep 240221 = 90083) (by norm_num)
theorem B436853 : Blo 111784 436853 := bbase (se 5 (by rfl) ⟨20477, by rfl⟩ : syracuseStep 436853 = 40955) (by norm_num)
theorem B404117 : Blo 111784 404117 := bbase (se 6 (by rfl) ⟨9471, by rfl⟩ : syracuseStep 404117 = 18943) (by norm_num)
theorem B305813 : Blo 111784 305813 := bbase (se 6 (by rfl) ⟨7167, by rfl⟩ : syracuseStep 305813 = 14335) (by norm_num)
theorem B142013 : Blo 111784 142013 := bbase (se 3 (by rfl) ⟨26627, by rfl⟩ : syracuseStep 142013 = 53255) (by norm_num)
theorem B731861 : Blo 111784 731861 := bbase (se 7 (by rfl) ⟨8576, by rfl⟩ : syracuseStep 731861 = 17153) (by norm_num)
theorem B240365 : Blo 111784 240365 := bbase (se 3 (by rfl) ⟨45068, by rfl⟩ : syracuseStep 240365 = 90137) (by norm_num)
theorem B142069 : Blo 111784 142069 := bbase (se 5 (by rfl) ⟨6659, by rfl⟩ : syracuseStep 142069 = 13319) (by norm_num)
theorem B568133 : Blo 111784 568133 := bbase (se 4 (by rfl) ⟨53262, by rfl⟩ : syracuseStep 568133 = 106525) (by norm_num)
theorem B142165 : Blo 111784 142165 := bbase (se 9 (by rfl) ⟨416, by rfl⟩ : syracuseStep 142165 = 833) (by norm_num)
theorem B175061 : Blo 111784 175061 := bbase (se 7 (by rfl) ⟨2051, by rfl⟩ : syracuseStep 175061 = 4103) (by norm_num)
theorem B142337 : Blo 111784 142337 := bbase (se 2 (by rfl) ⟨53376, by rfl⟩ : syracuseStep 142337 = 106753) (by norm_num)
theorem B142393 : Blo 111784 142393 := bbase (se 2 (by rfl) ⟨53397, by rfl⟩ : syracuseStep 142393 = 106795) (by norm_num)
theorem B240725 : Blo 111784 240725 := bbase (se 8 (by rfl) ⟨1410, by rfl⟩ : syracuseStep 240725 = 2821) (by norm_num)
theorem B207973 : Blo 111784 207973 := bbase (se 4 (by rfl) ⟨19497, by rfl⟩ : syracuseStep 207973 = 38995) (by norm_num)
theorem B208013 : Blo 111784 208013 := bbase (se 3 (by rfl) ⟨39002, by rfl⟩ : syracuseStep 208013 = 78005) (by norm_num)
theorem B142489 : Blo 111784 142489 := bbase (se 2 (by rfl) ⟨53433, by rfl⟩ : syracuseStep 142489 = 106867) (by norm_num)
theorem B273709 : Blo 111784 273709 := bbase (se 3 (by rfl) ⟨51320, by rfl⟩ : syracuseStep 273709 = 102641) (by norm_num)
theorem B142661 : Blo 111784 142661 := bbase (se 4 (by rfl) ⟨13374, by rfl⟩ : syracuseStep 142661 = 26749) (by norm_num)
theorem B142717 : Blo 111784 142717 := bbase (se 3 (by rfl) ⟨26759, by rfl⟩ : syracuseStep 142717 = 53519) (by norm_num)
theorem B142813 : Blo 111784 142813 := bbase (se 3 (by rfl) ⟨26777, by rfl⟩ : syracuseStep 142813 = 53555) (by norm_num)
theorem B142985 : Blo 111784 142985 := bbase (se 2 (by rfl) ⟨53619, by rfl⟩ : syracuseStep 142985 = 107239) (by norm_num)
theorem B143041 : Blo 111784 143041 := bbase (se 2 (by rfl) ⟨53640, by rfl⟩ : syracuseStep 143041 = 107281) (by norm_num)
theorem B143137 : Blo 111784 143137 := bbase (se 2 (by rfl) ⟨53676, by rfl⟩ : syracuseStep 143137 = 107353) (by norm_num)
theorem B2207573 : Blo 111784 2207573 := bbase (se 9 (by rfl) ⟨6467, by rfl⟩ : syracuseStep 2207573 = 12935) (by norm_num)
theorem B405445 : Blo 111784 405445 := bbase (se 4 (by rfl) ⟨38010, by rfl⟩ : syracuseStep 405445 = 76021) (by norm_num)
theorem B241613 : Blo 111784 241613 := bbase (se 3 (by rfl) ⟨45302, by rfl⟩ : syracuseStep 241613 = 90605) (by norm_num)
theorem B143309 : Blo 111784 143309 := bbase (se 3 (by rfl) ⟨26870, by rfl⟩ : syracuseStep 143309 = 53741) (by norm_num)
theorem B143365 : Blo 111784 143365 := bbase (se 4 (by rfl) ⟨13440, by rfl⟩ : syracuseStep 143365 = 26881) (by norm_num)
theorem B569429 : Blo 111784 569429 := bbase (se 8 (by rfl) ⟨3336, by rfl⟩ : syracuseStep 569429 = 6673) (by norm_num)
theorem B143461 : Blo 111784 143461 := bbase (se 4 (by rfl) ⟨13449, by rfl⟩ : syracuseStep 143461 = 26899) (by norm_num)
theorem B241861 : Blo 111784 241861 := bbase (se 4 (by rfl) ⟨22674, by rfl⟩ : syracuseStep 241861 = 45349) (by norm_num)
theorem B143633 : Blo 111784 143633 := bbase (se 2 (by rfl) ⟨53862, by rfl⟩ : syracuseStep 143633 = 107725) (by norm_num)
theorem B667925 : Blo 111784 667925 := bbase (se 6 (by rfl) ⟨15654, by rfl⟩ : syracuseStep 667925 = 31309) (by norm_num)
theorem B143689 : Blo 111784 143689 := bbase (se 2 (by rfl) ⟨53883, by rfl⟩ : syracuseStep 143689 = 107767) (by norm_num)
theorem B143785 : Blo 111784 143785 := bbase (se 2 (by rfl) ⟨53919, by rfl⟩ : syracuseStep 143785 = 107839) (by norm_num)
theorem B274909 : Blo 111784 274909 := bbase (se 3 (by rfl) ⟨51545, by rfl⟩ : syracuseStep 274909 = 103091) (by norm_num)
theorem B143957 : Blo 111784 143957 := bbase (se 8 (by rfl) ⟨843, by rfl⟩ : syracuseStep 143957 = 1687) (by norm_num)
theorem B144013 : Blo 111784 144013 := bbase (se 3 (by rfl) ⟨27002, by rfl⟩ : syracuseStep 144013 = 54005) (by norm_num)
theorem B438965 : Blo 111784 438965 := bbase (se 5 (by rfl) ⟨20576, by rfl⟩ : syracuseStep 438965 = 41153) (by norm_num)
theorem B242365 : Blo 111784 242365 := bbase (se 3 (by rfl) ⟨45443, by rfl⟩ : syracuseStep 242365 = 90887) (by norm_num)
theorem B144109 : Blo 111784 144109 := bbase (se 3 (by rfl) ⟨27020, by rfl⟩ : syracuseStep 144109 = 54041) (by norm_num)
theorem B1946389 : Blo 111784 1946389 := bbase (se 6 (by rfl) ⟨45618, by rfl⟩ : syracuseStep 1946389 = 91237) (by norm_num)
theorem B144281 : Blo 111784 144281 := bbase (se 2 (by rfl) ⟨54105, by rfl⟩ : syracuseStep 144281 = 108211) (by norm_num)
theorem B144337 : Blo 111784 144337 := bbase (se 2 (by rfl) ⟨54126, by rfl⟩ : syracuseStep 144337 = 108253) (by norm_num)
theorem B439253 : Blo 111784 439253 := bbase (se 7 (by rfl) ⟨5147, by rfl⟩ : syracuseStep 439253 = 10295) (by norm_num)
theorem B144433 : Blo 111784 144433 := bbase (se 2 (by rfl) ⟨54162, by rfl⟩ : syracuseStep 144433 = 108325) (by norm_num)
theorem B275525 : Blo 111784 275525 := bbase (se 4 (by rfl) ⟨25830, by rfl⟩ : syracuseStep 275525 = 51661) (by norm_num)
theorem B275581 : Blo 111784 275581 := bbase (se 3 (by rfl) ⟨51671, by rfl⟩ : syracuseStep 275581 = 103343) (by norm_num)
theorem B308357 : Blo 111784 308357 := bbase (se 4 (by rfl) ⟨28908, by rfl⟩ : syracuseStep 308357 = 57817) (by norm_num)
theorem B144605 : Blo 111784 144605 := bbase (se 3 (by rfl) ⟨27113, by rfl⟩ : syracuseStep 144605 = 54227) (by norm_num)
theorem B275717 : Blo 111784 275717 := bbase (se 4 (by rfl) ⟨25848, by rfl⟩ : syracuseStep 275717 = 51697) (by norm_num)
theorem B144661 : Blo 111784 144661 := bbase (se 6 (by rfl) ⟨3390, by rfl⟩ : syracuseStep 144661 = 6781) (by norm_num)
theorem B537941 : Blo 111784 537941 := bbase (se 13 (by rfl) ⟨98, by rfl⟩ : syracuseStep 537941 = 197) (by norm_num)
theorem B570725 : Blo 111784 570725 := bbase (se 4 (by rfl) ⟨53505, by rfl⟩ : syracuseStep 570725 = 107011) (by norm_num)
theorem B406885 : Blo 111784 406885 := bbase (se 4 (by rfl) ⟨38145, by rfl⟩ : syracuseStep 406885 = 76291) (by norm_num)
theorem B275813 : Blo 111784 275813 := bbase (se 4 (by rfl) ⟨25857, by rfl⟩ : syracuseStep 275813 = 51715) (by norm_num)
theorem B144757 : Blo 111784 144757 := bbase (se 5 (by rfl) ⟨6785, by rfl⟩ : syracuseStep 144757 = 13571) (by norm_num)
theorem B144929 : Blo 111784 144929 := bbase (se 2 (by rfl) ⟨54348, by rfl⟩ : syracuseStep 144929 = 108697) (by norm_num)
theorem B243253 : Blo 111784 243253 := bbase (se 5 (by rfl) ⟨11402, by rfl⟩ : syracuseStep 243253 = 22805) (by norm_num)
theorem B144985 : Blo 111784 144985 := bbase (se 2 (by rfl) ⟨54369, by rfl⟩ : syracuseStep 144985 = 108739) (by norm_num)
theorem B145081 : Blo 111784 145081 := bbase (se 2 (by rfl) ⟨54405, by rfl⟩ : syracuseStep 145081 = 108811) (by norm_num)
theorem B145253 : Blo 111784 145253 := bbase (se 4 (by rfl) ⟨13617, by rfl⟩ : syracuseStep 145253 = 27235) (by norm_num)
theorem B145297 : Blo 111784 145297 := bbase (se 2 (by rfl) ⟨54486, by rfl⟩ : syracuseStep 145297 = 108973) (by norm_num)
theorem B145309 : Blo 111784 145309 := bbase (se 3 (by rfl) ⟨27245, by rfl⟩ : syracuseStep 145309 = 54491) (by norm_num)
theorem B145405 : Blo 111784 145405 := bbase (se 3 (by rfl) ⟨27263, by rfl⟩ : syracuseStep 145405 = 54527) (by norm_num)
theorem B276517 : Blo 111784 276517 := bbase (se 4 (by rfl) ⟨25923, by rfl⟩ : syracuseStep 276517 = 51847) (by norm_num)
theorem B243749 : Blo 111784 243749 := bbase (se 4 (by rfl) ⟨22851, by rfl⟩ : syracuseStep 243749 = 45703) (by norm_num)
theorem B145577 : Blo 111784 145577 := bbase (se 2 (by rfl) ⟨54591, by rfl⟩ : syracuseStep 145577 = 109183) (by norm_num)
theorem B145633 : Blo 111784 145633 := bbase (se 2 (by rfl) ⟨54612, by rfl⟩ : syracuseStep 145633 = 109225) (by norm_num)
theorem B178453 : Blo 111784 178453 := bbase (se 6 (by rfl) ⟨4182, by rfl⟩ : syracuseStep 178453 = 8365) (by norm_num)
theorem B145729 : Blo 111784 145729 := bbase (se 2 (by rfl) ⟨54648, by rfl⟩ : syracuseStep 145729 = 109297) (by norm_num)
theorem B145901 : Blo 111784 145901 := bbase (se 3 (by rfl) ⟨27356, by rfl⟩ : syracuseStep 145901 = 54713) (by norm_num)
theorem B145957 : Blo 111784 145957 := bbase (se 4 (by rfl) ⟨13683, by rfl⟩ : syracuseStep 145957 = 27367) (by norm_num)
theorem B572021 : Blo 111784 572021 := bbase (se 5 (by rfl) ⟨26813, by rfl⟩ : syracuseStep 572021 = 53627) (by norm_num)
theorem B146053 : Blo 111784 146053 := bbase (se 4 (by rfl) ⟨13692, by rfl⟩ : syracuseStep 146053 = 27385) (by norm_num)
theorem B146225 : Blo 111784 146225 := bbase (se 2 (by rfl) ⟨54834, by rfl⟩ : syracuseStep 146225 = 109669) (by norm_num)
theorem B310085 : Blo 111784 310085 := bbase (se 4 (by rfl) ⟨29070, by rfl⟩ : syracuseStep 310085 = 58141) (by norm_num)
theorem B146281 : Blo 111784 146281 := bbase (se 2 (by rfl) ⟨54855, by rfl⟩ : syracuseStep 146281 = 109711) (by norm_num)
theorem B244637 : Blo 111784 244637 := bbase (se 3 (by rfl) ⟨45869, by rfl⟩ : syracuseStep 244637 = 91739) (by norm_num)
theorem B113593 : Blo 111784 113593 := bbase (se 2 (by rfl) ⟨42597, by rfl⟩ : syracuseStep 113593 = 85195) (by norm_num)
theorem B146377 : Blo 111784 146377 := bbase (se 2 (by rfl) ⟨54891, by rfl⟩ : syracuseStep 146377 = 109783) (by norm_num)
theorem B277453 : Blo 111784 277453 := bbase (se 3 (by rfl) ⟨52022, by rfl⟩ : syracuseStep 277453 = 104045) (by norm_num)
theorem B244757 : Blo 111784 244757 := bbase (se 6 (by rfl) ⟨5736, by rfl⟩ : syracuseStep 244757 = 11473) (by norm_num)
theorem B867509 : Blo 111784 867509 := bbase (se 5 (by rfl) ⟨40664, by rfl⟩ : syracuseStep 867509 = 81329) (by norm_num)
theorem B179653 : Blo 111784 179653 := bbase (se 4 (by rfl) ⟨16842, by rfl⟩ : syracuseStep 179653 = 33685) (by norm_num)
theorem B212557 : Blo 111784 212557 := bbase (se 3 (by rfl) ⟨39854, by rfl⟩ : syracuseStep 212557 = 79709) (by norm_num)
theorem B245389 : Blo 111784 245389 := bbase (se 3 (by rfl) ⟨46010, by rfl⟩ : syracuseStep 245389 = 92021) (by norm_num)
theorem B245413 : Blo 111784 245413 := bbase (se 4 (by rfl) ⟨23007, by rfl⟩ : syracuseStep 245413 = 46015) (by norm_num)
theorem B212701 : Blo 111784 212701 := bbase (se 3 (by rfl) ⟨39881, by rfl⟩ : syracuseStep 212701 = 79763) (by norm_num)
theorem B606005 : Blo 111784 606005 := bbase (se 5 (by rfl) ⟨28406, by rfl⟩ : syracuseStep 606005 = 56813) (by norm_num)
theorem B147253 : Blo 111784 147253 := bbase (se 5 (by rfl) ⟨6902, by rfl⟩ : syracuseStep 147253 = 13805) (by norm_num)
theorem B212861 : Blo 111784 212861 := bbase (se 3 (by rfl) ⟨39911, by rfl⟩ : syracuseStep 212861 = 79823) (by norm_num)
theorem B573317 : Blo 111784 573317 := bbase (se 4 (by rfl) ⟨53748, by rfl⟩ : syracuseStep 573317 = 107497) (by norm_num)
theorem B213005 : Blo 111784 213005 := bbase (se 3 (by rfl) ⟨39938, by rfl⟩ : syracuseStep 213005 = 79877) (by norm_num)
theorem B180325 : Blo 111784 180325 := bbase (se 4 (by rfl) ⟨16905, by rfl⟩ : syracuseStep 180325 = 33811) (by norm_num)
theorem B213293 : Blo 111784 213293 := bbase (se 3 (by rfl) ⟨39992, by rfl⟩ : syracuseStep 213293 = 79985) (by norm_num)
theorem B115021 : Blo 111784 115021 := bbase (se 3 (by rfl) ⟨21566, by rfl⟩ : syracuseStep 115021 = 43133) (by norm_num)
theorem B213445 : Blo 111784 213445 := bbase (se 4 (by rfl) ⟨20010, by rfl⟩ : syracuseStep 213445 = 40021) (by norm_num)
theorem B246277 : Blo 111784 246277 := bbase (se 4 (by rfl) ⟨23088, by rfl⟩ : syracuseStep 246277 = 46177) (by norm_num)
theorem B737909 : Blo 111784 737909 := bbase (se 5 (by rfl) ⟨34589, by rfl⟩ : syracuseStep 737909 = 69179) (by norm_num)
theorem B246397 : Blo 111784 246397 := bbase (se 3 (by rfl) ⟨46199, by rfl⟩ : syracuseStep 246397 = 92399) (by norm_num)
theorem B115345 : Blo 111784 115345 := bbase (se 2 (by rfl) ⟨43254, by rfl⟩ : syracuseStep 115345 = 86509) (by norm_num)
theorem B213749 : Blo 111784 213749 := bbase (se 5 (by rfl) ⟨10019, by rfl⟩ : syracuseStep 213749 = 20039) (by norm_num)
theorem B377621 : Blo 111784 377621 := bbase (se 6 (by rfl) ⟨8850, by rfl⟩ : syracuseStep 377621 = 17701) (by norm_num)
theorem B246653 : Blo 111784 246653 := bbase (se 3 (by rfl) ⟨46247, by rfl⟩ : syracuseStep 246653 = 92495) (by norm_num)
theorem B115669 : Blo 111784 115669 := bbase (se 7 (by rfl) ⟨1355, by rfl⟩ : syracuseStep 115669 = 2711) (by norm_num)
theorem B181325 : Blo 111784 181325 := bbase (se 3 (by rfl) ⟨33998, by rfl⟩ : syracuseStep 181325 = 67997) (by norm_num)
theorem B574613 : Blo 111784 574613 := bbase (se 6 (by rfl) ⟨13467, by rfl⟩ : syracuseStep 574613 = 26935) (by norm_num)
theorem B279733 : Blo 111784 279733 := bbase (se 5 (by rfl) ⟨13112, by rfl⟩ : syracuseStep 279733 = 26225) (by norm_num)
theorem B378053 : Blo 111784 378053 := bbase (se 4 (by rfl) ⟨35442, by rfl⟩ : syracuseStep 378053 = 70885) (by norm_num)
theorem B968021 : Blo 111784 968021 := bbase (se 12 (by rfl) ⟨354, by rfl⟩ : syracuseStep 968021 = 709) (by norm_num)
theorem B214501 : Blo 111784 214501 := bbase (se 4 (by rfl) ⟨20109, by rfl⟩ : syracuseStep 214501 = 40219) (by norm_num)
theorem B345637 : Blo 111784 345637 := bbase (se 4 (by rfl) ⟨32403, by rfl⟩ : syracuseStep 345637 = 64807) (by norm_num)
theorem B378485 : Blo 111784 378485 := bbase (se 5 (by rfl) ⟨17741, by rfl⟩ : syracuseStep 378485 = 35483) (by norm_num)
theorem B214645 : Blo 111784 214645 := bbase (se 5 (by rfl) ⟨10061, by rfl⟩ : syracuseStep 214645 = 20123) (by norm_num)
theorem B214805 : Blo 111784 214805 := bbase (se 6 (by rfl) ⟨5034, by rfl⟩ : syracuseStep 214805 = 10069) (by norm_num)
theorem B214949 : Blo 111784 214949 := bbase (se 4 (by rfl) ⟨20151, by rfl⟩ : syracuseStep 214949 = 40303) (by norm_num)
theorem B378917 : Blo 111784 378917 := bbase (se 4 (by rfl) ⟨35523, by rfl⟩ : syracuseStep 378917 = 71047) (by norm_num)
theorem B116821 : Blo 111784 116821 := bbase (se 8 (by rfl) ⟨684, by rfl⟩ : syracuseStep 116821 = 1369) (by norm_num)
theorem B247901 : Blo 111784 247901 := bbase (se 3 (by rfl) ⟨46481, by rfl⟩ : syracuseStep 247901 = 92963) (by norm_num)
theorem B542821 : Blo 111784 542821 := bbase (se 4 (by rfl) ⟨50889, by rfl⟩ : syracuseStep 542821 = 101779) (by norm_num)
theorem B215237 : Blo 111784 215237 := bbase (se 4 (by rfl) ⟨20178, by rfl⟩ : syracuseStep 215237 = 40357) (by norm_num)
theorem B215389 : Blo 111784 215389 := bbase (se 3 (by rfl) ⟨40385, by rfl⟩ : syracuseStep 215389 = 80771) (by norm_num)
theorem B641429 : Blo 111784 641429 := bbase (se 6 (by rfl) ⟨15033, by rfl⟩ : syracuseStep 641429 = 30067) (by norm_num)
theorem B575909 : Blo 111784 575909 := bbase (se 4 (by rfl) ⟨53991, by rfl⟩ : syracuseStep 575909 = 107983) (by norm_num)
theorem B379349 : Blo 111784 379349 := bbase (se 7 (by rfl) ⟨4445, by rfl⟩ : syracuseStep 379349 = 8891) (by norm_num)
theorem B182837 : Blo 111784 182837 := bbase (se 5 (by rfl) ⟨8570, by rfl⟩ : syracuseStep 182837 = 17141) (by norm_num)
theorem B215693 : Blo 111784 215693 := bbase (se 3 (by rfl) ⟨40442, by rfl⟩ : syracuseStep 215693 = 80885) (by norm_num)
theorem B477845 : Blo 111784 477845 := bbase (se 6 (by rfl) ⟨11199, by rfl⟩ : syracuseStep 477845 = 22399) (by norm_num)
theorem B379781 : Blo 111784 379781 := bbase (se 4 (by rfl) ⟨35604, by rfl⟩ : syracuseStep 379781 = 71209) (by norm_num)
theorem B478133 : Blo 111784 478133 := bbase (se 5 (by rfl) ⟨22412, by rfl⟩ : syracuseStep 478133 = 44825) (by norm_num)
theorem B183293 : Blo 111784 183293 := bbase (se 3 (by rfl) ⟨34367, by rfl⟩ : syracuseStep 183293 = 68735) (by norm_num)
theorem B1559573 : Blo 111784 1559573 := bbase (se 6 (by rfl) ⟨36552, by rfl⟩ : syracuseStep 1559573 = 73105) (by norm_num)
theorem B347381 : Blo 111784 347381 := bbase (se 5 (by rfl) ⟨16283, by rfl⟩ : syracuseStep 347381 = 32567) (by norm_num)
theorem B380213 : Blo 111784 380213 := bbase (se 5 (by rfl) ⟨17822, by rfl⟩ : syracuseStep 380213 = 35645) (by norm_num)
theorem B216445 : Blo 111784 216445 := bbase (se 3 (by rfl) ⟨40583, by rfl⟩ : syracuseStep 216445 = 81167) (by norm_num)
theorem B216589 : Blo 111784 216589 := bbase (se 3 (by rfl) ⟨40610, by rfl⟩ : syracuseStep 216589 = 81221) (by norm_num)
theorem B642613 : Blo 111784 642613 := bbase (se 5 (by rfl) ⟨30122, by rfl⟩ : syracuseStep 642613 = 60245) (by norm_num)
theorem B413333 : Blo 111784 413333 := bbase (se 6 (by rfl) ⟨9687, by rfl⟩ : syracuseStep 413333 = 19375) (by norm_num)
theorem B478885 : Blo 111784 478885 := bbase (se 4 (by rfl) ⟨44895, by rfl⟩ : syracuseStep 478885 = 89791) (by norm_num)
theorem B216749 : Blo 111784 216749 := bbase (se 3 (by rfl) ⟨40640, by rfl⟩ : syracuseStep 216749 = 81281) (by norm_num)
theorem B577205 : Blo 111784 577205 := bbase (se 5 (by rfl) ⟨27056, by rfl⟩ : syracuseStep 577205 = 54113) (by norm_num)
theorem B380645 : Blo 111784 380645 := bbase (se 4 (by rfl) ⟨35685, by rfl⟩ : syracuseStep 380645 = 71371) (by norm_num)
theorem B216821 : Blo 111784 216821 := bbase (se 5 (by rfl) ⟨10163, by rfl⟩ : syracuseStep 216821 = 20327) (by norm_num)
theorem B216893 : Blo 111784 216893 := bbase (se 3 (by rfl) ⟨40667, by rfl⟩ : syracuseStep 216893 = 81335) (by norm_num)
theorem B184133 : Blo 111784 184133 := bbase (se 4 (by rfl) ⟨17262, by rfl⟩ : syracuseStep 184133 = 34525) (by norm_num)
theorem B184285 : Blo 111784 184285 := bbase (se 3 (by rfl) ⟨34553, by rfl⟩ : syracuseStep 184285 = 69107) (by norm_num)
theorem B577573 : Blo 111784 577573 := bbase (se 4 (by rfl) ⟨54147, by rfl⟩ : syracuseStep 577573 = 108295) (by norm_num)
theorem B217181 : Blo 111784 217181 := bbase (se 3 (by rfl) ⟨40721, by rfl⟩ : syracuseStep 217181 = 81443) (by norm_num)
theorem B381077 : Blo 111784 381077 := bbase (se 6 (by rfl) ⟨8931, by rfl⟩ : syracuseStep 381077 = 17863) (by norm_num)
theorem B151717 : Blo 111784 151717 := bbase (se 4 (by rfl) ⟨14223, by rfl⟩ : syracuseStep 151717 = 28447) (by norm_num)
theorem B413909 : Blo 111784 413909 := bbase (se 7 (by rfl) ⟨4850, by rfl⟩ : syracuseStep 413909 = 9701) (by norm_num)
theorem B217333 : Blo 111784 217333 := bbase (se 5 (by rfl) ⟨10187, by rfl⟩ : syracuseStep 217333 = 20375) (by norm_num)
theorem B282973 : Blo 111784 282973 := bbase (se 3 (by rfl) ⟨53057, by rfl⟩ : syracuseStep 282973 = 106115) (by norm_num)
theorem B250229 : Blo 111784 250229 := bbase (se 5 (by rfl) ⟨11729, by rfl⟩ : syracuseStep 250229 = 23459) (by norm_num)
theorem B479621 : Blo 111784 479621 := bbase (se 4 (by rfl) ⟨44964, by rfl⟩ : syracuseStep 479621 = 89929) (by norm_num)
theorem B348565 : Blo 111784 348565 := bbase (se 6 (by rfl) ⟨8169, by rfl⟩ : syracuseStep 348565 = 16339) (by norm_num)
theorem B283085 : Blo 111784 283085 := bbase (se 3 (by rfl) ⟨53078, by rfl⟩ : syracuseStep 283085 = 106157) (by norm_num)
theorem B217637 : Blo 111784 217637 := bbase (se 4 (by rfl) ⟨20403, by rfl⟩ : syracuseStep 217637 = 40807) (by norm_num)
theorem B381509 : Blo 111784 381509 := bbase (se 4 (by rfl) ⟨35766, by rfl⟩ : syracuseStep 381509 = 71533) (by norm_num)
theorem B184933 : Blo 111784 184933 := bbase (se 4 (by rfl) ⟨17337, by rfl⟩ : syracuseStep 184933 = 34675) (by norm_num)
theorem B283277 : Blo 111784 283277 := bbase (se 3 (by rfl) ⟨53114, by rfl⟩ : syracuseStep 283277 = 106229) (by norm_num)
theorem B119713 : Blo 111784 119713 := bbase (se 2 (by rfl) ⟨44892, by rfl⟩ : syracuseStep 119713 = 89785) (by norm_num)
theorem B578501 : Blo 111784 578501 := bbase (se 4 (by rfl) ⟨54234, by rfl⟩ : syracuseStep 578501 = 108469) (by norm_num)
theorem B807893 : Blo 111784 807893 := bbase (se 7 (by rfl) ⟨9467, by rfl⟩ : syracuseStep 807893 = 18935) (by norm_num)
theorem B283621 : Blo 111784 283621 := bbase (se 4 (by rfl) ⟨26589, by rfl⟩ : syracuseStep 283621 = 53179) (by norm_num)
theorem B381941 : Blo 111784 381941 := bbase (se 5 (by rfl) ⟨17903, by rfl⟩ : syracuseStep 381941 = 35807) (by norm_num)
theorem B119837 : Blo 111784 119837 := bbase (se 3 (by rfl) ⟨22469, by rfl⟩ : syracuseStep 119837 = 44939) (by norm_num)
theorem B283733 : Blo 111784 283733 := bbase (se 8 (by rfl) ⟨1662, by rfl⟩ : syracuseStep 283733 = 3325) (by norm_num)
theorem B185437 : Blo 111784 185437 := bbase (se 3 (by rfl) ⟨34769, by rfl⟩ : syracuseStep 185437 = 69539) (by norm_num)
theorem B283925 : Blo 111784 283925 := bbase (se 6 (by rfl) ⟨6654, by rfl⟩ : syracuseStep 283925 = 13309) (by norm_num)
theorem B218389 : Blo 111784 218389 := bbase (se 6 (by rfl) ⟨5118, by rfl⟩ : syracuseStep 218389 = 10237) (by norm_num)
theorem B120089 : Blo 111784 120089 := bbase (se 2 (by rfl) ⟨45033, by rfl⟩ : syracuseStep 120089 = 90067) (by norm_num)
theorem B152885 : Blo 111784 152885 := bbase (se 5 (by rfl) ⟨7166, by rfl⟩ : syracuseStep 152885 = 14333) (by norm_num)
theorem B382373 : Blo 111784 382373 := bbase (se 4 (by rfl) ⟨35847, by rfl⟩ : syracuseStep 382373 = 71695) (by norm_num)
theorem B218533 : Blo 111784 218533 := bbase (se 4 (by rfl) ⟨20487, by rfl⟩ : syracuseStep 218533 = 40975) (by norm_num)
theorem B644597 : Blo 111784 644597 := bbase (se 5 (by rfl) ⟨30215, by rfl⟩ : syracuseStep 644597 = 60431) (by norm_num)
theorem B153101 : Blo 111784 153101 := bbase (se 3 (by rfl) ⟨28706, by rfl⟩ : syracuseStep 153101 = 57413) (by norm_num)
theorem B349733 : Blo 111784 349733 := bbase (se 4 (by rfl) ⟨32787, by rfl⟩ : syracuseStep 349733 = 65575) (by norm_num)
theorem B218693 : Blo 111784 218693 := bbase (se 4 (by rfl) ⟨20502, by rfl⟩ : syracuseStep 218693 = 41005) (by norm_num)
theorem B284269 : Blo 111784 284269 := bbase (se 3 (by rfl) ⟨53300, by rfl⟩ : syracuseStep 284269 = 106601) (by norm_num)
theorem B251549 : Blo 111784 251549 := bbase (se 3 (by rfl) ⟨47165, by rfl⟩ : syracuseStep 251549 = 94331) (by norm_num)
theorem B120533 : Blo 111784 120533 := bbase (se 7 (by rfl) ⟨1412, by rfl⟩ : syracuseStep 120533 = 2825) (by norm_num)
theorem B218837 : Blo 111784 218837 := bbase (se 7 (by rfl) ⟨2564, by rfl⟩ : syracuseStep 218837 = 5129) (by norm_num)
theorem B284381 : Blo 111784 284381 := bbase (se 3 (by rfl) ⟨53321, by rfl⟩ : syracuseStep 284381 = 106643) (by norm_num)
theorem B251621 : Blo 111784 251621 := bbase (se 4 (by rfl) ⟨23589, by rfl⟩ : syracuseStep 251621 = 47179) (by norm_num)
theorem B906997 : Blo 111784 906997 := bbase (se 5 (by rfl) ⟨42515, by rfl⟩ : syracuseStep 906997 = 85031) (by norm_num)
theorem B251693 : Blo 111784 251693 := bbase (se 3 (by rfl) ⟨47192, by rfl⟩ : syracuseStep 251693 = 94385) (by norm_num)
theorem B382805 : Blo 111784 382805 := bbase (se 9 (by rfl) ⟨1121, by rfl⟩ : syracuseStep 382805 = 2243) (by norm_num)
theorem B251765 : Blo 111784 251765 := bbase (se 5 (by rfl) ⟨11801, by rfl⟩ : syracuseStep 251765 = 23603) (by norm_num)
theorem B284573 : Blo 111784 284573 := bbase (se 3 (by rfl) ⟨53357, by rfl⟩ : syracuseStep 284573 = 106715) (by norm_num)
theorem B251837 : Blo 111784 251837 := bbase (se 3 (by rfl) ⟨47219, by rfl⟩ : syracuseStep 251837 = 94439) (by norm_num)
theorem B120781 : Blo 111784 120781 := bbase (se 3 (by rfl) ⟨22646, by rfl⟩ : syracuseStep 120781 = 45293) (by norm_num)
theorem B219125 : Blo 111784 219125 := bbase (se 5 (by rfl) ⟨10271, by rfl⟩ : syracuseStep 219125 = 20543) (by norm_num)
theorem B251909 : Blo 111784 251909 := bbase (se 4 (by rfl) ⟨23616, by rfl⟩ : syracuseStep 251909 = 47233) (by norm_num)
theorem B186397 : Blo 111784 186397 := bbase (se 3 (by rfl) ⟨34949, by rfl⟩ : syracuseStep 186397 = 69899) (by norm_num)
theorem B251981 : Blo 111784 251981 := bbase (se 3 (by rfl) ⟨47246, by rfl⟩ : syracuseStep 251981 = 94493) (by norm_num)
theorem B415829 : Blo 111784 415829 := bbase (se 8 (by rfl) ⟨2436, by rfl⟩ : syracuseStep 415829 = 4873) (by norm_num)
theorem B219277 : Blo 111784 219277 := bbase (se 3 (by rfl) ⟨41114, by rfl⟩ : syracuseStep 219277 = 82229) (by norm_num)
theorem B252053 : Blo 111784 252053 := bbase (se 6 (by rfl) ⟨5907, by rfl⟩ : syracuseStep 252053 = 11815) (by norm_num)
theorem B547013 : Blo 111784 547013 := bbase (se 4 (by rfl) ⟨51282, by rfl⟩ : syracuseStep 547013 = 102565) (by norm_num)
theorem B579797 : Blo 111784 579797 := bbase (se 7 (by rfl) ⟨6794, by rfl⟩ : syracuseStep 579797 = 13589) (by norm_num)
theorem B252125 : Blo 111784 252125 := bbase (se 3 (by rfl) ⟨47273, by rfl⟩ : syracuseStep 252125 = 94547) (by norm_num)
theorem B284917 : Blo 111784 284917 := bbase (se 5 (by rfl) ⟨13355, by rfl⟩ : syracuseStep 284917 = 26711) (by norm_num)
theorem B383237 : Blo 111784 383237 := bbase (se 4 (by rfl) ⟨35928, by rfl⟩ : syracuseStep 383237 = 71857) (by norm_num)
theorem B252197 : Blo 111784 252197 := bbase (se 4 (by rfl) ⟨23643, by rfl⟩ : syracuseStep 252197 = 47287) (by norm_num)
theorem B285029 : Blo 111784 285029 := bbase (se 4 (by rfl) ⟨26721, by rfl⟩ : syracuseStep 285029 = 53443) (by norm_num)
theorem B252269 : Blo 111784 252269 := bbase (se 3 (by rfl) ⟨47300, by rfl⟩ : syracuseStep 252269 = 94601) (by norm_num)
theorem B121225 : Blo 111784 121225 := bbase (se 2 (by rfl) ⟨45459, by rfl⟩ : syracuseStep 121225 = 90919) (by norm_num)
theorem B252341 : Blo 111784 252341 := bbase (se 5 (by rfl) ⟨11828, by rfl⟩ : syracuseStep 252341 = 23657) (by norm_num)
theorem B219581 : Blo 111784 219581 := bbase (se 3 (by rfl) ⟨41171, by rfl⟩ : syracuseStep 219581 = 82343) (by norm_num)
theorem B121285 : Blo 111784 121285 := bbase (se 4 (by rfl) ⟨11370, by rfl⟩ : syracuseStep 121285 = 22741) (by norm_num)
theorem B252413 : Blo 111784 252413 := bbase (se 3 (by rfl) ⟨47327, by rfl⟩ : syracuseStep 252413 = 94655) (by norm_num)
theorem B285221 : Blo 111784 285221 := bbase (se 4 (by rfl) ⟨26739, by rfl⟩ : syracuseStep 285221 = 53479) (by norm_num)
theorem B252485 : Blo 111784 252485 := bbase (se 4 (by rfl) ⟨23670, by rfl⟩ : syracuseStep 252485 = 47341) (by norm_num)
theorem B645749 : Blo 111784 645749 := bbase (se 5 (by rfl) ⟨30269, by rfl⟩ : syracuseStep 645749 = 60539) (by norm_num)
theorem B252557 : Blo 111784 252557 := bbase (se 3 (by rfl) ⟨47354, by rfl⟩ : syracuseStep 252557 = 94709) (by norm_num)
theorem B383669 : Blo 111784 383669 := bbase (se 5 (by rfl) ⟨17984, by rfl⟩ : syracuseStep 383669 = 35969) (by norm_num)
theorem B252629 : Blo 111784 252629 := bbase (se 7 (by rfl) ⟨2960, by rfl⟩ : syracuseStep 252629 = 5921) (by norm_num)
theorem B121601 : Blo 111784 121601 := bbase (se 2 (by rfl) ⟨45600, by rfl⟩ : syracuseStep 121601 = 91201) (by norm_num)
theorem B875285 : Blo 111784 875285 := bbase (se 6 (by rfl) ⟨20514, by rfl⟩ : syracuseStep 875285 = 41029) (by norm_num)
theorem B252701 : Blo 111784 252701 := bbase (se 3 (by rfl) ⟨47381, by rfl⟩ : syracuseStep 252701 = 94763) (by norm_num)
theorem B187181 : Blo 111784 187181 := bbase (se 3 (by rfl) ⟨35096, by rfl⟩ : syracuseStep 187181 = 70193) (by norm_num)
theorem B2087765 : Blo 111784 2087765 := bbase (se 9 (by rfl) ⟨6116, by rfl⟩ : syracuseStep 2087765 = 12233) (by norm_num)
theorem B252773 : Blo 111784 252773 := bbase (se 4 (by rfl) ⟨23697, by rfl⟩ : syracuseStep 252773 = 47395) (by norm_num)
theorem B285565 : Blo 111784 285565 := bbase (se 3 (by rfl) ⟨53543, by rfl⟩ : syracuseStep 285565 = 107087) (by norm_num)
theorem B842645 : Blo 111784 842645 := bbase (se 6 (by rfl) ⟨19749, by rfl⟩ : syracuseStep 842645 = 39499) (by norm_num)
theorem B252845 : Blo 111784 252845 := bbase (se 3 (by rfl) ⟨47408, by rfl⟩ : syracuseStep 252845 = 94817) (by norm_num)
theorem B809909 : Blo 111784 809909 := bbase (se 5 (by rfl) ⟨37964, by rfl⟩ : syracuseStep 809909 = 75929) (by norm_num)
theorem B318437 : Blo 111784 318437 := bbase (se 4 (by rfl) ⟨29853, by rfl⟩ : syracuseStep 318437 = 59707) (by norm_num)
theorem B285677 : Blo 111784 285677 := bbase (se 3 (by rfl) ⟨53564, by rfl⟩ : syracuseStep 285677 = 107129) (by norm_num)
theorem B252917 : Blo 111784 252917 := bbase (se 5 (by rfl) ⟨11855, by rfl⟩ : syracuseStep 252917 = 23711) (by norm_num)
theorem B252989 : Blo 111784 252989 := bbase (se 3 (by rfl) ⟨47435, by rfl⟩ : syracuseStep 252989 = 94871) (by norm_num)
theorem B351317 : Blo 111784 351317 := bbase (se 8 (by rfl) ⟨2058, by rfl⟩ : syracuseStep 351317 = 4117) (by norm_num)
theorem B384101 : Blo 111784 384101 := bbase (se 4 (by rfl) ⟨36009, by rfl⟩ : syracuseStep 384101 = 72019) (by norm_num)
theorem B253061 : Blo 111784 253061 := bbase (se 4 (by rfl) ⟨23724, by rfl⟩ : syracuseStep 253061 = 47449) (by norm_num)
theorem B285869 : Blo 111784 285869 := bbase (se 3 (by rfl) ⟨53600, by rfl⟩ : syracuseStep 285869 = 107201) (by norm_num)
theorem B220333 : Blo 111784 220333 := bbase (se 3 (by rfl) ⟨41312, by rfl⟩ : syracuseStep 220333 = 82625) (by norm_num)
theorem B122045 : Blo 111784 122045 := bbase (se 3 (by rfl) ⟨22883, by rfl⟩ : syracuseStep 122045 = 45767) (by norm_num)
theorem B253133 : Blo 111784 253133 := bbase (se 3 (by rfl) ⟨47462, by rfl⟩ : syracuseStep 253133 = 94925) (by norm_num)
theorem B122105 : Blo 111784 122105 := bbase (se 2 (by rfl) ⟨45789, by rfl⟩ : syracuseStep 122105 = 91579) (by norm_num)
theorem B253205 : Blo 111784 253205 := bbase (se 6 (by rfl) ⟨5934, by rfl⟩ : syracuseStep 253205 = 11869) (by norm_num)
theorem B253277 : Blo 111784 253277 := bbase (se 3 (by rfl) ⟨47489, by rfl⟩ : syracuseStep 253277 = 94979) (by norm_num)
theorem B122233 : Blo 111784 122233 := bbase (se 2 (by rfl) ⟨45837, by rfl⟩ : syracuseStep 122233 = 91675) (by norm_num)
theorem B253349 : Blo 111784 253349 := bbase (se 4 (by rfl) ⟨23751, by rfl⟩ : syracuseStep 253349 = 47503) (by norm_num)
theorem B581093 : Blo 111784 581093 := bbase (se 4 (by rfl) ⟨54477, by rfl⟩ : syracuseStep 581093 = 108955) (by norm_num)
theorem B253421 : Blo 111784 253421 := bbase (se 3 (by rfl) ⟨47516, by rfl⟩ : syracuseStep 253421 = 95033) (by norm_num)
theorem B286213 : Blo 111784 286213 := bbase (se 4 (by rfl) ⟨26832, by rfl⟩ : syracuseStep 286213 = 53665) (by norm_num)
theorem B384533 : Blo 111784 384533 := bbase (se 6 (by rfl) ⟨9012, by rfl⟩ : syracuseStep 384533 = 18025) (by norm_num)
theorem B253493 : Blo 111784 253493 := bbase (se 5 (by rfl) ⟨11882, by rfl⟩ : syracuseStep 253493 = 23765) (by norm_num)
theorem B482917 : Blo 111784 482917 := bbase (se 4 (by rfl) ⟨45273, by rfl⟩ : syracuseStep 482917 = 90547) (by norm_num)
theorem B286325 : Blo 111784 286325 := bbase (se 5 (by rfl) ⟨13421, by rfl⟩ : syracuseStep 286325 = 26843) (by norm_num)
theorem B253565 : Blo 111784 253565 := bbase (se 3 (by rfl) ⟨47543, by rfl⟩ : syracuseStep 253565 = 95087) (by norm_num)
theorem B646805 : Blo 111784 646805 := bbase (se 6 (by rfl) ⟨15159, by rfl⟩ : syracuseStep 646805 = 30319) (by norm_num)
theorem B253637 : Blo 111784 253637 := bbase (se 4 (by rfl) ⟨23778, by rfl⟩ : syracuseStep 253637 = 47557) (by norm_num)
theorem B253709 : Blo 111784 253709 := bbase (se 3 (by rfl) ⟨47570, by rfl⟩ : syracuseStep 253709 = 95141) (by norm_num)
theorem B286517 : Blo 111784 286517 := bbase (se 5 (by rfl) ⟨13430, by rfl⟩ : syracuseStep 286517 = 26861) (by norm_num)
theorem B122677 : Blo 111784 122677 := bbase (se 5 (by rfl) ⟨5750, by rfl⟩ : syracuseStep 122677 = 11501) (by norm_num)
theorem B253781 : Blo 111784 253781 := bbase (se 9 (by rfl) ⟨743, by rfl⟩ : syracuseStep 253781 = 1487) (by norm_num)
theorem B253853 : Blo 111784 253853 := bbase (se 3 (by rfl) ⟨47597, by rfl⟩ : syracuseStep 253853 = 95195) (by norm_num)
theorem B286621 : Blo 111784 286621 := bbase (se 3 (by rfl) ⟨53741, by rfl⟩ : syracuseStep 286621 = 107483) (by norm_num)
theorem B122797 : Blo 111784 122797 := bbase (se 3 (by rfl) ⟨23024, by rfl⟩ : syracuseStep 122797 = 46049) (by norm_num)
theorem B384965 : Blo 111784 384965 := bbase (se 4 (by rfl) ⟨36090, by rfl⟩ : syracuseStep 384965 = 72181) (by norm_num)
theorem B253925 : Blo 111784 253925 := bbase (se 4 (by rfl) ⟨23805, by rfl⟩ : syracuseStep 253925 = 47611) (by norm_num)
theorem B253997 : Blo 111784 253997 := bbase (se 3 (by rfl) ⟨47624, by rfl⟩ : syracuseStep 253997 = 95249) (by norm_num)
theorem B254069 : Blo 111784 254069 := bbase (se 5 (by rfl) ⟨11909, by rfl⟩ : syracuseStep 254069 = 23819) (by norm_num)
theorem B319621 : Blo 111784 319621 := bbase (se 4 (by rfl) ⟨29964, by rfl⟩ : syracuseStep 319621 = 59929) (by norm_num)
theorem B286861 : Blo 111784 286861 := bbase (se 3 (by rfl) ⟨53786, by rfl⟩ : syracuseStep 286861 = 107573) (by norm_num)
theorem B123049 : Blo 111784 123049 := bbase (se 2 (by rfl) ⟨46143, by rfl⟩ : syracuseStep 123049 = 92287) (by norm_num)
theorem B123053 : Blo 111784 123053 := bbase (se 3 (by rfl) ⟨23072, by rfl⟩ : syracuseStep 123053 = 46145) (by norm_num)
theorem B254141 : Blo 111784 254141 := bbase (se 3 (by rfl) ⟨47651, by rfl⟩ : syracuseStep 254141 = 95303) (by norm_num)
theorem B188669 : Blo 111784 188669 := bbase (se 3 (by rfl) ⟨35375, by rfl⟩ : syracuseStep 188669 = 70751) (by norm_num)
theorem B286973 : Blo 111784 286973 := bbase (se 3 (by rfl) ⟨53807, by rfl⟩ : syracuseStep 286973 = 107615) (by norm_num)
theorem B254213 : Blo 111784 254213 := bbase (se 4 (by rfl) ⟨23832, by rfl⟩ : syracuseStep 254213 = 47665) (by norm_num)
theorem B319781 : Blo 111784 319781 := bbase (se 4 (by rfl) ⟨29979, by rfl⟩ : syracuseStep 319781 = 59959) (by norm_num)
theorem B123205 : Blo 111784 123205 := bbase (se 4 (by rfl) ⟨11550, by rfl⟩ : syracuseStep 123205 = 23101) (by norm_num)
theorem B254285 : Blo 111784 254285 := bbase (se 3 (by rfl) ⟨47678, by rfl⟩ : syracuseStep 254285 = 95357) (by norm_num)
theorem B385397 : Blo 111784 385397 := bbase (se 5 (by rfl) ⟨18065, by rfl⟩ : syracuseStep 385397 = 36131) (by norm_num)
theorem B188797 : Blo 111784 188797 := bbase (se 3 (by rfl) ⟨35399, by rfl⟩ : syracuseStep 188797 = 70799) (by norm_num)
theorem B254357 : Blo 111784 254357 := bbase (se 6 (by rfl) ⟨5961, by rfl⟩ : syracuseStep 254357 = 11923) (by norm_num)
theorem B287165 : Blo 111784 287165 := bbase (se 3 (by rfl) ⟨53843, by rfl⟩ : syracuseStep 287165 = 107687) (by norm_num)
theorem B188885 : Blo 111784 188885 := bbase (se 7 (by rfl) ⟨2213, by rfl⟩ : syracuseStep 188885 = 4427) (by norm_num)
theorem B254429 : Blo 111784 254429 := bbase (se 3 (by rfl) ⟨47705, by rfl⟩ : syracuseStep 254429 = 95411) (by norm_num)
theorem B320021 : Blo 111784 320021 := bbase (se 6 (by rfl) ⟨7500, by rfl⟩ : syracuseStep 320021 = 15001) (by norm_num)
theorem B221717 : Blo 111784 221717 := bbase (se 6 (by rfl) ⟨5196, by rfl⟩ : syracuseStep 221717 = 10393) (by norm_num)
theorem B123425 : Blo 111784 123425 := bbase (se 2 (by rfl) ⟨46284, by rfl⟩ : syracuseStep 123425 = 92569) (by norm_num)
theorem B254501 : Blo 111784 254501 := bbase (se 4 (by rfl) ⟨23859, by rfl⟩ : syracuseStep 254501 = 47719) (by norm_num)
theorem B189013 : Blo 111784 189013 := bbase (se 8 (by rfl) ⟨1107, by rfl⟩ : syracuseStep 189013 = 2215) (by norm_num)
theorem B254573 : Blo 111784 254573 := bbase (se 3 (by rfl) ⟨47732, by rfl⟩ : syracuseStep 254573 = 95465) (by norm_num)
theorem B189101 : Blo 111784 189101 := bbase (se 3 (by rfl) ⟨35456, by rfl⟩ : syracuseStep 189101 = 70913) (by norm_num)
theorem B254645 : Blo 111784 254645 := bbase (se 5 (by rfl) ⟨11936, by rfl⟩ : syracuseStep 254645 = 23873) (by norm_num)
theorem B123589 : Blo 111784 123589 := bbase (se 4 (by rfl) ⟨11586, by rfl⟩ : syracuseStep 123589 = 23173) (by norm_num)
theorem B320213 : Blo 111784 320213 := bbase (se 7 (by rfl) ⟨3752, by rfl⟩ : syracuseStep 320213 = 7505) (by norm_num)
theorem B123617 : Blo 111784 123617 := bbase (se 2 (by rfl) ⟨46356, by rfl⟩ : syracuseStep 123617 = 92713) (by norm_num)
theorem B582389 : Blo 111784 582389 := bbase (se 5 (by rfl) ⟨27299, by rfl⟩ : syracuseStep 582389 = 54599) (by norm_num)
theorem B254717 : Blo 111784 254717 := bbase (se 3 (by rfl) ⟨47759, by rfl⟩ : syracuseStep 254717 = 95519) (by norm_num)
theorem B287509 : Blo 111784 287509 := bbase (se 6 (by rfl) ⟨6738, by rfl⟩ : syracuseStep 287509 = 13477) (by norm_num)
theorem B385829 : Blo 111784 385829 := bbase (se 4 (by rfl) ⟨36171, by rfl⟩ : syracuseStep 385829 = 72343) (by norm_num)
theorem B189229 : Blo 111784 189229 := bbase (se 3 (by rfl) ⟨35480, by rfl⟩ : syracuseStep 189229 = 70961) (by norm_num)
theorem B254789 : Blo 111784 254789 := bbase (se 4 (by rfl) ⟨23886, by rfl⟩ : syracuseStep 254789 = 47773) (by norm_num)
theorem B189317 : Blo 111784 189317 := bbase (se 4 (by rfl) ⟨17748, by rfl⟩ : syracuseStep 189317 = 35497) (by norm_num)
theorem B287621 : Blo 111784 287621 := bbase (se 4 (by rfl) ⟨26964, by rfl⟩ : syracuseStep 287621 = 53929) (by norm_num)
theorem B254861 : Blo 111784 254861 := bbase (se 3 (by rfl) ⟨47786, by rfl⟩ : syracuseStep 254861 = 95573) (by norm_num)
theorem B254933 : Blo 111784 254933 := bbase (se 7 (by rfl) ⟨2987, by rfl⟩ : syracuseStep 254933 = 5975) (by norm_num)
theorem B189445 : Blo 111784 189445 := bbase (se 4 (by rfl) ⟨17760, by rfl⟩ : syracuseStep 189445 = 35521) (by norm_num)
theorem B2057237 : Blo 111784 2057237 := bbase (se 6 (by rfl) ⟨48216, by rfl⟩ : syracuseStep 2057237 = 96433) (by norm_num)
theorem B255005 : Blo 111784 255005 := bbase (se 3 (by rfl) ⟨47813, by rfl⟩ : syracuseStep 255005 = 95627) (by norm_num)
theorem B287813 : Blo 111784 287813 := bbase (se 4 (by rfl) ⟨26982, by rfl⟩ : syracuseStep 287813 = 53965) (by norm_num)
theorem B189533 : Blo 111784 189533 := bbase (se 3 (by rfl) ⟨35537, by rfl⟩ : syracuseStep 189533 = 71075) (by norm_num)
theorem B255077 : Blo 111784 255077 := bbase (se 4 (by rfl) ⟨23913, by rfl⟩ : syracuseStep 255077 = 47827) (by norm_num)
theorem B255149 : Blo 111784 255149 := bbase (se 3 (by rfl) ⟨47840, by rfl⟩ : syracuseStep 255149 = 95681) (by norm_num)
theorem B386261 : Blo 111784 386261 := bbase (se 7 (by rfl) ⟨4526, by rfl⟩ : syracuseStep 386261 = 9053) (by norm_num)
theorem B189661 : Blo 111784 189661 := bbase (se 3 (by rfl) ⟨35561, by rfl⟩ : syracuseStep 189661 = 71123) (by norm_num)
theorem B255221 : Blo 111784 255221 := bbase (se 5 (by rfl) ⟨11963, by rfl⟩ : syracuseStep 255221 = 23927) (by norm_num)
theorem B189749 : Blo 111784 189749 := bbase (se 5 (by rfl) ⟨8894, by rfl⟩ : syracuseStep 189749 = 17789) (by norm_num)
theorem B517429 : Blo 111784 517429 := bbase (se 5 (by rfl) ⟨24254, by rfl⟩ : syracuseStep 517429 = 48509) (by norm_num)
theorem B877877 : Blo 111784 877877 := bbase (se 5 (by rfl) ⟨41150, by rfl⟩ : syracuseStep 877877 = 82301) (by norm_num)
theorem B255293 : Blo 111784 255293 := bbase (se 3 (by rfl) ⟨47867, by rfl⟩ : syracuseStep 255293 = 95735) (by norm_num)
theorem B255365 : Blo 111784 255365 := bbase (se 4 (by rfl) ⟨23940, by rfl⟩ : syracuseStep 255365 = 47881) (by norm_num)
theorem B681365 : Blo 111784 681365 := bbase (se 6 (by rfl) ⟨15969, by rfl⟩ : syracuseStep 681365 = 31939) (by norm_num)
theorem B288157 : Blo 111784 288157 := bbase (se 3 (by rfl) ⟨54029, by rfl⟩ : syracuseStep 288157 = 108059) (by norm_num)
theorem B189877 : Blo 111784 189877 := bbase (se 5 (by rfl) ⟨8900, by rfl⟩ : syracuseStep 189877 = 17801) (by norm_num)
theorem B255437 : Blo 111784 255437 := bbase (se 3 (by rfl) ⟨47894, by rfl⟩ : syracuseStep 255437 = 95789) (by norm_num)
theorem B976373 : Blo 111784 976373 := bbase (se 5 (by rfl) ⟨45767, by rfl⟩ : syracuseStep 976373 = 91535) (by norm_num)
theorem B222725 : Blo 111784 222725 := bbase (se 4 (by rfl) ⟨20880, by rfl⟩ : syracuseStep 222725 = 41761) (by norm_num)
theorem B189965 : Blo 111784 189965 := bbase (se 3 (by rfl) ⟨35618, by rfl⟩ : syracuseStep 189965 = 71237) (by norm_num)
theorem B288269 : Blo 111784 288269 := bbase (se 3 (by rfl) ⟨54050, by rfl⟩ : syracuseStep 288269 = 108101) (by norm_num)
theorem B255509 : Blo 111784 255509 := bbase (se 6 (by rfl) ⟨5988, by rfl⟩ : syracuseStep 255509 = 11977) (by norm_num)
theorem B255581 : Blo 111784 255581 := bbase (se 3 (by rfl) ⟨47921, by rfl⟩ : syracuseStep 255581 = 95843) (by norm_num)
theorem B386693 : Blo 111784 386693 := bbase (se 4 (by rfl) ⟨36252, by rfl⟩ : syracuseStep 386693 = 72505) (by norm_num)
theorem B190093 : Blo 111784 190093 := bbase (se 3 (by rfl) ⟨35642, by rfl⟩ : syracuseStep 190093 = 71285) (by norm_num)
theorem B255653 : Blo 111784 255653 := bbase (se 4 (by rfl) ⟨23967, by rfl⟩ : syracuseStep 255653 = 47935) (by norm_num)
theorem B321205 : Blo 111784 321205 := bbase (se 5 (by rfl) ⟨15056, by rfl⟩ : syracuseStep 321205 = 30113) (by norm_num)
theorem B288461 : Blo 111784 288461 := bbase (se 3 (by rfl) ⟨54086, by rfl⟩ : syracuseStep 288461 = 108173) (by norm_num)
theorem B190181 : Blo 111784 190181 := bbase (se 4 (by rfl) ⟨17829, by rfl⟩ : syracuseStep 190181 = 35659) (by norm_num)
theorem B255725 : Blo 111784 255725 := bbase (se 3 (by rfl) ⟨47948, by rfl⟩ : syracuseStep 255725 = 95897) (by norm_num)
theorem B255797 : Blo 111784 255797 := bbase (se 5 (by rfl) ⟨11990, by rfl⟩ : syracuseStep 255797 = 23981) (by norm_num)
theorem B190309 : Blo 111784 190309 := bbase (se 4 (by rfl) ⟨17841, by rfl⟩ : syracuseStep 190309 = 35683) (by norm_num)
theorem B255869 : Blo 111784 255869 := bbase (se 3 (by rfl) ⟨47975, by rfl⟩ : syracuseStep 255869 = 95951) (by norm_num)
theorem B190397 : Blo 111784 190397 := bbase (se 3 (by rfl) ⟨35699, by rfl⟩ : syracuseStep 190397 = 71399) (by norm_num)
theorem B255941 : Blo 111784 255941 := bbase (se 4 (by rfl) ⟨23994, by rfl⟩ : syracuseStep 255941 = 47989) (by norm_num)
theorem B583685 : Blo 111784 583685 := bbase (se 4 (by rfl) ⟨54720, by rfl⟩ : syracuseStep 583685 = 109441) (by norm_num)
theorem B256013 : Blo 111784 256013 := bbase (se 3 (by rfl) ⟨48002, by rfl⟩ : syracuseStep 256013 = 96005) (by norm_num)
theorem B288805 : Blo 111784 288805 := bbase (se 4 (by rfl) ⟨27075, by rfl⟩ : syracuseStep 288805 = 54151) (by norm_num)
theorem B387125 : Blo 111784 387125 := bbase (se 5 (by rfl) ⟨18146, by rfl⟩ : syracuseStep 387125 = 36293) (by norm_num)
theorem B190525 : Blo 111784 190525 := bbase (se 3 (by rfl) ⟨35723, by rfl⟩ : syracuseStep 190525 = 71447) (by norm_num)
theorem B256085 : Blo 111784 256085 := bbase (se 8 (by rfl) ⟨1500, by rfl⟩ : syracuseStep 256085 = 3001) (by norm_num)
theorem B190613 : Blo 111784 190613 := bbase (se 6 (by rfl) ⟨4467, by rfl⟩ : syracuseStep 190613 = 8935) (by norm_num)
theorem B288917 : Blo 111784 288917 := bbase (se 6 (by rfl) ⟨6771, by rfl⟩ : syracuseStep 288917 = 13543) (by norm_num)
theorem B256157 : Blo 111784 256157 := bbase (se 3 (by rfl) ⟨48029, by rfl⟩ : syracuseStep 256157 = 96059) (by norm_num)
theorem B256229 : Blo 111784 256229 := bbase (se 4 (by rfl) ⟨24021, by rfl⟩ : syracuseStep 256229 = 48043) (by norm_num)
theorem B190741 : Blo 111784 190741 := bbase (se 6 (by rfl) ⟨4470, by rfl⟩ : syracuseStep 190741 = 8941) (by norm_num)
theorem B256301 : Blo 111784 256301 := bbase (se 3 (by rfl) ⟨48056, by rfl⟩ : syracuseStep 256301 = 96113) (by norm_num)
theorem B289109 : Blo 111784 289109 := bbase (se 10 (by rfl) ⟨423, by rfl⟩ : syracuseStep 289109 = 847) (by norm_num)
theorem B190829 : Blo 111784 190829 := bbase (se 3 (by rfl) ⟨35780, by rfl⟩ : syracuseStep 190829 = 71561) (by norm_num)
theorem B256373 : Blo 111784 256373 := bbase (se 5 (by rfl) ⟨12017, by rfl⟩ : syracuseStep 256373 = 24035) (by norm_num)
theorem B256445 : Blo 111784 256445 := bbase (se 3 (by rfl) ⟨48083, by rfl⟩ : syracuseStep 256445 = 96167) (by norm_num)
theorem B387557 : Blo 111784 387557 := bbase (se 4 (by rfl) ⟨36333, by rfl⟩ : syracuseStep 387557 = 72667) (by norm_num)
theorem B190957 : Blo 111784 190957 := bbase (se 3 (by rfl) ⟨35804, by rfl⟩ : syracuseStep 190957 = 71609) (by norm_num)
theorem B256517 : Blo 111784 256517 := bbase (se 4 (by rfl) ⟨24048, by rfl⟩ : syracuseStep 256517 = 48097) (by norm_num)
theorem B485909 : Blo 111784 485909 := bbase (se 6 (by rfl) ⟨11388, by rfl⟩ : syracuseStep 485909 = 22777) (by norm_num)
theorem B191045 : Blo 111784 191045 := bbase (se 4 (by rfl) ⟨17910, by rfl⟩ : syracuseStep 191045 = 35821) (by norm_num)
theorem B256589 : Blo 111784 256589 := bbase (se 3 (by rfl) ⟨48110, by rfl⟩ : syracuseStep 256589 = 96221) (by norm_num)
theorem B256661 : Blo 111784 256661 := bbase (se 6 (by rfl) ⟨6015, by rfl⟩ : syracuseStep 256661 = 12031) (by norm_num)
theorem B289453 : Blo 111784 289453 := bbase (se 3 (by rfl) ⟨54272, by rfl⟩ : syracuseStep 289453 = 108545) (by norm_num)
theorem B191173 : Blo 111784 191173 := bbase (se 4 (by rfl) ⟨17922, by rfl⟩ : syracuseStep 191173 = 35845) (by norm_num)
theorem B256733 : Blo 111784 256733 := bbase (se 3 (by rfl) ⟨48137, by rfl⟩ : syracuseStep 256733 = 96275) (by norm_num)
theorem B322309 : Blo 111784 322309 := bbase (se 4 (by rfl) ⟨30216, by rfl⟩ : syracuseStep 322309 = 60433) (by norm_num)
theorem B191261 : Blo 111784 191261 := bbase (se 3 (by rfl) ⟨35861, by rfl⟩ : syracuseStep 191261 = 71723) (by norm_num)
theorem B289565 : Blo 111784 289565 := bbase (se 3 (by rfl) ⟨54293, by rfl⟩ : syracuseStep 289565 = 108587) (by norm_num)
theorem B256805 : Blo 111784 256805 := bbase (se 4 (by rfl) ⟨24075, by rfl⟩ : syracuseStep 256805 = 48151) (by norm_num)
theorem B125761 : Blo 111784 125761 := bbase (se 2 (by rfl) ⟨47160, by rfl⟩ : syracuseStep 125761 = 94321) (by norm_num)
theorem B125797 : Blo 111784 125797 := bbase (se 4 (by rfl) ⟨11793, by rfl⟩ : syracuseStep 125797 = 23587) (by norm_num)
theorem B256877 : Blo 111784 256877 := bbase (se 3 (by rfl) ⟨48164, by rfl⟩ : syracuseStep 256877 = 96329) (by norm_num)
theorem B125833 : Blo 111784 125833 := bbase (se 2 (by rfl) ⟨47187, by rfl⟩ : syracuseStep 125833 = 94375) (by norm_num)
theorem B387989 : Blo 111784 387989 := bbase (se 6 (by rfl) ⟨9093, by rfl⟩ : syracuseStep 387989 = 18187) (by norm_num)
theorem B191389 : Blo 111784 191389 := bbase (se 3 (by rfl) ⟨35885, by rfl⟩ : syracuseStep 191389 = 71771) (by norm_num)
theorem B125869 : Blo 111784 125869 := bbase (se 3 (by rfl) ⟨23600, by rfl⟩ : syracuseStep 125869 = 47201) (by norm_num)
theorem B256949 : Blo 111784 256949 := bbase (se 5 (by rfl) ⟨12044, by rfl⟩ : syracuseStep 256949 = 24089) (by norm_num)
theorem B125905 : Blo 111784 125905 := bbase (se 2 (by rfl) ⟨47214, by rfl⟩ : syracuseStep 125905 = 94429) (by norm_num)
theorem B289757 : Blo 111784 289757 := bbase (se 3 (by rfl) ⟨54329, by rfl⟩ : syracuseStep 289757 = 108659) (by norm_num)
theorem B125941 : Blo 111784 125941 := bbase (se 5 (by rfl) ⟨5903, by rfl⟩ : syracuseStep 125941 = 11807) (by norm_num)
theorem B191477 : Blo 111784 191477 := bbase (se 5 (by rfl) ⟨8975, by rfl⟩ : syracuseStep 191477 = 17951) (by norm_num)
theorem B257021 : Blo 111784 257021 := bbase (se 3 (by rfl) ⟨48191, by rfl⟩ : syracuseStep 257021 = 96383) (by norm_num)
theorem B125977 : Blo 111784 125977 := bbase (se 2 (by rfl) ⟨47241, by rfl⟩ : syracuseStep 125977 = 94483) (by norm_num)
theorem B257053 : Blo 111784 257053 := bbase (se 3 (by rfl) ⟨48197, by rfl⟩ : syracuseStep 257053 = 96395) (by norm_num)
theorem B126013 : Blo 111784 126013 := bbase (se 3 (by rfl) ⟨23627, by rfl⟩ : syracuseStep 126013 = 47255) (by norm_num)
theorem B257093 : Blo 111784 257093 := bbase (se 4 (by rfl) ⟨24102, by rfl⟩ : syracuseStep 257093 = 48205) (by norm_num)
theorem B126049 : Blo 111784 126049 := bbase (se 2 (by rfl) ⟨47268, by rfl⟩ : syracuseStep 126049 = 94537) (by norm_num)
theorem B191605 : Blo 111784 191605 := bbase (se 5 (by rfl) ⟨8981, by rfl⟩ : syracuseStep 191605 = 17963) (by norm_num)
theorem B126085 : Blo 111784 126085 := bbase (se 4 (by rfl) ⟨11820, by rfl⟩ : syracuseStep 126085 = 23641) (by norm_num)
theorem B257165 : Blo 111784 257165 := bbase (se 3 (by rfl) ⟨48218, by rfl⟩ : syracuseStep 257165 = 96437) (by norm_num)
theorem B126121 : Blo 111784 126121 := bbase (se 2 (by rfl) ⟨47295, by rfl⟩ : syracuseStep 126121 = 94591) (by norm_num)
theorem B126157 : Blo 111784 126157 := bbase (se 3 (by rfl) ⟨23654, by rfl⟩ : syracuseStep 126157 = 47309) (by norm_num)
theorem B191693 : Blo 111784 191693 := bbase (se 3 (by rfl) ⟨35942, by rfl⟩ : syracuseStep 191693 = 71885) (by norm_num)
theorem B2616533 : Blo 111784 2616533 := bbase (se 7 (by rfl) ⟨30662, by rfl⟩ : syracuseStep 2616533 = 61325) (by norm_num)
theorem B257237 : Blo 111784 257237 := bbase (se 7 (by rfl) ⟨3014, by rfl⟩ : syracuseStep 257237 = 6029) (by norm_num)
theorem B126193 : Blo 111784 126193 := bbase (se 2 (by rfl) ⟨47322, by rfl⟩ : syracuseStep 126193 = 94645) (by norm_num)
theorem B126229 : Blo 111784 126229 := bbase (se 6 (by rfl) ⟨2958, by rfl⟩ : syracuseStep 126229 = 5917) (by norm_num)
theorem B584981 : Blo 111784 584981 := bbase (se 6 (by rfl) ⟨13710, by rfl⟩ : syracuseStep 584981 = 27421) (by norm_num)
theorem B257309 : Blo 111784 257309 := bbase (se 3 (by rfl) ⟨48245, by rfl⟩ : syracuseStep 257309 = 96491) (by norm_num)
theorem B290101 : Blo 111784 290101 := bbase (se 5 (by rfl) ⟨13598, by rfl⟩ : syracuseStep 290101 = 27197) (by norm_num)
theorem B126265 : Blo 111784 126265 := bbase (se 2 (by rfl) ⟨47349, by rfl⟩ : syracuseStep 126265 = 94699) (by norm_num)
theorem B388421 : Blo 111784 388421 := bbase (se 4 (by rfl) ⟨36414, by rfl⟩ : syracuseStep 388421 = 72829) (by norm_num)
theorem B191821 : Blo 111784 191821 := bbase (se 3 (by rfl) ⟨35966, by rfl⟩ : syracuseStep 191821 = 71933) (by norm_num)
theorem B617813 : Blo 111784 617813 := bbase (se 11 (by rfl) ⟨452, by rfl⟩ : syracuseStep 617813 = 905) (by norm_num)
theorem B126301 : Blo 111784 126301 := bbase (se 3 (by rfl) ⟨23681, by rfl⟩ : syracuseStep 126301 = 47363) (by norm_num)
theorem B257381 : Blo 111784 257381 := bbase (se 4 (by rfl) ⟨24129, by rfl⟩ : syracuseStep 257381 = 48259) (by norm_num)
theorem B126337 : Blo 111784 126337 := bbase (se 2 (by rfl) ⟨47376, by rfl⟩ : syracuseStep 126337 = 94753) (by norm_num)
theorem B126373 : Blo 111784 126373 := bbase (se 4 (by rfl) ⟨11847, by rfl⟩ : syracuseStep 126373 = 23695) (by norm_num)
theorem B191909 : Blo 111784 191909 := bbase (se 4 (by rfl) ⟨17991, by rfl⟩ : syracuseStep 191909 = 35983) (by norm_num)
theorem B290213 : Blo 111784 290213 := bbase (se 4 (by rfl) ⟨27207, by rfl⟩ : syracuseStep 290213 = 54415) (by norm_num)
theorem B257453 : Blo 111784 257453 := bbase (se 3 (by rfl) ⟨48272, by rfl⟩ : syracuseStep 257453 = 96545) (by norm_num)
theorem B126409 : Blo 111784 126409 := bbase (se 2 (by rfl) ⟨47403, by rfl⟩ : syracuseStep 126409 = 94807) (by norm_num)
theorem B126445 : Blo 111784 126445 := bbase (se 3 (by rfl) ⟨23708, by rfl⟩ : syracuseStep 126445 = 47417) (by norm_num)
theorem B257525 : Blo 111784 257525 := bbase (se 5 (by rfl) ⟨12071, by rfl⟩ : syracuseStep 257525 = 24143) (by norm_num)
theorem B486917 : Blo 111784 486917 := bbase (se 4 (by rfl) ⟨45648, by rfl⟩ : syracuseStep 486917 = 91297) (by norm_num)
theorem B126481 : Blo 111784 126481 := bbase (se 2 (by rfl) ⟨47430, by rfl⟩ : syracuseStep 126481 = 94861) (by norm_num)
theorem B192037 : Blo 111784 192037 := bbase (se 4 (by rfl) ⟨18003, by rfl⟩ : syracuseStep 192037 = 36007) (by norm_num)
theorem B126517 : Blo 111784 126517 := bbase (se 5 (by rfl) ⟨5930, by rfl⟩ : syracuseStep 126517 = 11861) (by norm_num)
theorem B257597 : Blo 111784 257597 := bbase (se 3 (by rfl) ⟨48299, by rfl⟩ : syracuseStep 257597 = 96599) (by norm_num)
theorem B126553 : Blo 111784 126553 := bbase (se 2 (by rfl) ⟨47457, by rfl⟩ : syracuseStep 126553 = 94915) (by norm_num)
theorem B388709 : Blo 111784 388709 := bbase (se 4 (by rfl) ⟨36441, by rfl⟩ : syracuseStep 388709 = 72883) (by norm_num)
theorem B290405 : Blo 111784 290405 := bbase (se 4 (by rfl) ⟨27225, by rfl⟩ : syracuseStep 290405 = 54451) (by norm_num)
theorem B126589 : Blo 111784 126589 := bbase (se 3 (by rfl) ⟨23735, by rfl⟩ : syracuseStep 126589 = 47471) (by norm_num)
theorem B192125 : Blo 111784 192125 := bbase (se 3 (by rfl) ⟨36023, by rfl⟩ : syracuseStep 192125 = 72047) (by norm_num)
theorem B257669 : Blo 111784 257669 := bbase (se 4 (by rfl) ⟨24156, by rfl⟩ : syracuseStep 257669 = 48313) (by norm_num)
theorem B126625 : Blo 111784 126625 := bbase (se 2 (by rfl) ⟨47484, by rfl⟩ : syracuseStep 126625 = 94969) (by norm_num)
theorem B126661 : Blo 111784 126661 := bbase (se 4 (by rfl) ⟨11874, by rfl⟩ : syracuseStep 126661 = 23749) (by norm_num)
theorem B585413 : Blo 111784 585413 := bbase (se 4 (by rfl) ⟨54882, by rfl⟩ : syracuseStep 585413 = 109765) (by norm_num)
theorem B257741 : Blo 111784 257741 := bbase (se 3 (by rfl) ⟨48326, by rfl⟩ : syracuseStep 257741 = 96653) (by norm_num)
theorem B126697 : Blo 111784 126697 := bbase (se 2 (by rfl) ⟨47511, by rfl⟩ : syracuseStep 126697 = 95023) (by norm_num)
theorem B388853 : Blo 111784 388853 := bbase (se 5 (by rfl) ⟨18227, by rfl⟩ : syracuseStep 388853 = 36455) (by norm_num)
theorem B192253 : Blo 111784 192253 := bbase (se 3 (by rfl) ⟨36047, by rfl⟩ : syracuseStep 192253 = 72095) (by norm_num)
theorem B126733 : Blo 111784 126733 := bbase (se 3 (by rfl) ⟨23762, by rfl⟩ : syracuseStep 126733 = 47525) (by norm_num)
theorem B159509 : Blo 111784 159509 := bbase (se 6 (by rfl) ⟨3738, by rfl⟩ : syracuseStep 159509 = 7477) (by norm_num)
theorem B257813 : Blo 111784 257813 := bbase (se 6 (by rfl) ⟨6042, by rfl⟩ : syracuseStep 257813 = 12085) (by norm_num)
theorem B126769 : Blo 111784 126769 := bbase (se 2 (by rfl) ⟨47538, by rfl⟩ : syracuseStep 126769 = 95077) (by norm_num)
theorem B126805 : Blo 111784 126805 := bbase (se 9 (by rfl) ⟨371, by rfl⟩ : syracuseStep 126805 = 743) (by norm_num)
theorem B192341 : Blo 111784 192341 := bbase (se 9 (by rfl) ⟨563, by rfl⟩ : syracuseStep 192341 = 1127) (by norm_num)
theorem B257885 : Blo 111784 257885 := bbase (se 3 (by rfl) ⟨48353, by rfl⟩ : syracuseStep 257885 = 96707) (by norm_num)
theorem B126841 : Blo 111784 126841 := bbase (se 2 (by rfl) ⟨47565, by rfl⟩ : syracuseStep 126841 = 95131) (by norm_num)
theorem B126877 : Blo 111784 126877 := bbase (se 3 (by rfl) ⟨23789, by rfl⟩ : syracuseStep 126877 = 47579) (by norm_num)
theorem B257957 : Blo 111784 257957 := bbase (se 4 (by rfl) ⟨24183, by rfl⟩ : syracuseStep 257957 = 48367) (by norm_num)
theorem B290749 : Blo 111784 290749 := bbase (se 3 (by rfl) ⟨54515, by rfl⟩ : syracuseStep 290749 = 109031) (by norm_num)
theorem B126913 : Blo 111784 126913 := bbase (se 2 (by rfl) ⟨47592, by rfl⟩ : syracuseStep 126913 = 95185) (by norm_num)
theorem B192469 : Blo 111784 192469 := bbase (se 7 (by rfl) ⟨2255, by rfl⟩ : syracuseStep 192469 = 4511) (by norm_num)
theorem B126949 : Blo 111784 126949 := bbase (se 4 (by rfl) ⟨11901, by rfl⟩ : syracuseStep 126949 = 23803) (by norm_num)
theorem B258029 : Blo 111784 258029 := bbase (se 3 (by rfl) ⟨48380, by rfl⟩ : syracuseStep 258029 = 96761) (by norm_num)
theorem B716789 : Blo 111784 716789 := bbase (se 5 (by rfl) ⟨33599, by rfl⟩ : syracuseStep 716789 = 67199) (by norm_num)
theorem B126985 : Blo 111784 126985 := bbase (se 2 (by rfl) ⟨47619, by rfl⟩ : syracuseStep 126985 = 95239) (by norm_num)
theorem B127021 : Blo 111784 127021 := bbase (se 3 (by rfl) ⟨23816, by rfl⟩ : syracuseStep 127021 = 47633) (by norm_num)
theorem B192557 : Blo 111784 192557 := bbase (se 3 (by rfl) ⟨36104, by rfl⟩ : syracuseStep 192557 = 72209) (by norm_num)
theorem B290861 : Blo 111784 290861 := bbase (se 3 (by rfl) ⟨54536, by rfl⟩ : syracuseStep 290861 = 109073) (by norm_num)
theorem B258101 : Blo 111784 258101 := bbase (se 5 (by rfl) ⟨12098, by rfl⟩ : syracuseStep 258101 = 24197) (by norm_num)
theorem B127057 : Blo 111784 127057 := bbase (se 2 (by rfl) ⟨47646, by rfl⟩ : syracuseStep 127057 = 95293) (by norm_num)
theorem B2093141 : Blo 111784 2093141 := bbase (se 8 (by rfl) ⟨12264, by rfl⟩ : syracuseStep 2093141 = 24529) (by norm_num)
theorem B127093 : Blo 111784 127093 := bbase (se 5 (by rfl) ⟨5957, by rfl⟩ : syracuseStep 127093 = 11915) (by norm_num)
theorem B258173 : Blo 111784 258173 := bbase (se 3 (by rfl) ⟨48407, by rfl⟩ : syracuseStep 258173 = 96815) (by norm_num)
theorem B127129 : Blo 111784 127129 := bbase (se 2 (by rfl) ⟨47673, by rfl⟩ : syracuseStep 127129 = 95347) (by norm_num)
theorem B389285 : Blo 111784 389285 := bbase (se 4 (by rfl) ⟨36495, by rfl⟩ : syracuseStep 389285 = 72991) (by norm_num)
theorem B192685 : Blo 111784 192685 := bbase (se 3 (by rfl) ⟨36128, by rfl⟩ : syracuseStep 192685 = 72257) (by norm_num)
theorem B749749 : Blo 111784 749749 := bbase (se 5 (by rfl) ⟨35144, by rfl⟩ : syracuseStep 749749 = 70289) (by norm_num)
theorem B127165 : Blo 111784 127165 := bbase (se 3 (by rfl) ⟨23843, by rfl⟩ : syracuseStep 127165 = 47687) (by norm_num)
theorem B258245 : Blo 111784 258245 := bbase (se 4 (by rfl) ⟨24210, by rfl⟩ : syracuseStep 258245 = 48421) (by norm_num)
theorem B127201 : Blo 111784 127201 := bbase (se 2 (by rfl) ⟨47700, by rfl⟩ : syracuseStep 127201 = 95401) (by norm_num)
theorem B323813 : Blo 111784 323813 := bbase (se 4 (by rfl) ⟨30357, by rfl⟩ : syracuseStep 323813 = 60715) (by norm_num)
theorem B291053 : Blo 111784 291053 := bbase (se 3 (by rfl) ⟨54572, by rfl⟩ : syracuseStep 291053 = 109145) (by norm_num)
theorem B127237 : Blo 111784 127237 := bbase (se 4 (by rfl) ⟨11928, by rfl⟩ : syracuseStep 127237 = 23857) (by norm_num)
theorem B192773 : Blo 111784 192773 := bbase (se 4 (by rfl) ⟨18072, by rfl⟩ : syracuseStep 192773 = 36145) (by norm_num)
theorem B258317 : Blo 111784 258317 := bbase (se 3 (by rfl) ⟨48434, by rfl⟩ : syracuseStep 258317 = 96869) (by norm_num)
theorem B127273 : Blo 111784 127273 := bbase (se 2 (by rfl) ⟨47727, by rfl⟩ : syracuseStep 127273 = 95455) (by norm_num)
theorem B160061 : Blo 111784 160061 := bbase (se 3 (by rfl) ⟨30011, by rfl⟩ : syracuseStep 160061 = 60023) (by norm_num)
theorem B127309 : Blo 111784 127309 := bbase (se 3 (by rfl) ⟨23870, by rfl⟩ : syracuseStep 127309 = 47741) (by norm_num)
theorem B258389 : Blo 111784 258389 := bbase (se 10 (by rfl) ⟨378, by rfl⟩ : syracuseStep 258389 = 757) (by norm_num)
theorem B127345 : Blo 111784 127345 := bbase (se 2 (by rfl) ⟨47754, by rfl⟩ : syracuseStep 127345 = 95509) (by norm_num)
theorem B192901 : Blo 111784 192901 := bbase (se 4 (by rfl) ⟨18084, by rfl⟩ : syracuseStep 192901 = 36169) (by norm_num)
theorem B127381 : Blo 111784 127381 := bbase (se 6 (by rfl) ⟨2985, by rfl⟩ : syracuseStep 127381 = 5971) (by norm_num)
theorem B258461 : Blo 111784 258461 := bbase (se 3 (by rfl) ⟨48461, by rfl⟩ : syracuseStep 258461 = 96923) (by norm_num)
theorem B127417 : Blo 111784 127417 := bbase (se 2 (by rfl) ⟨47781, by rfl⟩ : syracuseStep 127417 = 95563) (by norm_num)
theorem B127453 : Blo 111784 127453 := bbase (se 3 (by rfl) ⟨23897, by rfl⟩ : syracuseStep 127453 = 47795) (by norm_num)
theorem B192989 : Blo 111784 192989 := bbase (se 3 (by rfl) ⟨36185, by rfl⟩ : syracuseStep 192989 = 72371) (by norm_num)
theorem B258533 : Blo 111784 258533 := bbase (se 4 (by rfl) ⟨24237, by rfl⟩ : syracuseStep 258533 = 48475) (by norm_num)
theorem B127489 : Blo 111784 127489 := bbase (se 2 (by rfl) ⟨47808, by rfl⟩ : syracuseStep 127489 = 95617) (by norm_num)
theorem B127525 : Blo 111784 127525 := bbase (se 4 (by rfl) ⟨11955, by rfl⟩ : syracuseStep 127525 = 23911) (by norm_num)
theorem B258605 : Blo 111784 258605 := bbase (se 3 (by rfl) ⟨48488, by rfl⟩ : syracuseStep 258605 = 96977) (by norm_num)
theorem B193085 : Blo 111784 193085 := bbase (se 3 (by rfl) ⟨36203, by rfl⟩ : syracuseStep 193085 = 72407) (by norm_num)
theorem B291397 : Blo 111784 291397 := bbase (se 4 (by rfl) ⟨27318, by rfl⟩ : syracuseStep 291397 = 54637) (by norm_num)
theorem B127561 : Blo 111784 127561 := bbase (se 2 (by rfl) ⟨47835, by rfl⟩ : syracuseStep 127561 = 95671) (by norm_num)
theorem B389717 : Blo 111784 389717 := bbase (se 8 (by rfl) ⟨2283, by rfl⟩ : syracuseStep 389717 = 4567) (by norm_num)
theorem B193117 : Blo 111784 193117 := bbase (se 3 (by rfl) ⟨36209, by rfl⟩ : syracuseStep 193117 = 72419) (by norm_num)
theorem B127597 : Blo 111784 127597 := bbase (se 3 (by rfl) ⟨23924, by rfl⟩ : syracuseStep 127597 = 47849) (by norm_num)
theorem B258677 : Blo 111784 258677 := bbase (se 5 (by rfl) ⟨12125, by rfl⟩ : syracuseStep 258677 = 24251) (by norm_num)
theorem B127633 : Blo 111784 127633 := bbase (se 2 (by rfl) ⟨47862, by rfl⟩ : syracuseStep 127633 = 95725) (by norm_num)
theorem B127637 : Blo 111784 127637 := bbase (se 6 (by rfl) ⟨2991, by rfl⟩ : syracuseStep 127637 = 5983) (by norm_num)
theorem B127669 : Blo 111784 127669 := bbase (se 5 (by rfl) ⟨5984, by rfl⟩ : syracuseStep 127669 = 11969) (by norm_num)
theorem B193205 : Blo 111784 193205 := bbase (se 5 (by rfl) ⟨9056, by rfl⟩ : syracuseStep 193205 = 18113) (by norm_num)
theorem B291509 : Blo 111784 291509 := bbase (se 5 (by rfl) ⟨13664, by rfl⟩ : syracuseStep 291509 = 27329) (by norm_num)
theorem B258749 : Blo 111784 258749 := bbase (se 3 (by rfl) ⟨48515, by rfl⟩ : syracuseStep 258749 = 97031) (by norm_num)
theorem B127693 : Blo 111784 127693 := bbase (se 3 (by rfl) ⟨23942, by rfl⟩ : syracuseStep 127693 = 47885) (by norm_num)
theorem B127705 : Blo 111784 127705 := bbase (se 2 (by rfl) ⟨47889, by rfl⟩ : syracuseStep 127705 = 95779) (by norm_num)
theorem B127741 : Blo 111784 127741 := bbase (se 3 (by rfl) ⟨23951, by rfl⟩ : syracuseStep 127741 = 47903) (by norm_num)
theorem B258821 : Blo 111784 258821 := bbase (se 4 (by rfl) ⟨24264, by rfl⟩ : syracuseStep 258821 = 48529) (by norm_num)
theorem B127777 : Blo 111784 127777 := bbase (se 2 (by rfl) ⟨47916, by rfl⟩ : syracuseStep 127777 = 95833) (by norm_num)
theorem B193333 : Blo 111784 193333 := bbase (se 5 (by rfl) ⟨9062, by rfl⟩ : syracuseStep 193333 = 18125) (by norm_num)
theorem B127813 : Blo 111784 127813 := bbase (se 4 (by rfl) ⟨11982, by rfl⟩ : syracuseStep 127813 = 23965) (by norm_num)
theorem B258893 : Blo 111784 258893 := bbase (se 3 (by rfl) ⟨48542, by rfl⟩ : syracuseStep 258893 = 97085) (by norm_num)
theorem B127849 : Blo 111784 127849 := bbase (se 2 (by rfl) ⟨47943, by rfl⟩ : syracuseStep 127849 = 95887) (by norm_num)
theorem B291701 : Blo 111784 291701 := bbase (se 5 (by rfl) ⟨13673, by rfl⟩ : syracuseStep 291701 = 27347) (by norm_num)
theorem B127885 : Blo 111784 127885 := bbase (se 3 (by rfl) ⟨23978, by rfl⟩ : syracuseStep 127885 = 47957) (by norm_num)
theorem B193421 : Blo 111784 193421 := bbase (se 3 (by rfl) ⟨36266, by rfl⟩ : syracuseStep 193421 = 72533) (by norm_num)
theorem B258965 : Blo 111784 258965 := bbase (se 6 (by rfl) ⟨6069, by rfl⟩ : syracuseStep 258965 = 12139) (by norm_num)
theorem B127921 : Blo 111784 127921 := bbase (se 2 (by rfl) ⟨47970, by rfl⟩ : syracuseStep 127921 = 95941) (by norm_num)
theorem B127957 : Blo 111784 127957 := bbase (se 7 (by rfl) ⟨1499, by rfl⟩ : syracuseStep 127957 = 2999) (by norm_num)
theorem B259037 : Blo 111784 259037 := bbase (se 3 (by rfl) ⟨48569, by rfl⟩ : syracuseStep 259037 = 97139) (by norm_num)
theorem B127985 : Blo 111784 127985 := bbase (se 2 (by rfl) ⟨47994, by rfl⟩ : syracuseStep 127985 = 95989) (by norm_num)
theorem B127993 : Blo 111784 127993 := bbase (se 2 (by rfl) ⟨47997, by rfl⟩ : syracuseStep 127993 = 95995) (by norm_num)
theorem B390149 : Blo 111784 390149 := bbase (se 4 (by rfl) ⟨36576, by rfl⟩ : syracuseStep 390149 = 73153) (by norm_num)
theorem B193549 : Blo 111784 193549 := bbase (se 3 (by rfl) ⟨36290, by rfl⟩ : syracuseStep 193549 = 72581) (by norm_num)
theorem B128029 : Blo 111784 128029 := bbase (se 3 (by rfl) ⟨24005, by rfl⟩ : syracuseStep 128029 = 48011) (by norm_num)
theorem B259109 : Blo 111784 259109 := bbase (se 4 (by rfl) ⟨24291, by rfl⟩ : syracuseStep 259109 = 48583) (by norm_num)
theorem B160813 : Blo 111784 160813 := bbase (se 3 (by rfl) ⟨30152, by rfl⟩ : syracuseStep 160813 = 60305) (by norm_num)
theorem B128065 : Blo 111784 128065 := bbase (se 2 (by rfl) ⟨48024, by rfl⟩ : syracuseStep 128065 = 96049) (by norm_num)
theorem B128101 : Blo 111784 128101 := bbase (se 4 (by rfl) ⟨12009, by rfl⟩ : syracuseStep 128101 = 24019) (by norm_num)
theorem B193637 : Blo 111784 193637 := bbase (se 4 (by rfl) ⟨18153, by rfl⟩ : syracuseStep 193637 = 36307) (by norm_num)
theorem B259181 : Blo 111784 259181 := bbase (se 3 (by rfl) ⟨48596, by rfl⟩ : syracuseStep 259181 = 97193) (by norm_num)
theorem B128137 : Blo 111784 128137 := bbase (se 2 (by rfl) ⟨48051, by rfl⟩ : syracuseStep 128137 = 96103) (by norm_num)
theorem B128173 : Blo 111784 128173 := bbase (se 3 (by rfl) ⟨24032, by rfl⟩ : syracuseStep 128173 = 48065) (by norm_num)
theorem B259253 : Blo 111784 259253 := bbase (se 5 (by rfl) ⟨12152, by rfl⟩ : syracuseStep 259253 = 24305) (by norm_num)
theorem B292045 : Blo 111784 292045 := bbase (se 3 (by rfl) ⟨54758, by rfl⟩ : syracuseStep 292045 = 109517) (by norm_num)
theorem B128209 : Blo 111784 128209 := bbase (se 2 (by rfl) ⟨48078, by rfl⟩ : syracuseStep 128209 = 96157) (by norm_num)
theorem B193765 : Blo 111784 193765 := bbase (se 4 (by rfl) ⟨18165, by rfl⟩ : syracuseStep 193765 = 36331) (by norm_num)
theorem B128245 : Blo 111784 128245 := bbase (se 5 (by rfl) ⟨6011, by rfl⟩ : syracuseStep 128245 = 12023) (by norm_num)
theorem B488693 : Blo 111784 488693 := bbase (se 5 (by rfl) ⟨22907, by rfl⟩ : syracuseStep 488693 = 45815) (by norm_num)
theorem B259325 : Blo 111784 259325 := bbase (se 3 (by rfl) ⟨48623, by rfl⟩ : syracuseStep 259325 = 97247) (by norm_num)
theorem B128281 : Blo 111784 128281 := bbase (se 2 (by rfl) ⟨48105, by rfl⟩ : syracuseStep 128281 = 96211) (by norm_num)
theorem B128317 : Blo 111784 128317 := bbase (se 3 (by rfl) ⟨24059, by rfl⟩ : syracuseStep 128317 = 48119) (by norm_num)
theorem B193853 : Blo 111784 193853 := bbase (se 3 (by rfl) ⟨36347, by rfl⟩ : syracuseStep 193853 = 72695) (by norm_num)
theorem B292157 : Blo 111784 292157 := bbase (se 3 (by rfl) ⟨54779, by rfl⟩ : syracuseStep 292157 = 109559) (by norm_num)
theorem B259397 : Blo 111784 259397 := bbase (se 4 (by rfl) ⟨24318, by rfl⟩ : syracuseStep 259397 = 48637) (by norm_num)
theorem B128353 : Blo 111784 128353 := bbase (se 2 (by rfl) ⟨48132, by rfl⟩ : syracuseStep 128353 = 96265) (by norm_num)
theorem B128389 : Blo 111784 128389 := bbase (se 4 (by rfl) ⟨12036, by rfl⟩ : syracuseStep 128389 = 24073) (by norm_num)
theorem B259469 : Blo 111784 259469 := bbase (se 3 (by rfl) ⟨48650, by rfl⟩ : syracuseStep 259469 = 97301) (by norm_num)
theorem B128425 : Blo 111784 128425 := bbase (se 2 (by rfl) ⟨48159, by rfl⟩ : syracuseStep 128425 = 96319) (by norm_num)
theorem B390581 : Blo 111784 390581 := bbase (se 5 (by rfl) ⟨18308, by rfl⟩ : syracuseStep 390581 = 36617) (by norm_num)
theorem B193981 : Blo 111784 193981 := bbase (se 3 (by rfl) ⟨36371, by rfl⟩ : syracuseStep 193981 = 72743) (by norm_num)
theorem B128461 : Blo 111784 128461 := bbase (se 3 (by rfl) ⟨24086, by rfl⟩ : syracuseStep 128461 = 48173) (by norm_num)
theorem B259541 : Blo 111784 259541 := bbase (se 7 (by rfl) ⟨3041, by rfl⟩ : syracuseStep 259541 = 6083) (by norm_num)
theorem B128497 : Blo 111784 128497 := bbase (se 2 (by rfl) ⟨48186, by rfl⟩ : syracuseStep 128497 = 96373) (by norm_num)
theorem B292349 : Blo 111784 292349 := bbase (se 3 (by rfl) ⟨54815, by rfl⟩ : syracuseStep 292349 = 109631) (by norm_num)
theorem B128533 : Blo 111784 128533 := bbase (se 6 (by rfl) ⟨3012, by rfl⟩ : syracuseStep 128533 = 6025) (by norm_num)
theorem B194069 : Blo 111784 194069 := bbase (se 6 (by rfl) ⟨4548, by rfl⟩ : syracuseStep 194069 = 9097) (by norm_num)
theorem B259613 : Blo 111784 259613 := bbase (se 3 (by rfl) ⟨48677, by rfl⟩ : syracuseStep 259613 = 97355) (by norm_num)
theorem B128569 : Blo 111784 128569 := bbase (se 2 (by rfl) ⟨48213, by rfl⟩ : syracuseStep 128569 = 96427) (by norm_num)
theorem B128605 : Blo 111784 128605 := bbase (se 3 (by rfl) ⟨24113, by rfl⟩ : syracuseStep 128605 = 48227) (by norm_num)
theorem B259685 : Blo 111784 259685 := bbase (se 4 (by rfl) ⟨24345, by rfl⟩ : syracuseStep 259685 = 48691) (by norm_num)
theorem B128641 : Blo 111784 128641 := bbase (se 2 (by rfl) ⟨48240, by rfl⟩ : syracuseStep 128641 = 96481) (by norm_num)
theorem B194197 : Blo 111784 194197 := bbase (se 6 (by rfl) ⟨4551, by rfl⟩ : syracuseStep 194197 = 9103) (by norm_num)
theorem B128677 : Blo 111784 128677 := bbase (se 4 (by rfl) ⟨12063, by rfl⟩ : syracuseStep 128677 = 24127) (by norm_num)
theorem B259757 : Blo 111784 259757 := bbase (se 3 (by rfl) ⟨48704, by rfl⟩ : syracuseStep 259757 = 97409) (by norm_num)
theorem B128713 : Blo 111784 128713 := bbase (se 2 (by rfl) ⟨48267, by rfl⟩ : syracuseStep 128713 = 96535) (by norm_num)
theorem B128749 : Blo 111784 128749 := bbase (se 3 (by rfl) ⟨24140, by rfl⟩ : syracuseStep 128749 = 48281) (by norm_num)
theorem B194285 : Blo 111784 194285 := bbase (se 3 (by rfl) ⟨36428, by rfl⟩ : syracuseStep 194285 = 72857) (by norm_num)
theorem B259829 : Blo 111784 259829 := bbase (se 5 (by rfl) ⟨12179, by rfl⟩ : syracuseStep 259829 = 24359) (by norm_num)
theorem B128785 : Blo 111784 128785 := bbase (se 2 (by rfl) ⟨48294, by rfl⟩ : syracuseStep 128785 = 96589) (by norm_num)
theorem B325397 : Blo 111784 325397 := bbase (se 6 (by rfl) ⟨7626, by rfl⟩ : syracuseStep 325397 = 15253) (by norm_num)
theorem B128821 : Blo 111784 128821 := bbase (se 5 (by rfl) ⟨6038, by rfl⟩ : syracuseStep 128821 = 12077) (by norm_num)
theorem B259901 : Blo 111784 259901 := bbase (se 3 (by rfl) ⟨48731, by rfl⟩ : syracuseStep 259901 = 97463) (by norm_num)
theorem B161605 : Blo 111784 161605 := bbase (se 4 (by rfl) ⟨15150, by rfl⟩ : syracuseStep 161605 = 30301) (by norm_num)
theorem B292693 : Blo 111784 292693 := bbase (se 9 (by rfl) ⟨857, by rfl⟩ : syracuseStep 292693 = 1715) (by norm_num)
theorem B128857 : Blo 111784 128857 := bbase (se 2 (by rfl) ⟨48321, by rfl⟩ : syracuseStep 128857 = 96643) (by norm_num)
theorem B194413 : Blo 111784 194413 := bbase (se 3 (by rfl) ⟨36452, by rfl⟩ : syracuseStep 194413 = 72905) (by norm_num)
theorem B128893 : Blo 111784 128893 := bbase (se 3 (by rfl) ⟨24167, by rfl⟩ : syracuseStep 128893 = 48335) (by norm_num)
theorem B259973 : Blo 111784 259973 := bbase (se 4 (by rfl) ⟨24372, by rfl⟩ : syracuseStep 259973 = 48745) (by norm_num)
theorem B1963925 : Blo 111784 1963925 := bbase (se 6 (by rfl) ⟨46029, by rfl⟩ : syracuseStep 1963925 = 92059) (by norm_num)
theorem B128929 : Blo 111784 128929 := bbase (se 2 (by rfl) ⟨48348, by rfl⟩ : syracuseStep 128929 = 96697) (by norm_num)
theorem B128965 : Blo 111784 128965 := bbase (se 4 (by rfl) ⟨12090, by rfl⟩ : syracuseStep 128965 = 24181) (by norm_num)
theorem B194501 : Blo 111784 194501 := bbase (se 4 (by rfl) ⟨18234, by rfl⟩ : syracuseStep 194501 = 36469) (by norm_num)
theorem B292805 : Blo 111784 292805 := bbase (se 4 (by rfl) ⟨27450, by rfl⟩ : syracuseStep 292805 = 54901) (by norm_num)
theorem B260045 : Blo 111784 260045 := bbase (se 3 (by rfl) ⟨48758, by rfl⟩ : syracuseStep 260045 = 97517) (by norm_num)
theorem B129001 : Blo 111784 129001 := bbase (se 2 (by rfl) ⟨48375, by rfl⟩ : syracuseStep 129001 = 96751) (by norm_num)
theorem B129037 : Blo 111784 129037 := bbase (se 3 (by rfl) ⟨24194, by rfl⟩ : syracuseStep 129037 = 48389) (by norm_num)
theorem B260117 : Blo 111784 260117 := bbase (se 6 (by rfl) ⟨6096, by rfl⟩ : syracuseStep 260117 = 12193) (by norm_num)
theorem B129073 : Blo 111784 129073 := bbase (se 2 (by rfl) ⟨48402, by rfl⟩ : syracuseStep 129073 = 96805) (by norm_num)
theorem B194629 : Blo 111784 194629 := bbase (se 4 (by rfl) ⟨18246, by rfl⟩ : syracuseStep 194629 = 36493) (by norm_num)
theorem B129109 : Blo 111784 129109 := bbase (se 8 (by rfl) ⟨756, by rfl⟩ : syracuseStep 129109 = 1513) (by norm_num)
theorem B260189 : Blo 111784 260189 := bbase (se 3 (by rfl) ⟨48785, by rfl⟩ : syracuseStep 260189 = 97571) (by norm_num)
theorem B129145 : Blo 111784 129145 := bbase (se 2 (by rfl) ⟨48429, by rfl⟩ : syracuseStep 129145 = 96859) (by norm_num)
theorem B292997 : Blo 111784 292997 := bbase (se 4 (by rfl) ⟨27468, by rfl⟩ : syracuseStep 292997 = 54937) (by norm_num)
theorem B161941 : Blo 111784 161941 := bbase (se 6 (by rfl) ⟨3795, by rfl⟩ : syracuseStep 161941 = 7591) (by norm_num)
theorem B129181 : Blo 111784 129181 := bbase (se 3 (by rfl) ⟨24221, by rfl⟩ : syracuseStep 129181 = 48443) (by norm_num)
theorem B194717 : Blo 111784 194717 := bbase (se 3 (by rfl) ⟨36509, by rfl⟩ : syracuseStep 194717 = 73019) (by norm_num)
theorem B260261 : Blo 111784 260261 := bbase (se 4 (by rfl) ⟨24399, by rfl⟩ : syracuseStep 260261 = 48799) (by norm_num)
theorem B129217 : Blo 111784 129217 := bbase (se 2 (by rfl) ⟨48456, by rfl⟩ : syracuseStep 129217 = 96913) (by norm_num)
theorem B129253 : Blo 111784 129253 := bbase (se 4 (by rfl) ⟨12117, by rfl⟩ : syracuseStep 129253 = 24235) (by norm_num)
theorem B260333 : Blo 111784 260333 := bbase (se 3 (by rfl) ⟨48812, by rfl⟩ : syracuseStep 260333 = 97625) (by norm_num)
theorem B129289 : Blo 111784 129289 := bbase (se 2 (by rfl) ⟨48483, by rfl⟩ : syracuseStep 129289 = 96967) (by norm_num)
theorem B194845 : Blo 111784 194845 := bbase (se 3 (by rfl) ⟨36533, by rfl⟩ : syracuseStep 194845 = 73067) (by norm_num)
theorem B129325 : Blo 111784 129325 := bbase (se 3 (by rfl) ⟨24248, by rfl⟩ : syracuseStep 129325 = 48497) (by norm_num)
theorem B260405 : Blo 111784 260405 := bbase (se 5 (by rfl) ⟨12206, by rfl⟩ : syracuseStep 260405 = 24413) (by norm_num)
theorem B129361 : Blo 111784 129361 := bbase (se 2 (by rfl) ⟨48510, by rfl⟩ : syracuseStep 129361 = 97021) (by norm_num)
theorem B162157 : Blo 111784 162157 := bbase (se 3 (by rfl) ⟨30404, by rfl⟩ : syracuseStep 162157 = 60809) (by norm_num)
theorem B129397 : Blo 111784 129397 := bbase (se 5 (by rfl) ⟨6065, by rfl⟩ : syracuseStep 129397 = 12131) (by norm_num)
theorem B194933 : Blo 111784 194933 := bbase (se 5 (by rfl) ⟨9137, by rfl⟩ : syracuseStep 194933 = 18275) (by norm_num)
theorem B260477 : Blo 111784 260477 := bbase (se 3 (by rfl) ⟨48839, by rfl⟩ : syracuseStep 260477 = 97679) (by norm_num)
theorem B358805 : Blo 111784 358805 := bbase (se 6 (by rfl) ⟨8409, by rfl⟩ : syracuseStep 358805 = 16819) (by norm_num)
theorem B129433 : Blo 111784 129433 := bbase (se 2 (by rfl) ⟨48537, by rfl⟩ : syracuseStep 129433 = 97075) (by norm_num)
theorem B326069 : Blo 111784 326069 := bbase (se 5 (by rfl) ⟨15284, by rfl⟩ : syracuseStep 326069 = 30569) (by norm_num)
theorem B129469 : Blo 111784 129469 := bbase (se 3 (by rfl) ⟨24275, by rfl⟩ : syracuseStep 129469 = 48551) (by norm_num)
theorem B129505 : Blo 111784 129505 := bbase (se 2 (by rfl) ⟨48564, by rfl⟩ : syracuseStep 129505 = 97129) (by norm_num)
theorem B195061 : Blo 111784 195061 := bbase (se 5 (by rfl) ⟨9143, by rfl⟩ : syracuseStep 195061 = 18287) (by norm_num)
theorem B129541 : Blo 111784 129541 := bbase (se 4 (by rfl) ⟨12144, by rfl⟩ : syracuseStep 129541 = 24289) (by norm_num)
theorem B129577 : Blo 111784 129577 := bbase (se 2 (by rfl) ⟨48591, by rfl⟩ : syracuseStep 129577 = 97183) (by norm_num)
theorem B129613 : Blo 111784 129613 := bbase (se 3 (by rfl) ⟨24302, by rfl⟩ : syracuseStep 129613 = 48605) (by norm_num)
theorem B195149 : Blo 111784 195149 := bbase (se 3 (by rfl) ⟨36590, by rfl⟩ : syracuseStep 195149 = 73181) (by norm_num)
theorem B260693 : Blo 111784 260693 := bbase (se 8 (by rfl) ⟨1527, by rfl⟩ : syracuseStep 260693 = 3055) (by norm_num)
theorem B129649 : Blo 111784 129649 := bbase (se 2 (by rfl) ⟨48618, by rfl⟩ : syracuseStep 129649 = 97237) (by norm_num)
theorem B129685 : Blo 111784 129685 := bbase (se 6 (by rfl) ⟨3039, by rfl⟩ : syracuseStep 129685 = 6079) (by norm_num)
theorem B129721 : Blo 111784 129721 := bbase (se 2 (by rfl) ⟨48645, by rfl⟩ : syracuseStep 129721 = 97291) (by norm_num)
theorem B195277 : Blo 111784 195277 := bbase (se 3 (by rfl) ⟨36614, by rfl⟩ : syracuseStep 195277 = 73229) (by norm_num)
theorem B129745 : Blo 111784 129745 := bbase (se 2 (by rfl) ⟨48654, by rfl⟩ : syracuseStep 129745 = 97309) (by norm_num)
theorem B129757 : Blo 111784 129757 := bbase (se 3 (by rfl) ⟨24329, by rfl⟩ : syracuseStep 129757 = 48659) (by norm_num)
theorem B162533 : Blo 111784 162533 := bbase (se 4 (by rfl) ⟨15237, by rfl⟩ : syracuseStep 162533 = 30475) (by norm_num)
theorem B129793 : Blo 111784 129793 := bbase (se 2 (by rfl) ⟨48672, by rfl⟩ : syracuseStep 129793 = 97345) (by norm_num)
theorem B129829 : Blo 111784 129829 := bbase (se 4 (by rfl) ⟨12171, by rfl⟩ : syracuseStep 129829 = 24343) (by norm_num)
theorem B195365 : Blo 111784 195365 := bbase (se 4 (by rfl) ⟨18315, by rfl⟩ : syracuseStep 195365 = 36631) (by norm_num)
theorem B129865 : Blo 111784 129865 := bbase (se 2 (by rfl) ⟨48699, by rfl⟩ : syracuseStep 129865 = 97399) (by norm_num)
theorem B326501 : Blo 111784 326501 := bbase (se 4 (by rfl) ⟨30609, by rfl⟩ : syracuseStep 326501 = 61219) (by norm_num)
theorem B129901 : Blo 111784 129901 := bbase (se 3 (by rfl) ⟨24356, by rfl⟩ : syracuseStep 129901 = 48713) (by norm_num)
theorem B555893 : Blo 111784 555893 := bbase (se 5 (by rfl) ⟨26057, by rfl⟩ : syracuseStep 555893 = 52115) (by norm_num)
theorem B129937 : Blo 111784 129937 := bbase (se 2 (by rfl) ⟨48726, by rfl⟩ : syracuseStep 129937 = 97453) (by norm_num)
theorem B719765 : Blo 111784 719765 := bbase (se 6 (by rfl) ⟨16869, by rfl⟩ : syracuseStep 719765 = 33739) (by norm_num)
theorem B424885 : Blo 111784 424885 := bbase (se 5 (by rfl) ⟨19916, by rfl⟩ : syracuseStep 424885 = 39833) (by norm_num)
theorem B129973 : Blo 111784 129973 := bbase (se 5 (by rfl) ⟨6092, by rfl⟩ : syracuseStep 129973 = 12185) (by norm_num)
theorem B130009 : Blo 111784 130009 := bbase (se 2 (by rfl) ⟨48753, by rfl⟩ : syracuseStep 130009 = 97507) (by norm_num)
theorem B130045 : Blo 111784 130045 := bbase (se 3 (by rfl) ⟨24383, by rfl⟩ : syracuseStep 130045 = 48767) (by norm_num)
theorem B457733 : Blo 111784 457733 := bbase (se 4 (by rfl) ⟨42912, by rfl⟩ : syracuseStep 457733 = 85825) (by norm_num)
theorem B130081 : Blo 111784 130081 := bbase (se 2 (by rfl) ⟨48780, by rfl⟩ : syracuseStep 130081 = 97561) (by norm_num)
theorem B228413 : Blo 111784 228413 := bbase (se 3 (by rfl) ⟨42827, by rfl⟩ : syracuseStep 228413 = 85655) (by norm_num)
theorem B130117 : Blo 111784 130117 := bbase (se 4 (by rfl) ⟨12198, by rfl⟩ : syracuseStep 130117 = 24397) (by norm_num)
theorem B130153 : Blo 111784 130153 := bbase (se 2 (by rfl) ⟨48807, by rfl⟩ : syracuseStep 130153 = 97615) (by norm_num)
theorem B130189 : Blo 111784 130189 := bbase (se 3 (by rfl) ⟨24410, by rfl⟩ : syracuseStep 130189 = 48821) (by norm_num)
theorem B130225 : Blo 111784 130225 := bbase (se 2 (by rfl) ⟨48834, by rfl⟩ : syracuseStep 130225 = 97669) (by norm_num)
theorem B425189 : Blo 111784 425189 := bbase (se 4 (by rfl) ⟨39861, by rfl⟩ : syracuseStep 425189 = 79723) (by norm_num)
theorem B2227733 : Blo 111784 2227733 := bbase (se 6 (by rfl) ⟨52212, by rfl⟩ : syracuseStep 2227733 = 104425) (by norm_num)
theorem B327253 : Blo 111784 327253 := bbase (se 8 (by rfl) ⟨1917, by rfl⟩ : syracuseStep 327253 = 3835) (by norm_num)
theorem B229085 : Blo 111784 229085 := bbase (se 3 (by rfl) ⟨42953, by rfl⟩ : syracuseStep 229085 = 85907) (by norm_num)
theorem B556949 : Blo 111784 556949 := bbase (se 6 (by rfl) ⟨13053, by rfl⟩ : syracuseStep 556949 = 26107) (by norm_num)
theorem B131041 : Blo 111784 131041 := bbase (se 2 (by rfl) ⟨49140, by rfl⟩ : syracuseStep 131041 = 98281) (by norm_num)
theorem B196589 : Blo 111784 196589 := bbase (se 3 (by rfl) ⟨36860, by rfl⟩ : syracuseStep 196589 = 73721) (by norm_num)
theorem B851957 : Blo 111784 851957 := bbase (se 5 (by rfl) ⟨39935, by rfl⟩ : syracuseStep 851957 = 79871) (by norm_num)
theorem B163829 : Blo 111784 163829 := bbase (se 5 (by rfl) ⟨7679, by rfl⟩ : syracuseStep 163829 = 15359) (by norm_num)
theorem B426161 : Blo 111784 426161 := bstep (se 2 (by rfl) ⟨159810, by rfl⟩ : syracuseStep 426161 = 319621) B319621
theorem B3080389 : Blo 111784 3080389 := bstep (se 4 (by rfl) ⟨288786, by rfl⟩ : syracuseStep 3080389 = 577573) B577573
theorem B1474757 : Blo 111784 1474757 := bstep (se 4 (by rfl) ⟨138258, by rfl⟩ : syracuseStep 1474757 = 276517) B276517
theorem B360845 : Blo 111784 360845 := bstep (se 3 (by rfl) ⟨67658, by rfl⟩ : syracuseStep 360845 = 135317) B135317
theorem B491939 : Blo 111784 491939 := bstep (se 1 (by rfl) ⟨368954, by rfl⟩ : syracuseStep 491939 = 737909) B737909
theorem B164273 : Blo 111784 164273 := bstep (se 2 (by rfl) ⟨61602, by rfl⟩ : syracuseStep 164273 = 123205) B123205
theorem B623045 : Blo 111784 623045 := bstep (se 4 (by rfl) ⟨58410, by rfl⟩ : syracuseStep 623045 = 116821) B116821
theorem B328141 : Blo 111784 328141 := bstep (se 3 (by rfl) ⟨61526, by rfl⟩ : syracuseStep 328141 = 123053) B123053
theorem B164435 : Blo 111784 164435 := bstep (se 1 (by rfl) ⟨123326, by rfl⟩ : syracuseStep 164435 = 246653) B246653
theorem B328369 : Blo 111784 328369 := bstep (se 2 (by rfl) ⟨123138, by rfl⟩ : syracuseStep 328369 = 246277) B246277
theorem B361265 : Blo 111784 361265 := bstep (se 2 (by rfl) ⟨135474, by rfl⟩ : syracuseStep 361265 = 270949) B270949
theorem B426829 : Blo 111784 426829 := bstep (se 3 (by rfl) ⟨80030, by rfl⟩ : syracuseStep 426829 = 160061) B160061
theorem B328529 : Blo 111784 328529 := bstep (se 2 (by rfl) ⟨123198, by rfl⟩ : syracuseStep 328529 = 246397) B246397
theorem B656261 : Blo 111784 656261 := bstep (se 4 (by rfl) ⟨61524, by rfl⟩ : syracuseStep 656261 = 123049) B123049
theorem B328643 : Blo 111784 328643 := bstep (se 1 (by rfl) ⟨246482, by rfl⟩ : syracuseStep 328643 = 492965) B492965
theorem B623629 : Blo 111784 623629 := bstep (se 3 (by rfl) ⟨116930, by rfl⟩ : syracuseStep 623629 = 233861) B233861
theorem B4949045 : Blo 111784 4949045 := bstep (se 5 (by rfl) ⟨231986, by rfl⟩ : syracuseStep 4949045 = 463973) B463973
theorem B427619 : Blo 111784 427619 := bstep (se 1 (by rfl) ⟨320714, by rfl⟩ : syracuseStep 427619 = 641429) B641429
theorem B689905 : Blo 111784 689905 := bstep (se 2 (by rfl) ⟨258714, by rfl⟩ : syracuseStep 689905 = 517429) B517429
theorem B853901 : Blo 111784 853901 := bstep (se 3 (by rfl) ⟨160106, by rfl⟩ : syracuseStep 853901 = 320213) B320213
theorem B329645 : Blo 111784 329645 := bstep (se 3 (by rfl) ⟨61808, by rfl⟩ : syracuseStep 329645 = 123617) B123617
theorem B460849 : Blo 111784 460849 := bstep (se 2 (by rfl) ⟨172818, by rfl⟩ : syracuseStep 460849 = 345637) B345637
theorem B1378403 : Blo 111784 1378403 := bstep (se 1 (by rfl) ⟨1033802, by rfl⟩ : syracuseStep 1378403 = 2067605) B2067605
theorem B231587 : Blo 111784 231587 := bstep (se 1 (by rfl) ⟨173690, by rfl⟩ : syracuseStep 231587 = 347381) B347381
theorem B428273 : Blo 111784 428273 := bstep (se 2 (by rfl) ⟨160602, by rfl⟩ : syracuseStep 428273 = 321205) B321205
theorem B919907 : Blo 111784 919907 := bstep (se 1 (by rfl) ⟨689930, by rfl⟩ : syracuseStep 919907 = 1379861) B1379861
theorem B395857 : Blo 111784 395857 := bstep (se 2 (by rfl) ⟨148446, by rfl⟩ : syracuseStep 395857 = 296893) B296893
theorem B723761 : Blo 111784 723761 := bstep (se 2 (by rfl) ⟨271410, by rfl⟩ : syracuseStep 723761 = 542821) B542821
theorem B1576205 : Blo 111784 1576205 := bstep (se 3 (by rfl) ⟨295538, by rfl⟩ : syracuseStep 1576205 = 591077) B591077
theorem B790157 : Blo 111784 790157 := bstep (se 3 (by rfl) ⟨148154, by rfl⟩ : syracuseStep 790157 = 296309) B296309
theorem B429731 : Blo 111784 429731 := bstep (se 1 (by rfl) ⟨322298, by rfl⟩ : syracuseStep 429731 = 644597) B644597
theorem B429745 : Blo 111784 429745 := bstep (se 2 (by rfl) ⟨161154, by rfl⟩ : syracuseStep 429745 = 322309) B322309
theorem B233155 : Blo 111784 233155 := bstep (se 1 (by rfl) ⟨174866, by rfl⟩ : syracuseStep 233155 = 349733) B349733
theorem B659141 : Blo 111784 659141 := bstep (se 4 (by rfl) ⟨61794, by rfl⟩ : syracuseStep 659141 = 123589) B123589
theorem B167681 : Blo 111784 167681 := bstep (se 2 (by rfl) ⟨62880, by rfl⟩ : syracuseStep 167681 = 125761) B125761
theorem B691973 : Blo 111784 691973 := bstep (se 4 (by rfl) ⟨64872, by rfl⟩ : syracuseStep 691973 = 129745) B129745
theorem B167699 : Blo 111784 167699 := bstep (se 1 (by rfl) ⟨125774, by rfl⟩ : syracuseStep 167699 = 251549) B251549
theorem B167729 : Blo 111784 167729 := bstep (se 2 (by rfl) ⟨62898, by rfl⟩ : syracuseStep 167729 = 125797) B125797
theorem B167747 : Blo 111784 167747 := bstep (se 1 (by rfl) ⟨125810, by rfl⟩ : syracuseStep 167747 = 251621) B251621
theorem B167777 : Blo 111784 167777 := bstep (se 2 (by rfl) ⟨62916, by rfl⟩ : syracuseStep 167777 = 125833) B125833
theorem B167795 : Blo 111784 167795 := bstep (se 1 (by rfl) ⟨125846, by rfl⟩ : syracuseStep 167795 = 251693) B251693
theorem B167825 : Blo 111784 167825 := bstep (se 2 (by rfl) ⟨62934, by rfl⟩ : syracuseStep 167825 = 125869) B125869
theorem B167843 : Blo 111784 167843 := bstep (se 1 (by rfl) ⟨125882, by rfl⟩ : syracuseStep 167843 = 251765) B251765
theorem B167873 : Blo 111784 167873 := bstep (se 2 (by rfl) ⟨62952, by rfl⟩ : syracuseStep 167873 = 125905) B125905
theorem B167891 : Blo 111784 167891 := bstep (se 1 (by rfl) ⟨125918, by rfl⟩ : syracuseStep 167891 = 251837) B251837
theorem B167921 : Blo 111784 167921 := bstep (se 2 (by rfl) ⟨62970, by rfl⟩ : syracuseStep 167921 = 125941) B125941
theorem B167939 : Blo 111784 167939 := bstep (se 1 (by rfl) ⟨125954, by rfl⟩ : syracuseStep 167939 = 251909) B251909
theorem B167969 : Blo 111784 167969 := bstep (se 2 (by rfl) ⟨62988, by rfl⟩ : syracuseStep 167969 = 125977) B125977
theorem B167987 : Blo 111784 167987 := bstep (se 1 (by rfl) ⟨125990, by rfl⟩ : syracuseStep 167987 = 251981) B251981
theorem B168017 : Blo 111784 168017 := bstep (se 2 (by rfl) ⟨63006, by rfl⟩ : syracuseStep 168017 = 126013) B126013
theorem B168035 : Blo 111784 168035 := bstep (se 1 (by rfl) ⟨126026, by rfl⟩ : syracuseStep 168035 = 252053) B252053
theorem B135283 : Blo 111784 135283 := bstep (se 1 (by rfl) ⟨101462, by rfl⟩ : syracuseStep 135283 = 202925) B202925
theorem B168065 : Blo 111784 168065 := bstep (se 2 (by rfl) ⟨63024, by rfl⟩ : syracuseStep 168065 = 126049) B126049
theorem B364675 : Blo 111784 364675 := bstep (se 1 (by rfl) ⟨273506, by rfl⟩ : syracuseStep 364675 = 547013) B547013
theorem B168083 : Blo 111784 168083 := bstep (se 1 (by rfl) ⟨126062, by rfl⟩ : syracuseStep 168083 = 252125) B252125
theorem B168113 : Blo 111784 168113 := bstep (se 2 (by rfl) ⟨63042, by rfl⟩ : syracuseStep 168113 = 126085) B126085
theorem B168131 : Blo 111784 168131 := bstep (se 1 (by rfl) ⟨126098, by rfl⟩ : syracuseStep 168131 = 252197) B252197
theorem B135379 : Blo 111784 135379 := bstep (se 1 (by rfl) ⟨101534, by rfl⟩ : syracuseStep 135379 = 203069) B203069
theorem B168161 : Blo 111784 168161 := bstep (se 2 (by rfl) ⟨63060, by rfl⟩ : syracuseStep 168161 = 126121) B126121
theorem B168179 : Blo 111784 168179 := bstep (se 1 (by rfl) ⟨126134, by rfl⟩ : syracuseStep 168179 = 252269) B252269
theorem B168209 : Blo 111784 168209 := bstep (se 2 (by rfl) ⟨63078, by rfl⟩ : syracuseStep 168209 = 126157) B126157
theorem B168227 : Blo 111784 168227 := bstep (se 1 (by rfl) ⟨126170, by rfl⟩ : syracuseStep 168227 = 252341) B252341
theorem B168257 : Blo 111784 168257 := bstep (se 2 (by rfl) ⟨63096, by rfl⟩ : syracuseStep 168257 = 126193) B126193
theorem B168275 : Blo 111784 168275 := bstep (se 1 (by rfl) ⟨126206, by rfl⟩ : syracuseStep 168275 = 252413) B252413
theorem B135523 : Blo 111784 135523 := bstep (se 1 (by rfl) ⟨101642, by rfl⟩ : syracuseStep 135523 = 203285) B203285
theorem B168305 : Blo 111784 168305 := bstep (se 2 (by rfl) ⟨63114, by rfl⟩ : syracuseStep 168305 = 126229) B126229
theorem B168323 : Blo 111784 168323 := bstep (se 1 (by rfl) ⟨126242, by rfl⟩ : syracuseStep 168323 = 252485) B252485
theorem B364945 : Blo 111784 364945 := bstep (se 2 (by rfl) ⟨136854, by rfl⟩ : syracuseStep 364945 = 273709) B273709
theorem B168353 : Blo 111784 168353 := bstep (se 2 (by rfl) ⟨63132, by rfl⟩ : syracuseStep 168353 = 126265) B126265
theorem B430499 : Blo 111784 430499 := bstep (se 1 (by rfl) ⟨322874, by rfl⟩ : syracuseStep 430499 = 645749) B645749
theorem B168371 : Blo 111784 168371 := bstep (se 1 (by rfl) ⟨126278, by rfl⟩ : syracuseStep 168371 = 252557) B252557
theorem B168401 : Blo 111784 168401 := bstep (se 2 (by rfl) ⟨63150, by rfl⟩ : syracuseStep 168401 = 126301) B126301
theorem B168419 : Blo 111784 168419 := bstep (se 1 (by rfl) ⟨126314, by rfl⟩ : syracuseStep 168419 = 252629) B252629
theorem B168449 : Blo 111784 168449 := bstep (se 2 (by rfl) ⟨63168, by rfl⟩ : syracuseStep 168449 = 126337) B126337
theorem B168467 : Blo 111784 168467 := bstep (se 1 (by rfl) ⟨126350, by rfl⟩ : syracuseStep 168467 = 252701) B252701
theorem B168497 : Blo 111784 168497 := bstep (se 2 (by rfl) ⟨63186, by rfl⟩ : syracuseStep 168497 = 126373) B126373
theorem B168515 : Blo 111784 168515 := bstep (se 1 (by rfl) ⟨126386, by rfl⟩ : syracuseStep 168515 = 252773) B252773
theorem B168545 : Blo 111784 168545 := bstep (se 2 (by rfl) ⟨63204, by rfl⟩ : syracuseStep 168545 = 126409) B126409
theorem B561763 : Blo 111784 561763 := bstep (se 1 (by rfl) ⟨421322, by rfl⟩ : syracuseStep 561763 = 842645) B842645
theorem B1053283 : Blo 111784 1053283 := bstep (se 1 (by rfl) ⟨789962, by rfl⟩ : syracuseStep 1053283 = 1579925) B1579925
theorem B168563 : Blo 111784 168563 := bstep (se 1 (by rfl) ⟨126422, by rfl⟩ : syracuseStep 168563 = 252845) B252845
theorem B168593 : Blo 111784 168593 := bstep (se 2 (by rfl) ⟨63222, by rfl⟩ : syracuseStep 168593 = 126445) B126445
theorem B168611 : Blo 111784 168611 := bstep (se 1 (by rfl) ⟨126458, by rfl⟩ : syracuseStep 168611 = 252917) B252917
theorem B168641 : Blo 111784 168641 := bstep (se 2 (by rfl) ⟨63240, by rfl⟩ : syracuseStep 168641 = 126481) B126481
theorem B168659 : Blo 111784 168659 := bstep (se 1 (by rfl) ⟨126494, by rfl⟩ : syracuseStep 168659 = 252989) B252989
theorem B234211 : Blo 111784 234211 := bstep (se 1 (by rfl) ⟨175658, by rfl⟩ : syracuseStep 234211 = 351317) B351317
theorem B168689 : Blo 111784 168689 := bstep (se 2 (by rfl) ⟨63258, by rfl⟩ : syracuseStep 168689 = 126517) B126517
theorem B856817 : Blo 111784 856817 := bstep (se 2 (by rfl) ⟨321306, by rfl⟩ : syracuseStep 856817 = 642613) B642613
theorem B168707 : Blo 111784 168707 := bstep (se 1 (by rfl) ⟨126530, by rfl⟩ : syracuseStep 168707 = 253061) B253061
theorem B168737 : Blo 111784 168737 := bstep (se 2 (by rfl) ⟨63276, by rfl⟩ : syracuseStep 168737 = 126553) B126553
theorem B168755 : Blo 111784 168755 := bstep (se 1 (by rfl) ⟨126566, by rfl⟩ : syracuseStep 168755 = 253133) B253133
theorem B2495285 : Blo 111784 2495285 := bstep (se 5 (by rfl) ⟨116966, by rfl⟩ : syracuseStep 2495285 = 233933) B233933
theorem B168785 : Blo 111784 168785 := bstep (se 2 (by rfl) ⟨63294, by rfl⟩ : syracuseStep 168785 = 126589) B126589
theorem B168803 : Blo 111784 168803 := bstep (se 1 (by rfl) ⟨126602, by rfl⟩ : syracuseStep 168803 = 253205) B253205
theorem B463715 : Blo 111784 463715 := bstep (se 1 (by rfl) ⟨347786, by rfl⟩ : syracuseStep 463715 = 695573) B695573
theorem B168833 : Blo 111784 168833 := bstep (se 2 (by rfl) ⟨63312, by rfl⟩ : syracuseStep 168833 = 126625) B126625
theorem B168851 : Blo 111784 168851 := bstep (se 1 (by rfl) ⟨126638, by rfl⟩ : syracuseStep 168851 = 253277) B253277
theorem B168881 : Blo 111784 168881 := bstep (se 2 (by rfl) ⟨63330, by rfl⟩ : syracuseStep 168881 = 126661) B126661
theorem B168899 : Blo 111784 168899 := bstep (se 1 (by rfl) ⟨126674, by rfl⟩ : syracuseStep 168899 = 253349) B253349
theorem B922565 : Blo 111784 922565 := bstep (se 4 (by rfl) ⟨86490, by rfl⟩ : syracuseStep 922565 = 172981) B172981
theorem B168929 : Blo 111784 168929 := bstep (se 2 (by rfl) ⟨63348, by rfl⟩ : syracuseStep 168929 = 126697) B126697
theorem B168947 : Blo 111784 168947 := bstep (se 1 (by rfl) ⟨126710, by rfl⟩ : syracuseStep 168947 = 253421) B253421
theorem B168977 : Blo 111784 168977 := bstep (se 2 (by rfl) ⟨63366, by rfl⟩ : syracuseStep 168977 = 126733) B126733
theorem B168995 : Blo 111784 168995 := bstep (se 1 (by rfl) ⟨126746, by rfl⟩ : syracuseStep 168995 = 253493) B253493
theorem B169025 : Blo 111784 169025 := bstep (se 2 (by rfl) ⟨63384, by rfl⟩ : syracuseStep 169025 = 126769) B126769
theorem B169043 : Blo 111784 169043 := bstep (se 1 (by rfl) ⟨126782, by rfl⟩ : syracuseStep 169043 = 253565) B253565
theorem B431203 : Blo 111784 431203 := bstep (se 1 (by rfl) ⟨323402, by rfl⟩ : syracuseStep 431203 = 646805) B646805
theorem B169073 : Blo 111784 169073 := bstep (se 2 (by rfl) ⟨63402, by rfl⟩ : syracuseStep 169073 = 126805) B126805
theorem B169091 : Blo 111784 169091 := bstep (se 1 (by rfl) ⟨126818, by rfl⟩ : syracuseStep 169091 = 253637) B253637
theorem B169121 : Blo 111784 169121 := bstep (se 2 (by rfl) ⟨63420, by rfl⟩ : syracuseStep 169121 = 126841) B126841
theorem B169139 : Blo 111784 169139 := bstep (se 1 (by rfl) ⟨126854, by rfl⟩ : syracuseStep 169139 = 253709) B253709
theorem B726221 : Blo 111784 726221 := bstep (se 3 (by rfl) ⟨136166, by rfl⟩ : syracuseStep 726221 = 272333) B272333
theorem B169169 : Blo 111784 169169 := bstep (se 2 (by rfl) ⟨63438, by rfl⟩ : syracuseStep 169169 = 126877) B126877
theorem B169187 : Blo 111784 169187 := bstep (se 1 (by rfl) ⟨126890, by rfl⟩ : syracuseStep 169187 = 253781) B253781
theorem B169217 : Blo 111784 169217 := bstep (se 2 (by rfl) ⟨63456, by rfl⟩ : syracuseStep 169217 = 126913) B126913
theorem B169235 : Blo 111784 169235 := bstep (se 1 (by rfl) ⟨126926, by rfl⟩ : syracuseStep 169235 = 253853) B253853
theorem B169265 : Blo 111784 169265 := bstep (se 2 (by rfl) ⟨63474, by rfl⟩ : syracuseStep 169265 = 126949) B126949
theorem B169283 : Blo 111784 169283 := bstep (se 1 (by rfl) ⟨126962, by rfl⟩ : syracuseStep 169283 = 253925) B253925
theorem B169313 : Blo 111784 169313 := bstep (se 2 (by rfl) ⟨63492, by rfl⟩ : syracuseStep 169313 = 126985) B126985
theorem B169331 : Blo 111784 169331 := bstep (se 1 (by rfl) ⟨126998, by rfl⟩ : syracuseStep 169331 = 253997) B253997
theorem B169361 : Blo 111784 169361 := bstep (se 2 (by rfl) ⟨63510, by rfl⟩ : syracuseStep 169361 = 127021) B127021
theorem B169379 : Blo 111784 169379 := bstep (se 1 (by rfl) ⟨127034, by rfl⟩ : syracuseStep 169379 = 254069) B254069
theorem B169409 : Blo 111784 169409 := bstep (se 2 (by rfl) ⟨63528, by rfl⟩ : syracuseStep 169409 = 127057) B127057
theorem B169427 : Blo 111784 169427 := bstep (se 1 (by rfl) ⟨127070, by rfl⟩ : syracuseStep 169427 = 254141) B254141
theorem B169457 : Blo 111784 169457 := bstep (se 2 (by rfl) ⟨63546, by rfl⟩ : syracuseStep 169457 = 127093) B127093
theorem B169475 : Blo 111784 169475 := bstep (se 1 (by rfl) ⟨127106, by rfl⟩ : syracuseStep 169475 = 254213) B254213
theorem B169505 : Blo 111784 169505 := bstep (se 2 (by rfl) ⟨63564, by rfl⟩ : syracuseStep 169505 = 127129) B127129
theorem B136739 : Blo 111784 136739 := bstep (se 1 (by rfl) ⟨102554, by rfl⟩ : syracuseStep 136739 = 205109) B205109
theorem B202289 : Blo 111784 202289 := bstep (se 2 (by rfl) ⟨75858, by rfl⟩ : syracuseStep 202289 = 151717) B151717
theorem B169523 : Blo 111784 169523 := bstep (se 1 (by rfl) ⟨127142, by rfl⟩ : syracuseStep 169523 = 254285) B254285
theorem B661069 : Blo 111784 661069 := bstep (se 3 (by rfl) ⟨123950, by rfl⟩ : syracuseStep 661069 = 247901) B247901
theorem B169553 : Blo 111784 169553 := bstep (se 2 (by rfl) ⟨63582, by rfl⟩ : syracuseStep 169553 = 127165) B127165
theorem B169571 : Blo 111784 169571 := bstep (se 1 (by rfl) ⟨127178, by rfl⟩ : syracuseStep 169571 = 254357) B254357
theorem B169601 : Blo 111784 169601 := bstep (se 2 (by rfl) ⟨63600, by rfl⟩ : syracuseStep 169601 = 127201) B127201
theorem B169619 : Blo 111784 169619 := bstep (se 1 (by rfl) ⟨127214, by rfl⟩ : syracuseStep 169619 = 254429) B254429
theorem B169649 : Blo 111784 169649 := bstep (se 2 (by rfl) ⟨63618, by rfl⟩ : syracuseStep 169649 = 127237) B127237
theorem B1316533 : Blo 111784 1316533 := bstep (se 5 (by rfl) ⟨61712, by rfl⟩ : syracuseStep 1316533 = 123425) B123425
theorem B169667 : Blo 111784 169667 := bstep (se 1 (by rfl) ⟨127250, by rfl⟩ : syracuseStep 169667 = 254501) B254501
theorem B169697 : Blo 111784 169697 := bstep (se 2 (by rfl) ⟨63636, by rfl⟩ : syracuseStep 169697 = 127273) B127273
theorem B169715 : Blo 111784 169715 := bstep (se 1 (by rfl) ⟨127286, by rfl⟩ : syracuseStep 169715 = 254573) B254573
theorem B169745 : Blo 111784 169745 := bstep (se 2 (by rfl) ⟨63654, by rfl⟩ : syracuseStep 169745 = 127309) B127309
theorem B169763 : Blo 111784 169763 := bstep (se 1 (by rfl) ⟨127322, by rfl⟩ : syracuseStep 169763 = 254645) B254645
theorem B169793 : Blo 111784 169793 := bstep (se 2 (by rfl) ⟨63672, by rfl⟩ : syracuseStep 169793 = 127345) B127345
theorem B169811 : Blo 111784 169811 := bstep (se 1 (by rfl) ⟨127358, by rfl⟩ : syracuseStep 169811 = 254717) B254717
theorem B530275 : Blo 111784 530275 := bstep (se 1 (by rfl) ⟨397706, by rfl⟩ : syracuseStep 530275 = 795413) B795413
theorem B169841 : Blo 111784 169841 := bstep (se 2 (by rfl) ⟨63690, by rfl⟩ : syracuseStep 169841 = 127381) B127381
theorem B464753 : Blo 111784 464753 := bstep (se 2 (by rfl) ⟨174282, by rfl⟩ : syracuseStep 464753 = 348565) B348565
theorem B169859 : Blo 111784 169859 := bstep (se 1 (by rfl) ⟨127394, by rfl⟩ : syracuseStep 169859 = 254789) B254789
theorem B169889 : Blo 111784 169889 := bstep (se 2 (by rfl) ⟨63708, by rfl⟩ : syracuseStep 169889 = 127417) B127417
theorem B169907 : Blo 111784 169907 := bstep (se 1 (by rfl) ⟨127430, by rfl⟩ : syracuseStep 169907 = 254861) B254861
theorem B169937 : Blo 111784 169937 := bstep (se 2 (by rfl) ⟨63726, by rfl⟩ : syracuseStep 169937 = 127453) B127453
theorem B366545 : Blo 111784 366545 := bstep (se 2 (by rfl) ⟨137454, by rfl⟩ : syracuseStep 366545 = 274909) B274909
theorem B169955 : Blo 111784 169955 := bstep (se 1 (by rfl) ⟨127466, by rfl⟩ : syracuseStep 169955 = 254933) B254933
theorem B169985 : Blo 111784 169985 := bstep (se 2 (by rfl) ⟨63744, by rfl⟩ : syracuseStep 169985 = 127489) B127489
theorem B170003 : Blo 111784 170003 := bstep (se 1 (by rfl) ⟨127502, by rfl⟩ : syracuseStep 170003 = 255005) B255005
theorem B170033 : Blo 111784 170033 := bstep (se 2 (by rfl) ⟨63762, by rfl⟩ : syracuseStep 170033 = 127525) B127525
theorem B170051 : Blo 111784 170051 := bstep (se 1 (by rfl) ⟨127538, by rfl⟩ : syracuseStep 170051 = 255077) B255077
theorem B170081 : Blo 111784 170081 := bstep (se 2 (by rfl) ⟨63780, by rfl⟩ : syracuseStep 170081 = 127561) B127561
theorem B170099 : Blo 111784 170099 := bstep (se 1 (by rfl) ⟨127574, by rfl⟩ : syracuseStep 170099 = 255149) B255149
theorem B170129 : Blo 111784 170129 := bstep (se 2 (by rfl) ⟨63798, by rfl⟩ : syracuseStep 170129 = 127597) B127597
theorem B170147 : Blo 111784 170147 := bstep (se 1 (by rfl) ⟨127610, by rfl⟩ : syracuseStep 170147 = 255221) B255221
theorem B170177 : Blo 111784 170177 := bstep (se 2 (by rfl) ⟨63816, by rfl⟩ : syracuseStep 170177 = 127633) B127633
theorem B170195 : Blo 111784 170195 := bstep (se 1 (by rfl) ⟨127646, by rfl⟩ : syracuseStep 170195 = 255293) B255293
theorem B5445845 : Blo 111784 5445845 := bstep (se 7 (by rfl) ⟨63818, by rfl⟩ : syracuseStep 5445845 = 127637) B127637
theorem B170225 : Blo 111784 170225 := bstep (se 2 (by rfl) ⟨63834, by rfl⟩ : syracuseStep 170225 = 127669) B127669
theorem B170243 : Blo 111784 170243 := bstep (se 1 (by rfl) ⟨127682, by rfl⟩ : syracuseStep 170243 = 255365) B255365
theorem B170257 : Blo 111784 170257 := bstep (se 2 (by rfl) ⟨63846, by rfl⟩ : syracuseStep 170257 = 127693) B127693
theorem B170273 : Blo 111784 170273 := bstep (se 2 (by rfl) ⟨63852, by rfl⟩ : syracuseStep 170273 = 127705) B127705
theorem B366893 : Blo 111784 366893 := bstep (se 3 (by rfl) ⟨68792, by rfl⟩ : syracuseStep 366893 = 137585) B137585
theorem B170291 : Blo 111784 170291 := bstep (se 1 (by rfl) ⟨127718, by rfl⟩ : syracuseStep 170291 = 255437) B255437
theorem B170321 : Blo 111784 170321 := bstep (se 2 (by rfl) ⟨63870, by rfl⟩ : syracuseStep 170321 = 127741) B127741
theorem B268643 : Blo 111784 268643 := bstep (se 1 (by rfl) ⟨201482, by rfl⟩ : syracuseStep 268643 = 402965) B402965
theorem B170339 : Blo 111784 170339 := bstep (se 1 (by rfl) ⟨127754, by rfl⟩ : syracuseStep 170339 = 255509) B255509
theorem B2595185 : Blo 111784 2595185 := bstep (se 2 (by rfl) ⟨973194, by rfl⟩ : syracuseStep 2595185 = 1946389) B1946389
theorem B170369 : Blo 111784 170369 := bstep (se 2 (by rfl) ⟨63888, by rfl⟩ : syracuseStep 170369 = 127777) B127777
theorem B170387 : Blo 111784 170387 := bstep (se 1 (by rfl) ⟨127790, by rfl⟩ : syracuseStep 170387 = 255581) B255581
theorem B268721 : Blo 111784 268721 := bstep (se 2 (by rfl) ⟨100770, by rfl⟩ : syracuseStep 268721 = 201541) B201541
theorem B170417 : Blo 111784 170417 := bstep (se 2 (by rfl) ⟨63906, by rfl⟩ : syracuseStep 170417 = 127813) B127813
theorem B170435 : Blo 111784 170435 := bstep (se 1 (by rfl) ⟨127826, by rfl⟩ : syracuseStep 170435 = 255653) B255653
theorem B170465 : Blo 111784 170465 := bstep (se 2 (by rfl) ⟨63924, by rfl⟩ : syracuseStep 170465 = 127849) B127849
theorem B170483 : Blo 111784 170483 := bstep (se 1 (by rfl) ⟨127862, by rfl⟩ : syracuseStep 170483 = 255725) B255725
theorem B170513 : Blo 111784 170513 := bstep (se 2 (by rfl) ⟨63942, by rfl⟩ : syracuseStep 170513 = 127885) B127885
theorem B170531 : Blo 111784 170531 := bstep (se 1 (by rfl) ⟨127898, by rfl⟩ : syracuseStep 170531 = 255797) B255797
theorem B170561 : Blo 111784 170561 := bstep (se 2 (by rfl) ⟨63960, by rfl⟩ : syracuseStep 170561 = 127921) B127921
theorem B170579 : Blo 111784 170579 := bstep (se 1 (by rfl) ⟨127934, by rfl⟩ : syracuseStep 170579 = 255869) B255869
theorem B268913 : Blo 111784 268913 := bstep (se 2 (by rfl) ⟨100842, by rfl⟩ : syracuseStep 268913 = 201685) B201685
theorem B170609 : Blo 111784 170609 := bstep (se 2 (by rfl) ⟨63978, by rfl⟩ : syracuseStep 170609 = 127957) B127957
theorem B170627 : Blo 111784 170627 := bstep (se 1 (by rfl) ⟨127970, by rfl⟩ : syracuseStep 170627 = 255941) B255941
theorem B170657 : Blo 111784 170657 := bstep (se 2 (by rfl) ⟨63996, by rfl⟩ : syracuseStep 170657 = 127993) B127993
theorem B170675 : Blo 111784 170675 := bstep (se 1 (by rfl) ⟨128006, by rfl⟩ : syracuseStep 170675 = 256013) B256013
theorem B170705 : Blo 111784 170705 := bstep (se 2 (by rfl) ⟨64014, by rfl⟩ : syracuseStep 170705 = 128029) B128029
theorem B170723 : Blo 111784 170723 := bstep (se 1 (by rfl) ⟨128042, by rfl⟩ : syracuseStep 170723 = 256085) B256085
theorem B170753 : Blo 111784 170753 := bstep (se 2 (by rfl) ⟨64032, by rfl⟩ : syracuseStep 170753 = 128065) B128065
theorem B170771 : Blo 111784 170771 := bstep (se 1 (by rfl) ⟨128078, by rfl⟩ : syracuseStep 170771 = 256157) B256157
theorem B170801 : Blo 111784 170801 := bstep (se 2 (by rfl) ⟨64050, by rfl⟩ : syracuseStep 170801 = 128101) B128101
theorem B170819 : Blo 111784 170819 := bstep (se 1 (by rfl) ⟨128114, by rfl⟩ : syracuseStep 170819 = 256229) B256229
theorem B170849 : Blo 111784 170849 := bstep (se 2 (by rfl) ⟨64068, by rfl⟩ : syracuseStep 170849 = 128137) B128137
theorem B170867 : Blo 111784 170867 := bstep (se 1 (by rfl) ⟨128150, by rfl⟩ : syracuseStep 170867 = 256301) B256301
theorem B170897 : Blo 111784 170897 := bstep (se 2 (by rfl) ⟨64086, by rfl⟩ : syracuseStep 170897 = 128173) B128173
theorem B170915 : Blo 111784 170915 := bstep (se 1 (by rfl) ⟨128186, by rfl⟩ : syracuseStep 170915 = 256373) B256373
theorem B170945 : Blo 111784 170945 := bstep (se 2 (by rfl) ⟨64104, by rfl⟩ : syracuseStep 170945 = 128209) B128209
theorem B170963 : Blo 111784 170963 := bstep (se 1 (by rfl) ⟨128222, by rfl⟩ : syracuseStep 170963 = 256445) B256445
theorem B170993 : Blo 111784 170993 := bstep (se 2 (by rfl) ⟨64122, by rfl⟩ : syracuseStep 170993 = 128245) B128245
theorem B171011 : Blo 111784 171011 := bstep (se 1 (by rfl) ⟨128258, by rfl⟩ : syracuseStep 171011 = 256517) B256517
theorem B171041 : Blo 111784 171041 := bstep (se 2 (by rfl) ⟨64140, by rfl⟩ : syracuseStep 171041 = 128281) B128281
theorem B171059 : Blo 111784 171059 := bstep (se 1 (by rfl) ⟨128294, by rfl⟩ : syracuseStep 171059 = 256589) B256589
theorem B171089 : Blo 111784 171089 := bstep (se 2 (by rfl) ⟨64158, by rfl⟩ : syracuseStep 171089 = 128317) B128317
theorem B269411 : Blo 111784 269411 := bstep (se 1 (by rfl) ⟨202058, by rfl⟩ : syracuseStep 269411 = 404117) B404117
theorem B171107 : Blo 111784 171107 := bstep (se 1 (by rfl) ⟨128330, by rfl⟩ : syracuseStep 171107 = 256661) B256661
theorem B171137 : Blo 111784 171137 := bstep (se 2 (by rfl) ⟨64176, by rfl⟩ : syracuseStep 171137 = 128353) B128353
theorem B171155 : Blo 111784 171155 := bstep (se 1 (by rfl) ⟨128366, by rfl⟩ : syracuseStep 171155 = 256733) B256733
theorem B269489 : Blo 111784 269489 := bstep (se 2 (by rfl) ⟨101058, by rfl⟩ : syracuseStep 269489 = 202117) B202117
theorem B171185 : Blo 111784 171185 := bstep (se 2 (by rfl) ⟨64194, by rfl⟩ : syracuseStep 171185 = 128389) B128389
theorem B171203 : Blo 111784 171203 := bstep (se 1 (by rfl) ⟨128402, by rfl⟩ : syracuseStep 171203 = 256805) B256805
theorem B171233 : Blo 111784 171233 := bstep (se 2 (by rfl) ⟨64212, by rfl⟩ : syracuseStep 171233 = 128425) B128425
theorem B171251 : Blo 111784 171251 := bstep (se 1 (by rfl) ⟨128438, by rfl⟩ : syracuseStep 171251 = 256877) B256877
theorem B433421 : Blo 111784 433421 := bstep (se 3 (by rfl) ⟨81266, by rfl⟩ : syracuseStep 433421 = 162533) B162533
theorem B171281 : Blo 111784 171281 := bstep (se 2 (by rfl) ⟨64230, by rfl⟩ : syracuseStep 171281 = 128461) B128461
theorem B171299 : Blo 111784 171299 := bstep (se 1 (by rfl) ⟨128474, by rfl⟩ : syracuseStep 171299 = 256949) B256949
theorem B171329 : Blo 111784 171329 := bstep (se 2 (by rfl) ⟨64248, by rfl⟩ : syracuseStep 171329 = 128497) B128497
theorem B171347 : Blo 111784 171347 := bstep (se 1 (by rfl) ⟨128510, by rfl⟩ : syracuseStep 171347 = 257021) B257021
theorem B171377 : Blo 111784 171377 := bstep (se 2 (by rfl) ⟨64266, by rfl⟩ : syracuseStep 171377 = 128533) B128533
theorem B171395 : Blo 111784 171395 := bstep (se 1 (by rfl) ⟨128546, by rfl⟩ : syracuseStep 171395 = 257093) B257093
theorem B728453 : Blo 111784 728453 := bstep (se 4 (by rfl) ⟨68292, by rfl⟩ : syracuseStep 728453 = 136585) B136585
theorem B171425 : Blo 111784 171425 := bstep (se 2 (by rfl) ⟨64284, by rfl⟩ : syracuseStep 171425 = 128569) B128569
theorem B171443 : Blo 111784 171443 := bstep (se 1 (by rfl) ⟨128582, by rfl⟩ : syracuseStep 171443 = 257165) B257165
theorem B171473 : Blo 111784 171473 := bstep (se 2 (by rfl) ⟨64302, by rfl⟩ : syracuseStep 171473 = 128605) B128605
theorem B1744355 : Blo 111784 1744355 := bstep (se 1 (by rfl) ⟨1308266, by rfl⟩ : syracuseStep 1744355 = 2616533) B2616533
theorem B171491 : Blo 111784 171491 := bstep (se 1 (by rfl) ⟨128618, by rfl⟩ : syracuseStep 171491 = 257237) B257237
theorem B171521 : Blo 111784 171521 := bstep (se 2 (by rfl) ⟨64320, by rfl⟩ : syracuseStep 171521 = 128641) B128641
theorem B171539 : Blo 111784 171539 := bstep (se 1 (by rfl) ⟨128654, by rfl⟩ : syracuseStep 171539 = 257309) B257309
theorem B269873 : Blo 111784 269873 := bstep (se 2 (by rfl) ⟨101202, by rfl⟩ : syracuseStep 269873 = 202405) B202405
theorem B171569 : Blo 111784 171569 := bstep (se 2 (by rfl) ⟨64338, by rfl⟩ : syracuseStep 171569 = 128677) B128677
theorem B171587 : Blo 111784 171587 := bstep (se 1 (by rfl) ⟨128690, by rfl⟩ : syracuseStep 171587 = 257381) B257381
theorem B171617 : Blo 111784 171617 := bstep (se 2 (by rfl) ⟨64356, by rfl⟩ : syracuseStep 171617 = 128713) B128713
theorem B171635 : Blo 111784 171635 := bstep (se 1 (by rfl) ⟨128726, by rfl⟩ : syracuseStep 171635 = 257453) B257453
theorem B171665 : Blo 111784 171665 := bstep (se 2 (by rfl) ⟨64374, by rfl⟩ : syracuseStep 171665 = 128749) B128749
theorem B171683 : Blo 111784 171683 := bstep (se 1 (by rfl) ⟨128762, by rfl⟩ : syracuseStep 171683 = 257525) B257525
theorem B171713 : Blo 111784 171713 := bstep (se 2 (by rfl) ⟨64392, by rfl⟩ : syracuseStep 171713 = 128785) B128785
theorem B171731 : Blo 111784 171731 := bstep (se 1 (by rfl) ⟨128798, by rfl⟩ : syracuseStep 171731 = 257597) B257597
theorem B171761 : Blo 111784 171761 := bstep (se 2 (by rfl) ⟨64410, by rfl⟩ : syracuseStep 171761 = 128821) B128821
theorem B171779 : Blo 111784 171779 := bstep (se 1 (by rfl) ⟨128834, by rfl⟩ : syracuseStep 171779 = 257669) B257669
theorem B171809 : Blo 111784 171809 := bstep (se 2 (by rfl) ⟨64428, by rfl⟩ : syracuseStep 171809 = 128857) B128857
theorem B171827 : Blo 111784 171827 := bstep (se 1 (by rfl) ⟨128870, by rfl⟩ : syracuseStep 171827 = 257741) B257741
theorem B171857 : Blo 111784 171857 := bstep (se 2 (by rfl) ⟨64446, by rfl⟩ : syracuseStep 171857 = 128893) B128893
theorem B171875 : Blo 111784 171875 := bstep (se 1 (by rfl) ⟨128906, by rfl⟩ : syracuseStep 171875 = 257813) B257813
theorem B171905 : Blo 111784 171905 := bstep (se 2 (by rfl) ⟨64464, by rfl⟩ : syracuseStep 171905 = 128929) B128929
theorem B466829 : Blo 111784 466829 := bstep (se 3 (by rfl) ⟨87530, by rfl⟩ : syracuseStep 466829 = 175061) B175061
theorem B171923 : Blo 111784 171923 := bstep (se 1 (by rfl) ⟨128942, by rfl⟩ : syracuseStep 171923 = 257885) B257885
theorem B171953 : Blo 111784 171953 := bstep (se 2 (by rfl) ⟨64482, by rfl⟩ : syracuseStep 171953 = 128965) B128965
theorem B171971 : Blo 111784 171971 := bstep (se 1 (by rfl) ⟨128978, by rfl⟩ : syracuseStep 171971 = 257957) B257957
theorem B172001 : Blo 111784 172001 := bstep (se 2 (by rfl) ⟨64500, by rfl⟩ : syracuseStep 172001 = 129001) B129001
theorem B172019 : Blo 111784 172019 := bstep (se 1 (by rfl) ⟨129014, by rfl⟩ : syracuseStep 172019 = 258029) B258029
theorem B172049 : Blo 111784 172049 := bstep (se 2 (by rfl) ⟨64518, by rfl⟩ : syracuseStep 172049 = 129037) B129037
theorem B172067 : Blo 111784 172067 := bstep (se 1 (by rfl) ⟨129050, by rfl⟩ : syracuseStep 172067 = 258101) B258101
theorem B1450037 : Blo 111784 1450037 := bstep (se 5 (by rfl) ⟨67970, by rfl⟩ : syracuseStep 1450037 = 135941) B135941
theorem B172097 : Blo 111784 172097 := bstep (se 2 (by rfl) ⟨64536, by rfl⟩ : syracuseStep 172097 = 129073) B129073
theorem B172115 : Blo 111784 172115 := bstep (se 1 (by rfl) ⟨129086, by rfl⟩ : syracuseStep 172115 = 258173) B258173
theorem B368749 : Blo 111784 368749 := bstep (se 3 (by rfl) ⟨69140, by rfl⟩ : syracuseStep 368749 = 138281) B138281
theorem B172145 : Blo 111784 172145 := bstep (se 2 (by rfl) ⟨64554, by rfl⟩ : syracuseStep 172145 = 129109) B129109
theorem B172163 : Blo 111784 172163 := bstep (se 1 (by rfl) ⟨129122, by rfl⟩ : syracuseStep 172163 = 258245) B258245
theorem B172193 : Blo 111784 172193 := bstep (se 2 (by rfl) ⟨64572, by rfl⟩ : syracuseStep 172193 = 129145) B129145
theorem B172211 : Blo 111784 172211 := bstep (se 1 (by rfl) ⟨129158, by rfl⟩ : syracuseStep 172211 = 258317) B258317
theorem B172241 : Blo 111784 172241 := bstep (se 2 (by rfl) ⟨64590, by rfl⟩ : syracuseStep 172241 = 129181) B129181
theorem B172259 : Blo 111784 172259 := bstep (se 1 (by rfl) ⟨129194, by rfl⟩ : syracuseStep 172259 = 258389) B258389
theorem B172289 : Blo 111784 172289 := bstep (se 2 (by rfl) ⟨64608, by rfl⟩ : syracuseStep 172289 = 129217) B129217
theorem B172307 : Blo 111784 172307 := bstep (se 1 (by rfl) ⟨129230, by rfl⟩ : syracuseStep 172307 = 258461) B258461
theorem B172337 : Blo 111784 172337 := bstep (se 2 (by rfl) ⟨64626, by rfl⟩ : syracuseStep 172337 = 129253) B129253
theorem B172355 : Blo 111784 172355 := bstep (se 1 (by rfl) ⟨129266, by rfl⟩ : syracuseStep 172355 = 258533) B258533
theorem B172385 : Blo 111784 172385 := bstep (se 2 (by rfl) ⟨64644, by rfl⟩ : syracuseStep 172385 = 129289) B129289
theorem B237937 : Blo 111784 237937 := bstep (se 2 (by rfl) ⟨89226, by rfl⟩ : syracuseStep 237937 = 178453) B178453
theorem B172403 : Blo 111784 172403 := bstep (se 1 (by rfl) ⟨129302, by rfl⟩ : syracuseStep 172403 = 258605) B258605
theorem B172433 : Blo 111784 172433 := bstep (se 2 (by rfl) ⟨64662, by rfl⟩ : syracuseStep 172433 = 129325) B129325
theorem B172451 : Blo 111784 172451 := bstep (se 1 (by rfl) ⟨129338, by rfl⟩ : syracuseStep 172451 = 258677) B258677
theorem B172481 : Blo 111784 172481 := bstep (se 2 (by rfl) ⟨64680, by rfl⟩ : syracuseStep 172481 = 129361) B129361
theorem B172499 : Blo 111784 172499 := bstep (se 1 (by rfl) ⟨129374, by rfl⟩ : syracuseStep 172499 = 258749) B258749
theorem B172529 : Blo 111784 172529 := bstep (se 2 (by rfl) ⟨64698, by rfl⟩ : syracuseStep 172529 = 129397) B129397
theorem B172547 : Blo 111784 172547 := bstep (se 1 (by rfl) ⟨129410, by rfl⟩ : syracuseStep 172547 = 258821) B258821
theorem B172577 : Blo 111784 172577 := bstep (se 2 (by rfl) ⟨64716, by rfl⟩ : syracuseStep 172577 = 129433) B129433
theorem B172595 : Blo 111784 172595 := bstep (se 1 (by rfl) ⟨129446, by rfl⟩ : syracuseStep 172595 = 258893) B258893
theorem B172625 : Blo 111784 172625 := bstep (se 2 (by rfl) ⟨64734, by rfl⟩ : syracuseStep 172625 = 129469) B129469
theorem B172643 : Blo 111784 172643 := bstep (se 1 (by rfl) ⟨129482, by rfl⟩ : syracuseStep 172643 = 258965) B258965
theorem B172673 : Blo 111784 172673 := bstep (se 2 (by rfl) ⟨64752, by rfl⟩ : syracuseStep 172673 = 129505) B129505
theorem B172691 : Blo 111784 172691 := bstep (se 1 (by rfl) ⟨129518, by rfl⟩ : syracuseStep 172691 = 259037) B259037
theorem B172721 : Blo 111784 172721 := bstep (se 2 (by rfl) ⟨64770, by rfl⟩ : syracuseStep 172721 = 129541) B129541
theorem B172739 : Blo 111784 172739 := bstep (se 1 (by rfl) ⟨129554, by rfl⟩ : syracuseStep 172739 = 259109) B259109
theorem B172769 : Blo 111784 172769 := bstep (se 2 (by rfl) ⟨64788, by rfl⟩ : syracuseStep 172769 = 129577) B129577
theorem B172787 : Blo 111784 172787 := bstep (se 1 (by rfl) ⟨129590, by rfl⟩ : syracuseStep 172787 = 259181) B259181
theorem B205571 : Blo 111784 205571 := bstep (se 1 (by rfl) ⟨154178, by rfl⟩ : syracuseStep 205571 = 308357) B308357
theorem B172817 : Blo 111784 172817 := bstep (se 2 (by rfl) ⟨64806, by rfl⟩ : syracuseStep 172817 = 129613) B129613
theorem B172835 : Blo 111784 172835 := bstep (se 1 (by rfl) ⟨129626, by rfl⟩ : syracuseStep 172835 = 259253) B259253
theorem B172865 : Blo 111784 172865 := bstep (se 2 (by rfl) ⟨64824, by rfl⟩ : syracuseStep 172865 = 129649) B129649
theorem B172883 : Blo 111784 172883 := bstep (se 1 (by rfl) ⟨129662, by rfl⟩ : syracuseStep 172883 = 259325) B259325
theorem B172913 : Blo 111784 172913 := bstep (se 2 (by rfl) ⟨64842, by rfl⟩ : syracuseStep 172913 = 129685) B129685
theorem B172931 : Blo 111784 172931 := bstep (se 1 (by rfl) ⟨129698, by rfl⟩ : syracuseStep 172931 = 259397) B259397
theorem B172961 : Blo 111784 172961 := bstep (se 2 (by rfl) ⟨64860, by rfl⟩ : syracuseStep 172961 = 129721) B129721
theorem B172979 : Blo 111784 172979 := bstep (se 1 (by rfl) ⟨129734, by rfl⟩ : syracuseStep 172979 = 259469) B259469
theorem B173009 : Blo 111784 173009 := bstep (se 2 (by rfl) ⟨64878, by rfl⟩ : syracuseStep 173009 = 129757) B129757
theorem B173027 : Blo 111784 173027 := bstep (se 1 (by rfl) ⟨129770, by rfl⟩ : syracuseStep 173027 = 259541) B259541
theorem B173057 : Blo 111784 173057 := bstep (se 2 (by rfl) ⟨64896, by rfl⟩ : syracuseStep 173057 = 129793) B129793
theorem B173075 : Blo 111784 173075 := bstep (se 1 (by rfl) ⟨129806, by rfl⟩ : syracuseStep 173075 = 259613) B259613
theorem B173105 : Blo 111784 173105 := bstep (se 2 (by rfl) ⟨64914, by rfl⟩ : syracuseStep 173105 = 129829) B129829
theorem B173123 : Blo 111784 173123 := bstep (se 1 (by rfl) ⟨129842, by rfl⟩ : syracuseStep 173123 = 259685) B259685
theorem B173153 : Blo 111784 173153 := bstep (se 2 (by rfl) ⟨64932, by rfl⟩ : syracuseStep 173153 = 129865) B129865
theorem B173171 : Blo 111784 173171 := bstep (se 1 (by rfl) ⟨129878, by rfl⟩ : syracuseStep 173171 = 259757) B259757
theorem B173201 : Blo 111784 173201 := bstep (se 2 (by rfl) ⟨64950, by rfl⟩ : syracuseStep 173201 = 129901) B129901
theorem B173219 : Blo 111784 173219 := bstep (se 1 (by rfl) ⟨129914, by rfl⟩ : syracuseStep 173219 = 259829) B259829
theorem B173249 : Blo 111784 173249 := bstep (se 2 (by rfl) ⟨64968, by rfl⟩ : syracuseStep 173249 = 129937) B129937
theorem B173267 : Blo 111784 173267 := bstep (se 1 (by rfl) ⟨129950, by rfl⟩ : syracuseStep 173267 = 259901) B259901
theorem B566513 : Blo 111784 566513 := bstep (se 2 (by rfl) ⟨212442, by rfl⟩ : syracuseStep 566513 = 424885) B424885
theorem B173297 : Blo 111784 173297 := bstep (se 2 (by rfl) ⟨64986, by rfl⟩ : syracuseStep 173297 = 129973) B129973
theorem B173315 : Blo 111784 173315 := bstep (se 1 (by rfl) ⟨129986, by rfl⟩ : syracuseStep 173315 = 259973) B259973
theorem B271633 : Blo 111784 271633 := bstep (se 2 (by rfl) ⟨101862, by rfl⟩ : syracuseStep 271633 = 203725) B203725
theorem B369937 : Blo 111784 369937 := bstep (se 2 (by rfl) ⟨138726, by rfl⟩ : syracuseStep 369937 = 277453) B277453
theorem B173345 : Blo 111784 173345 := bstep (se 2 (by rfl) ⟨65004, by rfl⟩ : syracuseStep 173345 = 130009) B130009
theorem B173363 : Blo 111784 173363 := bstep (se 1 (by rfl) ⟨130022, by rfl⟩ : syracuseStep 173363 = 260045) B260045
theorem B173393 : Blo 111784 173393 := bstep (se 2 (by rfl) ⟨65022, by rfl⟩ : syracuseStep 173393 = 130045) B130045
theorem B173411 : Blo 111784 173411 := bstep (se 1 (by rfl) ⟨130058, by rfl⟩ : syracuseStep 173411 = 260117) B260117
theorem B173441 : Blo 111784 173441 := bstep (se 2 (by rfl) ⟨65040, by rfl⟩ : syracuseStep 173441 = 130081) B130081
theorem B173459 : Blo 111784 173459 := bstep (se 1 (by rfl) ⟨130094, by rfl⟩ : syracuseStep 173459 = 260189) B260189
theorem B173489 : Blo 111784 173489 := bstep (se 2 (by rfl) ⟨65058, by rfl⟩ : syracuseStep 173489 = 130117) B130117
theorem B173507 : Blo 111784 173507 := bstep (se 1 (by rfl) ⟨130130, by rfl⟩ : syracuseStep 173507 = 260261) B260261
theorem B173537 : Blo 111784 173537 := bstep (se 2 (by rfl) ⟨65076, by rfl⟩ : syracuseStep 173537 = 130153) B130153
theorem B173555 : Blo 111784 173555 := bstep (se 1 (by rfl) ⟨130166, by rfl⟩ : syracuseStep 173555 = 260333) B260333
theorem B173585 : Blo 111784 173585 := bstep (se 2 (by rfl) ⟨65094, by rfl⟩ : syracuseStep 173585 = 130189) B130189
theorem B173603 : Blo 111784 173603 := bstep (se 1 (by rfl) ⟨130202, by rfl⟩ : syracuseStep 173603 = 260405) B260405
theorem B173633 : Blo 111784 173633 := bstep (se 2 (by rfl) ⟨65112, by rfl⟩ : syracuseStep 173633 = 130225) B130225
theorem B173651 : Blo 111784 173651 := bstep (se 1 (by rfl) ⟨130238, by rfl⟩ : syracuseStep 173651 = 260477) B260477
theorem B239203 : Blo 111784 239203 := bstep (se 1 (by rfl) ⟨179402, by rfl⟩ : syracuseStep 239203 = 358805) B358805
theorem B206723 : Blo 111784 206723 := bstep (se 1 (by rfl) ⟨155042, by rfl⟩ : syracuseStep 206723 = 310085) B310085
theorem B370595 : Blo 111784 370595 := bstep (se 1 (by rfl) ⟨277946, by rfl⟩ : syracuseStep 370595 = 555893) B555893
theorem B239537 : Blo 111784 239537 := bstep (se 2 (by rfl) ⟨89826, by rfl⟩ : syracuseStep 239537 = 179653) B179653
theorem B305155 : Blo 111784 305155 := bstep (se 1 (by rfl) ⟨228866, by rfl⟩ : syracuseStep 305155 = 457733) B457733
theorem B436337 : Blo 111784 436337 := bstep (se 2 (by rfl) ⟨163626, by rfl⟩ : syracuseStep 436337 = 327253) B327253
theorem B1485155 : Blo 111784 1485155 := bstep (se 1 (by rfl) ⟨1113866, by rfl⟩ : syracuseStep 1485155 = 2227733) B2227733
theorem B404003 : Blo 111784 404003 := bstep (se 1 (by rfl) ⟨303002, by rfl⟩ : syracuseStep 404003 = 606005) B606005
theorem B141907 : Blo 111784 141907 := bstep (se 1 (by rfl) ⟨106430, by rfl⟩ : syracuseStep 141907 = 212861) B212861
theorem B371299 : Blo 111784 371299 := bstep (se 1 (by rfl) ⟨278474, by rfl⟩ : syracuseStep 371299 = 556949) B556949
theorem B174721 : Blo 111784 174721 := bstep (se 2 (by rfl) ⟨65520, by rfl⟩ : syracuseStep 174721 = 131041) B131041
theorem B1911437 : Blo 111784 1911437 := bstep (se 3 (by rfl) ⟨358394, by rfl⟩ : syracuseStep 1911437 = 716789) B716789
theorem B436877 : Blo 111784 436877 := bstep (se 3 (by rfl) ⟨81914, by rfl⟩ : syracuseStep 436877 = 163829) B163829
theorem B567971 : Blo 111784 567971 := bstep (se 1 (by rfl) ⟨425978, by rfl⟩ : syracuseStep 567971 = 851957) B851957
theorem B142003 : Blo 111784 142003 := bstep (se 1 (by rfl) ⟨106502, by rfl⟩ : syracuseStep 142003 = 213005) B213005
theorem B994117 : Blo 111784 994117 := bstep (se 4 (by rfl) ⟨93198, by rfl⟩ : syracuseStep 994117 = 186397) B186397
theorem B240707 : Blo 111784 240707 := bstep (se 1 (by rfl) ⟨180530, by rfl⟩ : syracuseStep 240707 = 361061) B361061
theorem B142499 : Blo 111784 142499 := bstep (se 1 (by rfl) ⟨106874, by rfl⟩ : syracuseStep 142499 = 213749) B213749
theorem B961733 : Blo 111784 961733 := bstep (se 4 (by rfl) ⟨90162, by rfl⟩ : syracuseStep 961733 = 180325) B180325
theorem B568781 : Blo 111784 568781 := bstep (se 3 (by rfl) ⟨106646, by rfl⟩ : syracuseStep 568781 = 213293) B213293
theorem B437795 : Blo 111784 437795 := bstep (se 1 (by rfl) ⟨328346, by rfl⟩ : syracuseStep 437795 = 656693) B656693
theorem B667277 : Blo 111784 667277 := bstep (se 3 (by rfl) ⟨125114, by rfl⟩ : syracuseStep 667277 = 250229) B250229
theorem B143203 : Blo 111784 143203 := bstep (se 1 (by rfl) ⟨107402, by rfl⟩ : syracuseStep 143203 = 214805) B214805
theorem B143299 : Blo 111784 143299 := bstep (se 1 (by rfl) ⟨107474, by rfl⟩ : syracuseStep 143299 = 214949) B214949
theorem B372977 : Blo 111784 372977 := bstep (se 2 (by rfl) ⟨139866, by rfl⟩ : syracuseStep 372977 = 279733) B279733
theorem B438691 : Blo 111784 438691 := bstep (se 1 (by rfl) ⟨329018, by rfl⟩ : syracuseStep 438691 = 658037) B658037
theorem B143795 : Blo 111784 143795 := bstep (se 1 (by rfl) ⟨107846, by rfl⟩ : syracuseStep 143795 = 215693) B215693
theorem B438797 : Blo 111784 438797 := bstep (se 3 (by rfl) ⟨82274, by rfl⟩ : syracuseStep 438797 = 164549) B164549
theorem B307889 : Blo 111784 307889 := bstep (se 2 (by rfl) ⟨115458, by rfl⟩ : syracuseStep 307889 = 230917) B230917
theorem B242723 : Blo 111784 242723 := bstep (se 1 (by rfl) ⟨182042, by rfl⟩ : syracuseStep 242723 = 364085) B364085
theorem B275555 : Blo 111784 275555 := bstep (se 1 (by rfl) ⟨206666, by rfl⟩ : syracuseStep 275555 = 413333) B413333
theorem B177265 : Blo 111784 177265 := bstep (se 2 (by rfl) ⟨66474, by rfl⟩ : syracuseStep 177265 = 132949) B132949
theorem B144499 : Blo 111784 144499 := bstep (se 1 (by rfl) ⟨108374, by rfl⟩ : syracuseStep 144499 = 216749) B216749
theorem B144547 : Blo 111784 144547 := bstep (se 1 (by rfl) ⟨108410, by rfl⟩ : syracuseStep 144547 = 216821) B216821
theorem B111795 : Blo 111784 111795 := bstep (se 1 (by rfl) ⟨83846, by rfl⟩ : syracuseStep 111795 = 167693) B167693
theorem B111811 : Blo 111784 111811 := bstep (se 1 (by rfl) ⟨83858, by rfl⟩ : syracuseStep 111811 = 167717) B167717
theorem B111827 : Blo 111784 111827 := bstep (se 1 (by rfl) ⟨83870, by rfl⟩ : syracuseStep 111827 = 167741) B167741
theorem B144595 : Blo 111784 144595 := bstep (se 1 (by rfl) ⟨108446, by rfl⟩ : syracuseStep 144595 = 216893) B216893
theorem B111843 : Blo 111784 111843 := bstep (se 1 (by rfl) ⟨83882, by rfl⟩ : syracuseStep 111843 = 167765) B167765
theorem B111859 : Blo 111784 111859 := bstep (se 1 (by rfl) ⟨83894, by rfl⟩ : syracuseStep 111859 = 167789) B167789
theorem B111875 : Blo 111784 111875 := bstep (se 1 (by rfl) ⟨83906, by rfl⟩ : syracuseStep 111875 = 167813) B167813
theorem B111891 : Blo 111784 111891 := bstep (se 1 (by rfl) ⟨83918, by rfl⟩ : syracuseStep 111891 = 167837) B167837
theorem B111907 : Blo 111784 111907 := bstep (se 1 (by rfl) ⟨83930, by rfl⟩ : syracuseStep 111907 = 167861) B167861
theorem B341293 : Blo 111784 341293 := bstep (se 3 (by rfl) ⟨63992, by rfl⟩ : syracuseStep 341293 = 127985) B127985
theorem B111923 : Blo 111784 111923 := bstep (se 1 (by rfl) ⟨83942, by rfl⟩ : syracuseStep 111923 = 167885) B167885
theorem B111939 : Blo 111784 111939 := bstep (se 1 (by rfl) ⟨83954, by rfl⟩ : syracuseStep 111939 = 167909) B167909
theorem B111955 : Blo 111784 111955 := bstep (se 1 (by rfl) ⟨83966, by rfl⟩ : syracuseStep 111955 = 167933) B167933
theorem B111971 : Blo 111784 111971 := bstep (se 1 (by rfl) ⟨83978, by rfl⟩ : syracuseStep 111971 = 167957) B167957
theorem B111987 : Blo 111784 111987 := bstep (se 1 (by rfl) ⟨83990, by rfl⟩ : syracuseStep 111987 = 167981) B167981
theorem B112003 : Blo 111784 112003 := bstep (se 1 (by rfl) ⟨84002, by rfl⟩ : syracuseStep 112003 = 168005) B168005
theorem B112019 : Blo 111784 112019 := bstep (se 1 (by rfl) ⟨84014, by rfl⟩ : syracuseStep 112019 = 168029) B168029
theorem B112035 : Blo 111784 112035 := bstep (se 1 (by rfl) ⟨84026, by rfl⟩ : syracuseStep 112035 = 168053) B168053
theorem B112051 : Blo 111784 112051 := bstep (se 1 (by rfl) ⟨84038, by rfl⟩ : syracuseStep 112051 = 168077) B168077
theorem B112067 : Blo 111784 112067 := bstep (se 1 (by rfl) ⟨84050, by rfl⟩ : syracuseStep 112067 = 168101) B168101
theorem B112083 : Blo 111784 112083 := bstep (se 1 (by rfl) ⟨84062, by rfl⟩ : syracuseStep 112083 = 168125) B168125
theorem B112099 : Blo 111784 112099 := bstep (se 1 (by rfl) ⟨84074, by rfl⟩ : syracuseStep 112099 = 168149) B168149
theorem B275939 : Blo 111784 275939 := bstep (se 1 (by rfl) ⟨206954, by rfl⟩ : syracuseStep 275939 = 413909) B413909
theorem B112115 : Blo 111784 112115 := bstep (se 1 (by rfl) ⟨84086, by rfl⟩ : syracuseStep 112115 = 168173) B168173
theorem B112131 : Blo 111784 112131 := bstep (se 1 (by rfl) ⟨84098, by rfl⟩ : syracuseStep 112131 = 168197) B168197
theorem B112147 : Blo 111784 112147 := bstep (se 1 (by rfl) ⟨84110, by rfl⟩ : syracuseStep 112147 = 168221) B168221
theorem B112163 : Blo 111784 112163 := bstep (se 1 (by rfl) ⟨84122, by rfl⟩ : syracuseStep 112163 = 168245) B168245
theorem B112179 : Blo 111784 112179 := bstep (se 1 (by rfl) ⟨84134, by rfl⟩ : syracuseStep 112179 = 168269) B168269
theorem B112195 : Blo 111784 112195 := bstep (se 1 (by rfl) ⟨84146, by rfl⟩ : syracuseStep 112195 = 168293) B168293
theorem B112211 : Blo 111784 112211 := bstep (se 1 (by rfl) ⟨84158, by rfl⟩ : syracuseStep 112211 = 168317) B168317
theorem B112227 : Blo 111784 112227 := bstep (se 1 (by rfl) ⟨84170, by rfl⟩ : syracuseStep 112227 = 168341) B168341
theorem B112243 : Blo 111784 112243 := bstep (se 1 (by rfl) ⟨84182, by rfl⟩ : syracuseStep 112243 = 168365) B168365
theorem B112259 : Blo 111784 112259 := bstep (se 1 (by rfl) ⟨84194, by rfl⟩ : syracuseStep 112259 = 168389) B168389
theorem B112275 : Blo 111784 112275 := bstep (se 1 (by rfl) ⟨84206, by rfl⟩ : syracuseStep 112275 = 168413) B168413
theorem B112291 : Blo 111784 112291 := bstep (se 1 (by rfl) ⟨84218, by rfl⟩ : syracuseStep 112291 = 168437) B168437
theorem B112307 : Blo 111784 112307 := bstep (se 1 (by rfl) ⟨84230, by rfl⟩ : syracuseStep 112307 = 168461) B168461
theorem B112323 : Blo 111784 112323 := bstep (se 1 (by rfl) ⟨84242, by rfl⟩ : syracuseStep 112323 = 168485) B168485
theorem B145091 : Blo 111784 145091 := bstep (se 1 (by rfl) ⟨108818, by rfl⟩ : syracuseStep 145091 = 217637) B217637
theorem B112339 : Blo 111784 112339 := bstep (se 1 (by rfl) ⟨84254, by rfl⟩ : syracuseStep 112339 = 168509) B168509
theorem B112355 : Blo 111784 112355 := bstep (se 1 (by rfl) ⟨84266, by rfl⟩ : syracuseStep 112355 = 168533) B168533
theorem B112371 : Blo 111784 112371 := bstep (se 1 (by rfl) ⟨84278, by rfl⟩ : syracuseStep 112371 = 168557) B168557
theorem B112387 : Blo 111784 112387 := bstep (se 1 (by rfl) ⟨84290, by rfl⟩ : syracuseStep 112387 = 168581) B168581
theorem B112403 : Blo 111784 112403 := bstep (se 1 (by rfl) ⟨84302, by rfl⟩ : syracuseStep 112403 = 168605) B168605
theorem B112419 : Blo 111784 112419 := bstep (se 1 (by rfl) ⟨84314, by rfl⟩ : syracuseStep 112419 = 168629) B168629
theorem B112435 : Blo 111784 112435 := bstep (se 1 (by rfl) ⟨84326, by rfl⟩ : syracuseStep 112435 = 168653) B168653
theorem B112451 : Blo 111784 112451 := bstep (se 1 (by rfl) ⟨84338, by rfl⟩ : syracuseStep 112451 = 168677) B168677
theorem B112467 : Blo 111784 112467 := bstep (se 1 (by rfl) ⟨84350, by rfl⟩ : syracuseStep 112467 = 168701) B168701
theorem B112483 : Blo 111784 112483 := bstep (se 1 (by rfl) ⟨84362, by rfl⟩ : syracuseStep 112483 = 168725) B168725
theorem B112499 : Blo 111784 112499 := bstep (se 1 (by rfl) ⟨84374, by rfl⟩ : syracuseStep 112499 = 168749) B168749
theorem B112515 : Blo 111784 112515 := bstep (se 1 (by rfl) ⟨84386, by rfl⟩ : syracuseStep 112515 = 168773) B168773
theorem B112531 : Blo 111784 112531 := bstep (se 1 (by rfl) ⟨84398, by rfl⟩ : syracuseStep 112531 = 168797) B168797
theorem B112547 : Blo 111784 112547 := bstep (se 1 (by rfl) ⟨84410, by rfl⟩ : syracuseStep 112547 = 168821) B168821
theorem B112563 : Blo 111784 112563 := bstep (se 1 (by rfl) ⟨84422, by rfl⟩ : syracuseStep 112563 = 168845) B168845
theorem B112579 : Blo 111784 112579 := bstep (se 1 (by rfl) ⟨84434, by rfl⟩ : syracuseStep 112579 = 168869) B168869
theorem B309187 : Blo 111784 309187 := bstep (se 1 (by rfl) ⟨231890, by rfl⟩ : syracuseStep 309187 = 463781) B463781
theorem B112595 : Blo 111784 112595 := bstep (se 1 (by rfl) ⟨84446, by rfl⟩ : syracuseStep 112595 = 168893) B168893
theorem B538595 : Blo 111784 538595 := bstep (se 1 (by rfl) ⟨403946, by rfl⟩ : syracuseStep 538595 = 807893) B807893
theorem B112611 : Blo 111784 112611 := bstep (se 1 (by rfl) ⟨84458, by rfl⟩ : syracuseStep 112611 = 168917) B168917
theorem B112627 : Blo 111784 112627 := bstep (se 1 (by rfl) ⟨84470, by rfl⟩ : syracuseStep 112627 = 168941) B168941
theorem B112643 : Blo 111784 112643 := bstep (se 1 (by rfl) ⟨84482, by rfl⟩ : syracuseStep 112643 = 168965) B168965
theorem B112659 : Blo 111784 112659 := bstep (se 1 (by rfl) ⟨84494, by rfl⟩ : syracuseStep 112659 = 168989) B168989
theorem B112675 : Blo 111784 112675 := bstep (se 1 (by rfl) ⟨84506, by rfl⟩ : syracuseStep 112675 = 169013) B169013
theorem B112691 : Blo 111784 112691 := bstep (se 1 (by rfl) ⟨84518, by rfl⟩ : syracuseStep 112691 = 169037) B169037
theorem B112707 : Blo 111784 112707 := bstep (se 1 (by rfl) ⟨84530, by rfl⟩ : syracuseStep 112707 = 169061) B169061
theorem B112723 : Blo 111784 112723 := bstep (se 1 (by rfl) ⟨84542, by rfl⟩ : syracuseStep 112723 = 169085) B169085
theorem B112739 : Blo 111784 112739 := bstep (se 1 (by rfl) ⟨84554, by rfl⟩ : syracuseStep 112739 = 169109) B169109
theorem B112755 : Blo 111784 112755 := bstep (se 1 (by rfl) ⟨84566, by rfl⟩ : syracuseStep 112755 = 169133) B169133
theorem B112771 : Blo 111784 112771 := bstep (se 1 (by rfl) ⟨84578, by rfl⟩ : syracuseStep 112771 = 169157) B169157
theorem B407693 : Blo 111784 407693 := bstep (se 3 (by rfl) ⟨76442, by rfl⟩ : syracuseStep 407693 = 152885) B152885
theorem B112787 : Blo 111784 112787 := bstep (se 1 (by rfl) ⟨84590, by rfl⟩ : syracuseStep 112787 = 169181) B169181
theorem B112803 : Blo 111784 112803 := bstep (se 1 (by rfl) ⟨84602, by rfl⟩ : syracuseStep 112803 = 169205) B169205
theorem B112819 : Blo 111784 112819 := bstep (se 1 (by rfl) ⟨84614, by rfl⟩ : syracuseStep 112819 = 169229) B169229
theorem B112835 : Blo 111784 112835 := bstep (se 1 (by rfl) ⟨84626, by rfl⟩ : syracuseStep 112835 = 169253) B169253
theorem B112851 : Blo 111784 112851 := bstep (se 1 (by rfl) ⟨84638, by rfl⟩ : syracuseStep 112851 = 169277) B169277
theorem B112867 : Blo 111784 112867 := bstep (se 1 (by rfl) ⟨84650, by rfl⟩ : syracuseStep 112867 = 169301) B169301
theorem B112883 : Blo 111784 112883 := bstep (se 1 (by rfl) ⟨84662, by rfl⟩ : syracuseStep 112883 = 169325) B169325
theorem B112899 : Blo 111784 112899 := bstep (se 1 (by rfl) ⟨84674, by rfl⟩ : syracuseStep 112899 = 169349) B169349
theorem B112915 : Blo 111784 112915 := bstep (se 1 (by rfl) ⟨84686, by rfl⟩ : syracuseStep 112915 = 169373) B169373
theorem B112931 : Blo 111784 112931 := bstep (se 1 (by rfl) ⟨84698, by rfl⟩ : syracuseStep 112931 = 169397) B169397
theorem B571697 : Blo 111784 571697 := bstep (se 2 (by rfl) ⟨214386, by rfl⟩ : syracuseStep 571697 = 428773) B428773
theorem B112947 : Blo 111784 112947 := bstep (se 1 (by rfl) ⟨84710, by rfl⟩ : syracuseStep 112947 = 169421) B169421
theorem B112963 : Blo 111784 112963 := bstep (se 1 (by rfl) ⟨84722, by rfl⟩ : syracuseStep 112963 = 169445) B169445
theorem B112979 : Blo 111784 112979 := bstep (se 1 (by rfl) ⟨84734, by rfl⟩ : syracuseStep 112979 = 169469) B169469
theorem B112995 : Blo 111784 112995 := bstep (se 1 (by rfl) ⟨84746, by rfl⟩ : syracuseStep 112995 = 169493) B169493
theorem B113011 : Blo 111784 113011 := bstep (se 1 (by rfl) ⟨84758, by rfl⟩ : syracuseStep 113011 = 169517) B169517
theorem B113027 : Blo 111784 113027 := bstep (se 1 (by rfl) ⟨84770, by rfl⟩ : syracuseStep 113027 = 169541) B169541
theorem B145795 : Blo 111784 145795 := bstep (se 1 (by rfl) ⟨109346, by rfl⟩ : syracuseStep 145795 = 218693) B218693
theorem B113043 : Blo 111784 113043 := bstep (se 1 (by rfl) ⟨84782, by rfl⟩ : syracuseStep 113043 = 169565) B169565
theorem B113059 : Blo 111784 113059 := bstep (se 1 (by rfl) ⟨84794, by rfl⟩ : syracuseStep 113059 = 169589) B169589
theorem B113075 : Blo 111784 113075 := bstep (se 1 (by rfl) ⟨84806, by rfl⟩ : syracuseStep 113075 = 169613) B169613
theorem B113091 : Blo 111784 113091 := bstep (se 1 (by rfl) ⟨84818, by rfl⟩ : syracuseStep 113091 = 169637) B169637
theorem B113107 : Blo 111784 113107 := bstep (se 1 (by rfl) ⟨84830, by rfl⟩ : syracuseStep 113107 = 169661) B169661
theorem B113123 : Blo 111784 113123 := bstep (se 1 (by rfl) ⟨84842, by rfl⟩ : syracuseStep 113123 = 169685) B169685
theorem B145891 : Blo 111784 145891 := bstep (se 1 (by rfl) ⟨109418, by rfl⟩ : syracuseStep 145891 = 218837) B218837
theorem B113139 : Blo 111784 113139 := bstep (se 1 (by rfl) ⟨84854, by rfl⟩ : syracuseStep 113139 = 169709) B169709
theorem B113155 : Blo 111784 113155 := bstep (se 1 (by rfl) ⟨84866, by rfl⟩ : syracuseStep 113155 = 169733) B169733
theorem B113171 : Blo 111784 113171 := bstep (se 1 (by rfl) ⟨84878, by rfl⟩ : syracuseStep 113171 = 169757) B169757
theorem B113187 : Blo 111784 113187 := bstep (se 1 (by rfl) ⟨84890, by rfl⟩ : syracuseStep 113187 = 169781) B169781
theorem B113203 : Blo 111784 113203 := bstep (se 1 (by rfl) ⟨84902, by rfl⟩ : syracuseStep 113203 = 169805) B169805
theorem B113219 : Blo 111784 113219 := bstep (se 1 (by rfl) ⟨84914, by rfl⟩ : syracuseStep 113219 = 169829) B169829
theorem B440909 : Blo 111784 440909 := bstep (se 3 (by rfl) ⟨82670, by rfl⟩ : syracuseStep 440909 = 165341) B165341
theorem B113235 : Blo 111784 113235 := bstep (se 1 (by rfl) ⟨84926, by rfl⟩ : syracuseStep 113235 = 169853) B169853
theorem B113251 : Blo 111784 113251 := bstep (se 1 (by rfl) ⟨84938, by rfl⟩ : syracuseStep 113251 = 169877) B169877
theorem B113267 : Blo 111784 113267 := bstep (se 1 (by rfl) ⟨84950, by rfl⟩ : syracuseStep 113267 = 169901) B169901
theorem B113283 : Blo 111784 113283 := bstep (se 1 (by rfl) ⟨84962, by rfl⟩ : syracuseStep 113283 = 169925) B169925
theorem B113299 : Blo 111784 113299 := bstep (se 1 (by rfl) ⟨84974, by rfl⟩ : syracuseStep 113299 = 169949) B169949
theorem B113315 : Blo 111784 113315 := bstep (se 1 (by rfl) ⟨84986, by rfl⟩ : syracuseStep 113315 = 169973) B169973
theorem B113331 : Blo 111784 113331 := bstep (se 1 (by rfl) ⟨84998, by rfl⟩ : syracuseStep 113331 = 169997) B169997
theorem B113347 : Blo 111784 113347 := bstep (se 1 (by rfl) ⟨85010, by rfl⟩ : syracuseStep 113347 = 170021) B170021
theorem B408269 : Blo 111784 408269 := bstep (se 3 (by rfl) ⟨76550, by rfl⟩ : syracuseStep 408269 = 153101) B153101
theorem B342737 : Blo 111784 342737 := bstep (se 2 (by rfl) ⟨128526, by rfl⟩ : syracuseStep 342737 = 257053) B257053
theorem B113363 : Blo 111784 113363 := bstep (se 1 (by rfl) ⟨85022, by rfl⟩ : syracuseStep 113363 = 170045) B170045
theorem B113379 : Blo 111784 113379 := bstep (se 1 (by rfl) ⟨85034, by rfl⟩ : syracuseStep 113379 = 170069) B170069
theorem B277219 : Blo 111784 277219 := bstep (se 1 (by rfl) ⟨207914, by rfl⟩ : syracuseStep 277219 = 415829) B415829
theorem B113395 : Blo 111784 113395 := bstep (se 1 (by rfl) ⟨85046, by rfl⟩ : syracuseStep 113395 = 170093) B170093
theorem B113411 : Blo 111784 113411 := bstep (se 1 (by rfl) ⟨85058, by rfl⟩ : syracuseStep 113411 = 170117) B170117
theorem B113427 : Blo 111784 113427 := bstep (se 1 (by rfl) ⟨85070, by rfl⟩ : syracuseStep 113427 = 170141) B170141
theorem B113443 : Blo 111784 113443 := bstep (se 1 (by rfl) ⟨85082, by rfl⟩ : syracuseStep 113443 = 170165) B170165
theorem B113459 : Blo 111784 113459 := bstep (se 1 (by rfl) ⟨85094, by rfl⟩ : syracuseStep 113459 = 170189) B170189
theorem B113475 : Blo 111784 113475 := bstep (se 1 (by rfl) ⟨85106, by rfl⟩ : syracuseStep 113475 = 170213) B170213
theorem B113491 : Blo 111784 113491 := bstep (se 1 (by rfl) ⟨85118, by rfl⟩ : syracuseStep 113491 = 170237) B170237
theorem B113507 : Blo 111784 113507 := bstep (se 1 (by rfl) ⟨85130, by rfl⟩ : syracuseStep 113507 = 170261) B170261
theorem B113523 : Blo 111784 113523 := bstep (se 1 (by rfl) ⟨85142, by rfl⟩ : syracuseStep 113523 = 170285) B170285
theorem B113539 : Blo 111784 113539 := bstep (se 1 (by rfl) ⟨85154, by rfl⟩ : syracuseStep 113539 = 170309) B170309
theorem B113555 : Blo 111784 113555 := bstep (se 1 (by rfl) ⟨85166, by rfl⟩ : syracuseStep 113555 = 170333) B170333
theorem B113571 : Blo 111784 113571 := bstep (se 1 (by rfl) ⟨85178, by rfl⟩ : syracuseStep 113571 = 170357) B170357
theorem B113587 : Blo 111784 113587 := bstep (se 1 (by rfl) ⟨85190, by rfl⟩ : syracuseStep 113587 = 170381) B170381
theorem B113603 : Blo 111784 113603 := bstep (se 1 (by rfl) ⟨85202, by rfl⟩ : syracuseStep 113603 = 170405) B170405
theorem B113619 : Blo 111784 113619 := bstep (se 1 (by rfl) ⟨85214, by rfl⟩ : syracuseStep 113619 = 170429) B170429
theorem B146387 : Blo 111784 146387 := bstep (se 1 (by rfl) ⟨109790, by rfl⟩ : syracuseStep 146387 = 219581) B219581
theorem B113635 : Blo 111784 113635 := bstep (se 1 (by rfl) ⟨85226, by rfl⟩ : syracuseStep 113635 = 170453) B170453
theorem B113651 : Blo 111784 113651 := bstep (se 1 (by rfl) ⟨85238, by rfl⟩ : syracuseStep 113651 = 170477) B170477
theorem B113667 : Blo 111784 113667 := bstep (se 1 (by rfl) ⟨85250, by rfl⟩ : syracuseStep 113667 = 170501) B170501
theorem B244739 : Blo 111784 244739 := bstep (se 1 (by rfl) ⟨183554, by rfl⟩ : syracuseStep 244739 = 367109) B367109
theorem B113683 : Blo 111784 113683 := bstep (se 1 (by rfl) ⟨85262, by rfl⟩ : syracuseStep 113683 = 170525) B170525
theorem B113699 : Blo 111784 113699 := bstep (se 1 (by rfl) ⟨85274, by rfl⟩ : syracuseStep 113699 = 170549) B170549
theorem B113715 : Blo 111784 113715 := bstep (se 1 (by rfl) ⟨85286, by rfl⟩ : syracuseStep 113715 = 170573) B170573
theorem B113731 : Blo 111784 113731 := bstep (se 1 (by rfl) ⟨85298, by rfl⟩ : syracuseStep 113731 = 170597) B170597
theorem B113747 : Blo 111784 113747 := bstep (se 1 (by rfl) ⟨85310, by rfl⟩ : syracuseStep 113747 = 170621) B170621
theorem B113763 : Blo 111784 113763 := bstep (se 1 (by rfl) ⟨85322, by rfl⟩ : syracuseStep 113763 = 170645) B170645
theorem B113779 : Blo 111784 113779 := bstep (se 1 (by rfl) ⟨85334, by rfl⟩ : syracuseStep 113779 = 170669) B170669
theorem B113795 : Blo 111784 113795 := bstep (se 1 (by rfl) ⟨85346, by rfl⟩ : syracuseStep 113795 = 170693) B170693
theorem B113811 : Blo 111784 113811 := bstep (se 1 (by rfl) ⟨85358, by rfl⟩ : syracuseStep 113811 = 170717) B170717
theorem B179363 : Blo 111784 179363 := bstep (se 1 (by rfl) ⟨134522, by rfl⟩ : syracuseStep 179363 = 269045) B269045
theorem B113827 : Blo 111784 113827 := bstep (se 1 (by rfl) ⟨85370, by rfl⟩ : syracuseStep 113827 = 170741) B170741
theorem B113843 : Blo 111784 113843 := bstep (se 1 (by rfl) ⟨85382, by rfl⟩ : syracuseStep 113843 = 170765) B170765
theorem B113859 : Blo 111784 113859 := bstep (se 1 (by rfl) ⟨85394, by rfl⟩ : syracuseStep 113859 = 170789) B170789
theorem B113875 : Blo 111784 113875 := bstep (se 1 (by rfl) ⟨85406, by rfl⟩ : syracuseStep 113875 = 170813) B170813
theorem B113891 : Blo 111784 113891 := bstep (se 1 (by rfl) ⟨85418, by rfl⟩ : syracuseStep 113891 = 170837) B170837
theorem B1391843 : Blo 111784 1391843 := bstep (se 1 (by rfl) ⟨1043882, by rfl⟩ : syracuseStep 1391843 = 2087765) B2087765
theorem B113907 : Blo 111784 113907 := bstep (se 1 (by rfl) ⟨85430, by rfl⟩ : syracuseStep 113907 = 170861) B170861
theorem B113923 : Blo 111784 113923 := bstep (se 1 (by rfl) ⟨85442, by rfl⟩ : syracuseStep 113923 = 170885) B170885
theorem B113939 : Blo 111784 113939 := bstep (se 1 (by rfl) ⟨85454, by rfl⟩ : syracuseStep 113939 = 170909) B170909
theorem B539939 : Blo 111784 539939 := bstep (se 1 (by rfl) ⟨404954, by rfl⟩ : syracuseStep 539939 = 809909) B809909
theorem B113955 : Blo 111784 113955 := bstep (se 1 (by rfl) ⟨85466, by rfl⟩ : syracuseStep 113955 = 170933) B170933
theorem B113971 : Blo 111784 113971 := bstep (se 1 (by rfl) ⟨85478, by rfl⟩ : syracuseStep 113971 = 170957) B170957
theorem B212291 : Blo 111784 212291 := bstep (se 1 (by rfl) ⟨159218, by rfl⟩ : syracuseStep 212291 = 318437) B318437
theorem B113987 : Blo 111784 113987 := bstep (se 1 (by rfl) ⟨85490, by rfl⟩ : syracuseStep 113987 = 170981) B170981
theorem B114003 : Blo 111784 114003 := bstep (se 1 (by rfl) ⟨85502, by rfl⟩ : syracuseStep 114003 = 171005) B171005
theorem B114019 : Blo 111784 114019 := bstep (se 1 (by rfl) ⟨85514, by rfl⟩ : syracuseStep 114019 = 171029) B171029
theorem B114035 : Blo 111784 114035 := bstep (se 1 (by rfl) ⟨85526, by rfl⟩ : syracuseStep 114035 = 171053) B171053
theorem B114051 : Blo 111784 114051 := bstep (se 1 (by rfl) ⟨85538, by rfl⟩ : syracuseStep 114051 = 171077) B171077
theorem B114067 : Blo 111784 114067 := bstep (se 1 (by rfl) ⟨85550, by rfl⟩ : syracuseStep 114067 = 171101) B171101
theorem B310691 : Blo 111784 310691 := bstep (se 1 (by rfl) ⟨233018, by rfl⟩ : syracuseStep 310691 = 466037) B466037
theorem B114083 : Blo 111784 114083 := bstep (se 1 (by rfl) ⟨85562, by rfl⟩ : syracuseStep 114083 = 171125) B171125
theorem B114099 : Blo 111784 114099 := bstep (se 1 (by rfl) ⟨85574, by rfl⟩ : syracuseStep 114099 = 171149) B171149
theorem B114115 : Blo 111784 114115 := bstep (se 1 (by rfl) ⟨85586, by rfl⟩ : syracuseStep 114115 = 171173) B171173
theorem B114131 : Blo 111784 114131 := bstep (se 1 (by rfl) ⟨85598, by rfl⟩ : syracuseStep 114131 = 171197) B171197
theorem B114147 : Blo 111784 114147 := bstep (se 1 (by rfl) ⟨85610, by rfl⟩ : syracuseStep 114147 = 171221) B171221
theorem B114163 : Blo 111784 114163 := bstep (se 1 (by rfl) ⟨85622, by rfl⟩ : syracuseStep 114163 = 171245) B171245
theorem B114179 : Blo 111784 114179 := bstep (se 1 (by rfl) ⟨85634, by rfl⟩ : syracuseStep 114179 = 171269) B171269
theorem B114195 : Blo 111784 114195 := bstep (se 1 (by rfl) ⟨85646, by rfl⟩ : syracuseStep 114195 = 171293) B171293
theorem B114211 : Blo 111784 114211 := bstep (se 1 (by rfl) ⟨85658, by rfl⟩ : syracuseStep 114211 = 171317) B171317
theorem B638513 : Blo 111784 638513 := bstep (se 2 (by rfl) ⟨239442, by rfl⟩ : syracuseStep 638513 = 478885) B478885
theorem B114227 : Blo 111784 114227 := bstep (se 1 (by rfl) ⟨85670, by rfl⟩ : syracuseStep 114227 = 171341) B171341
theorem B114243 : Blo 111784 114243 := bstep (se 1 (by rfl) ⟨85682, by rfl⟩ : syracuseStep 114243 = 171365) B171365
theorem B114259 : Blo 111784 114259 := bstep (se 1 (by rfl) ⟨85694, by rfl⟩ : syracuseStep 114259 = 171389) B171389
theorem B114275 : Blo 111784 114275 := bstep (se 1 (by rfl) ⟨85706, by rfl⟩ : syracuseStep 114275 = 171413) B171413
theorem B114291 : Blo 111784 114291 := bstep (se 1 (by rfl) ⟨85718, by rfl⟩ : syracuseStep 114291 = 171437) B171437
theorem B114307 : Blo 111784 114307 := bstep (se 1 (by rfl) ⟨85730, by rfl⟩ : syracuseStep 114307 = 171461) B171461
theorem B114323 : Blo 111784 114323 := bstep (se 1 (by rfl) ⟨85742, by rfl⟩ : syracuseStep 114323 = 171485) B171485
theorem B114339 : Blo 111784 114339 := bstep (se 1 (by rfl) ⟨85754, by rfl⟩ : syracuseStep 114339 = 171509) B171509
theorem B114355 : Blo 111784 114355 := bstep (se 1 (by rfl) ⟨85766, by rfl⟩ : syracuseStep 114355 = 171533) B171533
theorem B114371 : Blo 111784 114371 := bstep (se 1 (by rfl) ⟨85778, by rfl⟩ : syracuseStep 114371 = 171557) B171557
theorem B114387 : Blo 111784 114387 := bstep (se 1 (by rfl) ⟨85790, by rfl⟩ : syracuseStep 114387 = 171581) B171581
theorem B573155 : Blo 111784 573155 := bstep (se 1 (by rfl) ⟨429866, by rfl⟩ : syracuseStep 573155 = 859733) B859733
theorem B114403 : Blo 111784 114403 := bstep (se 1 (by rfl) ⟨85802, by rfl⟩ : syracuseStep 114403 = 171605) B171605
theorem B114419 : Blo 111784 114419 := bstep (se 1 (by rfl) ⟨85814, by rfl⟩ : syracuseStep 114419 = 171629) B171629
theorem B114435 : Blo 111784 114435 := bstep (se 1 (by rfl) ⟨85826, by rfl⟩ : syracuseStep 114435 = 171653) B171653
theorem B114451 : Blo 111784 114451 := bstep (se 1 (by rfl) ⟨85838, by rfl⟩ : syracuseStep 114451 = 171677) B171677
theorem B114467 : Blo 111784 114467 := bstep (se 1 (by rfl) ⟨85850, by rfl⟩ : syracuseStep 114467 = 171701) B171701
theorem B114483 : Blo 111784 114483 := bstep (se 1 (by rfl) ⟨85862, by rfl⟩ : syracuseStep 114483 = 171725) B171725
theorem B114499 : Blo 111784 114499 := bstep (se 1 (by rfl) ⟨85874, by rfl⟩ : syracuseStep 114499 = 171749) B171749
theorem B114515 : Blo 111784 114515 := bstep (se 1 (by rfl) ⟨85886, by rfl⟩ : syracuseStep 114515 = 171773) B171773
theorem B114531 : Blo 111784 114531 := bstep (se 1 (by rfl) ⟨85898, by rfl⟩ : syracuseStep 114531 = 171797) B171797
theorem B114547 : Blo 111784 114547 := bstep (se 1 (by rfl) ⟨85910, by rfl⟩ : syracuseStep 114547 = 171821) B171821
theorem B114563 : Blo 111784 114563 := bstep (se 1 (by rfl) ⟨85922, by rfl⟩ : syracuseStep 114563 = 171845) B171845
theorem B114579 : Blo 111784 114579 := bstep (se 1 (by rfl) ⟨85934, by rfl⟩ : syracuseStep 114579 = 171869) B171869
theorem B114595 : Blo 111784 114595 := bstep (se 1 (by rfl) ⟨85946, by rfl⟩ : syracuseStep 114595 = 171893) B171893
theorem B540593 : Blo 111784 540593 := bstep (se 2 (by rfl) ⟨202722, by rfl⟩ : syracuseStep 540593 = 405445) B405445
theorem B114611 : Blo 111784 114611 := bstep (se 1 (by rfl) ⟨85958, by rfl⟩ : syracuseStep 114611 = 171917) B171917
theorem B114627 : Blo 111784 114627 := bstep (se 1 (by rfl) ⟨85970, by rfl⟩ : syracuseStep 114627 = 171941) B171941
theorem B114643 : Blo 111784 114643 := bstep (se 1 (by rfl) ⟨85982, by rfl⟩ : syracuseStep 114643 = 171965) B171965
theorem B114659 : Blo 111784 114659 := bstep (se 1 (by rfl) ⟨85994, by rfl⟩ : syracuseStep 114659 = 171989) B171989
theorem B114675 : Blo 111784 114675 := bstep (se 1 (by rfl) ⟨86006, by rfl⟩ : syracuseStep 114675 = 172013) B172013
theorem B114691 : Blo 111784 114691 := bstep (se 1 (by rfl) ⟨86018, by rfl⟩ : syracuseStep 114691 = 172037) B172037
theorem B114707 : Blo 111784 114707 := bstep (se 1 (by rfl) ⟨86030, by rfl⟩ : syracuseStep 114707 = 172061) B172061
theorem B114723 : Blo 111784 114723 := bstep (se 1 (by rfl) ⟨86042, by rfl⟩ : syracuseStep 114723 = 172085) B172085
theorem B114739 : Blo 111784 114739 := bstep (se 1 (by rfl) ⟨86054, by rfl⟩ : syracuseStep 114739 = 172109) B172109
theorem B114755 : Blo 111784 114755 := bstep (se 1 (by rfl) ⟨86066, by rfl⟩ : syracuseStep 114755 = 172133) B172133
theorem B114771 : Blo 111784 114771 := bstep (se 1 (by rfl) ⟨86078, by rfl⟩ : syracuseStep 114771 = 172157) B172157
theorem B114787 : Blo 111784 114787 := bstep (se 1 (by rfl) ⟨86090, by rfl⟩ : syracuseStep 114787 = 172181) B172181
theorem B114803 : Blo 111784 114803 := bstep (se 1 (by rfl) ⟨86102, by rfl⟩ : syracuseStep 114803 = 172205) B172205
theorem B114819 : Blo 111784 114819 := bstep (se 1 (by rfl) ⟨86114, by rfl⟩ : syracuseStep 114819 = 172229) B172229
theorem B114835 : Blo 111784 114835 := bstep (se 1 (by rfl) ⟨86126, by rfl⟩ : syracuseStep 114835 = 172253) B172253
theorem B114851 : Blo 111784 114851 := bstep (se 1 (by rfl) ⟨86138, by rfl⟩ : syracuseStep 114851 = 172277) B172277
theorem B114867 : Blo 111784 114867 := bstep (se 1 (by rfl) ⟨86150, by rfl⟩ : syracuseStep 114867 = 172301) B172301
theorem B213187 : Blo 111784 213187 := bstep (se 1 (by rfl) ⟨159890, by rfl⟩ : syracuseStep 213187 = 319781) B319781
theorem B114883 : Blo 111784 114883 := bstep (se 1 (by rfl) ⟨86162, by rfl⟩ : syracuseStep 114883 = 172325) B172325
theorem B114899 : Blo 111784 114899 := bstep (se 1 (by rfl) ⟨86174, by rfl⟩ : syracuseStep 114899 = 172349) B172349
theorem B114915 : Blo 111784 114915 := bstep (se 1 (by rfl) ⟨86186, by rfl⟩ : syracuseStep 114915 = 172373) B172373
theorem B245987 : Blo 111784 245987 := bstep (se 1 (by rfl) ⟨184490, by rfl⟩ : syracuseStep 245987 = 368981) B368981
theorem B999665 : Blo 111784 999665 := bstep (se 2 (by rfl) ⟨374874, by rfl⟩ : syracuseStep 999665 = 749749) B749749
theorem B114931 : Blo 111784 114931 := bstep (se 1 (by rfl) ⟨86198, by rfl⟩ : syracuseStep 114931 = 172397) B172397
theorem B114947 : Blo 111784 114947 := bstep (se 1 (by rfl) ⟨86210, by rfl⟩ : syracuseStep 114947 = 172421) B172421
theorem B114963 : Blo 111784 114963 := bstep (se 1 (by rfl) ⟨86222, by rfl⟩ : syracuseStep 114963 = 172445) B172445
theorem B114979 : Blo 111784 114979 := bstep (se 1 (by rfl) ⟨86234, by rfl⟩ : syracuseStep 114979 = 172469) B172469
theorem B114995 : Blo 111784 114995 := bstep (se 1 (by rfl) ⟨86246, by rfl⟩ : syracuseStep 114995 = 172493) B172493
theorem B115011 : Blo 111784 115011 := bstep (se 1 (by rfl) ⟨86258, by rfl⟩ : syracuseStep 115011 = 172517) B172517
theorem B115027 : Blo 111784 115027 := bstep (se 1 (by rfl) ⟨86270, by rfl⟩ : syracuseStep 115027 = 172541) B172541
theorem B213347 : Blo 111784 213347 := bstep (se 1 (by rfl) ⟨160010, by rfl⟩ : syracuseStep 213347 = 320021) B320021
theorem B147811 : Blo 111784 147811 := bstep (se 1 (by rfl) ⟨110858, by rfl⟩ : syracuseStep 147811 = 221717) B221717
theorem B115043 : Blo 111784 115043 := bstep (se 1 (by rfl) ⟨86282, by rfl⟩ : syracuseStep 115043 = 172565) B172565
theorem B115059 : Blo 111784 115059 := bstep (se 1 (by rfl) ⟨86294, by rfl⟩ : syracuseStep 115059 = 172589) B172589
theorem B115075 : Blo 111784 115075 := bstep (se 1 (by rfl) ⟨86306, by rfl⟩ : syracuseStep 115075 = 172613) B172613
theorem B115091 : Blo 111784 115091 := bstep (se 1 (by rfl) ⟨86318, by rfl⟩ : syracuseStep 115091 = 172637) B172637
theorem B115107 : Blo 111784 115107 := bstep (se 1 (by rfl) ⟨86330, by rfl⟩ : syracuseStep 115107 = 172661) B172661
theorem B115123 : Blo 111784 115123 := bstep (se 1 (by rfl) ⟨86342, by rfl⟩ : syracuseStep 115123 = 172685) B172685
theorem B115139 : Blo 111784 115139 := bstep (se 1 (by rfl) ⟨86354, by rfl⟩ : syracuseStep 115139 = 172709) B172709
theorem B377297 : Blo 111784 377297 := bstep (se 2 (by rfl) ⟨141486, by rfl⟩ : syracuseStep 377297 = 282973) B282973
theorem B115155 : Blo 111784 115155 := bstep (se 1 (by rfl) ⟨86366, by rfl⟩ : syracuseStep 115155 = 172733) B172733
theorem B115171 : Blo 111784 115171 := bstep (se 1 (by rfl) ⟨86378, by rfl⟩ : syracuseStep 115171 = 172757) B172757
theorem B115187 : Blo 111784 115187 := bstep (se 1 (by rfl) ⟨86390, by rfl⟩ : syracuseStep 115187 = 172781) B172781
theorem B115203 : Blo 111784 115203 := bstep (se 1 (by rfl) ⟨86402, by rfl⟩ : syracuseStep 115203 = 172805) B172805
theorem B573965 : Blo 111784 573965 := bstep (se 3 (by rfl) ⟨107618, by rfl⟩ : syracuseStep 573965 = 215237) B215237
theorem B311825 : Blo 111784 311825 := bstep (se 2 (by rfl) ⟨116934, by rfl⟩ : syracuseStep 311825 = 233869) B233869
theorem B115219 : Blo 111784 115219 := bstep (se 1 (by rfl) ⟨86414, by rfl⟩ : syracuseStep 115219 = 172829) B172829
theorem B115235 : Blo 111784 115235 := bstep (se 1 (by rfl) ⟨86426, by rfl⟩ : syracuseStep 115235 = 172853) B172853
theorem B180787 : Blo 111784 180787 := bstep (se 1 (by rfl) ⟨135590, by rfl⟩ : syracuseStep 180787 = 271181) B271181
theorem B115251 : Blo 111784 115251 := bstep (se 1 (by rfl) ⟨86438, by rfl⟩ : syracuseStep 115251 = 172877) B172877
theorem B115267 : Blo 111784 115267 := bstep (se 1 (by rfl) ⟨86450, by rfl⟩ : syracuseStep 115267 = 172901) B172901
theorem B115283 : Blo 111784 115283 := bstep (se 1 (by rfl) ⟨86462, by rfl⟩ : syracuseStep 115283 = 172925) B172925
theorem B115299 : Blo 111784 115299 := bstep (se 1 (by rfl) ⟨86474, by rfl⟩ : syracuseStep 115299 = 172949) B172949
theorem B115315 : Blo 111784 115315 := bstep (se 1 (by rfl) ⟨86486, by rfl⟩ : syracuseStep 115315 = 172973) B172973
theorem B115331 : Blo 111784 115331 := bstep (se 1 (by rfl) ⟨86498, by rfl⟩ : syracuseStep 115331 = 172997) B172997
theorem B180883 : Blo 111784 180883 := bstep (se 1 (by rfl) ⟨135662, by rfl⟩ : syracuseStep 180883 = 271325) B271325
theorem B115347 : Blo 111784 115347 := bstep (se 1 (by rfl) ⟨86510, by rfl⟩ : syracuseStep 115347 = 173021) B173021
theorem B115363 : Blo 111784 115363 := bstep (se 1 (by rfl) ⟨86522, by rfl⟩ : syracuseStep 115363 = 173045) B173045
theorem B115379 : Blo 111784 115379 := bstep (se 1 (by rfl) ⟨86534, by rfl⟩ : syracuseStep 115379 = 173069) B173069
theorem B115395 : Blo 111784 115395 := bstep (se 1 (by rfl) ⟨86546, by rfl⟩ : syracuseStep 115395 = 173093) B173093
theorem B115411 : Blo 111784 115411 := bstep (se 1 (by rfl) ⟨86558, by rfl⟩ : syracuseStep 115411 = 173117) B173117
theorem B115427 : Blo 111784 115427 := bstep (se 1 (by rfl) ⟨86570, by rfl⟩ : syracuseStep 115427 = 173141) B173141
theorem B115443 : Blo 111784 115443 := bstep (se 1 (by rfl) ⟨86582, by rfl⟩ : syracuseStep 115443 = 173165) B173165
theorem B115459 : Blo 111784 115459 := bstep (se 1 (by rfl) ⟨86594, by rfl⟩ : syracuseStep 115459 = 173189) B173189
theorem B115475 : Blo 111784 115475 := bstep (se 1 (by rfl) ⟨86606, by rfl⟩ : syracuseStep 115475 = 173213) B173213
theorem B115491 : Blo 111784 115491 := bstep (se 1 (by rfl) ⟨86618, by rfl⟩ : syracuseStep 115491 = 173237) B173237
theorem B246577 : Blo 111784 246577 := bstep (se 2 (by rfl) ⟨92466, by rfl⟩ : syracuseStep 246577 = 184933) B184933
theorem B181043 : Blo 111784 181043 := bstep (se 1 (by rfl) ⟨135782, by rfl⟩ : syracuseStep 181043 = 271565) B271565
theorem B115507 : Blo 111784 115507 := bstep (se 1 (by rfl) ⟨86630, by rfl⟩ : syracuseStep 115507 = 173261) B173261
theorem B115523 : Blo 111784 115523 := bstep (se 1 (by rfl) ⟨86642, by rfl⟩ : syracuseStep 115523 = 173285) B173285
theorem B115539 : Blo 111784 115539 := bstep (se 1 (by rfl) ⟨86654, by rfl⟩ : syracuseStep 115539 = 173309) B173309
theorem B115555 : Blo 111784 115555 := bstep (se 1 (by rfl) ⟨86666, by rfl⟩ : syracuseStep 115555 = 173333) B173333
theorem B115571 : Blo 111784 115571 := bstep (se 1 (by rfl) ⟨86678, by rfl⟩ : syracuseStep 115571 = 173357) B173357
theorem B115587 : Blo 111784 115587 := bstep (se 1 (by rfl) ⟨86690, by rfl⟩ : syracuseStep 115587 = 173381) B173381
theorem B115603 : Blo 111784 115603 := bstep (se 1 (by rfl) ⟨86702, by rfl⟩ : syracuseStep 115603 = 173405) B173405
theorem B115619 : Blo 111784 115619 := bstep (se 1 (by rfl) ⟨86714, by rfl⟩ : syracuseStep 115619 = 173429) B173429
theorem B115635 : Blo 111784 115635 := bstep (se 1 (by rfl) ⟨86726, by rfl⟩ : syracuseStep 115635 = 173453) B173453
theorem B115651 : Blo 111784 115651 := bstep (se 1 (by rfl) ⟨86738, by rfl⟩ : syracuseStep 115651 = 173477) B173477
theorem B115667 : Blo 111784 115667 := bstep (se 1 (by rfl) ⟨86750, by rfl⟩ : syracuseStep 115667 = 173501) B173501
theorem B639971 : Blo 111784 639971 := bstep (se 1 (by rfl) ⟨479978, by rfl⟩ : syracuseStep 639971 = 959957) B959957
theorem B115683 : Blo 111784 115683 := bstep (se 1 (by rfl) ⟨86762, by rfl⟩ : syracuseStep 115683 = 173525) B173525
theorem B377837 : Blo 111784 377837 := bstep (se 3 (by rfl) ⟨70844, by rfl⟩ : syracuseStep 377837 = 141689) B141689
theorem B115699 : Blo 111784 115699 := bstep (se 1 (by rfl) ⟨86774, by rfl⟩ : syracuseStep 115699 = 173549) B173549
theorem B115715 : Blo 111784 115715 := bstep (se 1 (by rfl) ⟨86786, by rfl⟩ : syracuseStep 115715 = 173573) B173573
theorem B148483 : Blo 111784 148483 := bstep (se 1 (by rfl) ⟨111362, by rfl⟩ : syracuseStep 148483 = 222725) B222725
theorem B115731 : Blo 111784 115731 := bstep (se 1 (by rfl) ⟨86798, by rfl⟩ : syracuseStep 115731 = 173597) B173597
theorem B377891 : Blo 111784 377891 := bstep (se 1 (by rfl) ⟨283418, by rfl⟩ : syracuseStep 377891 = 566837) B566837
theorem B115747 : Blo 111784 115747 := bstep (se 1 (by rfl) ⟨86810, by rfl⟩ : syracuseStep 115747 = 173621) B173621
theorem B115763 : Blo 111784 115763 := bstep (se 1 (by rfl) ⟨86822, by rfl⟩ : syracuseStep 115763 = 173645) B173645
theorem B115779 : Blo 111784 115779 := bstep (se 1 (by rfl) ⟨86834, by rfl⟩ : syracuseStep 115779 = 173669) B173669
theorem B312419 : Blo 111784 312419 := bstep (se 1 (by rfl) ⟨234314, by rfl⟩ : syracuseStep 312419 = 468629) B468629
theorem B378161 : Blo 111784 378161 := bstep (se 2 (by rfl) ⟨141810, by rfl⟩ : syracuseStep 378161 = 283621) B283621
theorem B214417 : Blo 111784 214417 := bstep (se 2 (by rfl) ⟨80406, by rfl⟩ : syracuseStep 214417 = 160813) B160813
theorem B247249 : Blo 111784 247249 := bstep (se 2 (by rfl) ⟨92718, by rfl⟩ : syracuseStep 247249 = 185437) B185437
theorem B542285 : Blo 111784 542285 := bstep (se 3 (by rfl) ⟨101678, by rfl⟩ : syracuseStep 542285 = 203357) B203357
theorem B182017 : Blo 111784 182017 := bstep (se 2 (by rfl) ⟨68256, by rfl⟩ : syracuseStep 182017 = 136513) B136513
theorem B542513 : Blo 111784 542513 := bstep (se 2 (by rfl) ⟨203442, by rfl⟩ : syracuseStep 542513 = 406885) B406885
theorem B378701 : Blo 111784 378701 := bstep (se 3 (by rfl) ⟨71006, by rfl⟩ : syracuseStep 378701 = 142013) B142013
theorem B378755 : Blo 111784 378755 := bstep (se 1 (by rfl) ⟨284066, by rfl⟩ : syracuseStep 378755 = 568133) B568133
theorem B640973 : Blo 111784 640973 := bstep (se 3 (by rfl) ⟨120182, by rfl⟩ : syracuseStep 640973 = 240365) B240365
theorem B379025 : Blo 111784 379025 := bstep (se 2 (by rfl) ⟨142134, by rfl⟩ : syracuseStep 379025 = 284269) B284269
theorem B411875 : Blo 111784 411875 := bstep (se 1 (by rfl) ⟨308906, by rfl⟩ : syracuseStep 411875 = 617813) B617813
theorem B215473 : Blo 111784 215473 := bstep (se 2 (by rfl) ⟨80802, by rfl⟩ : syracuseStep 215473 = 161605) B161605
theorem B379565 : Blo 111784 379565 := bstep (se 3 (by rfl) ⟨71168, by rfl⟩ : syracuseStep 379565 = 142337) B142337
theorem B379619 : Blo 111784 379619 := bstep (se 1 (by rfl) ⟨284714, by rfl⟩ : syracuseStep 379619 = 569429) B569429
theorem B1395427 : Blo 111784 1395427 := bstep (se 1 (by rfl) ⟨1046570, by rfl⟩ : syracuseStep 1395427 = 2093141) B2093141
theorem B215875 : Blo 111784 215875 := bstep (se 1 (by rfl) ⟨161906, by rfl⟩ : syracuseStep 215875 = 323813) B323813
theorem B445283 : Blo 111784 445283 := bstep (se 1 (by rfl) ⟨333962, by rfl⟩ : syracuseStep 445283 = 667925) B667925
theorem B215921 : Blo 111784 215921 := bstep (se 2 (by rfl) ⟨80970, by rfl⟩ : syracuseStep 215921 = 161941) B161941
theorem B379889 : Blo 111784 379889 := bstep (se 2 (by rfl) ⟨142458, by rfl⟩ : syracuseStep 379889 = 284917) B284917
theorem B216209 : Blo 111784 216209 := bstep (se 2 (by rfl) ⟨81078, by rfl⟩ : syracuseStep 216209 = 162157) B162157
theorem B576881 : Blo 111784 576881 := bstep (se 2 (by rfl) ⟨216330, by rfl⟩ : syracuseStep 576881 = 432661) B432661
theorem B183683 : Blo 111784 183683 := bstep (se 1 (by rfl) ⟨137762, by rfl⟩ : syracuseStep 183683 = 275525) B275525
theorem B183811 : Blo 111784 183811 := bstep (se 1 (by rfl) ⟨137858, by rfl⟩ : syracuseStep 183811 = 275717) B275717
theorem B380429 : Blo 111784 380429 := bstep (se 3 (by rfl) ⟨71330, by rfl⟩ : syracuseStep 380429 = 142661) B142661
theorem B380483 : Blo 111784 380483 := bstep (se 1 (by rfl) ⟨285362, by rfl⟩ : syracuseStep 380483 = 570725) B570725
theorem B183875 : Blo 111784 183875 := bstep (se 1 (by rfl) ⟨137906, by rfl⟩ : syracuseStep 183875 = 275813) B275813
theorem B970481 : Blo 111784 970481 := bstep (se 2 (by rfl) ⟨363930, by rfl⟩ : syracuseStep 970481 = 727861) B727861
theorem B380753 : Blo 111784 380753 := bstep (se 2 (by rfl) ⟨142782, by rfl⟩ : syracuseStep 380753 = 285565) B285565
theorem B216931 : Blo 111784 216931 := bstep (se 1 (by rfl) ⟨162698, by rfl⟩ : syracuseStep 216931 = 325397) B325397
theorem B184369 : Blo 111784 184369 := bstep (se 2 (by rfl) ⟨69138, by rfl⟩ : syracuseStep 184369 = 138277) B138277
theorem B544973 : Blo 111784 544973 := bstep (se 3 (by rfl) ⟨102182, by rfl⟩ : syracuseStep 544973 = 204365) B204365
theorem B217379 : Blo 111784 217379 := bstep (se 1 (by rfl) ⟨163034, by rfl⟩ : syracuseStep 217379 = 326069) B326069
theorem B381293 : Blo 111784 381293 := bstep (se 3 (by rfl) ⟨71492, by rfl⟩ : syracuseStep 381293 = 142985) B142985
theorem B381347 : Blo 111784 381347 := bstep (se 1 (by rfl) ⟨286010, by rfl⟩ : syracuseStep 381347 = 572021) B572021
theorem B217667 : Blo 111784 217667 := bstep (se 1 (by rfl) ⟨163250, by rfl⟩ : syracuseStep 217667 = 326501) B326501
theorem B479843 : Blo 111784 479843 := bstep (se 1 (by rfl) ⟨359882, by rfl⟩ : syracuseStep 479843 = 719765) B719765
theorem B381617 : Blo 111784 381617 := bstep (se 2 (by rfl) ⟨143106, by rfl⟩ : syracuseStep 381617 = 286213) B286213
theorem B185041 : Blo 111784 185041 := bstep (se 2 (by rfl) ⟨69390, by rfl⟩ : syracuseStep 185041 = 138781) B138781
theorem B152275 : Blo 111784 152275 := bstep (se 1 (by rfl) ⟨114206, by rfl⟩ : syracuseStep 152275 = 228413) B228413
theorem B774917 : Blo 111784 774917 := bstep (se 4 (by rfl) ⟨72648, by rfl⟩ : syracuseStep 774917 = 145297) B145297
theorem B283409 : Blo 111784 283409 := bstep (se 2 (by rfl) ⟨106278, by rfl⟩ : syracuseStep 283409 = 212557) B212557
theorem B578339 : Blo 111784 578339 := bstep (se 1 (by rfl) ⟨433754, by rfl⟩ : syracuseStep 578339 = 867509) B867509
theorem B643889 : Blo 111784 643889 := bstep (se 2 (by rfl) ⟨241458, by rfl⟩ : syracuseStep 643889 = 482917) B482917
theorem B283459 : Blo 111784 283459 := bstep (se 1 (by rfl) ⟨212594, by rfl⟩ : syracuseStep 283459 = 425189) B425189
theorem B1528645 : Blo 111784 1528645 := bstep (se 4 (by rfl) ⟨143310, by rfl⟩ : syracuseStep 1528645 = 286621) B286621
theorem B283601 : Blo 111784 283601 := bstep (se 2 (by rfl) ⟨106350, by rfl⟩ : syracuseStep 283601 = 212701) B212701
theorem B152723 : Blo 111784 152723 := bstep (se 1 (by rfl) ⟨114542, by rfl⟩ : syracuseStep 152723 = 229085) B229085
theorem B382157 : Blo 111784 382157 := bstep (se 3 (by rfl) ⟨71654, by rfl⟩ : syracuseStep 382157 = 143309) B143309
theorem B382211 : Blo 111784 382211 := bstep (se 1 (by rfl) ⟨286658, by rfl⟩ : syracuseStep 382211 = 573317) B573317
theorem B873827 : Blo 111784 873827 := bstep (se 1 (by rfl) ⟨655370, by rfl⟩ : syracuseStep 873827 = 1310741) B1310741
theorem B218609 : Blo 111784 218609 := bstep (se 2 (by rfl) ⟨81978, by rfl⟩ : syracuseStep 218609 = 163957) B163957
theorem B382481 : Blo 111784 382481 := bstep (se 2 (by rfl) ⟨143430, by rfl⟩ : syracuseStep 382481 = 286861) B286861
theorem B579149 : Blo 111784 579149 := bstep (se 3 (by rfl) ⟨108590, by rfl⟩ : syracuseStep 579149 = 217181) B217181
theorem B153361 : Blo 111784 153361 := bstep (se 2 (by rfl) ⟨57510, by rfl⟩ : syracuseStep 153361 = 115021) B115021
theorem B415523 : Blo 111784 415523 := bstep (se 1 (by rfl) ⟨311642, by rfl⟩ : syracuseStep 415523 = 623285) B623285
theorem B251729 : Blo 111784 251729 := bstep (se 2 (by rfl) ⟨94398, by rfl⟩ : syracuseStep 251729 = 188797) B188797
theorem B251747 : Blo 111784 251747 := bstep (se 1 (by rfl) ⟨188810, by rfl⟩ : syracuseStep 251747 = 377621) B377621
theorem B284593 : Blo 111784 284593 := bstep (se 2 (by rfl) ⟨106722, by rfl⟩ : syracuseStep 284593 = 213445) B213445
theorem B383021 : Blo 111784 383021 := bstep (se 3 (by rfl) ⟨71816, by rfl⟩ : syracuseStep 383021 = 143633) B143633
theorem B1169477 : Blo 111784 1169477 := bstep (se 4 (by rfl) ⟨109638, by rfl⟩ : syracuseStep 1169477 = 219277) B219277
theorem B383075 : Blo 111784 383075 := bstep (se 1 (by rfl) ⟨287306, by rfl⟩ : syracuseStep 383075 = 574613) B574613
theorem B252017 : Blo 111784 252017 := bstep (se 2 (by rfl) ⟨94506, by rfl⟩ : syracuseStep 252017 = 189013) B189013
theorem B252035 : Blo 111784 252035 := bstep (se 1 (by rfl) ⟨189026, by rfl⟩ : syracuseStep 252035 = 378053) B378053
theorem B153793 : Blo 111784 153793 := bstep (se 2 (by rfl) ⟨57672, by rfl⟩ : syracuseStep 153793 = 115345) B115345
theorem B284867 : Blo 111784 284867 := bstep (se 1 (by rfl) ⟨213650, by rfl⟩ : syracuseStep 284867 = 427301) B427301
theorem B645347 : Blo 111784 645347 := bstep (se 1 (by rfl) ⟨484010, by rfl⟩ : syracuseStep 645347 = 968021) B968021
theorem B481585 : Blo 111784 481585 := bstep (se 2 (by rfl) ⟨180594, by rfl⟩ : syracuseStep 481585 = 361189) B361189
theorem B383345 : Blo 111784 383345 := bstep (se 2 (by rfl) ⟨143754, by rfl⟩ : syracuseStep 383345 = 287509) B287509
theorem B219505 : Blo 111784 219505 := bstep (se 2 (by rfl) ⟨82314, by rfl⟩ : syracuseStep 219505 = 164629) B164629
theorem B285059 : Blo 111784 285059 := bstep (se 1 (by rfl) ⟨213794, by rfl⟩ : syracuseStep 285059 = 427589) B427589
theorem B252305 : Blo 111784 252305 := bstep (se 2 (by rfl) ⟨94614, by rfl⟩ : syracuseStep 252305 = 189229) B189229
theorem B154003 : Blo 111784 154003 := bstep (se 1 (by rfl) ⟨115502, by rfl⟩ : syracuseStep 154003 = 231005) B231005
theorem B252323 : Blo 111784 252323 := bstep (se 1 (by rfl) ⟨189242, by rfl⟩ : syracuseStep 252323 = 378485) B378485
theorem B219665 : Blo 111784 219665 := bstep (se 2 (by rfl) ⟨82374, by rfl⟩ : syracuseStep 219665 = 164749) B164749
theorem B252593 : Blo 111784 252593 := bstep (se 2 (by rfl) ⟨94722, by rfl⟩ : syracuseStep 252593 = 189445) B189445
theorem B154291 : Blo 111784 154291 := bstep (se 1 (by rfl) ⟨115718, by rfl⟩ : syracuseStep 154291 = 231437) B231437
theorem B252611 : Blo 111784 252611 := bstep (se 1 (by rfl) ⟨189458, by rfl⟩ : syracuseStep 252611 = 378917) B378917
theorem B383885 : Blo 111784 383885 := bstep (se 3 (by rfl) ⟨71978, by rfl⟩ : syracuseStep 383885 = 143957) B143957
theorem B383939 : Blo 111784 383939 := bstep (se 1 (by rfl) ⟨287954, by rfl⟩ : syracuseStep 383939 = 575909) B575909
theorem B252881 : Blo 111784 252881 := bstep (se 2 (by rfl) ⟨94830, by rfl⟩ : syracuseStep 252881 = 189661) B189661
theorem B252899 : Blo 111784 252899 := bstep (se 1 (by rfl) ⟨189674, by rfl⟩ : syracuseStep 252899 = 379349) B379349
theorem B318563 : Blo 111784 318563 := bstep (se 1 (by rfl) ⟨238922, by rfl⟩ : syracuseStep 318563 = 477845) B477845
theorem B384209 : Blo 111784 384209 := bstep (se 2 (by rfl) ⟨144078, by rfl⟩ : syracuseStep 384209 = 288157) B288157
theorem B253169 : Blo 111784 253169 := bstep (se 2 (by rfl) ⟨94938, by rfl⟩ : syracuseStep 253169 = 189877) B189877
theorem B253187 : Blo 111784 253187 := bstep (se 1 (by rfl) ⟨189890, by rfl⟩ : syracuseStep 253187 = 379781) B379781
theorem B318755 : Blo 111784 318755 := bstep (se 1 (by rfl) ⟨239066, by rfl⟩ : syracuseStep 318755 = 478133) B478133
theorem B286001 : Blo 111784 286001 := bstep (se 2 (by rfl) ⟨107250, by rfl⟩ : syracuseStep 286001 = 214501) B214501
theorem B122195 : Blo 111784 122195 := bstep (se 1 (by rfl) ⟨91646, by rfl⟩ : syracuseStep 122195 = 183293) B183293
theorem B286051 : Blo 111784 286051 := bstep (se 1 (by rfl) ⟨214538, by rfl⟩ : syracuseStep 286051 = 429077) B429077
theorem B1039715 : Blo 111784 1039715 := bstep (se 1 (by rfl) ⟨779786, by rfl⟩ : syracuseStep 1039715 = 1559573) B1559573
theorem B286193 : Blo 111784 286193 := bstep (se 2 (by rfl) ⟨107322, by rfl⟩ : syracuseStep 286193 = 214645) B214645
theorem B253457 : Blo 111784 253457 := bstep (se 2 (by rfl) ⟨95046, by rfl⟩ : syracuseStep 253457 = 190093) B190093
theorem B253475 : Blo 111784 253475 := bstep (se 1 (by rfl) ⟨190106, by rfl⟩ : syracuseStep 253475 = 380213) B380213
theorem B384749 : Blo 111784 384749 := bstep (se 3 (by rfl) ⟨72140, by rfl⟩ : syracuseStep 384749 = 144281) B144281
theorem B384803 : Blo 111784 384803 := bstep (se 1 (by rfl) ⟨288602, by rfl⟩ : syracuseStep 384803 = 577205) B577205
theorem B253745 : Blo 111784 253745 := bstep (se 2 (by rfl) ⟨95154, by rfl⟩ : syracuseStep 253745 = 190309) B190309
theorem B253763 : Blo 111784 253763 := bstep (se 1 (by rfl) ⟨190322, by rfl⟩ : syracuseStep 253763 = 380645) B380645
theorem B385073 : Blo 111784 385073 := bstep (se 2 (by rfl) ⟨144402, by rfl⟩ : syracuseStep 385073 = 288805) B288805
theorem B319565 : Blo 111784 319565 := bstep (se 3 (by rfl) ⟨59918, by rfl⟩ : syracuseStep 319565 = 119837) B119837
theorem B254033 : Blo 111784 254033 := bstep (se 2 (by rfl) ⟨95262, by rfl⟩ : syracuseStep 254033 = 190525) B190525
theorem B254051 : Blo 111784 254051 := bstep (se 1 (by rfl) ⟨190538, by rfl⟩ : syracuseStep 254051 = 381077) B381077
theorem B483533 : Blo 111784 483533 := bstep (se 3 (by rfl) ⟨90662, by rfl⟩ : syracuseStep 483533 = 181325) B181325
theorem B745699 : Blo 111784 745699 := bstep (se 1 (by rfl) ⟨559274, by rfl⟩ : syracuseStep 745699 = 1118549) B1118549
theorem B319747 : Blo 111784 319747 := bstep (se 1 (by rfl) ⟨239810, by rfl⟩ : syracuseStep 319747 = 479621) B479621
theorem B188689 : Blo 111784 188689 := bstep (se 2 (by rfl) ⟨70758, by rfl⟩ : syracuseStep 188689 = 141517) B141517
theorem B188723 : Blo 111784 188723 := bstep (se 1 (by rfl) ⟨141542, by rfl⟩ : syracuseStep 188723 = 283085) B283085
theorem B254321 : Blo 111784 254321 := bstep (se 2 (by rfl) ⟨95370, by rfl⟩ : syracuseStep 254321 = 190741) B190741
theorem B254339 : Blo 111784 254339 := bstep (se 1 (by rfl) ⟨190754, by rfl⟩ : syracuseStep 254339 = 381509) B381509
theorem B582065 : Blo 111784 582065 := bstep (se 2 (by rfl) ⟨218274, by rfl⟩ : syracuseStep 582065 = 436549) B436549
theorem B188851 : Blo 111784 188851 := bstep (se 1 (by rfl) ⟨141638, by rfl⟩ : syracuseStep 188851 = 283277) B283277
theorem B287185 : Blo 111784 287185 := bstep (se 2 (by rfl) ⟨107694, by rfl⟩ : syracuseStep 287185 = 215389) B215389
theorem B188993 : Blo 111784 188993 := bstep (se 2 (by rfl) ⟨70872, by rfl⟩ : syracuseStep 188993 = 141745) B141745
theorem B385613 : Blo 111784 385613 := bstep (se 3 (by rfl) ⟨72302, by rfl⟩ : syracuseStep 385613 = 144605) B144605
theorem B156259 : Blo 111784 156259 := bstep (se 1 (by rfl) ⟨117194, by rfl⟩ : syracuseStep 156259 = 234389) B234389
theorem B385667 : Blo 111784 385667 := bstep (se 1 (by rfl) ⟨289250, by rfl⟩ : syracuseStep 385667 = 578501) B578501
theorem B254609 : Blo 111784 254609 := bstep (se 2 (by rfl) ⟨95478, by rfl⟩ : syracuseStep 254609 = 190957) B190957
theorem B254627 : Blo 111784 254627 := bstep (se 1 (by rfl) ⟨190970, by rfl⟩ : syracuseStep 254627 = 381941) B381941
theorem B189121 : Blo 111784 189121 := bstep (se 2 (by rfl) ⟨70920, by rfl⟩ : syracuseStep 189121 = 141841) B141841
theorem B189155 : Blo 111784 189155 := bstep (se 1 (by rfl) ⟨141866, by rfl⟩ : syracuseStep 189155 = 283733) B283733
theorem B287459 : Blo 111784 287459 := bstep (se 1 (by rfl) ⟨215594, by rfl⟩ : syracuseStep 287459 = 431189) B431189
theorem B320237 : Blo 111784 320237 := bstep (se 3 (by rfl) ⟨60044, by rfl⟩ : syracuseStep 320237 = 120089) B120089
theorem B189283 : Blo 111784 189283 := bstep (se 1 (by rfl) ⟨141962, by rfl⟩ : syracuseStep 189283 = 283925) B283925
theorem B385937 : Blo 111784 385937 := bstep (se 2 (by rfl) ⟨144726, by rfl⟩ : syracuseStep 385937 = 289453) B289453
theorem B287651 : Blo 111784 287651 := bstep (se 1 (by rfl) ⟨215738, by rfl⟩ : syracuseStep 287651 = 431477) B431477
theorem B254897 : Blo 111784 254897 := bstep (se 2 (by rfl) ⟨95586, by rfl⟩ : syracuseStep 254897 = 191173) B191173
theorem B254915 : Blo 111784 254915 := bstep (se 1 (by rfl) ⟨191186, by rfl⟩ : syracuseStep 254915 = 382373) B382373
theorem B189425 : Blo 111784 189425 := bstep (se 2 (by rfl) ⟨71034, by rfl⟩ : syracuseStep 189425 = 142069) B142069
theorem B189553 : Blo 111784 189553 := bstep (se 2 (by rfl) ⟨71082, by rfl⟩ : syracuseStep 189553 = 142165) B142165
theorem B189587 : Blo 111784 189587 := bstep (se 1 (by rfl) ⟨142190, by rfl⟩ : syracuseStep 189587 = 284381) B284381
theorem B255185 : Blo 111784 255185 := bstep (se 2 (by rfl) ⟨95694, by rfl⟩ : syracuseStep 255185 = 191389) B191389
theorem B255203 : Blo 111784 255203 := bstep (se 1 (by rfl) ⟨191402, by rfl⟩ : syracuseStep 255203 = 382805) B382805
theorem B189715 : Blo 111784 189715 := bstep (se 1 (by rfl) ⟨142286, by rfl⟩ : syracuseStep 189715 = 284573) B284573
theorem B189857 : Blo 111784 189857 := bstep (se 2 (by rfl) ⟨71196, by rfl⟩ : syracuseStep 189857 = 142393) B142393
theorem B386477 : Blo 111784 386477 := bstep (se 3 (by rfl) ⟨72464, by rfl⟩ : syracuseStep 386477 = 144929) B144929
theorem B386531 : Blo 111784 386531 := bstep (se 1 (by rfl) ⟨289898, by rfl⟩ : syracuseStep 386531 = 579797) B579797
theorem B255473 : Blo 111784 255473 := bstep (se 2 (by rfl) ⟨95802, by rfl⟩ : syracuseStep 255473 = 191605) B191605
theorem B255491 : Blo 111784 255491 := bstep (se 1 (by rfl) ⟨191618, by rfl⟩ : syracuseStep 255491 = 383237) B383237
theorem B157187 : Blo 111784 157187 := bstep (se 1 (by rfl) ⟨117890, by rfl⟩ : syracuseStep 157187 = 235781) B235781
theorem B189985 : Blo 111784 189985 := bstep (se 2 (by rfl) ⟨71244, by rfl⟩ : syracuseStep 189985 = 142489) B142489
theorem B190019 : Blo 111784 190019 := bstep (se 1 (by rfl) ⟨142514, by rfl⟩ : syracuseStep 190019 = 285029) B285029
theorem B190147 : Blo 111784 190147 := bstep (se 1 (by rfl) ⟨142610, by rfl⟩ : syracuseStep 190147 = 285221) B285221
theorem B386801 : Blo 111784 386801 := bstep (se 2 (by rfl) ⟨145050, by rfl⟩ : syracuseStep 386801 = 290101) B290101
theorem B255761 : Blo 111784 255761 := bstep (se 2 (by rfl) ⟨95910, by rfl⟩ : syracuseStep 255761 = 191821) B191821
theorem B255779 : Blo 111784 255779 := bstep (se 1 (by rfl) ⟨191834, by rfl⟩ : syracuseStep 255779 = 383669) B383669
theorem B190289 : Blo 111784 190289 := bstep (se 2 (by rfl) ⟨71358, by rfl⟩ : syracuseStep 190289 = 142717) B142717
theorem B288593 : Blo 111784 288593 := bstep (se 2 (by rfl) ⟨108222, by rfl⟩ : syracuseStep 288593 = 216445) B216445
theorem B583523 : Blo 111784 583523 := bstep (se 1 (by rfl) ⟨437642, by rfl⟩ : syracuseStep 583523 = 875285) B875285
theorem B124787 : Blo 111784 124787 := bstep (se 1 (by rfl) ⟨93590, by rfl⟩ : syracuseStep 124787 = 187181) B187181
theorem B288643 : Blo 111784 288643 := bstep (se 1 (by rfl) ⟨216482, by rfl⟩ : syracuseStep 288643 = 432965) B432965
theorem B321421 : Blo 111784 321421 := bstep (se 3 (by rfl) ⟨60266, by rfl⟩ : syracuseStep 321421 = 120533) B120533
theorem B190417 : Blo 111784 190417 := bstep (se 2 (by rfl) ⟨71406, by rfl⟩ : syracuseStep 190417 = 142813) B142813
theorem B190451 : Blo 111784 190451 := bstep (se 1 (by rfl) ⟨142838, by rfl⟩ : syracuseStep 190451 = 285677) B285677
theorem B288785 : Blo 111784 288785 := bstep (se 2 (by rfl) ⟨108294, by rfl⟩ : syracuseStep 288785 = 216589) B216589
theorem B256049 : Blo 111784 256049 := bstep (se 2 (by rfl) ⟨96018, by rfl⟩ : syracuseStep 256049 = 192037) B192037
theorem B256067 : Blo 111784 256067 := bstep (se 1 (by rfl) ⟨192050, by rfl⟩ : syracuseStep 256067 = 384101) B384101
theorem B190579 : Blo 111784 190579 := bstep (se 1 (by rfl) ⟨142934, by rfl⟩ : syracuseStep 190579 = 285869) B285869
theorem B190721 : Blo 111784 190721 := bstep (se 2 (by rfl) ⟨71520, by rfl⟩ : syracuseStep 190721 = 143041) B143041
theorem B387341 : Blo 111784 387341 := bstep (se 3 (by rfl) ⟨72626, by rfl⟩ : syracuseStep 387341 = 145253) B145253
theorem B387395 : Blo 111784 387395 := bstep (se 1 (by rfl) ⟨290546, by rfl⟩ : syracuseStep 387395 = 581093) B581093
theorem B256337 : Blo 111784 256337 := bstep (se 2 (by rfl) ⟨96126, by rfl⟩ : syracuseStep 256337 = 192253) B192253
theorem B256355 : Blo 111784 256355 := bstep (se 1 (by rfl) ⟨192266, by rfl⟩ : syracuseStep 256355 = 384533) B384533
theorem B190849 : Blo 111784 190849 := bstep (se 2 (by rfl) ⟨71568, by rfl⟩ : syracuseStep 190849 = 143137) B143137
theorem B190883 : Blo 111784 190883 := bstep (se 1 (by rfl) ⟨143162, by rfl⟩ : syracuseStep 190883 = 286325) B286325
theorem B616901 : Blo 111784 616901 := bstep (se 4 (by rfl) ⟨57834, by rfl⟩ : syracuseStep 616901 = 115669) B115669
theorem B191011 : Blo 111784 191011 := bstep (se 1 (by rfl) ⟨143258, by rfl⟩ : syracuseStep 191011 = 286517) B286517
theorem B879173 : Blo 111784 879173 := bstep (se 4 (by rfl) ⟨82422, by rfl⟩ : syracuseStep 879173 = 164845) B164845
theorem B387665 : Blo 111784 387665 := bstep (se 2 (by rfl) ⟨145374, by rfl⟩ : syracuseStep 387665 = 290749) B290749
theorem B3500657 : Blo 111784 3500657 := bstep (se 2 (by rfl) ⟨1312746, by rfl⟩ : syracuseStep 3500657 = 2625493) B2625493
theorem B256625 : Blo 111784 256625 := bstep (se 2 (by rfl) ⟨96234, by rfl⟩ : syracuseStep 256625 = 192469) B192469
theorem B256643 : Blo 111784 256643 := bstep (se 1 (by rfl) ⟨192482, by rfl⟩ : syracuseStep 256643 = 384965) B384965
theorem B584333 : Blo 111784 584333 := bstep (se 3 (by rfl) ⟨109562, by rfl⟩ : syracuseStep 584333 = 219125) B219125
theorem B191153 : Blo 111784 191153 := bstep (se 2 (by rfl) ⟨71682, by rfl⟩ : syracuseStep 191153 = 143365) B143365
theorem B191281 : Blo 111784 191281 := bstep (se 2 (by rfl) ⟨71730, by rfl⟩ : syracuseStep 191281 = 143461) B143461
theorem B125779 : Blo 111784 125779 := bstep (se 1 (by rfl) ⟨94334, by rfl⟩ : syracuseStep 125779 = 188669) B188669
theorem B191315 : Blo 111784 191315 := bstep (se 1 (by rfl) ⟨143486, by rfl⟩ : syracuseStep 191315 = 286973) B286973
theorem B256913 : Blo 111784 256913 := bstep (se 2 (by rfl) ⟨96342, by rfl⟩ : syracuseStep 256913 = 192685) B192685
theorem B256931 : Blo 111784 256931 := bstep (se 1 (by rfl) ⟨192698, by rfl⟩ : syracuseStep 256931 = 385397) B385397
theorem B322481 : Blo 111784 322481 := bstep (se 2 (by rfl) ⟨120930, by rfl⟩ : syracuseStep 322481 = 241861) B241861
theorem B191443 : Blo 111784 191443 := bstep (se 1 (by rfl) ⟨143582, by rfl⟩ : syracuseStep 191443 = 287165) B287165
theorem B125923 : Blo 111784 125923 := bstep (se 1 (by rfl) ⟨94442, by rfl⟩ : syracuseStep 125923 = 188885) B188885
theorem B289777 : Blo 111784 289777 := bstep (se 2 (by rfl) ⟨108666, by rfl⟩ : syracuseStep 289777 = 217333) B217333
theorem B453709 : Blo 111784 453709 := bstep (se 3 (by rfl) ⟨85070, by rfl⟩ : syracuseStep 453709 = 170141) B170141
theorem B191585 : Blo 111784 191585 := bstep (se 2 (by rfl) ⟨71844, by rfl⟩ : syracuseStep 191585 = 143689) B143689
theorem B388205 : Blo 111784 388205 := bstep (se 3 (by rfl) ⟨72788, by rfl⟩ : syracuseStep 388205 = 145577) B145577
theorem B126067 : Blo 111784 126067 := bstep (se 1 (by rfl) ⟨94550, by rfl⟩ : syracuseStep 126067 = 189101) B189101
theorem B388259 : Blo 111784 388259 := bstep (se 1 (by rfl) ⟨291194, by rfl⟩ : syracuseStep 388259 = 582389) B582389
theorem B257201 : Blo 111784 257201 := bstep (se 2 (by rfl) ⟨96450, by rfl⟩ : syracuseStep 257201 = 192901) B192901
theorem B257219 : Blo 111784 257219 := bstep (se 1 (by rfl) ⟨192914, by rfl⟩ : syracuseStep 257219 = 385829) B385829
theorem B1109189 : Blo 111784 1109189 := bstep (se 4 (by rfl) ⟨103986, by rfl⟩ : syracuseStep 1109189 = 207973) B207973
theorem B191713 : Blo 111784 191713 := bstep (se 2 (by rfl) ⟨71892, by rfl⟩ : syracuseStep 191713 = 143785) B143785
theorem B126211 : Blo 111784 126211 := bstep (se 1 (by rfl) ⟨94658, by rfl⟩ : syracuseStep 126211 = 189317) B189317
theorem B191747 : Blo 111784 191747 := bstep (se 1 (by rfl) ⟨143810, by rfl⟩ : syracuseStep 191747 = 287621) B287621
theorem B290051 : Blo 111784 290051 := bstep (se 1 (by rfl) ⟨217538, by rfl⟩ : syracuseStep 290051 = 435077) B435077
theorem B1469765 : Blo 111784 1469765 := bstep (se 4 (by rfl) ⟨137790, by rfl⟩ : syracuseStep 1469765 = 275581) B275581
theorem B1371491 : Blo 111784 1371491 := bstep (se 1 (by rfl) ⟨1028618, by rfl⟩ : syracuseStep 1371491 = 2057237) B2057237
theorem B191875 : Blo 111784 191875 := bstep (se 1 (by rfl) ⟨143906, by rfl⟩ : syracuseStep 191875 = 287813) B287813
theorem B126355 : Blo 111784 126355 := bstep (se 1 (by rfl) ⟨94766, by rfl⟩ : syracuseStep 126355 = 189533) B189533
theorem B388529 : Blo 111784 388529 := bstep (se 2 (by rfl) ⟨145698, by rfl⟩ : syracuseStep 388529 = 291397) B291397
theorem B290243 : Blo 111784 290243 := bstep (se 1 (by rfl) ⟨217682, by rfl⟩ : syracuseStep 290243 = 435365) B435365
theorem B257489 : Blo 111784 257489 := bstep (se 2 (by rfl) ⟨96558, by rfl⟩ : syracuseStep 257489 = 193117) B193117
theorem B257507 : Blo 111784 257507 := bstep (se 1 (by rfl) ⟨193130, by rfl⟩ : syracuseStep 257507 = 386261) B386261
theorem B192017 : Blo 111784 192017 := bstep (se 2 (by rfl) ⟨72006, by rfl⟩ : syracuseStep 192017 = 144013) B144013
theorem B126499 : Blo 111784 126499 := bstep (se 1 (by rfl) ⟨94874, by rfl⟩ : syracuseStep 126499 = 189749) B189749
theorem B585251 : Blo 111784 585251 := bstep (se 1 (by rfl) ⟨438938, by rfl⟩ : syracuseStep 585251 = 877877) B877877
theorem B2780725 : Blo 111784 2780725 := bstep (se 5 (by rfl) ⟨130346, by rfl⟩ : syracuseStep 2780725 = 260693) B260693
theorem B323153 : Blo 111784 323153 := bstep (se 2 (by rfl) ⟨121182, by rfl⟩ : syracuseStep 323153 = 242365) B242365
theorem B454243 : Blo 111784 454243 := bstep (se 1 (by rfl) ⟨340682, by rfl⟩ : syracuseStep 454243 = 681365) B681365
theorem B192145 : Blo 111784 192145 := bstep (se 2 (by rfl) ⟨72054, by rfl⟩ : syracuseStep 192145 = 144109) B144109
theorem B650915 : Blo 111784 650915 := bstep (se 1 (by rfl) ⟨488186, by rfl⟩ : syracuseStep 650915 = 976373) B976373
theorem B126643 : Blo 111784 126643 := bstep (se 1 (by rfl) ⟨94982, by rfl⟩ : syracuseStep 126643 = 189965) B189965
theorem B192179 : Blo 111784 192179 := bstep (se 1 (by rfl) ⟨144134, by rfl⟩ : syracuseStep 192179 = 288269) B288269
theorem B257777 : Blo 111784 257777 := bstep (se 2 (by rfl) ⟨96666, by rfl⟩ : syracuseStep 257777 = 193333) B193333
theorem B257795 : Blo 111784 257795 := bstep (se 1 (by rfl) ⟨193346, by rfl⟩ : syracuseStep 257795 = 386693) B386693
theorem B192307 : Blo 111784 192307 := bstep (se 1 (by rfl) ⟨144230, by rfl⟩ : syracuseStep 192307 = 288461) B288461
theorem B126787 : Blo 111784 126787 := bstep (se 1 (by rfl) ⟨95090, by rfl⟩ : syracuseStep 126787 = 190181) B190181
theorem B159617 : Blo 111784 159617 := bstep (se 2 (by rfl) ⟨59856, by rfl⟩ : syracuseStep 159617 = 119713) B119713
theorem B192449 : Blo 111784 192449 := bstep (se 2 (by rfl) ⟨72168, by rfl⟩ : syracuseStep 192449 = 144337) B144337
theorem B389069 : Blo 111784 389069 := bstep (se 3 (by rfl) ⟨72950, by rfl⟩ : syracuseStep 389069 = 145901) B145901
theorem B126931 : Blo 111784 126931 := bstep (se 1 (by rfl) ⟨95198, by rfl⟩ : syracuseStep 126931 = 190397) B190397
theorem B389123 : Blo 111784 389123 := bstep (se 1 (by rfl) ⟨291842, by rfl⟩ : syracuseStep 389123 = 583685) B583685
theorem B258065 : Blo 111784 258065 := bstep (se 2 (by rfl) ⟨96774, by rfl⟩ : syracuseStep 258065 = 193549) B193549
theorem B258083 : Blo 111784 258083 := bstep (se 1 (by rfl) ⟨193562, by rfl⟩ : syracuseStep 258083 = 387125) B387125
theorem B192577 : Blo 111784 192577 := bstep (se 2 (by rfl) ⟨72216, by rfl⟩ : syracuseStep 192577 = 144433) B144433
theorem B127075 : Blo 111784 127075 := bstep (se 1 (by rfl) ⟨95306, by rfl⟩ : syracuseStep 127075 = 190613) B190613
theorem B192611 : Blo 111784 192611 := bstep (se 1 (by rfl) ⟨144458, by rfl⟩ : syracuseStep 192611 = 288917) B288917
theorem B487565 : Blo 111784 487565 := bstep (se 3 (by rfl) ⟨91418, by rfl⟩ : syracuseStep 487565 = 182837) B182837
theorem B1667213 : Blo 111784 1667213 := bstep (se 3 (by rfl) ⟨312602, by rfl⟩ : syracuseStep 1667213 = 625205) B625205
theorem B192739 : Blo 111784 192739 := bstep (se 1 (by rfl) ⟨144554, by rfl⟩ : syracuseStep 192739 = 289109) B289109
theorem B127219 : Blo 111784 127219 := bstep (se 1 (by rfl) ⟨95414, by rfl⟩ : syracuseStep 127219 = 190829) B190829
theorem B389393 : Blo 111784 389393 := bstep (se 2 (by rfl) ⟨146022, by rfl⟩ : syracuseStep 389393 = 292045) B292045
theorem B258353 : Blo 111784 258353 := bstep (se 2 (by rfl) ⟨96882, by rfl⟩ : syracuseStep 258353 = 193765) B193765
theorem B258371 : Blo 111784 258371 := bstep (se 1 (by rfl) ⟨193778, by rfl⟩ : syracuseStep 258371 = 387557) B387557
theorem B323939 : Blo 111784 323939 := bstep (se 1 (by rfl) ⟨242954, by rfl⟩ : syracuseStep 323939 = 485909) B485909
theorem B192881 : Blo 111784 192881 := bstep (se 2 (by rfl) ⟨72330, by rfl⟩ : syracuseStep 192881 = 144661) B144661
theorem B291185 : Blo 111784 291185 := bstep (se 2 (by rfl) ⟨109194, by rfl⟩ : syracuseStep 291185 = 218389) B218389
theorem B127363 : Blo 111784 127363 := bstep (se 1 (by rfl) ⟨95522, by rfl⟩ : syracuseStep 127363 = 191045) B191045
theorem B815501 : Blo 111784 815501 := bstep (se 3 (by rfl) ⟨152906, by rfl⟩ : syracuseStep 815501 = 305813) B305813
theorem B160147 : Blo 111784 160147 := bstep (se 1 (by rfl) ⟨120110, by rfl⟩ : syracuseStep 160147 = 240221) B240221
theorem B291235 : Blo 111784 291235 := bstep (se 1 (by rfl) ⟨218426, by rfl⟩ : syracuseStep 291235 = 436853) B436853
theorem B487907 : Blo 111784 487907 := bstep (se 1 (by rfl) ⟨365930, by rfl⟩ : syracuseStep 487907 = 731861) B731861
theorem B193009 : Blo 111784 193009 := bstep (se 2 (by rfl) ⟨72378, by rfl⟩ : syracuseStep 193009 = 144757) B144757
theorem B127507 : Blo 111784 127507 := bstep (se 1 (by rfl) ⟨95630, by rfl⟩ : syracuseStep 127507 = 191261) B191261
theorem B193043 : Blo 111784 193043 := bstep (se 1 (by rfl) ⟨144782, by rfl⟩ : syracuseStep 193043 = 289565) B289565
theorem B291377 : Blo 111784 291377 := bstep (se 2 (by rfl) ⟨109266, by rfl⟩ : syracuseStep 291377 = 218533) B218533
theorem B258641 : Blo 111784 258641 := bstep (se 2 (by rfl) ⟨96990, by rfl⟩ : syracuseStep 258641 = 193981) B193981
theorem B258659 : Blo 111784 258659 := bstep (se 1 (by rfl) ⟨193994, by rfl⟩ : syracuseStep 258659 = 387989) B387989
theorem B193171 : Blo 111784 193171 := bstep (se 1 (by rfl) ⟨144878, by rfl⟩ : syracuseStep 193171 = 289757) B289757
theorem B127651 : Blo 111784 127651 := bstep (se 1 (by rfl) ⟨95738, by rfl⟩ : syracuseStep 127651 = 191477) B191477
theorem B324269 : Blo 111784 324269 := bstep (se 3 (by rfl) ⟨60800, by rfl⟩ : syracuseStep 324269 = 121601) B121601
theorem B160483 : Blo 111784 160483 := bstep (se 1 (by rfl) ⟨120362, by rfl⟩ : syracuseStep 160483 = 240725) B240725
theorem B324337 : Blo 111784 324337 := bstep (se 2 (by rfl) ⟨121626, by rfl⟩ : syracuseStep 324337 = 243253) B243253
theorem B193313 : Blo 111784 193313 := bstep (se 2 (by rfl) ⟨72492, by rfl⟩ : syracuseStep 193313 = 144985) B144985
theorem B389933 : Blo 111784 389933 := bstep (se 3 (by rfl) ⟨73112, by rfl⟩ : syracuseStep 389933 = 146225) B146225
theorem B127795 : Blo 111784 127795 := bstep (se 1 (by rfl) ⟨95846, by rfl⟩ : syracuseStep 127795 = 191693) B191693
theorem B389987 : Blo 111784 389987 := bstep (se 1 (by rfl) ⟨292490, by rfl⟩ : syracuseStep 389987 = 584981) B584981
theorem B258929 : Blo 111784 258929 := bstep (se 2 (by rfl) ⟨97098, by rfl⟩ : syracuseStep 258929 = 194197) B194197
theorem B258947 : Blo 111784 258947 := bstep (se 1 (by rfl) ⟨194210, by rfl⟩ : syracuseStep 258947 = 388421) B388421
theorem B193441 : Blo 111784 193441 := bstep (se 2 (by rfl) ⟨72540, by rfl⟩ : syracuseStep 193441 = 145081) B145081
theorem B488369 : Blo 111784 488369 := bstep (se 2 (by rfl) ⟨183138, by rfl⟩ : syracuseStep 488369 = 366277) B366277
theorem B127939 : Blo 111784 127939 := bstep (se 1 (by rfl) ⟨95954, by rfl⟩ : syracuseStep 127939 = 191909) B191909
theorem B193475 : Blo 111784 193475 := bstep (se 1 (by rfl) ⟨145106, by rfl⟩ : syracuseStep 193475 = 290213) B290213
theorem B1209329 : Blo 111784 1209329 := bstep (se 2 (by rfl) ⟨453498, by rfl⟩ : syracuseStep 1209329 = 906997) B906997
theorem B324611 : Blo 111784 324611 := bstep (se 1 (by rfl) ⟨243458, by rfl⟩ : syracuseStep 324611 = 486917) B486917
theorem B259139 : Blo 111784 259139 := bstep (se 1 (by rfl) ⟨194354, by rfl⟩ : syracuseStep 259139 = 388709) B388709
theorem B193603 : Blo 111784 193603 := bstep (se 1 (by rfl) ⟨145202, by rfl⟩ : syracuseStep 193603 = 290405) B290405
theorem B128083 : Blo 111784 128083 := bstep (se 1 (by rfl) ⟨96062, by rfl⟩ : syracuseStep 128083 = 192125) B192125
theorem B390257 : Blo 111784 390257 := bstep (se 2 (by rfl) ⟨146346, by rfl⟩ : syracuseStep 390257 = 292693) B292693
theorem B390275 : Blo 111784 390275 := bstep (se 1 (by rfl) ⟨292706, by rfl⟩ : syracuseStep 390275 = 585413) B585413
theorem B259217 : Blo 111784 259217 := bstep (se 2 (by rfl) ⟨97206, by rfl⟩ : syracuseStep 259217 = 194413) B194413
theorem B259235 : Blo 111784 259235 := bstep (se 1 (by rfl) ⟨194426, by rfl⟩ : syracuseStep 259235 = 388853) B388853
theorem B193745 : Blo 111784 193745 := bstep (se 2 (by rfl) ⟨72654, by rfl⟩ : syracuseStep 193745 = 145309) B145309
theorem B128227 : Blo 111784 128227 := bstep (se 1 (by rfl) ⟨96170, by rfl⟩ : syracuseStep 128227 = 192341) B192341
theorem B1471715 : Blo 111784 1471715 := bstep (se 1 (by rfl) ⟨1103786, by rfl⟩ : syracuseStep 1471715 = 2207573) B2207573
theorem B161041 : Blo 111784 161041 := bstep (se 2 (by rfl) ⟨60390, by rfl⟩ : syracuseStep 161041 = 120781) B120781
theorem B161075 : Blo 111784 161075 := bstep (se 1 (by rfl) ⟨120806, by rfl⟩ : syracuseStep 161075 = 241613) B241613
theorem B193873 : Blo 111784 193873 := bstep (se 2 (by rfl) ⟨72702, by rfl⟩ : syracuseStep 193873 = 145405) B145405
theorem B128371 : Blo 111784 128371 := bstep (se 1 (by rfl) ⟨96278, by rfl⟩ : syracuseStep 128371 = 192557) B192557
theorem B193907 : Blo 111784 193907 := bstep (se 1 (by rfl) ⟨145430, by rfl⟩ : syracuseStep 193907 = 290861) B290861
theorem B259505 : Blo 111784 259505 := bstep (se 2 (by rfl) ⟨97314, by rfl⟩ : syracuseStep 259505 = 194629) B194629
theorem B259523 : Blo 111784 259523 := bstep (se 1 (by rfl) ⟨194642, by rfl⟩ : syracuseStep 259523 = 389285) B389285
theorem B194035 : Blo 111784 194035 := bstep (se 1 (by rfl) ⟨145526, by rfl⟩ : syracuseStep 194035 = 291053) B291053
theorem B128515 : Blo 111784 128515 := bstep (se 1 (by rfl) ⟨96386, by rfl⟩ : syracuseStep 128515 = 192773) B192773
theorem B292369 : Blo 111784 292369 := bstep (se 2 (by rfl) ⟨109638, by rfl⟩ : syracuseStep 292369 = 219277) B219277
theorem B194177 : Blo 111784 194177 := bstep (se 2 (by rfl) ⟨72816, by rfl⟩ : syracuseStep 194177 = 145633) B145633
theorem B128659 : Blo 111784 128659 := bstep (se 1 (by rfl) ⟨96494, by rfl⟩ : syracuseStep 128659 = 192989) B192989
theorem B554701 : Blo 111784 554701 := bstep (se 3 (by rfl) ⟨104006, by rfl⟩ : syracuseStep 554701 = 208013) B208013
theorem B259793 : Blo 111784 259793 := bstep (se 2 (by rfl) ⟨97422, by rfl⟩ : syracuseStep 259793 = 194845) B194845
theorem B128723 : Blo 111784 128723 := bstep (se 1 (by rfl) ⟨96542, by rfl⟩ : syracuseStep 128723 = 193085) B193085
theorem B259811 : Blo 111784 259811 := bstep (se 1 (by rfl) ⟨194858, by rfl⟩ : syracuseStep 259811 = 389717) B389717
theorem B194305 : Blo 111784 194305 := bstep (se 2 (by rfl) ⟨72864, by rfl⟩ : syracuseStep 194305 = 145729) B145729
theorem B128803 : Blo 111784 128803 := bstep (se 1 (by rfl) ⟨96602, by rfl⟩ : syracuseStep 128803 = 193205) B193205
theorem B194339 : Blo 111784 194339 := bstep (se 1 (by rfl) ⟨145754, by rfl⟩ : syracuseStep 194339 = 291509) B291509
theorem B292643 : Blo 111784 292643 := bstep (se 1 (by rfl) ⟨219482, by rfl⟩ : syracuseStep 292643 = 438965) B438965
theorem B325453 : Blo 111784 325453 := bstep (se 3 (by rfl) ⟨61022, by rfl⟩ : syracuseStep 325453 = 122045) B122045
theorem B161633 : Blo 111784 161633 := bstep (se 2 (by rfl) ⟨60612, by rfl⟩ : syracuseStep 161633 = 121225) B121225
theorem B194467 : Blo 111784 194467 := bstep (se 1 (by rfl) ⟨145850, by rfl⟩ : syracuseStep 194467 = 291701) B291701
theorem B161713 : Blo 111784 161713 := bstep (se 2 (by rfl) ⟨60642, by rfl⟩ : syracuseStep 161713 = 121285) B121285
theorem B128947 : Blo 111784 128947 := bstep (se 1 (by rfl) ⟨96710, by rfl⟩ : syracuseStep 128947 = 193421) B193421
theorem B292835 : Blo 111784 292835 := bstep (se 1 (by rfl) ⟨219626, by rfl⟩ : syracuseStep 292835 = 439253) B439253
theorem B325613 : Blo 111784 325613 := bstep (se 3 (by rfl) ⟨61052, by rfl⟩ : syracuseStep 325613 = 122105) B122105
theorem B260081 : Blo 111784 260081 := bstep (se 2 (by rfl) ⟨97530, by rfl⟩ : syracuseStep 260081 = 195061) B195061
theorem B260099 : Blo 111784 260099 := bstep (se 1 (by rfl) ⟨195074, by rfl⟩ : syracuseStep 260099 = 390149) B390149
theorem B194609 : Blo 111784 194609 := bstep (se 2 (by rfl) ⟨72978, by rfl⟩ : syracuseStep 194609 = 145957) B145957
theorem B129091 : Blo 111784 129091 := bstep (se 1 (by rfl) ⟨96818, by rfl⟩ : syracuseStep 129091 = 193637) B193637
theorem B325795 : Blo 111784 325795 := bstep (se 1 (by rfl) ⟨244346, by rfl⟩ : syracuseStep 325795 = 488693) B488693
theorem B194737 : Blo 111784 194737 := bstep (se 2 (by rfl) ⟨73026, by rfl⟩ : syracuseStep 194737 = 146053) B146053
theorem B1308869 : Blo 111784 1308869 := bstep (se 4 (by rfl) ⟨122706, by rfl⟩ : syracuseStep 1308869 = 245413) B245413
theorem B129235 : Blo 111784 129235 := bstep (se 1 (by rfl) ⟨96926, by rfl⟩ : syracuseStep 129235 = 193853) B193853
theorem B194771 : Blo 111784 194771 := bstep (se 1 (by rfl) ⟨146078, by rfl⟩ : syracuseStep 194771 = 292157) B292157
theorem B358627 : Blo 111784 358627 := bstep (se 1 (by rfl) ⟨268970, by rfl⟩ : syracuseStep 358627 = 537941) B537941
theorem B260369 : Blo 111784 260369 := bstep (se 2 (by rfl) ⟨97638, by rfl⟩ : syracuseStep 260369 = 195277) B195277
theorem B260387 : Blo 111784 260387 := bstep (se 1 (by rfl) ⟨195290, by rfl⟩ : syracuseStep 260387 = 390581) B390581
theorem B194899 : Blo 111784 194899 := bstep (se 1 (by rfl) ⟨146174, by rfl⟩ : syracuseStep 194899 = 292349) B292349
theorem B129379 : Blo 111784 129379 := bstep (se 1 (by rfl) ⟨97034, by rfl⟩ : syracuseStep 129379 = 194069) B194069
theorem B195041 : Blo 111784 195041 := bstep (se 2 (by rfl) ⟨73140, by rfl⟩ : syracuseStep 195041 = 146281) B146281
theorem B129523 : Blo 111784 129523 := bstep (se 1 (by rfl) ⟨97142, by rfl⟩ : syracuseStep 129523 = 194285) B194285
theorem B2423317 : Blo 111784 2423317 := bstep (se 6 (by rfl) ⟨56796, by rfl⟩ : syracuseStep 2423317 = 113593) B113593
theorem B195169 : Blo 111784 195169 := bstep (se 2 (by rfl) ⟨73188, by rfl⟩ : syracuseStep 195169 = 146377) B146377
theorem B1309283 : Blo 111784 1309283 := bstep (se 1 (by rfl) ⟨981962, by rfl⟩ : syracuseStep 1309283 = 1963925) B1963925
theorem B129667 : Blo 111784 129667 := bstep (se 1 (by rfl) ⟨97250, by rfl⟩ : syracuseStep 129667 = 194501) B194501
theorem B195203 : Blo 111784 195203 := bstep (se 1 (by rfl) ⟨146402, by rfl⟩ : syracuseStep 195203 = 292805) B292805
theorem B162499 : Blo 111784 162499 := bstep (se 1 (by rfl) ⟨121874, by rfl⟩ : syracuseStep 162499 = 243749) B243749
theorem B195331 : Blo 111784 195331 := bstep (se 1 (by rfl) ⟨146498, by rfl⟩ : syracuseStep 195331 = 292997) B292997
theorem B129811 : Blo 111784 129811 := bstep (se 1 (by rfl) ⟨97358, by rfl⟩ : syracuseStep 129811 = 194717) B194717
theorem B293777 : Blo 111784 293777 := bstep (se 2 (by rfl) ⟨110166, by rfl⟩ : syracuseStep 293777 = 220333) B220333
theorem B129955 : Blo 111784 129955 := bstep (se 1 (by rfl) ⟨97466, by rfl⟩ : syracuseStep 129955 = 194933) B194933
theorem B654277 : Blo 111784 654277 := bstep (se 4 (by rfl) ⟨61338, by rfl⟩ : syracuseStep 654277 = 122677) B122677
theorem B621553 : Blo 111784 621553 := bstep (se 2 (by rfl) ⟨233082, by rfl⟩ : syracuseStep 621553 = 466165) B466165
theorem B130099 : Blo 111784 130099 := bstep (se 1 (by rfl) ⟨97574, by rfl⟩ : syracuseStep 130099 = 195149) B195149
theorem B162977 : Blo 111784 162977 := bstep (se 2 (by rfl) ⟨61116, by rfl⟩ : syracuseStep 162977 = 122233) B122233
theorem B130243 : Blo 111784 130243 := bstep (se 1 (by rfl) ⟨97682, by rfl⟩ : syracuseStep 130243 = 195365) B195365
theorem B163091 : Blo 111784 163091 := bstep (se 1 (by rfl) ⟨122318, by rfl⟩ : syracuseStep 163091 = 244637) B244637
theorem B163171 : Blo 111784 163171 := bstep (se 1 (by rfl) ⟨122378, by rfl⟩ : syracuseStep 163171 = 244757) B244757
theorem B425357 : Blo 111784 425357 := bstep (se 3 (by rfl) ⟨79754, by rfl⟩ : syracuseStep 425357 = 159509) B159509
theorem B491021 : Blo 111784 491021 := bstep (se 3 (by rfl) ⟨92066, by rfl⟩ : syracuseStep 491021 = 184133) B184133
theorem B327185 : Blo 111784 327185 := bstep (se 2 (by rfl) ⟨122694, by rfl⟩ : syracuseStep 327185 = 245389) B245389
theorem B196337 : Blo 111784 196337 := bstep (se 2 (by rfl) ⟨73626, by rfl⟩ : syracuseStep 196337 = 147253) B147253
theorem B2817845 : Blo 111784 2817845 := bstep (se 5 (by rfl) ⟨132086, by rfl⟩ : syracuseStep 2817845 = 264173) B264173
theorem B982853 : Blo 111784 982853 := bstep (se 4 (by rfl) ⟨92142, by rfl⟩ : syracuseStep 982853 = 184285) B184285
theorem B163729 : Blo 111784 163729 := bstep (se 2 (by rfl) ⟨61398, by rfl⟩ : syracuseStep 163729 = 122797) B122797
theorem B131059 : Blo 111784 131059 := bstep (se 1 (by rfl) ⟨98294, by rfl⟩ : syracuseStep 131059 = 196589) B196589
theorem B983171 : Blo 111784 983171 := bstep (se 1 (by rfl) ⟨737378, by rfl⟩ : syracuseStep 983171 = 1474757) B1474757
theorem B491665 : Blo 111784 491665 := bstep (se 2 (by rfl) ⟨184374, by rfl⟩ : syracuseStep 491665 = 368749) B368749
theorem B163991 : Blo 111784 163991 := bstep (se 1 (by rfl) ⟨122993, by rfl⟩ : syracuseStep 163991 = 245987) B245987
theorem B327959 : Blo 111784 327959 := bstep (se 1 (by rfl) ⟨245969, by rfl⟩ : syracuseStep 327959 = 491939) B491939
theorem B426329 : Blo 111784 426329 := bstep (se 2 (by rfl) ⟨159873, by rfl⟩ : syracuseStep 426329 = 319747) B319747
theorem B197081 : Blo 111784 197081 := bstep (se 2 (by rfl) ⟨73905, by rfl⟩ : syracuseStep 197081 = 147811) B147811
theorem B426647 : Blo 111784 426647 := bstep (se 1 (by rfl) ⟨319985, by rfl⟩ : syracuseStep 426647 = 639971) B639971
theorem B361523 : Blo 111784 361523 := bstep (se 1 (by rfl) ⟨271142, by rfl⟩ : syracuseStep 361523 = 542285) B542285
theorem B328769 : Blo 111784 328769 := bstep (se 2 (by rfl) ⟨123288, by rfl⟩ : syracuseStep 328769 = 246577) B246577
theorem B361675 : Blo 111784 361675 := bstep (se 1 (by rfl) ⟨271256, by rfl⟩ : syracuseStep 361675 = 542513) B542513
theorem B427315 : Blo 111784 427315 := bstep (se 1 (by rfl) ⟨320486, by rfl⟩ : syracuseStep 427315 = 640973) B640973
theorem B918935 : Blo 111784 918935 := bstep (se 1 (by rfl) ⟨689201, by rfl⟩ : syracuseStep 918935 = 1378403) B1378403
theorem B362177 : Blo 111784 362177 := bstep (se 2 (by rfl) ⟨135816, by rfl⟩ : syracuseStep 362177 = 271633) B271633
theorem B493249 : Blo 111784 493249 := bstep (se 2 (by rfl) ⟨184968, by rfl⟩ : syracuseStep 493249 = 369937) B369937
theorem B722789 : Blo 111784 722789 := bstep (se 4 (by rfl) ⟨67761, by rfl⟩ : syracuseStep 722789 = 135523) B135523
theorem B296855 : Blo 111784 296855 := bstep (se 1 (by rfl) ⟨222641, by rfl⟩ : syracuseStep 296855 = 445283) B445283
theorem B329665 : Blo 111784 329665 := bstep (se 2 (by rfl) ⟨123624, by rfl⟩ : syracuseStep 329665 = 247249) B247249
theorem B1050803 : Blo 111784 1050803 := bstep (se 1 (by rfl) ⟨788102, by rfl⟩ : syracuseStep 1050803 = 1576205) B1576205
theorem B919873 : Blo 111784 919873 := bstep (se 2 (by rfl) ⟨344952, by rfl⟩ : syracuseStep 919873 = 689905) B689905
theorem B526771 : Blo 111784 526771 := bstep (se 1 (by rfl) ⟨395078, by rfl⟩ : syracuseStep 526771 = 790157) B790157
theorem B461315 : Blo 111784 461315 := bstep (se 1 (by rfl) ⟨345986, by rfl⟩ : syracuseStep 461315 = 691973) B691973
theorem B428561 : Blo 111784 428561 := bstep (se 2 (by rfl) ⟨160710, by rfl⟩ : syracuseStep 428561 = 321421) B321421
theorem B429259 : Blo 111784 429259 := bstep (se 1 (by rfl) ⟨321944, by rfl⟩ : syracuseStep 429259 = 643889) B643889
theorem B3083669 : Blo 111784 3083669 := bstep (se 6 (by rfl) ⟨72273, by rfl⟩ : syracuseStep 3083669 = 144547) B144547
theorem B527809 : Blo 111784 527809 := bstep (se 2 (by rfl) ⟨197928, by rfl⟩ : syracuseStep 527809 = 395857) B395857
theorem B495065 : Blo 111784 495065 := bstep (se 2 (by rfl) ⟨185649, by rfl⟩ : syracuseStep 495065 = 371299) B371299
theorem B429533 : Blo 111784 429533 := bstep (se 3 (by rfl) ⟨80537, by rfl⟩ : syracuseStep 429533 = 161075) B161075
theorem B232961 : Blo 111784 232961 := bstep (se 2 (by rfl) ⟨87360, by rfl⟩ : syracuseStep 232961 = 174721) B174721
theorem B167705 : Blo 111784 167705 := bstep (se 2 (by rfl) ⟨62889, by rfl⟩ : syracuseStep 167705 = 125779) B125779
theorem B167819 : Blo 111784 167819 := bstep (se 1 (by rfl) ⟨125864, by rfl⟩ : syracuseStep 167819 = 251729) B251729
theorem B167831 : Blo 111784 167831 := bstep (se 1 (by rfl) ⟨125873, by rfl⟩ : syracuseStep 167831 = 251747) B251747
theorem B167897 : Blo 111784 167897 := bstep (se 2 (by rfl) ⟨62961, by rfl⟩ : syracuseStep 167897 = 125923) B125923
theorem B168011 : Blo 111784 168011 := bstep (se 1 (by rfl) ⟨126008, by rfl⟩ : syracuseStep 168011 = 252017) B252017
theorem B168023 : Blo 111784 168023 := bstep (se 1 (by rfl) ⟨126017, by rfl⟩ : syracuseStep 168023 = 252035) B252035
theorem B462941 : Blo 111784 462941 := bstep (se 3 (by rfl) ⟨86801, by rfl⟩ : syracuseStep 462941 = 173603) B173603
theorem B364637 : Blo 111784 364637 := bstep (se 3 (by rfl) ⟨68369, by rfl⟩ : syracuseStep 364637 = 136739) B136739
theorem B430231 : Blo 111784 430231 := bstep (se 1 (by rfl) ⟨322673, by rfl⟩ : syracuseStep 430231 = 645347) B645347
theorem B168089 : Blo 111784 168089 := bstep (se 2 (by rfl) ⟨63033, by rfl⟩ : syracuseStep 168089 = 126067) B126067
theorem B168203 : Blo 111784 168203 := bstep (se 1 (by rfl) ⟨126152, by rfl⟩ : syracuseStep 168203 = 252305) B252305
theorem B168215 : Blo 111784 168215 := bstep (se 1 (by rfl) ⟨126161, by rfl⟩ : syracuseStep 168215 = 252323) B252323
theorem B168281 : Blo 111784 168281 := bstep (se 2 (by rfl) ⟨63105, by rfl⟩ : syracuseStep 168281 = 126211) B126211
theorem B168395 : Blo 111784 168395 := bstep (se 1 (by rfl) ⟨126296, by rfl⟩ : syracuseStep 168395 = 252593) B252593
theorem B168407 : Blo 111784 168407 := bstep (se 1 (by rfl) ⟨126305, by rfl⟩ : syracuseStep 168407 = 252611) B252611
theorem B168473 : Blo 111784 168473 := bstep (se 2 (by rfl) ⟨63177, by rfl⟩ : syracuseStep 168473 = 126355) B126355
theorem B168587 : Blo 111784 168587 := bstep (se 1 (by rfl) ⟨126440, by rfl⟩ : syracuseStep 168587 = 252881) B252881
theorem B168599 : Blo 111784 168599 := bstep (se 1 (by rfl) ⟨126449, by rfl⟩ : syracuseStep 168599 = 252899) B252899
theorem B168665 : Blo 111784 168665 := bstep (se 2 (by rfl) ⟨63249, by rfl⟩ : syracuseStep 168665 = 126499) B126499
theorem B3707633 : Blo 111784 3707633 := bstep (se 2 (by rfl) ⟨1390362, by rfl⟩ : syracuseStep 3707633 = 2780725) B2780725
theorem B168779 : Blo 111784 168779 := bstep (se 1 (by rfl) ⟨126584, by rfl⟩ : syracuseStep 168779 = 253169) B253169
theorem B168791 : Blo 111784 168791 := bstep (se 1 (by rfl) ⟨126593, by rfl⟩ : syracuseStep 168791 = 253187) B253187
theorem B693143 : Blo 111784 693143 := bstep (se 1 (by rfl) ⟨519857, by rfl⟩ : syracuseStep 693143 = 1039715) B1039715
theorem B168857 : Blo 111784 168857 := bstep (se 2 (by rfl) ⟨63321, by rfl⟩ : syracuseStep 168857 = 126643) B126643
theorem B431021 : Blo 111784 431021 := bstep (se 3 (by rfl) ⟨80816, by rfl⟩ : syracuseStep 431021 = 161633) B161633
theorem B332765 : Blo 111784 332765 := bstep (se 3 (by rfl) ⟨62393, by rfl⟩ : syracuseStep 332765 = 124787) B124787
theorem B168971 : Blo 111784 168971 := bstep (se 1 (by rfl) ⟨126728, by rfl⟩ : syracuseStep 168971 = 253457) B253457
theorem B168983 : Blo 111784 168983 := bstep (se 1 (by rfl) ⟨126737, by rfl⟩ : syracuseStep 168983 = 253475) B253475
theorem B169049 : Blo 111784 169049 := bstep (se 2 (by rfl) ⟨63393, by rfl⟩ : syracuseStep 169049 = 126787) B126787
theorem B169163 : Blo 111784 169163 := bstep (se 1 (by rfl) ⟨126872, by rfl⟩ : syracuseStep 169163 = 253745) B253745
theorem B169175 : Blo 111784 169175 := bstep (se 1 (by rfl) ⟨126881, by rfl⟩ : syracuseStep 169175 = 253763) B253763
theorem B169241 : Blo 111784 169241 := bstep (se 2 (by rfl) ⟨63465, by rfl⟩ : syracuseStep 169241 = 126931) B126931
theorem B791909 : Blo 111784 791909 := bstep (se 4 (by rfl) ⟨74241, by rfl⟩ : syracuseStep 791909 = 148483) B148483
theorem B169355 : Blo 111784 169355 := bstep (se 1 (by rfl) ⟨127016, by rfl⟩ : syracuseStep 169355 = 254033) B254033
theorem B169367 : Blo 111784 169367 := bstep (se 1 (by rfl) ⟨127025, by rfl⟩ : syracuseStep 169367 = 254051) B254051
theorem B169433 : Blo 111784 169433 := bstep (se 2 (by rfl) ⟨63537, by rfl⟩ : syracuseStep 169433 = 127075) B127075
theorem B169547 : Blo 111784 169547 := bstep (se 1 (by rfl) ⟨127160, by rfl⟩ : syracuseStep 169547 = 254321) B254321
theorem B169559 : Blo 111784 169559 := bstep (se 1 (by rfl) ⟨127169, by rfl⟩ : syracuseStep 169559 = 254339) B254339
theorem B169625 : Blo 111784 169625 := bstep (se 2 (by rfl) ⟨63609, by rfl⟩ : syracuseStep 169625 = 127219) B127219
theorem B1087181 : Blo 111784 1087181 := bstep (se 3 (by rfl) ⟨203846, by rfl⟩ : syracuseStep 1087181 = 407693) B407693
theorem B169739 : Blo 111784 169739 := bstep (se 1 (by rfl) ⟨127304, by rfl⟩ : syracuseStep 169739 = 254609) B254609
theorem B169751 : Blo 111784 169751 := bstep (se 1 (by rfl) ⟨127313, by rfl⟩ : syracuseStep 169751 = 254627) B254627
theorem B137047 : Blo 111784 137047 := bstep (se 1 (by rfl) ⟨102785, by rfl⟩ : syracuseStep 137047 = 205571) B205571
theorem B169817 : Blo 111784 169817 := bstep (se 2 (by rfl) ⟨63681, by rfl⟩ : syracuseStep 169817 = 127363) B127363
theorem B169931 : Blo 111784 169931 := bstep (se 1 (by rfl) ⟨127448, by rfl⟩ : syracuseStep 169931 = 254897) B254897
theorem B169943 : Blo 111784 169943 := bstep (se 1 (by rfl) ⟨127457, by rfl⟩ : syracuseStep 169943 = 254915) B254915
theorem B170009 : Blo 111784 170009 := bstep (se 2 (by rfl) ⟨63753, by rfl⟩ : syracuseStep 170009 = 127507) B127507
theorem B170123 : Blo 111784 170123 := bstep (se 1 (by rfl) ⟨127592, by rfl⟩ : syracuseStep 170123 = 255185) B255185
theorem B170135 : Blo 111784 170135 := bstep (se 1 (by rfl) ⟨127601, by rfl⟩ : syracuseStep 170135 = 255203) B255203
theorem B170201 : Blo 111784 170201 := bstep (se 2 (by rfl) ⟨63825, by rfl⟩ : syracuseStep 170201 = 127651) B127651
theorem B203033 : Blo 111784 203033 := bstep (se 2 (by rfl) ⟨76137, by rfl⟩ : syracuseStep 203033 = 152275) B152275
theorem B432449 : Blo 111784 432449 := bstep (se 2 (by rfl) ⟨162168, by rfl⟩ : syracuseStep 432449 = 324337) B324337
theorem B170315 : Blo 111784 170315 := bstep (se 1 (by rfl) ⟨127736, by rfl⟩ : syracuseStep 170315 = 255473) B255473
theorem B170327 : Blo 111784 170327 := bstep (se 1 (by rfl) ⟨127745, by rfl⟩ : syracuseStep 170327 = 255491) B255491
theorem B170393 : Blo 111784 170393 := bstep (se 2 (by rfl) ⟨63897, by rfl⟩ : syracuseStep 170393 = 127795) B127795
theorem B2038193 : Blo 111784 2038193 := bstep (se 2 (by rfl) ⟨764322, by rfl⟩ : syracuseStep 2038193 = 1528645) B1528645
theorem B170507 : Blo 111784 170507 := bstep (se 1 (by rfl) ⟨127880, by rfl⟩ : syracuseStep 170507 = 255761) B255761
theorem B1645069 : Blo 111784 1645069 := bstep (se 3 (by rfl) ⟨308450, by rfl⟩ : syracuseStep 1645069 = 616901) B616901
theorem B170519 : Blo 111784 170519 := bstep (se 1 (by rfl) ⟨127889, by rfl⟩ : syracuseStep 170519 = 255779) B255779
theorem B170585 : Blo 111784 170585 := bstep (se 2 (by rfl) ⟨63969, by rfl⟩ : syracuseStep 170585 = 127939) B127939
theorem B170699 : Blo 111784 170699 := bstep (se 1 (by rfl) ⟨128024, by rfl⟩ : syracuseStep 170699 = 256049) B256049
theorem B170711 : Blo 111784 170711 := bstep (se 1 (by rfl) ⟨128033, by rfl⟩ : syracuseStep 170711 = 256067) B256067
theorem B170777 : Blo 111784 170777 := bstep (se 2 (by rfl) ⟨64041, by rfl⟩ : syracuseStep 170777 = 128083) B128083
theorem B170891 : Blo 111784 170891 := bstep (se 1 (by rfl) ⟨128168, by rfl⟩ : syracuseStep 170891 = 256337) B256337
theorem B170903 : Blo 111784 170903 := bstep (se 1 (by rfl) ⟨128177, by rfl⟩ : syracuseStep 170903 = 256355) B256355
theorem B990103 : Blo 111784 990103 := bstep (se 1 (by rfl) ⟨742577, by rfl⟩ : syracuseStep 990103 = 1485155) B1485155
theorem B170969 : Blo 111784 170969 := bstep (se 2 (by rfl) ⟨64113, by rfl⟩ : syracuseStep 170969 = 128227) B128227
theorem B269335 : Blo 111784 269335 := bstep (se 1 (by rfl) ⟨202001, by rfl⟩ : syracuseStep 269335 = 404003) B404003
theorem B2333771 : Blo 111784 2333771 := bstep (se 1 (by rfl) ⟨1750328, by rfl⟩ : syracuseStep 2333771 = 3500657) B3500657
theorem B171083 : Blo 111784 171083 := bstep (se 1 (by rfl) ⟨128312, by rfl⟩ : syracuseStep 171083 = 256625) B256625
theorem B171095 : Blo 111784 171095 := bstep (se 1 (by rfl) ⟨128321, by rfl⟩ : syracuseStep 171095 = 256643) B256643
theorem B171161 : Blo 111784 171161 := bstep (se 2 (by rfl) ⟨64185, by rfl⟩ : syracuseStep 171161 = 128371) B128371
theorem B171275 : Blo 111784 171275 := bstep (se 1 (by rfl) ⟨128456, by rfl⟩ : syracuseStep 171275 = 256913) B256913
theorem B171287 : Blo 111784 171287 := bstep (se 1 (by rfl) ⟨128465, by rfl⟩ : syracuseStep 171287 = 256931) B256931
theorem B171353 : Blo 111784 171353 := bstep (se 2 (by rfl) ⟨64257, by rfl⟩ : syracuseStep 171353 = 128515) B128515
theorem B171467 : Blo 111784 171467 := bstep (se 1 (by rfl) ⟨128600, by rfl⟩ : syracuseStep 171467 = 257201) B257201
theorem B171479 : Blo 111784 171479 := bstep (se 1 (by rfl) ⟨128609, by rfl⟩ : syracuseStep 171479 = 257219) B257219
theorem B171545 : Blo 111784 171545 := bstep (se 2 (by rfl) ⟨64329, by rfl⟩ : syracuseStep 171545 = 128659) B128659
theorem B171659 : Blo 111784 171659 := bstep (se 1 (by rfl) ⟨128744, by rfl⟩ : syracuseStep 171659 = 257489) B257489
theorem B171671 : Blo 111784 171671 := bstep (se 1 (by rfl) ⟨128753, by rfl⟩ : syracuseStep 171671 = 257507) B257507
theorem B204481 : Blo 111784 204481 := bstep (se 2 (by rfl) ⟨76680, by rfl⟩ : syracuseStep 204481 = 153361) B153361
theorem B171737 : Blo 111784 171737 := bstep (se 2 (by rfl) ⟨64401, by rfl⟩ : syracuseStep 171737 = 128803) B128803
theorem B433937 : Blo 111784 433937 := bstep (se 2 (by rfl) ⟨162726, by rfl⟩ : syracuseStep 433937 = 325453) B325453
theorem B433943 : Blo 111784 433943 := bstep (se 1 (by rfl) ⟨325457, by rfl⟩ : syracuseStep 433943 = 650915) B650915
theorem B171851 : Blo 111784 171851 := bstep (se 1 (by rfl) ⟨128888, by rfl⟩ : syracuseStep 171851 = 257777) B257777
theorem B171863 : Blo 111784 171863 := bstep (se 1 (by rfl) ⟨128897, by rfl⟩ : syracuseStep 171863 = 257795) B257795
theorem B171929 : Blo 111784 171929 := bstep (se 2 (by rfl) ⟨64473, by rfl⟩ : syracuseStep 171929 = 128947) B128947
theorem B172043 : Blo 111784 172043 := bstep (se 1 (by rfl) ⟨129032, by rfl⟩ : syracuseStep 172043 = 258065) B258065
theorem B172055 : Blo 111784 172055 := bstep (se 1 (by rfl) ⟨129041, by rfl⟩ : syracuseStep 172055 = 258083) B258083
theorem B172121 : Blo 111784 172121 := bstep (se 2 (by rfl) ⟨64545, by rfl⟩ : syracuseStep 172121 = 129091) B129091
theorem B172235 : Blo 111784 172235 := bstep (se 1 (by rfl) ⟨129176, by rfl⟩ : syracuseStep 172235 = 258353) B258353
theorem B172247 : Blo 111784 172247 := bstep (se 1 (by rfl) ⟨129185, by rfl⟩ : syracuseStep 172247 = 258371) B258371
theorem B434393 : Blo 111784 434393 := bstep (se 2 (by rfl) ⟨162897, by rfl⟩ : syracuseStep 434393 = 325795) B325795
theorem B205057 : Blo 111784 205057 := bstep (se 2 (by rfl) ⟨76896, by rfl⟩ : syracuseStep 205057 = 153793) B153793
theorem B172313 : Blo 111784 172313 := bstep (se 2 (by rfl) ⟨64617, by rfl⟩ : syracuseStep 172313 = 129235) B129235
theorem B172427 : Blo 111784 172427 := bstep (se 1 (by rfl) ⟨129320, by rfl⟩ : syracuseStep 172427 = 258641) B258641
theorem B172439 : Blo 111784 172439 := bstep (se 1 (by rfl) ⟨129329, by rfl⟩ : syracuseStep 172439 = 258659) B258659
theorem B434605 : Blo 111784 434605 := bstep (se 3 (by rfl) ⟨81488, by rfl⟩ : syracuseStep 434605 = 162977) B162977
theorem B205259 : Blo 111784 205259 := bstep (se 1 (by rfl) ⟨153944, by rfl⟩ : syracuseStep 205259 = 307889) B307889
theorem B172505 : Blo 111784 172505 := bstep (se 2 (by rfl) ⟨64689, by rfl⟩ : syracuseStep 172505 = 129379) B129379
theorem B205337 : Blo 111784 205337 := bstep (se 2 (by rfl) ⟨77001, by rfl⟩ : syracuseStep 205337 = 154003) B154003
theorem B172619 : Blo 111784 172619 := bstep (se 1 (by rfl) ⟨129464, by rfl⟩ : syracuseStep 172619 = 258929) B258929
theorem B172631 : Blo 111784 172631 := bstep (se 1 (by rfl) ⟨129473, by rfl⟩ : syracuseStep 172631 = 258947) B258947
theorem B3711581 : Blo 111784 3711581 := bstep (se 3 (by rfl) ⟨695921, by rfl⟩ : syracuseStep 3711581 = 1391843) B1391843
theorem B172697 : Blo 111784 172697 := bstep (se 2 (by rfl) ⟨64761, by rfl⟩ : syracuseStep 172697 = 129523) B129523
theorem B172759 : Blo 111784 172759 := bstep (se 1 (by rfl) ⟨129569, by rfl⟩ : syracuseStep 172759 = 259139) B259139
theorem B434909 : Blo 111784 434909 := bstep (se 3 (by rfl) ⟨81545, by rfl⟩ : syracuseStep 434909 = 163091) B163091
theorem B172811 : Blo 111784 172811 := bstep (se 1 (by rfl) ⟨129608, by rfl⟩ : syracuseStep 172811 = 259217) B259217
theorem B172823 : Blo 111784 172823 := bstep (se 1 (by rfl) ⟨129617, by rfl⟩ : syracuseStep 172823 = 259235) B259235
theorem B172889 : Blo 111784 172889 := bstep (se 2 (by rfl) ⟨64833, by rfl⟩ : syracuseStep 172889 = 129667) B129667
theorem B205721 : Blo 111784 205721 := bstep (se 2 (by rfl) ⟨77145, by rfl⟩ : syracuseStep 205721 = 154291) B154291
theorem B173003 : Blo 111784 173003 := bstep (se 1 (by rfl) ⟨129752, by rfl⟩ : syracuseStep 173003 = 259505) B259505
theorem B173015 : Blo 111784 173015 := bstep (se 1 (by rfl) ⟨129761, by rfl⟩ : syracuseStep 173015 = 259523) B259523
theorem B369625 : Blo 111784 369625 := bstep (se 2 (by rfl) ⟨138609, by rfl⟩ : syracuseStep 369625 = 277219) B277219
theorem B173081 : Blo 111784 173081 := bstep (se 2 (by rfl) ⟨64905, by rfl⟩ : syracuseStep 173081 = 129811) B129811
theorem B173195 : Blo 111784 173195 := bstep (se 1 (by rfl) ⟨129896, by rfl⟩ : syracuseStep 173195 = 259793) B259793
theorem B173207 : Blo 111784 173207 := bstep (se 1 (by rfl) ⟨129905, by rfl⟩ : syracuseStep 173207 = 259811) B259811
theorem B173273 : Blo 111784 173273 := bstep (se 2 (by rfl) ⟨64977, by rfl⟩ : syracuseStep 173273 = 129955) B129955
theorem B828737 : Blo 111784 828737 := bstep (se 2 (by rfl) ⟨310776, by rfl⟩ : syracuseStep 828737 = 621553) B621553
theorem B173387 : Blo 111784 173387 := bstep (se 1 (by rfl) ⟨130040, by rfl⟩ : syracuseStep 173387 = 260081) B260081
theorem B173399 : Blo 111784 173399 := bstep (se 1 (by rfl) ⟨130049, by rfl⟩ : syracuseStep 173399 = 260099) B260099
theorem B173465 : Blo 111784 173465 := bstep (se 2 (by rfl) ⟨65049, by rfl⟩ : syracuseStep 173465 = 130099) B130099
theorem B4793813 : Blo 111784 4793813 := bstep (se 7 (by rfl) ⟨56177, by rfl⟩ : syracuseStep 4793813 = 112355) B112355
theorem B173579 : Blo 111784 173579 := bstep (se 1 (by rfl) ⟨130184, by rfl⟩ : syracuseStep 173579 = 260369) B260369
theorem B173591 : Blo 111784 173591 := bstep (se 1 (by rfl) ⟨130193, by rfl⟩ : syracuseStep 173591 = 260387) B260387
theorem B173657 : Blo 111784 173657 := bstep (se 2 (by rfl) ⟨65121, by rfl⟩ : syracuseStep 173657 = 130243) B130243
theorem B272179 : Blo 111784 272179 := bstep (se 1 (by rfl) ⟨204134, by rfl⟩ : syracuseStep 272179 = 408269) B408269
theorem B141527 : Blo 111784 141527 := bstep (se 1 (by rfl) ⟨106145, by rfl⟩ : syracuseStep 141527 = 212291) B212291
theorem B207127 : Blo 111784 207127 := bstep (se 1 (by rfl) ⟨155345, by rfl⟩ : syracuseStep 207127 = 310691) B310691
theorem B1648997 : Blo 111784 1648997 := bstep (se 4 (by rfl) ⟨154593, by rfl⟩ : syracuseStep 1648997 = 309187) B309187
theorem B1878563 : Blo 111784 1878563 := bstep (se 1 (by rfl) ⟨1408922, by rfl⟩ : syracuseStep 1878563 = 2817845) B2817845
theorem B174745 : Blo 111784 174745 := bstep (se 2 (by rfl) ⟨65529, by rfl⟩ : syracuseStep 174745 = 131059) B131059
theorem B666443 : Blo 111784 666443 := bstep (se 1 (by rfl) ⟨499832, by rfl⟩ : syracuseStep 666443 = 999665) B999665
theorem B142231 : Blo 111784 142231 := bstep (se 1 (by rfl) ⟨106673, by rfl⟩ : syracuseStep 142231 = 213347) B213347
theorem B4107185 : Blo 111784 4107185 := bstep (se 2 (by rfl) ⟨1540194, by rfl⟩ : syracuseStep 4107185 = 3080389) B3080389
theorem B240563 : Blo 111784 240563 := bstep (se 1 (by rfl) ⟨180422, by rfl⟩ : syracuseStep 240563 = 360845) B360845
theorem B994265 : Blo 111784 994265 := bstep (se 2 (by rfl) ⟨372849, by rfl⟩ : syracuseStep 994265 = 745699) B745699
theorem B207883 : Blo 111784 207883 := bstep (se 1 (by rfl) ⟨155912, by rfl⟩ : syracuseStep 207883 = 311825) B311825
theorem B1453261 : Blo 111784 1453261 := bstep (se 3 (by rfl) ⟨272486, by rfl⟩ : syracuseStep 1453261 = 544973) B544973
theorem B437507 : Blo 111784 437507 := bstep (se 1 (by rfl) ⟨328130, by rfl⟩ : syracuseStep 437507 = 656261) B656261
theorem B437521 : Blo 111784 437521 := bstep (se 2 (by rfl) ⟨164070, by rfl⟩ : syracuseStep 437521 = 328141) B328141
theorem B208279 : Blo 111784 208279 := bstep (se 1 (by rfl) ⟨156209, by rfl⟩ : syracuseStep 208279 = 312419) B312419
theorem B241049 : Blo 111784 241049 := bstep (se 2 (by rfl) ⟨90393, by rfl⟩ : syracuseStep 241049 = 180787) B180787
theorem B208345 : Blo 111784 208345 := bstep (se 2 (by rfl) ⟨78129, by rfl⟩ : syracuseStep 208345 = 156259) B156259
theorem B437825 : Blo 111784 437825 := bstep (se 2 (by rfl) ⟨164184, by rfl⟩ : syracuseStep 437825 = 328369) B328369
theorem B569105 : Blo 111784 569105 := bstep (se 2 (by rfl) ⟨213414, by rfl⟩ : syracuseStep 569105 = 426829) B426829
theorem B438061 : Blo 111784 438061 := bstep (se 3 (by rfl) ⟨82136, by rfl⟩ : syracuseStep 438061 = 164273) B164273
theorem B569267 : Blo 111784 569267 := bstep (se 1 (by rfl) ⟨426950, by rfl⟩ : syracuseStep 569267 = 853901) B853901
theorem B831505 : Blo 111784 831505 := bstep (se 2 (by rfl) ⟨311814, by rfl⟩ : syracuseStep 831505 = 623629) B623629
theorem B274583 : Blo 111784 274583 := bstep (se 1 (by rfl) ⟨205937, by rfl⟩ : syracuseStep 274583 = 411875) B411875
theorem B438493 : Blo 111784 438493 := bstep (se 3 (by rfl) ⟨82217, by rfl⟩ : syracuseStep 438493 = 164435) B164435
theorem B143947 : Blo 111784 143947 := bstep (se 1 (by rfl) ⟨107960, by rfl⟩ : syracuseStep 143947 = 215921) B215921
theorem B963373 : Blo 111784 963373 := bstep (se 3 (by rfl) ⟨180632, by rfl⟩ : syracuseStep 963373 = 361265) B361265
theorem B242689 : Blo 111784 242689 := bstep (se 2 (by rfl) ⟨91008, by rfl⟩ : syracuseStep 242689 = 182017) B182017
theorem B439427 : Blo 111784 439427 := bstep (se 1 (by rfl) ⟨329570, by rfl⟩ : syracuseStep 439427 = 659141) B659141
theorem B111787 : Blo 111784 111787 := bstep (se 1 (by rfl) ⟨83840, by rfl⟩ : syracuseStep 111787 = 167681) B167681
theorem B111799 : Blo 111784 111799 := bstep (se 1 (by rfl) ⟨83849, by rfl⟩ : syracuseStep 111799 = 167699) B167699
theorem B111819 : Blo 111784 111819 := bstep (se 1 (by rfl) ⟨83864, by rfl⟩ : syracuseStep 111819 = 167729) B167729
theorem B111831 : Blo 111784 111831 := bstep (se 1 (by rfl) ⟨83873, by rfl⟩ : syracuseStep 111831 = 167747) B167747
theorem B111851 : Blo 111784 111851 := bstep (se 1 (by rfl) ⟨83888, by rfl⟩ : syracuseStep 111851 = 167777) B167777
theorem B111863 : Blo 111784 111863 := bstep (se 1 (by rfl) ⟨83897, by rfl⟩ : syracuseStep 111863 = 167795) B167795
theorem B111883 : Blo 111784 111883 := bstep (se 1 (by rfl) ⟨83912, by rfl⟩ : syracuseStep 111883 = 167825) B167825
theorem B111895 : Blo 111784 111895 := bstep (se 1 (by rfl) ⟨83921, by rfl⟩ : syracuseStep 111895 = 167843) B167843
theorem B111915 : Blo 111784 111915 := bstep (se 1 (by rfl) ⟨83936, by rfl⟩ : syracuseStep 111915 = 167873) B167873
theorem B111927 : Blo 111784 111927 := bstep (se 1 (by rfl) ⟨83945, by rfl⟩ : syracuseStep 111927 = 167891) B167891
theorem B111947 : Blo 111784 111947 := bstep (se 1 (by rfl) ⟨83960, by rfl⟩ : syracuseStep 111947 = 167921) B167921
theorem B111959 : Blo 111784 111959 := bstep (se 1 (by rfl) ⟨83969, by rfl⟩ : syracuseStep 111959 = 167939) B167939
theorem B406873 : Blo 111784 406873 := bstep (se 2 (by rfl) ⟨152577, by rfl⟩ : syracuseStep 406873 = 305155) B305155
theorem B111979 : Blo 111784 111979 := bstep (se 1 (by rfl) ⟨83984, by rfl⟩ : syracuseStep 111979 = 167969) B167969
theorem B111991 : Blo 111784 111991 := bstep (se 1 (by rfl) ⟨83993, by rfl⟩ : syracuseStep 111991 = 167987) B167987
theorem B112011 : Blo 111784 112011 := bstep (se 1 (by rfl) ⟨84008, by rfl⟩ : syracuseStep 112011 = 168017) B168017
theorem B112023 : Blo 111784 112023 := bstep (se 1 (by rfl) ⟨84017, by rfl⟩ : syracuseStep 112023 = 168035) B168035
theorem B112043 : Blo 111784 112043 := bstep (se 1 (by rfl) ⟨84032, by rfl⟩ : syracuseStep 112043 = 168065) B168065
theorem B112055 : Blo 111784 112055 := bstep (se 1 (by rfl) ⟨84041, by rfl⟩ : syracuseStep 112055 = 168083) B168083
theorem B112075 : Blo 111784 112075 := bstep (se 1 (by rfl) ⟨84056, by rfl⟩ : syracuseStep 112075 = 168113) B168113
theorem B112087 : Blo 111784 112087 := bstep (se 1 (by rfl) ⟨84065, by rfl⟩ : syracuseStep 112087 = 168131) B168131
theorem B308701 : Blo 111784 308701 := bstep (se 3 (by rfl) ⟨57881, by rfl⟩ : syracuseStep 308701 = 115763) B115763
theorem B112107 : Blo 111784 112107 := bstep (se 1 (by rfl) ⟨84080, by rfl⟩ : syracuseStep 112107 = 168161) B168161
theorem B112119 : Blo 111784 112119 := bstep (se 1 (by rfl) ⟨84089, by rfl⟩ : syracuseStep 112119 = 168179) B168179
theorem B112139 : Blo 111784 112139 := bstep (se 1 (by rfl) ⟨84104, by rfl⟩ : syracuseStep 112139 = 168209) B168209
theorem B112151 : Blo 111784 112151 := bstep (se 1 (by rfl) ⟨84113, by rfl⟩ : syracuseStep 112151 = 168227) B168227
theorem B144919 : Blo 111784 144919 := bstep (se 1 (by rfl) ⟨108689, by rfl⟩ : syracuseStep 144919 = 217379) B217379
theorem B112171 : Blo 111784 112171 := bstep (se 1 (by rfl) ⟨84128, by rfl⟩ : syracuseStep 112171 = 168257) B168257
theorem B112183 : Blo 111784 112183 := bstep (se 1 (by rfl) ⟨84137, by rfl⟩ : syracuseStep 112183 = 168275) B168275
theorem B112203 : Blo 111784 112203 := bstep (se 1 (by rfl) ⟨84152, by rfl⟩ : syracuseStep 112203 = 168305) B168305
theorem B112215 : Blo 111784 112215 := bstep (se 1 (by rfl) ⟨84161, by rfl⟩ : syracuseStep 112215 = 168323) B168323
theorem B112235 : Blo 111784 112235 := bstep (se 1 (by rfl) ⟨84176, by rfl⟩ : syracuseStep 112235 = 168353) B168353
theorem B112247 : Blo 111784 112247 := bstep (se 1 (by rfl) ⟨84185, by rfl⟩ : syracuseStep 112247 = 168371) B168371
theorem B112267 : Blo 111784 112267 := bstep (se 1 (by rfl) ⟨84200, by rfl⟩ : syracuseStep 112267 = 168401) B168401
theorem B112279 : Blo 111784 112279 := bstep (se 1 (by rfl) ⟨84209, by rfl⟩ : syracuseStep 112279 = 168419) B168419
theorem B112299 : Blo 111784 112299 := bstep (se 1 (by rfl) ⟨84224, by rfl⟩ : syracuseStep 112299 = 168449) B168449
theorem B112311 : Blo 111784 112311 := bstep (se 1 (by rfl) ⟨84233, by rfl⟩ : syracuseStep 112311 = 168467) B168467
theorem B112331 : Blo 111784 112331 := bstep (se 1 (by rfl) ⟨84248, by rfl⟩ : syracuseStep 112331 = 168497) B168497
theorem B112343 : Blo 111784 112343 := bstep (se 1 (by rfl) ⟨84257, by rfl⟩ : syracuseStep 112343 = 168515) B168515
theorem B407261 : Blo 111784 407261 := bstep (se 3 (by rfl) ⟨76361, by rfl⟩ : syracuseStep 407261 = 152723) B152723
theorem B112363 : Blo 111784 112363 := bstep (se 1 (by rfl) ⟨84272, by rfl⟩ : syracuseStep 112363 = 168545) B168545
theorem B112375 : Blo 111784 112375 := bstep (se 1 (by rfl) ⟨84281, by rfl⟩ : syracuseStep 112375 = 168563) B168563
theorem B112395 : Blo 111784 112395 := bstep (se 1 (by rfl) ⟨84296, by rfl⟩ : syracuseStep 112395 = 168593) B168593
theorem B112407 : Blo 111784 112407 := bstep (se 1 (by rfl) ⟨84305, by rfl⟩ : syracuseStep 112407 = 168611) B168611
theorem B112427 : Blo 111784 112427 := bstep (se 1 (by rfl) ⟨84320, by rfl⟩ : syracuseStep 112427 = 168641) B168641
theorem B112439 : Blo 111784 112439 := bstep (se 1 (by rfl) ⟨84329, by rfl⟩ : syracuseStep 112439 = 168659) B168659
theorem B112459 : Blo 111784 112459 := bstep (se 1 (by rfl) ⟨84344, by rfl⟩ : syracuseStep 112459 = 168689) B168689
theorem B571211 : Blo 111784 571211 := bstep (se 1 (by rfl) ⟨428408, by rfl⟩ : syracuseStep 571211 = 856817) B856817
theorem B112471 : Blo 111784 112471 := bstep (se 1 (by rfl) ⟨84353, by rfl⟩ : syracuseStep 112471 = 168707) B168707
theorem B112491 : Blo 111784 112491 := bstep (se 1 (by rfl) ⟨84368, by rfl⟩ : syracuseStep 112491 = 168737) B168737
theorem B112503 : Blo 111784 112503 := bstep (se 1 (by rfl) ⟨84377, by rfl⟩ : syracuseStep 112503 = 168755) B168755
theorem B112523 : Blo 111784 112523 := bstep (se 1 (by rfl) ⟨84392, by rfl⟩ : syracuseStep 112523 = 168785) B168785
theorem B112535 : Blo 111784 112535 := bstep (se 1 (by rfl) ⟨84401, by rfl⟩ : syracuseStep 112535 = 168803) B168803
theorem B309143 : Blo 111784 309143 := bstep (se 1 (by rfl) ⟨231857, by rfl⟩ : syracuseStep 309143 = 463715) B463715
theorem B112555 : Blo 111784 112555 := bstep (se 1 (by rfl) ⟨84416, by rfl⟩ : syracuseStep 112555 = 168833) B168833
theorem B112567 : Blo 111784 112567 := bstep (se 1 (by rfl) ⟨84425, by rfl⟩ : syracuseStep 112567 = 168851) B168851
theorem B112587 : Blo 111784 112587 := bstep (se 1 (by rfl) ⟨84440, by rfl⟩ : syracuseStep 112587 = 168881) B168881
theorem B112599 : Blo 111784 112599 := bstep (se 1 (by rfl) ⟨84449, by rfl⟩ : syracuseStep 112599 = 168899) B168899
theorem B112619 : Blo 111784 112619 := bstep (se 1 (by rfl) ⟨84464, by rfl⟩ : syracuseStep 112619 = 168929) B168929
theorem B112631 : Blo 111784 112631 := bstep (se 1 (by rfl) ⟨84473, by rfl⟩ : syracuseStep 112631 = 168947) B168947
theorem B112651 : Blo 111784 112651 := bstep (se 1 (by rfl) ⟨84488, by rfl⟩ : syracuseStep 112651 = 168977) B168977
theorem B112663 : Blo 111784 112663 := bstep (se 1 (by rfl) ⟨84497, by rfl⟩ : syracuseStep 112663 = 168995) B168995
theorem B112683 : Blo 111784 112683 := bstep (se 1 (by rfl) ⟨84512, by rfl⟩ : syracuseStep 112683 = 169025) B169025
theorem B112695 : Blo 111784 112695 := bstep (se 1 (by rfl) ⟨84521, by rfl⟩ : syracuseStep 112695 = 169043) B169043
theorem B112715 : Blo 111784 112715 := bstep (se 1 (by rfl) ⟨84536, by rfl⟩ : syracuseStep 112715 = 169073) B169073
theorem B112727 : Blo 111784 112727 := bstep (se 1 (by rfl) ⟨84545, by rfl⟩ : syracuseStep 112727 = 169091) B169091
theorem B964709 : Blo 111784 964709 := bstep (se 4 (by rfl) ⟨90441, by rfl⟩ : syracuseStep 964709 = 180883) B180883
theorem B112747 : Blo 111784 112747 := bstep (se 1 (by rfl) ⟨84560, by rfl⟩ : syracuseStep 112747 = 169121) B169121
theorem B112759 : Blo 111784 112759 := bstep (se 1 (by rfl) ⟨84569, by rfl⟩ : syracuseStep 112759 = 169139) B169139
theorem B112779 : Blo 111784 112779 := bstep (se 1 (by rfl) ⟨84584, by rfl⟩ : syracuseStep 112779 = 169169) B169169
theorem B112791 : Blo 111784 112791 := bstep (se 1 (by rfl) ⟨84593, by rfl⟩ : syracuseStep 112791 = 169187) B169187
theorem B112811 : Blo 111784 112811 := bstep (se 1 (by rfl) ⟨84608, by rfl⟩ : syracuseStep 112811 = 169217) B169217
theorem B112823 : Blo 111784 112823 := bstep (se 1 (by rfl) ⟨84617, by rfl⟩ : syracuseStep 112823 = 169235) B169235
theorem B112843 : Blo 111784 112843 := bstep (se 1 (by rfl) ⟨84632, by rfl⟩ : syracuseStep 112843 = 169265) B169265
theorem B112855 : Blo 111784 112855 := bstep (se 1 (by rfl) ⟨84641, by rfl⟩ : syracuseStep 112855 = 169283) B169283
theorem B112875 : Blo 111784 112875 := bstep (se 1 (by rfl) ⟨84656, by rfl⟩ : syracuseStep 112875 = 169313) B169313
theorem B112887 : Blo 111784 112887 := bstep (se 1 (by rfl) ⟨84665, by rfl⟩ : syracuseStep 112887 = 169331) B169331
theorem B112907 : Blo 111784 112907 := bstep (se 1 (by rfl) ⟨84680, by rfl⟩ : syracuseStep 112907 = 169361) B169361
theorem B112919 : Blo 111784 112919 := bstep (se 1 (by rfl) ⟨84689, by rfl⟩ : syracuseStep 112919 = 169379) B169379
theorem B112939 : Blo 111784 112939 := bstep (se 1 (by rfl) ⟨84704, by rfl⟩ : syracuseStep 112939 = 169409) B169409
theorem B112951 : Blo 111784 112951 := bstep (se 1 (by rfl) ⟨84713, by rfl⟩ : syracuseStep 112951 = 169427) B169427
theorem B112971 : Blo 111784 112971 := bstep (se 1 (by rfl) ⟨84728, by rfl⟩ : syracuseStep 112971 = 169457) B169457
theorem B145739 : Blo 111784 145739 := bstep (se 1 (by rfl) ⟨109304, by rfl⟩ : syracuseStep 145739 = 218609) B218609
theorem B112983 : Blo 111784 112983 := bstep (se 1 (by rfl) ⟨84737, by rfl⟩ : syracuseStep 112983 = 169475) B169475
theorem B113003 : Blo 111784 113003 := bstep (se 1 (by rfl) ⟨84752, by rfl⟩ : syracuseStep 113003 = 169505) B169505
theorem B113015 : Blo 111784 113015 := bstep (se 1 (by rfl) ⟨84761, by rfl⟩ : syracuseStep 113015 = 169523) B169523
theorem B113035 : Blo 111784 113035 := bstep (se 1 (by rfl) ⟨84776, by rfl⟩ : syracuseStep 113035 = 169553) B169553
theorem B113047 : Blo 111784 113047 := bstep (se 1 (by rfl) ⟨84785, by rfl⟩ : syracuseStep 113047 = 169571) B169571
theorem B113067 : Blo 111784 113067 := bstep (se 1 (by rfl) ⟨84800, by rfl⟩ : syracuseStep 113067 = 169601) B169601
theorem B1325489 : Blo 111784 1325489 := bstep (se 2 (by rfl) ⟨497058, by rfl⟩ : syracuseStep 1325489 = 994117) B994117
theorem B113079 : Blo 111784 113079 := bstep (se 1 (by rfl) ⟨84809, by rfl⟩ : syracuseStep 113079 = 169619) B169619
theorem B113099 : Blo 111784 113099 := bstep (se 1 (by rfl) ⟨84824, by rfl⟩ : syracuseStep 113099 = 169649) B169649
theorem B113111 : Blo 111784 113111 := bstep (se 1 (by rfl) ⟨84833, by rfl⟩ : syracuseStep 113111 = 169667) B169667
theorem B113131 : Blo 111784 113131 := bstep (se 1 (by rfl) ⟨84848, by rfl⟩ : syracuseStep 113131 = 169697) B169697
theorem B113143 : Blo 111784 113143 := bstep (se 1 (by rfl) ⟨84857, by rfl⟩ : syracuseStep 113143 = 169715) B169715
theorem B113163 : Blo 111784 113163 := bstep (se 1 (by rfl) ⟨84872, by rfl⟩ : syracuseStep 113163 = 169745) B169745
theorem B113175 : Blo 111784 113175 := bstep (se 1 (by rfl) ⟨84881, by rfl⟩ : syracuseStep 113175 = 169763) B169763
theorem B277015 : Blo 111784 277015 := bstep (se 1 (by rfl) ⟨207761, by rfl⟩ : syracuseStep 277015 = 415523) B415523
theorem B113195 : Blo 111784 113195 := bstep (se 1 (by rfl) ⟨84896, by rfl⟩ : syracuseStep 113195 = 169793) B169793
theorem B113207 : Blo 111784 113207 := bstep (se 1 (by rfl) ⟨84905, by rfl⟩ : syracuseStep 113207 = 169811) B169811
theorem B113227 : Blo 111784 113227 := bstep (se 1 (by rfl) ⟨84920, by rfl⟩ : syracuseStep 113227 = 169841) B169841
theorem B309835 : Blo 111784 309835 := bstep (se 1 (by rfl) ⟨232376, by rfl⟩ : syracuseStep 309835 = 464753) B464753
theorem B113239 : Blo 111784 113239 := bstep (se 1 (by rfl) ⟨84929, by rfl⟩ : syracuseStep 113239 = 169859) B169859
theorem B113259 : Blo 111784 113259 := bstep (se 1 (by rfl) ⟨84944, by rfl⟩ : syracuseStep 113259 = 169889) B169889
theorem B113271 : Blo 111784 113271 := bstep (se 1 (by rfl) ⟨84953, by rfl⟩ : syracuseStep 113271 = 169907) B169907
theorem B113291 : Blo 111784 113291 := bstep (se 1 (by rfl) ⟨84968, by rfl⟩ : syracuseStep 113291 = 169937) B169937
theorem B113303 : Blo 111784 113303 := bstep (se 1 (by rfl) ⟨84977, by rfl⟩ : syracuseStep 113303 = 169955) B169955
theorem B113323 : Blo 111784 113323 := bstep (se 1 (by rfl) ⟨84992, by rfl⟩ : syracuseStep 113323 = 169985) B169985
theorem B113335 : Blo 111784 113335 := bstep (se 1 (by rfl) ⟨85001, by rfl⟩ : syracuseStep 113335 = 170003) B170003
theorem B113355 : Blo 111784 113355 := bstep (se 1 (by rfl) ⟨85016, by rfl⟩ : syracuseStep 113355 = 170033) B170033
theorem B113367 : Blo 111784 113367 := bstep (se 1 (by rfl) ⟨85025, by rfl⟩ : syracuseStep 113367 = 170051) B170051
theorem B113387 : Blo 111784 113387 := bstep (se 1 (by rfl) ⟨85040, by rfl⟩ : syracuseStep 113387 = 170081) B170081
theorem B113399 : Blo 111784 113399 := bstep (se 1 (by rfl) ⟨85049, by rfl⟩ : syracuseStep 113399 = 170099) B170099
theorem B113419 : Blo 111784 113419 := bstep (se 1 (by rfl) ⟨85064, by rfl⟩ : syracuseStep 113419 = 170129) B170129
theorem B604945 : Blo 111784 604945 := bstep (se 2 (by rfl) ⟨226854, by rfl⟩ : syracuseStep 604945 = 453709) B453709
theorem B113431 : Blo 111784 113431 := bstep (se 1 (by rfl) ⟨85073, by rfl⟩ : syracuseStep 113431 = 170147) B170147
theorem B113451 : Blo 111784 113451 := bstep (se 1 (by rfl) ⟨85088, by rfl⟩ : syracuseStep 113451 = 170177) B170177
theorem B113463 : Blo 111784 113463 := bstep (se 1 (by rfl) ⟨85097, by rfl⟩ : syracuseStep 113463 = 170195) B170195
theorem B113483 : Blo 111784 113483 := bstep (se 1 (by rfl) ⟨85112, by rfl⟩ : syracuseStep 113483 = 170225) B170225
theorem B113495 : Blo 111784 113495 := bstep (se 1 (by rfl) ⟨85121, by rfl⟩ : syracuseStep 113495 = 170243) B170243
theorem B113515 : Blo 111784 113515 := bstep (se 1 (by rfl) ⟨85136, by rfl⟩ : syracuseStep 113515 = 170273) B170273
theorem B244595 : Blo 111784 244595 := bstep (se 1 (by rfl) ⟨183446, by rfl⟩ : syracuseStep 244595 = 366893) B366893
theorem B113527 : Blo 111784 113527 := bstep (se 1 (by rfl) ⟨85145, by rfl⟩ : syracuseStep 113527 = 170291) B170291
theorem B113547 : Blo 111784 113547 := bstep (se 1 (by rfl) ⟨85160, by rfl⟩ : syracuseStep 113547 = 170321) B170321
theorem B179095 : Blo 111784 179095 := bstep (se 1 (by rfl) ⟨134321, by rfl⟩ : syracuseStep 179095 = 268643) B268643
theorem B113559 : Blo 111784 113559 := bstep (se 1 (by rfl) ⟨85169, by rfl⟩ : syracuseStep 113559 = 170339) B170339
theorem B113579 : Blo 111784 113579 := bstep (se 1 (by rfl) ⟨85184, by rfl⟩ : syracuseStep 113579 = 170369) B170369
theorem B113591 : Blo 111784 113591 := bstep (se 1 (by rfl) ⟨85193, by rfl⟩ : syracuseStep 113591 = 170387) B170387
theorem B179147 : Blo 111784 179147 := bstep (se 1 (by rfl) ⟨134360, by rfl⟩ : syracuseStep 179147 = 268721) B268721
theorem B113611 : Blo 111784 113611 := bstep (se 1 (by rfl) ⟨85208, by rfl⟩ : syracuseStep 113611 = 170417) B170417
theorem B113623 : Blo 111784 113623 := bstep (se 1 (by rfl) ⟨85217, by rfl⟩ : syracuseStep 113623 = 170435) B170435
theorem B113643 : Blo 111784 113643 := bstep (se 1 (by rfl) ⟨85232, by rfl⟩ : syracuseStep 113643 = 170465) B170465
theorem B113655 : Blo 111784 113655 := bstep (se 1 (by rfl) ⟨85241, by rfl⟩ : syracuseStep 113655 = 170483) B170483
theorem B113675 : Blo 111784 113675 := bstep (se 1 (by rfl) ⟨85256, by rfl⟩ : syracuseStep 113675 = 170513) B170513
theorem B146443 : Blo 111784 146443 := bstep (se 1 (by rfl) ⟨109832, by rfl⟩ : syracuseStep 146443 = 219665) B219665
theorem B113687 : Blo 111784 113687 := bstep (se 1 (by rfl) ⟨85265, by rfl⟩ : syracuseStep 113687 = 170531) B170531
theorem B113707 : Blo 111784 113707 := bstep (se 1 (by rfl) ⟨85280, by rfl⟩ : syracuseStep 113707 = 170561) B170561
theorem B113719 : Blo 111784 113719 := bstep (se 1 (by rfl) ⟨85289, by rfl⟩ : syracuseStep 113719 = 170579) B170579
theorem B179275 : Blo 111784 179275 := bstep (se 1 (by rfl) ⟨134456, by rfl⟩ : syracuseStep 179275 = 268913) B268913
theorem B113739 : Blo 111784 113739 := bstep (se 1 (by rfl) ⟨85304, by rfl⟩ : syracuseStep 113739 = 170609) B170609
theorem B113751 : Blo 111784 113751 := bstep (se 1 (by rfl) ⟨85313, by rfl⟩ : syracuseStep 113751 = 170627) B170627
theorem B113771 : Blo 111784 113771 := bstep (se 1 (by rfl) ⟨85328, by rfl⟩ : syracuseStep 113771 = 170657) B170657
theorem B113783 : Blo 111784 113783 := bstep (se 1 (by rfl) ⟨85337, by rfl⟩ : syracuseStep 113783 = 170675) B170675
theorem B113803 : Blo 111784 113803 := bstep (se 1 (by rfl) ⟨85352, by rfl⟩ : syracuseStep 113803 = 170705) B170705
theorem B113815 : Blo 111784 113815 := bstep (se 1 (by rfl) ⟨85361, by rfl⟩ : syracuseStep 113815 = 170723) B170723
theorem B113835 : Blo 111784 113835 := bstep (se 1 (by rfl) ⟨85376, by rfl⟩ : syracuseStep 113835 = 170753) B170753
theorem B113847 : Blo 111784 113847 := bstep (se 1 (by rfl) ⟨85385, by rfl⟩ : syracuseStep 113847 = 170771) B170771
theorem B113867 : Blo 111784 113867 := bstep (se 1 (by rfl) ⟨85400, by rfl⟩ : syracuseStep 113867 = 170801) B170801
theorem B113879 : Blo 111784 113879 := bstep (se 1 (by rfl) ⟨85409, by rfl⟩ : syracuseStep 113879 = 170819) B170819
theorem B343261 : Blo 111784 343261 := bstep (se 3 (by rfl) ⟨64361, by rfl⟩ : syracuseStep 343261 = 128723) B128723
theorem B113899 : Blo 111784 113899 := bstep (se 1 (by rfl) ⟨85424, by rfl⟩ : syracuseStep 113899 = 170849) B170849
theorem B113911 : Blo 111784 113911 := bstep (se 1 (by rfl) ⟨85433, by rfl⟩ : syracuseStep 113911 = 170867) B170867
theorem B113931 : Blo 111784 113931 := bstep (se 1 (by rfl) ⟨85448, by rfl⟩ : syracuseStep 113931 = 170897) B170897
theorem B113943 : Blo 111784 113943 := bstep (se 1 (by rfl) ⟨85457, by rfl⟩ : syracuseStep 113943 = 170915) B170915
theorem B113963 : Blo 111784 113963 := bstep (se 1 (by rfl) ⟨85472, by rfl⟩ : syracuseStep 113963 = 170945) B170945
theorem B113975 : Blo 111784 113975 := bstep (se 1 (by rfl) ⟨85481, by rfl⟩ : syracuseStep 113975 = 170963) B170963
theorem B113995 : Blo 111784 113995 := bstep (se 1 (by rfl) ⟨85496, by rfl⟩ : syracuseStep 113995 = 170993) B170993
theorem B114007 : Blo 111784 114007 := bstep (se 1 (by rfl) ⟨85505, by rfl⟩ : syracuseStep 114007 = 171011) B171011
theorem B245081 : Blo 111784 245081 := bstep (se 2 (by rfl) ⟨91905, by rfl⟩ : syracuseStep 245081 = 183811) B183811
theorem B114027 : Blo 111784 114027 := bstep (se 1 (by rfl) ⟨85520, by rfl⟩ : syracuseStep 114027 = 171041) B171041
theorem B114039 : Blo 111784 114039 := bstep (se 1 (by rfl) ⟨85529, by rfl⟩ : syracuseStep 114039 = 171059) B171059
theorem B114059 : Blo 111784 114059 := bstep (se 1 (by rfl) ⟨85544, by rfl⟩ : syracuseStep 114059 = 171089) B171089
theorem B212375 : Blo 111784 212375 := bstep (se 1 (by rfl) ⟨159281, by rfl⟩ : syracuseStep 212375 = 318563) B318563
theorem B114071 : Blo 111784 114071 := bstep (se 1 (by rfl) ⟨85553, by rfl⟩ : syracuseStep 114071 = 171107) B171107
theorem B114091 : Blo 111784 114091 := bstep (se 1 (by rfl) ⟨85568, by rfl⟩ : syracuseStep 114091 = 171137) B171137
theorem B114103 : Blo 111784 114103 := bstep (se 1 (by rfl) ⟨85577, by rfl⟩ : syracuseStep 114103 = 171155) B171155
theorem B179659 : Blo 111784 179659 := bstep (se 1 (by rfl) ⟨134744, by rfl⟩ : syracuseStep 179659 = 269489) B269489
theorem B114123 : Blo 111784 114123 := bstep (se 1 (by rfl) ⟨85592, by rfl⟩ : syracuseStep 114123 = 171185) B171185
theorem B114135 : Blo 111784 114135 := bstep (se 1 (by rfl) ⟨85601, by rfl⟩ : syracuseStep 114135 = 171203) B171203
theorem B605657 : Blo 111784 605657 := bstep (se 2 (by rfl) ⟨227121, by rfl⟩ : syracuseStep 605657 = 454243) B454243
theorem B114155 : Blo 111784 114155 := bstep (se 1 (by rfl) ⟨85616, by rfl⟩ : syracuseStep 114155 = 171233) B171233
theorem B114167 : Blo 111784 114167 := bstep (se 1 (by rfl) ⟨85625, by rfl⟩ : syracuseStep 114167 = 171251) B171251
theorem B114187 : Blo 111784 114187 := bstep (se 1 (by rfl) ⟨85640, by rfl⟩ : syracuseStep 114187 = 171281) B171281
theorem B114199 : Blo 111784 114199 := bstep (se 1 (by rfl) ⟨85649, by rfl⟩ : syracuseStep 114199 = 171299) B171299
theorem B114219 : Blo 111784 114219 := bstep (se 1 (by rfl) ⟨85664, by rfl⟩ : syracuseStep 114219 = 171329) B171329
theorem B114231 : Blo 111784 114231 := bstep (se 1 (by rfl) ⟨85673, by rfl⟩ : syracuseStep 114231 = 171347) B171347
theorem B572993 : Blo 111784 572993 := bstep (se 2 (by rfl) ⟨214872, by rfl⟩ : syracuseStep 572993 = 429745) B429745
theorem B114251 : Blo 111784 114251 := bstep (se 1 (by rfl) ⟨85688, by rfl⟩ : syracuseStep 114251 = 171377) B171377
theorem B114263 : Blo 111784 114263 := bstep (se 1 (by rfl) ⟨85697, by rfl⟩ : syracuseStep 114263 = 171395) B171395
theorem B310873 : Blo 111784 310873 := bstep (se 2 (by rfl) ⟨116577, by rfl⟩ : syracuseStep 310873 = 233155) B233155
theorem B114283 : Blo 111784 114283 := bstep (se 1 (by rfl) ⟨85712, by rfl⟩ : syracuseStep 114283 = 171425) B171425
theorem B114295 : Blo 111784 114295 := bstep (se 1 (by rfl) ⟨85721, by rfl⟩ : syracuseStep 114295 = 171443) B171443
theorem B114315 : Blo 111784 114315 := bstep (se 1 (by rfl) ⟨85736, by rfl⟩ : syracuseStep 114315 = 171473) B171473
theorem B114327 : Blo 111784 114327 := bstep (se 1 (by rfl) ⟨85745, by rfl⟩ : syracuseStep 114327 = 171491) B171491
theorem B114347 : Blo 111784 114347 := bstep (se 1 (by rfl) ⟨85760, by rfl⟩ : syracuseStep 114347 = 171521) B171521
theorem B114359 : Blo 111784 114359 := bstep (se 1 (by rfl) ⟨85769, by rfl⟩ : syracuseStep 114359 = 171539) B171539
theorem B179915 : Blo 111784 179915 := bstep (se 1 (by rfl) ⟨134936, by rfl⟩ : syracuseStep 179915 = 269873) B269873
theorem B114379 : Blo 111784 114379 := bstep (se 1 (by rfl) ⟨85784, by rfl⟩ : syracuseStep 114379 = 171569) B171569
theorem B114391 : Blo 111784 114391 := bstep (se 1 (by rfl) ⟨85793, by rfl⟩ : syracuseStep 114391 = 171587) B171587
theorem B114411 : Blo 111784 114411 := bstep (se 1 (by rfl) ⟨85808, by rfl⟩ : syracuseStep 114411 = 171617) B171617
theorem B114423 : Blo 111784 114423 := bstep (se 1 (by rfl) ⟨85817, by rfl⟩ : syracuseStep 114423 = 171635) B171635
theorem B114443 : Blo 111784 114443 := bstep (se 1 (by rfl) ⟨85832, by rfl⟩ : syracuseStep 114443 = 171665) B171665
theorem B114455 : Blo 111784 114455 := bstep (se 1 (by rfl) ⟨85841, by rfl⟩ : syracuseStep 114455 = 171683) B171683
theorem B114475 : Blo 111784 114475 := bstep (se 1 (by rfl) ⟨85856, by rfl⟩ : syracuseStep 114475 = 171713) B171713
theorem B638765 : Blo 111784 638765 := bstep (se 3 (by rfl) ⟨119768, by rfl⟩ : syracuseStep 638765 = 239537) B239537
theorem B114487 : Blo 111784 114487 := bstep (se 1 (by rfl) ⟨85865, by rfl⟩ : syracuseStep 114487 = 171731) B171731
theorem B114507 : Blo 111784 114507 := bstep (se 1 (by rfl) ⟨85880, by rfl⟩ : syracuseStep 114507 = 171761) B171761
theorem B114519 : Blo 111784 114519 := bstep (se 1 (by rfl) ⟨85889, by rfl⟩ : syracuseStep 114519 = 171779) B171779
theorem B114539 : Blo 111784 114539 := bstep (se 1 (by rfl) ⟨85904, by rfl⟩ : syracuseStep 114539 = 171809) B171809
theorem B114551 : Blo 111784 114551 := bstep (se 1 (by rfl) ⟨85913, by rfl⟩ : syracuseStep 114551 = 171827) B171827
theorem B114571 : Blo 111784 114571 := bstep (se 1 (by rfl) ⟨85928, by rfl⟩ : syracuseStep 114571 = 171857) B171857
theorem B114583 : Blo 111784 114583 := bstep (se 1 (by rfl) ⟨85937, by rfl⟩ : syracuseStep 114583 = 171875) B171875
theorem B114603 : Blo 111784 114603 := bstep (se 1 (by rfl) ⟨85952, by rfl⟩ : syracuseStep 114603 = 171905) B171905
theorem B311219 : Blo 111784 311219 := bstep (se 1 (by rfl) ⟨233414, by rfl⟩ : syracuseStep 311219 = 466829) B466829
theorem B114615 : Blo 111784 114615 := bstep (se 1 (by rfl) ⟨85961, by rfl⟩ : syracuseStep 114615 = 171923) B171923
theorem B114635 : Blo 111784 114635 := bstep (se 1 (by rfl) ⟨85976, by rfl⟩ : syracuseStep 114635 = 171953) B171953
theorem B114647 : Blo 111784 114647 := bstep (se 1 (by rfl) ⟨85985, by rfl⟩ : syracuseStep 114647 = 171971) B171971
theorem B114667 : Blo 111784 114667 := bstep (se 1 (by rfl) ⟨86000, by rfl⟩ : syracuseStep 114667 = 172001) B172001
theorem B114679 : Blo 111784 114679 := bstep (se 1 (by rfl) ⟨86009, by rfl⟩ : syracuseStep 114679 = 172019) B172019
theorem B114699 : Blo 111784 114699 := bstep (se 1 (by rfl) ⟨86024, by rfl⟩ : syracuseStep 114699 = 172049) B172049
theorem B114711 : Blo 111784 114711 := bstep (se 1 (by rfl) ⟨86033, by rfl⟩ : syracuseStep 114711 = 172067) B172067
theorem B966691 : Blo 111784 966691 := bstep (se 1 (by rfl) ⟨725018, by rfl⟩ : syracuseStep 966691 = 1450037) B1450037
theorem B114731 : Blo 111784 114731 := bstep (se 1 (by rfl) ⟨86048, by rfl⟩ : syracuseStep 114731 = 172097) B172097
theorem B213043 : Blo 111784 213043 := bstep (se 1 (by rfl) ⟨159782, by rfl⟩ : syracuseStep 213043 = 319565) B319565
theorem B114743 : Blo 111784 114743 := bstep (se 1 (by rfl) ⟨86057, by rfl⟩ : syracuseStep 114743 = 172115) B172115
theorem B245825 : Blo 111784 245825 := bstep (se 2 (by rfl) ⟨92184, by rfl⟩ : syracuseStep 245825 = 184369) B184369
theorem B114763 : Blo 111784 114763 := bstep (se 1 (by rfl) ⟨86072, by rfl⟩ : syracuseStep 114763 = 172145) B172145
theorem B114775 : Blo 111784 114775 := bstep (se 1 (by rfl) ⟨86081, by rfl⟩ : syracuseStep 114775 = 172163) B172163
theorem B114795 : Blo 111784 114795 := bstep (se 1 (by rfl) ⟨86096, by rfl⟩ : syracuseStep 114795 = 172193) B172193
theorem B114807 : Blo 111784 114807 := bstep (se 1 (by rfl) ⟨86105, by rfl⟩ : syracuseStep 114807 = 172211) B172211
theorem B114827 : Blo 111784 114827 := bstep (se 1 (by rfl) ⟨86120, by rfl⟩ : syracuseStep 114827 = 172241) B172241
theorem B114839 : Blo 111784 114839 := bstep (se 1 (by rfl) ⟨86129, by rfl⟩ : syracuseStep 114839 = 172259) B172259
theorem B180377 : Blo 111784 180377 := bstep (se 2 (by rfl) ⟨67641, by rfl⟩ : syracuseStep 180377 = 135283) B135283
theorem B114859 : Blo 111784 114859 := bstep (se 1 (by rfl) ⟨86144, by rfl⟩ : syracuseStep 114859 = 172289) B172289
theorem B114871 : Blo 111784 114871 := bstep (se 1 (by rfl) ⟨86153, by rfl⟩ : syracuseStep 114871 = 172307) B172307
theorem B114891 : Blo 111784 114891 := bstep (se 1 (by rfl) ⟨86168, by rfl⟩ : syracuseStep 114891 = 172337) B172337
theorem B114903 : Blo 111784 114903 := bstep (se 1 (by rfl) ⟨86177, by rfl⟩ : syracuseStep 114903 = 172355) B172355
theorem B114923 : Blo 111784 114923 := bstep (se 1 (by rfl) ⟨86192, by rfl⟩ : syracuseStep 114923 = 172385) B172385
theorem B114935 : Blo 111784 114935 := bstep (se 1 (by rfl) ⟨86201, by rfl⟩ : syracuseStep 114935 = 172403) B172403
theorem B114955 : Blo 111784 114955 := bstep (se 1 (by rfl) ⟨86216, by rfl⟩ : syracuseStep 114955 = 172433) B172433
theorem B114967 : Blo 111784 114967 := bstep (se 1 (by rfl) ⟨86225, by rfl⟩ : syracuseStep 114967 = 172451) B172451
theorem B180505 : Blo 111784 180505 := bstep (se 2 (by rfl) ⟨67689, by rfl⟩ : syracuseStep 180505 = 135379) B135379
theorem B114987 : Blo 111784 114987 := bstep (se 1 (by rfl) ⟨86240, by rfl⟩ : syracuseStep 114987 = 172481) B172481
theorem B114999 : Blo 111784 114999 := bstep (se 1 (by rfl) ⟨86249, by rfl⟩ : syracuseStep 114999 = 172499) B172499
theorem B115019 : Blo 111784 115019 := bstep (se 1 (by rfl) ⟨86264, by rfl⟩ : syracuseStep 115019 = 172529) B172529
theorem B115031 : Blo 111784 115031 := bstep (se 1 (by rfl) ⟨86273, by rfl⟩ : syracuseStep 115031 = 172547) B172547
theorem B115051 : Blo 111784 115051 := bstep (se 1 (by rfl) ⟨86288, by rfl⟩ : syracuseStep 115051 = 172577) B172577
theorem B115063 : Blo 111784 115063 := bstep (se 1 (by rfl) ⟨86297, by rfl⟩ : syracuseStep 115063 = 172595) B172595
theorem B115083 : Blo 111784 115083 := bstep (se 1 (by rfl) ⟨86312, by rfl⟩ : syracuseStep 115083 = 172625) B172625
theorem B115095 : Blo 111784 115095 := bstep (se 1 (by rfl) ⟨86321, by rfl⟩ : syracuseStep 115095 = 172643) B172643
theorem B115115 : Blo 111784 115115 := bstep (se 1 (by rfl) ⟨86336, by rfl⟩ : syracuseStep 115115 = 172673) B172673
theorem B115127 : Blo 111784 115127 := bstep (se 1 (by rfl) ⟨86345, by rfl⟩ : syracuseStep 115127 = 172691) B172691
theorem B115147 : Blo 111784 115147 := bstep (se 1 (by rfl) ⟨86360, by rfl⟩ : syracuseStep 115147 = 172721) B172721
theorem B115159 : Blo 111784 115159 := bstep (se 1 (by rfl) ⟨86369, by rfl⟩ : syracuseStep 115159 = 172739) B172739
theorem B115179 : Blo 111784 115179 := bstep (se 1 (by rfl) ⟨86384, by rfl⟩ : syracuseStep 115179 = 172769) B172769
theorem B213491 : Blo 111784 213491 := bstep (se 1 (by rfl) ⟨160118, by rfl⟩ : syracuseStep 213491 = 320237) B320237
theorem B115191 : Blo 111784 115191 := bstep (se 1 (by rfl) ⟨86393, by rfl⟩ : syracuseStep 115191 = 172787) B172787
theorem B115211 : Blo 111784 115211 := bstep (se 1 (by rfl) ⟨86408, by rfl⟩ : syracuseStep 115211 = 172817) B172817
theorem B115223 : Blo 111784 115223 := bstep (se 1 (by rfl) ⟨86417, by rfl⟩ : syracuseStep 115223 = 172835) B172835
theorem B213529 : Blo 111784 213529 := bstep (se 2 (by rfl) ⟨80073, by rfl⟩ : syracuseStep 213529 = 160147) B160147
theorem B115243 : Blo 111784 115243 := bstep (se 1 (by rfl) ⟨86432, by rfl⟩ : syracuseStep 115243 = 172865) B172865
theorem B115255 : Blo 111784 115255 := bstep (se 1 (by rfl) ⟨86441, by rfl⟩ : syracuseStep 115255 = 172883) B172883
theorem B115275 : Blo 111784 115275 := bstep (se 1 (by rfl) ⟨86456, by rfl⟩ : syracuseStep 115275 = 172913) B172913
theorem B115287 : Blo 111784 115287 := bstep (se 1 (by rfl) ⟨86465, by rfl⟩ : syracuseStep 115287 = 172931) B172931
theorem B115307 : Blo 111784 115307 := bstep (se 1 (by rfl) ⟨86480, by rfl⟩ : syracuseStep 115307 = 172961) B172961
theorem B115319 : Blo 111784 115319 := bstep (se 1 (by rfl) ⟨86489, by rfl⟩ : syracuseStep 115319 = 172979) B172979
theorem B115339 : Blo 111784 115339 := bstep (se 1 (by rfl) ⟨86504, by rfl⟩ : syracuseStep 115339 = 173009) B173009
theorem B115351 : Blo 111784 115351 := bstep (se 1 (by rfl) ⟨86513, by rfl⟩ : syracuseStep 115351 = 173027) B173027
theorem B115371 : Blo 111784 115371 := bstep (se 1 (by rfl) ⟨86528, by rfl⟩ : syracuseStep 115371 = 173057) B173057
theorem B115383 : Blo 111784 115383 := bstep (se 1 (by rfl) ⟨86537, by rfl⟩ : syracuseStep 115383 = 173075) B173075
theorem B115403 : Blo 111784 115403 := bstep (se 1 (by rfl) ⟨86552, by rfl⟩ : syracuseStep 115403 = 173105) B173105
theorem B115415 : Blo 111784 115415 := bstep (se 1 (by rfl) ⟨86561, by rfl⟩ : syracuseStep 115415 = 173123) B173123
theorem B115435 : Blo 111784 115435 := bstep (se 1 (by rfl) ⟨86576, by rfl⟩ : syracuseStep 115435 = 173153) B173153
theorem B115447 : Blo 111784 115447 := bstep (se 1 (by rfl) ⟨86585, by rfl⟩ : syracuseStep 115447 = 173171) B173171
theorem B115467 : Blo 111784 115467 := bstep (se 1 (by rfl) ⟨86600, by rfl⟩ : syracuseStep 115467 = 173201) B173201
theorem B115479 : Blo 111784 115479 := bstep (se 1 (by rfl) ⟨86609, by rfl⟩ : syracuseStep 115479 = 173219) B173219
theorem B115499 : Blo 111784 115499 := bstep (se 1 (by rfl) ⟨86624, by rfl⟩ : syracuseStep 115499 = 173249) B173249
theorem B115511 : Blo 111784 115511 := bstep (se 1 (by rfl) ⟨86633, by rfl⟩ : syracuseStep 115511 = 173267) B173267
theorem B377675 : Blo 111784 377675 := bstep (se 1 (by rfl) ⟨283256, by rfl⟩ : syracuseStep 377675 = 566513) B566513
theorem B115531 : Blo 111784 115531 := bstep (se 1 (by rfl) ⟨86648, by rfl⟩ : syracuseStep 115531 = 173297) B173297
theorem B115543 : Blo 111784 115543 := bstep (se 1 (by rfl) ⟨86657, by rfl⟩ : syracuseStep 115543 = 173315) B173315
theorem B115563 : Blo 111784 115563 := bstep (se 1 (by rfl) ⟨86672, by rfl⟩ : syracuseStep 115563 = 173345) B173345
theorem B115575 : Blo 111784 115575 := bstep (se 1 (by rfl) ⟨86681, by rfl⟩ : syracuseStep 115575 = 173363) B173363
theorem B115595 : Blo 111784 115595 := bstep (se 1 (by rfl) ⟨86696, by rfl⟩ : syracuseStep 115595 = 173393) B173393
theorem B115607 : Blo 111784 115607 := bstep (se 1 (by rfl) ⟨86705, by rfl⟩ : syracuseStep 115607 = 173411) B173411
theorem B115627 : Blo 111784 115627 := bstep (se 1 (by rfl) ⟨86720, by rfl⟩ : syracuseStep 115627 = 173441) B173441
theorem B115639 : Blo 111784 115639 := bstep (se 1 (by rfl) ⟨86729, by rfl⟩ : syracuseStep 115639 = 173459) B173459
theorem B246721 : Blo 111784 246721 := bstep (se 2 (by rfl) ⟨92520, by rfl⟩ : syracuseStep 246721 = 185041) B185041
theorem B115659 : Blo 111784 115659 := bstep (se 1 (by rfl) ⟨86744, by rfl⟩ : syracuseStep 115659 = 173489) B173489
theorem B115671 : Blo 111784 115671 := bstep (se 1 (by rfl) ⟨86753, by rfl⟩ : syracuseStep 115671 = 173507) B173507
theorem B213977 : Blo 111784 213977 := bstep (se 2 (by rfl) ⟨80241, by rfl⟩ : syracuseStep 213977 = 160483) B160483
theorem B312281 : Blo 111784 312281 := bstep (se 2 (by rfl) ⟨117105, by rfl⟩ : syracuseStep 312281 = 234211) B234211
theorem B115691 : Blo 111784 115691 := bstep (se 1 (by rfl) ⟨86768, by rfl⟩ : syracuseStep 115691 = 173537) B173537
theorem B115703 : Blo 111784 115703 := bstep (se 1 (by rfl) ⟨86777, by rfl⟩ : syracuseStep 115703 = 173555) B173555
theorem B115723 : Blo 111784 115723 := bstep (se 1 (by rfl) ⟨86792, by rfl⟩ : syracuseStep 115723 = 173585) B173585
theorem B115735 : Blo 111784 115735 := bstep (se 1 (by rfl) ⟨86801, by rfl⟩ : syracuseStep 115735 = 173603) B173603
theorem B115755 : Blo 111784 115755 := bstep (se 1 (by rfl) ⟨86816, by rfl⟩ : syracuseStep 115755 = 173633) B173633
theorem B115767 : Blo 111784 115767 := bstep (se 1 (by rfl) ⟨86825, by rfl⟩ : syracuseStep 115767 = 173651) B173651
theorem B377945 : Blo 111784 377945 := bstep (se 2 (by rfl) ⟨141729, by rfl⟩ : syracuseStep 377945 = 283459) B283459
theorem B247063 : Blo 111784 247063 := bstep (se 1 (by rfl) ⟨185297, by rfl⟩ : syracuseStep 247063 = 370595) B370595
theorem B574937 : Blo 111784 574937 := bstep (se 2 (by rfl) ⟨215601, by rfl⟩ : syracuseStep 574937 = 431203) B431203
theorem B214721 : Blo 111784 214721 := bstep (se 2 (by rfl) ⟨80520, by rfl⟩ : syracuseStep 214721 = 161041) B161041
theorem B378647 : Blo 111784 378647 := bstep (se 1 (by rfl) ⟨283985, by rfl⟩ : syracuseStep 378647 = 567971) B567971
theorem B214987 : Blo 111784 214987 := bstep (se 1 (by rfl) ⟨161240, by rfl⟩ : syracuseStep 214987 = 322481) B322481
theorem B641155 : Blo 111784 641155 := bstep (se 1 (by rfl) ⟨480866, by rfl⟩ : syracuseStep 641155 = 961733) B961733
theorem B739459 : Blo 111784 739459 := bstep (se 1 (by rfl) ⟨554594, by rfl⟩ : syracuseStep 739459 = 1109189) B1109189
theorem B1755377 : Blo 111784 1755377 := bstep (se 2 (by rfl) ⟨658266, by rfl⟩ : syracuseStep 1755377 = 1316533) B1316533
theorem B739601 : Blo 111784 739601 := bstep (se 2 (by rfl) ⟨277350, by rfl⟩ : syracuseStep 739601 = 554701) B554701
theorem B379187 : Blo 111784 379187 := bstep (se 1 (by rfl) ⟨284390, by rfl⟩ : syracuseStep 379187 = 568781) B568781
theorem B215435 : Blo 111784 215435 := bstep (se 1 (by rfl) ⟨161576, by rfl⟩ : syracuseStep 215435 = 323153) B323153
theorem B444851 : Blo 111784 444851 := bstep (se 1 (by rfl) ⟨333638, by rfl⟩ : syracuseStep 444851 = 667277) B667277
theorem B707033 : Blo 111784 707033 := bstep (se 2 (by rfl) ⟨265137, by rfl⟩ : syracuseStep 707033 = 530275) B530275
theorem B379457 : Blo 111784 379457 := bstep (se 2 (by rfl) ⟨142296, by rfl⟩ : syracuseStep 379457 = 284593) B284593
theorem B215617 : Blo 111784 215617 := bstep (se 2 (by rfl) ⟨80856, by rfl⟩ : syracuseStep 215617 = 161713) B161713
theorem B248651 : Blo 111784 248651 := bstep (se 1 (by rfl) ⟨186488, by rfl⟩ : syracuseStep 248651 = 372977) B372977
theorem B215959 : Blo 111784 215959 := bstep (se 1 (by rfl) ⟨161969, by rfl⟩ : syracuseStep 215959 = 323939) B323939
theorem B543667 : Blo 111784 543667 := bstep (se 1 (by rfl) ⟨407750, by rfl⟩ : syracuseStep 543667 = 815501) B815501
theorem B478169 : Blo 111784 478169 := bstep (se 2 (by rfl) ⟨179313, by rfl⟩ : syracuseStep 478169 = 358627) B358627
theorem B576557 : Blo 111784 576557 := bstep (se 3 (by rfl) ⟨108104, by rfl⟩ : syracuseStep 576557 = 216209) B216209
theorem B642113 : Blo 111784 642113 := bstep (se 2 (by rfl) ⟨240792, by rfl⟩ : syracuseStep 642113 = 481585) B481585
theorem B379997 : Blo 111784 379997 := bstep (se 3 (by rfl) ⟨71249, by rfl⟩ : syracuseStep 379997 = 142499) B142499
theorem B216179 : Blo 111784 216179 := bstep (se 1 (by rfl) ⟨162134, by rfl⟩ : syracuseStep 216179 = 324269) B324269
theorem B806219 : Blo 111784 806219 := bstep (se 1 (by rfl) ⟨604664, by rfl⟩ : syracuseStep 806219 = 1209329) B1209329
theorem B216407 : Blo 111784 216407 := bstep (se 1 (by rfl) ⟨162305, by rfl⟩ : syracuseStep 216407 = 324611) B324611
theorem B3231089 : Blo 111784 3231089 := bstep (se 2 (by rfl) ⟨1211658, by rfl⟩ : syracuseStep 3231089 = 2423317) B2423317
theorem B183703 : Blo 111784 183703 := bstep (se 1 (by rfl) ⟨137777, by rfl⟩ : syracuseStep 183703 = 275555) B275555
theorem B3919373 : Blo 111784 3919373 := bstep (se 3 (by rfl) ⟨734882, by rfl⟩ : syracuseStep 3919373 = 1469765) B1469765
theorem B216665 : Blo 111784 216665 := bstep (se 2 (by rfl) ⟨81249, by rfl⟩ : syracuseStep 216665 = 162499) B162499
theorem B183959 : Blo 111784 183959 := bstep (se 1 (by rfl) ⟨137969, by rfl⟩ : syracuseStep 183959 = 275939) B275939
theorem B872369 : Blo 111784 872369 := bstep (se 2 (by rfl) ⟨327138, by rfl⟩ : syracuseStep 872369 = 654277) B654277
theorem B217075 : Blo 111784 217075 := bstep (se 1 (by rfl) ⟨162806, by rfl⟩ : syracuseStep 217075 = 325613) B325613
theorem B872579 : Blo 111784 872579 := bstep (se 1 (by rfl) ⟨654434, by rfl⟩ : syracuseStep 872579 = 1308869) B1308869
theorem B381131 : Blo 111784 381131 := bstep (se 1 (by rfl) ⟨285848, by rfl⟩ : syracuseStep 381131 = 571697) B571697
theorem B872855 : Blo 111784 872855 := bstep (se 1 (by rfl) ⟨654641, by rfl⟩ : syracuseStep 872855 = 1309283) B1309283
theorem B381401 : Blo 111784 381401 := bstep (se 2 (by rfl) ⟨143025, by rfl⟩ : syracuseStep 381401 = 286051) B286051
theorem B217561 : Blo 111784 217561 := bstep (se 2 (by rfl) ⟨81585, by rfl⟩ : syracuseStep 217561 = 163171) B163171
theorem B119575 : Blo 111784 119575 := bstep (se 1 (by rfl) ⟨89681, by rfl⟩ : syracuseStep 119575 = 179363) B179363
theorem B283571 : Blo 111784 283571 := bstep (se 1 (by rfl) ⟨212678, by rfl⟩ : syracuseStep 283571 = 425357) B425357
theorem B218123 : Blo 111784 218123 := bstep (se 1 (by rfl) ⟨163592, by rfl⟩ : syracuseStep 218123 = 327185) B327185
theorem B382103 : Blo 111784 382103 := bstep (se 1 (by rfl) ⟨286577, by rfl⟩ : syracuseStep 382103 = 573155) B573155
theorem B218305 : Blo 111784 218305 := bstep (se 2 (by rfl) ⟨81864, by rfl⟩ : syracuseStep 218305 = 163729) B163729
theorem B284107 : Blo 111784 284107 := bstep (se 1 (by rfl) ⟨213080, by rfl⟩ : syracuseStep 284107 = 426161) B426161
theorem B284249 : Blo 111784 284249 := bstep (se 2 (by rfl) ⟨106593, by rfl⟩ : syracuseStep 284249 = 213187) B213187
theorem B415363 : Blo 111784 415363 := bstep (se 1 (by rfl) ⟨311522, by rfl⟩ : syracuseStep 415363 = 623045) B623045
theorem B251531 : Blo 111784 251531 := bstep (se 1 (by rfl) ⟨188648, by rfl⟩ : syracuseStep 251531 = 377297) B377297
theorem B382643 : Blo 111784 382643 := bstep (se 1 (by rfl) ⟨286982, by rfl⟩ : syracuseStep 382643 = 573965) B573965
theorem B251585 : Blo 111784 251585 := bstep (se 2 (by rfl) ⟨94344, by rfl⟩ : syracuseStep 251585 = 188689) B188689
theorem B317249 : Blo 111784 317249 := bstep (se 2 (by rfl) ⟨118968, by rfl⟩ : syracuseStep 317249 = 237937) B237937
theorem B120695 : Blo 111784 120695 := bstep (se 1 (by rfl) ⟨90521, by rfl⟩ : syracuseStep 120695 = 181043) B181043
theorem B219019 : Blo 111784 219019 := bstep (se 1 (by rfl) ⟨164264, by rfl⟩ : syracuseStep 219019 = 328529) B328529
theorem B251801 : Blo 111784 251801 := bstep (se 2 (by rfl) ⟨94425, by rfl⟩ : syracuseStep 251801 = 188851) B188851
theorem B382913 : Blo 111784 382913 := bstep (se 2 (by rfl) ⟨143592, by rfl⟩ : syracuseStep 382913 = 287185) B287185
theorem B219095 : Blo 111784 219095 := bstep (se 1 (by rfl) ⟨164321, by rfl⟩ : syracuseStep 219095 = 328643) B328643
theorem B251891 : Blo 111784 251891 := bstep (se 1 (by rfl) ⟨188918, by rfl⟩ : syracuseStep 251891 = 377837) B377837
theorem B251927 : Blo 111784 251927 := bstep (se 1 (by rfl) ⟨188945, by rfl⟩ : syracuseStep 251927 = 377891) B377891
theorem B3299363 : Blo 111784 3299363 := bstep (se 1 (by rfl) ⟨2474522, by rfl⟩ : syracuseStep 3299363 = 4949045) B4949045
theorem B252107 : Blo 111784 252107 := bstep (se 1 (by rfl) ⟨189080, by rfl⟩ : syracuseStep 252107 = 378161) B378161
theorem B252161 : Blo 111784 252161 := bstep (se 2 (by rfl) ⟨94560, by rfl⟩ : syracuseStep 252161 = 189121) B189121
theorem B2873717 : Blo 111784 2873717 := bstep (se 5 (by rfl) ⟨134705, by rfl⟩ : syracuseStep 2873717 = 269411) B269411
theorem B285079 : Blo 111784 285079 := bstep (se 1 (by rfl) ⟨213809, by rfl⟩ : syracuseStep 285079 = 427619) B427619
theorem B252377 : Blo 111784 252377 := bstep (se 2 (by rfl) ⟨94641, by rfl⟩ : syracuseStep 252377 = 189283) B189283
theorem B383453 : Blo 111784 383453 := bstep (se 3 (by rfl) ⟨71897, by rfl⟩ : syracuseStep 383453 = 143795) B143795
theorem B252467 : Blo 111784 252467 := bstep (se 1 (by rfl) ⟨189350, by rfl⟩ : syracuseStep 252467 = 378701) B378701
theorem B252503 : Blo 111784 252503 := bstep (se 1 (by rfl) ⟨189377, by rfl⟩ : syracuseStep 252503 = 378755) B378755
theorem B219763 : Blo 111784 219763 := bstep (se 1 (by rfl) ⟨164822, by rfl⟩ : syracuseStep 219763 = 329645) B329645
theorem B252683 : Blo 111784 252683 := bstep (se 1 (by rfl) ⟨189512, by rfl⟩ : syracuseStep 252683 = 379025) B379025
theorem B154391 : Blo 111784 154391 := bstep (se 1 (by rfl) ⟨115793, by rfl⟩ : syracuseStep 154391 = 231587) B231587
theorem B252737 : Blo 111784 252737 := bstep (se 2 (by rfl) ⟨94776, by rfl⟩ : syracuseStep 252737 = 189553) B189553
theorem B285515 : Blo 111784 285515 := bstep (se 1 (by rfl) ⟨214136, by rfl⟩ : syracuseStep 285515 = 428273) B428273
theorem B580445 : Blo 111784 580445 := bstep (se 3 (by rfl) ⟨108833, by rfl⟩ : syracuseStep 580445 = 217667) B217667
theorem B613271 : Blo 111784 613271 := bstep (se 1 (by rfl) ⟨459953, by rfl⟩ : syracuseStep 613271 = 919907) B919907
theorem B252953 : Blo 111784 252953 := bstep (se 2 (by rfl) ⟨94857, by rfl⟩ : syracuseStep 252953 = 189715) B189715
theorem B253043 : Blo 111784 253043 := bstep (se 1 (by rfl) ⟨189782, by rfl⟩ : syracuseStep 253043 = 379565) B379565
theorem B253079 : Blo 111784 253079 := bstep (se 1 (by rfl) ⟨189809, by rfl⟩ : syracuseStep 253079 = 379619) B379619
theorem B285889 : Blo 111784 285889 := bstep (se 2 (by rfl) ⟨107208, by rfl⟩ : syracuseStep 285889 = 214417) B214417
theorem B482507 : Blo 111784 482507 := bstep (se 1 (by rfl) ⟨361880, by rfl⟩ : syracuseStep 482507 = 723761) B723761
theorem B253259 : Blo 111784 253259 := bstep (se 1 (by rfl) ⟨189944, by rfl⟩ : syracuseStep 253259 = 379889) B379889
theorem B253313 : Blo 111784 253313 := bstep (se 2 (by rfl) ⟨94992, by rfl⟩ : syracuseStep 253313 = 189985) B189985
theorem B384587 : Blo 111784 384587 := bstep (se 1 (by rfl) ⟨288440, by rfl⟩ : syracuseStep 384587 = 576881) B576881
theorem B122455 : Blo 111784 122455 := bstep (se 1 (by rfl) ⟨91841, by rfl⟩ : syracuseStep 122455 = 183683) B183683
theorem B253529 : Blo 111784 253529 := bstep (se 2 (by rfl) ⟨95073, by rfl⟩ : syracuseStep 253529 = 190147) B190147
theorem B253619 : Blo 111784 253619 := bstep (se 1 (by rfl) ⟨190214, by rfl⟩ : syracuseStep 253619 = 380429) B380429
theorem B253655 : Blo 111784 253655 := bstep (se 1 (by rfl) ⟨190241, by rfl⟩ : syracuseStep 253655 = 380483) B380483
theorem B286487 : Blo 111784 286487 := bstep (se 1 (by rfl) ⟨214865, by rfl⟩ : syracuseStep 286487 = 429731) B429731
theorem B646987 : Blo 111784 646987 := bstep (se 1 (by rfl) ⟨485240, by rfl⟩ : syracuseStep 646987 = 970481) B970481
theorem B384857 : Blo 111784 384857 := bstep (se 2 (by rfl) ⟨144321, by rfl⟩ : syracuseStep 384857 = 288643) B288643
theorem B253835 : Blo 111784 253835 := bstep (se 1 (by rfl) ⟨190376, by rfl⟩ : syracuseStep 253835 = 380753) B380753
theorem B253889 : Blo 111784 253889 := bstep (se 2 (by rfl) ⟨95208, by rfl⟩ : syracuseStep 253889 = 190417) B190417
theorem B614465 : Blo 111784 614465 := bstep (se 2 (by rfl) ⟨230424, by rfl⟩ : syracuseStep 614465 = 460849) B460849
theorem B647261 : Blo 111784 647261 := bstep (se 3 (by rfl) ⟨121361, by rfl⟩ : syracuseStep 647261 = 242723) B242723
theorem B254105 : Blo 111784 254105 := bstep (se 2 (by rfl) ⟨95289, by rfl⟩ : syracuseStep 254105 = 190579) B190579
theorem B254195 : Blo 111784 254195 := bstep (se 1 (by rfl) ⟨190646, by rfl⟩ : syracuseStep 254195 = 381293) B381293
theorem B286999 : Blo 111784 286999 := bstep (se 1 (by rfl) ⟨215249, by rfl⟩ : syracuseStep 286999 = 430499) B430499
theorem B254231 : Blo 111784 254231 := bstep (se 1 (by rfl) ⟨190673, by rfl⟩ : syracuseStep 254231 = 381347) B381347
theorem B319895 : Blo 111784 319895 := bstep (se 1 (by rfl) ⟨239921, by rfl⟩ : syracuseStep 319895 = 479843) B479843
theorem B254411 : Blo 111784 254411 := bstep (se 1 (by rfl) ⟨190808, by rfl⟩ : syracuseStep 254411 = 381617) B381617
theorem B254465 : Blo 111784 254465 := bstep (se 2 (by rfl) ⟨95424, by rfl⟩ : syracuseStep 254465 = 190849) B190849
theorem B516611 : Blo 111784 516611 := bstep (se 1 (by rfl) ⟨387458, by rfl⟩ : syracuseStep 516611 = 774917) B774917
theorem B188939 : Blo 111784 188939 := bstep (se 1 (by rfl) ⟨141704, by rfl⟩ : syracuseStep 188939 = 283409) B283409
theorem B385559 : Blo 111784 385559 := bstep (se 1 (by rfl) ⟨289169, by rfl⟩ : syracuseStep 385559 = 578339) B578339
theorem B1663523 : Blo 111784 1663523 := bstep (se 1 (by rfl) ⟨1247642, by rfl⟩ : syracuseStep 1663523 = 2495285) B2495285
theorem B287297 : Blo 111784 287297 := bstep (se 2 (by rfl) ⟨107736, by rfl⟩ : syracuseStep 287297 = 215473) B215473
theorem B615043 : Blo 111784 615043 := bstep (se 1 (by rfl) ⟨461282, by rfl⟩ : syracuseStep 615043 = 922565) B922565
theorem B189067 : Blo 111784 189067 := bstep (se 1 (by rfl) ⟨141800, by rfl⟩ : syracuseStep 189067 = 283601) B283601
theorem B254681 : Blo 111784 254681 := bstep (se 2 (by rfl) ⟨95505, by rfl⟩ : syracuseStep 254681 = 191011) B191011
theorem B189209 : Blo 111784 189209 := bstep (se 2 (by rfl) ⟨70953, by rfl⟩ : syracuseStep 189209 = 141907) B141907
theorem B254771 : Blo 111784 254771 := bstep (se 1 (by rfl) ⟨191078, by rfl⟩ : syracuseStep 254771 = 382157) B382157
theorem B484147 : Blo 111784 484147 := bstep (se 1 (by rfl) ⟨363110, by rfl⟩ : syracuseStep 484147 = 726221) B726221
theorem B254807 : Blo 111784 254807 := bstep (se 1 (by rfl) ⟨191105, by rfl⟩ : syracuseStep 254807 = 382211) B382211
theorem B582551 : Blo 111784 582551 := bstep (se 1 (by rfl) ⟨436913, by rfl⟩ : syracuseStep 582551 = 873827) B873827
theorem B189337 : Blo 111784 189337 := bstep (se 2 (by rfl) ⟨71001, by rfl⟩ : syracuseStep 189337 = 142003) B142003
theorem B1860569 : Blo 111784 1860569 := bstep (se 2 (by rfl) ⟨697713, by rfl⟩ : syracuseStep 1860569 = 1395427) B1395427
theorem B254987 : Blo 111784 254987 := bstep (se 1 (by rfl) ⟨191240, by rfl⟩ : syracuseStep 254987 = 382481) B382481
theorem B386099 : Blo 111784 386099 := bstep (se 1 (by rfl) ⟨289574, by rfl⟩ : syracuseStep 386099 = 579149) B579149
theorem B255041 : Blo 111784 255041 := bstep (se 2 (by rfl) ⟨95640, by rfl⟩ : syracuseStep 255041 = 191281) B191281
theorem B287833 : Blo 111784 287833 := bstep (se 2 (by rfl) ⟨107937, by rfl⟩ : syracuseStep 287833 = 215875) B215875
theorem B255257 : Blo 111784 255257 := bstep (se 2 (by rfl) ⟨95721, by rfl⟩ : syracuseStep 255257 = 191443) B191443
theorem B386369 : Blo 111784 386369 := bstep (se 2 (by rfl) ⟨144888, by rfl⟩ : syracuseStep 386369 = 289777) B289777
theorem B419165 : Blo 111784 419165 := bstep (se 3 (by rfl) ⟨78593, by rfl⟩ : syracuseStep 419165 = 157187) B157187
theorem B255347 : Blo 111784 255347 := bstep (se 1 (by rfl) ⟨191510, by rfl⟩ : syracuseStep 255347 = 383021) B383021
theorem B779651 : Blo 111784 779651 := bstep (se 1 (by rfl) ⟨584738, by rfl⟩ : syracuseStep 779651 = 1169477) B1169477
theorem B255383 : Blo 111784 255383 := bstep (se 1 (by rfl) ⟨191537, by rfl⟩ : syracuseStep 255383 = 383075) B383075
theorem B189911 : Blo 111784 189911 := bstep (se 1 (by rfl) ⟨142433, by rfl⟩ : syracuseStep 189911 = 284867) B284867
theorem B3630563 : Blo 111784 3630563 := bstep (se 1 (by rfl) ⟨2722922, by rfl⟩ : syracuseStep 3630563 = 5445845) B5445845
theorem B1730123 : Blo 111784 1730123 := bstep (se 1 (by rfl) ⟨1297592, by rfl⟩ : syracuseStep 1730123 = 2595185) B2595185
theorem B255563 : Blo 111784 255563 := bstep (se 1 (by rfl) ⟨191672, by rfl⟩ : syracuseStep 255563 = 383345) B383345
theorem B190039 : Blo 111784 190039 := bstep (se 1 (by rfl) ⟨142529, by rfl⟩ : syracuseStep 190039 = 285059) B285059
theorem B255617 : Blo 111784 255617 := bstep (se 2 (by rfl) ⟨95856, by rfl⟩ : syracuseStep 255617 = 191713) B191713
theorem B255833 : Blo 111784 255833 := bstep (se 2 (by rfl) ⟨95937, by rfl⟩ : syracuseStep 255833 = 191875) B191875
theorem B386909 : Blo 111784 386909 := bstep (se 3 (by rfl) ⟨72545, by rfl⟩ : syracuseStep 386909 = 145091) B145091
theorem B255923 : Blo 111784 255923 := bstep (se 1 (by rfl) ⟨191942, by rfl⟩ : syracuseStep 255923 = 383885) B383885
theorem B255959 : Blo 111784 255959 := bstep (se 1 (by rfl) ⟨191969, by rfl⟩ : syracuseStep 255959 = 383939) B383939
theorem B256139 : Blo 111784 256139 := bstep (se 1 (by rfl) ⟨192104, by rfl⟩ : syracuseStep 256139 = 384209) B384209
theorem B288947 : Blo 111784 288947 := bstep (se 1 (by rfl) ⟨216710, by rfl⟩ : syracuseStep 288947 = 433421) B433421
theorem B256193 : Blo 111784 256193 := bstep (se 2 (by rfl) ⟨96072, by rfl⟩ : syracuseStep 256193 = 192145) B192145
theorem B190667 : Blo 111784 190667 := bstep (se 1 (by rfl) ⟨143000, by rfl⟩ : syracuseStep 190667 = 286001) B286001
theorem B485635 : Blo 111784 485635 := bstep (se 1 (by rfl) ⟨364226, by rfl⟩ : syracuseStep 485635 = 728453) B728453
theorem B190795 : Blo 111784 190795 := bstep (se 1 (by rfl) ⟨143096, by rfl⟩ : syracuseStep 190795 = 286193) B286193
theorem B551261 : Blo 111784 551261 := bstep (se 3 (by rfl) ⟨103361, by rfl⟩ : syracuseStep 551261 = 206723) B206723
theorem B256409 : Blo 111784 256409 := bstep (se 2 (by rfl) ⟨96153, by rfl⟩ : syracuseStep 256409 = 192307) B192307
theorem B190937 : Blo 111784 190937 := bstep (se 2 (by rfl) ⟨71601, by rfl⟩ : syracuseStep 190937 = 143203) B143203
theorem B289241 : Blo 111784 289241 := bstep (se 2 (by rfl) ⟨108465, by rfl⟩ : syracuseStep 289241 = 216931) B216931
theorem B256499 : Blo 111784 256499 := bstep (se 1 (by rfl) ⟨192374, by rfl⟩ : syracuseStep 256499 = 384749) B384749
theorem B256535 : Blo 111784 256535 := bstep (se 1 (by rfl) ⟨192401, by rfl⟩ : syracuseStep 256535 = 384803) B384803
theorem B977453 : Blo 111784 977453 := bstep (se 3 (by rfl) ⟨183272, by rfl⟩ : syracuseStep 977453 = 366545) B366545
theorem B191065 : Blo 111784 191065 := bstep (se 2 (by rfl) ⟨71649, by rfl⟩ : syracuseStep 191065 = 143299) B143299
theorem B256715 : Blo 111784 256715 := bstep (se 1 (by rfl) ⟨192536, by rfl⟩ : syracuseStep 256715 = 385073) B385073
theorem B256769 : Blo 111784 256769 := bstep (se 2 (by rfl) ⟨96288, by rfl⟩ : syracuseStep 256769 = 192577) B192577
theorem B322355 : Blo 111784 322355 := bstep (se 1 (by rfl) ⟨241766, by rfl⟩ : syracuseStep 322355 = 483533) B483533
theorem B486233 : Blo 111784 486233 := bstep (se 2 (by rfl) ⟨182337, by rfl⟩ : syracuseStep 486233 = 364675) B364675
theorem B125815 : Blo 111784 125815 := bstep (se 1 (by rfl) ⟨94361, by rfl⟩ : syracuseStep 125815 = 188723) B188723
theorem B388043 : Blo 111784 388043 := bstep (se 1 (by rfl) ⟨291032, by rfl⟩ : syracuseStep 388043 = 582065) B582065
theorem B256985 : Blo 111784 256985 := bstep (se 2 (by rfl) ⟨96369, by rfl⟩ : syracuseStep 256985 = 192739) B192739
theorem B125995 : Blo 111784 125995 := bstep (se 1 (by rfl) ⟨94496, by rfl⟩ : syracuseStep 125995 = 188993) B188993
theorem B257075 : Blo 111784 257075 := bstep (se 1 (by rfl) ⟨192806, by rfl⟩ : syracuseStep 257075 = 385613) B385613
theorem B257111 : Blo 111784 257111 := bstep (se 1 (by rfl) ⟨192833, by rfl⟩ : syracuseStep 257111 = 385667) B385667
theorem B126103 : Blo 111784 126103 := bstep (se 1 (by rfl) ⟨94577, by rfl⟩ : syracuseStep 126103 = 189155) B189155
theorem B191639 : Blo 111784 191639 := bstep (se 1 (by rfl) ⟨143729, by rfl⟩ : syracuseStep 191639 = 287459) B287459
theorem B2157749 : Blo 111784 2157749 := bstep (se 5 (by rfl) ⟨101144, by rfl⟩ : syracuseStep 2157749 = 202289) B202289
theorem B486593 : Blo 111784 486593 := bstep (se 2 (by rfl) ⟨182472, by rfl⟩ : syracuseStep 486593 = 364945) B364945
theorem B584921 : Blo 111784 584921 := bstep (se 2 (by rfl) ⟨219345, by rfl⟩ : syracuseStep 584921 = 438691) B438691
theorem B388313 : Blo 111784 388313 := bstep (se 2 (by rfl) ⟨145617, by rfl⟩ : syracuseStep 388313 = 291235) B291235
theorem B945413 : Blo 111784 945413 := bstep (se 4 (by rfl) ⟨88632, by rfl⟩ : syracuseStep 945413 = 177265) B177265
theorem B257291 : Blo 111784 257291 := bstep (se 1 (by rfl) ⟨192968, by rfl⟩ : syracuseStep 257291 = 385937) B385937
theorem B191767 : Blo 111784 191767 := bstep (se 1 (by rfl) ⟨143825, by rfl⟩ : syracuseStep 191767 = 287651) B287651
theorem B257345 : Blo 111784 257345 := bstep (se 2 (by rfl) ⟨96504, by rfl⟩ : syracuseStep 257345 = 193009) B193009
theorem B126283 : Blo 111784 126283 := bstep (se 1 (by rfl) ⟨94712, by rfl⟩ : syracuseStep 126283 = 189425) B189425
theorem B126391 : Blo 111784 126391 := bstep (se 1 (by rfl) ⟨94793, by rfl⟩ : syracuseStep 126391 = 189587) B189587
theorem B749017 : Blo 111784 749017 := bstep (se 2 (by rfl) ⟨280881, by rfl⟩ : syracuseStep 749017 = 561763) B561763
theorem B1404377 : Blo 111784 1404377 := bstep (se 2 (by rfl) ⟨526641, by rfl⟩ : syracuseStep 1404377 = 1053283) B1053283
theorem B257561 : Blo 111784 257561 := bstep (se 2 (by rfl) ⟨96585, by rfl⟩ : syracuseStep 257561 = 193171) B193171
theorem B126571 : Blo 111784 126571 := bstep (se 1 (by rfl) ⟨94928, by rfl⟩ : syracuseStep 126571 = 189857) B189857
theorem B257651 : Blo 111784 257651 := bstep (se 1 (by rfl) ⟨193238, by rfl⟩ : syracuseStep 257651 = 386477) B386477
theorem B257687 : Blo 111784 257687 := bstep (se 1 (by rfl) ⟨193265, by rfl⟩ : syracuseStep 257687 = 386531) B386531
theorem B126679 : Blo 111784 126679 := bstep (se 1 (by rfl) ⟨95009, by rfl⟩ : syracuseStep 126679 = 190019) B190019
theorem B257867 : Blo 111784 257867 := bstep (se 1 (by rfl) ⟨193400, by rfl⟩ : syracuseStep 257867 = 386801) B386801
theorem B257921 : Blo 111784 257921 := bstep (se 2 (by rfl) ⟨96720, by rfl⟩ : syracuseStep 257921 = 193441) B193441
theorem B126859 : Blo 111784 126859 := bstep (se 1 (by rfl) ⟨95144, by rfl⟩ : syracuseStep 126859 = 190289) B190289
theorem B192395 : Blo 111784 192395 := bstep (se 1 (by rfl) ⟨144296, by rfl⟩ : syracuseStep 192395 = 288593) B288593
theorem B389015 : Blo 111784 389015 := bstep (se 1 (by rfl) ⟨291761, by rfl⟩ : syracuseStep 389015 = 583523) B583523
theorem B126967 : Blo 111784 126967 := bstep (se 1 (by rfl) ⟨95225, by rfl⟩ : syracuseStep 126967 = 190451) B190451
theorem B192523 : Blo 111784 192523 := bstep (se 1 (by rfl) ⟨144392, by rfl⟩ : syracuseStep 192523 = 288785) B288785
theorem B290891 : Blo 111784 290891 := bstep (se 1 (by rfl) ⟨218168, by rfl⟩ : syracuseStep 290891 = 436337) B436337
theorem B258137 : Blo 111784 258137 := bstep (se 2 (by rfl) ⟨96801, by rfl⟩ : syracuseStep 258137 = 193603) B193603
theorem B192665 : Blo 111784 192665 := bstep (se 2 (by rfl) ⟨72249, by rfl⟩ : syracuseStep 192665 = 144499) B144499
theorem B127147 : Blo 111784 127147 := bstep (se 1 (by rfl) ⟨95360, by rfl⟩ : syracuseStep 127147 = 190721) B190721
theorem B258227 : Blo 111784 258227 := bstep (se 1 (by rfl) ⟨193670, by rfl⟩ : syracuseStep 258227 = 387341) B387341
theorem B258263 : Blo 111784 258263 := bstep (se 1 (by rfl) ⟨193697, by rfl⟩ : syracuseStep 258263 = 387395) B387395
theorem B127255 : Blo 111784 127255 := bstep (se 1 (by rfl) ⟨95441, by rfl⟩ : syracuseStep 127255 = 190883) B190883
theorem B192793 : Blo 111784 192793 := bstep (se 2 (by rfl) ⟨72297, by rfl⟩ : syracuseStep 192793 = 144595) B144595
theorem B586115 : Blo 111784 586115 := bstep (se 1 (by rfl) ⟨439586, by rfl⟩ : syracuseStep 586115 = 879173) B879173
theorem B258443 : Blo 111784 258443 := bstep (se 1 (by rfl) ⟨193832, by rfl⟩ : syracuseStep 258443 = 387665) B387665
theorem B455057 : Blo 111784 455057 := bstep (se 2 (by rfl) ⟨170646, by rfl⟩ : syracuseStep 455057 = 341293) B341293
theorem B1274291 : Blo 111784 1274291 := bstep (se 1 (by rfl) ⟨955718, by rfl⟩ : syracuseStep 1274291 = 1911437) B1911437
theorem B291251 : Blo 111784 291251 := bstep (se 1 (by rfl) ⟨218438, by rfl⟩ : syracuseStep 291251 = 436877) B436877
theorem B389555 : Blo 111784 389555 := bstep (se 1 (by rfl) ⟨292166, by rfl⟩ : syracuseStep 389555 = 584333) B584333
theorem B258497 : Blo 111784 258497 := bstep (se 2 (by rfl) ⟨96936, by rfl⟩ : syracuseStep 258497 = 193873) B193873
theorem B127435 : Blo 111784 127435 := bstep (se 1 (by rfl) ⟨95576, by rfl⟩ : syracuseStep 127435 = 191153) B191153
theorem B127543 : Blo 111784 127543 := bstep (se 1 (by rfl) ⟨95657, by rfl⟩ : syracuseStep 127543 = 191315) B191315
theorem B258713 : Blo 111784 258713 := bstep (se 2 (by rfl) ⟨97017, by rfl⟩ : syracuseStep 258713 = 194035) B194035
theorem B389825 : Blo 111784 389825 := bstep (se 2 (by rfl) ⟨146184, by rfl⟩ : syracuseStep 389825 = 292369) B292369
theorem B160471 : Blo 111784 160471 := bstep (se 1 (by rfl) ⟨120353, by rfl⟩ : syracuseStep 160471 = 240707) B240707
theorem B127723 : Blo 111784 127723 := bstep (se 1 (by rfl) ⟨95792, by rfl⟩ : syracuseStep 127723 = 191585) B191585
theorem B258803 : Blo 111784 258803 := bstep (se 1 (by rfl) ⟨194102, by rfl⟩ : syracuseStep 258803 = 388205) B388205
theorem B881425 : Blo 111784 881425 := bstep (se 2 (by rfl) ⟨330534, by rfl⟩ : syracuseStep 881425 = 661069) B661069
theorem B258839 : Blo 111784 258839 := bstep (se 1 (by rfl) ⟨194129, by rfl⟩ : syracuseStep 258839 = 388259) B388259
theorem B127831 : Blo 111784 127831 := bstep (se 1 (by rfl) ⟨95873, by rfl⟩ : syracuseStep 127831 = 191747) B191747
theorem B193367 : Blo 111784 193367 := bstep (se 1 (by rfl) ⟨145025, by rfl⟩ : syracuseStep 193367 = 290051) B290051
theorem B914327 : Blo 111784 914327 := bstep (se 1 (by rfl) ⟨685745, by rfl⟩ : syracuseStep 914327 = 1371491) B1371491
theorem B259019 : Blo 111784 259019 := bstep (se 1 (by rfl) ⟨194264, by rfl⟩ : syracuseStep 259019 = 388529) B388529
theorem B193495 : Blo 111784 193495 := bstep (se 1 (by rfl) ⟨145121, by rfl⟩ : syracuseStep 193495 = 290243) B290243
theorem B259073 : Blo 111784 259073 := bstep (se 2 (by rfl) ⟨97152, by rfl⟩ : syracuseStep 259073 = 194305) B194305
theorem B128011 : Blo 111784 128011 := bstep (se 1 (by rfl) ⟨96008, by rfl⟩ : syracuseStep 128011 = 192017) B192017
theorem B390167 : Blo 111784 390167 := bstep (se 1 (by rfl) ⟨292625, by rfl⟩ : syracuseStep 390167 = 585251) B585251
theorem B291863 : Blo 111784 291863 := bstep (se 1 (by rfl) ⟨218897, by rfl⟩ : syracuseStep 291863 = 437795) B437795
theorem B128119 : Blo 111784 128119 := bstep (se 1 (by rfl) ⟨96089, by rfl⟩ : syracuseStep 128119 = 192179) B192179
theorem B259289 : Blo 111784 259289 := bstep (se 2 (by rfl) ⟨97233, by rfl⟩ : syracuseStep 259289 = 194467) B194467
theorem B390365 : Blo 111784 390365 := bstep (se 3 (by rfl) ⟨73193, by rfl⟩ : syracuseStep 390365 = 146387) B146387
theorem B128299 : Blo 111784 128299 := bstep (se 1 (by rfl) ⟨96224, by rfl⟩ : syracuseStep 128299 = 192449) B192449
theorem B259379 : Blo 111784 259379 := bstep (se 1 (by rfl) ⟨194534, by rfl⟩ : syracuseStep 259379 = 389069) B389069
theorem B259415 : Blo 111784 259415 := bstep (se 1 (by rfl) ⟨194561, by rfl⟩ : syracuseStep 259415 = 389123) B389123
theorem B652637 : Blo 111784 652637 := bstep (se 3 (by rfl) ⟨122369, by rfl⟩ : syracuseStep 652637 = 244739) B244739
theorem B128407 : Blo 111784 128407 := bstep (se 1 (by rfl) ⟨96305, by rfl⟩ : syracuseStep 128407 = 192611) B192611
theorem B325043 : Blo 111784 325043 := bstep (se 1 (by rfl) ⟨243782, by rfl⟩ : syracuseStep 325043 = 487565) B487565
theorem B1111475 : Blo 111784 1111475 := bstep (se 1 (by rfl) ⟨833606, by rfl⟩ : syracuseStep 1111475 = 1667213) B1667213
theorem B259595 : Blo 111784 259595 := bstep (se 1 (by rfl) ⟨194696, by rfl⟩ : syracuseStep 259595 = 389393) B389393
theorem B259649 : Blo 111784 259649 := bstep (se 2 (by rfl) ⟨97368, by rfl⟩ : syracuseStep 259649 = 194737) B194737
theorem B128587 : Blo 111784 128587 := bstep (se 1 (by rfl) ⟨96440, by rfl⟩ : syracuseStep 128587 = 192881) B192881
theorem B194123 : Blo 111784 194123 := bstep (se 1 (by rfl) ⟨145592, by rfl⟩ : syracuseStep 194123 = 291185) B291185
theorem B325271 : Blo 111784 325271 := bstep (se 1 (by rfl) ⟨243953, by rfl⟩ : syracuseStep 325271 = 487907) B487907
theorem B292531 : Blo 111784 292531 := bstep (se 1 (by rfl) ⟨219398, by rfl⟩ : syracuseStep 292531 = 438797) B438797
theorem B128695 : Blo 111784 128695 := bstep (se 1 (by rfl) ⟨96521, by rfl⟩ : syracuseStep 128695 = 193043) B193043
theorem B227009 : Blo 111784 227009 := bstep (se 2 (by rfl) ⟨85128, by rfl⟩ : syracuseStep 227009 = 170257) B170257
theorem B194251 : Blo 111784 194251 := bstep (se 1 (by rfl) ⟨145688, by rfl⟩ : syracuseStep 194251 = 291377) B291377
theorem B259865 : Blo 111784 259865 := bstep (se 2 (by rfl) ⟨97449, by rfl⟩ : syracuseStep 259865 = 194899) B194899
theorem B292673 : Blo 111784 292673 := bstep (se 2 (by rfl) ⟨109752, by rfl⟩ : syracuseStep 292673 = 219505) B219505
theorem B194393 : Blo 111784 194393 := bstep (se 2 (by rfl) ⟨72897, by rfl⟩ : syracuseStep 194393 = 145795) B145795
theorem B1275749 : Blo 111784 1275749 := bstep (se 4 (by rfl) ⟨119601, by rfl⟩ : syracuseStep 1275749 = 239203) B239203
theorem B128875 : Blo 111784 128875 := bstep (se 1 (by rfl) ⟨96656, by rfl⟩ : syracuseStep 128875 = 193313) B193313
theorem B259955 : Blo 111784 259955 := bstep (se 1 (by rfl) ⟨194966, by rfl⟩ : syracuseStep 259955 = 389933) B389933
theorem B259991 : Blo 111784 259991 := bstep (se 1 (by rfl) ⟨194993, by rfl⟩ : syracuseStep 259991 = 389987) B389987
theorem B325579 : Blo 111784 325579 := bstep (se 1 (by rfl) ⟨244184, by rfl⟩ : syracuseStep 325579 = 488369) B488369
theorem B128983 : Blo 111784 128983 := bstep (se 1 (by rfl) ⟨96737, by rfl⟩ : syracuseStep 128983 = 193475) B193475
theorem B194521 : Blo 111784 194521 := bstep (se 2 (by rfl) ⟨72945, by rfl⟩ : syracuseStep 194521 = 145891) B145891
theorem B260171 : Blo 111784 260171 := bstep (se 1 (by rfl) ⟨195128, by rfl⟩ : syracuseStep 260171 = 390257) B390257
theorem B260183 : Blo 111784 260183 := bstep (se 1 (by rfl) ⟨195137, by rfl⟩ : syracuseStep 260183 = 390275) B390275
theorem B850013 : Blo 111784 850013 := bstep (se 3 (by rfl) ⟨159377, by rfl⟩ : syracuseStep 850013 = 318755) B318755
theorem B260225 : Blo 111784 260225 := bstep (se 2 (by rfl) ⟨97584, by rfl⟩ : syracuseStep 260225 = 195169) B195169
theorem B129163 : Blo 111784 129163 := bstep (se 1 (by rfl) ⟨96872, by rfl⟩ : syracuseStep 129163 = 193745) B193745
theorem B981143 : Blo 111784 981143 := bstep (se 1 (by rfl) ⟨735857, by rfl⟩ : syracuseStep 981143 = 1471715) B1471715
theorem B325853 : Blo 111784 325853 := bstep (se 3 (by rfl) ⟨61097, by rfl⟩ : syracuseStep 325853 = 122195) B122195
theorem B129271 : Blo 111784 129271 := bstep (se 1 (by rfl) ⟨96953, by rfl⟩ : syracuseStep 129271 = 193907) B193907
theorem B260441 : Blo 111784 260441 := bstep (se 2 (by rfl) ⟨97665, by rfl⟩ : syracuseStep 260441 = 195331) B195331
theorem B129451 : Blo 111784 129451 := bstep (se 1 (by rfl) ⟨97088, by rfl⟩ : syracuseStep 129451 = 194177) B194177
theorem B129559 : Blo 111784 129559 := bstep (se 1 (by rfl) ⟨97169, by rfl⟩ : syracuseStep 129559 = 194339) B194339
theorem B195095 : Blo 111784 195095 := bstep (se 1 (by rfl) ⟨146321, by rfl⟩ : syracuseStep 195095 = 292643) B292643
theorem B4651613 : Blo 111784 4651613 := bstep (se 3 (by rfl) ⟨872177, by rfl⟩ : syracuseStep 4651613 = 1744355) B1744355
theorem B359063 : Blo 111784 359063 := bstep (se 1 (by rfl) ⟨269297, by rfl⟩ : syracuseStep 359063 = 538595) B538595
theorem B195223 : Blo 111784 195223 := bstep (se 1 (by rfl) ⟨146417, by rfl⟩ : syracuseStep 195223 = 292835) B292835
theorem B129739 : Blo 111784 129739 := bstep (se 1 (by rfl) ⟨97304, by rfl⟩ : syracuseStep 129739 = 194609) B194609
theorem B129847 : Blo 111784 129847 := bstep (se 1 (by rfl) ⟨97385, by rfl⟩ : syracuseStep 129847 = 194771) B194771
theorem B490333 : Blo 111784 490333 := bstep (se 3 (by rfl) ⟨91937, by rfl⟩ : syracuseStep 490333 = 183875) B183875
theorem B130027 : Blo 111784 130027 := bstep (se 1 (by rfl) ⟨97520, by rfl⟩ : syracuseStep 130027 = 195041) B195041
theorem B293939 : Blo 111784 293939 := bstep (se 1 (by rfl) ⟨220454, by rfl⟩ : syracuseStep 293939 = 440909) B440909
theorem B130135 : Blo 111784 130135 := bstep (se 1 (by rfl) ⟨97601, by rfl⟩ : syracuseStep 130135 = 195203) B195203
theorem B228491 : Blo 111784 228491 := bstep (se 1 (by rfl) ⟨171368, by rfl⟩ : syracuseStep 228491 = 342737) B342737
theorem B195851 : Blo 111784 195851 := bstep (se 1 (by rfl) ⟨146888, by rfl⟩ : syracuseStep 195851 = 293777) B293777
theorem B359959 : Blo 111784 359959 := bstep (se 1 (by rfl) ⟨269969, by rfl⟩ : syracuseStep 359959 = 539939) B539939
theorem B425645 : Blo 111784 425645 := bstep (se 3 (by rfl) ⟨79808, by rfl⟩ : syracuseStep 425645 = 159617) B159617
theorem B327347 : Blo 111784 327347 := bstep (se 1 (by rfl) ⟨245510, by rfl⟩ : syracuseStep 327347 = 491021) B491021
theorem B425675 : Blo 111784 425675 := bstep (se 1 (by rfl) ⟨319256, by rfl⟩ : syracuseStep 425675 = 638513) B638513
theorem B130891 : Blo 111784 130891 := bstep (se 1 (by rfl) ⟨98168, by rfl⟩ : syracuseStep 130891 = 196337) B196337
theorem B655235 : Blo 111784 655235 := bstep (se 1 (by rfl) ⟨491426, by rfl⟩ : syracuseStep 655235 = 982853) B982853
theorem B360395 : Blo 111784 360395 := bstep (se 1 (by rfl) ⟨270296, by rfl⟩ : syracuseStep 360395 = 540593) B540593
theorem B163883 : Blo 111784 163883 := bstep (se 1 (by rfl) ⟨122912, by rfl⟩ : syracuseStep 163883 = 245825) B245825
theorem B655447 : Blo 111784 655447 := bstep (se 1 (by rfl) ⟨491585, by rfl⟩ : syracuseStep 655447 = 983171) B983171
theorem B655553 : Blo 111784 655553 := bstep (se 2 (by rfl) ⟨245832, by rfl⟩ : syracuseStep 655553 = 491665) B491665
theorem B40337621 : Blo 111784 40337621 := bstep (se 7 (by rfl) ⟨472706, by rfl⟩ : syracuseStep 40337621 = 945413) B945413
theorem B131387 : Blo 111784 131387 := bstep (se 1 (by rfl) ⟨98540, by rfl⟩ : syracuseStep 131387 = 197081) B197081
theorem B2326877 : Blo 111784 2326877 := bstep (se 3 (by rfl) ⟨436289, by rfl⟩ : syracuseStep 2326877 = 872579) B872579
theorem B820057 : Blo 111784 820057 := bstep (se 2 (by rfl) ⟨307521, by rfl⟩ : syracuseStep 820057 = 615043) B615043
theorem B230345 : Blo 111784 230345 := bstep (se 2 (by rfl) ⟨86379, by rfl⟩ : syracuseStep 230345 = 172759) B172759
theorem B328961 : Blo 111784 328961 := bstep (se 2 (by rfl) ⟨123360, by rfl⟩ : syracuseStep 328961 = 246721) B246721
theorem B197903 : Blo 111784 197903 := bstep (se 1 (by rfl) ⟨148427, by rfl⟩ : syracuseStep 197903 = 296855) B296855
theorem B492833 : Blo 111784 492833 := bstep (se 2 (by rfl) ⟨184812, by rfl⟩ : syracuseStep 492833 = 369625) B369625
theorem B493067 : Blo 111784 493067 := bstep (se 1 (by rfl) ⟨369800, by rfl⟩ : syracuseStep 493067 = 739601) B739601
theorem B296567 : Blo 111784 296567 := bstep (se 1 (by rfl) ⟨222425, by rfl⟩ : syracuseStep 296567 = 444851) B444851
theorem B329417 : Blo 111784 329417 := bstep (se 2 (by rfl) ⟨123531, by rfl⟩ : syracuseStep 329417 = 247063) B247063
theorem B428075 : Blo 111784 428075 := bstep (se 1 (by rfl) ⟨321056, by rfl⟩ : syracuseStep 428075 = 642113) B642113
theorem B657665 : Blo 111784 657665 := bstep (se 2 (by rfl) ⟨246624, by rfl⟩ : syracuseStep 657665 = 493249) B493249
theorem B330043 : Blo 111784 330043 := bstep (se 1 (by rfl) ⟨247532, by rfl⟩ : syracuseStep 330043 = 495065) B495065
theorem B854873 : Blo 111784 854873 := bstep (se 2 (by rfl) ⟨320577, by rfl⟩ : syracuseStep 854873 = 641155) B641155
theorem B985945 : Blo 111784 985945 := bstep (se 2 (by rfl) ⟨369729, by rfl⟩ : syracuseStep 985945 = 739459) B739459
theorem B462095 : Blo 111784 462095 := bstep (se 1 (by rfl) ⟨346571, by rfl⟩ : syracuseStep 462095 = 693143) B693143
theorem B232993 : Blo 111784 232993 := bstep (se 2 (by rfl) ⟨87372, by rfl⟩ : syracuseStep 232993 = 174745) B174745
theorem B527939 : Blo 111784 527939 := bstep (se 1 (by rfl) ⟨395954, by rfl⟩ : syracuseStep 527939 = 791909) B791909
theorem B167687 : Blo 111784 167687 := bstep (se 1 (by rfl) ⟨125765, by rfl⟩ : syracuseStep 167687 = 251531) B251531
theorem B855845 : Blo 111784 855845 := bstep (se 4 (by rfl) ⟨80235, by rfl⟩ : syracuseStep 855845 = 160471) B160471
theorem B167723 : Blo 111784 167723 := bstep (se 1 (by rfl) ⟨125792, by rfl⟩ : syracuseStep 167723 = 251585) B251585
theorem B724787 : Blo 111784 724787 := bstep (se 1 (by rfl) ⟨543590, by rfl⟩ : syracuseStep 724787 = 1087181) B1087181
theorem B167753 : Blo 111784 167753 := bstep (se 2 (by rfl) ⟨62907, by rfl⟩ : syracuseStep 167753 = 125815) B125815
theorem B724889 : Blo 111784 724889 := bstep (se 2 (by rfl) ⟨271833, by rfl⟩ : syracuseStep 724889 = 543667) B543667
theorem B167867 : Blo 111784 167867 := bstep (se 1 (by rfl) ⟨125900, by rfl⟩ : syracuseStep 167867 = 251801) B251801
theorem B167927 : Blo 111784 167927 := bstep (se 1 (by rfl) ⟨125945, by rfl⟩ : syracuseStep 167927 = 251891) B251891
theorem B167951 : Blo 111784 167951 := bstep (se 1 (by rfl) ⟨125963, by rfl⟩ : syracuseStep 167951 = 251927) B251927
theorem B2199575 : Blo 111784 2199575 := bstep (se 1 (by rfl) ⟨1649681, by rfl⟩ : syracuseStep 2199575 = 3299363) B3299363
theorem B167993 : Blo 111784 167993 := bstep (se 2 (by rfl) ⟨62997, by rfl⟩ : syracuseStep 167993 = 125995) B125995
theorem B168071 : Blo 111784 168071 := bstep (se 1 (by rfl) ⟨126053, by rfl⟩ : syracuseStep 168071 = 252107) B252107
theorem B168107 : Blo 111784 168107 := bstep (se 1 (by rfl) ⟨126080, by rfl⟩ : syracuseStep 168107 = 252161) B252161
theorem B135355 : Blo 111784 135355 := bstep (se 1 (by rfl) ⟨101516, by rfl⟩ : syracuseStep 135355 = 203033) B203033
theorem B168137 : Blo 111784 168137 := bstep (se 2 (by rfl) ⟨63051, by rfl⟩ : syracuseStep 168137 = 126103) B126103
theorem B1937681 : Blo 111784 1937681 := bstep (se 2 (by rfl) ⟨726630, by rfl⟩ : syracuseStep 1937681 = 1453261) B1453261
theorem B168251 : Blo 111784 168251 := bstep (se 1 (by rfl) ⟨126188, by rfl⟩ : syracuseStep 168251 = 252377) B252377
theorem B168311 : Blo 111784 168311 := bstep (se 1 (by rfl) ⟨126233, by rfl⟩ : syracuseStep 168311 = 252467) B252467
theorem B168335 : Blo 111784 168335 := bstep (se 1 (by rfl) ⟨126251, by rfl⟩ : syracuseStep 168335 = 252503) B252503
theorem B168377 : Blo 111784 168377 := bstep (se 2 (by rfl) ⟨63141, by rfl⟩ : syracuseStep 168377 = 126283) B126283
theorem B168455 : Blo 111784 168455 := bstep (se 1 (by rfl) ⟨126341, by rfl⟩ : syracuseStep 168455 = 252683) B252683
theorem B168491 : Blo 111784 168491 := bstep (se 1 (by rfl) ⟨126368, by rfl⟩ : syracuseStep 168491 = 252737) B252737
theorem B168521 : Blo 111784 168521 := bstep (se 2 (by rfl) ⟨63195, by rfl⟩ : syracuseStep 168521 = 126391) B126391
theorem B168635 : Blo 111784 168635 := bstep (se 1 (by rfl) ⟨126476, by rfl⟩ : syracuseStep 168635 = 252953) B252953
theorem B168695 : Blo 111784 168695 := bstep (se 1 (by rfl) ⟨126521, by rfl⟩ : syracuseStep 168695 = 253043) B253043
theorem B168719 : Blo 111784 168719 := bstep (se 1 (by rfl) ⟨126539, by rfl⟩ : syracuseStep 168719 = 253079) B253079
theorem B168761 : Blo 111784 168761 := bstep (se 2 (by rfl) ⟨63285, by rfl⟩ : syracuseStep 168761 = 126571) B126571
theorem B168839 : Blo 111784 168839 := bstep (se 1 (by rfl) ⟨126629, by rfl⟩ : syracuseStep 168839 = 253259) B253259
theorem B168875 : Blo 111784 168875 := bstep (se 1 (by rfl) ⟨126656, by rfl⟩ : syracuseStep 168875 = 253313) B253313
theorem B168905 : Blo 111784 168905 := bstep (se 2 (by rfl) ⟨63339, by rfl⟩ : syracuseStep 168905 = 126679) B126679
theorem B169019 : Blo 111784 169019 := bstep (se 1 (by rfl) ⟨126764, by rfl⟩ : syracuseStep 169019 = 253529) B253529
theorem B824381 : Blo 111784 824381 := bstep (se 3 (by rfl) ⟨154571, by rfl⟩ : syracuseStep 824381 = 309143) B309143
theorem B169079 : Blo 111784 169079 := bstep (se 1 (by rfl) ⟨126809, by rfl⟩ : syracuseStep 169079 = 253619) B253619
theorem B169103 : Blo 111784 169103 := bstep (se 1 (by rfl) ⟨126827, by rfl⟩ : syracuseStep 169103 = 253655) B253655
theorem B169145 : Blo 111784 169145 := bstep (se 2 (by rfl) ⟨63429, by rfl⟩ : syracuseStep 169145 = 126859) B126859
theorem B169223 : Blo 111784 169223 := bstep (se 1 (by rfl) ⟨126917, by rfl⟩ : syracuseStep 169223 = 253835) B253835
theorem B169259 : Blo 111784 169259 := bstep (se 1 (by rfl) ⟨126944, by rfl⟩ : syracuseStep 169259 = 253889) B253889
theorem B169289 : Blo 111784 169289 := bstep (se 2 (by rfl) ⟨63483, by rfl⟩ : syracuseStep 169289 = 126967) B126967
theorem B431507 : Blo 111784 431507 := bstep (se 1 (by rfl) ⟨323630, by rfl⟩ : syracuseStep 431507 = 647261) B647261
theorem B169403 : Blo 111784 169403 := bstep (se 1 (by rfl) ⟨127052, by rfl⟩ : syracuseStep 169403 = 254105) B254105
theorem B169463 : Blo 111784 169463 := bstep (se 1 (by rfl) ⟨127097, by rfl⟩ : syracuseStep 169463 = 254195) B254195
theorem B169487 : Blo 111784 169487 := bstep (se 1 (by rfl) ⟨127115, by rfl⟩ : syracuseStep 169487 = 254231) B254231
theorem B169529 : Blo 111784 169529 := bstep (se 2 (by rfl) ⟨63573, by rfl⟩ : syracuseStep 169529 = 127147) B127147
theorem B693821 : Blo 111784 693821 := bstep (se 3 (by rfl) ⟨130091, by rfl⟩ : syracuseStep 693821 = 260183) B260183
theorem B169607 : Blo 111784 169607 := bstep (se 1 (by rfl) ⟨127205, by rfl⟩ : syracuseStep 169607 = 254411) B254411
theorem B169643 : Blo 111784 169643 := bstep (se 1 (by rfl) ⟨127232, by rfl⟩ : syracuseStep 169643 = 254465) B254465
theorem B136891 : Blo 111784 136891 := bstep (se 1 (by rfl) ⟨102668, by rfl⟩ : syracuseStep 136891 = 205337) B205337
theorem B169673 : Blo 111784 169673 := bstep (se 2 (by rfl) ⟨63627, by rfl⟩ : syracuseStep 169673 = 127255) B127255
theorem B169787 : Blo 111784 169787 := bstep (se 1 (by rfl) ⟨127340, by rfl⟩ : syracuseStep 169787 = 254681) B254681
theorem B169847 : Blo 111784 169847 := bstep (se 1 (by rfl) ⟨127385, by rfl⟩ : syracuseStep 169847 = 254771) B254771
theorem B169871 : Blo 111784 169871 := bstep (se 1 (by rfl) ⟨127403, by rfl⟩ : syracuseStep 169871 = 254807) B254807
theorem B169913 : Blo 111784 169913 := bstep (se 2 (by rfl) ⟨63717, by rfl⟩ : syracuseStep 169913 = 127435) B127435
theorem B137147 : Blo 111784 137147 := bstep (se 1 (by rfl) ⟨102860, by rfl⟩ : syracuseStep 137147 = 205721) B205721
theorem B169991 : Blo 111784 169991 := bstep (se 1 (by rfl) ⟨127493, by rfl⟩ : syracuseStep 169991 = 254987) B254987
theorem B170027 : Blo 111784 170027 := bstep (se 1 (by rfl) ⟨127520, by rfl⟩ : syracuseStep 170027 = 255041) B255041
theorem B170057 : Blo 111784 170057 := bstep (se 2 (by rfl) ⟨63771, by rfl⟩ : syracuseStep 170057 = 127543) B127543
theorem B170171 : Blo 111784 170171 := bstep (se 1 (by rfl) ⟨127628, by rfl⟩ : syracuseStep 170171 = 255257) B255257
theorem B170231 : Blo 111784 170231 := bstep (se 1 (by rfl) ⟨127673, by rfl⟩ : syracuseStep 170231 = 255347) B255347
theorem B170255 : Blo 111784 170255 := bstep (se 1 (by rfl) ⟨127691, by rfl⟩ : syracuseStep 170255 = 255383) B255383
theorem B170297 : Blo 111784 170297 := bstep (se 2 (by rfl) ⟨63861, by rfl⟩ : syracuseStep 170297 = 127723) B127723
theorem B1153415 : Blo 111784 1153415 := bstep (se 1 (by rfl) ⟨865061, by rfl⟩ : syracuseStep 1153415 = 1730123) B1730123
theorem B170375 : Blo 111784 170375 := bstep (se 1 (by rfl) ⟨127781, by rfl⟩ : syracuseStep 170375 = 255563) B255563
theorem B1284497 : Blo 111784 1284497 := bstep (se 2 (by rfl) ⟨481686, by rfl⟩ : syracuseStep 1284497 = 963373) B963373
theorem B170411 : Blo 111784 170411 := bstep (se 1 (by rfl) ⟨127808, by rfl⟩ : syracuseStep 170411 = 255617) B255617
theorem B170441 : Blo 111784 170441 := bstep (se 2 (by rfl) ⟨63915, by rfl⟩ : syracuseStep 170441 = 127831) B127831
theorem B170555 : Blo 111784 170555 := bstep (se 1 (by rfl) ⟨127916, by rfl⟩ : syracuseStep 170555 = 255833) B255833
theorem B170615 : Blo 111784 170615 := bstep (se 1 (by rfl) ⟨127961, by rfl⟩ : syracuseStep 170615 = 255923) B255923
theorem B170639 : Blo 111784 170639 := bstep (se 1 (by rfl) ⟨127979, by rfl⟩ : syracuseStep 170639 = 255959) B255959
theorem B170681 : Blo 111784 170681 := bstep (se 2 (by rfl) ⟨64005, by rfl⟩ : syracuseStep 170681 = 128011) B128011
theorem B170759 : Blo 111784 170759 := bstep (se 1 (by rfl) ⟨128069, by rfl⟩ : syracuseStep 170759 = 256139) B256139
theorem B170795 : Blo 111784 170795 := bstep (se 1 (by rfl) ⟨128096, by rfl⟩ : syracuseStep 170795 = 256193) B256193
theorem B170825 : Blo 111784 170825 := bstep (se 2 (by rfl) ⟨64059, by rfl⟩ : syracuseStep 170825 = 128119) B128119
theorem B367507 : Blo 111784 367507 := bstep (se 1 (by rfl) ⟨275630, by rfl⟩ : syracuseStep 367507 = 551261) B551261
theorem B170939 : Blo 111784 170939 := bstep (se 1 (by rfl) ⟨128204, by rfl⟩ : syracuseStep 170939 = 256409) B256409
theorem B170999 : Blo 111784 170999 := bstep (se 1 (by rfl) ⟨128249, by rfl⟩ : syracuseStep 170999 = 256499) B256499
theorem B171023 : Blo 111784 171023 := bstep (se 1 (by rfl) ⟨128267, by rfl⟩ : syracuseStep 171023 = 256535) B256535
theorem B171065 : Blo 111784 171065 := bstep (se 2 (by rfl) ⟨64149, by rfl⟩ : syracuseStep 171065 = 128299) B128299
theorem B171143 : Blo 111784 171143 := bstep (se 1 (by rfl) ⟨128357, by rfl⟩ : syracuseStep 171143 = 256715) B256715
theorem B171179 : Blo 111784 171179 := bstep (se 1 (by rfl) ⟨128384, by rfl⟩ : syracuseStep 171179 = 256769) B256769
theorem B171209 : Blo 111784 171209 := bstep (se 2 (by rfl) ⟨64203, by rfl⟩ : syracuseStep 171209 = 128407) B128407
theorem B171323 : Blo 111784 171323 := bstep (se 1 (by rfl) ⟨128492, by rfl⟩ : syracuseStep 171323 = 256985) B256985
theorem B662843 : Blo 111784 662843 := bstep (se 1 (by rfl) ⟨497132, by rfl⟩ : syracuseStep 662843 = 994265) B994265
theorem B171383 : Blo 111784 171383 := bstep (se 1 (by rfl) ⟨128537, by rfl⟩ : syracuseStep 171383 = 257075) B257075
theorem B171407 : Blo 111784 171407 := bstep (se 1 (by rfl) ⟨128555, by rfl⟩ : syracuseStep 171407 = 257111) B257111
theorem B171449 : Blo 111784 171449 := bstep (se 2 (by rfl) ⟨64293, by rfl⟩ : syracuseStep 171449 = 128587) B128587
theorem B171527 : Blo 111784 171527 := bstep (se 1 (by rfl) ⟨128645, by rfl⟩ : syracuseStep 171527 = 257291) B257291
theorem B171563 : Blo 111784 171563 := bstep (se 1 (by rfl) ⟨128672, by rfl⟩ : syracuseStep 171563 = 257345) B257345
theorem B171593 : Blo 111784 171593 := bstep (se 2 (by rfl) ⟨64347, by rfl⟩ : syracuseStep 171593 = 128695) B128695
theorem B171707 : Blo 111784 171707 := bstep (se 1 (by rfl) ⟨128780, by rfl⟩ : syracuseStep 171707 = 257561) B257561
theorem B171767 : Blo 111784 171767 := bstep (se 1 (by rfl) ⟨128825, by rfl⟩ : syracuseStep 171767 = 257651) B257651
theorem B171791 : Blo 111784 171791 := bstep (se 1 (by rfl) ⟨128843, by rfl⟩ : syracuseStep 171791 = 257687) B257687
theorem B171833 : Blo 111784 171833 := bstep (se 2 (by rfl) ⟨64437, by rfl⟩ : syracuseStep 171833 = 128875) B128875
theorem B171911 : Blo 111784 171911 := bstep (se 1 (by rfl) ⟨128933, by rfl⟩ : syracuseStep 171911 = 257867) B257867
theorem B171947 : Blo 111784 171947 := bstep (se 1 (by rfl) ⟨128960, by rfl⟩ : syracuseStep 171947 = 257921) B257921
theorem B434105 : Blo 111784 434105 := bstep (se 2 (by rfl) ⟨162789, by rfl⟩ : syracuseStep 434105 = 325579) B325579
theorem B171977 : Blo 111784 171977 := bstep (se 2 (by rfl) ⟨64491, by rfl⟩ : syracuseStep 171977 = 128983) B128983
theorem B172091 : Blo 111784 172091 := bstep (se 1 (by rfl) ⟨129068, by rfl⟩ : syracuseStep 172091 = 258137) B258137
theorem B172151 : Blo 111784 172151 := bstep (se 1 (by rfl) ⟨129113, by rfl⟩ : syracuseStep 172151 = 258227) B258227
theorem B172175 : Blo 111784 172175 := bstep (se 1 (by rfl) ⟨129131, by rfl⟩ : syracuseStep 172175 = 258263) B258263
theorem B172217 : Blo 111784 172217 := bstep (se 2 (by rfl) ⟨64581, by rfl⟩ : syracuseStep 172217 = 129163) B129163
theorem B1646837 : Blo 111784 1646837 := bstep (se 5 (by rfl) ⟨77195, by rfl⟩ : syracuseStep 1646837 = 154391) B154391
theorem B172295 : Blo 111784 172295 := bstep (se 1 (by rfl) ⟨129221, by rfl⟩ : syracuseStep 172295 = 258443) B258443
theorem B303371 : Blo 111784 303371 := bstep (se 1 (by rfl) ⟨227528, by rfl⟩ : syracuseStep 303371 = 455057) B455057
theorem B172331 : Blo 111784 172331 := bstep (se 1 (by rfl) ⟨129248, by rfl⟩ : syracuseStep 172331 = 258497) B258497
theorem B172361 : Blo 111784 172361 := bstep (se 2 (by rfl) ⟨64635, by rfl⟩ : syracuseStep 172361 = 129271) B129271
theorem B172475 : Blo 111784 172475 := bstep (se 1 (by rfl) ⟨129356, by rfl⟩ : syracuseStep 172475 = 258713) B258713
theorem B172535 : Blo 111784 172535 := bstep (se 1 (by rfl) ⟨129401, by rfl⟩ : syracuseStep 172535 = 258803) B258803
theorem B172559 : Blo 111784 172559 := bstep (se 1 (by rfl) ⟨129419, by rfl⟩ : syracuseStep 172559 = 258839) B258839
theorem B172601 : Blo 111784 172601 := bstep (se 2 (by rfl) ⟨64725, by rfl⟩ : syracuseStep 172601 = 129451) B129451
theorem B172679 : Blo 111784 172679 := bstep (se 1 (by rfl) ⟨129509, by rfl⟩ : syracuseStep 172679 = 259019) B259019
theorem B172715 : Blo 111784 172715 := bstep (se 1 (by rfl) ⟨129536, by rfl⟩ : syracuseStep 172715 = 259073) B259073
theorem B172745 : Blo 111784 172745 := bstep (se 2 (by rfl) ⟨64779, by rfl⟩ : syracuseStep 172745 = 129559) B129559
theorem B369353 : Blo 111784 369353 := bstep (se 2 (by rfl) ⟨138507, by rfl⟩ : syracuseStep 369353 = 277015) B277015
theorem B172859 : Blo 111784 172859 := bstep (se 1 (by rfl) ⟨129644, by rfl⟩ : syracuseStep 172859 = 259289) B259289
theorem B172919 : Blo 111784 172919 := bstep (se 1 (by rfl) ⟨129689, by rfl⟩ : syracuseStep 172919 = 259379) B259379
theorem B172943 : Blo 111784 172943 := bstep (se 1 (by rfl) ⟨129707, by rfl⟩ : syracuseStep 172943 = 259415) B259415
theorem B435091 : Blo 111784 435091 := bstep (se 1 (by rfl) ⟨326318, by rfl⟩ : syracuseStep 435091 = 652637) B652637
theorem B172985 : Blo 111784 172985 := bstep (se 2 (by rfl) ⟨64869, by rfl⟩ : syracuseStep 172985 = 129739) B129739
theorem B173063 : Blo 111784 173063 := bstep (se 1 (by rfl) ⟨129797, by rfl⟩ : syracuseStep 173063 = 259595) B259595
theorem B173099 : Blo 111784 173099 := bstep (se 1 (by rfl) ⟨129824, by rfl⟩ : syracuseStep 173099 = 259649) B259649
theorem B173129 : Blo 111784 173129 := bstep (se 2 (by rfl) ⟨64923, by rfl⟩ : syracuseStep 173129 = 129847) B129847
theorem B271507 : Blo 111784 271507 := bstep (se 1 (by rfl) ⟨203630, by rfl⟩ : syracuseStep 271507 = 407261) B407261
theorem B173243 : Blo 111784 173243 := bstep (se 1 (by rfl) ⟨129932, by rfl⟩ : syracuseStep 173243 = 259865) B259865
theorem B238793 : Blo 111784 238793 := bstep (se 2 (by rfl) ⟨89547, by rfl⟩ : syracuseStep 238793 = 179095) B179095
theorem B1320137 : Blo 111784 1320137 := bstep (se 2 (by rfl) ⟨495051, by rfl⟩ : syracuseStep 1320137 = 990103) B990103
theorem B1615085 : Blo 111784 1615085 := bstep (se 3 (by rfl) ⟨302828, by rfl⟩ : syracuseStep 1615085 = 605657) B605657
theorem B1287413 : Blo 111784 1287413 := bstep (se 5 (by rfl) ⟨60347, by rfl⟩ : syracuseStep 1287413 = 120695) B120695
theorem B173303 : Blo 111784 173303 := bstep (se 1 (by rfl) ⟨129977, by rfl⟩ : syracuseStep 173303 = 259955) B259955
theorem B173327 : Blo 111784 173327 := bstep (se 1 (by rfl) ⟨129995, by rfl⟩ : syracuseStep 173327 = 259991) B259991
theorem B173369 : Blo 111784 173369 := bstep (se 2 (by rfl) ⟨65013, by rfl⟩ : syracuseStep 173369 = 130027) B130027
theorem B173447 : Blo 111784 173447 := bstep (se 1 (by rfl) ⟨130085, by rfl⟩ : syracuseStep 173447 = 260171) B260171
theorem B566675 : Blo 111784 566675 := bstep (se 1 (by rfl) ⟨425006, by rfl⟩ : syracuseStep 566675 = 850013) B850013
theorem B173483 : Blo 111784 173483 := bstep (se 1 (by rfl) ⟨130112, by rfl⟩ : syracuseStep 173483 = 260225) B260225
theorem B239033 : Blo 111784 239033 := bstep (se 2 (by rfl) ⟨89637, by rfl⟩ : syracuseStep 239033 = 179275) B179275
theorem B173513 : Blo 111784 173513 := bstep (se 2 (by rfl) ⟨65067, by rfl⟩ : syracuseStep 173513 = 130135) B130135
theorem B173627 : Blo 111784 173627 := bstep (se 1 (by rfl) ⟨130220, by rfl⟩ : syracuseStep 173627 = 260441) B260441
theorem B1451621 : Blo 111784 1451621 := bstep (se 4 (by rfl) ⟨136089, by rfl⟩ : syracuseStep 1451621 = 272179) B272179
theorem B239375 : Blo 111784 239375 := bstep (se 1 (by rfl) ⟨179531, by rfl⟩ : syracuseStep 239375 = 359063) B359063
theorem B239545 : Blo 111784 239545 := bstep (se 2 (by rfl) ⟨89829, by rfl⟩ : syracuseStep 239545 = 179659) B179659
theorem B272641 : Blo 111784 272641 := bstep (se 2 (by rfl) ⟨102240, by rfl⟩ : syracuseStep 272641 = 204481) B204481
theorem B141583 : Blo 111784 141583 := bstep (se 1 (by rfl) ⟨106187, by rfl⟩ : syracuseStep 141583 = 212375) B212375
theorem B862649 : Blo 111784 862649 := bstep (se 2 (by rfl) ⟨323493, by rfl⟩ : syracuseStep 862649 = 646987) B646987
theorem B174521 : Blo 111784 174521 := bstep (se 2 (by rfl) ⟨65445, by rfl⟩ : syracuseStep 174521 = 130891) B130891
theorem B436823 : Blo 111784 436823 := bstep (se 1 (by rfl) ⟨327617, by rfl⟩ : syracuseStep 436823 = 655235) B655235
theorem B207479 : Blo 111784 207479 := bstep (se 1 (by rfl) ⟨155609, by rfl⟩ : syracuseStep 207479 = 311219) B311219
theorem B240263 : Blo 111784 240263 := bstep (se 1 (by rfl) ⟨180197, by rfl⟩ : syracuseStep 240263 = 360395) B360395
theorem B1288921 : Blo 111784 1288921 := bstep (se 2 (by rfl) ⟨483345, by rfl⟩ : syracuseStep 1288921 = 966691) B966691
theorem B142327 : Blo 111784 142327 := bstep (se 1 (by rfl) ⟨106745, by rfl⟩ : syracuseStep 142327 = 213491) B213491
theorem B240673 : Blo 111784 240673 := bstep (se 2 (by rfl) ⟨90252, by rfl⟩ : syracuseStep 240673 = 180505) B180505
theorem B437309 : Blo 111784 437309 := bstep (se 3 (by rfl) ⟨81995, by rfl⟩ : syracuseStep 437309 = 163991) B163991
theorem B142651 : Blo 111784 142651 := bstep (se 1 (by rfl) ⟨106988, by rfl⟩ : syracuseStep 142651 = 213977) B213977
theorem B208187 : Blo 111784 208187 := bstep (se 1 (by rfl) ⟨156140, by rfl⟩ : syracuseStep 208187 = 312281) B312281
theorem B241015 : Blo 111784 241015 := bstep (se 1 (by rfl) ⟨180761, by rfl⟩ : syracuseStep 241015 = 361523) B361523
theorem B241451 : Blo 111784 241451 := bstep (se 1 (by rfl) ⟨181088, by rfl⟩ : syracuseStep 241451 = 362177) B362177
theorem B143147 : Blo 111784 143147 := bstep (se 1 (by rfl) ⟨107360, by rfl⟩ : syracuseStep 143147 = 214721) B214721
theorem B1093637 : Blo 111784 1093637 := bstep (se 4 (by rfl) ⟨102528, by rfl⟩ : syracuseStep 1093637 = 205057) B205057
theorem B700535 : Blo 111784 700535 := bstep (se 1 (by rfl) ⟨525401, by rfl⟩ : syracuseStep 700535 = 1050803) B1050803
theorem B143623 : Blo 111784 143623 := bstep (se 1 (by rfl) ⟨107717, by rfl⟩ : syracuseStep 143623 = 215435) B215435
theorem B569753 : Blo 111784 569753 := bstep (se 2 (by rfl) ⟨213657, by rfl⟩ : syracuseStep 569753 = 427315) B427315
theorem B144119 : Blo 111784 144119 := bstep (se 1 (by rfl) ⟨108089, by rfl⟩ : syracuseStep 144119 = 216179) B216179
theorem B537479 : Blo 111784 537479 := bstep (se 1 (by rfl) ⟨403109, by rfl⟩ : syracuseStep 537479 = 806219) B806219
theorem B144271 : Blo 111784 144271 := bstep (se 1 (by rfl) ⟨108203, by rfl⟩ : syracuseStep 144271 = 216407) B216407
theorem B144443 : Blo 111784 144443 := bstep (se 1 (by rfl) ⟨108332, by rfl⟩ : syracuseStep 144443 = 216665) B216665
theorem B111803 : Blo 111784 111803 := bstep (se 1 (by rfl) ⟨83852, by rfl⟩ : syracuseStep 111803 = 167705) B167705
theorem B439553 : Blo 111784 439553 := bstep (se 2 (by rfl) ⟨164832, by rfl⟩ : syracuseStep 439553 = 329665) B329665
theorem B111879 : Blo 111784 111879 := bstep (se 1 (by rfl) ⟨83909, by rfl⟩ : syracuseStep 111879 = 167819) B167819
theorem B111887 : Blo 111784 111887 := bstep (se 1 (by rfl) ⟨83915, by rfl⟩ : syracuseStep 111887 = 167831) B167831
theorem B111931 : Blo 111784 111931 := bstep (se 1 (by rfl) ⟨83948, by rfl⟩ : syracuseStep 111931 = 167897) B167897
theorem B112007 : Blo 111784 112007 := bstep (se 1 (by rfl) ⟨84005, by rfl⟩ : syracuseStep 112007 = 168011) B168011
theorem B112015 : Blo 111784 112015 := bstep (se 1 (by rfl) ⟨84011, by rfl⟩ : syracuseStep 112015 = 168023) B168023
theorem B308627 : Blo 111784 308627 := bstep (se 1 (by rfl) ⟨231470, by rfl⟩ : syracuseStep 308627 = 462941) B462941
theorem B243091 : Blo 111784 243091 := bstep (se 1 (by rfl) ⟨182318, by rfl⟩ : syracuseStep 243091 = 364637) B364637
theorem B112059 : Blo 111784 112059 := bstep (se 1 (by rfl) ⟨84044, by rfl⟩ : syracuseStep 112059 = 168089) B168089
theorem B112135 : Blo 111784 112135 := bstep (se 1 (by rfl) ⟨84101, by rfl⟩ : syracuseStep 112135 = 168203) B168203
theorem B112143 : Blo 111784 112143 := bstep (se 1 (by rfl) ⟨84107, by rfl⟩ : syracuseStep 112143 = 168215) B168215
theorem B112187 : Blo 111784 112187 := bstep (se 1 (by rfl) ⟨84140, by rfl⟩ : syracuseStep 112187 = 168281) B168281
theorem B112263 : Blo 111784 112263 := bstep (se 1 (by rfl) ⟨84197, by rfl⟩ : syracuseStep 112263 = 168395) B168395
theorem B112271 : Blo 111784 112271 := bstep (se 1 (by rfl) ⟨84203, by rfl⟩ : syracuseStep 112271 = 168407) B168407
theorem B112315 : Blo 111784 112315 := bstep (se 1 (by rfl) ⟨84236, by rfl⟩ : syracuseStep 112315 = 168473) B168473
theorem B1226497 : Blo 111784 1226497 := bstep (se 2 (by rfl) ⟨459936, by rfl⟩ : syracuseStep 1226497 = 919873) B919873
theorem B112391 : Blo 111784 112391 := bstep (se 1 (by rfl) ⟨84293, by rfl⟩ : syracuseStep 112391 = 168587) B168587
theorem B112399 : Blo 111784 112399 := bstep (se 1 (by rfl) ⟨84299, by rfl⟩ : syracuseStep 112399 = 168599) B168599
theorem B112443 : Blo 111784 112443 := bstep (se 1 (by rfl) ⟨84332, by rfl⟩ : syracuseStep 112443 = 168665) B168665
theorem B2471755 : Blo 111784 2471755 := bstep (se 1 (by rfl) ⟨1853816, by rfl⟩ : syracuseStep 2471755 = 3707633) B3707633
theorem B112519 : Blo 111784 112519 := bstep (se 1 (by rfl) ⟨84389, by rfl⟩ : syracuseStep 112519 = 168779) B168779
theorem B112527 : Blo 111784 112527 := bstep (se 1 (by rfl) ⟨84395, by rfl⟩ : syracuseStep 112527 = 168791) B168791
theorem B702361 : Blo 111784 702361 := bstep (se 2 (by rfl) ⟨263385, by rfl⟩ : syracuseStep 702361 = 526771) B526771
theorem B112571 : Blo 111784 112571 := bstep (se 1 (by rfl) ⟨84428, by rfl⟩ : syracuseStep 112571 = 168857) B168857
theorem B112647 : Blo 111784 112647 := bstep (se 1 (by rfl) ⟨84485, by rfl⟩ : syracuseStep 112647 = 168971) B168971
theorem B145415 : Blo 111784 145415 := bstep (se 1 (by rfl) ⟨109061, by rfl⟩ : syracuseStep 145415 = 218123) B218123
theorem B112655 : Blo 111784 112655 := bstep (se 1 (by rfl) ⟨84491, by rfl⟩ : syracuseStep 112655 = 168983) B168983
theorem B112699 : Blo 111784 112699 := bstep (se 1 (by rfl) ⟨84524, by rfl⟩ : syracuseStep 112699 = 169049) B169049
theorem B112775 : Blo 111784 112775 := bstep (se 1 (by rfl) ⟨84581, by rfl⟩ : syracuseStep 112775 = 169163) B169163
theorem B112783 : Blo 111784 112783 := bstep (se 1 (by rfl) ⟨84587, by rfl⟩ : syracuseStep 112783 = 169175) B169175
theorem B112827 : Blo 111784 112827 := bstep (se 1 (by rfl) ⟨84620, by rfl⟩ : syracuseStep 112827 = 169241) B169241
theorem B112903 : Blo 111784 112903 := bstep (se 1 (by rfl) ⟨84677, by rfl⟩ : syracuseStep 112903 = 169355) B169355
theorem B112911 : Blo 111784 112911 := bstep (se 1 (by rfl) ⟨84683, by rfl⟩ : syracuseStep 112911 = 169367) B169367
theorem B112955 : Blo 111784 112955 := bstep (se 1 (by rfl) ⟨84716, by rfl⟩ : syracuseStep 112955 = 169433) B169433
theorem B113031 : Blo 111784 113031 := bstep (se 1 (by rfl) ⟨84773, by rfl⟩ : syracuseStep 113031 = 169547) B169547
theorem B113039 : Blo 111784 113039 := bstep (se 1 (by rfl) ⟨84779, by rfl⟩ : syracuseStep 113039 = 169559) B169559
theorem B113083 : Blo 111784 113083 := bstep (se 1 (by rfl) ⟨84812, by rfl⟩ : syracuseStep 113083 = 169625) B169625
theorem B113159 : Blo 111784 113159 := bstep (se 1 (by rfl) ⟨84869, by rfl⟩ : syracuseStep 113159 = 169739) B169739
theorem B113167 : Blo 111784 113167 := bstep (se 1 (by rfl) ⟨84875, by rfl⟩ : syracuseStep 113167 = 169751) B169751
theorem B211499 : Blo 111784 211499 := bstep (se 1 (by rfl) ⟨158624, by rfl⟩ : syracuseStep 211499 = 317249) B317249
theorem B113211 : Blo 111784 113211 := bstep (se 1 (by rfl) ⟨84908, by rfl⟩ : syracuseStep 113211 = 169817) B169817
theorem B113287 : Blo 111784 113287 := bstep (se 1 (by rfl) ⟨84965, by rfl⟩ : syracuseStep 113287 = 169931) B169931
theorem B113295 : Blo 111784 113295 := bstep (se 1 (by rfl) ⟨84971, by rfl⟩ : syracuseStep 113295 = 169943) B169943
theorem B146063 : Blo 111784 146063 := bstep (se 1 (by rfl) ⟨109547, by rfl⟩ : syracuseStep 146063 = 219095) B219095
theorem B277177 : Blo 111784 277177 := bstep (se 2 (by rfl) ⟨103941, by rfl⟩ : syracuseStep 277177 = 207883) B207883
theorem B113339 : Blo 111784 113339 := bstep (se 1 (by rfl) ⟨85004, by rfl⟩ : syracuseStep 113339 = 170009) B170009
theorem B113415 : Blo 111784 113415 := bstep (se 1 (by rfl) ⟨85061, by rfl⟩ : syracuseStep 113415 = 170123) B170123
theorem B113423 : Blo 111784 113423 := bstep (se 1 (by rfl) ⟨85067, by rfl⟩ : syracuseStep 113423 = 170135) B170135
theorem B637733 : Blo 111784 637733 := bstep (se 4 (by rfl) ⟨59787, by rfl⟩ : syracuseStep 637733 = 119575) B119575
theorem B113467 : Blo 111784 113467 := bstep (se 1 (by rfl) ⟨85100, by rfl⟩ : syracuseStep 113467 = 170201) B170201
theorem B113543 : Blo 111784 113543 := bstep (se 1 (by rfl) ⟨85157, by rfl⟩ : syracuseStep 113543 = 170315) B170315
theorem B113551 : Blo 111784 113551 := bstep (se 1 (by rfl) ⟨85163, by rfl⟩ : syracuseStep 113551 = 170327) B170327
theorem B1915811 : Blo 111784 1915811 := bstep (se 1 (by rfl) ⟨1436858, by rfl⟩ : syracuseStep 1915811 = 2873717) B2873717
theorem B572345 : Blo 111784 572345 := bstep (se 2 (by rfl) ⟨214629, by rfl⟩ : syracuseStep 572345 = 429259) B429259
theorem B113595 : Blo 111784 113595 := bstep (se 1 (by rfl) ⟨85196, by rfl⟩ : syracuseStep 113595 = 170393) B170393
theorem B1358795 : Blo 111784 1358795 := bstep (se 1 (by rfl) ⟨1019096, by rfl⟩ : syracuseStep 1358795 = 2038193) B2038193
theorem B113671 : Blo 111784 113671 := bstep (se 1 (by rfl) ⟨85253, by rfl⟩ : syracuseStep 113671 = 170507) B170507
theorem B113679 : Blo 111784 113679 := bstep (se 1 (by rfl) ⟨85259, by rfl⟩ : syracuseStep 113679 = 170519) B170519
theorem B113723 : Blo 111784 113723 := bstep (se 1 (by rfl) ⟨85292, by rfl⟩ : syracuseStep 113723 = 170585) B170585
theorem B113799 : Blo 111784 113799 := bstep (se 1 (by rfl) ⟨85349, by rfl⟩ : syracuseStep 113799 = 170699) B170699
theorem B113807 : Blo 111784 113807 := bstep (se 1 (by rfl) ⟨85355, by rfl⟩ : syracuseStep 113807 = 170711) B170711
theorem B113851 : Blo 111784 113851 := bstep (se 1 (by rfl) ⟨85388, by rfl⟩ : syracuseStep 113851 = 170777) B170777
theorem B244937 : Blo 111784 244937 := bstep (se 2 (by rfl) ⟨91851, by rfl⟩ : syracuseStep 244937 = 183703) B183703
theorem B277705 : Blo 111784 277705 := bstep (se 2 (by rfl) ⟨104139, by rfl⟩ : syracuseStep 277705 = 208279) B208279
theorem B703745 : Blo 111784 703745 := bstep (se 2 (by rfl) ⟨263904, by rfl⟩ : syracuseStep 703745 = 527809) B527809
theorem B113927 : Blo 111784 113927 := bstep (se 1 (by rfl) ⟨85445, by rfl⟩ : syracuseStep 113927 = 170891) B170891
theorem B408847 : Blo 111784 408847 := bstep (se 1 (by rfl) ⟨306635, by rfl⟩ : syracuseStep 408847 = 613271) B613271
theorem B113935 : Blo 111784 113935 := bstep (se 1 (by rfl) ⟨85451, by rfl⟩ : syracuseStep 113935 = 170903) B170903
theorem B998689 : Blo 111784 998689 := bstep (se 2 (by rfl) ⟨374508, by rfl⟩ : syracuseStep 998689 = 749017) B749017
theorem B277793 : Blo 111784 277793 := bstep (se 2 (by rfl) ⟨104172, by rfl⟩ : syracuseStep 277793 = 208345) B208345
theorem B113979 : Blo 111784 113979 := bstep (se 1 (by rfl) ⟨85484, by rfl⟩ : syracuseStep 113979 = 170969) B170969
theorem B1555847 : Blo 111784 1555847 := bstep (se 1 (by rfl) ⟨1166885, by rfl⟩ : syracuseStep 1555847 = 2333771) B2333771
theorem B114055 : Blo 111784 114055 := bstep (se 1 (by rfl) ⟨85541, by rfl⟩ : syracuseStep 114055 = 171083) B171083
theorem B114063 : Blo 111784 114063 := bstep (se 1 (by rfl) ⟨85547, by rfl⟩ : syracuseStep 114063 = 171095) B171095
theorem B114107 : Blo 111784 114107 := bstep (se 1 (by rfl) ⟨85580, by rfl⟩ : syracuseStep 114107 = 171161) B171161
theorem B114183 : Blo 111784 114183 := bstep (se 1 (by rfl) ⟨85637, by rfl⟩ : syracuseStep 114183 = 171275) B171275
theorem B114191 : Blo 111784 114191 := bstep (se 1 (by rfl) ⟨85643, by rfl⟩ : syracuseStep 114191 = 171287) B171287
theorem B114235 : Blo 111784 114235 := bstep (se 1 (by rfl) ⟨85676, by rfl⟩ : syracuseStep 114235 = 171353) B171353
theorem B114311 : Blo 111784 114311 := bstep (se 1 (by rfl) ⟨85733, by rfl⟩ : syracuseStep 114311 = 171467) B171467
theorem B114319 : Blo 111784 114319 := bstep (se 1 (by rfl) ⟨85739, by rfl⟩ : syracuseStep 114319 = 171479) B171479
theorem B114363 : Blo 111784 114363 := bstep (se 1 (by rfl) ⟨85772, by rfl⟩ : syracuseStep 114363 = 171545) B171545
theorem B114439 : Blo 111784 114439 := bstep (se 1 (by rfl) ⟨85829, by rfl⟩ : syracuseStep 114439 = 171659) B171659
theorem B114447 : Blo 111784 114447 := bstep (se 1 (by rfl) ⟨85835, by rfl⟩ : syracuseStep 114447 = 171671) B171671
theorem B114491 : Blo 111784 114491 := bstep (se 1 (by rfl) ⟨85868, by rfl⟩ : syracuseStep 114491 = 171737) B171737
theorem B114567 : Blo 111784 114567 := bstep (se 1 (by rfl) ⟨85925, by rfl⟩ : syracuseStep 114567 = 171851) B171851
theorem B114575 : Blo 111784 114575 := bstep (se 1 (by rfl) ⟨85931, by rfl⟩ : syracuseStep 114575 = 171863) B171863
theorem B114619 : Blo 111784 114619 := bstep (se 1 (by rfl) ⟨85964, by rfl⟩ : syracuseStep 114619 = 171929) B171929
theorem B114695 : Blo 111784 114695 := bstep (se 1 (by rfl) ⟨86021, by rfl⟩ : syracuseStep 114695 = 172043) B172043
theorem B114703 : Blo 111784 114703 := bstep (se 1 (by rfl) ⟨86027, by rfl⟩ : syracuseStep 114703 = 172055) B172055
theorem B409643 : Blo 111784 409643 := bstep (se 1 (by rfl) ⟨307232, by rfl⟩ : syracuseStep 409643 = 614465) B614465
theorem B114747 : Blo 111784 114747 := bstep (se 1 (by rfl) ⟨86060, by rfl⟩ : syracuseStep 114747 = 172121) B172121
theorem B114823 : Blo 111784 114823 := bstep (se 1 (by rfl) ⟨86117, by rfl⟩ : syracuseStep 114823 = 172235) B172235
theorem B114831 : Blo 111784 114831 := bstep (se 1 (by rfl) ⟨86123, by rfl⟩ : syracuseStep 114831 = 172247) B172247
theorem B114875 : Blo 111784 114875 := bstep (se 1 (by rfl) ⟨86156, by rfl⟩ : syracuseStep 114875 = 172313) B172313
theorem B573641 : Blo 111784 573641 := bstep (se 2 (by rfl) ⟨215115, by rfl⟩ : syracuseStep 573641 = 430231) B430231
theorem B606437 : Blo 111784 606437 := bstep (se 4 (by rfl) ⟨56853, by rfl⟩ : syracuseStep 606437 = 113707) B113707
theorem B114951 : Blo 111784 114951 := bstep (se 1 (by rfl) ⟨86213, by rfl⟩ : syracuseStep 114951 = 172427) B172427
theorem B213263 : Blo 111784 213263 := bstep (se 1 (by rfl) ⟨159947, by rfl⟩ : syracuseStep 213263 = 319895) B319895
theorem B114959 : Blo 111784 114959 := bstep (se 1 (by rfl) ⟨86219, by rfl⟩ : syracuseStep 114959 = 172439) B172439
theorem B115003 : Blo 111784 115003 := bstep (se 1 (by rfl) ⟨86252, by rfl⟩ : syracuseStep 115003 = 172505) B172505
theorem B344407 : Blo 111784 344407 := bstep (se 1 (by rfl) ⟨258305, by rfl⟩ : syracuseStep 344407 = 516611) B516611
theorem B115079 : Blo 111784 115079 := bstep (se 1 (by rfl) ⟨86309, by rfl⟩ : syracuseStep 115079 = 172619) B172619
theorem B115087 : Blo 111784 115087 := bstep (se 1 (by rfl) ⟨86315, by rfl⟩ : syracuseStep 115087 = 172631) B172631
theorem B2474387 : Blo 111784 2474387 := bstep (se 1 (by rfl) ⟨1855790, by rfl⟩ : syracuseStep 2474387 = 3711581) B3711581
theorem B115131 : Blo 111784 115131 := bstep (se 1 (by rfl) ⟨86348, by rfl⟩ : syracuseStep 115131 = 172697) B172697
theorem B115207 : Blo 111784 115207 := bstep (se 1 (by rfl) ⟨86405, by rfl⟩ : syracuseStep 115207 = 172811) B172811
theorem B115215 : Blo 111784 115215 := bstep (se 1 (by rfl) ⟨86411, by rfl⟩ : syracuseStep 115215 = 172823) B172823
theorem B115259 : Blo 111784 115259 := bstep (se 1 (by rfl) ⟨86444, by rfl⟩ : syracuseStep 115259 = 172889) B172889
theorem B377405 : Blo 111784 377405 := bstep (se 3 (by rfl) ⟨70763, by rfl⟩ : syracuseStep 377405 = 141527) B141527
theorem B115335 : Blo 111784 115335 := bstep (se 1 (by rfl) ⟨86501, by rfl⟩ : syracuseStep 115335 = 173003) B173003
theorem B115343 : Blo 111784 115343 := bstep (se 1 (by rfl) ⟨86507, by rfl⟩ : syracuseStep 115343 = 173015) B173015
theorem B115387 : Blo 111784 115387 := bstep (se 1 (by rfl) ⟨86540, by rfl⟩ : syracuseStep 115387 = 173081) B173081
theorem B115463 : Blo 111784 115463 := bstep (se 1 (by rfl) ⟨86597, by rfl⟩ : syracuseStep 115463 = 173195) B173195
theorem B115471 : Blo 111784 115471 := bstep (se 1 (by rfl) ⟨86603, by rfl⟩ : syracuseStep 115471 = 173207) B173207
theorem B115515 : Blo 111784 115515 := bstep (se 1 (by rfl) ⟨86636, by rfl⟩ : syracuseStep 115515 = 173273) B173273
theorem B115591 : Blo 111784 115591 := bstep (se 1 (by rfl) ⟨86693, by rfl⟩ : syracuseStep 115591 = 173387) B173387
theorem B115599 : Blo 111784 115599 := bstep (se 1 (by rfl) ⟨86699, by rfl⟩ : syracuseStep 115599 = 173399) B173399
theorem B279443 : Blo 111784 279443 := bstep (se 1 (by rfl) ⟨209582, by rfl⟩ : syracuseStep 279443 = 419165) B419165
theorem B115643 : Blo 111784 115643 := bstep (se 1 (by rfl) ⟨86732, by rfl⟩ : syracuseStep 115643 = 173465) B173465
theorem B3195875 : Blo 111784 3195875 := bstep (se 1 (by rfl) ⟨2396906, by rfl⟩ : syracuseStep 3195875 = 4793813) B4793813
theorem B115719 : Blo 111784 115719 := bstep (se 1 (by rfl) ⟨86789, by rfl⟩ : syracuseStep 115719 = 173579) B173579
theorem B115727 : Blo 111784 115727 := bstep (se 1 (by rfl) ⟨86795, by rfl⟩ : syracuseStep 115727 = 173591) B173591
theorem B115771 : Blo 111784 115771 := bstep (se 1 (by rfl) ⟨86828, by rfl⟩ : syracuseStep 115771 = 173657) B173657
theorem B1885421 : Blo 111784 1885421 := bstep (se 3 (by rfl) ⟨353516, by rfl⟩ : syracuseStep 1885421 = 707033) B707033
theorem B1230173 : Blo 111784 1230173 := bstep (se 3 (by rfl) ⟨230657, by rfl⟩ : syracuseStep 1230173 = 461315) B461315
theorem B1099331 : Blo 111784 1099331 := bstep (se 1 (by rfl) ⟨824498, by rfl⟩ : syracuseStep 1099331 = 1648997) B1648997
theorem B542497 : Blo 111784 542497 := bstep (se 2 (by rfl) ⟨203436, by rfl⟩ : syracuseStep 542497 = 406873) B406873
theorem B214903 : Blo 111784 214903 := bstep (se 1 (by rfl) ⟨161177, by rfl⟩ : syracuseStep 214903 = 322355) B322355
theorem B444295 : Blo 111784 444295 := bstep (se 1 (by rfl) ⟨333221, by rfl⟩ : syracuseStep 444295 = 666443) B666443
theorem B378809 : Blo 111784 378809 := bstep (se 2 (by rfl) ⟨142053, by rfl⟩ : syracuseStep 378809 = 284107) B284107
theorem B2738123 : Blo 111784 2738123 := bstep (se 1 (by rfl) ⟨2053592, by rfl⟩ : syracuseStep 2738123 = 4107185) B4107185
theorem B411601 : Blo 111784 411601 := bstep (se 2 (by rfl) ⟨154350, by rfl⟩ : syracuseStep 411601 = 308701) B308701
theorem B936251 : Blo 111784 936251 := bstep (se 1 (by rfl) ⟨702188, by rfl⟩ : syracuseStep 936251 = 1404377) B1404377
theorem B182729 : Blo 111784 182729 := bstep (se 2 (by rfl) ⟨68523, by rfl⟩ : syracuseStep 182729 = 137047) B137047
theorem B379403 : Blo 111784 379403 := bstep (se 1 (by rfl) ⟨284552, by rfl⟩ : syracuseStep 379403 = 569105) B569105
theorem B379511 : Blo 111784 379511 := bstep (se 1 (by rfl) ⟨284633, by rfl⟩ : syracuseStep 379511 = 569267) B569267
theorem B183055 : Blo 111784 183055 := bstep (se 1 (by rfl) ⟨137291, by rfl⟩ : syracuseStep 183055 = 274583) B274583
theorem B380105 : Blo 111784 380105 := bstep (se 2 (by rfl) ⟨142539, by rfl⟩ : syracuseStep 380105 = 285079) B285079
theorem B609551 : Blo 111784 609551 := bstep (se 1 (by rfl) ⟨457163, by rfl⟩ : syracuseStep 609551 = 914327) B914327
theorem B413113 : Blo 111784 413113 := bstep (se 2 (by rfl) ⟨154917, by rfl⟩ : syracuseStep 413113 = 309835) B309835
theorem B216695 : Blo 111784 216695 := bstep (se 1 (by rfl) ⟨162521, by rfl⟩ : syracuseStep 216695 = 325043) B325043
theorem B740983 : Blo 111784 740983 := bstep (se 1 (by rfl) ⟨555737, by rfl⟩ : syracuseStep 740983 = 1111475) B1111475
theorem B806593 : Blo 111784 806593 := bstep (se 2 (by rfl) ⟨302472, by rfl⟩ : syracuseStep 806593 = 604945) B604945
theorem B216847 : Blo 111784 216847 := bstep (se 1 (by rfl) ⟨162635, by rfl⟩ : syracuseStep 216847 = 325271) B325271
theorem B151339 : Blo 111784 151339 := bstep (se 1 (by rfl) ⟨113504, by rfl⟩ : syracuseStep 151339 = 227009) B227009
theorem B380807 : Blo 111784 380807 := bstep (se 1 (by rfl) ⟨285605, by rfl⟩ : syracuseStep 380807 = 571211) B571211
theorem B643139 : Blo 111784 643139 := bstep (se 1 (by rfl) ⟨482354, by rfl⟩ : syracuseStep 643139 = 964709) B964709
theorem B217235 : Blo 111784 217235 := bstep (se 1 (by rfl) ⟨162926, by rfl⟩ : syracuseStep 217235 = 325853) B325853
theorem B381185 : Blo 111784 381185 := bstep (se 2 (by rfl) ⟨142944, by rfl⟩ : syracuseStep 381185 = 285889) B285889
theorem B3101075 : Blo 111784 3101075 := bstep (se 1 (by rfl) ⟨2325806, by rfl⟩ : syracuseStep 3101075 = 4651613) B4651613
theorem B479773 : Blo 111784 479773 := bstep (se 3 (by rfl) ⟨89957, by rfl⟩ : syracuseStep 479773 = 179915) B179915
theorem B119431 : Blo 111784 119431 := bstep (se 1 (by rfl) ⟨89573, by rfl⟩ : syracuseStep 119431 = 179147) B179147
theorem B479945 : Blo 111784 479945 := bstep (se 2 (by rfl) ⟨179979, by rfl⟩ : syracuseStep 479945 = 359959) B359959
theorem B152327 : Blo 111784 152327 := bstep (se 1 (by rfl) ⟨114245, by rfl⟩ : syracuseStep 152327 = 228491) B228491
theorem B414497 : Blo 111784 414497 := bstep (se 2 (by rfl) ⟨155436, by rfl⟩ : syracuseStep 414497 = 310873) B310873
theorem B381995 : Blo 111784 381995 := bstep (se 1 (by rfl) ⟨286496, by rfl⟩ : syracuseStep 381995 = 572993) B572993
theorem B283763 : Blo 111784 283763 := bstep (se 1 (by rfl) ⟨212822, by rfl⟩ : syracuseStep 283763 = 425645) B425645
theorem B218231 : Blo 111784 218231 := bstep (se 1 (by rfl) ⟨163673, by rfl⟩ : syracuseStep 218231 = 327347) B327347
theorem B283783 : Blo 111784 283783 := bstep (se 1 (by rfl) ⟨212837, by rfl⟩ : syracuseStep 283783 = 425675) B425675
theorem B284057 : Blo 111784 284057 := bstep (se 2 (by rfl) ⟨106521, by rfl⟩ : syracuseStep 284057 = 213043) B213043
theorem B120251 : Blo 111784 120251 := bstep (se 1 (by rfl) ⟨90188, by rfl⟩ : syracuseStep 120251 = 180377) B180377
theorem B218639 : Blo 111784 218639 := bstep (se 1 (by rfl) ⟨163979, by rfl⟩ : syracuseStep 218639 = 327959) B327959
theorem B284219 : Blo 111784 284219 := bstep (se 1 (by rfl) ⟨213164, by rfl⟩ : syracuseStep 284219 = 426329) B426329
theorem B284431 : Blo 111784 284431 := bstep (se 1 (by rfl) ⟨213323, by rfl⟩ : syracuseStep 284431 = 426647) B426647
theorem B251783 : Blo 111784 251783 := bstep (se 1 (by rfl) ⟨188837, by rfl⟩ : syracuseStep 251783 = 377675) B377675
theorem B579473 : Blo 111784 579473 := bstep (se 2 (by rfl) ⟨217302, by rfl⟩ : syracuseStep 579473 = 434605) B434605
theorem B284705 : Blo 111784 284705 := bstep (se 2 (by rfl) ⟨106764, by rfl⟩ : syracuseStep 284705 = 213529) B213529
theorem B219179 : Blo 111784 219179 := bstep (se 1 (by rfl) ⟨164384, by rfl⟩ : syracuseStep 219179 = 328769) B328769
theorem B251963 : Blo 111784 251963 := bstep (se 1 (by rfl) ⟨188972, by rfl⟩ : syracuseStep 251963 = 377945) B377945
theorem B252089 : Blo 111784 252089 := bstep (se 2 (by rfl) ⟨94533, by rfl⟩ : syracuseStep 252089 = 189067) B189067
theorem B612623 : Blo 111784 612623 := bstep (se 1 (by rfl) ⟨459467, by rfl⟩ : syracuseStep 612623 = 918935) B918935
theorem B383291 : Blo 111784 383291 := bstep (se 1 (by rfl) ⟨287468, by rfl⟩ : syracuseStep 383291 = 574937) B574937
theorem B645529 : Blo 111784 645529 := bstep (se 2 (by rfl) ⟨242073, by rfl⟩ : syracuseStep 645529 = 484147) B484147
theorem B252431 : Blo 111784 252431 := bstep (se 1 (by rfl) ⟨189323, by rfl⟩ : syracuseStep 252431 = 378647) B378647
theorem B252449 : Blo 111784 252449 := bstep (se 2 (by rfl) ⟨94668, by rfl⟩ : syracuseStep 252449 = 189337) B189337
theorem B481859 : Blo 111784 481859 := bstep (se 1 (by rfl) ⟨361394, by rfl⟩ : syracuseStep 481859 = 722789) B722789
theorem B383777 : Blo 111784 383777 := bstep (se 2 (by rfl) ⟨143916, by rfl⟩ : syracuseStep 383777 = 287833) B287833
theorem B1530661 : Blo 111784 1530661 := bstep (se 4 (by rfl) ⟨143499, by rfl⟩ : syracuseStep 1530661 = 286999) B286999
theorem B1104677 : Blo 111784 1104677 := bstep (se 4 (by rfl) ⟨103563, by rfl⟩ : syracuseStep 1104677 = 207127) B207127
theorem B1170251 : Blo 111784 1170251 := bstep (se 1 (by rfl) ⟨877688, by rfl⟩ : syracuseStep 1170251 = 1755377) B1755377
theorem B252791 : Blo 111784 252791 := bstep (se 1 (by rfl) ⟨189593, by rfl⟩ : syracuseStep 252791 = 379187) B379187
theorem B285707 : Blo 111784 285707 := bstep (se 1 (by rfl) ⟨214280, by rfl⟩ : syracuseStep 285707 = 428561) B428561
theorem B252971 : Blo 111784 252971 := bstep (se 1 (by rfl) ⟨189728, by rfl⟩ : syracuseStep 252971 = 379457) B379457
theorem B318779 : Blo 111784 318779 := bstep (se 1 (by rfl) ⟨239084, by rfl⟩ : syracuseStep 318779 = 478169) B478169
theorem B384371 : Blo 111784 384371 := bstep (se 1 (by rfl) ⟨288278, by rfl⟩ : syracuseStep 384371 = 576557) B576557
theorem B253331 : Blo 111784 253331 := bstep (se 1 (by rfl) ⟨189998, by rfl⟩ : syracuseStep 253331 = 379997) B379997
theorem B253385 : Blo 111784 253385 := bstep (se 2 (by rfl) ⟨95019, by rfl⟩ : syracuseStep 253385 = 190039) B190039
theorem B2154059 : Blo 111784 2154059 := bstep (se 1 (by rfl) ⟨1615544, by rfl⟩ : syracuseStep 2154059 = 3231089) B3231089
theorem B2055779 : Blo 111784 2055779 := bstep (se 1 (by rfl) ⟨1541834, by rfl⟩ : syracuseStep 2055779 = 3083669) B3083669
theorem B286355 : Blo 111784 286355 := bstep (se 1 (by rfl) ⟨214766, by rfl⟩ : syracuseStep 286355 = 429533) B429533
theorem B2612915 : Blo 111784 2612915 := bstep (se 1 (by rfl) ⟨1959686, by rfl⟩ : syracuseStep 2612915 = 3919373) B3919373
theorem B122639 : Blo 111784 122639 := bstep (se 1 (by rfl) ⟨91979, by rfl⟩ : syracuseStep 122639 = 183959) B183959
theorem B286649 : Blo 111784 286649 := bstep (se 2 (by rfl) ⟨107493, by rfl⟩ : syracuseStep 286649 = 214987) B214987
theorem B581579 : Blo 111784 581579 := bstep (se 1 (by rfl) ⟨436184, by rfl⟩ : syracuseStep 581579 = 872369) B872369
theorem B254087 : Blo 111784 254087 := bstep (se 1 (by rfl) ⟨190565, by rfl⟩ : syracuseStep 254087 = 381131) B381131
theorem B581903 : Blo 111784 581903 := bstep (se 1 (by rfl) ⟨436427, by rfl⟩ : syracuseStep 581903 = 872855) B872855
theorem B254267 : Blo 111784 254267 := bstep (se 1 (by rfl) ⟨190700, by rfl⟩ : syracuseStep 254267 = 381401) B381401
theorem B647513 : Blo 111784 647513 := bstep (se 2 (by rfl) ⟨242817, by rfl⟩ : syracuseStep 647513 = 485635) B485635
theorem B1171805 : Blo 111784 1171805 := bstep (se 3 (by rfl) ⟨219713, by rfl⟩ : syracuseStep 1171805 = 439427) B439427
theorem B254393 : Blo 111784 254393 := bstep (se 2 (by rfl) ⟨95397, by rfl⟩ : syracuseStep 254393 = 190795) B190795
theorem B287347 : Blo 111784 287347 := bstep (se 1 (by rfl) ⟨215510, by rfl⟩ : syracuseStep 287347 = 431021) B431021
theorem B189047 : Blo 111784 189047 := bstep (se 1 (by rfl) ⟨141785, by rfl⟩ : syracuseStep 189047 = 283571) B283571
theorem B221843 : Blo 111784 221843 := bstep (se 1 (by rfl) ⟨166382, by rfl⟩ : syracuseStep 221843 = 332765) B332765
theorem B287489 : Blo 111784 287489 := bstep (se 2 (by rfl) ⟨107808, by rfl⟩ : syracuseStep 287489 = 215617) B215617
theorem B254735 : Blo 111784 254735 := bstep (se 1 (by rfl) ⟨191051, by rfl⟩ : syracuseStep 254735 = 382103) B382103
theorem B254753 : Blo 111784 254753 := bstep (se 2 (by rfl) ⟨95532, by rfl⟩ : syracuseStep 254753 = 191065) B191065
theorem B189499 : Blo 111784 189499 := bstep (se 1 (by rfl) ⟨142124, by rfl⟩ : syracuseStep 189499 = 284249) B284249
theorem B255095 : Blo 111784 255095 := bstep (se 1 (by rfl) ⟨191321, by rfl⟩ : syracuseStep 255095 = 382643) B382643
theorem B189641 : Blo 111784 189641 := bstep (se 2 (by rfl) ⟨71115, by rfl⟩ : syracuseStep 189641 = 142231) B142231
theorem B287945 : Blo 111784 287945 := bstep (se 2 (by rfl) ⟨107979, by rfl⟩ : syracuseStep 287945 = 215959) B215959
theorem B255275 : Blo 111784 255275 := bstep (se 1 (by rfl) ⟨191456, by rfl⟩ : syracuseStep 255275 = 382913) B382913
theorem B288299 : Blo 111784 288299 := bstep (se 1 (by rfl) ⟨216224, by rfl⟩ : syracuseStep 288299 = 432449) B432449
theorem B255635 : Blo 111784 255635 := bstep (se 1 (by rfl) ⟨191726, by rfl⟩ : syracuseStep 255635 = 383453) B383453
theorem B583361 : Blo 111784 583361 := bstep (se 2 (by rfl) ⟨218760, by rfl⟩ : syracuseStep 583361 = 437521) B437521
theorem B255689 : Blo 111784 255689 := bstep (se 2 (by rfl) ⟨95883, by rfl⟩ : syracuseStep 255689 = 191767) B191767
theorem B190343 : Blo 111784 190343 := bstep (se 1 (by rfl) ⟨142757, by rfl⟩ : syracuseStep 190343 = 285515) B285515
theorem B386963 : Blo 111784 386963 := bstep (se 1 (by rfl) ⟨290222, by rfl⟩ : syracuseStep 386963 = 580445) B580445
theorem B2189429 : Blo 111784 2189429 := bstep (se 5 (by rfl) ⟨102629, by rfl⟩ : syracuseStep 2189429 = 205259) B205259
theorem B321671 : Blo 111784 321671 := bstep (se 1 (by rfl) ⟨241253, by rfl⟩ : syracuseStep 321671 = 482507) B482507
theorem B256391 : Blo 111784 256391 := bstep (se 1 (by rfl) ⟨192293, by rfl⟩ : syracuseStep 256391 = 384587) B384587
theorem B584081 : Blo 111784 584081 := bstep (se 2 (by rfl) ⟨219030, by rfl⟩ : syracuseStep 584081 = 438061) B438061
theorem B289291 : Blo 111784 289291 := bstep (se 1 (by rfl) ⟨216968, by rfl⟩ : syracuseStep 289291 = 433937) B433937
theorem B289295 : Blo 111784 289295 := bstep (se 1 (by rfl) ⟨216971, by rfl⟩ : syracuseStep 289295 = 433943) B433943
theorem B190991 : Blo 111784 190991 := bstep (se 1 (by rfl) ⟨143243, by rfl⟩ : syracuseStep 190991 = 286487) B286487
theorem B256571 : Blo 111784 256571 := bstep (se 1 (by rfl) ⟨192428, by rfl⟩ : syracuseStep 256571 = 384857) B384857
theorem B289433 : Blo 111784 289433 := bstep (se 2 (by rfl) ⟨108537, by rfl⟩ : syracuseStep 289433 = 217075) B217075
theorem B256697 : Blo 111784 256697 := bstep (se 2 (by rfl) ⟨96261, by rfl⟩ : syracuseStep 256697 = 192523) B192523
theorem B1108673 : Blo 111784 1108673 := bstep (se 2 (by rfl) ⟨415752, by rfl⟩ : syracuseStep 1108673 = 831505) B831505
theorem B289595 : Blo 111784 289595 := bstep (se 1 (by rfl) ⟨217196, by rfl⟩ : syracuseStep 289595 = 434393) B434393
theorem B584657 : Blo 111784 584657 := bstep (se 2 (by rfl) ⟨219246, by rfl⟩ : syracuseStep 584657 = 438493) B438493
theorem B125959 : Blo 111784 125959 := bstep (se 1 (by rfl) ⟨94469, by rfl⟩ : syracuseStep 125959 = 188939) B188939
theorem B257039 : Blo 111784 257039 := bstep (se 1 (by rfl) ⟨192779, by rfl⟩ : syracuseStep 257039 = 385559) B385559
theorem B1109015 : Blo 111784 1109015 := bstep (se 1 (by rfl) ⟨831761, by rfl⟩ : syracuseStep 1109015 = 1663523) B1663523
theorem B257057 : Blo 111784 257057 := bstep (se 2 (by rfl) ⟨96396, by rfl⟩ : syracuseStep 257057 = 192793) B192793
theorem B191531 : Blo 111784 191531 := bstep (se 1 (by rfl) ⟨143648, by rfl⟩ : syracuseStep 191531 = 287297) B287297
theorem B289939 : Blo 111784 289939 := bstep (se 1 (by rfl) ⟨217454, by rfl⟩ : syracuseStep 289939 = 434909) B434909
theorem B126139 : Blo 111784 126139 := bstep (se 1 (by rfl) ⟨94604, by rfl⟩ : syracuseStep 126139 = 189209) B189209
theorem B388367 : Blo 111784 388367 := bstep (se 1 (by rfl) ⟨291275, by rfl⟩ : syracuseStep 388367 = 582551) B582551
theorem B290081 : Blo 111784 290081 := bstep (se 2 (by rfl) ⟨108780, by rfl⟩ : syracuseStep 290081 = 217561) B217561
theorem B1240379 : Blo 111784 1240379 := bstep (se 1 (by rfl) ⟨930284, by rfl⟩ : syracuseStep 1240379 = 1860569) B1860569
theorem B257399 : Blo 111784 257399 := bstep (se 1 (by rfl) ⟨193049, by rfl⟩ : syracuseStep 257399 = 386099) B386099
theorem B191929 : Blo 111784 191929 := bstep (se 2 (by rfl) ⟨71973, by rfl⟩ : syracuseStep 191929 = 143947) B143947
theorem B388637 : Blo 111784 388637 := bstep (se 3 (by rfl) ⟨72869, by rfl⟩ : syracuseStep 388637 = 145739) B145739
theorem B257579 : Blo 111784 257579 := bstep (se 1 (by rfl) ⟨193184, by rfl⟩ : syracuseStep 257579 = 386369) B386369
theorem B552491 : Blo 111784 552491 := bstep (se 1 (by rfl) ⟨414368, by rfl⟩ : syracuseStep 552491 = 828737) B828737
theorem B519767 : Blo 111784 519767 := bstep (se 1 (by rfl) ⟨389825, by rfl⟩ : syracuseStep 519767 = 779651) B779651
theorem B126607 : Blo 111784 126607 := bstep (se 1 (by rfl) ⟨94955, by rfl⟩ : syracuseStep 126607 = 189911) B189911
theorem B2420375 : Blo 111784 2420375 := bstep (se 1 (by rfl) ⟨1815281, by rfl⟩ : syracuseStep 2420375 = 3630563) B3630563
theorem B1175233 : Blo 111784 1175233 := bstep (se 2 (by rfl) ⟨440712, by rfl⟩ : syracuseStep 1175233 = 881425) B881425
theorem B1928933 : Blo 111784 1928933 := bstep (se 4 (by rfl) ⟨180837, by rfl⟩ : syracuseStep 1928933 = 361675) B361675
theorem B3534637 : Blo 111784 3534637 := bstep (se 3 (by rfl) ⟨662744, by rfl⟩ : syracuseStep 3534637 = 1325489) B1325489
theorem B1830725 : Blo 111784 1830725 := bstep (se 4 (by rfl) ⟨171630, by rfl⟩ : syracuseStep 1830725 = 343261) B343261
theorem B257939 : Blo 111784 257939 := bstep (se 1 (by rfl) ⟨193454, by rfl⟩ : syracuseStep 257939 = 386909) B386909
theorem B257993 : Blo 111784 257993 := bstep (se 2 (by rfl) ⟨96747, by rfl⟩ : syracuseStep 257993 = 193495) B193495
theorem B323585 : Blo 111784 323585 := bstep (se 2 (by rfl) ⟨121344, by rfl⟩ : syracuseStep 323585 = 242689) B242689
theorem B5009501 : Blo 111784 5009501 := bstep (se 3 (by rfl) ⟨939281, by rfl⟩ : syracuseStep 5009501 = 1878563) B1878563
theorem B192631 : Blo 111784 192631 := bstep (se 1 (by rfl) ⟨144473, by rfl⟩ : syracuseStep 192631 = 288947) B288947
theorem B127111 : Blo 111784 127111 := bstep (se 1 (by rfl) ⟨95333, by rfl⟩ : syracuseStep 127111 = 190667) B190667
theorem B291073 : Blo 111784 291073 := bstep (se 2 (by rfl) ⟨109152, by rfl⟩ : syracuseStep 291073 = 218305) B218305
theorem B127291 : Blo 111784 127291 := bstep (se 1 (by rfl) ⟨95468, by rfl⟩ : syracuseStep 127291 = 190937) B190937
theorem B192827 : Blo 111784 192827 := bstep (se 1 (by rfl) ⟨144620, by rfl⟩ : syracuseStep 192827 = 289241) B289241
theorem B651635 : Blo 111784 651635 := bstep (se 1 (by rfl) ⟨488726, by rfl⟩ : syracuseStep 651635 = 977453) B977453
theorem B324155 : Blo 111784 324155 := bstep (se 1 (by rfl) ⟨243116, by rfl⟩ : syracuseStep 324155 = 486233) B486233
theorem B160375 : Blo 111784 160375 := bstep (se 1 (by rfl) ⟨120281, by rfl⟩ : syracuseStep 160375 = 240563) B240563
theorem B258695 : Blo 111784 258695 := bstep (se 1 (by rfl) ⟨194021, by rfl⟩ : syracuseStep 258695 = 388043) B388043
theorem B193225 : Blo 111784 193225 := bstep (se 2 (by rfl) ⟨72459, by rfl⟩ : syracuseStep 193225 = 144919) B144919
theorem B127759 : Blo 111784 127759 := bstep (se 1 (by rfl) ⟨95819, by rfl⟩ : syracuseStep 127759 = 191639) B191639
theorem B1438499 : Blo 111784 1438499 := bstep (se 1 (by rfl) ⟨1078874, by rfl⟩ : syracuseStep 1438499 = 2157749) B2157749
theorem B324395 : Blo 111784 324395 := bstep (se 1 (by rfl) ⟨243296, by rfl⟩ : syracuseStep 324395 = 486593) B486593
theorem B389947 : Blo 111784 389947 := bstep (se 1 (by rfl) ⟨292460, by rfl⟩ : syracuseStep 389947 = 584921) B584921
theorem B258875 : Blo 111784 258875 := bstep (se 1 (by rfl) ⟨194156, by rfl⟩ : syracuseStep 258875 = 388313) B388313
theorem B291671 : Blo 111784 291671 := bstep (se 1 (by rfl) ⟨218753, by rfl⟩ : syracuseStep 291671 = 437507) B437507
theorem B553817 : Blo 111784 553817 := bstep (se 2 (by rfl) ⟨207681, by rfl⟩ : syracuseStep 553817 = 415363) B415363
theorem B390041 : Blo 111784 390041 := bstep (se 2 (by rfl) ⟨146265, by rfl⟩ : syracuseStep 390041 = 292531) B292531
theorem B259001 : Blo 111784 259001 := bstep (se 2 (by rfl) ⟨97125, by rfl⟩ : syracuseStep 259001 = 194251) B194251
theorem B160699 : Blo 111784 160699 := bstep (se 1 (by rfl) ⟨120524, by rfl⟩ : syracuseStep 160699 = 241049) B241049
theorem B291883 : Blo 111784 291883 := bstep (se 1 (by rfl) ⟨218912, by rfl⟩ : syracuseStep 291883 = 437825) B437825
theorem B292025 : Blo 111784 292025 := bstep (se 2 (by rfl) ⟨109509, by rfl⟩ : syracuseStep 292025 = 219019) B219019
theorem B128263 : Blo 111784 128263 := bstep (se 1 (by rfl) ⟨96197, by rfl⟩ : syracuseStep 128263 = 192395) B192395
theorem B259343 : Blo 111784 259343 := bstep (se 1 (by rfl) ⟨194507, by rfl⟩ : syracuseStep 259343 = 389015) B389015
theorem B259361 : Blo 111784 259361 := bstep (se 2 (by rfl) ⟨97260, by rfl⟩ : syracuseStep 259361 = 194521) B194521
theorem B193927 : Blo 111784 193927 := bstep (se 1 (by rfl) ⟨145445, by rfl⟩ : syracuseStep 193927 = 290891) B290891
theorem B128443 : Blo 111784 128443 := bstep (se 1 (by rfl) ⟨96332, by rfl⟩ : syracuseStep 128443 = 192665) B192665
theorem B390743 : Blo 111784 390743 := bstep (se 1 (by rfl) ⟨293057, by rfl⟩ : syracuseStep 390743 = 586115) B586115
theorem B849527 : Blo 111784 849527 := bstep (se 1 (by rfl) ⟨637145, by rfl⟩ : syracuseStep 849527 = 1274291) B1274291
theorem B194167 : Blo 111784 194167 := bstep (se 1 (by rfl) ⟨145625, by rfl⟩ : syracuseStep 194167 = 291251) B291251
theorem B259703 : Blo 111784 259703 := bstep (se 1 (by rfl) ⟨194777, by rfl⟩ : syracuseStep 259703 = 389555) B389555
theorem B653093 : Blo 111784 653093 := bstep (se 4 (by rfl) ⟨61227, by rfl⟩ : syracuseStep 653093 = 122455) B122455
theorem B259883 : Blo 111784 259883 := bstep (se 1 (by rfl) ⟨194912, by rfl⟩ : syracuseStep 259883 = 389825) B389825
theorem B128911 : Blo 111784 128911 := bstep (se 1 (by rfl) ⟨96683, by rfl⟩ : syracuseStep 128911 = 193367) B193367
theorem B260111 : Blo 111784 260111 := bstep (se 1 (by rfl) ⟨195083, by rfl⟩ : syracuseStep 260111 = 390167) B390167
theorem B194575 : Blo 111784 194575 := bstep (se 1 (by rfl) ⟨145931, by rfl⟩ : syracuseStep 194575 = 291863) B291863
theorem B2193425 : Blo 111784 2193425 := bstep (se 2 (by rfl) ⟨822534, by rfl⟩ : syracuseStep 2193425 = 1645069) B1645069
theorem B2652277 : Blo 111784 2652277 := bstep (se 5 (by rfl) ⟨124325, by rfl⟩ : syracuseStep 2652277 = 248651) B248651
theorem B260243 : Blo 111784 260243 := bstep (se 1 (by rfl) ⟨195182, by rfl⟩ : syracuseStep 260243 = 390365) B390365
theorem B293017 : Blo 111784 293017 := bstep (se 2 (by rfl) ⟨109881, by rfl⟩ : syracuseStep 293017 = 219763) B219763
theorem B260297 : Blo 111784 260297 := bstep (se 2 (by rfl) ⟨97611, by rfl⟩ : syracuseStep 260297 = 195223) B195223
theorem B129415 : Blo 111784 129415 := bstep (se 1 (by rfl) ⟨97061, by rfl⟩ : syracuseStep 129415 = 194123) B194123
theorem B653777 : Blo 111784 653777 := bstep (se 2 (by rfl) ⟨245166, by rfl⟩ : syracuseStep 653777 = 490333) B490333
theorem B195115 : Blo 111784 195115 := bstep (se 1 (by rfl) ⟨146336, by rfl⟩ : syracuseStep 195115 = 292673) B292673
theorem B129595 : Blo 111784 129595 := bstep (se 1 (by rfl) ⟨97196, by rfl⟩ : syracuseStep 129595 = 194393) B194393
theorem B850499 : Blo 111784 850499 := bstep (se 1 (by rfl) ⟨637874, by rfl⟩ : syracuseStep 850499 = 1275749) B1275749
theorem B621229 : Blo 111784 621229 := bstep (se 3 (by rfl) ⟨116480, by rfl⟩ : syracuseStep 621229 = 232961) B232961
theorem B195257 : Blo 111784 195257 := bstep (se 2 (by rfl) ⟨73221, by rfl⟩ : syracuseStep 195257 = 146443) B146443
theorem B359113 : Blo 111784 359113 := bstep (se 2 (by rfl) ⟨134667, by rfl⟩ : syracuseStep 359113 = 269335) B269335
theorem B654095 : Blo 111784 654095 := bstep (se 1 (by rfl) ⟨490571, by rfl⟩ : syracuseStep 654095 = 981143) B981143
theorem B130063 : Blo 111784 130063 := bstep (se 1 (by rfl) ⟨97547, by rfl⟩ : syracuseStep 130063 = 195095) B195095
theorem B163063 : Blo 111784 163063 := bstep (se 1 (by rfl) ⟨122297, by rfl⟩ : syracuseStep 163063 = 244595) B244595
theorem B195959 : Blo 111784 195959 := bstep (se 1 (by rfl) ⟨146969, by rfl⟩ : syracuseStep 195959 = 293939) B293939
theorem B130567 : Blo 111784 130567 := bstep (se 1 (by rfl) ⟨97925, by rfl⟩ : syracuseStep 130567 = 195851) B195851
theorem B163387 : Blo 111784 163387 := bstep (se 1 (by rfl) ⟨122540, by rfl⟩ : syracuseStep 163387 = 245081) B245081
theorem B425843 : Blo 111784 425843 := bstep (se 1 (by rfl) ⟨319382, by rfl⟩ : syracuseStep 425843 = 638765) B638765
theorem B1868093 : Blo 111784 1868093 := bstep (se 3 (by rfl) ⟨350267, by rfl⟩ : syracuseStep 1868093 = 700535) B700535
theorem B459209 : Blo 111784 459209 := bstep (se 2 (by rfl) ⟨172203, by rfl⟩ : syracuseStep 459209 = 344407) B344407
theorem B2130583 : Blo 111784 2130583 := bstep (se 1 (by rfl) ⟨1597937, by rfl⟩ : syracuseStep 2130583 = 3195875) B3195875
theorem B328555 : Blo 111784 328555 := bstep (se 1 (by rfl) ⟨246416, by rfl⟩ : syracuseStep 328555 = 492833) B492833
theorem B820115 : Blo 111784 820115 := bstep (se 1 (by rfl) ⟨615086, by rfl⟩ : syracuseStep 820115 = 1230173) B1230173
theorem B328711 : Blo 111784 328711 := bstep (se 1 (by rfl) ⟨246533, by rfl⟩ : syracuseStep 328711 = 493067) B493067
theorem B197711 : Blo 111784 197711 := bstep (se 1 (by rfl) ⟨148283, by rfl⟩ : syracuseStep 197711 = 296567) B296567
theorem B362009 : Blo 111784 362009 := bstep (se 2 (by rfl) ⟨135753, by rfl⟩ : syracuseStep 362009 = 271507) B271507
theorem B624167 : Blo 111784 624167 := bstep (se 1 (by rfl) ⟨468125, by rfl⟩ : syracuseStep 624167 = 936251) B936251
theorem B723329 : Blo 111784 723329 := bstep (se 2 (by rfl) ⟨271248, by rfl⟩ : syracuseStep 723329 = 542497) B542497
theorem B592393 : Blo 111784 592393 := bstep (se 2 (by rfl) ⟨222147, by rfl⟩ : syracuseStep 592393 = 444295) B444295
theorem B428759 : Blo 111784 428759 := bstep (se 1 (by rfl) ⟨321569, by rfl⟩ : syracuseStep 428759 = 643139) B643139
theorem B2067383 : Blo 111784 2067383 := bstep (se 1 (by rfl) ⟨1550537, by rfl⟩ : syracuseStep 2067383 = 3101075) B3101075
theorem B363521 : Blo 111784 363521 := bstep (se 2 (by rfl) ⟨136320, by rfl⟩ : syracuseStep 363521 = 272641) B272641
theorem B527741 : Blo 111784 527741 := bstep (se 3 (by rfl) ⟨98951, by rfl⟩ : syracuseStep 527741 = 197903) B197903
theorem B462547 : Blo 111784 462547 := bstep (se 1 (by rfl) ⟨346910, by rfl⟩ : syracuseStep 462547 = 693821) B693821
theorem B1314593 : Blo 111784 1314593 := bstep (se 2 (by rfl) ⟨492972, by rfl⟩ : syracuseStep 1314593 = 985945) B985945
theorem B167855 : Blo 111784 167855 := bstep (se 1 (by rfl) ⟨125891, by rfl⟩ : syracuseStep 167855 = 251783) B251783
theorem B167945 : Blo 111784 167945 := bstep (se 2 (by rfl) ⟨62979, by rfl⟩ : syracuseStep 167945 = 125959) B125959
theorem B167975 : Blo 111784 167975 := bstep (se 1 (by rfl) ⟨125981, by rfl⟩ : syracuseStep 167975 = 251963) B251963
theorem B168059 : Blo 111784 168059 := bstep (se 1 (by rfl) ⟨126044, by rfl⟩ : syracuseStep 168059 = 252089) B252089
theorem B168185 : Blo 111784 168185 := bstep (se 2 (by rfl) ⟨63069, by rfl⟩ : syracuseStep 168185 = 126139) B126139
theorem B856331 : Blo 111784 856331 := bstep (se 1 (by rfl) ⟨642248, by rfl⟩ : syracuseStep 856331 = 1284497) B1284497
theorem B168287 : Blo 111784 168287 := bstep (se 1 (by rfl) ⟨126215, by rfl⟩ : syracuseStep 168287 = 252431) B252431
theorem B168299 : Blo 111784 168299 := bstep (se 1 (by rfl) ⟨126224, by rfl⟩ : syracuseStep 168299 = 252449) B252449
theorem B168527 : Blo 111784 168527 := bstep (se 1 (by rfl) ⟨126395, by rfl⟩ : syracuseStep 168527 = 252791) B252791
theorem B168647 : Blo 111784 168647 := bstep (se 1 (by rfl) ⟨126485, by rfl⟩ : syracuseStep 168647 = 252971) B252971
theorem B987977 : Blo 111784 987977 := bstep (se 2 (by rfl) ⟨370491, by rfl⟩ : syracuseStep 987977 = 740983) B740983
theorem B168809 : Blo 111784 168809 := bstep (se 2 (by rfl) ⟨63303, by rfl⟩ : syracuseStep 168809 = 126607) B126607
theorem B168887 : Blo 111784 168887 := bstep (se 1 (by rfl) ⟨126665, by rfl⟩ : syracuseStep 168887 = 253331) B253331
theorem B168923 : Blo 111784 168923 := bstep (se 1 (by rfl) ⟨126692, by rfl⟩ : syracuseStep 168923 = 253385) B253385
theorem B201785 : Blo 111784 201785 := bstep (se 2 (by rfl) ⟨75669, by rfl⟩ : syracuseStep 201785 = 151339) B151339
theorem B1741943 : Blo 111784 1741943 := bstep (se 1 (by rfl) ⟨1306457, by rfl⟩ : syracuseStep 1741943 = 2612915) B2612915
theorem B365725 : Blo 111784 365725 := bstep (se 3 (by rfl) ⟨68573, by rfl⟩ : syracuseStep 365725 = 137147) B137147
theorem B693629 : Blo 111784 693629 := bstep (se 3 (by rfl) ⟨130055, by rfl⟩ : syracuseStep 693629 = 260111) B260111
theorem B169391 : Blo 111784 169391 := bstep (se 1 (by rfl) ⟨127043, by rfl⟩ : syracuseStep 169391 = 254087) B254087
theorem B202247 : Blo 111784 202247 := bstep (se 1 (by rfl) ⟨151685, by rfl⟩ : syracuseStep 202247 = 303371) B303371
theorem B169481 : Blo 111784 169481 := bstep (se 2 (by rfl) ⟨63555, by rfl⟩ : syracuseStep 169481 = 127111) B127111
theorem B169511 : Blo 111784 169511 := bstep (se 1 (by rfl) ⟨127133, by rfl⟩ : syracuseStep 169511 = 254267) B254267
theorem B431675 : Blo 111784 431675 := bstep (se 1 (by rfl) ⟨323756, by rfl⟩ : syracuseStep 431675 = 647513) B647513
theorem B169595 : Blo 111784 169595 := bstep (se 1 (by rfl) ⟨127196, by rfl⟩ : syracuseStep 169595 = 254393) B254393
theorem B857789 : Blo 111784 857789 := bstep (se 3 (by rfl) ⟨160835, by rfl⟩ : syracuseStep 857789 = 321671) B321671
theorem B169721 : Blo 111784 169721 := bstep (se 2 (by rfl) ⟨63645, by rfl⟩ : syracuseStep 169721 = 127291) B127291
theorem B169823 : Blo 111784 169823 := bstep (se 1 (by rfl) ⟨127367, by rfl⟩ : syracuseStep 169823 = 254735) B254735
theorem B169835 : Blo 111784 169835 := bstep (se 1 (by rfl) ⟨127376, by rfl⟩ : syracuseStep 169835 = 254753) B254753
theorem B170063 : Blo 111784 170063 := bstep (se 1 (by rfl) ⟨127547, by rfl⟩ : syracuseStep 170063 = 255095) B255095
theorem B858275 : Blo 111784 858275 := bstep (se 1 (by rfl) ⟨643706, by rfl⟩ : syracuseStep 858275 = 1287413) B1287413
theorem B170183 : Blo 111784 170183 := bstep (se 1 (by rfl) ⟨127637, by rfl⟩ : syracuseStep 170183 = 255275) B255275
theorem B170345 : Blo 111784 170345 := bstep (se 2 (by rfl) ⟨63879, by rfl⟩ : syracuseStep 170345 = 127759) B127759
theorem B170423 : Blo 111784 170423 := bstep (se 1 (by rfl) ⟨127817, by rfl⟩ : syracuseStep 170423 = 255635) B255635
theorem B170459 : Blo 111784 170459 := bstep (se 1 (by rfl) ⟨127844, by rfl⟩ : syracuseStep 170459 = 255689) B255689
theorem B170927 : Blo 111784 170927 := bstep (se 1 (by rfl) ⟨128195, by rfl⟩ : syracuseStep 170927 = 256391) B256391
theorem B171017 : Blo 111784 171017 := bstep (se 2 (by rfl) ⟨64131, by rfl⟩ : syracuseStep 171017 = 128263) B128263
theorem B171047 : Blo 111784 171047 := bstep (se 1 (by rfl) ⟨128285, by rfl⟩ : syracuseStep 171047 = 256571) B256571
theorem B171131 : Blo 111784 171131 := bstep (se 1 (by rfl) ⟨128348, by rfl⟩ : syracuseStep 171131 = 256697) B256697
theorem B171257 : Blo 111784 171257 := bstep (se 2 (by rfl) ⟨64221, by rfl⟩ : syracuseStep 171257 = 128443) B128443
theorem B171359 : Blo 111784 171359 := bstep (se 1 (by rfl) ⟨128519, by rfl⟩ : syracuseStep 171359 = 257039) B257039
theorem B171371 : Blo 111784 171371 := bstep (se 1 (by rfl) ⟨128528, by rfl⟩ : syracuseStep 171371 = 257057) B257057
theorem B826919 : Blo 111784 826919 := bstep (se 1 (by rfl) ⟨620189, by rfl⟩ : syracuseStep 826919 = 1240379) B1240379
theorem B138791 : Blo 111784 138791 := bstep (se 1 (by rfl) ⟨104093, by rfl⟩ : syracuseStep 138791 = 208187) B208187
theorem B171599 : Blo 111784 171599 := bstep (se 1 (by rfl) ⟨128699, by rfl⟩ : syracuseStep 171599 = 257399) B257399
theorem B171719 : Blo 111784 171719 := bstep (se 1 (by rfl) ⟨128789, by rfl⟩ : syracuseStep 171719 = 257579) B257579
theorem B368327 : Blo 111784 368327 := bstep (se 1 (by rfl) ⟨276245, by rfl⟩ : syracuseStep 368327 = 552491) B552491
theorem B1285955 : Blo 111784 1285955 := bstep (se 1 (by rfl) ⟨964466, by rfl⟩ : syracuseStep 1285955 = 1928933) B1928933
theorem B171881 : Blo 111784 171881 := bstep (se 2 (by rfl) ⟨64455, by rfl⟩ : syracuseStep 171881 = 128911) B128911
theorem B1220483 : Blo 111784 1220483 := bstep (se 1 (by rfl) ⟨915362, by rfl⟩ : syracuseStep 1220483 = 1830725) B1830725
theorem B171959 : Blo 111784 171959 := bstep (se 1 (by rfl) ⟨128969, by rfl⟩ : syracuseStep 171959 = 257939) B257939
theorem B171995 : Blo 111784 171995 := bstep (se 1 (by rfl) ⟨128996, by rfl⟩ : syracuseStep 171995 = 257993) B257993
theorem B729091 : Blo 111784 729091 := bstep (se 1 (by rfl) ⟨546818, by rfl⟩ : syracuseStep 729091 = 1093637) B1093637
theorem B434423 : Blo 111784 434423 := bstep (se 1 (by rfl) ⟨325817, by rfl⟩ : syracuseStep 434423 = 651635) B651635
theorem B172463 : Blo 111784 172463 := bstep (se 1 (by rfl) ⟨129347, by rfl⟩ : syracuseStep 172463 = 258695) B258695
theorem B172553 : Blo 111784 172553 := bstep (se 2 (by rfl) ⟨64707, by rfl⟩ : syracuseStep 172553 = 129415) B129415
theorem B958999 : Blo 111784 958999 := bstep (se 1 (by rfl) ⟨719249, by rfl⟩ : syracuseStep 958999 = 1438499) B1438499
theorem B860705 : Blo 111784 860705 := bstep (se 2 (by rfl) ⟨322764, by rfl⟩ : syracuseStep 860705 = 645529) B645529
theorem B172583 : Blo 111784 172583 := bstep (se 1 (by rfl) ⟨129437, by rfl⟩ : syracuseStep 172583 = 258875) B258875
theorem B369211 : Blo 111784 369211 := bstep (se 1 (by rfl) ⟨276908, by rfl⟩ : syracuseStep 369211 = 553817) B553817
theorem B172667 : Blo 111784 172667 := bstep (se 1 (by rfl) ⟨129500, by rfl⟩ : syracuseStep 172667 = 259001) B259001
theorem B172793 : Blo 111784 172793 := bstep (se 2 (by rfl) ⟨64797, by rfl⟩ : syracuseStep 172793 = 129595) B129595
theorem B172895 : Blo 111784 172895 := bstep (se 1 (by rfl) ⟨129671, by rfl⟩ : syracuseStep 172895 = 259343) B259343
theorem B172907 : Blo 111784 172907 := bstep (se 1 (by rfl) ⟨129680, by rfl⟩ : syracuseStep 172907 = 259361) B259361
theorem B828305 : Blo 111784 828305 := bstep (se 2 (by rfl) ⟨310614, by rfl⟩ : syracuseStep 828305 = 621229) B621229
theorem B369569 : Blo 111784 369569 := bstep (se 2 (by rfl) ⟨138588, by rfl⟩ : syracuseStep 369569 = 277177) B277177
theorem B205751 : Blo 111784 205751 := bstep (se 1 (by rfl) ⟨154313, by rfl⟩ : syracuseStep 205751 = 308627) B308627
theorem B2040881 : Blo 111784 2040881 := bstep (se 2 (by rfl) ⟨765330, by rfl⟩ : syracuseStep 2040881 = 1530661) B1530661
theorem B566351 : Blo 111784 566351 := bstep (se 1 (by rfl) ⟨424763, by rfl⟩ : syracuseStep 566351 = 849527) B849527
theorem B173135 : Blo 111784 173135 := bstep (se 1 (by rfl) ⟨129851, by rfl⟩ : syracuseStep 173135 = 259703) B259703
theorem B435395 : Blo 111784 435395 := bstep (se 1 (by rfl) ⟨326546, by rfl⟩ : syracuseStep 435395 = 653093) B653093
theorem B173255 : Blo 111784 173255 := bstep (se 1 (by rfl) ⟨129941, by rfl⟩ : syracuseStep 173255 = 259883) B259883
theorem B173417 : Blo 111784 173417 := bstep (se 2 (by rfl) ⟨65031, by rfl⟩ : syracuseStep 173417 = 130063) B130063
theorem B173495 : Blo 111784 173495 := bstep (se 1 (by rfl) ⟨130121, by rfl⟩ : syracuseStep 173495 = 260243) B260243
theorem B173531 : Blo 111784 173531 := bstep (se 1 (by rfl) ⟨130148, by rfl⟩ : syracuseStep 173531 = 260297) B260297
theorem B370273 : Blo 111784 370273 := bstep (se 2 (by rfl) ⟨138852, by rfl⟩ : syracuseStep 370273 = 277705) B277705
theorem B435851 : Blo 111784 435851 := bstep (se 1 (by rfl) ⟨326888, by rfl⟩ : syracuseStep 435851 = 653777) B653777
theorem B140999 : Blo 111784 140999 := bstep (se 1 (by rfl) ⟨105749, by rfl⟩ : syracuseStep 140999 = 211499) B211499
theorem B566999 : Blo 111784 566999 := bstep (se 1 (by rfl) ⟨425249, by rfl⟩ : syracuseStep 566999 = 850499) B850499
theorem B436063 : Blo 111784 436063 := bstep (se 1 (by rfl) ⟨327047, by rfl⟩ : syracuseStep 436063 = 654095) B654095
theorem B174089 : Blo 111784 174089 := bstep (se 2 (by rfl) ⟨65283, by rfl⟩ : syracuseStep 174089 = 130567) B130567
theorem B469163 : Blo 111784 469163 := bstep (se 1 (by rfl) ⟨351872, by rfl⟩ : syracuseStep 469163 = 703745) B703745
theorem B273095 : Blo 111784 273095 := bstep (se 1 (by rfl) ⟨204821, by rfl⟩ : syracuseStep 273095 = 409643) B409643
theorem B437021 : Blo 111784 437021 := bstep (se 3 (by rfl) ⟨81941, by rfl⟩ : syracuseStep 437021 = 163883) B163883
theorem B437035 : Blo 111784 437035 := bstep (se 1 (by rfl) ⟨327776, by rfl⟩ : syracuseStep 437035 = 655553) B655553
theorem B404291 : Blo 111784 404291 := bstep (se 1 (by rfl) ⟨303218, by rfl⟩ : syracuseStep 404291 = 606437) B606437
theorem B142175 : Blo 111784 142175 := bstep (se 1 (by rfl) ⟨106631, by rfl⟩ : syracuseStep 142175 = 213263) B213263
theorem B1551251 : Blo 111784 1551251 := bstep (se 1 (by rfl) ⟨1163438, by rfl⟩ : syracuseStep 1551251 = 2326877) B2326877
theorem B1649591 : Blo 111784 1649591 := bstep (se 1 (by rfl) ⟨1237193, by rfl⟩ : syracuseStep 1649591 = 2474387) B2474387
theorem B3124813 : Blo 111784 3124813 := bstep (se 3 (by rfl) ⟨585902, by rfl⟩ : syracuseStep 3124813 = 1171805) B1171805
theorem B732887 : Blo 111784 732887 := bstep (se 1 (by rfl) ⟨549665, by rfl⟩ : syracuseStep 732887 = 1099331) B1099331
theorem B1093409 : Blo 111784 1093409 := bstep (se 2 (by rfl) ⟨410028, by rfl⟩ : syracuseStep 1093409 = 820057) B820057
theorem B438443 : Blo 111784 438443 := bstep (se 1 (by rfl) ⟨328832, by rfl⟩ : syracuseStep 438443 = 657665) B657665
theorem B569915 : Blo 111784 569915 := bstep (se 1 (by rfl) ⟨427436, by rfl⟩ : syracuseStep 569915 = 854873) B854873
theorem B406205 : Blo 111784 406205 := bstep (se 3 (by rfl) ⟨76163, by rfl⟩ : syracuseStep 406205 = 152327) B152327
theorem B406367 : Blo 111784 406367 := bstep (se 1 (by rfl) ⟨304775, by rfl⟩ : syracuseStep 406367 = 609551) B609551
theorem B308063 : Blo 111784 308063 := bstep (se 1 (by rfl) ⟨231047, by rfl⟩ : syracuseStep 308063 = 462095) B462095
theorem B111791 : Blo 111784 111791 := bstep (se 1 (by rfl) ⟨83843, by rfl⟩ : syracuseStep 111791 = 167687) B167687
theorem B570563 : Blo 111784 570563 := bstep (se 1 (by rfl) ⟨427922, by rfl⟩ : syracuseStep 570563 = 855845) B855845
theorem B111815 : Blo 111784 111815 := bstep (se 1 (by rfl) ⟨83861, by rfl⟩ : syracuseStep 111815 = 167723) B167723
theorem B111835 : Blo 111784 111835 := bstep (se 1 (by rfl) ⟨83876, by rfl⟩ : syracuseStep 111835 = 167753) B167753
theorem B111911 : Blo 111784 111911 := bstep (se 1 (by rfl) ⟨83933, by rfl⟩ : syracuseStep 111911 = 167867) B167867
theorem B111951 : Blo 111784 111951 := bstep (se 1 (by rfl) ⟨83963, by rfl⟩ : syracuseStep 111951 = 167927) B167927
theorem B111967 : Blo 111784 111967 := bstep (se 1 (by rfl) ⟨83975, by rfl⟩ : syracuseStep 111967 = 167951) B167951
theorem B111995 : Blo 111784 111995 := bstep (se 1 (by rfl) ⟨83996, by rfl⟩ : syracuseStep 111995 = 167993) B167993
theorem B112047 : Blo 111784 112047 := bstep (se 1 (by rfl) ⟨84035, by rfl⟩ : syracuseStep 112047 = 168071) B168071
theorem B144823 : Blo 111784 144823 := bstep (se 1 (by rfl) ⟨108617, by rfl⟩ : syracuseStep 144823 = 217235) B217235
theorem B112071 : Blo 111784 112071 := bstep (se 1 (by rfl) ⟨84053, by rfl⟩ : syracuseStep 112071 = 168107) B168107
theorem B112091 : Blo 111784 112091 := bstep (se 1 (by rfl) ⟨84068, by rfl⟩ : syracuseStep 112091 = 168137) B168137
theorem B1291787 : Blo 111784 1291787 := bstep (se 1 (by rfl) ⟨968840, by rfl⟩ : syracuseStep 1291787 = 1937681) B1937681
theorem B112167 : Blo 111784 112167 := bstep (se 1 (by rfl) ⟨84125, by rfl⟩ : syracuseStep 112167 = 168251) B168251
theorem B112207 : Blo 111784 112207 := bstep (se 1 (by rfl) ⟨84155, by rfl⟩ : syracuseStep 112207 = 168311) B168311
theorem B112223 : Blo 111784 112223 := bstep (se 1 (by rfl) ⟨84167, by rfl⟩ : syracuseStep 112223 = 168335) B168335
theorem B112251 : Blo 111784 112251 := bstep (se 1 (by rfl) ⟨84188, by rfl⟩ : syracuseStep 112251 = 168377) B168377
theorem B112303 : Blo 111784 112303 := bstep (se 1 (by rfl) ⟨84227, by rfl⟩ : syracuseStep 112303 = 168455) B168455
theorem B112327 : Blo 111784 112327 := bstep (se 1 (by rfl) ⟨84245, by rfl⟩ : syracuseStep 112327 = 168491) B168491
theorem B112347 : Blo 111784 112347 := bstep (se 1 (by rfl) ⟨84260, by rfl⟩ : syracuseStep 112347 = 168521) B168521
theorem B440057 : Blo 111784 440057 := bstep (se 2 (by rfl) ⟨165021, by rfl⟩ : syracuseStep 440057 = 330043) B330043
theorem B112423 : Blo 111784 112423 := bstep (se 1 (by rfl) ⟨84317, by rfl⟩ : syracuseStep 112423 = 168635) B168635
theorem B112463 : Blo 111784 112463 := bstep (se 1 (by rfl) ⟨84347, by rfl⟩ : syracuseStep 112463 = 168695) B168695
theorem B112479 : Blo 111784 112479 := bstep (se 1 (by rfl) ⟨84359, by rfl⟩ : syracuseStep 112479 = 168719) B168719
theorem B636781 : Blo 111784 636781 := bstep (se 3 (by rfl) ⟨119396, by rfl⟩ : syracuseStep 636781 = 238793) B238793
theorem B112507 : Blo 111784 112507 := bstep (se 1 (by rfl) ⟨84380, by rfl⟩ : syracuseStep 112507 = 168761) B168761
theorem B112559 : Blo 111784 112559 := bstep (se 1 (by rfl) ⟨84419, by rfl⟩ : syracuseStep 112559 = 168839) B168839
theorem B112583 : Blo 111784 112583 := bstep (se 1 (by rfl) ⟨84437, by rfl⟩ : syracuseStep 112583 = 168875) B168875
theorem B5027789 : Blo 111784 5027789 := bstep (se 3 (by rfl) ⟨942710, by rfl⟩ : syracuseStep 5027789 = 1885421) B1885421
theorem B112603 : Blo 111784 112603 := bstep (se 1 (by rfl) ⟨84452, by rfl⟩ : syracuseStep 112603 = 168905) B168905
theorem B112679 : Blo 111784 112679 := bstep (se 1 (by rfl) ⟨84509, by rfl⟩ : syracuseStep 112679 = 169019) B169019
theorem B112719 : Blo 111784 112719 := bstep (se 1 (by rfl) ⟨84539, by rfl⟩ : syracuseStep 112719 = 169079) B169079
theorem B145487 : Blo 111784 145487 := bstep (se 1 (by rfl) ⟨109115, by rfl⟩ : syracuseStep 145487 = 218231) B218231
theorem B112735 : Blo 111784 112735 := bstep (se 1 (by rfl) ⟨84551, by rfl⟩ : syracuseStep 112735 = 169103) B169103
theorem B112763 : Blo 111784 112763 := bstep (se 1 (by rfl) ⟨84572, by rfl⟩ : syracuseStep 112763 = 169145) B169145
theorem B112815 : Blo 111784 112815 := bstep (se 1 (by rfl) ⟨84611, by rfl⟩ : syracuseStep 112815 = 169223) B169223
theorem B112839 : Blo 111784 112839 := bstep (se 1 (by rfl) ⟨84629, by rfl⟩ : syracuseStep 112839 = 169259) B169259
theorem B112859 : Blo 111784 112859 := bstep (se 1 (by rfl) ⟨84644, by rfl⟩ : syracuseStep 112859 = 169289) B169289
theorem B1718561 : Blo 111784 1718561 := bstep (se 2 (by rfl) ⟨644460, by rfl⟩ : syracuseStep 1718561 = 1288921) B1288921
theorem B112935 : Blo 111784 112935 := bstep (se 1 (by rfl) ⟨84701, by rfl⟩ : syracuseStep 112935 = 169403) B169403
theorem B112975 : Blo 111784 112975 := bstep (se 1 (by rfl) ⟨84731, by rfl⟩ : syracuseStep 112975 = 169463) B169463
theorem B112991 : Blo 111784 112991 := bstep (se 1 (by rfl) ⟨84743, by rfl⟩ : syracuseStep 112991 = 169487) B169487
theorem B244073 : Blo 111784 244073 := bstep (se 2 (by rfl) ⟨91527, by rfl⟩ : syracuseStep 244073 = 183055) B183055
theorem B113019 : Blo 111784 113019 := bstep (se 1 (by rfl) ⟨84764, by rfl⟩ : syracuseStep 113019 = 169529) B169529
theorem B113071 : Blo 111784 113071 := bstep (se 1 (by rfl) ⟨84803, by rfl⟩ : syracuseStep 113071 = 169607) B169607
theorem B113095 : Blo 111784 113095 := bstep (se 1 (by rfl) ⟨84821, by rfl⟩ : syracuseStep 113095 = 169643) B169643
theorem B113115 : Blo 111784 113115 := bstep (se 1 (by rfl) ⟨84836, by rfl⟩ : syracuseStep 113115 = 169673) B169673
theorem B113191 : Blo 111784 113191 := bstep (se 1 (by rfl) ⟨84893, by rfl⟩ : syracuseStep 113191 = 169787) B169787
theorem B113231 : Blo 111784 113231 := bstep (se 1 (by rfl) ⟨84923, by rfl⟩ : syracuseStep 113231 = 169847) B169847
theorem B113247 : Blo 111784 113247 := bstep (se 1 (by rfl) ⟨84935, by rfl⟩ : syracuseStep 113247 = 169871) B169871
theorem B113275 : Blo 111784 113275 := bstep (se 1 (by rfl) ⟨84956, by rfl⟩ : syracuseStep 113275 = 169913) B169913
theorem B113327 : Blo 111784 113327 := bstep (se 1 (by rfl) ⟨84995, by rfl⟩ : syracuseStep 113327 = 169991) B169991
theorem B113351 : Blo 111784 113351 := bstep (se 1 (by rfl) ⟨85013, by rfl⟩ : syracuseStep 113351 = 170027) B170027
theorem B146119 : Blo 111784 146119 := bstep (se 1 (by rfl) ⟨109589, by rfl⟩ : syracuseStep 146119 = 219179) B219179
theorem B113371 : Blo 111784 113371 := bstep (se 1 (by rfl) ⟨85028, by rfl⟩ : syracuseStep 113371 = 170057) B170057
theorem B113447 : Blo 111784 113447 := bstep (se 1 (by rfl) ⟨85085, by rfl⟩ : syracuseStep 113447 = 170171) B170171
theorem B113487 : Blo 111784 113487 := bstep (se 1 (by rfl) ⟨85115, by rfl⟩ : syracuseStep 113487 = 170231) B170231
theorem B408415 : Blo 111784 408415 := bstep (se 1 (by rfl) ⟨306311, by rfl⟩ : syracuseStep 408415 = 612623) B612623
theorem B113503 : Blo 111784 113503 := bstep (se 1 (by rfl) ⟨85127, by rfl⟩ : syracuseStep 113503 = 170255) B170255
theorem B113531 : Blo 111784 113531 := bstep (se 1 (by rfl) ⟨85148, by rfl⟩ : syracuseStep 113531 = 170297) B170297
theorem B768943 : Blo 111784 768943 := bstep (se 1 (by rfl) ⟨576707, by rfl⟩ : syracuseStep 768943 = 1153415) B1153415
theorem B113583 : Blo 111784 113583 := bstep (se 1 (by rfl) ⟨85187, by rfl⟩ : syracuseStep 113583 = 170375) B170375
theorem B113607 : Blo 111784 113607 := bstep (se 1 (by rfl) ⟨85205, by rfl⟩ : syracuseStep 113607 = 170411) B170411
theorem B113627 : Blo 111784 113627 := bstep (se 1 (by rfl) ⟨85220, by rfl⟩ : syracuseStep 113627 = 170441) B170441
theorem B113703 : Blo 111784 113703 := bstep (se 1 (by rfl) ⟨85277, by rfl⟩ : syracuseStep 113703 = 170555) B170555
theorem B113743 : Blo 111784 113743 := bstep (se 1 (by rfl) ⟨85307, by rfl⟩ : syracuseStep 113743 = 170615) B170615
theorem B113759 : Blo 111784 113759 := bstep (se 1 (by rfl) ⟨85319, by rfl⟩ : syracuseStep 113759 = 170639) B170639
theorem B113787 : Blo 111784 113787 := bstep (se 1 (by rfl) ⟨85340, by rfl⟩ : syracuseStep 113787 = 170681) B170681
theorem B113839 : Blo 111784 113839 := bstep (se 1 (by rfl) ⟨85379, by rfl⟩ : syracuseStep 113839 = 170759) B170759
theorem B736451 : Blo 111784 736451 := bstep (se 1 (by rfl) ⟨552338, by rfl⟩ : syracuseStep 736451 = 1104677) B1104677
theorem B113863 : Blo 111784 113863 := bstep (se 1 (by rfl) ⟨85397, by rfl⟩ : syracuseStep 113863 = 170795) B170795
theorem B113883 : Blo 111784 113883 := bstep (se 1 (by rfl) ⟨85412, by rfl⟩ : syracuseStep 113883 = 170825) B170825
theorem B113959 : Blo 111784 113959 := bstep (se 1 (by rfl) ⟨85469, by rfl⟩ : syracuseStep 113959 = 170939) B170939
theorem B113999 : Blo 111784 113999 := bstep (se 1 (by rfl) ⟨85499, by rfl⟩ : syracuseStep 113999 = 170999) B170999
theorem B114015 : Blo 111784 114015 := bstep (se 1 (by rfl) ⟨85511, by rfl⟩ : syracuseStep 114015 = 171023) B171023
theorem B114043 : Blo 111784 114043 := bstep (se 1 (by rfl) ⟨85532, by rfl⟩ : syracuseStep 114043 = 171065) B171065
theorem B310657 : Blo 111784 310657 := bstep (se 2 (by rfl) ⟨116496, by rfl⟩ : syracuseStep 310657 = 232993) B232993
theorem B114095 : Blo 111784 114095 := bstep (se 1 (by rfl) ⟨85571, by rfl⟩ : syracuseStep 114095 = 171143) B171143
theorem B114119 : Blo 111784 114119 := bstep (se 1 (by rfl) ⟨85589, by rfl⟩ : syracuseStep 114119 = 171179) B171179
theorem B114139 : Blo 111784 114139 := bstep (se 1 (by rfl) ⟨85604, by rfl⟩ : syracuseStep 114139 = 171209) B171209
theorem B212519 : Blo 111784 212519 := bstep (se 1 (by rfl) ⟨159389, by rfl⟩ : syracuseStep 212519 = 318779) B318779
theorem B114215 : Blo 111784 114215 := bstep (se 1 (by rfl) ⟨85661, by rfl⟩ : syracuseStep 114215 = 171323) B171323
theorem B441895 : Blo 111784 441895 := bstep (se 1 (by rfl) ⟨331421, by rfl⟩ : syracuseStep 441895 = 662843) B662843
theorem B114255 : Blo 111784 114255 := bstep (se 1 (by rfl) ⟨85691, by rfl⟩ : syracuseStep 114255 = 171383) B171383
theorem B114271 : Blo 111784 114271 := bstep (se 1 (by rfl) ⟨85703, by rfl⟩ : syracuseStep 114271 = 171407) B171407
theorem B114299 : Blo 111784 114299 := bstep (se 1 (by rfl) ⟨85724, by rfl⟩ : syracuseStep 114299 = 171449) B171449
theorem B114351 : Blo 111784 114351 := bstep (se 1 (by rfl) ⟨85763, by rfl⟩ : syracuseStep 114351 = 171527) B171527
theorem B114375 : Blo 111784 114375 := bstep (se 1 (by rfl) ⟨85781, by rfl⟩ : syracuseStep 114375 = 171563) B171563
theorem B114395 : Blo 111784 114395 := bstep (se 1 (by rfl) ⟨85796, by rfl⟩ : syracuseStep 114395 = 171593) B171593
theorem B114471 : Blo 111784 114471 := bstep (se 1 (by rfl) ⟨85853, by rfl⟩ : syracuseStep 114471 = 171707) B171707
theorem B114511 : Blo 111784 114511 := bstep (se 1 (by rfl) ⟨85883, by rfl⟩ : syracuseStep 114511 = 171767) B171767
theorem B114527 : Blo 111784 114527 := bstep (se 1 (by rfl) ⟨85895, by rfl⟩ : syracuseStep 114527 = 171791) B171791
theorem B114555 : Blo 111784 114555 := bstep (se 1 (by rfl) ⟨85916, by rfl⟩ : syracuseStep 114555 = 171833) B171833
theorem B114607 : Blo 111784 114607 := bstep (se 1 (by rfl) ⟨85955, by rfl⟩ : syracuseStep 114607 = 171911) B171911
theorem B114631 : Blo 111784 114631 := bstep (se 1 (by rfl) ⟨85973, by rfl⟩ : syracuseStep 114631 = 171947) B171947
theorem B114651 : Blo 111784 114651 := bstep (se 1 (by rfl) ⟨85988, by rfl⟩ : syracuseStep 114651 = 171977) B171977
theorem B114727 : Blo 111784 114727 := bstep (se 1 (by rfl) ⟨86045, by rfl⟩ : syracuseStep 114727 = 172091) B172091
theorem B114767 : Blo 111784 114767 := bstep (se 1 (by rfl) ⟨86075, by rfl⟩ : syracuseStep 114767 = 172151) B172151
theorem B114783 : Blo 111784 114783 := bstep (se 1 (by rfl) ⟨86087, by rfl⟩ : syracuseStep 114783 = 172175) B172175
theorem B114811 : Blo 111784 114811 := bstep (se 1 (by rfl) ⟨86108, by rfl⟩ : syracuseStep 114811 = 172217) B172217
theorem B1097891 : Blo 111784 1097891 := bstep (se 1 (by rfl) ⟨823418, by rfl⟩ : syracuseStep 1097891 = 1646837) B1646837
theorem B114863 : Blo 111784 114863 := bstep (se 1 (by rfl) ⟨86147, by rfl⟩ : syracuseStep 114863 = 172295) B172295
theorem B114887 : Blo 111784 114887 := bstep (se 1 (by rfl) ⟨86165, by rfl⟩ : syracuseStep 114887 = 172331) B172331
theorem B114907 : Blo 111784 114907 := bstep (se 1 (by rfl) ⟨86180, by rfl⟩ : syracuseStep 114907 = 172361) B172361
theorem B180473 : Blo 111784 180473 := bstep (se 2 (by rfl) ⟨67677, by rfl⟩ : syracuseStep 180473 = 135355) B135355
theorem B114983 : Blo 111784 114983 := bstep (se 1 (by rfl) ⟨86237, by rfl⟩ : syracuseStep 114983 = 172475) B172475
theorem B115023 : Blo 111784 115023 := bstep (se 1 (by rfl) ⟨86267, by rfl⟩ : syracuseStep 115023 = 172535) B172535
theorem B115039 : Blo 111784 115039 := bstep (se 1 (by rfl) ⟨86279, by rfl⟩ : syracuseStep 115039 = 172559) B172559
theorem B115067 : Blo 111784 115067 := bstep (se 1 (by rfl) ⟨86300, by rfl⟩ : syracuseStep 115067 = 172601) B172601
theorem B115119 : Blo 111784 115119 := bstep (se 1 (by rfl) ⟨86339, by rfl⟩ : syracuseStep 115119 = 172679) B172679
theorem B147895 : Blo 111784 147895 := bstep (se 1 (by rfl) ⟨110921, by rfl⟩ : syracuseStep 147895 = 221843) B221843
theorem B115143 : Blo 111784 115143 := bstep (se 1 (by rfl) ⟨86357, by rfl⟩ : syracuseStep 115143 = 172715) B172715
theorem B115163 : Blo 111784 115163 := bstep (se 1 (by rfl) ⟨86372, by rfl⟩ : syracuseStep 115163 = 172745) B172745
theorem B246235 : Blo 111784 246235 := bstep (se 1 (by rfl) ⟨184676, by rfl⟩ : syracuseStep 246235 = 369353) B369353
theorem B115239 : Blo 111784 115239 := bstep (se 1 (by rfl) ⟨86429, by rfl⟩ : syracuseStep 115239 = 172859) B172859
theorem B115279 : Blo 111784 115279 := bstep (se 1 (by rfl) ⟨86459, by rfl⟩ : syracuseStep 115279 = 172919) B172919
theorem B115295 : Blo 111784 115295 := bstep (se 1 (by rfl) ⟨86471, by rfl⟩ : syracuseStep 115295 = 172943) B172943
theorem B115323 : Blo 111784 115323 := bstep (se 1 (by rfl) ⟨86492, by rfl⟩ : syracuseStep 115323 = 172985) B172985
theorem B115375 : Blo 111784 115375 := bstep (se 1 (by rfl) ⟨86531, by rfl⟩ : syracuseStep 115375 = 173063) B173063
theorem B115399 : Blo 111784 115399 := bstep (se 1 (by rfl) ⟨86549, by rfl⟩ : syracuseStep 115399 = 173099) B173099
theorem B639697 : Blo 111784 639697 := bstep (se 2 (by rfl) ⟨239886, by rfl⟩ : syracuseStep 639697 = 479773) B479773
theorem B115419 : Blo 111784 115419 := bstep (se 1 (by rfl) ⟨86564, by rfl⟩ : syracuseStep 115419 = 173129) B173129
theorem B115495 : Blo 111784 115495 := bstep (se 1 (by rfl) ⟨86621, by rfl⟩ : syracuseStep 115495 = 173243) B173243
theorem B213833 : Blo 111784 213833 := bstep (se 2 (by rfl) ⟨80187, by rfl⟩ : syracuseStep 213833 = 160375) B160375
theorem B115535 : Blo 111784 115535 := bstep (se 1 (by rfl) ⟨86651, by rfl⟩ : syracuseStep 115535 = 173303) B173303
theorem B115551 : Blo 111784 115551 := bstep (se 1 (by rfl) ⟨86663, by rfl⟩ : syracuseStep 115551 = 173327) B173327
theorem B115579 : Blo 111784 115579 := bstep (se 1 (by rfl) ⟨86684, by rfl⟩ : syracuseStep 115579 = 173369) B173369
theorem B115631 : Blo 111784 115631 := bstep (se 1 (by rfl) ⟨86723, by rfl⟩ : syracuseStep 115631 = 173447) B173447
theorem B377783 : Blo 111784 377783 := bstep (se 1 (by rfl) ⟨283337, by rfl⟩ : syracuseStep 377783 = 566675) B566675
theorem B115655 : Blo 111784 115655 := bstep (se 1 (by rfl) ⟨86741, by rfl⟩ : syracuseStep 115655 = 173483) B173483
theorem B115675 : Blo 111784 115675 := bstep (se 1 (by rfl) ⟨86756, by rfl⟩ : syracuseStep 115675 = 173513) B173513
theorem B115751 : Blo 111784 115751 := bstep (se 1 (by rfl) ⟨86813, by rfl⟩ : syracuseStep 115751 = 173627) B173627
theorem B967747 : Blo 111784 967747 := bstep (se 1 (by rfl) ⟨725810, by rfl⟩ : syracuseStep 967747 = 1451621) B1451621
theorem B214265 : Blo 111784 214265 := bstep (se 2 (by rfl) ⟨80349, by rfl⟩ : syracuseStep 214265 = 160699) B160699
theorem B1459619 : Blo 111784 1459619 := bstep (se 1 (by rfl) ⟨1094714, by rfl⟩ : syracuseStep 1459619 = 2189429) B2189429
theorem B378377 : Blo 111784 378377 := bstep (se 2 (by rfl) ⟨141891, by rfl⟩ : syracuseStep 378377 = 283783) B283783
theorem B575099 : Blo 111784 575099 := bstep (se 1 (by rfl) ⟨431324, by rfl⟩ : syracuseStep 575099 = 862649) B862649
theorem B116347 : Blo 111784 116347 := bstep (se 1 (by rfl) ⟨87260, by rfl⟩ : syracuseStep 116347 = 174521) B174521
theorem B739115 : Blo 111784 739115 := bstep (se 1 (by rfl) ⟨554336, by rfl⟩ : syracuseStep 739115 = 1108673) B1108673
theorem B739343 : Blo 111784 739343 := bstep (se 1 (by rfl) ⟨554507, by rfl⟩ : syracuseStep 739343 = 1109015) B1109015
theorem B182521 : Blo 111784 182521 := bstep (se 2 (by rfl) ⟨68445, by rfl⟩ : syracuseStep 182521 = 136891) B136891
theorem B379241 : Blo 111784 379241 := bstep (se 2 (by rfl) ⟨142215, by rfl⟩ : syracuseStep 379241 = 284431) B284431
theorem B346511 : Blo 111784 346511 := bstep (se 1 (by rfl) ⟨259883, by rfl⟩ : syracuseStep 346511 = 519767) B519767
theorem B3295673 : Blo 111784 3295673 := bstep (se 2 (by rfl) ⟨1235877, by rfl⟩ : syracuseStep 3295673 = 2471755) B2471755
theorem B936481 : Blo 111784 936481 := bstep (se 2 (by rfl) ⟨351180, by rfl⟩ : syracuseStep 936481 = 702361) B702361
theorem B215723 : Blo 111784 215723 := bstep (se 1 (by rfl) ⟨161792, by rfl⟩ : syracuseStep 215723 = 323585) B323585
theorem B379835 : Blo 111784 379835 := bstep (se 1 (by rfl) ⟨284876, by rfl⟩ : syracuseStep 379835 = 569753) B569753
theorem B871397 : Blo 111784 871397 := bstep (se 4 (by rfl) ⟨81693, by rfl⟩ : syracuseStep 871397 = 163387) B163387
theorem B216103 : Blo 111784 216103 := bstep (se 1 (by rfl) ⟨162077, by rfl⟩ : syracuseStep 216103 = 324155) B324155
theorem B216263 : Blo 111784 216263 := bstep (se 1 (by rfl) ⟨162197, by rfl⟩ : syracuseStep 216263 = 324395) B324395
theorem B478817 : Blo 111784 478817 := bstep (se 2 (by rfl) ⟨179556, by rfl⟩ : syracuseStep 478817 = 359113) B359113
theorem B1462283 : Blo 111784 1462283 := bstep (se 1 (by rfl) ⟨1096712, by rfl⟩ : syracuseStep 1462283 = 2193425) B2193425
theorem B577853 : Blo 111784 577853 := bstep (se 3 (by rfl) ⟨108347, by rfl⟩ : syracuseStep 577853 = 216695) B216695
theorem B217417 : Blo 111784 217417 := bstep (se 2 (by rfl) ⟨81531, by rfl⟩ : syracuseStep 217417 = 163063) B163063
theorem B545129 : Blo 111784 545129 := bstep (se 2 (by rfl) ⟨204423, by rfl⟩ : syracuseStep 545129 = 408847) B408847
theorem B1331585 : Blo 111784 1331585 := bstep (se 2 (by rfl) ⟨499344, by rfl⟩ : syracuseStep 1331585 = 998689) B998689
theorem B381563 : Blo 111784 381563 := bstep (se 1 (by rfl) ⟨286172, by rfl⟩ : syracuseStep 381563 = 572345) B572345
theorem B905863 : Blo 111784 905863 := bstep (se 1 (by rfl) ⟨679397, by rfl⟩ : syracuseStep 905863 = 1358795) B1358795
theorem B381725 : Blo 111784 381725 := bstep (se 3 (by rfl) ⟨71573, by rfl⟩ : syracuseStep 381725 = 143147) B143147
theorem B185195 : Blo 111784 185195 := bstep (se 1 (by rfl) ⟨138896, by rfl⟩ : syracuseStep 185195 = 277793) B277793
theorem B1037231 : Blo 111784 1037231 := bstep (se 1 (by rfl) ⟨777923, by rfl⟩ : syracuseStep 1037231 = 1555847) B1555847
theorem B283895 : Blo 111784 283895 := bstep (se 1 (by rfl) ⟨212921, by rfl⟩ : syracuseStep 283895 = 425843) B425843
theorem B873929 : Blo 111784 873929 := bstep (se 2 (by rfl) ⟨327723, by rfl⟩ : syracuseStep 873929 = 655447) B655447
theorem B382427 : Blo 111784 382427 := bstep (se 1 (by rfl) ⟨286820, by rfl⟩ : syracuseStep 382427 = 573641) B573641
theorem B26891747 : Blo 111784 26891747 := bstep (se 1 (by rfl) ⟨20168810, by rfl⟩ : syracuseStep 26891747 = 40337621) B40337621
theorem B251603 : Blo 111784 251603 := bstep (se 1 (by rfl) ⟨188702, by rfl⟩ : syracuseStep 251603 = 377405) B377405
theorem B186295 : Blo 111784 186295 := bstep (se 1 (by rfl) ⟨139721, by rfl⟩ : syracuseStep 186295 = 279443) B279443
theorem B153563 : Blo 111784 153563 := bstep (se 1 (by rfl) ⟨115172, by rfl⟩ : syracuseStep 153563 = 230345) B230345
theorem B383129 : Blo 111784 383129 := bstep (se 2 (by rfl) ⟨143673, by rfl⟩ : syracuseStep 383129 = 287347) B287347
theorem B350365 : Blo 111784 350365 := bstep (se 3 (by rfl) ⟨65693, by rfl⟩ : syracuseStep 350365 = 131387) B131387
theorem B219611 : Blo 111784 219611 := bstep (se 1 (by rfl) ⟨164708, by rfl⟩ : syracuseStep 219611 = 329417) B329417
theorem B580121 : Blo 111784 580121 := bstep (se 2 (by rfl) ⟨217545, by rfl⟩ : syracuseStep 580121 = 435091) B435091
theorem B252539 : Blo 111784 252539 := bstep (se 1 (by rfl) ⟨189404, by rfl⟩ : syracuseStep 252539 = 378809) B378809
theorem B1825415 : Blo 111784 1825415 := bstep (se 1 (by rfl) ⟨1369061, by rfl⟩ : syracuseStep 1825415 = 2738123) B2738123
theorem B285383 : Blo 111784 285383 := bstep (se 1 (by rfl) ⟨214037, by rfl⟩ : syracuseStep 285383 = 428075) B428075
theorem B252665 : Blo 111784 252665 := bstep (se 2 (by rfl) ⟨94749, by rfl⟩ : syracuseStep 252665 = 189499) B189499
theorem B121819 : Blo 111784 121819 := bstep (se 1 (by rfl) ⟨91364, by rfl⟩ : syracuseStep 121819 = 182729) B182729
theorem B252935 : Blo 111784 252935 := bstep (se 1 (by rfl) ⟨189701, by rfl⟩ : syracuseStep 252935 = 379403) B379403
theorem B253007 : Blo 111784 253007 := bstep (se 1 (by rfl) ⟨189755, by rfl⟩ : syracuseStep 253007 = 379511) B379511
theorem B384317 : Blo 111784 384317 := bstep (se 3 (by rfl) ⟨72059, by rfl⟩ : syracuseStep 384317 = 144119) B144119
theorem B1105325 : Blo 111784 1105325 := bstep (se 3 (by rfl) ⟨207248, by rfl⟩ : syracuseStep 1105325 = 414497) B414497
theorem B253403 : Blo 111784 253403 := bstep (se 1 (by rfl) ⟨190052, by rfl⟩ : syracuseStep 253403 = 380105) B380105
theorem B351959 : Blo 111784 351959 := bstep (se 1 (by rfl) ⟨263969, by rfl⟩ : syracuseStep 351959 = 527939) B527939
theorem B286537 : Blo 111784 286537 := bstep (se 2 (by rfl) ⟨107451, by rfl⟩ : syracuseStep 286537 = 214903) B214903
theorem B483191 : Blo 111784 483191 := bstep (se 1 (by rfl) ⟨362393, by rfl⟩ : syracuseStep 483191 = 724787) B724787
theorem B319393 : Blo 111784 319393 := bstep (se 2 (by rfl) ⟨119772, by rfl⟩ : syracuseStep 319393 = 239545) B239545
theorem B253871 : Blo 111784 253871 := bstep (se 1 (by rfl) ⟨190403, by rfl⟩ : syracuseStep 253871 = 380807) B380807
theorem B483259 : Blo 111784 483259 := bstep (se 1 (by rfl) ⟨362444, by rfl⟩ : syracuseStep 483259 = 724889) B724889
theorem B548801 : Blo 111784 548801 := bstep (se 2 (by rfl) ⟨205800, by rfl⟩ : syracuseStep 548801 = 411601) B411601
theorem B1466383 : Blo 111784 1466383 := bstep (se 1 (by rfl) ⟨1099787, by rfl⟩ : syracuseStep 1466383 = 2199575) B2199575
theorem B385181 : Blo 111784 385181 := bstep (se 3 (by rfl) ⟨72221, by rfl⟩ : syracuseStep 385181 = 144443) B144443
theorem B254123 : Blo 111784 254123 := bstep (se 1 (by rfl) ⟨190592, by rfl⟩ : syracuseStep 254123 = 381185) B381185
theorem B188777 : Blo 111784 188777 := bstep (se 2 (by rfl) ⟨70791, by rfl⟩ : syracuseStep 188777 = 141583) B141583
theorem B319963 : Blo 111784 319963 := bstep (se 1 (by rfl) ⟨239972, by rfl⟩ : syracuseStep 319963 = 479945) B479945
theorem B1172141 : Blo 111784 1172141 := bstep (se 3 (by rfl) ⟨219776, by rfl⟩ : syracuseStep 1172141 = 439553) B439553
theorem B877229 : Blo 111784 877229 := bstep (se 3 (by rfl) ⟨164480, by rfl⟩ : syracuseStep 877229 = 328961) B328961
theorem B385721 : Blo 111784 385721 := bstep (se 2 (by rfl) ⟨144645, by rfl⟩ : syracuseStep 385721 = 289291) B289291
theorem B254663 : Blo 111784 254663 := bstep (se 1 (by rfl) ⟨190997, by rfl⟩ : syracuseStep 254663 = 381995) B381995
theorem B549587 : Blo 111784 549587 := bstep (se 1 (by rfl) ⟨412190, by rfl⟩ : syracuseStep 549587 = 824381) B824381
theorem B189175 : Blo 111784 189175 := bstep (se 1 (by rfl) ⟨141881, by rfl⟩ : syracuseStep 189175 = 283763) B283763
theorem B287671 : Blo 111784 287671 := bstep (se 1 (by rfl) ⟨215753, by rfl⟩ : syracuseStep 287671 = 431507) B431507
theorem B189371 : Blo 111784 189371 := bstep (se 1 (by rfl) ⟨142028, by rfl⟩ : syracuseStep 189371 = 284057) B284057
theorem B189479 : Blo 111784 189479 := bstep (se 1 (by rfl) ⟨142109, by rfl⟩ : syracuseStep 189479 = 284219) B284219
theorem B320669 : Blo 111784 320669 := bstep (se 3 (by rfl) ⟨60125, by rfl⟩ : syracuseStep 320669 = 120251) B120251
theorem B386315 : Blo 111784 386315 := bstep (se 1 (by rfl) ⟨289736, by rfl⟩ : syracuseStep 386315 = 579473) B579473
theorem B189769 : Blo 111784 189769 := bstep (se 2 (by rfl) ⟨71163, by rfl⟩ : syracuseStep 189769 = 142327) B142327
theorem B189803 : Blo 111784 189803 := bstep (se 1 (by rfl) ⟨142352, by rfl⟩ : syracuseStep 189803 = 284705) B284705
theorem B583037 : Blo 111784 583037 := bstep (se 3 (by rfl) ⟨109319, by rfl⟩ : syracuseStep 583037 = 218639) B218639
theorem B320897 : Blo 111784 320897 := bstep (se 2 (by rfl) ⟨120336, by rfl⟩ : syracuseStep 320897 = 240673) B240673
theorem B386585 : Blo 111784 386585 := bstep (se 2 (by rfl) ⟨144969, by rfl⟩ : syracuseStep 386585 = 289939) B289939
theorem B255527 : Blo 111784 255527 := bstep (se 1 (by rfl) ⟨191645, by rfl⟩ : syracuseStep 255527 = 383291) B383291
theorem B321239 : Blo 111784 321239 := bstep (se 1 (by rfl) ⟨240929, by rfl⟩ : syracuseStep 321239 = 481859) B481859
theorem B190201 : Blo 111784 190201 := bstep (se 2 (by rfl) ⟨71325, by rfl⟩ : syracuseStep 190201 = 142651) B142651
theorem B321353 : Blo 111784 321353 := bstep (se 2 (by rfl) ⟨120507, by rfl⟩ : syracuseStep 321353 = 241015) B241015
theorem B255851 : Blo 111784 255851 := bstep (se 1 (by rfl) ⟨191888, by rfl⟩ : syracuseStep 255851 = 383777) B383777
theorem B780167 : Blo 111784 780167 := bstep (se 1 (by rfl) ⟨585125, by rfl⟩ : syracuseStep 780167 = 1170251) B1170251
theorem B255905 : Blo 111784 255905 := bstep (se 2 (by rfl) ⟨95964, by rfl⟩ : syracuseStep 255905 = 191929) B191929
theorem B550817 : Blo 111784 550817 := bstep (se 2 (by rfl) ⟨206556, by rfl⟩ : syracuseStep 550817 = 413113) B413113
theorem B190471 : Blo 111784 190471 := bstep (se 1 (by rfl) ⟨142853, by rfl⟩ : syracuseStep 190471 = 285707) B285707
theorem B256247 : Blo 111784 256247 := bstep (se 1 (by rfl) ⟨192185, by rfl⟩ : syracuseStep 256247 = 384371) B384371
theorem B1075457 : Blo 111784 1075457 := bstep (se 2 (by rfl) ⟨403296, by rfl⟩ : syracuseStep 1075457 = 806593) B806593
theorem B1566977 : Blo 111784 1566977 := bstep (se 2 (by rfl) ⟨587616, by rfl⟩ : syracuseStep 1566977 = 1175233) B1175233
theorem B289129 : Blo 111784 289129 := bstep (se 2 (by rfl) ⟨108423, by rfl⟩ : syracuseStep 289129 = 216847) B216847
theorem B1436039 : Blo 111784 1436039 := bstep (se 1 (by rfl) ⟨1077029, by rfl⟩ : syracuseStep 1436039 = 2154059) B2154059
theorem B4712849 : Blo 111784 4712849 := bstep (se 2 (by rfl) ⟨1767318, by rfl⟩ : syracuseStep 4712849 = 3534637) B3534637
theorem B1370519 : Blo 111784 1370519 := bstep (se 1 (by rfl) ⟨1027889, by rfl⟩ : syracuseStep 1370519 = 2055779) B2055779
theorem B190903 : Blo 111784 190903 := bstep (se 1 (by rfl) ⟨143177, by rfl⟩ : syracuseStep 190903 = 286355) B286355
theorem B191099 : Blo 111784 191099 := bstep (se 1 (by rfl) ⟨143324, by rfl⟩ : syracuseStep 191099 = 286649) B286649
theorem B289403 : Blo 111784 289403 := bstep (se 1 (by rfl) ⟨217052, by rfl⟩ : syracuseStep 289403 = 434105) B434105
theorem B387719 : Blo 111784 387719 := bstep (se 1 (by rfl) ⟨290789, by rfl⟩ : syracuseStep 387719 = 581579) B581579
theorem B387773 : Blo 111784 387773 := bstep (se 3 (by rfl) ⟨72707, by rfl⟩ : syracuseStep 387773 = 145415) B145415
theorem B256841 : Blo 111784 256841 := bstep (se 2 (by rfl) ⟨96315, by rfl⟩ : syracuseStep 256841 = 192631) B192631
theorem B387935 : Blo 111784 387935 := bstep (se 1 (by rfl) ⟨290951, by rfl⟩ : syracuseStep 387935 = 581903) B581903
theorem B388097 : Blo 111784 388097 := bstep (se 2 (by rfl) ⟨145536, by rfl⟩ : syracuseStep 388097 = 291073) B291073
theorem B191497 : Blo 111784 191497 := bstep (se 2 (by rfl) ⟨71811, by rfl⟩ : syracuseStep 191497 = 143623) B143623
theorem B126031 : Blo 111784 126031 := bstep (se 1 (by rfl) ⟨94523, by rfl⟩ : syracuseStep 126031 = 189047) B189047
theorem B191659 : Blo 111784 191659 := bstep (se 1 (by rfl) ⟨143744, by rfl⟩ : syracuseStep 191659 = 287489) B287489
theorem B126427 : Blo 111784 126427 := bstep (se 1 (by rfl) ⟨94820, by rfl⟩ : syracuseStep 126427 = 189641) B189641
theorem B191963 : Blo 111784 191963 := bstep (se 1 (by rfl) ⟨143972, by rfl⟩ : syracuseStep 191963 = 287945) B287945
theorem B880091 : Blo 111784 880091 := bstep (se 1 (by rfl) ⟨660068, by rfl⟩ : syracuseStep 880091 = 1320137) B1320137
theorem B1076723 : Blo 111784 1076723 := bstep (se 1 (by rfl) ⟨807542, by rfl⟩ : syracuseStep 1076723 = 1615085) B1615085
theorem B159241 : Blo 111784 159241 := bstep (se 2 (by rfl) ⟨59715, by rfl⟩ : syracuseStep 159241 = 119431) B119431
theorem B257633 : Blo 111784 257633 := bstep (se 2 (by rfl) ⟨96612, by rfl⟩ : syracuseStep 257633 = 193225) B193225
theorem B159355 : Blo 111784 159355 := bstep (se 1 (by rfl) ⟨119516, by rfl⟩ : syracuseStep 159355 = 239033) B239033
theorem B192199 : Blo 111784 192199 := bstep (se 1 (by rfl) ⟨144149, by rfl⟩ : syracuseStep 192199 = 288299) B288299
theorem B519929 : Blo 111784 519929 := bstep (se 2 (by rfl) ⟨194973, by rfl⟩ : syracuseStep 519929 = 389947) B389947
theorem B388907 : Blo 111784 388907 := bstep (se 1 (by rfl) ⟨291680, by rfl⟩ : syracuseStep 388907 = 583361) B583361
theorem B159583 : Blo 111784 159583 := bstep (se 1 (by rfl) ⟨119687, by rfl⟩ : syracuseStep 159583 = 239375) B239375
theorem B192361 : Blo 111784 192361 := bstep (se 2 (by rfl) ⟨72135, by rfl⟩ : syracuseStep 192361 = 144271) B144271
theorem B126895 : Blo 111784 126895 := bstep (se 1 (by rfl) ⟨95171, by rfl⟩ : syracuseStep 126895 = 190343) B190343
theorem B257975 : Blo 111784 257975 := bstep (se 1 (by rfl) ⟨193481, by rfl⟩ : syracuseStep 257975 = 386963) B386963
theorem B389177 : Blo 111784 389177 := bstep (se 2 (by rfl) ⟨145941, by rfl⟩ : syracuseStep 389177 = 291883) B291883
theorem B389387 : Blo 111784 389387 := bstep (se 1 (by rfl) ⟨292040, by rfl⟩ : syracuseStep 389387 = 584081) B584081
theorem B553277 : Blo 111784 553277 := bstep (se 3 (by rfl) ⟨103739, by rfl⟩ : syracuseStep 553277 = 207479) B207479
theorem B192863 : Blo 111784 192863 := bstep (se 1 (by rfl) ⟨144647, by rfl⟩ : syracuseStep 192863 = 289295) B289295
theorem B127327 : Blo 111784 127327 := bstep (se 1 (by rfl) ⟨95495, by rfl⟩ : syracuseStep 127327 = 190991) B190991
theorem B389501 : Blo 111784 389501 := bstep (se 3 (by rfl) ⟨73031, by rfl⟩ : syracuseStep 389501 = 146063) B146063
theorem B291215 : Blo 111784 291215 := bstep (se 1 (by rfl) ⟨218411, by rfl⟩ : syracuseStep 291215 = 436823) B436823
theorem B160175 : Blo 111784 160175 := bstep (se 1 (by rfl) ⟨120131, by rfl⟩ : syracuseStep 160175 = 240263) B240263
theorem B192955 : Blo 111784 192955 := bstep (se 1 (by rfl) ⟨144716, by rfl⟩ : syracuseStep 192955 = 289433) B289433
theorem B258569 : Blo 111784 258569 := bstep (se 2 (by rfl) ⟨96963, by rfl⟩ : syracuseStep 258569 = 193927) B193927
theorem B324121 : Blo 111784 324121 := bstep (se 2 (by rfl) ⟨121545, by rfl⟩ : syracuseStep 324121 = 243091) B243091
theorem B193063 : Blo 111784 193063 := bstep (se 1 (by rfl) ⟨144797, by rfl⟩ : syracuseStep 193063 = 289595) B289595
theorem B389771 : Blo 111784 389771 := bstep (se 1 (by rfl) ⟨292328, by rfl⟩ : syracuseStep 389771 = 584657) B584657
theorem B127687 : Blo 111784 127687 := bstep (se 1 (by rfl) ⟨95765, by rfl⟩ : syracuseStep 127687 = 191531) B191531
theorem B291539 : Blo 111784 291539 := bstep (se 1 (by rfl) ⟨218654, by rfl⟩ : syracuseStep 291539 = 437309) B437309
theorem B1700621 : Blo 111784 1700621 := bstep (se 3 (by rfl) ⟨318866, by rfl⟩ : syracuseStep 1700621 = 637733) B637733
theorem B258889 : Blo 111784 258889 := bstep (se 2 (by rfl) ⟨97083, by rfl⟩ : syracuseStep 258889 = 194167) B194167
theorem B258911 : Blo 111784 258911 := bstep (se 1 (by rfl) ⟨194183, by rfl⟩ : syracuseStep 258911 = 388367) B388367
theorem B193387 : Blo 111784 193387 := bstep (se 1 (by rfl) ⟨145040, by rfl⟩ : syracuseStep 193387 = 290081) B290081
theorem B1635329 : Blo 111784 1635329 := bstep (se 2 (by rfl) ⟨613248, by rfl⟩ : syracuseStep 1635329 = 1226497) B1226497
theorem B259091 : Blo 111784 259091 := bstep (se 1 (by rfl) ⟨194318, by rfl⟩ : syracuseStep 259091 = 388637) B388637
theorem B160967 : Blo 111784 160967 := bstep (se 1 (by rfl) ⟨120725, by rfl⟩ : syracuseStep 160967 = 241451) B241451
theorem B259433 : Blo 111784 259433 := bstep (se 2 (by rfl) ⟨97287, by rfl⟩ : syracuseStep 259433 = 194575) B194575
theorem B3339667 : Blo 111784 3339667 := bstep (se 1 (by rfl) ⟨2504750, by rfl⟩ : syracuseStep 3339667 = 5009501) B5009501
theorem B3536369 : Blo 111784 3536369 := bstep (se 2 (by rfl) ⟨1326138, by rfl⟩ : syracuseStep 3536369 = 2652277) B2652277
theorem B390689 : Blo 111784 390689 := bstep (se 2 (by rfl) ⟨146508, by rfl⟩ : syracuseStep 390689 = 293017) B293017
theorem B128551 : Blo 111784 128551 := bstep (se 1 (by rfl) ⟨96413, by rfl⟩ : syracuseStep 128551 = 192827) B192827
theorem B194447 : Blo 111784 194447 := bstep (se 1 (by rfl) ⟨145835, by rfl⟩ : syracuseStep 194447 = 291671) B291671
theorem B358319 : Blo 111784 358319 := bstep (se 1 (by rfl) ⟨268739, by rfl⟩ : syracuseStep 358319 = 537479) B537479
theorem B260027 : Blo 111784 260027 := bstep (se 1 (by rfl) ⟨195020, by rfl⟩ : syracuseStep 260027 = 390041) B390041
theorem B260153 : Blo 111784 260153 := bstep (se 2 (by rfl) ⟨97557, by rfl⟩ : syracuseStep 260153 = 195115) B195115
theorem B194683 : Blo 111784 194683 := bstep (se 1 (by rfl) ⟨146012, by rfl⟩ : syracuseStep 194683 = 292025) B292025
theorem B522557 : Blo 111784 522557 := bstep (se 3 (by rfl) ⟨97979, by rfl⟩ : syracuseStep 522557 = 195959) B195959
theorem B260495 : Blo 111784 260495 := bstep (se 1 (by rfl) ⟨195371, by rfl⟩ : syracuseStep 260495 = 390743) B390743
theorem B490009 : Blo 111784 490009 := bstep (se 2 (by rfl) ⟨183753, by rfl⟩ : syracuseStep 490009 = 367507) B367507
theorem B6454333 : Blo 111784 6454333 := bstep (se 3 (by rfl) ⟨1210187, by rfl⟩ : syracuseStep 6454333 = 2420375) B2420375
theorem B130171 : Blo 111784 130171 := bstep (se 1 (by rfl) ⟨97628, by rfl⟩ : syracuseStep 130171 = 195257) B195257
theorem B1277207 : Blo 111784 1277207 := bstep (se 1 (by rfl) ⟨957905, by rfl⟩ : syracuseStep 1277207 = 1915811) B1915811
theorem B327037 : Blo 111784 327037 := bstep (se 3 (by rfl) ⟨61319, by rfl⟩ : syracuseStep 327037 = 122639) B122639
theorem B163291 : Blo 111784 163291 := bstep (se 1 (by rfl) ⟨122468, by rfl⟩ : syracuseStep 163291 = 244937) B244937
theorem B1245395 : Blo 111784 1245395 := bstep (se 1 (by rfl) ⟨934046, by rfl⟩ : syracuseStep 1245395 = 1868093) B1868093
theorem B426617 : Blo 111784 426617 := bstep (se 2 (by rfl) ⟨159981, by rfl⟩ : syracuseStep 426617 = 319963) B319963
theorem B328313 : Blo 111784 328313 := bstep (se 2 (by rfl) ⟨123117, by rfl⟩ : syracuseStep 328313 = 246235) B246235
theorem B1278665 : Blo 111784 1278665 := bstep (se 2 (by rfl) ⟨479499, by rfl⟩ : syracuseStep 1278665 = 958999) B958999
theorem B131807 : Blo 111784 131807 := bstep (se 1 (by rfl) ⟨98855, by rfl⟩ : syracuseStep 131807 = 197711) B197711
theorem B492281 : Blo 111784 492281 := bstep (se 2 (by rfl) ⟨184605, by rfl⟩ : syracuseStep 492281 = 369211) B369211
theorem B1475405 : Blo 111784 1475405 := bstep (se 3 (by rfl) ⟨276638, by rfl⟩ : syracuseStep 1475405 = 553277) B553277
theorem B852929 : Blo 111784 852929 := bstep (se 2 (by rfl) ⟨319848, by rfl⟩ : syracuseStep 852929 = 639697) B639697
theorem B427133 : Blo 111784 427133 := bstep (se 3 (by rfl) ⟨80087, by rfl⟩ : syracuseStep 427133 = 160175) B160175
theorem B492743 : Blo 111784 492743 := bstep (se 1 (by rfl) ⟨369557, by rfl⟩ : syracuseStep 492743 = 739115) B739115
theorem B492895 : Blo 111784 492895 := bstep (se 1 (by rfl) ⟨369671, by rfl⟩ : syracuseStep 492895 = 739343) B739343
theorem B231007 : Blo 111784 231007 := bstep (se 1 (by rfl) ⟨173255, by rfl⟩ : syracuseStep 231007 = 346511) B346511
theorem B2197115 : Blo 111784 2197115 := bstep (se 1 (by rfl) ⟨1647836, by rfl⟩ : syracuseStep 2197115 = 3295673) B3295673
theorem B1378255 : Blo 111784 1378255 := bstep (se 1 (by rfl) ⟨1033691, by rfl⟩ : syracuseStep 1378255 = 2067383) B2067383
theorem B493697 : Blo 111784 493697 := bstep (se 2 (by rfl) ⟨185136, by rfl⟩ : syracuseStep 493697 = 370273) B370273
theorem B821501 : Blo 111784 821501 := bstep (se 3 (by rfl) ⟨154031, by rfl⟩ : syracuseStep 821501 = 308063) B308063
theorem B788773 : Blo 111784 788773 := bstep (se 4 (by rfl) ⟨73947, by rfl⟩ : syracuseStep 788773 = 147895) B147895
theorem B985517 : Blo 111784 985517 := bstep (se 3 (by rfl) ⟨184784, by rfl⟩ : syracuseStep 985517 = 369569) B369569
theorem B16714421 : Blo 111784 16714421 := bstep (se 5 (by rfl) ⟨783488, by rfl⟩ : syracuseStep 16714421 = 1566977) B1566977
theorem B5442349 : Blo 111784 5442349 := bstep (se 3 (by rfl) ⟨1020440, by rfl⟩ : syracuseStep 5442349 = 2040881) B2040881
theorem B363419 : Blo 111784 363419 := bstep (se 1 (by rfl) ⟨272564, by rfl⟩ : syracuseStep 363419 = 545129) B545129
theorem B887723 : Blo 111784 887723 := bstep (se 1 (by rfl) ⟨665792, by rfl⟩ : syracuseStep 887723 = 1331585) B1331585
theorem B429245 : Blo 111784 429245 := bstep (se 3 (by rfl) ⟨80483, by rfl⟩ : syracuseStep 429245 = 160967) B160967
theorem B658651 : Blo 111784 658651 := bstep (se 1 (by rfl) ⟨493988, by rfl⟩ : syracuseStep 658651 = 987977) B987977
theorem B691487 : Blo 111784 691487 := bstep (se 1 (by rfl) ⟨518615, by rfl⟩ : syracuseStep 691487 = 1037231) B1037231
theorem B789857 : Blo 111784 789857 := bstep (se 2 (by rfl) ⟨296196, by rfl⟩ : syracuseStep 789857 = 592393) B592393
theorem B1248641 : Blo 111784 1248641 := bstep (se 2 (by rfl) ⟨468240, by rfl⟩ : syracuseStep 1248641 = 936481) B936481
theorem B462419 : Blo 111784 462419 := bstep (se 1 (by rfl) ⟨346814, by rfl⟩ : syracuseStep 462419 = 693629) B693629
theorem B17927831 : Blo 111784 17927831 := bstep (se 1 (by rfl) ⟨13445873, by rfl⟩ : syracuseStep 17927831 = 26891747) B26891747
theorem B134831 : Blo 111784 134831 := bstep (se 1 (by rfl) ⟨101123, by rfl⟩ : syracuseStep 134831 = 202247) B202247
theorem B167735 : Blo 111784 167735 := bstep (se 1 (by rfl) ⟨125801, by rfl⟩ : syracuseStep 167735 = 251603) B251603
theorem B2330477 : Blo 111784 2330477 := bstep (se 3 (by rfl) ⟨436964, by rfl⟩ : syracuseStep 2330477 = 873929) B873929
theorem B168041 : Blo 111784 168041 := bstep (se 2 (by rfl) ⟨63015, by rfl⟩ : syracuseStep 168041 = 126031) B126031
theorem B168359 : Blo 111784 168359 := bstep (se 1 (by rfl) ⟨126269, by rfl⟩ : syracuseStep 168359 = 252539) B252539
theorem B1216943 : Blo 111784 1216943 := bstep (se 1 (by rfl) ⟨912707, by rfl⟩ : syracuseStep 1216943 = 1825415) B1825415
theorem B168443 : Blo 111784 168443 := bstep (se 1 (by rfl) ⟨126332, by rfl⟩ : syracuseStep 168443 = 252665) B252665
theorem B168569 : Blo 111784 168569 := bstep (se 2 (by rfl) ⟨63213, by rfl⟩ : syracuseStep 168569 = 126427) B126427
theorem B168623 : Blo 111784 168623 := bstep (se 1 (by rfl) ⟨126467, by rfl⟩ : syracuseStep 168623 = 252935) B252935
theorem B168671 : Blo 111784 168671 := bstep (se 1 (by rfl) ⟨126503, by rfl⟩ : syracuseStep 168671 = 253007) B253007
theorem B4166417 : Blo 111784 4166417 := bstep (se 2 (by rfl) ⟨1562406, by rfl⟩ : syracuseStep 4166417 = 3124813) B3124813
theorem B168935 : Blo 111784 168935 := bstep (se 1 (by rfl) ⟨126701, by rfl⟩ : syracuseStep 168935 = 253403) B253403
theorem B13407437 : Blo 111784 13407437 := bstep (se 3 (by rfl) ⟨2513894, by rfl⟩ : syracuseStep 13407437 = 5027789) B5027789
theorem B857303 : Blo 111784 857303 := bstep (se 1 (by rfl) ⟨642977, by rfl⟩ : syracuseStep 857303 = 1285955) B1285955
theorem B169193 : Blo 111784 169193 := bstep (se 2 (by rfl) ⟨63447, by rfl⟩ : syracuseStep 169193 = 126895) B126895
theorem B169247 : Blo 111784 169247 := bstep (se 1 (by rfl) ⟨126935, by rfl⟩ : syracuseStep 169247 = 253871) B253871
theorem B365867 : Blo 111784 365867 := bstep (se 1 (by rfl) ⟨274400, by rfl⟩ : syracuseStep 365867 = 548801) B548801
theorem B464237 : Blo 111784 464237 := bstep (se 3 (by rfl) ⟨87044, by rfl⟩ : syracuseStep 464237 = 174089) B174089
theorem B169415 : Blo 111784 169415 := bstep (se 1 (by rfl) ⟨127061, by rfl⟩ : syracuseStep 169415 = 254123) B254123
theorem B1251101 : Blo 111784 1251101 := bstep (se 3 (by rfl) ⟨234581, by rfl⟩ : syracuseStep 1251101 = 469163) B469163
theorem B169769 : Blo 111784 169769 := bstep (se 2 (by rfl) ⟨63663, by rfl⟩ : syracuseStep 169769 = 127327) B127327
theorem B169775 : Blo 111784 169775 := bstep (se 1 (by rfl) ⟨127331, by rfl⟩ : syracuseStep 169775 = 254663) B254663
theorem B366391 : Blo 111784 366391 := bstep (se 1 (by rfl) ⟨274793, by rfl⟩ : syracuseStep 366391 = 549587) B549587
theorem B432161 : Blo 111784 432161 := bstep (se 2 (by rfl) ⟨162060, by rfl⟩ : syracuseStep 432161 = 324121) B324121
theorem B170249 : Blo 111784 170249 := bstep (se 2 (by rfl) ⟨63843, by rfl⟩ : syracuseStep 170249 = 127687) B127687
theorem B170351 : Blo 111784 170351 := bstep (se 1 (by rfl) ⟨127763, by rfl⟩ : syracuseStep 170351 = 255527) B255527
theorem B170567 : Blo 111784 170567 := bstep (se 1 (by rfl) ⟨127925, by rfl⟩ : syracuseStep 170567 = 255851) B255851
theorem B170603 : Blo 111784 170603 := bstep (se 1 (by rfl) ⟨127952, by rfl⟩ : syracuseStep 170603 = 255905) B255905
theorem B367211 : Blo 111784 367211 := bstep (se 1 (by rfl) ⟨275408, by rfl⟩ : syracuseStep 367211 = 550817) B550817
theorem B170831 : Blo 111784 170831 := bstep (se 1 (by rfl) ⟨128123, by rfl⟩ : syracuseStep 170831 = 256247) B256247
theorem B957359 : Blo 111784 957359 := bstep (se 1 (by rfl) ⟨718019, by rfl⟩ : syracuseStep 957359 = 1436039) B1436039
theorem B171227 : Blo 111784 171227 := bstep (se 1 (by rfl) ⟨128420, by rfl⟩ : syracuseStep 171227 = 256841) B256841
theorem B171401 : Blo 111784 171401 := bstep (se 2 (by rfl) ⟨64275, by rfl⟩ : syracuseStep 171401 = 128551) B128551
theorem B171755 : Blo 111784 171755 := bstep (se 1 (by rfl) ⟨128816, by rfl⟩ : syracuseStep 171755 = 257633) B257633
theorem B728939 : Blo 111784 728939 := bstep (se 1 (by rfl) ⟨546704, by rfl⟩ : syracuseStep 728939 = 1093409) B1093409
theorem B171983 : Blo 111784 171983 := bstep (se 1 (by rfl) ⟨128987, by rfl⟩ : syracuseStep 171983 = 257975) B257975
theorem B467153 : Blo 111784 467153 := bstep (se 2 (by rfl) ⟨175182, by rfl⟩ : syracuseStep 467153 = 350365) B350365
theorem B172379 : Blo 111784 172379 := bstep (se 1 (by rfl) ⟨129284, by rfl⟩ : syracuseStep 172379 = 258569) B258569
theorem B270803 : Blo 111784 270803 := bstep (se 1 (by rfl) ⟨203102, by rfl⟩ : syracuseStep 270803 = 406205) B406205
theorem B270911 : Blo 111784 270911 := bstep (se 1 (by rfl) ⟨203183, by rfl⟩ : syracuseStep 270911 = 406367) B406367
theorem B172607 : Blo 111784 172607 := bstep (se 1 (by rfl) ⟨129455, by rfl⟩ : syracuseStep 172607 = 258911) B258911
theorem B1090219 : Blo 111784 1090219 := bstep (se 1 (by rfl) ⟨817664, by rfl⟩ : syracuseStep 1090219 = 1635329) B1635329
theorem B172727 : Blo 111784 172727 := bstep (se 1 (by rfl) ⟨129545, by rfl⟩ : syracuseStep 172727 = 259091) B259091
theorem B172955 : Blo 111784 172955 := bstep (se 1 (by rfl) ⟨129716, by rfl⟩ : syracuseStep 172955 = 259433) B259433
theorem B861191 : Blo 111784 861191 := bstep (se 1 (by rfl) ⟨645893, by rfl⟩ : syracuseStep 861191 = 1291787) B1291787
theorem B1025257 : Blo 111784 1025257 := bstep (se 2 (by rfl) ⟨384471, by rfl⟩ : syracuseStep 1025257 = 768943) B768943
theorem B238879 : Blo 111784 238879 := bstep (se 1 (by rfl) ⟨179159, by rfl⟩ : syracuseStep 238879 = 358319) B358319
theorem B173351 : Blo 111784 173351 := bstep (se 1 (by rfl) ⟨130013, by rfl⟩ : syracuseStep 173351 = 260027) B260027
theorem B173435 : Blo 111784 173435 := bstep (se 1 (by rfl) ⟨130076, by rfl⟩ : syracuseStep 173435 = 260153) B260153
theorem B370109 : Blo 111784 370109 := bstep (se 3 (by rfl) ⟨69395, by rfl⟩ : syracuseStep 370109 = 138791) B138791
theorem B173561 : Blo 111784 173561 := bstep (se 2 (by rfl) ⟨65085, by rfl⟩ : syracuseStep 173561 = 130171) B130171
theorem B173663 : Blo 111784 173663 := bstep (se 1 (by rfl) ⟨130247, by rfl⟩ : syracuseStep 173663 = 260495) B260495
theorem B436049 : Blo 111784 436049 := bstep (se 2 (by rfl) ⟨163518, by rfl⟩ : syracuseStep 436049 = 327037) B327037
theorem B141679 : Blo 111784 141679 := bstep (se 1 (by rfl) ⟨106259, by rfl⟩ : syracuseStep 141679 = 212519) B212519
theorem B731927 : Blo 111784 731927 := bstep (se 1 (by rfl) ⟨548945, by rfl⟩ : syracuseStep 731927 = 1097891) B1097891
theorem B306139 : Blo 111784 306139 := bstep (se 1 (by rfl) ⟨229604, by rfl⟩ : syracuseStep 306139 = 459209) B459209
theorem B142555 : Blo 111784 142555 := bstep (se 1 (by rfl) ⟨106916, by rfl⟩ : syracuseStep 142555 = 213833) B213833
theorem B438281 : Blo 111784 438281 := bstep (se 2 (by rfl) ⟨164355, by rfl⟩ : syracuseStep 438281 = 328711) B328711
theorem B1290329 : Blo 111784 1290329 := bstep (se 2 (by rfl) ⟨483873, by rfl⟩ : syracuseStep 1290329 = 967747) B967747
theorem B242347 : Blo 111784 242347 := bstep (se 1 (by rfl) ⟨181760, by rfl⟩ : syracuseStep 242347 = 363521) B363521
theorem B144175 : Blo 111784 144175 := bstep (se 1 (by rfl) ⟨108131, by rfl⟩ : syracuseStep 144175 = 216263) B216263
theorem B111903 : Blo 111784 111903 := bstep (se 1 (by rfl) ⟨83927, by rfl⟩ : syracuseStep 111903 = 167855) B167855
theorem B111963 : Blo 111784 111963 := bstep (se 1 (by rfl) ⟨83972, by rfl⟩ : syracuseStep 111963 = 167945) B167945
theorem B111983 : Blo 111784 111983 := bstep (se 1 (by rfl) ⟨83987, by rfl⟩ : syracuseStep 111983 = 167975) B167975
theorem B112039 : Blo 111784 112039 := bstep (se 1 (by rfl) ⟨84029, by rfl⟩ : syracuseStep 112039 = 168059) B168059
theorem B538093 : Blo 111784 538093 := bstep (se 3 (by rfl) ⟨100892, by rfl⟩ : syracuseStep 538093 = 201785) B201785
theorem B112123 : Blo 111784 112123 := bstep (se 1 (by rfl) ⟨84092, by rfl⟩ : syracuseStep 112123 = 168185) B168185
theorem B570887 : Blo 111784 570887 := bstep (se 1 (by rfl) ⟨428165, by rfl⟩ : syracuseStep 570887 = 856331) B856331
theorem B112191 : Blo 111784 112191 := bstep (se 1 (by rfl) ⟨84143, by rfl⟩ : syracuseStep 112191 = 168287) B168287
theorem B112199 : Blo 111784 112199 := bstep (se 1 (by rfl) ⟨84149, by rfl⟩ : syracuseStep 112199 = 168299) B168299
theorem B243361 : Blo 111784 243361 := bstep (se 2 (by rfl) ⟨91260, by rfl⟩ : syracuseStep 243361 = 182521) B182521
theorem B112351 : Blo 111784 112351 := bstep (se 1 (by rfl) ⟨84263, by rfl⟩ : syracuseStep 112351 = 168527) B168527
theorem B112431 : Blo 111784 112431 := bstep (se 1 (by rfl) ⟨84323, by rfl⟩ : syracuseStep 112431 = 168647) B168647
theorem B112539 : Blo 111784 112539 := bstep (se 1 (by rfl) ⟨84404, by rfl⟩ : syracuseStep 112539 = 168809) B168809
theorem B112591 : Blo 111784 112591 := bstep (se 1 (by rfl) ⟨84443, by rfl⟩ : syracuseStep 112591 = 168887) B168887
theorem B112615 : Blo 111784 112615 := bstep (se 1 (by rfl) ⟨84461, by rfl⟩ : syracuseStep 112615 = 168923) B168923
theorem B571373 : Blo 111784 571373 := bstep (se 3 (by rfl) ⟨107132, by rfl⟩ : syracuseStep 571373 = 214265) B214265
theorem B112927 : Blo 111784 112927 := bstep (se 1 (by rfl) ⟨84695, by rfl⟩ : syracuseStep 112927 = 169391) B169391
theorem B112987 : Blo 111784 112987 := bstep (se 1 (by rfl) ⟨84740, by rfl⟩ : syracuseStep 112987 = 169481) B169481
theorem B113007 : Blo 111784 113007 := bstep (se 1 (by rfl) ⟨84755, by rfl⟩ : syracuseStep 113007 = 169511) B169511
theorem B113063 : Blo 111784 113063 := bstep (se 1 (by rfl) ⟨84797, by rfl⟩ : syracuseStep 113063 = 169595) B169595
theorem B571859 : Blo 111784 571859 := bstep (se 1 (by rfl) ⟨428894, by rfl⟩ : syracuseStep 571859 = 857789) B857789
theorem B113147 : Blo 111784 113147 := bstep (se 1 (by rfl) ⟨84860, by rfl⟩ : syracuseStep 113147 = 169721) B169721
theorem B113215 : Blo 111784 113215 := bstep (se 1 (by rfl) ⟨84911, by rfl⟩ : syracuseStep 113215 = 169823) B169823
theorem B113223 : Blo 111784 113223 := bstep (se 1 (by rfl) ⟨84917, by rfl⟩ : syracuseStep 113223 = 169835) B169835
theorem B113375 : Blo 111784 113375 := bstep (se 1 (by rfl) ⟨85031, by rfl⟩ : syracuseStep 113375 = 170063) B170063
theorem B965357 : Blo 111784 965357 := bstep (se 3 (by rfl) ⟨181004, by rfl⟩ : syracuseStep 965357 = 362009) B362009
theorem B572183 : Blo 111784 572183 := bstep (se 1 (by rfl) ⟨429137, by rfl⟩ : syracuseStep 572183 = 858275) B858275
theorem B113455 : Blo 111784 113455 := bstep (se 1 (by rfl) ⟨85091, by rfl⟩ : syracuseStep 113455 = 170183) B170183
theorem B113563 : Blo 111784 113563 := bstep (se 1 (by rfl) ⟨85172, by rfl⟩ : syracuseStep 113563 = 170345) B170345
theorem B113615 : Blo 111784 113615 := bstep (se 1 (by rfl) ⟨85211, by rfl⟩ : syracuseStep 113615 = 170423) B170423
theorem B113639 : Blo 111784 113639 := bstep (se 1 (by rfl) ⟨85229, by rfl⟩ : syracuseStep 113639 = 170459) B170459
theorem B375997 : Blo 111784 375997 := bstep (se 3 (by rfl) ⟨70499, by rfl⟩ : syracuseStep 375997 = 140999) B140999
theorem B1752293 : Blo 111784 1752293 := bstep (se 4 (by rfl) ⟨164277, by rfl⟩ : syracuseStep 1752293 = 328555) B328555
theorem B113951 : Blo 111784 113951 := bstep (se 1 (by rfl) ⟨85463, by rfl⟩ : syracuseStep 113951 = 170927) B170927
theorem B114011 : Blo 111784 114011 := bstep (se 1 (by rfl) ⟨85508, by rfl⟩ : syracuseStep 114011 = 171017) B171017
theorem B212321 : Blo 111784 212321 := bstep (se 2 (by rfl) ⟨79620, by rfl⟩ : syracuseStep 212321 = 159241) B159241
theorem B114031 : Blo 111784 114031 := bstep (se 1 (by rfl) ⟨85523, by rfl⟩ : syracuseStep 114031 = 171047) B171047
theorem B114087 : Blo 111784 114087 := bstep (se 1 (by rfl) ⟨85565, by rfl⟩ : syracuseStep 114087 = 171131) B171131
theorem B212473 : Blo 111784 212473 := bstep (se 2 (by rfl) ⟨79677, by rfl⟩ : syracuseStep 212473 = 159355) B159355
theorem B114171 : Blo 111784 114171 := bstep (se 1 (by rfl) ⟨85628, by rfl⟩ : syracuseStep 114171 = 171257) B171257
theorem B114239 : Blo 111784 114239 := bstep (se 1 (by rfl) ⟨85679, by rfl⟩ : syracuseStep 114239 = 171359) B171359
theorem B114247 : Blo 111784 114247 := bstep (se 1 (by rfl) ⟨85685, by rfl⟩ : syracuseStep 114247 = 171371) B171371
theorem B736883 : Blo 111784 736883 := bstep (se 1 (by rfl) ⟨552662, by rfl⟩ : syracuseStep 736883 = 1105325) B1105325
theorem B114399 : Blo 111784 114399 := bstep (se 1 (by rfl) ⟨85799, by rfl⟩ : syracuseStep 114399 = 171599) B171599
theorem B212777 : Blo 111784 212777 := bstep (se 2 (by rfl) ⟨79791, by rfl⟩ : syracuseStep 212777 = 159583) B159583
theorem B114479 : Blo 111784 114479 := bstep (se 1 (by rfl) ⟨85859, by rfl⟩ : syracuseStep 114479 = 171719) B171719
theorem B114587 : Blo 111784 114587 := bstep (se 1 (by rfl) ⟨85940, by rfl⟩ : syracuseStep 114587 = 171881) B171881
theorem B114639 : Blo 111784 114639 := bstep (se 1 (by rfl) ⟨85979, by rfl⟩ : syracuseStep 114639 = 171959) B171959
theorem B114663 : Blo 111784 114663 := bstep (se 1 (by rfl) ⟨85997, by rfl⟩ : syracuseStep 114663 = 171995) B171995
theorem B114975 : Blo 111784 114975 := bstep (se 1 (by rfl) ⟨86231, by rfl⟩ : syracuseStep 114975 = 172463) B172463
theorem B115035 : Blo 111784 115035 := bstep (se 1 (by rfl) ⟨86276, by rfl⟩ : syracuseStep 115035 = 172553) B172553
theorem B573803 : Blo 111784 573803 := bstep (se 1 (by rfl) ⟨430352, by rfl⟩ : syracuseStep 573803 = 860705) B860705
theorem B115055 : Blo 111784 115055 := bstep (se 1 (by rfl) ⟨86291, by rfl⟩ : syracuseStep 115055 = 172583) B172583
theorem B115111 : Blo 111784 115111 := bstep (se 1 (by rfl) ⟨86333, by rfl⟩ : syracuseStep 115111 = 172667) B172667
theorem B115195 : Blo 111784 115195 := bstep (se 1 (by rfl) ⟨86396, by rfl⟩ : syracuseStep 115195 = 172793) B172793
theorem B115263 : Blo 111784 115263 := bstep (se 1 (by rfl) ⟨86447, by rfl⟩ : syracuseStep 115263 = 172895) B172895
theorem B115271 : Blo 111784 115271 := bstep (se 1 (by rfl) ⟨86453, by rfl⟩ : syracuseStep 115271 = 172907) B172907
theorem B377567 : Blo 111784 377567 := bstep (se 1 (by rfl) ⟨283175, by rfl⟩ : syracuseStep 377567 = 566351) B566351
theorem B115423 : Blo 111784 115423 := bstep (se 1 (by rfl) ⟨86567, by rfl⟩ : syracuseStep 115423 = 173135) B173135
theorem B213779 : Blo 111784 213779 := bstep (se 1 (by rfl) ⟨160334, by rfl⟩ : syracuseStep 213779 = 320669) B320669
theorem B115503 : Blo 111784 115503 := bstep (se 1 (by rfl) ⟨86627, by rfl⟩ : syracuseStep 115503 = 173255) B173255
theorem B115611 : Blo 111784 115611 := bstep (se 1 (by rfl) ⟨86708, by rfl⟩ : syracuseStep 115611 = 173417) B173417
theorem B213931 : Blo 111784 213931 := bstep (se 1 (by rfl) ⟨160448, by rfl⟩ : syracuseStep 213931 = 320897) B320897
theorem B115663 : Blo 111784 115663 := bstep (se 1 (by rfl) ⟨86747, by rfl⟩ : syracuseStep 115663 = 173495) B173495
theorem B115687 : Blo 111784 115687 := bstep (se 1 (by rfl) ⟨86765, by rfl⟩ : syracuseStep 115687 = 173531) B173531
theorem B345185 : Blo 111784 345185 := bstep (se 2 (by rfl) ⟨129444, by rfl⟩ : syracuseStep 345185 = 258889) B258889
theorem B377999 : Blo 111784 377999 := bstep (se 1 (by rfl) ⟨283499, by rfl⟩ : syracuseStep 377999 = 566999) B566999
theorem B214159 : Blo 111784 214159 := bstep (se 1 (by rfl) ⟨160619, by rfl⟩ : syracuseStep 214159 = 321239) B321239
theorem B214235 : Blo 111784 214235 := bstep (se 1 (by rfl) ⟨160676, by rfl⟩ : syracuseStep 214235 = 321353) B321353
theorem B575261 : Blo 111784 575261 := bstep (se 3 (by rfl) ⟨107861, by rfl⟩ : syracuseStep 575261 = 215723) B215723
theorem B182063 : Blo 111784 182063 := bstep (se 1 (by rfl) ⟨136547, by rfl⟩ : syracuseStep 182063 = 273095) B273095
theorem B1034167 : Blo 111784 1034167 := bstep (se 1 (by rfl) ⟨775625, by rfl⟩ : syracuseStep 1034167 = 1551251) B1551251
theorem B1099727 : Blo 111784 1099727 := bstep (se 1 (by rfl) ⟨824795, by rfl⟩ : syracuseStep 1099727 = 1649591) B1649591
theorem B379133 : Blo 111784 379133 := bstep (se 3 (by rfl) ⟨71087, by rfl⟩ : syracuseStep 379133 = 142175) B142175
theorem B346619 : Blo 111784 346619 := bstep (se 1 (by rfl) ⟨259964, by rfl⟩ : syracuseStep 346619 = 519929) B519929
theorem B248393 : Blo 111784 248393 := bstep (se 2 (by rfl) ⟨93147, by rfl⟩ : syracuseStep 248393 = 186295) B186295
theorem B379943 : Blo 111784 379943 := bstep (se 1 (by rfl) ⟨284957, by rfl⟩ : syracuseStep 379943 = 569915) B569915
theorem B1133747 : Blo 111784 1133747 := bstep (se 1 (by rfl) ⟨850310, by rfl⟩ : syracuseStep 1133747 = 1700621) B1700621
theorem B380375 : Blo 111784 380375 := bstep (se 1 (by rfl) ⟨285281, by rfl⟩ : syracuseStep 380375 = 570563) B570563
theorem B544553 : Blo 111784 544553 := bstep (se 2 (by rfl) ⟨204207, by rfl⟩ : syracuseStep 544553 = 408415) B408415
theorem B8605777 : Blo 111784 8605777 := bstep (se 2 (by rfl) ⟨3227166, by rfl⟩ : syracuseStep 8605777 = 6454333) B6454333
theorem B2445461 : Blo 111784 2445461 := bstep (se 6 (by rfl) ⟨57315, by rfl⟩ : syracuseStep 2445461 = 114631) B114631
theorem B348371 : Blo 111784 348371 := bstep (se 1 (by rfl) ⟨261278, by rfl⟩ : syracuseStep 348371 = 522557) B522557
theorem B414209 : Blo 111784 414209 := bstep (se 2 (by rfl) ⟨155328, by rfl⟩ : syracuseStep 414209 = 310657) B310657
theorem B938557 : Blo 111784 938557 := bstep (se 3 (by rfl) ⟨175979, by rfl⟩ : syracuseStep 938557 = 351959) B351959
theorem B217721 : Blo 111784 217721 := bstep (se 2 (by rfl) ⟨81645, by rfl⟩ : syracuseStep 217721 = 163291) B163291
theorem B382049 : Blo 111784 382049 := bstep (se 2 (by rfl) ⟨143268, by rfl⟩ : syracuseStep 382049 = 286537) B286537
theorem B644345 : Blo 111784 644345 := bstep (se 2 (by rfl) ⟨241629, by rfl⟩ : syracuseStep 644345 = 483259) B483259
theorem B972121 : Blo 111784 972121 := bstep (se 2 (by rfl) ⟨364545, by rfl⟩ : syracuseStep 972121 = 729091) B729091
theorem B1955177 : Blo 111784 1955177 := bstep (se 2 (by rfl) ⟨733191, by rfl⟩ : syracuseStep 1955177 = 1466383) B1466383
theorem B546743 : Blo 111784 546743 := bstep (se 1 (by rfl) ⟨410057, by rfl⟩ : syracuseStep 546743 = 820115) B820115
theorem B251855 : Blo 111784 251855 := bstep (se 1 (by rfl) ⟨188891, by rfl⟩ : syracuseStep 251855 = 377783) B377783
theorem B481261 : Blo 111784 481261 := bstep (se 3 (by rfl) ⟨90236, by rfl⟩ : syracuseStep 481261 = 180473) B180473
theorem B2840777 : Blo 111784 2840777 := bstep (se 2 (by rfl) ⟨1065291, by rfl⟩ : syracuseStep 2840777 = 2130583) B2130583
theorem B973079 : Blo 111784 973079 := bstep (se 1 (by rfl) ⟨729809, by rfl⟩ : syracuseStep 973079 = 1459619) B1459619
theorem B252233 : Blo 111784 252233 := bstep (se 2 (by rfl) ⟨94587, by rfl⟩ : syracuseStep 252233 = 189175) B189175
theorem B252251 : Blo 111784 252251 := bstep (se 1 (by rfl) ⟨189188, by rfl⟩ : syracuseStep 252251 = 378377) B378377
theorem B416111 : Blo 111784 416111 := bstep (se 1 (by rfl) ⟨312083, by rfl⟩ : syracuseStep 416111 = 624167) B624167
theorem B383399 : Blo 111784 383399 := bstep (se 1 (by rfl) ⟨287549, by rfl⟩ : syracuseStep 383399 = 575099) B575099
theorem B383561 : Blo 111784 383561 := bstep (se 2 (by rfl) ⟨143835, by rfl⟩ : syracuseStep 383561 = 287671) B287671
theorem B252827 : Blo 111784 252827 := bstep (se 1 (by rfl) ⟨189620, by rfl⟩ : syracuseStep 252827 = 379241) B379241
theorem B482219 : Blo 111784 482219 := bstep (se 1 (by rfl) ⟨361664, by rfl⟩ : syracuseStep 482219 = 723329) B723329
theorem B253025 : Blo 111784 253025 := bstep (se 2 (by rfl) ⟨94884, by rfl⟩ : syracuseStep 253025 = 189769) B189769
theorem B285839 : Blo 111784 285839 := bstep (se 1 (by rfl) ⟨214379, by rfl⟩ : syracuseStep 285839 = 428759) B428759
theorem B253223 : Blo 111784 253223 := bstep (se 1 (by rfl) ⟨189917, by rfl⟩ : syracuseStep 253223 = 379835) B379835
theorem B580931 : Blo 111784 580931 := bstep (se 1 (by rfl) ⟨435698, by rfl⟩ : syracuseStep 580931 = 871397) B871397
theorem B155129 : Blo 111784 155129 := bstep (se 2 (by rfl) ⟨58173, by rfl⟩ : syracuseStep 155129 = 116347) B116347
theorem B351827 : Blo 111784 351827 := bstep (se 1 (by rfl) ⟨263870, by rfl⟩ : syracuseStep 351827 = 527741) B527741
theorem B253601 : Blo 111784 253601 := bstep (se 2 (by rfl) ⟨95100, by rfl⟩ : syracuseStep 253601 = 190201) B190201
theorem B319211 : Blo 111784 319211 := bstep (se 1 (by rfl) ⟨239408, by rfl⟩ : syracuseStep 319211 = 478817) B478817
theorem B581417 : Blo 111784 581417 := bstep (se 2 (by rfl) ⟨218031, by rfl⟩ : syracuseStep 581417 = 436063) B436063
theorem B548669 : Blo 111784 548669 := bstep (se 3 (by rfl) ⟨102875, by rfl⟩ : syracuseStep 548669 = 205751) B205751
theorem B876395 : Blo 111784 876395 := bstep (se 1 (by rfl) ⟨657296, by rfl⟩ : syracuseStep 876395 = 1314593) B1314593
theorem B974855 : Blo 111784 974855 := bstep (se 1 (by rfl) ⟨731141, by rfl⟩ : syracuseStep 974855 = 1462283) B1462283
theorem B253961 : Blo 111784 253961 := bstep (se 2 (by rfl) ⟨95235, by rfl⟩ : syracuseStep 253961 = 190471) B190471
theorem B385235 : Blo 111784 385235 := bstep (se 1 (by rfl) ⟨288926, by rfl⟩ : syracuseStep 385235 = 577853) B577853
theorem B4645181 : Blo 111784 4645181 := bstep (se 3 (by rfl) ⟨870971, by rfl⟩ : syracuseStep 4645181 = 1741943) B1741943
theorem B254375 : Blo 111784 254375 := bstep (se 1 (by rfl) ⟨190781, by rfl⟩ : syracuseStep 254375 = 381563) B381563
theorem B385505 : Blo 111784 385505 := bstep (se 2 (by rfl) ⟨144564, by rfl⟩ : syracuseStep 385505 = 289129) B289129
theorem B254483 : Blo 111784 254483 := bstep (se 1 (by rfl) ⟨190862, by rfl⟩ : syracuseStep 254483 = 381725) B381725
theorem B123463 : Blo 111784 123463 := bstep (se 1 (by rfl) ⟨92597, by rfl⟩ : syracuseStep 123463 = 185195) B185195
theorem B254537 : Blo 111784 254537 := bstep (se 2 (by rfl) ⟨95451, by rfl⟩ : syracuseStep 254537 = 190903) B190903
theorem B189263 : Blo 111784 189263 := bstep (se 1 (by rfl) ⟨141947, by rfl⟩ : syracuseStep 189263 = 283895) B283895
theorem B254951 : Blo 111784 254951 := bstep (se 1 (by rfl) ⟨191213, by rfl⟩ : syracuseStep 254951 = 382427) B382427
theorem B287783 : Blo 111784 287783 := bstep (se 1 (by rfl) ⟨215837, by rfl⟩ : syracuseStep 287783 = 431675) B431675
theorem B582713 : Blo 111784 582713 := bstep (se 2 (by rfl) ⟨218517, by rfl⟩ : syracuseStep 582713 = 437035) B437035
theorem B255329 : Blo 111784 255329 := bstep (se 2 (by rfl) ⟨95748, by rfl⟩ : syracuseStep 255329 = 191497) B191497
theorem B288137 : Blo 111784 288137 := bstep (se 2 (by rfl) ⟨108051, by rfl⟩ : syracuseStep 288137 = 216103) B216103
theorem B255419 : Blo 111784 255419 := bstep (se 1 (by rfl) ⟨191564, by rfl⟩ : syracuseStep 255419 = 383129) B383129
theorem B255545 : Blo 111784 255545 := bstep (se 2 (by rfl) ⟨95829, by rfl⟩ : syracuseStep 255545 = 191659) B191659
theorem B386747 : Blo 111784 386747 := bstep (se 1 (by rfl) ⟨290060, by rfl⟩ : syracuseStep 386747 = 580121) B580121
theorem B190255 : Blo 111784 190255 := bstep (se 1 (by rfl) ⟨142691, by rfl⟩ : syracuseStep 190255 = 285383) B285383
theorem B256211 : Blo 111784 256211 := bstep (se 1 (by rfl) ⟨192158, by rfl⟩ : syracuseStep 256211 = 384317) B384317
theorem B256265 : Blo 111784 256265 := bstep (se 2 (by rfl) ⟨96099, by rfl⟩ : syracuseStep 256265 = 192199) B192199
theorem B616729 : Blo 111784 616729 := bstep (se 2 (by rfl) ⟨231273, by rfl⟩ : syracuseStep 616729 = 462547) B462547
theorem B551279 : Blo 111784 551279 := bstep (se 1 (by rfl) ⟨413459, by rfl⟩ : syracuseStep 551279 = 826919) B826919
theorem B256481 : Blo 111784 256481 := bstep (se 2 (by rfl) ⟨96180, by rfl⟩ : syracuseStep 256481 = 192361) B192361
theorem B322127 : Blo 111784 322127 := bstep (se 1 (by rfl) ⟨241595, by rfl⟩ : syracuseStep 322127 = 483191) B483191
theorem B813655 : Blo 111784 813655 := bstep (se 1 (by rfl) ⟨610241, by rfl⟩ : syracuseStep 813655 = 1220483) B1220483
theorem B256787 : Blo 111784 256787 := bstep (se 1 (by rfl) ⟨192590, by rfl⟩ : syracuseStep 256787 = 385181) B385181
theorem B289615 : Blo 111784 289615 := bstep (se 1 (by rfl) ⟨217211, by rfl⟩ : syracuseStep 289615 = 434423) B434423
theorem B387965 : Blo 111784 387965 := bstep (se 3 (by rfl) ⟨72743, by rfl⟩ : syracuseStep 387965 = 145487) B145487
theorem B125851 : Blo 111784 125851 := bstep (se 1 (by rfl) ⟨94388, by rfl⟩ : syracuseStep 125851 = 188777) B188777
theorem B289889 : Blo 111784 289889 := bstep (se 2 (by rfl) ⟨108708, by rfl⟩ : syracuseStep 289889 = 217417) B217417
theorem B781427 : Blo 111784 781427 := bstep (se 1 (by rfl) ⟨586070, by rfl⟩ : syracuseStep 781427 = 1172141) B1172141
theorem B584819 : Blo 111784 584819 := bstep (se 1 (by rfl) ⟨438614, by rfl⟩ : syracuseStep 584819 = 877229) B877229
theorem B257147 : Blo 111784 257147 := bstep (se 1 (by rfl) ⟨192860, by rfl⟩ : syracuseStep 257147 = 385721) B385721
theorem B257273 : Blo 111784 257273 := bstep (se 2 (by rfl) ⟨96477, by rfl⟩ : syracuseStep 257273 = 192955) B192955
theorem B552203 : Blo 111784 552203 := bstep (se 1 (by rfl) ⟨414152, by rfl⟩ : syracuseStep 552203 = 828305) B828305
theorem B126247 : Blo 111784 126247 := bstep (se 1 (by rfl) ⟨94685, by rfl⟩ : syracuseStep 126247 = 189371) B189371
theorem B126319 : Blo 111784 126319 := bstep (se 1 (by rfl) ⟨94739, by rfl⟩ : syracuseStep 126319 = 189479) B189479
theorem B257417 : Blo 111784 257417 := bstep (se 2 (by rfl) ⟨96531, by rfl⟩ : syracuseStep 257417 = 193063) B193063
theorem B290263 : Blo 111784 290263 := bstep (se 1 (by rfl) ⟨217697, by rfl⟩ : syracuseStep 290263 = 435395) B435395
theorem B257543 : Blo 111784 257543 := bstep (se 1 (by rfl) ⟨193157, by rfl⟩ : syracuseStep 257543 = 386315) B386315
theorem B1207817 : Blo 111784 1207817 := bstep (se 2 (by rfl) ⟨452931, by rfl⟩ : syracuseStep 1207817 = 905863) B905863
theorem B126535 : Blo 111784 126535 := bstep (se 1 (by rfl) ⟨94901, by rfl⟩ : syracuseStep 126535 = 189803) B189803
theorem B388691 : Blo 111784 388691 := bstep (se 1 (by rfl) ⟨291518, by rfl⟩ : syracuseStep 388691 = 583037) B583037
theorem B650861 : Blo 111784 650861 := bstep (se 3 (by rfl) ⟨122036, by rfl⟩ : syracuseStep 650861 = 244073) B244073
theorem B257723 : Blo 111784 257723 := bstep (se 1 (by rfl) ⟨193292, by rfl⟩ : syracuseStep 257723 = 386585) B386585
theorem B290567 : Blo 111784 290567 := bstep (se 1 (by rfl) ⟨217925, by rfl⟩ : syracuseStep 290567 = 435851) B435851
theorem B257849 : Blo 111784 257849 := bstep (se 2 (by rfl) ⟨96693, by rfl⟩ : syracuseStep 257849 = 193387) B193387
theorem B585629 : Blo 111784 585629 := bstep (se 3 (by rfl) ⟨109805, by rfl⟩ : syracuseStep 585629 = 219611) B219611
theorem B520111 : Blo 111784 520111 := bstep (se 1 (by rfl) ⟨390083, by rfl⟩ : syracuseStep 520111 = 780167) B780167
theorem B716971 : Blo 111784 716971 := bstep (se 1 (by rfl) ⟨537728, by rfl⟩ : syracuseStep 716971 = 1075457) B1075457
theorem B487633 : Blo 111784 487633 := bstep (se 2 (by rfl) ⟨182862, by rfl⟩ : syracuseStep 487633 = 365725) B365725
theorem B3141899 : Blo 111784 3141899 := bstep (se 1 (by rfl) ⟨2356424, by rfl⟩ : syracuseStep 3141899 = 4712849) B4712849
theorem B913679 : Blo 111784 913679 := bstep (se 1 (by rfl) ⟨685259, by rfl⟩ : syracuseStep 913679 = 1370519) B1370519
theorem B127399 : Blo 111784 127399 := bstep (se 1 (by rfl) ⟨95549, by rfl⟩ : syracuseStep 127399 = 191099) B191099
theorem B192935 : Blo 111784 192935 := bstep (se 1 (by rfl) ⟨144701, by rfl⟩ : syracuseStep 192935 = 289403) B289403
theorem B258479 : Blo 111784 258479 := bstep (se 1 (by rfl) ⟨193859, by rfl⟩ : syracuseStep 258479 = 387719) B387719
theorem B258515 : Blo 111784 258515 := bstep (se 1 (by rfl) ⟨193886, by rfl⟩ : syracuseStep 258515 = 387773) B387773
theorem B291347 : Blo 111784 291347 := bstep (se 1 (by rfl) ⟨218510, by rfl⟩ : syracuseStep 291347 = 437021) B437021
theorem B4452889 : Blo 111784 4452889 := bstep (se 2 (by rfl) ⟨1669833, by rfl⟩ : syracuseStep 4452889 = 3339667) B3339667
theorem B258623 : Blo 111784 258623 := bstep (se 1 (by rfl) ⟨193967, by rfl⟩ : syracuseStep 258623 = 387935) B387935
theorem B193097 : Blo 111784 193097 := bstep (se 2 (by rfl) ⟨72411, by rfl⟩ : syracuseStep 193097 = 144823) B144823
theorem B258731 : Blo 111784 258731 := bstep (se 1 (by rfl) ⟨194048, by rfl⟩ : syracuseStep 258731 = 388097) B388097
theorem B1078109 : Blo 111784 1078109 := bstep (se 3 (by rfl) ⟨202145, by rfl⟩ : syracuseStep 1078109 = 404291) B404291
theorem B127975 : Blo 111784 127975 := bstep (se 1 (by rfl) ⟨95981, by rfl⟩ : syracuseStep 127975 = 191963) B191963
theorem B586727 : Blo 111784 586727 := bstep (se 1 (by rfl) ⟨440045, by rfl⟩ : syracuseStep 586727 = 880091) B880091
theorem B717815 : Blo 111784 717815 := bstep (se 1 (by rfl) ⟨538361, by rfl⟩ : syracuseStep 717815 = 1076723) B1076723
theorem B488591 : Blo 111784 488591 := bstep (se 1 (by rfl) ⟨366443, by rfl⟩ : syracuseStep 488591 = 732887) B732887
theorem B849041 : Blo 111784 849041 := bstep (se 2 (by rfl) ⟨318390, by rfl⟩ : syracuseStep 849041 = 636781) B636781
theorem B259271 : Blo 111784 259271 := bstep (se 1 (by rfl) ⟨194453, by rfl⟩ : syracuseStep 259271 = 388907) B388907
theorem B259451 : Blo 111784 259451 := bstep (se 1 (by rfl) ⟨194588, by rfl⟩ : syracuseStep 259451 = 389177) B389177
theorem B292295 : Blo 111784 292295 := bstep (se 1 (by rfl) ⟨219221, by rfl⟩ : syracuseStep 292295 = 438443) B438443
theorem B259577 : Blo 111784 259577 := bstep (se 2 (by rfl) ⟨97341, by rfl⟩ : syracuseStep 259577 = 194683) B194683
theorem B259591 : Blo 111784 259591 := bstep (se 1 (by rfl) ⟨194693, by rfl⟩ : syracuseStep 259591 = 389387) B389387
theorem B128575 : Blo 111784 128575 := bstep (se 1 (by rfl) ⟨96431, by rfl⟩ : syracuseStep 128575 = 192863) B192863
theorem B259667 : Blo 111784 259667 := bstep (se 1 (by rfl) ⟨194750, by rfl⟩ : syracuseStep 259667 = 389501) B389501
theorem B194143 : Blo 111784 194143 := bstep (se 1 (by rfl) ⟨145607, by rfl⟩ : syracuseStep 194143 = 291215) B291215
theorem B259847 : Blo 111784 259847 := bstep (se 1 (by rfl) ⟨194885, by rfl⟩ : syracuseStep 259847 = 389771) B389771
theorem B194359 : Blo 111784 194359 := bstep (se 1 (by rfl) ⟨145769, by rfl⟩ : syracuseStep 194359 = 291539) B291539
theorem B653345 : Blo 111784 653345 := bstep (se 2 (by rfl) ⟨245004, by rfl⟩ : syracuseStep 653345 = 490009) B490009
theorem B194825 : Blo 111784 194825 := bstep (se 2 (by rfl) ⟨73059, by rfl⟩ : syracuseStep 194825 = 146119) B146119
theorem B2357579 : Blo 111784 2357579 := bstep (se 1 (by rfl) ⟨1768184, by rfl⟩ : syracuseStep 2357579 = 3536369) B3536369
theorem B260459 : Blo 111784 260459 := bstep (se 1 (by rfl) ⟨195344, by rfl⟩ : syracuseStep 260459 = 390689) B390689
theorem B293371 : Blo 111784 293371 := bstep (se 1 (by rfl) ⟨220028, by rfl⟩ : syracuseStep 293371 = 440057) B440057
theorem B129631 : Blo 111784 129631 := bstep (se 1 (by rfl) ⟨97223, by rfl⟩ : syracuseStep 129631 = 194447) B194447
theorem B162425 : Blo 111784 162425 := bstep (se 2 (by rfl) ⟨60909, by rfl⟩ : syracuseStep 162425 = 121819) B121819
theorem B1145707 : Blo 111784 1145707 := bstep (se 1 (by rfl) ⟨859280, by rfl⟩ : syracuseStep 1145707 = 1718561) B1718561
theorem B982205 : Blo 111784 982205 := bstep (se 3 (by rfl) ⟨184163, by rfl⟩ : syracuseStep 982205 = 368327) B368327
theorem B589193 : Blo 111784 589193 := bstep (se 2 (by rfl) ⟨220947, by rfl⟩ : syracuseStep 589193 = 441895) B441895
theorem B490967 : Blo 111784 490967 := bstep (se 1 (by rfl) ⟨368225, by rfl⟩ : syracuseStep 490967 = 736451) B736451
theorem B851471 : Blo 111784 851471 := bstep (se 1 (by rfl) ⟨638603, by rfl⟩ : syracuseStep 851471 = 1277207) B1277207
theorem B1638005 : Blo 111784 1638005 := bstep (se 5 (by rfl) ⟨76781, by rfl⟩ : syracuseStep 1638005 = 153563) B153563
theorem B425857 : Blo 111784 425857 := bstep (se 2 (by rfl) ⟨159696, by rfl⟩ : syracuseStep 425857 = 319393) B319393
theorem B852443 : Blo 111784 852443 := bstep (se 1 (by rfl) ⟨639332, by rfl⟩ : syracuseStep 852443 = 1278665) B1278665
theorem B328187 : Blo 111784 328187 := bstep (se 1 (by rfl) ⟨246140, by rfl⟩ : syracuseStep 328187 = 492281) B492281
theorem B983603 : Blo 111784 983603 := bstep (se 1 (by rfl) ⟨737702, by rfl⟩ : syracuseStep 983603 = 1475405) B1475405
theorem B230123 : Blo 111784 230123 := bstep (se 1 (by rfl) ⟨172592, by rfl⟩ : syracuseStep 230123 = 345185) B345185
theorem B328495 : Blo 111784 328495 := bstep (se 1 (by rfl) ⟨246371, by rfl⟩ : syracuseStep 328495 = 492743) B492743
theorem B329131 : Blo 111784 329131 := bstep (se 1 (by rfl) ⟨246848, by rfl⟩ : syracuseStep 329131 = 493697) B493697
theorem B722429 : Blo 111784 722429 := bstep (se 3 (by rfl) ⟨135455, by rfl⟩ : syracuseStep 722429 = 270911) B270911
theorem B657011 : Blo 111784 657011 := bstep (se 1 (by rfl) ⟨492758, by rfl⟩ : syracuseStep 657011 = 985517) B985517
theorem B11142947 : Blo 111784 11142947 := bstep (se 1 (by rfl) ⟨8357210, by rfl⟩ : syracuseStep 11142947 = 16714421) B16714421
theorem B657193 : Blo 111784 657193 := bstep (se 2 (by rfl) ⟨246447, by rfl⟩ : syracuseStep 657193 = 492895) B492895
theorem B591815 : Blo 111784 591815 := bstep (se 1 (by rfl) ⟨443861, by rfl⟩ : syracuseStep 591815 = 887723) B887723
theorem B755831 : Blo 111784 755831 := bstep (se 1 (by rfl) ⟨566873, by rfl⟩ : syracuseStep 755831 = 1133747) B1133747
theorem B460991 : Blo 111784 460991 := bstep (se 1 (by rfl) ⟨345743, by rfl⟩ : syracuseStep 460991 = 691487) B691487
theorem B526571 : Blo 111784 526571 := bstep (se 1 (by rfl) ⟨394928, by rfl⟩ : syracuseStep 526571 = 789857) B789857
theorem B363035 : Blo 111784 363035 := bstep (se 1 (by rfl) ⟨272276, by rfl⟩ : syracuseStep 363035 = 544553) B544553
theorem B1378889 : Blo 111784 1378889 := bstep (se 2 (by rfl) ⟨517083, by rfl⟩ : syracuseStep 1378889 = 1034167) B1034167
theorem B1837673 : Blo 111784 1837673 := bstep (se 2 (by rfl) ⟨689127, by rfl⟩ : syracuseStep 1837673 = 1378255) B1378255
theorem B232247 : Blo 111784 232247 := bstep (se 1 (by rfl) ⟨174185, by rfl⟩ : syracuseStep 232247 = 348371) B348371
theorem B822305 : Blo 111784 822305 := bstep (se 2 (by rfl) ⟨308364, by rfl⟩ : syracuseStep 822305 = 616729) B616729
theorem B658469 : Blo 111784 658469 := bstep (se 4 (by rfl) ⟨61731, by rfl⟩ : syracuseStep 658469 = 123463) B123463
theorem B1051697 : Blo 111784 1051697 := bstep (se 2 (by rfl) ⟨394386, by rfl⟩ : syracuseStep 1051697 = 788773) B788773
theorem B1084873 : Blo 111784 1084873 := bstep (se 2 (by rfl) ⟨406827, by rfl⟩ : syracuseStep 1084873 = 813655) B813655
theorem B429563 : Blo 111784 429563 := bstep (se 1 (by rfl) ⟨322172, by rfl⟩ : syracuseStep 429563 = 644345) B644345
theorem B167801 : Blo 111784 167801 := bstep (se 2 (by rfl) ⟨62925, by rfl⟩ : syracuseStep 167801 = 125851) B125851
theorem B364495 : Blo 111784 364495 := bstep (se 1 (by rfl) ⟨273371, by rfl⟩ : syracuseStep 364495 = 546743) B546743
theorem B167903 : Blo 111784 167903 := bstep (se 1 (by rfl) ⟨125927, by rfl⟩ : syracuseStep 167903 = 251855) B251855
theorem B168155 : Blo 111784 168155 := bstep (se 1 (by rfl) ⟨126116, by rfl⟩ : syracuseStep 168155 = 252233) B252233
theorem B168167 : Blo 111784 168167 := bstep (se 1 (by rfl) ⟨126125, by rfl⟩ : syracuseStep 168167 = 252251) B252251
theorem B168329 : Blo 111784 168329 := bstep (se 2 (by rfl) ⟨63123, by rfl⟩ : syracuseStep 168329 = 126247) B126247
theorem B168425 : Blo 111784 168425 := bstep (se 2 (by rfl) ⟨63159, by rfl⟩ : syracuseStep 168425 = 126319) B126319
theorem B168551 : Blo 111784 168551 := bstep (se 1 (by rfl) ⟨126413, by rfl⟩ : syracuseStep 168551 = 252827) B252827
theorem B168683 : Blo 111784 168683 := bstep (se 1 (by rfl) ⟨126512, by rfl⟩ : syracuseStep 168683 = 253025) B253025
theorem B168713 : Blo 111784 168713 := bstep (se 2 (by rfl) ⟨63267, by rfl⟩ : syracuseStep 168713 = 126535) B126535
theorem B168815 : Blo 111784 168815 := bstep (se 1 (by rfl) ⟨126611, by rfl⟩ : syracuseStep 168815 = 253223) B253223
theorem B234551 : Blo 111784 234551 := bstep (se 1 (by rfl) ⟨175913, by rfl⟩ : syracuseStep 234551 = 351827) B351827
theorem B169067 : Blo 111784 169067 := bstep (se 1 (by rfl) ⟨126800, by rfl⟩ : syracuseStep 169067 = 253601) B253601
theorem B365779 : Blo 111784 365779 := bstep (se 1 (by rfl) ⟨274334, by rfl⟩ : syracuseStep 365779 = 548669) B548669
theorem B693481 : Blo 111784 693481 := bstep (se 2 (by rfl) ⟨260055, by rfl⟩ : syracuseStep 693481 = 520111) B520111
theorem B169307 : Blo 111784 169307 := bstep (se 1 (by rfl) ⟨126980, by rfl⟩ : syracuseStep 169307 = 253961) B253961
theorem B11474369 : Blo 111784 11474369 := bstep (se 2 (by rfl) ⟨4302888, by rfl⟩ : syracuseStep 11474369 = 8605777) B8605777
theorem B955961 : Blo 111784 955961 := bstep (se 2 (by rfl) ⟨358485, by rfl⟩ : syracuseStep 955961 = 716971) B716971
theorem B169583 : Blo 111784 169583 := bstep (se 1 (by rfl) ⟨127187, by rfl⟩ : syracuseStep 169583 = 254375) B254375
theorem B169655 : Blo 111784 169655 := bstep (se 1 (by rfl) ⟨127241, by rfl⟩ : syracuseStep 169655 = 254483) B254483
theorem B169691 : Blo 111784 169691 := bstep (se 1 (by rfl) ⟨127268, by rfl⟩ : syracuseStep 169691 = 254537) B254537
theorem B169865 : Blo 111784 169865 := bstep (se 2 (by rfl) ⟨63699, by rfl⟩ : syracuseStep 169865 = 127399) B127399
theorem B169967 : Blo 111784 169967 := bstep (se 1 (by rfl) ⟨127475, by rfl⟩ : syracuseStep 169967 = 254951) B254951
theorem B5937185 : Blo 111784 5937185 := bstep (se 2 (by rfl) ⟨2226444, by rfl⟩ : syracuseStep 5937185 = 4452889) B4452889
theorem B1251409 : Blo 111784 1251409 := bstep (se 2 (by rfl) ⟨469278, by rfl⟩ : syracuseStep 1251409 = 938557) B938557
theorem B170219 : Blo 111784 170219 := bstep (se 1 (by rfl) ⟨127664, by rfl⟩ : syracuseStep 170219 = 255329) B255329
theorem B170279 : Blo 111784 170279 := bstep (se 1 (by rfl) ⟨127709, by rfl⟩ : syracuseStep 170279 = 255419) B255419
theorem B170363 : Blo 111784 170363 := bstep (se 1 (by rfl) ⟨127772, by rfl⟩ : syracuseStep 170363 = 255545) B255545
theorem B170633 : Blo 111784 170633 := bstep (se 2 (by rfl) ⟨63987, by rfl⟩ : syracuseStep 170633 = 127975) B127975
theorem B924317 : Blo 111784 924317 := bstep (se 3 (by rfl) ⟨173309, by rfl⟩ : syracuseStep 924317 = 346619) B346619
theorem B170807 : Blo 111784 170807 := bstep (se 1 (by rfl) ⟨128105, by rfl⟩ : syracuseStep 170807 = 256211) B256211
theorem B170843 : Blo 111784 170843 := bstep (se 1 (by rfl) ⟨128132, by rfl⟩ : syracuseStep 170843 = 256265) B256265
theorem B662381 : Blo 111784 662381 := bstep (se 3 (by rfl) ⟨124196, by rfl⟩ : syracuseStep 662381 = 248393) B248393
theorem B367519 : Blo 111784 367519 := bstep (se 1 (by rfl) ⟨275639, by rfl⟩ : syracuseStep 367519 = 551279) B551279
theorem B170987 : Blo 111784 170987 := bstep (se 1 (by rfl) ⟨128240, by rfl⟩ : syracuseStep 170987 = 256481) B256481
theorem B433133 : Blo 111784 433133 := bstep (se 3 (by rfl) ⟨81212, by rfl⟩ : syracuseStep 433133 = 162425) B162425
theorem B171191 : Blo 111784 171191 := bstep (se 1 (by rfl) ⟨128393, by rfl⟩ : syracuseStep 171191 = 256787) B256787
theorem B171431 : Blo 111784 171431 := bstep (se 1 (by rfl) ⟨128573, by rfl⟩ : syracuseStep 171431 = 257147) B257147
theorem B171433 : Blo 111784 171433 := bstep (se 2 (by rfl) ⟨64287, by rfl⟩ : syracuseStep 171433 = 128575) B128575
theorem B171515 : Blo 111784 171515 := bstep (se 1 (by rfl) ⟨128636, by rfl⟩ : syracuseStep 171515 = 257273) B257273
theorem B368135 : Blo 111784 368135 := bstep (se 1 (by rfl) ⟨276101, by rfl⟩ : syracuseStep 368135 = 552203) B552203
theorem B171611 : Blo 111784 171611 := bstep (se 1 (by rfl) ⟨128708, by rfl⟩ : syracuseStep 171611 = 257417) B257417
theorem B171695 : Blo 111784 171695 := bstep (se 1 (by rfl) ⟨128771, by rfl⟩ : syracuseStep 171695 = 257543) B257543
theorem B433907 : Blo 111784 433907 := bstep (se 1 (by rfl) ⟨325430, by rfl⟩ : syracuseStep 433907 = 650861) B650861
theorem B171815 : Blo 111784 171815 := bstep (se 1 (by rfl) ⟨128861, by rfl⟩ : syracuseStep 171815 = 257723) B257723
theorem B171899 : Blo 111784 171899 := bstep (se 1 (by rfl) ⟨128924, by rfl⟩ : syracuseStep 171899 = 257849) B257849
theorem B860219 : Blo 111784 860219 := bstep (se 1 (by rfl) ⟨645164, by rfl⟩ : syracuseStep 860219 = 1290329) B1290329
theorem B172319 : Blo 111784 172319 := bstep (se 1 (by rfl) ⟨129239, by rfl⟩ : syracuseStep 172319 = 258479) B258479
theorem B172343 : Blo 111784 172343 := bstep (se 1 (by rfl) ⟨129257, by rfl⟩ : syracuseStep 172343 = 258515) B258515
theorem B172415 : Blo 111784 172415 := bstep (se 1 (by rfl) ⟨129311, by rfl⟩ : syracuseStep 172415 = 258623) B258623
theorem B172487 : Blo 111784 172487 := bstep (se 1 (by rfl) ⟨129365, by rfl⟩ : syracuseStep 172487 = 258731) B258731
theorem B566027 : Blo 111784 566027 := bstep (se 1 (by rfl) ⟨424520, by rfl⟩ : syracuseStep 566027 = 849041) B849041
theorem B172841 : Blo 111784 172841 := bstep (se 2 (by rfl) ⟨64815, by rfl⟩ : syracuseStep 172841 = 129631) B129631
theorem B172847 : Blo 111784 172847 := bstep (se 1 (by rfl) ⟨129635, by rfl⟩ : syracuseStep 172847 = 259271) B259271
theorem B172967 : Blo 111784 172967 := bstep (se 1 (by rfl) ⟨129725, by rfl⟩ : syracuseStep 172967 = 259451) B259451
theorem B566189 : Blo 111784 566189 := bstep (se 3 (by rfl) ⟨106160, by rfl⟩ : syracuseStep 566189 = 212321) B212321
theorem B173051 : Blo 111784 173051 := bstep (se 1 (by rfl) ⟨129788, by rfl⟩ : syracuseStep 173051 = 259577) B259577
theorem B173111 : Blo 111784 173111 := bstep (se 1 (by rfl) ⟨129833, by rfl⟩ : syracuseStep 173111 = 259667) B259667
theorem B173231 : Blo 111784 173231 := bstep (se 1 (by rfl) ⟨129923, by rfl⟩ : syracuseStep 173231 = 259847) B259847
theorem B435563 : Blo 111784 435563 := bstep (se 1 (by rfl) ⟨326672, by rfl⟩ : syracuseStep 435563 = 653345) B653345
theorem B173639 : Blo 111784 173639 := bstep (se 1 (by rfl) ⟨130229, by rfl⟩ : syracuseStep 173639 = 260459) B260459
theorem B501329 : Blo 111784 501329 := bstep (se 2 (by rfl) ⟨187998, by rfl⟩ : syracuseStep 501329 = 375997) B375997
theorem B4368013 : Blo 111784 4368013 := bstep (se 3 (by rfl) ⟨819002, by rfl⟩ : syracuseStep 4368013 = 1638005) B1638005
theorem B567647 : Blo 111784 567647 := bstep (se 1 (by rfl) ⟨425735, by rfl⟩ : syracuseStep 567647 = 851471) B851471
theorem B567809 : Blo 111784 567809 := bstep (se 2 (by rfl) ⟨212928, by rfl⟩ : syracuseStep 567809 = 425857) B425857
theorem B141851 : Blo 111784 141851 := bstep (se 1 (by rfl) ⟨106388, by rfl⟩ : syracuseStep 141851 = 212777) B212777
theorem B830263 : Blo 111784 830263 := bstep (se 1 (by rfl) ⟨622697, by rfl⟩ : syracuseStep 830263 = 1245395) B1245395
theorem B568619 : Blo 111784 568619 := bstep (se 1 (by rfl) ⟨426464, by rfl⟩ : syracuseStep 568619 = 852929) B852929
theorem B142823 : Blo 111784 142823 := bstep (se 1 (by rfl) ⟨107117, by rfl⟩ : syracuseStep 142823 = 214235) B214235
theorem B1453625 : Blo 111784 1453625 := bstep (se 2 (by rfl) ⟨545109, by rfl⟩ : syracuseStep 1453625 = 1090219) B1090219
theorem B733151 : Blo 111784 733151 := bstep (se 1 (by rfl) ⟨549863, by rfl⟩ : syracuseStep 733151 = 1099727) B1099727
theorem B242279 : Blo 111784 242279 := bstep (se 1 (by rfl) ⟨181709, by rfl⟩ : syracuseStep 242279 = 363419) B363419
theorem B570077 : Blo 111784 570077 := bstep (se 3 (by rfl) ⟨106889, by rfl⟩ : syracuseStep 570077 = 213779) B213779
theorem B308009 : Blo 111784 308009 := bstep (se 2 (by rfl) ⟨115503, by rfl⟩ : syracuseStep 308009 = 231007) B231007
theorem B832427 : Blo 111784 832427 := bstep (se 1 (by rfl) ⟨624320, by rfl⟩ : syracuseStep 832427 = 1248641) B1248641
theorem B308279 : Blo 111784 308279 := bstep (se 1 (by rfl) ⟨231209, by rfl⟩ : syracuseStep 308279 = 462419) B462419
theorem B111823 : Blo 111784 111823 := bstep (se 1 (by rfl) ⟨83867, by rfl⟩ : syracuseStep 111823 = 167735) B167735
theorem B1553651 : Blo 111784 1553651 := bstep (se 1 (by rfl) ⟨1165238, by rfl⟩ : syracuseStep 1553651 = 2330477) B2330477
theorem B112027 : Blo 111784 112027 := bstep (se 1 (by rfl) ⟨84020, by rfl⟩ : syracuseStep 112027 = 168041) B168041
theorem B112239 : Blo 111784 112239 := bstep (se 1 (by rfl) ⟨84179, by rfl⟩ : syracuseStep 112239 = 168359) B168359
theorem B112295 : Blo 111784 112295 := bstep (se 1 (by rfl) ⟨84221, by rfl⟩ : syracuseStep 112295 = 168443) B168443
theorem B276139 : Blo 111784 276139 := bstep (se 1 (by rfl) ⟨207104, by rfl⟩ : syracuseStep 276139 = 414209) B414209
theorem B112379 : Blo 111784 112379 := bstep (se 1 (by rfl) ⟨84284, by rfl⟩ : syracuseStep 112379 = 168569) B168569
theorem B145147 : Blo 111784 145147 := bstep (se 1 (by rfl) ⟨108860, by rfl⟩ : syracuseStep 145147 = 217721) B217721
theorem B112415 : Blo 111784 112415 := bstep (se 1 (by rfl) ⟨84311, by rfl⟩ : syracuseStep 112415 = 168623) B168623
theorem B112447 : Blo 111784 112447 := bstep (se 1 (by rfl) ⟨84335, by rfl⟩ : syracuseStep 112447 = 168671) B168671
theorem B112623 : Blo 111784 112623 := bstep (se 1 (by rfl) ⟨84467, by rfl⟩ : syracuseStep 112623 = 168935) B168935
theorem B571535 : Blo 111784 571535 := bstep (se 1 (by rfl) ⟨428651, by rfl⟩ : syracuseStep 571535 = 857303) B857303
theorem B112795 : Blo 111784 112795 := bstep (se 1 (by rfl) ⟨84596, by rfl⟩ : syracuseStep 112795 = 169193) B169193
theorem B112831 : Blo 111784 112831 := bstep (se 1 (by rfl) ⟨84623, by rfl⟩ : syracuseStep 112831 = 169247) B169247
theorem B243911 : Blo 111784 243911 := bstep (se 1 (by rfl) ⟨182933, by rfl⟩ : syracuseStep 243911 = 365867) B365867
theorem B309491 : Blo 111784 309491 := bstep (se 1 (by rfl) ⟨232118, by rfl⟩ : syracuseStep 309491 = 464237) B464237
theorem B112943 : Blo 111784 112943 := bstep (se 1 (by rfl) ⟨84707, by rfl⟩ : syracuseStep 112943 = 169415) B169415
theorem B7256465 : Blo 111784 7256465 := bstep (se 2 (by rfl) ⟨2721174, by rfl⟩ : syracuseStep 7256465 = 5442349) B5442349
theorem B834067 : Blo 111784 834067 := bstep (se 1 (by rfl) ⟨625550, by rfl⟩ : syracuseStep 834067 = 1251101) B1251101
theorem B113179 : Blo 111784 113179 := bstep (se 1 (by rfl) ⟨84884, by rfl⟩ : syracuseStep 113179 = 169769) B169769
theorem B113183 : Blo 111784 113183 := bstep (se 1 (by rfl) ⟨84887, by rfl⟩ : syracuseStep 113183 = 169775) B169775
theorem B408185 : Blo 111784 408185 := bstep (se 2 (by rfl) ⟨153069, by rfl⟩ : syracuseStep 408185 = 306139) B306139
theorem B113499 : Blo 111784 113499 := bstep (se 1 (by rfl) ⟨85124, by rfl⟩ : syracuseStep 113499 = 170249) B170249
theorem B113567 : Blo 111784 113567 := bstep (se 1 (by rfl) ⟨85175, by rfl⟩ : syracuseStep 113567 = 170351) B170351
theorem B113711 : Blo 111784 113711 := bstep (se 1 (by rfl) ⟨85283, by rfl⟩ : syracuseStep 113711 = 170567) B170567
theorem B113735 : Blo 111784 113735 := bstep (se 1 (by rfl) ⟨85301, by rfl⟩ : syracuseStep 113735 = 170603) B170603
theorem B113887 : Blo 111784 113887 := bstep (se 1 (by rfl) ⟨85415, by rfl⟩ : syracuseStep 113887 = 170831) B170831
theorem B6110437 : Blo 111784 6110437 := bstep (se 4 (by rfl) ⟨572853, by rfl⟩ : syracuseStep 6110437 = 1145707) B1145707
theorem B638239 : Blo 111784 638239 := bstep (se 1 (by rfl) ⟨478679, by rfl⟩ : syracuseStep 638239 = 957359) B957359
theorem B114151 : Blo 111784 114151 := bstep (se 1 (by rfl) ⟨85613, by rfl⟩ : syracuseStep 114151 = 171227) B171227
theorem B114267 : Blo 111784 114267 := bstep (se 1 (by rfl) ⟨85700, by rfl⟩ : syracuseStep 114267 = 171401) B171401
theorem B212807 : Blo 111784 212807 := bstep (se 1 (by rfl) ⟨159605, by rfl⟩ : syracuseStep 212807 = 319211) B319211
theorem B114503 : Blo 111784 114503 := bstep (se 1 (by rfl) ⟨85877, by rfl⟩ : syracuseStep 114503 = 171755) B171755
theorem B114655 : Blo 111784 114655 := bstep (se 1 (by rfl) ⟨85991, by rfl⟩ : syracuseStep 114655 = 171983) B171983
theorem B311435 : Blo 111784 311435 := bstep (se 1 (by rfl) ⟨233576, by rfl⟩ : syracuseStep 311435 = 467153) B467153
theorem B3096787 : Blo 111784 3096787 := bstep (se 1 (by rfl) ⟨2322590, by rfl⟩ : syracuseStep 3096787 = 4645181) B4645181
theorem B114919 : Blo 111784 114919 := bstep (se 1 (by rfl) ⟨86189, by rfl⟩ : syracuseStep 114919 = 172379) B172379
theorem B180535 : Blo 111784 180535 := bstep (se 1 (by rfl) ⟨135401, by rfl⟩ : syracuseStep 180535 = 270803) B270803
theorem B115071 : Blo 111784 115071 := bstep (se 1 (by rfl) ⟨86303, by rfl⟩ : syracuseStep 115071 = 172607) B172607
theorem B115151 : Blo 111784 115151 := bstep (se 1 (by rfl) ⟨86363, by rfl⟩ : syracuseStep 115151 = 172727) B172727
theorem B115303 : Blo 111784 115303 := bstep (se 1 (by rfl) ⟨86477, by rfl⟩ : syracuseStep 115303 = 172955) B172955
theorem B574127 : Blo 111784 574127 := bstep (se 1 (by rfl) ⟨430595, by rfl⟩ : syracuseStep 574127 = 861191) B861191
theorem B115567 : Blo 111784 115567 := bstep (se 1 (by rfl) ⟨86675, by rfl⟩ : syracuseStep 115567 = 173351) B173351
theorem B115623 : Blo 111784 115623 := bstep (se 1 (by rfl) ⟨86717, by rfl⟩ : syracuseStep 115623 = 173435) B173435
theorem B246739 : Blo 111784 246739 := bstep (se 1 (by rfl) ⟨185054, by rfl⟩ : syracuseStep 246739 = 370109) B370109
theorem B115707 : Blo 111784 115707 := bstep (se 1 (by rfl) ⟨86780, by rfl⟩ : syracuseStep 115707 = 173561) B173561
theorem B115775 : Blo 111784 115775 := bstep (se 1 (by rfl) ⟨86831, by rfl⟩ : syracuseStep 115775 = 173663) B173663
theorem B214751 : Blo 111784 214751 := bstep (se 1 (by rfl) ⟨161063, by rfl⟩ : syracuseStep 214751 = 322127) B322127
theorem B1296161 : Blo 111784 1296161 := bstep (se 2 (by rfl) ⟨486060, by rfl⟩ : syracuseStep 1296161 = 972121) B972121
theorem B346121 : Blo 111784 346121 := bstep (se 2 (by rfl) ⟨129795, by rfl⟩ : syracuseStep 346121 = 259591) B259591
theorem B805211 : Blo 111784 805211 := bstep (se 1 (by rfl) ⟨603908, by rfl⟩ : syracuseStep 805211 = 1207817) B1207817
theorem B641681 : Blo 111784 641681 := bstep (se 2 (by rfl) ⟨240630, by rfl⟩ : syracuseStep 641681 = 481261) B481261
theorem B609119 : Blo 111784 609119 := bstep (se 1 (by rfl) ⟨456839, by rfl⟩ : syracuseStep 609119 = 913679) B913679
theorem B478543 : Blo 111784 478543 := bstep (se 1 (by rfl) ⟨358907, by rfl⟩ : syracuseStep 478543 = 717815) B717815
theorem B380591 : Blo 111784 380591 := bstep (se 1 (by rfl) ⟨285443, by rfl⟩ : syracuseStep 380591 = 570887) B570887
theorem B413677 : Blo 111784 413677 := bstep (se 3 (by rfl) ⟨77564, by rfl⟩ : syracuseStep 413677 = 155129) B155129
theorem B380915 : Blo 111784 380915 := bstep (se 1 (by rfl) ⟨285686, by rfl⟩ : syracuseStep 380915 = 571373) B571373
theorem B381239 : Blo 111784 381239 := bstep (se 1 (by rfl) ⟨285929, by rfl⟩ : syracuseStep 381239 = 571859) B571859
theorem B643571 : Blo 111784 643571 := bstep (se 1 (by rfl) ⟨482678, by rfl⟩ : syracuseStep 643571 = 965357) B965357
theorem B381455 : Blo 111784 381455 := bstep (se 1 (by rfl) ⟨286091, by rfl⟩ : syracuseStep 381455 = 572183) B572183
theorem B283297 : Blo 111784 283297 := bstep (se 2 (by rfl) ⟨106236, by rfl⟩ : syracuseStep 283297 = 212473) B212473
theorem B1168195 : Blo 111784 1168195 := bstep (se 1 (by rfl) ⟨876146, by rfl⟩ : syracuseStep 1168195 = 1752293) B1752293
theorem B382535 : Blo 111784 382535 := bstep (se 1 (by rfl) ⟨286901, by rfl⟩ : syracuseStep 382535 = 573803) B573803
theorem B284411 : Blo 111784 284411 := bstep (se 1 (by rfl) ⟨213308, by rfl⟩ : syracuseStep 284411 = 426617) B426617
theorem B218875 : Blo 111784 218875 := bstep (se 1 (by rfl) ⟨164156, by rfl⟩ : syracuseStep 218875 = 328313) B328313
theorem B251711 : Blo 111784 251711 := bstep (se 1 (by rfl) ⟨188783, by rfl⟩ : syracuseStep 251711 = 377567) B377567
theorem B284755 : Blo 111784 284755 := bstep (se 1 (by rfl) ⟨213566, by rfl⟩ : syracuseStep 284755 = 427133) B427133
theorem B251999 : Blo 111784 251999 := bstep (se 1 (by rfl) ⟨188999, by rfl⟩ : syracuseStep 251999 = 377999) B377999
theorem B1464743 : Blo 111784 1464743 := bstep (se 1 (by rfl) ⟨1098557, by rfl⟩ : syracuseStep 1464743 = 2197115) B2197115
theorem B383507 : Blo 111784 383507 := bstep (se 1 (by rfl) ⟨287630, by rfl⟩ : syracuseStep 383507 = 575261) B575261
theorem B121375 : Blo 111784 121375 := bstep (se 1 (by rfl) ⟨91031, by rfl⟩ : syracuseStep 121375 = 182063) B182063
theorem B285241 : Blo 111784 285241 := bstep (se 2 (by rfl) ⟨106965, by rfl⟩ : syracuseStep 285241 = 213931) B213931
theorem B252755 : Blo 111784 252755 := bstep (se 1 (by rfl) ⟨189566, by rfl⟩ : syracuseStep 252755 = 379133) B379133
theorem B547667 : Blo 111784 547667 := bstep (se 1 (by rfl) ⟨410750, by rfl⟩ : syracuseStep 547667 = 821501) B821501
theorem B285545 : Blo 111784 285545 := bstep (se 2 (by rfl) ⟨107079, by rfl⟩ : syracuseStep 285545 = 214159) B214159
theorem B1367009 : Blo 111784 1367009 := bstep (se 2 (by rfl) ⟨512628, by rfl⟩ : syracuseStep 1367009 = 1025257) B1025257
theorem B318505 : Blo 111784 318505 := bstep (se 2 (by rfl) ⟨119439, by rfl⟩ : syracuseStep 318505 = 238879) B238879
theorem B351485 : Blo 111784 351485 := bstep (se 3 (by rfl) ⟨65903, by rfl⟩ : syracuseStep 351485 = 131807) B131807
theorem B253295 : Blo 111784 253295 := bstep (se 1 (by rfl) ⟨189971, by rfl⟩ : syracuseStep 253295 = 379943) B379943
theorem B286163 : Blo 111784 286163 := bstep (se 1 (by rfl) ⟨214622, by rfl⟩ : syracuseStep 286163 = 429245) B429245
theorem B253583 : Blo 111784 253583 := bstep (se 1 (by rfl) ⟨190187, by rfl⟩ : syracuseStep 253583 = 380375) B380375
theorem B253673 : Blo 111784 253673 := bstep (se 2 (by rfl) ⟨95127, by rfl⟩ : syracuseStep 253673 = 190255) B190255
theorem B11951887 : Blo 111784 11951887 := bstep (se 1 (by rfl) ⟨8963915, by rfl⟩ : syracuseStep 11951887 = 17927831) B17927831
theorem B1564645 : Blo 111784 1564645 := bstep (se 4 (by rfl) ⟨146685, by rfl⟩ : syracuseStep 1564645 = 293371) B293371
theorem B1630307 : Blo 111784 1630307 := bstep (se 1 (by rfl) ⟨1222730, by rfl⟩ : syracuseStep 1630307 = 2445461) B2445461
theorem B811295 : Blo 111784 811295 := bstep (se 1 (by rfl) ⟨608471, by rfl⟩ : syracuseStep 811295 = 1216943) B1216943
theorem B188905 : Blo 111784 188905 := bstep (se 2 (by rfl) ⟨70839, by rfl⟩ : syracuseStep 188905 = 141679) B141679
theorem B2777611 : Blo 111784 2777611 := bstep (se 1 (by rfl) ⟨2083208, by rfl⟩ : syracuseStep 2777611 = 4166417) B4166417
theorem B254699 : Blo 111784 254699 := bstep (se 1 (by rfl) ⟨191024, by rfl⟩ : syracuseStep 254699 = 382049) B382049
theorem B8938291 : Blo 111784 8938291 := bstep (se 1 (by rfl) ⟨6703718, by rfl⟩ : syracuseStep 8938291 = 13407437) B13407437
theorem B1303451 : Blo 111784 1303451 := bstep (se 1 (by rfl) ⟨977588, by rfl⟩ : syracuseStep 1303451 = 1955177) B1955177
theorem B386153 : Blo 111784 386153 := bstep (se 2 (by rfl) ⟨144807, by rfl⟩ : syracuseStep 386153 = 289615) B289615
theorem B779453 : Blo 111784 779453 := bstep (se 3 (by rfl) ⟨146147, by rfl⟩ : syracuseStep 779453 = 292295) B292295
theorem B288107 : Blo 111784 288107 := bstep (se 1 (by rfl) ⟨216080, by rfl⟩ : syracuseStep 288107 = 432161) B432161
theorem B1893851 : Blo 111784 1893851 := bstep (se 1 (by rfl) ⟨1420388, by rfl⟩ : syracuseStep 1893851 = 2840777) B2840777
theorem B648719 : Blo 111784 648719 := bstep (se 1 (by rfl) ⟨486539, by rfl⟩ : syracuseStep 648719 = 973079) B973079
theorem B255599 : Blo 111784 255599 := bstep (se 1 (by rfl) ⟨191699, by rfl⟩ : syracuseStep 255599 = 383399) B383399
theorem B190073 : Blo 111784 190073 := bstep (se 2 (by rfl) ⟨71277, by rfl⟩ : syracuseStep 190073 = 142555) B142555
theorem B878201 : Blo 111784 878201 := bstep (se 2 (by rfl) ⟨329325, by rfl⟩ : syracuseStep 878201 = 658651) B658651
theorem B255707 : Blo 111784 255707 := bstep (se 1 (by rfl) ⟨191780, by rfl⟩ : syracuseStep 255707 = 383561) B383561
theorem B321479 : Blo 111784 321479 := bstep (se 1 (by rfl) ⟨241109, by rfl⟩ : syracuseStep 321479 = 482219) B482219
theorem B387017 : Blo 111784 387017 := bstep (se 2 (by rfl) ⟨145131, by rfl⟩ : syracuseStep 387017 = 290263) B290263
theorem B190559 : Blo 111784 190559 := bstep (se 1 (by rfl) ⟨142919, by rfl⟩ : syracuseStep 190559 = 285839) B285839
theorem B387287 : Blo 111784 387287 := bstep (se 1 (by rfl) ⟨290465, by rfl⟩ : syracuseStep 387287 = 580931) B580931
theorem B387611 : Blo 111784 387611 := bstep (se 1 (by rfl) ⟨290708, by rfl⟩ : syracuseStep 387611 = 581417) B581417
theorem B485959 : Blo 111784 485959 := bstep (se 1 (by rfl) ⟨364469, by rfl⟩ : syracuseStep 485959 = 728939) B728939
theorem B584263 : Blo 111784 584263 := bstep (se 1 (by rfl) ⟨438197, by rfl⟩ : syracuseStep 584263 = 876395) B876395
theorem B649903 : Blo 111784 649903 := bstep (se 1 (by rfl) ⟨487427, by rfl⟩ : syracuseStep 649903 = 974855) B974855
theorem B256823 : Blo 111784 256823 := bstep (se 1 (by rfl) ⟨192617, by rfl⟩ : syracuseStep 256823 = 385235) B385235
theorem B650177 : Blo 111784 650177 := bstep (se 2 (by rfl) ⟨243816, by rfl⟩ : syracuseStep 650177 = 487633) B487633
theorem B257003 : Blo 111784 257003 := bstep (se 1 (by rfl) ⟨192752, by rfl⟩ : syracuseStep 257003 = 385505) B385505
theorem B126175 : Blo 111784 126175 := bstep (se 1 (by rfl) ⟨94631, by rfl⟩ : syracuseStep 126175 = 189263) B189263
theorem B191855 : Blo 111784 191855 := bstep (se 1 (by rfl) ⟨143891, by rfl⟩ : syracuseStep 191855 = 287783) B287783
theorem B388475 : Blo 111784 388475 := bstep (se 1 (by rfl) ⟨291356, by rfl⟩ : syracuseStep 388475 = 582713) B582713
theorem B323129 : Blo 111784 323129 := bstep (se 2 (by rfl) ⟨121173, by rfl⟩ : syracuseStep 323129 = 242347) B242347
theorem B192091 : Blo 111784 192091 := bstep (se 1 (by rfl) ⟨144068, by rfl⟩ : syracuseStep 192091 = 288137) B288137
theorem B1109629 : Blo 111784 1109629 := bstep (se 3 (by rfl) ⟨208055, by rfl⟩ : syracuseStep 1109629 = 416111) B416111
theorem B192233 : Blo 111784 192233 := bstep (se 2 (by rfl) ⟨72087, by rfl⟩ : syracuseStep 192233 = 144175) B144175
theorem B257831 : Blo 111784 257831 := bstep (se 1 (by rfl) ⟨193373, by rfl⟩ : syracuseStep 257831 = 386747) B386747
theorem B290699 : Blo 111784 290699 := bstep (se 1 (by rfl) ⟨218024, by rfl⟩ : syracuseStep 290699 = 436049) B436049
theorem B979229 : Blo 111784 979229 := bstep (se 3 (by rfl) ⟨183605, by rfl⟩ : syracuseStep 979229 = 367211) B367211
theorem B487951 : Blo 111784 487951 := bstep (se 1 (by rfl) ⟨365963, by rfl⟩ : syracuseStep 487951 = 731927) B731927
theorem B258643 : Blo 111784 258643 := bstep (se 1 (by rfl) ⟨193982, by rfl⟩ : syracuseStep 258643 = 387965) B387965
theorem B717457 : Blo 111784 717457 := bstep (se 2 (by rfl) ⟨269046, by rfl⟩ : syracuseStep 717457 = 538093) B538093
theorem B193259 : Blo 111784 193259 := bstep (se 1 (by rfl) ⟨144944, by rfl⟩ : syracuseStep 193259 = 289889) B289889
theorem B520951 : Blo 111784 520951 := bstep (se 1 (by rfl) ⟨390713, by rfl⟩ : syracuseStep 520951 = 781427) B781427
theorem B389879 : Blo 111784 389879 := bstep (se 1 (by rfl) ⟨292409, by rfl⟩ : syracuseStep 389879 = 584819) B584819
theorem B258857 : Blo 111784 258857 := bstep (se 2 (by rfl) ⟨97071, by rfl⟩ : syracuseStep 258857 = 194143) B194143
theorem B324481 : Blo 111784 324481 := bstep (se 2 (by rfl) ⟨121680, by rfl⟩ : syracuseStep 324481 = 243361) B243361
theorem B259127 : Blo 111784 259127 := bstep (se 1 (by rfl) ⟨194345, by rfl⟩ : syracuseStep 259127 = 388691) B388691
theorem B488521 : Blo 111784 488521 := bstep (se 2 (by rfl) ⟨183195, by rfl⟩ : syracuseStep 488521 = 366391) B366391
theorem B259145 : Blo 111784 259145 := bstep (se 2 (by rfl) ⟨97179, by rfl⟩ : syracuseStep 259145 = 194359) B194359
theorem B193711 : Blo 111784 193711 := bstep (se 1 (by rfl) ⟨145283, by rfl⟩ : syracuseStep 193711 = 290567) B290567
theorem B390419 : Blo 111784 390419 := bstep (se 1 (by rfl) ⟨292814, by rfl⟩ : syracuseStep 390419 = 585629) B585629
theorem B292187 : Blo 111784 292187 := bstep (se 1 (by rfl) ⟨219140, by rfl⟩ : syracuseStep 292187 = 438281) B438281
theorem B2094599 : Blo 111784 2094599 := bstep (se 1 (by rfl) ⟨1570949, by rfl⟩ : syracuseStep 2094599 = 3141899) B3141899
theorem B128623 : Blo 111784 128623 := bstep (se 1 (by rfl) ⟨96467, by rfl⟩ : syracuseStep 128623 = 192935) B192935
theorem B194231 : Blo 111784 194231 := bstep (se 1 (by rfl) ⟨145673, by rfl⟩ : syracuseStep 194231 = 291347) B291347
theorem B128731 : Blo 111784 128731 := bstep (se 1 (by rfl) ⟨96548, by rfl⟩ : syracuseStep 128731 = 193097) B193097
theorem B718739 : Blo 111784 718739 := bstep (se 1 (by rfl) ⟨539054, by rfl⟩ : syracuseStep 718739 = 1078109) B1078109
theorem B391151 : Blo 111784 391151 := bstep (se 1 (by rfl) ⟨293363, by rfl⟩ : syracuseStep 391151 = 586727) B586727
theorem B325727 : Blo 111784 325727 := bstep (se 1 (by rfl) ⟨244295, by rfl⟩ : syracuseStep 325727 = 488591) B488591
theorem B129883 : Blo 111784 129883 := bstep (se 1 (by rfl) ⟨97412, by rfl⟩ : syracuseStep 129883 = 194825) B194825
theorem B1571719 : Blo 111784 1571719 := bstep (se 1 (by rfl) ⟨1178789, by rfl⟩ : syracuseStep 1571719 = 2357579) B2357579
theorem B359549 : Blo 111784 359549 := bstep (se 3 (by rfl) ⟨67415, by rfl⟩ : syracuseStep 359549 = 134831) B134831
theorem B654803 : Blo 111784 654803 := bstep (se 1 (by rfl) ⟨491102, by rfl⟩ : syracuseStep 654803 = 982205) B982205
theorem B392795 : Blo 111784 392795 := bstep (se 1 (by rfl) ⟨294596, by rfl⟩ : syracuseStep 392795 = 589193) B589193
theorem B327311 : Blo 111784 327311 := bstep (se 1 (by rfl) ⟨245483, by rfl⟩ : syracuseStep 327311 = 490967) B490967
theorem B491255 : Blo 111784 491255 := bstep (se 1 (by rfl) ⟨368441, by rfl⟩ : syracuseStep 491255 = 736883) B736883
theorem B4129049 : Blo 111784 4129049 := bstep (se 2 (by rfl) ⟨1548393, by rfl⟩ : syracuseStep 4129049 = 3096787) B3096787
theorem B655735 : Blo 111784 655735 := bstep (se 1 (by rfl) ⟨491801, by rfl⟩ : syracuseStep 655735 = 983603) B983603
theorem B3703481 : Blo 111784 3703481 := bstep (se 2 (by rfl) ⟨1388805, by rfl⟩ : syracuseStep 3703481 = 2777611) B2777611
theorem B328985 : Blo 111784 328985 := bstep (se 2 (by rfl) ⟨123369, by rfl⟩ : syracuseStep 328985 = 246739) B246739
theorem B394543 : Blo 111784 394543 := bstep (se 1 (by rfl) ⟨295907, by rfl⟩ : syracuseStep 394543 = 591815) B591815
theorem B230747 : Blo 111784 230747 := bstep (se 1 (by rfl) ⟨173060, by rfl⟩ : syracuseStep 230747 = 346121) B346121
theorem B919259 : Blo 111784 919259 := bstep (se 1 (by rfl) ⟨689444, by rfl⟩ : syracuseStep 919259 = 1378889) B1378889
theorem B427787 : Blo 111784 427787 := bstep (se 1 (by rfl) ⟨320840, by rfl⟩ : syracuseStep 427787 = 641681) B641681
theorem B429047 : Blo 111784 429047 := bstep (se 1 (by rfl) ⟨321785, by rfl⟩ : syracuseStep 429047 = 643571) B643571
theorem B1379429 : Blo 111784 1379429 := bstep (se 4 (by rfl) ⟨129321, by rfl⟩ : syracuseStep 1379429 = 258643) B258643
theorem B167807 : Blo 111784 167807 := bstep (se 1 (by rfl) ⟨125855, by rfl⟩ : syracuseStep 167807 = 251711) B251711
theorem B167999 : Blo 111784 167999 := bstep (se 1 (by rfl) ⟨125999, by rfl⟩ : syracuseStep 167999 = 251999) B251999
theorem B168233 : Blo 111784 168233 := bstep (se 2 (by rfl) ⟨63087, by rfl⟩ : syracuseStep 168233 = 126175) B126175
theorem B168503 : Blo 111784 168503 := bstep (se 1 (by rfl) ⟨126377, by rfl⟩ : syracuseStep 168503 = 252755) B252755
theorem B365111 : Blo 111784 365111 := bstep (se 1 (by rfl) ⟨273833, by rfl⟩ : syracuseStep 365111 = 547667) B547667
theorem B1446497 : Blo 111784 1446497 := bstep (se 2 (by rfl) ⟨542436, by rfl⟩ : syracuseStep 1446497 = 1084873) B1084873
theorem B1479505 : Blo 111784 1479505 := bstep (se 2 (by rfl) ⟨554814, by rfl⟩ : syracuseStep 1479505 = 1109629) B1109629
theorem B234323 : Blo 111784 234323 := bstep (se 1 (by rfl) ⟨175742, by rfl⟩ : syracuseStep 234323 = 351485) B351485
theorem B168863 : Blo 111784 168863 := bstep (se 1 (by rfl) ⟨126647, by rfl⟩ : syracuseStep 168863 = 253295) B253295
theorem B169055 : Blo 111784 169055 := bstep (se 1 (by rfl) ⟨126791, by rfl⟩ : syracuseStep 169055 = 253583) B253583
theorem B169115 : Blo 111784 169115 := bstep (se 1 (by rfl) ⟨126836, by rfl⟩ : syracuseStep 169115 = 253673) B253673
theorem B1086871 : Blo 111784 1086871 := bstep (se 1 (by rfl) ⟨815153, by rfl⟩ : syracuseStep 1086871 = 1630307) B1630307
theorem B15832493 : Blo 111784 15832493 := bstep (se 3 (by rfl) ⟨2968592, by rfl⟩ : syracuseStep 15832493 = 5937185) B5937185
theorem B169799 : Blo 111784 169799 := bstep (se 1 (by rfl) ⟨127349, by rfl⟩ : syracuseStep 169799 = 254699) B254699
theorem B956609 : Blo 111784 956609 := bstep (se 2 (by rfl) ⟨358728, by rfl⟩ : syracuseStep 956609 = 717457) B717457
theorem B694601 : Blo 111784 694601 := bstep (se 2 (by rfl) ⟨260475, by rfl⟩ : syracuseStep 694601 = 520951) B520951
theorem B432479 : Blo 111784 432479 := bstep (se 1 (by rfl) ⟨324359, by rfl⟩ : syracuseStep 432479 = 648719) B648719
theorem B334219 : Blo 111784 334219 := bstep (se 1 (by rfl) ⟨250664, by rfl⟩ : syracuseStep 334219 = 501329) B501329
theorem B170399 : Blo 111784 170399 := bstep (se 1 (by rfl) ⟨127799, by rfl⟩ : syracuseStep 170399 = 255599) B255599
theorem B170471 : Blo 111784 170471 := bstep (se 1 (by rfl) ⟨127853, by rfl⟩ : syracuseStep 170471 = 255707) B255707
theorem B432641 : Blo 111784 432641 := bstep (se 2 (by rfl) ⟨162240, by rfl⟩ : syracuseStep 432641 = 324481) B324481
theorem B924641 : Blo 111784 924641 := bstep (se 2 (by rfl) ⟨346740, by rfl⟩ : syracuseStep 924641 = 693481) B693481
theorem B171215 : Blo 111784 171215 := bstep (se 1 (by rfl) ⟨128411, by rfl⟩ : syracuseStep 171215 = 256823) B256823
theorem B433451 : Blo 111784 433451 := bstep (se 1 (by rfl) ⟨325088, by rfl⟩ : syracuseStep 433451 = 650177) B650177
theorem B171335 : Blo 111784 171335 := bstep (se 1 (by rfl) ⟨128501, by rfl⟩ : syracuseStep 171335 = 257003) B257003
theorem B171497 : Blo 111784 171497 := bstep (se 2 (by rfl) ⟨64311, by rfl⟩ : syracuseStep 171497 = 128623) B128623
theorem B171641 : Blo 111784 171641 := bstep (se 2 (by rfl) ⟨64365, by rfl⟩ : syracuseStep 171641 = 128731) B128731
theorem B171887 : Blo 111784 171887 := bstep (se 1 (by rfl) ⟨128915, by rfl⟩ : syracuseStep 171887 = 257831) B257831
theorem B205339 : Blo 111784 205339 := bstep (se 1 (by rfl) ⟨154004, by rfl⟩ : syracuseStep 205339 = 308009) B308009
theorem B172571 : Blo 111784 172571 := bstep (se 1 (by rfl) ⟨129428, by rfl⟩ : syracuseStep 172571 = 258857) B258857
theorem B205519 : Blo 111784 205519 := bstep (se 1 (by rfl) ⟨154139, by rfl⟩ : syracuseStep 205519 = 308279) B308279
theorem B172751 : Blo 111784 172751 := bstep (se 1 (by rfl) ⟨129563, by rfl⟩ : syracuseStep 172751 = 259127) B259127
theorem B172763 : Blo 111784 172763 := bstep (se 1 (by rfl) ⟨129572, by rfl⟩ : syracuseStep 172763 = 259145) B259145
theorem B173177 : Blo 111784 173177 := bstep (se 2 (by rfl) ⟨64941, by rfl⟩ : syracuseStep 173177 = 129883) B129883
theorem B861677 : Blo 111784 861677 := bstep (se 3 (by rfl) ⟨161564, by rfl⟩ : syracuseStep 861677 = 323129) B323129
theorem B206327 : Blo 111784 206327 := bstep (se 1 (by rfl) ⟨154745, by rfl⟩ : syracuseStep 206327 = 309491) B309491
theorem B272123 : Blo 111784 272123 := bstep (se 1 (by rfl) ⟨204092, by rfl⟩ : syracuseStep 272123 = 408185) B408185
theorem B239699 : Blo 111784 239699 := bstep (se 1 (by rfl) ⟨179774, by rfl⟩ : syracuseStep 239699 = 359549) B359549
theorem B567485 : Blo 111784 567485 := bstep (se 3 (by rfl) ⟨106403, by rfl⟩ : syracuseStep 567485 = 212807) B212807
theorem B436535 : Blo 111784 436535 := bstep (se 1 (by rfl) ⟨327401, by rfl⟩ : syracuseStep 436535 = 654803) B654803
theorem B15935849 : Blo 111784 15935849 := bstep (se 2 (by rfl) ⟨5975943, by rfl⟩ : syracuseStep 15935849 = 11951887) B11951887
theorem B207623 : Blo 111784 207623 := bstep (se 1 (by rfl) ⟨155717, by rfl⟩ : syracuseStep 207623 = 311435) B311435
theorem B568295 : Blo 111784 568295 := bstep (se 1 (by rfl) ⟨426221, by rfl⟩ : syracuseStep 568295 = 852443) B852443
theorem B240713 : Blo 111784 240713 := bstep (se 2 (by rfl) ⟨90267, by rfl⟩ : syracuseStep 240713 = 180535) B180535
theorem B437993 : Blo 111784 437993 := bstep (se 2 (by rfl) ⟨164247, by rfl⟩ : syracuseStep 437993 = 328495) B328495
theorem B438007 : Blo 111784 438007 := bstep (se 1 (by rfl) ⟨328505, by rfl⟩ : syracuseStep 438007 = 657011) B657011
theorem B864107 : Blo 111784 864107 := bstep (se 1 (by rfl) ⟨648080, by rfl⟩ : syracuseStep 864107 = 1296161) B1296161
theorem B307327 : Blo 111784 307327 := bstep (se 1 (by rfl) ⟨230495, by rfl⟩ : syracuseStep 307327 = 460991) B460991
theorem B536807 : Blo 111784 536807 := bstep (se 1 (by rfl) ⟨402605, by rfl⟩ : syracuseStep 536807 = 805211) B805211
theorem B242023 : Blo 111784 242023 := bstep (se 1 (by rfl) ⟨181517, by rfl⟩ : syracuseStep 242023 = 363035) B363035
theorem B1225115 : Blo 111784 1225115 := bstep (se 1 (by rfl) ⟨918836, by rfl⟩ : syracuseStep 1225115 = 1837673) B1837673
theorem B438841 : Blo 111784 438841 := bstep (se 2 (by rfl) ⟨164565, by rfl⟩ : syracuseStep 438841 = 329131) B329131
theorem B406079 : Blo 111784 406079 := bstep (se 1 (by rfl) ⟨304559, by rfl⟩ : syracuseStep 406079 = 609119) B609119
theorem B438979 : Blo 111784 438979 := bstep (se 1 (by rfl) ⟨329234, by rfl⟩ : syracuseStep 438979 = 658469) B658469
theorem B701131 : Blo 111784 701131 := bstep (se 1 (by rfl) ⟨525848, by rfl⟩ : syracuseStep 701131 = 1051697) B1051697
theorem B111867 : Blo 111784 111867 := bstep (se 1 (by rfl) ⟨83900, by rfl⟩ : syracuseStep 111867 = 167801) B167801
theorem B111935 : Blo 111784 111935 := bstep (se 1 (by rfl) ⟨83951, by rfl⟩ : syracuseStep 111935 = 167903) B167903
theorem B2602405 : Blo 111784 2602405 := bstep (se 4 (by rfl) ⟨243975, by rfl⟩ : syracuseStep 2602405 = 487951) B487951
theorem B112103 : Blo 111784 112103 := bstep (se 1 (by rfl) ⟨84077, by rfl⟩ : syracuseStep 112103 = 168155) B168155
theorem B112111 : Blo 111784 112111 := bstep (se 1 (by rfl) ⟨84083, by rfl⟩ : syracuseStep 112111 = 168167) B168167
theorem B112219 : Blo 111784 112219 := bstep (se 1 (by rfl) ⟨84164, by rfl⟩ : syracuseStep 112219 = 168329) B168329
theorem B112283 : Blo 111784 112283 := bstep (se 1 (by rfl) ⟨84212, by rfl⟩ : syracuseStep 112283 = 168425) B168425
theorem B112367 : Blo 111784 112367 := bstep (se 1 (by rfl) ⟨84275, by rfl⟩ : syracuseStep 112367 = 168551) B168551
theorem B112455 : Blo 111784 112455 := bstep (se 1 (by rfl) ⟨84341, by rfl⟩ : syracuseStep 112455 = 168683) B168683
theorem B112475 : Blo 111784 112475 := bstep (se 1 (by rfl) ⟨84356, by rfl⟩ : syracuseStep 112475 = 168713) B168713
theorem B112543 : Blo 111784 112543 := bstep (se 1 (by rfl) ⟨84407, by rfl⟩ : syracuseStep 112543 = 168815) B168815
theorem B112711 : Blo 111784 112711 := bstep (se 1 (by rfl) ⟨84533, by rfl⟩ : syracuseStep 112711 = 169067) B169067
theorem B112871 : Blo 111784 112871 := bstep (se 1 (by rfl) ⟨84653, by rfl⟩ : syracuseStep 112871 = 169307) B169307
theorem B866537 : Blo 111784 866537 := bstep (se 2 (by rfl) ⟨324951, by rfl⟩ : syracuseStep 866537 = 649903) B649903
theorem B7649579 : Blo 111784 7649579 := bstep (se 1 (by rfl) ⟨5737184, by rfl⟩ : syracuseStep 7649579 = 11474369) B11474369
theorem B637307 : Blo 111784 637307 := bstep (se 1 (by rfl) ⟨477980, by rfl⟩ : syracuseStep 637307 = 955961) B955961
theorem B113055 : Blo 111784 113055 := bstep (se 1 (by rfl) ⟨84791, by rfl⟩ : syracuseStep 113055 = 169583) B169583
theorem B113103 : Blo 111784 113103 := bstep (se 1 (by rfl) ⟨84827, by rfl⟩ : syracuseStep 113103 = 169655) B169655
theorem B113127 : Blo 111784 113127 := bstep (se 1 (by rfl) ⟨84845, by rfl⟩ : syracuseStep 113127 = 169691) B169691
theorem B113243 : Blo 111784 113243 := bstep (se 1 (by rfl) ⟨84932, by rfl⟩ : syracuseStep 113243 = 169865) B169865
theorem B113311 : Blo 111784 113311 := bstep (se 1 (by rfl) ⟨84983, by rfl⟩ : syracuseStep 113311 = 169967) B169967
theorem B5585597 : Blo 111784 5585597 := bstep (se 3 (by rfl) ⟨1047299, by rfl⟩ : syracuseStep 5585597 = 2094599) B2094599
theorem B113479 : Blo 111784 113479 := bstep (se 1 (by rfl) ⟨85109, by rfl⟩ : syracuseStep 113479 = 170219) B170219
theorem B113519 : Blo 111784 113519 := bstep (se 1 (by rfl) ⟨85139, by rfl⟩ : syracuseStep 113519 = 170279) B170279
theorem B113575 : Blo 111784 113575 := bstep (se 1 (by rfl) ⟨85181, by rfl⟩ : syracuseStep 113575 = 170363) B170363
theorem B113755 : Blo 111784 113755 := bstep (se 1 (by rfl) ⟨85316, by rfl⟩ : syracuseStep 113755 = 170633) B170633
theorem B638057 : Blo 111784 638057 := bstep (se 2 (by rfl) ⟨239271, by rfl⟩ : syracuseStep 638057 = 478543) B478543
theorem B113871 : Blo 111784 113871 := bstep (se 1 (by rfl) ⟨85403, by rfl⟩ : syracuseStep 113871 = 170807) B170807
theorem B113895 : Blo 111784 113895 := bstep (se 1 (by rfl) ⟨85421, by rfl⟩ : syracuseStep 113895 = 170843) B170843
theorem B441587 : Blo 111784 441587 := bstep (se 1 (by rfl) ⟨331190, by rfl⟩ : syracuseStep 441587 = 662381) B662381
theorem B572669 : Blo 111784 572669 := bstep (se 3 (by rfl) ⟨107375, by rfl⟩ : syracuseStep 572669 = 214751) B214751
theorem B113991 : Blo 111784 113991 := bstep (se 1 (by rfl) ⟨85493, by rfl⟩ : syracuseStep 113991 = 170987) B170987
theorem B114127 : Blo 111784 114127 := bstep (se 1 (by rfl) ⟨85595, by rfl⟩ : syracuseStep 114127 = 171191) B171191
theorem B114287 : Blo 111784 114287 := bstep (se 1 (by rfl) ⟨85715, by rfl⟩ : syracuseStep 114287 = 171431) B171431
theorem B114343 : Blo 111784 114343 := bstep (se 1 (by rfl) ⟨85757, by rfl⟩ : syracuseStep 114343 = 171515) B171515
theorem B245423 : Blo 111784 245423 := bstep (se 1 (by rfl) ⟨184067, by rfl⟩ : syracuseStep 245423 = 368135) B368135
theorem B114407 : Blo 111784 114407 := bstep (se 1 (by rfl) ⟨85805, by rfl⟩ : syracuseStep 114407 = 171611) B171611
theorem B114463 : Blo 111784 114463 := bstep (se 1 (by rfl) ⟨85847, by rfl⟩ : syracuseStep 114463 = 171695) B171695
theorem B114543 : Blo 111784 114543 := bstep (se 1 (by rfl) ⟨85907, by rfl⟩ : syracuseStep 114543 = 171815) B171815
theorem B114599 : Blo 111784 114599 := bstep (se 1 (by rfl) ⟨85949, by rfl⟩ : syracuseStep 114599 = 171899) B171899
theorem B573479 : Blo 111784 573479 := bstep (se 1 (by rfl) ⟨430109, by rfl⟩ : syracuseStep 573479 = 860219) B860219
theorem B540863 : Blo 111784 540863 := bstep (se 1 (by rfl) ⟨405647, by rfl⟩ : syracuseStep 540863 = 811295) B811295
theorem B114879 : Blo 111784 114879 := bstep (se 1 (by rfl) ⟨86159, by rfl⟩ : syracuseStep 114879 = 172319) B172319
theorem B114895 : Blo 111784 114895 := bstep (se 1 (by rfl) ⟨86171, by rfl⟩ : syracuseStep 114895 = 172343) B172343
theorem B114943 : Blo 111784 114943 := bstep (se 1 (by rfl) ⟨86207, by rfl⟩ : syracuseStep 114943 = 172415) B172415
theorem B114991 : Blo 111784 114991 := bstep (se 1 (by rfl) ⟨86243, by rfl⟩ : syracuseStep 114991 = 172487) B172487
theorem B2015549 : Blo 111784 2015549 := bstep (se 3 (by rfl) ⟨377915, by rfl⟩ : syracuseStep 2015549 = 755831) B755831
theorem B377351 : Blo 111784 377351 := bstep (se 1 (by rfl) ⟨283013, by rfl⟩ : syracuseStep 377351 = 566027) B566027
theorem B115227 : Blo 111784 115227 := bstep (se 1 (by rfl) ⟨86420, by rfl⟩ : syracuseStep 115227 = 172841) B172841
theorem B115231 : Blo 111784 115231 := bstep (se 1 (by rfl) ⟨86423, by rfl⟩ : syracuseStep 115231 = 172847) B172847
theorem B868967 : Blo 111784 868967 := bstep (se 1 (by rfl) ⟨651725, by rfl⟩ : syracuseStep 868967 = 1303451) B1303451
theorem B115311 : Blo 111784 115311 := bstep (se 1 (by rfl) ⟨86483, by rfl⟩ : syracuseStep 115311 = 172967) B172967
theorem B377459 : Blo 111784 377459 := bstep (se 1 (by rfl) ⟨283094, by rfl⟩ : syracuseStep 377459 = 566189) B566189
theorem B115367 : Blo 111784 115367 := bstep (se 1 (by rfl) ⟨86525, by rfl⟩ : syracuseStep 115367 = 173051) B173051
theorem B115407 : Blo 111784 115407 := bstep (se 1 (by rfl) ⟨86555, by rfl⟩ : syracuseStep 115407 = 173111) B173111
theorem B115487 : Blo 111784 115487 := bstep (se 1 (by rfl) ⟨86615, by rfl⟩ : syracuseStep 115487 = 173231) B173231
theorem B377729 : Blo 111784 377729 := bstep (se 2 (by rfl) ⟨141648, by rfl⟩ : syracuseStep 377729 = 283297) B283297
theorem B1262567 : Blo 111784 1262567 := bstep (se 1 (by rfl) ⟨946925, by rfl⟩ : syracuseStep 1262567 = 1893851) B1893851
theorem B115759 : Blo 111784 115759 := bstep (se 1 (by rfl) ⟨86819, by rfl⟩ : syracuseStep 115759 = 173639) B173639
theorem B1557593 : Blo 111784 1557593 := bstep (se 2 (by rfl) ⟨584097, by rfl⟩ : syracuseStep 1557593 = 1168195) B1168195
theorem B214319 : Blo 111784 214319 := bstep (se 1 (by rfl) ⟨160739, by rfl⟩ : syracuseStep 214319 = 321479) B321479
theorem B378269 : Blo 111784 378269 := bstep (se 3 (by rfl) ⟨70925, by rfl⟩ : syracuseStep 378269 = 141851) B141851
theorem B378431 : Blo 111784 378431 := bstep (se 1 (by rfl) ⟨283823, by rfl⟩ : syracuseStep 378431 = 567647) B567647
theorem B378539 : Blo 111784 378539 := bstep (se 1 (by rfl) ⟨283904, by rfl⟩ : syracuseStep 378539 = 567809) B567809
theorem B379079 : Blo 111784 379079 := bstep (se 1 (by rfl) ⟨284309, by rfl⟩ : syracuseStep 379079 = 568619) B568619
theorem B969083 : Blo 111784 969083 := bstep (se 1 (by rfl) ⟨726812, by rfl⟩ : syracuseStep 969083 = 1453625) B1453625
theorem B379673 : Blo 111784 379673 := bstep (se 2 (by rfl) ⟨142377, by rfl⟩ : syracuseStep 379673 = 284755) B284755
theorem B380051 : Blo 111784 380051 := bstep (se 1 (by rfl) ⟨285038, by rfl⟩ : syracuseStep 380051 = 570077) B570077
theorem B380321 : Blo 111784 380321 := bstep (se 2 (by rfl) ⟨142620, by rfl⟩ : syracuseStep 380321 = 285241) B285241
theorem B1035767 : Blo 111784 1035767 := bstep (se 1 (by rfl) ⟨776825, by rfl⟩ : syracuseStep 1035767 = 1553651) B1553651
theorem B479159 : Blo 111784 479159 := bstep (se 1 (by rfl) ⟨359369, by rfl⟩ : syracuseStep 479159 = 718739) B718739
theorem B380861 : Blo 111784 380861 := bstep (se 3 (by rfl) ⟨71411, by rfl⟩ : syracuseStep 380861 = 142823) B142823
theorem B217151 : Blo 111784 217151 := bstep (se 1 (by rfl) ⟨162863, by rfl⟩ : syracuseStep 217151 = 325727) B325727
theorem B381023 : Blo 111784 381023 := bstep (se 1 (by rfl) ⟨285767, by rfl⟩ : syracuseStep 381023 = 571535) B571535
theorem B4837643 : Blo 111784 4837643 := bstep (se 1 (by rfl) ⟨3628232, by rfl⟩ : syracuseStep 4837643 = 7256465) B7256465
theorem B8147249 : Blo 111784 8147249 := bstep (se 2 (by rfl) ⟨3055218, by rfl⟩ : syracuseStep 8147249 = 6110437) B6110437
theorem B218207 : Blo 111784 218207 := bstep (se 1 (by rfl) ⟨163655, by rfl⟩ : syracuseStep 218207 = 327311) B327311
theorem B2086193 : Blo 111784 2086193 := bstep (se 2 (by rfl) ⟨782322, by rfl⟩ : syracuseStep 2086193 = 1564645) B1564645
theorem B218791 : Blo 111784 218791 := bstep (se 1 (by rfl) ⟨164093, by rfl⟩ : syracuseStep 218791 = 328187) B328187
theorem B382751 : Blo 111784 382751 := bstep (se 1 (by rfl) ⟨287063, by rfl⟩ : syracuseStep 382751 = 574127) B574127
theorem B153415 : Blo 111784 153415 := bstep (se 1 (by rfl) ⟨115061, by rfl⟩ : syracuseStep 153415 = 230123) B230123
theorem B251873 : Blo 111784 251873 := bstep (se 2 (by rfl) ⟨94452, by rfl⟩ : syracuseStep 251873 = 188905) B188905
theorem B481619 : Blo 111784 481619 := bstep (se 1 (by rfl) ⟨361214, by rfl⟩ : syracuseStep 481619 = 722429) B722429
theorem B11917721 : Blo 111784 11917721 := bstep (se 2 (by rfl) ⟨4469145, by rfl⟩ : syracuseStep 11917721 = 8938291) B8938291
theorem B7428631 : Blo 111784 7428631 := bstep (se 1 (by rfl) ⟨5571473, by rfl⟩ : syracuseStep 7428631 = 11142947) B11142947
theorem B351047 : Blo 111784 351047 := bstep (se 1 (by rfl) ⟨263285, by rfl⟩ : syracuseStep 351047 = 526571) B526571
theorem B548203 : Blo 111784 548203 := bstep (se 1 (by rfl) ⟨411152, by rfl⟩ : syracuseStep 548203 = 822305) B822305
theorem B286375 : Blo 111784 286375 := bstep (se 1 (by rfl) ⟨214781, by rfl⟩ : syracuseStep 286375 = 429563) B429563
theorem B876257 : Blo 111784 876257 := bstep (se 2 (by rfl) ⟨328596, by rfl⟩ : syracuseStep 876257 = 657193) B657193
theorem B253727 : Blo 111784 253727 := bstep (se 1 (by rfl) ⟨190295, by rfl⟩ : syracuseStep 253727 = 380591) B380591
theorem B253943 : Blo 111784 253943 := bstep (se 1 (by rfl) ⟨190457, by rfl⟩ : syracuseStep 253943 = 380915) B380915
theorem B4448357 : Blo 111784 4448357 := bstep (se 4 (by rfl) ⟨417033, by rfl⟩ : syracuseStep 4448357 = 834067) B834067
theorem B254159 : Blo 111784 254159 := bstep (se 1 (by rfl) ⟨190619, by rfl⟩ : syracuseStep 254159 = 381239) B381239
theorem B93184277 : Blo 111784 93184277 := bstep (se 6 (by rfl) ⟨2184006, by rfl⟩ : syracuseStep 93184277 = 4368013) B4368013
theorem B254303 : Blo 111784 254303 := bstep (se 1 (by rfl) ⟨190727, by rfl⟩ : syracuseStep 254303 = 381455) B381455
theorem B156367 : Blo 111784 156367 := bstep (se 1 (by rfl) ⟨117275, by rfl⟩ : syracuseStep 156367 = 234551) B234551
theorem B647945 : Blo 111784 647945 := bstep (se 2 (by rfl) ⟨242979, by rfl⟩ : syracuseStep 647945 = 485959) B485959
theorem B779017 : Blo 111784 779017 := bstep (se 2 (by rfl) ⟨292131, by rfl⟩ : syracuseStep 779017 = 584263) B584263
theorem B255023 : Blo 111784 255023 := bstep (se 1 (by rfl) ⟨191267, by rfl⟩ : syracuseStep 255023 = 382535) B382535
theorem B1107017 : Blo 111784 1107017 := bstep (se 2 (by rfl) ⟨415131, by rfl⟩ : syracuseStep 1107017 = 830263) B830263
theorem B189607 : Blo 111784 189607 := bstep (se 1 (by rfl) ⟨142205, by rfl⟩ : syracuseStep 189607 = 284411) B284411
theorem B976495 : Blo 111784 976495 := bstep (se 1 (by rfl) ⟨732371, by rfl⟩ : syracuseStep 976495 = 1464743) B1464743
theorem B255671 : Blo 111784 255671 := bstep (se 1 (by rfl) ⟨191753, by rfl⟩ : syracuseStep 255671 = 383507) B383507
theorem B616211 : Blo 111784 616211 := bstep (se 1 (by rfl) ⟨462158, by rfl⟩ : syracuseStep 616211 = 924317) B924317
theorem B190363 : Blo 111784 190363 := bstep (se 1 (by rfl) ⟨142772, by rfl⟩ : syracuseStep 190363 = 285545) B285545
theorem B911339 : Blo 111784 911339 := bstep (se 1 (by rfl) ⟨683504, by rfl⟩ : syracuseStep 911339 = 1367009) B1367009
theorem B288755 : Blo 111784 288755 := bstep (se 1 (by rfl) ⟨216566, by rfl⟩ : syracuseStep 288755 = 433133) B433133
theorem B256121 : Blo 111784 256121 := bstep (se 2 (by rfl) ⟨96045, by rfl⟩ : syracuseStep 256121 = 192091) B192091
theorem B190775 : Blo 111784 190775 := bstep (se 1 (by rfl) ⟨143081, by rfl⟩ : syracuseStep 190775 = 286163) B286163
theorem B289271 : Blo 111784 289271 := bstep (se 1 (by rfl) ⟨216953, by rfl⟩ : syracuseStep 289271 = 433907) B433907
theorem B485993 : Blo 111784 485993 := bstep (se 2 (by rfl) ⟨182247, by rfl⟩ : syracuseStep 485993 = 364495) B364495
theorem B551569 : Blo 111784 551569 := bstep (se 2 (by rfl) ⟨206838, by rfl⟩ : syracuseStep 551569 = 413677) B413677
theorem B650429 : Blo 111784 650429 := bstep (se 3 (by rfl) ⟨121955, by rfl⟩ : syracuseStep 650429 = 243911) B243911
theorem B257435 : Blo 111784 257435 := bstep (se 1 (by rfl) ⟨193076, by rfl⟩ : syracuseStep 257435 = 386153) B386153
theorem B519635 : Blo 111784 519635 := bstep (se 1 (by rfl) ⟨389726, by rfl⟩ : syracuseStep 519635 = 779453) B779453
theorem B192071 : Blo 111784 192071 := bstep (se 1 (by rfl) ⟨144053, by rfl⟩ : syracuseStep 192071 = 288107) B288107
theorem B290375 : Blo 111784 290375 := bstep (se 1 (by rfl) ⟨217781, by rfl⟩ : syracuseStep 290375 = 435563) B435563
theorem B126715 : Blo 111784 126715 := bstep (se 1 (by rfl) ⟨95036, by rfl⟩ : syracuseStep 126715 = 190073) B190073
theorem B585467 : Blo 111784 585467 := bstep (se 1 (by rfl) ⟨439100, by rfl⟩ : syracuseStep 585467 = 878201) B878201
theorem B258011 : Blo 111784 258011 := bstep (se 1 (by rfl) ⟨193508, by rfl⟩ : syracuseStep 258011 = 387017) B387017
theorem B127039 : Blo 111784 127039 := bstep (se 1 (by rfl) ⟨95279, by rfl⟩ : syracuseStep 127039 = 190559) B190559
theorem B651361 : Blo 111784 651361 := bstep (se 2 (by rfl) ⟨244260, by rfl⟩ : syracuseStep 651361 = 488521) B488521
theorem B258191 : Blo 111784 258191 := bstep (se 1 (by rfl) ⟨193643, by rfl⟩ : syracuseStep 258191 = 387287) B387287
theorem B258281 : Blo 111784 258281 := bstep (se 2 (by rfl) ⟨96855, by rfl⟩ : syracuseStep 258281 = 193711) B193711
theorem B487705 : Blo 111784 487705 := bstep (se 2 (by rfl) ⟨182889, by rfl⟩ : syracuseStep 487705 = 365779) B365779
theorem B258407 : Blo 111784 258407 := bstep (se 1 (by rfl) ⟨193805, by rfl⟩ : syracuseStep 258407 = 387611) B387611
theorem B619325 : Blo 111784 619325 := bstep (se 3 (by rfl) ⟨116123, by rfl⟩ : syracuseStep 619325 = 232247) B232247
theorem B127903 : Blo 111784 127903 := bstep (se 1 (by rfl) ⟨95927, by rfl⟩ : syracuseStep 127903 = 191855) B191855
theorem B258983 : Blo 111784 258983 := bstep (se 1 (by rfl) ⟨194237, by rfl⟩ : syracuseStep 258983 = 388475) B388475
theorem B193529 : Blo 111784 193529 := bstep (se 2 (by rfl) ⟨72573, by rfl⟩ : syracuseStep 193529 = 145147) B145147
theorem B291833 : Blo 111784 291833 := bstep (se 2 (by rfl) ⟨109437, by rfl⟩ : syracuseStep 291833 = 218875) B218875
theorem B128155 : Blo 111784 128155 := bstep (se 1 (by rfl) ⟨96116, by rfl⟩ : syracuseStep 128155 = 192233) B192233
theorem B193799 : Blo 111784 193799 := bstep (se 1 (by rfl) ⟨145349, by rfl⟩ : syracuseStep 193799 = 290699) B290699
theorem B488767 : Blo 111784 488767 := bstep (se 1 (by rfl) ⟨366575, by rfl⟩ : syracuseStep 488767 = 733151) B733151
theorem B1668545 : Blo 111784 1668545 := bstep (se 2 (by rfl) ⟨625704, by rfl⟩ : syracuseStep 1668545 = 1251409) B1251409
theorem B652819 : Blo 111784 652819 := bstep (se 1 (by rfl) ⟨489614, by rfl⟩ : syracuseStep 652819 = 979229) B979229
theorem B161519 : Blo 111784 161519 := bstep (se 1 (by rfl) ⟨121139, by rfl⟩ : syracuseStep 161519 = 242279) B242279
theorem B128839 : Blo 111784 128839 := bstep (se 1 (by rfl) ⟨96629, by rfl⟩ : syracuseStep 128839 = 193259) B193259
theorem B259919 : Blo 111784 259919 := bstep (se 1 (by rfl) ⟨194939, by rfl⟩ : syracuseStep 259919 = 389879) B389879
theorem B554951 : Blo 111784 554951 := bstep (se 1 (by rfl) ⟨416213, by rfl⟩ : syracuseStep 554951 = 832427) B832427
theorem B161833 : Blo 111784 161833 := bstep (se 2 (by rfl) ⟨60687, by rfl⟩ : syracuseStep 161833 = 121375) B121375
theorem B260279 : Blo 111784 260279 := bstep (se 1 (by rfl) ⟨195209, by rfl⟩ : syracuseStep 260279 = 390419) B390419
theorem B1472741 : Blo 111784 1472741 := bstep (se 4 (by rfl) ⟨138069, by rfl⟩ : syracuseStep 1472741 = 276139) B276139
theorem B194791 : Blo 111784 194791 := bstep (se 1 (by rfl) ⟨146093, by rfl⟩ : syracuseStep 194791 = 292187) B292187
theorem B129487 : Blo 111784 129487 := bstep (se 1 (by rfl) ⟨97115, by rfl⟩ : syracuseStep 129487 = 194231) B194231
theorem B2095625 : Blo 111784 2095625 := bstep (se 2 (by rfl) ⟨785859, by rfl⟩ : syracuseStep 2095625 = 1571719) B1571719
theorem B490025 : Blo 111784 490025 := bstep (se 2 (by rfl) ⟨183759, by rfl⟩ : syracuseStep 490025 = 367519) B367519
theorem B260767 : Blo 111784 260767 := bstep (se 1 (by rfl) ⟨195575, by rfl⟩ : syracuseStep 260767 = 391151) B391151
theorem B424673 : Blo 111784 424673 := bstep (se 2 (by rfl) ⟨159252, by rfl⟩ : syracuseStep 424673 = 318505) B318505
theorem B850985 : Blo 111784 850985 := bstep (se 2 (by rfl) ⟨319119, by rfl⟩ : syracuseStep 850985 = 638239) B638239
theorem B228577 : Blo 111784 228577 := bstep (se 2 (by rfl) ⟨85716, by rfl⟩ : syracuseStep 228577 = 171433) B171433
theorem B261863 : Blo 111784 261863 := bstep (se 1 (by rfl) ⟨196397, by rfl⟩ : syracuseStep 261863 = 392795) B392795
theorem B327503 : Blo 111784 327503 := bstep (se 1 (by rfl) ⟨245627, by rfl⟩ : syracuseStep 327503 = 491255) B491255
theorem B360575 : Blo 111784 360575 := bstep (se 1 (by rfl) ⟨270431, by rfl⟩ : syracuseStep 360575 = 540863) B540863
theorem B2752699 : Blo 111784 2752699 := bstep (se 1 (by rfl) ⟨2064524, by rfl⟩ : syracuseStep 2752699 = 4129049) B4129049
theorem B1343699 : Blo 111784 1343699 := bstep (se 1 (by rfl) ⟨1007774, by rfl⟩ : syracuseStep 1343699 = 2015549) B2015549
theorem B526057 : Blo 111784 526057 := bstep (se 2 (by rfl) ⟨197271, by rfl⟩ : syracuseStep 526057 = 394543) B394543
theorem B919619 : Blo 111784 919619 := bstep (se 1 (by rfl) ⟨689714, by rfl⟩ : syracuseStep 919619 = 1379429) B1379429
theorem B10554995 : Blo 111784 10554995 := bstep (se 1 (by rfl) ⟨7916246, by rfl⟩ : syracuseStep 10554995 = 15832493) B15832493
theorem B167915 : Blo 111784 167915 := bstep (se 1 (by rfl) ⟨125936, by rfl⟩ : syracuseStep 167915 = 251873) B251873
theorem B463067 : Blo 111784 463067 := bstep (se 1 (by rfl) ⟨347300, by rfl⟩ : syracuseStep 463067 = 694601) B694601
theorem B234031 : Blo 111784 234031 := bstep (se 1 (by rfl) ⟨175523, by rfl⟩ : syracuseStep 234031 = 351047) B351047
theorem B430717 : Blo 111784 430717 := bstep (se 3 (by rfl) ⟨80759, by rfl⟩ : syracuseStep 430717 = 161519) B161519
theorem B168953 : Blo 111784 168953 := bstep (se 2 (by rfl) ⟨63357, by rfl⟩ : syracuseStep 168953 = 126715) B126715
theorem B1479869 : Blo 111784 1479869 := bstep (se 3 (by rfl) ⟨277475, by rfl⟩ : syracuseStep 1479869 = 554951) B554951
theorem B169151 : Blo 111784 169151 := bstep (se 1 (by rfl) ⟨126863, by rfl⟩ : syracuseStep 169151 = 253727) B253727
theorem B169295 : Blo 111784 169295 := bstep (se 1 (by rfl) ⟨126971, by rfl⟩ : syracuseStep 169295 = 253943) B253943
theorem B169385 : Blo 111784 169385 := bstep (se 2 (by rfl) ⟨63519, by rfl⟩ : syracuseStep 169385 = 127039) B127039
theorem B169439 : Blo 111784 169439 := bstep (se 1 (by rfl) ⟨127079, by rfl⟩ : syracuseStep 169439 = 254159) B254159
theorem B169535 : Blo 111784 169535 := bstep (se 1 (by rfl) ⟨127151, by rfl⟩ : syracuseStep 169535 = 254303) B254303
theorem B431963 : Blo 111784 431963 := bstep (se 1 (by rfl) ⟨323972, by rfl⟩ : syracuseStep 431963 = 647945) B647945
theorem B170015 : Blo 111784 170015 := bstep (se 1 (by rfl) ⟨127511, by rfl⟩ : syracuseStep 170015 = 255023) B255023
theorem B137551 : Blo 111784 137551 := bstep (se 1 (by rfl) ⟨103163, by rfl⟩ : syracuseStep 137551 = 206327) B206327
theorem B1972673 : Blo 111784 1972673 := bstep (se 2 (by rfl) ⟨739752, by rfl⟩ : syracuseStep 1972673 = 1479505) B1479505
theorem B170447 : Blo 111784 170447 := bstep (se 1 (by rfl) ⟨127835, by rfl⟩ : syracuseStep 170447 = 255671) B255671
theorem B170537 : Blo 111784 170537 := bstep (se 2 (by rfl) ⟨63951, by rfl⟩ : syracuseStep 170537 = 127903) B127903
theorem B170747 : Blo 111784 170747 := bstep (se 1 (by rfl) ⟨128060, by rfl⟩ : syracuseStep 170747 = 256121) B256121
theorem B170873 : Blo 111784 170873 := bstep (se 2 (by rfl) ⟨64077, by rfl⟩ : syracuseStep 170873 = 128155) B128155
theorem B10623899 : Blo 111784 10623899 := bstep (se 1 (by rfl) ⟨7967924, by rfl⟩ : syracuseStep 10623899 = 15935849) B15935849
theorem B1449161 : Blo 111784 1449161 := bstep (se 2 (by rfl) ⟨543435, by rfl⟩ : syracuseStep 1449161 = 1086871) B1086871
theorem B433619 : Blo 111784 433619 := bstep (se 1 (by rfl) ⟨325214, by rfl⟩ : syracuseStep 433619 = 650429) B650429
theorem B171623 : Blo 111784 171623 := bstep (se 1 (by rfl) ⟨128717, by rfl⟩ : syracuseStep 171623 = 257435) B257435
theorem B204553 : Blo 111784 204553 := bstep (se 2 (by rfl) ⟨76707, by rfl⟩ : syracuseStep 204553 = 153415) B153415
theorem B171785 : Blo 111784 171785 := bstep (se 2 (by rfl) ⟨64419, by rfl⟩ : syracuseStep 171785 = 128839) B128839
theorem B172007 : Blo 111784 172007 := bstep (se 1 (by rfl) ⟨129005, by rfl⟩ : syracuseStep 172007 = 258011) B258011
theorem B172127 : Blo 111784 172127 := bstep (se 1 (by rfl) ⟨129095, by rfl⟩ : syracuseStep 172127 = 258191) B258191
theorem B172187 : Blo 111784 172187 := bstep (se 1 (by rfl) ⟨129140, by rfl⟩ : syracuseStep 172187 = 258281) B258281
theorem B172271 : Blo 111784 172271 := bstep (se 1 (by rfl) ⟨129203, by rfl⟩ : syracuseStep 172271 = 258407) B258407
theorem B270719 : Blo 111784 270719 := bstep (se 1 (by rfl) ⟨203039, by rfl⟩ : syracuseStep 270719 = 406079) B406079
theorem B172649 : Blo 111784 172649 := bstep (se 2 (by rfl) ⟨64743, by rfl⟩ : syracuseStep 172649 = 129487) B129487
theorem B172655 : Blo 111784 172655 := bstep (se 1 (by rfl) ⟨129491, by rfl⟩ : syracuseStep 172655 = 258983) B258983
theorem B9904841 : Blo 111784 9904841 := bstep (se 2 (by rfl) ⟨3714315, by rfl⟩ : syracuseStep 9904841 = 7428631) B7428631
theorem B1385693 : Blo 111784 1385693 := bstep (se 3 (by rfl) ⟨259817, by rfl⟩ : syracuseStep 1385693 = 519635) B519635
theorem B173279 : Blo 111784 173279 := bstep (se 1 (by rfl) ⟨129959, by rfl⟩ : syracuseStep 173279 = 259919) B259919
theorem B2762045 : Blo 111784 2762045 := bstep (se 3 (by rfl) ⟨517883, by rfl⟩ : syracuseStep 2762045 = 1035767) B1035767
theorem B173519 : Blo 111784 173519 := bstep (se 1 (by rfl) ⟨130139, by rfl⟩ : syracuseStep 173519 = 260279) B260279
theorem B304769 : Blo 111784 304769 := bstep (se 2 (by rfl) ⟨114288, by rfl⟩ : syracuseStep 304769 = 228577) B228577
theorem B730937 : Blo 111784 730937 := bstep (se 2 (by rfl) ⟨274101, by rfl⟩ : syracuseStep 730937 = 548203) B548203
theorem B567323 : Blo 111784 567323 := bstep (se 1 (by rfl) ⟨425492, by rfl⟩ : syracuseStep 567323 = 850985) B850985
theorem B174575 : Blo 111784 174575 := bstep (se 1 (by rfl) ⟨130931, by rfl⟩ : syracuseStep 174575 = 261863) B261863
theorem B2468987 : Blo 111784 2468987 := bstep (se 1 (by rfl) ⟨1851740, by rfl⟩ : syracuseStep 2468987 = 3703481) B3703481
theorem B273785 : Blo 111784 273785 := bstep (se 2 (by rfl) ⟨102669, by rfl⟩ : syracuseStep 273785 = 205339) B205339
theorem B248491405 : Blo 111784 248491405 := bstep (se 3 (by rfl) ⟨46592138, by rfl⟩ : syracuseStep 248491405 = 93184277) B93184277
theorem B142879 : Blo 111784 142879 := bstep (se 1 (by rfl) ⟨107159, by rfl⟩ : syracuseStep 142879 = 214319) B214319
theorem B274025 : Blo 111784 274025 := bstep (se 2 (by rfl) ⟨102759, by rfl⟩ : syracuseStep 274025 = 205519) B205519
theorem B208489 : Blo 111784 208489 := bstep (se 2 (by rfl) ⟨78183, by rfl⟩ : syracuseStep 208489 = 156367) B156367
theorem B111871 : Blo 111784 111871 := bstep (se 1 (by rfl) ⟨83903, by rfl⟩ : syracuseStep 111871 = 167807) B167807
theorem B111999 : Blo 111784 111999 := bstep (se 1 (by rfl) ⟨83999, by rfl⟩ : syracuseStep 111999 = 167999) B167999
theorem B144767 : Blo 111784 144767 := bstep (se 1 (by rfl) ⟨108575, by rfl⟩ : syracuseStep 144767 = 217151) B217151
theorem B3225095 : Blo 111784 3225095 := bstep (se 1 (by rfl) ⟨2418821, by rfl⟩ : syracuseStep 3225095 = 4837643) B4837643
theorem B112155 : Blo 111784 112155 := bstep (se 1 (by rfl) ⟨84116, by rfl⟩ : syracuseStep 112155 = 168233) B168233
theorem B2340485 : Blo 111784 2340485 := bstep (se 4 (by rfl) ⟨219420, by rfl⟩ : syracuseStep 2340485 = 438841) B438841
theorem B112335 : Blo 111784 112335 := bstep (se 1 (by rfl) ⟨84251, by rfl⟩ : syracuseStep 112335 = 168503) B168503
theorem B243407 : Blo 111784 243407 := bstep (se 1 (by rfl) ⟨182555, by rfl⟩ : syracuseStep 243407 = 365111) B365111
theorem B964331 : Blo 111784 964331 := bstep (se 1 (by rfl) ⟨723248, by rfl⟩ : syracuseStep 964331 = 1446497) B1446497
theorem B112575 : Blo 111784 112575 := bstep (se 1 (by rfl) ⟨84431, by rfl⟩ : syracuseStep 112575 = 168863) B168863
theorem B112703 : Blo 111784 112703 := bstep (se 1 (by rfl) ⟨84527, by rfl⟩ : syracuseStep 112703 = 169055) B169055
theorem B145471 : Blo 111784 145471 := bstep (se 1 (by rfl) ⟨109103, by rfl⟩ : syracuseStep 145471 = 218207) B218207
theorem B112743 : Blo 111784 112743 := bstep (se 1 (by rfl) ⟨84557, by rfl⟩ : syracuseStep 112743 = 169115) B169115
theorem B735425 : Blo 111784 735425 := bstep (se 2 (by rfl) ⟨275784, by rfl⟩ : syracuseStep 735425 = 551569) B551569
theorem B113199 : Blo 111784 113199 := bstep (se 1 (by rfl) ⟨84899, by rfl⟩ : syracuseStep 113199 = 169799) B169799
theorem B637739 : Blo 111784 637739 := bstep (se 1 (by rfl) ⟨478304, by rfl⟩ : syracuseStep 637739 = 956609) B956609
theorem B7945147 : Blo 111784 7945147 := bstep (se 1 (by rfl) ⟨5958860, by rfl⟩ : syracuseStep 7945147 = 11917721) B11917721
theorem B113599 : Blo 111784 113599 := bstep (se 1 (by rfl) ⟨85199, by rfl⟩ : syracuseStep 113599 = 170399) B170399
theorem B113647 : Blo 111784 113647 := bstep (se 1 (by rfl) ⟨85235, by rfl⟩ : syracuseStep 113647 = 170471) B170471
theorem B114143 : Blo 111784 114143 := bstep (se 1 (by rfl) ⟨85607, by rfl⟩ : syracuseStep 114143 = 171215) B171215
theorem B114223 : Blo 111784 114223 := bstep (se 1 (by rfl) ⟨85667, by rfl⟩ : syracuseStep 114223 = 171335) B171335
theorem B114331 : Blo 111784 114331 := bstep (se 1 (by rfl) ⟨85748, by rfl⟩ : syracuseStep 114331 = 171497) B171497
theorem B114427 : Blo 111784 114427 := bstep (se 1 (by rfl) ⟨85820, by rfl⟩ : syracuseStep 114427 = 171641) B171641
theorem B114591 : Blo 111784 114591 := bstep (se 1 (by rfl) ⟨85943, by rfl⟩ : syracuseStep 114591 = 171887) B171887
theorem B2965571 : Blo 111784 2965571 := bstep (se 1 (by rfl) ⟨2224178, by rfl⟩ : syracuseStep 2965571 = 4448357) B4448357
theorem B868481 : Blo 111784 868481 := bstep (se 2 (by rfl) ⟨325680, by rfl⟩ : syracuseStep 868481 = 651361) B651361
theorem B409769 : Blo 111784 409769 := bstep (se 2 (by rfl) ⟨153663, by rfl⟩ : syracuseStep 409769 = 307327) B307327
theorem B639197 : Blo 111784 639197 := bstep (se 3 (by rfl) ⟨119849, by rfl⟩ : syracuseStep 639197 = 239699) B239699
theorem B115047 : Blo 111784 115047 := bstep (se 1 (by rfl) ⟨86285, by rfl⟩ : syracuseStep 115047 = 172571) B172571
theorem B115167 : Blo 111784 115167 := bstep (se 1 (by rfl) ⟨86375, by rfl⟩ : syracuseStep 115167 = 172751) B172751
theorem B115175 : Blo 111784 115175 := bstep (se 1 (by rfl) ⟨86381, by rfl⟩ : syracuseStep 115175 = 172763) B172763
theorem B738011 : Blo 111784 738011 := bstep (se 1 (by rfl) ⟨553508, by rfl⟩ : syracuseStep 738011 = 1107017) B1107017
theorem B115451 : Blo 111784 115451 := bstep (se 1 (by rfl) ⟨86588, by rfl⟩ : syracuseStep 115451 = 173177) B173177
theorem B934841 : Blo 111784 934841 := bstep (se 2 (by rfl) ⟨350565, by rfl⟩ : syracuseStep 934841 = 701131) B701131
theorem B574451 : Blo 111784 574451 := bstep (se 1 (by rfl) ⟨430838, by rfl⟩ : syracuseStep 574451 = 861677) B861677
theorem B181415 : Blo 111784 181415 := bstep (se 1 (by rfl) ⟨136061, by rfl⟩ : syracuseStep 181415 = 272123) B272123
theorem B410807 : Blo 111784 410807 := bstep (se 1 (by rfl) ⟨308105, by rfl⟩ : syracuseStep 410807 = 616211) B616211
theorem B607559 : Blo 111784 607559 := bstep (se 1 (by rfl) ⟨455669, by rfl⟩ : syracuseStep 607559 = 911339) B911339
theorem B378323 : Blo 111784 378323 := bstep (se 1 (by rfl) ⟨283742, by rfl⟩ : syracuseStep 378323 = 567485) B567485
theorem B378863 : Blo 111784 378863 := bstep (se 1 (by rfl) ⟨284147, by rfl⟩ : syracuseStep 378863 = 568295) B568295
theorem B870425 : Blo 111784 870425 := bstep (se 2 (by rfl) ⟨326409, by rfl⟩ : syracuseStep 870425 = 652819) B652819
theorem B576071 : Blo 111784 576071 := bstep (se 1 (by rfl) ⟨432053, by rfl⟩ : syracuseStep 576071 = 864107) B864107
theorem B215777 : Blo 111784 215777 := bstep (se 2 (by rfl) ⟨80916, by rfl⟩ : syracuseStep 215777 = 161833) B161833
theorem B445625 : Blo 111784 445625 := bstep (se 2 (by rfl) ⟨167109, by rfl⟩ : syracuseStep 445625 = 334219) B334219
theorem B412883 : Blo 111784 412883 := bstep (se 1 (by rfl) ⟨309662, by rfl⟩ : syracuseStep 412883 = 619325) B619325
theorem B347689 : Blo 111784 347689 := bstep (se 2 (by rfl) ⟨130383, by rfl⟩ : syracuseStep 347689 = 260767) B260767
theorem B577691 : Blo 111784 577691 := bstep (se 1 (by rfl) ⟨433268, by rfl⟩ : syracuseStep 577691 = 866537) B866537
theorem B5099719 : Blo 111784 5099719 := bstep (se 1 (by rfl) ⟨3824789, by rfl⟩ : syracuseStep 5099719 = 7649579) B7649579
theorem B1397083 : Blo 111784 1397083 := bstep (se 1 (by rfl) ⟨1047812, by rfl⟩ : syracuseStep 1397083 = 2095625) B2095625
theorem B3723731 : Blo 111784 3723731 := bstep (se 1 (by rfl) ⟨2792798, by rfl⟩ : syracuseStep 3723731 = 5585597) B5585597
theorem B283115 : Blo 111784 283115 := bstep (se 1 (by rfl) ⟨212336, by rfl⟩ : syracuseStep 283115 = 424673) B424673
theorem B381779 : Blo 111784 381779 := bstep (se 1 (by rfl) ⟨286334, by rfl⟩ : syracuseStep 381779 = 572669) B572669
theorem B873341 : Blo 111784 873341 := bstep (se 3 (by rfl) ⟨163751, by rfl⟩ : syracuseStep 873341 = 327503) B327503
theorem B381833 : Blo 111784 381833 := bstep (se 2 (by rfl) ⟨143187, by rfl⟩ : syracuseStep 381833 = 286375) B286375
theorem B382319 : Blo 111784 382319 := bstep (se 1 (by rfl) ⟨286739, by rfl⟩ : syracuseStep 382319 = 573479) B573479
theorem B251567 : Blo 111784 251567 := bstep (se 1 (by rfl) ⟨188675, by rfl⟩ : syracuseStep 251567 = 377351) B377351
theorem B579311 : Blo 111784 579311 := bstep (se 1 (by rfl) ⟨434483, by rfl⟩ : syracuseStep 579311 = 868967) B868967
theorem B251639 : Blo 111784 251639 := bstep (se 1 (by rfl) ⟨188729, by rfl⟩ : syracuseStep 251639 = 377459) B377459
theorem B874313 : Blo 111784 874313 := bstep (se 2 (by rfl) ⟨327867, by rfl⟩ : syracuseStep 874313 = 655735) B655735
theorem B251819 : Blo 111784 251819 := bstep (se 1 (by rfl) ⟨188864, by rfl⟩ : syracuseStep 251819 = 377729) B377729
theorem B841711 : Blo 111784 841711 := bstep (se 1 (by rfl) ⟨631283, by rfl⟩ : syracuseStep 841711 = 1262567) B1262567
theorem B1038395 : Blo 111784 1038395 := bstep (se 1 (by rfl) ⟨778796, by rfl⟩ : syracuseStep 1038395 = 1557593) B1557593
theorem B219323 : Blo 111784 219323 := bstep (se 1 (by rfl) ⟨164492, by rfl⟩ : syracuseStep 219323 = 328985) B328985
theorem B252179 : Blo 111784 252179 := bstep (se 1 (by rfl) ⟨189134, by rfl⟩ : syracuseStep 252179 = 378269) B378269
theorem B1038689 : Blo 111784 1038689 := bstep (se 2 (by rfl) ⟨389508, by rfl⟩ : syracuseStep 1038689 = 779017) B779017
theorem B252287 : Blo 111784 252287 := bstep (se 1 (by rfl) ⟨189215, by rfl⟩ : syracuseStep 252287 = 378431) B378431
theorem B252359 : Blo 111784 252359 := bstep (se 1 (by rfl) ⟨189269, by rfl⟩ : syracuseStep 252359 = 378539) B378539
theorem B612839 : Blo 111784 612839 := bstep (se 1 (by rfl) ⟨459629, by rfl⟩ : syracuseStep 612839 = 919259) B919259
theorem B285191 : Blo 111784 285191 := bstep (se 1 (by rfl) ⟨213893, by rfl⟩ : syracuseStep 285191 = 427787) B427787
theorem B252719 : Blo 111784 252719 := bstep (se 1 (by rfl) ⟨189539, by rfl⟩ : syracuseStep 252719 = 379079) B379079
theorem B252809 : Blo 111784 252809 := bstep (se 2 (by rfl) ⟨94803, by rfl⟩ : syracuseStep 252809 = 189607) B189607
theorem B646055 : Blo 111784 646055 := bstep (se 1 (by rfl) ⟨484541, by rfl⟩ : syracuseStep 646055 = 969083) B969083
theorem B253115 : Blo 111784 253115 := bstep (se 1 (by rfl) ⟨189836, by rfl⟩ : syracuseStep 253115 = 379673) B379673
theorem B286031 : Blo 111784 286031 := bstep (se 1 (by rfl) ⟨214523, by rfl⟩ : syracuseStep 286031 = 429047) B429047
theorem B253367 : Blo 111784 253367 := bstep (se 1 (by rfl) ⟨190025, by rfl⟩ : syracuseStep 253367 = 380051) B380051
theorem B1301993 : Blo 111784 1301993 := bstep (se 2 (by rfl) ⟨488247, by rfl⟩ : syracuseStep 1301993 = 976495) B976495
theorem B253547 : Blo 111784 253547 := bstep (se 1 (by rfl) ⟨190160, by rfl⟩ : syracuseStep 253547 = 380321) B380321
theorem B253817 : Blo 111784 253817 := bstep (se 2 (by rfl) ⟨95181, by rfl⟩ : syracuseStep 253817 = 190363) B190363
theorem B319439 : Blo 111784 319439 := bstep (se 1 (by rfl) ⟨239579, by rfl⟩ : syracuseStep 319439 = 479159) B479159
theorem B253907 : Blo 111784 253907 := bstep (se 1 (by rfl) ⟨190430, by rfl⟩ : syracuseStep 253907 = 380861) B380861
theorem B254015 : Blo 111784 254015 := bstep (se 1 (by rfl) ⟨190511, by rfl⟩ : syracuseStep 254015 = 381023) B381023
theorem B5431499 : Blo 111784 5431499 := bstep (se 1 (by rfl) ⟨4073624, by rfl⟩ : syracuseStep 5431499 = 8147249) B8147249
theorem B156215 : Blo 111784 156215 := bstep (se 1 (by rfl) ⟨117161, by rfl⟩ : syracuseStep 156215 = 234323) B234323
theorem B5563181 : Blo 111784 5563181 := bstep (se 3 (by rfl) ⟨1043096, by rfl⟩ : syracuseStep 5563181 = 2086193) B2086193
theorem B615325 : Blo 111784 615325 := bstep (se 3 (by rfl) ⟨115373, by rfl⟩ : syracuseStep 615325 = 230747) B230747
theorem B255167 : Blo 111784 255167 := bstep (se 1 (by rfl) ⟨191375, by rfl⟩ : syracuseStep 255167 = 382751) B382751
theorem B321079 : Blo 111784 321079 := bstep (se 1 (by rfl) ⟨240809, by rfl⟩ : syracuseStep 321079 = 481619) B481619
theorem B288319 : Blo 111784 288319 := bstep (se 1 (by rfl) ⟨216239, by rfl⟩ : syracuseStep 288319 = 432479) B432479
theorem B288427 : Blo 111784 288427 := bstep (se 1 (by rfl) ⟨216320, by rfl⟩ : syracuseStep 288427 = 432641) B432641
theorem B616427 : Blo 111784 616427 := bstep (se 1 (by rfl) ⟨462320, by rfl⟩ : syracuseStep 616427 = 924641) B924641
theorem B288967 : Blo 111784 288967 := bstep (se 1 (by rfl) ⟨216725, by rfl⟩ : syracuseStep 288967 = 433451) B433451
theorem B584009 : Blo 111784 584009 := bstep (se 2 (by rfl) ⟨219003, by rfl⟩ : syracuseStep 584009 = 438007) B438007
theorem B584171 : Blo 111784 584171 := bstep (se 1 (by rfl) ⟨438128, by rfl⟩ : syracuseStep 584171 = 876257) B876257
theorem B650273 : Blo 111784 650273 := bstep (se 2 (by rfl) ⟨243852, by rfl⟩ : syracuseStep 650273 = 487705) B487705
theorem B322697 : Blo 111784 322697 := bstep (se 2 (by rfl) ⟨121011, by rfl⟩ : syracuseStep 322697 = 242023) B242023
theorem B585305 : Blo 111784 585305 := bstep (se 2 (by rfl) ⟨219489, by rfl⟩ : syracuseStep 585305 = 438979) B438979
theorem B192503 : Blo 111784 192503 := bstep (se 1 (by rfl) ⟨144377, by rfl⟩ : syracuseStep 192503 = 288755) B288755
theorem B127183 : Blo 111784 127183 := bstep (se 1 (by rfl) ⟨95387, by rfl⟩ : syracuseStep 127183 = 190775) B190775
theorem B291023 : Blo 111784 291023 := bstep (se 1 (by rfl) ⟨218267, by rfl⟩ : syracuseStep 291023 = 436535) B436535
theorem B192847 : Blo 111784 192847 := bstep (se 1 (by rfl) ⟨144635, by rfl⟩ : syracuseStep 192847 = 289271) B289271
theorem B323995 : Blo 111784 323995 := bstep (se 1 (by rfl) ⟨242996, by rfl⟩ : syracuseStep 323995 = 485993) B485993
theorem B651689 : Blo 111784 651689 := bstep (se 2 (by rfl) ⟨244383, by rfl⟩ : syracuseStep 651689 = 488767) B488767
theorem B3469873 : Blo 111784 3469873 := bstep (se 2 (by rfl) ⟨1301202, by rfl⟩ : syracuseStep 3469873 = 2602405) B2602405
theorem B553661 : Blo 111784 553661 := bstep (se 3 (by rfl) ⟨103811, by rfl⟩ : syracuseStep 553661 = 207623) B207623
theorem B160475 : Blo 111784 160475 := bstep (se 1 (by rfl) ⟨120356, by rfl⟩ : syracuseStep 160475 = 240713) B240713
theorem B291721 : Blo 111784 291721 := bstep (se 2 (by rfl) ⟨109395, by rfl⟩ : syracuseStep 291721 = 218791) B218791
theorem B128047 : Blo 111784 128047 := bstep (se 1 (by rfl) ⟨96035, by rfl⟩ : syracuseStep 128047 = 192071) B192071
theorem B193583 : Blo 111784 193583 := bstep (se 1 (by rfl) ⟨145187, by rfl⟩ : syracuseStep 193583 = 290375) B290375
theorem B291995 : Blo 111784 291995 := bstep (se 1 (by rfl) ⟨218996, by rfl⟩ : syracuseStep 291995 = 437993) B437993
theorem B390311 : Blo 111784 390311 := bstep (se 1 (by rfl) ⟨292733, by rfl⟩ : syracuseStep 390311 = 585467) B585467
theorem B357871 : Blo 111784 357871 := bstep (se 1 (by rfl) ⟨268403, by rfl⟩ : syracuseStep 357871 = 536807) B536807
theorem B816743 : Blo 111784 816743 := bstep (se 1 (by rfl) ⟨612557, by rfl⟩ : syracuseStep 816743 = 1225115) B1225115
theorem B259721 : Blo 111784 259721 := bstep (se 2 (by rfl) ⟨97395, by rfl⟩ : syracuseStep 259721 = 194791) B194791
theorem B129019 : Blo 111784 129019 := bstep (se 1 (by rfl) ⟨96764, by rfl⟩ : syracuseStep 129019 = 193529) B193529
theorem B194555 : Blo 111784 194555 := bstep (se 1 (by rfl) ⟨145916, by rfl⟩ : syracuseStep 194555 = 291833) B291833
theorem B129199 : Blo 111784 129199 := bstep (se 1 (by rfl) ⟨96899, by rfl⟩ : syracuseStep 129199 = 193799) B193799
theorem B1112363 : Blo 111784 1112363 := bstep (se 1 (by rfl) ⟨834272, by rfl⟩ : syracuseStep 1112363 = 1668545) B1668545
theorem B981827 : Blo 111784 981827 := bstep (se 1 (by rfl) ⟨736370, by rfl⟩ : syracuseStep 981827 = 1472741) B1472741
theorem B424871 : Blo 111784 424871 := bstep (se 1 (by rfl) ⟨318653, by rfl⟩ : syracuseStep 424871 = 637307) B637307
theorem B326683 : Blo 111784 326683 := bstep (se 1 (by rfl) ⟨245012, by rfl⟩ : syracuseStep 326683 = 490025) B490025
theorem B425371 : Blo 111784 425371 := bstep (se 1 (by rfl) ⟨319028, by rfl⟩ : syracuseStep 425371 = 638057) B638057
theorem B294391 : Blo 111784 294391 := bstep (se 1 (by rfl) ⟨220793, by rfl⟩ : syracuseStep 294391 = 441587) B441587
theorem B163615 : Blo 111784 163615 := bstep (se 1 (by rfl) ⟨122711, by rfl⟩ : syracuseStep 163615 = 245423) B245423
theorem B426131 : Blo 111784 426131 := bstep (se 1 (by rfl) ⟨319598, by rfl⟩ : syracuseStep 426131 = 639197) B639197
theorem B3670265 : Blo 111784 3670265 := bstep (se 2 (by rfl) ⟨1376349, by rfl⟩ : syracuseStep 3670265 = 2752699) B2752699
theorem B492007 : Blo 111784 492007 := bstep (se 1 (by rfl) ⟨369005, by rfl⟩ : syracuseStep 492007 = 738011) B738011
theorem B623227 : Blo 111784 623227 := bstep (se 1 (by rfl) ⟨467420, by rfl⟩ : syracuseStep 623227 = 934841) B934841
theorem B820433 : Blo 111784 820433 := bstep (se 2 (by rfl) ⟨307662, by rfl⟩ : syracuseStep 820433 = 615325) B615325
theorem B427933 : Blo 111784 427933 := bstep (se 3 (by rfl) ⟨80237, by rfl⟩ : syracuseStep 427933 = 160475) B160475
theorem B428105 : Blo 111784 428105 := bstep (se 2 (by rfl) ⟨160539, by rfl⟩ : syracuseStep 428105 = 321079) B321079
theorem B297083 : Blo 111784 297083 := bstep (se 1 (by rfl) ⟨222812, by rfl⟩ : syracuseStep 297083 = 445625) B445625
theorem B986579 : Blo 111784 986579 := bstep (se 1 (by rfl) ⟨739934, by rfl⟩ : syracuseStep 986579 = 1479869) B1479869
theorem B167711 : Blo 111784 167711 := bstep (se 1 (by rfl) ⟨125783, by rfl⟩ : syracuseStep 167711 = 251567) B251567
theorem B167759 : Blo 111784 167759 := bstep (se 1 (by rfl) ⟨125819, by rfl⟩ : syracuseStep 167759 = 251639) B251639
theorem B167879 : Blo 111784 167879 := bstep (se 1 (by rfl) ⟨125909, by rfl⟩ : syracuseStep 167879 = 251819) B251819
theorem B692263 : Blo 111784 692263 := bstep (se 1 (by rfl) ⟨519197, by rfl⟩ : syracuseStep 692263 = 1038395) B1038395
theorem B168119 : Blo 111784 168119 := bstep (se 1 (by rfl) ⟨126089, by rfl⟩ : syracuseStep 168119 = 252179) B252179
theorem B692459 : Blo 111784 692459 := bstep (se 1 (by rfl) ⟨519344, by rfl⟩ : syracuseStep 692459 = 1038689) B1038689
theorem B168191 : Blo 111784 168191 := bstep (se 1 (by rfl) ⟨126143, by rfl⟩ : syracuseStep 168191 = 252287) B252287
theorem B1315115 : Blo 111784 1315115 := bstep (se 1 (by rfl) ⟨986336, by rfl⟩ : syracuseStep 1315115 = 1972673) B1972673
theorem B168239 : Blo 111784 168239 := bstep (se 1 (by rfl) ⟨126179, by rfl⟩ : syracuseStep 168239 = 252359) B252359
theorem B6951349 : Blo 111784 6951349 := bstep (se 5 (by rfl) ⟨325844, by rfl⟩ : syracuseStep 6951349 = 651689) B651689
theorem B331321873 : Blo 111784 331321873 := bstep (se 2 (by rfl) ⟨124245702, by rfl⟩ : syracuseStep 331321873 = 248491405) B248491405
theorem B168479 : Blo 111784 168479 := bstep (se 1 (by rfl) ⟨126359, by rfl⟩ : syracuseStep 168479 = 252719) B252719
theorem B168539 : Blo 111784 168539 := bstep (se 1 (by rfl) ⟨126404, by rfl⟩ : syracuseStep 168539 = 252809) B252809
theorem B7082599 : Blo 111784 7082599 := bstep (se 1 (by rfl) ⟨5311949, by rfl⟩ : syracuseStep 7082599 = 10623899) B10623899
theorem B430703 : Blo 111784 430703 := bstep (se 1 (by rfl) ⟨323027, by rfl⟩ : syracuseStep 430703 = 646055) B646055
theorem B463585 : Blo 111784 463585 := bstep (se 2 (by rfl) ⟨173844, by rfl⟩ : syracuseStep 463585 = 347689) B347689
theorem B168743 : Blo 111784 168743 := bstep (se 1 (by rfl) ⟨126557, by rfl⟩ : syracuseStep 168743 = 253115) B253115
theorem B168911 : Blo 111784 168911 := bstep (se 1 (by rfl) ⟨126683, by rfl⟩ : syracuseStep 168911 = 253367) B253367
theorem B42374117 : Blo 111784 42374117 := bstep (se 4 (by rfl) ⟨3972573, by rfl⟩ : syracuseStep 42374117 = 7945147) B7945147
theorem B169031 : Blo 111784 169031 := bstep (se 1 (by rfl) ⟨126773, by rfl⟩ : syracuseStep 169031 = 253547) B253547
theorem B169211 : Blo 111784 169211 := bstep (se 1 (by rfl) ⟨126908, by rfl⟩ : syracuseStep 169211 = 253817) B253817
theorem B169271 : Blo 111784 169271 := bstep (se 1 (by rfl) ⟨126953, by rfl⟩ : syracuseStep 169271 = 253907) B253907
theorem B169343 : Blo 111784 169343 := bstep (se 1 (by rfl) ⟨127007, by rfl⟩ : syracuseStep 169343 = 254015) B254015
theorem B169577 : Blo 111784 169577 := bstep (se 2 (by rfl) ⟨63591, by rfl⟩ : syracuseStep 169577 = 127183) B127183
theorem B3708787 : Blo 111784 3708787 := bstep (se 1 (by rfl) ⟨2781590, by rfl⟩ : syracuseStep 3708787 = 5563181) B5563181
theorem B431993 : Blo 111784 431993 := bstep (se 2 (by rfl) ⟨161997, by rfl⟩ : syracuseStep 431993 = 323995) B323995
theorem B4626497 : Blo 111784 4626497 := bstep (se 2 (by rfl) ⟨1734936, by rfl⟩ : syracuseStep 4626497 = 3469873) B3469873
theorem B170111 : Blo 111784 170111 := bstep (se 1 (by rfl) ⟨127583, by rfl⟩ : syracuseStep 170111 = 255167) B255167
theorem B923795 : Blo 111784 923795 := bstep (se 1 (by rfl) ⟨692846, by rfl⟩ : syracuseStep 923795 = 1385693) B1385693
theorem B1841363 : Blo 111784 1841363 := bstep (se 1 (by rfl) ⟨1381022, by rfl⟩ : syracuseStep 1841363 = 2762045) B2762045
theorem B465533 : Blo 111784 465533 := bstep (se 3 (by rfl) ⟨87287, by rfl⟩ : syracuseStep 465533 = 174575) B174575
theorem B170729 : Blo 111784 170729 := bstep (se 2 (by rfl) ⟨64023, by rfl⟩ : syracuseStep 170729 = 128047) B128047
theorem B1645991 : Blo 111784 1645991 := bstep (se 1 (by rfl) ⟨1234493, by rfl⟩ : syracuseStep 1645991 = 2468987) B2468987
theorem B1122281 : Blo 111784 1122281 := bstep (se 2 (by rfl) ⟨420855, by rfl⟩ : syracuseStep 1122281 = 841711) B841711
theorem B172025 : Blo 111784 172025 := bstep (se 2 (by rfl) ⟨64509, by rfl⟩ : syracuseStep 172025 = 129019) B129019
theorem B172265 : Blo 111784 172265 := bstep (se 2 (by rfl) ⟨64599, by rfl⟩ : syracuseStep 172265 = 129199) B129199
theorem B369107 : Blo 111784 369107 := bstep (se 1 (by rfl) ⟨276830, by rfl⟩ : syracuseStep 369107 = 553661) B553661
theorem B730093 : Blo 111784 730093 := bstep (se 3 (by rfl) ⟨136892, by rfl⟩ : syracuseStep 730093 = 273785) B273785
theorem B173147 : Blo 111784 173147 := bstep (se 1 (by rfl) ⟨129860, by rfl⟩ : syracuseStep 173147 = 259721) B259721
theorem B435577 : Blo 111784 435577 := bstep (se 2 (by rfl) ⟨163341, by rfl⟩ : syracuseStep 435577 = 326683) B326683
theorem B567161 : Blo 111784 567161 := bstep (se 2 (by rfl) ⟨212685, by rfl⟩ : syracuseStep 567161 = 425371) B425371
theorem B272737 : Blo 111784 272737 := bstep (se 2 (by rfl) ⟨102276, by rfl⟩ : syracuseStep 272737 = 204553) B204553
theorem B1977047 : Blo 111784 1977047 := bstep (se 1 (by rfl) ⟨1482785, by rfl⟩ : syracuseStep 1977047 = 2965571) B2965571
theorem B240383 : Blo 111784 240383 := bstep (se 1 (by rfl) ⟨180287, by rfl⟩ : syracuseStep 240383 = 360575) B360575
theorem B273179 : Blo 111784 273179 := bstep (se 1 (by rfl) ⟨204884, by rfl⟩ : syracuseStep 273179 = 409769) B409769
theorem B895799 : Blo 111784 895799 := bstep (se 1 (by rfl) ⟨671849, by rfl⟩ : syracuseStep 895799 = 1343699) B1343699
theorem B273871 : Blo 111784 273871 := bstep (se 1 (by rfl) ⟨205403, by rfl⟩ : syracuseStep 273871 = 410807) B410807
theorem B143851 : Blo 111784 143851 := bstep (se 1 (by rfl) ⟨107888, by rfl⟩ : syracuseStep 143851 = 215777) B215777
theorem B275255 : Blo 111784 275255 := bstep (se 1 (by rfl) ⟨206441, by rfl⟩ : syracuseStep 275255 = 412883) B412883
theorem B111943 : Blo 111784 111943 := bstep (se 1 (by rfl) ⟨83957, by rfl⟩ : syracuseStep 111943 = 167915) B167915
theorem B308711 : Blo 111784 308711 := bstep (se 1 (by rfl) ⟨231533, by rfl⟩ : syracuseStep 308711 = 463067) B463067
theorem B112635 : Blo 111784 112635 := bstep (se 1 (by rfl) ⟨84476, by rfl⟩ : syracuseStep 112635 = 168953) B168953
theorem B112767 : Blo 111784 112767 := bstep (se 1 (by rfl) ⟨84575, by rfl⟩ : syracuseStep 112767 = 169151) B169151
theorem B1620157 : Blo 111784 1620157 := bstep (se 3 (by rfl) ⟨303779, by rfl⟩ : syracuseStep 1620157 = 607559) B607559
theorem B112863 : Blo 111784 112863 := bstep (se 1 (by rfl) ⟨84647, by rfl⟩ : syracuseStep 112863 = 169295) B169295
theorem B112923 : Blo 111784 112923 := bstep (se 1 (by rfl) ⟨84692, by rfl⟩ : syracuseStep 112923 = 169385) B169385
theorem B112959 : Blo 111784 112959 := bstep (se 1 (by rfl) ⟨84719, by rfl⟩ : syracuseStep 112959 = 169439) B169439
theorem B113023 : Blo 111784 113023 := bstep (se 1 (by rfl) ⟨84767, by rfl⟩ : syracuseStep 113023 = 169535) B169535
theorem B113343 : Blo 111784 113343 := bstep (se 1 (by rfl) ⟨85007, by rfl⟩ : syracuseStep 113343 = 170015) B170015
theorem B146215 : Blo 111784 146215 := bstep (se 1 (by rfl) ⟨109661, by rfl⟩ : syracuseStep 146215 = 219323) B219323
theorem B113631 : Blo 111784 113631 := bstep (se 1 (by rfl) ⟨85223, by rfl⟩ : syracuseStep 113631 = 170447) B170447
theorem B408559 : Blo 111784 408559 := bstep (se 1 (by rfl) ⟨306419, by rfl⟩ : syracuseStep 408559 = 612839) B612839
theorem B113691 : Blo 111784 113691 := bstep (se 1 (by rfl) ⟨85268, by rfl⟩ : syracuseStep 113691 = 170537) B170537
theorem B113831 : Blo 111784 113831 := bstep (se 1 (by rfl) ⟨85373, by rfl⟩ : syracuseStep 113831 = 170747) B170747
theorem B113915 : Blo 111784 113915 := bstep (se 1 (by rfl) ⟨85436, by rfl⟩ : syracuseStep 113915 = 170873) B170873
theorem B966107 : Blo 111784 966107 := bstep (se 1 (by rfl) ⟨724580, by rfl⟩ : syracuseStep 966107 = 1449161) B1449161
theorem B277985 : Blo 111784 277985 := bstep (se 2 (by rfl) ⟨104244, by rfl⟩ : syracuseStep 277985 = 208489) B208489
theorem B867995 : Blo 111784 867995 := bstep (se 1 (by rfl) ⟨650996, by rfl⟩ : syracuseStep 867995 = 1301993) B1301993
theorem B114415 : Blo 111784 114415 := bstep (se 1 (by rfl) ⟨85811, by rfl⟩ : syracuseStep 114415 = 171623) B171623
theorem B114523 : Blo 111784 114523 := bstep (se 1 (by rfl) ⟨85892, by rfl⟩ : syracuseStep 114523 = 171785) B171785
theorem B212959 : Blo 111784 212959 := bstep (se 1 (by rfl) ⟨159719, by rfl⟩ : syracuseStep 212959 = 319439) B319439
theorem B114671 : Blo 111784 114671 := bstep (se 1 (by rfl) ⟨86003, by rfl⟩ : syracuseStep 114671 = 172007) B172007
theorem B114751 : Blo 111784 114751 := bstep (se 1 (by rfl) ⟨86063, by rfl⟩ : syracuseStep 114751 = 172127) B172127
theorem B114791 : Blo 111784 114791 := bstep (se 1 (by rfl) ⟨86093, by rfl⟩ : syracuseStep 114791 = 172187) B172187
theorem B3620999 : Blo 111784 3620999 := bstep (se 1 (by rfl) ⟨2715749, by rfl⟩ : syracuseStep 3620999 = 5431499) B5431499
theorem B114847 : Blo 111784 114847 := bstep (se 1 (by rfl) ⟨86135, by rfl⟩ : syracuseStep 114847 = 172271) B172271
theorem B180479 : Blo 111784 180479 := bstep (se 1 (by rfl) ⟨135359, by rfl⟩ : syracuseStep 180479 = 270719) B270719
theorem B6799625 : Blo 111784 6799625 := bstep (se 2 (by rfl) ⟨2549859, by rfl⟩ : syracuseStep 6799625 = 5099719) B5099719
theorem B115099 : Blo 111784 115099 := bstep (se 1 (by rfl) ⟨86324, by rfl⟩ : syracuseStep 115099 = 172649) B172649
theorem B115103 : Blo 111784 115103 := bstep (se 1 (by rfl) ⟨86327, by rfl⟩ : syracuseStep 115103 = 172655) B172655
theorem B6603227 : Blo 111784 6603227 := bstep (se 1 (by rfl) ⟨4952420, by rfl⟩ : syracuseStep 6603227 = 9904841) B9904841
theorem B312041 : Blo 111784 312041 := bstep (se 2 (by rfl) ⟨117015, by rfl⟩ : syracuseStep 312041 = 234031) B234031
theorem B115519 : Blo 111784 115519 := bstep (se 1 (by rfl) ⟨86639, by rfl⟩ : syracuseStep 115519 = 173279) B173279
theorem B574289 : Blo 111784 574289 := bstep (se 2 (by rfl) ⟨215358, by rfl⟩ : syracuseStep 574289 = 430717) B430717
theorem B115679 : Blo 111784 115679 := bstep (se 1 (by rfl) ⟨86759, by rfl⟩ : syracuseStep 115679 = 173519) B173519
theorem B410951 : Blo 111784 410951 := bstep (se 1 (by rfl) ⟨308213, by rfl⟩ : syracuseStep 410951 = 616427) B616427
theorem B378215 : Blo 111784 378215 := bstep (se 1 (by rfl) ⟨283661, by rfl⟩ : syracuseStep 378215 = 567323) B567323
theorem B477161 : Blo 111784 477161 := bstep (se 2 (by rfl) ⟨178935, by rfl⟩ : syracuseStep 477161 = 357871) B357871
theorem B215131 : Blo 111784 215131 := bstep (se 1 (by rfl) ⟨161348, by rfl⟩ : syracuseStep 215131 = 322697) B322697
theorem B182683 : Blo 111784 182683 := bstep (se 1 (by rfl) ⟨137012, by rfl⟩ : syracuseStep 182683 = 274025) B274025
theorem B183401 : Blo 111784 183401 := bstep (se 2 (by rfl) ⟨68775, by rfl⟩ : syracuseStep 183401 = 137551) B137551
theorem B2150063 : Blo 111784 2150063 := bstep (se 1 (by rfl) ⟨1612547, by rfl⟩ : syracuseStep 2150063 = 3225095) B3225095
theorem B544495 : Blo 111784 544495 := bstep (se 1 (by rfl) ⟨408371, by rfl⟩ : syracuseStep 544495 = 816743) B816743
theorem B1560323 : Blo 111784 1560323 := bstep (se 1 (by rfl) ⟨1170242, by rfl⟩ : syracuseStep 1560323 = 2340485) B2340485
theorem B642887 : Blo 111784 642887 := bstep (se 1 (by rfl) ⟨482165, by rfl⟩ : syracuseStep 642887 = 964331) B964331
theorem B2805637 : Blo 111784 2805637 := bstep (se 4 (by rfl) ⟨263028, by rfl⟩ : syracuseStep 2805637 = 526057) B526057
theorem B741575 : Blo 111784 741575 := bstep (se 1 (by rfl) ⟨556181, by rfl⟩ : syracuseStep 741575 = 1112363) B1112363
theorem B283247 : Blo 111784 283247 := bstep (se 1 (by rfl) ⟨212435, by rfl⟩ : syracuseStep 283247 = 424871) B424871
theorem B218153 : Blo 111784 218153 := bstep (se 2 (by rfl) ⟨81807, by rfl⟩ : syracuseStep 218153 = 163615) B163615
theorem B578987 : Blo 111784 578987 := bstep (se 1 (by rfl) ⟨434240, by rfl⟩ : syracuseStep 578987 = 868481) B868481
theorem B382967 : Blo 111784 382967 := bstep (se 1 (by rfl) ⟨287225, by rfl⟩ : syracuseStep 382967 = 574451) B574451
theorem B120943 : Blo 111784 120943 := bstep (se 1 (by rfl) ⟨90707, by rfl⟩ : syracuseStep 120943 = 181415) B181415
theorem B252215 : Blo 111784 252215 := bstep (se 1 (by rfl) ⟨189161, by rfl⟩ : syracuseStep 252215 = 378323) B378323
theorem B252575 : Blo 111784 252575 := bstep (se 1 (by rfl) ⟨189431, by rfl⟩ : syracuseStep 252575 = 378863) B378863
theorem B580283 : Blo 111784 580283 := bstep (se 1 (by rfl) ⟨435212, by rfl⟩ : syracuseStep 580283 = 870425) B870425
theorem B613079 : Blo 111784 613079 := bstep (se 1 (by rfl) ⟨459809, by rfl⟩ : syracuseStep 613079 = 919619) B919619
theorem B416573 : Blo 111784 416573 := bstep (se 3 (by rfl) ⟨78107, by rfl⟩ : syracuseStep 416573 = 156215) B156215
theorem B384047 : Blo 111784 384047 := bstep (se 1 (by rfl) ⟨288035, by rfl⟩ : syracuseStep 384047 = 576071) B576071
theorem B384425 : Blo 111784 384425 := bstep (se 2 (by rfl) ⟨144159, by rfl⟩ : syracuseStep 384425 = 288319) B288319
theorem B384569 : Blo 111784 384569 := bstep (se 2 (by rfl) ⟨144213, by rfl⟩ : syracuseStep 384569 = 288427) B288427
theorem B385127 : Blo 111784 385127 := bstep (se 1 (by rfl) ⟨288845, by rfl⟩ : syracuseStep 385127 = 577691) B577691
theorem B385289 : Blo 111784 385289 := bstep (se 2 (by rfl) ⟨144483, by rfl⟩ : syracuseStep 385289 = 288967) B288967
theorem B2482487 : Blo 111784 2482487 := bstep (se 1 (by rfl) ⟨1861865, by rfl⟩ : syracuseStep 2482487 = 3723731) B3723731
theorem B188743 : Blo 111784 188743 := bstep (se 1 (by rfl) ⟨141557, by rfl⟩ : syracuseStep 188743 = 283115) B283115
theorem B254519 : Blo 111784 254519 := bstep (se 1 (by rfl) ⟨190889, by rfl⟩ : syracuseStep 254519 = 381779) B381779
theorem B582227 : Blo 111784 582227 := bstep (se 1 (by rfl) ⟨436670, by rfl⟩ : syracuseStep 582227 = 873341) B873341
theorem B254555 : Blo 111784 254555 := bstep (se 1 (by rfl) ⟨190916, by rfl⟩ : syracuseStep 254555 = 381833) B381833
theorem B254879 : Blo 111784 254879 := bstep (se 1 (by rfl) ⟨191159, by rfl⟩ : syracuseStep 254879 = 382319) B382319
theorem B386045 : Blo 111784 386045 := bstep (se 3 (by rfl) ⟨72383, by rfl⟩ : syracuseStep 386045 = 144767) B144767
theorem B386207 : Blo 111784 386207 := bstep (se 1 (by rfl) ⟨289655, by rfl⟩ : syracuseStep 386207 = 579311) B579311
theorem B582875 : Blo 111784 582875 := bstep (se 1 (by rfl) ⟨437156, by rfl⟩ : syracuseStep 582875 = 874313) B874313
theorem B287975 : Blo 111784 287975 := bstep (se 1 (by rfl) ⟨215981, by rfl⟩ : syracuseStep 287975 = 431963) B431963
theorem B812717 : Blo 111784 812717 := bstep (se 3 (by rfl) ⟨152384, by rfl⟩ : syracuseStep 812717 = 304769) B304769
theorem B190127 : Blo 111784 190127 := bstep (se 1 (by rfl) ⟨142595, by rfl⟩ : syracuseStep 190127 = 285191) B285191
theorem B190505 : Blo 111784 190505 := bstep (se 2 (by rfl) ⟨71439, by rfl⟩ : syracuseStep 190505 = 142879) B142879
theorem B190687 : Blo 111784 190687 := bstep (se 1 (by rfl) ⟨143015, by rfl⟩ : syracuseStep 190687 = 286031) B286031
theorem B289079 : Blo 111784 289079 := bstep (se 1 (by rfl) ⟨216809, by rfl⟩ : syracuseStep 289079 = 433619) B433619
theorem B257129 : Blo 111784 257129 := bstep (se 2 (by rfl) ⟨96423, by rfl⟩ : syracuseStep 257129 = 192847) B192847
theorem B1862777 : Blo 111784 1862777 := bstep (se 2 (by rfl) ⟨698541, by rfl⟩ : syracuseStep 1862777 = 1397083) B1397083
theorem B388961 : Blo 111784 388961 := bstep (se 2 (by rfl) ⟨145860, by rfl⟩ : syracuseStep 388961 = 291721) B291721
theorem B487291 : Blo 111784 487291 := bstep (se 1 (by rfl) ⟨365468, by rfl⟩ : syracuseStep 487291 = 730937) B730937
theorem B389339 : Blo 111784 389339 := bstep (se 1 (by rfl) ⟨292004, by rfl⟩ : syracuseStep 389339 = 584009) B584009
theorem B389447 : Blo 111784 389447 := bstep (se 1 (by rfl) ⟨292085, by rfl⟩ : syracuseStep 389447 = 584171) B584171
theorem B390203 : Blo 111784 390203 := bstep (se 1 (by rfl) ⟨292652, by rfl⟩ : syracuseStep 390203 = 585305) B585305
theorem B128335 : Blo 111784 128335 := bstep (se 1 (by rfl) ⟨96251, by rfl⟩ : syracuseStep 128335 = 192503) B192503
theorem B193961 : Blo 111784 193961 := bstep (se 2 (by rfl) ⟨72735, by rfl⟩ : syracuseStep 193961 = 145471) B145471
theorem B1734061 : Blo 111784 1734061 := bstep (se 3 (by rfl) ⟨325136, by rfl⟩ : syracuseStep 1734061 = 650273) B650273
theorem B194015 : Blo 111784 194015 := bstep (se 1 (by rfl) ⟨145511, by rfl⟩ : syracuseStep 194015 = 291023) B291023
theorem B129055 : Blo 111784 129055 := bstep (se 1 (by rfl) ⟨96791, by rfl⟩ : syracuseStep 129055 = 193583) B193583
theorem B194663 : Blo 111784 194663 := bstep (se 1 (by rfl) ⟨145997, by rfl⟩ : syracuseStep 194663 = 291995) B291995
theorem B260207 : Blo 111784 260207 := bstep (se 1 (by rfl) ⟨195155, by rfl⟩ : syracuseStep 260207 = 390311) B390311
theorem B162271 : Blo 111784 162271 := bstep (se 1 (by rfl) ⟨121703, by rfl⟩ : syracuseStep 162271 = 243407) B243407
theorem B129703 : Blo 111784 129703 := bstep (se 1 (by rfl) ⟨97277, by rfl⟩ : syracuseStep 129703 = 194555) B194555
theorem B490283 : Blo 111784 490283 := bstep (se 1 (by rfl) ⟨367712, by rfl⟩ : syracuseStep 490283 = 735425) B735425
theorem B28146653 : Blo 111784 28146653 := bstep (se 3 (by rfl) ⟨5277497, by rfl⟩ : syracuseStep 28146653 = 10554995) B10554995
theorem B425159 : Blo 111784 425159 := bstep (se 1 (by rfl) ⟨318869, by rfl⟩ : syracuseStep 425159 = 637739) B637739
theorem B654551 : Blo 111784 654551 := bstep (se 1 (by rfl) ⟨490913, by rfl⟩ : syracuseStep 654551 = 981827) B981827
theorem B392521 : Blo 111784 392521 := bstep (se 2 (by rfl) ⟨147195, by rfl⟩ : syracuseStep 392521 = 294391) B294391
theorem B656009 : Blo 111784 656009 := bstep (se 2 (by rfl) ⟨246003, by rfl⟩ : syracuseStep 656009 = 492007) B492007
theorem B198055 : Blo 111784 198055 := bstep (se 1 (by rfl) ⟨148541, by rfl⟩ : syracuseStep 198055 = 297083) B297083
theorem B657719 : Blo 111784 657719 := bstep (se 1 (by rfl) ⟨493289, by rfl⟩ : syracuseStep 657719 = 986579) B986579
theorem B428591 : Blo 111784 428591 := bstep (se 1 (by rfl) ⟨321443, by rfl⟩ : syracuseStep 428591 = 642887) B642887
theorem B494383 : Blo 111784 494383 := bstep (se 1 (by rfl) ⟨370787, by rfl⟩ : syracuseStep 494383 = 741575) B741575
theorem B461639 : Blo 111784 461639 := bstep (se 1 (by rfl) ⟨346229, by rfl⟩ : syracuseStep 461639 = 692459) B692459
theorem B28249411 : Blo 111784 28249411 := bstep (se 1 (by rfl) ⟨21187058, by rfl⟩ : syracuseStep 28249411 = 42374117) B42374117
theorem B823229 : Blo 111784 823229 := bstep (se 3 (by rfl) ⟨154355, by rfl⟩ : syracuseStep 823229 = 308711) B308711
theorem B3084331 : Blo 111784 3084331 := bstep (se 1 (by rfl) ⟨2313248, by rfl⟩ : syracuseStep 3084331 = 4626497) B4626497
theorem B168143 : Blo 111784 168143 := bstep (se 1 (by rfl) ⟨126107, by rfl⟩ : syracuseStep 168143 = 252215) B252215
theorem B168383 : Blo 111784 168383 := bstep (se 1 (by rfl) ⟨126287, by rfl⟩ : syracuseStep 168383 = 252575) B252575
theorem B365161 : Blo 111784 365161 := bstep (se 2 (by rfl) ⟨136935, by rfl⟩ : syracuseStep 365161 = 273871) B273871
theorem B725993 : Blo 111784 725993 := bstep (se 2 (by rfl) ⟨272247, by rfl⟩ : syracuseStep 725993 = 544495) B544495
theorem B3740849 : Blo 111784 3740849 := bstep (se 2 (by rfl) ⟨1402818, by rfl⟩ : syracuseStep 3740849 = 2805637) B2805637
theorem B923017 : Blo 111784 923017 := bstep (se 2 (by rfl) ⟨346131, by rfl⟩ : syracuseStep 923017 = 692263) B692263
theorem B169679 : Blo 111784 169679 := bstep (se 1 (by rfl) ⟨127259, by rfl⟩ : syracuseStep 169679 = 254519) B254519
theorem B169703 : Blo 111784 169703 := bstep (se 1 (by rfl) ⟨127277, by rfl⟩ : syracuseStep 169703 = 254555) B254555
theorem B169919 : Blo 111784 169919 := bstep (se 1 (by rfl) ⟨127439, by rfl⟩ : syracuseStep 169919 = 254879) B254879
theorem B9443465 : Blo 111784 9443465 := bstep (se 2 (by rfl) ⟨3541299, by rfl⟩ : syracuseStep 9443465 = 7082599) B7082599
theorem B171113 : Blo 111784 171113 := bstep (se 2 (by rfl) ⟨64167, by rfl⟩ : syracuseStep 171113 = 128335) B128335
theorem B1318031 : Blo 111784 1318031 := bstep (se 1 (by rfl) ⟨988523, by rfl⟩ : syracuseStep 1318031 = 1977047) B1977047
theorem B171419 : Blo 111784 171419 := bstep (se 1 (by rfl) ⟨128564, by rfl⟩ : syracuseStep 171419 = 257129) B257129
theorem B728477 : Blo 111784 728477 := bstep (se 3 (by rfl) ⟨136589, by rfl⟩ : syracuseStep 728477 = 273179) B273179
theorem B172073 : Blo 111784 172073 := bstep (se 2 (by rfl) ⟨64527, by rfl⟩ : syracuseStep 172073 = 129055) B129055
theorem B172937 : Blo 111784 172937 := bstep (se 2 (by rfl) ⟨64851, by rfl⟩ : syracuseStep 172937 = 129703) B129703
theorem B173471 : Blo 111784 173471 := bstep (se 1 (by rfl) ⟨130103, by rfl⟩ : syracuseStep 173471 = 260207) B260207
theorem B436367 : Blo 111784 436367 := bstep (se 1 (by rfl) ⟨327275, by rfl⟩ : syracuseStep 436367 = 654551) B654551
theorem B4533083 : Blo 111784 4533083 := bstep (se 1 (by rfl) ⟨3399812, by rfl⟩ : syracuseStep 4533083 = 6799625) B6799625
theorem B4402151 : Blo 111784 4402151 := bstep (se 1 (by rfl) ⟨3301613, by rfl⟩ : syracuseStep 4402151 = 6603227) B6603227
theorem B208027 : Blo 111784 208027 := bstep (se 1 (by rfl) ⟨156020, by rfl⟩ : syracuseStep 208027 = 312041) B312041
theorem B830969 : Blo 111784 830969 := bstep (se 2 (by rfl) ⟨311613, by rfl⟩ : syracuseStep 830969 = 623227) B623227
theorem B1454597 : Blo 111784 1454597 := bstep (se 4 (by rfl) ⟨136368, by rfl⟩ : syracuseStep 1454597 = 272737) B272737
theorem B111807 : Blo 111784 111807 := bstep (se 1 (by rfl) ⟨83855, by rfl⟩ : syracuseStep 111807 = 167711) B167711
theorem B570577 : Blo 111784 570577 := bstep (se 2 (by rfl) ⟨213966, by rfl⟩ : syracuseStep 570577 = 427933) B427933
theorem B111839 : Blo 111784 111839 := bstep (se 1 (by rfl) ⟨83879, by rfl⟩ : syracuseStep 111839 = 167759) B167759
theorem B111919 : Blo 111784 111919 := bstep (se 1 (by rfl) ⟨83939, by rfl⟩ : syracuseStep 111919 = 167879) B167879
theorem B112079 : Blo 111784 112079 := bstep (se 1 (by rfl) ⟨84059, by rfl⟩ : syracuseStep 112079 = 168119) B168119
theorem B112127 : Blo 111784 112127 := bstep (se 1 (by rfl) ⟨84095, by rfl⟩ : syracuseStep 112127 = 168191) B168191
theorem B112159 : Blo 111784 112159 := bstep (se 1 (by rfl) ⟨84119, by rfl⟩ : syracuseStep 112159 = 168239) B168239
theorem B112319 : Blo 111784 112319 := bstep (se 1 (by rfl) ⟨84239, by rfl⟩ : syracuseStep 112319 = 168479) B168479
theorem B112359 : Blo 111784 112359 := bstep (se 1 (by rfl) ⟨84269, by rfl⟩ : syracuseStep 112359 = 168539) B168539
theorem B112495 : Blo 111784 112495 := bstep (se 1 (by rfl) ⟨84371, by rfl⟩ : syracuseStep 112495 = 168743) B168743
theorem B243577 : Blo 111784 243577 := bstep (se 2 (by rfl) ⟨91341, by rfl⟩ : syracuseStep 243577 = 182683) B182683
theorem B112607 : Blo 111784 112607 := bstep (se 1 (by rfl) ⟨84455, by rfl⟩ : syracuseStep 112607 = 168911) B168911
theorem B112687 : Blo 111784 112687 := bstep (se 1 (by rfl) ⟨84515, by rfl⟩ : syracuseStep 112687 = 169031) B169031
theorem B112807 : Blo 111784 112807 := bstep (se 1 (by rfl) ⟨84605, by rfl⟩ : syracuseStep 112807 = 169211) B169211
theorem B1095869 : Blo 111784 1095869 := bstep (se 3 (by rfl) ⟨205475, by rfl⟩ : syracuseStep 1095869 = 410951) B410951
theorem B112847 : Blo 111784 112847 := bstep (se 1 (by rfl) ⟨84635, by rfl⟩ : syracuseStep 112847 = 169271) B169271
theorem B112895 : Blo 111784 112895 := bstep (se 1 (by rfl) ⟨84671, by rfl⟩ : syracuseStep 112895 = 169343) B169343
theorem B113051 : Blo 111784 113051 := bstep (se 1 (by rfl) ⟨84788, by rfl⟩ : syracuseStep 113051 = 169577) B169577
theorem B113407 : Blo 111784 113407 := bstep (se 1 (by rfl) ⟨85055, by rfl⟩ : syracuseStep 113407 = 170111) B170111
theorem B1227575 : Blo 111784 1227575 := bstep (se 1 (by rfl) ⟨920681, by rfl⟩ : syracuseStep 1227575 = 1841363) B1841363
theorem B310355 : Blo 111784 310355 := bstep (se 1 (by rfl) ⟨232766, by rfl⟩ : syracuseStep 310355 = 465533) B465533
theorem B408719 : Blo 111784 408719 := bstep (se 1 (by rfl) ⟨306539, by rfl⟩ : syracuseStep 408719 = 613079) B613079
theorem B113819 : Blo 111784 113819 := bstep (se 1 (by rfl) ⟨85364, by rfl⟩ : syracuseStep 113819 = 170729) B170729
theorem B277715 : Blo 111784 277715 := bstep (se 1 (by rfl) ⟨208286, by rfl⟩ : syracuseStep 277715 = 416573) B416573
theorem B1097327 : Blo 111784 1097327 := bstep (se 1 (by rfl) ⟨822995, by rfl⟩ : syracuseStep 1097327 = 1645991) B1645991
theorem B114683 : Blo 111784 114683 := bstep (se 1 (by rfl) ⟨86012, by rfl⟩ : syracuseStep 114683 = 172025) B172025
theorem B114843 : Blo 111784 114843 := bstep (se 1 (by rfl) ⟨86132, by rfl⟩ : syracuseStep 114843 = 172265) B172265
theorem B1654991 : Blo 111784 1654991 := bstep (se 1 (by rfl) ⟨1241243, by rfl⟩ : syracuseStep 1654991 = 2482487) B2482487
theorem B246071 : Blo 111784 246071 := bstep (se 1 (by rfl) ⟨184553, by rfl⟩ : syracuseStep 246071 = 369107) B369107
theorem B441762497 : Blo 111784 441762497 := bstep (se 2 (by rfl) ⟨165660936, by rfl⟩ : syracuseStep 441762497 = 331321873) B331321873
theorem B115431 : Blo 111784 115431 := bstep (se 1 (by rfl) ⟨86573, by rfl⟩ : syracuseStep 115431 = 173147) B173147
theorem B541811 : Blo 111784 541811 := bstep (se 1 (by rfl) ⟨406358, by rfl⟩ : syracuseStep 541811 = 812717) B812717
theorem B378107 : Blo 111784 378107 := bstep (se 1 (by rfl) ⟨283580, by rfl⟩ : syracuseStep 378107 = 567161) B567161
theorem B2312081 : Blo 111784 2312081 := bstep (se 2 (by rfl) ⟨867030, by rfl⟩ : syracuseStep 2312081 = 1734061) B1734061
theorem B183503 : Blo 111784 183503 := bstep (se 1 (by rfl) ⟨137627, by rfl⟩ : syracuseStep 183503 = 275255) B275255
theorem B216361 : Blo 111784 216361 := bstep (se 2 (by rfl) ⟨81135, by rfl⟩ : syracuseStep 216361 = 162271) B162271
theorem B544745 : Blo 111784 544745 := bstep (se 2 (by rfl) ⟨204279, by rfl⟩ : syracuseStep 544745 = 408559) B408559
theorem B18764435 : Blo 111784 18764435 := bstep (se 1 (by rfl) ⟨14073326, by rfl⟩ : syracuseStep 18764435 = 28146653) B28146653
theorem B283439 : Blo 111784 283439 := bstep (se 1 (by rfl) ⟨212579, by rfl⟩ : syracuseStep 283439 = 425159) B425159
theorem B644071 : Blo 111784 644071 := bstep (se 1 (by rfl) ⟨483053, by rfl⟩ : syracuseStep 644071 = 966107) B966107
theorem B185323 : Blo 111784 185323 := bstep (se 1 (by rfl) ⟨138992, by rfl⟩ : syracuseStep 185323 = 277985) B277985
theorem B578663 : Blo 111784 578663 := bstep (se 1 (by rfl) ⟨433997, by rfl⟩ : syracuseStep 578663 = 867995) B867995
theorem B283945 : Blo 111784 283945 := bstep (se 2 (by rfl) ⟨106479, by rfl⟩ : syracuseStep 283945 = 212959) B212959
theorem B2413999 : Blo 111784 2413999 := bstep (se 1 (by rfl) ⟨1810499, by rfl⟩ : syracuseStep 2413999 = 3620999) B3620999
theorem B284087 : Blo 111784 284087 := bstep (se 1 (by rfl) ⟨213065, by rfl⟩ : syracuseStep 284087 = 426131) B426131
theorem B2446843 : Blo 111784 2446843 := bstep (se 1 (by rfl) ⟨1835132, by rfl⟩ : syracuseStep 2446843 = 3670265) B3670265
theorem B251657 : Blo 111784 251657 := bstep (se 2 (by rfl) ⟨94371, by rfl⟩ : syracuseStep 251657 = 188743) B188743
theorem B382859 : Blo 111784 382859 := bstep (se 1 (by rfl) ⟨287144, by rfl⟩ : syracuseStep 382859 = 574289) B574289
theorem B645029 : Blo 111784 645029 := bstep (se 4 (by rfl) ⟨60471, by rfl⟩ : syracuseStep 645029 = 120943) B120943
theorem B481277 : Blo 111784 481277 := bstep (se 3 (by rfl) ⟨90239, by rfl⟩ : syracuseStep 481277 = 180479) B180479
theorem B546955 : Blo 111784 546955 := bstep (se 1 (by rfl) ⟨410216, by rfl⟩ : syracuseStep 546955 = 820433) B820433
theorem B252143 : Blo 111784 252143 := bstep (se 1 (by rfl) ⟨189107, by rfl⟩ : syracuseStep 252143 = 378215) B378215
theorem B973457 : Blo 111784 973457 := bstep (se 2 (by rfl) ⟨365046, by rfl⟩ : syracuseStep 973457 = 730093) B730093
theorem B318107 : Blo 111784 318107 := bstep (se 1 (by rfl) ⟨238580, by rfl⟩ : syracuseStep 318107 = 477161) B477161
theorem B285403 : Blo 111784 285403 := bstep (se 1 (by rfl) ⟨214052, by rfl⟩ : syracuseStep 285403 = 428105) B428105
theorem B580769 : Blo 111784 580769 := bstep (se 2 (by rfl) ⟨217788, by rfl⟩ : syracuseStep 580769 = 435577) B435577
theorem B122267 : Blo 111784 122267 := bstep (se 1 (by rfl) ⟨91700, by rfl⟩ : syracuseStep 122267 = 183401) B183401
theorem B1433375 : Blo 111784 1433375 := bstep (se 1 (by rfl) ⟨1075031, by rfl⟩ : syracuseStep 1433375 = 2150063) B2150063
theorem B1040215 : Blo 111784 1040215 := bstep (se 1 (by rfl) ⟨780161, by rfl⟩ : syracuseStep 1040215 = 1560323) B1560323
theorem B581741 : Blo 111784 581741 := bstep (se 3 (by rfl) ⟨109076, by rfl⟩ : syracuseStep 581741 = 218153) B218153
theorem B286841 : Blo 111784 286841 := bstep (se 2 (by rfl) ⟨107565, by rfl⟩ : syracuseStep 286841 = 215131) B215131
theorem B876743 : Blo 111784 876743 := bstep (se 1 (by rfl) ⟨657557, by rfl⟩ : syracuseStep 876743 = 1315115) B1315115
theorem B254249 : Blo 111784 254249 := bstep (se 2 (by rfl) ⟨95343, by rfl⟩ : syracuseStep 254249 = 190687) B190687
theorem B188831 : Blo 111784 188831 := bstep (se 1 (by rfl) ⟨141623, by rfl⟩ : syracuseStep 188831 = 283247) B283247
theorem B287135 : Blo 111784 287135 := bstep (se 1 (by rfl) ⟨215351, by rfl⟩ : syracuseStep 287135 = 430703) B430703
theorem B385991 : Blo 111784 385991 := bstep (se 1 (by rfl) ⟨289493, by rfl⟩ : syracuseStep 385991 = 578987) B578987
theorem B517229 : Blo 111784 517229 := bstep (se 3 (by rfl) ⟨96980, by rfl⟩ : syracuseStep 517229 = 193961) B193961
theorem B287995 : Blo 111784 287995 := bstep (se 1 (by rfl) ⟨215996, by rfl⟩ : syracuseStep 287995 = 431993) B431993
theorem B255311 : Blo 111784 255311 := bstep (se 1 (by rfl) ⟨191483, by rfl⟩ : syracuseStep 255311 = 382967) B382967
theorem B615863 : Blo 111784 615863 := bstep (se 1 (by rfl) ⟨461897, by rfl⟩ : syracuseStep 615863 = 923795) B923795
theorem B386855 : Blo 111784 386855 := bstep (se 1 (by rfl) ⟨290141, by rfl⟩ : syracuseStep 386855 = 580283) B580283
theorem B256031 : Blo 111784 256031 := bstep (se 1 (by rfl) ⟨192023, by rfl⟩ : syracuseStep 256031 = 384047) B384047
theorem B256283 : Blo 111784 256283 := bstep (se 1 (by rfl) ⟨192212, by rfl⟩ : syracuseStep 256283 = 384425) B384425
theorem B256379 : Blo 111784 256379 := bstep (se 1 (by rfl) ⟨192284, by rfl⟩ : syracuseStep 256379 = 384569) B384569
theorem B649721 : Blo 111784 649721 := bstep (se 2 (by rfl) ⟨243645, by rfl⟩ : syracuseStep 649721 = 487291) B487291
theorem B748187 : Blo 111784 748187 := bstep (se 1 (by rfl) ⟨561140, by rfl⟩ : syracuseStep 748187 = 1122281) B1122281
theorem B256751 : Blo 111784 256751 := bstep (se 1 (by rfl) ⟨192563, by rfl⟩ : syracuseStep 256751 = 385127) B385127
theorem B256859 : Blo 111784 256859 := bstep (se 1 (by rfl) ⟨192644, by rfl⟩ : syracuseStep 256859 = 385289) B385289
theorem B388151 : Blo 111784 388151 := bstep (se 1 (by rfl) ⟨291113, by rfl⟩ : syracuseStep 388151 = 582227) B582227
theorem B9268465 : Blo 111784 9268465 := bstep (se 2 (by rfl) ⟨3475674, by rfl⟩ : syracuseStep 9268465 = 6951349) B6951349
theorem B191801 : Blo 111784 191801 := bstep (se 2 (by rfl) ⟨71925, by rfl⟩ : syracuseStep 191801 = 143851) B143851
theorem B257363 : Blo 111784 257363 := bstep (se 1 (by rfl) ⟨193022, by rfl⟩ : syracuseStep 257363 = 386045) B386045
theorem B257471 : Blo 111784 257471 := bstep (se 1 (by rfl) ⟨193103, by rfl⟩ : syracuseStep 257471 = 386207) B386207
theorem B388583 : Blo 111784 388583 := bstep (se 1 (by rfl) ⟨291437, by rfl⟩ : syracuseStep 388583 = 582875) B582875
theorem B191983 : Blo 111784 191983 := bstep (se 1 (by rfl) ⟨143987, by rfl⟩ : syracuseStep 191983 = 287975) B287975
theorem B618113 : Blo 111784 618113 := bstep (se 2 (by rfl) ⟨231792, by rfl⟩ : syracuseStep 618113 = 463585) B463585
theorem B126751 : Blo 111784 126751 := bstep (se 1 (by rfl) ⟨95063, by rfl⟩ : syracuseStep 126751 = 190127) B190127
theorem B127003 : Blo 111784 127003 := bstep (se 1 (by rfl) ⟨95252, by rfl⟩ : syracuseStep 127003 = 190505) B190505
theorem B192719 : Blo 111784 192719 := bstep (se 1 (by rfl) ⟨144539, by rfl⟩ : syracuseStep 192719 = 289079) B289079
theorem B160255 : Blo 111784 160255 := bstep (se 1 (by rfl) ⟨120191, by rfl⟩ : syracuseStep 160255 = 240383) B240383
theorem B1241851 : Blo 111784 1241851 := bstep (se 1 (by rfl) ⟨931388, by rfl⟩ : syracuseStep 1241851 = 1862777) B1862777
theorem B2388797 : Blo 111784 2388797 := bstep (se 3 (by rfl) ⟨447899, by rfl⟩ : syracuseStep 2388797 = 895799) B895799
theorem B4945049 : Blo 111784 4945049 := bstep (se 2 (by rfl) ⟨1854393, by rfl⟩ : syracuseStep 4945049 = 3708787) B3708787
theorem B259307 : Blo 111784 259307 := bstep (se 1 (by rfl) ⟨194480, by rfl⟩ : syracuseStep 259307 = 388961) B388961
theorem B259559 : Blo 111784 259559 := bstep (se 1 (by rfl) ⟨194669, by rfl⟩ : syracuseStep 259559 = 389339) B389339
theorem B259631 : Blo 111784 259631 := bstep (se 1 (by rfl) ⟨194723, by rfl⟩ : syracuseStep 259631 = 389447) B389447
theorem B2160209 : Blo 111784 2160209 := bstep (se 2 (by rfl) ⟨810078, by rfl⟩ : syracuseStep 2160209 = 1620157) B1620157
theorem B260135 : Blo 111784 260135 := bstep (se 1 (by rfl) ⟨195101, by rfl⟩ : syracuseStep 260135 = 390203) B390203
theorem B129307 : Blo 111784 129307 := bstep (se 1 (by rfl) ⟨96980, by rfl⟩ : syracuseStep 129307 = 193961) B193961
theorem B129343 : Blo 111784 129343 := bstep (se 1 (by rfl) ⟨97007, by rfl⟩ : syracuseStep 129343 = 194015) B194015
theorem B194953 : Blo 111784 194953 := bstep (se 2 (by rfl) ⟨73107, by rfl⟩ : syracuseStep 194953 = 146215) B146215
theorem B129775 : Blo 111784 129775 := bstep (se 1 (by rfl) ⟨97331, by rfl⟩ : syracuseStep 129775 = 194663) B194663
theorem B523361 : Blo 111784 523361 := bstep (se 2 (by rfl) ⟨196260, by rfl⟩ : syracuseStep 523361 = 392521) B392521
theorem B326855 : Blo 111784 326855 := bstep (se 1 (by rfl) ⟨245141, by rfl⟩ : syracuseStep 326855 = 490283) B490283
theorem B164047 : Blo 111784 164047 := bstep (se 1 (by rfl) ⟨123035, by rfl⟩ : syracuseStep 164047 = 246071) B246071
theorem B2917093 : Blo 111784 2917093 := bstep (se 4 (by rfl) ⟨273477, by rfl⟩ : syracuseStep 2917093 = 546955) B546955
theorem B361207 : Blo 111784 361207 := bstep (se 1 (by rfl) ⟨270905, by rfl⟩ : syracuseStep 361207 = 541811) B541811
theorem B1541387 : Blo 111784 1541387 := bstep (se 1 (by rfl) ⟨1156040, by rfl⟩ : syracuseStep 1541387 = 2312081) B2312081
theorem B264073 : Blo 111784 264073 := bstep (se 2 (by rfl) ⟨99027, by rfl⟩ : syracuseStep 264073 = 198055) B198055
theorem B363163 : Blo 111784 363163 := bstep (se 1 (by rfl) ⟨272372, by rfl⟩ : syracuseStep 363163 = 544745) B544745
theorem B2493899 : Blo 111784 2493899 := bstep (se 1 (by rfl) ⟨1870424, by rfl⟩ : syracuseStep 2493899 = 3740849) B3740849
theorem B659177 : Blo 111784 659177 := bstep (se 2 (by rfl) ⟨247191, by rfl⟩ : syracuseStep 659177 = 494383) B494383
theorem B1642301 : Blo 111784 1642301 := bstep (se 3 (by rfl) ⟨307931, by rfl⟩ : syracuseStep 1642301 = 615863) B615863
theorem B167771 : Blo 111784 167771 := bstep (se 1 (by rfl) ⟨125828, by rfl⟩ : syracuseStep 167771 = 251657) B251657
theorem B430019 : Blo 111784 430019 := bstep (se 1 (by rfl) ⟨322514, by rfl⟩ : syracuseStep 430019 = 645029) B645029
theorem B6295643 : Blo 111784 6295643 := bstep (se 1 (by rfl) ⟨4721732, by rfl⟩ : syracuseStep 6295643 = 9443465) B9443465
theorem B168095 : Blo 111784 168095 := bstep (se 1 (by rfl) ⟨126071, by rfl⟩ : syracuseStep 168095 = 252143) B252143
theorem B12357953 : Blo 111784 12357953 := bstep (se 2 (by rfl) ⟨4634232, by rfl⟩ : syracuseStep 12357953 = 9268465) B9268465
theorem B169001 : Blo 111784 169001 := bstep (se 2 (by rfl) ⟨63375, by rfl⟩ : syracuseStep 169001 = 126751) B126751
theorem B955583 : Blo 111784 955583 := bstep (se 1 (by rfl) ⟨716687, by rfl⟩ : syracuseStep 955583 = 1433375) B1433375
theorem B169337 : Blo 111784 169337 := bstep (se 2 (by rfl) ⟨63501, by rfl⟩ : syracuseStep 169337 = 127003) B127003
theorem B169499 : Blo 111784 169499 := bstep (se 1 (by rfl) ⟨127124, by rfl⟩ : syracuseStep 169499 = 254249) B254249
theorem B170207 : Blo 111784 170207 := bstep (se 1 (by rfl) ⟨127655, by rfl⟩ : syracuseStep 170207 = 255311) B255311
theorem B858761 : Blo 111784 858761 := bstep (se 2 (by rfl) ⟨322035, by rfl⟩ : syracuseStep 858761 = 644071) B644071
theorem B170687 : Blo 111784 170687 := bstep (se 1 (by rfl) ⟨128015, by rfl⟩ : syracuseStep 170687 = 256031) B256031
theorem B170855 : Blo 111784 170855 := bstep (se 1 (by rfl) ⟨128141, by rfl⟩ : syracuseStep 170855 = 256283) B256283
theorem B760769 : Blo 111784 760769 := bstep (se 2 (by rfl) ⟨285288, by rfl⟩ : syracuseStep 760769 = 570577) B570577
theorem B433147 : Blo 111784 433147 := bstep (se 1 (by rfl) ⟨324860, by rfl⟩ : syracuseStep 433147 = 649721) B649721
theorem B498791 : Blo 111784 498791 := bstep (se 1 (by rfl) ⟨374093, by rfl⟩ : syracuseStep 498791 = 748187) B748187
theorem B171167 : Blo 111784 171167 := bstep (se 1 (by rfl) ⟨128375, by rfl⟩ : syracuseStep 171167 = 256751) B256751
theorem B171239 : Blo 111784 171239 := bstep (se 1 (by rfl) ⟨128429, by rfl⟩ : syracuseStep 171239 = 256859) B256859
theorem B3022055 : Blo 111784 3022055 := bstep (se 1 (by rfl) ⟨2266541, by rfl⟩ : syracuseStep 3022055 = 4533083) B4533083
theorem B3218665 : Blo 111784 3218665 := bstep (se 2 (by rfl) ⟨1206999, by rfl⟩ : syracuseStep 3218665 = 2413999) B2413999
theorem B171575 : Blo 111784 171575 := bstep (se 1 (by rfl) ⟨128681, by rfl⟩ : syracuseStep 171575 = 257363) B257363
theorem B171647 : Blo 111784 171647 := bstep (se 1 (by rfl) ⟨128735, by rfl⟩ : syracuseStep 171647 = 257471) B257471
theorem B172409 : Blo 111784 172409 := bstep (se 2 (by rfl) ⟨64653, by rfl⟩ : syracuseStep 172409 = 129307) B129307
theorem B172457 : Blo 111784 172457 := bstep (se 2 (by rfl) ⟨64671, by rfl⟩ : syracuseStep 172457 = 129343) B129343
theorem B172871 : Blo 111784 172871 := bstep (se 1 (by rfl) ⟨129653, by rfl⟩ : syracuseStep 172871 = 259307) B259307
theorem B173033 : Blo 111784 173033 := bstep (se 2 (by rfl) ⟨64887, by rfl⟩ : syracuseStep 173033 = 129775) B129775
theorem B173039 : Blo 111784 173039 := bstep (se 1 (by rfl) ⟨129779, by rfl⟩ : syracuseStep 173039 = 259559) B259559
theorem B173087 : Blo 111784 173087 := bstep (se 1 (by rfl) ⟨129815, by rfl⟩ : syracuseStep 173087 = 259631) B259631
theorem B173423 : Blo 111784 173423 := bstep (se 1 (by rfl) ⟨130067, by rfl⟩ : syracuseStep 173423 = 260135) B260135
theorem B730579 : Blo 111784 730579 := bstep (se 1 (by rfl) ⟨547934, by rfl⟩ : syracuseStep 730579 = 1095869) B1095869
theorem B2926205 : Blo 111784 2926205 := bstep (se 3 (by rfl) ⟨548663, by rfl⟩ : syracuseStep 2926205 = 1097327) B1097327
theorem B206903 : Blo 111784 206903 := bstep (se 1 (by rfl) ⟨155177, by rfl⟩ : syracuseStep 206903 = 310355) B310355
theorem B272479 : Blo 111784 272479 := bstep (se 1 (by rfl) ⟨204359, by rfl⟩ : syracuseStep 272479 = 408719) B408719
theorem B1386953 : Blo 111784 1386953 := bstep (se 2 (by rfl) ⟨520107, by rfl⟩ : syracuseStep 1386953 = 1040215) B1040215
theorem B437339 : Blo 111784 437339 := bstep (se 1 (by rfl) ⟨328004, by rfl⟩ : syracuseStep 437339 = 656009) B656009
theorem B438479 : Blo 111784 438479 := bstep (se 1 (by rfl) ⟨328859, by rfl⟩ : syracuseStep 438479 = 657719) B657719
theorem B112095 : Blo 111784 112095 := bstep (se 1 (by rfl) ⟨84071, by rfl⟩ : syracuseStep 112095 = 168143) B168143
theorem B112255 : Blo 111784 112255 := bstep (se 1 (by rfl) ⟨84191, by rfl⟩ : syracuseStep 112255 = 168383) B168383
theorem B113119 : Blo 111784 113119 := bstep (se 1 (by rfl) ⟨84839, by rfl⟩ : syracuseStep 113119 = 169679) B169679
theorem B113135 : Blo 111784 113135 := bstep (se 1 (by rfl) ⟨84851, by rfl⟩ : syracuseStep 113135 = 169703) B169703
theorem B113279 : Blo 111784 113279 := bstep (se 1 (by rfl) ⟨84959, by rfl⟩ : syracuseStep 113279 = 169919) B169919
theorem B37665881 : Blo 111784 37665881 := bstep (se 2 (by rfl) ⟨14124705, by rfl⟩ : syracuseStep 37665881 = 28249411) B28249411
theorem B212071 : Blo 111784 212071 := bstep (se 1 (by rfl) ⟨159053, by rfl⟩ : syracuseStep 212071 = 318107) B318107
theorem B114075 : Blo 111784 114075 := bstep (se 1 (by rfl) ⟨85556, by rfl⟩ : syracuseStep 114075 = 171113) B171113
theorem B114279 : Blo 111784 114279 := bstep (se 1 (by rfl) ⟨85709, by rfl⟩ : syracuseStep 114279 = 171419) B171419
theorem B114715 : Blo 111784 114715 := bstep (se 1 (by rfl) ⟨86036, by rfl⟩ : syracuseStep 114715 = 172073) B172073
theorem B4112441 : Blo 111784 4112441 := bstep (se 2 (by rfl) ⟨1542165, by rfl⟩ : syracuseStep 4112441 = 3084331) B3084331
theorem B115291 : Blo 111784 115291 := bstep (se 1 (by rfl) ⟨86468, by rfl⟩ : syracuseStep 115291 = 172937) B172937
theorem B213673 : Blo 111784 213673 := bstep (se 2 (by rfl) ⟨80127, by rfl⟩ : syracuseStep 213673 = 160255) B160255
theorem B344819 : Blo 111784 344819 := bstep (se 1 (by rfl) ⟨258614, by rfl⟩ : syracuseStep 344819 = 517229) B517229
theorem B115647 : Blo 111784 115647 := bstep (se 1 (by rfl) ⟨86735, by rfl⟩ : syracuseStep 115647 = 173471) B173471
theorem B1655801 : Blo 111784 1655801 := bstep (se 2 (by rfl) ⟨620925, by rfl⟩ : syracuseStep 1655801 = 1241851) B1241851
theorem B247097 : Blo 111784 247097 := bstep (se 2 (by rfl) ⟨92661, by rfl⟩ : syracuseStep 247097 = 185323) B185323
theorem B378593 : Blo 111784 378593 := bstep (se 2 (by rfl) ⟨141972, by rfl⟩ : syracuseStep 378593 = 283945) B283945
theorem B1230689 : Blo 111784 1230689 := bstep (se 2 (by rfl) ⟨461508, by rfl⟩ : syracuseStep 1230689 = 923017) B923017
theorem B2934767 : Blo 111784 2934767 := bstep (se 1 (by rfl) ⟨2201075, by rfl⟩ : syracuseStep 2934767 = 4402151) B4402151
theorem B3262457 : Blo 111784 3262457 := bstep (se 2 (by rfl) ⟨1223421, by rfl⟩ : syracuseStep 3262457 = 2446843) B2446843
theorem B1231037 : Blo 111784 1231037 := bstep (se 3 (by rfl) ⟨230819, by rfl⟩ : syracuseStep 1231037 = 461639) B461639
theorem B412075 : Blo 111784 412075 := bstep (se 1 (by rfl) ⟨309056, by rfl⟩ : syracuseStep 412075 = 618113) B618113
theorem B969731 : Blo 111784 969731 := bstep (se 1 (by rfl) ⟨727298, by rfl⟩ : syracuseStep 969731 = 1454597) B1454597
theorem B1592531 : Blo 111784 1592531 := bstep (se 1 (by rfl) ⟨1194398, by rfl⟩ : syracuseStep 1592531 = 2388797) B2388797
theorem B740573 : Blo 111784 740573 := bstep (se 3 (by rfl) ⟨138857, by rfl⟩ : syracuseStep 740573 = 277715) B277715
theorem B3296699 : Blo 111784 3296699 := bstep (se 1 (by rfl) ⟨2472524, by rfl⟩ : syracuseStep 3296699 = 4945049) B4945049
theorem B380537 : Blo 111784 380537 := bstep (se 2 (by rfl) ⟨142701, by rfl⟩ : syracuseStep 380537 = 285403) B285403
theorem B1299077 : Blo 111784 1299077 := bstep (se 4 (by rfl) ⟨121788, by rfl⟩ : syracuseStep 1299077 = 243577) B243577
theorem B348907 : Blo 111784 348907 := bstep (se 1 (by rfl) ⟨261680, by rfl⟩ : syracuseStep 348907 = 523361) B523361
theorem B217903 : Blo 111784 217903 := bstep (se 1 (by rfl) ⟨163427, by rfl⟩ : syracuseStep 217903 = 326855) B326855
theorem B1103327 : Blo 111784 1103327 := bstep (se 1 (by rfl) ⟨827495, by rfl⟩ : syracuseStep 1103327 = 1654991) B1654991
theorem B294508331 : Blo 111784 294508331 := bstep (se 1 (by rfl) ⟨220881248, by rfl⟩ : syracuseStep 294508331 = 441762497) B441762497
theorem B252071 : Blo 111784 252071 := bstep (se 1 (by rfl) ⟨189053, by rfl⟩ : syracuseStep 252071 = 378107) B378107
theorem B383993 : Blo 111784 383993 := bstep (se 2 (by rfl) ⟨143997, by rfl⟩ : syracuseStep 383993 = 287995) B287995
theorem B285727 : Blo 111784 285727 := bstep (se 1 (by rfl) ⟨214295, by rfl⟩ : syracuseStep 285727 = 428591) B428591
theorem B548819 : Blo 111784 548819 := bstep (se 1 (by rfl) ⟨411614, by rfl⟩ : syracuseStep 548819 = 823229) B823229
theorem B12509623 : Blo 111784 12509623 := bstep (se 1 (by rfl) ⟨9382217, by rfl⟩ : syracuseStep 12509623 = 18764435) B18764435
theorem B188959 : Blo 111784 188959 := bstep (se 1 (by rfl) ⟨141719, by rfl⟩ : syracuseStep 188959 = 283439) B283439
theorem B483995 : Blo 111784 483995 := bstep (se 1 (by rfl) ⟨362996, by rfl⟩ : syracuseStep 483995 = 725993) B725993
theorem B385775 : Blo 111784 385775 := bstep (se 1 (by rfl) ⟨289331, by rfl⟩ : syracuseStep 385775 = 578663) B578663
theorem B189391 : Blo 111784 189391 := bstep (se 1 (by rfl) ⟨142043, by rfl⟩ : syracuseStep 189391 = 284087) B284087
theorem B255239 : Blo 111784 255239 := bstep (se 1 (by rfl) ⟨191429, by rfl⟩ : syracuseStep 255239 = 382859) B382859
theorem B320851 : Blo 111784 320851 := bstep (se 1 (by rfl) ⟨240638, by rfl⟩ : syracuseStep 320851 = 481277) B481277
theorem B288481 : Blo 111784 288481 := bstep (se 2 (by rfl) ⟨108180, by rfl⟩ : syracuseStep 288481 = 216361) B216361
theorem B648971 : Blo 111784 648971 := bstep (se 1 (by rfl) ⟨486728, by rfl⟩ : syracuseStep 648971 = 973457) B973457
theorem B255977 : Blo 111784 255977 := bstep (se 2 (by rfl) ⟨95991, by rfl⟩ : syracuseStep 255977 = 191983) B191983
theorem B878687 : Blo 111784 878687 := bstep (se 1 (by rfl) ⟨659015, by rfl⟩ : syracuseStep 878687 = 1318031) B1318031
theorem B387179 : Blo 111784 387179 := bstep (se 1 (by rfl) ⟨290384, by rfl⟩ : syracuseStep 387179 = 580769) B580769
theorem B485651 : Blo 111784 485651 := bstep (se 1 (by rfl) ⟨364238, by rfl⟩ : syracuseStep 485651 = 728477) B728477
theorem B387827 : Blo 111784 387827 := bstep (se 1 (by rfl) ⟨290870, by rfl⟩ : syracuseStep 387827 = 581741) B581741
theorem B191227 : Blo 111784 191227 := bstep (se 1 (by rfl) ⟨143420, by rfl⟩ : syracuseStep 191227 = 286841) B286841
theorem B584495 : Blo 111784 584495 := bstep (se 1 (by rfl) ⟨438371, by rfl⟩ : syracuseStep 584495 = 876743) B876743
theorem B125887 : Blo 111784 125887 := bstep (se 1 (by rfl) ⟨94415, by rfl⟩ : syracuseStep 125887 = 188831) B188831
theorem B191423 : Blo 111784 191423 := bstep (se 1 (by rfl) ⟨143567, by rfl⟩ : syracuseStep 191423 = 287135) B287135
theorem B257327 : Blo 111784 257327 := bstep (se 1 (by rfl) ⟨192995, by rfl⟩ : syracuseStep 257327 = 385991) B385991
theorem B486881 : Blo 111784 486881 := bstep (se 2 (by rfl) ⟨182580, by rfl⟩ : syracuseStep 486881 = 365161) B365161
theorem B1109477 : Blo 111784 1109477 := bstep (se 4 (by rfl) ⟨104013, by rfl⟩ : syracuseStep 1109477 = 208027) B208027
theorem B683677 : Blo 111784 683677 := bstep (se 3 (by rfl) ⟨128189, by rfl⟩ : syracuseStep 683677 = 256379) B256379
theorem B257903 : Blo 111784 257903 := bstep (se 1 (by rfl) ⟨193427, by rfl⟩ : syracuseStep 257903 = 386855) B386855
theorem B290911 : Blo 111784 290911 := bstep (se 1 (by rfl) ⟨218183, by rfl⟩ : syracuseStep 290911 = 436367) B436367
theorem B258767 : Blo 111784 258767 := bstep (se 1 (by rfl) ⟨194075, by rfl⟩ : syracuseStep 258767 = 388151) B388151
theorem B127867 : Blo 111784 127867 := bstep (se 1 (by rfl) ⟨95900, by rfl⟩ : syracuseStep 127867 = 191801) B191801
theorem B259055 : Blo 111784 259055 := bstep (se 1 (by rfl) ⟨194291, by rfl⟩ : syracuseStep 259055 = 388583) B388583
theorem B553979 : Blo 111784 553979 := bstep (se 1 (by rfl) ⟨415484, by rfl⟩ : syracuseStep 553979 = 830969) B830969
theorem B128479 : Blo 111784 128479 := bstep (se 1 (by rfl) ⟨96359, by rfl⟩ : syracuseStep 128479 = 192719) B192719
theorem B259937 : Blo 111784 259937 := bstep (se 2 (by rfl) ⟨97476, by rfl⟩ : syracuseStep 259937 = 194953) B194953
theorem B489341 : Blo 111784 489341 := bstep (se 3 (by rfl) ⟨91751, by rfl⟩ : syracuseStep 489341 = 183503) B183503
theorem B1440139 : Blo 111784 1440139 := bstep (se 1 (by rfl) ⟨1080104, by rfl⟩ : syracuseStep 1440139 = 2160209) B2160209
theorem B326045 : Blo 111784 326045 := bstep (se 3 (by rfl) ⟨61133, by rfl⟩ : syracuseStep 326045 = 122267) B122267
theorem B818383 : Blo 111784 818383 := bstep (se 1 (by rfl) ⟨613787, by rfl⟩ : syracuseStep 818383 = 1227575) B1227575
theorem B229879 : Blo 111784 229879 := bstep (se 1 (by rfl) ⟨172409, by rfl⟩ : syracuseStep 229879 = 344819) B344819
theorem B820459 : Blo 111784 820459 := bstep (se 1 (by rfl) ⟨615344, by rfl⟩ : syracuseStep 820459 = 1230689) B1230689
theorem B820691 : Blo 111784 820691 := bstep (se 1 (by rfl) ⟨615518, by rfl⟩ : syracuseStep 820691 = 1231037) B1231037
theorem B427801 : Blo 111784 427801 := bstep (se 2 (by rfl) ⟨160425, by rfl⟩ : syracuseStep 427801 = 320851) B320851
theorem B493715 : Blo 111784 493715 := bstep (se 1 (by rfl) ⟨370286, by rfl⟩ : syracuseStep 493715 = 740573) B740573
theorem B66717989 : Blo 111784 66717989 := bstep (se 4 (by rfl) ⟨6254811, by rfl⟩ : syracuseStep 66717989 = 12509623) B12509623
theorem B2197799 : Blo 111784 2197799 := bstep (se 1 (by rfl) ⟨1648349, by rfl⟩ : syracuseStep 2197799 = 3296699) B3296699
theorem B4197095 : Blo 111784 4197095 := bstep (se 1 (by rfl) ⟨3147821, by rfl⟩ : syracuseStep 4197095 = 6295643) B6295643
theorem B363305 : Blo 111784 363305 := bstep (se 2 (by rfl) ⟨136239, by rfl⟩ : syracuseStep 363305 = 272479) B272479
theorem B658925 : Blo 111784 658925 := bstep (se 3 (by rfl) ⟨123548, by rfl⟩ : syracuseStep 658925 = 247097) B247097
theorem B167849 : Blo 111784 167849 := bstep (se 2 (by rfl) ⟨62943, by rfl⟩ : syracuseStep 167849 = 125887) B125887
theorem B168047 : Blo 111784 168047 := bstep (se 1 (by rfl) ⟨126035, by rfl⟩ : syracuseStep 168047 = 252071) B252071
theorem B332527 : Blo 111784 332527 := bstep (se 1 (by rfl) ⟨249395, by rfl⟩ : syracuseStep 332527 = 498791) B498791
theorem B365879 : Blo 111784 365879 := bstep (se 1 (by rfl) ⟨274409, by rfl⟩ : syracuseStep 365879 = 548819) B548819
theorem B170159 : Blo 111784 170159 := bstep (se 1 (by rfl) ⟨127619, by rfl⟩ : syracuseStep 170159 = 255239) B255239
theorem B465209 : Blo 111784 465209 := bstep (se 2 (by rfl) ⟨174453, by rfl⟩ : syracuseStep 465209 = 348907) B348907
theorem B170489 : Blo 111784 170489 := bstep (se 2 (by rfl) ⟨63933, by rfl⟩ : syracuseStep 170489 = 127867) B127867
theorem B432647 : Blo 111784 432647 := bstep (se 1 (by rfl) ⟨324485, by rfl⟩ : syracuseStep 432647 = 648971) B648971
theorem B170651 : Blo 111784 170651 := bstep (se 1 (by rfl) ⟨127988, by rfl⟩ : syracuseStep 170651 = 255977) B255977
theorem B137935 : Blo 111784 137935 := bstep (se 1 (by rfl) ⟨103451, by rfl⟩ : syracuseStep 137935 = 206903) B206903
theorem B924635 : Blo 111784 924635 := bstep (se 1 (by rfl) ⟨693476, by rfl⟩ : syracuseStep 924635 = 1386953) B1386953
theorem B171305 : Blo 111784 171305 := bstep (se 2 (by rfl) ⟨64239, by rfl⟩ : syracuseStep 171305 = 128479) B128479
theorem B171551 : Blo 111784 171551 := bstep (se 1 (by rfl) ⟨128663, by rfl⟩ : syracuseStep 171551 = 257327) B257327
theorem B171935 : Blo 111784 171935 := bstep (se 1 (by rfl) ⟨128951, by rfl⟩ : syracuseStep 171935 = 257903) B257903
theorem B172511 : Blo 111784 172511 := bstep (se 1 (by rfl) ⟨129383, by rfl⟩ : syracuseStep 172511 = 258767) B258767
theorem B172703 : Blo 111784 172703 := bstep (se 1 (by rfl) ⟨129527, by rfl⟩ : syracuseStep 172703 = 259055) B259055
theorem B369319 : Blo 111784 369319 := bstep (se 1 (by rfl) ⟨276989, by rfl⟩ : syracuseStep 369319 = 553979) B553979
theorem B173291 : Blo 111784 173291 := bstep (se 1 (by rfl) ⟨129968, by rfl⟩ : syracuseStep 173291 = 259937) B259937
theorem B1091177 : Blo 111784 1091177 := bstep (se 2 (by rfl) ⟨409191, by rfl⟩ : syracuseStep 1091177 = 818383) B818383
theorem B25110587 : Blo 111784 25110587 := bstep (se 1 (by rfl) ⟨18832940, by rfl⟩ : syracuseStep 25110587 = 37665881) B37665881
theorem B2174971 : Blo 111784 2174971 := bstep (se 1 (by rfl) ⟨1631228, by rfl⟩ : syracuseStep 2174971 = 3262457) B3262457
theorem B1061687 : Blo 111784 1061687 := bstep (se 1 (by rfl) ⟨796265, by rfl⟩ : syracuseStep 1061687 = 1592531) B1592531
theorem B439451 : Blo 111784 439451 := bstep (se 1 (by rfl) ⟨329588, by rfl⟩ : syracuseStep 439451 = 659177) B659177
theorem B1094867 : Blo 111784 1094867 := bstep (se 1 (by rfl) ⟨821150, by rfl⟩ : syracuseStep 1094867 = 1642301) B1642301
theorem B111847 : Blo 111784 111847 := bstep (se 1 (by rfl) ⟨83885, by rfl⟩ : syracuseStep 111847 = 167771) B167771
theorem B112063 : Blo 111784 112063 := bstep (se 1 (by rfl) ⟨84047, by rfl⟩ : syracuseStep 112063 = 168095) B168095
theorem B8238635 : Blo 111784 8238635 := bstep (se 1 (by rfl) ⟨6178976, by rfl⟩ : syracuseStep 8238635 = 12357953) B12357953
theorem B866051 : Blo 111784 866051 := bstep (se 1 (by rfl) ⟨649538, by rfl⟩ : syracuseStep 866051 = 1299077) B1299077
theorem B112667 : Blo 111784 112667 := bstep (se 1 (by rfl) ⟨84500, by rfl⟩ : syracuseStep 112667 = 169001) B169001
theorem B4110365 : Blo 111784 4110365 := bstep (se 3 (by rfl) ⟨770693, by rfl⟩ : syracuseStep 4110365 = 1541387) B1541387
theorem B637055 : Blo 111784 637055 := bstep (se 1 (by rfl) ⟨477791, by rfl⟩ : syracuseStep 637055 = 955583) B955583
theorem B112891 : Blo 111784 112891 := bstep (se 1 (by rfl) ⟨84668, by rfl⟩ : syracuseStep 112891 = 169337) B169337
theorem B735551 : Blo 111784 735551 := bstep (se 1 (by rfl) ⟨551663, by rfl⟩ : syracuseStep 735551 = 1103327) B1103327
theorem B112999 : Blo 111784 112999 := bstep (se 1 (by rfl) ⟨84749, by rfl⟩ : syracuseStep 112999 = 169499) B169499
theorem B113471 : Blo 111784 113471 := bstep (se 1 (by rfl) ⟨85103, by rfl⟩ : syracuseStep 113471 = 170207) B170207
theorem B572507 : Blo 111784 572507 := bstep (se 1 (by rfl) ⟨429380, by rfl⟩ : syracuseStep 572507 = 858761) B858761
theorem B113791 : Blo 111784 113791 := bstep (se 1 (by rfl) ⟨85343, by rfl⟩ : syracuseStep 113791 = 170687) B170687
theorem B113903 : Blo 111784 113903 := bstep (se 1 (by rfl) ⟨85427, by rfl⟩ : syracuseStep 113903 = 170855) B170855
theorem B507179 : Blo 111784 507179 := bstep (se 1 (by rfl) ⟨380384, by rfl⟩ : syracuseStep 507179 = 760769) B760769
theorem B114111 : Blo 111784 114111 := bstep (se 1 (by rfl) ⟨85583, by rfl⟩ : syracuseStep 114111 = 171167) B171167
theorem B114159 : Blo 111784 114159 := bstep (se 1 (by rfl) ⟨85619, by rfl⟩ : syracuseStep 114159 = 171239) B171239
theorem B2014703 : Blo 111784 2014703 := bstep (se 1 (by rfl) ⟨1511027, by rfl⟩ : syracuseStep 2014703 = 3022055) B3022055
theorem B114383 : Blo 111784 114383 := bstep (se 1 (by rfl) ⟨85787, by rfl⟩ : syracuseStep 114383 = 171575) B171575
theorem B114431 : Blo 111784 114431 := bstep (se 1 (by rfl) ⟨85823, by rfl⟩ : syracuseStep 114431 = 171647) B171647
theorem B114939 : Blo 111784 114939 := bstep (se 1 (by rfl) ⟨86204, by rfl⟩ : syracuseStep 114939 = 172409) B172409
theorem B114971 : Blo 111784 114971 := bstep (se 1 (by rfl) ⟨86228, by rfl⟩ : syracuseStep 114971 = 172457) B172457
theorem B115247 : Blo 111784 115247 := bstep (se 1 (by rfl) ⟨86435, by rfl⟩ : syracuseStep 115247 = 172871) B172871
theorem B115355 : Blo 111784 115355 := bstep (se 1 (by rfl) ⟨86516, by rfl⟩ : syracuseStep 115355 = 173033) B173033
theorem B115359 : Blo 111784 115359 := bstep (se 1 (by rfl) ⟨86519, by rfl⟩ : syracuseStep 115359 = 173039) B173039
theorem B115391 : Blo 111784 115391 := bstep (se 1 (by rfl) ⟨86543, by rfl⟩ : syracuseStep 115391 = 173087) B173087
theorem B115615 : Blo 111784 115615 := bstep (se 1 (by rfl) ⟨86711, by rfl⟩ : syracuseStep 115615 = 173423) B173423
theorem B869453 : Blo 111784 869453 := bstep (se 3 (by rfl) ⟨163022, by rfl⟩ : syracuseStep 869453 = 326045) B326045
theorem B1950803 : Blo 111784 1950803 := bstep (se 1 (by rfl) ⟨1463102, by rfl⟩ : syracuseStep 1950803 = 2926205) B2926205
theorem B739651 : Blo 111784 739651 := bstep (se 1 (by rfl) ⟨554738, by rfl⟩ : syracuseStep 739651 = 1109477) B1109477
theorem B1920185 : Blo 111784 1920185 := bstep (se 2 (by rfl) ⟨720069, by rfl⟩ : syracuseStep 1920185 = 1440139) B1440139
theorem B577529 : Blo 111784 577529 := bstep (se 2 (by rfl) ⟨216573, by rfl⟩ : syracuseStep 577529 = 433147) B433147
theorem B380969 : Blo 111784 380969 := bstep (se 2 (by rfl) ⟨142863, by rfl⟩ : syracuseStep 380969 = 285727) B285727
theorem B282761 : Blo 111784 282761 := bstep (se 2 (by rfl) ⟨106035, by rfl⟩ : syracuseStep 282761 = 212071) B212071
theorem B2741627 : Blo 111784 2741627 := bstep (se 1 (by rfl) ⟨2056220, by rfl⟩ : syracuseStep 2741627 = 4112441) B4112441
theorem B218729 : Blo 111784 218729 := bstep (se 2 (by rfl) ⟨82023, by rfl⟩ : syracuseStep 218729 = 164047) B164047
theorem B1103867 : Blo 111784 1103867 := bstep (se 1 (by rfl) ⟨827900, by rfl⟩ : syracuseStep 1103867 = 1655801) B1655801
theorem B251945 : Blo 111784 251945 := bstep (se 2 (by rfl) ⟨94479, by rfl⟩ : syracuseStep 251945 = 188959) B188959
theorem B284897 : Blo 111784 284897 := bstep (se 2 (by rfl) ⟨106836, by rfl⟩ : syracuseStep 284897 = 213673) B213673
theorem B3889457 : Blo 111784 3889457 := bstep (se 2 (by rfl) ⟨1458546, by rfl⟩ : syracuseStep 3889457 = 2917093) B2917093
theorem B481609 : Blo 111784 481609 := bstep (se 2 (by rfl) ⟨180603, by rfl⟩ : syracuseStep 481609 = 361207) B361207
theorem B252395 : Blo 111784 252395 := bstep (se 1 (by rfl) ⟨189296, by rfl⟩ : syracuseStep 252395 = 378593) B378593
theorem B252521 : Blo 111784 252521 := bstep (se 2 (by rfl) ⟨94695, by rfl⟩ : syracuseStep 252521 = 189391) B189391
theorem B1956511 : Blo 111784 1956511 := bstep (se 1 (by rfl) ⟨1467383, by rfl⟩ : syracuseStep 1956511 = 2934767) B2934767
theorem B974105 : Blo 111784 974105 := bstep (se 2 (by rfl) ⟨365289, by rfl⟩ : syracuseStep 974105 = 730579) B730579
theorem B646487 : Blo 111784 646487 := bstep (se 1 (by rfl) ⟨484865, by rfl⟩ : syracuseStep 646487 = 969731) B969731
theorem B384641 : Blo 111784 384641 := bstep (se 2 (by rfl) ⟨144240, by rfl⟩ : syracuseStep 384641 = 288481) B288481
theorem B1662599 : Blo 111784 1662599 := bstep (se 1 (by rfl) ⟨1246949, by rfl⟩ : syracuseStep 1662599 = 2493899) B2493899
theorem B253691 : Blo 111784 253691 := bstep (se 1 (by rfl) ⟨190268, by rfl⟩ : syracuseStep 253691 = 380537) B380537
theorem B352097 : Blo 111784 352097 := bstep (se 2 (by rfl) ⟨132036, by rfl⟩ : syracuseStep 352097 = 264073) B264073
theorem B286679 : Blo 111784 286679 := bstep (se 1 (by rfl) ⟨215009, by rfl⟩ : syracuseStep 286679 = 430019) B430019
theorem B549433 : Blo 111784 549433 := bstep (se 2 (by rfl) ⟨206037, by rfl⟩ : syracuseStep 549433 = 412075) B412075
theorem B484217 : Blo 111784 484217 := bstep (se 2 (by rfl) ⟨181581, by rfl⟩ : syracuseStep 484217 = 363163) B363163
theorem B254969 : Blo 111784 254969 := bstep (se 2 (by rfl) ⟨95613, by rfl⟩ : syracuseStep 254969 = 191227) B191227
theorem B196338887 : Blo 111784 196338887 := bstep (se 1 (by rfl) ⟨147254165, by rfl⟩ : syracuseStep 196338887 = 294508331) B294508331
theorem B255995 : Blo 111784 255995 := bstep (se 1 (by rfl) ⟨191996, by rfl⟩ : syracuseStep 255995 = 383993) B383993
theorem B911569 : Blo 111784 911569 := bstep (se 2 (by rfl) ⟨341838, by rfl⟩ : syracuseStep 911569 = 683677) B683677
theorem B1304909 : Blo 111784 1304909 := bstep (se 3 (by rfl) ⟨244670, by rfl⟩ : syracuseStep 1304909 = 489341) B489341
theorem B387881 : Blo 111784 387881 := bstep (se 2 (by rfl) ⟨145455, by rfl⟩ : syracuseStep 387881 = 290911) B290911
theorem B322663 : Blo 111784 322663 := bstep (se 1 (by rfl) ⟨241997, by rfl⟩ : syracuseStep 322663 = 483995) B483995
theorem B257183 : Blo 111784 257183 := bstep (se 1 (by rfl) ⟨192887, by rfl⟩ : syracuseStep 257183 = 385775) B385775
theorem B290537 : Blo 111784 290537 := bstep (se 2 (by rfl) ⟨108951, by rfl⟩ : syracuseStep 290537 = 217903) B217903
theorem B585791 : Blo 111784 585791 := bstep (se 1 (by rfl) ⟨439343, by rfl⟩ : syracuseStep 585791 = 878687) B878687
theorem B258119 : Blo 111784 258119 := bstep (se 1 (by rfl) ⟨193589, by rfl⟩ : syracuseStep 258119 = 387179) B387179
theorem B323767 : Blo 111784 323767 := bstep (se 1 (by rfl) ⟨242825, by rfl⟩ : syracuseStep 323767 = 485651) B485651
theorem B258551 : Blo 111784 258551 := bstep (se 1 (by rfl) ⟨193913, by rfl⟩ : syracuseStep 258551 = 387827) B387827
theorem B389663 : Blo 111784 389663 := bstep (se 1 (by rfl) ⟨292247, by rfl⟩ : syracuseStep 389663 = 584495) B584495
theorem B127615 : Blo 111784 127615 := bstep (se 1 (by rfl) ⟨95711, by rfl⟩ : syracuseStep 127615 = 191423) B191423
theorem B291559 : Blo 111784 291559 := bstep (se 1 (by rfl) ⟨218669, by rfl⟩ : syracuseStep 291559 = 437339) B437339
theorem B324587 : Blo 111784 324587 := bstep (se 1 (by rfl) ⟨243440, by rfl⟩ : syracuseStep 324587 = 486881) B486881
theorem B292319 : Blo 111784 292319 := bstep (se 1 (by rfl) ⟨219239, by rfl⟩ : syracuseStep 292319 = 438479) B438479
theorem B4291553 : Blo 111784 4291553 := bstep (se 2 (by rfl) ⟨1609332, by rfl⟩ : syracuseStep 4291553 = 3218665) B3218665
theorem B492425 : Blo 111784 492425 := bstep (se 2 (by rfl) ⟨184659, by rfl⟩ : syracuseStep 492425 = 369319) B369319
theorem B1280123 : Blo 111784 1280123 := bstep (se 1 (by rfl) ⟨960092, by rfl⟩ : syracuseStep 1280123 = 1920185) B1920185
theorem B1215425 : Blo 111784 1215425 := bstep (se 2 (by rfl) ⟨455784, by rfl⟩ : syracuseStep 1215425 = 911569) B911569
theorem B986201 : Blo 111784 986201 := bstep (se 2 (by rfl) ⟨369825, by rfl⟩ : syracuseStep 986201 = 739651) B739651
theorem B7311005 : Blo 111784 7311005 := bstep (se 3 (by rfl) ⟨1370813, by rfl⟩ : syracuseStep 7311005 = 2741627) B2741627
theorem B167963 : Blo 111784 167963 := bstep (se 1 (by rfl) ⟨125972, by rfl⟩ : syracuseStep 167963 = 251945) B251945
theorem B430217 : Blo 111784 430217 := bstep (se 2 (by rfl) ⟨161331, by rfl⟩ : syracuseStep 430217 = 322663) B322663
theorem B2592971 : Blo 111784 2592971 := bstep (se 1 (by rfl) ⟨1944728, by rfl⟩ : syracuseStep 2592971 = 3889457) B3889457
theorem B168263 : Blo 111784 168263 := bstep (se 1 (by rfl) ⟨126197, by rfl⟩ : syracuseStep 168263 = 252395) B252395
theorem B168347 : Blo 111784 168347 := bstep (se 1 (by rfl) ⟨126260, by rfl⟩ : syracuseStep 168347 = 252521) B252521
theorem B430991 : Blo 111784 430991 := bstep (se 1 (by rfl) ⟨323243, by rfl⟩ : syracuseStep 430991 = 646487) B646487
theorem B169127 : Blo 111784 169127 := bstep (se 1 (by rfl) ⟨126845, by rfl⟩ : syracuseStep 169127 = 253691) B253691
theorem B234731 : Blo 111784 234731 := bstep (se 1 (by rfl) ⟨176048, by rfl⟩ : syracuseStep 234731 = 352097) B352097
theorem B431689 : Blo 111784 431689 := bstep (se 2 (by rfl) ⟨161883, by rfl⟩ : syracuseStep 431689 = 323767) B323767
theorem B1316573 : Blo 111784 1316573 := bstep (se 3 (by rfl) ⟨246857, by rfl⟩ : syracuseStep 1316573 = 493715) B493715
theorem B169979 : Blo 111784 169979 := bstep (se 1 (by rfl) ⟨127484, by rfl⟩ : syracuseStep 169979 = 254969) B254969
theorem B170153 : Blo 111784 170153 := bstep (se 2 (by rfl) ⟨63807, by rfl⟩ : syracuseStep 170153 = 127615) B127615
theorem B727451 : Blo 111784 727451 := bstep (se 1 (by rfl) ⟨545588, by rfl⟩ : syracuseStep 727451 = 1091177) B1091177
theorem B170663 : Blo 111784 170663 := bstep (se 1 (by rfl) ⟨127997, by rfl⟩ : syracuseStep 170663 = 255995) B255995
theorem B171455 : Blo 111784 171455 := bstep (se 1 (by rfl) ⟨128591, by rfl⟩ : syracuseStep 171455 = 257183) B257183
theorem B11444141 : Blo 111784 11444141 := bstep (se 3 (by rfl) ⟨2145776, by rfl⟩ : syracuseStep 11444141 = 4291553) B4291553
theorem B172079 : Blo 111784 172079 := bstep (se 1 (by rfl) ⟨129059, by rfl⟩ : syracuseStep 172079 = 258119) B258119
theorem B172367 : Blo 111784 172367 := bstep (se 1 (by rfl) ⟨129275, by rfl⟩ : syracuseStep 172367 = 258551) B258551
theorem B1352477 : Blo 111784 1352477 := bstep (se 3 (by rfl) ⟨253589, by rfl⟩ : syracuseStep 1352477 = 507179) B507179
theorem B729911 : Blo 111784 729911 := bstep (se 1 (by rfl) ⟨547433, by rfl⟩ : syracuseStep 729911 = 1094867) B1094867
theorem B306505 : Blo 111784 306505 := bstep (se 2 (by rfl) ⟨114939, by rfl⟩ : syracuseStep 306505 = 229879) B229879
theorem B732577 : Blo 111784 732577 := bstep (se 2 (by rfl) ⟨274716, by rfl⟩ : syracuseStep 732577 = 549433) B549433
theorem B44478659 : Blo 111784 44478659 := bstep (se 1 (by rfl) ⟨33358994, by rfl⟩ : syracuseStep 44478659 = 66717989) B66717989
theorem B1093945 : Blo 111784 1093945 := bstep (se 2 (by rfl) ⟨410229, by rfl⟩ : syracuseStep 1093945 = 820459) B820459
theorem B2568581 : Blo 111784 2568581 := bstep (se 4 (by rfl) ⟨240804, by rfl⟩ : syracuseStep 2568581 = 481609) B481609
theorem B2798063 : Blo 111784 2798063 := bstep (se 1 (by rfl) ⟨2098547, by rfl⟩ : syracuseStep 2798063 = 4197095) B4197095
theorem B242203 : Blo 111784 242203 := bstep (se 1 (by rfl) ⟨181652, by rfl⟩ : syracuseStep 242203 = 363305) B363305
theorem B439283 : Blo 111784 439283 := bstep (se 1 (by rfl) ⟨329462, by rfl⟩ : syracuseStep 439283 = 658925) B658925
theorem B570401 : Blo 111784 570401 := bstep (se 2 (by rfl) ⟨213900, by rfl⟩ : syracuseStep 570401 = 427801) B427801
theorem B111899 : Blo 111784 111899 := bstep (se 1 (by rfl) ⟨83924, by rfl⟩ : syracuseStep 111899 = 167849) B167849
theorem B865565 : Blo 111784 865565 := bstep (se 3 (by rfl) ⟨162293, by rfl⟩ : syracuseStep 865565 = 324587) B324587
theorem B112031 : Blo 111784 112031 := bstep (se 1 (by rfl) ⟨84023, by rfl⟩ : syracuseStep 112031 = 168047) B168047
theorem B243919 : Blo 111784 243919 := bstep (se 1 (by rfl) ⟨182939, by rfl⟩ : syracuseStep 243919 = 365879) B365879
theorem B145819 : Blo 111784 145819 := bstep (se 1 (by rfl) ⟨109364, by rfl⟩ : syracuseStep 145819 = 218729) B218729
theorem B735911 : Blo 111784 735911 := bstep (se 1 (by rfl) ⟨551933, by rfl⟩ : syracuseStep 735911 = 1103867) B1103867
theorem B113439 : Blo 111784 113439 := bstep (se 1 (by rfl) ⟨85079, by rfl⟩ : syracuseStep 113439 = 170159) B170159
theorem B310139 : Blo 111784 310139 := bstep (se 1 (by rfl) ⟨232604, by rfl⟩ : syracuseStep 310139 = 465209) B465209
theorem B113659 : Blo 111784 113659 := bstep (se 1 (by rfl) ⟨85244, by rfl⟩ : syracuseStep 113659 = 170489) B170489
theorem B113767 : Blo 111784 113767 := bstep (se 1 (by rfl) ⟨85325, by rfl⟩ : syracuseStep 113767 = 170651) B170651
theorem B114203 : Blo 111784 114203 := bstep (se 1 (by rfl) ⟨85652, by rfl⟩ : syracuseStep 114203 = 171305) B171305
theorem B114367 : Blo 111784 114367 := bstep (se 1 (by rfl) ⟨85775, by rfl⟩ : syracuseStep 114367 = 171551) B171551
theorem B114623 : Blo 111784 114623 := bstep (se 1 (by rfl) ⟨85967, by rfl⟩ : syracuseStep 114623 = 171935) B171935
theorem B2899961 : Blo 111784 2899961 := bstep (se 2 (by rfl) ⟨1087485, by rfl⟩ : syracuseStep 2899961 = 2174971) B2174971
theorem B115007 : Blo 111784 115007 := bstep (se 1 (by rfl) ⟨86255, by rfl⟩ : syracuseStep 115007 = 172511) B172511
theorem B115135 : Blo 111784 115135 := bstep (se 1 (by rfl) ⟨86351, by rfl⟩ : syracuseStep 115135 = 172703) B172703
theorem B130892591 : Blo 111784 130892591 := bstep (se 1 (by rfl) ⟨98169443, by rfl⟩ : syracuseStep 130892591 = 196338887) B196338887
theorem B115527 : Blo 111784 115527 := bstep (se 1 (by rfl) ⟨86645, by rfl⟩ : syracuseStep 115527 = 173291) B173291
theorem B443369 : Blo 111784 443369 := bstep (se 2 (by rfl) ⟨166263, by rfl⟩ : syracuseStep 443369 = 332527) B332527
theorem B869939 : Blo 111784 869939 := bstep (se 1 (by rfl) ⟨652454, by rfl⟩ : syracuseStep 869939 = 1304909) B1304909
theorem B707791 : Blo 111784 707791 := bstep (se 1 (by rfl) ⟨530843, by rfl⟩ : syracuseStep 707791 = 1061687) B1061687
theorem B2608681 : Blo 111784 2608681 := bstep (se 2 (by rfl) ⟨978255, by rfl⟩ : syracuseStep 2608681 = 1956511) B1956511
theorem B183913 : Blo 111784 183913 := bstep (se 2 (by rfl) ⟨68967, by rfl⟩ : syracuseStep 183913 = 137935) B137935
theorem B5492423 : Blo 111784 5492423 := bstep (se 1 (by rfl) ⟨4119317, by rfl⟩ : syracuseStep 5492423 = 8238635) B8238635
theorem B577367 : Blo 111784 577367 := bstep (se 1 (by rfl) ⟨433025, by rfl⟩ : syracuseStep 577367 = 866051) B866051
theorem B2740243 : Blo 111784 2740243 := bstep (se 1 (by rfl) ⟨2055182, by rfl⟩ : syracuseStep 2740243 = 4110365) B4110365
theorem B381671 : Blo 111784 381671 := bstep (se 1 (by rfl) ⟨286253, by rfl⟩ : syracuseStep 381671 = 572507) B572507
theorem B579635 : Blo 111784 579635 := bstep (se 1 (by rfl) ⟨434726, by rfl⟩ : syracuseStep 579635 = 869453) B869453
theorem B1300535 : Blo 111784 1300535 := bstep (se 1 (by rfl) ⟨975401, by rfl⟩ : syracuseStep 1300535 = 1950803) B1950803
theorem B547127 : Blo 111784 547127 := bstep (se 1 (by rfl) ⟨410345, by rfl⟩ : syracuseStep 547127 = 820691) B820691
theorem B1465199 : Blo 111784 1465199 := bstep (se 1 (by rfl) ⟨1098899, by rfl⟩ : syracuseStep 1465199 = 2197799) B2197799
theorem B385019 : Blo 111784 385019 := bstep (se 1 (by rfl) ⟨288764, by rfl⟩ : syracuseStep 385019 = 577529) B577529
theorem B253979 : Blo 111784 253979 := bstep (se 1 (by rfl) ⟨190484, by rfl⟩ : syracuseStep 253979 = 380969) B380969
theorem B188507 : Blo 111784 188507 := bstep (se 1 (by rfl) ⟨141380, by rfl⟩ : syracuseStep 188507 = 282761) B282761
theorem B189931 : Blo 111784 189931 := bstep (se 1 (by rfl) ⟨142448, by rfl⟩ : syracuseStep 189931 = 284897) B284897
theorem B288431 : Blo 111784 288431 := bstep (se 1 (by rfl) ⟨216323, by rfl⟩ : syracuseStep 288431 = 432647) B432647
theorem B616423 : Blo 111784 616423 := bstep (se 1 (by rfl) ⟨462317, by rfl⟩ : syracuseStep 616423 = 924635) B924635
theorem B649403 : Blo 111784 649403 := bstep (se 1 (by rfl) ⟨487052, by rfl⟩ : syracuseStep 649403 = 974105) B974105
theorem B256427 : Blo 111784 256427 := bstep (se 1 (by rfl) ⟨192320, by rfl⟩ : syracuseStep 256427 = 384641) B384641
theorem B1108399 : Blo 111784 1108399 := bstep (se 1 (by rfl) ⟨831299, by rfl⟩ : syracuseStep 1108399 = 1662599) B1662599
theorem B191119 : Blo 111784 191119 := bstep (se 1 (by rfl) ⟨143339, by rfl⟩ : syracuseStep 191119 = 286679) B286679
theorem B322811 : Blo 111784 322811 := bstep (se 1 (by rfl) ⟨242108, by rfl⟩ : syracuseStep 322811 = 484217) B484217
theorem B388745 : Blo 111784 388745 := bstep (se 2 (by rfl) ⟨145779, by rfl⟩ : syracuseStep 388745 = 291559) B291559
theorem B16740391 : Blo 111784 16740391 := bstep (se 1 (by rfl) ⟨12555293, by rfl⟩ : syracuseStep 16740391 = 25110587) B25110587
theorem B258587 : Blo 111784 258587 := bstep (se 1 (by rfl) ⟨193940, by rfl⟩ : syracuseStep 258587 = 387881) B387881
theorem B193691 : Blo 111784 193691 := bstep (se 1 (by rfl) ⟨145268, by rfl⟩ : syracuseStep 193691 = 290537) B290537
theorem B390527 : Blo 111784 390527 := bstep (se 1 (by rfl) ⟨292895, by rfl⟩ : syracuseStep 390527 = 585791) B585791
theorem B259775 : Blo 111784 259775 := bstep (se 1 (by rfl) ⟨194831, by rfl⟩ : syracuseStep 259775 = 389663) B389663
theorem B292967 : Blo 111784 292967 := bstep (se 1 (by rfl) ⟨219725, by rfl⟩ : syracuseStep 292967 = 439451) B439451
theorem B194879 : Blo 111784 194879 := bstep (se 1 (by rfl) ⟨146159, by rfl⟩ : syracuseStep 194879 = 292319) B292319
theorem B424703 : Blo 111784 424703 := bstep (se 1 (by rfl) ⟨318527, by rfl⟩ : syracuseStep 424703 = 637055) B637055
theorem B490367 : Blo 111784 490367 := bstep (se 1 (by rfl) ⟨367775, by rfl⟩ : syracuseStep 490367 = 735551) B735551
theorem B1343135 : Blo 111784 1343135 := bstep (se 1 (by rfl) ⟨1007351, by rfl⟩ : syracuseStep 1343135 = 2014703) B2014703
theorem B328283 : Blo 111784 328283 := bstep (se 1 (by rfl) ⟨246212, by rfl⟩ : syracuseStep 328283 = 492425) B492425
theorem B295579 : Blo 111784 295579 := bstep (se 1 (by rfl) ⟨221684, by rfl⟩ : syracuseStep 295579 = 443369) B443369
theorem B853415 : Blo 111784 853415 := bstep (se 1 (by rfl) ⟨640061, by rfl⟩ : syracuseStep 853415 = 1280123) B1280123
theorem B657467 : Blo 111784 657467 := bstep (se 1 (by rfl) ⟨493100, by rfl⟩ : syracuseStep 657467 = 986201) B986201
theorem B3606605 : Blo 111784 3606605 := bstep (se 3 (by rfl) ⟨676238, by rfl⟩ : syracuseStep 3606605 = 1352477) B1352477
theorem B349046909 : Blo 111784 349046909 := bstep (se 3 (by rfl) ⟨65446295, by rfl⟩ : syracuseStep 349046909 = 130892591) B130892591
theorem B821897 : Blo 111784 821897 := bstep (se 2 (by rfl) ⟨308211, by rfl⟩ : syracuseStep 821897 = 616423) B616423
theorem B1477865 : Blo 111784 1477865 := bstep (se 2 (by rfl) ⟨554199, by rfl⟩ : syracuseStep 1477865 = 1108399) B1108399
theorem B364751 : Blo 111784 364751 := bstep (se 1 (by rfl) ⟨273563, by rfl⟩ : syracuseStep 364751 = 547127) B547127
theorem B3478241 : Blo 111784 3478241 := bstep (se 2 (by rfl) ⟨1304340, by rfl⟩ : syracuseStep 3478241 = 2608681) B2608681
theorem B169319 : Blo 111784 169319 := bstep (se 1 (by rfl) ⟨126989, by rfl⟩ : syracuseStep 169319 = 253979) B253979
theorem B22320521 : Blo 111784 22320521 := bstep (se 2 (by rfl) ⟨8370195, by rfl⟩ : syracuseStep 22320521 = 16740391) B16740391
theorem B432935 : Blo 111784 432935 := bstep (se 1 (by rfl) ⟨324701, by rfl⟩ : syracuseStep 432935 = 649403) B649403
theorem B170951 : Blo 111784 170951 := bstep (se 1 (by rfl) ⟨128213, by rfl⟩ : syracuseStep 170951 = 256427) B256427
theorem B1712387 : Blo 111784 1712387 := bstep (se 1 (by rfl) ⟨1284290, by rfl⟩ : syracuseStep 1712387 = 2568581) B2568581
theorem B172391 : Blo 111784 172391 := bstep (se 1 (by rfl) ⟨129293, by rfl⟩ : syracuseStep 172391 = 258587) B258587
theorem B173183 : Blo 111784 173183 := bstep (se 1 (by rfl) ⟨129887, by rfl⟩ : syracuseStep 173183 = 259775) B259775
theorem B206759 : Blo 111784 206759 := bstep (se 1 (by rfl) ⟨155069, by rfl⟩ : syracuseStep 206759 = 310139) B310139
theorem B895423 : Blo 111784 895423 := bstep (se 1 (by rfl) ⟨671567, by rfl⟩ : syracuseStep 895423 = 1343135) B1343135
theorem B502685 : Blo 111784 502685 := bstep (se 3 (by rfl) ⟨94253, by rfl⟩ : syracuseStep 502685 = 188507) B188507
theorem B1946429 : Blo 111784 1946429 := bstep (se 3 (by rfl) ⟨364955, by rfl⟩ : syracuseStep 1946429 = 729911) B729911
theorem B111975 : Blo 111784 111975 := bstep (se 1 (by rfl) ⟨83981, by rfl⟩ : syracuseStep 111975 = 167963) B167963
theorem B112175 : Blo 111784 112175 := bstep (se 1 (by rfl) ⟨84131, by rfl⟩ : syracuseStep 112175 = 168263) B168263
theorem B112231 : Blo 111784 112231 := bstep (se 1 (by rfl) ⟨84173, by rfl⟩ : syracuseStep 112231 = 168347) B168347
theorem B112751 : Blo 111784 112751 := bstep (se 1 (by rfl) ⟨84563, by rfl⟩ : syracuseStep 112751 = 169127) B169127
theorem B113319 : Blo 111784 113319 := bstep (se 1 (by rfl) ⟨84989, by rfl⟩ : syracuseStep 113319 = 169979) B169979
theorem B867023 : Blo 111784 867023 := bstep (se 1 (by rfl) ⟨650267, by rfl⟩ : syracuseStep 867023 = 1300535) B1300535
theorem B113435 : Blo 111784 113435 := bstep (se 1 (by rfl) ⟨85076, by rfl⟩ : syracuseStep 113435 = 170153) B170153
theorem B408673 : Blo 111784 408673 := bstep (se 2 (by rfl) ⟨153252, by rfl⟩ : syracuseStep 408673 = 306505) B306505
theorem B113775 : Blo 111784 113775 := bstep (se 1 (by rfl) ⟨85331, by rfl⟩ : syracuseStep 113775 = 170663) B170663
theorem B114303 : Blo 111784 114303 := bstep (se 1 (by rfl) ⟨85727, by rfl⟩ : syracuseStep 114303 = 171455) B171455
theorem B3653657 : Blo 111784 3653657 := bstep (se 2 (by rfl) ⟨1370121, by rfl⟩ : syracuseStep 3653657 = 2740243) B2740243
theorem B114719 : Blo 111784 114719 := bstep (se 1 (by rfl) ⟨86039, by rfl⟩ : syracuseStep 114719 = 172079) B172079
theorem B114911 : Blo 111784 114911 := bstep (se 1 (by rfl) ⟨86183, by rfl⟩ : syracuseStep 114911 = 172367) B172367
theorem B1458593 : Blo 111784 1458593 := bstep (se 2 (by rfl) ⟨546972, by rfl⟩ : syracuseStep 1458593 = 1093945) B1093945
theorem B575585 : Blo 111784 575585 := bstep (se 2 (by rfl) ⟨215844, by rfl⟩ : syracuseStep 575585 = 431689) B431689
theorem B215207 : Blo 111784 215207 := bstep (se 1 (by rfl) ⟨161405, by rfl⟩ : syracuseStep 215207 = 322811) B322811
theorem B380267 : Blo 111784 380267 := bstep (se 1 (by rfl) ⟨285200, by rfl⟩ : syracuseStep 380267 = 570401) B570401
theorem B577043 : Blo 111784 577043 := bstep (se 1 (by rfl) ⟨432782, by rfl⟩ : syracuseStep 577043 = 865565) B865565
theorem B283135 : Blo 111784 283135 := bstep (se 1 (by rfl) ⟨212351, by rfl⟩ : syracuseStep 283135 = 424703) B424703
theorem B579959 : Blo 111784 579959 := bstep (se 1 (by rfl) ⟨434969, by rfl⟩ : syracuseStep 579959 = 869939) B869939
theorem B253241 : Blo 111784 253241 := bstep (se 2 (by rfl) ⟨94965, by rfl⟩ : syracuseStep 253241 = 189931) B189931
theorem B777701 : Blo 111784 777701 := bstep (se 4 (by rfl) ⟨72909, by rfl⟩ : syracuseStep 777701 = 145819) B145819
theorem B4874003 : Blo 111784 4874003 := bstep (se 1 (by rfl) ⟨3655502, by rfl⟩ : syracuseStep 4874003 = 7311005) B7311005
theorem B3661615 : Blo 111784 3661615 := bstep (se 1 (by rfl) ⟨2746211, by rfl⟩ : syracuseStep 3661615 = 5492423) B5492423
theorem B384911 : Blo 111784 384911 := bstep (se 1 (by rfl) ⟨288683, by rfl⟩ : syracuseStep 384911 = 577367) B577367
theorem B286811 : Blo 111784 286811 := bstep (se 1 (by rfl) ⟨215108, by rfl⟩ : syracuseStep 286811 = 430217) B430217
theorem B1728647 : Blo 111784 1728647 := bstep (se 1 (by rfl) ⟨1296485, by rfl⟩ : syracuseStep 1728647 = 2592971) B2592971
theorem B254447 : Blo 111784 254447 := bstep (se 1 (by rfl) ⟨190835, by rfl⟩ : syracuseStep 254447 = 381671) B381671
theorem B287327 : Blo 111784 287327 := bstep (se 1 (by rfl) ⟨215495, by rfl⟩ : syracuseStep 287327 = 430991) B430991
theorem B156487 : Blo 111784 156487 := bstep (se 1 (by rfl) ⟨117365, by rfl⟩ : syracuseStep 156487 = 234731) B234731
theorem B254825 : Blo 111784 254825 := bstep (se 2 (by rfl) ⟨95559, by rfl⟩ : syracuseStep 254825 = 191119) B191119
theorem B877715 : Blo 111784 877715 := bstep (se 1 (by rfl) ⟨658286, by rfl⟩ : syracuseStep 877715 = 1316573) B1316573
theorem B386423 : Blo 111784 386423 := bstep (se 1 (by rfl) ⟨289817, by rfl⟩ : syracuseStep 386423 = 579635) B579635
theorem B484967 : Blo 111784 484967 := bstep (se 1 (by rfl) ⟨363725, by rfl⟩ : syracuseStep 484967 = 727451) B727451
theorem B943721 : Blo 111784 943721 := bstep (se 2 (by rfl) ⟨353895, by rfl⟩ : syracuseStep 943721 = 707791) B707791
theorem B976769 : Blo 111784 976769 := bstep (se 2 (by rfl) ⟨366288, by rfl⟩ : syracuseStep 976769 = 732577) B732577
theorem B976799 : Blo 111784 976799 := bstep (se 1 (by rfl) ⟨732599, by rfl⟩ : syracuseStep 976799 = 1465199) B1465199
theorem B7629427 : Blo 111784 7629427 := bstep (se 1 (by rfl) ⟨5722070, by rfl⟩ : syracuseStep 7629427 = 11444141) B11444141
theorem B256679 : Blo 111784 256679 := bstep (se 1 (by rfl) ⟨192509, by rfl⟩ : syracuseStep 256679 = 385019) B385019
theorem B322937 : Blo 111784 322937 := bstep (se 2 (by rfl) ⟨121101, by rfl⟩ : syracuseStep 322937 = 242203) B242203
theorem B192287 : Blo 111784 192287 := bstep (se 1 (by rfl) ⟨144215, by rfl⟩ : syracuseStep 192287 = 288431) B288431
theorem B259163 : Blo 111784 259163 := bstep (se 1 (by rfl) ⟨194372, by rfl⟩ : syracuseStep 259163 = 388745) B388745
theorem B3241133 : Blo 111784 3241133 := bstep (se 3 (by rfl) ⟨607712, by rfl⟩ : syracuseStep 3241133 = 1215425) B1215425
theorem B29652439 : Blo 111784 29652439 := bstep (se 1 (by rfl) ⟨22239329, by rfl⟩ : syracuseStep 29652439 = 44478659) B44478659
theorem B325225 : Blo 111784 325225 := bstep (se 2 (by rfl) ⟨121959, by rfl⟩ : syracuseStep 325225 = 243919) B243919
theorem B1865375 : Blo 111784 1865375 := bstep (se 1 (by rfl) ⟨1399031, by rfl⟩ : syracuseStep 1865375 = 2798063) B2798063
theorem B980869 : Blo 111784 980869 := bstep (se 4 (by rfl) ⟨91956, by rfl⟩ : syracuseStep 980869 = 183913) B183913
theorem B292855 : Blo 111784 292855 := bstep (se 1 (by rfl) ⟨219641, by rfl⟩ : syracuseStep 292855 = 439283) B439283
theorem B129127 : Blo 111784 129127 := bstep (se 1 (by rfl) ⟨96845, by rfl⟩ : syracuseStep 129127 = 193691) B193691
theorem B260351 : Blo 111784 260351 := bstep (se 1 (by rfl) ⟨195263, by rfl⟩ : syracuseStep 260351 = 390527) B390527
theorem B195311 : Blo 111784 195311 := bstep (se 1 (by rfl) ⟨146483, by rfl⟩ : syracuseStep 195311 = 292967) B292967
theorem B129919 : Blo 111784 129919 := bstep (se 1 (by rfl) ⟨97439, by rfl⟩ : syracuseStep 129919 = 194879) B194879
theorem B490607 : Blo 111784 490607 := bstep (se 1 (by rfl) ⟨367955, by rfl⟩ : syracuseStep 490607 = 735911) B735911
theorem B326911 : Blo 111784 326911 := bstep (se 1 (by rfl) ⟨245183, by rfl⟩ : syracuseStep 326911 = 490367) B490367
theorem B1933307 : Blo 111784 1933307 := bstep (se 1 (by rfl) ⟨1449980, by rfl⟩ : syracuseStep 1933307 = 2899961) B2899961
theorem B9275309 : Blo 111784 9275309 := bstep (se 3 (by rfl) ⟨1739120, by rfl⟩ : syracuseStep 9275309 = 3478241) B3478241
theorem B985243 : Blo 111784 985243 := bstep (se 1 (by rfl) ⟨738932, by rfl⟩ : syracuseStep 985243 = 1477865) B1477865
theorem B1576421 : Blo 111784 1576421 := bstep (se 4 (by rfl) ⟨147789, by rfl⟩ : syracuseStep 1576421 = 295579) B295579
theorem B14880347 : Blo 111784 14880347 := bstep (se 1 (by rfl) ⟨11160260, by rfl⟩ : syracuseStep 14880347 = 22320521) B22320521
theorem B168827 : Blo 111784 168827 := bstep (se 1 (by rfl) ⟨126620, by rfl⟩ : syracuseStep 168827 = 253241) B253241
theorem B3249335 : Blo 111784 3249335 := bstep (se 1 (by rfl) ⟨2437001, by rfl⟩ : syracuseStep 3249335 = 4874003) B4874003
theorem B1152431 : Blo 111784 1152431 := bstep (se 1 (by rfl) ⟨864323, by rfl⟩ : syracuseStep 1152431 = 1728647) B1728647
theorem B169631 : Blo 111784 169631 := bstep (se 1 (by rfl) ⟨127223, by rfl⟩ : syracuseStep 169631 = 254447) B254447
theorem B169883 : Blo 111784 169883 := bstep (se 1 (by rfl) ⟨127412, by rfl⟩ : syracuseStep 169883 = 254825) B254825
theorem B629147 : Blo 111784 629147 := bstep (se 1 (by rfl) ⟨471860, by rfl⟩ : syracuseStep 629147 = 943721) B943721
theorem B171119 : Blo 111784 171119 := bstep (se 1 (by rfl) ⟨128339, by rfl⟩ : syracuseStep 171119 = 256679) B256679
theorem B335123 : Blo 111784 335123 := bstep (se 1 (by rfl) ⟨251342, by rfl⟩ : syracuseStep 335123 = 502685) B502685
theorem B433633 : Blo 111784 433633 := bstep (se 2 (by rfl) ⟨162612, by rfl⟩ : syracuseStep 433633 = 325225) B325225
theorem B172169 : Blo 111784 172169 := bstep (se 2 (by rfl) ⟨64563, by rfl⟩ : syracuseStep 172169 = 129127) B129127
theorem B172775 : Blo 111784 172775 := bstep (se 1 (by rfl) ⟨129581, by rfl⟩ : syracuseStep 172775 = 259163) B259163
theorem B173225 : Blo 111784 173225 := bstep (se 2 (by rfl) ⟨64959, by rfl⟩ : syracuseStep 173225 = 129919) B129919
theorem B173567 : Blo 111784 173567 := bstep (se 1 (by rfl) ⟨130175, by rfl⟩ : syracuseStep 173567 = 260351) B260351
theorem B435881 : Blo 111784 435881 := bstep (se 2 (by rfl) ⟨163455, by rfl⟩ : syracuseStep 435881 = 326911) B326911
theorem B1288871 : Blo 111784 1288871 := bstep (se 1 (by rfl) ⟨966653, by rfl⟩ : syracuseStep 1288871 = 1933307) B1933307
theorem B2435771 : Blo 111784 2435771 := bstep (se 1 (by rfl) ⟨1826828, by rfl⟩ : syracuseStep 2435771 = 3653657) B3653657
theorem B4566365 : Blo 111784 4566365 := bstep (se 3 (by rfl) ⟨856193, by rfl⟩ : syracuseStep 4566365 = 1712387) B1712387
theorem B568943 : Blo 111784 568943 := bstep (se 1 (by rfl) ⟨426707, by rfl⟩ : syracuseStep 568943 = 853415) B853415
theorem B208649 : Blo 111784 208649 := bstep (se 2 (by rfl) ⟨78243, by rfl⟩ : syracuseStep 208649 = 156487) B156487
theorem B438311 : Blo 111784 438311 := bstep (se 1 (by rfl) ⟨328733, by rfl⟩ : syracuseStep 438311 = 657467) B657467
theorem B2404403 : Blo 111784 2404403 := bstep (se 1 (by rfl) ⟨1803302, by rfl⟩ : syracuseStep 2404403 = 3606605) B3606605
theorem B232697939 : Blo 111784 232697939 := bstep (se 1 (by rfl) ⟨174523454, by rfl⟩ : syracuseStep 232697939 = 349046909) B349046909
theorem B143471 : Blo 111784 143471 := bstep (se 1 (by rfl) ⟨107603, by rfl⟩ : syracuseStep 143471 = 215207) B215207
theorem B243167 : Blo 111784 243167 := bstep (se 1 (by rfl) ⟨182375, by rfl⟩ : syracuseStep 243167 = 364751) B364751
theorem B1193897 : Blo 111784 1193897 := bstep (se 2 (by rfl) ⟨447711, by rfl⟩ : syracuseStep 1193897 = 895423) B895423
theorem B10172569 : Blo 111784 10172569 := bstep (se 2 (by rfl) ⟨3814713, by rfl⟩ : syracuseStep 10172569 = 7629427) B7629427
theorem B112879 : Blo 111784 112879 := bstep (se 1 (by rfl) ⟨84659, by rfl⟩ : syracuseStep 112879 = 169319) B169319
theorem B1293245 : Blo 111784 1293245 := bstep (se 3 (by rfl) ⟨242483, by rfl⟩ : syracuseStep 1293245 = 484967) B484967
theorem B113967 : Blo 111784 113967 := bstep (se 1 (by rfl) ⟨85475, by rfl⟩ : syracuseStep 113967 = 170951) B170951
theorem B114927 : Blo 111784 114927 := bstep (se 1 (by rfl) ⟨86195, by rfl⟩ : syracuseStep 114927 = 172391) B172391
theorem B377513 : Blo 111784 377513 := bstep (se 2 (by rfl) ⟨141567, by rfl⟩ : syracuseStep 377513 = 283135) B283135
theorem B115455 : Blo 111784 115455 := bstep (se 1 (by rfl) ⟨86591, by rfl⟩ : syracuseStep 115455 = 173183) B173183
theorem B39536585 : Blo 111784 39536585 := bstep (se 2 (by rfl) ⟨14826219, by rfl⟩ : syracuseStep 39536585 = 29652439) B29652439
theorem B215291 : Blo 111784 215291 := bstep (se 1 (by rfl) ⟨161468, by rfl⟩ : syracuseStep 215291 = 322937) B322937
theorem B1297619 : Blo 111784 1297619 := bstep (se 1 (by rfl) ⟨973214, by rfl⟩ : syracuseStep 1297619 = 1946429) B1946429
theorem B544897 : Blo 111784 544897 := bstep (se 2 (by rfl) ⟨204336, by rfl⟩ : syracuseStep 544897 = 408673) B408673
theorem B578015 : Blo 111784 578015 := bstep (se 1 (by rfl) ⟨433511, by rfl⟩ : syracuseStep 578015 = 867023) B867023
theorem B972395 : Blo 111784 972395 := bstep (se 1 (by rfl) ⟨729296, by rfl⟩ : syracuseStep 972395 = 1458593) B1458593
theorem B218855 : Blo 111784 218855 := bstep (se 1 (by rfl) ⟨164141, by rfl⟩ : syracuseStep 218855 = 328283) B328283
theorem B383723 : Blo 111784 383723 := bstep (se 1 (by rfl) ⟨287792, by rfl⟩ : syracuseStep 383723 = 575585) B575585
theorem B547931 : Blo 111784 547931 := bstep (se 1 (by rfl) ⟨410948, by rfl⟩ : syracuseStep 547931 = 821897) B821897
theorem B253511 : Blo 111784 253511 := bstep (se 1 (by rfl) ⟨190133, by rfl⟩ : syracuseStep 253511 = 380267) B380267
theorem B384695 : Blo 111784 384695 := bstep (se 1 (by rfl) ⟨288521, by rfl⟩ : syracuseStep 384695 = 577043) B577043
theorem B386639 : Blo 111784 386639 := bstep (se 1 (by rfl) ⟨289979, by rfl⟩ : syracuseStep 386639 = 579959) B579959
theorem B288623 : Blo 111784 288623 := bstep (se 1 (by rfl) ⟨216467, by rfl⟩ : syracuseStep 288623 = 432935) B432935
theorem B518467 : Blo 111784 518467 := bstep (se 1 (by rfl) ⟨388850, by rfl⟩ : syracuseStep 518467 = 777701) B777701
theorem B551357 : Blo 111784 551357 := bstep (se 3 (by rfl) ⟨103379, by rfl⟩ : syracuseStep 551357 = 206759) B206759
theorem B256607 : Blo 111784 256607 := bstep (se 1 (by rfl) ⟨192455, by rfl⟩ : syracuseStep 256607 = 384911) B384911
theorem B191207 : Blo 111784 191207 := bstep (se 1 (by rfl) ⟨143405, by rfl⟩ : syracuseStep 191207 = 286811) B286811
theorem B191551 : Blo 111784 191551 := bstep (se 1 (by rfl) ⟨143663, by rfl⟩ : syracuseStep 191551 = 287327) B287327
theorem B585143 : Blo 111784 585143 := bstep (se 1 (by rfl) ⟨438857, by rfl⟩ : syracuseStep 585143 = 877715) B877715
theorem B257615 : Blo 111784 257615 := bstep (se 1 (by rfl) ⟨193211, by rfl⟩ : syracuseStep 257615 = 386423) B386423
theorem B651179 : Blo 111784 651179 := bstep (se 1 (by rfl) ⟨488384, by rfl⟩ : syracuseStep 651179 = 976769) B976769
theorem B651199 : Blo 111784 651199 := bstep (se 1 (by rfl) ⟨488399, by rfl⟩ : syracuseStep 651199 = 976799) B976799
theorem B1307825 : Blo 111784 1307825 := bstep (se 2 (by rfl) ⟨490434, by rfl⟩ : syracuseStep 1307825 = 980869) B980869
theorem B128191 : Blo 111784 128191 := bstep (se 1 (by rfl) ⟨96143, by rfl⟩ : syracuseStep 128191 = 192287) B192287
theorem B390473 : Blo 111784 390473 := bstep (se 2 (by rfl) ⟨146427, by rfl⟩ : syracuseStep 390473 = 292855) B292855
theorem B2160755 : Blo 111784 2160755 := bstep (se 1 (by rfl) ⟨1620566, by rfl⟩ : syracuseStep 2160755 = 3241133) B3241133
theorem B1243583 : Blo 111784 1243583 := bstep (se 1 (by rfl) ⟨932687, by rfl⟩ : syracuseStep 1243583 = 1865375) B1865375
theorem B19528613 : Blo 111784 19528613 := bstep (se 4 (by rfl) ⟨1830807, by rfl⟩ : syracuseStep 19528613 = 3661615) B3661615
theorem B130207 : Blo 111784 130207 := bstep (se 1 (by rfl) ⟨97655, by rfl⟩ : syracuseStep 130207 = 195311) B195311
theorem B327071 : Blo 111784 327071 := bstep (se 1 (by rfl) ⟨245303, by rfl⟩ : syracuseStep 327071 = 490607) B490607
theorem B620527837 : Blo 111784 620527837 := bstep (se 3 (by rfl) ⟨116348969, by rfl⟩ : syracuseStep 620527837 = 232697939) B232697939
theorem B1050947 : Blo 111784 1050947 := bstep (se 1 (by rfl) ⟨788210, by rfl⟩ : syracuseStep 1050947 = 1576421) B1576421
theorem B1313657 : Blo 111784 1313657 := bstep (se 2 (by rfl) ⟨492621, by rfl⟩ : syracuseStep 1313657 = 985243) B985243
theorem B691289 : Blo 111784 691289 := bstep (se 2 (by rfl) ⟨259233, by rfl⟩ : syracuseStep 691289 = 518467) B518467
theorem B2166223 : Blo 111784 2166223 := bstep (se 1 (by rfl) ⟨1624667, by rfl⟩ : syracuseStep 2166223 = 3249335) B3249335
theorem B169007 : Blo 111784 169007 := bstep (se 1 (by rfl) ⟨126755, by rfl⟩ : syracuseStep 169007 = 253511) B253511
theorem B3183725 : Blo 111784 3183725 := bstep (se 3 (by rfl) ⟨596948, by rfl⟩ : syracuseStep 3183725 = 1193897) B1193897
theorem B726529 : Blo 111784 726529 := bstep (se 2 (by rfl) ⟨272448, by rfl⟩ : syracuseStep 726529 = 544897) B544897
theorem B170921 : Blo 111784 170921 := bstep (se 2 (by rfl) ⟨64095, by rfl⟩ : syracuseStep 170921 = 128191) B128191
theorem B367571 : Blo 111784 367571 := bstep (se 1 (by rfl) ⟨275678, by rfl⟩ : syracuseStep 367571 = 551357) B551357
theorem B171071 : Blo 111784 171071 := bstep (se 1 (by rfl) ⟨128303, by rfl⟩ : syracuseStep 171071 = 256607) B256607
theorem B859247 : Blo 111784 859247 := bstep (se 1 (by rfl) ⟨644435, by rfl⟩ : syracuseStep 859247 = 1288871) B1288871
theorem B6495389 : Blo 111784 6495389 := bstep (se 3 (by rfl) ⟨1217885, by rfl⟩ : syracuseStep 6495389 = 2435771) B2435771
theorem B171743 : Blo 111784 171743 := bstep (se 1 (by rfl) ⟨128807, by rfl⟩ : syracuseStep 171743 = 257615) B257615
theorem B139099 : Blo 111784 139099 := bstep (se 1 (by rfl) ⟨104324, by rfl⟩ : syracuseStep 139099 = 208649) B208649
theorem B434119 : Blo 111784 434119 := bstep (se 1 (by rfl) ⟨325589, by rfl⟩ : syracuseStep 434119 = 651179) B651179
theorem B173609 : Blo 111784 173609 := bstep (se 2 (by rfl) ⟨65103, by rfl⟩ : syracuseStep 173609 = 130207) B130207
theorem B829055 : Blo 111784 829055 := bstep (se 1 (by rfl) ⟨621791, by rfl⟩ : syracuseStep 829055 = 1243583) B1243583
theorem B13019075 : Blo 111784 13019075 := bstep (se 1 (by rfl) ⟨9764306, by rfl⟩ : syracuseStep 13019075 = 19528613) B19528613
theorem B862163 : Blo 111784 862163 := bstep (se 1 (by rfl) ⟨646622, by rfl⟩ : syracuseStep 862163 = 1293245) B1293245
theorem B26357723 : Blo 111784 26357723 := bstep (se 1 (by rfl) ⟨19768292, by rfl⟩ : syracuseStep 26357723 = 39536585) B39536585
theorem B143527 : Blo 111784 143527 := bstep (se 1 (by rfl) ⟨107645, by rfl⟩ : syracuseStep 143527 = 215291) B215291
theorem B865079 : Blo 111784 865079 := bstep (se 1 (by rfl) ⟨648809, by rfl⟩ : syracuseStep 865079 = 1297619) B1297619
theorem B112551 : Blo 111784 112551 := bstep (se 1 (by rfl) ⟨84413, by rfl⟩ : syracuseStep 112551 = 168827) B168827
theorem B768287 : Blo 111784 768287 := bstep (se 1 (by rfl) ⟨576215, by rfl⟩ : syracuseStep 768287 = 1152431) B1152431
theorem B113087 : Blo 111784 113087 := bstep (se 1 (by rfl) ⟨84815, by rfl⟩ : syracuseStep 113087 = 169631) B169631
theorem B145903 : Blo 111784 145903 := bstep (se 1 (by rfl) ⟨109427, by rfl⟩ : syracuseStep 145903 = 218855) B218855
theorem B113255 : Blo 111784 113255 := bstep (se 1 (by rfl) ⟨84941, by rfl⟩ : syracuseStep 113255 = 169883) B169883
theorem B114079 : Blo 111784 114079 := bstep (se 1 (by rfl) ⟨85559, by rfl⟩ : syracuseStep 114079 = 171119) B171119
theorem B868265 : Blo 111784 868265 := bstep (se 2 (by rfl) ⟨325599, by rfl⟩ : syracuseStep 868265 = 651199) B651199
theorem B114779 : Blo 111784 114779 := bstep (se 1 (by rfl) ⟨86084, by rfl⟩ : syracuseStep 114779 = 172169) B172169
theorem B115183 : Blo 111784 115183 := bstep (se 1 (by rfl) ⟨86387, by rfl⟩ : syracuseStep 115183 = 172775) B172775
theorem B115483 : Blo 111784 115483 := bstep (se 1 (by rfl) ⟨86612, by rfl⟩ : syracuseStep 115483 = 173225) B173225
theorem B115711 : Blo 111784 115711 := bstep (se 1 (by rfl) ⟨86783, by rfl⟩ : syracuseStep 115711 = 173567) B173567
theorem B379295 : Blo 111784 379295 := bstep (se 1 (by rfl) ⟨284471, by rfl⟩ : syracuseStep 379295 = 568943) B568943
theorem B1461149 : Blo 111784 1461149 := bstep (se 3 (by rfl) ⟨273965, by rfl⟩ : syracuseStep 1461149 = 547931) B547931
theorem B871883 : Blo 111784 871883 := bstep (se 1 (by rfl) ⟨653912, by rfl⟩ : syracuseStep 871883 = 1307825) B1307825
theorem B578177 : Blo 111784 578177 := bstep (se 2 (by rfl) ⟨216816, by rfl⟩ : syracuseStep 578177 = 433633) B433633
theorem B218047 : Blo 111784 218047 := bstep (se 1 (by rfl) ⟨163535, by rfl⟩ : syracuseStep 218047 = 327071) B327071
theorem B382589 : Blo 111784 382589 := bstep (se 3 (by rfl) ⟨71735, by rfl⟩ : syracuseStep 382589 = 143471) B143471
theorem B251675 : Blo 111784 251675 := bstep (se 1 (by rfl) ⟨188756, by rfl⟩ : syracuseStep 251675 = 377513) B377513
theorem B6183539 : Blo 111784 6183539 := bstep (se 1 (by rfl) ⟨4637654, by rfl⟩ : syracuseStep 6183539 = 9275309) B9275309
theorem B9920231 : Blo 111784 9920231 := bstep (se 1 (by rfl) ⟨7440173, by rfl⟩ : syracuseStep 9920231 = 14880347) B14880347
theorem B385343 : Blo 111784 385343 := bstep (se 1 (by rfl) ⟨289007, by rfl⟩ : syracuseStep 385343 = 578015) B578015
theorem B648263 : Blo 111784 648263 := bstep (se 1 (by rfl) ⟨486197, by rfl⟩ : syracuseStep 648263 = 972395) B972395
theorem B648445 : Blo 111784 648445 := bstep (se 3 (by rfl) ⟨121583, by rfl⟩ : syracuseStep 648445 = 243167) B243167
theorem B255401 : Blo 111784 255401 := bstep (se 2 (by rfl) ⟨95775, by rfl⟩ : syracuseStep 255401 = 191551) B191551
theorem B419431 : Blo 111784 419431 := bstep (se 1 (by rfl) ⟨314573, by rfl⟩ : syracuseStep 419431 = 629147) B629147
theorem B255815 : Blo 111784 255815 := bstep (se 1 (by rfl) ⟨191861, by rfl⟩ : syracuseStep 255815 = 383723) B383723
theorem B223415 : Blo 111784 223415 := bstep (se 1 (by rfl) ⟨167561, by rfl⟩ : syracuseStep 223415 = 335123) B335123
theorem B256463 : Blo 111784 256463 := bstep (se 1 (by rfl) ⟨192347, by rfl⟩ : syracuseStep 256463 = 384695) B384695
theorem B257759 : Blo 111784 257759 := bstep (se 1 (by rfl) ⟨193319, by rfl⟩ : syracuseStep 257759 = 386639) B386639
theorem B290587 : Blo 111784 290587 := bstep (se 1 (by rfl) ⟨217940, by rfl⟩ : syracuseStep 290587 = 435881) B435881
theorem B192415 : Blo 111784 192415 := bstep (se 1 (by rfl) ⟨144311, by rfl⟩ : syracuseStep 192415 = 288623) B288623
theorem B127471 : Blo 111784 127471 := bstep (se 1 (by rfl) ⟨95603, by rfl⟩ : syracuseStep 127471 = 191207) B191207
theorem B3044243 : Blo 111784 3044243 := bstep (se 1 (by rfl) ⟨2283182, by rfl⟩ : syracuseStep 3044243 = 4566365) B4566365
theorem B390095 : Blo 111784 390095 := bstep (se 1 (by rfl) ⟨292571, by rfl⟩ : syracuseStep 390095 = 585143) B585143
theorem B292207 : Blo 111784 292207 := bstep (se 1 (by rfl) ⟨219155, by rfl⟩ : syracuseStep 292207 = 438311) B438311
theorem B1602935 : Blo 111784 1602935 := bstep (se 1 (by rfl) ⟨1202201, by rfl⟩ : syracuseStep 1602935 = 2404403) B2404403
theorem B13563425 : Blo 111784 13563425 := bstep (se 2 (by rfl) ⟨5086284, by rfl⟩ : syracuseStep 13563425 = 10172569) B10172569
theorem B260315 : Blo 111784 260315 := bstep (se 1 (by rfl) ⟨195236, by rfl⟩ : syracuseStep 260315 = 390473) B390473
theorem B1440503 : Blo 111784 1440503 := bstep (se 1 (by rfl) ⟨1080377, by rfl⟩ : syracuseStep 1440503 = 2160755) B2160755
theorem B460859 : Blo 111784 460859 := bstep (se 1 (by rfl) ⟨345644, by rfl⟩ : syracuseStep 460859 = 691289) B691289
theorem B559241 : Blo 111784 559241 := bstep (se 2 (by rfl) ⟨209715, by rfl⟩ : syracuseStep 559241 = 419431) B419431
theorem B167783 : Blo 111784 167783 := bstep (se 1 (by rfl) ⟨125837, by rfl⟩ : syracuseStep 167783 = 251675) B251675
theorem B2888297 : Blo 111784 2888297 := bstep (se 2 (by rfl) ⟨1083111, by rfl⟩ : syracuseStep 2888297 = 2166223) B2166223
theorem B4330259 : Blo 111784 4330259 := bstep (se 1 (by rfl) ⟨3247694, by rfl⟩ : syracuseStep 4330259 = 6495389) B6495389
theorem B169961 : Blo 111784 169961 := bstep (se 2 (by rfl) ⟨63735, by rfl⟩ : syracuseStep 169961 = 127471) B127471
theorem B432175 : Blo 111784 432175 := bstep (se 1 (by rfl) ⟨324131, by rfl⟩ : syracuseStep 432175 = 648263) B648263
theorem B170267 : Blo 111784 170267 := bstep (se 1 (by rfl) ⟨127700, by rfl⟩ : syracuseStep 170267 = 255401) B255401
theorem B170543 : Blo 111784 170543 := bstep (se 1 (by rfl) ⟨127907, by rfl⟩ : syracuseStep 170543 = 255815) B255815
theorem B170975 : Blo 111784 170975 := bstep (se 1 (by rfl) ⟨128231, by rfl⟩ : syracuseStep 170975 = 256463) B256463
theorem B171839 : Blo 111784 171839 := bstep (se 1 (by rfl) ⟨128879, by rfl⟩ : syracuseStep 171839 = 257759) B257759
theorem B17571815 : Blo 111784 17571815 := bstep (se 1 (by rfl) ⟨13178861, by rfl⟩ : syracuseStep 17571815 = 26357723) B26357723
theorem B173543 : Blo 111784 173543 := bstep (se 1 (by rfl) ⟨130157, by rfl⟩ : syracuseStep 173543 = 260315) B260315
theorem B960335 : Blo 111784 960335 := bstep (se 1 (by rfl) ⟨720251, by rfl⟩ : syracuseStep 960335 = 1440503) B1440503
theorem B827370449 : Blo 111784 827370449 := bstep (se 2 (by rfl) ⟨310263918, by rfl⟩ : syracuseStep 827370449 = 620527837) B620527837
theorem B700631 : Blo 111784 700631 := bstep (se 1 (by rfl) ⟨525473, by rfl⟩ : syracuseStep 700631 = 1050947) B1050947
theorem B864593 : Blo 111784 864593 := bstep (se 2 (by rfl) ⟨324222, by rfl⟩ : syracuseStep 864593 = 648445) B648445
theorem B112671 : Blo 111784 112671 := bstep (se 1 (by rfl) ⟨84503, by rfl⟩ : syracuseStep 112671 = 169007) B169007
theorem B113947 : Blo 111784 113947 := bstep (se 1 (by rfl) ⟨85460, by rfl⟩ : syracuseStep 113947 = 170921) B170921
theorem B245047 : Blo 111784 245047 := bstep (se 1 (by rfl) ⟨183785, by rfl⟩ : syracuseStep 245047 = 367571) B367571
theorem B114047 : Blo 111784 114047 := bstep (se 1 (by rfl) ⟨85535, by rfl⟩ : syracuseStep 114047 = 171071) B171071
theorem B572831 : Blo 111784 572831 := bstep (se 1 (by rfl) ⟨429623, by rfl⟩ : syracuseStep 572831 = 859247) B859247
theorem B114495 : Blo 111784 114495 := bstep (se 1 (by rfl) ⟨85871, by rfl⟩ : syracuseStep 114495 = 171743) B171743
theorem B115739 : Blo 111784 115739 := bstep (se 1 (by rfl) ⟨86804, by rfl⟩ : syracuseStep 115739 = 173609) B173609
theorem B574775 : Blo 111784 574775 := bstep (se 1 (by rfl) ⟨431081, by rfl⟩ : syracuseStep 574775 = 862163) B862163
theorem B148943 : Blo 111784 148943 := bstep (se 1 (by rfl) ⟨111707, by rfl⟩ : syracuseStep 148943 = 223415) B223415
theorem B968705 : Blo 111784 968705 := bstep (se 2 (by rfl) ⟨363264, by rfl⟩ : syracuseStep 968705 = 726529) B726529
theorem B576719 : Blo 111784 576719 := bstep (se 1 (by rfl) ⟨432539, by rfl⟩ : syracuseStep 576719 = 865079) B865079
theorem B1068623 : Blo 111784 1068623 := bstep (se 1 (by rfl) ⟨801467, by rfl⟩ : syracuseStep 1068623 = 1602935) B1602935
theorem B512191 : Blo 111784 512191 := bstep (se 1 (by rfl) ⟨384143, by rfl⟩ : syracuseStep 512191 = 768287) B768287
theorem B185465 : Blo 111784 185465 := bstep (se 2 (by rfl) ⟨69549, by rfl⟩ : syracuseStep 185465 = 139099) B139099
theorem B578825 : Blo 111784 578825 := bstep (se 2 (by rfl) ⟨217059, by rfl⟩ : syracuseStep 578825 = 434119) B434119
theorem B578843 : Blo 111784 578843 := bstep (se 1 (by rfl) ⟨434132, by rfl⟩ : syracuseStep 578843 = 868265) B868265
theorem B252863 : Blo 111784 252863 := bstep (se 1 (by rfl) ⟨189647, by rfl⟩ : syracuseStep 252863 = 379295) B379295
theorem B875771 : Blo 111784 875771 := bstep (se 1 (by rfl) ⟨656828, by rfl⟩ : syracuseStep 875771 = 1313657) B1313657
theorem B974099 : Blo 111784 974099 := bstep (se 1 (by rfl) ⟨730574, by rfl⟩ : syracuseStep 974099 = 1461149) B1461149
theorem B581255 : Blo 111784 581255 := bstep (se 1 (by rfl) ⟨435941, by rfl⟩ : syracuseStep 581255 = 871883) B871883
theorem B385451 : Blo 111784 385451 := bstep (se 1 (by rfl) ⟨289088, by rfl⟩ : syracuseStep 385451 = 578177) B578177
theorem B2122483 : Blo 111784 2122483 := bstep (se 1 (by rfl) ⟨1591862, by rfl⟩ : syracuseStep 2122483 = 3183725) B3183725
theorem B255059 : Blo 111784 255059 := bstep (se 1 (by rfl) ⟨191294, by rfl⟩ : syracuseStep 255059 = 382589) B382589
theorem B4122359 : Blo 111784 4122359 := bstep (se 1 (by rfl) ⟨3091769, by rfl⟩ : syracuseStep 4122359 = 6183539) B6183539
theorem B387449 : Blo 111784 387449 := bstep (se 2 (by rfl) ⟨145293, by rfl⟩ : syracuseStep 387449 = 290587) B290587
theorem B6613487 : Blo 111784 6613487 := bstep (se 1 (by rfl) ⟨4960115, by rfl⟩ : syracuseStep 6613487 = 9920231) B9920231
theorem B256553 : Blo 111784 256553 := bstep (se 2 (by rfl) ⟨96207, by rfl⟩ : syracuseStep 256553 = 192415) B192415
theorem B256895 : Blo 111784 256895 := bstep (se 1 (by rfl) ⟨192671, by rfl⟩ : syracuseStep 256895 = 385343) B385343
theorem B191369 : Blo 111784 191369 := bstep (se 2 (by rfl) ⟨71763, by rfl⟩ : syracuseStep 191369 = 143527) B143527
theorem B552703 : Blo 111784 552703 := bstep (se 1 (by rfl) ⟨414527, by rfl⟩ : syracuseStep 552703 = 829055) B829055
theorem B290729 : Blo 111784 290729 := bstep (se 2 (by rfl) ⟨109023, by rfl⟩ : syracuseStep 290729 = 218047) B218047
theorem B8679383 : Blo 111784 8679383 := bstep (se 1 (by rfl) ⟨6509537, by rfl⟩ : syracuseStep 8679383 = 13019075) B13019075
theorem B389609 : Blo 111784 389609 := bstep (se 2 (by rfl) ⟨146103, by rfl⟩ : syracuseStep 389609 = 292207) B292207
theorem B2029495 : Blo 111784 2029495 := bstep (se 1 (by rfl) ⟨1522121, by rfl⟩ : syracuseStep 2029495 = 3044243) B3044243
theorem B260063 : Blo 111784 260063 := bstep (se 1 (by rfl) ⟨195047, by rfl⟩ : syracuseStep 260063 = 390095) B390095
theorem B194537 : Blo 111784 194537 := bstep (se 2 (by rfl) ⟨72951, by rfl⟩ : syracuseStep 194537 = 145903) B145903
theorem B9042283 : Blo 111784 9042283 := bstep (se 1 (by rfl) ⟨6781712, by rfl⟩ : syracuseStep 9042283 = 13563425) B13563425
theorem B4915829 : Blo 111784 4915829 := bstep (se 5 (by rfl) ⟨230429, by rfl⟩ : syracuseStep 4915829 = 460859) B460859
theorem B2886839 : Blo 111784 2886839 := bstep (se 1 (by rfl) ⟨2165129, by rfl⟩ : syracuseStep 2886839 = 4330259) B4330259
theorem B397181 : Blo 111784 397181 := bstep (se 3 (by rfl) ⟨74471, by rfl⟩ : syracuseStep 397181 = 148943) B148943
theorem B168575 : Blo 111784 168575 := bstep (se 1 (by rfl) ⟨126431, by rfl⟩ : syracuseStep 168575 = 252863) B252863
theorem B170039 : Blo 111784 170039 := bstep (se 1 (by rfl) ⟨127529, by rfl⟩ : syracuseStep 170039 = 255059) B255059
theorem B171035 : Blo 111784 171035 := bstep (se 1 (by rfl) ⟨128276, by rfl⟩ : syracuseStep 171035 = 256553) B256553
theorem B171263 : Blo 111784 171263 := bstep (se 1 (by rfl) ⟨128447, by rfl⟩ : syracuseStep 171263 = 256895) B256895
theorem B467087 : Blo 111784 467087 := bstep (se 1 (by rfl) ⟨350315, by rfl⟩ : syracuseStep 467087 = 700631) B700631
theorem B173375 : Blo 111784 173375 := bstep (se 1 (by rfl) ⟨130031, by rfl⟩ : syracuseStep 173375 = 260063) B260063
theorem B2829977 : Blo 111784 2829977 := bstep (se 2 (by rfl) ⟨1061241, by rfl⟩ : syracuseStep 2829977 = 2122483) B2122483
theorem B372827 : Blo 111784 372827 := bstep (se 1 (by rfl) ⟨279620, by rfl⟩ : syracuseStep 372827 = 559241) B559241
theorem B111855 : Blo 111784 111855 := bstep (se 1 (by rfl) ⟨83891, by rfl⟩ : syracuseStep 111855 = 167783) B167783
theorem B113307 : Blo 111784 113307 := bstep (se 1 (by rfl) ⟨84980, by rfl⟩ : syracuseStep 113307 = 169961) B169961
theorem B113511 : Blo 111784 113511 := bstep (se 1 (by rfl) ⟨85133, by rfl⟩ : syracuseStep 113511 = 170267) B170267
theorem B113695 : Blo 111784 113695 := bstep (se 1 (by rfl) ⟨85271, by rfl⟩ : syracuseStep 113695 = 170543) B170543
theorem B113983 : Blo 111784 113983 := bstep (se 1 (by rfl) ⟨85487, by rfl⟩ : syracuseStep 113983 = 170975) B170975
theorem B736937 : Blo 111784 736937 := bstep (se 2 (by rfl) ⟨276351, by rfl⟩ : syracuseStep 736937 = 552703) B552703
theorem B114559 : Blo 111784 114559 := bstep (se 1 (by rfl) ⟨85919, by rfl⟩ : syracuseStep 114559 = 171839) B171839
theorem B11714543 : Blo 111784 11714543 := bstep (se 1 (by rfl) ⟨8785907, by rfl⟩ : syracuseStep 11714543 = 17571815) B17571815
theorem B115695 : Blo 111784 115695 := bstep (se 1 (by rfl) ⟨86771, by rfl⟩ : syracuseStep 115695 = 173543) B173543
theorem B640223 : Blo 111784 640223 := bstep (se 1 (by rfl) ⟨480167, by rfl⟩ : syracuseStep 640223 = 960335) B960335
theorem B4408991 : Blo 111784 4408991 := bstep (se 1 (by rfl) ⟨3306743, by rfl⟩ : syracuseStep 4408991 = 6613487) B6613487
theorem B2705993 : Blo 111784 2705993 := bstep (se 2 (by rfl) ⟨1014747, by rfl⟩ : syracuseStep 2705993 = 2029495) B2029495
theorem B5786255 : Blo 111784 5786255 := bstep (se 1 (by rfl) ⟨4339691, by rfl⟩ : syracuseStep 5786255 = 8679383) B8679383
theorem B576233 : Blo 111784 576233 := bstep (se 2 (by rfl) ⟨216087, by rfl⟩ : syracuseStep 576233 = 432175) B432175
theorem B576395 : Blo 111784 576395 := bstep (se 1 (by rfl) ⟨432296, by rfl⟩ : syracuseStep 576395 = 864593) B864593
theorem B381887 : Blo 111784 381887 := bstep (se 1 (by rfl) ⟨286415, by rfl⟩ : syracuseStep 381887 = 572831) B572831
theorem B383183 : Blo 111784 383183 := bstep (se 1 (by rfl) ⟨287387, by rfl⟩ : syracuseStep 383183 = 574775) B574775
theorem B645803 : Blo 111784 645803 := bstep (se 1 (by rfl) ⟨484352, by rfl⟩ : syracuseStep 645803 = 968705) B968705
theorem B384479 : Blo 111784 384479 := bstep (se 1 (by rfl) ⟨288359, by rfl⟩ : syracuseStep 384479 = 576719) B576719
theorem B712415 : Blo 111784 712415 := bstep (se 1 (by rfl) ⟨534311, by rfl⟩ : syracuseStep 712415 = 1068623) B1068623
theorem B1925531 : Blo 111784 1925531 := bstep (se 1 (by rfl) ⟨1444148, by rfl⟩ : syracuseStep 1925531 = 2888297) B2888297
theorem B123643 : Blo 111784 123643 := bstep (se 1 (by rfl) ⟨92732, by rfl⟩ : syracuseStep 123643 = 185465) B185465
theorem B385883 : Blo 111784 385883 := bstep (se 1 (by rfl) ⟨289412, by rfl⟩ : syracuseStep 385883 = 578825) B578825
theorem B385895 : Blo 111784 385895 := bstep (se 1 (by rfl) ⟨289421, by rfl⟩ : syracuseStep 385895 = 578843) B578843
theorem B583847 : Blo 111784 583847 := bstep (se 1 (by rfl) ⟨437885, by rfl⟩ : syracuseStep 583847 = 875771) B875771
theorem B649399 : Blo 111784 649399 := bstep (se 1 (by rfl) ⟨487049, by rfl⟩ : syracuseStep 649399 = 974099) B974099
theorem B387503 : Blo 111784 387503 := bstep (se 1 (by rfl) ⟨290627, by rfl⟩ : syracuseStep 387503 = 581255) B581255
theorem B682921 : Blo 111784 682921 := bstep (se 2 (by rfl) ⟨256095, by rfl⟩ : syracuseStep 682921 = 512191) B512191
theorem B256967 : Blo 111784 256967 := bstep (se 1 (by rfl) ⟨192725, by rfl⟩ : syracuseStep 256967 = 385451) B385451
theorem B2748239 : Blo 111784 2748239 := bstep (se 1 (by rfl) ⟨2061179, by rfl⟩ : syracuseStep 2748239 = 4122359) B4122359
theorem B258299 : Blo 111784 258299 := bstep (se 1 (by rfl) ⟨193724, by rfl⟩ : syracuseStep 258299 = 387449) B387449
theorem B127579 : Blo 111784 127579 := bstep (se 1 (by rfl) ⟨95684, by rfl⟩ : syracuseStep 127579 = 191369) B191369
theorem B551580299 : Blo 111784 551580299 := bstep (se 1 (by rfl) ⟨413685224, by rfl⟩ : syracuseStep 551580299 = 827370449) B827370449
theorem B193819 : Blo 111784 193819 := bstep (se 1 (by rfl) ⟨145364, by rfl⟩ : syracuseStep 193819 = 290729) B290729
theorem B259739 : Blo 111784 259739 := bstep (se 1 (by rfl) ⟨194804, by rfl⟩ : syracuseStep 259739 = 389609) B389609
theorem B12056377 : Blo 111784 12056377 := bstep (se 2 (by rfl) ⟨4521141, by rfl⟩ : syracuseStep 12056377 = 9042283) B9042283
theorem B129691 : Blo 111784 129691 := bstep (se 1 (by rfl) ⟨97268, by rfl⟩ : syracuseStep 129691 = 194537) B194537
theorem B326729 : Blo 111784 326729 := bstep (se 2 (by rfl) ⟨122523, by rfl⟩ : syracuseStep 326729 = 245047) B245047
theorem B1245565 : Blo 111784 1245565 := bstep (se 3 (by rfl) ⟨233543, by rfl⟩ : syracuseStep 1245565 = 467087) B467087
theorem B3277219 : Blo 111784 3277219 := bstep (se 1 (by rfl) ⟨2457914, by rfl⟩ : syracuseStep 3277219 = 4915829) B4915829
theorem B426815 : Blo 111784 426815 := bstep (se 1 (by rfl) ⟨320111, by rfl⟩ : syracuseStep 426815 = 640223) B640223
theorem B164857 : Blo 111784 164857 := bstep (se 2 (by rfl) ⟨61821, by rfl⟩ : syracuseStep 164857 = 123643) B123643
theorem B1803995 : Blo 111784 1803995 := bstep (se 1 (by rfl) ⟨1352996, by rfl⟩ : syracuseStep 1803995 = 2705993) B2705993
theorem B691685 : Blo 111784 691685 := bstep (se 4 (by rfl) ⟨64845, by rfl⟩ : syracuseStep 691685 = 129691) B129691
theorem B430535 : Blo 111784 430535 := bstep (se 1 (by rfl) ⟨322901, by rfl⟩ : syracuseStep 430535 = 645803) B645803
theorem B3642245 : Blo 111784 3642245 := bstep (se 4 (by rfl) ⟨341460, by rfl⟩ : syracuseStep 3642245 = 682921) B682921
theorem B1283687 : Blo 111784 1283687 := bstep (se 1 (by rfl) ⟨962765, by rfl⟩ : syracuseStep 1283687 = 1925531) B1925531
theorem B170105 : Blo 111784 170105 := bstep (se 2 (by rfl) ⟨63789, by rfl⟩ : syracuseStep 170105 = 127579) B127579
theorem B171311 : Blo 111784 171311 := bstep (se 1 (by rfl) ⟨128483, by rfl⟩ : syracuseStep 171311 = 256967) B256967
theorem B172199 : Blo 111784 172199 := bstep (se 1 (by rfl) ⟨129149, by rfl⟩ : syracuseStep 172199 = 258299) B258299
theorem B173159 : Blo 111784 173159 := bstep (se 1 (by rfl) ⟨129869, by rfl⟩ : syracuseStep 173159 = 259739) B259739
theorem B1059149 : Blo 111784 1059149 := bstep (se 3 (by rfl) ⟨198590, by rfl⟩ : syracuseStep 1059149 = 397181) B397181
theorem B7809695 : Blo 111784 7809695 := bstep (se 1 (by rfl) ⟨5857271, by rfl⟩ : syracuseStep 7809695 = 11714543) B11714543
theorem B865865 : Blo 111784 865865 := bstep (se 2 (by rfl) ⟨324699, by rfl⟩ : syracuseStep 865865 = 649399) B649399
theorem B112383 : Blo 111784 112383 := bstep (se 1 (by rfl) ⟨84287, by rfl⟩ : syracuseStep 112383 = 168575) B168575
theorem B113359 : Blo 111784 113359 := bstep (se 1 (by rfl) ⟨85019, by rfl⟩ : syracuseStep 113359 = 170039) B170039
theorem B114023 : Blo 111784 114023 := bstep (se 1 (by rfl) ⟨85517, by rfl⟩ : syracuseStep 114023 = 171035) B171035
theorem B114175 : Blo 111784 114175 := bstep (se 1 (by rfl) ⟨85631, by rfl⟩ : syracuseStep 114175 = 171263) B171263
theorem B115583 : Blo 111784 115583 := bstep (se 1 (by rfl) ⟨86687, by rfl⟩ : syracuseStep 115583 = 173375) B173375
theorem B16075169 : Blo 111784 16075169 := bstep (se 2 (by rfl) ⟨6028188, by rfl⟩ : syracuseStep 16075169 = 12056377) B12056377
theorem B1886651 : Blo 111784 1886651 := bstep (se 1 (by rfl) ⟨1414988, by rfl⟩ : syracuseStep 1886651 = 2829977) B2829977
theorem B248551 : Blo 111784 248551 := bstep (se 1 (by rfl) ⟨186413, by rfl⟩ : syracuseStep 248551 = 372827) B372827
theorem B217819 : Blo 111784 217819 := bstep (se 1 (by rfl) ⟨163364, by rfl⟩ : syracuseStep 217819 = 326729) B326729
theorem B2939327 : Blo 111784 2939327 := bstep (se 1 (by rfl) ⟨2204495, by rfl⟩ : syracuseStep 2939327 = 4408991) B4408991
theorem B3857503 : Blo 111784 3857503 := bstep (se 1 (by rfl) ⟨2893127, by rfl⟩ : syracuseStep 3857503 = 5786255) B5786255
theorem B384155 : Blo 111784 384155 := bstep (se 1 (by rfl) ⟨288116, by rfl⟩ : syracuseStep 384155 = 576233) B576233
theorem B384263 : Blo 111784 384263 := bstep (se 1 (by rfl) ⟨288197, by rfl⟩ : syracuseStep 384263 = 576395) B576395
theorem B1924559 : Blo 111784 1924559 := bstep (se 1 (by rfl) ⟨1443419, by rfl⟩ : syracuseStep 1924559 = 2886839) B2886839
theorem B254591 : Blo 111784 254591 := bstep (se 1 (by rfl) ⟨190943, by rfl⟩ : syracuseStep 254591 = 381887) B381887
theorem B255455 : Blo 111784 255455 := bstep (se 1 (by rfl) ⟨191591, by rfl⟩ : syracuseStep 255455 = 383183) B383183
theorem B256319 : Blo 111784 256319 := bstep (se 1 (by rfl) ⟨192239, by rfl⟩ : syracuseStep 256319 = 384479) B384479
theorem B257255 : Blo 111784 257255 := bstep (se 1 (by rfl) ⟨192941, by rfl⟩ : syracuseStep 257255 = 385883) B385883
theorem B257263 : Blo 111784 257263 := bstep (se 1 (by rfl) ⟨192947, by rfl⟩ : syracuseStep 257263 = 385895) B385895
theorem B389231 : Blo 111784 389231 := bstep (se 1 (by rfl) ⟨291923, by rfl⟩ : syracuseStep 389231 = 583847) B583847
theorem B258335 : Blo 111784 258335 := bstep (se 1 (by rfl) ⟨193751, by rfl⟩ : syracuseStep 258335 = 387503) B387503
theorem B258425 : Blo 111784 258425 := bstep (se 2 (by rfl) ⟨96909, by rfl⟩ : syracuseStep 258425 = 193819) B193819
theorem B1832159 : Blo 111784 1832159 := bstep (se 1 (by rfl) ⟨1374119, by rfl⟩ : syracuseStep 1832159 = 2748239) B2748239
theorem B367720199 : Blo 111784 367720199 := bstep (se 1 (by rfl) ⟨275790149, by rfl⟩ : syracuseStep 367720199 = 551580299) B551580299
theorem B1899773 : Blo 111784 1899773 := bstep (se 3 (by rfl) ⟨356207, by rfl⟩ : syracuseStep 1899773 = 712415) B712415
theorem B491291 : Blo 111784 491291 := bstep (se 1 (by rfl) ⟨368468, by rfl⟩ : syracuseStep 491291 = 736937) B736937
theorem B10716779 : Blo 111784 10716779 := bstep (se 1 (by rfl) ⟨8037584, by rfl⟩ : syracuseStep 10716779 = 16075169) B16075169
theorem B461123 : Blo 111784 461123 := bstep (se 1 (by rfl) ⟨345842, by rfl⟩ : syracuseStep 461123 = 691685) B691685
theorem B2428163 : Blo 111784 2428163 := bstep (se 1 (by rfl) ⟨1821122, by rfl⟩ : syracuseStep 2428163 = 3642245) B3642245
theorem B855791 : Blo 111784 855791 := bstep (se 1 (by rfl) ⟨641843, by rfl⟩ : syracuseStep 855791 = 1283687) B1283687
theorem B1283039 : Blo 111784 1283039 := bstep (se 1 (by rfl) ⟨962279, by rfl⟩ : syracuseStep 1283039 = 1924559) B1924559
theorem B169727 : Blo 111784 169727 := bstep (se 1 (by rfl) ⟨127295, by rfl⟩ : syracuseStep 169727 = 254591) B254591
theorem B170303 : Blo 111784 170303 := bstep (se 1 (by rfl) ⟨127727, by rfl⟩ : syracuseStep 170303 = 255455) B255455
theorem B170879 : Blo 111784 170879 := bstep (se 1 (by rfl) ⟨128159, by rfl⟩ : syracuseStep 170879 = 256319) B256319
theorem B171503 : Blo 111784 171503 := bstep (se 1 (by rfl) ⟨128627, by rfl⟩ : syracuseStep 171503 = 257255) B257255
theorem B172223 : Blo 111784 172223 := bstep (se 1 (by rfl) ⟨129167, by rfl⟩ : syracuseStep 172223 = 258335) B258335
theorem B172283 : Blo 111784 172283 := bstep (se 1 (by rfl) ⟨129212, by rfl⟩ : syracuseStep 172283 = 258425) B258425
theorem B1221439 : Blo 111784 1221439 := bstep (se 1 (by rfl) ⟨916079, by rfl⟩ : syracuseStep 1221439 = 1832159) B1832159
theorem B245146799 : Blo 111784 245146799 := bstep (se 1 (by rfl) ⟨183860099, by rfl⟩ : syracuseStep 245146799 = 367720199) B367720199
theorem B4369625 : Blo 111784 4369625 := bstep (se 2 (by rfl) ⟨1638609, by rfl⟩ : syracuseStep 4369625 = 3277219) B3277219
theorem B1257767 : Blo 111784 1257767 := bstep (se 1 (by rfl) ⟨943325, by rfl⟩ : syracuseStep 1257767 = 1886651) B1886651
theorem B1325605 : Blo 111784 1325605 := bstep (se 4 (by rfl) ⟨124275, by rfl⟩ : syracuseStep 1325605 = 248551) B248551
theorem B113403 : Blo 111784 113403 := bstep (se 1 (by rfl) ⟨85052, by rfl⟩ : syracuseStep 113403 = 170105) B170105
theorem B114207 : Blo 111784 114207 := bstep (se 1 (by rfl) ⟨85655, by rfl⟩ : syracuseStep 114207 = 171311) B171311
theorem B114799 : Blo 111784 114799 := bstep (se 1 (by rfl) ⟨86099, by rfl⟩ : syracuseStep 114799 = 172199) B172199
theorem B115439 : Blo 111784 115439 := bstep (se 1 (by rfl) ⟨86579, by rfl⟩ : syracuseStep 115439 = 173159) B173159
theorem B706099 : Blo 111784 706099 := bstep (se 1 (by rfl) ⟨529574, by rfl⟩ : syracuseStep 706099 = 1059149) B1059149
theorem B577243 : Blo 111784 577243 := bstep (se 1 (by rfl) ⟨432932, by rfl⟩ : syracuseStep 577243 = 865865) B865865
theorem B1266515 : Blo 111784 1266515 := bstep (se 1 (by rfl) ⟨949886, by rfl⟩ : syracuseStep 1266515 = 1899773) B1899773
theorem B1660753 : Blo 111784 1660753 := bstep (se 2 (by rfl) ⟨622782, by rfl⟩ : syracuseStep 1660753 = 1245565) B1245565
theorem B284543 : Blo 111784 284543 := bstep (se 1 (by rfl) ⟨213407, by rfl⟩ : syracuseStep 284543 = 426815) B426815
theorem B1202663 : Blo 111784 1202663 := bstep (se 1 (by rfl) ⟨901997, by rfl⟩ : syracuseStep 1202663 = 1803995) B1803995
theorem B219809 : Blo 111784 219809 := bstep (se 2 (by rfl) ⟨82428, by rfl⟩ : syracuseStep 219809 = 164857) B164857
theorem B287023 : Blo 111784 287023 := bstep (se 1 (by rfl) ⟨215267, by rfl⟩ : syracuseStep 287023 = 430535) B430535
theorem B1959551 : Blo 111784 1959551 := bstep (se 1 (by rfl) ⟨1469663, by rfl⟩ : syracuseStep 1959551 = 2939327) B2939327
theorem B256103 : Blo 111784 256103 := bstep (se 1 (by rfl) ⟨192077, by rfl⟩ : syracuseStep 256103 = 384155) B384155
theorem B256175 : Blo 111784 256175 := bstep (se 1 (by rfl) ⟨192131, by rfl⟩ : syracuseStep 256175 = 384263) B384263
theorem B290425 : Blo 111784 290425 := bstep (se 2 (by rfl) ⟨108909, by rfl⟩ : syracuseStep 290425 = 217819) B217819
theorem B1372069 : Blo 111784 1372069 := bstep (se 4 (by rfl) ⟨128631, by rfl⟩ : syracuseStep 1372069 = 257263) B257263
theorem B5206463 : Blo 111784 5206463 := bstep (se 1 (by rfl) ⟨3904847, by rfl⟩ : syracuseStep 5206463 = 7809695) B7809695
theorem B259487 : Blo 111784 259487 := bstep (se 1 (by rfl) ⟨194615, by rfl⟩ : syracuseStep 259487 = 389231) B389231
theorem B5143337 : Blo 111784 5143337 := bstep (se 2 (by rfl) ⟨1928751, by rfl⟩ : syracuseStep 5143337 = 3857503) B3857503
theorem B327527 : Blo 111784 327527 := bstep (se 1 (by rfl) ⟨245645, by rfl⟩ : syracuseStep 327527 = 491291) B491291
theorem B7144519 : Blo 111784 7144519 := bstep (se 1 (by rfl) ⟨5358389, by rfl⟩ : syracuseStep 7144519 = 10716779) B10716779
theorem B855359 : Blo 111784 855359 := bstep (se 1 (by rfl) ⟨641519, by rfl⟩ : syracuseStep 855359 = 1283039) B1283039
theorem B170735 : Blo 111784 170735 := bstep (se 1 (by rfl) ⟨128051, by rfl⟩ : syracuseStep 170735 = 256103) B256103
theorem B170783 : Blo 111784 170783 := bstep (se 1 (by rfl) ⟨128087, by rfl⟩ : syracuseStep 170783 = 256175) B256175
theorem B172991 : Blo 111784 172991 := bstep (se 1 (by rfl) ⟨129743, by rfl⟩ : syracuseStep 172991 = 259487) B259487
theorem B7317701 : Blo 111784 7317701 := bstep (se 4 (by rfl) ⟨686034, by rfl⟩ : syracuseStep 7317701 = 1372069) B1372069
theorem B307415 : Blo 111784 307415 := bstep (se 1 (by rfl) ⟨230561, by rfl⟩ : syracuseStep 307415 = 461123) B461123
theorem B1618775 : Blo 111784 1618775 := bstep (se 1 (by rfl) ⟨1214081, by rfl⟩ : syracuseStep 1618775 = 2428163) B2428163
theorem B570527 : Blo 111784 570527 := bstep (se 1 (by rfl) ⟨427895, by rfl⟩ : syracuseStep 570527 = 855791) B855791
theorem B113151 : Blo 111784 113151 := bstep (se 1 (by rfl) ⟨84863, by rfl⟩ : syracuseStep 113151 = 169727) B169727
theorem B113535 : Blo 111784 113535 := bstep (se 1 (by rfl) ⟨85151, by rfl⟩ : syracuseStep 113535 = 170303) B170303
theorem B801775 : Blo 111784 801775 := bstep (se 1 (by rfl) ⟨601331, by rfl⟩ : syracuseStep 801775 = 1202663) B1202663
theorem B146539 : Blo 111784 146539 := bstep (se 1 (by rfl) ⟨109904, by rfl⟩ : syracuseStep 146539 = 219809) B219809
theorem B113919 : Blo 111784 113919 := bstep (se 1 (by rfl) ⟨85439, by rfl⟩ : syracuseStep 113919 = 170879) B170879
theorem B769657 : Blo 111784 769657 := bstep (se 2 (by rfl) ⟨288621, by rfl⟩ : syracuseStep 769657 = 577243) B577243
theorem B114335 : Blo 111784 114335 := bstep (se 1 (by rfl) ⟨85751, by rfl⟩ : syracuseStep 114335 = 171503) B171503
theorem B114815 : Blo 111784 114815 := bstep (se 1 (by rfl) ⟨86111, by rfl⟩ : syracuseStep 114815 = 172223) B172223
theorem B114855 : Blo 111784 114855 := bstep (se 1 (by rfl) ⟨86141, by rfl⟩ : syracuseStep 114855 = 172283) B172283
theorem B163431199 : Blo 111784 163431199 := bstep (se 1 (by rfl) ⟨122573399, by rfl⟩ : syracuseStep 163431199 = 245146799) B245146799
theorem B2214337 : Blo 111784 2214337 := bstep (se 2 (by rfl) ⟨830376, by rfl⟩ : syracuseStep 2214337 = 1660753) B1660753
theorem B838511 : Blo 111784 838511 := bstep (se 1 (by rfl) ⟨628883, by rfl⟩ : syracuseStep 838511 = 1257767) B1257767
theorem B3428891 : Blo 111784 3428891 := bstep (se 1 (by rfl) ⟨2571668, by rfl⟩ : syracuseStep 3428891 = 5143337) B5143337
theorem B218351 : Blo 111784 218351 := bstep (se 1 (by rfl) ⟨163763, by rfl⟩ : syracuseStep 218351 = 327527) B327527
theorem B382697 : Blo 111784 382697 := bstep (se 2 (by rfl) ⟨143511, by rfl⟩ : syracuseStep 382697 = 287023) B287023
theorem B1628585 : Blo 111784 1628585 := bstep (se 2 (by rfl) ⟨610719, by rfl⟩ : syracuseStep 1628585 = 1221439) B1221439
theorem B941465 : Blo 111784 941465 := bstep (se 2 (by rfl) ⟨353049, by rfl⟩ : syracuseStep 941465 = 706099) B706099
theorem B844343 : Blo 111784 844343 := bstep (se 1 (by rfl) ⟨633257, by rfl⟩ : syracuseStep 844343 = 1266515) B1266515
theorem B189695 : Blo 111784 189695 := bstep (se 1 (by rfl) ⟨142271, by rfl⟩ : syracuseStep 189695 = 284543) B284543
theorem B387233 : Blo 111784 387233 := bstep (se 2 (by rfl) ⟨145212, by rfl⟩ : syracuseStep 387233 = 290425) B290425
theorem B1306367 : Blo 111784 1306367 := bstep (se 1 (by rfl) ⟨979775, by rfl⟩ : syracuseStep 1306367 = 1959551) B1959551
theorem B2913083 : Blo 111784 2913083 := bstep (se 1 (by rfl) ⟨2184812, by rfl⟩ : syracuseStep 2913083 = 4369625) B4369625
theorem B3470975 : Blo 111784 3470975 := bstep (se 1 (by rfl) ⟨2603231, by rfl⟩ : syracuseStep 3470975 = 5206463) B5206463
theorem B1767473 : Blo 111784 1767473 := bstep (se 2 (by rfl) ⟨662802, by rfl⟩ : syracuseStep 1767473 = 1325605) B1325605
theorem B217908265 : Blo 111784 217908265 := bstep (se 2 (by rfl) ⟨81715599, by rfl⟩ : syracuseStep 217908265 = 163431199) B163431199
theorem B559007 : Blo 111784 559007 := bstep (se 1 (by rfl) ⟨419255, by rfl⟩ : syracuseStep 559007 = 838511) B838511
theorem B2952449 : Blo 111784 2952449 := bstep (se 2 (by rfl) ⟨1107168, by rfl⟩ : syracuseStep 2952449 = 2214337) B2214337
theorem B1085723 : Blo 111784 1085723 := bstep (se 1 (by rfl) ⟨814292, by rfl⟩ : syracuseStep 1085723 = 1628585) B1628585
theorem B627643 : Blo 111784 627643 := bstep (se 1 (by rfl) ⟨470732, by rfl⟩ : syracuseStep 627643 = 941465) B941465
theorem B562895 : Blo 111784 562895 := bstep (se 1 (by rfl) ⟨422171, by rfl⟩ : syracuseStep 562895 = 844343) B844343
theorem B204943 : Blo 111784 204943 := bstep (se 1 (by rfl) ⟨153707, by rfl⟩ : syracuseStep 204943 = 307415) B307415
theorem B1942055 : Blo 111784 1942055 := bstep (se 1 (by rfl) ⟨1456541, by rfl⟩ : syracuseStep 1942055 = 2913083) B2913083
theorem B1026209 : Blo 111784 1026209 := bstep (se 2 (by rfl) ⟨384828, by rfl⟩ : syracuseStep 1026209 = 769657) B769657
theorem B570239 : Blo 111784 570239 := bstep (se 1 (by rfl) ⟨427679, by rfl⟩ : syracuseStep 570239 = 855359) B855359
theorem B145567 : Blo 111784 145567 := bstep (se 1 (by rfl) ⟨109175, by rfl⟩ : syracuseStep 145567 = 218351) B218351
theorem B113823 : Blo 111784 113823 := bstep (se 1 (by rfl) ⟨85367, by rfl⟩ : syracuseStep 113823 = 170735) B170735
theorem B113855 : Blo 111784 113855 := bstep (se 1 (by rfl) ⟨85391, by rfl⟩ : syracuseStep 113855 = 170783) B170783
theorem B115327 : Blo 111784 115327 := bstep (se 1 (by rfl) ⟨86495, by rfl⟩ : syracuseStep 115327 = 172991) B172991
theorem B870911 : Blo 111784 870911 := bstep (se 1 (by rfl) ⟨653183, by rfl⟩ : syracuseStep 870911 = 1306367) B1306367
theorem B380351 : Blo 111784 380351 := bstep (se 1 (by rfl) ⟨285263, by rfl⟩ : syracuseStep 380351 = 570527) B570527
theorem B2313983 : Blo 111784 2313983 := bstep (se 1 (by rfl) ⟨1735487, by rfl⟩ : syracuseStep 2313983 = 3470975) B3470975
theorem B1069033 : Blo 111784 1069033 := bstep (se 2 (by rfl) ⟨400887, by rfl⟩ : syracuseStep 1069033 = 801775) B801775
theorem B9526025 : Blo 111784 9526025 := bstep (se 2 (by rfl) ⟨3572259, by rfl⟩ : syracuseStep 9526025 = 7144519) B7144519
theorem B2285927 : Blo 111784 2285927 := bstep (se 1 (by rfl) ⟨1714445, by rfl⟩ : syracuseStep 2285927 = 3428891) B3428891
theorem B255131 : Blo 111784 255131 := bstep (se 1 (by rfl) ⟨191348, by rfl⟩ : syracuseStep 255131 = 382697) B382697
theorem B126463 : Blo 111784 126463 := bstep (se 1 (by rfl) ⟨94847, by rfl⟩ : syracuseStep 126463 = 189695) B189695
theorem B258155 : Blo 111784 258155 := bstep (se 1 (by rfl) ⟨193616, by rfl⟩ : syracuseStep 258155 = 387233) B387233
theorem B4878467 : Blo 111784 4878467 := bstep (se 1 (by rfl) ⟨3658850, by rfl⟩ : syracuseStep 4878467 = 7317701) B7317701
theorem B1079183 : Blo 111784 1079183 := bstep (se 1 (by rfl) ⟨809387, by rfl⟩ : syracuseStep 1079183 = 1618775) B1618775
theorem B1178315 : Blo 111784 1178315 := bstep (se 1 (by rfl) ⟨883736, by rfl⟩ : syracuseStep 1178315 = 1767473) B1767473
theorem B195385 : Blo 111784 195385 := bstep (se 2 (by rfl) ⟨73269, by rfl⟩ : syracuseStep 195385 = 146539) B146539
theorem B1968299 : Blo 111784 1968299 := bstep (se 1 (by rfl) ⟨1476224, by rfl⟩ : syracuseStep 1968299 = 2952449) B2952449
theorem B1542655 : Blo 111784 1542655 := bstep (se 1 (by rfl) ⟨1156991, by rfl⟩ : syracuseStep 1542655 = 2313983) B2313983
theorem B723815 : Blo 111784 723815 := bstep (se 1 (by rfl) ⟨542861, by rfl⟩ : syracuseStep 723815 = 1085723) B1085723
theorem B168617 : Blo 111784 168617 := bstep (se 2 (by rfl) ⟨63231, by rfl⟩ : syracuseStep 168617 = 126463) B126463
theorem B170087 : Blo 111784 170087 := bstep (se 1 (by rfl) ⟨127565, by rfl⟩ : syracuseStep 170087 = 255131) B255131
theorem B172103 : Blo 111784 172103 := bstep (se 1 (by rfl) ⟨129077, by rfl⟩ : syracuseStep 172103 = 258155) B258155
theorem B3252311 : Blo 111784 3252311 := bstep (se 1 (by rfl) ⟨2439233, by rfl⟩ : syracuseStep 3252311 = 4878467) B4878467
theorem B273257 : Blo 111784 273257 := bstep (se 2 (by rfl) ⟨102471, by rfl⟩ : syracuseStep 273257 = 204943) B204943
theorem B372671 : Blo 111784 372671 := bstep (se 1 (by rfl) ⟨279503, by rfl⟩ : syracuseStep 372671 = 559007) B559007
theorem B375263 : Blo 111784 375263 := bstep (se 1 (by rfl) ⟨281447, by rfl⟩ : syracuseStep 375263 = 562895) B562895
theorem B1425377 : Blo 111784 1425377 := bstep (se 2 (by rfl) ⟨534516, by rfl⟩ : syracuseStep 1425377 = 1069033) B1069033
theorem B1523951 : Blo 111784 1523951 := bstep (se 1 (by rfl) ⟨1142963, by rfl⟩ : syracuseStep 1523951 = 2285927) B2285927
theorem B1294703 : Blo 111784 1294703 := bstep (se 1 (by rfl) ⟨971027, by rfl⟩ : syracuseStep 1294703 = 1942055) B1942055
theorem B836857 : Blo 111784 836857 := bstep (se 2 (by rfl) ⟨313821, by rfl⟩ : syracuseStep 836857 = 627643) B627643
theorem B380159 : Blo 111784 380159 := bstep (se 1 (by rfl) ⟨285119, by rfl⟩ : syracuseStep 380159 = 570239) B570239
theorem B290544353 : Blo 111784 290544353 := bstep (se 2 (by rfl) ⟨108954132, by rfl⟩ : syracuseStep 290544353 = 217908265) B217908265
theorem B580607 : Blo 111784 580607 := bstep (se 1 (by rfl) ⟨435455, by rfl⟩ : syracuseStep 580607 = 870911) B870911
theorem B253567 : Blo 111784 253567 := bstep (se 1 (by rfl) ⟨190175, by rfl⟩ : syracuseStep 253567 = 380351) B380351
theorem B6350683 : Blo 111784 6350683 := bstep (se 1 (by rfl) ⟨4763012, by rfl⟩ : syracuseStep 6350683 = 9526025) B9526025
theorem B684139 : Blo 111784 684139 := bstep (se 1 (by rfl) ⟨513104, by rfl⟩ : syracuseStep 684139 = 1026209) B1026209
theorem B194089 : Blo 111784 194089 := bstep (se 2 (by rfl) ⟨72783, by rfl⟩ : syracuseStep 194089 = 145567) B145567
theorem B260513 : Blo 111784 260513 := bstep (se 2 (by rfl) ⟨97692, by rfl⟩ : syracuseStep 260513 = 195385) B195385
theorem B719455 : Blo 111784 719455 := bstep (se 1 (by rfl) ⟨539591, by rfl⟩ : syracuseStep 719455 = 1079183) B1079183
theorem B785543 : Blo 111784 785543 := bstep (se 1 (by rfl) ⟨589157, by rfl⟩ : syracuseStep 785543 = 1178315) B1178315
theorem B1015967 : Blo 111784 1015967 := bstep (se 1 (by rfl) ⟨761975, by rfl⟩ : syracuseStep 1015967 = 1523951) B1523951
theorem B1312199 : Blo 111784 1312199 := bstep (se 1 (by rfl) ⟨984149, by rfl⟩ : syracuseStep 1312199 = 1968299) B1968299
theorem B8227493 : Blo 111784 8227493 := bstep (se 4 (by rfl) ⟨771327, by rfl⟩ : syracuseStep 8227493 = 1542655) B1542655
theorem B193696235 : Blo 111784 193696235 := bstep (se 1 (by rfl) ⟨145272176, by rfl⟩ : syracuseStep 193696235 = 290544353) B290544353
theorem B2168207 : Blo 111784 2168207 := bstep (se 1 (by rfl) ⟨1626155, by rfl⟩ : syracuseStep 2168207 = 3252311) B3252311
theorem B4463237 : Blo 111784 4463237 := bstep (se 4 (by rfl) ⟨418428, by rfl⟩ : syracuseStep 4463237 = 836857) B836857
theorem B959273 : Blo 111784 959273 := bstep (se 2 (by rfl) ⟨359727, by rfl⟩ : syracuseStep 959273 = 719455) B719455
theorem B173675 : Blo 111784 173675 := bstep (se 1 (by rfl) ⟨130256, by rfl⟩ : syracuseStep 173675 = 260513) B260513
theorem B338089 : Blo 111784 338089 := bstep (se 2 (by rfl) ⟨126783, by rfl⟩ : syracuseStep 338089 = 253567) B253567
theorem B863135 : Blo 111784 863135 := bstep (se 1 (by rfl) ⟨647351, by rfl⟩ : syracuseStep 863135 = 1294703) B1294703
theorem B8467577 : Blo 111784 8467577 := bstep (se 2 (by rfl) ⟨3175341, by rfl⟩ : syracuseStep 8467577 = 6350683) B6350683
theorem B112411 : Blo 111784 112411 := bstep (se 1 (by rfl) ⟨84308, by rfl⟩ : syracuseStep 112411 = 168617) B168617
theorem B113391 : Blo 111784 113391 := bstep (se 1 (by rfl) ⟨85043, by rfl⟩ : syracuseStep 113391 = 170087) B170087
theorem B114735 : Blo 111784 114735 := bstep (se 1 (by rfl) ⟨86051, by rfl⟩ : syracuseStep 114735 = 172103) B172103
theorem B182171 : Blo 111784 182171 := bstep (se 1 (by rfl) ⟨136628, by rfl⟩ : syracuseStep 182171 = 273257) B273257
theorem B248447 : Blo 111784 248447 := bstep (se 1 (by rfl) ⟨186335, by rfl⟩ : syracuseStep 248447 = 372671) B372671
theorem B250175 : Blo 111784 250175 := bstep (se 1 (by rfl) ⟨187631, by rfl⟩ : syracuseStep 250175 = 375263) B375263
theorem B482543 : Blo 111784 482543 := bstep (se 1 (by rfl) ⟨361907, by rfl⟩ : syracuseStep 482543 = 723815) B723815
theorem B253439 : Blo 111784 253439 := bstep (se 1 (by rfl) ⟨190079, by rfl⟩ : syracuseStep 253439 = 380159) B380159
theorem B387071 : Blo 111784 387071 := bstep (se 1 (by rfl) ⟨290303, by rfl⟩ : syracuseStep 387071 = 580607) B580607
theorem B912185 : Blo 111784 912185 := bstep (se 2 (by rfl) ⟨342069, by rfl⟩ : syracuseStep 912185 = 684139) B684139
theorem B258785 : Blo 111784 258785 := bstep (se 2 (by rfl) ⟨97044, by rfl⟩ : syracuseStep 258785 = 194089) B194089
theorem B2094781 : Blo 111784 2094781 := bstep (se 3 (by rfl) ⟨392771, by rfl⟩ : syracuseStep 2094781 = 785543) B785543
theorem B3801005 : Blo 111784 3801005 := bstep (se 3 (by rfl) ⟨712688, by rfl⟩ : syracuseStep 3801005 = 1425377) B1425377
theorem B1445471 : Blo 111784 1445471 := bstep (se 1 (by rfl) ⟨1084103, by rfl⟩ : syracuseStep 1445471 = 2168207) B2168207
theorem B168959 : Blo 111784 168959 := bstep (se 1 (by rfl) ⟨126719, by rfl⟩ : syracuseStep 168959 = 253439) B253439
theorem B662525 : Blo 111784 662525 := bstep (se 3 (by rfl) ⟨124223, by rfl⟩ : syracuseStep 662525 = 248447) B248447
theorem B2793041 : Blo 111784 2793041 := bstep (se 2 (by rfl) ⟨1047390, by rfl⟩ : syracuseStep 2793041 = 2094781) B2094781
theorem B172523 : Blo 111784 172523 := bstep (se 1 (by rfl) ⟨129392, by rfl⟩ : syracuseStep 172523 = 258785) B258785
theorem B5645051 : Blo 111784 5645051 := bstep (se 1 (by rfl) ⟨4233788, by rfl⟩ : syracuseStep 5645051 = 8467577) B8467577
theorem B2534003 : Blo 111784 2534003 := bstep (se 1 (by rfl) ⟨1900502, by rfl⟩ : syracuseStep 2534003 = 3801005) B3801005
theorem B667133 : Blo 111784 667133 := bstep (se 3 (by rfl) ⟨125087, by rfl⟩ : syracuseStep 667133 = 250175) B250175
theorem B5484995 : Blo 111784 5484995 := bstep (se 1 (by rfl) ⟨4113746, by rfl⟩ : syracuseStep 5484995 = 8227493) B8227493
theorem B639515 : Blo 111784 639515 := bstep (se 1 (by rfl) ⟨479636, by rfl⟩ : syracuseStep 639515 = 959273) B959273
theorem B115783 : Blo 111784 115783 := bstep (se 1 (by rfl) ⟨86837, by rfl⟩ : syracuseStep 115783 = 173675) B173675
theorem B608123 : Blo 111784 608123 := bstep (se 1 (by rfl) ⟨456092, by rfl⟩ : syracuseStep 608123 = 912185) B912185
theorem B575423 : Blo 111784 575423 := bstep (se 1 (by rfl) ⟨431567, by rfl⟩ : syracuseStep 575423 = 863135) B863135
theorem B2709245 : Blo 111784 2709245 := bstep (se 3 (by rfl) ⟨507983, by rfl⟩ : syracuseStep 2709245 = 1015967) B1015967
theorem B874799 : Blo 111784 874799 := bstep (se 1 (by rfl) ⟨656099, by rfl⟩ : syracuseStep 874799 = 1312199) B1312199
theorem B121447 : Blo 111784 121447 := bstep (se 1 (by rfl) ⟨91085, by rfl⟩ : syracuseStep 121447 = 182171) B182171
theorem B450785 : Blo 111784 450785 := bstep (se 2 (by rfl) ⟨169044, by rfl⟩ : syracuseStep 450785 = 338089) B338089
theorem B129130823 : Blo 111784 129130823 := bstep (se 1 (by rfl) ⟨96848117, by rfl⟩ : syracuseStep 129130823 = 193696235) B193696235
theorem B2975491 : Blo 111784 2975491 := bstep (se 1 (by rfl) ⟨2231618, by rfl⟩ : syracuseStep 2975491 = 4463237) B4463237
theorem B321695 : Blo 111784 321695 := bstep (se 1 (by rfl) ⟨241271, by rfl⟩ : syracuseStep 321695 = 482543) B482543
theorem B258047 : Blo 111784 258047 := bstep (se 1 (by rfl) ⟨193535, by rfl⟩ : syracuseStep 258047 = 387071) B387071
theorem B426343 : Blo 111784 426343 := bstep (se 1 (by rfl) ⟨319757, by rfl⟩ : syracuseStep 426343 = 639515) B639515
theorem B3967321 : Blo 111784 3967321 := bstep (se 2 (by rfl) ⟨1487745, by rfl⟩ : syracuseStep 3967321 = 2975491) B2975491
theorem B300523 : Blo 111784 300523 := bstep (se 1 (by rfl) ⟨225392, by rfl⟩ : syracuseStep 300523 = 450785) B450785
theorem B86087215 : Blo 111784 86087215 := bstep (se 1 (by rfl) ⟨64565411, by rfl⟩ : syracuseStep 86087215 = 129130823) B129130823
theorem B172031 : Blo 111784 172031 := bstep (se 1 (by rfl) ⟨129023, by rfl⟩ : syracuseStep 172031 = 258047) B258047
theorem B405415 : Blo 111784 405415 := bstep (se 1 (by rfl) ⟨304061, by rfl⟩ : syracuseStep 405415 = 608123) B608123
theorem B963647 : Blo 111784 963647 := bstep (se 1 (by rfl) ⟨722735, by rfl⟩ : syracuseStep 963647 = 1445471) B1445471
theorem B112639 : Blo 111784 112639 := bstep (se 1 (by rfl) ⟨84479, by rfl⟩ : syracuseStep 112639 = 168959) B168959
theorem B7224653 : Blo 111784 7224653 := bstep (se 3 (by rfl) ⟨1354622, by rfl⟩ : syracuseStep 7224653 = 2709245) B2709245
theorem B441683 : Blo 111784 441683 := bstep (se 1 (by rfl) ⟨331262, by rfl⟩ : syracuseStep 441683 = 662525) B662525
theorem B115015 : Blo 111784 115015 := bstep (se 1 (by rfl) ⟨86261, by rfl⟩ : syracuseStep 115015 = 172523) B172523
theorem B214463 : Blo 111784 214463 := bstep (se 1 (by rfl) ⟨160847, by rfl⟩ : syracuseStep 214463 = 321695) B321695
theorem B1689335 : Blo 111784 1689335 := bstep (se 1 (by rfl) ⟨1267001, by rfl⟩ : syracuseStep 1689335 = 2534003) B2534003
theorem B444755 : Blo 111784 444755 := bstep (se 1 (by rfl) ⟨333566, by rfl⟩ : syracuseStep 444755 = 667133) B667133
theorem B3656663 : Blo 111784 3656663 := bstep (se 1 (by rfl) ⟨2742497, by rfl⟩ : syracuseStep 3656663 = 5484995) B5484995
theorem B383615 : Blo 111784 383615 := bstep (se 1 (by rfl) ⟨287711, by rfl⟩ : syracuseStep 383615 = 575423) B575423
theorem B583199 : Blo 111784 583199 := bstep (se 1 (by rfl) ⟨437399, by rfl⟩ : syracuseStep 583199 = 874799) B874799
theorem B1862027 : Blo 111784 1862027 := bstep (se 1 (by rfl) ⟨1396520, by rfl⟩ : syracuseStep 1862027 = 2793041) B2793041
theorem B3763367 : Blo 111784 3763367 := bstep (se 1 (by rfl) ⟨2822525, by rfl⟩ : syracuseStep 3763367 = 5645051) B5645051
theorem B161929 : Blo 111784 161929 := bstep (se 2 (by rfl) ⟨60723, by rfl⟩ : syracuseStep 161929 = 121447) B121447
theorem B296503 : Blo 111784 296503 := bstep (se 1 (by rfl) ⟨222377, by rfl⟩ : syracuseStep 296503 = 444755) B444755
theorem B400697 : Blo 111784 400697 := bstep (se 2 (by rfl) ⟨150261, by rfl⟩ : syracuseStep 400697 = 300523) B300523
theorem B568457 : Blo 111784 568457 := bstep (se 2 (by rfl) ⟨213171, by rfl⟩ : syracuseStep 568457 = 426343) B426343
theorem B863621 : Blo 111784 863621 := bstep (se 4 (by rfl) ⟨80964, by rfl⟩ : syracuseStep 863621 = 161929) B161929
theorem B142975 : Blo 111784 142975 := bstep (se 1 (by rfl) ⟨107231, by rfl⟩ : syracuseStep 142975 = 214463) B214463
theorem B1126223 : Blo 111784 1126223 := bstep (se 1 (by rfl) ⟨844667, by rfl⟩ : syracuseStep 1126223 = 1689335) B1689335
theorem B2437775 : Blo 111784 2437775 := bstep (se 1 (by rfl) ⟨1828331, by rfl⟩ : syracuseStep 2437775 = 3656663) B3656663
theorem B5289761 : Blo 111784 5289761 := bstep (se 2 (by rfl) ⟨1983660, by rfl⟩ : syracuseStep 5289761 = 3967321) B3967321
theorem B114687 : Blo 111784 114687 := bstep (se 1 (by rfl) ⟨86015, by rfl⟩ : syracuseStep 114687 = 172031) B172031
theorem B2508911 : Blo 111784 2508911 := bstep (se 1 (by rfl) ⟨1881683, by rfl⟩ : syracuseStep 2508911 = 3763367) B3763367
theorem B642431 : Blo 111784 642431 := bstep (se 1 (by rfl) ⟨481823, by rfl⟩ : syracuseStep 642431 = 963647) B963647
theorem B255743 : Blo 111784 255743 := bstep (se 1 (by rfl) ⟨191807, by rfl⟩ : syracuseStep 255743 = 383615) B383615
theorem B388799 : Blo 111784 388799 := bstep (se 1 (by rfl) ⟨291599, by rfl⟩ : syracuseStep 388799 = 583199) B583199
theorem B1241351 : Blo 111784 1241351 := bstep (se 1 (by rfl) ⟨931013, by rfl⟩ : syracuseStep 1241351 = 1862027) B1862027
theorem B114782953 : Blo 111784 114782953 := bstep (se 2 (by rfl) ⟨43043607, by rfl⟩ : syracuseStep 114782953 = 86087215) B86087215
theorem B2162213 : Blo 111784 2162213 := bstep (se 4 (by rfl) ⟨202707, by rfl⟩ : syracuseStep 2162213 = 405415) B405415
theorem B4816435 : Blo 111784 4816435 := bstep (se 1 (by rfl) ⟨3612326, by rfl⟩ : syracuseStep 4816435 = 7224653) B7224653
theorem B294455 : Blo 111784 294455 := bstep (se 1 (by rfl) ⟨220841, by rfl⟩ : syracuseStep 294455 = 441683) B441683
theorem B6325397 : Blo 111784 6325397 := bstep (se 6 (by rfl) ⟨148251, by rfl⟩ : syracuseStep 6325397 = 296503) B296503
theorem B1672607 : Blo 111784 1672607 := bstep (se 1 (by rfl) ⟨1254455, by rfl⟩ : syracuseStep 1672607 = 2508911) B2508911
theorem B428287 : Blo 111784 428287 := bstep (se 1 (by rfl) ⟨321215, by rfl⟩ : syracuseStep 428287 = 642431) B642431
theorem B267131 : Blo 111784 267131 := bstep (se 1 (by rfl) ⟨200348, by rfl⟩ : syracuseStep 267131 = 400697) B400697
theorem B170495 : Blo 111784 170495 := bstep (se 1 (by rfl) ⟨127871, by rfl⟩ : syracuseStep 170495 = 255743) B255743
theorem B827567 : Blo 111784 827567 := bstep (se 1 (by rfl) ⟨620675, by rfl⟩ : syracuseStep 827567 = 1241351) B1241351
theorem B153043937 : Blo 111784 153043937 := bstep (se 2 (by rfl) ⟨57391476, by rfl⟩ : syracuseStep 153043937 = 114782953) B114782953
theorem B378971 : Blo 111784 378971 := bstep (se 1 (by rfl) ⟨284228, by rfl⟩ : syracuseStep 378971 = 568457) B568457
theorem B575747 : Blo 111784 575747 := bstep (se 1 (by rfl) ⟨431810, by rfl⟩ : syracuseStep 575747 = 863621) B863621
theorem B1625183 : Blo 111784 1625183 := bstep (se 1 (by rfl) ⟨1218887, by rfl⟩ : syracuseStep 1625183 = 2437775) B2437775
theorem B3526507 : Blo 111784 3526507 := bstep (se 1 (by rfl) ⟨2644880, by rfl⟩ : syracuseStep 3526507 = 5289761) B5289761
theorem B190633 : Blo 111784 190633 := bstep (se 2 (by rfl) ⟨71487, by rfl⟩ : syracuseStep 190633 = 142975) B142975
theorem B259199 : Blo 111784 259199 := bstep (se 1 (by rfl) ⟨194399, by rfl⟩ : syracuseStep 259199 = 388799) B388799
theorem B750815 : Blo 111784 750815 := bstep (se 1 (by rfl) ⟨563111, by rfl⟩ : syracuseStep 750815 = 1126223) B1126223
theorem B6421913 : Blo 111784 6421913 := bstep (se 2 (by rfl) ⟨2408217, by rfl⟩ : syracuseStep 6421913 = 4816435) B4816435
theorem B1441475 : Blo 111784 1441475 := bstep (se 1 (by rfl) ⟨1081106, by rfl⟩ : syracuseStep 1441475 = 2162213) B2162213
theorem B196303 : Blo 111784 196303 := bstep (se 1 (by rfl) ⟨147227, by rfl⟩ : syracuseStep 196303 = 294455) B294455
theorem B1083455 : Blo 111784 1083455 := bstep (se 1 (by rfl) ⟨812591, by rfl⟩ : syracuseStep 1083455 = 1625183) B1625183
theorem B4460285 : Blo 111784 4460285 := bstep (se 3 (by rfl) ⟨836303, by rfl⟩ : syracuseStep 4460285 = 1672607) B1672607
theorem B172799 : Blo 111784 172799 := bstep (se 1 (by rfl) ⟨129599, by rfl⟩ : syracuseStep 172799 = 259199) B259199
theorem B500543 : Blo 111784 500543 := bstep (se 1 (by rfl) ⟨375407, by rfl⟩ : syracuseStep 500543 = 750815) B750815
theorem B960983 : Blo 111784 960983 := bstep (se 1 (by rfl) ⟨720737, by rfl⟩ : syracuseStep 960983 = 1441475) B1441475
theorem B571049 : Blo 111784 571049 := bstep (se 2 (by rfl) ⟨214143, by rfl⟩ : syracuseStep 571049 = 428287) B428287
theorem B178087 : Blo 111784 178087 := bstep (se 1 (by rfl) ⟨133565, by rfl⟩ : syracuseStep 178087 = 267131) B267131
theorem B113663 : Blo 111784 113663 := bstep (se 1 (by rfl) ⟨85247, by rfl⟩ : syracuseStep 113663 = 170495) B170495
theorem B4702009 : Blo 111784 4702009 := bstep (se 2 (by rfl) ⟨1763253, by rfl⟩ : syracuseStep 4702009 = 3526507) B3526507
theorem B4281275 : Blo 111784 4281275 := bstep (se 1 (by rfl) ⟨3210956, by rfl⟩ : syracuseStep 4281275 = 6421913) B6421913
theorem B102029291 : Blo 111784 102029291 := bstep (se 1 (by rfl) ⟨76521968, by rfl⟩ : syracuseStep 102029291 = 153043937) B153043937
theorem B4216931 : Blo 111784 4216931 := bstep (se 1 (by rfl) ⟨3162698, by rfl⟩ : syracuseStep 4216931 = 6325397) B6325397
theorem B252647 : Blo 111784 252647 := bstep (se 1 (by rfl) ⟨189485, by rfl⟩ : syracuseStep 252647 = 378971) B378971
theorem B383831 : Blo 111784 383831 := bstep (se 1 (by rfl) ⟨287873, by rfl⟩ : syracuseStep 383831 = 575747) B575747
theorem B254177 : Blo 111784 254177 := bstep (se 2 (by rfl) ⟨95316, by rfl⟩ : syracuseStep 254177 = 190633) B190633
theorem B551711 : Blo 111784 551711 := bstep (se 1 (by rfl) ⟨413783, by rfl⟩ : syracuseStep 551711 = 827567) B827567
theorem B261737 : Blo 111784 261737 := bstep (se 2 (by rfl) ⟨98151, by rfl⟩ : syracuseStep 261737 = 196303) B196303
theorem B722303 : Blo 111784 722303 := bstep (se 1 (by rfl) ⟨541727, by rfl⟩ : syracuseStep 722303 = 1083455) B1083455
theorem B168431 : Blo 111784 168431 := bstep (se 1 (by rfl) ⟨126323, by rfl⟩ : syracuseStep 168431 = 252647) B252647
theorem B169451 : Blo 111784 169451 := bstep (se 1 (by rfl) ⟨127088, by rfl⟩ : syracuseStep 169451 = 254177) B254177
theorem B333695 : Blo 111784 333695 := bstep (se 1 (by rfl) ⟨250271, by rfl⟩ : syracuseStep 333695 = 500543) B500543
theorem B237449 : Blo 111784 237449 := bstep (se 2 (by rfl) ⟨89043, by rfl⟩ : syracuseStep 237449 = 178087) B178087
theorem B174491 : Blo 111784 174491 := bstep (se 1 (by rfl) ⟨130868, by rfl⟩ : syracuseStep 174491 = 261737) B261737
theorem B6269345 : Blo 111784 6269345 := bstep (se 2 (by rfl) ⟨2351004, by rfl⟩ : syracuseStep 6269345 = 4702009) B4702009
theorem B11416733 : Blo 111784 11416733 := bstep (se 3 (by rfl) ⟨2140637, by rfl⟩ : syracuseStep 11416733 = 4281275) B4281275
theorem B115199 : Blo 111784 115199 := bstep (se 1 (by rfl) ⟨86399, by rfl⟩ : syracuseStep 115199 = 172799) B172799
theorem B640655 : Blo 111784 640655 := bstep (se 1 (by rfl) ⟨480491, by rfl⟩ : syracuseStep 640655 = 960983) B960983
theorem B380699 : Blo 111784 380699 := bstep (se 1 (by rfl) ⟨285524, by rfl⟩ : syracuseStep 380699 = 571049) B571049
theorem B2973523 : Blo 111784 2973523 := bstep (se 1 (by rfl) ⟨2230142, by rfl⟩ : syracuseStep 2973523 = 4460285) B4460285
theorem B68019527 : Blo 111784 68019527 := bstep (se 1 (by rfl) ⟨51014645, by rfl⟩ : syracuseStep 68019527 = 102029291) B102029291
theorem B2811287 : Blo 111784 2811287 := bstep (se 1 (by rfl) ⟨2108465, by rfl⟩ : syracuseStep 2811287 = 4216931) B4216931
theorem B255887 : Blo 111784 255887 := bstep (se 1 (by rfl) ⟨191915, by rfl⟩ : syracuseStep 255887 = 383831) B383831
theorem B1471229 : Blo 111784 1471229 := bstep (se 3 (by rfl) ⟨275855, by rfl⟩ : syracuseStep 1471229 = 551711) B551711
theorem B427103 : Blo 111784 427103 := bstep (se 1 (by rfl) ⟨320327, by rfl⟩ : syracuseStep 427103 = 640655) B640655
theorem B1874191 : Blo 111784 1874191 := bstep (se 1 (by rfl) ⟨1405643, by rfl⟩ : syracuseStep 1874191 = 2811287) B2811287
theorem B170591 : Blo 111784 170591 := bstep (se 1 (by rfl) ⟨127943, by rfl⟩ : syracuseStep 170591 = 255887) B255887
theorem B7611155 : Blo 111784 7611155 := bstep (se 1 (by rfl) ⟨5708366, by rfl⟩ : syracuseStep 7611155 = 11416733) B11416733
theorem B633197 : Blo 111784 633197 := bstep (se 3 (by rfl) ⟨118724, by rfl⟩ : syracuseStep 633197 = 237449) B237449
theorem B112287 : Blo 111784 112287 := bstep (se 1 (by rfl) ⟨84215, by rfl⟩ : syracuseStep 112287 = 168431) B168431
theorem B112967 : Blo 111784 112967 := bstep (se 1 (by rfl) ⟨84725, by rfl⟩ : syracuseStep 112967 = 169451) B169451
theorem B116327 : Blo 111784 116327 := bstep (se 1 (by rfl) ⟨87245, by rfl⟩ : syracuseStep 116327 = 174491) B174491
theorem B4179563 : Blo 111784 4179563 := bstep (se 1 (by rfl) ⟨3134672, by rfl⟩ : syracuseStep 4179563 = 6269345) B6269345
theorem B481535 : Blo 111784 481535 := bstep (se 1 (by rfl) ⟨361151, by rfl⟩ : syracuseStep 481535 = 722303) B722303
theorem B253799 : Blo 111784 253799 := bstep (se 1 (by rfl) ⟨190349, by rfl⟩ : syracuseStep 253799 = 380699) B380699
theorem B222463 : Blo 111784 222463 := bstep (se 1 (by rfl) ⟨166847, by rfl⟩ : syracuseStep 222463 = 333695) B333695
theorem B45346351 : Blo 111784 45346351 := bstep (se 1 (by rfl) ⟨34009763, by rfl⟩ : syracuseStep 45346351 = 68019527) B68019527
theorem B980819 : Blo 111784 980819 := bstep (se 1 (by rfl) ⟨735614, by rfl⟩ : syracuseStep 980819 = 1471229) B1471229
theorem B3964697 : Blo 111784 3964697 := bstep (se 2 (by rfl) ⟨1486761, by rfl⟩ : syracuseStep 3964697 = 2973523) B2973523
theorem B2786375 : Blo 111784 2786375 := bstep (se 1 (by rfl) ⟨2089781, by rfl⟩ : syracuseStep 2786375 = 4179563) B4179563
theorem B296617 : Blo 111784 296617 := bstep (se 2 (by rfl) ⟨111231, by rfl⟩ : syracuseStep 296617 = 222463) B222463
theorem B60461801 : Blo 111784 60461801 := bstep (se 2 (by rfl) ⟨22673175, by rfl⟩ : syracuseStep 60461801 = 45346351) B45346351
theorem B169199 : Blo 111784 169199 := bstep (se 1 (by rfl) ⟨126899, by rfl⟩ : syracuseStep 169199 = 253799) B253799
theorem B2498921 : Blo 111784 2498921 := bstep (se 2 (by rfl) ⟨937095, by rfl⟩ : syracuseStep 2498921 = 1874191) B1874191
theorem B310205 : Blo 111784 310205 := bstep (se 3 (by rfl) ⟨58163, by rfl⟩ : syracuseStep 310205 = 116327) B116327
theorem B113727 : Blo 111784 113727 := bstep (se 1 (by rfl) ⟨85295, by rfl⟩ : syracuseStep 113727 = 170591) B170591
theorem B2643131 : Blo 111784 2643131 := bstep (se 1 (by rfl) ⟨1982348, by rfl⟩ : syracuseStep 2643131 = 3964697) B3964697
theorem B284735 : Blo 111784 284735 := bstep (se 1 (by rfl) ⟨213551, by rfl⟩ : syracuseStep 284735 = 427103) B427103
theorem B321023 : Blo 111784 321023 := bstep (se 1 (by rfl) ⟨240767, by rfl⟩ : syracuseStep 321023 = 481535) B481535
theorem B5074103 : Blo 111784 5074103 := bstep (se 1 (by rfl) ⟨3805577, by rfl⟩ : syracuseStep 5074103 = 7611155) B7611155
theorem B422131 : Blo 111784 422131 := bstep (se 1 (by rfl) ⟨316598, by rfl⟩ : syracuseStep 422131 = 633197) B633197
theorem B653879 : Blo 111784 653879 := bstep (se 1 (by rfl) ⟨490409, by rfl⟩ : syracuseStep 653879 = 980819) B980819
theorem B395489 : Blo 111784 395489 := bstep (se 2 (by rfl) ⟨148308, by rfl⟩ : syracuseStep 395489 = 296617) B296617
theorem B40307867 : Blo 111784 40307867 := bstep (se 1 (by rfl) ⟨30230900, by rfl⟩ : syracuseStep 40307867 = 60461801) B60461801
theorem B562841 : Blo 111784 562841 := bstep (se 2 (by rfl) ⟨211065, by rfl⟩ : syracuseStep 562841 = 422131) B422131
theorem B1743677 : Blo 111784 1743677 := bstep (se 3 (by rfl) ⟨326939, by rfl⟩ : syracuseStep 1743677 = 653879) B653879
theorem B3382735 : Blo 111784 3382735 := bstep (se 1 (by rfl) ⟨2537051, by rfl⟩ : syracuseStep 3382735 = 5074103) B5074103
theorem B206803 : Blo 111784 206803 := bstep (se 1 (by rfl) ⟨155102, by rfl⟩ : syracuseStep 206803 = 310205) B310205
theorem B112799 : Blo 111784 112799 := bstep (se 1 (by rfl) ⟨84599, by rfl⟩ : syracuseStep 112799 = 169199) B169199
theorem B214015 : Blo 111784 214015 := bstep (se 1 (by rfl) ⟨160511, by rfl⟩ : syracuseStep 214015 = 321023) B321023
theorem B1857583 : Blo 111784 1857583 := bstep (se 1 (by rfl) ⟨1393187, by rfl⟩ : syracuseStep 1857583 = 2786375) B2786375
theorem B1762087 : Blo 111784 1762087 := bstep (se 1 (by rfl) ⟨1321565, by rfl⟩ : syracuseStep 1762087 = 2643131) B2643131
theorem B189823 : Blo 111784 189823 := bstep (se 1 (by rfl) ⟨142367, by rfl⟩ : syracuseStep 189823 = 284735) B284735
theorem B1665947 : Blo 111784 1665947 := bstep (se 1 (by rfl) ⟨1249460, by rfl⟩ : syracuseStep 1665947 = 2498921) B2498921
theorem B26871911 : Blo 111784 26871911 := bstep (se 1 (by rfl) ⟨20153933, by rfl⟩ : syracuseStep 26871911 = 40307867) B40307867
theorem B1054637 : Blo 111784 1054637 := bstep (se 3 (by rfl) ⟨197744, by rfl⟩ : syracuseStep 1054637 = 395489) B395489
theorem B275737 : Blo 111784 275737 := bstep (se 2 (by rfl) ⟨103401, by rfl⟩ : syracuseStep 275737 = 206803) B206803
theorem B375227 : Blo 111784 375227 := bstep (se 1 (by rfl) ⟨281420, by rfl⟩ : syracuseStep 375227 = 562841) B562841
theorem B1162451 : Blo 111784 1162451 := bstep (se 1 (by rfl) ⟨871838, by rfl⟩ : syracuseStep 1162451 = 1743677) B1743677
theorem B2476777 : Blo 111784 2476777 := bstep (se 2 (by rfl) ⟨928791, by rfl⟩ : syracuseStep 2476777 = 1857583) B1857583
theorem B4510313 : Blo 111784 4510313 := bstep (se 2 (by rfl) ⟨1691367, by rfl⟩ : syracuseStep 4510313 = 3382735) B3382735
theorem B2349449 : Blo 111784 2349449 := bstep (se 2 (by rfl) ⟨881043, by rfl⟩ : syracuseStep 2349449 = 1762087) B1762087
theorem B285353 : Blo 111784 285353 := bstep (se 2 (by rfl) ⟨107007, by rfl⟩ : syracuseStep 285353 = 214015) B214015
theorem B253097 : Blo 111784 253097 := bstep (se 2 (by rfl) ⟨94911, by rfl⟩ : syracuseStep 253097 = 189823) B189823
theorem B1110631 : Blo 111784 1110631 := bstep (se 1 (by rfl) ⟨832973, by rfl⟩ : syracuseStep 1110631 = 1665947) B1665947
theorem B168731 : Blo 111784 168731 := bstep (se 1 (by rfl) ⟨126548, by rfl⟩ : syracuseStep 168731 = 253097) B253097
theorem B1480841 : Blo 111784 1480841 := bstep (se 2 (by rfl) ⟨555315, by rfl⟩ : syracuseStep 1480841 = 1110631) B1110631
theorem B367649 : Blo 111784 367649 := bstep (se 2 (by rfl) ⟨137868, by rfl⟩ : syracuseStep 367649 = 275737) B275737
theorem B703091 : Blo 111784 703091 := bstep (se 1 (by rfl) ⟨527318, by rfl⟩ : syracuseStep 703091 = 1054637) B1054637
theorem B3099869 : Blo 111784 3099869 := bstep (se 3 (by rfl) ⟨581225, by rfl⟩ : syracuseStep 3099869 = 1162451) B1162451
theorem B250151 : Blo 111784 250151 := bstep (se 1 (by rfl) ⟨187613, by rfl⟩ : syracuseStep 250151 = 375227) B375227
theorem B17914607 : Blo 111784 17914607 := bstep (se 1 (by rfl) ⟨13435955, by rfl⟩ : syracuseStep 17914607 = 26871911) B26871911
theorem B3006875 : Blo 111784 3006875 := bstep (se 1 (by rfl) ⟨2255156, by rfl⟩ : syracuseStep 3006875 = 4510313) B4510313
theorem B3302369 : Blo 111784 3302369 := bstep (se 2 (by rfl) ⟨1238388, by rfl⟩ : syracuseStep 3302369 = 2476777) B2476777
theorem B1566299 : Blo 111784 1566299 := bstep (se 1 (by rfl) ⟨1174724, by rfl⟩ : syracuseStep 1566299 = 2349449) B2349449
theorem B190235 : Blo 111784 190235 := bstep (se 1 (by rfl) ⟨142676, by rfl⟩ : syracuseStep 190235 = 285353) B285353
theorem B2066579 : Blo 111784 2066579 := bstep (se 1 (by rfl) ⟨1549934, by rfl⟩ : syracuseStep 2066579 = 3099869) B3099869
theorem B987227 : Blo 111784 987227 := bstep (se 1 (by rfl) ⟨740420, by rfl⟩ : syracuseStep 987227 = 1480841) B1480841
theorem B2004583 : Blo 111784 2004583 := bstep (se 1 (by rfl) ⟨1503437, by rfl⟩ : syracuseStep 2004583 = 3006875) B3006875
theorem B2201579 : Blo 111784 2201579 := bstep (se 1 (by rfl) ⟨1651184, by rfl⟩ : syracuseStep 2201579 = 3302369) B3302369
theorem B1874909 : Blo 111784 1874909 := bstep (se 3 (by rfl) ⟨351545, by rfl⟩ : syracuseStep 1874909 = 703091) B703091
theorem B2668277 : Blo 111784 2668277 := bstep (se 5 (by rfl) ⟨125075, by rfl⟩ : syracuseStep 2668277 = 250151) B250151
theorem B112487 : Blo 111784 112487 := bstep (se 1 (by rfl) ⟨84365, by rfl⟩ : syracuseStep 112487 = 168731) B168731
theorem B11943071 : Blo 111784 11943071 := bstep (se 1 (by rfl) ⟨8957303, by rfl⟩ : syracuseStep 11943071 = 17914607) B17914607
theorem B245099 : Blo 111784 245099 := bstep (se 1 (by rfl) ⟨183824, by rfl⟩ : syracuseStep 245099 = 367649) B367649
theorem B1044199 : Blo 111784 1044199 := bstep (se 1 (by rfl) ⟨783149, by rfl⟩ : syracuseStep 1044199 = 1566299) B1566299
theorem B126823 : Blo 111784 126823 := bstep (se 1 (by rfl) ⟨95117, by rfl⟩ : syracuseStep 126823 = 190235) B190235
theorem B1377719 : Blo 111784 1377719 := bstep (se 1 (by rfl) ⟨1033289, by rfl⟩ : syracuseStep 1377719 = 2066579) B2066579
theorem B658151 : Blo 111784 658151 := bstep (se 1 (by rfl) ⟨493613, by rfl⟩ : syracuseStep 658151 = 987227) B987227
theorem B1249939 : Blo 111784 1249939 := bstep (se 1 (by rfl) ⟨937454, by rfl⟩ : syracuseStep 1249939 = 1874909) B1874909
theorem B169097 : Blo 111784 169097 := bstep (se 2 (by rfl) ⟨63411, by rfl⟩ : syracuseStep 169097 = 126823) B126823
theorem B1778851 : Blo 111784 1778851 := bstep (se 1 (by rfl) ⟨1334138, by rfl⟩ : syracuseStep 1778851 = 2668277) B2668277
theorem B1392265 : Blo 111784 1392265 := bstep (se 2 (by rfl) ⟨522099, by rfl⟩ : syracuseStep 1392265 = 1044199) B1044199
theorem B2672777 : Blo 111784 2672777 := bstep (se 2 (by rfl) ⟨1002291, by rfl⟩ : syracuseStep 2672777 = 2004583) B2004583
theorem B1467719 : Blo 111784 1467719 := bstep (se 1 (by rfl) ⟨1100789, by rfl⟩ : syracuseStep 1467719 = 2201579) B2201579
theorem B7962047 : Blo 111784 7962047 := bstep (se 1 (by rfl) ⟨5971535, by rfl⟩ : syracuseStep 7962047 = 11943071) B11943071
theorem B163399 : Blo 111784 163399 := bstep (se 1 (by rfl) ⟨122549, by rfl⟩ : syracuseStep 163399 = 245099) B245099
theorem B918479 : Blo 111784 918479 := bstep (se 1 (by rfl) ⟨688859, by rfl⟩ : syracuseStep 918479 = 1377719) B1377719
theorem B1781851 : Blo 111784 1781851 := bstep (se 1 (by rfl) ⟨1336388, by rfl⟩ : syracuseStep 1781851 = 2672777) B2672777
theorem B2371801 : Blo 111784 2371801 := bstep (se 2 (by rfl) ⟨889425, by rfl⟩ : syracuseStep 2371801 = 1778851) B1778851
theorem B438767 : Blo 111784 438767 := bstep (se 1 (by rfl) ⟨329075, by rfl⟩ : syracuseStep 438767 = 658151) B658151
theorem B112731 : Blo 111784 112731 := bstep (se 1 (by rfl) ⟨84548, by rfl⟩ : syracuseStep 112731 = 169097) B169097
theorem B217865 : Blo 111784 217865 := bstep (se 2 (by rfl) ⟨81699, by rfl⟩ : syracuseStep 217865 = 163399) B163399
theorem B1856353 : Blo 111784 1856353 := bstep (se 2 (by rfl) ⟨696132, by rfl⟩ : syracuseStep 1856353 = 1392265) B1392265
theorem B1666585 : Blo 111784 1666585 := bstep (se 2 (by rfl) ⟨624969, by rfl⟩ : syracuseStep 1666585 = 1249939) B1249939
theorem B978479 : Blo 111784 978479 := bstep (se 1 (by rfl) ⟨733859, by rfl⟩ : syracuseStep 978479 = 1467719) B1467719
theorem B5308031 : Blo 111784 5308031 := bstep (se 1 (by rfl) ⟨3981023, by rfl⟩ : syracuseStep 5308031 = 7962047) B7962047
theorem B145243 : Blo 111784 145243 := bstep (se 1 (by rfl) ⟨108932, by rfl⟩ : syracuseStep 145243 = 217865) B217865
theorem B2375801 : Blo 111784 2375801 := bstep (se 2 (by rfl) ⟨890925, by rfl⟩ : syracuseStep 2375801 = 1781851) B1781851
theorem B3162401 : Blo 111784 3162401 := bstep (se 2 (by rfl) ⟨1185900, by rfl⟩ : syracuseStep 3162401 = 2371801) B2371801
theorem B2475137 : Blo 111784 2475137 := bstep (se 2 (by rfl) ⟨928176, by rfl⟩ : syracuseStep 2475137 = 1856353) B1856353
theorem B612319 : Blo 111784 612319 := bstep (se 1 (by rfl) ⟨459239, by rfl⟩ : syracuseStep 612319 = 918479) B918479
theorem B2222113 : Blo 111784 2222113 := bstep (se 2 (by rfl) ⟨833292, by rfl⟩ : syracuseStep 2222113 = 1666585) B1666585
theorem B652319 : Blo 111784 652319 := bstep (se 1 (by rfl) ⟨489239, by rfl⟩ : syracuseStep 652319 = 978479) B978479
theorem B292511 : Blo 111784 292511 := bstep (se 1 (by rfl) ⟨219383, by rfl⟩ : syracuseStep 292511 = 438767) B438767
theorem B3538687 : Blo 111784 3538687 := bstep (se 1 (by rfl) ⟨2654015, by rfl⟩ : syracuseStep 3538687 = 5308031) B5308031
theorem B434879 : Blo 111784 434879 := bstep (se 1 (by rfl) ⟨326159, by rfl⟩ : syracuseStep 434879 = 652319) B652319
theorem B1583867 : Blo 111784 1583867 := bstep (se 1 (by rfl) ⟨1187900, by rfl⟩ : syracuseStep 1583867 = 2375801) B2375801
theorem B2108267 : Blo 111784 2108267 := bstep (se 1 (by rfl) ⟨1581200, by rfl⟩ : syracuseStep 2108267 = 3162401) B3162401
theorem B1650091 : Blo 111784 1650091 := bstep (se 1 (by rfl) ⟨1237568, by rfl⟩ : syracuseStep 1650091 = 2475137) B2475137
theorem B2962817 : Blo 111784 2962817 := bstep (se 2 (by rfl) ⟨1111056, by rfl⟩ : syracuseStep 2962817 = 2222113) B2222113
theorem B193657 : Blo 111784 193657 := bstep (se 2 (by rfl) ⟨72621, by rfl⟩ : syracuseStep 193657 = 145243) B145243
theorem B816425 : Blo 111784 816425 := bstep (se 2 (by rfl) ⟨306159, by rfl⟩ : syracuseStep 816425 = 612319) B612319
theorem B195007 : Blo 111784 195007 := bstep (se 1 (by rfl) ⟨146255, by rfl⟩ : syracuseStep 195007 = 292511) B292511
theorem B4718249 : Blo 111784 4718249 := bstep (se 2 (by rfl) ⟨1769343, by rfl⟩ : syracuseStep 4718249 = 3538687) B3538687
theorem B2200121 : Blo 111784 2200121 := bstep (se 2 (by rfl) ⟨825045, by rfl⟩ : syracuseStep 2200121 = 1650091) B1650091
theorem B1055911 : Blo 111784 1055911 := bstep (se 1 (by rfl) ⟨791933, by rfl⟩ : syracuseStep 1055911 = 1583867) B1583867
theorem B1975211 : Blo 111784 1975211 := bstep (se 1 (by rfl) ⟨1481408, by rfl⟩ : syracuseStep 1975211 = 2962817) B2962817
theorem B544283 : Blo 111784 544283 := bstep (se 1 (by rfl) ⟨408212, by rfl⟩ : syracuseStep 544283 = 816425) B816425
theorem B289919 : Blo 111784 289919 := bstep (se 1 (by rfl) ⟨217439, by rfl⟩ : syracuseStep 289919 = 434879) B434879
theorem B258209 : Blo 111784 258209 := bstep (se 2 (by rfl) ⟨96828, by rfl⟩ : syracuseStep 258209 = 193657) B193657
theorem B1405511 : Blo 111784 1405511 := bstep (se 1 (by rfl) ⟨1054133, by rfl⟩ : syracuseStep 1405511 = 2108267) B2108267
theorem B260009 : Blo 111784 260009 := bstep (se 2 (by rfl) ⟨97503, by rfl⟩ : syracuseStep 260009 = 195007) B195007
theorem B3145499 : Blo 111784 3145499 := bstep (se 1 (by rfl) ⟨2359124, by rfl⟩ : syracuseStep 3145499 = 4718249) B4718249
theorem B362855 : Blo 111784 362855 := bstep (se 1 (by rfl) ⟨272141, by rfl⟩ : syracuseStep 362855 = 544283) B544283
theorem B1316807 : Blo 111784 1316807 := bstep (se 1 (by rfl) ⟨987605, by rfl⟩ : syracuseStep 1316807 = 1975211) B1975211
theorem B172139 : Blo 111784 172139 := bstep (se 1 (by rfl) ⟨129104, by rfl⟩ : syracuseStep 172139 = 258209) B258209
theorem B173339 : Blo 111784 173339 := bstep (se 1 (by rfl) ⟨130004, by rfl⟩ : syracuseStep 173339 = 260009) B260009
theorem B937007 : Blo 111784 937007 := bstep (se 1 (by rfl) ⟨702755, by rfl⟩ : syracuseStep 937007 = 1405511) B1405511
theorem B1466747 : Blo 111784 1466747 := bstep (se 1 (by rfl) ⟨1100060, by rfl⟩ : syracuseStep 1466747 = 2200121) B2200121
theorem B193279 : Blo 111784 193279 := bstep (se 1 (by rfl) ⟨144959, by rfl⟩ : syracuseStep 193279 = 289919) B289919
theorem B1407881 : Blo 111784 1407881 := bstep (se 2 (by rfl) ⟨527955, by rfl⟩ : syracuseStep 1407881 = 1055911) B1055911
theorem B2096999 : Blo 111784 2096999 := bstep (se 1 (by rfl) ⟨1572749, by rfl⟩ : syracuseStep 2096999 = 3145499) B3145499
theorem B624671 : Blo 111784 624671 := bstep (se 1 (by rfl) ⟨468503, by rfl⟩ : syracuseStep 624671 = 937007) B937007
theorem B241903 : Blo 111784 241903 := bstep (se 1 (by rfl) ⟨181427, by rfl⟩ : syracuseStep 241903 = 362855) B362855
theorem B114759 : Blo 111784 114759 := bstep (se 1 (by rfl) ⟨86069, by rfl⟩ : syracuseStep 114759 = 172139) B172139
theorem B115559 : Blo 111784 115559 := bstep (se 1 (by rfl) ⟨86669, by rfl⟩ : syracuseStep 115559 = 173339) B173339
theorem B3754349 : Blo 111784 3754349 := bstep (se 3 (by rfl) ⟨703940, by rfl⟩ : syracuseStep 3754349 = 1407881) B1407881
theorem B1397999 : Blo 111784 1397999 := bstep (se 1 (by rfl) ⟨1048499, by rfl⟩ : syracuseStep 1397999 = 2096999) B2096999
theorem B877871 : Blo 111784 877871 := bstep (se 1 (by rfl) ⟨658403, by rfl⟩ : syracuseStep 877871 = 1316807) B1316807
theorem B977831 : Blo 111784 977831 := bstep (se 1 (by rfl) ⟨733373, by rfl⟩ : syracuseStep 977831 = 1466747) B1466747
theorem B257705 : Blo 111784 257705 := bstep (se 2 (by rfl) ⟨96639, by rfl⟩ : syracuseStep 257705 = 193279) B193279
theorem B171803 : Blo 111784 171803 := bstep (se 1 (by rfl) ⟨128852, by rfl⟩ : syracuseStep 171803 = 257705) B257705
theorem B2502899 : Blo 111784 2502899 := bstep (se 1 (by rfl) ⟨1877174, by rfl⟩ : syracuseStep 2502899 = 3754349) B3754349
theorem B931999 : Blo 111784 931999 := bstep (se 1 (by rfl) ⟨698999, by rfl⟩ : syracuseStep 931999 = 1397999) B1397999
theorem B416447 : Blo 111784 416447 := bstep (se 1 (by rfl) ⟨312335, by rfl⟩ : syracuseStep 416447 = 624671) B624671
theorem B322537 : Blo 111784 322537 := bstep (se 2 (by rfl) ⟨120951, by rfl⟩ : syracuseStep 322537 = 241903) B241903
theorem B585247 : Blo 111784 585247 := bstep (se 1 (by rfl) ⟨438935, by rfl⟩ : syracuseStep 585247 = 877871) B877871
theorem B651887 : Blo 111784 651887 := bstep (se 1 (by rfl) ⟨488915, by rfl⟩ : syracuseStep 651887 = 977831) B977831
theorem B430049 : Blo 111784 430049 := bstep (se 2 (by rfl) ⟨161268, by rfl⟩ : syracuseStep 430049 = 322537) B322537
theorem B434591 : Blo 111784 434591 := bstep (se 1 (by rfl) ⟨325943, by rfl⟩ : syracuseStep 434591 = 651887) B651887
theorem B277631 : Blo 111784 277631 := bstep (se 1 (by rfl) ⟨208223, by rfl⟩ : syracuseStep 277631 = 416447) B416447
theorem B114535 : Blo 111784 114535 := bstep (se 1 (by rfl) ⟨85901, by rfl⟩ : syracuseStep 114535 = 171803) B171803
theorem B780329 : Blo 111784 780329 := bstep (se 2 (by rfl) ⟨292623, by rfl⟩ : syracuseStep 780329 = 585247) B585247
theorem B1668599 : Blo 111784 1668599 := bstep (se 1 (by rfl) ⟨1251449, by rfl⟩ : syracuseStep 1668599 = 2502899) B2502899
theorem B1242665 : Blo 111784 1242665 := bstep (se 2 (by rfl) ⟨465999, by rfl⟩ : syracuseStep 1242665 = 931999) B931999
theorem B828443 : Blo 111784 828443 := bstep (se 1 (by rfl) ⟨621332, by rfl⟩ : syracuseStep 828443 = 1242665) B1242665
theorem B185087 : Blo 111784 185087 := bstep (se 1 (by rfl) ⟨138815, by rfl⟩ : syracuseStep 185087 = 277631) B277631
theorem B286699 : Blo 111784 286699 := bstep (se 1 (by rfl) ⟨215024, by rfl⟩ : syracuseStep 286699 = 430049) B430049
theorem B289727 : Blo 111784 289727 := bstep (se 1 (by rfl) ⟨217295, by rfl⟩ : syracuseStep 289727 = 434591) B434591
theorem B520219 : Blo 111784 520219 := bstep (se 1 (by rfl) ⟨390164, by rfl⟩ : syracuseStep 520219 = 780329) B780329
theorem B1112399 : Blo 111784 1112399 := bstep (se 1 (by rfl) ⟨834299, by rfl⟩ : syracuseStep 1112399 = 1668599) B1668599
theorem B693625 : Blo 111784 693625 := bstep (se 2 (by rfl) ⟨260109, by rfl⟩ : syracuseStep 693625 = 520219) B520219
theorem B741599 : Blo 111784 741599 := bstep (se 1 (by rfl) ⟨556199, by rfl⟩ : syracuseStep 741599 = 1112399) B1112399
theorem B382265 : Blo 111784 382265 := bstep (se 2 (by rfl) ⟨143349, by rfl⟩ : syracuseStep 382265 = 286699) B286699
theorem B123391 : Blo 111784 123391 := bstep (se 1 (by rfl) ⟨92543, by rfl⟩ : syracuseStep 123391 = 185087) B185087
theorem B552295 : Blo 111784 552295 := bstep (se 1 (by rfl) ⟨414221, by rfl⟩ : syracuseStep 552295 = 828443) B828443
theorem B193151 : Blo 111784 193151 := bstep (se 1 (by rfl) ⟨144863, by rfl⟩ : syracuseStep 193151 = 289727) B289727
theorem B164521 : Blo 111784 164521 := bstep (se 2 (by rfl) ⟨61695, by rfl⟩ : syracuseStep 164521 = 123391) B123391
theorem B494399 : Blo 111784 494399 := bstep (se 1 (by rfl) ⟨370799, by rfl⟩ : syracuseStep 494399 = 741599) B741599
theorem B924833 : Blo 111784 924833 := bstep (se 2 (by rfl) ⟨346812, by rfl⟩ : syracuseStep 924833 = 693625) B693625
theorem B736393 : Blo 111784 736393 := bstep (se 2 (by rfl) ⟨276147, by rfl⟩ : syracuseStep 736393 = 552295) B552295
theorem B254843 : Blo 111784 254843 := bstep (se 1 (by rfl) ⟨191132, by rfl⟩ : syracuseStep 254843 = 382265) B382265
theorem B128767 : Blo 111784 128767 := bstep (se 1 (by rfl) ⟨96575, by rfl⟩ : syracuseStep 128767 = 193151) B193151
theorem B329599 : Blo 111784 329599 := bstep (se 1 (by rfl) ⟨247199, by rfl⟩ : syracuseStep 329599 = 494399) B494399
theorem B169895 : Blo 111784 169895 := bstep (se 1 (by rfl) ⟨127421, by rfl⟩ : syracuseStep 169895 = 254843) B254843
theorem B171689 : Blo 111784 171689 := bstep (se 2 (by rfl) ⟨64383, by rfl⟩ : syracuseStep 171689 = 128767) B128767
theorem B219361 : Blo 111784 219361 := bstep (se 2 (by rfl) ⟨82260, by rfl⟩ : syracuseStep 219361 = 164521) B164521
theorem B616555 : Blo 111784 616555 := bstep (se 1 (by rfl) ⟨462416, by rfl⟩ : syracuseStep 616555 = 924833) B924833
theorem B981857 : Blo 111784 981857 := bstep (se 2 (by rfl) ⟨368196, by rfl⟩ : syracuseStep 981857 = 736393) B736393
theorem B822073 : Blo 111784 822073 := bstep (se 2 (by rfl) ⟨308277, by rfl⟩ : syracuseStep 822073 = 616555) B616555
theorem B439465 : Blo 111784 439465 := bstep (se 2 (by rfl) ⟨164799, by rfl⟩ : syracuseStep 439465 = 329599) B329599
theorem B113263 : Blo 111784 113263 := bstep (se 1 (by rfl) ⟨84947, by rfl⟩ : syracuseStep 113263 = 169895) B169895
theorem B114459 : Blo 111784 114459 := bstep (se 1 (by rfl) ⟨85844, by rfl⟩ : syracuseStep 114459 = 171689) B171689
theorem B292481 : Blo 111784 292481 := bstep (se 2 (by rfl) ⟨109680, by rfl⟩ : syracuseStep 292481 = 219361) B219361
theorem B654571 : Blo 111784 654571 := bstep (se 1 (by rfl) ⟨490928, by rfl⟩ : syracuseStep 654571 = 981857) B981857
theorem B1096097 : Blo 111784 1096097 := bstep (se 2 (by rfl) ⟨411036, by rfl⟩ : syracuseStep 1096097 = 822073) B822073
theorem B3491045 : Blo 111784 3491045 := bstep (se 4 (by rfl) ⟨327285, by rfl⟩ : syracuseStep 3491045 = 654571) B654571
theorem B585953 : Blo 111784 585953 := bstep (se 2 (by rfl) ⟨219732, by rfl⟩ : syracuseStep 585953 = 439465) B439465
theorem B194987 : Blo 111784 194987 := bstep (se 1 (by rfl) ⟨146240, by rfl⟩ : syracuseStep 194987 = 292481) B292481
theorem B2327363 : Blo 111784 2327363 := bstep (se 1 (by rfl) ⟨1745522, by rfl⟩ : syracuseStep 2327363 = 3491045) B3491045
theorem B11691701 : Blo 111784 11691701 := bstep (se 5 (by rfl) ⟨548048, by rfl⟩ : syracuseStep 11691701 = 1096097) B1096097
theorem B390635 : Blo 111784 390635 := bstep (se 1 (by rfl) ⟨292976, by rfl⟩ : syracuseStep 390635 = 585953) B585953
theorem B129991 : Blo 111784 129991 := bstep (se 1 (by rfl) ⟨97493, by rfl⟩ : syracuseStep 129991 = 194987) B194987
theorem B173321 : Blo 111784 173321 := bstep (se 2 (by rfl) ⟨64995, by rfl⟩ : syracuseStep 173321 = 129991) B129991
theorem B1551575 : Blo 111784 1551575 := bstep (se 1 (by rfl) ⟨1163681, by rfl⟩ : syracuseStep 1551575 = 2327363) B2327363
theorem B7794467 : Blo 111784 7794467 := bstep (se 1 (by rfl) ⟨5845850, by rfl⟩ : syracuseStep 7794467 = 11691701) B11691701
theorem B260423 : Blo 111784 260423 := bstep (se 1 (by rfl) ⟨195317, by rfl⟩ : syracuseStep 260423 = 390635) B390635
theorem B173615 : Blo 111784 173615 := bstep (se 1 (by rfl) ⟨130211, by rfl⟩ : syracuseStep 173615 = 260423) B260423
theorem B115547 : Blo 111784 115547 := bstep (se 1 (by rfl) ⟨86660, by rfl⟩ : syracuseStep 115547 = 173321) B173321
theorem B1034383 : Blo 111784 1034383 := bstep (se 1 (by rfl) ⟨775787, by rfl⟩ : syracuseStep 1034383 = 1551575) B1551575
theorem B5196311 : Blo 111784 5196311 := bstep (se 1 (by rfl) ⟨3897233, by rfl⟩ : syracuseStep 5196311 = 7794467) B7794467
theorem B1379177 : Blo 111784 1379177 := bstep (se 2 (by rfl) ⟨517191, by rfl⟩ : syracuseStep 1379177 = 1034383) B1034383
theorem B115743 : Blo 111784 115743 := bstep (se 1 (by rfl) ⟨86807, by rfl⟩ : syracuseStep 115743 = 173615) B173615
theorem B3464207 : Blo 111784 3464207 := bstep (se 1 (by rfl) ⟨2598155, by rfl⟩ : syracuseStep 3464207 = 5196311) B5196311
theorem B919451 : Blo 111784 919451 := bstep (se 1 (by rfl) ⟨689588, by rfl⟩ : syracuseStep 919451 = 1379177) B1379177
theorem B2309471 : Blo 111784 2309471 := bstep (se 1 (by rfl) ⟨1732103, by rfl⟩ : syracuseStep 2309471 = 3464207) B3464207
theorem B2451869 : Blo 111784 2451869 := bstep (se 3 (by rfl) ⟨459725, by rfl⟩ : syracuseStep 2451869 = 919451) B919451
theorem B1539647 : Blo 111784 1539647 := bstep (se 1 (by rfl) ⟨1154735, by rfl⟩ : syracuseStep 1539647 = 2309471) B2309471
theorem B1026431 : Blo 111784 1026431 := bstep (se 1 (by rfl) ⟨769823, by rfl⟩ : syracuseStep 1026431 = 1539647) B1539647
theorem B1634579 : Blo 111784 1634579 := bstep (se 1 (by rfl) ⟨1225934, by rfl⟩ : syracuseStep 1634579 = 2451869) B2451869
theorem B1089719 : Blo 111784 1089719 := bstep (se 1 (by rfl) ⟨817289, by rfl⟩ : syracuseStep 1089719 = 1634579) B1634579
theorem B684287 : Blo 111784 684287 := bstep (se 1 (by rfl) ⟨513215, by rfl⟩ : syracuseStep 684287 = 1026431) B1026431
theorem B726479 : Blo 111784 726479 := bstep (se 1 (by rfl) ⟨544859, by rfl⟩ : syracuseStep 726479 = 1089719) B1089719
theorem B456191 : Blo 111784 456191 := bstep (se 1 (by rfl) ⟨342143, by rfl⟩ : syracuseStep 456191 = 684287) B684287
theorem B304127 : Blo 111784 304127 := bstep (se 1 (by rfl) ⟨228095, by rfl⟩ : syracuseStep 304127 = 456191) B456191
theorem B484319 : Blo 111784 484319 := bstep (se 1 (by rfl) ⟨363239, by rfl⟩ : syracuseStep 484319 = 726479) B726479
theorem B202751 : Blo 111784 202751 := bstep (se 1 (by rfl) ⟨152063, by rfl⟩ : syracuseStep 202751 = 304127) B304127
theorem B322879 : Blo 111784 322879 := bstep (se 1 (by rfl) ⟨242159, by rfl⟩ : syracuseStep 322879 = 484319) B484319
theorem B135167 : Blo 111784 135167 := bstep (se 1 (by rfl) ⟨101375, by rfl⟩ : syracuseStep 135167 = 202751) B202751
theorem B430505 : Blo 111784 430505 := bstep (se 2 (by rfl) ⟨161439, by rfl⟩ : syracuseStep 430505 = 322879) B322879
theorem B287003 : Blo 111784 287003 := bstep (se 1 (by rfl) ⟨215252, by rfl⟩ : syracuseStep 287003 = 430505) B430505
theorem B360445 : Blo 111784 360445 := bstep (se 3 (by rfl) ⟨67583, by rfl⟩ : syracuseStep 360445 = 135167) B135167
theorem B480593 : Blo 111784 480593 := bstep (se 2 (by rfl) ⟨180222, by rfl⟩ : syracuseStep 480593 = 360445) B360445
theorem B191335 : Blo 111784 191335 := bstep (se 1 (by rfl) ⟨143501, by rfl⟩ : syracuseStep 191335 = 287003) B287003
theorem B1281581 : Blo 111784 1281581 := bstep (se 3 (by rfl) ⟨240296, by rfl⟩ : syracuseStep 1281581 = 480593) B480593
theorem B255113 : Blo 111784 255113 := bstep (se 2 (by rfl) ⟨95667, by rfl⟩ : syracuseStep 255113 = 191335) B191335
theorem B854387 : Blo 111784 854387 := bstep (se 1 (by rfl) ⟨640790, by rfl⟩ : syracuseStep 854387 = 1281581) B1281581
theorem B170075 : Blo 111784 170075 := bstep (se 1 (by rfl) ⟨127556, by rfl⟩ : syracuseStep 170075 = 255113) B255113
theorem B569591 : Blo 111784 569591 := bstep (se 1 (by rfl) ⟨427193, by rfl⟩ : syracuseStep 569591 = 854387) B854387
theorem B113383 : Blo 111784 113383 := bstep (se 1 (by rfl) ⟨85037, by rfl⟩ : syracuseStep 113383 = 170075) B170075
theorem B379727 : Blo 111784 379727 := bstep (se 1 (by rfl) ⟨284795, by rfl⟩ : syracuseStep 379727 = 569591) B569591
theorem B253151 : Blo 111784 253151 := bstep (se 1 (by rfl) ⟨189863, by rfl⟩ : syracuseStep 253151 = 379727) B379727
theorem B168767 : Blo 111784 168767 := bstep (se 1 (by rfl) ⟨126575, by rfl⟩ : syracuseStep 168767 = 253151) B253151
theorem B112511 : Blo 111784 112511 := bstep (se 1 (by rfl) ⟨84383, by rfl⟩ : syracuseStep 112511 = 168767) B168767

theorem C0 (j : ℕ) (h1 : 27946 ≤ j) (h2 : j ≤ 28645) : Blo 111784 (4 * j + 3) := by
  interval_cases j
  · exact B111787
  · exact B111791
  · exact B111795
  · exact B111799
  · exact B111803
  · exact B111807
  · exact B111811
  · exact B111815
  · exact B111819
  · exact B111823
  · exact B111827
  · exact B111831
  · exact B111835
  · exact B111839
  · exact B111843
  · exact B111847
  · exact B111851
  · exact B111855
  · exact B111859
  · exact B111863
  · exact B111867
  · exact B111871
  · exact B111875
  · exact B111879
  · exact B111883
  · exact B111887
  · exact B111891
  · exact B111895
  · exact B111899
  · exact B111903
  · exact B111907
  · exact B111911
  · exact B111915
  · exact B111919
  · exact B111923
  · exact B111927
  · exact B111931
  · exact B111935
  · exact B111939
  · exact B111943
  · exact B111947
  · exact B111951
  · exact B111955
  · exact B111959
  · exact B111963
  · exact B111967
  · exact B111971
  · exact B111975
  · exact B111979
  · exact B111983
  · exact B111987
  · exact B111991
  · exact B111995
  · exact B111999
  · exact B112003
  · exact B112007
  · exact B112011
  · exact B112015
  · exact B112019
  · exact B112023
  · exact B112027
  · exact B112031
  · exact B112035
  · exact B112039
  · exact B112043
  · exact B112047
  · exact B112051
  · exact B112055
  · exact B112059
  · exact B112063
  · exact B112067
  · exact B112071
  · exact B112075
  · exact B112079
  · exact B112083
  · exact B112087
  · exact B112091
  · exact B112095
  · exact B112099
  · exact B112103
  · exact B112107
  · exact B112111
  · exact B112115
  · exact B112119
  · exact B112123
  · exact B112127
  · exact B112131
  · exact B112135
  · exact B112139
  · exact B112143
  · exact B112147
  · exact B112151
  · exact B112155
  · exact B112159
  · exact B112163
  · exact B112167
  · exact B112171
  · exact B112175
  · exact B112179
  · exact B112183
  · exact B112187
  · exact B112191
  · exact B112195
  · exact B112199
  · exact B112203
  · exact B112207
  · exact B112211
  · exact B112215
  · exact B112219
  · exact B112223
  · exact B112227
  · exact B112231
  · exact B112235
  · exact B112239
  · exact B112243
  · exact B112247
  · exact B112251
  · exact B112255
  · exact B112259
  · exact B112263
  · exact B112267
  · exact B112271
  · exact B112275
  · exact B112279
  · exact B112283
  · exact B112287
  · exact B112291
  · exact B112295
  · exact B112299
  · exact B112303
  · exact B112307
  · exact B112311
  · exact B112315
  · exact B112319
  · exact B112323
  · exact B112327
  · exact B112331
  · exact B112335
  · exact B112339
  · exact B112343
  · exact B112347
  · exact B112351
  · exact B112355
  · exact B112359
  · exact B112363
  · exact B112367
  · exact B112371
  · exact B112375
  · exact B112379
  · exact B112383
  · exact B112387
  · exact B112391
  · exact B112395
  · exact B112399
  · exact B112403
  · exact B112407
  · exact B112411
  · exact B112415
  · exact B112419
  · exact B112423
  · exact B112427
  · exact B112431
  · exact B112435
  · exact B112439
  · exact B112443
  · exact B112447
  · exact B112451
  · exact B112455
  · exact B112459
  · exact B112463
  · exact B112467
  · exact B112471
  · exact B112475
  · exact B112479
  · exact B112483
  · exact B112487
  · exact B112491
  · exact B112495
  · exact B112499
  · exact B112503
  · exact B112507
  · exact B112511
  · exact B112515
  · exact B112519
  · exact B112523
  · exact B112527
  · exact B112531
  · exact B112535
  · exact B112539
  · exact B112543
  · exact B112547
  · exact B112551
  · exact B112555
  · exact B112559
  · exact B112563
  · exact B112567
  · exact B112571
  · exact B112575
  · exact B112579
  · exact B112583
  · exact B112587
  · exact B112591
  · exact B112595
  · exact B112599
  · exact B112603
  · exact B112607
  · exact B112611
  · exact B112615
  · exact B112619
  · exact B112623
  · exact B112627
  · exact B112631
  · exact B112635
  · exact B112639
  · exact B112643
  · exact B112647
  · exact B112651
  · exact B112655
  · exact B112659
  · exact B112663
  · exact B112667
  · exact B112671
  · exact B112675
  · exact B112679
  · exact B112683
  · exact B112687
  · exact B112691
  · exact B112695
  · exact B112699
  · exact B112703
  · exact B112707
  · exact B112711
  · exact B112715
  · exact B112719
  · exact B112723
  · exact B112727
  · exact B112731
  · exact B112735
  · exact B112739
  · exact B112743
  · exact B112747
  · exact B112751
  · exact B112755
  · exact B112759
  · exact B112763
  · exact B112767
  · exact B112771
  · exact B112775
  · exact B112779
  · exact B112783
  · exact B112787
  · exact B112791
  · exact B112795
  · exact B112799
  · exact B112803
  · exact B112807
  · exact B112811
  · exact B112815
  · exact B112819
  · exact B112823
  · exact B112827
  · exact B112831
  · exact B112835
  · exact B112839
  · exact B112843
  · exact B112847
  · exact B112851
  · exact B112855
  · exact B112859
  · exact B112863
  · exact B112867
  · exact B112871
  · exact B112875
  · exact B112879
  · exact B112883
  · exact B112887
  · exact B112891
  · exact B112895
  · exact B112899
  · exact B112903
  · exact B112907
  · exact B112911
  · exact B112915
  · exact B112919
  · exact B112923
  · exact B112927
  · exact B112931
  · exact B112935
  · exact B112939
  · exact B112943
  · exact B112947
  · exact B112951
  · exact B112955
  · exact B112959
  · exact B112963
  · exact B112967
  · exact B112971
  · exact B112975
  · exact B112979
  · exact B112983
  · exact B112987
  · exact B112991
  · exact B112995
  · exact B112999
  · exact B113003
  · exact B113007
  · exact B113011
  · exact B113015
  · exact B113019
  · exact B113023
  · exact B113027
  · exact B113031
  · exact B113035
  · exact B113039
  · exact B113043
  · exact B113047
  · exact B113051
  · exact B113055
  · exact B113059
  · exact B113063
  · exact B113067
  · exact B113071
  · exact B113075
  · exact B113079
  · exact B113083
  · exact B113087
  · exact B113091
  · exact B113095
  · exact B113099
  · exact B113103
  · exact B113107
  · exact B113111
  · exact B113115
  · exact B113119
  · exact B113123
  · exact B113127
  · exact B113131
  · exact B113135
  · exact B113139
  · exact B113143
  · exact B113147
  · exact B113151
  · exact B113155
  · exact B113159
  · exact B113163
  · exact B113167
  · exact B113171
  · exact B113175
  · exact B113179
  · exact B113183
  · exact B113187
  · exact B113191
  · exact B113195
  · exact B113199
  · exact B113203
  · exact B113207
  · exact B113211
  · exact B113215
  · exact B113219
  · exact B113223
  · exact B113227
  · exact B113231
  · exact B113235
  · exact B113239
  · exact B113243
  · exact B113247
  · exact B113251
  · exact B113255
  · exact B113259
  · exact B113263
  · exact B113267
  · exact B113271
  · exact B113275
  · exact B113279
  · exact B113283
  · exact B113287
  · exact B113291
  · exact B113295
  · exact B113299
  · exact B113303
  · exact B113307
  · exact B113311
  · exact B113315
  · exact B113319
  · exact B113323
  · exact B113327
  · exact B113331
  · exact B113335
  · exact B113339
  · exact B113343
  · exact B113347
  · exact B113351
  · exact B113355
  · exact B113359
  · exact B113363
  · exact B113367
  · exact B113371
  · exact B113375
  · exact B113379
  · exact B113383
  · exact B113387
  · exact B113391
  · exact B113395
  · exact B113399
  · exact B113403
  · exact B113407
  · exact B113411
  · exact B113415
  · exact B113419
  · exact B113423
  · exact B113427
  · exact B113431
  · exact B113435
  · exact B113439
  · exact B113443
  · exact B113447
  · exact B113451
  · exact B113455
  · exact B113459
  · exact B113463
  · exact B113467
  · exact B113471
  · exact B113475
  · exact B113479
  · exact B113483
  · exact B113487
  · exact B113491
  · exact B113495
  · exact B113499
  · exact B113503
  · exact B113507
  · exact B113511
  · exact B113515
  · exact B113519
  · exact B113523
  · exact B113527
  · exact B113531
  · exact B113535
  · exact B113539
  · exact B113543
  · exact B113547
  · exact B113551
  · exact B113555
  · exact B113559
  · exact B113563
  · exact B113567
  · exact B113571
  · exact B113575
  · exact B113579
  · exact B113583
  · exact B113587
  · exact B113591
  · exact B113595
  · exact B113599
  · exact B113603
  · exact B113607
  · exact B113611
  · exact B113615
  · exact B113619
  · exact B113623
  · exact B113627
  · exact B113631
  · exact B113635
  · exact B113639
  · exact B113643
  · exact B113647
  · exact B113651
  · exact B113655
  · exact B113659
  · exact B113663
  · exact B113667
  · exact B113671
  · exact B113675
  · exact B113679
  · exact B113683
  · exact B113687
  · exact B113691
  · exact B113695
  · exact B113699
  · exact B113703
  · exact B113707
  · exact B113711
  · exact B113715
  · exact B113719
  · exact B113723
  · exact B113727
  · exact B113731
  · exact B113735
  · exact B113739
  · exact B113743
  · exact B113747
  · exact B113751
  · exact B113755
  · exact B113759
  · exact B113763
  · exact B113767
  · exact B113771
  · exact B113775
  · exact B113779
  · exact B113783
  · exact B113787
  · exact B113791
  · exact B113795
  · exact B113799
  · exact B113803
  · exact B113807
  · exact B113811
  · exact B113815
  · exact B113819
  · exact B113823
  · exact B113827
  · exact B113831
  · exact B113835
  · exact B113839
  · exact B113843
  · exact B113847
  · exact B113851
  · exact B113855
  · exact B113859
  · exact B113863
  · exact B113867
  · exact B113871
  · exact B113875
  · exact B113879
  · exact B113883
  · exact B113887
  · exact B113891
  · exact B113895
  · exact B113899
  · exact B113903
  · exact B113907
  · exact B113911
  · exact B113915
  · exact B113919
  · exact B113923
  · exact B113927
  · exact B113931
  · exact B113935
  · exact B113939
  · exact B113943
  · exact B113947
  · exact B113951
  · exact B113955
  · exact B113959
  · exact B113963
  · exact B113967
  · exact B113971
  · exact B113975
  · exact B113979
  · exact B113983
  · exact B113987
  · exact B113991
  · exact B113995
  · exact B113999
  · exact B114003
  · exact B114007
  · exact B114011
  · exact B114015
  · exact B114019
  · exact B114023
  · exact B114027
  · exact B114031
  · exact B114035
  · exact B114039
  · exact B114043
  · exact B114047
  · exact B114051
  · exact B114055
  · exact B114059
  · exact B114063
  · exact B114067
  · exact B114071
  · exact B114075
  · exact B114079
  · exact B114083
  · exact B114087
  · exact B114091
  · exact B114095
  · exact B114099
  · exact B114103
  · exact B114107
  · exact B114111
  · exact B114115
  · exact B114119
  · exact B114123
  · exact B114127
  · exact B114131
  · exact B114135
  · exact B114139
  · exact B114143
  · exact B114147
  · exact B114151
  · exact B114155
  · exact B114159
  · exact B114163
  · exact B114167
  · exact B114171
  · exact B114175
  · exact B114179
  · exact B114183
  · exact B114187
  · exact B114191
  · exact B114195
  · exact B114199
  · exact B114203
  · exact B114207
  · exact B114211
  · exact B114215
  · exact B114219
  · exact B114223
  · exact B114227
  · exact B114231
  · exact B114235
  · exact B114239
  · exact B114243
  · exact B114247
  · exact B114251
  · exact B114255
  · exact B114259
  · exact B114263
  · exact B114267
  · exact B114271
  · exact B114275
  · exact B114279
  · exact B114283
  · exact B114287
  · exact B114291
  · exact B114295
  · exact B114299
  · exact B114303
  · exact B114307
  · exact B114311
  · exact B114315
  · exact B114319
  · exact B114323
  · exact B114327
  · exact B114331
  · exact B114335
  · exact B114339
  · exact B114343
  · exact B114347
  · exact B114351
  · exact B114355
  · exact B114359
  · exact B114363
  · exact B114367
  · exact B114371
  · exact B114375
  · exact B114379
  · exact B114383
  · exact B114387
  · exact B114391
  · exact B114395
  · exact B114399
  · exact B114403
  · exact B114407
  · exact B114411
  · exact B114415
  · exact B114419
  · exact B114423
  · exact B114427
  · exact B114431
  · exact B114435
  · exact B114439
  · exact B114443
  · exact B114447
  · exact B114451
  · exact B114455
  · exact B114459
  · exact B114463
  · exact B114467
  · exact B114471
  · exact B114475
  · exact B114479
  · exact B114483
  · exact B114487
  · exact B114491
  · exact B114495
  · exact B114499
  · exact B114503
  · exact B114507
  · exact B114511
  · exact B114515
  · exact B114519
  · exact B114523
  · exact B114527
  · exact B114531
  · exact B114535
  · exact B114539
  · exact B114543
  · exact B114547
  · exact B114551
  · exact B114555
  · exact B114559
  · exact B114563
  · exact B114567
  · exact B114571
  · exact B114575
  · exact B114579
  · exact B114583

theorem C1 (j : ℕ) (h1 : 28646 ≤ j) (h2 : j ≤ 28945) : Blo 111784 (4 * j + 3) := by
  interval_cases j
  · exact B114587
  · exact B114591
  · exact B114595
  · exact B114599
  · exact B114603
  · exact B114607
  · exact B114611
  · exact B114615
  · exact B114619
  · exact B114623
  · exact B114627
  · exact B114631
  · exact B114635
  · exact B114639
  · exact B114643
  · exact B114647
  · exact B114651
  · exact B114655
  · exact B114659
  · exact B114663
  · exact B114667
  · exact B114671
  · exact B114675
  · exact B114679
  · exact B114683
  · exact B114687
  · exact B114691
  · exact B114695
  · exact B114699
  · exact B114703
  · exact B114707
  · exact B114711
  · exact B114715
  · exact B114719
  · exact B114723
  · exact B114727
  · exact B114731
  · exact B114735
  · exact B114739
  · exact B114743
  · exact B114747
  · exact B114751
  · exact B114755
  · exact B114759
  · exact B114763
  · exact B114767
  · exact B114771
  · exact B114775
  · exact B114779
  · exact B114783
  · exact B114787
  · exact B114791
  · exact B114795
  · exact B114799
  · exact B114803
  · exact B114807
  · exact B114811
  · exact B114815
  · exact B114819
  · exact B114823
  · exact B114827
  · exact B114831
  · exact B114835
  · exact B114839
  · exact B114843
  · exact B114847
  · exact B114851
  · exact B114855
  · exact B114859
  · exact B114863
  · exact B114867
  · exact B114871
  · exact B114875
  · exact B114879
  · exact B114883
  · exact B114887
  · exact B114891
  · exact B114895
  · exact B114899
  · exact B114903
  · exact B114907
  · exact B114911
  · exact B114915
  · exact B114919
  · exact B114923
  · exact B114927
  · exact B114931
  · exact B114935
  · exact B114939
  · exact B114943
  · exact B114947
  · exact B114951
  · exact B114955
  · exact B114959
  · exact B114963
  · exact B114967
  · exact B114971
  · exact B114975
  · exact B114979
  · exact B114983
  · exact B114987
  · exact B114991
  · exact B114995
  · exact B114999
  · exact B115003
  · exact B115007
  · exact B115011
  · exact B115015
  · exact B115019
  · exact B115023
  · exact B115027
  · exact B115031
  · exact B115035
  · exact B115039
  · exact B115043
  · exact B115047
  · exact B115051
  · exact B115055
  · exact B115059
  · exact B115063
  · exact B115067
  · exact B115071
  · exact B115075
  · exact B115079
  · exact B115083
  · exact B115087
  · exact B115091
  · exact B115095
  · exact B115099
  · exact B115103
  · exact B115107
  · exact B115111
  · exact B115115
  · exact B115119
  · exact B115123
  · exact B115127
  · exact B115131
  · exact B115135
  · exact B115139
  · exact B115143
  · exact B115147
  · exact B115151
  · exact B115155
  · exact B115159
  · exact B115163
  · exact B115167
  · exact B115171
  · exact B115175
  · exact B115179
  · exact B115183
  · exact B115187
  · exact B115191
  · exact B115195
  · exact B115199
  · exact B115203
  · exact B115207
  · exact B115211
  · exact B115215
  · exact B115219
  · exact B115223
  · exact B115227
  · exact B115231
  · exact B115235
  · exact B115239
  · exact B115243
  · exact B115247
  · exact B115251
  · exact B115255
  · exact B115259
  · exact B115263
  · exact B115267
  · exact B115271
  · exact B115275
  · exact B115279
  · exact B115283
  · exact B115287
  · exact B115291
  · exact B115295
  · exact B115299
  · exact B115303
  · exact B115307
  · exact B115311
  · exact B115315
  · exact B115319
  · exact B115323
  · exact B115327
  · exact B115331
  · exact B115335
  · exact B115339
  · exact B115343
  · exact B115347
  · exact B115351
  · exact B115355
  · exact B115359
  · exact B115363
  · exact B115367
  · exact B115371
  · exact B115375
  · exact B115379
  · exact B115383
  · exact B115387
  · exact B115391
  · exact B115395
  · exact B115399
  · exact B115403
  · exact B115407
  · exact B115411
  · exact B115415
  · exact B115419
  · exact B115423
  · exact B115427
  · exact B115431
  · exact B115435
  · exact B115439
  · exact B115443
  · exact B115447
  · exact B115451
  · exact B115455
  · exact B115459
  · exact B115463
  · exact B115467
  · exact B115471
  · exact B115475
  · exact B115479
  · exact B115483
  · exact B115487
  · exact B115491
  · exact B115495
  · exact B115499
  · exact B115503
  · exact B115507
  · exact B115511
  · exact B115515
  · exact B115519
  · exact B115523
  · exact B115527
  · exact B115531
  · exact B115535
  · exact B115539
  · exact B115543
  · exact B115547
  · exact B115551
  · exact B115555
  · exact B115559
  · exact B115563
  · exact B115567
  · exact B115571
  · exact B115575
  · exact B115579
  · exact B115583
  · exact B115587
  · exact B115591
  · exact B115595
  · exact B115599
  · exact B115603
  · exact B115607
  · exact B115611
  · exact B115615
  · exact B115619
  · exact B115623
  · exact B115627
  · exact B115631
  · exact B115635
  · exact B115639
  · exact B115643
  · exact B115647
  · exact B115651
  · exact B115655
  · exact B115659
  · exact B115663
  · exact B115667
  · exact B115671
  · exact B115675
  · exact B115679
  · exact B115683
  · exact B115687
  · exact B115691
  · exact B115695
  · exact B115699
  · exact B115703
  · exact B115707
  · exact B115711
  · exact B115715
  · exact B115719
  · exact B115723
  · exact B115727
  · exact B115731
  · exact B115735
  · exact B115739
  · exact B115743
  · exact B115747
  · exact B115751
  · exact B115755
  · exact B115759
  · exact B115763
  · exact B115767
  · exact B115771
  · exact B115775
  · exact B115779
  · exact B115783

theorem solution (m : ℕ) (hlo : 111784 ≤ m) (hhi : m ≤ 115784) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 27946 ≤ j := by omega
    have hj2 : j ≤ 28945 := by omega
    have hb : Blo 111784 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 28646 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
