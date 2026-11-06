-- Prove2me | solution 1 for isBigO_log_mul_add
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:29:31.840202+00:00
-- url     : https://prove2.me/submissions/afd7858e-34e5-47ec-a290-8460295801ad

import Mathlib.Analysis.SumIntegralComparisons

open Real Filter Asymptotics
open scoped Topology

private theorem tendsto_mul_add_atTop_aux {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Tendsto (fun x => a * x + b) atTop atTop :=
  tendsto_atTop_add_const_right _ b (tendsto_id.const_mul_atTop ha)

private theorem log_mul_add_isBigO_log_aux {a : ℝ} (ha : 0 < a) (b : ℝ) :
    (fun x => Real.log (a * x + b)) =O[atTop] Real.log := by
  apply IsBigO.of_bound (2 : ℕ)
  have l2 : ∀ᶠ x : ℝ in atTop, 0 ≤ Real.log x :=
    tendsto_atTop.mp tendsto_log_atTop 0
  have l3 : ∀ᶠ x : ℝ in atTop, 0 ≤ Real.log (a * x + b) :=
    tendsto_atTop.mp (tendsto_log_atTop.comp (tendsto_mul_add_atTop_aux ha b)) 0
  have l5 : ∀ᶠ x : ℝ in atTop, 1 ≤ a * x + b :=
    tendsto_atTop.mp (tendsto_mul_add_atTop_aux ha b) 1
  have l1 : ∀ᶠ x : ℝ in atTop, a * x + b ≤ x ^ 2 := by
    filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (|a| + |b|)] with x hx hab
    have hx0 : 0 ≤ x := zero_le_one.trans hx
    have hxm1 : 0 ≤ x - 1 := sub_nonneg.mpr hx
    calc
      a * x + b ≤ |a| * x + |b| := by
        exact add_le_add (mul_le_mul_of_nonneg_right (le_abs_self a) hx0) (le_abs_self b)
      _ ≤ (|a| + |b|) * x := by
        nlinarith [mul_nonneg (abs_nonneg b) hxm1]
      _ ≤ x * x := mul_le_mul_of_nonneg_right hab hx0
      _ = x ^ 2 := by ring
  filter_upwards [l1, l2, l3, l5] with x l1 l2 l3 l5
  simpa [abs_eq_self.mpr l2, abs_eq_self.mpr l3, Real.log_pow] using
    Real.log_le_log (by linarith) l1

theorem solution {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Real.log =O[atTop] (fun x => Real.log (a * x + b)) := by
  convert (log_mul_add_isBigO_log_aux (b := -b / a) (inv_pos.mpr ha)).comp_tendsto
    (tendsto_mul_add_atTop_aux (b := b) ha) using 1
  · ext x
    simp only [Function.comp_apply]
    congr
    field_simp
    simp
  · rfl
