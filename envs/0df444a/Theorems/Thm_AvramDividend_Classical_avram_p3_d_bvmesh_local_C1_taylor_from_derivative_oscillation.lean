-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_d_bvmesh_local_C1_taylor_from_derivative_oscillation
-- name    : AvramDividend.Classical.avram_p3_d_bvmesh_local_C1_taylor_from_derivative_oscillation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:04:25.9959+00:00
-- url     : https://prove2.me/theorems/f016bd96-af64-41a0-9ccc-54e32a40b200
-- title:
--   Localised first-order C1 Taylor bound from derivative oscillation on the actual mesh segment
-- statement:
--   For an arbitrary oriented real segment a to b, if f is differentiable throughout its undirected closed segment, its derivative is interval integrable, and every derivative value on its undirected half-open segment differs from deriv f a by at most epsilon, then the exact first-order Taylor remainder has absolute value at most epsilon times |b-a|. The assumptions apply only to that segment, permitting strict interior localisation of the original reserve and avoiding any global C1/C2 boundary extension. It directly supplies htaylor to the weighted source-jump grid remainder lemma, once a uniform derivative modulus and source-jump-removed mesh refinement are established.
-- source:
--   Pinned Mathlib intervalIntegral.integral_deriv_eq_sub, integral_sub, integral_const and norm_integral_le_of_norm_le_const types were inspected at 0df444a360eaa60ab8c11dca51a86af692955474. P3-C original frozen-source weighted grid 837277c5 and P3-A original real-sum BV residual continuity 38d9546f motivate applying the bound with a=z_i, b=z_i+c_i. The theorem uses the actual segment and does not assert derivative control at boundary contact.

import Mathlib
open MeasureTheory

theorem AvramDividend.Classical.avram_p3_d_bvmesh_local_C1_taylor_from_derivative_oscillation
    (f : ℝ → ℝ) (a b ε : ℝ)
    (hdiff : ∀ x ∈ Set.uIcc a b, DifferentiableAt ℝ f x)
    (hInt : IntervalIntegrable (deriv f) volume a b)
    (hosc : ∀ x ∈ Set.uIoc a b, |deriv f x - deriv f a| ≤ ε) :
    |f b - f a - deriv f a * (b - a)| ≤ ε * |b - a| := by sorry
