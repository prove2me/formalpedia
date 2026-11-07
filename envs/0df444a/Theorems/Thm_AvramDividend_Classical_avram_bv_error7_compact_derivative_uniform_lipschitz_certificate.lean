-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_error7_compact_derivative_uniform_lipschitz_certificate
-- name    : AvramDividend.Classical.avram_bv_error7_compact_derivative_uniform_lipschitz_certificate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T09:43:25.055628+00:00
-- url     : https://prove2.me/theorems/de85ec50-0e10-4e41-b96b-5af782202697
-- title:
--   Compact differentiable real function with continuous derivative admits one global Lipschitz and derivative bound
-- statement:
--   If a real-valued w is differentiable at each point of a compact interval Icc a b and its derivative is continuous there, one finite nonnegative real L bounds |deriv w| everywhere on the interval and also makes w L-Lipschitz on that interval. The compactness bound and convex mean-value theorem are exact, and this is the mathematical adapter required for original BV physical-grid C1 Taylor global domination without separate artificial Lipschitz assumptions.
-- source:
--   Compact derivative bound child avram_bv_error7_compact_continuous_deriv_uniform_bound (authoring job 0a1bd324-4a96-4250-b350-d8c477c0962e); pinned Mathlib Convex.norm_image_sub_le_of_norm_deriv_le. Intended downstream source-specific original BV compact C1 adapter and global Taylor error source mass theorem 12895109.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_error7_compact_derivative_uniform_lipschitz_certificate
    (w : ℝ → ℝ) (a b : ℝ)
    (hDiff : ∀ y ∈ Set.Icc a b, DifferentiableAt ℝ w y)
    (hDerCont : ContinuousOn (deriv w) (Set.Icc a b)) :
    ∃ L : ℝ, 0 ≤ L ∧
      (∀ y ∈ Set.Icc a b, ∀ z ∈ Set.Icc a b,
        |w z - w y| ≤ L * |z - y|) ∧
      (∀ y ∈ Set.Icc a b, |deriv w y| ≤ L) := by sorry
