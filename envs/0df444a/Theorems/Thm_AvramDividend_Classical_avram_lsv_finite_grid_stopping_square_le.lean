-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_lsv_finite_grid_stopping_square_le
-- name    : AvramDividend.Classical.avram_lsv_finite_grid_stopping_square_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T12:10:14.871468+00:00
-- url     : https://prove2.me/theorems/67ac86ce-f512-42b2-a288-0b3e516d01db
-- title:
--   L2 contraction of a genuine martingale sampled at an original nonnegative finite-grid stopping time
-- statement:
--   For a real-valued true martingale on the original nonnegative time axis and an actual countable-range stopping time bounded by deterministic t, stoppedValue is square-integrable and its mean square is no larger than the terminal mean square. This faithfully adapts the conditional-expectation contraction argument from lean-lsv, with the finite-grid restriction stated explicitly. There is no imposed running envelope and no assumed Lévy-to-Brownian identification. CC BY 4.0 upstream.

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false
noncomputable section

/-
Adapted from dufeteller/lean-lsv,
LSV/LocalizedStoppingL2Convergence.lean continuous_martingale_stopping_square_le,
and LSV/LocalizedOptionalSamplingL1.lean finite-grid stopped conditional expectation,
commit a5f604de2e1ae431de4cbecde23e5694a12ba719.
Upstream CC BY 4.0, attribution to original source authors.
The stop is restricted to countable range, using Mathlib's finite/countable-grid
conditional sampling identity; the stronger arbitrary-stop limit is not asserted.
-/

theorem AvramDividend.Classical.avram_lsv_finite_grid_stopping_square_le
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (M : ℝ≥0 → Ω → ℝ) (hM : Martingale M ℱ μ)
    (t : ℝ≥0) (hM2 : MemLp (M t) 2 μ)
    (τ : Ω → WithTop ℝ≥0)
    (hτ : IsStoppingTime ℱ τ)
    (hτle : ∀ ω, τ ω ≤ (t : WithTop ℝ≥0))
    (hτcount : (range τ).Countable) :
    MemLp (stoppedValue M τ) 2 μ ∧
      (∫ ω, (stoppedValue M τ ω)^2 ∂μ) ≤
        ∫ ω, (M t ω)^2 ∂μ := by sorry
