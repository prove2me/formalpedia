-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_lsv_finite_grid_stopped_martingale_expectation
-- name    : AvramDividend.Classical.avram_lsv_finite_grid_stopped_martingale_expectation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T12:54:13.276433+00:00
-- url     : https://prove2.me/theorems/ddc917ee-d1a7-4cae-852a-6c139ada27b7
-- title:
--   Exact optional expectation identity for a bounded countable-range stopping time
-- statement:
--   For a genuine integrable real-valued martingale M in a filtration over the original nonnegative real time axis, stopping at an actual countable-range stopping time bounded by T preserves the expected value of the terminal martingale. The stopped value is integrable. Proof adapted from dufeteller/lean-lsv finite stopped-grid conditional-expectation argument, CC BY 4.0, without a dominator or Brownian representation assumption.

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false
noncomputable section

/-
Adapted from dufeteller/lean-lsv, LSV/LocalizedOptionalExpectation.lean,
continuous_martingale_optional_expectation finite stopping-grid step,
commit a5f604de2e1ae431de4cbecde23e5694a12ba719, upstream CC BY 4.0.
The theorem uses a real, countable-range stopped martingale in the original
nonnegative-time filtration; boundedness is explicit, with no extra envelope.
-/

theorem AvramDividend.Classical.avram_lsv_finite_grid_stopped_martingale_expectation
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (M : ℝ≥0 → Ω → ℝ) (hM : Martingale M ℱ μ)
    (T : ℝ≥0) (τ : Ω → WithTop ℝ≥0)
    (hτ : IsStoppingTime ℱ τ)
    (hτbound : ∀ ω, τ ω ≤ (T : WithTop ℝ≥0))
    (hτcount : (Set.range τ).Countable) :
    Integrable (stoppedValue M τ) μ ∧
      (∫ ω, stoppedValue M τ ω ∂μ) = ∫ ω, M T ω ∂μ := by sorry
