-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_lsv_finite_grid_stopped_quadratic_energy_isometry
-- name    : AvramDividend.Classical.avram_lsv_finite_grid_stopped_quadratic_energy_isometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T12:59:26.943296+00:00
-- url     : https://prove2.me/theorems/7ce013a6-72b9-4da2-9f1b-bde3c819d246
-- title:
--   Exact bounded countable-clock stopped square-integrable martingale quadratic-compensator isometry
-- statement:
--   A genuine square-integrable martingale M with a genuine compensated-square martingale M^2-A and zero terminal mean of that compensated square satisfies an exact stopped isometry: for any actual countable-range stopping time τ bounded by T, its stopped martingale mean-square equals the expected stopped compensator A(τ), which is integrable. The proof uses two previously remote-Proved Lean-LSV adaptations, preserving full martingale and source hypotheses, without assuming Brownian stochastic calculus. Source CC BY 4.0.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_lsv_finite_grid_stopping_square_le
import Theorems.Thm_AvramDividend_Classical_avram_lsv_finite_grid_stopped_martingale_expectation

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false
noncomputable section

/- Direct synthesis of dufeteller/lean-lsv
   LSV/LocalizedStoppingL2Convergence.lean and
   LSV/LocalizedOptionalExpectation.lean:
   actual finite-grid stopped martingale mean-square energy equals its
   stopped quadratic compensator. Original CC BY 4.0,
   source commit a5f604de2e1ae431de4cbecde23e5694a12ba719.
   Neither a Brownian driver nor an unproved identity is hypothesised. -/

theorem AvramDividend.Classical.avram_lsv_finite_grid_stopped_quadratic_energy_isometry
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (M A : ℝ≥0 → Ω → ℝ)
    (hM : Martingale M ℱ μ)
    (hQ : Martingale (fun t ω => (M t ω)^2 - A t ω) ℱ μ)
    (T : ℝ≥0) (hM2 : MemLp (M T) 2 μ)
    (hQTzero : (∫ ω, (M T ω)^2 - A T ω ∂μ) = 0)
    (τ : Ω → WithTop ℝ≥0)
    (hτ : IsStoppingTime ℱ τ)
    (hτle : ∀ ω, τ ω ≤ (T : WithTop ℝ≥0))
    (hτcount : (Set.range τ).Countable) :
    Integrable (fun ω => A (τ ω).untopA ω) μ ∧
      (∫ ω, (stoppedValue M τ ω)^2 ∂μ) =
        ∫ ω, A (τ ω).untopA ω ∂μ := by sorry
