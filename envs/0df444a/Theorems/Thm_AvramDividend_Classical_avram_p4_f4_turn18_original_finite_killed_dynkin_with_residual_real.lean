-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f4_turn18_original_finite_killed_dynkin_with_residual_real
-- name    : AvramDividend.Classical.avram_p4_f4_turn18_original_finite_killed_dynkin_with_residual_real
-- status  : Open
-- author  : @WillR
-- created : 2026-11-06T14:26:45.213334+00:00
-- url     : https://prove2.me/theorems/da2f8134-a424-40f6-a527-a6779165e74a
-- title:
--   Original finite killed mixed Lévy Dynkin expectation with real-time residual
-- statement:
--   For the original mixed Gaussian-jump Levy process stopped at the corrected upper, lower and finite-horizon clocks, the discounted terminal payoff is at most its initial value plus the integrable discounted generator residual over the physical real-time cells.
-- source:
--   Original stochastic Ito-Dynkin expectation source for canonical 674b46f8; mathematically independent of deterministic HJB sign.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f4_turn18_original_finite_killed_dynkin_with_residual_real
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ : X.σ ≠ 0)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hTop : C = ⊤) :
    ∀ (b : ℝ) (n : ℕ), 1 ≤ b →
      let τ : Ω → ℝ≥0∞ := fun ω =>
        min (twoSidedExitUpTimeCorrected X (b - 1) ω)
          (min (twoSidedExitDownTimeCorrected X (-1) ω) (n : ℝ≥0∞))
      let R : Ω → ℝ := fun ω =>
        ∫ s : ℝ in Icc (0 : ℝ) (n : ℝ),
          if ENNReal.ofReal s < τ ω ∧
            0 < 1 + X.X (Real.toNNReal s) ω ∧ ENNReal.ofReal (1 + X.X (Real.toNNReal s) ω) < C then
            Real.exp (-(q * s)) *
              (X.generator w (1 + X.X (Real.toNNReal s) ω) - q * w (1 + X.X (Real.toNNReal s) ω))
          else 0
      Integrable R P ∧
        (∫ ω, Real.exp (-(q * ENNReal.toReal (τ ω))) *
          w (1 + X.X (ENNReal.toNNReal (τ ω)) ω) ∂P)
          ≤ w 1 + ∫ ω, R ω ∂P := by sorry
