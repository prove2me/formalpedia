-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f11_original_interior_stopped_dynkin_signed_expectation
-- name    : AvramDividend.Classical.avram_p4_f11_original_interior_stopped_dynkin_signed_expectation
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T08:57:09.936907+00:00
-- url     : https://prove2.me/theorems/8a4e7f86-fd75-4567-a4e8-b19722af6e9a
-- title:
--   Original positive-horizon killed first-exit physical stopped Dynkin expectation with signed HJB residual
-- statement:
--   For the actual spectrally negative Levy surplus with nonzero Gaussian and negative jump components, original right-continuous first-up/first-down clocks, positive finite horizon n, and the original HJB test w, the signed generator residual on the positive pre-exit clock is integrable, and the expected actual discounted stopped terminal is bounded above by w(1) plus the expected signed generator residual. This isolates the physical stopped Ito-Meyer martingale and localisation proof from the already Proved generator nonpositivity.
-- source:
--   Original Avram theorem 3c77d12f; original signed generator sign already Proved bc6f30da. Genuine physical stopped Ito-Meyer/Dynkin source, not an assumed budget.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f11_original_interior_stopped_dynkin_signed_expectation
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
    ∀ (b : ℝ) (n : ℕ), 1 < b → 0 < n →
      let τ : Ω → ℝ≥0∞ := fun ω =>
        min (twoSidedExitUpTimeCorrected X (b - 1) ω)
          (min (twoSidedExitDownTimeCorrected X (-1) ω) (n : ℝ≥0∞))
      ∃ R : Ω → ℝ,
        Integrable R P ∧
        (∀ ω : Ω, R ω =
          (∫ s : ℝ in Icc (0 : ℝ) (n : ℝ),
            if ENNReal.ofReal s < τ ω ∧
              0 < 1 + X.X (Real.toNNReal s) ω ∧
              ENNReal.ofReal (1 + X.X (Real.toNNReal s) ω) < C then
              Real.exp (-(q * s)) *
                (X.generator w (1 + X.X (Real.toNNReal s) ω) -
                  q * w (1 + X.X (Real.toNNReal s) ω))
            else 0)) ∧
        (∫ ω, Real.exp (-(q * ENNReal.toReal (τ ω))) *
            w (1 + X.X (ENNReal.toNNReal (τ ω)) ω) ∂P) ≤
          w 1 + ∫ ω, R ω ∂P := by sorry
