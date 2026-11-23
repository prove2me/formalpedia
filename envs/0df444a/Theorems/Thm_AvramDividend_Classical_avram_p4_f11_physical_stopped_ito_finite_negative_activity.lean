-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f11_physical_stopped_ito_finite_negative_activity
-- name    : AvramDividend.Classical.avram_p4_f11_physical_stopped_ito_finite_negative_activity
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T09:21:47.519801+00:00
-- url     : https://prove2.me/theorems/4d908ed8-f4c8-4f3c-bd56-8eb3c56ffca2
-- title:
--   Original positive-horizon mixed Gaussian and negative jump physical stopped Ito-Meyer, finite negative activity
-- statement:
--   Exact original first-up/down bounded stopped discounted physical Ito-Meyer signed generator and centred martingale witness, retaining real finite horizon, nonzero Gaussian, original negative Levy measure and HJB assumptions, with negative jump measure finite total mass. Must prove actual stopped stochastic integral, not assume its mean zero or conclusion.
-- source:
--   Avram original physical stopped Ito source 5c92237d-d818-47a0-bb27-0901d08abe3c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f11_physical_stopped_ito_finite_negative_activity
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
    (hActivity : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hTop : C = ⊤) :
    ∀ (b : ℝ) (n : ℕ), 1 < b → 0 < n →
      let τ : Ω → ℝ≥0∞ := fun ω =>
        min (twoSidedExitUpTimeCorrected X (b - 1) ω)
          (min (twoSidedExitDownTimeCorrected X (-1) ω) (n : ℝ≥0∞))
      ∃ (R M : Ω → ℝ),
        Integrable R P ∧ Integrable M P ∧
        (∀ ω : Ω, R ω =
          (∫ s : ℝ in Icc (0 : ℝ) (n : ℝ),
            if ENNReal.ofReal s < τ ω ∧
              0 < 1 + X.X (Real.toNNReal s) ω ∧
              ENNReal.ofReal (1 + X.X (Real.toNNReal s) ω) < C then
              Real.exp (-(q * s)) *
                (X.generator w (1 + X.X (Real.toNNReal s) ω) -
                  q * w (1 + X.X (Real.toNNReal s) ω))
            else 0)) ∧
        (∫ ω, M ω ∂P) = 0 ∧
        (∀ᵐ ω ∂P,
          Real.exp (-(q * ENNReal.toReal (τ ω))) *
            w (1 + X.X (ENNReal.toNNReal (τ ω)) ω) ≤
          w 1 + M ω + R ω) := by sorry
