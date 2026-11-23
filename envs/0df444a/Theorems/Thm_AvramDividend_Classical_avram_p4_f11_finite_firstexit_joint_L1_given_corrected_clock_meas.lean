-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f11_finite_firstexit_joint_L1_given_corrected_clock_meas
-- name    : AvramDividend.Classical.avram_p4_f11_finite_firstexit_joint_L1_given_corrected_clock_meas
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T10:50:09.280282+00:00
-- url     : https://prove2.me/theorems/403df939-525b-48b7-b606-643169a8d167
-- title:
--   Original joint killed generator L1 given measurable actual clipped first-exit clock
-- statement:
--   With the same spectrally negative Levy X, full HJB and finite-activity hypotheses, and the exact corrected upper/lower first-exit finite clock assumed measurable, prove joint absolute time-space integrability of the killed signed discounted generator residual. The true stochastic boundary occupation and generator composition measurability still require proof; clock measurability is separately Proved.
-- source:
--   Original joint L1 source f7b4214b, Measurable corrected finite clock from direct Proved theorem ea026c53.

import Mathlib
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f11_finite_firstexit_joint_L1_given_corrected_clock_meas
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
    (hFields :
      ∃ (R Jsmall M : ℝ≥0 → Ω → ℝ),
        (∀ᵐ ω ∂P, ∀ u : ℝ≥0,
          Tendsto (fun k : ℕ =>
            avram_p4_h_gaussian_intrinsic_truncated_residual X k u ω)
            atTop (𝓝 (R u ω))) ∧
        (∀ᵐ ω ∂P, ∀ u : ℝ≥0,
          Tendsto (fun k : ℕ =>
            avram_p4_h_gaussian_intrinsic_small_band_compensated X k u ω)
            atTop (𝓝 (Jsmall u ω))) ∧
        (∀ u : ℝ≥0, Integrable (R u) P) ∧
        (∀ u : ℝ≥0, Integrable (Jsmall u) P) ∧
        (∀ a b : ℝ≥0, a ≤ b →
          ∀ᵐ ω ∂P, condExp (𝓕.rightCont a) P (R b) ω = R a ω) ∧
        (∀ a b : ℝ≥0, a ≤ b →
          ∀ᵐ ω ∂P, condExp (𝓕.rightCont a) P (Jsmall b) ω = Jsmall a ω) ∧
        (∀ u ω, X.X u ω = (u : ℝ) * X.c + M u ω + Jsmall u ω +
          avram_p4_h_gaussian_intrinsic_large_jump_sum X u ω)
    )
    (hTop : C = ⊤) :
    ∀ (b : ℝ) (n : ℕ), 1 < b → 0 < n →
      Measurable (fun ω : Ω =>
        min (twoSidedExitUpTimeCorrected X (b - 1) ω)
          (min (twoSidedExitDownTimeCorrected X (-1) ω) (n : ℝ≥0∞))) →
      let τ : Ω → ℝ≥0∞ := fun ω =>
        min (twoSidedExitUpTimeCorrected X (b - 1) ω)
          (min (twoSidedExitDownTimeCorrected X (-1) ω) (n : ℝ≥0∞))
      Integrable (fun p : ℝ × Ω =>
            if ENNReal.ofReal p.1 < τ p.2 ∧
              0 < 1 + X.X (Real.toNNReal p.1) p.2 ∧
              ENNReal.ofReal (1 + X.X (Real.toNNReal p.1) p.2) < C then
              Real.exp (-(q * p.1)) *
                (X.generator w (1 + X.X (Real.toNNReal p.1) p.2) -
                  q * w (1 + X.X (Real.toNNReal p.1) p.2))
            else 0)
        (((volume : Measure ℝ).restrict (Icc (0 : ℝ) (n : ℝ))).prod P) := by sorry
