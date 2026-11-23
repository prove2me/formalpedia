-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f11_finite_activity_intrinsic_to_physical_first_exit_ito
-- name    : AvramDividend.Classical.avram_p4_f11_finite_activity_intrinsic_to_physical_first_exit_ito
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T09:39:08.355804+00:00
-- url     : https://prove2.me/theorems/d4439b71-a494-40d2-9a14-028e4b1ee01a
-- title:
--   From original finite-activity intrinsic Gaussian and negative-mark martingales to the physical discounted two-sided stopped Ito-Meyer witness
-- statement:
--   Prove the original mixed Gaussian and negative compound-Poisson physical discounted two-sided first-exit Ito-Meyer martingale and signed HJB generator residual, given the exact global physical Levy decomposition into drift, intrinsic Gaussian martingale, compensated small negative marks and large negative marks with true right-continuous-filtration centring. This isolates the real first-exit weighted Ito limit, with no changed process, HJB, exit clock, or stochastic conclusion assumed.
-- source:
--   Original finite-activity physical source 4d908ed8 and globally Proved intrinsic martingale fields via b213 19339df6.

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

theorem AvramDividend.Classical.avram_p4_f11_finite_activity_intrinsic_to_physical_first_exit_ito
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
