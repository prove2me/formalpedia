-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f7_hjb_finite_reward_to_terminal_real
-- name    : AvramDividend.Classical.avram_p4_f7_hjb_finite_reward_to_terminal_real
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T10:34:52.333967+00:00
-- url     : https://prove2.me/theorems/df0e45ff-ed84-4a95-a45b-1eb1c89ea071
-- title:
--   Original bounded killed upcross reward controlled by stopped discounted terminal potential
-- statement:
--   A purely boundary-contact and nonnegative-integration lemma, independent of the Ito stochastic supermartingale proof: for finite upper and lower original Levy exit clocks and finite n, the killed discounted upcrossing reward w(b) times the expected discount is bounded by the expected discounted stopped reserve potential w(1+X_tau). The jump-free upward overshoot and nonnegative HJB test payoff justify the pathwise comparison; finite capped terminal values justify conversion from ENNReal to real expectations.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f7_hjb_finite_reward_to_terminal_real
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
      w b * (∫⁻ ω,
        if twoSidedExitUpTimeCorrected X (b - 1) ω <
             twoSidedExitDownTimeCorrected X (-1) ω ∧
           twoSidedExitUpTimeCorrected X (b - 1) ω ≤ (n : ℝ≥0∞) then
          ENNReal.ofReal (Real.exp (-(q *
            ENNReal.toReal (twoSidedExitUpTimeCorrected X (b - 1) ω))))
        else 0 ∂P).toReal ≤
      (∫⁻ ω, ENNReal.ofReal
        (Real.exp (-(q * ENNReal.toReal (τ ω))) *
          w (1 + X.X (ENNReal.toNNReal (τ ω)) ω)) ∂P).toReal := by sorry
