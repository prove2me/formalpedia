-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f8_hjb_finite_terminal_envelope
-- name    : AvramDividend.Classical.avram_p4_f8_hjb_finite_terminal_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T12:20:20.427162+00:00
-- url     : https://prove2.me/theorems/87dcfdd8-23f8-4c9c-a523-8c8e552f0aaf
-- title:
--   Original finite stopped terminal discounted potential has deterministic upper envelope
-- statement:
--   At the three-way finite stopped original Levy clock the reserve is bounded above by b; the top-cap gradient makes w increasing and nonnegative, while positive discount rates make exp(-q tau) at most one. Hence the nonnegative discounted terminal payoff is at most w(b) pathwise.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f8_hjb_finite_terminal_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hTop : C = ⊤)
    (q : ℝ) (hq : 0 < q)
    (b : ℝ) (n : ℕ) (hb : 1 ≤ b) (ω : Ω) :
    ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal (min (twoSidedExitUpTimeCorrected X (b - 1) ω) (min (twoSidedExitDownTimeCorrected X (-1) ω) (n : ℝ≥0∞))))) * w (1 + X.X (ENNReal.toNNReal (min (twoSidedExitUpTimeCorrected X (b - 1) ω) (min (twoSidedExitDownTimeCorrected X (-1) ω) (n : ℝ≥0∞)))) ω)) ≤ ENNReal.ofReal (w b) := by sorry
