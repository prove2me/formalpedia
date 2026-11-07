-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f6_original_qscale_killed_exit_factorisation
-- name    : AvramDividend.Classical.avram_p4_f6_original_qscale_killed_exit_factorisation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T09:31:01.641181+00:00
-- url     : https://prove2.me/theorems/a3e423af-cc22-4f33-9e57-3c705b1be360
-- title:
--   Canonical q-scale at reserve one factors through the original killed two-sided exit transform
-- statement:
--   The q-scale W(1) is the q-scale at upper barrier b times the real-valued corrected discounted upper-before-down exit probability, for original Lévy process and 1≤b. Requires the original stochastic q-scale two-sided exit formula, independently of HJB supersolution.
-- source:
--   Exact original killed q-scale identity independent of the generator/HJB supermartingale source. This is the other factor in fe2d23f9; the real-valued factor is bounded by 1 and couples both children on identical X/q/b/initial reserve.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f6_original_qscale_killed_exit_factorisation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) (hWone : 0 < W 1) :
    ∀ b : ℝ, 1 ≤ b →
      W 1 = (twoSidedExitExpectationCorrected X q b 1).toReal * W b := by sorry
