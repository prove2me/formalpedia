-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_positive_cap_C1_gradient_linear_lower_envelope
-- name    : AvramDividend.Classical.avram_wave7_02_original_positive_cap_C1_gradient_linear_lower_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:43:00.781756+00:00
-- url     : https://prove2.me/theorems/f138f64f-f82c-4fdc-943c-d77f480ba88f
-- title:
--   Original positive-cap C1 HJB derivative bounds candidate from below by initial value plus reserve
-- statement:
--   For the original Avram positive-cap C1 candidate with derivative at least one, the adjusted function y↦w(y)-y is monotone on every compact nonnegative reserve interval below the cap. This yields w(y)≥w(0)+y without needing nonnegativity of w(0), and directly controls terminal-value reserve envelopes in the BV stopped verification.
-- source:
--   Pinned Mathlib derivative-monotonicity, applied to the actual C1 candidate minus the identity on the original extended-real cap interior.

import Mathlib
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Defs
open Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_positive_cap_C1_gradient_linear_lower_envelope
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (b : ℝ) (hb : 0 ≤ b) (hbC : ENNReal.ofReal b < C) :
    ∀ y ∈ Icc (0 : ℝ) b, w 0 + y ≤ w y := by sorry
