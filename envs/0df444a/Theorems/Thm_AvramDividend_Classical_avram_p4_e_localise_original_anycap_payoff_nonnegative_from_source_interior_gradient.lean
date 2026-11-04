-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_anycap_payoff_nonnegative_from_source_interior_gradient
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_anycap_payoff_nonnegative_from_source_interior_gradient
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T15:48:40.315816+00:00
-- url     : https://prove2.me/theorems/79db013c-9a6c-4ff2-9410-2e3bf66ca8a0
-- title:
--   Original unrestricted cap source interior C² and slope-one gradient force nonnegative capped payoff including boundaries
-- statement:
--   For arbitrary ENNReal cap C, including top, the exact source w(0)≥0, ContinuousOn w (Ici 0), ContDiffOn ℝ 2 w {y|0<y∧ofReal y<C}, and 1≤deriv w on the same interior force w(y)≥0 for every capped nonnegative real state. At each y, apply Mathlib monotoneOn_of_deriv_nonneg on [0,y]. Every 0<z<y has ofReal z<ofReal y≤C; thus C² and gradient bound apply on the interval interior. This gives the true endpoint payoff sign without any occupation-zero assumption, including C=⊤.
-- source:
--   Mathlib.Analysis.Calculus.Deriv.MeanValue.monotoneOn_of_deriv_nonneg; ContDiffOn.differentiableOn; ENNReal.ofReal_lt_ofReal_iff'.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The exact original C² interior and slope-one bound imply w≥0 at every capped nonnegative state, even for an infinite cap. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_anycap_payoff_nonnegative_from_source_interior_gradient
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0)
    (hwCont : ContinuousOn w (Ici (0 : ℝ)))
    (hwSmooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hwGrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y) :
    ∀ y : ℝ, 0 ≤ y → ENNReal.ofReal y ≤ C → 0 ≤ w y := by sorry
