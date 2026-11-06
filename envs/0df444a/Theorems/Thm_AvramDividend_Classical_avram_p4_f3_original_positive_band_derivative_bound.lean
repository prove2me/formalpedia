-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_positive_band_derivative_bound
-- name    : AvramDividend.Classical.avram_p4_f3_original_positive_band_derivative_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T14:32:59.524207+00:00
-- url     : https://prove2.me/theorems/69ecd18b-c168-4e8e-815e-9d4de476f47a
-- title:
--   Canonical original UBV positive reserve compact-band derivative bound without extra hypotheses
-- statement:
--   From the exact canonical ContDiffOn C2 smoothness on positive reserves strictly below cap C, for any 0<delta<=K with ofReal K<C, produce a finite bound on the derivative of w throughout [delta,K]. Openness of the ENNReal cap interior is derived directly from continuity of ofReal. This supplies the justified coefficient localisation used for source Gaussian and small-jump L2 estimates, while not asserting a global bound at 0, C, or C=top.
-- source:
--   Pinned Mathlib ENNReal.continuous_ofReal, ENNReal.ofReal_le_ofReal, ContDiffOn.continuousOn_deriv_of_isOpen and IsCompact.exists_bound_of_continuousOn applied to the canonical UBV interior; no extra stochastic construction assumptions.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_positive_band_derivative_bound
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (δ K : ℝ) (hδ : 0 < δ) (hδK : δ ≤ K)
    (hK : ENNReal.ofReal K < C) :
    ∃ B : ℝ, ∀ y ∈ Icc δ K, |deriv w y| ≤ B := by sorry
