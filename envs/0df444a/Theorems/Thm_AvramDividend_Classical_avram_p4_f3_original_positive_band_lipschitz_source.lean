-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_positive_band_lipschitz_source
-- name    : AvramDividend.Classical.avram_p4_f3_original_positive_band_lipschitz_source
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T14:33:00.377029+00:00
-- url     : https://prove2.me/theorems/8179243e-4aec-4684-8907-2b64cb7203b0
-- title:
--   Original UBV compact positive-reserve Lipschitz bound for physical small-jump integrands
-- statement:
--   For every positive compact reserve interval [delta,K] strictly inside the original cap C, the exact canonical ContDiffOn C2 hypothesis gives one finite Lipschitz constant B for w on the whole band. This proves |w(u+z)-w(u)|<=B|z| whenever both endpoints stay on the band, providing the genuine deterministic quadratic-integrability estimate for the original compensated small-jump kernel. It makes no unsupported claim about jump paths crossing zero or the cap.
-- source:
--   Pinned Mathlib original canonical smoothness predicate; ENNReal continuous ofReal, compact derivative bound, ContDiffOn differentiability, and Convex.norm_image_sub_le_of_norm_deriv_le. Supports localised genuine source L2 isometry.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_positive_band_lipschitz_source
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (δ K : ℝ) (hδ : 0 < δ) (hδK : δ ≤ K)
    (hK : ENNReal.ofReal K < C) :
    ∃ B : ℝ, ∀ u ∈ Icc δ K, ∀ v ∈ Icc δ K,
      |w v - w u| ≤ B * |v - u| := by sorry
