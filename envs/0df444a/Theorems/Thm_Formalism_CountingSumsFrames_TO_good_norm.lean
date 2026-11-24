-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_good_norm
-- name    : Formalism.CountingSumsFrames.TO.good_norm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:39:10.074836+00:00
-- url     : https://prove2.me/theorems/8445b753-8f94-4608-bbbf-8cb5e28c5ddb
-- title:
--   TO: good norm
-- statement:
--   The TO construction uses the good norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L2957-L2982
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L2957-L2982

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames Formalism.CountingSumsFrames.TO
open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime]

theorem Formalism.CountingSumsFrames.TO.good_norm (E : ℝ) (hE : 0 ≤ E) (d : ℚ_[p]) (hd : ¬ ‖d‖ < (p : ℝ) ^ (-E)) :
    ‖(p : ℚ_[p]) ^ ⌊E⌋₊ / d‖ ≤ 1 ∧ d ≠ 0 := by sorry
