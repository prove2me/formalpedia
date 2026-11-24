-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_isWt_iff_wh
-- name    : Formalism.CountingSumsFrames.TO.isWt_iff_wh
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:35:48.139417+00:00
-- url     : https://prove2.me/theorems/b1999b97-adc6-49e4-af29-e300b3e27cbe
-- title:
--   TO: is Wt iff wh
-- statement:
--   The TO construction uses the is Wt iff wh property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L2539-L2548
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L2539-L2548

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
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem Formalism.CountingSumsFrames.TO.isWt_iff_wh (L : Letters N) (j : ℕ) (ν : Fin r → ℤ) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    (GA p L j).IsWt ν x ↔ x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L j) ν := by sorry
