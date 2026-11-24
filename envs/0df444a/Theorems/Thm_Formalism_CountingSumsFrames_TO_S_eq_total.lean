-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_S_eq_total
-- name    : Formalism.CountingSumsFrames.TO.S_eq_total
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:34:53.02267+00:00
-- url     : https://prove2.me/theorems/89db9316-68d5-4e4a-acd3-44f807303308
-- title:
--   TO: S eq total
-- statement:
--   The TO construction uses the S eq total property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L3019-L3035
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L3019-L3035

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

theorem Formalism.CountingSumsFrames.TO.S_eq_total {N : ℕ} (L : Letters N) (T : TieData) (i : Fin T.t) (h : T.pos i + 1 < N) :
    (L.takeD (T.pos i + 1)).total = T.S L i := by sorry
