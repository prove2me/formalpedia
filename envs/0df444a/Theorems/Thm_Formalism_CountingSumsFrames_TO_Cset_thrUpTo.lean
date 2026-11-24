-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_Cset_thrUpTo
-- name    : Formalism.CountingSumsFrames.TO.Cset_thrUpTo
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:37:27.16056+00:00
-- url     : https://prove2.me/theorems/783081e4-ff87-4212-aa56-3abf4fb0b048
-- title:
--   TO: Cset thr Up To
-- statement:
--   The TO construction uses the Cset thr Up To property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L3076-L3084
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L3076-L3084

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
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem Formalism.CountingSumsFrames.TO.Cset_thrUpTo [NeZero r] (L : Letters N) (T : TieData) (i : Fin T.t) :
    Cset p (r := r) L (T.pos i + 1 + 1) T.J (T.thrUpTo i) = Cset p L (T.pos i + 1 + 1) T.J T.thr := by sorry
