-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_FfL_apply
-- name    : Formalism.CountingSumsFrames.TO.FfL_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:33:51.945716+00:00
-- url     : https://prove2.me/theorems/1d77c67a-3810-40a5-9400-ec0e9748a0dc
-- title:
--   TO: Ff L apply
-- statement:
--   The TO construction uses the Ff L apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L2167-L2168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L2167-L2168

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
open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity Formalism.GM.TM MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem Formalism.CountingSumsFrames.TO.FfL_apply [NeZero N] (L : Letters N) (T : TieData) (i : Fin T.t) (ρ : Fin r) (n : ℕ)
    (f : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p]) : FfL p L T i ρ n f = T.Ffull p L i ρ n f := by sorry
