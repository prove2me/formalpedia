-- Prove2me | Theorems.Thm_Formalism_L2_Indef_LevelLink_Tw_eq
-- name    : Formalism.L2.Indef.LevelLink.Tw_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:46:53.474968+00:00
-- url     : https://prove2.me/theorems/9299f328-d105-49fc-b0bc-8a4d7077baf6
-- title:
--   Level Link: Tw eq
-- statement:
--   The Level Link construction uses the Tw eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefUse.lean#L426-L429
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefUse.lean#L426-L429

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_JacquetSubsetSums_SeparationTR
import Definitions.Def_Formalism_DivisorInequality_StatementObj
import Definitions.Def_Formalism_QuotientMetricDivisors_DivIntoDualShift
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefUse
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Indef
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem Formalism.L2.Indef.LevelLink.Tw_eq {Bs : DefBase K} {Df Df' : DefSide Bs} {S : IndefData Df} {S' : IndefData Df'}
    (h : LevelLink S S') (h0 : S.H0) (h0' : S'.H0) : S.Tw = S'.Tw := by sorry
