-- Prove2me | Theorems.Thm_Formalism_MainNotions_Gaps_T0_SumDat_Ok_sum_le_named
-- name    : Formalism.MainNotions.Gaps.T0.SumDat.Ok.sum_le_named
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T09:55:53.780466+00:00
-- url     : https://prove2.me/theorems/cac60088-d761-4a08-892a-e341d27bb43a
-- title:
--   Ok: sum le named
-- statement:
--   The Ok construction uses the sum le named property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/QuotientParamNonneg.lean#L296-L303
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/QuotientParamNonneg.lean#L296-L303

import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_FourTermSumBoundOfParameters
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_QuotientParamNonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.T0
open Formalism.MainNotions.Gaps.T0.SumDat
variable {ι : Type*} (X : SumDat ι)
variable {X}

theorem Formalism.MainNotions.Gaps.T0.SumDat.Ok.sum_le_named (h : X.Ok) : ∑ la ∈ X.s, X.rr la * X.l la ≤ X.totalNamed := by sorry
