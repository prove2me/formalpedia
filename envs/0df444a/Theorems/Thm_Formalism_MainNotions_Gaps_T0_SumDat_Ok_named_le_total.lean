-- Prove2me | Theorems.Thm_Formalism_MainNotions_Gaps_T0_SumDat_Ok_named_le_total
-- name    : Formalism.MainNotions.Gaps.T0.SumDat.Ok.named_le_total
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T09:56:22.463998+00:00
-- url     : https://prove2.me/theorems/6bb59692-ccaf-4b0c-b15b-3fdb2ff4f916
-- title:
--   Ok: named le total
-- statement:
--   The Ok construction uses the named le total property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/QuotientParamNonneg.lean#L305-L307
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/QuotientParamNonneg.lean#L305-L307

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

theorem Formalism.MainNotions.Gaps.T0.SumDat.Ok.named_le_total (h : X.Ok) {PP : ℝ} (hP : X.Rel PP) : X.totalNamed ≤ X.total PP := by sorry
