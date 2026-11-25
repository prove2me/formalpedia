-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_HaP_haSpanSt_of
-- name    : Formalism.L2.FormalSeriesBounds.HaP.haSpanSt_of
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:46:57.201805+00:00
-- url     : https://prove2.me/theorems/8835e22c-b5c1-479e-a1f9-474fddf83548
-- title:
--   Ha P: ha Span St of
-- statement:
--   The Ha P construction uses the ha Span St of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHaSpan.lean#L259-L315
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHaSpan.lean#L259-L315

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHaDefs
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePDescSpanSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHaSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.HaP
open MvPolynomial Formalism.L2.Pj

theorem Formalism.L2.FormalSeriesBounds.HaP.haSpanSt_of (hS : SatRetrSt) (hR : RowInvUpSt) : HaSpanSt := by sorry
