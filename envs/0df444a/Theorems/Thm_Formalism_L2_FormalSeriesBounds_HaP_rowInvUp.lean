-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_HaP_rowInvUp
-- name    : Formalism.L2.FormalSeriesBounds.HaP.rowInvUp
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:31:13.596777+00:00
-- url     : https://prove2.me/theorems/872cb235-329c-4d83-97b3-bd928907b776
-- title:
--   Ha P: row Inv Up
-- statement:
--   The Ha P construction uses the row Inv Up property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHaLeaves.lean#L35-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHaLeaves.lean#L35-L74

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHaDefs
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHaLeaves
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

theorem Formalism.L2.FormalSeriesBounds.HaP.rowInvUp : RowInvUpSt := by sorry
