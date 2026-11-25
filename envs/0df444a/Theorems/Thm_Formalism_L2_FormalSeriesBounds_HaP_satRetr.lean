-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_HaP_satRetr
-- name    : Formalism.L2.FormalSeriesBounds.HaP.satRetr
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:31:19.974808+00:00
-- url     : https://prove2.me/theorems/2e7894bc-f49e-4134-84c4-018a6836d2b8
-- title:
--   Ha P: sat Retr
-- statement:
--   The Ha P construction uses the sat Retr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHaLeaves.lean#L14-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHaLeaves.lean#L14-L33

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

theorem Formalism.L2.FormalSeriesBounds.HaP.satRetr : SatRetrSt := by sorry
