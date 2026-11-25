-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_first_chern_integral
-- name    : Formalism.L2.FormalSeriesBounds.RF.first_chern_integral
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:53:15.150456+00:00
-- url     : https://prove2.me/theorems/56196e66-4328-40bd-a765-c12acfe2bb16
-- title:
--   RF: first chern integral
-- statement:
--   The RF construction uses the first chern integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieMemC.lean#L140-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieMemC.lean#L140-L147

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValBlocksCChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NormOneIntegral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieMemC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds Formalism.L2.Pj

theorem Formalism.L2.FormalSeriesBounds.RF.first_chern_integral : IsotropicToStdSubstIntegral := by sorry
