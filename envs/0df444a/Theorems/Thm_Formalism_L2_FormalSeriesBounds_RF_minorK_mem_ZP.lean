-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_minorK_mem_ZP
-- name    : Formalism.L2.FormalSeriesBounds.RF.minorK_mem_ZP
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:47:05.011293+00:00
-- url     : https://prove2.me/theorems/148f1152-cef3-4cf1-848f-aa5d2c527902
-- title:
--   RF: minor K mem ZP
-- statement:
--   The RF construction uses the minor K mem ZP property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/NormOneIntegral.lean#L39-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/NormOneIntegral.lean#L39-L43

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipNormOne
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NormOneIntegral
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
variable {C : Type} [Field C]

theorem Formalism.L2.FormalSeriesBounds.RF.minorK_mem_ZP (N N' k : ℕ) : minorK C N N' k ∈ ZP C (Fin N × Fin N') := by sorry
