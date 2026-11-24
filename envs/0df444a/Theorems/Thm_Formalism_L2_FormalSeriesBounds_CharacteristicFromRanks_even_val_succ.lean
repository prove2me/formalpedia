-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_CharacteristicFromRanks_even_val_succ
-- name    : Formalism.L2.FormalSeriesBounds.CharacteristicFromRanks.even_val_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:55:53.239223+00:00
-- url     : https://prove2.me/theorems/3470aeb9-8b16-4a79-9c61-459d6a428386
-- title:
--   Characteristic From Ranks: even val succ
-- statement:
--   The Characteristic From Ranks construction uses the even val succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CharacteristicFromRanks.lean#L137-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CharacteristicFromRanks.lean#L137-L153

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_Interface
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ExistsStrictMonoMinor
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CharacteristicFromRanks
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
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds
open Formalism.L2.FormalSeriesBounds.CharacteristicFromRanks
variable {C : Type} [Field C]

theorem Formalism.L2.FormalSeriesBounds.CharacteristicFromRanks.even_val_succ {d : ℕ} [NeZero d] (hd : Even d) (b : ZMod d) :
    Even (b + 1).val ↔ ¬ Even b.val := by sorry
