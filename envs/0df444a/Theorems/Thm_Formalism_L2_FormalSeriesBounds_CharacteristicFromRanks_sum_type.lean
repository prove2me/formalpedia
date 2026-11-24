-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_CharacteristicFromRanks_sum_type
-- name    : Formalism.L2.FormalSeriesBounds.CharacteristicFromRanks.sum_type
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:50:23.308772+00:00
-- url     : https://prove2.me/theorems/4096ea10-ec13-4abb-9945-60ba1bfc0cdc
-- title:
--   Characteristic From Ranks: sum type
-- statement:
--   The Characteristic From Ranks construction uses the sum type property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CharacteristicFromRanks.lean#L71-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CharacteristicFromRanks.lean#L71-L77

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

theorem Formalism.L2.FormalSeriesBounds.CharacteristicFromRanks.sum_type {ι : Type} [Fintype ι] (P : ι → Prop) {m : ℕ} (e : Fin m ≃ {x // P x})
    (F : ι → C) (hF : ∀ x, ¬ P x → F x = 0) : ∑ c, F (e c) = ∑ x, F x := by sorry
