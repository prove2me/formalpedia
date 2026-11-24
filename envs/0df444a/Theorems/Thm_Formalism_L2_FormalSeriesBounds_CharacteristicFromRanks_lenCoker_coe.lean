-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_CharacteristicFromRanks_lenCoker_coe
-- name    : Formalism.L2.FormalSeriesBounds.CharacteristicFromRanks.lenCoker_coe
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:12:25.52045+00:00
-- url     : https://prove2.me/theorems/3ace6b00-3df8-4dd6-bd64-5dcc3fbb7222
-- title:
--   Characteristic From Ranks: len Coker coe
-- statement:
--   The Characteristic From Ranks construction uses the len Coker coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CharacteristicFromRanks.lean#L63-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CharacteristicFromRanks.lean#L63-L69

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

theorem Formalism.L2.FormalSeriesBounds.CharacteristicFromRanks.lenCoker_coe (V : VF C) {m h : ℕ} (α : Matrix (Fin m) (Fin h) (intR V)) :
    S4.lenCoker (vR V) α = S4.lenCoker V.v (Matrix.of fun i k => (α i k : C)) := by sorry
