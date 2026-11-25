-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_intC_neg
-- name    : Formalism.L2.FormalSeriesBounds.AltInv.intC_neg
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:19:22.555062+00:00
-- url     : https://prove2.me/theorems/bd593296-e696-4ef1-b086-c977e819c138
-- title:
--   Alt Inv: int C neg
-- statement:
--   The Alt Inv construction uses the int C neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/AltInv.lean#L26-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/AltInv.lean#L26-L28

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_AltInv
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
open MvPowerSeries
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.AltInv
variable {C : Type*} [Field C] (v : AddValuation C (WithTop ℝ))
variable {v}

theorem Formalism.L2.FormalSeriesBounds.AltInv.intC_neg {x : C} (hx : IntC v x) : IntC v (-x) := by sorry
