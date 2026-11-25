-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_intC_sub
-- name    : Formalism.L2.FormalSeriesBounds.AltInv.intC_sub
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:19:33.912804+00:00
-- url     : https://prove2.me/theorems/a8def272-bbf9-4149-8183-679364f0b3ee
-- title:
--   Alt Inv: int C sub
-- statement:
--   The Alt Inv construction uses the int C sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/AltInv.lean#L33-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/AltInv.lean#L33-L35

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

theorem Formalism.L2.FormalSeriesBounds.AltInv.intC_sub {x y : C} (hx : IntC v x) (hy : IntC v y) : IntC v (x - y) := by sorry
