-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_intS_pow
-- name    : Formalism.L2.FormalSeriesBounds.AltInv.intS_pow
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:19:33.926355+00:00
-- url     : https://prove2.me/theorems/d86b4a32-dbcb-4aaf-b197-82976d56cd9c
-- title:
--   Alt Inv: int S pow
-- statement:
--   The Alt Inv construction uses the int S pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/AltInv.lean#L79-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/AltInv.lean#L79-L86

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
variable {σ τ : Type*}

theorem Formalism.L2.FormalSeriesBounds.AltInv.intS_pow {f : MvPowerSeries σ C} (hf : IntS v f) (n : ℕ) : IntS v (f ^ n) := by sorry
