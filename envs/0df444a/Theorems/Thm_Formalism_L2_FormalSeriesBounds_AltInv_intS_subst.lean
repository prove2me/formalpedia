-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_intS_subst
-- name    : Formalism.L2.FormalSeriesBounds.AltInv.intS_subst
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:19:23.078341+00:00
-- url     : https://prove2.me/theorems/39fef14d-1204-42da-93c2-638fc0471e48
-- title:
--   Alt Inv: int S subst
-- statement:
--   The Alt Inv construction uses the int S subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/AltInv.lean#L96-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/AltInv.lean#L96-L103

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

theorem Formalism.L2.FormalSeriesBounds.AltInv.intS_subst [Finite σ] {a : σ → MvPowerSeries τ C} (ha0 : ∀ s, constantCoeff (a s) = 0)
    (ha : ∀ s, IntS v (a s)) {γ : MvPowerSeries σ C} (hγ : IntS v γ) : IntS v (subst a γ) := by sorry
