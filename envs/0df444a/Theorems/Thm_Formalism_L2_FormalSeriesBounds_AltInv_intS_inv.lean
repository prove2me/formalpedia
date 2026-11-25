-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_intS_inv
-- name    : Formalism.L2.FormalSeriesBounds.AltInv.intS_inv
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:19:22.714377+00:00
-- url     : https://prove2.me/theorems/3248c46c-fe28-4cc0-bde7-6b6fb076cd62
-- title:
--   Alt Inv: int S inv
-- statement:
--   The Alt Inv construction uses the int S inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/AltInv.lean#L197-L337
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/AltInv.lean#L197-L337

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

theorem Formalism.L2.FormalSeriesBounds.AltInv.intS_inv [Fintype σ] (Φ t : σ → MvPowerSeries σ C) (hΦ0 : ∀ x, constantCoeff (Φ x) = 0)
    (hΦ : ∀ x, IntS v (Φ x))
    (hL : v (Matrix.of fun x y : σ => coeff (Finsupp.single y 1) (Φ x)).det = 0)
    (ht0 : ∀ y, constantCoeff (t y) = 0) (heq : ∀ x, subst t (Φ x) = X x) : ∀ y, IntS v (t y) := by sorry
