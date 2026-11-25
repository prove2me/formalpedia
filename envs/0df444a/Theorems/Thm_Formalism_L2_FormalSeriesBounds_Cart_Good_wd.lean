-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_Cart_Good_wd
-- name    : Formalism.L2.FormalSeriesBounds.Cart.Good.wd
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:37:48.984423+00:00
-- url     : https://prove2.me/theorems/e1f4bd3b-1c61-4273-91b0-924c7e004efd
-- title:
--   Good: wd
-- statement:
--   The Good construction uses the wd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ScaledSecondIntegral.lean#L214-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ScaledSecondIntegral.lean#L214-L233

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeNatCast
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ScaledSecondIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Finset
noncomputable section
variable {C : Type*} [Field C] {V : VF C} {d : ℕ} {I J : Type*}
open Formalism.L2.FormalSeriesBounds.Cart
variable (X : Cart V d I J)
variable {X}

theorem Formalism.L2.FormalSeriesBounds.Cart.Good.wd {a : ZMod d} {u : I → C} {x x' : ℕ → I ⊕ J → C}
    (h : X.Good a u x) (h' : X.Good a u x') (n : I ⊕ J) : V.Ge 0 (x 2 n - x' 2 n) := by sorry
