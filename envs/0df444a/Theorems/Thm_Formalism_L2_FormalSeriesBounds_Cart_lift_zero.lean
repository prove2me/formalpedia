-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_Cart_lift_zero
-- name    : Formalism.L2.FormalSeriesBounds.Cart.lift_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:36:18.268433+00:00
-- url     : https://prove2.me/theorems/9984cae4-629b-4558-a4b9-410e9c7e118c
-- title:
--   Cart: lift zero
-- statement:
--   The Cart construction uses the lift zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ScaledSecondIntegral.lean#L87-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ScaledSecondIntegral.lean#L87-L93

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
variable [DecidableEq I]
variable [Fintype I]

theorem Formalism.L2.FormalSeriesBounds.Cart.lift_zero (h : I ⊕ J → C) : X.lift h 0 = h := by sorry
