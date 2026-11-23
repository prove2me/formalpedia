-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_Cart_lift_apply
-- name    : Formalism.L2.FormalSeriesBounds.Cart.lift_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:35:10.787089+00:00
-- url     : https://prove2.me/theorems/2c82a70c-9870-4a33-9841-2d4e857d0de1
-- title:
--   Cart: lift apply
-- statement:
--   The Cart construction uses the lift apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ScaledSecondIntegral.lean#L82-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ScaledSecondIntegral.lean#L82-L85

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

theorem Formalism.L2.FormalSeriesBounds.Cart.lift_apply (h : I ⊕ J → C) (i : ℕ) (n : I ⊕ J) : X.lift h i n =
    (∑ b, h (Sum.inl b) ^ (V.l ^ i) * X.std b i n) +
      const0 (Sum.elim 0 (fun j => h (Sum.inr j))) i n := by sorry
