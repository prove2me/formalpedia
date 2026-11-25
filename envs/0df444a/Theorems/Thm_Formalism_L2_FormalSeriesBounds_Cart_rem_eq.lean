-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_Cart_rem_eq
-- name    : Formalism.L2.FormalSeriesBounds.Cart.rem_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:43:53.614941+00:00
-- url     : https://prove2.me/theorems/f8e7f55f-0083-574d-84dc-433e97b3ff31
-- title:
--   Cart: rem eq
-- statement:
--   The Cart construction uses the rem eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ScaledSecondIntegral.lean#L130-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ScaledSecondIntegral.lean#L130-L136

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

theorem Formalism.L2.FormalSeriesBounds.Cart.rem_eq (x : ℕ → I ⊕ J → C) (s : ℕ) :
    X.rem x s = x - ∑ s' ∈ range s, Vpow s' (X.lift (X.rem x s' s')) := by sorry
