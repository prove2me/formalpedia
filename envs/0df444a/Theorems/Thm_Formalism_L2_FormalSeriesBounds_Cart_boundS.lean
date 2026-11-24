-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_Cart_boundS
-- name    : Formalism.L2.FormalSeriesBounds.Cart.boundS
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:57:31.860659+00:00
-- url     : https://prove2.me/theorems/0c031e5f-1f14-40e9-a57c-1e02d287dce7
-- title:
--   Cart: bound S
-- statement:
--   The Cart construction uses the bound S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ScaledSecondIntegral.lean#L95-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ScaledSecondIntegral.lean#L95-L124

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

theorem Formalism.L2.FormalSeriesBounds.Cart.boundS : ∀ (i s : ℕ) (x : ℕ → I ⊕ J → C), x ∈ X.Ty → (∀ j < s, x j = 0) →
    ∀ n, V.Ge (-(i : ℝ)) (x (s + i) n) := by sorry
