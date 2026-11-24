-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_Cart_Vpow_mem
-- name    : Formalism.L2.FormalSeriesBounds.Cart.Vpow_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:49:45.007997+00:00
-- url     : https://prove2.me/theorems/ec4d0133-75df-4584-9953-8e45c105bab7
-- title:
--   Cart: Vpow mem
-- statement:
--   The Cart construction uses the Vpow mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ScaledSecondIntegral.lean#L30-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ScaledSecondIntegral.lean#L30-L33

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

theorem Formalism.L2.FormalSeriesBounds.Cart.Vpow_mem (s : ℕ) {x : ℕ → I ⊕ J → C} (hx : x ∈ X.Ty) : Vpow s x ∈ X.Ty := by sorry
