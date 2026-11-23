-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_Cart_lift_mem
-- name    : Formalism.L2.FormalSeriesBounds.Cart.lift_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:36:01.826269+00:00
-- url     : https://prove2.me/theorems/b390cf27-c3e8-4a4a-966c-640d1c72a1b8
-- title:
--   Cart: lift mem
-- statement:
--   The Cart construction uses the lift mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ScaledSecondIntegral.lean#L77-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ScaledSecondIntegral.lean#L77-L80

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

theorem Formalism.L2.FormalSeriesBounds.Cart.lift_mem {h : I ⊕ J → C} (hh : ∀ n, V.Ge 0 (h n)) : X.lift h ∈ X.Ty := by sorry
