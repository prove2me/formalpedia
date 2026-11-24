-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_Cart_Good_bound
-- name    : Formalism.L2.FormalSeriesBounds.Cart.Good.bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:57:25.416523+00:00
-- url     : https://prove2.me/theorems/4af2f2f0-d9ab-4215-891b-fe251723d382
-- title:
--   Good: bound
-- statement:
--   The Good construction uses the bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ScaledSecondIntegral.lean#L149-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ScaledSecondIntegral.lean#L149-L173

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

theorem Formalism.L2.FormalSeriesBounds.Cart.Good.bound [DecidableEq I] [Fintype I] {a : ZMod d} {u : I → C} {x : ℕ → I ⊕ J → C}
    (h : X.Good a u x) (i : ℕ) (n : I ⊕ J) : V.Ge (-((i : ℝ) + 1)) (x (i + 2) n) := by sorry
