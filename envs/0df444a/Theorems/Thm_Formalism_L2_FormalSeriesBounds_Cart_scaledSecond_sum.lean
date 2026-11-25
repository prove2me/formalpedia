-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_Cart_scaledSecond_sum
-- name    : Formalism.L2.FormalSeriesBounds.Cart.scaledSecond_sum
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:23:46.145552+00:00
-- url     : https://prove2.me/theorems/be934ef0-2920-41bb-ac60-66f00860937e
-- title:
--   Cart: scaled Second sum
-- statement:
--   The Cart construction uses the scaled Second sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ScaledSecondIntegral.lean#L204-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ScaledSecondIntegral.lean#L204-L207

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

theorem Formalism.L2.FormalSeriesBounds.Cart.scaledSecond_sum {ι : Type*} (s : Finset ι) (x : ι → ℕ → I ⊕ J → C) (co : ι → C) (b : I) :
    X.V2 (∑ k ∈ s, teich V.l (co k) (x k)) b = ∑ k ∈ s, co k ^ (V.l ^ 2) * X.V2 (x k) b := by sorry
