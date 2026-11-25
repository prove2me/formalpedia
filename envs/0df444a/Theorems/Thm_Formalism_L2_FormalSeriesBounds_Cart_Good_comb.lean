-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_Cart_Good_comb
-- name    : Formalism.L2.FormalSeriesBounds.Cart.Good.comb
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:14:21.30963+00:00
-- url     : https://prove2.me/theorems/881e5387-6a9c-468a-a641-ce61c71d9a77
-- title:
--   Good: comb
-- statement:
--   The Good construction uses the comb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ScaledSecondIntegral.lean#L186-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ScaledSecondIntegral.lean#L186-L202

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

theorem Formalism.L2.FormalSeriesBounds.Cart.Good.comb {ι : Type*} (s : Finset ι) {a : ZMod d} {u : ι → I → C}
    {x : ι → ℕ → I ⊕ J → C} {co : ι → C} (hco : ∀ k ∈ s, V.Ge 0 (co k))
    (h : ∀ k ∈ s, X.Good a (u k) (x k)) :
    X.Good a (∑ k ∈ s, co k • u k) (∑ k ∈ s, teich V.l (co k) (x k)) := by sorry
