-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_Cart_remL_eq
-- name    : Formalism.L2.FormalSeriesBounds.Cart.remL_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:55:33.065415+00:00
-- url     : https://prove2.me/theorems/325dc065-5415-41a5-ad7a-e33cce09644f
-- title:
--   Cart: rem L eq
-- statement:
--   The Cart construction uses the rem L eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CartesianBoundOnCurves.lean#L129-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CartesianBoundOnCurves.lean#L129-L135

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ScaledSecondIntegral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
open Formalism.L2.FormalSeriesBounds.Cart
variable (X : Cart V d I J)
variable {X} {L : (I ⊕ J → C) → ℕ → I ⊕ J → C}

theorem Formalism.L2.FormalSeriesBounds.Cart.remL_eq (x : ℕ → I ⊕ J → C) (s : ℕ) :
    remL L x s = x - ∑ s' ∈ Finset.range s, Vpow s' (L (remL L x s' s')) := by sorry
