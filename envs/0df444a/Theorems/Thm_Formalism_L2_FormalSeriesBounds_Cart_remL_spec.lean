-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_Cart_remL_spec
-- name    : Formalism.L2.FormalSeriesBounds.Cart.remL_spec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:49:52.286265+00:00
-- url     : https://prove2.me/theorems/563090c4-de8c-4b24-af79-5be31590477a
-- title:
--   Cart: rem L spec
-- statement:
--   The Cart construction uses the rem L spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CartesianBoundOnCurves.lean#L107-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CartesianBoundOnCurves.lean#L107-L127

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

theorem Formalism.L2.FormalSeriesBounds.Cart.remL_spec (hmem : ∀ h, (∀ n, V.Ge 0 (h n)) → L h ∈ X.Ty) (hzero : ∀ h, L h 0 = h)
    {x : ℕ → I ⊕ J → C} (hx : x ∈ X.Ty) :
    ∀ s, remL L x s ∈ X.Ty ∧ ∀ j < s, remL L x s j = 0 := by sorry
