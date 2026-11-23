-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_Cart_std_spec
-- name    : Formalism.L2.FormalSeriesBounds.Cart.std_spec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:37:38.298838+00:00
-- url     : https://prove2.me/theorems/b309048c-a46a-4862-a6fe-12edad1559e7
-- title:
--   Cart: std spec
-- statement:
--   The Cart construction uses the std spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ScaledSecondIntegral.lean#L69-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ScaledSecondIntegral.lean#L69-L70

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

theorem Formalism.L2.FormalSeriesBounds.Cart.std_spec (b : I) : X.IsCurve (X.ty (Sum.inl b)) (Pi.single b 1) (X.std b) := by sorry
