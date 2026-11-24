-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_Sys_lift_zero
-- name    : Formalism.L2.FormalSeriesBounds.Sys.lift_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:58:09.958806+00:00
-- url     : https://prove2.me/theorems/89c64a80-c18a-41a0-b218-63fd9dbef5a1
-- title:
--   Sys: lift zero
-- statement:
--   The Sys construction uses the lift zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CartesianBoundOnCurves.lean#L213-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CartesianBoundOnCurves.lean#L213-L220

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ScaledSecondIntegral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Cart_lift_zero

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
open Formalism.L2.FormalSeriesBounds.Sys
variable {X : Cart V d I J} (S : Sys X)

theorem Formalism.L2.FormalSeriesBounds.Sys.lift_zero (h : I ⊕ J → C) : S.lift h 0 = h := by sorry
