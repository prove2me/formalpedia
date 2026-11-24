-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_Sys_lift_mem
-- name    : Formalism.L2.FormalSeriesBounds.Sys.lift_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:57:51.898568+00:00
-- url     : https://prove2.me/theorems/dd5133c1-40de-4b10-81db-39249bc4b7f7
-- title:
--   Sys: lift mem
-- statement:
--   The Sys construction uses the lift mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CartesianBoundOnCurves.lean#L206-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CartesianBoundOnCurves.lean#L206-L206

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ScaledSecondIntegral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Cart_lift_mem

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

theorem Formalism.L2.FormalSeriesBounds.Sys.lift_mem {h : I ⊕ J → C} (hh : ∀ n, V.Ge 0 (h n)) : S.lift h ∈ X.Ty := by sorry
