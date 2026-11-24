-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_Sys_co_int
-- name    : Formalism.L2.FormalSeriesBounds.Sys.co_int
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:05:50.653414+00:00
-- url     : https://prove2.me/theorems/3616e51b-5b32-4038-9ed6-4dab3937f5f3
-- title:
--   Sys: co int
-- statement:
--   The Sys construction uses the co int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CartesianBoundOnCurves.lean#L188-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CartesianBoundOnCurves.lean#L188-L192

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
open Formalism.L2.FormalSeriesBounds.Sys
variable {X : Cart V d I J} (S : Sys X)

theorem Formalism.L2.FormalSeriesBounds.Sys.co_int {h : I ⊕ J → C} (hh : ∀ n, V.Ge 0 (h n)) (b : I) : V.Ge 0 (S.co h b) := by sorry
