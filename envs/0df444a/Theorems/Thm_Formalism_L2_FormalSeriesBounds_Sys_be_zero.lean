-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_Sys_be_zero
-- name    : Formalism.L2.FormalSeriesBounds.Sys.be_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:58:00.184238+00:00
-- url     : https://prove2.me/theorems/c1f342c1-7d6e-41c8-9b73-43a950bc900a
-- title:
--   Sys: be zero
-- statement:
--   The Sys construction uses the be zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CartesianBoundOnCurves.lean#L168-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CartesianBoundOnCurves.lean#L168-L170

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

theorem Formalism.L2.FormalSeriesBounds.Sys.be_zero (c : I) (κ : J) : S.cur c 0 (Sum.inr κ) = 0 := by sorry
