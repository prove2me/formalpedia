-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_Sys_lift_apply
-- name    : Formalism.L2.FormalSeriesBounds.Sys.lift_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:05:43.5115+00:00
-- url     : https://prove2.me/theorems/46672b12-e738-4026-8e54-7c0e42cbbe8d
-- title:
--   Sys: lift apply
-- statement:
--   The Sys construction uses the lift apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CartesianBoundOnCurves.lean#L208-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CartesianBoundOnCurves.lean#L208-L211

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ScaledSecondIntegral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Cart_lift_apply

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

theorem Formalism.L2.FormalSeriesBounds.Sys.lift_apply (h : I ⊕ J → C) (i : ℕ) (n : I ⊕ J) : S.lift h i n =
    (∑ b, S.co h b ^ (V.l ^ i) * S.cur b i n) +
      const0 (Sum.elim (0 : I → C) (fun j => h (Sum.inr j))) i n := by sorry
