-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_prod
-- name    : Formalism.L2.FormalSeriesBounds.VF.Ge.prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:49:34.008808+00:00
-- url     : https://prove2.me/theorems/c2ac48f9-c743-47b4-ba97-02869ba85236
-- title:
--   Ge: prod
-- statement:
--   The Ge construction uses the prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CartesianBoundOnCurves.lean#L43-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CartesianBoundOnCurves.lean#L43-L46

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

theorem Formalism.L2.FormalSeriesBounds.VF.Ge.prod {ι : Type*} {s : Finset ι} {f : ι → C} (h : ∀ i ∈ s, V.Ge 0 (f i)) :
    V.Ge 0 (∏ i ∈ s, f i) := by sorry
