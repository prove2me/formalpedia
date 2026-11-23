-- Prove2me | Theorems.Thm_CompanionTheory_D_LK_Car_ann_apply
-- name    : CompanionTheory.D.LK.Car.ann_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:12:14.172309+00:00
-- url     : https://prove2.me/theorems/41dbe869-76eb-48d7-b3a1-144a14511422
-- title:
--   Car: ann apply
-- statement:
--   The Car construction uses the ann apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/CreApply.lean#L58-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/CreApply.lean#L58-L59

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_CreApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.LK CompanionTheory.D.LK.Car
variable {n : ℕ}
variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem CompanionTheory.D.LK.Car.ann_apply (i : Pos n) (x : Cn n V) (A : Finset (Pos n)) :
    ann i x A = if i ∈ A then 0 else sg i A • x (insert i A) := by sorry
