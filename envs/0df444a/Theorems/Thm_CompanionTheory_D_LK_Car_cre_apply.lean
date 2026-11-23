-- Prove2me | Theorems.Thm_CompanionTheory_D_LK_Car_cre_apply
-- name    : CompanionTheory.D.LK.Car.cre_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:13:11.32053+00:00
-- url     : https://prove2.me/theorems/36909981-5772-4b2f-aca6-dddc93873faa
-- title:
--   Car: cre apply
-- statement:
--   The Car construction uses the cre apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/CreApply.lean#L61-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/CreApply.lean#L61-L62

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

theorem CompanionTheory.D.LK.Car.cre_apply (i : Pos n) (x : Cn n V) (A : Finset (Pos n)) :
    cre i x A = if i ∈ A then sg i A • x (A.erase i) else 0 := by sorry
