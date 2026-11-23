-- Prove2me | Theorems.Thm_CompanionTheory_D_LK_Car_sg_erase
-- name    : CompanionTheory.D.LK.Car.sg_erase
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T06:26:35.174912+00:00
-- url     : https://prove2.me/theorems/83e723fe-70c4-4b4b-b770-e56d09b340bc
-- title:
--   Car: sg erase
-- statement:
--   The Car construction uses the sg erase property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/CreApply.lean#L50-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/CreApply.lean#L50-L54

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

theorem CompanionTheory.D.LK.Car.sg_erase (i : Pos n) {j : Pos n} {A : Finset (Pos n)} (h : j ∈ A) :
    sg i (A.erase j) = tw i j * sg i A := by sorry
