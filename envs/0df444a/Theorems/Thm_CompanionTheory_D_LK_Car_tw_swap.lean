-- Prove2me | Theorems.Thm_CompanionTheory_D_LK_Car_tw_swap
-- name    : CompanionTheory.D.LK.Car.tw_swap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:26:33.788168+00:00
-- url     : https://prove2.me/theorems/cbffccec-bd82-4b0c-ad72-9084f972a972
-- title:
--   Car: tw swap
-- statement:
--   The Car construction uses the tw swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/CreApply.lean#L31-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/CreApply.lean#L31-L36

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

theorem CompanionTheory.D.LK.Car.tw_swap {i j : Pos n} (h : i ≠ j) : tw j i = -tw i j := by sorry
