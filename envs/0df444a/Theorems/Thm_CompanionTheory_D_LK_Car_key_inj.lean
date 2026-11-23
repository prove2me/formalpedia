-- Prove2me | Theorems.Thm_CompanionTheory_D_LK_Car_key_inj
-- name    : CompanionTheory.D.LK.Car.key_inj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:27:08.631571+00:00
-- url     : https://prove2.me/theorems/e3be436e-bef2-4c51-a0ba-bd8fe54106cf
-- title:
--   Car: key inj
-- statement:
--   The Car construction uses the key inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/CreApply.lean#L11-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/CreApply.lean#L11-L22

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

theorem CompanionTheory.D.LK.Car.key_inj {i j : Pos n} (h : key i = key j) : i = j := by sorry
