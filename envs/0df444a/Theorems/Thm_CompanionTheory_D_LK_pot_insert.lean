-- Prove2me | Theorems.Thm_CompanionTheory_D_LK_pot_insert
-- name    : CompanionTheory.D.LK.pot_insert
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:27:43.066266+00:00
-- url     : https://prove2.me/theorems/5bea0c0f-00fc-4776-8293-aa143a369d3f
-- title:
--   LK: pot insert
-- statement:
--   The LK construction uses the pot insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/DifferentialBoundedSupport.lean#L114-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/DifferentialBoundedSupport.lean#L114-L115

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_CreApply
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_DifferentialBoundedSupport
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
open CompanionTheory CompanionTheory.D CompanionTheory.D.LK
open Car Formalism.REAL
variable {n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem CompanionTheory.D.LK.pot_insert {i : Pos n} {B : Finset (Pos n)} (h : i ∉ B) :
    pot (insert i B) = n - ((i.1.2 : ℕ) - (i.1.1 : ℕ)) + pot B := by sorry
