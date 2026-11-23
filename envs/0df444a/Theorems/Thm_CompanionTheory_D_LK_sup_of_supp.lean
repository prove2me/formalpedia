-- Prove2me | Theorems.Thm_CompanionTheory_D_LK_sup_of_supp
-- name    : CompanionTheory.D.LK.sup_of_supp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:28:07.210713+00:00
-- url     : https://prove2.me/theorems/d478835b-fcda-4c1e-8bd0-0220174e196d
-- title:
--   LK: sup of supp
-- statement:
--   The LK construction uses the sup of supp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/DifferentialCommutesWeightOperator.lean#L105-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/DifferentialCommutesWeightOperator.lean#L105-L106

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_DifferentialBoundedSupport
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_DifferentialCommutesWeightOperator
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
open CompanionTheory.D.DSIC (KRel)
variable {n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem CompanionTheory.D.LK.sup_of_supp {ε : Fin n → Bool} {B : Finset (Pos n)} {j : ℕ} {x : Cn n V} {y : Cn n W} (hx : Sup ε B j x)
    (h : ∀ A, x A = 0 → y A = 0) : Sup ε B j y := by sorry
