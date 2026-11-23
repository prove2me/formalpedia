-- Prove2me | Theorems.Thm_CompanionTheory_D_LK_Sup_sub
-- name    : CompanionTheory.D.LK.Sup.sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:27:10.827013+00:00
-- url     : https://prove2.me/theorems/fb75e8c5-ce76-41be-8cc3-17423c720be1
-- title:
--   Sup: sub
-- statement:
--   The Sup construction uses the sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/DifferentialCommutesWeightOperator.lean#L108-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/DifferentialCommutesWeightOperator.lean#L108-L112

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

theorem CompanionTheory.D.LK.Sup.sub {ε : Fin n → Bool} {B : Finset (Pos n)} {j : ℕ} {x y : Cn n V} (hx : Sup ε B j x) (hy : Sup ε B j y) :
    Sup ε B j (x - y) := by sorry
