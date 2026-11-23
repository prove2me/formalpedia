-- Prove2me | Theorems.Thm_CompanionTheory_D_LK_Ft_apply
-- name    : CompanionTheory.D.LK.Ft_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:25:40.896118+00:00
-- url     : https://prove2.me/theorems/d10f55a9-9b31-4531-a4d4-96446c11204a
-- title:
--   LK: Ft apply
-- statement:
--   The LK construction uses the Ft apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/DifferentialCommutesWeightOperator.lean#L21-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/DifferentialCommutesWeightOperator.lean#L21-L22

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

theorem CompanionTheory.D.LK.Ft_apply (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (c : Fin n) (x : Cn n V)
    (A : Finset (Pos n)) : Ft ε E c x A = E c c (x A) + (wt (A.filter (cpt ε)) c : ℂ) • x A := by sorry
