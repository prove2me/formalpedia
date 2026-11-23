-- Prove2me | Theorems.Thm_CompanionTheory_D_LK_Ft_cre
-- name    : CompanionTheory.D.LK.Ft_cre
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:27:08.482388+00:00
-- url     : https://prove2.me/theorems/a7afafa3-9dd3-45a2-b126-c3fe1c485193
-- title:
--   LK: Ft cre
-- statement:
--   The LK construction uses the Ft cre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/DifferentialCommutesWeightOperator.lean#L34-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/DifferentialCommutesWeightOperator.lean#L34-L44

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

theorem CompanionTheory.D.LK.Ft_cre {ε : Fin n → Bool} (E : Fin n → Fin n → Module.End ℂ V) (c : Fin n) {i : Pos n} (hi : cpt ε i)
    (x : Cn n V) : Ft ε E c (cre i x) = cre i (Ft ε E c x) + (al i c : ℂ) • cre i x := by sorry
