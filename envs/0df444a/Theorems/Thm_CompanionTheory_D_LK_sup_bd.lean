-- Prove2me | Theorems.Thm_CompanionTheory_D_LK_sup_bd
-- name    : CompanionTheory.D.LK.sup_bd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:26:43.454346+00:00
-- url     : https://prove2.me/theorems/883caff1-220b-4169-b3c1-33c5e592eaf7
-- title:
--   LK: sup bd
-- statement:
--   The LK construction uses the sup bd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/DifferentialBoundedSupport.lean#L96-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/DifferentialBoundedSupport.lean#L96-L112

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

theorem CompanionTheory.D.LK.sup_bd {ε : Fin n → Bool} (E : Fin n → Fin n → Module.End ℂ V) {B : Finset (Pos n)} {j : ℕ} {x : Cn n V}
    (hx : Sup ε B j x) {A : Finset (Pos n)} (h : bd ε E x A ≠ 0) :
    (A.filter fun i => ¬cpt ε i) = B ∧ (A.filter (cpt ε)).card + 1 = j := by sorry
