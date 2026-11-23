-- Prove2me | Theorems.Thm_CompanionTheory_D_LK_bd_ne
-- name    : CompanionTheory.D.LK.bd_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:50:31.387889+00:00
-- url     : https://prove2.me/theorems/4781a8ac-e675-45d2-9b7d-9aed2ca4fb73
-- title:
--   LK: bd ne
-- statement:
--   The LK construction uses the bd ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/DifferentialBoundedSupport.lean#L74-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/DifferentialBoundedSupport.lean#L74-L88

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

theorem CompanionTheory.D.LK.bd_ne (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (x : Cn n V) (A : Finset (Pos n))
    (h : bd ε E x A ≠ 0) :
    (∃ i, cpt ε i ∧ ann i x A ≠ 0) ∨ ∃ i j k, Tri ε i j k ∧ cre k (ann j (ann i x)) A ≠ 0 := by sorry
