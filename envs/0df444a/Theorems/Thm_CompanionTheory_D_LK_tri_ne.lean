-- Prove2me | Theorems.Thm_CompanionTheory_D_LK_tri_ne
-- name    : CompanionTheory.D.LK.tri_ne
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T06:25:47.814801+00:00
-- url     : https://prove2.me/theorems/91da34c2-97d0-4f52-8fb4-13a3b9d6bf3b
-- title:
--   LK: tri ne
-- statement:
--   The LK construction uses the tri ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/DifferentialBoundedSupport.lean#L38-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/DifferentialBoundedSupport.lean#L38-L43

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

theorem CompanionTheory.D.LK.tri_ne {i j k : Pos n} {x : Cn n V} {A : Finset (Pos n)} (h : cre k (ann j (ann i x)) A ≠ 0) :
    k ∈ A ∧ j ∉ A.erase k ∧ i ∉ insert j (A.erase k) ∧ x (insert i (insert j (A.erase k))) ≠ 0 := by sorry
