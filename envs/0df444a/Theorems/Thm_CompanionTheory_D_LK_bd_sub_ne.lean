-- Prove2me | Theorems.Thm_CompanionTheory_D_LK_bd_sub_ne
-- name    : CompanionTheory.D.LK.bd_sub_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:27:06.502259+00:00
-- url     : https://prove2.me/theorems/9f0b47e3-f9fc-4fea-a4b2-2c3811939d37
-- title:
--   LK: bd sub ne
-- statement:
--   The LK construction uses the bd sub ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/DifferentialBoundedSupport.lean#L50-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/DifferentialBoundedSupport.lean#L50-L72

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

theorem CompanionTheory.D.LK.bd_sub_ne {ε₀ ε : Fin n → Bool} (h0 : ∀ a b, ε a = ε b → ε₀ a = ε₀ b) (E : Fin n → Fin n → Module.End ℂ V)
    (x : Cn n V) (A : Finset (Pos n)) (h : bd ε₀ E x A ≠ bd ε E x A) :
    (∃ i, cpt ε₀ i ∧ ¬cpt ε i ∧ ann i x A ≠ 0) ∨
      ∃ i j k, Tri ε₀ i j k ∧ ¬(cpt ε i ∧ cpt ε j) ∧ cre k (ann j (ann i x)) A ≠ 0 := by sorry
