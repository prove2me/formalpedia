-- Prove2me | solution 1 for standardCondition_lovasz
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:42:51.971233+00:00
-- url     : https://prove2.me/submissions/bf33e9df-48f8-4e33-bb65-384ef437efe5

import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.NNRat.Floor
import Mathlib.Tactic.Rify
import Definitions.Def_Polychromatic_Colouring
import Definitions.Def_Polychromatic_Compactness
import Definitions.Def_Polychromatic_LocalLemma
import Definitions.Def_Polychromatic_Existence
import Theorems.Thm_hasPolychromColouring_neg
import Theorems.Thm_hasPolychromColouring_univ
import Theorems.Thm_standardCondition_of
attribute [local simp] hasPolychromColouring_neg
attribute [local simp] hasPolychromColouring_univ



set_option autoImplicit true
open Finset
open Pointwise
variable {G : Type*} [AddCommGroup G]
open MeasureTheory ProbabilityTheory
theorem _root_.solution [DecidableEq G] {k : ℕ} {S X : Finset G} (hk : k ≠ 0) :
    standardCondition
      (Measure.pi (fun _ ↦ uniformOn Set.univ))
      (fun x : X ↦ {χ : X + S → Fin k | ∃ c, ∀ s : S, χ ⟨x + s, add_mem_add x.2 s.2⟩ ≠ c})
      (fun x : X ↦ X.attach.filter (fun i ↦ x.1 - i.1 ∈ (S - S).erase 0)) := by
  have : Nonempty (Fin k) := Fin.pos_iff_nonempty.1 (by grind)
  set add : X → S → X + S := fun x s ↦ ⟨x + s, add_mem_add x.2 s.2⟩
  set D : X → Finset (X + S) := fun x ↦ S.attach.image (fun s ↦ add x s)
  refine standardCondition_of _ D ?_ (by fun_prop)
    (iIndepFun_pi (X := fun i x ↦ x) (by fun_prop)) ?_
  · simp only [ne_eq, mem_erase, mem_sub, mem_filter, mem_attach, true_and, not_and, not_exists,
      disjoint_left, mem_image, Subtype.exists, forall_exists_index, Subtype.forall, mem_add,
      Subtype.mk.injEq, and_imp, D, add]
    rintro x₁ hx₁ x₂ hx₂ hne hS _ x₃ hx₃ s₁ hs₁ rfl s₂ hs₂ h s₃ hs₃ h'
    exact hS (by grind) s₂ hs₂ s₃ hs₃ (by grind)
  · rintro x
    refine ⟨{χ : X + S → Fin k | ∃ c, ∀ s : S, χ ⟨x + s, add_mem_add x.2 s.2⟩ ≠ c},
      MeasurableSet.of_discrete, ?_, rfl⟩
    simp only [DependsOn, coe_image, coe_attach, Set.image_univ, Set.mem_range, Subtype.exists,
      forall_exists_index, Subtype.forall, Subtype.mk.injEq, Set.mem_setOf_eq, eq_iff_iff, D,
      add]
    intro χ₁ χ₂ h
    peel with c s hs
    rw [h _ _ _ hs rfl]
