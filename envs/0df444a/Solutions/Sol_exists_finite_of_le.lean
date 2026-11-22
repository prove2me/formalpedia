-- Prove2me | solution 1 for exists_finite_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:44:54.320026+00:00
-- url     : https://prove2.me/submissions/4252aa29-0cba-4b8f-b91c-4074b1438997

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
import Theorems.Thm_standardCondition_lovasz
import Theorems.Thm_prob_bad_event
import Theorems.Thm_card_neighbour
import Theorems.Thm_nonempty_of_uniformOn_apply_pos
import Theorems.Thm_hasPolychromColouring_neg
import Theorems.Thm_hasPolychromColouring_univ
import Theorems.Thm_lopsidedCondition_of_standardCondition
import Theorems.Thm_symmetricLocalLemma
attribute [local simp] hasPolychromColouring_neg
attribute [local simp] hasPolychromColouring_univ



set_option autoImplicit true
open Finset
open Pointwise
variable {G : Type*} [AddCommGroup G]
open MeasureTheory ProbabilityTheory
theorem _root_.solution [DecidableEq G] {k m : ℕ} (X : Finset G) {S : Finset G} (hm : #S = m)
    (hm₂ : 2 ≤ m) (hk : k ≠ 0) (hkm : polychromColouringBound k m) :
    ∃ χ : G → Fin k, ∀ x ∈ X, ∀ c : Fin k, ∃ i ∈ x +ᵥ S, χ i = c := by
  let Y : Finset G := X + S
  have : NeZero k := ⟨hk⟩
  let add : X → S → Y := fun x s ↦ ⟨x + s, add_mem_add x.2 s.2⟩
  let A (x : X) : Set (Y → Fin k) := {χ | ∃ c, ∀ s, χ (add x s) ≠ c}
  let D : X → Finset Y := fun x ↦ S.attach.image (fun s ↦ add x s)
  let N : X → Finset X := fun x ↦ X.attach.filter (fun i ↦ x.1 - i.1 ∈ (S - S).erase 0)
  let P : Measure (Y → Fin k) := Measure.pi fun _ ↦ uniformOn Set.univ
  have hP : P = uniformOn Set.univ := by simp only [P, ← uniformOn_pi, Set.pi_univ]
  have hPAN : standardCondition P A N := standardCondition_lovasz hk
  let p : ℝ := k * (1 - (k : ℝ)⁻¹) ^ m
  have hp (x : X) : P.real (A x) ≤ p := prob_bad_event hm hk
  have hp₀ : 0 ≤ p := by
    apply mul_nonneg (by positivity) (pow_nonneg _ _)
    simp only [sub_nonneg]
    apply inv_le_one_of_one_le₀ (by simp; lia)
  have hm₀ : m * (m - 1) ≠ 0 := by
    have : 0 < m * (m - 1) := mul_pos (by grind) (by grind)
    exact this.ne'
  have :  0 < P.real (⋂ i, (A i)ᶜ) := by
    apply symmetricLocalLemma (fun i ↦ .of_discrete) hm₀ (p := p)
      (d := m * (m - 1)) (lopsidedCondition_of_standardCondition hPAN) hp
      (fun i ↦ card_neighbour hm)
    calc
      Real.exp 1 * p * ((m * (m - 1) : ℕ) + 1) = Real.exp 1 * p * (m * (m - 1) + 1) := by
          have : 1 ≤ m := by lia
          simp [this]
      _ = _ := by simp only [p]; ring
      _ ≤ _ := hkm
  have : (⋂ i, (A i)ᶜ).Nonempty := by
    rw [hP, Measure.real_def, ENNReal.toReal_pos_iff] at this
    simpa using nonempty_of_uniformOn_apply_pos this.1
  obtain ⟨χ, hχ⟩ := this
  refine ⟨fun g ↦ if hg : g ∈ Y then χ ⟨g, hg⟩ else 0, ?_⟩
  intro x hx c
  simp only [ne_eq, Subtype.forall, Set.mem_iInter, Set.mem_compl_iff, Set.mem_setOf_eq, not_exists,
    not_forall, Decidable.not_not, A, add] at hχ
  obtain ⟨s, hs, hc⟩ := hχ x hx c
  refine ⟨x + s, ?_⟩
  simp [add_mem_add, hx, hs, Y, hc]
