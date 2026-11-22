-- Prove2me | solution 1 for prob_bad_event
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:43:00.213177+00:00
-- url     : https://prove2.me/submissions/856d7e2e-a044-4d72-81f7-5d5513298568

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
import Theorems.Thm_P2M_pi_pi__7f25e995c05a
import Theorems.Thm_hasPolychromColouring_neg
import Theorems.Thm_hasPolychromColouring_univ
attribute [local simp] hasPolychromColouring_neg
attribute [local simp] hasPolychromColouring_univ



set_option autoImplicit true
open Finset
open Pointwise
variable {G : Type*} [AddCommGroup G]
open MeasureTheory ProbabilityTheory
theorem _root_.solution [DecidableEq G] {k m : ℕ} {S X : Finset G} {x : X} (hm : #S = m) (hk : k ≠ 0) :
    (Measure.pi (fun _ ↦ uniformOn Set.univ) : Measure (X + S → Fin k)).real
      {χ : X + S → Fin k | ∃ c, ∀ s : S, χ ⟨x + s, add_mem_add x.2 s.2⟩ ≠ c} ≤
        k * (1 - (k : ℝ)⁻¹) ^ m := by
  have : Nonempty (Fin k) := Fin.pos_iff_nonempty.1 (by grind)
  set add : X → S → X + S := fun x s ↦ ⟨x + s, add_mem_add x.2 s.2⟩
  set P : Measure (X + S → Fin k) := Measure.pi (fun _ ↦ uniformOn Set.univ)
  have : {χ : X + S → Fin k | ∃ c, ∀ s : S, χ ⟨x + s, add_mem_add x.2 s.2⟩ ≠ c} =
      ⋃ c : Fin k, (add x '' Set.univ : Set (X + S)).pi fun _ ↦ {c}ᶜ := by
    ext χ
    simp only [ne_eq, Subtype.forall, Set.mem_setOf_eq, Set.image_univ, Set.mem_iUnion,
      Set.mem_pi, Set.mem_range, Subtype.exists, Set.mem_compl_iff, Set.mem_singleton_iff,
      forall_exists_index, Subtype.mk.injEq, add]
    peel with c
    constructor
    · rintro h y hy s hs rfl
      exact h _ hs
    · rintro h s hs
      exact h _ _ _ hs rfl
  calc
    _ = P.real (⋃ c : Fin k, (add x '' Set.univ).pi fun _ ↦ {c}ᶜ) := by rw [this]
    _ ≤ ∑ c, P.real ((add x '' Set.univ).pi fun _ ↦ {c}ᶜ) := measureReal_iUnion_fintype_le _
    _ = ∑ c, P.real ((univ.image (add x) : Set (X + S)).pi fun _ ↦ {c}ᶜ) := by simp
    _ = ∑ c : Fin k, ((Measure.count {c}ᶜ).toReal / k) ^ #(S.attach.image (add x)) := by
      simp only [Measure.real_def, P, pi_pi']
      simp [uniformOn_univ]
    _ = ∑ c : Fin k, ((k - 1 : ℝ) / k) ^ #S := by
      congr! with c hc
      · have : ({c}ᶜ : Set (Fin k)) = ({c}ᶜ : Finset (Fin k)) := by simp
        rw [this, Measure.count_apply_finset, ENNReal.toReal_natCast, Finset.card_compl,
          Fintype.card_fin, card_singleton, Nat.cast_sub (by lia), Nat.cast_one]
      · rw [card_image_of_injective, card_attach]
        simp [Function.Injective, add]
    _ = k * (1 - (k : ℝ)⁻¹) ^ m := by simp [sub_div, field, hk, hm]
