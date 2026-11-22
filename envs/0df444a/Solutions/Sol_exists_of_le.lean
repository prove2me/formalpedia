-- Prove2me | solution 1 for exists_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:45:39.14454+00:00
-- url     : https://prove2.me/submissions/c1151700-a95e-49fa-9c1b-08052829c8f0

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
import Theorems.Thm_exists_finite_of_le
import Theorems.Thm_hasPolychromColouring_neg
import Theorems.Thm_hasPolychromColouring_univ
attribute [local simp] hasPolychromColouring_neg
attribute [local simp] hasPolychromColouring_univ



set_option autoImplicit true
open Finset
open Pointwise
variable {G : Type*} [AddCommGroup G]
open MeasureTheory ProbabilityTheory
theorem _root_.solution {k m : ℕ} {S : Finset G} (hm : #S = m) (hm₂ : 2 ≤ m) (hk : k ≠ 0)
    (hkm : polychromColouringBound k m) :
    HasPolychromColouring (Fin k) S := by
-- ANCHOR_END: exists_of_le
  classical
  have (X : Finset G) : ∃ χ : G → Fin k, ∀ x ∈ X, ∀ (c : Fin k), ∃ i ∈ x +ᵥ S, χ i = c :=
    exists_finite_of_le X hm hm₂ hk hkm
  choose g hg using this
  obtain ⟨χ, hχ⟩ := Finset.rado_selection (α := G) (β := fun _ ↦ Fin k) g
  refine ⟨χ, ?_⟩
  rw [isPolychrom_iff]
  intro x c
  obtain ⟨X, hxX, hX⟩ := hχ (x +ᵥ insert 0 S)
  obtain ⟨i, hi, hi'⟩ := hg X x (hxX (mem_vadd_finset.2 ⟨0, by simp⟩)) c
  refine ⟨i, hi, ?_⟩
  rw [hX _ _, hi']
  apply vadd_finset_subset_vadd_finset _ hi
  simp
