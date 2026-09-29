-- Prove2me | solution 1 for nonempty_closed_matrix_set_has_frobenius_sq_minimizer
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-06-23T05:35:22.628663+00:00
-- url     : https://prove2.me/submissions/3fa15332-c692-44a0-8afc-bb33d81a5aec

import Mathlib.Tactic
import Definitions.Def_matrix_completion_tangent

open MatrixCompletion
open scoped BigOperators Classical

/-!
Source: Candès–Recht 2009 (arXiv:0805.4471 v3) / CACM 55(6) 2012, §4.1, the
least-squares dual certificate construction.  The candidate certificate is
defined as the minimal-Frobenius-norm solution of the feasibility problem
(eqs (4.5)–(4.6): minimize ‖Y‖_F over the affine constraint set), and the proof
silently uses the standard fact that a nonempty *closed* subset of the
finite-dimensional matrix space attains a Frobenius-norm minimizer.  This file
supplies exactly that existence-of-minimizer fact (stated with the
square-root-free `frobeniusNormSq`).

This is a paper-backed analytic prerequisite, not an improvised step: it is the
Weierstrass extreme-value argument (continuous coercive objective attains its
infimum on a closed set in finite dimension) underlying the §4.1 least-squares
certificate.
-/

/-- `frobeniusNormSq` is continuous on the matrix space (finite sum of squared
coordinate projections). -/
private theorem fro_cont {n₁ n₂ : ℕ} :
    Continuous (fun X : Matrix (Fin n₁) (Fin n₂) ℝ => frobeniusNormSq X) := by
  unfold frobeniusNormSq
  apply continuous_finset_sum; intro i _
  apply continuous_finset_sum; intro j _
  exact (continuous_apply j).comp (continuous_apply i) |>.pow 2

/-- Each entry's square is bounded by the full Frobenius-norm-square (all
summands are nonnegative). -/
private theorem entry_sq_le_fro {n₁ n₂ : ℕ} (X : Matrix (Fin n₁) (Fin n₂) ℝ)
    (i : Fin n₁) (j : Fin n₂) : (X i j) ^ 2 ≤ frobeniusNormSq X := by
  unfold frobeniusNormSq
  calc (X i j) ^ 2 ≤ ∑ b : Fin n₂, (X i b) ^ 2 := by
            apply Finset.single_le_sum (f := fun b => (X i b) ^ 2)
            · intro b _; positivity
            · exact Finset.mem_univ j
    _ ≤ ∑ a : Fin n₁, ∑ b : Fin n₂, (X a b) ^ 2 := by
            apply Finset.single_le_sum (f := fun a => ∑ b : Fin n₂, (X a b) ^ 2)
            · intro a _; positivity
            · exact Finset.mem_univ i

/-- A nonempty closed subset of the finite-dimensional real-matrix space attains
a minimizer of the squared Frobenius norm. -/
theorem solution {n₁ n₂ : ℕ} (C : Set (Matrix (Fin n₁) (Fin n₂) ℝ)) :
    C.Nonempty → IsClosed C →
    ∃ Y : Matrix (Fin n₁) (Fin n₂) ℝ,
      Y ∈ C ∧ ∀ Z : Matrix (Fin n₁) (Fin n₂) ℝ,
        Z ∈ C → frobeniusNormSq Y ≤ frobeniusNormSq Z := by
  intro hne hcl
  obtain ⟨c0, hc0⟩ := hne
  set f : Matrix (Fin n₁) (Fin n₂) ℝ → ℝ := fun X => frobeniusNormSq X with hf
  set B : ℝ := Real.sqrt (f c0) with hB
  -- the compact entrywise box `∏ Icc (-B) B`
  set box : Set (Matrix (Fin n₁) (Fin n₂) ℝ) :=
    Set.univ.pi (fun _ : Fin n₁ => Set.univ.pi (fun _ : Fin n₂ => Set.Icc (-B) B)) with hbox
  have hbox_compact : IsCompact box :=
    isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_Icc))
  have hbox_mem : ∀ Z : Matrix (Fin n₁) (Fin n₂) ℝ,
      (∀ i j, Z i j ∈ Set.Icc (-B) B) → Z ∈ box := by
    intro Z h
    rw [hbox]
    exact Set.mem_univ_pi.mpr (fun i => Set.mem_univ_pi.mpr (fun j => h i j))
  -- restrict to the closed sublevel set `f ≤ f c0`
  set K : Set (Matrix (Fin n₁) (Fin n₂) ℝ) := C ∩ {Z | f Z ≤ f c0} with hK
  have hKne : K.Nonempty := ⟨c0, hc0, by simp [hf]⟩
  have hsub_closed : IsClosed {Z : Matrix (Fin n₁) (Fin n₂) ℝ | f Z ≤ f c0} :=
    isClosed_le fro_cont continuous_const
  have hKcl : IsClosed K := hcl.inter hsub_closed
  have hfc0_nonneg : 0 ≤ f c0 := by
    show 0 ≤ frobeniusNormSq c0
    unfold frobeniusNormSq; positivity
  -- `K` is a closed subset of the compact box, hence compact
  have hKbox : K ⊆ box := by
    intro Z hZ
    apply hbox_mem
    intro i j
    have hZf : f Z ≤ f c0 := hZ.2
    have hsq : (Z i j) ^ 2 ≤ f c0 := le_trans (entry_sq_le_fro Z i j) hZf
    have habs : |Z i j| ≤ B := by
      rw [hB, ← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt hsq
    rw [abs_le] at habs
    exact ⟨habs.1, habs.2⟩
  have hKcomp : IsCompact K := hbox_compact.of_isClosed_subset hKcl hKbox
  -- continuous objective attains its minimum on the nonempty compact `K`
  obtain ⟨Y, hYK, hYmin⟩ := hKcomp.exists_isMinOn hKne (fro_cont.continuousOn)
  refine ⟨Y, hYK.1, ?_⟩
  intro Z hZ
  by_cases hZK : Z ∈ K
  · exact hYmin hZK
  · -- `Z ∉ K` while `Z ∈ C` forces `f c0 < f Z`, and `f Y ≤ f c0`
    have hZgt : f c0 < f Z := by
      by_contra h; push_neg at h; exact hZK ⟨hZ, h⟩
    have hYc0 : f Y ≤ f c0 := hYK.2
    exact le_of_lt (lt_of_le_of_lt hYc0 hZgt)
