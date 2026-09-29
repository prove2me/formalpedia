-- Prove2me | solution 1 for hermitian_eigenspan_decomp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-05-06T01:23:46.675556+00:00
-- url     : https://prove2.me/submissions/14893eed-c88e-43d7-9e53-5b848cff8e33

import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Star

open Matrix

/-!
# Spectral decomposition on a subspace spanned by eigenvectors

Fundamental primitive of Hermitian-matrix spectral theory: pick any subset
`S` of indices into the eigenbasis of a Hermitian matrix `A`, form the
subspace spanned by the corresponding eigenvectors (viewed as functions
`V → ℝ`). Then:

* the dimension of that subspace equals `S.card` (orthonormal basis ⇒
  linear independence ⇒ rank = card);
* every vector in the span admits a coefficient function `c : V → ℝ` such
  that the Euclidean dot products on both `v` and `A *ᵥ v` reduce to
  squared / weighted-squared sums over `S`.

This is exactly the content needed to bound Rayleigh quotients on
eigenvector subspaces — the heart of the Courant–Fischer min-max
characterization. Both the lower-bound (`hermitian_kth_eigenvalue_witness`)
and upper-bound (`hermitian_kth_eigenvalue_dual_witness`) primitives reduce
to this lemma plus a one-line antitone-monotonicity argument.

Not currently in Mathlib in this form.
-/


open Matrix

/-!
# Full proof — `hermitian_eigenspan_decomp`
-/

theorem solution
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {A : Matrix V V ℝ} (hA : A.IsHermitian) (S : Finset V) :
    Module.finrank ℝ
        (Submodule.span ℝ ((S : Set V).image
          (fun j => (⇑(hA.eigenvectorBasis j) : V → ℝ)))) = S.card ∧
    ∀ v : V → ℝ,
      v ∈ Submodule.span ℝ ((S : Set V).image
          (fun j => (⇑(hA.eigenvectorBasis j) : V → ℝ))) →
      ∃ c : V → ℝ,
        v ⬝ᵥ v = ∑ j ∈ S, (c j) ^ 2 ∧
        A *ᵥ v ⬝ᵥ v = ∑ j ∈ S, (c j) ^ 2 * hA.eigenvalues j := by
  classical
  set e : V → V → ℝ := fun j => ⇑(hA.eigenvectorBasis j) with he_def
  -- Orthonormality bridge: e j ⬝ᵥ e k = if j = k then 1 else 0.
  have h_dot_evec : ∀ j k : V, e j ⬝ᵥ e k = if j = k then 1 else 0 := by
    intro j k
    have h_orth : Orthonormal ℝ ⇑hA.eigenvectorBasis :=
      hA.eigenvectorBasis.orthonormal
    have h_inner :
        @inner ℝ _ _ (hA.eigenvectorBasis j) (hA.eigenvectorBasis k)
          = if j = k then 1 else 0 :=
      orthonormal_iff_ite.mp h_orth j k
    have h_inner_eq :
        @inner ℝ _ _ (hA.eigenvectorBasis j) (hA.eigenvectorBasis k)
          = e j ⬝ᵥ e k := by
      -- inner ⟨x, y⟩_ℝ = ofLp y ⬝ᵥ star (ofLp x) = e k ⬝ᵥ e j; commute on ℝ.
      change (hA.eigenvectorBasis k).ofLp ⬝ᵥ star ((hA.eigenvectorBasis j).ofLp)
          = e j ⬝ᵥ e k
      change e k ⬝ᵥ star (e j) = e j ⬝ᵥ e k
      rw [show (star (e j) : V → ℝ) = e j from funext (fun _ => star_trivial _)]
      exact dotProduct_comm _ _
    rw [← h_inner_eq]; exact h_inner
  -- Eigenequation.
  have h_eig : ∀ j : V, A *ᵥ e j = hA.eigenvalues j • e j := fun j =>
    hA.mulVec_eigenvectorBasis j
  -- Linear independence on S.
  have h_li : LinearIndependent ℝ (fun j : (S : Set V) => e j.val) := by
    rw [linearIndependent_iff']
    intro T g hsum k hk_mem
    have h_zero : (∑ j ∈ T, g j • e j.val) ⬝ᵥ e k.val = 0 := by
      rw [hsum]; exact zero_dotProduct _
    rw [sum_dotProduct] at h_zero
    have h_term : ∀ j ∈ T,
        (g j • e j.val) ⬝ᵥ e k.val = if j = k then g j else 0 := by
      intro j _
      rw [smul_dotProduct, h_dot_evec, smul_eq_mul]
      by_cases h : j = k
      · rw [if_pos h, if_pos (by rw [h])]; ring
      · rw [if_neg h, if_neg (fun heq => h (Subtype.ext heq))]; ring
    rw [Finset.sum_congr rfl h_term] at h_zero
    rw [Finset.sum_ite_eq' T k] at h_zero
    simpa [hk_mem] using h_zero
  -- Part 1: dim of span = card S.
  have h_dim_span :
      Module.finrank ℝ
          (Submodule.span ℝ ((S : Set V).image (fun j => e j))) = S.card := by
    have h_eq : ((S : Set V).image (fun j => e j))
        = Set.range (fun j : (S : Set V) => e j.val) := by
      ext x; simp [Set.mem_image, Set.mem_range, Subtype.exists]
    rw [h_eq, finrank_span_eq_card h_li]
    simp
  refine ⟨h_dim_span, ?_⟩
  intro v hv
  rw [show ((S : Set V).image (fun j => e j))
      = ((S.image e) : Set (V → ℝ)) from by simp [Finset.coe_image]] at hv
  rw [Submodule.mem_span_finset] at hv
  obtain ⟨f, _, hf_sum⟩ := hv
  let c : V → ℝ := fun j => f (e j)
  have h_e_inj : Set.InjOn e (S : Set V) := by
    intro j₁ hj₁ j₂ hj₂ heq
    by_contra h_ne
    have h_self : e j₁ ⬝ᵥ e j₁ = 1 := by rw [h_dot_evec]; simp
    have h_cross : e j₁ ⬝ᵥ e j₂ = 0 := by rw [h_dot_evec, if_neg h_ne]
    nth_rewrite 2 [heq] at h_self
    linarith
  have hv_eq : v = ∑ j ∈ S, c j • e j := by
    have h1 : v = ∑ a ∈ S.image e, f a • a := hf_sum.symm
    have h2 : ∑ a ∈ S.image e, f a • a = ∑ j ∈ S, f (e j) • e j :=
      Finset.sum_image h_e_inj
    rw [h1, h2]
  refine ⟨c, ?_, ?_⟩
  · -- v ⬝ᵥ v = ∑ j ∈ S, (c j)^2.
    rw [hv_eq, sum_dotProduct]
    apply Finset.sum_congr rfl
    intro j hj
    rw [dotProduct_sum]
    rw [Finset.sum_eq_single j]
    · rw [smul_dotProduct, dotProduct_smul, h_dot_evec, if_pos rfl,
          smul_eq_mul, smul_eq_mul]
      ring
    · intro k _ hk_ne
      rw [smul_dotProduct, dotProduct_smul, h_dot_evec,
          if_neg (fun h => hk_ne h.symm), smul_eq_mul, smul_eq_mul]
      ring
    · intro hj_not; exact (hj_not hj).elim
  · -- A *ᵥ v ⬝ᵥ v = ∑ j ∈ S, (c j)^2 * eigenvalues j.
    rw [hv_eq]
    have h_Av : A *ᵥ ∑ j ∈ S, c j • e j = ∑ j ∈ S, c j • hA.eigenvalues j • e j := by
      rw [Matrix.mulVec_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [Matrix.mulVec_smul, h_eig j]
    rw [h_Av, sum_dotProduct]
    apply Finset.sum_congr rfl
    intro j hj
    rw [dotProduct_sum]
    rw [Finset.sum_eq_single j]
    · rw [smul_dotProduct, smul_dotProduct,
          dotProduct_smul, h_dot_evec, if_pos rfl,
          smul_eq_mul, smul_eq_mul, smul_eq_mul]
      ring
    · intro k _ hk_ne
      rw [smul_dotProduct, smul_dotProduct,
          dotProduct_smul, h_dot_evec,
          if_neg (fun h => hk_ne h.symm),
          smul_eq_mul, smul_eq_mul, smul_eq_mul]
      ring
    · intro hj_not; exact (hj_not hj).elim
