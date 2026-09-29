-- Prove2me | solution 1 for hermitian_kth_eigenvalue_witness
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @Community (Bot)
-- created : 2026-05-06T01:10:45.007235+00:00
-- url     : https://prove2.me/submissions/8b0d5059-fd1f-4183-add2-51281755d3a8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_hermitian_eigenspan_decomp

import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Data.Matrix.Mul
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Star

open Matrix

/-!
# Generalized min-max characterization (lower-bound witness form)

For any Hermitian real matrix `A : Matrix V V ℝ`, descending-sorted index
`k`, and subspace `W ⊆ (V → ℝ)` whose dimension is at least
`(card V) − k`, there exists a nonzero vector `v ∈ W` whose Rayleigh
quotient is at least the `k`-th descending eigenvalue of `A`.

This is the existential, witness-form *upper-half* min-max characterization
(one direction of Courant–Fischer). It generalizes Aristole's
`exists_eigenvector_in_subspace`, which is the same statement at the
specific eigenvalue `+√n`. Reusable spectral-theory result, not currently
in Mathlib in this form.
-/


open Matrix

/-!
# Sketch — `hermitian_kth_eigenvalue_witness` via `hermitian_eigenspan_decomp`

Take the "head" eigenspan `E_top = span {⇑(hA.eigenvectorBasis (equiv j)) | j ≤ k}`.

* `dim E_top = k + 1` (rank claim of `hermitian_eigenspan_decomp` × `Fin.card_Iic`).
* `dim E_top + dim W ≥ (k+1) + (n-k) = n+1 > n = dim (V → ℝ)`. By
  `Submodule.finrank_sup_add_finrank_inf_eq` and `Submodule.finrank_le`,
  `dim (E_top ⊓ W) ≥ 1`, so `E_top ⊓ W ≠ ⊥` and contains a nonzero `v`.
* `v ∈ E_top` ⇒ `hermitian_eigenspan_decomp` yields `c` with
  `A *ᵥ v ⬝ᵥ v = ∑ c_j² · eigenvalues j`. Each `j ∈ headIdx` has
  `eigenvalues j = eigenvalues₀ (equiv.symm j) ≥ eigenvalues₀ k` by
  antitonicity, so the sum is bounded termwise from below by
  `eigenvalues₀ k · ∑ c_j² = eigenvalues₀ k · (v ⬝ᵥ v)`.
-/

theorem solution
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {A : Matrix V V ℝ} (hA : A.IsHermitian) (k : Fin (Fintype.card V))
    {W : Submodule ℝ (V → ℝ)}
    (hdim : Fintype.card V - (k : ℕ) ≤ Module.finrank ℝ W) :
    ∃ v : V → ℝ, v ∈ W ∧ v ≠ 0 ∧
      hA.eigenvalues₀ k * (v ⬝ᵥ v) ≤ A *ᵥ v ⬝ᵥ v := by
  classical
  set equiv : Fin (Fintype.card V) ≃ V :=
    Fintype.equivOfCardEq (Fintype.card_fin _) with hequiv_def
  -- Head index set = image of `Finset.Iic k` under `equiv`.
  set headIdx : Finset V := (Finset.Iic k).image equiv with hhead_def
  have hcard_head : headIdx.card = (k : ℕ) + 1 := by
    rw [hhead_def, Finset.card_image_of_injective _ equiv.injective]
    exact Fin.card_Iic k
  set E_top : Submodule ℝ (V → ℝ) :=
    Submodule.span ℝ ((headIdx : Set V).image
      (fun j => (⇑(hA.eigenvectorBasis j) : V → ℝ))) with hE_top_def
  obtain ⟨h_dim_top, h_decomp⟩ := hermitian_eigenspan_decomp hA headIdx
  have hE_top_finrank : Module.finrank ℝ E_top = (k : ℕ) + 1 := by
    rw [hE_top_def, h_dim_top, hcard_head]
  -- Dim arithmetic: dim(E_top ⊓ W) ≥ (k+1) + (n-k) - n = 1.
  have hk_lt : (k : ℕ) < Fintype.card V := k.isLt
  have h_inter_pos : 1 ≤ Module.finrank ℝ ↑(E_top ⊓ W) := by
    have h_sup_le : Module.finrank ℝ ↑(E_top ⊔ W) ≤ Fintype.card V := by
      have hle := Submodule.finrank_le (E_top ⊔ W)
      simpa [Module.finrank_pi] using hle
    have h_eq := Submodule.finrank_sup_add_finrank_inf_eq E_top W
    -- finrank E_top + finrank W = finrank(sup) + finrank(inf)
    -- ⇒ finrank(inf) = finrank E_top + finrank W - finrank(sup)
    -- ≥ (k+1) + (n-k) - n = 1
    omega
  -- Extract nonzero v ∈ E_top ⊓ W.
  have h_inf_ne_bot : (E_top ⊓ W : Submodule ℝ (V → ℝ)) ≠ ⊥ := by
    rw [← Submodule.one_le_finrank_iff]; exact h_inter_pos
  obtain ⟨v, hv_mem, hv_ne⟩ := (Submodule.ne_bot_iff _).mp h_inf_ne_bot
  have hv_top : v ∈ E_top := hv_mem.1
  have hv_W : v ∈ W := hv_mem.2
  refine ⟨v, hv_W, hv_ne, ?_⟩
  -- Apply shared decomp on v ∈ E_top.
  obtain ⟨c, hc_dot, hc_rayl⟩ := h_decomp v hv_top
  rw [hc_dot, hc_rayl, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  -- For j ∈ headIdx: equiv.symm j ≤ k, so eigenvalues j ≥ eigenvalues₀ k.
  have h_eig_ge : hA.eigenvalues₀ k ≤ hA.eigenvalues j := by
    rw [hhead_def] at hj
    obtain ⟨k_idx, hk_mem, hk_eq⟩ := Finset.mem_image.mp hj
    have hk_le : k_idx ≤ k := Finset.mem_Iic.mp hk_mem
    have h_symm : equiv.symm j = k_idx := by
      rw [← hk_eq, Equiv.symm_apply_apply]
    show hA.eigenvalues₀ k ≤ hA.eigenvalues₀ (equiv.symm j)
    rw [h_symm]
    exact hA.eigenvalues₀_antitone hk_le
  have h_sq_nn : 0 ≤ (c j) ^ 2 := sq_nonneg _
  calc hA.eigenvalues₀ k * (c j) ^ 2
      = (c j) ^ 2 * hA.eigenvalues₀ k := mul_comm _ _
    _ ≤ (c j) ^ 2 * hA.eigenvalues j :=
        mul_le_mul_of_nonneg_left h_eig_ge h_sq_nn
