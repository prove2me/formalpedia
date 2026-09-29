-- Prove2me | solution 1 for general_rademacher_matrix_2p_trace_moment_general_index
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-06-25T03:10:59.770642+00:00
-- url     : https://prove2.me/submissions/9cb75840-cf82-4d1d-895d-f3196710c850

import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Reflection
import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_general_rademacher_matrix_2p_trace_moment
import Theorems.Thm_eigenvalue_le_of_quadratic_form_le
import Theorems.Thm_trace_pow_reindex

open Matrix
open scoped BigOperators

/-- **General-index Rademacher matrix trace-moment engine.**
The engine `general_rademacher_matrix_2p_trace_moment` (b6bf4feb) is stated for matrices indexed
by `Fin d`.  This node lifts it to an arbitrary finite index type `μ` (the dilation family used in
the Schatten assembly lives over `Fin n₁ ⊕ Fin n₂`), with `d := Fintype.card μ`.  The reduction
reindexes the whole family along an equivalence `μ ≃ Fin (card μ)`, transports the quadratic-form
bound (which feeds `eigenvalue_le_of_quadratic_form_le`), and transports the trace-moment back via
`trace_pow_reindex`.

The variance hypothesis is given in **quadratic-form** shape
`star v ⬝ᵥ V *ᵥ v ≤ normV * (star v ⬝ᵥ v)` (with `V = ∑ c, H c * H c`); this is exactly what the
block-diagonal Schatten assembly produces and is equivalent to the eigenvalue bound for the
Hermitian `V`. -/
theorem solution
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {μ : Type*} [Fintype μ] [DecidableEq μ]
    (H : ι → Matrix μ μ ℝ) (hHerm : ∀ c, (H c).IsHermitian)
    (normV : ℝ) (hnormVnn : 0 ≤ normV)
    (hVHerm : (∑ c : ι, H c * H c).IsHermitian)
    (hquad : ∀ v : μ → ℝ,
      (star v ⬝ᵥ (∑ c : ι, H c * H c) *ᵥ v) ≤ normV * (star v ⬝ᵥ v))
    (p : ℕ) :
    (∑ eps : Finset ι, ((1 : ℝ) / 2) ^ (Fintype.card ι)
        * Matrix.trace ((∑ c : ι, (if c ∈ eps then (1 : ℝ) else -1) • H c) ^ (2 * p)))
      ≤ ((Nat.factorial (2 * p) : ℝ) / ((2 ^ p : ℝ) * (Nat.factorial p : ℝ)))
          * normV ^ p * (Fintype.card μ : ℝ) := by
  classical
  -- choose an equivalence μ ≃ Fin (card μ)
  set d : ℕ := Fintype.card μ with hd
  set e : μ ≃ Fin d := Fintype.equivFin μ with he
  -- reindexed family
  set H' : ι → Matrix (Fin d) (Fin d) ℝ := fun c => (H c).reindex e e with hH'
  -- distribution helpers
  have hreindex_mul : ∀ (A B : Matrix μ μ ℝ),
      (A * B).reindex e e = (A.reindex e e) * (B.reindex e e) := by
    intro A B
    simp only [Matrix.reindex_apply]
    rw [← Matrix.submatrix_mul_equiv A B e.symm e.symm e.symm]
  have hreindex_sum : ∀ (s : Finset ι) (f : ι → Matrix μ μ ℝ),
      (∑ c ∈ s, f c).reindex e e = ∑ c ∈ s, (f c).reindex e e := by
    intro s f
    ext i j; simp [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.sum_apply]
  have hreindex_smul : ∀ (s : ℝ) (A : Matrix μ μ ℝ),
      (s • A).reindex e e = s • (A.reindex e e) := by
    intro s A
    ext i j; simp [Matrix.reindex_apply, Matrix.submatrix_apply]
  -- H' is Hermitian
  have hHerm' : ∀ c, (H' c).IsHermitian := by
    intro c
    show ((H c).reindex e e).IsHermitian
    rw [Matrix.reindex_apply]
    exact (isHermitian_submatrix_equiv e.symm).mpr (hHerm c)
  -- V' = ∑ H'c * H'c = V.reindex e e
  have hVeq : (∑ c : ι, H' c * H' c) = (∑ c : ι, H c * H c).reindex e e := by
    rw [hreindex_sum]
    apply Finset.sum_congr rfl
    intro c _
    rw [hH', hreindex_mul]
  -- V' is Hermitian
  have hVHerm' : (∑ c : ι, H' c * H' c).IsHermitian := by
    rw [hVeq, Matrix.reindex_apply]
    exact (isHermitian_submatrix_equiv e.symm).mpr hVHerm
  -- quadratic-form bound transports to V', then gives eigenvalue bound for V'
  have hquad' : ∀ w : Fin d → ℝ,
      (star w ⬝ᵥ (∑ c : ι, H' c * H' c) *ᵥ w) ≤ normV * (star w ⬝ᵥ w) := by
    intro w
    rw [hVeq]
    -- transport quadratic form to μ side via change of variable w ↦ w ∘ e
    have htrans : (star w ⬝ᵥ ((∑ c : ι, H c * H c).reindex e e) *ᵥ w)
        = (star (w ∘ e) ⬝ᵥ (∑ c : ι, H c * H c) *ᵥ (w ∘ e)) := by
      simp only [Matrix.reindex_apply]
      rw [Matrix.submatrix_mulVec_equiv, dotProduct_comp_equiv_symm]
      congr 1
    rw [htrans]
    have hww : (star w ⬝ᵥ w) = (star (w ∘ e) ⬝ᵥ (w ∘ e)) := by
      simp only [dotProduct, Pi.star_apply, Function.comp_apply]
      rw [← Equiv.sum_comp e]
    rw [hww]
    exact hquad (w ∘ e)
  have hnormV' : ∀ i, hVHerm'.eigenvalues i ≤ normV := by
    intro i
    exact eigenvalue_le_of_quadratic_form_le _ hVHerm' normV hquad' i
  -- apply the Fin d engine
  have hEngine := general_rademacher_matrix_2p_trace_moment H' hHerm' normV hnormVnn hVHerm' hnormV' p
  -- the RHS dimension factor is (d : ℝ) = (card μ : ℝ)
  -- transport the LHS traces: trace((∑ sign•H'c)^(2p)) = trace((∑ sign•Hc)^(2p))
  have htraceLHS : ∀ eps : Finset ι,
      Matrix.trace ((∑ c : ι, (if c ∈ eps then (1 : ℝ) else -1) • H' c) ^ (2 * p))
        = Matrix.trace ((∑ c : ι, (if c ∈ eps then (1 : ℝ) else -1) • H c) ^ (2 * p)) := by
    intro eps
    have hsumeq : (∑ c : ι, (if c ∈ eps then (1 : ℝ) else -1) • H' c)
        = (∑ c : ι, (if c ∈ eps then (1 : ℝ) else -1) • H c).reindex e e := by
      rw [hreindex_sum]
      apply Finset.sum_congr rfl
      intro c _
      rw [hH', hreindex_smul]
    rw [hsumeq, trace_pow_reindex]
  -- rewrite the engine LHS into the μ-indexed LHS
  have hLHSeq :
      (∑ eps : Finset ι, ((1 : ℝ) / 2) ^ (Fintype.card ι)
          * Matrix.trace ((∑ c : ι, (if c ∈ eps then (1 : ℝ) else -1) • H' c) ^ (2 * p)))
        = (∑ eps : Finset ι, ((1 : ℝ) / 2) ^ (Fintype.card ι)
            * Matrix.trace ((∑ c : ι, (if c ∈ eps then (1 : ℝ) else -1) • H c) ^ (2 * p))) := by
    apply Finset.sum_congr rfl
    intro eps _
    rw [htraceLHS eps]
  rw [hLHSeq] at hEngine
  -- (d : ℝ) = (Fintype.card μ : ℝ) is definitional (d := Fintype.card μ)
  exact hEngine

#print axioms solution
