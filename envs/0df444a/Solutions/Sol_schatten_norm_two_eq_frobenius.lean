-- Prove2me | solution 1 for schatten_norm_two_eq_frobenius
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-06-23T17:50:50.864312+00:00
-- url     : https://prove2.me/submissions/097f4900-844f-4991-9503-520364e08eb2

import Definitions.Def_matrix_completion_schatten
import Definitions.Def_matrix_completion_tangent
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Trace

/-!
F2 — Schatten 2-norm equals the Frobenius norm.
Equivalently `∑ σ_k(X)² = ‖X‖_F²`.
Source: Candès–Recht 2009 (arXiv:0805.4471), §6.1 lines 1633-1635.

Self-contained: the operator-SVD reconstruction toolkit (SVDProbe) is the same one used
in the ACCEPTED Sol_C1_trace_duality; here it is reduced to the trace identity
`∑ σ_k² = ∑_j ‖T e_j‖²` (trace of `T*∘T`, basis-independent).
-/

open Module InnerProductSpace LinearMap Matrix
open scoped BigOperators

namespace SVDProbe

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

noncomputable abbrev gram (T : E →ₗ[ℝ] F) : E →ₗ[ℝ] E := adjoint T ∘ₗ T

theorem gram_symm (T : E →ₗ[ℝ] F) : (gram T).IsSymmetric :=
  T.isSymmetric_adjoint_comp_self

noncomputable def rsv (T : E →ₗ[ℝ] F) {n : ℕ} (hn : finrank ℝ E = n) :
    OrthonormalBasis (Fin n) ℝ E :=
  (gram_symm T).eigenvectorBasis hn

noncomputable def evals (T : E →ₗ[ℝ] F) {n : ℕ} (hn : finrank ℝ E = n) : Fin n → ℝ :=
  (gram_symm T).eigenvalues hn

noncomputable def sval (T : E →ₗ[ℝ] F) {n : ℕ} (_hn : finrank ℝ E = n) (k : Fin n) : ℝ :=
  T.singularValues k

theorem sval_sq (T : E →ₗ[ℝ] F) {n : ℕ} (hn : finrank ℝ E = n) (k : Fin n) :
    sval T hn k ^ 2 = evals T hn k := by
  unfold sval evals
  rw [T.sq_singularValues_fin hn k]

theorem inner_Tv (T : E →ₗ[ℝ] F) (a b : E) :
    inner ℝ (T a) (T b) = inner ℝ (gram T a) b := by
  unfold gram
  rw [LinearMap.comp_apply, ← LinearMap.adjoint_inner_left]

theorem inner_Tv_eig (T : E →ₗ[ℝ] F) {n : ℕ} (hn : finrank ℝ E = n) (i j : Fin n) :
    inner ℝ (T (rsv T hn i)) (T (rsv T hn j))
      = if i = j then evals T hn i else 0 := by
  rw [inner_Tv]
  unfold gram rsv evals
  rw [show (adjoint T ∘ₗ T) ((gram_symm T).eigenvectorBasis hn i)
        = (gram T) ((gram_symm T).eigenvectorBasis hn i) from rfl]
  rw [(gram_symm T).apply_eigenvectorBasis hn i]
  rw [inner_smul_left]
  rw [orthonormal_iff_ite.mp ((gram_symm T).eigenvectorBasis hn).orthonormal i j]
  simp only [conj_trivial]
  by_cases h : i = j
  · subst h; rw [if_pos rfl, if_pos rfl, mul_one, RCLike.ofReal_real_eq_id]; rfl
  · rw [if_neg h, if_neg h, mul_zero]

theorem normSq_Tv (T : E →ₗ[ℝ] F) {n : ℕ} (hn : finrank ℝ E = n) (k : Fin n) :
    ‖T (rsv T hn k)‖ ^ 2 = sval T hn k ^ 2 := by
  have heig : inner ℝ (T (rsv T hn k)) (T (rsv T hn k)) = evals T hn k := by
    have h := inner_Tv_eig T hn k k
    rw [if_pos rfl] at h; exact h
  rw [@norm_sq_eq_re_inner ℝ, heig, sval_sq, RCLike.re_to_real]

theorem hsNormSq_eq_trace {ι : Type*} [Fintype ι] (T : E →ₗ[ℝ] F) (b : OrthonormalBasis ι ℝ E) :
    (∑ j, inner ℝ (T (b j)) (T (b j))) = (adjoint T ∘ₗ T).trace ℝ E := by
  rw [LinearMap.trace_eq_sum_inner _ b]
  apply Finset.sum_congr rfl
  intro j _
  rw [LinearMap.comp_apply, ← LinearMap.adjoint_inner_right T (b j) (T (b j))]

theorem sum_sval_sq_eq_sum_normSq {ι : Type*} [Fintype ι] (T : E →ₗ[ℝ] F)
    (b : OrthonormalBasis ι ℝ E) {n : ℕ} (hn : finrank ℝ E = n) :
    (∑ k, sval T hn k ^ 2) = ∑ j, ‖T (b j)‖ ^ 2 := by
  have hr : (∑ k, ‖T (rsv T hn k)‖ ^ 2) = (adjoint T ∘ₗ T).trace ℝ E := by
    have := hsNormSq_eq_trace T (rsv T hn)
    rw [← this]; apply Finset.sum_congr rfl; intro k _
    rw [@norm_sq_eq_re_inner ℝ, RCLike.re_to_real]
  have hb : (∑ j, ‖T (b j)‖ ^ 2) = (adjoint T ∘ₗ T).trace ℝ E := by
    have := hsNormSq_eq_trace T b
    rw [← this]; apply Finset.sum_congr rfl; intro j _
    rw [@norm_sq_eq_re_inner ℝ, RCLike.re_to_real]
  calc (∑ k, sval T hn k ^ 2) = ∑ k, ‖T (rsv T hn k)‖ ^ 2 := by
            apply Finset.sum_congr rfl; intro k _; rw [normSq_Tv]
    _ = (adjoint T ∘ₗ T).trace ℝ E := hr
    _ = ∑ j, ‖T (b j)‖ ^ 2 := hb.symm

end SVDProbe

namespace MatrixCompletion

open SVDProbe

variable {n1 n2 : ℕ}

theorem sum_singularValues_sq_eq_frobeniusSq (X : RealMatrix n1 n2) :
    (∑ k : Fin n2, ((toEuclideanLin X).singularValues k) ^ 2) = frobeniusNormSq X := by
  have hn : finrank ℝ (EuclideanSpace ℝ (Fin n2)) = n2 := finrank_euclideanSpace_fin
  set T := toEuclideanLin X with hT
  have hsum : (∑ k : Fin n2, sval T hn k ^ 2)
      = ∑ j : Fin n2, ‖T (EuclideanSpace.basisFun (Fin n2) ℝ j)‖ ^ 2 :=
    sum_sval_sq_eq_sum_normSq T (EuclideanSpace.basisFun (Fin n2) ℝ) hn
  have hcol : ∀ j : Fin n2,
      ‖T (EuclideanSpace.basisFun (Fin n2) ℝ j)‖ ^ 2 = ∑ i : Fin n1, (X i j) ^ 2 := by
    intro j
    rw [@norm_sq_eq_re_inner ℝ, RCLike.re_to_real, PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [EuclideanSpace.basisFun_apply]
    simp only [hT, toEuclideanLin_apply]
    have hval : (X *ᵥ (EuclideanSpace.single j (1:ℝ)).ofLp) i = X i j := by
      simp only [Matrix.mulVec, EuclideanSpace.ofLp_single, dotProduct_single, mul_one]
    rw [hval]
    rw [show (⟪X i j, X i j⟫_ℝ : ℝ) = X i j * (starRingEnd ℝ) (X i j) from RCLike.inner_apply _ _,
        conj_trivial]
    ring
  have hlhs : (∑ k : Fin n2, (T.singularValues k) ^ 2)
      = ∑ k : Fin n2, sval T hn k ^ 2 := rfl
  rw [hlhs, hsum]
  unfold frobeniusNormSq
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  exact hcol j

theorem schatten_norm_two_eq_frobenius_proof (X : RealMatrix n1 n2) :
    schattenNorm 2 X = frobeniusNorm X := by
  unfold schattenNorm frobeniusNorm
  have hsq : (∑ k : Fin n2, Real.rpow ((toEuclideanLin X).singularValues k) 2)
      = frobeniusNormSq X := by
    rw [← sum_singularValues_sq_eq_frobeniusSq X]
    apply Finset.sum_congr rfl
    intro k _
    have : ((toEuclideanLin X).singularValues k).rpow 2
        = ((toEuclideanLin X).singularValues k) ^ (2:ℝ) := rfl
    rw [this, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  rw [hsq]
  have hhalf : (frobeniusNormSq X).rpow (2:ℝ)⁻¹ = (frobeniusNormSq X) ^ (1/2 : ℝ) := by
    rw [show ((2:ℝ)⁻¹) = (1/2 : ℝ) by norm_num]; rfl
  rw [hhalf, ← Real.sqrt_eq_rpow]

end MatrixCompletion

open MatrixCompletion
open scoped BigOperators

theorem solution (n1 n2 : Nat) (X : MatrixCompletion.RealMatrix n1 n2) :
    MatrixCompletion.schattenNorm 2 X = MatrixCompletion.frobeniusNorm X :=
  MatrixCompletion.schatten_norm_two_eq_frobenius_proof X
