-- Prove2me | solution 1 for schatten_norm_even_pow_eq_trace_row_gram_pow
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-06-23T20:43:35.227209+00:00
-- url     : https://prove2.me/submissions/3c30f942-fa08-4b73-a65a-c6f76eb2934f

import Definitions.Def_matrix_completion_schatten
import Definitions.Def_matrix_completion_tangent
import Mathlib.Analysis.InnerProductSpace.Trace

open MatrixCompletion
open scoped Classical BigOperators InnerProductSpace

noncomputable section

open LinearMap

private theorem eigPowSum_eq_tracePow {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    {n : ℕ} (hn : Module.finrank 𝕜 E = n) {T : E →ₗ[𝕜] E}
    (hT : T.IsSymmetric) (m : ℕ) :
    LinearMap.trace 𝕜 E (T ^ m) = ∑ i, ((hT.eigenvalues hn i : 𝕜)) ^ m := by
  set b := hT.eigenvectorBasis hn with hb
  rw [LinearMap.trace_eq_sum_inner (T ^ m) b]
  apply Fintype.sum_congr
  intro i
  have hev : Module.End.HasEigenvector T (hT.eigenvalues hn i : 𝕜) (b i) :=
    hT.hasEigenvector_eigenvectorBasis hn i
  rw [hev.pow_apply m, inner_smul_right]
  have : ⟪b i, b i⟫_𝕜 = 1 := by simp [b.orthonormal.1 i]
  rw [this, mul_one]

private theorem toEuclideanLin_mul {l m k : ℕ} (A : Matrix (Fin l) (Fin m) ℝ)
    (B : Matrix (Fin m) (Fin k) ℝ) :
    Matrix.toEuclideanLin (A * B) =
      (Matrix.toEuclideanLin A) ∘ₗ (Matrix.toEuclideanLin B) := by
  ext v i
  simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec]

private theorem toEuclideanLin_pow {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (m : ℕ) :
    (Matrix.toEuclideanLin A) ^ m = Matrix.toEuclideanLin (A ^ m) := by
  induction m with
  | zero => ext v i; simp
  | succ k ih =>
    rw [pow_succ, pow_succ, ih, toEuclideanLin_mul, Module.End.mul_eq_comp]

private theorem trace_col_gram_pow_eq_row_gram_pow {n1 n2 : ℕ}
    (X : RealMatrix n1 n2) (n : ℕ) (hn : 1 ≤ n) :
    Matrix.trace ((X.transpose * X) ^ n) = Matrix.trace ((X * X.transpose) ^ n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hn
  rw [show 0 + m + 1 = m + 1 from by ring]
  have key : ∀ j : ℕ, (X.transpose * X) ^ (j + 1)
      = X.transpose * (X * X.transpose) ^ j * X := by
    intro j
    induction j with
    | zero => simp
    | succ k ih =>
      calc (X.transpose * X) ^ (k + 1 + 1)
          = (X.transpose * X) ^ (k + 1) * (X.transpose * X) := by rw [pow_succ]
        _ = (X.transpose * (X * X.transpose) ^ k * X) * (X.transpose * X) := by rw [ih]
        _ = X.transpose * ((X * X.transpose) ^ k * (X * X.transpose)) * X := by
              simp only [Matrix.mul_assoc]
        _ = X.transpose * (X * X.transpose) ^ (k + 1) * X := by
              rw [← pow_succ]
  rw [key m]
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, ← pow_succ]

theorem solution (n : ℕ) (hn : 1 ≤ n)
    {n1 n2 : ℕ} (X : RealMatrix n1 n2) :
    schattenNorm (2 * n) X ^ (2 * n) = Matrix.trace ((X * X.transpose) ^ n) := by
  rw [← trace_col_gram_pow_eq_row_gram_pow X n hn]
  set T := Matrix.toEuclideanLin X with hT
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin n2)) = n2 := by simp
  set q : ℝ := 2 * (n : ℝ) with hq
  have hqpos : (0 : ℝ) < q := by rw [hq]; positivity
  have hq_natCast : ((2 * n : ℕ) : ℝ) = q := by rw [hq]; push_cast; ring
  have hsum_nonneg : (0 : ℝ) ≤ ∑ k : Fin n2, Real.rpow (T.singularValues k) q := by
    apply Finset.sum_nonneg
    intro k _
    exact Real.rpow_nonneg (T.singularValues_nonneg k) q
  have hround : schattenNorm (2 * n) X ^ (2 * n) =
      ∑ k : Fin n2, Real.rpow (T.singularValues k) q := by
    rw [schattenNorm]
    set S : ℝ := ∑ k : Fin n2, Real.rpow (T.singularValues k) q with hS
    have hSnn : (0 : ℝ) ≤ S := hsum_nonneg
    calc (Real.rpow S q⁻¹) ^ (2 * n)
        = Real.rpow (Real.rpow S q⁻¹) (((2 * n : ℕ) : ℝ)) :=
          (Real.rpow_natCast (Real.rpow S q⁻¹) (2 * n)).symm
      _ = Real.rpow (Real.rpow S q⁻¹) q := by rw [hq_natCast]
      _ = Real.rpow S (q⁻¹ * q) := (Real.rpow_mul hSnn _ _).symm
      _ = Real.rpow S 1 := by rw [inv_mul_cancel₀ (ne_of_gt hqpos)]
      _ = S := Real.rpow_one S
  rw [hround]
  have hsym : (T.adjoint ∘ₗ T).IsSymmetric := T.isSymmetric_adjoint_comp_self
  have hstep2 : ∀ k : Fin n2, Real.rpow (T.singularValues k) q =
      (hsym.eigenvalues hfin k) ^ n := by
    intro k
    have hsq : (T.singularValues k) ^ 2 = hsym.eigenvalues hfin k :=
      T.sq_singularValues_fin hfin k
    calc Real.rpow (T.singularValues k) q
        = Real.rpow (T.singularValues k) ((2 * n : ℕ) : ℝ) := by rw [hq_natCast]
      _ = (T.singularValues k) ^ (2 * n) := Real.rpow_natCast _ (2 * n)
      _ = ((T.singularValues k) ^ 2) ^ n := by rw [pow_mul]
      _ = (hsym.eigenvalues hfin k) ^ n := by rw [hsq]
  rw [Finset.sum_congr rfl (fun k _ => hstep2 k)]
  have heig : (∑ k : Fin n2, (hsym.eigenvalues hfin k) ^ n) =
      LinearMap.trace ℝ _ ((T.adjoint ∘ₗ T) ^ n) := by
    rw [eigPowSum_eq_tracePow hfin hsym n]; push_cast; rfl
  rw [heig]
  have hadj : (T.adjoint ∘ₗ T) = Matrix.toEuclideanLin (X.transpose * X) := by
    have hXt : X.transpose = X.conjTranspose := by
      ext i j; rw [Matrix.conjTranspose_apply, Matrix.transpose_apply, star_trivial]
    rw [hT, hXt, toEuclideanLin_mul, Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    try rfl
  rw [hadj, toEuclideanLin_pow, Matrix.toEuclideanLin_eq_toLin_orthonormal,
    Matrix.trace_toLin_eq]

#print axioms solution

end
