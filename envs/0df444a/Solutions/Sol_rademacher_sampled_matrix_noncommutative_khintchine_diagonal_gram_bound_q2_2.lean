-- Prove2me | solution 2 for rademacher_sampled_matrix_noncommutative_khintchine_diagonal_gram_bound_q2
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:49:25.150583+00:00
-- url     : https://prove2.me/submissions/0ecf6faa-56cd-492d-a691-dc448240019b

import Mathlib
import Definitions.Def_matrix_completion_gram_schatten

set_option autoImplicit false

namespace KhintchineProof

-- Accepted proof by LukeBernese; submission f0c8827c-b0b4-4398-a1de-943a010a1a2f.
-- Original source SHA-256: e179132c747dec438d0584f784de63d674b03882f04ac6c395d8ae1024ed490d.
namespace KhintchineDependency0
open scoped BigOperators

theorem sum_rpow_le_card_rpow_mul_sum_rpow {N : ℕ}
    (σ : Fin N → ℝ) (hσ : ∀ k, 0 ≤ σ k) (q s : ℝ) (hq : 0 < q) (hqs : q ≤ s) :
    (∑ k, (σ k) ^ q) ≤ (N : ℝ) ^ (1 - q / s) * (∑ k, (σ k) ^ s) ^ (q / s) := by
  classical
  have hs : 0 < s := lt_of_lt_of_le hq hqs
  set p : ℝ := s / q with hp
  have hp1 : 1 ≤ p := by rw [hp, le_div_iff₀ hq]; linarith
  have hf0 : ∀ k, (0:ℝ) ≤ (σ k) ^ q := fun k => Real.rpow_nonneg (hσ k) q
  have hHolder := Real.inner_le_weight_mul_Lp_of_nonneg (Finset.univ : Finset (Fin N)) hp1
    (fun _ => (1:ℝ)) (fun k => (σ k) ^ q) (fun _ => zero_le_one) hf0
  simp only [one_mul] at hHolder
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hHolder
  have hfp : ∀ k, ((σ k) ^ q) ^ p = (σ k) ^ s := by
    intro k
    rw [← Real.rpow_mul (hσ k)]
    congr 1
    rw [hp]; field_simp
  simp only [hfp] at hHolder
  have hpinv : p⁻¹ = q / s := by rw [hp, inv_div]
  rw [hpinv] at hHolder
  exact hHolder
end KhintchineDependency0
export KhintchineDependency0 (sum_rpow_le_card_rpow_mul_sum_rpow)

-- Accepted proof by Hartmann_Psi; submission 3c30f942-fa08-4b73-a65a-c6f76eb2934f.
-- Original source SHA-256: 6e3161e85e966669a33bfa6ca9b09bf7bccb217535c22fbefddaf26eac687d23.
namespace KhintchineDependency1
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

theorem schatten_norm_even_pow_eq_trace_row_gram_pow (n : ℕ) (hn : 1 ≤ n)
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



end
end KhintchineDependency1
export KhintchineDependency1 (schatten_norm_even_pow_eq_trace_row_gram_pow)

-- Accepted proof by LukeBernese; submission f9d78012-3f6a-4ba3-8837-1f7fa7c9eb1b.
-- Original source SHA-256: cbce2d6c296065f9b3dc4d9932796112c28931f611fb58e88d8d207e04257f7d.
namespace KhintchineDependency2
open Matrix
open scoped BigOperators

theorem trace_dilation_even_pow {n1 n2 : ℕ} (S : Matrix (Fin n1) (Fin n2) ℝ) (n : ℕ) :
    Matrix.trace ((Matrix.fromBlocks 0 S Sᵀ 0) ^ (2 * n))
      = Matrix.trace ((S * Sᵀ) ^ n) + Matrix.trace ((Sᵀ * S) ^ n) := by
  classical
  -- ℋ^(2n) = blockdiag((S Sᵀ)^n, (Sᵀ S)^n)
  have dilation_sq : (Matrix.fromBlocks 0 S Sᵀ 0) ^ 2
      = Matrix.fromBlocks (S * Sᵀ) 0 0 (Sᵀ * S) := by
    rw [pow_two, Matrix.fromBlocks_multiply]
    simp
  have dilation_even_pow : ∀ k : ℕ, (Matrix.fromBlocks 0 S Sᵀ 0) ^ (2 * k)
      = Matrix.fromBlocks ((S * Sᵀ) ^ k) 0 0 ((Sᵀ * S) ^ k) := by
    intro k
    induction k with
    | zero => simp [Matrix.fromBlocks_one]
    | succ j ih =>
        have h2 : 2 * (j + 1) = 2 * j + 2 := by ring
        rw [h2, pow_add, ih, dilation_sq, Matrix.fromBlocks_multiply]
        simp [pow_succ]
  -- trace of a block matrix = trace TL + trace BR
  have trace_fromBlocks : ∀ (A : Matrix (Fin n1) (Fin n1) ℝ) (B : Matrix (Fin n1) (Fin n2) ℝ)
      (C : Matrix (Fin n2) (Fin n1) ℝ) (D : Matrix (Fin n2) (Fin n2) ℝ),
      Matrix.trace (Matrix.fromBlocks A B C D) = Matrix.trace A + Matrix.trace D := by
    intro A B C D
    simp only [Matrix.trace, Matrix.diag_apply]
    rw [Fintype.sum_sum_type]
    simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂]
  rw [dilation_even_pow, trace_fromBlocks]
end KhintchineDependency2
export KhintchineDependency2 (trace_dilation_even_pow)

-- Accepted proof by Harry_Xu; submission 2ab3c601-dc90-4b3b-826d-cb441bf86a9b.
-- Original source SHA-256: a75cf62123fd0fa5acbf34f6847904327a2dfe154308fff6cd1ddf1c553df0ba.
namespace KhintchineDependency3
open Matrix
open scoped BigOperators
open scoped MatrixOrder

theorem general_rademacher_matrix_2p_trace_moment
    {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}
    (H : ι → Matrix (Fin d) (Fin d) ℝ)
    (hHerm : ∀ c, (H c).IsHermitian)
    (normV : ℝ) (hnormVnn : 0 ≤ normV)
    (hVHerm : (∑ c : ι, H c * H c).IsHermitian)
    (hnormV : ∀ i, hVHerm.eigenvalues i ≤ normV)
    (p : ℕ) :
    (∑ eps : Finset ι, ((1 : ℝ) / 2) ^ (Fintype.card ι)
        * Matrix.trace ((∑ c : ι, (if c ∈ eps then (1 : ℝ) else -1) • H c) ^ (2 * p)))
      ≤ ((Nat.factorial (2 * p) : ℝ) / ((2 ^ p : ℝ) * (Nat.factorial p : ℝ)))
          * normV ^ p * (d : ℝ) := by
  classical
  let doubleFactOdd : ℕ → ℝ :=
    fun p => (Nat.factorial (2 * p) : ℝ) / ((2 ^ p : ℝ) * (Nat.factorial p : ℝ))
  let sgn : Finset ι → ι → ℝ := fun eps c => if c ∈ eps then 1 else -1
  let Ex : (Finset ι → ℝ) → ℝ :=
    fun F => ∑ eps : Finset ι, ((1 : ℝ) / 2) ^ Fintype.card ι * F eps
  let Xmat : Finset ι → Matrix (Fin d) (Fin d) ℝ :=
    fun eps => ∑ c : ι, (sgn eps c) • H c
  let Rest : ι → Finset ι → Matrix (Fin d) (Fin d) ℝ :=
    fun c eps => ∑ c' ∈ (Finset.univ.erase c), (sgn eps c') • H c'
  let VarProxy : Matrix (Fin d) (Fin d) ℝ := ∑ c : ι, H c * H c

  have trace_mul_nonneg_of_posSemidef
      {B A : Matrix (Fin d) (Fin d) ℝ} (hB : B.PosSemidef) (hA : A.PosSemidef) :
      0 ≤ Matrix.trace (B * A) := by
    obtain ⟨X, hX⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg
    rw [hX]
    have hXA : (X * A * Xᴴ).PosSemidef := hA.mul_mul_conjTranspose_same X
    have htrace : 0 ≤ Matrix.trace (X * A * Xᴴ) := hXA.trace_nonneg
    convert htrace using 1
    calc
      Matrix.trace ((star X * X) * A) = Matrix.trace ((Xᴴ * X) * A) := by
        rw [Matrix.star_eq_conjTranspose]
      _ = Matrix.trace (A * Xᴴ * X) := Matrix.trace_mul_cycle Xᴴ X A
      _ = Matrix.trace (X * A * Xᴴ) := Matrix.trace_mul_cycle A Xᴴ X

  have norm_smul_one_sub_posSemidef {M : Matrix (Fin d) (Fin d) ℝ}
      (hM : M.IsHermitian) (normM : ℝ) (hnorm : ∀ i, hM.eigenvalues i ≤ normM) :
      (normM • (1 : Matrix (Fin d) (Fin d) ℝ) - M).PosSemidef := by
    let U : Matrix (Fin d) (Fin d) ℝ := hM.eigenvectorUnitary
    let D : Matrix (Fin d) (Fin d) ℝ := diagonal fun i => normM - hM.eigenvalues i
    have hD : D.PosSemidef := by
      dsimp [D]
      exact Matrix.PosSemidef.diagonal (fun i => sub_nonneg.mpr (hnorm i))
    have hUDU : (U * D * Uᴴ).PosSemidef := by
      simpa [U] using hD.mul_mul_conjTranspose_same U
    convert hUDU using 1
    dsimp [U, D]
    have hU : (↑hM.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ) *
        (↑hM.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)ᴴ = 1 := by
      simpa [Matrix.star_eq_conjTranspose] using
        (Unitary.coe_mul_star_self hM.eigenvectorUnitary)
    conv_lhs => rw [hM.spectral_theorem]
    rw [← hU]
    rw [← Matrix.smul_mul normM
      (↑hM.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)
      ((↑hM.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)ᴴ)]
    rw [Matrix.smul_eq_mul_diagonal
      (↑hM.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ) normM]
    have hdiag :
        diagonal (fun i : Fin d => normM - hM.eigenvalues i) =
          (diagonal (fun _ : Fin d => normM) - diagonal hM.eigenvalues :
            Matrix (Fin d) (Fin d) ℝ) := by
      rw [diagonal_sub]
    simp [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
    rw [hdiag]
    noncomm_ring

  have tropp_fact_2_2 (M A : Matrix (Fin d) (Fin d) ℝ)
      (hM : M.IsHermitian) (hA : A.PosSemidef) (normM : ℝ)
      (hnorm : ∀ i, hM.eigenvalues i ≤ normM) :
      Matrix.trace (M * A) ≤ normM * Matrix.trace A := by
    let B : Matrix (Fin d) (Fin d) ℝ := normM • 1 - M
    have hB : B.PosSemidef := by
      simpa [B] using norm_smul_one_sub_posSemidef hM normM hnorm
    have hnonneg : 0 ≤ Matrix.trace (B * A) :=
      trace_mul_nonneg_of_posSemidef hB hA
    have htrace : 0 ≤ normM * Matrix.trace A - Matrix.trace (M * A) := by
      simpa [B, Matrix.sub_mul, Matrix.trace_sub, Matrix.trace_smul] using hnonneg
    linarith

  have scalar_bound (lam mu : ℝ) (r q : ℕ) (hq : q ≤ 2 * r) :
      lam ^ q * mu ^ (2 * r - q) + lam ^ (2 * r - q) * mu ^ q
        ≤ lam ^ (2 * r) + mu ^ (2 * r) := by
    let p := 2 * r - q
    change lam ^ q * mu ^ p + lam ^ p * mu ^ q ≤ lam ^ (2 * r) + mu ^ (2 * r)
    have hpq : q + p = 2 * r := by
      dsimp [p]
      exact Nat.add_sub_of_le hq
    have hpar : Even p ↔ Even q := by
      dsimp [p]
      rw [Nat.even_sub hq]
      have h2r : Even (2 * r) := even_two_mul r
      simp [h2r]
    have hprod : 0 ≤ (lam ^ q - mu ^ q) * (lam ^ p - mu ^ p) := by
      rcases Nat.even_or_odd q with hqe | hqo
      · have hpe : Even p := hpar.mpr hqe
        by_cases hle : |mu| ≤ |lam|
        · have hqle : mu ^ q ≤ lam ^ q := by
            calc
              mu ^ q = |mu| ^ q := (hqe.pow_abs mu).symm
              _ ≤ |lam| ^ q := pow_le_pow_left₀ (abs_nonneg mu) hle q
              _ = lam ^ q := hqe.pow_abs lam
          have hple : mu ^ p ≤ lam ^ p := by
            calc
              mu ^ p = |mu| ^ p := (hpe.pow_abs mu).symm
              _ ≤ |lam| ^ p := pow_le_pow_left₀ (abs_nonneg mu) hle p
              _ = lam ^ p := hpe.pow_abs lam
          exact mul_nonneg (sub_nonneg.mpr hqle) (sub_nonneg.mpr hple)
        · have hle' : |lam| ≤ |mu| := le_of_not_ge hle
          have hqle : lam ^ q ≤ mu ^ q := by
            calc
              lam ^ q = |lam| ^ q := (hqe.pow_abs lam).symm
              _ ≤ |mu| ^ q := pow_le_pow_left₀ (abs_nonneg lam) hle' q
              _ = mu ^ q := hqe.pow_abs mu
          have hple : lam ^ p ≤ mu ^ p := by
            calc
              lam ^ p = |lam| ^ p := (hpe.pow_abs lam).symm
              _ ≤ |mu| ^ p := pow_le_pow_left₀ (abs_nonneg lam) hle' p
              _ = mu ^ p := hpe.pow_abs mu
          exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hqle) (sub_nonpos.mpr hple)
      · have hpe : Odd p := by
          refine Nat.not_even_iff_odd.mp ?_
          intro hpe
          exact (Nat.not_even_iff_odd.mpr hqo) (hpar.mp hpe)
        by_cases hle : mu ≤ lam
        · have hqle : mu ^ q ≤ lam ^ q := hqo.strictMono_pow.monotone hle
          have hple : mu ^ p ≤ lam ^ p := hpe.strictMono_pow.monotone hle
          exact mul_nonneg (sub_nonneg.mpr hqle) (sub_nonneg.mpr hple)
        · have hle' : lam ≤ mu := le_of_not_ge hle
          have hqle : lam ^ q ≤ mu ^ q := hqo.strictMono_pow.monotone hle'
          have hple : lam ^ p ≤ mu ^ p := hpe.strictMono_pow.monotone hle'
          exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hqle) (sub_nonpos.mpr hple)
    have hmain :
        lam ^ q * mu ^ p + lam ^ p * mu ^ q ≤ lam ^ q * lam ^ p + mu ^ q * mu ^ p := by
      nlinarith [hprod]
    calc
      lam ^ q * mu ^ p + lam ^ p * mu ^ q
          ≤ lam ^ q * lam ^ p + mu ^ q * mu ^ p := hmain
      _ = lam ^ (q + p) + mu ^ (q + p) := by
        rw [pow_add, pow_add]
      _ = lam ^ (2 * r) + mu ^ (2 * r) := by
        rw [hpq]

  have hermitian_pow_eq (A : Matrix (Fin d) (Fin d) ℝ)
      (hA : A.IsHermitian) (k : ℕ) :
      A ^ k =
        (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ) *
          diagonal (fun i => hA.eigenvalues i ^ k) *
          (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)ᴴ := by
    conv_lhs => rw [hA.spectral_theorem]
    rw [← map_pow ((Unitary.conjStarAlgAut ℝ (Matrix (Fin d) (Fin d) ℝ)) hA.eigenvectorUnitary)
      (diagonal (RCLike.ofReal ∘ hA.eigenvalues)) k]
    simp [Unitary.conjStarAlgAut_apply, Matrix.diagonal_pow, Matrix.star_eq_conjTranspose,
      Matrix.mul_assoc]
    congr 1

  have trace_conjTranspose_diagonal_mul_diagonal
      (G : Matrix (Fin d) (Fin d) ℝ) (α β : Fin d → ℝ) :
      Matrix.trace (Gᴴ * diagonal α * G * diagonal β)
        =
      ∑ i : Fin d, ∑ j : Fin d, α i * β j * (G i j) ^ 2 := by
    simp [Matrix.trace, Matrix.mul_apply, Matrix.diagonal, Finset.sum_mul, pow_two]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _hi
    apply Finset.sum_congr rfl
    intro j _hj
    ring

  have trace_basis_change (M : Matrix (Fin d) (Fin d) ℝ)
      (hM : M.IsHermitian) (U V : Matrix (Fin d) (Fin d) ℝ)
      (α β : Fin d → ℝ) :
      Matrix.trace (M * (U * diagonal α * Uᴴ) * M * (V * diagonal β * Vᴴ))
        =
      Matrix.trace (((Uᴴ * M * V)ᴴ) * diagonal α * (Uᴴ * M * V) * diagonal β) := by
    have hMt : Mᵀ = M := by
      simpa [Matrix.star_eq_conjTranspose] using hM.eq
    calc
      Matrix.trace (M * (U * diagonal α * Uᴴ) * M * (V * diagonal β * Vᴴ))
          = Matrix.trace ((M * (U * diagonal α * Uᴴ) * M * (V * diagonal β)) * Vᴴ) := by
            simp [Matrix.mul_assoc]
      _ = Matrix.trace (Vᴴ * (M * (U * diagonal α * Uᴴ) * M * (V * diagonal β))) := by
            rw [Matrix.trace_mul_comm]
      _ = Matrix.trace (((Uᴴ * M * V)ᴴ) * diagonal α * (Uᴴ * M * V) * diagonal β) := by
            simp [Matrix.mul_assoc, hMt]

  have trace_eigenbasis (M W Y : Matrix (Fin d) (Fin d) ℝ)
      (hM : M.IsHermitian) (hW : W.IsHermitian) (hY : Y.IsHermitian)
      (a b : ℕ) :
      Matrix.trace (M * W ^ a * M * Y ^ b)
        =
      ∑ i : Fin d, ∑ j : Fin d,
        hW.eigenvalues i ^ a * hY.eigenvalues j ^ b *
          (((hW.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)ᴴ *
            M * (hY.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)) i j) ^ 2 := by
    let U : Matrix (Fin d) (Fin d) ℝ := hW.eigenvectorUnitary
    let V : Matrix (Fin d) (Fin d) ℝ := hY.eigenvectorUnitary
    let G : Matrix (Fin d) (Fin d) ℝ := Uᴴ * M * V
    calc
      Matrix.trace (M * W ^ a * M * Y ^ b)
          = Matrix.trace
              (M * (U * diagonal (fun i => hW.eigenvalues i ^ a) * Uᴴ) *
                M * (V * diagonal (fun j => hY.eigenvalues j ^ b) * Vᴴ)) := by
            dsimp [U, V]
            conv_lhs =>
              rw [hermitian_pow_eq W hW a, hermitian_pow_eq Y hY b]
      _ = Matrix.trace (Gᴴ * diagonal (fun i => hW.eigenvalues i ^ a) *
            G * diagonal (fun j => hY.eigenvalues j ^ b)) := by
            simpa [G] using
              trace_basis_change M hM U V
                (fun i => hW.eigenvalues i ^ a) (fun j => hY.eigenvalues j ^ b)
      _ = ∑ i : Fin d, ∑ j : Fin d,
            hW.eigenvalues i ^ a * hY.eigenvalues j ^ b *
              (((hW.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)ᴴ *
                M * (hY.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)) i j) ^ 2 := by
            simpa [G, U, V] using
              trace_conjTranspose_diagonal_mul_diagonal G
                (fun i => hW.eigenvalues i ^ a) (fun j => hY.eigenvalues j ^ b)

  have tropp_fact_2_4 (M W Y : Matrix (Fin d) (Fin d) ℝ)
      (hM : M.IsHermitian) (hW : W.IsHermitian) (hY : Y.IsHermitian)
      (r q : ℕ) (hq : q ≤ 2 * r) :
      Matrix.trace (M * W ^ q * M * Y ^ (2 * r - q))
          + Matrix.trace (M * W ^ (2 * r - q) * M * Y ^ q)
        ≤ Matrix.trace (M * M * (W ^ (2 * r) + Y ^ (2 * r))) := by
    let p := 2 * r - q
    let G : Matrix (Fin d) (Fin d) ℝ :=
      (hW.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)ᴴ *
        M * (hY.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)
    have hRHS :
        Matrix.trace (M * M * (W ^ (2 * r) + Y ^ (2 * r)))
          =
        Matrix.trace (M * W ^ (2 * r) * M * Y ^ 0)
          + Matrix.trace (M * W ^ 0 * M * Y ^ (2 * r)) := by
      rw [Matrix.mul_add, Matrix.trace_add]
      simp [Matrix.mul_assoc]
      simpa [Matrix.mul_assoc] using (Matrix.trace_mul_cycle M (W ^ (2 * r)) M).symm
    rw [hRHS]
    rw [trace_eigenbasis M W Y hM hW hY q p,
      trace_eigenbasis M W Y hM hW hY p q,
      trace_eigenbasis M W Y hM hW hY (2 * r) 0,
      trace_eigenbasis M W Y hM hW hY 0 (2 * r)]
    dsimp [p, G]
    calc
      (∑ i : Fin d, ∑ j : Fin d,
            hW.eigenvalues i ^ q * hY.eigenvalues j ^ (2 * r - q) *
              (((hW.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)ᴴ *
                M * (hY.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)) i j) ^ 2)
          +
          (∑ i : Fin d, ∑ j : Fin d,
            hW.eigenvalues i ^ (2 * r - q) * hY.eigenvalues j ^ q *
              (((hW.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)ᴴ *
                M * (hY.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)) i j) ^ 2)
          =
          ∑ i : Fin d, ∑ j : Fin d,
            (hW.eigenvalues i ^ q * hY.eigenvalues j ^ (2 * r - q) *
                (((hW.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)ᴴ *
                  M * (hY.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)) i j) ^ 2
              +
              hW.eigenvalues i ^ (2 * r - q) * hY.eigenvalues j ^ q *
                (((hW.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)ᴴ *
                  M * (hY.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)) i j) ^ 2) := by
            simp [Finset.sum_add_distrib]
      _ ≤ ∑ i : Fin d, ∑ j : Fin d,
            (hW.eigenvalues i ^ (2 * r) * hY.eigenvalues j ^ 0 *
                (((hW.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)ᴴ *
                  M * (hY.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)) i j) ^ 2
              +
              hW.eigenvalues i ^ 0 * hY.eigenvalues j ^ (2 * r) *
                (((hW.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)ᴴ *
                  M * (hY.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)) i j) ^ 2) := by
            apply Finset.sum_le_sum
            intro i _hi
            apply Finset.sum_le_sum
            intro j _hj
            have hs := scalar_bound (hW.eigenvalues i) (hY.eigenvalues j) r q hq
            have hsq :
                0 ≤
                  (((hW.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)ᴴ *
                    M * (hY.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)) i j) ^ 2 :=
              sq_nonneg _
            nlinarith [mul_le_mul_of_nonneg_right hs hsq]
      _ =
          (∑ i : Fin d, ∑ j : Fin d,
            hW.eigenvalues i ^ (2 * r) * hY.eigenvalues j ^ 0 *
              (((hW.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)ᴴ *
                M * (hY.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)) i j) ^ 2)
          +
          (∑ i : Fin d, ∑ j : Fin d,
            hW.eigenvalues i ^ 0 * hY.eigenvalues j ^ (2 * r) *
              (((hW.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)ᴴ *
                M * (hY.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)) i j) ^ 2) := by
            simp [Finset.sum_add_distrib]

  have doubleFactOdd_zero : doubleFactOdd 0 = 1 := by
    simp [doubleFactOdd]

  have doubleFactOdd_succ (p : ℕ) :
      doubleFactOdd (p + 1) = (2 * p + 1 : ℝ) * doubleFactOdd p := by
    simp only [doubleFactOdd]
    have hfac2 : (Nat.factorial (2 * (p + 1)) : ℝ)
        = (2 * (p + 1) : ℝ) * (2 * p + 1 : ℝ) * (Nat.factorial (2 * p) : ℝ) := by
      have h1 : 2 * (p + 1) = (2 * p + 1) + 1 := by ring
      rw [h1, Nat.factorial_succ]
      have h2 : (2 * p + 1) = (2 * p) + 1 := by ring
      rw [h2, Nat.factorial_succ]
      push_cast
      ring
    have hpow : (2 ^ (p + 1) : ℝ) = 2 * 2 ^ p := by rw [pow_succ]; ring
    have hfacp : (Nat.factorial (p + 1) : ℝ) = (p + 1 : ℝ) * (Nat.factorial p : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    rw [hfac2, hpow, hfacp]
    have hp1 : (0 : ℝ) < (p + 1 : ℝ) := by positivity
    have hfp : (0 : ℝ) < (Nat.factorial p : ℝ) := by exact_mod_cast Nat.factorial_pos p
    have hpw : (0 : ℝ) < (2 ^ p : ℝ) := by positivity
    field_simp

  have doubleFactOdd_nonneg (p : ℕ) : 0 ≤ doubleFactOdd p := by
    simp only [doubleFactOdd]
    positivity

  have recursion_iterate (T : ℕ → ℝ) (B e : ℝ) (hB : 0 ≤ B)
      (hT0 : T 0 = e) (hTnn : ∀ p, 0 ≤ T p)
      (hrec : ∀ p, 1 ≤ p → T p ≤ (2 * p - 1 : ℝ) * B * T (p - 1)) :
      ∀ p, T p ≤ doubleFactOdd p * B ^ p * e := by
    intro p
    induction p with
    | zero => simp [hT0, doubleFactOdd_zero]
    | succ k ih =>
      have hstep := hrec (k + 1) (by omega)
      have hidx : (k + 1) - 1 = k := by omega
      rw [hidx] at hstep
      push_cast at hstep
      have hstep' : T (k + 1) ≤ (2 * (k : ℝ) + 1) * B * T k := by
        have : (2 * ((k : ℝ) + 1) - 1) = (2 * (k : ℝ) + 1) := by ring
        calc T (k + 1) ≤ (2 * ((k : ℝ) + 1) - 1) * B * T k := by linarith [hstep]
          _ = (2 * (k : ℝ) + 1) * B * T k := by rw [this]
      have hstep := hstep'
      have hcoefnn : (0 : ℝ) ≤ (2 * k + 1 : ℝ) := by positivity
      calc T (k + 1) ≤ (2 * k + 1 : ℝ) * B * T k := hstep
        _ ≤ (2 * k + 1 : ℝ) * B * (doubleFactOdd k * B ^ k * e) := by
              apply mul_le_mul_of_nonneg_left ih
              exact mul_nonneg hcoefnn hB
        _ = doubleFactOdd (k + 1) * B ^ (k + 1) * e := by
              rw [doubleFactOdd_succ]; ring

  have sgn_sq (eps : Finset ι) (c : ι) : sgn eps c ^ 2 = 1 := by
    by_cases h : c ∈ eps <;> simp [sgn, h]

  have sgn_mul_self (eps : Finset ι) (c : ι) : sgn eps c * sgn eps c = 1 := by
    by_cases h : c ∈ eps <;> simp [sgn, h]

  have Ex_const_mul (a : ℝ) (F : Finset ι → ℝ) :
      Ex (fun eps => a * F eps) = a * Ex F := by
    simp [Ex]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro eps _
    ring

  have Ex_add (F G : Finset ι → ℝ) :
      Ex (fun eps => F eps + G eps) = Ex F + Ex G := by
    simp [Ex]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro eps _
    ring

  have Ex_sub (F G : Finset ι → ℝ) :
      Ex (fun eps => F eps - G eps) = Ex F - Ex G := by
    simp [Ex]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro eps _
    ring

  have Ex_sum_univ (F : ι → Finset ι → ℝ) :
      Ex (fun eps => ∑ k : ι, F k eps) = ∑ k : ι, Ex (F k) := by
    simp [Ex]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro eps _
    rw [Finset.mul_sum]

  have Ex_mono (F G : Finset ι → ℝ) (h : ∀ eps, F eps ≤ G eps) : Ex F ≤ Ex G := by
    simp [Ex]
    apply Finset.sum_le_sum
    intro eps _
    apply mul_le_mul_of_nonneg_left (h eps)
    positivity

  have Xmat_split (c : ι) (eps : Finset ι) :
      Xmat eps = Rest c eps + (sgn eps c) • H c := by
    change (∑ c' : ι, (sgn eps c') • H c') =
      (∑ c' ∈ (Finset.univ.erase c), (sgn eps c') • H c') + (sgn eps c) • H c
    rw [add_comm]
    exact (Finset.add_sum_erase Finset.univ (fun c' => (sgn eps c') • H c') (Finset.mem_univ c)).symm

  have Rest_flip_invariant (c : ι) (eps : Finset ι) :
      Rest c (symmDiff eps {c}) = Rest c eps := by
    change (∑ c' ∈ (Finset.univ.erase c), (sgn (symmDiff eps {c}) c') • H c') =
      ∑ c' ∈ (Finset.univ.erase c), (sgn eps c') • H c'
    apply Finset.sum_congr rfl
    intro c' hc'
    have hne : c' ≠ c := Finset.ne_of_mem_erase hc'
    have : sgn (symmDiff eps {c}) c' = sgn eps c' := by
      simp [sgn, Finset.mem_symmDiff, hne]
    rw [this]

  have sgn_flip (c : ι) (eps : Finset ι) :
      sgn (symmDiff eps {c}) c = - sgn eps c := by
    by_cases h : c ∈ eps
    · have hnot : c ∉ symmDiff eps ({c} : Finset ι) := by simp [Finset.mem_symmDiff, h]
      simp [sgn, h, hnot]
    · have hin : c ∈ symmDiff eps ({c} : Finset ι) := by simp [Finset.mem_symmDiff, h]
      simp [sgn, h, hin]

  have Ex_symmetrize (c : ι) (F : Finset ι → ℝ) :
      Ex F = Ex (fun eps => (1 / 2 : ℝ) * (F eps + F (symmDiff eps {c}))) := by
    have hbij : Ex (fun eps => F (symmDiff eps {c})) = Ex F := by
      change (∑ eps : Finset ι, ((1 : ℝ) / 2) ^ Fintype.card ι * F (symmDiff eps {c})) =
        ∑ eps : Finset ι, ((1 : ℝ) / 2) ^ Fintype.card ι * F eps
      apply Finset.sum_nbij' (fun eps => symmDiff eps {c}) (fun eps => symmDiff eps {c})
      · intro a _; exact Finset.mem_univ _
      · intro a _; exact Finset.mem_univ _
      · intro a _; exact symmDiff_symmDiff_cancel_right {c} a
      · intro a _; exact symmDiff_symmDiff_cancel_right {c} a
      · intro a _; rfl
    calc Ex F = (1 / 2 : ℝ) * (Ex F + Ex (fun eps => F (symmDiff eps {c}))) := by
              rw [hbij]; ring
      _ = (1 / 2 : ℝ) * Ex (fun eps => F eps + F (symmDiff eps {c})) := by rw [Ex_add]
      _ = Ex (fun eps => (1 / 2 : ℝ) * (F eps + F (symmDiff eps {c}))) := by rw [Ex_const_mul]

  have trace_lead_split (eps : Finset ι) (m : ℕ) :
      Matrix.trace (Xmat eps * (Xmat eps) ^ m)
        = ∑ c : ι, sgn eps c * Matrix.trace (H c * (Xmat eps) ^ m) := by
    conv_lhs => rw [show Xmat eps * (Xmat eps) ^ m
        = (∑ c : ι, (sgn eps c) • H c) * (Xmat eps) ^ m from by simp [Xmat]]
    rw [Finset.sum_mul, Matrix.trace_sum]
    apply Finset.sum_congr rfl
    intro c _
    rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]

  have Xmat_flip_split (c : ι) (eps : Finset ι) :
      Xmat (symmDiff eps {c}) = Rest c eps - (sgn eps c) • H c := by
    rw [Xmat_split c (symmDiff eps {c}), Rest_flip_invariant c eps, sgn_flip c eps]
    rw [neg_smul, ← sub_eq_add_neg]

  have Xmat_diff (c : ι) (eps : Finset ι) :
      Xmat eps - Xmat (symmDiff eps {c}) = (2 * sgn eps c) • H c := by
    rw [Xmat_split c eps, Xmat_flip_split c eps]
    rw [add_sub_sub_cancel, ← two_smul ℝ ((sgn eps c) • H c), smul_smul]

  have sbp_coord (c : ι) (n : ℕ) :
      Ex (fun eps => sgn eps c * Matrix.trace (H c * (Xmat eps) ^ n))
        = Ex (fun eps => ∑ q ∈ Finset.range n,
            Matrix.trace (H c * (Xmat eps) ^ q * H c
              * (Xmat (symmDiff eps {c})) ^ (n - 1 - q))) := by
    rw [Ex_symmetrize c (fun eps => sgn eps c * Matrix.trace (H c * (Xmat eps) ^ n))]
    change (∑ eps : Finset ι, ((1 : ℝ) / 2) ^ Fintype.card ι *
        ((1 / 2 : ℝ) *
          (sgn eps c * Matrix.trace (H c * (Xmat eps) ^ n) +
            sgn (symmDiff eps {c}) c *
              Matrix.trace (H c * (Xmat (symmDiff eps {c})) ^ n)))) =
      ∑ eps : Finset ι, ((1 : ℝ) / 2) ^ Fintype.card ι *
        (∑ q ∈ Finset.range n,
          Matrix.trace (H c * (Xmat eps) ^ q * H c *
            (Xmat (symmDiff eps {c})) ^ (n - 1 - q)))
    apply Finset.sum_congr rfl
    intro eps _
    congr 1
    set s : ℝ := sgn eps c with hs
    set W : Matrix (Fin d) (Fin d) ℝ := Xmat eps with hW
    set Y : Matrix (Fin d) (Fin d) ℝ := Xmat (symmDiff eps {c}) with hY
    have hsgnflip : sgn (symmDiff eps {c}) c = - s := sgn_flip c eps
    have hg2 : sgn (symmDiff eps {c}) c
          * Matrix.trace (H c * (Xmat (symmDiff eps {c})) ^ n)
        = - s * Matrix.trace (H c * Y ^ n) := by
      rw [hsgnflip]
    have hWmY : W - Y = (2 * s) • H c := by
      rw [hW, hY]; exact Xmat_diff c eps
    have htel : W ^ n - Y ^ n
        = ∑ q ∈ Finset.range n, W ^ q * (W - Y) * Y ^ (n - 1 - q) := by
      clear hg2 hsgnflip
      induction n with
      | zero => simp
      | succ k ih =>
        have hrec : W ^ (k + 1) - Y ^ (k + 1)
            = (W ^ k - Y ^ k) * Y + W ^ k * (W - Y) := by
          rw [pow_succ, pow_succ]; noncomm_ring
        rw [hrec, ih, Finset.sum_mul, Finset.sum_range_succ]
        congr 1
        · apply Finset.sum_congr rfl
          intro q hq
          rw [Finset.mem_range] at hq
          have hidx : k - 1 - q + 1 = k + 1 - 1 - q := by omega
          rw [mul_assoc, mul_assoc, ← pow_succ, hidx, ← mul_assoc]
        · have hidx : k + 1 - 1 - k = 0 := by omega
          rw [hidx, pow_zero, mul_one]
    have hs2 : s * s = 1 := by rw [hs]; exact sgn_mul_self eps c
    have key : (1 : ℝ) / 2 * (s * Matrix.trace (H c * W ^ n) + -s * Matrix.trace (H c * Y ^ n))
        = ∑ q ∈ Finset.range n,
            Matrix.trace (H c * W ^ q * H c * Y ^ (n - 1 - q)) := by
      have hcombine : s * Matrix.trace (H c * W ^ n) + -s * Matrix.trace (H c * Y ^ n)
          = s * Matrix.trace (H c * (W ^ n - Y ^ n)) := by
        rw [Matrix.mul_sub, Matrix.trace_sub]; ring
      rw [hcombine, htel]
      rw [Matrix.mul_sum, Matrix.trace_sum, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      rw [hWmY]
      have hpull : Matrix.trace (H c * (W ^ q * (2 * s) • H c * Y ^ (n - 1 - q)))
          = (2 * s) * Matrix.trace (H c * W ^ q * H c * Y ^ (n - 1 - q)) := by
        have e1 : H c * (W ^ q * (2 * s) • H c * Y ^ (n - 1 - q))
            = (2 * s) • (H c * W ^ q * H c * Y ^ (n - 1 - q)) := by
          simp only [Matrix.smul_mul, Matrix.mul_smul]
          congr 1
          noncomm_ring
        rw [e1, Matrix.trace_smul, smul_eq_mul]
      rw [hpull]
      rw [show (1 : ℝ) / 2 * (s * ((2 * s) * Matrix.trace (H c * W ^ q * H c * Y ^ (n - 1 - q))))
          = (s * s) * Matrix.trace (H c * W ^ q * H c * Y ^ (n - 1 - q)) from by ring]
      rw [hs2, one_mul]
    rw [hg2]
    exact key

  have qsum_le (M W Y : Matrix (Fin d) (Fin d) ℝ)
      (hM : M.IsHermitian) (hW : W.IsHermitian) (hY : Y.IsHermitian) (r : ℕ) :
      ∑ q ∈ Finset.range (2 * r + 1),
          Matrix.trace (M * W ^ q * M * Y ^ (2 * r - q))
        ≤ ((2 * r + 1 : ℝ) / 2) * Matrix.trace (M * M * (W ^ (2 * r) + Y ^ (2 * r))) := by
    set L := ∑ q ∈ Finset.range (2 * r + 1),
        Matrix.trace (M * W ^ q * M * Y ^ (2 * r - q)) with hL
    have hrefl : ∑ q ∈ Finset.range (2 * r + 1),
          Matrix.trace (M * W ^ (2 * r - q) * M * Y ^ q) = L := by
      rw [hL]
      rw [← Finset.sum_range_reflect
          (fun q => Matrix.trace (M * W ^ (2 * r - q) * M * Y ^ q)) (2 * r + 1)]
      apply Finset.sum_congr rfl
      intro q hq
      rw [Finset.mem_range] at hq
      have h1 : 2 * r + 1 - 1 - q = 2 * r - q := by omega
      have h2 : 2 * r - (2 * r - q) = q := by omega
      rw [h1, h2]
    have htwoL : 2 * L = ∑ q ∈ Finset.range (2 * r + 1),
        (Matrix.trace (M * W ^ q * M * Y ^ (2 * r - q))
          + Matrix.trace (M * W ^ (2 * r - q) * M * Y ^ q)) := by
      rw [Finset.sum_add_distrib, hrefl, two_mul]
    have hbound : ∑ q ∈ Finset.range (2 * r + 1),
        (Matrix.trace (M * W ^ q * M * Y ^ (2 * r - q))
          + Matrix.trace (M * W ^ (2 * r - q) * M * Y ^ q))
        ≤ ∑ q ∈ Finset.range (2 * r + 1),
            Matrix.trace (M * M * (W ^ (2 * r) + Y ^ (2 * r))) := by
      apply Finset.sum_le_sum
      intro q hq
      rw [Finset.mem_range] at hq
      exact tropp_fact_2_4 M W Y hM hW hY r q (by omega)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hbound
    have : (2 : ℝ) * L ≤ (2 * r + 1 : ℝ) * Matrix.trace (M * M * (W ^ (2 * r) + Y ^ (2 * r))) := by
      calc (2 : ℝ) * L = ∑ q ∈ Finset.range (2 * r + 1),
              (Matrix.trace (M * W ^ q * M * Y ^ (2 * r - q))
                + Matrix.trace (M * W ^ (2 * r - q) * M * Y ^ q)) := htwoL
        _ ≤ ((2 * r + 1 : ℕ) : ℝ) * Matrix.trace (M * M * (W ^ (2 * r) + Y ^ (2 * r))) := hbound
        _ = (2 * r + 1 : ℝ) * Matrix.trace (M * M * (W ^ (2 * r) + Y ^ (2 * r))) := by push_cast; ring
    linarith

  have Xmat_isHermitian (eps : Finset ι) : (Xmat eps).IsHermitian := by
    dsimp [Xmat, Matrix.IsHermitian]
    rw [Matrix.conjTranspose_sum]
    apply Finset.sum_congr rfl
    intro c _
    rw [Matrix.conjTranspose_smul, star_trivial, (hHerm c)]

  have Ex_flip (c : ι) (F : Finset ι → ℝ) :
      Ex (fun eps => F (symmDiff eps {c})) = Ex F := by
    change (∑ eps : Finset ι, ((1 : ℝ) / 2) ^ Fintype.card ι * F (symmDiff eps {c})) =
      ∑ eps : Finset ι, ((1 : ℝ) / 2) ^ Fintype.card ι * F eps
    apply Finset.sum_nbij' (fun eps => symmDiff eps {c}) (fun eps => symmDiff eps {c})
    · intro a _; exact Finset.mem_univ _
    · intro a _; exact Finset.mem_univ _
    · intro a _; exact symmDiff_symmDiff_cancel_right {c} a
    · intro a _; exact symmDiff_symmDiff_cancel_right {c} a
    · intro a _; rfl

  have coord_recursion (c : ι) (r : ℕ) :
      Ex (fun eps => sgn eps c * Matrix.trace (H c * (Xmat eps) ^ (2 * r + 1)))
        ≤ (2 * r + 1 : ℝ) * Ex (fun eps => Matrix.trace (H c * H c * (Xmat eps) ^ (2 * r))) := by
    rw [sbp_coord c (2 * r + 1)]
    have hstep : ∀ eps : Finset ι,
        (∑ q ∈ Finset.range (2 * r + 1),
          Matrix.trace (H c * (Xmat eps) ^ q * H c
            * (Xmat (symmDiff eps {c})) ^ (2 * r + 1 - 1 - q)))
        ≤ ((2 * r + 1 : ℝ) / 2)
            * Matrix.trace (H c * H c
                * ((Xmat eps) ^ (2 * r) + (Xmat (symmDiff eps {c})) ^ (2 * r))) := by
      intro eps
      have hidx : ∀ q, 2 * r + 1 - 1 - q = 2 * r - q := by intro q; omega
      simp only [hidx]
      exact qsum_le (H c) (Xmat eps) (Xmat (symmDiff eps {c}))
        (hHerm c) (Xmat_isHermitian eps)
        (Xmat_isHermitian (symmDiff eps {c})) r
    refine le_trans (Ex_mono _ _ hstep) ?_
    have hsplit : ∀ eps : Finset ι,
        ((2 * r + 1 : ℝ) / 2)
          * Matrix.trace (H c * H c
              * ((Xmat eps) ^ (2 * r) + (Xmat (symmDiff eps {c})) ^ (2 * r)))
        = ((2 * r + 1 : ℝ) / 2)
            * (Matrix.trace (H c * H c * (Xmat eps) ^ (2 * r))
              + Matrix.trace (H c * H c * (Xmat (symmDiff eps {c})) ^ (2 * r))) := by
      intro eps; rw [Matrix.mul_add, Matrix.trace_add]
    rw [show (fun eps : Finset ι => ((2 * r + 1 : ℝ) / 2)
          * Matrix.trace (H c * H c
              * ((Xmat eps) ^ (2 * r) + (Xmat (symmDiff eps {c})) ^ (2 * r))))
        = (fun eps => ((2 * r + 1 : ℝ) / 2)
            * (Matrix.trace (H c * H c * (Xmat eps) ^ (2 * r))
              + Matrix.trace (H c * H c * (Xmat (symmDiff eps {c})) ^ (2 * r))))
          from funext hsplit]
    rw [Ex_const_mul]
    rw [Ex_add]
    rw [Ex_flip c (fun eps => Matrix.trace (H c * H c * (Xmat eps) ^ (2 * r)))]
    set A := Ex (fun eps => Matrix.trace (H c * H c * (Xmat eps) ^ (2 * r))) with hA
    apply le_of_eq
    ring

  have even_pow_posSemidef {M : Matrix (Fin d) (Fin d) ℝ}
      (hM : M.IsHermitian) (r : ℕ) : (M ^ (2 * r)).PosSemidef := by
    have hHpow : (M ^ r)ᴴ = M ^ r := (Matrix.IsHermitian.pow hM r)
    have hsplit : M ^ (2 * r) = (M ^ r)ᴴ * (M ^ r) := by
      rw [hHpow, two_mul, pow_add]
    rw [hsplit]
    exact Matrix.posSemidef_conjTranspose_mul_self _

  have step_recursion (r : ℕ) :
      Ex (fun eps => Matrix.trace ((Xmat eps) ^ (2 * (r + 1))))
        ≤ (2 * r + 1 : ℝ) * normV * Ex (fun eps => Matrix.trace ((Xmat eps) ^ (2 * r))) := by
    have h12 : Ex (fun eps => Matrix.trace ((Xmat eps) ^ (2 * (r + 1))))
        = ∑ c : ι, Ex (fun eps => sgn eps c * Matrix.trace (H c * (Xmat eps) ^ (2 * r + 1))) := by
      have hpow : ∀ eps : Finset ι, (Xmat eps) ^ (2 * (r + 1))
          = Xmat eps * (Xmat eps) ^ (2 * r + 1) := by
        intro eps
        rw [show 2 * (r + 1) = (2 * r + 1) + 1 from by omega, pow_succ']
      rw [show (fun eps => Matrix.trace ((Xmat eps) ^ (2 * (r + 1))))
            = (fun eps => Matrix.trace (Xmat eps * (Xmat eps) ^ (2 * r + 1)))
          from funext (fun eps => by rw [hpow eps])]
      rw [show (fun eps => Matrix.trace (Xmat eps * (Xmat eps) ^ (2 * r + 1)))
            = (fun eps => ∑ c : ι, sgn eps c * Matrix.trace (H c * (Xmat eps) ^ (2 * r + 1)))
          from funext (fun eps => trace_lead_split eps (2 * r + 1))]
      rw [Ex_sum_univ]
    rw [h12]
    have h3 : ∑ c : ι, Ex (fun eps => sgn eps c * Matrix.trace (H c * (Xmat eps) ^ (2 * r + 1)))
        ≤ ∑ c : ι, (2 * r + 1 : ℝ) * Ex (fun eps => Matrix.trace (H c * H c * (Xmat eps) ^ (2 * r))) := by
      apply Finset.sum_le_sum
      intro c _
      exact coord_recursion c r
    refine le_trans h3 ?_
    rw [← Finset.mul_sum]
    rw [show ∑ c : ι, Ex (fun eps => Matrix.trace (H c * H c * (Xmat eps) ^ (2 * r)))
          = Ex (fun eps => Matrix.trace ((∑ c : ι, H c * H c) * (Xmat eps) ^ (2 * r))) from by
          rw [← Ex_sum_univ]
          apply congrArg
          funext eps
          rw [Finset.sum_mul, Matrix.trace_sum]]
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have h5 : ∀ eps : Finset ι,
        Matrix.trace ((∑ c : ι, H c * H c) * (Xmat eps) ^ (2 * r))
          ≤ normV * Matrix.trace ((Xmat eps) ^ (2 * r)) := by
      intro eps
      exact tropp_fact_2_2 (∑ c : ι, H c * H c) ((Xmat eps) ^ (2 * r)) hVHerm
        (even_pow_posSemidef (Xmat_isHermitian eps) r) normV hnormV
    refine le_trans (Ex_mono _ _ h5) ?_
    rw [Ex_const_mul]

  have Ex_nonneg (F : Finset ι → ℝ) (hF : ∀ eps, 0 ≤ F eps) : 0 ≤ Ex F := by
    simp [Ex]
    apply Finset.sum_nonneg
    intro eps _
    apply mul_nonneg _ (hF eps)
    positivity

  have Ex_const (a : ℝ) : Ex (fun _ : Finset ι => a) = a := by
    simp [Ex]

  have Ex_trace_even_nonneg (p : ℕ) :
      0 ≤ Ex (fun eps => Matrix.trace ((Xmat eps) ^ (2 * p))) := by
    apply Ex_nonneg
    intro eps
    exact (even_pow_posSemidef (Xmat_isHermitian eps) p).trace_nonneg

  have general_2p_trace_moment (p : ℕ) :
      Ex (fun eps => Matrix.trace ((Xmat eps) ^ (2 * p)))
        ≤ doubleFactOdd p * normV ^ p * (d : ℝ) := by
    set T : ℕ → ℝ := fun k => Ex (fun eps => Matrix.trace ((Xmat eps) ^ (2 * k))) with hT
    have hT0 : T 0 = (d : ℝ) := by
      rw [hT]; simp only [Nat.mul_zero, pow_zero]
      rw [show (fun _ : Finset ι => Matrix.trace (1 : Matrix (Fin d) (Fin d) ℝ))
            = (fun _ : Finset ι => (d : ℝ)) from funext (fun _ => by
              rw [Matrix.trace_one]; simp)]
      exact Ex_const (d : ℝ)
    have hTnn : ∀ k, 0 ≤ T k := fun k => Ex_trace_even_nonneg k
    have hrec : ∀ k, 1 ≤ k → T k ≤ (2 * k - 1 : ℝ) * normV * T (k - 1) := by
      intro k hk
      obtain ⟨r, rfl⟩ : ∃ r, k = r + 1 := ⟨k - 1, by omega⟩
      have := step_recursion r
      have hidx : (r + 1) - 1 = r := by omega
      rw [hT]; rw [hidx]
      calc Ex (fun eps => Matrix.trace ((Xmat eps) ^ (2 * (r + 1))))
          ≤ (2 * r + 1 : ℝ) * normV * Ex (fun eps => Matrix.trace ((Xmat eps) ^ (2 * r))) := this
        _ = (2 * (r + 1 : ℕ) - 1 : ℝ) * normV * Ex (fun eps => Matrix.trace ((Xmat eps) ^ (2 * r))) := by
              push_cast; ring
    exact recursion_iterate T normV (d : ℝ) hnormVnn hT0 hTnn hrec p

  simpa [Ex, Xmat, sgn, doubleFactOdd] using general_2p_trace_moment p
end KhintchineDependency3
export KhintchineDependency3 (general_rademacher_matrix_2p_trace_moment)

-- Accepted proof by LukeBernese; submission 19df491f-7576-4497-9339-7b79b45c0855.
-- Original source SHA-256: adb70693703fe7b3864e1d3b34334f6ef4cb4903e5b77f6ebdb81b35ea89b8fc.
namespace KhintchineDependency4
open Matrix
open scoped BigOperators

theorem eigenvalue_le_of_quadratic_form_le {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsHermitian) (normV : ℝ)
    (hquad : ∀ v : Fin d → ℝ, (star v ⬝ᵥ A *ᵥ v) ≤ normV * (star v ⬝ᵥ v))
    (i : Fin d) :
    hA.eigenvalues i ≤ normV := by
  classical
  set v : Fin d → ℝ := ⇑(hA.eigenvectorBasis i) with hv
  have hev : A *ᵥ v = hA.eigenvalues i • v := hA.mulVec_eigenvectorBasis i
  have hunit : (star v ⬝ᵥ v) = 1 := by
    have ho := hA.eigenvectorBasis.orthonormal.1 i
    have hstar : (star v ⬝ᵥ v) = ∑ k, v k * v k := by
      simp [dotProduct, Pi.star_apply, star_trivial, mul_comm]
    rw [hstar]
    have hnorm : ‖hA.eigenvectorBasis i‖ = 1 := ho
    have hsq : ‖hA.eigenvectorBasis i‖ ^ 2 = ∑ k, v k * v k := by
      rw [EuclideanSpace.norm_eq]
      rw [Real.sq_sqrt (by positivity)]
      congr 1; funext k; rw [hv]; simp [Real.norm_eq_abs, sq_abs, pow_two]
    rw [← hsq, hnorm]; norm_num
  have hqf : (star v ⬝ᵥ A *ᵥ v) = hA.eigenvalues i := by
    rw [hev, dotProduct_smul, smul_eq_mul, hunit, mul_one]
  have hb := hquad v
  rw [hqf, hunit, mul_one] at hb
  exact hb
end KhintchineDependency4
export KhintchineDependency4 (eigenvalue_le_of_quadratic_form_le)

-- Accepted proof by LukeBernese; submission 300219f9-3bd0-4864-9aac-b52c00743056.
-- Original source SHA-256: 0ddf45e9f1bfa351977cacbb96be0dc51d369d84c5054c1fae9a0572e733bab8.
namespace KhintchineDependency5
open scoped BigOperators
open Matrix

theorem trace_pow_reindex {m n R : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [CommRing R] (M : Matrix m m R) (e : m ≃ n) (k : ℕ) :
    Matrix.trace ((M.reindex e e) ^ k) = Matrix.trace (M ^ k) := by
  classical
  -- reindex commutes with powers
  have reindex_pow : ∀ j : ℕ, (M.reindex e e) ^ j = (M ^ j).reindex e e := by
    intro j
    induction j with
    | zero => simp [Matrix.reindex_apply, Matrix.submatrix_one_equiv]
    | succ i ih =>
        rw [pow_succ, pow_succ, ih]
        simp only [Matrix.reindex_apply]
        rw [Matrix.submatrix_mul_equiv (M ^ i) M e.symm e.symm e.symm]
  -- trace is reindex-invariant
  have trace_reindex : ∀ (P : Matrix m m R), Matrix.trace (P.reindex e e) = Matrix.trace P := by
    intro P
    unfold Matrix.trace Matrix.diag
    rw [← Equiv.sum_comp e (fun i => (P.reindex e e) (i) (i))]
    apply Finset.sum_congr rfl
    intro i _
    simp [Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [reindex_pow, trace_reindex]
end KhintchineDependency5
export KhintchineDependency5 (trace_pow_reindex)

-- Accepted proof by LukeBernese; submission 9cb75840-cf82-4d1d-895d-f3196710c850.
-- Original source SHA-256: 90f0dc56b7cc06dea4e527fea9b527838e2982ecd4c840d4475679caf49702c7.
namespace KhintchineDependency6
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
theorem general_rademacher_matrix_2p_trace_moment_general_index
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
end KhintchineDependency6
export KhintchineDependency6 (general_rademacher_matrix_2p_trace_moment_general_index)

-- Accepted proof by LukeBernese; submission 48408094-17cc-421b-9171-c6f849208e63.
-- Original source SHA-256: 91bd1fbdf9ae5786b5130408a117d1e662cfec45008f3dc783db429d530b4642.
namespace KhintchineDependency7
theorem double_factorial_central_quotient_le_two_p_pow (p : ℕ) :
    ((Nat.factorial (2 * p) : ℝ) / ((2 ^ p : ℝ) * (Nat.factorial p : ℝ))) ≤ (2 * p : ℝ) ^ p := by
  induction p with
  | zero => simp
  | succ n ih =>
    -- recurrence: dfR (n+1) = dfR n * (2n+1)
    have hrec : ((Nat.factorial (2 * (n + 1)) : ℝ) / ((2 ^ (n + 1) : ℝ) * (Nat.factorial (n + 1) : ℝ)))
        = ((Nat.factorial (2 * n) : ℝ) / ((2 ^ n : ℝ) * (Nat.factorial n : ℝ))) * (2 * n + 1) := by
      have h2 : (2 : ℝ) ^ (n + 1) = 2 ^ n * 2 := by rw [pow_succ]
      have hfp : ((Nat.factorial (n + 1) : ℝ)) = (Nat.factorial n) * (n + 1) := by
        rw [Nat.factorial_succ]; push_cast; ring
      have h2p : 2 * (n + 1) = (2 * n + 1) + 1 := by ring
      have hf2 : ((Nat.factorial (2 * (n + 1)) : ℝ)) =
          (Nat.factorial (2 * n) : ℝ) * (2 * n + 1) * (2 * n + 2) := by
        rw [h2p, Nat.factorial_succ, Nat.factorial_succ]
        push_cast
        ring
      rw [h2, hfp, hf2]
      have hpfac : (0 : ℝ) < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
      have h2pos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
      field_simp
    rw [hrec]
    have hbase : (0 : ℝ) ≤ (2 * n : ℝ) := by positivity
    rw [show (2 * (↑(n + 1) : ℝ)) = 2 * (n : ℝ) + 2 by push_cast; ring, pow_succ]
    have hmono : (2 * n : ℝ) ^ n ≤ (2 * n + 2 : ℝ) ^ n :=
      pow_le_pow_left₀ hbase (by linarith) n
    calc ((Nat.factorial (2 * n) : ℝ) / ((2 ^ n : ℝ) * (Nat.factorial n : ℝ))) * (2 * n + 1)
        ≤ (2 * n : ℝ) ^ n * (2 * n + 1) := by
          apply mul_le_mul_of_nonneg_right ih; positivity
      _ ≤ (2 * n + 2 : ℝ) ^ n * (2 * n + 2) := by
          apply mul_le_mul hmono (by linarith) (by linarith) (by positivity)
end KhintchineDependency7
export KhintchineDependency7 (double_factorial_central_quotient_le_two_p_pow)

-- Accepted proof by Hartmann_Psi; submission 3055c8a7-063e-4521-b3dc-105ee36e2d31.
-- Original source SHA-256: 2bbb28353e9d5d46336679187c6d714f907756a290f1a67666668d37c2759ff9.
namespace KhintchineDependency8
open scoped Real

theorem rank_rpow_inv_le_exp_one_of_log_le
    (N : ℕ) (q : ℝ) (hN : 1 ≤ N) (hq : 1 ≤ q)
    (hlog : Real.log (N : ℝ) ≤ q) :
    Real.rpow (N : ℝ) q⁻¹ ≤ Real.exp 1 := by
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le one_pos hNR
  have hqpos : (0 : ℝ) < q := lt_of_lt_of_le one_pos hq
  have hlogN_nonneg : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hNR
  rw [show Real.rpow (N : ℝ) q⁻¹ = (N : ℝ) ^ (q⁻¹ : ℝ) from rfl,
      Real.rpow_def_of_pos hNpos]
  apply Real.exp_le_exp.mpr
  rw [mul_inv_le_iff₀ hqpos]
  simpa using hlog
end KhintchineDependency8
export KhintchineDependency8 (rank_rpow_inv_le_exp_one_of_log_le)

-- Accepted proof by LukeBernese; submission 4b6beefe-f67c-4a41-b805-abdad6aa4171.
-- Original source SHA-256: 5d03be9afd4749a044324ebbc2b2acbabfa762645a172f5ac3e9458911791ac1.
namespace KhintchineDependency9
open scoped BigOperators

theorem engine_rhs_root_le
    (n d : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d) (normV : ℝ) (hV : 0 ≤ normV)
    (hlog : Real.log (d : ℝ) ≤ (2 * n : ℕ)) :
    Real.rpow
      (((Nat.factorial (2 * n) : ℝ) / ((2 ^ n : ℝ) * (Nat.factorial n : ℝ)))
        * normV ^ n * (d : ℝ)) ((1 : ℝ) / (2 * n))
      ≤ Real.sqrt (2 * n : ℕ) * Real.exp 1 * Real.sqrt normV := by
  have h2n : (0:ℝ) < 2 * n := by positivity
  set dblfact : ℝ := (Nat.factorial (2 * n) : ℝ) / ((2 ^ n : ℝ) * (Nat.factorial n : ℝ)) with hdf
  have hdf0 : 0 ≤ dblfact := by rw [hdf]; positivity
  have hnV : (0:ℝ) ≤ normV ^ n := by positivity
  have hdR : (0:ℝ) ≤ (d : ℝ) := by positivity
  show (dblfact * normV ^ n * (d:ℝ)) ^ ((1:ℝ) / (2 * n))
      ≤ Real.sqrt (2 * n : ℕ) * Real.exp 1 * Real.sqrt normV
  rw [Real.mul_rpow (by positivity) hdR, Real.mul_rpow hdf0 hnV]
  have hf1 : dblfact ^ ((1:ℝ) / (2 * n)) ≤ Real.sqrt (2 * n : ℕ) := by
    have hpa : dblfact ≤ (2 * n : ℝ) ^ n := double_factorial_central_quotient_le_two_p_pow n
    calc dblfact ^ ((1:ℝ) / (2 * n))
        ≤ ((2 * n : ℝ) ^ n) ^ ((1:ℝ) / (2 * n)) := by
          apply Real.rpow_le_rpow hdf0 hpa (by positivity)
      _ = Real.sqrt (2 * n : ℕ) := by
          rw [← Real.rpow_natCast (2 * n : ℝ) n, ← Real.rpow_mul (by positivity),
              Real.sqrt_eq_rpow]
          congr 1
          · push_cast; ring
          · push_cast; field_simp
  have hf2 : (normV ^ n) ^ ((1:ℝ) / (2 * n)) = Real.sqrt normV := by
    rw [← Real.rpow_natCast normV n, ← Real.rpow_mul hV, Real.sqrt_eq_rpow]
    congr 1
    push_cast; field_simp
  have hf3 : (d : ℝ) ^ ((1:ℝ) / (2 * n)) ≤ Real.exp 1 := by
    have hw := rank_rpow_inv_le_exp_one_of_log_le d (2 * n : ℕ) hd (by
      have : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
      push_cast; nlinarith) (by push_cast at hlog ⊢; linarith)
    rw [show ((2 * n : ℕ) : ℝ)⁻¹ = (1:ℝ) / (2 * n) by push_cast; rw [one_div]] at hw
    exact hw
  rw [hf2]
  have hsqV : (0:ℝ) ≤ Real.sqrt normV := Real.sqrt_nonneg _
  have hsq2n : (0:ℝ) ≤ Real.sqrt (2 * n : ℕ) := Real.sqrt_nonneg _
  have hposD : (0:ℝ) ≤ (d:ℝ) ^ ((1:ℝ)/(2*n)) := Real.rpow_nonneg hdR _
  calc dblfact ^ ((1:ℝ)/(2*n)) * Real.sqrt normV * (d:ℝ) ^ ((1:ℝ)/(2*n))
      ≤ Real.sqrt (2 * n : ℕ) * Real.sqrt normV * Real.exp 1 := by
        apply mul_le_mul _ hf3 hposD (by positivity)
        exact mul_le_mul hf1 (le_refl _) hsqV hsq2n
    _ = Real.sqrt (2 * n : ℕ) * Real.exp 1 * Real.sqrt normV := by ring
end KhintchineDependency9
export KhintchineDependency9 (engine_rhs_root_le)

-- Accepted proof by LukeBernese; submission afdd8e7e-7437-4141-8c92-c8791184c75e.
-- Original source SHA-256: b92ae37ad8027ba0e4aa19453318f6d46212739c4a5347d00385e2548c2194af.
namespace KhintchineDependency10
open Matrix MatrixCompletion
open scoped BigOperators

/-! ## Vendored internal block machinery (helper defs/lemmas; not platform vocabulary). -/

noncomputable def dilation {n1 n2 : ℕ} (S : Matrix (Fin n1) (Fin n2) ℝ) :
    Matrix (Fin n1 ⊕ Fin n2) (Fin n1 ⊕ Fin n2) ℝ :=
  Matrix.fromBlocks 0 S Sᵀ 0

noncomputable def coordScaled {n1 n2 : Nat}
    (Omega : Finset (Fin n1 × Fin n2)) (p : Real)
    (X : RealMatrix n1 n2) (c : Fin n1 × Fin n2) : RealMatrix n1 n2 :=
  fun i j => if (i, j) = c then p⁻¹ * (if c ∈ Omega then X c.1 c.2 else 0) else 0

noncomputable def coordVal {n1 n2 : Nat}
    (Omega : Finset (Fin n1 × Fin n2)) (p : Real)
    (X : RealMatrix n1 n2) (c : Fin n1 × Fin n2) : ℝ :=
  p⁻¹ * (if c ∈ Omega then X c.1 c.2 else 0)

noncomputable def rowEnergyVec {n1 n2 : Nat}
    (Omega : Finset (Fin n1 × Fin n2)) (p : Real) (X : RealMatrix n1 n2) :
    Fin n1 → ℝ :=
  fun i => ∑ j : Fin n2, (coordVal Omega p X (i, j)) ^ 2

noncomputable def colEnergyVec {n1 n2 : Nat}
    (Omega : Finset (Fin n1 × Fin n2)) (p : Real) (X : RealMatrix n1 n2) :
    Fin n2 → ℝ :=
  fun j => ∑ i : Fin n1, (coordVal Omega p X (i, j)) ^ 2

private lemma dilation_sq {n1 n2 : ℕ} (S : Matrix (Fin n1) (Fin n2) ℝ) :
    (dilation S) ^ 2 = Matrix.fromBlocks (S * Sᵀ) 0 0 (Sᵀ * S) := by
  rw [pow_two, dilation, Matrix.fromBlocks_multiply]; simp

private lemma coordScaled_mul_transpose {n1 n2 : Nat}
    (Omega : Finset (Fin n1 × Fin n2)) (p : Real) (X : RealMatrix n1 n2)
    (c : Fin n1 × Fin n2) :
    (coordScaled Omega p X c) * (coordScaled Omega p X c)ᵀ
      = fun i i' => if i = c.1 ∧ i' = c.1 then (coordVal Omega p X c) ^ 2 else 0 := by
  classical
  funext i i'
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  have hcs : ∀ a b, coordScaled Omega p X c a b
      = if (a, b) = c then coordVal Omega p X c else 0 := by intro a b; rfl
  simp only [hcs]
  rw [Finset.sum_eq_single c.2]
  · simp only [show ((i, c.2) = c) ↔ (i = c.1) by rw [Prod.ext_iff]; simp,
               show ((i', c.2) = c) ↔ (i' = c.1) by rw [Prod.ext_iff]; simp]
    by_cases h1 : i = c.1 <;> by_cases h2 : i' = c.1 <;> simp [h1, h2, sq]
  · intro b _ hb
    rw [if_neg (fun h => hb (Prod.ext_iff.mp h).2)]; ring
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma sum_coordScaled_mul_transpose {n1 n2 : Nat}
    (Omega : Finset (Fin n1 × Fin n2)) (p : Real) (X : RealMatrix n1 n2) :
    (∑ c : Fin n1 × Fin n2, (coordScaled Omega p X c) * (coordScaled Omega p X c)ᵀ)
      = Matrix.diagonal (rowEnergyVec Omega p X) := by
  classical
  funext i i'
  rw [Matrix.sum_apply]
  simp only [coordScaled_mul_transpose, Matrix.diagonal]
  by_cases hii : i = i'
  · subst hii
    simp only [Matrix.of_apply, if_pos rfl]
    rw [rowEnergyVec, Fintype.sum_prod_type, Finset.sum_eq_single i]
    · refine Finset.sum_congr rfl (fun b _ => ?_); simp
    · intro a _ ha
      refine Finset.sum_eq_zero (fun b _ => ?_)
      rw [if_neg]; rintro ⟨h1, _⟩; exact ha h1.symm
    · intro h; exact absurd (Finset.mem_univ _) h
  · simp only [Matrix.of_apply, if_neg hii]
    refine Finset.sum_eq_zero (fun c _ => ?_)
    rw [if_neg]; rintro ⟨h1, h2⟩; exact hii (h1.trans h2.symm)

private lemma transpose_mul_coordScaled {n1 n2 : Nat}
    (Omega : Finset (Fin n1 × Fin n2)) (p : Real) (X : RealMatrix n1 n2)
    (c : Fin n1 × Fin n2) :
    (coordScaled Omega p X c)ᵀ * (coordScaled Omega p X c)
      = fun j j' => if j = c.2 ∧ j' = c.2 then (coordVal Omega p X c) ^ 2 else 0 := by
  classical
  funext j j'
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  have hcs : ∀ a b, coordScaled Omega p X c a b
      = if (a, b) = c then coordVal Omega p X c else 0 := fun a b => rfl
  simp only [hcs]
  rw [Finset.sum_eq_single c.1]
  · simp only [show ((c.1, j) = c) ↔ (j = c.2) by rw [Prod.ext_iff]; simp,
               show ((c.1, j') = c) ↔ (j' = c.2) by rw [Prod.ext_iff]; simp]
    by_cases h1 : j = c.2 <;> by_cases h2 : j' = c.2 <;> simp [h1, h2, sq]
  · intro a _ ha
    rw [if_neg (fun h => ha (Prod.ext_iff.mp h).1)]; ring
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma sum_transpose_mul_coordScaled {n1 n2 : Nat}
    (Omega : Finset (Fin n1 × Fin n2)) (p : Real) (X : RealMatrix n1 n2) :
    (∑ c : Fin n1 × Fin n2, (coordScaled Omega p X c)ᵀ * (coordScaled Omega p X c))
      = Matrix.diagonal (colEnergyVec Omega p X) := by
  classical
  funext j j'
  rw [Matrix.sum_apply]
  simp only [transpose_mul_coordScaled, Matrix.diagonal]
  by_cases hjj : j = j'
  · subst hjj
    simp only [Matrix.of_apply, if_pos rfl, colEnergyVec]
    rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_eq_single j]
    · refine Finset.sum_congr rfl (fun a _ => ?_); simp
    · intro b _ hb
      refine Finset.sum_eq_zero (fun a _ => ?_)
      rw [if_neg]; rintro ⟨h1, _⟩; exact hb h1.symm
    · intro h; exact absurd (Finset.mem_univ _) h
  · simp only [Matrix.of_apply, if_neg hjj]
    refine Finset.sum_eq_zero (fun c _ => ?_)
    rw [if_neg]; rintro ⟨h1, h2⟩; exact hjj (h1.trans h2.symm)

private lemma sum_dilation_coordScaled_sq_eq_blockdiag {n1 n2 : Nat}
    (Omega : Finset (Fin n1 × Fin n2)) (p : Real) (X : RealMatrix n1 n2) :
    (∑ c : Fin n1 × Fin n2, (dilation (coordScaled Omega p X c)) ^ 2)
      = Matrix.fromBlocks (Matrix.diagonal (rowEnergyVec Omega p X)) 0 0
          (Matrix.diagonal (colEnergyVec Omega p X)) := by
  classical
  simp only [dilation_sq]
  rw [← sum_coordScaled_mul_transpose, ← sum_transpose_mul_coordScaled]
  funext x y
  rw [Matrix.sum_apply]
  cases x with
  | inl i => cases y with
    | inl i' => simp [Matrix.fromBlocks_apply₁₁, Matrix.sum_apply]
    | inr j' => simp [Matrix.fromBlocks_apply₁₂]
  | inr j => cases y with
    | inl i' => simp [Matrix.fromBlocks_apply₂₁]
    | inr j' => simp [Matrix.fromBlocks_apply₂₂, Matrix.sum_apply]

private lemma rSM_eq_signed_sum {n1 n2 : Nat}
    (Omega eps : Finset (Fin n1 × Fin n2)) (p : Real) (X : RealMatrix n1 n2) :
    rademacherSampledMatrix Omega eps p X
      = ∑ c : Fin n1 × Fin n2, rademacherSign eps c.1 c.2 • coordScaled Omega p X c := by
  classical
  funext i j
  rw [Matrix.sum_apply, Finset.sum_eq_single (i, j)]
  · simp only [coordScaled, rademacherSampledMatrix, rademacherSign, Matrix.smul_apply,
      smul_eq_mul]
    by_cases hO : (i, j) ∈ Omega
    · rw [if_pos hO, if_pos hO, if_true]; ring
    · rw [if_neg hO, if_neg hO]; simp
  · intro c _ hc
    simp only [coordScaled, Matrix.smul_apply, smul_eq_mul]
    rw [if_neg (by exact fun h => hc (by rw [← h]))]; ring
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma engine_lhs_eq_rademacherExpectation {n1 n2 : Nat} {μ : Type*}
    [Fintype μ] [DecidableEq μ]
    (H : (Fin n1 × Fin n2) → Matrix μ μ ℝ) (p : Nat) :
    (∑ eps : Finset (Fin n1 × Fin n2),
        ((1 : ℝ) / 2) ^ (Fintype.card (Fin n1 × Fin n2))
          * Matrix.trace ((∑ c : Fin n1 × Fin n2,
              (if c ∈ eps then (1 : ℝ) else -1) • H c) ^ (2 * p)))
      = rademacherExpectation
          (fun eps => Matrix.trace ((∑ c : Fin n1 × Fin n2,
              rademacherSign eps c.1 c.2 • H c) ^ (2 * p))) := by
  unfold rademacherExpectation rademacherObservationWeight rademacherSign
  rfl

private lemma diagonal_quadratic_form_le {n : ℕ} (d : Fin n → ℝ) (B : ℝ)
    (hd : ∀ k, d k ≤ B) (hv : ∀ k, (0:ℝ) ≤ d k) (v : Fin n → ℝ) :
    (star v ⬝ᵥ (diagonal d) *ᵥ v) ≤ B * (star v ⬝ᵥ v) := by
  classical
  have hL : (star v ⬝ᵥ (diagonal d) *ᵥ v) = ∑ k, d k * (v k * v k) := by
    rw [dotProduct]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [mulVec_diagonal]; simp [Pi.star_apply, star_trivial]; ring
  have hR : B * (star v ⬝ᵥ v) = ∑ k, B * (v k * v k) := by
    rw [dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp [Pi.star_apply, star_trivial]
  rw [hL, hR]
  refine Finset.sum_le_sum (fun k _ => ?_)
  exact mul_le_mul_of_nonneg_right (hd k) (mul_self_nonneg _)

private lemma block_diagonal_quadratic_form_le {n1 n2 : ℕ}
    (a : Fin n1 → ℝ) (b : Fin n2 → ℝ) (B : ℝ)
    (ha : ∀ i, a i ≤ B) (hb : ∀ j, b j ≤ B)
    (ha0 : ∀ i, (0:ℝ) ≤ a i) (hb0 : ∀ j, (0:ℝ) ≤ b j)
    (w : Fin n1 ⊕ Fin n2 → ℝ) :
    (star w ⬝ᵥ (Matrix.fromBlocks (diagonal a) 0 0 (diagonal b)) *ᵥ w)
      ≤ B * (star w ⬝ᵥ w) := by
  classical
  set v1 : Fin n1 → ℝ := fun i => w (Sum.inl i) with hv1
  set v2 : Fin n2 → ℝ := fun j => w (Sum.inr j) with hv2
  have hmv : (Matrix.fromBlocks (diagonal a) 0 0 (diagonal b)) *ᵥ w
      = Sum.elim ((diagonal a) *ᵥ v1) ((diagonal b) *ᵥ v2) := by
    rw [fromBlocks_mulVec]; simp only [Matrix.zero_mulVec, add_zero, zero_add]; rfl
  rw [hmv]
  have hsplit : (star w ⬝ᵥ Sum.elim ((diagonal a) *ᵥ v1) ((diagonal b) *ᵥ v2))
      = (star v1 ⬝ᵥ (diagonal a) *ᵥ v1) + (star v2 ⬝ᵥ (diagonal b) *ᵥ v2) := by
    rw [dotProduct, Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Pi.star_apply, hv1, hv2]; rfl
  have hww : (star w ⬝ᵥ w) = (star v1 ⬝ᵥ v1) + (star v2 ⬝ᵥ v2) := by
    rw [dotProduct, Fintype.sum_sum_type]
    simp only [Pi.star_apply, hv1, hv2]; rfl
  rw [hsplit, hww, mul_add]
  have h1 := diagonal_quadratic_form_le a B ha ha0 v1
  have h2 := diagonal_quadratic_form_le b B hb hb0 v2
  linarith

private lemma dilation_add {n1 n2 : ℕ} (A B : Matrix (Fin n1) (Fin n2) ℝ) :
    dilation (A + B) = dilation A + dilation B := by
  classical
  funext x y
  cases x with
  | inl i => cases y with
    | inl i' => simp [dilation, Matrix.fromBlocks_apply₁₁]
    | inr j' => simp [dilation, Matrix.fromBlocks_apply₁₂]
  | inr j => cases y with
    | inl i' => simp [dilation, Matrix.fromBlocks_apply₂₁, Matrix.transpose_apply]
    | inr j' => simp [dilation, Matrix.fromBlocks_apply₂₂]

private lemma dilation_smul {n1 n2 : ℕ} (s : ℝ) (A : Matrix (Fin n1) (Fin n2) ℝ) :
    dilation (s • A) = s • dilation A := by
  classical
  funext x y
  cases x with
  | inl i => cases y with
    | inl i' => simp [dilation, Matrix.fromBlocks_apply₁₁]
    | inr j' => simp [dilation, Matrix.fromBlocks_apply₁₂]
  | inr j => cases y with
    | inl i' => simp [dilation, Matrix.fromBlocks_apply₂₁, Matrix.transpose_apply]
    | inr j' => simp [dilation, Matrix.fromBlocks_apply₂₂]

private lemma dilation_sum {n1 n2 : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → Matrix (Fin n1) (Fin n2) ℝ) :
    dilation (∑ c ∈ s, f c) = ∑ c ∈ s, dilation (f c) := by
  classical
  induction s using Finset.induction with
  | empty => simp only [Finset.sum_empty]; funext x y; cases x <;> cases y <;> simp [dilation, Matrix.fromBlocks]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, dilation_add, ih]

private lemma dilation_isHermitian {n1 n2 : ℕ} (A : Matrix (Fin n1) (Fin n2) ℝ) :
    (dilation A).IsHermitian := by
  classical
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_eq_transpose_of_trivial]
  funext x y
  cases x with
  | inl i => cases y with
    | inl i' => simp [dilation, Matrix.fromBlocks_apply₁₁, Matrix.transpose_apply]
    | inr j' => simp [dilation, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
                  Matrix.transpose_apply]
  | inr j => cases y with
    | inl i' => simp [dilation, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₁₂,
                  Matrix.transpose_apply]
    | inr j' => simp [dilation, Matrix.fromBlocks_apply₂₂, Matrix.transpose_apply]

/-- D1-link with the platform `schattenNorm`, inlined from the two imported children
(`schatten_norm_even_pow_eq_trace_row_gram_pow` 197d0150 + `trace_dilation_even_pow` 68317d2d). -/
private lemma schatten_even_pow_le_trace_dilation_even_pow
    (n : Nat) (hn : 1 ≤ n) {n1 n2 : Nat} (X : RealMatrix n1 n2) :
    schattenNorm (2 * n) X ^ (2 * n) ≤ Matrix.trace ((dilation X) ^ (2 * n)) := by
  rw [schatten_norm_even_pow_eq_trace_row_gram_pow n hn X]
  show _ ≤ Matrix.trace ((Matrix.fromBlocks 0 X Xᵀ 0) ^ (2 * n))
  rw [trace_dilation_even_pow]
  have hPSD : (Xᵀ * X).PosSemidef := by
    have := Matrix.posSemidef_conjTranspose_mul_self X
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this
  have hnn : 0 ≤ Matrix.trace ((Xᵀ * X) ^ n) := (hPSD.pow n).trace_nonneg
  have hkey : Matrix.trace ((X * X.transpose) ^ n)
      ≤ Matrix.trace ((X * X.transpose) ^ n) + Matrix.trace ((Xᵀ * X) ^ n) := by linarith
  simpa using hkey

/-! ## Energy discharge helpers (rowEnergyVec/colEnergyVec ≤ variance-scale²). -/

private lemma rowEnergyMax_nonneg {n1 n2 : Nat}
    (Omega : Finset (Fin n1 × Fin n2)) (X : RealMatrix n1 n2) :
    0 ≤ sampledRowEnergyMax Omega X := by
  unfold sampledRowEnergyMax
  rcases isEmpty_or_nonempty (Fin n1) with h | h
  · rw [Real.iSup_of_isEmpty]
  · exact Real.iSup_nonneg (fun i => Finset.sum_nonneg (fun j _ => by positivity))

private lemma colEnergyMax_nonneg {n1 n2 : Nat}
    (Omega : Finset (Fin n1 × Fin n2)) (X : RealMatrix n1 n2) :
    0 ≤ sampledColumnEnergyMax Omega X := by
  unfold sampledColumnEnergyMax
  rcases isEmpty_or_nonempty (Fin n2) with h | h
  · rw [Real.iSup_of_isEmpty]
  · exact Real.iSup_nonneg (fun j => Finset.sum_nonneg (fun i _ => by positivity))

/-- `rowEnergyVec Ω p X i = p⁻² · ∑_j δ_ij X_ij²`. -/
private lemma rowEnergyVec_eq {n1 n2 : Nat}
    (Omega : Finset (Fin n1 × Fin n2)) (p : Real) (X : RealMatrix n1 n2) (i : Fin n1) :
    rowEnergyVec Omega p X i
      = (p⁻¹)^2 * ∑ j : Fin n2, if (i, j) ∈ Omega then X i j ^ 2 else 0 := by
  rw [rowEnergyVec, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [coordVal]
  by_cases h : (i, j) ∈ Omega
  · simp only [h, if_true]; ring
  · simp only [h, if_false]; ring

private lemma colEnergyVec_eq {n1 n2 : Nat}
    (Omega : Finset (Fin n1 × Fin n2)) (p : Real) (X : RealMatrix n1 n2) (j : Fin n2) :
    colEnergyVec Omega p X j
      = (p⁻¹)^2 * ∑ i : Fin n1, if (i, j) ∈ Omega then X i j ^ 2 else 0 := by
  rw [colEnergyVec, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [coordVal]
  by_cases h : (i, j) ∈ Omega
  · simp only [h, if_true]; ring
  · simp only [h, if_false]; ring

/-! ## MAIN: even-2n Schatten moment bound (variance-scale RHS, platform vocabulary). -/

theorem even2n_schatten_moment_bound {n1 n2 : Nat} (n : Nat) (hn : 1 ≤ n)
    (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (X : RealMatrix n1 n2)
    (hd1 : 1 ≤ (n1 + n2)) (hlog : Real.log ((n1 + n2 : ℕ)) ≤ (2 * n : ℕ)) :
    rademacherExpectation (fun eps =>
        schattenNorm (2 * n : ℝ) (rademacherSampledMatrix Omega eps p X) ^ (2 * n))
      ≤ (Real.sqrt (2 * n : ℕ) * Real.exp 1
          * rademacherSampledVarianceScale Omega p X) ^ (2 * n) := by
  classical
  -- variance scale and its square as the eigenvalue bound B
  set emax : ℝ := max (sampledRowEnergyMax Omega X) (sampledColumnEnergyMax Omega X) with hemax
  have hemax0 : 0 ≤ emax := le_max_of_le_left (rowEnergyMax_nonneg Omega X)
  set B : ℝ := (p⁻¹)^2 * emax with hBdef
  have hpinv2 : 0 ≤ (p⁻¹)^2 := sq_nonneg _
  have hB0 : 0 ≤ B := by rw [hBdef]; exact mul_nonneg hpinv2 hemax0
  have hrsvs : rademacherSampledVarianceScale Omega p X = p⁻¹ * Real.sqrt emax := by
    unfold rademacherSampledVarianceScale; rw [hemax]
  -- final even-power identity: (√(2n)·e·√B)^(2n) = (√(2n)·e·rsvs)^(2n)
  -- (since √B = |p⁻¹|·√emax and rsvs = p⁻¹·√emax differ only by the sign of p⁻¹,
  --  killed by the even exponent 2n)
  have hfinalEq : (Real.sqrt (2 * n : ℕ) * Real.exp 1 * Real.sqrt B) ^ (2 * n)
      = (Real.sqrt (2 * n : ℕ) * Real.exp 1
          * rademacherSampledVarianceScale Omega p X) ^ (2 * n) := by
    have hAnn : (0:ℝ) ≤ Real.sqrt (2 * n : ℕ) * Real.exp 1 := by positivity
    have heven : Even (2 * n) := ⟨n, by ring⟩
    rw [hBdef, hrsvs, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
    -- both sides equal |√(2n)·e·p⁻¹·√emax|^(2n)
    rw [show Real.sqrt (2 * n : ℕ) * Real.exp 1 * (|p⁻¹| * Real.sqrt emax)
          = |Real.sqrt (2 * n : ℕ) * Real.exp 1 * (p⁻¹ * Real.sqrt emax)| by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg (2 * n : ℕ)),
          abs_of_nonneg (le_of_lt (Real.exp_pos 1)), abs_of_nonneg (Real.sqrt_nonneg emax)]]
    rw [heven.pow_abs]
  -- energy discharge: rowEnergyVec i ≤ B, colEnergyVec j ≤ B, and ≥ 0
  have hrow0 : ∀ i, 0 ≤ rowEnergyVec Omega p X i := fun i =>
    Finset.sum_nonneg (fun j _ => by positivity)
  have hcol0 : ∀ j, 0 ≤ colEnergyVec Omega p X j := fun j =>
    Finset.sum_nonneg (fun i _ => by positivity)
  have hrow : ∀ i, rowEnergyVec Omega p X i ≤ B := by
    intro i
    rw [rowEnergyVec_eq, hBdef]
    apply mul_le_mul_of_nonneg_left _ hpinv2
    refine le_trans ?_ (le_max_left _ _)
    unfold sampledRowEnergyMax
    exact le_ciSup (f := fun i => ∑ j : Fin n2, if (i, j) ∈ Omega then X i j ^ 2 else 0)
      (Finite.bddAbove_range _) i
  have hcol : ∀ j, colEnergyVec Omega p X j ≤ B := by
    intro j
    rw [colEnergyVec_eq, hBdef]
    apply mul_le_mul_of_nonneg_left _ hpinv2
    refine le_trans ?_ (le_max_right _ _)
    unfold sampledColumnEnergyMax
    exact le_ciSup (f := fun j => ∑ i : Fin n1, if (i, j) ∈ Omega then X i j ^ 2 else 0)
      (Finite.bddAbove_range _) j
  -- The Hermitian family used by the engine: H c = dilation (coordScaled c) over Fin n1 ⊕ Fin n2.
  set H : (Fin n1 × Fin n2) → Matrix (Fin n1 ⊕ Fin n2) (Fin n1 ⊕ Fin n2) ℝ :=
    fun c => dilation (coordScaled Omega p X c) with hHdef
  have hHerm : ∀ c, (H c).IsHermitian := fun c => dilation_isHermitian _
  have hVeq : (∑ c : Fin n1 × Fin n2, H c * H c)
      = Matrix.fromBlocks (Matrix.diagonal (rowEnergyVec Omega p X)) 0 0
          (Matrix.diagonal (colEnergyVec Omega p X)) := by
    have hsq : ∀ c, H c * H c = (dilation (coordScaled Omega p X c)) ^ 2 := by
      intro c; rw [hHdef, pow_two]
    simp_rw [hsq]
    exact sum_dilation_coordScaled_sq_eq_blockdiag Omega p X
  have hVHerm : (∑ c : Fin n1 × Fin n2, H c * H c).IsHermitian := by
    rw [hVeq]
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_eq_transpose_of_trivial,
        Matrix.fromBlocks_transpose, Matrix.diagonal_transpose, Matrix.diagonal_transpose,
        Matrix.transpose_zero, Matrix.transpose_zero]
  -- quadratic-form bound for V = ∑ H c * H c
  have hquad : ∀ w : (Fin n1 ⊕ Fin n2) → ℝ,
      (star w ⬝ᵥ (∑ c : Fin n1 × Fin n2, H c * H c) *ᵥ w) ≤ B * (star w ⬝ᵥ w) := by
    intro w
    rw [hVeq]
    exact block_diagonal_quadratic_form_le (rowEnergyVec Omega p X)
      (colEnergyVec Omega p X) B hrow hcol hrow0 hcol0 w
  -- ENGINE (general-index, quadratic-form form)
  have hcardμ : (Fintype.card (Fin n1 ⊕ Fin n2) : ℝ) = (n1 + n2 : ℕ) := by
    simp [Fintype.card_sum]
  have hEngine := general_rademacher_matrix_2p_trace_moment_general_index
    H hHerm B hB0 hVHerm hquad n
  rw [hcardμ] at hEngine
  have hLHSeq := engine_lhs_eq_rademacherExpectation H n
  rw [hLHSeq] at hEngine
  -- dilation(rSM eps) = ∑ c, sign • H c
  have hdilrSM : ∀ eps : Finset (Fin n1 × Fin n2),
      dilation (rademacherSampledMatrix Omega eps p X)
        = ∑ c : Fin n1 × Fin n2, rademacherSign eps c.1 c.2 • H c := by
    intro eps
    rw [rSM_eq_signed_sum Omega eps p X, dilation_sum]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [dilation_smul]
  -- Monotone-expectation chain
  have hchain :
      rademacherExpectation (fun eps =>
          schattenNorm (2 * n : ℝ) (rademacherSampledMatrix Omega eps p X) ^ (2 * n))
        ≤ ((Nat.factorial (2*n):ℝ)/((2^n:ℝ)*(Nat.factorial n:ℝ))) * B^n * (n1 + n2 : ℕ) := by
    refine le_trans ?_ hEngine
    unfold rademacherExpectation
    refine Finset.sum_le_sum (fun eps _ => ?_)
    have hw0 : (0:ℝ) ≤ rademacherObservationWeight eps := by
      unfold rademacherObservationWeight; positivity
    apply mul_le_mul_of_nonneg_left _ hw0
    dsimp only
    have hd1' := schatten_even_pow_le_trace_dilation_even_pow n hn
      (rademacherSampledMatrix Omega eps p X)
    rw [← hdilrSM eps]
    exact hd1'
  -- engine RHS root bound
  set Y : ℝ := ((Nat.factorial (2*n):ℝ)/((2^n:ℝ)*(Nat.factorial n:ℝ))) * B^n * (n1 + n2 : ℕ)
    with hYdef
  have hY0 : 0 ≤ Y := by rw [hYdef]; positivity
  have hroot := engine_rhs_root_le n (n1 + n2) hn hd1 B hB0 (by
    push_cast at hlog ⊢; convert hlog using 2 <;> push_cast <;> ring)
  have hRHS_nn : (0:ℝ) ≤ Real.sqrt (2 * n : ℕ) * Real.exp 1 * Real.sqrt B := by positivity
  have h2nne : (2 * n) ≠ 0 := by positivity
  have hroundtrip : (Real.rpow Y ((1:ℝ)/(2*n))) ^ (2 * n) = Y := by
    have hexp : (1:ℝ)/(2 * n) = ((2 * n : ℕ):ℝ)⁻¹ := by push_cast; rw [one_div]
    rw [hexp]; exact Real.rpow_inv_natCast_pow hY0 h2nne
  have hpow : (Real.rpow Y ((1:ℝ)/(2*n))) ^ (2 * n)
      ≤ (Real.sqrt (2 * n : ℕ) * Real.exp 1 * Real.sqrt B) ^ (2 * n) :=
    pow_le_pow_left₀ (Real.rpow_nonneg hY0 _) hroot (2 * n)
  rw [hroundtrip] at hpow
  -- combine; rewrite √B = variance scale
  calc rademacherExpectation (fun eps =>
          schattenNorm (2 * n : ℝ) (rademacherSampledMatrix Omega eps p X) ^ (2 * n))
      ≤ Y := hchain
    _ ≤ (Real.sqrt (2 * n : ℕ) * Real.exp 1 * Real.sqrt B) ^ (2 * n) := hpow
    _ = (Real.sqrt (2 * n : ℕ) * Real.exp 1
          * rademacherSampledVarianceScale Omega p X) ^ (2 * n) := hfinalEq
end KhintchineDependency10
export KhintchineDependency10 (even2n_schatten_moment_bound)

-- Accepted proof by Grace; submission 88125b66-513f-49fe-b6f7-d74d65ab2619.
-- Original source SHA-256: 02913cf636dfbb235f42d29229f3cd7822f3a239719192533e8001d88285b0b3.
namespace KhintchineDependency11
open MatrixCompletion
open scoped BigOperators

theorem rademacher_expectation_power_mean
    {n1 n2 : Nat} (r s : ℝ) (hr : 0 < r) (hrs : r ≤ s)
    (F : Finset (Fin n1 × Fin n2) → ℝ) (hF : ∀ eps, 0 ≤ F eps) :
    rademacherExpectation (fun eps => (F eps) ^ r)
      ≤ Real.rpow (rademacherExpectation (fun eps => (F eps) ^ s)) (r / s) := by
  classical
  set N : ℕ := Fintype.card (Fin n1 × Fin n2) with hN
  set w : Finset (Fin n1 × Fin n2) → ℝ :=
    fun eps => rademacherObservationWeight eps with hw
  have hwnn : ∀ eps : Finset (Fin n1 × Fin n2), 0 ≤ w eps := by
    intro eps
    simp only [hw, rademacherObservationWeight]
    positivity
  have hwsum : ∑ eps : Finset (Fin n1 × Fin n2), w eps = 1 := by
    simp only [hw, rademacherObservationWeight]
    rw [Finset.sum_const]
    have hcard : (Finset.univ : Finset (Finset (Fin n1 × Fin n2))).card
        = 2 ^ N := by
      rw [Finset.card_univ, hN]
      exact Fintype.card_finset
    rw [hcard]
    rw [nsmul_eq_mul]
    rw [← hN]
    rw [div_pow, one_pow]
    rw [mul_one_div]
    rw [div_eq_one_iff_eq]
    · push_cast; ring
    · positivity
  have hp : (1 : ℝ) ≤ s / r := by
    rw [le_div_iff₀ hr]; linarith
  have hznn : ∀ eps : Finset (Fin n1 × Fin n2), 0 ≤ (F eps) ^ r := by
    intro eps
    exact Real.rpow_nonneg (hF eps) r
  have key := Real.arith_mean_le_rpow_mean (Finset.univ)
    w (fun eps => (F eps) ^ r)
    (fun i _ => hwnn i) hwsum (fun i _ => hznn i) hp
  have hpow : ∀ eps : Finset (Fin n1 × Fin n2),
      ((F eps) ^ r) ^ (s / r) = (F eps) ^ s := by
    intro eps
    rw [← Real.rpow_mul (hF eps)]
    congr 1
    field_simp
  have hexp : (1 : ℝ) / (s / r) = r / s := by
    rw [one_div_div]
  simp only [rademacherExpectation]
  calc ∑ eps : Finset (Fin n1 × Fin n2),
        rademacherObservationWeight eps * (F eps) ^ r
      = ∑ eps : Finset (Fin n1 × Fin n2), w eps * (F eps) ^ r := by rfl
    _ ≤ (∑ eps : Finset (Fin n1 × Fin n2), w eps * ((F eps) ^ r) ^ (s / r)) ^ (1 / (s / r)) := key
    _ = (∑ eps : Finset (Fin n1 × Fin n2), w eps * (F eps) ^ s) ^ (r / s) := by
          rw [hexp]
          congr 1
          apply Finset.sum_congr rfl
          intro eps _
          rw [hpow eps]
    _ = Real.rpow (∑ eps : Finset (Fin n1 × Fin n2),
          rademacherObservationWeight eps * (F eps) ^ s) (r / s) := by rfl
end KhintchineDependency11
export KhintchineDependency11 (rademacher_expectation_power_mean)

-- Accepted proof by LukeBernese; submission 754df2b3-de47-47a2-9ad0-f21c832c5282.
-- Original source SHA-256: 6e7c18447e8b0e0d92fc09df0851c1fe2b209f2955edf55dd33682aac3a76c57.
namespace KhintchineDependency12
open Matrix MatrixCompletion
open scoped BigOperators

/-! ## Helper facts -/

private lemma rExp_nonneg {n1 n2 : Nat} (F : Finset (Fin n1 × Fin n2) → ℝ)
    (hF : ∀ eps, 0 ≤ F eps) : 0 ≤ rademacherExpectation F := by
  unfold rademacherExpectation rademacherObservationWeight
  apply Finset.sum_nonneg
  intro eps _
  apply mul_nonneg (by positivity) (hF eps)

private lemma rExp_mono {n1 n2 : Nat} (F G : Finset (Fin n1 × Fin n2) → ℝ)
    (h : ∀ eps, F eps ≤ G eps) :
    rademacherExpectation F ≤ rademacherExpectation G := by
  unfold rademacherExpectation rademacherObservationWeight
  apply Finset.sum_le_sum
  intro eps _
  apply mul_le_mul_of_nonneg_left (h eps) (by positivity)

private lemma schattenNorm_base_nonneg {n1 n2 : Nat} (q : ℝ) (M : RealMatrix n1 n2) :
    0 ≤ ∑ k : Fin n2, Real.rpow ((Matrix.toEuclideanLin M).singularValues k) q :=
  Finset.sum_nonneg (fun k _ => Real.rpow_nonneg (LinearMap.singularValues_nonneg _ _) _)

private lemma schattenNorm_nonneg {n1 n2 : Nat} (q : ℝ) (M : RealMatrix n1 n2) :
    0 ≤ schattenNorm q M := by
  unfold schattenNorm; exact Real.rpow_nonneg (schattenNorm_base_nonneg q M) _

private lemma schattenNorm_rpow_self {n1 n2 : Nat} (q : ℝ) (hq : 0 < q) (M : RealMatrix n1 n2) :
    (schattenNorm q M) ^ q = ∑ k : Fin n2, ((Matrix.toEuclideanLin M).singularValues k) ^ q := by
  rw [show (schattenNorm q M) ^ q
        = ((∑ k : Fin n2, Real.rpow ((Matrix.toEuclideanLin M).singularValues k) q) ^ (q⁻¹)) ^ q
        from rfl]
  rw [← Real.rpow_mul (schattenNorm_base_nonneg q M)]
  rw [inv_mul_cancel₀ (ne_of_gt hq), Real.rpow_one]
  rfl

/-! ## STEP A (pointwise): schatten_q^q ≤ N^{1-q/2n} · schatten_2n^q -/

private lemma stepA {n1 n2 : Nat} (n : Nat) (hn : 1 ≤ n) (q : ℝ) (hq2 : 2 ≤ q) (hqle : q ≤ 2 * n)
    (M : RealMatrix n1 n2) :
    (schattenNorm q M) ^ q
      ≤ (n2 : ℝ) ^ (1 - q / (2 * n)) * (schattenNorm (2 * n : ℝ) M) ^ q := by
  have hq0 : 0 < q := by linarith
  have h2n0 : (0:ℝ) < 2 * n := by positivity
  set σ : Fin n2 → ℝ := fun k => (Matrix.toEuclideanLin M).singularValues k with hσdef
  have hσ0 : ∀ k, 0 ≤ σ k := fun k => LinearMap.singularValues_nonneg _ _
  rw [schattenNorm_rpow_self q hq0 M]
  have hpm := sum_rpow_le_card_rpow_mul_sum_rpow σ hσ0 q (2 * n : ℝ) hq0 hqle
  have hb : (∑ k, (σ k) ^ (2 * n : ℝ)) ^ (q / (2 * n)) = (schattenNorm (2 * n : ℝ) M) ^ q := by
    rw [← schattenNorm_rpow_self (2 * n : ℝ) h2n0 M]
    rw [← Real.rpow_mul (schattenNorm_nonneg _ _)]
    congr 1
    field_simp
  rw [hb] at hpm
  exact hpm

/-! ## Window collapse: N^{1-q/2n} ≤ e²  -/

private lemma window_collapse (N : ℕ) (hN : 1 ≤ N) (n : ℕ) (hn : 1 ≤ n) (q : ℝ)
    (hq2 : 2 ≤ q) (hqle : q ≤ 2 * n) (h2nle : (2 * n : ℝ) ≤ q + 2)
    (hlogN : Real.log (N : ℝ) ≤ q) :
    (N : ℝ) ^ (1 - q / (2 * n)) ≤ Real.exp 1 ^ 2 := by
  have hq0 : 0 < q := by linarith
  have h2n0 : (0:ℝ) < 2 * n := by positivity
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0:ℝ) < N := by linarith
  have hexp : 1 - q / (2 * n) ≤ 2 / q := by
    have hstep1 : 1 - q / (2 * n) ≤ 2 / (2 * n) := by
      have h1 : (1 - q / (2 * n)) = ((2 * n : ℝ) - q) / (2 * n) := by field_simp
      rw [h1, div_le_div_iff_of_pos_right h2n0]
      linarith
    have hstep2 : 2 / (2 * n : ℝ) ≤ 2 / q := by
      apply div_le_div_of_nonneg_left (by norm_num) hq0 hqle
    linarith
  calc (N : ℝ) ^ (1 - q / (2 * n))
      ≤ (N : ℝ) ^ (2 / q) := by
        apply Real.rpow_le_rpow_of_exponent_le hN1 hexp
    _ = ((N : ℝ) ^ (q⁻¹)) ^ (2:ℝ) := by
        rw [← Real.rpow_mul (le_of_lt hNpos)]
        congr 1; rw [inv_mul_eq_div]
    _ ≤ (Real.exp 1) ^ (2:ℝ) := by
        apply Real.rpow_le_rpow (Real.rpow_nonneg (le_of_lt hNpos) _)
        · exact rank_rpow_inv_le_exp_one_of_log_le N q hN (by linarith) hlogN
        · norm_num
    _ = Real.exp 1 ^ 2 := by rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]

/-! ## Combined general-q bound -/

private lemma general_q_bound {n1 n2 : Nat} (n : Nat) (hn : 1 ≤ n)
    (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (hp : 0 ≤ p) (X : RealMatrix n1 n2)
    (q : ℝ) (hq2 : 2 ≤ q) (hqle : q ≤ 2 * n) (h2nle : (2 * n : ℝ) ≤ q + 2)
    (hd1 : 1 ≤ (n1 + n2)) (hlogd : Real.log ((n1 + n2 : ℕ)) ≤ (2 * n : ℕ))
    (hN1 : 1 ≤ n2) (hlogN : Real.log (n2 : ℝ) ≤ q) :
    rademacherExpectation (fun eps =>
        schattenNorm q (rademacherSampledMatrix Omega eps p X) ^ q)
      ≤ Real.exp 1 ^ 2 *
          (Real.sqrt (2 * n : ℕ) * Real.exp 1 * rademacherSampledVarianceScale Omega p X) ^ q := by
  have hq0 : 0 < q := by linarith
  have h2n0 : (0:ℝ) < 2 * n := by positivity
  set rsvs := rademacherSampledVarianceScale Omega p X with hrsvs
  set G : Finset (Fin n1 × Fin n2) → ℝ :=
    fun eps => schattenNorm (2 * n : ℝ) (rademacherSampledMatrix Omega eps p X) with hG
  have hGnn : ∀ eps, 0 ≤ G eps := fun eps => schattenNorm_nonneg _ _
  have hB : rademacherExpectation (fun eps =>
              schattenNorm q (rademacherSampledMatrix Omega eps p X) ^ q)
            ≤ (n2 : ℝ) ^ (1 - q / (2 * n)) *
                rademacherExpectation (fun eps => (G eps) ^ q) := by
    rw [show (n2 : ℝ) ^ (1 - q / (2 * n)) * rademacherExpectation (fun eps => (G eps) ^ q)
          = rademacherExpectation (fun eps => (n2 : ℝ) ^ (1 - q / (2 * n)) * (G eps) ^ q) from ?_]
    · apply rExp_mono
      intro eps
      exact stepA n hn q hq2 hqle (rademacherSampledMatrix Omega eps p X)
    · unfold rademacherExpectation
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro eps _; ring
  have hJ := rademacher_expectation_power_mean (n1 := n1) (n2 := n2) q (2 * n) hq0 hqle G hGnn
  have hD : rademacherExpectation (fun eps => (G eps) ^ (2 * n : ℝ))
            ≤ (Real.sqrt (2 * n : ℕ) * Real.exp 1 * rsvs) ^ (2 * n) := by
    have := even2n_schatten_moment_bound n hn Omega p X hd1 hlogd
    have halign : (fun eps => (G eps) ^ (2 * n : ℝ))
        = (fun eps => schattenNorm (2 * n : ℝ) (rademacherSampledMatrix Omega eps p X) ^ (2 * n)) := by
      funext eps
      rw [hG]
      rw [← Real.rpow_natCast (schattenNorm (2*n:ℝ) (rademacherSampledMatrix Omega eps p X)) (2*n)]
      norm_num
    rw [halign]
    exact this
  have hExpGq_nn : 0 ≤ rademacherExpectation (fun eps => (G eps) ^ (2 * n : ℝ)) :=
    rExp_nonneg _ (fun eps => Real.rpow_nonneg (hGnn eps) _)
  have hrsvs_nn : 0 ≤ rsvs := by
    rw [hrsvs]; unfold rademacherSampledVarianceScale
    apply mul_nonneg (inv_nonneg.mpr hp) (Real.sqrt_nonneg _)
  have hRHS_nn : 0 ≤ Real.sqrt (2 * n : ℕ) * Real.exp 1 * rsvs := by
    apply mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (le_of_lt (Real.exp_pos _))) hrsvs_nn
  have hChain : rademacherExpectation (fun eps => (G eps) ^ q)
      ≤ (Real.sqrt (2 * n : ℕ) * Real.exp 1 * rsvs) ^ q := by
    calc rademacherExpectation (fun eps => (G eps) ^ q)
        ≤ (rademacherExpectation (fun eps => (G eps) ^ (2 * n : ℝ))) ^ (q / (2 * n)) := hJ
      _ ≤ ((Real.sqrt (2 * n : ℕ) * Real.exp 1 * rsvs) ^ (2 * n)) ^ (q / (2 * n)) := by
            apply Real.rpow_le_rpow hExpGq_nn hD (by positivity)
      _ = (Real.sqrt (2 * n : ℕ) * Real.exp 1 * rsvs) ^ q := by
            rw [← Real.rpow_natCast (Real.sqrt (2*n:ℕ) * Real.exp 1 * rsvs) (2*n)]
            rw [← Real.rpow_mul hRHS_nn]
            congr 1; push_cast; field_simp
  have hwin := window_collapse n2 hN1 n hn q hq2 hqle h2nle hlogN
  calc rademacherExpectation (fun eps =>
          schattenNorm q (rademacherSampledMatrix Omega eps p X) ^ q)
      ≤ (n2 : ℝ) ^ (1 - q / (2 * n)) * rademacherExpectation (fun eps => (G eps) ^ q) := hB
    _ ≤ Real.exp 1 ^ 2 * (Real.sqrt (2 * n : ℕ) * Real.exp 1 * rsvs) ^ q := by
        apply mul_le_mul hwin hChain
          (rExp_nonneg _ (fun eps => Real.rpow_nonneg (hGnn eps) _))
        positivity

/-! ## Constant fold -/

private lemma const_fold (n : ℕ) (hn : 1 ≤ n) (q : ℝ) (hq2 : 2 ≤ q) (h2nle : (2 * n : ℝ) ≤ q + 2)
    (rsvs : ℝ) (hrsvs : 0 ≤ rsvs) :
    Real.exp 1 ^ 2 * (Real.sqrt (2 * n : ℕ) * Real.exp 1 * rsvs) ^ q
      ≤ ((Real.exp 1 ^ 3 * Real.sqrt 2) * Real.sqrt q * rsvs) ^ q := by
  have hq0 : 0 < q := by linarith
  have he1 : (1:ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1:ℝ); linarith
  have hepos : 0 < Real.exp 1 := Real.exp_pos _
  have h2n2q : (2 * n : ℝ) ≤ 2 * q := by nlinarith
  have hsqrt : Real.sqrt (2 * n : ℕ) ≤ Real.sqrt 2 * Real.sqrt q := by
    rw [← Real.sqrt_mul (by norm_num)]
    apply Real.sqrt_le_sqrt
    push_cast; linarith
  set A : ℝ := Real.sqrt (2 * n : ℕ) * Real.exp 1 * rsvs with hAdef
  set Bc : ℝ := (Real.exp 1 ^ 3 * Real.sqrt 2) * Real.sqrt q * rsvs with hBdef
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  have hkey : Real.exp 1 ^ 2 * A ≤ Bc := by
    rw [hAdef, hBdef]
    have hstep : Real.exp 1 ^ 2 * (Real.sqrt (2 * n : ℕ) * Real.exp 1)
        ≤ Real.exp 1 ^ 3 * Real.sqrt 2 * Real.sqrt q := by
      have hsq2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
      have hsqq : 0 ≤ Real.sqrt q := Real.sqrt_nonneg _
      calc Real.exp 1 ^ 2 * (Real.sqrt (2 * n : ℕ) * Real.exp 1)
          = Real.exp 1 ^ 3 * Real.sqrt (2 * n : ℕ) := by ring
        _ ≤ Real.exp 1 ^ 3 * (Real.sqrt 2 * Real.sqrt q) := by
            apply mul_le_mul_of_nonneg_left hsqrt (by positivity)
        _ = Real.exp 1 ^ 3 * Real.sqrt 2 * Real.sqrt q := by ring
    calc Real.exp 1 ^ 2 * (Real.sqrt (2 * n : ℕ) * Real.exp 1 * rsvs)
        = (Real.exp 1 ^ 2 * (Real.sqrt (2 * n : ℕ) * Real.exp 1)) * rsvs := by ring
      _ ≤ (Real.exp 1 ^ 3 * Real.sqrt 2 * Real.sqrt q) * rsvs := by
          apply mul_le_mul_of_nonneg_right hstep hrsvs
      _ = Real.exp 1 ^ 3 * Real.sqrt 2 * Real.sqrt q * rsvs := by ring
  have hB0 : 0 ≤ Bc := le_trans (by positivity) hkey
  have hstep1 : Real.exp 1 ^ 2 * A ^ q ≤ (Real.exp 1 ^ 2 * A) ^ q := by
    rw [Real.mul_rpow (by positivity) hA0]
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hA0 q)
    have hbase1 : (1:ℝ) ≤ Real.exp 1 ^ 2 := by nlinarith [hepos, he1]
    calc Real.exp 1 ^ 2 = (Real.exp 1 ^ 2) ^ (1:ℝ) := by rw [Real.rpow_one]
      _ ≤ (Real.exp 1 ^ 2) ^ q := Real.rpow_le_rpow_of_exponent_le hbase1 (by linarith)
  calc Real.exp 1 ^ 2 * A ^ q
      ≤ (Real.exp 1 ^ 2 * A) ^ q := hstep1
    _ ≤ Bc ^ q := by apply Real.rpow_le_rpow (by positivity) hkey (le_of_lt hq0)

/-! ## FINAL : the exact 3090c7ef target -/

theorem rademacher_sampled_matrix_schatten_moment_khintchine_q_ge_two_variance_scale :
    ∃ Ckh : ℝ, 0 < Ckh ∧
      ∀ C' : ℝ, Ckh ≤ C' →
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m q : ℕ)
        (Omega : Finset (Fin n₁ × Fin n₂))
        (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        2 ≤ q →
        (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) →
        rademacherExpectation
            (fun eps =>
              schattenNorm (q : ℝ)
                (rademacherSampledMatrix Omega eps
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q) ≤
          (C' * Real.sqrt (q : ℝ) *
            rademacherSampledVarianceScale Omega
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q := by
  refine ⟨Real.exp 1 ^ 3 * Real.sqrt 2, by positivity, ?_⟩
  intro C' hC' β hβ n₁ n₂ m q Omega X hq2 hqlog
  rw [Nat.cast_max] at hqlog
  set p : ℝ := (m:ℝ)/((n₁:ℝ)*(n₂:ℝ)) with hp
  have hp0 : 0 ≤ p := by rw [hp]; positivity
  set rsvs := rademacherSampledVarianceScale Omega p X with hrsvs
  have hrsvs0 : 0 ≤ rsvs := by
    rw [hrsvs]; unfold rademacherSampledVarianceScale; positivity
  rcases Nat.eq_zero_or_pos n₂ with hn2z | hN1
  · subst hn2z
    have hLHS0 : rademacherExpectation (fun eps =>
        schattenNorm (q:ℝ) (rademacherSampledMatrix Omega eps p X) ^ q) = 0 := by
      have hsch0 : ∀ eps : Finset (Fin n₁ × Fin 0),
          schattenNorm (q:ℝ) (rademacherSampledMatrix Omega eps p X) = 0 := by
        intro eps
        unfold schattenNorm
        rw [Finset.sum_of_isEmpty]
        exact Real.zero_rpow (by positivity)
      have : (fun eps => schattenNorm (q:ℝ) (rademacherSampledMatrix Omega eps p X) ^ q)
          = (fun _ : Finset (Fin n₁ × Fin 0) => (0:ℝ)) := by
        funext eps; rw [hsch0 eps]; exact zero_pow (by omega)
      rw [this]
      unfold rademacherExpectation
      simp
    rw [hLHS0]
    have hC'0 : 0 ≤ C' := le_trans (by positivity) hC'
    apply pow_nonneg
    apply mul_nonneg (mul_nonneg hC'0 (Real.sqrt_nonneg _)) hrsvs0
  set n : ℕ := (q + 1) / 2 with hndef
  have hqR : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq2
  have hn1 : 1 ≤ n := by rw [hndef]; omega
  have h2n_ge : q ≤ 2 * n := by rw [hndef]; omega
  have h2n_le : 2 * n ≤ q + 1 := by rw [hndef]; omega
  have hqle : (q:ℝ) ≤ (2 * n : ℝ) := by exact_mod_cast h2n_ge
  have h2nle : (2 * n : ℝ) ≤ (q:ℝ) + 2 := by
    have : (2 * n : ℝ) ≤ (q:ℝ) + 1 := by exact_mod_cast h2n_le
    linarith
  have hmaxpos : (1:ℝ) ≤ (max n₁ n₂ : ℝ) := by
    have hnat : 1 ≤ max n₁ n₂ := le_trans hN1 (le_max_right n₁ n₂)
    have : (1:ℝ) ≤ ((max n₁ n₂ : ℕ) : ℝ) := by exact_mod_cast hnat
    rwa [Nat.cast_max] at this
  have hlogmax_nn : 0 ≤ Real.log (max n₁ n₂ : ℝ) := Real.log_nonneg hmaxpos
  have hq_ge_2logmax : (q:ℝ) ≥ 2 * Real.log (max n₁ n₂ : ℝ) := by
    have : β * Real.log (max n₁ n₂ : ℝ) ≥ 2 * Real.log (max n₁ n₂ : ℝ) := by
      apply mul_le_mul_of_nonneg_right (le_of_lt hβ) hlogmax_nn
    linarith
  have hlogN : Real.log (n₂ : ℝ) ≤ (q:ℝ) := by
    have h1 : Real.log (n₂ : ℝ) ≤ Real.log (max n₁ n₂ : ℝ) := by
      rcases Nat.eq_zero_or_pos n₂ with h0 | hpos
      · simp [h0]; positivity
      · apply Real.log_le_log (by exact_mod_cast hpos)
        exact_mod_cast le_max_right n₁ n₂
    have h2 : Real.log (max n₁ n₂ : ℝ) ≤ (q:ℝ) := by
      nlinarith [hlogmax_nn]
    linarith
  have hd1 : 1 ≤ n₁ + n₂ := by omega
  have hlogd : Real.log ((n₁ + n₂ : ℕ)) ≤ ((2 * n : ℕ):ℝ) := by
    have hsum_le : ((n₁ + n₂ : ℕ):ℝ) ≤ 2 * (max n₁ n₂ : ℝ) := by
      push_cast; rw [two_mul]
      have ha : (n₁ : ℝ) ≤ (max n₁ n₂ : ℝ) := by exact_mod_cast le_max_left n₁ n₂
      have hb : (n₂ : ℝ) ≤ (max n₁ n₂ : ℝ) := by exact_mod_cast le_max_right n₁ n₂
      linarith
    have hsumpos : (0:ℝ) < ((n₁ + n₂ : ℕ):ℝ) := by exact_mod_cast hd1
    calc Real.log ((n₁ + n₂ : ℕ):ℝ)
        ≤ Real.log (2 * (max n₁ n₂ : ℝ)) := Real.log_le_log hsumpos hsum_le
      _ = Real.log 2 + Real.log (max n₁ n₂ : ℝ) := by
          rw [Real.log_mul (by norm_num) (by positivity)]
      _ ≤ (q:ℝ) := by
          have hlog2le1 : Real.log 2 ≤ 1 := by
            rw [show (1:ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
            apply Real.log_le_log (by norm_num)
            linarith [Real.add_one_le_exp (1:ℝ)]
          linarith [hlog2le1, hq_ge_2logmax, hqR]
      _ ≤ ((2 * n : ℕ):ℝ) := by exact_mod_cast h2n_ge
  have hgen := general_q_bound n hn1 Omega p hp0 X (q:ℝ) hqR hqle h2nle hd1 hlogd hN1 hlogN
  have hcf := const_fold n hn1 (q:ℝ) hqR h2nle rsvs hrsvs0
  have hcombined : rademacherExpectation (fun eps =>
        schattenNorm (q:ℝ) (rademacherSampledMatrix Omega eps p X) ^ (q:ℝ))
      ≤ ((Real.exp 1 ^ 3 * Real.sqrt 2) * Real.sqrt (q:ℝ) * rsvs) ^ (q:ℝ) :=
    le_trans hgen hcf
  have hq0 : (0:ℝ) < (q:ℝ) := by linarith [hqR]
  have hLHS_eq : rademacherExpectation (fun eps =>
        schattenNorm (q:ℝ) (rademacherSampledMatrix Omega eps p X) ^ q)
      = rademacherExpectation (fun eps =>
        schattenNorm (q:ℝ) (rademacherSampledMatrix Omega eps p X) ^ (q:ℝ)) := by
    apply congrArg
    funext eps
    rw [← Real.rpow_natCast (schattenNorm (q:ℝ) (rademacherSampledMatrix Omega eps p X)) q]
  rw [hLHS_eq]
  have hCkh_le : (Real.exp 1 ^ 3 * Real.sqrt 2) ≤ C' := hC'
  have hbase_nn : 0 ≤ C' * Real.sqrt (q:ℝ) * rsvs := by
    have : 0 ≤ C' := le_trans (by positivity) hC'
    apply mul_nonneg (mul_nonneg this (Real.sqrt_nonneg _)) hrsvs0
  rw [← Real.rpow_natCast (C' * Real.sqrt (q:ℝ) * rsvs) q]
  refine le_trans hcombined ?_
  apply Real.rpow_le_rpow (by positivity) ?_ (le_of_lt hq0)
  apply mul_le_mul_of_nonneg_right _ hrsvs0
  apply mul_le_mul_of_nonneg_right hCkh_le (Real.sqrt_nonneg _)
end KhintchineDependency12
export KhintchineDependency12 (rademacher_sampled_matrix_schatten_moment_khintchine_q_ge_two_variance_scale)

set_option autoImplicit false

open MatrixCompletion
open scoped BigOperators

namespace GramComparison

lemma component_le_lp {ι : Type*} [Fintype ι] (f : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) (q : ℝ) (hq : 0 < q) (i : ι) :
    f i ≤ (∑ j, (f j) ^ q) ^ q⁻¹ := by
  classical
  have hsum : (f i) ^ q ≤ ∑ j, (f j) ^ q :=
    Finset.single_le_sum (fun j _ => Real.rpow_nonneg (hf j) _) (Finset.mem_univ i)
  have h := Real.rpow_le_rpow (Real.rpow_nonneg (hf i) _) hsum
    (inv_nonneg.mpr hq.le)
  rwa [← Real.rpow_mul (hf i), mul_inv_cancel₀ hq.ne', Real.rpow_one] at h

lemma scaled_sqrt_sup_le_lp {ι : Type*} [Fintype ι] (energy : ι → ℝ)
    (a : ℝ) (ha : 0 ≤ a) (q : ℝ) (hq : 0 < q) :
    a * Real.sqrt (⨆ i, energy i) ≤
      (∑ i, (a * Real.sqrt (energy i)) ^ q) ^ q⁻¹ := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl h =>
      simp [iSup_of_empty', Real.sSup_empty, Real.zero_rpow (inv_pos.mpr hq).ne']
  | inr h =>
      obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := energy)
      rw [← hi]
      exact component_le_lp (fun i => a * Real.sqrt (energy i))
        (fun i => mul_nonneg ha (Real.sqrt_nonneg _)) q hq i

theorem variance_le_gram {n1 n2 : ℕ}
    (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (hp : 0 ≤ p)
    (X : RealMatrix n1 n2) (q : ℝ) (hq : 0 < q) :
    rademacherSampledVarianceScale Omega p X ≤
      max (sampledRowGramSchatten Omega p X q)
        (sampledColumnGramSchatten Omega p X q) := by
  have hr : p⁻¹ * Real.sqrt (sampledRowEnergyMax Omega X) ≤
      sampledRowGramSchatten Omega p X q :=
    scaled_sqrt_sup_le_lp _ _ (inv_nonneg.mpr hp) q hq
  have hc : p⁻¹ * Real.sqrt (sampledColumnEnergyMax Omega X) ≤
      sampledColumnGramSchatten Omega p X q :=
    scaled_sqrt_sup_le_lp _ _ (inv_nonneg.mpr hp) q hq
  unfold rademacherSampledVarianceScale
  rcases le_total (sampledRowEnergyMax Omega X) (sampledColumnEnergyMax Omega X) with h | h
  · rw [max_eq_right h]
    exact hc.trans (le_max_right _ _)
  · rw [max_eq_left h]
    exact hr.trans (le_max_left _ _)

end GramComparison

theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m q : ℕ)
        (Omega : Finset (Fin n₁ × Fin n₂))
        (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        2 ≤ q →
        (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) →
        rademacherExpectation
            (fun eps =>
              schattenNorm (q : ℝ)
                (rademacherSampledMatrix Omega eps
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q) ≤
          (C * Real.sqrt (q : ℝ) *
            max (sampledRowGramSchatten Omega
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X (q : ℝ))
                (sampledColumnGramSchatten Omega
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X (q : ℝ))) ^ q := by
  obtain ⟨C, hC, hbound⟩ :=
    rademacher_sampled_matrix_schatten_moment_khintchine_q_ge_two_variance_scale
  refine ⟨C, hC, ?_⟩
  intro β hβ n₁ n₂ m q Omega X hq hwindow
  have hp : 0 ≤ (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) := by positivity
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hscale := GramComparison.variance_le_gram Omega
    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) hp X (q : ℝ) hqpos
  have hfactor : 0 ≤ C * Real.sqrt (q : ℝ) :=
    mul_nonneg hC.le (Real.sqrt_nonneg _)
  have hbase : 0 ≤ C * Real.sqrt (q : ℝ) *
      rademacherSampledVarianceScale Omega
        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X := by
    apply mul_nonneg hfactor
    unfold rademacherSampledVarianceScale
    exact mul_nonneg (inv_nonneg.mpr hp) (Real.sqrt_nonneg _)
  exact (hbound C le_rfl β hβ n₁ n₂ m q Omega X hq hwindow).trans
    (pow_le_pow_left₀ hbase (mul_le_mul_of_nonneg_left hscale hfactor) q)


end KhintchineProof

open MatrixCompletion

theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m q : ℕ)
        (Omega : Finset (Fin n₁ × Fin n₂))
        (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        2 ≤ q →
        (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) →
        rademacherExpectation
            (fun eps =>
              schattenNorm (q : ℝ)
                (rademacherSampledMatrix Omega eps
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q) ≤
          (C * Real.sqrt (q : ℝ) *
            max (sampledRowGramSchatten Omega
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X (q : ℝ))
                (sampledColumnGramSchatten Omega
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X (q : ℝ))) ^ q := by
  exact KhintchineProof.solution


#print axioms solution

