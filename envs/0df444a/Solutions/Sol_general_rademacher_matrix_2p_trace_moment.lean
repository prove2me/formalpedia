-- Prove2me | solution 1 for general_rademacher_matrix_2p_trace_moment
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-06-24T04:53:24.856986+00:00
-- url     : https://prove2.me/submissions/2ab3c601-dc90-4b3b-826d-cb441bf86a9b

import Mathlib
open Matrix
open scoped BigOperators
open scoped MatrixOrder

theorem solution
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
