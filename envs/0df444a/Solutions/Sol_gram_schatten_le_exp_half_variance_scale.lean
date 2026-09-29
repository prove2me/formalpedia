-- Prove2me | solution 1 for gram_schatten_le_exp_half_variance_scale
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-06-22T02:15:29.557412+00:00
-- url     : https://prove2.me/submissions/2c69db68-d607-44c4-b18c-efe3007f312b

import Definitions.Def_matrix_completion_gram_schatten
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open scoped BigOperators
open MatrixCompletion

namespace MatrixCompletion

open scoped Classical BigOperators

/-- Pure `ℓ_q ≤ N^{1/q}·ℓ_∞` comparison for finitely many nonnegative reals. -/
theorem lq_le_card_rpow_inv_mul_sup {N : ℕ} (a : Fin N → ℝ) (q B : ℝ)
    (hq : 1 ≤ q) (hB : 0 ≤ B) (ha : ∀ i, 0 ≤ a i) (hsup : ∀ i, a i ≤ B) :
    Real.rpow (∑ i : Fin N, Real.rpow (a i) q) q⁻¹ ≤ (N : ℝ) ^ q⁻¹ * B := by
  have hqpos : 0 < q := lt_of_lt_of_le one_pos hq
  have hsum_le : (∑ i : Fin N, Real.rpow (a i) q) ≤ (N : ℝ) * Real.rpow B q := by
    have : (∑ i : Fin N, Real.rpow (a i) q) ≤ ∑ _i : Fin N, Real.rpow B q := by
      apply Finset.sum_le_sum
      intro i _
      exact Real.rpow_le_rpow (ha i) (hsup i) (le_of_lt hqpos)
    simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using this
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hqne : q ≠ 0 := ne_of_gt hqpos
  have hNq : ((N : ℝ) ^ q⁻¹) ^ q = (N : ℝ) := by
    rw [← Real.rpow_mul hNnn, inv_mul_cancel₀ hqne, Real.rpow_one]
  have hRHSnn : (0 : ℝ) ≤ (N : ℝ) ^ q⁻¹ * B := by positivity
  have hrhs_eq : (N : ℝ) * Real.rpow B q = Real.rpow ((N : ℝ) ^ q⁻¹ * B) q := by
    rw [show Real.rpow ((N : ℝ) ^ q⁻¹ * B) q = ((N : ℝ) ^ q⁻¹ * B) ^ q from rfl,
      Real.mul_rpow (by positivity) hB, hNq]
    rfl
  rw [hrhs_eq] at hsum_le
  have hmono :
      Real.rpow (∑ i : Fin N, Real.rpow (a i) q) q⁻¹ ≤
        Real.rpow (Real.rpow ((N : ℝ) ^ q⁻¹ * B) q) q⁻¹ := by
    apply Real.rpow_le_rpow _ hsum_le (by positivity)
    apply Finset.sum_nonneg
    intro i _
    exact Real.rpow_nonneg (ha i) q
  have hcollapse : Real.rpow (Real.rpow ((N : ℝ) ^ q⁻¹ * B) q) q⁻¹ = (N : ℝ) ^ q⁻¹ * B :=
    Real.rpow_rpow_inv hRHSnn hqne
  rw [hcollapse] at hmono
  exact hmono

/-- Window collapse: for `M ≥ 1`, `β > 2`, `q ≥ β·log M`, `q ≥ 1`, we have `M^{1/q} ≤ e^{1/2}`. -/
theorem card_rpow_inv_le_exp_half {M : ℕ} (q β : ℝ)
    (hM : 1 ≤ M) (hβ : 2 < β) (hq : 1 ≤ q)
    (hqlog : q ≥ β * Real.log (M : ℝ)) :
    ((M : ℝ) ^ q⁻¹) ≤ Real.exp (1 / 2) := by
  have hqpos : 0 < q := lt_of_lt_of_le one_pos hq
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hMpos : (0 : ℝ) < (M : ℝ) := lt_of_lt_of_le one_pos hM1
  have hlognn : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg hM1
  have hrw : (M : ℝ) ^ q⁻¹ = Real.exp (Real.log (M : ℝ) * q⁻¹) := by
    rw [Real.rpow_def_of_pos hMpos]
  rw [hrw]
  apply Real.exp_le_exp.mpr
  rcases eq_or_lt_of_le hlognn with hlog0 | hlogpos
  · rw [← hlog0]; simp
  · have hβpos : 0 < β := by linarith
    have hqge : β * Real.log (M : ℝ) ≤ q := hqlog
    have hqgepos : 0 < β * Real.log (M : ℝ) := mul_pos hβpos hlogpos
    have hqpos' : 0 < q := lt_of_lt_of_le hqgepos hqge
    rw [mul_inv_le_iff₀ hqpos']
    have hstep : Real.log (M : ℝ) ≤ (1/2 : ℝ) * (β * Real.log (M : ℝ)) := by
      have hb : (1 : ℝ) ≤ (1/2 : ℝ) * β := by linarith
      nlinarith [hlogpos, hb]
    linarith

theorem row_value_le_varScale {n1 n2 : Nat}
    (Omega : Finset (Fin n1 × Fin n2)) (p : Real) (X : RealMatrix n1 n2)
    (hp : 0 ≤ p⁻¹) (i : Fin n1) :
    p⁻¹ * Real.sqrt (∑ j : Fin n2, if (i, j) ∈ Omega then X i j ^ 2 else 0) ≤
      rademacherSampledVarianceScale Omega p X := by
  unfold rademacherSampledVarianceScale
  apply mul_le_mul_of_nonneg_left _ hp
  apply Real.sqrt_le_sqrt
  refine le_trans ?_ (le_max_left _ _)
  apply le_ciSup (f := fun i : Fin n1 => ∑ j : Fin n2, if (i, j) ∈ Omega then X i j ^ 2 else 0)
  exact Finite.bddAbove_range _

theorem col_value_le_varScale {n1 n2 : Nat}
    (Omega : Finset (Fin n1 × Fin n2)) (p : Real) (X : RealMatrix n1 n2)
    (hp : 0 ≤ p⁻¹) (j : Fin n2) :
    p⁻¹ * Real.sqrt (∑ i : Fin n1, if (i, j) ∈ Omega then X i j ^ 2 else 0) ≤
      rademacherSampledVarianceScale Omega p X := by
  unfold rademacherSampledVarianceScale
  apply mul_le_mul_of_nonneg_left _ hp
  apply Real.sqrt_le_sqrt
  refine le_trans ?_ (le_max_right _ _)
  apply le_ciSup (f := fun j : Fin n2 => ∑ i : Fin n1, if (i, j) ∈ Omega then X i j ^ 2 else 0)
  exact Finite.bddAbove_range _

theorem varScale_nonneg {n1 n2 : Nat}
    (Omega : Finset (Fin n1 × Fin n2)) (p : Real) (X : RealMatrix n1 n2)
    (hp : 0 ≤ p) : 0 ≤ rademacherSampledVarianceScale Omega p X := by
  unfold rademacherSampledVarianceScale
  exact mul_nonneg (by positivity) (Real.sqrt_nonneg _)

end MatrixCompletion

open MatrixCompletion

/-- **Node B** (CR2009 §6.1, Lemma 6.1 reference comparison, p.24).  The diagonal-Gram
Schatten norms of the coordinate Rademacher series are bounded by the conditional variance
scale `rademacherSampledVarianceScale`, up to the absolute constant `e^{1/2}`, in the window
`q ≥ β·log(max n₁ n₂)` with `β > 2`.  This combines the pure `ℓ_q ≤ N^{1/q}·ℓ_∞` comparison
with the window collapse `(max n₁ n₂)^{1/q} ≤ e^{1/β} ≤ e^{1/2}`. -/
theorem solution {n1 n2 : Nat}
    (Omega : Finset (Fin n1 × Fin n2)) (p : Real) (X : Matrix (Fin n1) (Fin n2) ℝ)
    (q β : Real) (hp : 0 ≤ p) (hβ : 2 < β) (hq : 1 ≤ q)
    (hqlog : q ≥ β * Real.log (↑(max n1 n2))) :
    max (sampledRowGramSchatten Omega p X q) (sampledColumnGramSchatten Omega p X q) ≤
      Real.exp (1 / 2) * rademacherSampledVarianceScale Omega p X := by
  have hpinv : 0 ≤ p⁻¹ := by positivity
  set V := rademacherSampledVarianceScale Omega p X with hV
  have hVnn : 0 ≤ V := varScale_nonneg Omega p X hp
  have hqpos : 0 < q := lt_of_lt_of_le one_pos hq
  have hMcase : 1 ≤ max n1 n2 ∨ max n1 n2 = 0 := by
    rcases Nat.eq_zero_or_pos (max n1 n2) with h | h
    · right; exact h
    · left; exact h
  have hn1le : (n1 : ℝ) ≤ ((max n1 n2 : ℕ) : ℝ) := by exact_mod_cast Nat.le_max_left n1 n2
  have hn2le : (n2 : ℝ) ≤ ((max n1 n2 : ℕ) : ℝ) := by exact_mod_cast Nat.le_max_right n1 n2
  have hq0le : (0 : ℝ) ≤ q⁻¹ := by positivity
  have hn1factor : (n1 : ℝ) ^ q⁻¹ ≤ ((max n1 n2 : ℕ) : ℝ) ^ q⁻¹ :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hn1le hq0le
  have hn2factor : (n2 : ℝ) ^ q⁻¹ ≤ ((max n1 n2 : ℕ) : ℝ) ^ q⁻¹ :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hn2le hq0le
  have hwin : ((max n1 n2 : ℕ) : ℝ) ^ q⁻¹ * V ≤ Real.exp (1/2) * V := by
    rcases hMcase with hM | hM0
    · exact mul_le_mul_of_nonneg_right (card_rpow_inv_le_exp_half q β hM hβ hq hqlog) hVnn
    · rw [hM0]; simp only [Nat.cast_zero]; rw [Real.zero_rpow (by positivity)]
      have : (0:ℝ) ≤ Real.exp (1/2) * V := mul_nonneg (le_of_lt (Real.exp_pos _)) hVnn
      simpa using this
  have hrow : sampledRowGramSchatten Omega p X q ≤ Real.exp (1/2) * V := by
    have h1 : sampledRowGramSchatten Omega p X q ≤ (n1 : ℝ) ^ q⁻¹ * V := by
      unfold sampledRowGramSchatten
      exact lq_le_card_rpow_inv_mul_sup
        (fun i => p⁻¹ * Real.sqrt (∑ j : Fin n2, if (i, j) ∈ Omega then X i j ^ 2 else 0))
        q V hq hVnn
        (fun i => mul_nonneg hpinv (Real.sqrt_nonneg _))
        (fun i => row_value_le_varScale Omega p X hpinv i)
    have h2 : (n1 : ℝ) ^ q⁻¹ * V ≤ ((max n1 n2 : ℕ) : ℝ) ^ q⁻¹ * V :=
      mul_le_mul_of_nonneg_right hn1factor hVnn
    linarith
  have hcol : sampledColumnGramSchatten Omega p X q ≤ Real.exp (1/2) * V := by
    have h1 : sampledColumnGramSchatten Omega p X q ≤ (n2 : ℝ) ^ q⁻¹ * V := by
      unfold sampledColumnGramSchatten
      exact lq_le_card_rpow_inv_mul_sup
        (fun j => p⁻¹ * Real.sqrt (∑ i : Fin n1, if (i, j) ∈ Omega then X i j ^ 2 else 0))
        q V hq hVnn
        (fun j => mul_nonneg hpinv (Real.sqrt_nonneg _))
        (fun j => col_value_le_varScale Omega p X hpinv j)
    have h2 : (n2 : ℝ) ^ q⁻¹ * V ≤ ((max n1 n2 : ℕ) : ℝ) ^ q⁻¹ * V :=
      mul_le_mul_of_nonneg_right hn2factor hVnn
    linarith
  exact max_le hrow hcol
