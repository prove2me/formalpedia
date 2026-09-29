-- Prove2me | solution 1 for schatten_norm_le_exp_spectral_norm
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-21T17:56:58.461085+00:00
-- url     : https://prove2.me/submissions/7098b02b-40a3-4cf8-9019-3b6dd3ccbaac

import Definitions.Def_matrix_completion_schatten
import Definitions.Def_matrix_completion_tangent
import Theorems.Thm_singular_value_zero_le_spectral_norm
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.InnerProductSpace.SingularValues

open MatrixCompletion
open scoped BigOperators

/-- `n^{1/q} ≤ e` when `1 ≤ q` and `log n ≤ q`. -/
private theorem n_rpow_inv_q_le_e (n : ℕ) (q : ℝ) (hq : 1 ≤ q)
    (hlog : Real.log (n : ℝ) ≤ q) : (n : ℝ) ^ q⁻¹ ≤ Real.exp 1 := by
  have hqpos : (0:ℝ) < q := lt_of_lt_of_le one_pos hq
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n
    · rw [Nat.cast_zero, Real.zero_rpow (by positivity)]; positivity
    · rw [Nat.cast_one, Real.one_rpow]; exact Real.one_le_exp (by norm_num)
  · have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast Nat.one_le_of_lt hn
    have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
    have hexp : q⁻¹ ≤ (Real.log (n:ℝ))⁻¹ := (inv_le_inv₀ hqpos hlogpos).mpr hlog
    calc (n : ℝ) ^ q⁻¹ ≤ (n : ℝ) ^ (Real.log (n:ℝ))⁻¹ :=
          Real.rpow_le_rpow_of_exponent_le hn1 hexp
      _ ≤ Real.exp 1 := Real.rpow_inv_log_le_exp_one

theorem solution :
    ∀ {n₁ n₂ : ℕ} (q : ℝ) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
      1 ≤ q → Real.log (n₂ : ℝ) ≤ q →
      schattenNorm q X ≤ Real.exp 1 * spectralNorm X := by
  intro n₁ n₂ q X hq hlog
  set T := Matrix.toEuclideanLin X with hT
  set σ := fun k : ℕ => T.singularValues k with hσ
  have hqpos : (0:ℝ) < q := lt_of_lt_of_le one_pos hq
  have hqne : q ≠ 0 := ne_of_gt hqpos
  have hσ0_nn : 0 ≤ σ 0 := T.singularValues_nonneg 0
  have hanti : ∀ k : Fin n₂, σ (k : ℕ) ≤ σ 0 :=
    fun k => T.singularValues_antitone (Nat.zero_le _)
  have hpow : ∀ k : Fin n₂, (σ (k:ℕ)) ^ q ≤ (σ 0) ^ q :=
    fun k => Real.rpow_le_rpow (T.singularValues_nonneg _) (hanti k) (le_of_lt hqpos)
  have hsum : (∑ k : Fin n₂, (σ (k:ℕ)) ^ q) ≤ (n₂ : ℝ) * (σ 0) ^ q := by
    calc (∑ k : Fin n₂, (σ (k:ℕ)) ^ q)
        ≤ ∑ _k : Fin n₂, (σ 0) ^ q := Finset.sum_le_sum (fun k _ => hpow k)
      _ = (n₂ : ℝ) * (σ 0) ^ q := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hschatten_eq : schattenNorm q X = (∑ k : Fin n₂, (σ (k:ℕ)) ^ q) ^ q⁻¹ := rfl
  have hsum_nn : 0 ≤ ∑ k : Fin n₂, (σ (k:ℕ)) ^ q :=
    Finset.sum_nonneg (fun k _ => Real.rpow_nonneg (T.singularValues_nonneg _) _)
  have hinv_nn : (0:ℝ) ≤ q⁻¹ := by positivity
  have step1 : (∑ k : Fin n₂, (σ (k:ℕ)) ^ q) ^ q⁻¹
      ≤ ((n₂ : ℝ) * (σ 0) ^ q) ^ q⁻¹ :=
    Real.rpow_le_rpow hsum_nn hsum hinv_nn
  have step2 : ((n₂ : ℝ) * (σ 0) ^ q) ^ q⁻¹ = (n₂ : ℝ) ^ q⁻¹ * (σ 0) := by
    rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hσ0_nn _)]
    rw [Real.rpow_rpow_inv hσ0_nn hqne]
  have hne : (n₂ : ℝ) ^ q⁻¹ ≤ Real.exp 1 := n_rpow_inv_q_le_e n₂ q hq hlog
  have step3 : (n₂ : ℝ) ^ q⁻¹ * (σ 0) ≤ Real.exp 1 * (σ 0) :=
    mul_le_mul_of_nonneg_right hne hσ0_nn
  have step4 : Real.exp 1 * (σ 0) ≤ Real.exp 1 * spectralNorm X :=
    mul_le_mul_of_nonneg_left (singular_value_zero_le_spectral_norm X)
      (le_of_lt (Real.exp_pos 1))
  calc schattenNorm q X
      = (∑ k : Fin n₂, (σ (k:ℕ)) ^ q) ^ q⁻¹ := hschatten_eq
    _ ≤ ((n₂ : ℝ) * (σ 0) ^ q) ^ q⁻¹ := step1
    _ = (n₂ : ℝ) ^ q⁻¹ * (σ 0) := step2
    _ ≤ Real.exp 1 * (σ 0) := step3
    _ ≤ Real.exp 1 * spectralNorm X := step4
