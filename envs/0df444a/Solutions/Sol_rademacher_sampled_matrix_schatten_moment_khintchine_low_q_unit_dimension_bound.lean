-- Prove2me | solution 1 for rademacher_sampled_matrix_schatten_moment_khintchine_low_q_unit_dimension_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-23T21:20:34.812173+00:00
-- url     : https://prove2.me/submissions/651d690d-0796-4e0b-896e-543357919c6d

import Definitions.Def_matrix_completion_gram_schatten
import Theorems.Thm_schatten_norm_le_rank_rpow_smul_spectral_norm
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic

open MatrixCompletion
open scoped Classical BigOperators Matrix.Norms.L2Operator

private lemma spectralNorm_eq_l2_opNorm
    {n₁ n₂ : ℕ} (X : Matrix (Fin n₁) (Fin n₂) ℝ) :
    spectralNorm X = ‖X‖ := by
  simp [spectralNorm, Matrix.l2_opNorm_def]

private lemma spectralNorm_const_one_by_one (a : ℝ) :
    spectralNorm (fun _ _ : Fin 1 => a) = |a| := by
  have hdiag :
      Matrix.of (fun _ _ : Fin 1 => a) =
        (Matrix.diagonal (fun _ : Fin 1 => a) :
          Matrix (Fin 1) (Fin 1) ℝ) := by
    ext i j
    fin_cases i
    fin_cases j
    simp
  have h1 : spectralNorm (Matrix.of (fun _ _ : Fin 1 => a)) =
      ‖Matrix.of (fun _ _ : Fin 1 => a)‖ := spectralNorm_eq_l2_opNorm _
  have h2 : ‖Matrix.of (fun _ _ : Fin 1 => a)‖ =
      ‖(Matrix.diagonal (fun _ : Fin 1 => a) : Matrix (Fin 1) (Fin 1) ℝ)‖ := by
    rw [hdiag]
  have h3 : ‖(Matrix.diagonal (fun _ : Fin 1 => a) : Matrix (Fin 1) (Fin 1) ℝ)‖ = |a| := by
    rw [Matrix.l2_opNorm_diagonal]
    simp
  exact h1.trans (h2.trans h3)

private lemma finrank_range_toEuclideanLin_le_one_of_max_le_one
    {n₁ n₂ : ℕ} (hmax : max n₁ n₂ ≤ 1)
    (Y : Matrix (Fin n₁) (Fin n₂) ℝ) :
    Module.finrank ℝ (LinearMap.range (Matrix.toEuclideanLin Y)) ≤ 1 := by
  have hn₁ : n₁ ≤ 1 := le_trans (Nat.le_max_left n₁ n₂) hmax
  calc
    Module.finrank ℝ (LinearMap.range (Matrix.toEuclideanLin Y))
        ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin n₁)) :=
          Submodule.finrank_le (LinearMap.range (Matrix.toEuclideanLin Y))
    _ = n₁ := by simp
    _ ≤ 1 := hn₁

private lemma schattenNorm_le_spectralNorm_of_max_le_one
    {n₁ n₂ : ℕ} (hmax : max n₁ n₂ ≤ 1)
    (Y : Matrix (Fin n₁) (Fin n₂) ℝ) :
    schattenNorm 1 Y ≤ spectralNorm Y := by
  have h := schatten_norm_le_rank_rpow_smul_spectral_norm (q := (1 : ℝ)) Y (by norm_num)
  have hrank : ((Module.finrank ℝ
      (LinearMap.range (Matrix.toEuclideanLin Y)) : ℝ)) ≤ 1 := by
    exact_mod_cast finrank_range_toEuclideanLin_le_one_of_max_le_one hmax Y
  have hfactor :
      Real.rpow
          ((Module.finrank ℝ
            (LinearMap.range (Matrix.toEuclideanLin Y)) : ℝ)) (1 : ℝ)⁻¹ ≤ 1 := by
    simpa using hrank
  have hspec : 0 ≤ spectralNorm Y := by
    unfold spectralNorm
    positivity
  nlinarith [mul_le_mul_of_nonneg_right hfactor hspec, h]

private lemma rademacherObservationWeight_nonneg {n₁ n₂ : ℕ}
    (eps : Finset (Fin n₁ × Fin n₂)) :
    0 ≤ rademacherObservationWeight eps := by
  unfold rademacherObservationWeight
  positivity

private lemma rademacherObservationWeight_sum_eq_one {n₁ n₂ : ℕ} :
    (∑ eps : Finset (Fin n₁ × Fin n₂),
      rademacherObservationWeight eps) = 1 := by
  classical
  unfold rademacherObservationWeight
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset]
  norm_num [Nat.cast_pow]
  rw [← mul_pow]
  norm_num

private lemma rademacherSampledVarianceScale_nonneg {n₁ n₂ : ℕ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (p : ℝ)
    (X : Matrix (Fin n₁) (Fin n₂) ℝ) (hp : 0 ≤ p) :
    0 ≤ rademacherSampledVarianceScale Omega p X := by
  unfold rademacherSampledVarianceScale
  exact mul_nonneg (inv_nonneg.mpr hp) (Real.sqrt_nonneg _)

private lemma rademacherSampledMatrix_spectral_le_variance_scale_of_max_le_one
    {n₁ n₂ : ℕ} (hmax : max n₁ n₂ ≤ 1)
    (Omega eps : Finset (Fin n₁ × Fin n₂)) (p : ℝ)
    (X : Matrix (Fin n₁) (Fin n₂) ℝ) (hp : 0 ≤ p) :
    spectralNorm (rademacherSampledMatrix Omega eps p X) ≤
      rademacherSampledVarianceScale Omega p X := by
  have hn₁ : n₁ ≤ 1 := le_trans (Nat.le_max_left n₁ n₂) hmax
  have hn₂ : n₂ ≤ 1 := le_trans (Nat.le_max_right n₁ n₂) hmax
  interval_cases n₁ <;> interval_cases n₂
  · simp [rademacherSampledVarianceScale,
      sampledRowEnergyMax, sampledColumnEnergyMax, spectralNorm]
  · have hY :
        rademacherSampledMatrix Omega eps p X =
          (0 : Matrix (Fin 0) (Fin 1) ℝ) := by
      ext i
      exact Fin.elim0 i
    rw [hY]
    simp [rademacherSampledVarianceScale, sampledRowEnergyMax,
      sampledColumnEnergyMax, spectralNorm]
  · simp [rademacherSampledVarianceScale,
      sampledRowEnergyMax, sampledColumnEnergyMax, spectralNorm]
  · by_cases hmem : ((0 : Fin 1), (0 : Fin 1)) ∈ Omega
    · by_cases hsign : ((0 : Fin 1), (0 : Fin 1)) ∈ eps
      · have hY :
            rademacherSampledMatrix Omega eps p X =
              (fun _ _ : Fin 1 => p⁻¹ * X 0 0) := by
          ext i j
          fin_cases i
          fin_cases j
          simp [rademacherSampledMatrix, rademacherSign, hmem, hsign]
        rw [hY, spectralNorm_const_one_by_one]
        simp [rademacherSampledVarianceScale, sampledRowEnergyMax,
          sampledColumnEnergyMax, hmem, Real.sqrt_sq_eq_abs, max_self,
          abs_mul, abs_of_nonneg (inv_nonneg.mpr hp)]
      · have hY :
            rademacherSampledMatrix Omega eps p X =
              (fun _ _ : Fin 1 => -(p⁻¹ * X 0 0)) := by
          ext i j
          fin_cases i
          fin_cases j
          simp [rademacherSampledMatrix, rademacherSign, hmem, hsign]
        rw [hY, spectralNorm_const_one_by_one]
        simp [rademacherSampledVarianceScale, sampledRowEnergyMax,
          sampledColumnEnergyMax, hmem, Real.sqrt_sq_eq_abs, max_self,
          abs_mul, abs_of_nonneg (inv_nonneg.mpr hp)]
    · have hY :
          rademacherSampledMatrix Omega eps p X =
            (0 : Matrix (Fin 1) (Fin 1) ℝ) := by
        ext i j
        fin_cases i
        fin_cases j
        simp [rademacherSampledMatrix, hmem]
      rw [hY]
      simp [rademacherSampledVarianceScale, sampledRowEnergyMax,
        sampledColumnEnergyMax, hmem, spectralNorm]

private lemma rademacher_schatten_expectation_le_variance_scale_of_low_q_unit
    {n₁ n₂ m q : ℕ}
    (Omega : Finset (Fin n₁ × Fin n₂))
    (X : Matrix (Fin n₁) (Fin n₂) ℝ)
    (hq_one : 1 ≤ q) (hq_low : ¬ 2 ≤ q)
    (hmax : max n₁ n₂ ≤ 1) :
    rademacherExpectation
        (fun eps =>
          schattenNorm (q : ℝ)
            (rademacherSampledMatrix Omega eps
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q) ≤
      rademacherSampledVarianceScale Omega
        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X := by
  have hq_eq : q = 1 := by omega
  subst q
  have hp : 0 ≤ ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) := by positivity
  have hpoint :
      ∀ eps : Finset (Fin n₁ × Fin n₂),
        schattenNorm 1
            (rademacherSampledMatrix Omega eps
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ≤
          rademacherSampledVarianceScale Omega
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X := by
    intro eps
    exact le_trans
      (schattenNorm_le_spectralNorm_of_max_le_one hmax _)
      (rademacherSampledMatrix_spectral_le_variance_scale_of_max_le_one
        hmax Omega eps _ X hp)
  unfold rademacherExpectation
  calc
    (∑ eps : Finset (Fin n₁ × Fin n₂),
          rademacherObservationWeight eps *
          (fun eps =>
            schattenNorm (((1 : ℕ) : ℝ))
              (rademacherSampledMatrix Omega eps
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ (1 : ℕ)) eps)
        ≤ ∑ eps : Finset (Fin n₁ × Fin n₂),
            rademacherObservationWeight eps *
              rademacherSampledVarianceScale Omega
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X := by
          apply Finset.sum_le_sum
          intro eps _heps
          simpa using mul_le_mul_of_nonneg_left (hpoint eps)
            (rademacherObservationWeight_nonneg eps)
    _ = rademacherSampledVarianceScale Omega
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X := by
          rw [← Finset.sum_mul]
          rw [rademacherObservationWeight_sum_eq_one]
          simp

theorem solution :
    ∃ Ckh : ℝ, 0 < Ckh ∧
      ∀ C' : ℝ, Ckh ≤ C' →
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m q : ℕ)
        (Omega : Finset (Fin n₁ × Fin n₂))
        (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        1 ≤ q →
        ¬ 2 ≤ q →
        max n₁ n₂ ≤ 1 →
        (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) →
        rademacherExpectation
            (fun eps =>
              schattenNorm (q : ℝ)
                (rademacherSampledMatrix Omega eps
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q) ≤
          (C' * Real.sqrt (q : ℝ) *
            rademacherSampledVarianceScale Omega
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q := by
  refine ⟨1, by norm_num, ?_⟩
  intro C' hC' β _hβ n₁ n₂ m q Omega X hq_one hq_low hmax _hq_log
  have hq_eq : q = 1 := by omega
  subst q
  have hbase :=
    rademacher_schatten_expectation_le_variance_scale_of_low_q_unit
      (m := m) (q := 1) (Omega := Omega) (X := X) hq_one hq_low hmax
  have hp : 0 ≤ ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) := by positivity
  have hvar_nonneg :
      0 ≤ rademacherSampledVarianceScale Omega
        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X :=
    rademacherSampledVarianceScale_nonneg Omega _ X hp
  have hscale :
      rademacherSampledVarianceScale Omega
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X ≤
        (C' * Real.sqrt (((1 : ℕ) : ℝ)) *
          rademacherSampledVarianceScale Omega
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ (1 : ℕ) := by
    rw [pow_one]
    norm_num
    nlinarith [mul_le_mul_of_nonneg_right hC' hvar_nonneg]
  exact le_trans hbase hscale
