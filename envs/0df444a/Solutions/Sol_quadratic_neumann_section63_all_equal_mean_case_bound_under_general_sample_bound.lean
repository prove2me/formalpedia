-- Prove2me | solution 1 for quadratic_neumann_section63_all_equal_mean_case_bound_under_general_sample_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-30T18:16:01.939744+00:00
-- url     : https://prove2.me/submissions/782e286b-0285-42f2-bb9c-2591c44f01f0

import Theorems.Thm_quadratic_neumann_all_equal_mean_as_scaled_base_matrix
import Theorems.Thm_quadratic_neumann_all_equal_base_spectral_norm_bound_min_dim
import Theorems.Thm_sample_ratio_between_zero_and_one
import Mathlib.Tactic

open MatrixCompletion

private lemma spectralNorm_smul_le_abs
    {n₁ n₂ : ℕ} (a : ℝ) (X : Matrix (Fin n₁) (Fin n₂) ℝ) :
    spectralNorm (a • X) ≤ |a| * spectralNorm X := by
  unfold spectralNorm
  have hlin :
      LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (a • X)) =
        a • LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin X) := by
    ext v i
    simp [Matrix.toEuclideanLin]
  rw [hlin]
  rw [norm_smul]
  simp [Real.norm_eq_abs]

private lemma quadratic_all_equal_scalar_abs_le (p : ℝ)
    (hp : 0 ≤ p) (hp_one : p ≤ 1) :
    |1 - 3 * p + 2 * p ^ 2| ≤ 1 := by
  apply abs_le.mpr
  constructor
  · have hsq : 0 ≤ (2 * p - (3 / 2 : ℝ)) ^ 2 := sq_nonneg _
    nlinarith
  · nlinarith

private lemma all_equal_mean_bound_from_min_dim_base
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (p Cbase μ₀ : ℝ) :
    0 ≤ p → p ≤ 1 →
    quadraticNeumannAllEqualMeanContribution S p =
      ((p⁻¹) ^ 2 * (1 - 3 * p + 2 * p ^ 2)) •
        quadraticNeumannAllEqualBaseMatrix S →
    spectralNorm (quadraticNeumannAllEqualBaseMatrix S) ≤
      Cbase * ((μ₀ * (r : ℝ) / (↑(min n₁ n₂))) ^ 2) →
    spectralNorm (quadraticNeumannAllEqualMeanContribution S p) ≤
      Cbase * (((p⁻¹) ^ 2) *
        ((μ₀ * (r : ℝ) / (↑(min n₁ n₂))) ^ 2)) := by
  intro hp hp_one hmean hbase
  rw [hmean]
  let B : Matrix (Fin n₁) (Fin n₂) ℝ := quadraticNeumannAllEqualBaseMatrix S
  let s : ℝ := μ₀ * (r : ℝ) / (↑(min n₁ n₂))
  let a : ℝ := (p⁻¹) ^ 2 * (1 - 3 * p + 2 * p ^ 2)
  have hinv_sq_nonneg : 0 ≤ (p⁻¹) ^ 2 := sq_nonneg _
  have habs_coeff :
      |a| ≤ (p⁻¹) ^ 2 := by
    have hscalar := quadratic_all_equal_scalar_abs_le p hp hp_one
    calc
      |a| = (p⁻¹) ^ 2 * |1 - 3 * p + 2 * p ^ 2| := by
        simp [a, abs_mul]
      _ ≤ (p⁻¹) ^ 2 * 1 := by
        exact mul_le_mul_of_nonneg_left hscalar hinv_sq_nonneg
      _ = (p⁻¹) ^ 2 := by ring
  have hnorm :
      spectralNorm (a • B) ≤ |a| * spectralNorm B :=
    spectralNorm_smul_le_abs a B
  have hcoeff_norm :
      |a| * spectralNorm B ≤
        (p⁻¹) ^ 2 * spectralNorm B := by
    exact mul_le_mul_of_nonneg_right habs_coeff (norm_nonneg _)
  have hbase' :
      spectralNorm B ≤ Cbase * (s ^ 2) := by
    simpa [B, s] using hbase
  have hscaled_base :
      (p⁻¹) ^ 2 * spectralNorm B ≤
        (p⁻¹) ^ 2 * (Cbase * s ^ 2) := by
    exact mul_le_mul_of_nonneg_left hbase' hinv_sq_nonneg
  have hrearrange :
      (p⁻¹) ^ 2 * (Cbase * s ^ 2) =
        Cbase * (((p⁻¹) ^ 2) * s ^ 2) := by ring
  calc
    spectralNorm (a • B) ≤ |a| * spectralNorm B := hnorm
    _ ≤ (p⁻¹) ^ 2 * spectralNorm B := hcoeff_norm
    _ ≤ (p⁻¹) ^ 2 * (Cbase * s ^ 2) := hscaled_base
    _ = Cbase * (((p⁻¹) ^ 2) * s ^ 2) := hrearrange

private lemma max_mul_min_cast_div
    {n₁ n₂ : ℕ} (hmin : 0 < min n₁ n₂) :
    ((n₁ : ℝ) * (n₂ : ℝ)) / ((min n₁ n₂ : ℕ) : ℝ) =
      ((max n₁ n₂ : ℕ) : ℝ) := by
  have hprod_nat : max n₁ n₂ * min n₁ n₂ = n₁ * n₂ :=
    max_mul_min n₁ n₂
  have hprod :
      ((max n₁ n₂ : ℕ) : ℝ) * ((min n₁ n₂ : ℕ) : ℝ) =
        (n₁ : ℝ) * (n₂ : ℝ) := by
    exact_mod_cast hprod_nat
  have hmin_ne : ((min n₁ n₂ : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hmin)
  calc
    ((n₁ : ℝ) * (n₂ : ℝ)) / ((min n₁ n₂ : ℕ) : ℝ)
        = (((max n₁ n₂ : ℕ) : ℝ) * ((min n₁ n₂ : ℕ) : ℝ)) /
            ((min n₁ n₂ : ℕ) : ℝ) := by rw [hprod]
    _ = ((max n₁ n₂ : ℕ) : ℝ) := by field_simp [hmin_ne]

private lemma all_equal_mean_min_scale_eq_second_term
    {n₁ n₂ r m : ℕ} (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hm : 0 < m)
    (μ₀ : ℝ) :
    ((((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) ^ 2 *
        ((μ₀ * (r : ℝ) / ((min n₁ n₂ : ℕ) : ℝ)) ^ 2)) =
      μ₀ ^ 2 * ((((max n₁ n₂ : ℕ) : ℝ) * (r : ℝ)) / (m : ℝ)) ^ 2 := by
  have hmin_nat : 0 < min n₁ n₂ := lt_min hn₁ hn₂
  let mn : ℝ := ((min n₁ n₂ : ℕ) : ℝ)
  let nn : ℝ := (n₁ : ℝ) * (n₂ : ℝ)
  let N : ℝ := ((max n₁ n₂ : ℕ) : ℝ)
  have hm_ne : (m : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hm)
  have hmn_ne : mn ≠ 0 := by
    dsimp [mn]
    exact_mod_cast (ne_of_gt hmin_nat)
  have hnn_ne : nn ≠ 0 := by
    dsimp [nn]
    positivity
  have hnn_div_min : nn / mn = N := by
    simpa [nn, mn, N] using max_mul_min_cast_div (n₁ := n₁) (n₂ := n₂) hmin_nat
  have hp_inv :
      (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) = nn / (m : ℝ) := by
    dsimp [nn]
    field_simp [hm_ne, hnn_ne]
  rw [hp_inv]
  have hrewrite : nn = N * mn := by
    have h := hnn_div_min
    field_simp [hmn_ne] at h
    linarith
  rw [hrewrite]
  field_simp [hm_ne, hmn_ne]
  ring

theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ C' : ℝ, C ≤ C' →
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          C' * max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
                  (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4))
            * (↑(max n₁ n₂)) * (r : ℝ) * (β * Real.log (↑(max n₁ n₂))) →
        spectralNorm
            (quadraticNeumannAllEqualMeanContribution S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
          (let N : ℝ := ↑(max n₁ n₂)
           let R : ℝ := (r : ℝ)
           let Mobs : ℝ := (m : ℝ)
           let logN : ℝ := Real.log N
           C *
             ((μ₀ ^ 2 * μ₁) *
                Real.sqrt ((N * R * (β * logN)) / Mobs) *
                  ((N * R) / Mobs) ^ 2 +
              μ₀ ^ 2 * ((N * R) / Mobs) ^ 2 +
              Real.sqrt (β * logN) *
                  Real.rpow ((N * R) / Mobs) ((3 : ℝ) / 2) *
                    (μ₀ ^ 2 * R) +
              Real.rpow
                ((μ₀ * μ₁ * N * R * (β * logN)) / Mobs)
                ((3 : ℝ) / 2))) := by
  rcases quadratic_neumann_all_equal_base_spectral_norm_bound_min_dim with
    ⟨Cbase, hCbase_pos, hbase⟩
  refine ⟨max 1 Cbase, ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  intro C' _hC' β hβ n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 _hA1 _hmLower
  let C : ℝ := max 1 Cbase
  let p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
  let N : ℝ := ((max n₁ n₂ : ℕ) : ℝ)
  let R : ℝ := (r : ℝ)
  let Mobs : ℝ := (m : ℝ)
  let logN : ℝ := Real.log N
  let term₁ : ℝ :=
    (μ₀ ^ 2 * μ₁) * Real.sqrt ((N * R * (β * logN)) / Mobs) *
      ((N * R) / Mobs) ^ 2
  let term₂ : ℝ := μ₀ ^ 2 * ((N * R) / Mobs) ^ 2
  let term₃ : ℝ :=
    Real.sqrt (β * logN) *
      Real.rpow ((N * R) / Mobs) ((3 : ℝ) / 2) * (μ₀ ^ 2 * R)
  let term₄ : ℝ :=
    Real.rpow ((μ₀ * μ₁ * N * R * (β * logN)) / Mobs) ((3 : ℝ) / 2)
  let Φ : ℝ := term₁ + term₂ + term₃ + term₄
  have hC_nonneg : 0 ≤ C := by
    exact le_trans zero_le_one (le_max_left (1 : ℝ) Cbase)
  have hCbase_le_C : Cbase ≤ C := le_max_right (1 : ℝ) Cbase
  have hμ₀_nonneg : 0 ≤ μ₀ := le_trans zero_le_one hμ₀
  have hμ₁_nonneg : 0 ≤ μ₁ := le_trans zero_le_one hμ₁
  have hβ_nonneg : 0 ≤ β := by linarith
  have hN_nat : 0 < max n₁ n₂ :=
    lt_of_lt_of_le hn₁ (Nat.le_max_left n₁ n₂)
  have hN_pos : 0 < N := by
    dsimp [N]
    exact_mod_cast hN_nat
  have hN_one : 1 ≤ N := by
    dsimp [N]
    exact_mod_cast (Nat.succ_le_of_lt hN_nat)
  have hR_pos : 0 < R := by
    dsimp [R]
    exact_mod_cast hr
  have hlogN_nonneg : 0 ≤ logN := by
    dsimp [logN]
    exact Real.log_nonneg hN_one
  have hratio := sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm
  have hmean_rep :=
    quadratic_neumann_all_equal_mean_as_scaled_base_matrix S p
  have hbase_bound :=
    hbase n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hA0
  have hmean_bound :
      spectralNorm
          (quadraticNeumannAllEqualMeanContribution S
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
        Cbase * ((((((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) ^ 2) *
          ((μ₀ * (r : ℝ) / (↑(min n₁ n₂))) ^ 2))) := by
    simpa [p] using
      all_equal_mean_bound_from_min_dim_base S p Cbase μ₀
        hratio.1 hratio.2 hmean_rep hbase_bound
  by_cases hmzero : m = 0
  · subst m
    have hzero_bound :
        spectralNorm
            (quadraticNeumannAllEqualMeanContribution S
              ((0 : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤ 0 := by
      have hp0 : ((0 : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) = 0 := by simp
      rw [hp0, quadratic_neumann_all_equal_mean_as_scaled_base_matrix S 0]
      simpa using
        spectralNorm_smul_le_abs (0 : ℝ)
          (quadraticNeumannAllEqualBaseMatrix S)
    simpa [C, N, R, Mobs, logN] using hzero_bound
  · have hm_pos_nat : 0 < m := Nat.pos_of_ne_zero hmzero
    have hMobs_pos : 0 < Mobs := by
      dsimp [Mobs]
      exact_mod_cast hm_pos_nat
    have hscale_eq :
        (((((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) ^ 2) *
            ((μ₀ * (r : ℝ) / (↑(min n₁ n₂))) ^ 2)) =
          term₂ := by
      simpa [term₂, N, R, Mobs] using
        all_equal_mean_min_scale_eq_second_term
          (n₁ := n₁) (n₂ := n₂) (r := r) (m := m) hn₁ hn₂ hm_pos_nat μ₀
    have hterm₂_nonneg : 0 ≤ term₂ := by
      dsimp [term₂, N, R, Mobs]
      positivity
    have hCbase_scale_le :
        Cbase *
            (((((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) ^ 2) *
              ((μ₀ * (r : ℝ) / (↑(min n₁ n₂))) ^ 2)) ≤
          C * term₂ := by
      rw [hscale_eq]
      exact mul_le_mul_of_nonneg_right hCbase_le_C hterm₂_nonneg
    have hterm₁_nonneg : 0 ≤ term₁ := by
      dsimp [term₁, N, R, Mobs, logN]
      positivity
    have hterm₃_nonneg : 0 ≤ term₃ := by
      dsimp [term₃, N, R, Mobs, logN]
      positivity
    have hterm₄_nonneg : 0 ≤ term₄ := by
      dsimp [term₄, N, R, Mobs, logN]
      apply Real.rpow_nonneg
      positivity
    have hterm₂_le_Φ : term₂ ≤ Φ := by
      dsimp [Φ]
      nlinarith
    have hCterm₂_le : C * term₂ ≤ C * Φ := by
      exact mul_le_mul_of_nonneg_left hterm₂_le_Φ hC_nonneg
    calc
      spectralNorm
          (quadraticNeumannAllEqualMeanContribution S
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
          Cbase * ((((((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) ^ 2) *
            ((μ₀ * (r : ℝ) / (↑(min n₁ n₂))) ^ 2))) := hmean_bound
      _ ≤ C * term₂ := hCbase_scale_le
      _ ≤ C * Φ := hCterm₂_le
      _ =
          (let N : ℝ := ↑(max n₁ n₂)
           let R : ℝ := (r : ℝ)
           let Mobs : ℝ := (m : ℝ)
           let logN : ℝ := Real.log N
           C *
             ((μ₀ ^ 2 * μ₁) *
                Real.sqrt ((N * R * (β * logN)) / Mobs) *
                  ((N * R) / Mobs) ^ 2 +
              μ₀ ^ 2 * ((N * R) / Mobs) ^ 2 +
              Real.sqrt (β * logN) *
                  Real.rpow ((N * R) / Mobs) ((3 : ℝ) / 2) *
                    (μ₀ ^ 2 * R) +
              Real.rpow
                ((μ₀ * μ₁ * N * R * (β * logN)) / Mobs)
                ((3 : ℝ) / 2))) := by
          rfl
