-- Prove2me | solution 1 for linear_neumann_diagonal_centered_general_sample_threshold_from_min_dim_base_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-30T16:10:21.952584+00:00
-- url     : https://prove2.me/submissions/f1628ce0-2ef8-4e61-8479-50290f80e6ab

import Definitions.Def_matrix_completion_neumann
import Mathlib.Tactic

open MatrixCompletion

set_option maxHeartbeats 800000

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

private lemma sample_ratio_abs_two_prefactor_le_card_div_sample
    {n₁ n₂ m : ℕ} (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hm : m ≤ n₁ * n₂)
    (hm_pos : 0 < m) :
    abs ((((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹ *
        (1 - 2 * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))))) ≤
      ((n₁ : ℝ) * (n₂ : ℝ)) / (m : ℝ) := by
  let p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
  have hden_pos : 0 < (n₁ : ℝ) * (n₂ : ℝ) :=
    mul_pos (Nat.cast_pos.mpr hn₁) (Nat.cast_pos.mpr hn₂)
  have hm_pos_real : 0 < (m : ℝ) := Nat.cast_pos.mpr hm_pos
  have hp_pos : 0 < p := by
    dsimp [p]
    positivity
  have hp_nonneg : 0 ≤ p := le_of_lt hp_pos
  have hp_le_one : p ≤ 1 := by
    dsimp [p]
    rw [div_le_iff₀ hden_pos]
    have hm_real : (m : ℝ) ≤ (n₁ : ℝ) * (n₂ : ℝ) := by exact_mod_cast hm
    simpa using hm_real
  have h_abs_factor : |1 - 2 * p| ≤ 1 := by
    rw [abs_le]
    constructor <;> nlinarith
  have hp_inv_nonneg : 0 ≤ p⁻¹ := inv_nonneg.mpr hp_nonneg
  have hmain : |p⁻¹ * (1 - 2 * p)| ≤ p⁻¹ := by
    calc
      |p⁻¹ * (1 - 2 * p)|
          = p⁻¹ * |1 - 2 * p| := by
              rw [abs_mul, abs_of_nonneg hp_inv_nonneg]
      _ ≤ p⁻¹ * 1 := mul_le_mul_of_nonneg_left h_abs_factor hp_inv_nonneg
      _ = p⁻¹ := by ring
  have hp_inv_eq : p⁻¹ = ((n₁ : ℝ) * (n₂ : ℝ)) / (m : ℝ) := by
    dsimp [p]
    field_simp [hden_pos.ne', hm_pos_real.ne']
  simpa [p, hp_inv_eq] using hmain

private lemma centered_diagonal_scalar_absorption
    (Cfixed Cbase : ℝ) :
    0 < Cfixed → 0 < Cbase →
    ∃ Cthreshold : ℝ, 0 < Cthreshold ∧
      ∀ C' : ℝ, Cthreshold ≤ C' →
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (μ₀ μ₁ : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        (m : ℝ) ≥
          C' * max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
                  (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4))
            * (↑(max n₁ n₂)) * (r : ℝ) *
              (β * Real.log (↑(max n₁ n₂))) →
        abs ((((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹ *
            (1 - 2 * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))))) *
          (Cfixed * Real.sqrt
            ((β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂))) /
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
            (Cbase * μ₁ *
              Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                (μ₀ * (r : ℝ) / (↑(min n₁ n₂))))) ≤
          (1 : ℝ) / 32 := by
  intro hCfixed hCbase
  let Cthreshold : ℝ :=
    max 1 (((1024 : ℝ) * (Cfixed * Cbase) ^ 2) * ((Real.log (2 : ℝ)) ^ 2)⁻¹)
  refine ⟨Cthreshold, ?_, ?_⟩
  · have hlog2 : 0 < Real.log (2 : ℝ) :=
      Real.log_pos (by norm_num : (1 : ℝ) < 2)
    have hterm_nonneg :
        0 ≤ ((1024 : ℝ) * (Cfixed * Cbase) ^ 2) * ((Real.log (2 : ℝ)) ^ 2)⁻¹ := by
      positivity
    exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  intro C' hC' β hβ n₁ n₂ r m μ₀ μ₁ hn₁ hn₂ hr hm hμ₀ hμ₁ hmLower
  by_cases hm_zero : m = 0
  · subst m
    simp
  · have hm_pos_nat : 0 < m := Nat.pos_of_ne_zero hm_zero
    let N : ℝ := (max n₁ n₂ : ℕ)
    let d : ℝ := (min n₁ n₂ : ℕ)
    let nn : ℝ := (n₁ : ℝ) * (n₂ : ℝ)
    let L : ℝ := β * Real.log N
    let K : ℝ := max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
        (μ₀ * Real.rpow N ((1 : ℝ) / 4))
    let A : ℝ := Cfixed * Cbase
    let E : ℝ :=
      abs ((((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹ *
          (1 - 2 * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))))) *
        (Cfixed * Real.sqrt
          ((β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂))) /
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
          (Cbase * μ₁ *
            Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))))
    have hlog2_pos : 0 < Real.log (2 : ℝ) :=
      Real.log_pos (by norm_num : (1 : ℝ) < 2)
    have hC'_ge_one : (1 : ℝ) ≤ C' := le_trans (le_max_left _ _) hC'
    have hC'_pos : 0 < C' := lt_of_lt_of_le zero_lt_one hC'_ge_one
    have hA_pos : 0 < A := by
      dsimp [A]
      positivity
    have hA_nonneg : 0 ≤ A := le_of_lt hA_pos
    have hμ₀_nonneg : 0 ≤ μ₀ := le_trans zero_le_one hμ₀
    have hμ₁_nonneg : 0 ≤ μ₁ := le_trans zero_le_one hμ₁
    have hμ₀_pos : 0 < μ₀ := lt_of_lt_of_le zero_lt_one hμ₀
    have hμ₁_pos : 0 < μ₁ := lt_of_lt_of_le zero_lt_one hμ₁
    have hmin_nat : 0 < min n₁ n₂ := lt_min hn₁ hn₂
    have hN_nat : 0 < max n₁ n₂ :=
      lt_of_lt_of_le hn₁ (Nat.le_max_left n₁ n₂)
    have hN_pos : 0 < N := by
      dsimp [N]
      exact_mod_cast hN_nat
    have hN_ge_one : (1 : ℝ) ≤ N := by
      dsimp [N]
      exact_mod_cast (Nat.succ_le_of_lt hN_nat)
    have hd_pos : 0 < d := by
      dsimp [d]
      exact_mod_cast hmin_nat
    have hnn_pos : 0 < nn := by
      dsimp [nn]
      positivity
    have hm_pos : 0 < (m : ℝ) := by exact_mod_cast hm_pos_nat
    by_cases hN_one_nat : max n₁ n₂ = 1
    · have hn₁_one : n₁ = 1 := by omega
      have hn₂_one : n₂ = 1 := by omega
      have hm_le_one : m ≤ 1 := by
        have hprod_one : n₁ * n₂ = 1 := by rw [hn₁_one, hn₂_one]
        simpa [hprod_one] using hm
      have hm_one : m = 1 := by omega
      subst m
      simp [hn₁_one, hn₂_one]
    · have hN_ge_two_nat : 2 ≤ max n₁ n₂ := by omega
      have hN_ge_two : (2 : ℝ) ≤ N := by
        dsimp [N]
        exact_mod_cast hN_ge_two_nat
      have hlog_ge_log2 : Real.log (2 : ℝ) ≤ Real.log N :=
        Real.log_le_log (by norm_num : (0 : ℝ) < 2) hN_ge_two
      have hlogN_nonneg : 0 ≤ Real.log N :=
        le_trans (le_of_lt hlog2_pos) hlog_ge_log2
      have hβ_ge_one : (1 : ℝ) ≤ β := by linarith
      have hL_ge_log2 : Real.log (2 : ℝ) ≤ L := by
        have htmp : (1 : ℝ) * Real.log N ≤ β * Real.log N :=
          mul_le_mul_of_nonneg_right hβ_ge_one hlogN_nonneg
        exact le_trans hlog_ge_log2 (by simpa [L] using htmp)
      have hL_pos : 0 < L := lt_of_lt_of_le hlog2_pos hL_ge_log2
      have hK_ge_mu1sq : μ₁ ^ 2 ≤ K := by
        dsimp [K]
        exact le_trans (le_max_left _ _) (le_max_left _ _)
      have hK_nonneg : 0 ≤ K := le_trans (sq_nonneg μ₁) hK_ge_mu1sq
      have hK_pos : 0 < K :=
        lt_of_lt_of_le (by positivity : 0 < μ₁ ^ 2) hK_ge_mu1sq
      have hN_rpow_quarter_ge_one :
          (1 : ℝ) ≤ Real.rpow N ((1 : ℝ) / 4) := by
        have hpow := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hN_ge_one
          (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 4)
        simpa using hpow
      have hK_ge_mu0 : μ₀ ≤ K := by
        have hmu0_le : μ₀ ≤ μ₀ * Real.rpow N ((1 : ℝ) / 4) := by
          calc
            μ₀ = μ₀ * 1 := by ring
            _ ≤ μ₀ * Real.rpow N ((1 : ℝ) / 4) :=
              mul_le_mul_of_nonneg_left hN_rpow_quarter_ge_one hμ₀_nonneg
        exact le_trans hmu0_le (by dsimp [K]; exact le_max_right _ _)
      have hK3_ge :
          μ₀ ^ 2 * μ₁ ^ 2 ≤ K ^ 3 := by
        have h1 : μ₀ * μ₀ ≤ K * K :=
          mul_le_mul hK_ge_mu0 hK_ge_mu0 hμ₀_nonneg hK_nonneg
        have h2 : (μ₀ * μ₀) * (μ₁ ^ 2) ≤ (K * K) * K :=
          mul_le_mul h1 hK_ge_mu1sq (by positivity) (by positivity)
        nlinarith
      have hLower' : (m : ℝ) ≥ C' * K * N * (r : ℝ) * L := by
        simpa [K, N, L, mul_assoc] using hmLower
      have hr_pos : 0 < (r : ℝ) := by exact_mod_cast hr
      have hsample_pos : 0 < C' * K * N * (r : ℝ) * L := by positivity
      have hm_pos_from_sample : 0 < (m : ℝ) := lt_of_lt_of_le hsample_pos hLower'
      have hsample_cube :
          (C' * K * N * (r : ℝ) * L) ^ 3 ≤ (m : ℝ) ^ 3 := by
        exact pow_le_pow_left₀ (le_of_lt hsample_pos) hLower' 3
      have hpref := sample_ratio_abs_two_prefactor_le_card_div_sample
        hn₁ hn₂ hm hm_pos_nat
      have hnn_div_d : nn / d = N := by
        simpa [nn, d, N] using max_mul_min_cast_div (n₁ := n₁) (n₂ := n₂) hmin_nat
      have harg1_nonneg :
          0 ≤ (β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂))) /
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) := by
        positivity
      have harg2_nonneg :
          0 ≤ (r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) := by
        positivity
      have hE_nonneg : 0 ≤ E := by
        dsimp [E]
        positivity
      have hraw_sq_le :
          E ^ 2 ≤
            (A ^ 2) * (μ₀ ^ 2 * μ₁ ^ 2 * N ^ 3 * (r : ℝ) ^ 3 * L) /
              ((m : ℝ) ^ 3) := by
        dsimp [E, A, L, N, nn, d] at *
        have hsqrt_sq₁ :
            (Real.sqrt
              ((β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))) ^ 2 =
              ((β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) := by
          rw [Real.sq_sqrt harg1_nonneg]
        have hsqrt_sq₂ :
            (Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ^ 2 =
              ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) := by
          rw [Real.sq_sqrt harg2_nonneg]
        have hleft_bound_sq :
            abs ((((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹ *
                (1 - 2 * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))))) ^ 2 ≤
              (((n₁ : ℝ) * (n₂ : ℝ)) / (m : ℝ)) ^ 2 := by
          exact pow_le_pow_left₀ (abs_nonneg _) hpref 2
        have hnonneg_rest :
            0 ≤
              (Cfixed *
                  Real.sqrt
                    ((β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂))) /
                      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                (Cbase * μ₁ *
                    Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                  (μ₀ * (r : ℝ) / (↑(min n₁ n₂))))) ^ 2 := by
          positivity
        calc
          E ^ 2
              ≤ ((((n₁ : ℝ) * (n₂ : ℝ)) / (m : ℝ)) ^ 2) *
                  (Cfixed *
                      Real.sqrt
                        ((β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂))) /
                          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                    (Cbase * μ₁ *
                        Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                      (μ₀ * (r : ℝ) / (↑(min n₁ n₂))))) ^ 2 := by
                dsimp [E]
                rw [mul_pow]
                exact mul_le_mul_of_nonneg_right hleft_bound_sq hnonneg_rest
          _ =
              (A ^ 2) * (μ₀ ^ 2 * μ₁ ^ 2 * ((↑(max n₁ n₂) : ℝ) ^ 3) *
                  (r : ℝ) ^ 3 * (β * Real.log (↑(max n₁ n₂)))) /
                ((m : ℝ) ^ 3) := by
                rw [mul_pow, mul_pow, mul_pow, mul_pow, hsqrt_sq₁, hsqrt_sq₂]
                have hprod :
                    (n₁ : ℝ) * (n₂ : ℝ) =
                      ((max n₁ n₂ : ℕ) : ℝ) * ((min n₁ n₂ : ℕ) : ℝ) := by
                  have hprod_nat : max n₁ n₂ * min n₁ n₂ = n₁ * n₂ :=
                    max_mul_min n₁ n₂
                  exact_mod_cast hprod_nat.symm
                field_simp [hm_pos.ne', hnn_pos.ne',
                  (show ((min n₁ n₂ : ℕ) : ℝ) ≠ 0 by exact ne_of_gt hd_pos)]
                have hprod_sq :
                    (n₁ : ℝ) ^ 2 * (n₂ : ℝ) ^ 2 =
                      ((max n₁ n₂ : ℕ) : ℝ) ^ 2 *
                        ((min n₁ n₂ : ℕ) : ℝ) ^ 2 := by
                  calc
                    (n₁ : ℝ) ^ 2 * (n₂ : ℝ) ^ 2
                        = ((n₁ : ℝ) * (n₂ : ℝ)) ^ 2 := by ring
                    _ = (((max n₁ n₂ : ℕ) : ℝ) *
                          ((min n₁ n₂ : ℕ) : ℝ)) ^ 2 := by rw [hprod]
                    _ = ((max n₁ n₂ : ℕ) : ℝ) ^ 2 *
                          ((min n₁ n₂ : ℕ) : ℝ) ^ 2 := by ring
                rw [hprod_sq]
                dsimp [A]
                ring
      have hmain_sq :
          E ^ 2 ≤ (1 / 32 : ℝ) ^ 2 := by
        have hden_pos : 0 < (m : ℝ) ^ 3 := by positivity
        have htarget_numer :
            (A ^ 2) * (μ₀ ^ 2 * μ₁ ^ 2 * N ^ 3 * (r : ℝ) ^ 3 * L) ≤
              ((m : ℝ) ^ 3) * ((1 / 32 : ℝ) ^ 2) := by
          have hC_bound :
              A ^ 2 ≤ C' * (Real.log (2 : ℝ)) ^ 2 / 1024 := by
            have hCt :
                ((1024 : ℝ) * A ^ 2) * ((Real.log (2 : ℝ)) ^ 2)⁻¹ ≤ C' := by
              exact le_trans (le_max_right (1 : ℝ)
                (((1024 : ℝ) * (Cfixed * Cbase) ^ 2) *
                  ((Real.log (2 : ℝ)) ^ 2)⁻¹)) hC'
            have hlog_ne : Real.log (2 : ℝ) ≠ 0 := ne_of_gt hlog2_pos
            have hlog_sq_pos : 0 < (Real.log (2 : ℝ)) ^ 2 :=
              sq_pos_of_ne_zero hlog_ne
            have hCt_mul :
                ((1024 : ℝ) * A ^ 2) ≤ C' * (Real.log (2 : ℝ)) ^ 2 := by
              have hmul := mul_le_mul_of_nonneg_right hCt (le_of_lt hlog_sq_pos)
              field_simp [hlog_ne] at hmul
              simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
            rw [div_eq_mul_inv]
            norm_num
            nlinarith [hCt_mul]
          have hL_sq_ge : (Real.log (2 : ℝ)) ^ 2 ≤ L ^ 2 := by
            exact (sq_le_sq₀ (le_of_lt hlog2_pos) (le_of_lt hL_pos)).mpr hL_ge_log2
          have hsample_cube_expanded :
              C' ^ 3 * K ^ 3 * N ^ 3 * (r : ℝ) ^ 3 * L ^ 3 ≤ (m : ℝ) ^ 3 := by
            calc
              C' ^ 3 * K ^ 3 * N ^ 3 * (r : ℝ) ^ 3 * L ^ 3
                  = (C' * K * N * (r : ℝ) * L) ^ 3 := by ring
              _ ≤ (m : ℝ) ^ 3 := hsample_cube
          have hcoeff :
              A ^ 2 * (μ₀ ^ 2 * μ₁ ^ 2 * N ^ 3 * (r : ℝ) ^ 3 * L) ≤
                (C' ^ 3 * K ^ 3 * N ^ 3 * (r : ℝ) ^ 3 * L ^ 3) *
                  ((1 / 32 : ℝ) ^ 2) := by
            have hA_to_C :
                A ^ 2 * 1024 ≤ C' * (Real.log (2 : ℝ)) ^ 2 := by
              nlinarith [hC_bound]
            have hK3L2 :
                μ₀ ^ 2 * μ₁ ^ 2 * (Real.log (2 : ℝ)) ^ 2 ≤ K ^ 3 * L ^ 2 := by
              have hmul := mul_le_mul hK3_ge hL_sq_ge (by positivity) (by positivity)
              nlinarith [hmul]
            have hCprime : C' ≤ C' ^ 3 := by
              have hsq : (1 : ℝ) ≤ C' ^ 2 := by nlinarith [hC'_ge_one]
              calc
                C' = C' * 1 := by ring
                _ ≤ C' * C' ^ 2 := mul_le_mul_of_nonneg_left hsq (le_of_lt hC'_pos)
                _ = C' ^ 3 := by ring
            have hnonneg_geom : 0 ≤ N ^ 3 * (r : ℝ) ^ 3 * L := by positivity
            have hbig :
                A ^ 2 * (μ₀ ^ 2 * μ₁ ^ 2 * L) ≤
                  (C' ^ 3 * K ^ 3 * L ^ 3) / 1024 := by
              have hleft :
                  A ^ 2 * (μ₀ ^ 2 * μ₁ ^ 2 * L) * 1024 ≤
                    C' ^ 3 * K ^ 3 * L ^ 3 := by
                calc
                  A ^ 2 * (μ₀ ^ 2 * μ₁ ^ 2 * L) * 1024
                      = (A ^ 2 * 1024) * (μ₀ ^ 2 * μ₁ ^ 2) * L := by ring
                  _ ≤ (C' * (Real.log (2 : ℝ)) ^ 2) *
                        (μ₀ ^ 2 * μ₁ ^ 2) * L := by
                        gcongr
                  _ = C' * (μ₀ ^ 2 * μ₁ ^ 2 * (Real.log (2 : ℝ)) ^ 2) * L := by ring
                  _ ≤ C' * (K ^ 3 * L ^ 2) * L := by
                        gcongr
                  _ = C' * K ^ 3 * L ^ 3 := by ring
                  _ ≤ C' ^ 3 * K ^ 3 * L ^ 3 := by
                        gcongr
              have h1024 : (0 : ℝ) < 1024 := by norm_num
              rw [le_div_iff₀ h1024]
              simpa [mul_assoc, mul_left_comm, mul_comm] using hleft
            calc
              A ^ 2 * (μ₀ ^ 2 * μ₁ ^ 2 * N ^ 3 * (r : ℝ) ^ 3 * L)
                  = (A ^ 2 * (μ₀ ^ 2 * μ₁ ^ 2 * L)) *
                      (N ^ 3 * (r : ℝ) ^ 3) := by ring
              _ ≤ ((C' ^ 3 * K ^ 3 * L ^ 3) / 1024) *
                    (N ^ 3 * (r : ℝ) ^ 3) := by
                    gcongr
              _ = (C' ^ 3 * K ^ 3 * N ^ 3 * (r : ℝ) ^ 3 * L ^ 3) *
                    ((1 / 32 : ℝ) ^ 2) := by norm_num; ring
          exact le_trans hcoeff (by
            exact mul_le_mul_of_nonneg_right hsample_cube_expanded (by norm_num))
        have hfrac :
            (A ^ 2) * (μ₀ ^ 2 * μ₁ ^ 2 * N ^ 3 * (r : ℝ) ^ 3 * L) /
                ((m : ℝ) ^ 3) ≤
              (1 / 32 : ℝ) ^ 2 := by
          rw [div_le_iff₀ hden_pos]
          simpa [mul_comm, mul_left_comm, mul_assoc] using htarget_numer
        exact le_trans hraw_sq_le hfrac
      simpa [E] using
        (sq_le_sq₀ hE_nonneg (by norm_num : (0 : ℝ) ≤ (1 / 32 : ℝ))).mp hmain_sq

theorem solution
    (Cfixed Cbase : ℝ) :
    0 < Cfixed → 0 < Cbase →
    ∃ Cthreshold : ℝ, 0 < Cthreshold ∧
      ∀ C' : ℝ, Cthreshold ≤ C' →
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          C' * max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
                  (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4))
            * (↑(max n₁ n₂)) * (r : ℝ) *
              (β * Real.log (↑(max n₁ n₂))) →
        ∀ Omega : Finset (Fin n₁ × Fin n₂),
        linearNeumannDiagonalCenteredContribution Omega S
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) =
          (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹ *
              (1 - 2 * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))) •
            centeredSamplingFluctuation Omega
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (linearNeumannDiagonalBaseMatrix S) →
        entrySupNorm (linearNeumannDiagonalBaseMatrix S) ≤
          Cbase * μ₁ *
            Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) →
        CenteredSamplingSpectralBound Omega
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (linearNeumannDiagonalBaseMatrix S)
            (Cfixed * Real.sqrt
              ((β * (↑(max n₁ n₂)) *
                  Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              entrySupNorm (linearNeumannDiagonalBaseMatrix S)) →
        spectralNorm
            (linearNeumannDiagonalCenteredContribution Omega S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
          (1 : ℝ) / 32 := by
  intro hCfixed hCbase
  rcases centered_diagonal_scalar_absorption Cfixed Cbase hCfixed hCbase with
    ⟨Cthreshold, hCthreshold, hScalar⟩
  refine ⟨Cthreshold, hCthreshold, ?_⟩
  intro C' hC' β hβ n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ hr hm hμ₀ hμ₁ _hA0 _hA1 hmLower
    Omega hRep hBase hCentered
  let p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
  let a : ℝ := p⁻¹ * (1 - 2 * p)
  let B : Matrix (Fin n₁) (Fin n₂) ℝ := linearNeumannDiagonalBaseMatrix S
  have hEvent :
      spectralNorm (centeredSamplingFluctuation Omega p B) ≤
        Cfixed * Real.sqrt
          ((β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂))) / p) *
          entrySupNorm B := by
    simpa [CenteredSamplingSpectralBound, p, B] using hCentered
  have hcoef_nonneg :
      0 ≤ |a| * (Cfixed * Real.sqrt
          ((β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂))) / p)) := by
    positivity
  have hnorm :
      spectralNorm (linearNeumannDiagonalCenteredContribution Omega S p) ≤
        |a| *
          (Cfixed * Real.sqrt
            ((β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂))) / p) *
            entrySupNorm B) := by
    rw [hRep]
    exact le_trans
      (spectralNorm_smul_le_abs a (centeredSamplingFluctuation Omega p B))
      (mul_le_mul_of_nonneg_left hEvent (abs_nonneg a))
  have hentry_step :
      |a| *
          (Cfixed * Real.sqrt
            ((β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂))) / p) *
            entrySupNorm B) ≤
        |a| *
          (Cfixed * Real.sqrt
            ((β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂))) / p) *
            (Cbase * μ₁ *
              Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                (μ₀ * (r : ℝ) / (↑(min n₁ n₂))))) := by
    have hcoef :
        0 ≤ |a| *
          (Cfixed * Real.sqrt
            ((β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂))) / p)) := by
      positivity
    nlinarith [mul_le_mul_of_nonneg_left hBase hcoef]
  have hscalar := hScalar C' hC' β hβ n₁ n₂ r m μ₀ μ₁
    hn₁ hn₂ hr hm hμ₀ hμ₁ hmLower
  exact le_trans hnorm (le_trans hentry_step (by simpa [p, a, B, mul_assoc] using hscalar))
