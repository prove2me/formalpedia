-- Prove2me | solution 1 for quadratic_neumann_first_index_distinct_centered_decoupled_threshold_from_tight_coefficient_scale
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-07-04T13:21:03.505901+00:00
-- url     : https://prove2.me/submissions/3244c911-f8af-4964-8ffe-67fb0ad88e5c

import Definitions.Def_matrix_completion_tangent
import Mathlib.Analysis.Complex.ExponentialBounds

open MatrixCompletion

/-- Deterministic threshold absorption for the centered `ω₁ ≠ ω₂ = ω₃`
decoupled quadratic term: the outer prefactor `p⁻¹(1-2p)`, the Theorem 6.3
spectral factor `√(βn log n / p)`, and the tight Lemma 6.7 coefficient scale
(with `μ₁ = μ₀√r`) absorb into `Cthreshold · λ^{-3/2}` under the quadratic
Neumann sample bound `m ≥ λ μ₀^{4/3} n r^{4/3} β log n`. -/
theorem solution
    (Cfixed Ccoef : ℝ) :
    0 < Cfixed → 0 < Ccoef →
    ∃ Cthreshold : ℝ, 0 < Cthreshold ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (μ₀ : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ →
        (m : ℝ) ≥
          lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
            (↑(max n₁ n₂)) * Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
              (β * Real.log (↑(max n₁ n₂))) →
        ∀ (Omega : Finset (Fin n₁ × Fin n₂))
          (B Y : Matrix (Fin n₁) (Fin n₂) ℝ),
        Y =
          (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹ *
              (1 - 2 * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))) •
            centeredSamplingFluctuation Omega
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) B →
        entrySupNorm B ≤
          Ccoef *
            (Real.sqrt
                (((β + 2) * Real.log (↑(max n₁ n₂))) /
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                (μ₀ * Real.sqrt (r : ℝ) *
                  Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                    Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) *
                      (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))) +
              (((β + 2) * Real.log (↑(max n₁ n₂))) /
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                (μ₀ * Real.sqrt (r : ℝ) *
                  Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                    (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) *
                      (μ₀ * (r : ℝ) / (↑(min n₁ n₂))))) →
        CenteredSamplingSpectralBound Omega
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) B
            (Cfixed * Real.sqrt
              ((β * (↑(max n₁ n₂)) *
                  Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              entrySupNorm B) →
        spectralNorm Y ≤
          Cthreshold * Real.rpow lam (-((3 : ℝ) / 2)) := by
  intro hCf hCc
  -- small-context scalar helpers
  have one_le_mul' : ∀ {a b : ℝ}, 1 ≤ a → 1 ≤ b → 1 ≤ a * b := by
    intro a b ha hb
    calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
      _ ≤ a * b := mul_le_mul ha hb zero_le_one (le_trans zero_le_one ha)
  -- x³ ≤ U²·√U for U = x^{4/3}, 1 ≤ x
  have rpow43_cube : ∀ x : ℝ, 0 < x → 1 ≤ x →
      x ^ 3 ≤ (Real.rpow x ((4 : ℝ) / 3)) ^ 2 *
        Real.sqrt (Real.rpow x ((4 : ℝ) / 3)) := by
    intro x hx0 hx1
    have hnot : Real.rpow x ((4 : ℝ) / 3) = x ^ ((4 : ℝ) / 3) := rfl
    rw [hnot]
    have h2 : (x ^ ((4 : ℝ) / 3)) ^ (2 : ℕ) = x ^ ((8 : ℝ) / 3) := by
      rw [← Real.rpow_natCast (x ^ ((4 : ℝ) / 3)) 2,
        ← Real.rpow_mul (le_of_lt hx0)]
      norm_num
    have hs : Real.sqrt (x ^ ((4 : ℝ) / 3)) = x ^ ((2 : ℝ) / 3) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (le_of_lt hx0)]
      norm_num
    have hc : x ^ (3 : ℕ) = x ^ ((3 : ℝ)) := by
      rw [← Real.rpow_natCast x 3]; norm_num
    rw [h2, hs, hc, ← Real.rpow_add hx0]
    apply Real.rpow_le_rpow_of_exponent_le hx1
    norm_num
  -- x²·√x ≤ U² for U = x^{4/3}, 1 ≤ x  (i.e. x^{5/2} ≤ x^{8/3})
  have rpow43_sq : ∀ x : ℝ, 0 < x → 1 ≤ x →
      x ^ 2 * Real.sqrt x ≤ (Real.rpow x ((4 : ℝ) / 3)) ^ 2 := by
    intro x hx0 hx1
    have hnot : Real.rpow x ((4 : ℝ) / 3) = x ^ ((4 : ℝ) / 3) := rfl
    rw [hnot]
    have h2 : (x ^ ((4 : ℝ) / 3)) ^ (2 : ℕ) = x ^ ((8 : ℝ) / 3) := by
      rw [← Real.rpow_natCast (x ^ ((4 : ℝ) / 3)) 2,
        ← Real.rpow_mul (le_of_lt hx0)]
      norm_num
    have hs : Real.sqrt x = x ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow x
    have hc : x ^ (2 : ℕ) = x ^ ((2 : ℝ)) := by
      rw [← Real.rpow_natCast x 2]; norm_num
    rw [h2, hs, hc, ← Real.rpow_add hx0]
    apply Real.rpow_le_rpow_of_exponent_le hx1
    norm_num
  refine ⟨4 * (Cfixed * Ccoef), by positivity, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m μ₀ hn₁ hn₂ hr hm hμ₀ hsample Omega B Y hY hB hcsf
  have hlam0 : (0 : ℝ) < lam := lt_of_lt_of_le one_pos hlam
  have hn₁R : (0 : ℝ) < (n₁ : ℝ) := by exact_mod_cast hn₁
  have hn₂R : (0 : ℝ) < (n₂ : ℝ) := by exact_mod_cast hn₂
  have hμ₀0 : (0 : ℝ) < μ₀ := lt_of_lt_of_le one_pos hμ₀
  have hrR1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hrR0 : (0 : ℝ) < (r : ℝ) := lt_of_lt_of_le one_pos hrR1
  set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp_def
  -- spectral norm of a scalar multiple
  have hsmul : ∀ (c : ℝ) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
      spectralNorm (c • X) = |c| * spectralNorm X := by
    intro c X
    unfold spectralNorm
    rw [map_smul, map_smul, norm_smul, Real.norm_eq_abs]
  have hcsf_nonneg : 0 ≤ spectralNorm (centeredSamplingFluctuation Omega p B) := by
    unfold spectralNorm; exact norm_nonneg _
  have hYnorm : spectralNorm Y =
      |p⁻¹ * (1 - 2 * p)| *
        spectralNorm (centeredSamplingFluctuation Omega p B) := by
    rw [hY, hsmul]
  unfold CenteredSamplingSpectralBound at hcsf
  by_cases hmax1 : max n₁ n₂ = 1
  · -- degenerate case: n₁ = n₂ = 1, log term vanishes
    have hlog0 : Real.log (↑(max n₁ n₂) : ℝ) = 0 := by
      rw [hmax1]; simp
    have hbound0 : Cfixed * Real.sqrt
        ((β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂))) / p) *
        entrySupNorm B = 0 := by
      rw [hlog0]
      simp
    have hzero : spectralNorm (centeredSamplingFluctuation Omega p B) = 0 := by
      rw [hbound0] at hcsf
      exact le_antisymm hcsf hcsf_nonneg
    rw [hYnorm, hzero, mul_zero]
    exact le_of_lt (mul_pos (by positivity)
      (Real.rpow_pos_of_pos hlam0 (-((3 : ℝ) / 2))))
  · -- main case: max n₁ n₂ ≥ 2
    have hmax_ge1 : 1 ≤ max n₁ n₂ := le_max_of_le_left hn₁
    have hmax2 : 2 ≤ max n₁ n₂ := by omega
    have hnR2 : (2 : ℝ) ≤ (↑(max n₁ n₂) : ℝ) := by exact_mod_cast hmax2
    have hmn_pos : 0 < min n₁ n₂ := lt_min hn₁ hn₂
    have hmnR0' : (0 : ℝ) < (↑(min n₁ n₂) : ℝ) := by exact_mod_cast hmn_pos
    set nR : ℝ := (↑(max n₁ n₂) : ℝ) with hnR_def
    set mnR : ℝ := (↑(min n₁ n₂) : ℝ) with hmnR_def
    have hnR0 : (0 : ℝ) < nR := lt_of_lt_of_le two_pos hnR2
    have hmnR0 : (0 : ℝ) < mnR := hmnR0'
    -- log 2 > 1/2 via exp(1/2) < 2
    have hexp_half : Real.exp ((1 : ℝ) / 2) < 2 := by
      have hsq : Real.exp ((1 : ℝ) / 2) * Real.exp ((1 : ℝ) / 2) = Real.exp 1 := by
        rw [← Real.exp_add]; norm_num
      nlinarith [Real.exp_one_lt_d9, Real.exp_pos ((1 : ℝ) / 2)]
    have hlog2 : (1 : ℝ) / 2 < Real.log 2 :=
      (Real.lt_log_iff_exp_lt two_pos).mpr hexp_half
    have hloglog : Real.log 2 ≤ Real.log nR := Real.log_le_log two_pos hnR2
    have hlognR : (1 : ℝ) / 2 < Real.log nR := lt_of_lt_of_le hlog2 hloglog
    have hlognR0 : (0 : ℝ) < Real.log nR := by linarith
    -- opaque abbreviations
    obtain ⟨L, hL_def⟩ : ∃ x : ℝ, x = β * Real.log nR := ⟨_, rfl⟩
    obtain ⟨L₂, hL₂_def⟩ : ∃ x : ℝ, x = (β + 2) * Real.log nR := ⟨_, rfl⟩
    obtain ⟨U, hU_def⟩ : ∃ x : ℝ, x = Real.rpow μ₀ ((4 : ℝ) / 3) := ⟨_, rfl⟩
    obtain ⟨V, hV_def⟩ : ∃ x : ℝ, x = Real.rpow (r : ℝ) ((4 : ℝ) / 3) := ⟨_, rfl⟩
    rw [← hU_def, ← hV_def, ← hL_def] at hsample
    have hL1 : (1 : ℝ) ≤ L := by
      rw [hL_def]
      calc (1 : ℝ) = 2 * (1 / 2) := by norm_num
        _ ≤ β * Real.log nR :=
            mul_le_mul (le_of_lt hβ) (le_of_lt hlognR) (by norm_num)
              (le_trans (by norm_num) (le_of_lt hβ))
    have hL0 : (0 : ℝ) < L := lt_of_lt_of_le one_pos hL1
    have hL₂0 : (0 : ℝ) < L₂ := by
      rw [hL₂_def]
      exact mul_pos (by linarith) hlognR0
    have hL₂le : L₂ ≤ 2 * L := by
      rw [hL₂_def, hL_def]
      have hb2 : β + 2 ≤ 2 * β := by linarith
      calc (β + 2) * Real.log nR ≤ (2 * β) * Real.log nR :=
            mul_le_mul_of_nonneg_right hb2 (le_of_lt hlognR0)
        _ = 2 * (β * Real.log nR) := by ring
    have hU1 : (1 : ℝ) ≤ U := by
      rw [hU_def]
      calc (1 : ℝ) = Real.rpow μ₀ 0 := (Real.rpow_zero μ₀).symm
        _ ≤ Real.rpow μ₀ ((4 : ℝ) / 3) :=
            Real.rpow_le_rpow_of_exponent_le hμ₀ (by norm_num)
    have hV1 : (1 : ℝ) ≤ V := by
      rw [hV_def]
      calc (1 : ℝ) = Real.rpow (r : ℝ) 0 := (Real.rpow_zero _).symm
        _ ≤ Real.rpow (r : ℝ) ((4 : ℝ) / 3) :=
            Real.rpow_le_rpow_of_exponent_le hrR1 (by norm_num)
    have hU0 : (0 : ℝ) < U := lt_of_lt_of_le one_pos hU1
    have hV0 : (0 : ℝ) < V := lt_of_lt_of_le one_pos hV1
    obtain ⟨K, hK_def⟩ : ∃ x : ℝ, x = lam * U * V * L := ⟨_, rfl⟩
    have hK1 : (1 : ℝ) ≤ K := by
      rw [hK_def]
      exact one_le_mul' (one_le_mul' (one_le_mul' hlam hU1) hV1) hL1
    have hK0 : (0 : ℝ) < K := lt_of_lt_of_le one_pos hK1
    -- m > 0, p ∈ (0, 1]
    have hm_pos : (0 : ℝ) < (m : ℝ) := by
      refine lt_of_lt_of_le ?_ hsample
      exact mul_pos (mul_pos (mul_pos (mul_pos hlam0 hU0) hnR0) hV0) hL0
    have hp_pos : 0 < p := div_pos hm_pos (mul_pos hn₁R hn₂R)
    have hp_le1 : p ≤ 1 := by
      rw [hp_def, div_le_one (mul_pos hn₁R hn₂R)]
      calc (m : ℝ) ≤ ((n₁ * n₂ : ℕ) : ℝ) := by exact_mod_cast hm
        _ = (n₁ : ℝ) * (n₂ : ℝ) := by push_cast; ring
    -- product of max and min casts
    have hmaxmin : nR * mnR = (n₁ : ℝ) * (n₂ : ℝ) := by
      rw [hnR_def, hmnR_def]
      rcases le_total n₁ n₂ with h | h
      · rw [max_eq_right h, min_eq_left h]; try ring
      · rw [max_eq_left h, min_eq_right h]; try ring
    -- lower bound on p
    have hp_low : K / mnR ≤ p := by
      rw [div_le_iff₀ hmnR0, hp_def, div_mul_eq_mul_div,
        le_div_iff₀ (mul_pos hn₁R hn₂R)]
      calc K * ((n₁ : ℝ) * (n₂ : ℝ)) = K * (nR * mnR) := by rw [hmaxmin]
        _ = (lam * U * nR * V * L) * mnR := by rw [hK_def]; ring
        _ ≤ (m : ℝ) * mnR := mul_le_mul_of_nonneg_right hsample (le_of_lt hmnR0)
    obtain ⟨A, hA_def⟩ : ∃ x : ℝ, x = p⁻¹ := ⟨_, rfl⟩
    obtain ⟨D, hD_def⟩ : ∃ x : ℝ, x = mnR / K := ⟨_, rfl⟩
    have hA0 : (0 : ℝ) < A := by rw [hA_def]; exact inv_pos.mpr hp_pos
    have hD0 : (0 : ℝ) < D := by rw [hD_def]; exact div_pos hmnR0 hK0
    have hA_le_D : A ≤ D := by
      have hKm : (0 : ℝ) < K / mnR := div_pos hK0 hmnR0
      have h1d := one_div_le_one_div_of_le hKm hp_low
      rw [hA_def, hD_def]
      calc p⁻¹ = 1 / p := (one_div p).symm
        _ ≤ 1 / (K / mnR) := h1d
        _ = mnR / K := by rw [one_div_div]
    -- prefactor: |p⁻¹(1-2p)| ≤ A
    have hpinv_pos : (0 : ℝ) < p⁻¹ := inv_pos.mpr hp_pos
    have habs : |1 - 2 * p| ≤ 1 :=
      abs_le.mpr ⟨by linarith, by linarith [le_of_lt hp_pos]⟩
    have hpref : |p⁻¹ * (1 - 2 * p)| ≤ A := by
      rw [abs_mul, abs_of_pos hpinv_pos]
      calc p⁻¹ * |1 - 2 * p| ≤ p⁻¹ * 1 :=
            mul_le_mul_of_nonneg_left habs (le_of_lt hpinv_pos)
        _ = A := by rw [hA_def, mul_one]
    -- rewrite the sqrt arguments
    have hsqrt_arg : (β * nR * Real.log nR) / p = L * nR * A := by
      rw [hL_def, hA_def, div_eq_mul_inv]; ring
    have hL₂A : ((β + 2) * Real.log nR) / p = L₂ * A := by
      rw [hL₂_def, hA_def, div_eq_mul_inv]
    rw [hsqrt_arg] at hcsf
    rw [hL₂A] at hB
    -- square-root opaque variables
    obtain ⟨sA, hsA_def⟩ : ∃ x : ℝ, x = Real.sqrt A := ⟨_, rfl⟩
    obtain ⟨sD, hsD_def⟩ : ∃ x : ℝ, x = Real.sqrt D := ⟨_, rfl⟩
    obtain ⟨sL, hsL_def⟩ : ∃ x : ℝ, x = Real.sqrt L := ⟨_, rfl⟩
    obtain ⟨sL₂, hsL₂_def⟩ : ∃ x : ℝ, x = Real.sqrt L₂ := ⟨_, rfl⟩
    obtain ⟨sU, hsU_def⟩ : ∃ x : ℝ, x = Real.sqrt U := ⟨_, rfl⟩
    obtain ⟨sV, hsV_def⟩ : ∃ x : ℝ, x = Real.sqrt V := ⟨_, rfl⟩
    obtain ⟨sK, hsK_def⟩ : ∃ x : ℝ, x = Real.sqrt K := ⟨_, rfl⟩
    obtain ⟨slam, hslam_def⟩ : ∃ x : ℝ, x = Real.sqrt lam := ⟨_, rfl⟩
    obtain ⟨smu, hsmu_def⟩ : ∃ x : ℝ, x = Real.sqrt μ₀ := ⟨_, rfl⟩
    obtain ⟨srr, hsrr_def⟩ : ∃ x : ℝ, x = Real.sqrt (r : ℝ) := ⟨_, rfl⟩
    obtain ⟨snR, hsnR_def⟩ : ∃ x : ℝ, x = Real.sqrt nR := ⟨_, rfl⟩
    obtain ⟨smn, hsmn_def⟩ : ∃ x : ℝ, x = Real.sqrt mnR := ⟨_, rfl⟩
    have hsA0 : (0 : ℝ) < sA := by
      rw [hsA_def]; exact Real.sqrt_pos.mpr hA0
    have hsD0 : (0 : ℝ) < sD := by
      rw [hsD_def]; exact Real.sqrt_pos.mpr hD0
    have hsL0 : (0 : ℝ) < sL := by
      rw [hsL_def]; exact Real.sqrt_pos.mpr hL0
    have hsL₂0 : (0 : ℝ) < sL₂ := by
      rw [hsL₂_def]; exact Real.sqrt_pos.mpr hL₂0
    have hsU0 : (0 : ℝ) < sU := by
      rw [hsU_def]; exact Real.sqrt_pos.mpr hU0
    have hsV0 : (0 : ℝ) < sV := by
      rw [hsV_def]; exact Real.sqrt_pos.mpr hV0
    have hsK0 : (0 : ℝ) < sK := by
      rw [hsK_def]; exact Real.sqrt_pos.mpr hK0
    have hslam0 : (0 : ℝ) < slam := by
      rw [hslam_def]; exact Real.sqrt_pos.mpr hlam0
    have hsmu0 : (0 : ℝ) < smu := by
      rw [hsmu_def]; exact Real.sqrt_pos.mpr hμ₀0
    have hsrr0 : (0 : ℝ) < srr := by
      rw [hsrr_def]; exact Real.sqrt_pos.mpr hrR0
    have hsnR0 : (0 : ℝ) < snR := by
      rw [hsnR_def]; exact Real.sqrt_pos.mpr hnR0
    have hsmn0 : (0 : ℝ) < smn := by
      rw [hsmn_def]; exact Real.sqrt_pos.mpr hmnR0
    have hsA_sq : sA ^ 2 = A := by
      rw [hsA_def]; exact Real.sq_sqrt (le_of_lt hA0)
    have hsL_sq : sL ^ 2 = L := by
      rw [hsL_def]; exact Real.sq_sqrt (le_of_lt hL0)
    have hsL₂_sq : sL₂ ^ 2 = L₂ := by
      rw [hsL₂_def]; exact Real.sq_sqrt (le_of_lt hL₂0)
    have hsU_sq : sU ^ 2 = U := by
      rw [hsU_def]; exact Real.sq_sqrt (le_of_lt hU0)
    have hsV_sq : sV ^ 2 = V := by
      rw [hsV_def]; exact Real.sq_sqrt (le_of_lt hV0)
    have hsK_sq : sK ^ 2 = K := by
      rw [hsK_def]; exact Real.sq_sqrt (le_of_lt hK0)
    have hslam_sq : slam ^ 2 = lam := by
      rw [hslam_def]; exact Real.sq_sqrt (le_of_lt hlam0)
    have hsmu_sq : smu ^ 2 = μ₀ := by
      rw [hsmu_def]; exact Real.sq_sqrt (le_of_lt hμ₀0)
    have hsrr_sq : srr ^ 2 = (r : ℝ) := by
      rw [hsrr_def]; exact Real.sq_sqrt (le_of_lt hrR0)
    have hsmn_sq : smn ^ 2 = mnR := by
      rw [hsmn_def]; exact Real.sq_sqrt (le_of_lt hmnR0)
    -- one ≤ facts for the sqrt variables that need them
    have hsL1 : (1 : ℝ) ≤ sL := by
      rw [hsL_def]; exact Real.one_le_sqrt.mpr hL1
    have hslam1 : (1 : ℝ) ≤ slam := by
      rw [hslam_def]; exact Real.one_le_sqrt.mpr hlam
    -- splitting the composite square roots
    have hsqrtLNA : Real.sqrt (L * nR * A) = sL * snR * sA := by
      rw [Real.sqrt_mul (mul_nonneg (le_of_lt hL0) (le_of_lt hnR0)),
        Real.sqrt_mul (le_of_lt hL0), ← hsL_def, ← hsnR_def, ← hsA_def]
    have hsqrtL₂A : Real.sqrt (L₂ * A) = sL₂ * sA := by
      rw [Real.sqrt_mul (le_of_lt hL₂0), ← hsL₂_def, ← hsA_def]
    have hn1n2_eq : (n₁ : ℝ) * (n₂ : ℝ) = nR * mnR := hmaxmin.symm
    have hra : Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) =
        srr / (snR * smn) := by
      rw [hn1n2_eq, Real.sqrt_div (le_of_lt hrR0),
        Real.sqrt_mul (le_of_lt hnR0), ← hsrr_def, ← hsnR_def, ← hsmn_def]
    have hmur : Real.sqrt (μ₀ * (r : ℝ) / mnR) = smu * srr / smn := by
      rw [Real.sqrt_div (mul_nonneg (le_of_lt hμ₀0) (le_of_lt hrR0)),
        Real.sqrt_mul (le_of_lt hμ₀0), ← hsmu_def, ← hsrr_def, ← hsmn_def]
    -- the two tight-scale products in sqrt variables
    have hc1 : μ₀ * Real.sqrt (r : ℝ) *
        Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
          Real.sqrt (μ₀ * (r : ℝ) / mnR) * (μ₀ * (r : ℝ) / mnR) =
        smu ^ 5 * srr ^ 5 / (snR * smn ^ 4) := by
      rw [hra, hmur, ← hsrr_def, ← hsmu_sq, ← hsrr_sq, ← hsmn_sq]
      field_simp
    have hc2 : μ₀ * Real.sqrt (r : ℝ) *
        Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
          (μ₀ * (r : ℝ) / mnR) * (μ₀ * (r : ℝ) / mnR) =
        smu ^ 6 * srr ^ 6 / (snR * smn ^ 5) := by
      rw [hra, ← hsrr_def, ← hsmu_sq, ← hsrr_sq, ← hsmn_sq]
      field_simp
    -- the two absorbed terms
    have hTermI_eq : A * Real.sqrt (L * nR * A) *
        (Real.sqrt (L₂ * A) * (smu ^ 5 * srr ^ 5 / (snR * smn ^ 4))) =
        sA ^ 4 * sL * sL₂ * smu ^ 5 * srr ^ 5 / smn ^ 4 := by
      rw [hsqrtLNA, hsqrtL₂A, ← hsA_sq]
      field_simp
    have hTermII_eq : A * Real.sqrt (L * nR * A) *
        ((L₂ * A) * (smu ^ 6 * srr ^ 6 / (snR * smn ^ 5))) =
        sA ^ 5 * sL * sL₂ ^ 2 * smu ^ 6 * srr ^ 6 / smn ^ 5 := by
      rw [hsqrtLNA, ← hsA_sq, ← hsL₂_sq]
      field_simp
    -- comparison of A-powers with D-powers
    have hsA_le_sD : sA ≤ sD := by
      rw [hsA_def, hsD_def]; exact Real.sqrt_le_sqrt hA_le_D
    have hsD_eq : sD = smn / sK := by
      rw [hsD_def, hD_def, Real.sqrt_div (le_of_lt hmnR0),
        ← hsmn_def, ← hsK_def]
    have hsK_split : sK = slam * sU * sV * sL := by
      rw [hsK_def, hK_def,
        Real.sqrt_mul (mul_nonneg (mul_nonneg (le_of_lt hlam0) (le_of_lt hU0))
          (le_of_lt hV0)),
        Real.sqrt_mul (mul_nonneg (le_of_lt hlam0) (le_of_lt hU0)),
        Real.sqrt_mul (le_of_lt hlam0),
        ← hslam_def, ← hsU_def, ← hsV_def, ← hsL_def]
    -- √2 ≤ 2
    have hsqrt2_le : Real.sqrt 2 ≤ 2 := by
      have h4 : Real.sqrt 4 = 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
      calc Real.sqrt 2 ≤ Real.sqrt 4 :=
            Real.sqrt_le_sqrt (by norm_num)
        _ = 2 := h4
    have hsL₂_le : sL₂ ≤ Real.sqrt 2 * sL := by
      rw [hsL₂_def, hsL_def, ← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      exact Real.sqrt_le_sqrt hL₂le
    -- power comparisons against U, V
    have hsmu5_le : smu ^ 5 ≤ sU ^ 4 := by
      have hlhs : smu ^ 5 = μ₀ ^ 2 * Real.sqrt μ₀ := by
        have h1 : smu ^ 5 = (smu ^ 2) ^ 2 * smu := by ring
        rw [h1, hsmu_sq, hsmu_def]
      have hrhs : sU ^ 4 = U ^ 2 := by
        have h1 : sU ^ 4 = (sU ^ 2) ^ 2 := by ring
        rw [h1, hsU_sq]
      rw [hlhs, hrhs, hU_def]
      exact rpow43_sq μ₀ hμ₀0 hμ₀
    have hsrr5_le : srr ^ 5 ≤ sV ^ 4 := by
      have hlhs : srr ^ 5 = (r : ℝ) ^ 2 * Real.sqrt (r : ℝ) := by
        have h1 : srr ^ 5 = (srr ^ 2) ^ 2 * srr := by ring
        rw [h1, hsrr_sq, hsrr_def]
      have hrhs : sV ^ 4 = V ^ 2 := by
        have h1 : sV ^ 4 = (sV ^ 2) ^ 2 := by ring
        rw [h1, hsV_sq]
      rw [hlhs, hrhs, hV_def]
      exact rpow43_sq (r : ℝ) hrR0 hrR1
    have hsmu6_le : smu ^ 6 ≤ sU ^ 5 := by
      have hlhs : smu ^ 6 = μ₀ ^ 3 := by
        have h1 : smu ^ 6 = (smu ^ 2) ^ 3 := by ring
        rw [h1, hsmu_sq]
      have hrhs : sU ^ 5 = U ^ 2 * Real.sqrt U := by
        have h1 : sU ^ 5 = (sU ^ 2) ^ 2 * sU := by ring
        rw [h1, hsU_sq, hsU_def]
      rw [hlhs, hrhs, hU_def]
      exact rpow43_cube μ₀ hμ₀0 hμ₀
    have hsrr6_le : srr ^ 6 ≤ sV ^ 5 := by
      have hlhs : srr ^ 6 = (r : ℝ) ^ 3 := by
        have h1 : srr ^ 6 = (srr ^ 2) ^ 3 := by ring
        rw [h1, hsrr_sq]
      have hrhs : sV ^ 5 = V ^ 2 * Real.sqrt V := by
        have h1 : sV ^ 5 = (sV ^ 2) ^ 2 * sV := by ring
        rw [h1, hsV_sq, hsV_def]
      rw [hlhs, hrhs, hV_def]
      exact rpow43_cube (r : ℝ) hrR0 hrR1
    -- λ^{-3/2} = 1 / slam³
    have hrpow_expand : Real.rpow lam (-((3 : ℝ) / 2)) = 1 / slam ^ 3 := by
      rw [show Real.rpow lam (-((3 : ℝ) / 2)) = lam ^ (-((3 : ℝ) / 2)) from rfl,
        Real.rpow_neg (le_of_lt hlam0), one_div]
      congr 1
      have h32 : ((3 : ℝ) / 2) = 1 + 1 / 2 := by norm_num
      rw [h32, Real.rpow_add hlam0, Real.rpow_one, ← Real.sqrt_eq_rpow,
        ← hslam_def, ← hslam_sq]
      ring
    -- Term I bound
    have hTermI_le : sA ^ 4 * sL * sL₂ * smu ^ 5 * srr ^ 5 / smn ^ 4 ≤
        2 * Real.rpow lam (-((3 : ℝ) / 2)) := by
      have hQ_nonneg : (0 : ℝ) ≤ sL * sL₂ * smu ^ 5 * srr ^ 5 :=
        mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt hsL0) (le_of_lt hsL₂0))
          (pow_nonneg (le_of_lt hsmu0) 5)) (pow_nonneg (le_of_lt hsrr0) 5)
      have hpow4 : sA ^ 4 ≤ sD ^ 4 :=
        pow_le_pow_left₀ (le_of_lt hsA0) hsA_le_sD 4
      have hstep1 : sA ^ 4 * sL * sL₂ * smu ^ 5 * srr ^ 5 / smn ^ 4 ≤
          sD ^ 4 * sL * sL₂ * smu ^ 5 * srr ^ 5 / smn ^ 4 := by
        have hnum : sA ^ 4 * sL * sL₂ * smu ^ 5 * srr ^ 5 ≤
            sD ^ 4 * sL * sL₂ * smu ^ 5 * srr ^ 5 := by
          have h1 : sA ^ 4 * (sL * sL₂ * smu ^ 5 * srr ^ 5) ≤
              sD ^ 4 * (sL * sL₂ * smu ^ 5 * srr ^ 5) :=
            mul_le_mul_of_nonneg_right hpow4 hQ_nonneg
          calc sA ^ 4 * sL * sL₂ * smu ^ 5 * srr ^ 5
              = sA ^ 4 * (sL * sL₂ * smu ^ 5 * srr ^ 5) := by ring
            _ ≤ sD ^ 4 * (sL * sL₂ * smu ^ 5 * srr ^ 5) := h1
            _ = sD ^ 4 * sL * sL₂ * smu ^ 5 * srr ^ 5 := by ring
        calc sA ^ 4 * sL * sL₂ * smu ^ 5 * srr ^ 5 / smn ^ 4
            = (sA ^ 4 * sL * sL₂ * smu ^ 5 * srr ^ 5) * (smn ^ 4)⁻¹ :=
              div_eq_mul_inv _ _
          _ ≤ (sD ^ 4 * sL * sL₂ * smu ^ 5 * srr ^ 5) * (smn ^ 4)⁻¹ :=
              mul_le_mul_of_nonneg_right hnum
                (inv_nonneg.mpr (pow_nonneg (le_of_lt hsmn0) 4))
          _ = sD ^ 4 * sL * sL₂ * smu ^ 5 * srr ^ 5 / smn ^ 4 :=
              (div_eq_mul_inv _ _).symm
      have hstep2 : sD ^ 4 * sL * sL₂ * smu ^ 5 * srr ^ 5 / smn ^ 4 =
          sL * sL₂ * smu ^ 5 * srr ^ 5 / sK ^ 4 := by
        rw [hsD_eq, div_pow]
        field_simp
      have hstep3 : sL * sL₂ * smu ^ 5 * srr ^ 5 / sK ^ 4 ≤ 2 / slam ^ 3 := by
        rw [div_le_div_iff₀ (pow_pos hsK0 4) (pow_pos hslam0 3)]
        -- goal: sL * sL₂ * smu^5 * srr^5 * slam^3 ≤ 2 * sK^4
        have hbound : sL * sL₂ * smu ^ 5 * srr ^ 5 * slam ^ 3 ≤
            sL * (Real.sqrt 2 * sL) * sU ^ 4 * sV ^ 4 * slam ^ 4 := by
          have hs1 : sL * sL₂ ≤ sL * (Real.sqrt 2 * sL) :=
            mul_le_mul_of_nonneg_left hsL₂_le (le_of_lt hsL0)
          have hs2 : sL * sL₂ * smu ^ 5 ≤ sL * (Real.sqrt 2 * sL) * sU ^ 4 :=
            mul_le_mul hs1 hsmu5_le (pow_nonneg (le_of_lt hsmu0) 5)
              (mul_nonneg (le_of_lt hsL0)
                (mul_nonneg (Real.sqrt_nonneg 2) (le_of_lt hsL0)))
          have hs3 : sL * sL₂ * smu ^ 5 * srr ^ 5 ≤
              sL * (Real.sqrt 2 * sL) * sU ^ 4 * sV ^ 4 :=
            mul_le_mul hs2 hsrr5_le (pow_nonneg (le_of_lt hsrr0) 5)
              (mul_nonneg (mul_nonneg (le_of_lt hsL0)
                (mul_nonneg (Real.sqrt_nonneg 2) (le_of_lt hsL0)))
                (pow_nonneg (le_of_lt hsU0) 4))
          have hs4 : slam ^ 3 ≤ slam ^ 4 :=
            pow_le_pow_right₀ hslam1 (by norm_num)
          exact mul_le_mul hs3 hs4 (pow_nonneg (le_of_lt hslam0) 3)
            (mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt hsL0)
              (mul_nonneg (Real.sqrt_nonneg 2) (le_of_lt hsL0)))
              (pow_nonneg (le_of_lt hsU0) 4)) (pow_nonneg (le_of_lt hsV0) 4))
        refine le_trans hbound ?_
        have hsqrt2sL : Real.sqrt 2 * (sL * sL) ≤ 2 * (sL ^ 2 * sL ^ 2) := by
          have hsLsq : sL * sL ≤ sL ^ 2 * sL ^ 2 := by
            have h1 : sL * sL = sL ^ 2 := (sq sL).symm
            have h2 : sL ^ 2 ≤ sL ^ 2 * sL ^ 2 := by
              calc sL ^ 2 = sL ^ 2 * 1 := (mul_one _).symm
                _ ≤ sL ^ 2 * sL ^ 2 := by
                    apply mul_le_mul_of_nonneg_left ?_
                      (pow_nonneg (le_of_lt hsL0) 2)
                    calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
                      _ ≤ sL * sL := mul_le_mul hsL1 hsL1 zero_le_one
                          (le_trans zero_le_one hsL1)
                      _ = sL ^ 2 := (sq sL).symm
            rw [h1]; exact h2
          exact mul_le_mul hsqrt2_le hsLsq
            (mul_nonneg (le_of_lt hsL0) (le_of_lt hsL0)) (by norm_num)
        calc sL * (Real.sqrt 2 * sL) * sU ^ 4 * sV ^ 4 * slam ^ 4
            = (Real.sqrt 2 * (sL * sL)) * (sU ^ 4 * sV ^ 4 * slam ^ 4) := by
              ring
          _ ≤ (2 * (sL ^ 2 * sL ^ 2)) * (sU ^ 4 * sV ^ 4 * slam ^ 4) := by
              apply mul_le_mul_of_nonneg_right hsqrt2sL
              exact mul_nonneg (mul_nonneg (pow_nonneg (le_of_lt hsU0) 4)
                (pow_nonneg (le_of_lt hsV0) 4)) (pow_nonneg (le_of_lt hslam0) 4)
          _ = 2 * (slam * sU * sV * sL) ^ 4 := by ring
          _ = 2 * sK ^ 4 := by rw [hsK_split]
      rw [hrpow_expand]
      calc sA ^ 4 * sL * sL₂ * smu ^ 5 * srr ^ 5 / smn ^ 4
          ≤ sD ^ 4 * sL * sL₂ * smu ^ 5 * srr ^ 5 / smn ^ 4 := hstep1
        _ = sL * sL₂ * smu ^ 5 * srr ^ 5 / sK ^ 4 := hstep2
        _ ≤ 2 / slam ^ 3 := hstep3
        _ = 2 * (1 / slam ^ 3) := by ring
    -- Term II bound
    have hTermII_le : sA ^ 5 * sL * sL₂ ^ 2 * smu ^ 6 * srr ^ 6 / smn ^ 5 ≤
        2 * Real.rpow lam (-((3 : ℝ) / 2)) := by
      have hQ2_nonneg : (0 : ℝ) ≤ sL * sL₂ ^ 2 * smu ^ 6 * srr ^ 6 :=
        mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt hsL0)
          (pow_nonneg (le_of_lt hsL₂0) 2)) (pow_nonneg (le_of_lt hsmu0) 6))
          (pow_nonneg (le_of_lt hsrr0) 6)
      have hpow5 : sA ^ 5 ≤ sD ^ 5 :=
        pow_le_pow_left₀ (le_of_lt hsA0) hsA_le_sD 5
      have hstep1 : sA ^ 5 * sL * sL₂ ^ 2 * smu ^ 6 * srr ^ 6 / smn ^ 5 ≤
          sD ^ 5 * sL * sL₂ ^ 2 * smu ^ 6 * srr ^ 6 / smn ^ 5 := by
        have hnum : sA ^ 5 * sL * sL₂ ^ 2 * smu ^ 6 * srr ^ 6 ≤
            sD ^ 5 * sL * sL₂ ^ 2 * smu ^ 6 * srr ^ 6 := by
          have h1 : sA ^ 5 * (sL * sL₂ ^ 2 * smu ^ 6 * srr ^ 6) ≤
              sD ^ 5 * (sL * sL₂ ^ 2 * smu ^ 6 * srr ^ 6) :=
            mul_le_mul_of_nonneg_right hpow5 hQ2_nonneg
          calc sA ^ 5 * sL * sL₂ ^ 2 * smu ^ 6 * srr ^ 6
              = sA ^ 5 * (sL * sL₂ ^ 2 * smu ^ 6 * srr ^ 6) := by ring
            _ ≤ sD ^ 5 * (sL * sL₂ ^ 2 * smu ^ 6 * srr ^ 6) := h1
            _ = sD ^ 5 * sL * sL₂ ^ 2 * smu ^ 6 * srr ^ 6 := by ring
        calc sA ^ 5 * sL * sL₂ ^ 2 * smu ^ 6 * srr ^ 6 / smn ^ 5
            = (sA ^ 5 * sL * sL₂ ^ 2 * smu ^ 6 * srr ^ 6) * (smn ^ 5)⁻¹ :=
              div_eq_mul_inv _ _
          _ ≤ (sD ^ 5 * sL * sL₂ ^ 2 * smu ^ 6 * srr ^ 6) * (smn ^ 5)⁻¹ :=
              mul_le_mul_of_nonneg_right hnum
                (inv_nonneg.mpr (pow_nonneg (le_of_lt hsmn0) 5))
          _ = sD ^ 5 * sL * sL₂ ^ 2 * smu ^ 6 * srr ^ 6 / smn ^ 5 :=
              (div_eq_mul_inv _ _).symm
      have hstep2 : sD ^ 5 * sL * sL₂ ^ 2 * smu ^ 6 * srr ^ 6 / smn ^ 5 =
          sL * sL₂ ^ 2 * smu ^ 6 * srr ^ 6 / sK ^ 5 := by
        rw [hsD_eq, div_pow]
        field_simp
      have hstep3 : sL * sL₂ ^ 2 * smu ^ 6 * srr ^ 6 / sK ^ 5 ≤
          2 / slam ^ 3 := by
        rw [div_le_div_iff₀ (pow_pos hsK0 5) (pow_pos hslam0 3)]
        -- goal: sL * sL₂^2 * smu^6 * srr^6 * slam^3 ≤ 2 * sK^5
        have hL₂sq_le : sL₂ ^ 2 ≤ 2 * sL ^ 2 := by
          rw [hsL₂_sq, hsL_sq]; exact hL₂le
        have hbound : sL * sL₂ ^ 2 * smu ^ 6 * srr ^ 6 * slam ^ 3 ≤
            sL * (2 * sL ^ 2) * sU ^ 5 * sV ^ 5 * slam ^ 5 := by
          have hs1 : sL * sL₂ ^ 2 ≤ sL * (2 * sL ^ 2) :=
            mul_le_mul_of_nonneg_left hL₂sq_le (le_of_lt hsL0)
          have hs2 : sL * sL₂ ^ 2 * smu ^ 6 ≤ sL * (2 * sL ^ 2) * sU ^ 5 :=
            mul_le_mul hs1 hsmu6_le (pow_nonneg (le_of_lt hsmu0) 6)
              (mul_nonneg (le_of_lt hsL0)
                (mul_nonneg (by norm_num) (pow_nonneg (le_of_lt hsL0) 2)))
          have hs3 : sL * sL₂ ^ 2 * smu ^ 6 * srr ^ 6 ≤
              sL * (2 * sL ^ 2) * sU ^ 5 * sV ^ 5 :=
            mul_le_mul hs2 hsrr6_le (pow_nonneg (le_of_lt hsrr0) 6)
              (mul_nonneg (mul_nonneg (le_of_lt hsL0)
                (mul_nonneg (by norm_num) (pow_nonneg (le_of_lt hsL0) 2)))
                (pow_nonneg (le_of_lt hsU0) 5))
          have hs4 : slam ^ 3 ≤ slam ^ 5 :=
            pow_le_pow_right₀ hslam1 (by norm_num)
          exact mul_le_mul hs3 hs4 (pow_nonneg (le_of_lt hslam0) 3)
            (mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt hsL0)
              (mul_nonneg (by norm_num) (pow_nonneg (le_of_lt hsL0) 2)))
              (pow_nonneg (le_of_lt hsU0) 5)) (pow_nonneg (le_of_lt hsV0) 5))
        refine le_trans hbound ?_
        have hsL3_le : sL ^ 3 ≤ sL ^ 5 :=
          pow_le_pow_right₀ hsL1 (by norm_num)
        calc sL * (2 * sL ^ 2) * sU ^ 5 * sV ^ 5 * slam ^ 5
            = 2 * (sL ^ 3 * (sU ^ 5 * sV ^ 5 * slam ^ 5)) := by ring
          _ ≤ 2 * (sL ^ 5 * (sU ^ 5 * sV ^ 5 * slam ^ 5)) := by
              apply mul_le_mul_of_nonneg_left ?_ (by norm_num)
              apply mul_le_mul_of_nonneg_right hsL3_le
              exact mul_nonneg (mul_nonneg (pow_nonneg (le_of_lt hsU0) 5)
                (pow_nonneg (le_of_lt hsV0) 5)) (pow_nonneg (le_of_lt hslam0) 5)
          _ = 2 * (slam * sU * sV * sL) ^ 5 := by ring
          _ = 2 * sK ^ 5 := by rw [hsK_split]
      rw [hrpow_expand]
      calc sA ^ 5 * sL * sL₂ ^ 2 * smu ^ 6 * srr ^ 6 / smn ^ 5
          ≤ sD ^ 5 * sL * sL₂ ^ 2 * smu ^ 6 * srr ^ 6 / smn ^ 5 := hstep1
        _ = sL * sL₂ ^ 2 * smu ^ 6 * srr ^ 6 / sK ^ 5 := hstep2
        _ ≤ 2 / slam ^ 3 := hstep3
        _ = 2 * (1 / slam ^ 3) := by ring
    -- scalar absorption for the whole tight scale
    have hscalar : A * Real.sqrt (L * nR * A) *
        (Real.sqrt (L₂ * A) *
            (μ₀ * Real.sqrt (r : ℝ) *
              Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                Real.sqrt (μ₀ * (r : ℝ) / mnR) *
                  (μ₀ * (r : ℝ) / mnR)) +
          (L₂ * A) *
            (μ₀ * Real.sqrt (r : ℝ) *
              Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                (μ₀ * (r : ℝ) / mnR) *
                  (μ₀ * (r : ℝ) / mnR))) ≤
        4 * Real.rpow lam (-((3 : ℝ) / 2)) := by
      rw [hc1, hc2, mul_add, hTermI_eq, hTermII_eq]
      calc sA ^ 4 * sL * sL₂ * smu ^ 5 * srr ^ 5 / smn ^ 4 +
            sA ^ 5 * sL * sL₂ ^ 2 * smu ^ 6 * srr ^ 6 / smn ^ 5
          ≤ 2 * Real.rpow lam (-((3 : ℝ) / 2)) +
              2 * Real.rpow lam (-((3 : ℝ) / 2)) :=
            add_le_add hTermI_le hTermII_le
        _ = 4 * Real.rpow lam (-((3 : ℝ) / 2)) := by ring
    -- assemble the norm chain
    have hscale_nonneg : (0 : ℝ) ≤ Cfixed * Real.sqrt (L * nR * A) :=
      mul_nonneg (le_of_lt hCf) (Real.sqrt_nonneg _)
    have h1 : spectralNorm (centeredSamplingFluctuation Omega p B) ≤
        Cfixed * Real.sqrt (L * nR * A) *
          (Ccoef *
            (Real.sqrt (L₂ * A) *
                (μ₀ * Real.sqrt (r : ℝ) *
                  Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                    Real.sqrt (μ₀ * (r : ℝ) / mnR) *
                      (μ₀ * (r : ℝ) / mnR)) +
              (L₂ * A) *
                (μ₀ * Real.sqrt (r : ℝ) *
                  Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                    (μ₀ * (r : ℝ) / mnR) *
                      (μ₀ * (r : ℝ) / mnR)))) := by
      calc spectralNorm (centeredSamplingFluctuation Omega p B)
          ≤ Cfixed * Real.sqrt (L * nR * A) * entrySupNorm B := hcsf
        _ ≤ Cfixed * Real.sqrt (L * nR * A) *
            (Ccoef *
              (Real.sqrt (L₂ * A) *
                  (μ₀ * Real.sqrt (r : ℝ) *
                    Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                      Real.sqrt (μ₀ * (r : ℝ) / mnR) *
                        (μ₀ * (r : ℝ) / mnR)) +
                (L₂ * A) *
                  (μ₀ * Real.sqrt (r : ℝ) *
                    Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                      (μ₀ * (r : ℝ) / mnR) *
                        (μ₀ * (r : ℝ) / mnR)))) :=
            mul_le_mul_of_nonneg_left hB hscale_nonneg
    calc spectralNorm Y
        = |p⁻¹ * (1 - 2 * p)| *
            spectralNorm (centeredSamplingFluctuation Omega p B) := hYnorm
      _ ≤ A * (Cfixed * Real.sqrt (L * nR * A) *
            (Ccoef *
              (Real.sqrt (L₂ * A) *
                  (μ₀ * Real.sqrt (r : ℝ) *
                    Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                      Real.sqrt (μ₀ * (r : ℝ) / mnR) *
                        (μ₀ * (r : ℝ) / mnR)) +
                (L₂ * A) *
                  (μ₀ * Real.sqrt (r : ℝ) *
                    Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                      (μ₀ * (r : ℝ) / mnR) *
                        (μ₀ * (r : ℝ) / mnR))))) :=
          mul_le_mul hpref h1 hcsf_nonneg (le_of_lt hA0)
      _ = (Cfixed * Ccoef) *
            (A * Real.sqrt (L * nR * A) *
              (Real.sqrt (L₂ * A) *
                  (μ₀ * Real.sqrt (r : ℝ) *
                    Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                      Real.sqrt (μ₀ * (r : ℝ) / mnR) *
                        (μ₀ * (r : ℝ) / mnR)) +
                (L₂ * A) *
                  (μ₀ * Real.sqrt (r : ℝ) *
                    Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                      (μ₀ * (r : ℝ) / mnR) *
                        (μ₀ * (r : ℝ) / mnR)))) := by ring
      _ ≤ (Cfixed * Ccoef) * (4 * Real.rpow lam (-((3 : ℝ) / 2))) :=
          mul_le_mul_of_nonneg_left hscalar
            (mul_nonneg (le_of_lt hCf) (le_of_lt hCc))
      _ = 4 * (Cfixed * Ccoef) * Real.rpow lam (-((3 : ℝ) / 2)) := by ring
