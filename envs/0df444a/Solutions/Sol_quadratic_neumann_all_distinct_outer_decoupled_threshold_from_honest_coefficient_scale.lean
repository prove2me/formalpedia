-- Prove2me | solution 1 for quadratic_neumann_all_distinct_outer_decoupled_threshold_from_honest_coefficient_scale
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-07-04T14:18:53.618598+00:00
-- url     : https://prove2.me/submissions/01fd5c36-8033-47a2-84a2-fba3b027ac45

import Definitions.Def_matrix_completion_tangent
import Mathlib.Analysis.Complex.ExponentialBounds

open MatrixCompletion

/-- Deterministic threshold absorption for the all-distinct decoupled quadratic
term (honest min-dim scale): the Theorem 6.3 factor `√(β n log n / p)` times the
honest four-term middle coefficient scale (at `μ₁ = μ₀√r`) absorbs into
`36 (Cfixed Ccoef) · λ^{-3/2}` under `m ≥ λ μ₀^{4/3} n r^{4/3} β log n`.
This is the λ^{-3/2}-tight case: the four monomials cancel exactly
(`(L/K)^{3/2}·(μ₀r)² = λ^{-3/2}` for the leading term). -/
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
          centeredSamplingFluctuation Omega
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) B →
        entrySupNorm B ≤
          Ccoef *
            (Real.sqrt
                  (((β + 2) * Real.log (↑(max n₁ n₂))) /
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                (Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) *
                  (Real.sqrt
                        (((β + 4) * Real.log (↑(max n₁ n₂))) /
                          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                      (μ₀ * Real.sqrt (r : ℝ) *
                        Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                        Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))) +
                    (((β + 4) * Real.log (↑(max n₁ n₂))) /
                        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                      (μ₀ * Real.sqrt (r : ℝ) *
                        Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                        (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))))) +
              (((β + 2) * Real.log (↑(max n₁ n₂))) /
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                ((μ₀ * (r : ℝ) / (↑(min n₁ n₂))) *
                  (Real.sqrt
                        (((β + 4) * Real.log (↑(max n₁ n₂))) /
                          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                      (μ₀ * Real.sqrt (r : ℝ) *
                        Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                        Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))) +
                    (((β + 4) * Real.log (↑(max n₁ n₂))) /
                        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                      (μ₀ * Real.sqrt (r : ℝ) *
                        Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                        (μ₀ * (r : ℝ) / (↑(min n₁ n₂))))))) →
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
  -- x² ≤ U·√U for U = x^{4/3}, 1 ≤ x  (x² = x^{4/3+2/3}, exact)
  have rpow43_two : ∀ x : ℝ, 0 < x → 1 ≤ x →
      x ^ 2 ≤ (Real.rpow x ((4 : ℝ) / 3)) * Real.sqrt (Real.rpow x ((4 : ℝ) / 3)) := by
    intro x hx0 hx1
    have hnot : Real.rpow x ((4 : ℝ) / 3) = x ^ ((4 : ℝ) / 3) := rfl
    rw [hnot]
    have hs : Real.sqrt (x ^ ((4 : ℝ) / 3)) = x ^ ((2 : ℝ) / 3) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (le_of_lt hx0)]
      norm_num
    have hc : x ^ (2 : ℕ) = x ^ ((2 : ℝ)) := by
      rw [← Real.rpow_natCast x 2]; norm_num
    rw [hs, hc, ← Real.rpow_add hx0]
    apply Real.rpow_le_rpow_of_exponent_le hx1
    norm_num
  -- x²·√x ≤ U² for U = x^{4/3}, 1 ≤ x  (x^{5/2} ≤ x^{8/3})
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
  -- x³ ≤ U²·√U for U = x^{4/3}, 1 ≤ x  (x³ ≤ x^{10/3})
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
  refine ⟨36 * (Cfixed * Ccoef), by positivity, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m μ₀ hn₁ hn₂ hr hm hμ₀ hsample Omega B Y hY hB hcsf
  have hlam0 : (0 : ℝ) < lam := lt_of_lt_of_le one_pos hlam
  have hn₁R : (0 : ℝ) < (n₁ : ℝ) := by exact_mod_cast hn₁
  have hn₂R : (0 : ℝ) < (n₂ : ℝ) := by exact_mod_cast hn₂
  have hμ₀0 : (0 : ℝ) < μ₀ := lt_of_lt_of_le one_pos hμ₀
  have hrR1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hrR0 : (0 : ℝ) < (r : ℝ) := lt_of_lt_of_le one_pos hrR1
  set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp_def
  have hcsf_nonneg : 0 ≤ spectralNorm (centeredSamplingFluctuation Omega p B) := by
    unfold spectralNorm; exact norm_nonneg _
  have hYnorm : spectralNorm Y =
      spectralNorm (centeredSamplingFluctuation Omega p B) := by
    rw [hY]
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
    rw [hYnorm, hzero]
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
    obtain ⟨L₄, hL₄_def⟩ : ∃ x : ℝ, x = (β + 4) * Real.log nR := ⟨_, rfl⟩
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
    have hL₄0 : (0 : ℝ) < L₄ := by
      rw [hL₄_def]
      exact mul_pos (by linarith) hlognR0
    have hL₂le : L₂ ≤ 4 * L := by
      rw [hL₂_def, hL_def]
      have hb2 : β + 2 ≤ 4 * β := by linarith
      calc (β + 2) * Real.log nR ≤ (4 * β) * Real.log nR :=
            mul_le_mul_of_nonneg_right hb2 (le_of_lt hlognR0)
        _ = 4 * (β * Real.log nR) := by ring
    have hL₄le : L₄ ≤ 4 * L := by
      rw [hL₄_def, hL_def]
      have hb4 : β + 4 ≤ 4 * β := by linarith
      calc (β + 4) * Real.log nR ≤ (4 * β) * Real.log nR :=
            mul_le_mul_of_nonneg_right hb4 (le_of_lt hlognR0)
        _ = 4 * (β * Real.log nR) := by ring
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
    -- rewrite the sqrt arguments
    have hsqrt_arg : (β * nR * Real.log nR) / p = L * nR * A := by
      rw [hL_def, hA_def, div_eq_mul_inv]; ring
    have hL₂A : ((β + 2) * Real.log nR) / p = L₂ * A := by
      rw [hL₂_def, hA_def, div_eq_mul_inv]
    have hL₄A : ((β + 4) * Real.log nR) / p = L₄ * A := by
      rw [hL₄_def, hA_def, div_eq_mul_inv]
    rw [hsqrt_arg] at hcsf
    rw [hL₂A, hL₄A] at hB
    -- square-root opaque variables
    obtain ⟨sA, hsA_def⟩ : ∃ x : ℝ, x = Real.sqrt A := ⟨_, rfl⟩
    obtain ⟨sD, hsD_def⟩ : ∃ x : ℝ, x = Real.sqrt D := ⟨_, rfl⟩
    obtain ⟨sL, hsL_def⟩ : ∃ x : ℝ, x = Real.sqrt L := ⟨_, rfl⟩
    obtain ⟨sL₂, hsL₂_def⟩ : ∃ x : ℝ, x = Real.sqrt L₂ := ⟨_, rfl⟩
    obtain ⟨sL₄, hsL₄_def⟩ : ∃ x : ℝ, x = Real.sqrt L₄ := ⟨_, rfl⟩
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
    have hsL₄0 : (0 : ℝ) < sL₄ := by
      rw [hsL₄_def]; exact Real.sqrt_pos.mpr hL₄0
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
    have hsL₄_sq : sL₄ ^ 2 = L₄ := by
      rw [hsL₄_def]; exact Real.sq_sqrt (le_of_lt hL₄0)
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
    have hsL1 : (1 : ℝ) ≤ sL := by
      rw [hsL_def]; exact Real.one_le_sqrt.mpr hL1
    have hslam1 : (1 : ℝ) ≤ slam := by
      rw [hslam_def]; exact Real.one_le_sqrt.mpr hlam
    -- sL₂ ≤ 2 sL and sL₄ ≤ 2 sL (from L₂, L₄ ≤ 4L)
    have hsL₂_le : sL₂ ≤ 2 * sL := by
      have h4 : Real.sqrt (4 * L) = 2 * Real.sqrt L := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
        congr 1
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
      rw [hsL₂_def, hsL_def, ← h4]
      exact Real.sqrt_le_sqrt hL₂le
    have hsL₄_le : sL₄ ≤ 2 * sL := by
      have h4 : Real.sqrt (4 * L) = 2 * Real.sqrt L := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
        congr 1
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
      rw [hsL₄_def, hsL_def, ← h4]
      exact Real.sqrt_le_sqrt hL₄le
    -- splitting composite square roots
    have hsqrtLNA : Real.sqrt (L * nR * A) = sL * snR * sA := by
      rw [Real.sqrt_mul (mul_nonneg (le_of_lt hL0) (le_of_lt hnR0)),
        Real.sqrt_mul (le_of_lt hL0), ← hsL_def, ← hsnR_def, ← hsA_def]
    have hsqrtL₂A : Real.sqrt (L₂ * A) = sL₂ * sA := by
      rw [Real.sqrt_mul (le_of_lt hL₂0), ← hsL₂_def, ← hsA_def]
    have hsqrtL₄A : Real.sqrt (L₄ * A) = sL₄ * sA := by
      rw [Real.sqrt_mul (le_of_lt hL₄0), ← hsL₄_def, ← hsA_def]
    have hn1n2_eq : (n₁ : ℝ) * (n₂ : ℝ) = nR * mnR := hmaxmin.symm
    have hra : Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) =
        srr / (snR * smn) := by
      rw [hn1n2_eq, Real.sqrt_div (le_of_lt hrR0),
        Real.sqrt_mul (le_of_lt hnR0), ← hsrr_def, ← hsnR_def, ← hsmn_def]
    have hmur : Real.sqrt (μ₀ * (r : ℝ) / mnR) = smu * srr / smn := by
      rw [Real.sqrt_div (mul_nonneg (le_of_lt hμ₀0) (le_of_lt hrR0)),
        Real.sqrt_mul (le_of_lt hμ₀0), ← hsmu_def, ← hsrr_def, ← hsmn_def]
    -- comparison of A with D and split of D, K
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
    -- power comparisons against U, V
    have hsmu4_le : smu ^ 4 ≤ sU ^ 3 := by
      have hlhs : smu ^ 4 = μ₀ ^ 2 := by
        have h1 : smu ^ 4 = (smu ^ 2) ^ 2 := by ring
        rw [h1, hsmu_sq]
      have hrhs : sU ^ 3 = U * Real.sqrt U := by
        have h1 : sU ^ 3 = sU ^ 2 * sU := by ring
        rw [h1, hsU_sq, hsU_def]
      rw [hlhs, hrhs, hU_def]
      exact rpow43_two μ₀ hμ₀0 hμ₀
    have hsrr4_le : srr ^ 4 ≤ sV ^ 3 := by
      have hlhs : srr ^ 4 = (r : ℝ) ^ 2 := by
        have h1 : srr ^ 4 = (srr ^ 2) ^ 2 := by ring
        rw [h1, hsrr_sq]
      have hrhs : sV ^ 3 = V * Real.sqrt V := by
        have h1 : sV ^ 3 = sV ^ 2 * sV := by ring
        rw [h1, hsV_sq, hsV_def]
      rw [hlhs, hrhs, hV_def]
      exact rpow43_two (r : ℝ) hrR0 hrR1
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
    -- generic monomial bounds G_k := sL^k sA^k smu^{k+1} srr^{k+1} / smn^k ≤ λ^{-3/2}
    have hGgen : ∀ k : ℕ, 3 ≤ k →
        smu ^ (k + 1) ≤ sU ^ k → srr ^ (k + 1) ≤ sV ^ k →
        sL ^ k * sA ^ k * smu ^ (k + 1) * srr ^ (k + 1) / smn ^ k ≤
          Real.rpow lam (-((3 : ℝ) / 2)) := by
      intro k hk3 hmuk hrrk
      have hQ_nonneg : (0 : ℝ) ≤ sL ^ k * smu ^ (k + 1) * srr ^ (k + 1) :=
        mul_nonneg (mul_nonneg (pow_nonneg (le_of_lt hsL0) k)
          (pow_nonneg (le_of_lt hsmu0) (k + 1)))
          (pow_nonneg (le_of_lt hsrr0) (k + 1))
      have hpowk : sA ^ k ≤ sD ^ k :=
        pow_le_pow_left₀ (le_of_lt hsA0) hsA_le_sD k
      have hstep1 : sL ^ k * sA ^ k * smu ^ (k + 1) * srr ^ (k + 1) / smn ^ k ≤
          sL ^ k * sD ^ k * smu ^ (k + 1) * srr ^ (k + 1) / smn ^ k := by
        have hnum : sL ^ k * sA ^ k * smu ^ (k + 1) * srr ^ (k + 1) ≤
            sL ^ k * sD ^ k * smu ^ (k + 1) * srr ^ (k + 1) := by
          have h1 : sA ^ k * (sL ^ k * smu ^ (k + 1) * srr ^ (k + 1)) ≤
              sD ^ k * (sL ^ k * smu ^ (k + 1) * srr ^ (k + 1)) :=
            mul_le_mul_of_nonneg_right hpowk hQ_nonneg
          calc sL ^ k * sA ^ k * smu ^ (k + 1) * srr ^ (k + 1)
              = sA ^ k * (sL ^ k * smu ^ (k + 1) * srr ^ (k + 1)) := by ring
            _ ≤ sD ^ k * (sL ^ k * smu ^ (k + 1) * srr ^ (k + 1)) := h1
            _ = sL ^ k * sD ^ k * smu ^ (k + 1) * srr ^ (k + 1) := by ring
        calc sL ^ k * sA ^ k * smu ^ (k + 1) * srr ^ (k + 1) / smn ^ k
            = (sL ^ k * sA ^ k * smu ^ (k + 1) * srr ^ (k + 1)) * (smn ^ k)⁻¹ :=
              div_eq_mul_inv _ _
          _ ≤ (sL ^ k * sD ^ k * smu ^ (k + 1) * srr ^ (k + 1)) * (smn ^ k)⁻¹ :=
              mul_le_mul_of_nonneg_right hnum
                (inv_nonneg.mpr (pow_nonneg (le_of_lt hsmn0) k))
          _ = sL ^ k * sD ^ k * smu ^ (k + 1) * srr ^ (k + 1) / smn ^ k :=
              (div_eq_mul_inv _ _).symm
      have hstep2 : sL ^ k * sD ^ k * smu ^ (k + 1) * srr ^ (k + 1) / smn ^ k =
          sL ^ k * smu ^ (k + 1) * srr ^ (k + 1) / sK ^ k := by
        rw [hsD_eq, div_pow]
        field_simp
      have hstep3 : sL ^ k * smu ^ (k + 1) * srr ^ (k + 1) / sK ^ k ≤
          1 / slam ^ 3 := by
        rw [div_le_div_iff₀ (pow_pos hsK0 k) (pow_pos hslam0 3)]
        have hslam_pow : slam ^ 3 ≤ slam ^ k :=
          pow_le_pow_right₀ hslam1 hk3
        have hs1 : sL ^ k * smu ^ (k + 1) ≤ sL ^ k * sU ^ k :=
          mul_le_mul_of_nonneg_left hmuk (pow_nonneg (le_of_lt hsL0) k)
        have hs2 : sL ^ k * smu ^ (k + 1) * srr ^ (k + 1) ≤
            sL ^ k * sU ^ k * sV ^ k :=
          mul_le_mul hs1 hrrk (pow_nonneg (le_of_lt hsrr0) (k + 1))
            (mul_nonneg (pow_nonneg (le_of_lt hsL0) k)
              (pow_nonneg (le_of_lt hsU0) k))
        calc sL ^ k * smu ^ (k + 1) * srr ^ (k + 1) * slam ^ 3
            ≤ sL ^ k * sU ^ k * sV ^ k * slam ^ k :=
              mul_le_mul hs2 hslam_pow (pow_nonneg (le_of_lt hslam0) 3)
                (mul_nonneg (mul_nonneg (pow_nonneg (le_of_lt hsL0) k)
                  (pow_nonneg (le_of_lt hsU0) k))
                  (pow_nonneg (le_of_lt hsV0) k))
          _ = (slam * sU * sV * sL) ^ k := by rw [mul_pow, mul_pow, mul_pow]; ring
          _ = sK ^ k := by rw [hsK_split]
          _ = 1 * sK ^ k := (one_mul _).symm
      rw [hrpow_expand]
      calc sL ^ k * sA ^ k * smu ^ (k + 1) * srr ^ (k + 1) / smn ^ k
          ≤ sL ^ k * sD ^ k * smu ^ (k + 1) * srr ^ (k + 1) / smn ^ k := hstep1
        _ = sL ^ k * smu ^ (k + 1) * srr ^ (k + 1) / sK ^ k := hstep2
        _ ≤ 1 / slam ^ 3 := hstep3
    have hG3 := hGgen 3 (by norm_num) hsmu4_le hsrr4_le
    have hG4 := hGgen 4 (by norm_num) hsmu5_le hsrr5_le
    have hG5 := hGgen 5 (by norm_num) hsmu6_le hsrr6_le
    -- the four expanded monomials
    have hX11_le : sL * sL₂ * sL₄ * sA ^ 3 * smu ^ 4 * srr ^ 4 / smn ^ 3 ≤
        4 * Real.rpow lam (-((3 : ℝ) / 2)) := by
      have hfac : sL * sL₂ * sL₄ ≤ 4 * sL ^ 3 := by
        have h1 : sL * sL₂ ≤ sL * (2 * sL) :=
          mul_le_mul_of_nonneg_left hsL₂_le (le_of_lt hsL0)
        have h2 : sL * sL₂ * sL₄ ≤ (sL * (2 * sL)) * (2 * sL) :=
          mul_le_mul h1 hsL₄_le (le_of_lt hsL₄0)
            (mul_nonneg (le_of_lt hsL0)
              (mul_nonneg (by norm_num) (le_of_lt hsL0)))
        calc sL * sL₂ * sL₄ ≤ (sL * (2 * sL)) * (2 * sL) := h2
          _ = 4 * sL ^ 3 := by ring
      have hrest_nonneg : (0 : ℝ) ≤ sA ^ 3 * smu ^ 4 * srr ^ 4 / smn ^ 3 := by
        apply div_nonneg _ (pow_nonneg (le_of_lt hsmn0) 3)
        exact mul_nonneg (mul_nonneg (pow_nonneg (le_of_lt hsA0) 3)
          (pow_nonneg (le_of_lt hsmu0) 4)) (pow_nonneg (le_of_lt hsrr0) 4)
      calc sL * sL₂ * sL₄ * sA ^ 3 * smu ^ 4 * srr ^ 4 / smn ^ 3
          = (sL * sL₂ * sL₄) * (sA ^ 3 * smu ^ 4 * srr ^ 4 / smn ^ 3) := by
            ring
        _ ≤ (4 * sL ^ 3) * (sA ^ 3 * smu ^ 4 * srr ^ 4 / smn ^ 3) :=
            mul_le_mul_of_nonneg_right hfac hrest_nonneg
        _ = 4 * (sL ^ 3 * sA ^ 3 * smu ^ (3 + 1) * srr ^ (3 + 1) / smn ^ 3) := by
            norm_num
            try ring
        _ ≤ 4 * Real.rpow lam (-((3 : ℝ) / 2)) := by
            apply mul_le_mul_of_nonneg_left hG3 (by norm_num)
    have hX12_le : sL * sL₂ * sL₄ ^ 2 * sA ^ 4 * smu ^ 5 * srr ^ 5 / smn ^ 4 ≤
        8 * Real.rpow lam (-((3 : ℝ) / 2)) := by
      have hL₄sq : sL₄ ^ 2 ≤ 4 * sL ^ 2 := by
        have h := mul_le_mul hsL₄_le hsL₄_le (le_of_lt hsL₄0)
          (mul_nonneg (by norm_num) (le_of_lt hsL0))
        calc sL₄ ^ 2 = sL₄ * sL₄ := sq sL₄
          _ ≤ (2 * sL) * (2 * sL) := h
          _ = 4 * sL ^ 2 := by ring
      have hfac : sL * sL₂ * sL₄ ^ 2 ≤ 8 * sL ^ 4 := by
        have h1 : sL * sL₂ ≤ sL * (2 * sL) :=
          mul_le_mul_of_nonneg_left hsL₂_le (le_of_lt hsL0)
        have h2 : sL * sL₂ * sL₄ ^ 2 ≤ (sL * (2 * sL)) * (4 * sL ^ 2) :=
          mul_le_mul h1 hL₄sq (pow_nonneg (le_of_lt hsL₄0) 2)
            (mul_nonneg (le_of_lt hsL0)
              (mul_nonneg (by norm_num) (le_of_lt hsL0)))
        calc sL * sL₂ * sL₄ ^ 2 ≤ (sL * (2 * sL)) * (4 * sL ^ 2) := h2
          _ = 8 * sL ^ 4 := by ring
      have hrest_nonneg : (0 : ℝ) ≤ sA ^ 4 * smu ^ 5 * srr ^ 5 / smn ^ 4 := by
        apply div_nonneg _ (pow_nonneg (le_of_lt hsmn0) 4)
        exact mul_nonneg (mul_nonneg (pow_nonneg (le_of_lt hsA0) 4)
          (pow_nonneg (le_of_lt hsmu0) 5)) (pow_nonneg (le_of_lt hsrr0) 5)
      calc sL * sL₂ * sL₄ ^ 2 * sA ^ 4 * smu ^ 5 * srr ^ 5 / smn ^ 4
          = (sL * sL₂ * sL₄ ^ 2) * (sA ^ 4 * smu ^ 5 * srr ^ 5 / smn ^ 4) := by
            ring
        _ ≤ (8 * sL ^ 4) * (sA ^ 4 * smu ^ 5 * srr ^ 5 / smn ^ 4) :=
            mul_le_mul_of_nonneg_right hfac hrest_nonneg
        _ = 8 * (sL ^ 4 * sA ^ 4 * smu ^ (4 + 1) * srr ^ (4 + 1) / smn ^ 4) := by
            norm_num
            try ring
        _ ≤ 8 * Real.rpow lam (-((3 : ℝ) / 2)) := by
            apply mul_le_mul_of_nonneg_left hG4 (by norm_num)
    have hX21_le : sL * sL₂ ^ 2 * sL₄ * sA ^ 4 * smu ^ 5 * srr ^ 5 / smn ^ 4 ≤
        8 * Real.rpow lam (-((3 : ℝ) / 2)) := by
      have hL₂sq : sL₂ ^ 2 ≤ 4 * sL ^ 2 := by
        have h := mul_le_mul hsL₂_le hsL₂_le (le_of_lt hsL₂0)
          (mul_nonneg (by norm_num) (le_of_lt hsL0))
        calc sL₂ ^ 2 = sL₂ * sL₂ := sq sL₂
          _ ≤ (2 * sL) * (2 * sL) := h
          _ = 4 * sL ^ 2 := by ring
      have hfac : sL * sL₂ ^ 2 * sL₄ ≤ 8 * sL ^ 4 := by
        have h1 : sL * sL₂ ^ 2 ≤ sL * (4 * sL ^ 2) :=
          mul_le_mul_of_nonneg_left hL₂sq (le_of_lt hsL0)
        have h2 : sL * sL₂ ^ 2 * sL₄ ≤ (sL * (4 * sL ^ 2)) * (2 * sL) :=
          mul_le_mul h1 hsL₄_le (le_of_lt hsL₄0)
            (mul_nonneg (le_of_lt hsL0)
              (mul_nonneg (by norm_num) (pow_nonneg (le_of_lt hsL0) 2)))
        calc sL * sL₂ ^ 2 * sL₄ ≤ (sL * (4 * sL ^ 2)) * (2 * sL) := h2
          _ = 8 * sL ^ 4 := by ring
      have hrest_nonneg : (0 : ℝ) ≤ sA ^ 4 * smu ^ 5 * srr ^ 5 / smn ^ 4 := by
        apply div_nonneg _ (pow_nonneg (le_of_lt hsmn0) 4)
        exact mul_nonneg (mul_nonneg (pow_nonneg (le_of_lt hsA0) 4)
          (pow_nonneg (le_of_lt hsmu0) 5)) (pow_nonneg (le_of_lt hsrr0) 5)
      calc sL * sL₂ ^ 2 * sL₄ * sA ^ 4 * smu ^ 5 * srr ^ 5 / smn ^ 4
          = (sL * sL₂ ^ 2 * sL₄) * (sA ^ 4 * smu ^ 5 * srr ^ 5 / smn ^ 4) := by
            ring
        _ ≤ (8 * sL ^ 4) * (sA ^ 4 * smu ^ 5 * srr ^ 5 / smn ^ 4) :=
            mul_le_mul_of_nonneg_right hfac hrest_nonneg
        _ = 8 * (sL ^ 4 * sA ^ 4 * smu ^ (4 + 1) * srr ^ (4 + 1) / smn ^ 4) := by
            norm_num
            try ring
        _ ≤ 8 * Real.rpow lam (-((3 : ℝ) / 2)) := by
            apply mul_le_mul_of_nonneg_left hG4 (by norm_num)
    have hX22_le : sL * sL₂ ^ 2 * sL₄ ^ 2 * sA ^ 5 * smu ^ 6 * srr ^ 6 / smn ^ 5 ≤
        16 * Real.rpow lam (-((3 : ℝ) / 2)) := by
      have hL₂sq : sL₂ ^ 2 ≤ 4 * sL ^ 2 := by
        have h := mul_le_mul hsL₂_le hsL₂_le (le_of_lt hsL₂0)
          (mul_nonneg (by norm_num) (le_of_lt hsL0))
        calc sL₂ ^ 2 = sL₂ * sL₂ := sq sL₂
          _ ≤ (2 * sL) * (2 * sL) := h
          _ = 4 * sL ^ 2 := by ring
      have hL₄sq : sL₄ ^ 2 ≤ 4 * sL ^ 2 := by
        have h := mul_le_mul hsL₄_le hsL₄_le (le_of_lt hsL₄0)
          (mul_nonneg (by norm_num) (le_of_lt hsL0))
        calc sL₄ ^ 2 = sL₄ * sL₄ := sq sL₄
          _ ≤ (2 * sL) * (2 * sL) := h
          _ = 4 * sL ^ 2 := by ring
      have hfac : sL * sL₂ ^ 2 * sL₄ ^ 2 ≤ 16 * sL ^ 5 := by
        have h1 : sL * sL₂ ^ 2 ≤ sL * (4 * sL ^ 2) :=
          mul_le_mul_of_nonneg_left hL₂sq (le_of_lt hsL0)
        have h2 : sL * sL₂ ^ 2 * sL₄ ^ 2 ≤ (sL * (4 * sL ^ 2)) * (4 * sL ^ 2) :=
          mul_le_mul h1 hL₄sq (pow_nonneg (le_of_lt hsL₄0) 2)
            (mul_nonneg (le_of_lt hsL0)
              (mul_nonneg (by norm_num) (pow_nonneg (le_of_lt hsL0) 2)))
        calc sL * sL₂ ^ 2 * sL₄ ^ 2 ≤ (sL * (4 * sL ^ 2)) * (4 * sL ^ 2) := h2
          _ = 16 * sL ^ 5 := by ring
      have hrest_nonneg : (0 : ℝ) ≤ sA ^ 5 * smu ^ 6 * srr ^ 6 / smn ^ 5 := by
        apply div_nonneg _ (pow_nonneg (le_of_lt hsmn0) 5)
        exact mul_nonneg (mul_nonneg (pow_nonneg (le_of_lt hsA0) 5)
          (pow_nonneg (le_of_lt hsmu0) 6)) (pow_nonneg (le_of_lt hsrr0) 6)
      calc sL * sL₂ ^ 2 * sL₄ ^ 2 * sA ^ 5 * smu ^ 6 * srr ^ 6 / smn ^ 5
          = (sL * sL₂ ^ 2 * sL₄ ^ 2) * (sA ^ 5 * smu ^ 6 * srr ^ 6 / smn ^ 5) := by
            ring
        _ ≤ (16 * sL ^ 5) * (sA ^ 5 * smu ^ 6 * srr ^ 6 / smn ^ 5) :=
            mul_le_mul_of_nonneg_right hfac hrest_nonneg
        _ = 16 * (sL ^ 5 * sA ^ 5 * smu ^ (5 + 1) * srr ^ (5 + 1) / smn ^ 5) := by
            norm_num
            try ring
        _ ≤ 16 * Real.rpow lam (-((3 : ℝ) / 2)) := by
            apply mul_le_mul_of_nonneg_left hG5 (by norm_num)
    -- expansion of the honest scale times the 6.3 factor into the four monomials
    have hexpand : Real.sqrt (L * nR * A) *
        (Real.sqrt (L₂ * A) *
            (Real.sqrt (μ₀ * (r : ℝ) / mnR) *
              (Real.sqrt (L₄ * A) *
                  (μ₀ * Real.sqrt (r : ℝ) *
                    Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                    Real.sqrt (μ₀ * (r : ℝ) / mnR)) +
                (L₄ * A) *
                  (μ₀ * Real.sqrt (r : ℝ) *
                    Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                    (μ₀ * (r : ℝ) / mnR)))) +
          (L₂ * A) *
            ((μ₀ * (r : ℝ) / mnR) *
              (Real.sqrt (L₄ * A) *
                  (μ₀ * Real.sqrt (r : ℝ) *
                    Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                    Real.sqrt (μ₀ * (r : ℝ) / mnR)) +
                (L₄ * A) *
                  (μ₀ * Real.sqrt (r : ℝ) *
                    Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                    (μ₀ * (r : ℝ) / mnR))))) =
        sL * sL₂ * sL₄ * sA ^ 3 * smu ^ 4 * srr ^ 4 / smn ^ 3 +
          sL * sL₂ * sL₄ ^ 2 * sA ^ 4 * smu ^ 5 * srr ^ 5 / smn ^ 4 +
          (sL * sL₂ ^ 2 * sL₄ * sA ^ 4 * smu ^ 5 * srr ^ 5 / smn ^ 4 +
            sL * sL₂ ^ 2 * sL₄ ^ 2 * sA ^ 5 * smu ^ 6 * srr ^ 6 / smn ^ 5) := by
      rw [hsqrtLNA, hsqrtL₂A, hsqrtL₄A, hmur, hra, ← hsrr_def,
        ← hsL₂_sq, ← hsL₄_sq, ← hsA_sq, ← hsmu_sq, ← hsrr_sq, ← hsmn_sq]
      field_simp
      try ring
    -- scalar absorption for the whole honest scale
    have hscalar : Real.sqrt (L * nR * A) *
        (Real.sqrt (L₂ * A) *
            (Real.sqrt (μ₀ * (r : ℝ) / mnR) *
              (Real.sqrt (L₄ * A) *
                  (μ₀ * Real.sqrt (r : ℝ) *
                    Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                    Real.sqrt (μ₀ * (r : ℝ) / mnR)) +
                (L₄ * A) *
                  (μ₀ * Real.sqrt (r : ℝ) *
                    Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                    (μ₀ * (r : ℝ) / mnR)))) +
          (L₂ * A) *
            ((μ₀ * (r : ℝ) / mnR) *
              (Real.sqrt (L₄ * A) *
                  (μ₀ * Real.sqrt (r : ℝ) *
                    Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                    Real.sqrt (μ₀ * (r : ℝ) / mnR)) +
                (L₄ * A) *
                  (μ₀ * Real.sqrt (r : ℝ) *
                    Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                    (μ₀ * (r : ℝ) / mnR))))) ≤
        36 * Real.rpow lam (-((3 : ℝ) / 2)) := by
      rw [hexpand]
      have hsum1 := add_le_add hX11_le hX12_le
      have hsum2 := add_le_add hX21_le hX22_le
      have := add_le_add hsum1 hsum2
      calc sL * sL₂ * sL₄ * sA ^ 3 * smu ^ 4 * srr ^ 4 / smn ^ 3 +
            sL * sL₂ * sL₄ ^ 2 * sA ^ 4 * smu ^ 5 * srr ^ 5 / smn ^ 4 +
            (sL * sL₂ ^ 2 * sL₄ * sA ^ 4 * smu ^ 5 * srr ^ 5 / smn ^ 4 +
              sL * sL₂ ^ 2 * sL₄ ^ 2 * sA ^ 5 * smu ^ 6 * srr ^ 6 / smn ^ 5)
          ≤ 4 * Real.rpow lam (-((3 : ℝ) / 2)) +
              8 * Real.rpow lam (-((3 : ℝ) / 2)) +
              (8 * Real.rpow lam (-((3 : ℝ) / 2)) +
                16 * Real.rpow lam (-((3 : ℝ) / 2))) := this
        _ = 36 * Real.rpow lam (-((3 : ℝ) / 2)) := by ring
    -- assemble the norm chain
    have hscale_nonneg : (0 : ℝ) ≤ Cfixed * Real.sqrt (L * nR * A) :=
      mul_nonneg (le_of_lt hCf) (Real.sqrt_nonneg _)
    have h1 : spectralNorm (centeredSamplingFluctuation Omega p B) ≤
        Cfixed * Real.sqrt (L * nR * A) *
          (Ccoef *
            (Real.sqrt (L₂ * A) *
                (Real.sqrt (μ₀ * (r : ℝ) / mnR) *
                  (Real.sqrt (L₄ * A) *
                      (μ₀ * Real.sqrt (r : ℝ) *
                        Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                        Real.sqrt (μ₀ * (r : ℝ) / mnR)) +
                    (L₄ * A) *
                      (μ₀ * Real.sqrt (r : ℝ) *
                        Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                        (μ₀ * (r : ℝ) / mnR)))) +
              (L₂ * A) *
                ((μ₀ * (r : ℝ) / mnR) *
                  (Real.sqrt (L₄ * A) *
                      (μ₀ * Real.sqrt (r : ℝ) *
                        Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                        Real.sqrt (μ₀ * (r : ℝ) / mnR)) +
                    (L₄ * A) *
                      (μ₀ * Real.sqrt (r : ℝ) *
                        Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                        (μ₀ * (r : ℝ) / mnR)))))) := by
      calc spectralNorm (centeredSamplingFluctuation Omega p B)
          ≤ Cfixed * Real.sqrt (L * nR * A) * entrySupNorm B := hcsf
        _ ≤ _ := mul_le_mul_of_nonneg_left hB hscale_nonneg
    calc spectralNorm Y
        = spectralNorm (centeredSamplingFluctuation Omega p B) := hYnorm
      _ ≤ Cfixed * Real.sqrt (L * nR * A) *
          (Ccoef *
            (Real.sqrt (L₂ * A) *
                (Real.sqrt (μ₀ * (r : ℝ) / mnR) *
                  (Real.sqrt (L₄ * A) *
                      (μ₀ * Real.sqrt (r : ℝ) *
                        Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                        Real.sqrt (μ₀ * (r : ℝ) / mnR)) +
                    (L₄ * A) *
                      (μ₀ * Real.sqrt (r : ℝ) *
                        Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                        (μ₀ * (r : ℝ) / mnR)))) +
              (L₂ * A) *
                ((μ₀ * (r : ℝ) / mnR) *
                  (Real.sqrt (L₄ * A) *
                      (μ₀ * Real.sqrt (r : ℝ) *
                        Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                        Real.sqrt (μ₀ * (r : ℝ) / mnR)) +
                    (L₄ * A) *
                      (μ₀ * Real.sqrt (r : ℝ) *
                        Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                        (μ₀ * (r : ℝ) / mnR)))))) := h1
      _ = (Cfixed * Ccoef) *
          (Real.sqrt (L * nR * A) *
            (Real.sqrt (L₂ * A) *
                (Real.sqrt (μ₀ * (r : ℝ) / mnR) *
                  (Real.sqrt (L₄ * A) *
                      (μ₀ * Real.sqrt (r : ℝ) *
                        Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                        Real.sqrt (μ₀ * (r : ℝ) / mnR)) +
                    (L₄ * A) *
                      (μ₀ * Real.sqrt (r : ℝ) *
                        Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                        (μ₀ * (r : ℝ) / mnR)))) +
              (L₂ * A) *
                ((μ₀ * (r : ℝ) / mnR) *
                  (Real.sqrt (L₄ * A) *
                      (μ₀ * Real.sqrt (r : ℝ) *
                        Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                        Real.sqrt (μ₀ * (r : ℝ) / mnR)) +
                    (L₄ * A) *
                      (μ₀ * Real.sqrt (r : ℝ) *
                        Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                        (μ₀ * (r : ℝ) / mnR)))))) := by ring
      _ ≤ (Cfixed * Ccoef) * (36 * Real.rpow lam (-((3 : ℝ) / 2))) :=
          mul_le_mul_of_nonneg_left hscalar
            (mul_nonneg (le_of_lt hCf) (le_of_lt hCc))
      _ = 36 * (Cfixed * Ccoef) * Real.rpow lam (-((3 : ℝ) / 2)) := by ring
