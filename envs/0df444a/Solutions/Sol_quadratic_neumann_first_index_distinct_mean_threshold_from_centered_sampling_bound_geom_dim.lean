-- Prove2me | solution 1 for quadratic_neumann_first_index_distinct_mean_threshold_from_centered_sampling_bound_geom_dim
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-07-04T13:19:32.094984+00:00
-- url     : https://prove2.me/submissions/f7e4c7aa-9c4b-4998-8917-deec6f88212e

import Definitions.Def_matrix_completion_neumann
import Mathlib.Analysis.Complex.ExponentialBounds

open MatrixCompletion

/-- H2: geometric-scale deterministic threshold for the mean part of the
`ω₁ ≠ ω₂ = ω₃` quadratic term. -/
theorem solution
    (Cfixed Ccoef : ℝ) :
    0 < Cfixed → 0 < Ccoef →
    ∃ Cthreshold : ℝ, 0 < Cthreshold ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ → 1 ≤ μ₀ → A0 S μ₀ →
        (m : ℝ) ≥ lam * Real.rpow μ₀ ((4 : ℝ) / 3) * (↑(max n₁ n₂)) *
          Real.rpow (r : ℝ) ((4 : ℝ) / 3) * (β * Real.log (↑(max n₁ n₂))) →
        ∀ Omega : Finset (Fin n₁ × Fin n₂),
        quadraticNeumannFirstIndexDistinctMeanContribution Omega S
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) =
          (1 - ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) •
            centeredSamplingFluctuation Omega ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (quadraticFirstIndexDistinctMeanCoefficientMatrix S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) →
        entrySupNorm (quadraticFirstIndexDistinctMeanCoefficientMatrix S
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
          Ccoef * (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) *
            (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) *
              (μ₀ * (r : ℝ) / Real.sqrt ((n₁ : ℝ) * (n₂ : ℝ))) *
                (1 + μ₀ * (r : ℝ) / (↑(min n₁ n₂))) →
        CenteredSamplingSpectralBound Omega ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (quadraticFirstIndexDistinctMeanCoefficientMatrix S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))
            (Cfixed * Real.sqrt
              ((β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              entrySupNorm (quadraticFirstIndexDistinctMeanCoefficientMatrix S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))) →
        spectralNorm (quadraticNeumannFirstIndexDistinctMeanContribution Omega S
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
          Cthreshold * Real.rpow lam (-((3 : ℝ) / 2)) := by
  intro hCf hCc
  -- small-context scalar helpers
  have one_le_mul' : ∀ {a b : ℝ}, 1 ≤ a → 1 ≤ b → 1 ≤ a * b := by
    intro a b ha hb
    calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
      _ ≤ a * b := mul_le_mul ha hb zero_le_one (le_trans zero_le_one ha)
  -- x^{4/3} · √(x^{4/3}) = x² for x > 0 (exact exponent bookkeeping)
  have rpow43_sq : ∀ x : ℝ, 0 < x →
      Real.rpow x ((4 : ℝ) / 3) * Real.sqrt (Real.rpow x ((4 : ℝ) / 3)) = x ^ 2 := by
    intro x hx0
    have hnot : Real.rpow x ((4 : ℝ) / 3) = x ^ ((4 : ℝ) / 3) := rfl
    rw [hnot]
    have hs : Real.sqrt (x ^ ((4 : ℝ) / 3)) = x ^ ((2 : ℝ) / 3) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (le_of_lt hx0)]
      norm_num
    rw [hs, ← Real.rpow_add hx0]
    rw [show ((4 : ℝ) / 3 + 2 / 3) = ((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
  -- x ≤ x^{4/3} for x ≥ 1
  have le_rpow43 : ∀ x : ℝ, 1 ≤ x → x ≤ Real.rpow x ((4 : ℝ) / 3) := by
    intro x hx1
    calc x = Real.rpow x 1 := (Real.rpow_one x).symm
      _ ≤ Real.rpow x ((4 : ℝ) / 3) :=
          Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  refine ⟨2 * Cfixed * Ccoef, by positivity, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m M μ₀ S hn₁ hn₂ hr hm hμ₀ hA0 hsample Omega
    hid hB hcsf
  have hlam0 : (0 : ℝ) < lam := lt_of_lt_of_le one_pos hlam
  have hrpowlam : (0 : ℝ) < Real.rpow lam (-((3 : ℝ) / 2)) :=
    Real.rpow_pos_of_pos hlam0 _
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
  have hcsf_nonneg : 0 ≤ spectralNorm (centeredSamplingFluctuation Omega p
      (quadraticFirstIndexDistinctMeanCoefficientMatrix S p)) := by
    unfold spectralNorm; exact norm_nonneg _
  have hYnorm : spectralNorm
      (quadraticNeumannFirstIndexDistinctMeanContribution Omega S p) =
      |1 - p| * spectralNorm (centeredSamplingFluctuation Omega p
        (quadraticFirstIndexDistinctMeanCoefficientMatrix S p)) := by
    rw [hid, hsmul]
  unfold CenteredSamplingSpectralBound at hcsf
  by_cases hmax1 : max n₁ n₂ = 1
  · -- degenerate case: n₁ = n₂ = 1, the log factor vanishes
    have hlog0 : Real.log (↑(max n₁ n₂) : ℝ) = 0 := by
      rw [hmax1]; simp
    have hbound0 : Cfixed * Real.sqrt
        ((β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂))) / p) *
        entrySupNorm (quadraticFirstIndexDistinctMeanCoefficientMatrix S p) = 0 := by
      rw [hlog0]
      simp
    have hzero : spectralNorm (centeredSamplingFluctuation Omega p
        (quadraticFirstIndexDistinctMeanCoefficientMatrix S p)) = 0 := by
      rw [hbound0] at hcsf
      exact le_antisymm hcsf hcsf_nonneg
    rw [hYnorm, hzero, mul_zero]
    positivity
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
    -- exact square identities
    have hU2 : U * Real.sqrt U = μ₀ ^ 2 := by
      rw [hU_def]; exact rpow43_sq μ₀ hμ₀0
    have hV2 : V * Real.sqrt V = (r : ℝ) ^ 2 := by
      rw [hV_def]; exact rpow43_sq (r : ℝ) hrR0
    have hμU : μ₀ ≤ U := by rw [hU_def]; exact le_rpow43 μ₀ hμ₀
    have hrV : (r : ℝ) ≤ V := by rw [hV_def]; exact le_rpow43 (r : ℝ) hrR1
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
    -- the coefficient scales
    obtain ⟨t, ht_def⟩ : ∃ x : ℝ, x = μ₀ * (r : ℝ) / mnR := ⟨_, rfl⟩
    obtain ⟨g, hg_def⟩ : ∃ x : ℝ, x = μ₀ * (r : ℝ) / Real.sqrt ((n₁ : ℝ) * (n₂ : ℝ)) :=
      ⟨_, rfl⟩
    have hsqrtn12 : (0 : ℝ) < Real.sqrt ((n₁ : ℝ) * (n₂ : ℝ)) :=
      Real.sqrt_pos.mpr (mul_pos hn₁R hn₂R)
    have ht0 : (0 : ℝ) < t := by
      rw [ht_def]; exact div_pos (mul_pos hμ₀0 hrR0) hmnR0
    have hg0 : (0 : ℝ) < g := by
      rw [hg_def]; exact div_pos (mul_pos hμ₀0 hrR0) hsqrtn12
    -- t ≤ 1: mnR ≥ lam·U·V·L ≥ μ₀·r
    have hmnR_ge : lam * U * V * L ≤ mnR := by
      have h1 : (lam * U * V * L) * nR ≤ mnR * nR := by
        calc (lam * U * V * L) * nR = lam * U * nR * V * L := by ring
          _ ≤ (m : ℝ) := hsample
          _ ≤ (n₁ : ℝ) * (n₂ : ℝ) := by
              calc (m : ℝ) ≤ ((n₁ * n₂ : ℕ) : ℝ) := by exact_mod_cast hm
                _ = (n₁ : ℝ) * (n₂ : ℝ) := by push_cast; ring
          _ = nR * mnR := hmaxmin.symm
          _ = mnR * nR := by ring
      exact le_of_mul_le_mul_right h1 hnR0
    have hμr_le : μ₀ * (r : ℝ) ≤ lam * U * V * L := by
      calc μ₀ * (r : ℝ) ≤ U * V :=
            mul_le_mul hμU hrV (le_of_lt hrR0) (le_of_lt hU0)
        _ = 1 * (U * V) * 1 := by ring
        _ ≤ lam * (U * V) * L := by
            refine mul_le_mul (mul_le_mul_of_nonneg_right hlam ?_) hL1 zero_le_one ?_
            · exact le_of_lt (mul_pos hU0 hV0)
            · exact mul_nonneg (le_of_lt hlam0) (le_of_lt (mul_pos hU0 hV0))
        _ = lam * U * V * L := by ring
    have ht_le1 : t ≤ 1 := by
      rw [ht_def, div_le_one hmnR0]
      exact le_trans hμr_le hmnR_ge
    have h1t_le2 : 1 + t ≤ 2 := by linarith
    -- rewrite the coefficient bound with opaque scales
    have hB' : entrySupNorm (quadraticFirstIndexDistinctMeanCoefficientMatrix S p) ≤
        Ccoef * A * t * g * (1 + t) := by
      refine hB.trans_eq ?_
      rw [hA_def, ht_def, hg_def]
    -- rewrite the sqrt argument
    have hsqrt_arg : (β * nR * Real.log nR) / p = L * nR * A := by
      rw [hL_def, hA_def, div_eq_mul_inv]; ring
    -- norm chain
    have hEsup_nonneg : 0 ≤ entrySupNorm
        (quadraticFirstIndexDistinctMeanCoefficientMatrix S p) := by
      have h := hcsf_nonneg
      by_contra hneg
      rw [not_le] at hneg
      have hb0 : Cfixed * Real.sqrt ((β * nR * Real.log nR) / p) *
          entrySupNorm (quadraticFirstIndexDistinctMeanCoefficientMatrix S p) < 0 := by
        have hCs : (0 : ℝ) < Cfixed * Real.sqrt ((β * nR * Real.log nR) / p) := by
          apply mul_pos hCf
          apply Real.sqrt_pos.mpr
          rw [hsqrt_arg]
          exact mul_pos (mul_pos hL0 hnR0) hA0
        exact mul_neg_of_pos_of_neg hCs hneg
      exact absurd (lt_of_le_of_lt (le_trans h hcsf) hb0) (lt_irrefl _)
    have habs1p : |1 - p| ≤ 1 := by
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - p)]
      linarith
    have hchain : spectralNorm
        (quadraticNeumannFirstIndexDistinctMeanContribution Omega S p) ≤
        Cfixed * Real.sqrt (L * nR * A) * (Ccoef * A * t * g * 2) := by
      rw [hYnorm]
      have h1 : spectralNorm (centeredSamplingFluctuation Omega p
          (quadraticFirstIndexDistinctMeanCoefficientMatrix S p)) ≤
          Cfixed * Real.sqrt (L * nR * A) * (Ccoef * A * t * g * 2) := by
        calc spectralNorm (centeredSamplingFluctuation Omega p
              (quadraticFirstIndexDistinctMeanCoefficientMatrix S p))
            ≤ Cfixed * Real.sqrt ((β * nR * Real.log nR) / p) *
              entrySupNorm (quadraticFirstIndexDistinctMeanCoefficientMatrix S p) :=
              hcsf
          _ = Cfixed * Real.sqrt (L * nR * A) *
              entrySupNorm (quadraticFirstIndexDistinctMeanCoefficientMatrix S p) := by
              rw [hsqrt_arg]
          _ ≤ Cfixed * Real.sqrt (L * nR * A) * (Ccoef * A * t * g * (1 + t)) := by
              apply mul_le_mul_of_nonneg_left hB'
              exact mul_nonneg (le_of_lt hCf) (Real.sqrt_nonneg _)
          _ ≤ Cfixed * Real.sqrt (L * nR * A) * (Ccoef * A * t * g * 2) := by
              apply mul_le_mul_of_nonneg_left
              · apply mul_le_mul_of_nonneg_left h1t_le2
                have : (0 : ℝ) ≤ Ccoef * A * t * g := by
                  exact mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt hCc)
                    (le_of_lt hA0)) (le_of_lt ht0)) (le_of_lt hg0)
                exact this
              · exact mul_nonneg (le_of_lt hCf) (Real.sqrt_nonneg _)
      calc |1 - p| * spectralNorm (centeredSamplingFluctuation Omega p
            (quadraticFirstIndexDistinctMeanCoefficientMatrix S p))
          ≤ 1 * spectralNorm (centeredSamplingFluctuation Omega p
            (quadraticFirstIndexDistinctMeanCoefficientMatrix S p)) :=
            mul_le_mul_of_nonneg_right habs1p hcsf_nonneg
        _ = spectralNorm (centeredSamplingFluctuation Omega p
            (quadraticFirstIndexDistinctMeanCoefficientMatrix S p)) := one_mul _
        _ ≤ Cfixed * Real.sqrt (L * nR * A) * (Ccoef * A * t * g * 2) := h1
    -- scalar absorption: √(L·nR·A)·A·t·g ≤ lam^{-3/2}
    have hscalar : Real.sqrt (L * nR * A) * (A * t * g) ≤
        Real.rpow lam (-((3 : ℝ) / 2)) := by
      -- monotone in A ≤ D
      have hsA : (0 : ℝ) ≤ Real.sqrt A := Real.sqrt_nonneg _
      have hsK : (0 : ℝ) < Real.sqrt K := Real.sqrt_pos.mpr hK0
      have hsmn : (0 : ℝ) < Real.sqrt mnR := Real.sqrt_pos.mpr hmnR0
      have hsnR : (0 : ℝ) < Real.sqrt nR := Real.sqrt_pos.mpr hnR0
      have hslam : (0 : ℝ) < Real.sqrt lam := Real.sqrt_pos.mpr hlam0
      have hsU : (0 : ℝ) < Real.sqrt U := Real.sqrt_pos.mpr hU0
      have hsV : (0 : ℝ) < Real.sqrt V := Real.sqrt_pos.mpr hV0
      have hsL : (0 : ℝ) < Real.sqrt L := Real.sqrt_pos.mpr hL0
      have hmono : Real.sqrt (L * nR * A) * (A * t * g) ≤
          Real.sqrt (L * nR * D) * (D * t * g) := by
        have h1 : Real.sqrt (L * nR * A) ≤ Real.sqrt (L * nR * D) := by
          apply Real.sqrt_le_sqrt
          exact mul_le_mul_of_nonneg_left hA_le_D
            (le_of_lt (mul_pos hL0 hnR0))
        have h2 : A * t * g ≤ D * t * g := by
          apply mul_le_mul_of_nonneg_right _ (le_of_lt hg0)
          exact mul_le_mul_of_nonneg_right hA_le_D (le_of_lt ht0)
        exact mul_le_mul h1 h2
          (mul_nonneg (mul_nonneg (le_of_lt hA0) (le_of_lt ht0)) (le_of_lt hg0))
          (Real.sqrt_nonneg _)
      refine hmono.trans ?_
      -- exact simplification at A = D
      have hsimp : Real.sqrt (L * nR * D) * (D * t * g) =
          Real.sqrt L * (μ₀ ^ 2 * (r : ℝ) ^ 2) / (K * Real.sqrt K) := by
        rw [hD_def, ht_def, hg_def]
        have hLnD : Real.sqrt (L * nR * (mnR / K)) =
            Real.sqrt L * Real.sqrt ((n₁ : ℝ) * (n₂ : ℝ)) / Real.sqrt K := by
          rw [show L * nR * (mnR / K) = L * ((n₁ : ℝ) * (n₂ : ℝ)) / K by
              rw [← hmaxmin]; ring,
            Real.sqrt_div' (L * ((n₁ : ℝ) * (n₂ : ℝ))) (le_of_lt hK0),
            Real.sqrt_mul (le_of_lt hL0)]
        rw [hLnD]
        field_simp
        try ring
      rw [hsimp]
      -- final comparison
      have hrpow_expand : Real.rpow lam (-((3 : ℝ) / 2)) =
          1 / (lam * Real.sqrt lam) := by
        rw [show Real.rpow lam (-((3 : ℝ) / 2)) = lam ^ (-((3 : ℝ) / 2)) from rfl,
          Real.rpow_neg (le_of_lt hlam0), one_div]
        congr 1
        have h32 : ((3 : ℝ) / 2) = 1 + 1 / 2 := by norm_num
        rw [h32, Real.rpow_add hlam0, Real.rpow_one, ← Real.sqrt_eq_rpow]
      rw [hrpow_expand,
        div_le_div_iff₀ (mul_pos hK0 hsK) (mul_pos hlam0 hslam), one_mul]
      -- goal: √L·μ₀²·r²·(lam·√lam) ≤ K·√K
      have hsqrtK : Real.sqrt K = Real.sqrt lam * Real.sqrt U * Real.sqrt V *
          Real.sqrt L := by
        rw [hK_def,
          Real.sqrt_mul (mul_nonneg (mul_nonneg (le_of_lt hlam0) (le_of_lt hU0))
            (le_of_lt hV0)),
          Real.sqrt_mul (mul_nonneg (le_of_lt hlam0) (le_of_lt hU0)),
          Real.sqrt_mul (le_of_lt hlam0)]
      have hfacpos : (0 : ℝ) ≤ (lam * Real.sqrt lam) * (U * Real.sqrt U) *
          (V * Real.sqrt V) * Real.sqrt L := by
        have e1 : (0 : ℝ) ≤ lam * Real.sqrt lam :=
          mul_nonneg (le_of_lt hlam0) (le_of_lt hslam)
        have e2 : (0 : ℝ) ≤ U * Real.sqrt U :=
          mul_nonneg (le_of_lt hU0) (le_of_lt hsU)
        have e3 : (0 : ℝ) ≤ V * Real.sqrt V :=
          mul_nonneg (le_of_lt hV0) (le_of_lt hsV)
        exact mul_nonneg (mul_nonneg (mul_nonneg e1 e2) e3) (le_of_lt hsL)
      calc Real.sqrt L * (μ₀ ^ 2 * (r : ℝ) ^ 2) * (lam * Real.sqrt lam)
          = ((lam * Real.sqrt lam) * (U * Real.sqrt U) * (V * Real.sqrt V) *
              Real.sqrt L) * 1 := by
            rw [← hU2, ← hV2]; ring
        _ ≤ ((lam * Real.sqrt lam) * (U * Real.sqrt U) * (V * Real.sqrt V) *
              Real.sqrt L) * L := mul_le_mul_of_nonneg_left hL1 hfacpos
        _ = K * Real.sqrt K := by
            rw [hsqrtK, hK_def]; ring
    -- combine
    calc spectralNorm (quadraticNeumannFirstIndexDistinctMeanContribution Omega S p)
        ≤ Cfixed * Real.sqrt (L * nR * A) * (Ccoef * A * t * g * 2) := hchain
      _ = (2 * Cfixed * Ccoef) * (Real.sqrt (L * nR * A) * (A * t * g)) := by
          ring
      _ ≤ (2 * Cfixed * Ccoef) * Real.rpow lam (-((3 : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_left hscalar (by positivity)
