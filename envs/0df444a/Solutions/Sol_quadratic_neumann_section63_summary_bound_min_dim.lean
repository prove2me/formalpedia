-- Prove2me | solution 1 for quadratic_neumann_section63_summary_bound_min_dim
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-01T10:43:36.326821+00:00
-- url     : https://prove2.me/submissions/90c49567-f7be-4ca3-acb2-344d64638249

import Theorems.Thm_quadratic_neumann_section63_all_equal_case_bound_under_general_sample_bound
import Theorems.Thm_quadratic_neumann_section63_first_index_distinct_case_bound_min_dim
import Theorems.Thm_quadratic_neumann_section63_middle_index_distinct_case_bound_under_general_sample_bound
import Theorems.Thm_quadratic_neumann_section63_last_index_distinct_case_bound_under_general_sample_bound
import Theorems.Thm_quadratic_neumann_section63_all_distinct_case_bound_under_general_sample_bound
import Theorems.Thm_second_neumann_certificate_term_spectral_norm_le_index_partition_sum
import Theorems.Thm_bernoulli_finite_index_intersection_probability_from_pointwise_bounds
import Theorems.Thm_bernoulli_event_probability_mono
import Theorems.Thm_neumann_certificate_term_spectral_bound_mono
import Theorems.Thm_sample_ratio_between_zero_and_one
import Mathlib.Tactic

set_option maxHeartbeats 3200000

open MatrixCompletion

/-!
Source: Candès–Recht 2008, Section 6.3, PDF pp. 30--34, the five-way split (6.20)
and the summary display on PDF p. 34, stated at the **corrected rectangular**
five-term scale `Φ + t₅`.

Assembles the §6.3 summary estimate for the second Neumann correction from the five
index-partition case bounds:
* the corrected first-index-distinct case
  (`..._first_index_distinct_case_bound_min_dim`) at the five-term scale `Φ + t₅`;
* the other four cases (all-equal, middle/last-index-distinct, all-distinct) at the
  four-term `Φ`, lifted to `Φ + t₅` by monotonicity (`t₅ ≥ 0`).

Mechanism identical to the `..._summary_bound_under_general_sample_bound` assembly,
but at the sound rectangular scale so the whole §6.3 mean/centered chain of the
first case closes (routing the mean part through the honest Lemma-6.8 `r/min`
coefficient instead of the false `N`-only stub).
-/

private lemma spectralNorm_add_le
    {n₁ n₂ : ℕ} (X Y : Matrix (Fin n₁) (Fin n₂) ℝ) :
    spectralNorm (X + Y) ≤ spectralNorm X + spectralNorm Y := by
  unfold spectralNorm
  have hlin :
      LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (X + Y)) =
        LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin X) +
          LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin Y) := by
    ext v i
    simp [Matrix.toEuclideanLin]
  rw [hlin]
  exact norm_add_le _ _

set_option maxHeartbeats 3200000 in
theorem solution :
    ∃ Csec csec : ℝ, 0 < Csec ∧ 0 < csec ∧
      ∀ C' : ℝ, Csec ≤ C' →
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
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              NeumannCertificateTermSpectralBound Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) 2
                (let N : ℝ := ↑(max n₁ n₂)
                 let R : ℝ := (r : ℝ)
                 let Mobs : ℝ := (m : ℝ)
                 let logN : ℝ := Real.log N
                 Csec *
                   ((μ₀ ^ 2 * μ₁) *
                      Real.sqrt ((N * R * (β * logN)) / Mobs) *
                        ((N * R) / Mobs) ^ 2 +
                    μ₀ ^ 2 * ((N * R) / Mobs) ^ 2 +
                    Real.sqrt (β * logN) *
                        Real.rpow ((N * R) / Mobs) ((3 : ℝ) / 2) *
                          (μ₀ ^ 2 * R) +
                    Real.rpow
                      ((μ₀ * μ₁ * N * R * (β * logN)) / Mobs)
                      ((3 : ℝ) / 2) +
                    Real.sqrt (β * logN) * μ₀ ^ 2 *
                        Real.rpow ((N * R) / Mobs) ((3 : ℝ) / 2) *
                          Real.sqrt ((N * R) / (↑(min n₁ n₂)))))) ≥
          1 - csec * Real.rpow (↑(max n₁ n₂)) (-β) := by
  obtain ⟨C0, c0, hC0, hc0, H0⟩ :=
    quadratic_neumann_section63_all_equal_case_bound_under_general_sample_bound
  obtain ⟨C1, c1, hC1, hc1, H1⟩ :=
    quadratic_neumann_section63_first_index_distinct_case_bound_min_dim
  obtain ⟨C2, c2, hC2, hc2, H2⟩ :=
    quadratic_neumann_section63_middle_index_distinct_case_bound_under_general_sample_bound
  obtain ⟨C3, c3, hC3, hc3, H3⟩ :=
    quadratic_neumann_section63_last_index_distinct_case_bound_under_general_sample_bound
  obtain ⟨C4, c4, hC4, hc4, H4⟩ :=
    quadratic_neumann_section63_all_distinct_case_bound_under_general_sample_bound
  set Cmax : ℝ := max (max (max C0 C1) (max C2 C3)) C4 with hCmax
  set cmax : ℝ := max (max (max c0 c1) (max c2 c3)) c4 with hcmax
  have hCmax_pos : 0 < Cmax := by
    have : C0 ≤ Cmax := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)
    linarith
  have hcmax_pos : 0 < cmax := by
    have : c0 ≤ cmax := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)
    linarith
  refine ⟨5 * Cmax, 5 * cmax, by positivity, by positivity, ?_⟩
  intro C' hC' β hβ n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
  set N : ℝ := (↑(max n₁ n₂) : ℝ) with hN
  set R : ℝ := (r : ℝ) with hR
  set Mobs : ℝ := (m : ℝ) with hMobs
  set logN : ℝ := Real.log N with hlogN
  -- the plain four-term scale Φ₄
  set Φ4 : ℝ :=
    ((μ₀ ^ 2 * μ₁) *
        Real.sqrt ((N * R * (β * logN)) / Mobs) * ((N * R) / Mobs) ^ 2 +
      μ₀ ^ 2 * ((N * R) / Mobs) ^ 2 +
      Real.sqrt (β * logN) *
          Real.rpow ((N * R) / Mobs) ((3 : ℝ) / 2) * (μ₀ ^ 2 * R) +
      Real.rpow ((μ₀ * μ₁ * N * R * (β * logN)) / Mobs) ((3 : ℝ) / 2)) with hΦ4
  -- the fifth min-aware term t₅ ≥ 0
  set t5 : ℝ :=
    Real.sqrt (β * logN) * μ₀ ^ 2 *
      Real.rpow ((N * R) / Mobs) ((3 : ℝ) / 2) *
        Real.sqrt ((N * R) / (↑(min n₁ n₂))) with ht5
  -- the corrected five-term scale Φ = Φ₄ + t₅
  set Φ : ℝ := Φ4 + t5 with hΦ
  set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp
  have hN_nat : 0 < max n₁ n₂ := lt_of_lt_of_le hn₁ (Nat.le_max_left n₁ n₂)
  have hN_pos : 0 < N := by rw [hN]; exact_mod_cast hN_nat
  have hR_pos : 0 < R := by rw [hR]; exact_mod_cast hr
  have hMobs_nonneg : 0 ≤ Mobs := by rw [hMobs]; positivity
  have hmn_pos : 0 < ((min n₁ n₂ : ℕ) : ℝ) := by
    have : 0 < min n₁ n₂ := lt_min hn₁ hn₂; exact_mod_cast this
  have ht5_nonneg : 0 ≤ t5 := by
    rw [ht5]
    have hbaseM_nonneg : 0 ≤ (N * R) / Mobs := by positivity
    have := Real.rpow_nonneg hbaseM_nonneg ((3:ℝ)/2)
    have h2 := Real.sqrt_nonneg ((N * R) / (↑(min n₁ n₂)))
    positivity
  have hΦ4_nonneg : (0 : ℝ) ≤ Φ4 := by
    have hNR : (0 : ℝ) ≤ N * R := by apply mul_nonneg <;> positivity
    have h1 : (0 : ℝ) ≤ (μ₀ ^ 2 * μ₁) *
        Real.sqrt ((N * R * (β * logN)) / Mobs) * ((N * R) / Mobs) ^ 2 := by
      apply mul_nonneg; apply mul_nonneg
      · positivity
      · exact Real.sqrt_nonneg _
      · positivity
    have h2 : (0 : ℝ) ≤ μ₀ ^ 2 * ((N * R) / Mobs) ^ 2 := by positivity
    have h3 : (0 : ℝ) ≤ Real.sqrt (β * logN) *
        Real.rpow ((N * R) / Mobs) ((3 : ℝ) / 2) * (μ₀ ^ 2 * R) := by
      apply mul_nonneg; apply mul_nonneg
      · exact Real.sqrt_nonneg _
      · exact Real.rpow_nonneg (by positivity) _
      · positivity
    have h4 : (0 : ℝ) ≤ Real.rpow ((μ₀ * μ₁ * N * R * (β * logN)) / Mobs) ((3 : ℝ) / 2) :=
      Real.rpow_nonneg (by positivity) _
    rw [hΦ4]; linarith
  have hΦ_nonneg : (0 : ℝ) ≤ Φ := by rw [hΦ]; linarith
  have hΦ4_le_Φ : Φ4 ≤ Φ := by rw [hΦ]; linarith
  obtain ⟨hp0, hp1⟩ := sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm
  have hfail : (0 : ℝ) ≤ Real.rpow (↑(max n₁ n₂)) (-β) := Real.rpow_nonneg (by positivity) _
  have hC0_le : C0 ≤ Cmax := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)
  have hC1_le : C1 ≤ Cmax := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
  have hC2_le : C2 ≤ Cmax := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)
  have hC3_le : C3 ≤ Cmax := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)
  have hC4_le : C4 ≤ Cmax := le_max_right _ _
  have hc0_le : c0 ≤ cmax := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)
  have hc1_le : c1 ≤ cmax := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
  have hc2_le : c2 ≤ cmax := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)
  have hc3_le : c3 ≤ cmax := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)
  have hc4_le : c4 ≤ cmax := le_max_right _ _
  have hC'0 : C0 ≤ C' := le_trans (le_trans hC0_le (by nlinarith [hCmax_pos])) hC'
  have hC'1 : C1 ≤ C' := le_trans (le_trans hC1_le (by nlinarith [hCmax_pos])) hC'
  have hC'2 : C2 ≤ C' := le_trans (le_trans hC2_le (by nlinarith [hCmax_pos])) hC'
  have hC'3 : C3 ≤ C' := le_trans (le_trans hC3_le (by nlinarith [hCmax_pos])) hC'
  have hC'4 : C4 ≤ C' := le_trans (le_trans hC4_le (by nlinarith [hCmax_pos])) hC'
  -- E0: all-equal case at plain Φ₄, lifted to Cmax·Φ
  have E0 :
      bernoulliEventProb p
          (fun Omega =>
            spectralNorm (quadraticNeumannAllEqualContribution Omega S p) ≤ Cmax * Φ) ≥
        1 - cmax * Real.rpow (↑(max n₁ n₂)) (-β) := by
    have hb := H0 C' hC'0 β hβ n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
    have hmono :
        bernoulliEventProb p
            (fun Omega =>
              spectralNorm (quadraticNeumannAllEqualContribution Omega S p) ≤ C0 * Φ4) ≤
          bernoulliEventProb p
            (fun Omega =>
              spectralNorm (quadraticNeumannAllEqualContribution Omega S p) ≤ Cmax * Φ) := by
      apply bernoulli_event_probability_mono p _ _ hp0 hp1
      intro Omega hle
      refine le_trans hle ?_
      calc C0 * Φ4 ≤ Cmax * Φ4 := mul_le_mul_of_nonneg_right hC0_le hΦ4_nonneg
        _ ≤ Cmax * Φ := mul_le_mul_of_nonneg_left hΦ4_le_Φ (le_of_lt hCmax_pos)
    have hb' :
        bernoulliEventProb p
            (fun Omega =>
              spectralNorm (quadraticNeumannAllEqualContribution Omega S p) ≤ C0 * Φ4) ≥
          1 - c0 * Real.rpow (↑(max n₁ n₂)) (-β) := by
      simpa only [hN, hR, hMobs, hlogN, hΦ4, hp] using hb
    have : (1 : ℝ) - cmax * Real.rpow (↑(max n₁ n₂)) (-β) ≤
        1 - c0 * Real.rpow (↑(max n₁ n₂)) (-β) := by nlinarith [hfail, hc0_le]
    linarith [le_trans hb' hmono, this]
  -- E1: corrected first case ALREADY at Φ = Φ₄ + t₅
  have E1 :
      bernoulliEventProb p
          (fun Omega =>
            spectralNorm (quadraticNeumannFirstIndexDistinctContribution Omega S p) ≤ Cmax * Φ) ≥
        1 - cmax * Real.rpow (↑(max n₁ n₂)) (-β) := by
    have hb := H1 C' hC'1 β hβ n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
    have hmono :
        bernoulliEventProb p
            (fun Omega =>
              spectralNorm (quadraticNeumannFirstIndexDistinctContribution Omega S p) ≤ C1 * Φ) ≤
          bernoulliEventProb p
            (fun Omega =>
              spectralNorm (quadraticNeumannFirstIndexDistinctContribution Omega S p) ≤ Cmax * Φ) := by
      apply bernoulli_event_probability_mono p _ _ hp0 hp1
      intro Omega hle
      exact le_trans hle (mul_le_mul_of_nonneg_right hC1_le hΦ_nonneg)
    have hb' :
        bernoulliEventProb p
            (fun Omega =>
              spectralNorm (quadraticNeumannFirstIndexDistinctContribution Omega S p) ≤ C1 * Φ) ≥
          1 - c1 * Real.rpow (↑(max n₁ n₂)) (-β) := by
      simpa only [hN, hR, hMobs, hlogN, hΦ, hΦ4, ht5, hp] using hb
    have : (1 : ℝ) - cmax * Real.rpow (↑(max n₁ n₂)) (-β) ≤
        1 - c1 * Real.rpow (↑(max n₁ n₂)) (-β) := by nlinarith [hfail, hc1_le]
    linarith [le_trans hb' hmono, this]
  -- E2: middle case at plain Φ₄, lifted
  have E2 :
      bernoulliEventProb p
          (fun Omega =>
            spectralNorm (quadraticNeumannMiddleIndexDistinctContribution Omega S p) ≤ Cmax * Φ) ≥
        1 - cmax * Real.rpow (↑(max n₁ n₂)) (-β) := by
    have hb := H2 C' hC'2 β hβ n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
    have hmono :
        bernoulliEventProb p
            (fun Omega =>
              spectralNorm (quadraticNeumannMiddleIndexDistinctContribution Omega S p) ≤ C2 * Φ4) ≤
          bernoulliEventProb p
            (fun Omega =>
              spectralNorm (quadraticNeumannMiddleIndexDistinctContribution Omega S p) ≤ Cmax * Φ) := by
      apply bernoulli_event_probability_mono p _ _ hp0 hp1
      intro Omega hle
      refine le_trans hle ?_
      calc C2 * Φ4 ≤ Cmax * Φ4 := mul_le_mul_of_nonneg_right hC2_le hΦ4_nonneg
        _ ≤ Cmax * Φ := mul_le_mul_of_nonneg_left hΦ4_le_Φ (le_of_lt hCmax_pos)
    have hb' :
        bernoulliEventProb p
            (fun Omega =>
              spectralNorm (quadraticNeumannMiddleIndexDistinctContribution Omega S p) ≤ C2 * Φ4) ≥
          1 - c2 * Real.rpow (↑(max n₁ n₂)) (-β) := by
      simpa only [hN, hR, hMobs, hlogN, hΦ4, hp] using hb
    have : (1 : ℝ) - cmax * Real.rpow (↑(max n₁ n₂)) (-β) ≤
        1 - c2 * Real.rpow (↑(max n₁ n₂)) (-β) := by nlinarith [hfail, hc2_le]
    linarith [le_trans hb' hmono, this]
  -- E3: last case at plain Φ₄, lifted
  have E3 :
      bernoulliEventProb p
          (fun Omega =>
            spectralNorm (quadraticNeumannLastIndexDistinctContribution Omega S p) ≤ Cmax * Φ) ≥
        1 - cmax * Real.rpow (↑(max n₁ n₂)) (-β) := by
    have hb := H3 C' hC'3 β hβ n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
    have hmono :
        bernoulliEventProb p
            (fun Omega =>
              spectralNorm (quadraticNeumannLastIndexDistinctContribution Omega S p) ≤ C3 * Φ4) ≤
          bernoulliEventProb p
            (fun Omega =>
              spectralNorm (quadraticNeumannLastIndexDistinctContribution Omega S p) ≤ Cmax * Φ) := by
      apply bernoulli_event_probability_mono p _ _ hp0 hp1
      intro Omega hle
      refine le_trans hle ?_
      calc C3 * Φ4 ≤ Cmax * Φ4 := mul_le_mul_of_nonneg_right hC3_le hΦ4_nonneg
        _ ≤ Cmax * Φ := mul_le_mul_of_nonneg_left hΦ4_le_Φ (le_of_lt hCmax_pos)
    have hb' :
        bernoulliEventProb p
            (fun Omega =>
              spectralNorm (quadraticNeumannLastIndexDistinctContribution Omega S p) ≤ C3 * Φ4) ≥
          1 - c3 * Real.rpow (↑(max n₁ n₂)) (-β) := by
      simpa only [hN, hR, hMobs, hlogN, hΦ4, hp] using hb
    have : (1 : ℝ) - cmax * Real.rpow (↑(max n₁ n₂)) (-β) ≤
        1 - c3 * Real.rpow (↑(max n₁ n₂)) (-β) := by nlinarith [hfail, hc3_le]
    linarith [le_trans hb' hmono, this]
  -- E4: all-distinct case at plain Φ₄, lifted
  have E4 :
      bernoulliEventProb p
          (fun Omega =>
            spectralNorm (quadraticNeumannAllDistinctContribution Omega S p) ≤ Cmax * Φ) ≥
        1 - cmax * Real.rpow (↑(max n₁ n₂)) (-β) := by
    have hb := H4 C' hC'4 β hβ n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
    have hmono :
        bernoulliEventProb p
            (fun Omega =>
              spectralNorm (quadraticNeumannAllDistinctContribution Omega S p) ≤ C4 * Φ4) ≤
          bernoulliEventProb p
            (fun Omega =>
              spectralNorm (quadraticNeumannAllDistinctContribution Omega S p) ≤ Cmax * Φ) := by
      apply bernoulli_event_probability_mono p _ _ hp0 hp1
      intro Omega hle
      refine le_trans hle ?_
      calc C4 * Φ4 ≤ Cmax * Φ4 := mul_le_mul_of_nonneg_right hC4_le hΦ4_nonneg
        _ ≤ Cmax * Φ := mul_le_mul_of_nonneg_left hΦ4_le_Φ (le_of_lt hCmax_pos)
    have hb' :
        bernoulliEventProb p
            (fun Omega =>
              spectralNorm (quadraticNeumannAllDistinctContribution Omega S p) ≤ C4 * Φ4) ≥
          1 - c4 * Real.rpow (↑(max n₁ n₂)) (-β) := by
      simpa only [hN, hR, hMobs, hlogN, hΦ4, hp] using hb
    have : (1 : ℝ) - cmax * Real.rpow (↑(max n₁ n₂)) (-β) ≤
        1 - c4 * Real.rpow (↑(max n₁ n₂)) (-β) := by nlinarith [hfail, hc4_le]
    linarith [le_trans hb' hmono, this]
  -- assemble the five events at the shared scale Cmax * Φ
  let Event : Fin 5 → Finset (Fin n₁ × Fin n₂) → Prop := fun i Omega =>
    match i with
    | 0 => spectralNorm (quadraticNeumannAllEqualContribution Omega S p) ≤ Cmax * Φ
    | 1 => spectralNorm (quadraticNeumannFirstIndexDistinctContribution Omega S p) ≤ Cmax * Φ
    | 2 => spectralNorm (quadraticNeumannMiddleIndexDistinctContribution Omega S p) ≤ Cmax * Φ
    | 3 => spectralNorm (quadraticNeumannLastIndexDistinctContribution Omega S p) ≤ Cmax * Φ
    | 4 => spectralNorm (quadraticNeumannAllDistinctContribution Omega S p) ≤ Cmax * Φ
  have hEventProb : ∀ i : Fin 5,
      bernoulliEventProb p (Event i) ≥
        1 - cmax * Real.rpow (↑(max n₁ n₂)) (-β) := by
    intro i
    fin_cases i
    · exact E0
    · exact E1
    · exact E2
    · exact E3
    · exact E4
  have hInter :=
    bernoulli_finite_index_intersection_probability_from_pointwise_bounds
      (ι := Fin 5) p cmax (Real.rpow (↑(max n₁ n₂)) (-β)) Event hp0 hp1 hEventProb
  rw [show (Fintype.card (Fin 5) : ℝ) = 5 by simp] at hInter
  have hStep :
      bernoulliEventProb p (fun Omega => ∀ i : Fin 5, Event i Omega) ≤
        bernoulliEventProb p
          (fun Omega =>
            NeumannCertificateTermSpectralBound Omega S p 2 ((5 * Cmax) * Φ)) := by
    apply bernoulli_event_probability_mono p _ _ hp0 hp1
    intro Omega hall
    have h0 := hall 0
    have h1 := hall 1
    have h2 := hall 2
    have h3 := hall 3
    have h4 := hall 4
    simp only [Event] at h0 h1 h2 h3 h4
    have htri :=
      second_neumann_certificate_term_spectral_norm_le_index_partition_sum S Omega p
    have hsub :
        spectralNorm
          ((((quadraticNeumannAllEqualContribution Omega S p +
            quadraticNeumannFirstIndexDistinctContribution Omega S p) +
            quadraticNeumannMiddleIndexDistinctContribution Omega S p) +
            quadraticNeumannLastIndexDistinctContribution Omega S p) +
            quadraticNeumannAllDistinctContribution Omega S p) ≤
          spectralNorm (quadraticNeumannAllEqualContribution Omega S p) +
          spectralNorm (quadraticNeumannFirstIndexDistinctContribution Omega S p) +
          spectralNorm (quadraticNeumannMiddleIndexDistinctContribution Omega S p) +
          spectralNorm (quadraticNeumannLastIndexDistinctContribution Omega S p) +
          spectralNorm (quadraticNeumannAllDistinctContribution Omega S p) := by
      refine le_trans (spectralNorm_add_le _ _) ?_
      have hA := spectralNorm_add_le
        ((quadraticNeumannAllEqualContribution Omega S p +
            quadraticNeumannFirstIndexDistinctContribution Omega S p) +
            quadraticNeumannMiddleIndexDistinctContribution Omega S p)
        (quadraticNeumannLastIndexDistinctContribution Omega S p)
      have hB := spectralNorm_add_le
        (quadraticNeumannAllEqualContribution Omega S p +
            quadraticNeumannFirstIndexDistinctContribution Omega S p)
        (quadraticNeumannMiddleIndexDistinctContribution Omega S p)
      have hC := spectralNorm_add_le
        (quadraticNeumannAllEqualContribution Omega S p)
        (quadraticNeumannFirstIndexDistinctContribution Omega S p)
      linarith
    have hbound :
        spectralNorm (neumannCertificateTerm Omega S p 2) ≤ (5 * Cmax) * Φ := by
      have := le_trans htri hsub
      have h5 :
          spectralNorm (quadraticNeumannAllEqualContribution Omega S p) +
          spectralNorm (quadraticNeumannFirstIndexDistinctContribution Omega S p) +
          spectralNorm (quadraticNeumannMiddleIndexDistinctContribution Omega S p) +
          spectralNorm (quadraticNeumannLastIndexDistinctContribution Omega S p) +
          spectralNorm (quadraticNeumannAllDistinctContribution Omega S p) ≤
            (5 * Cmax) * Φ := by
        have hexp : (5 * Cmax) * Φ =
            Cmax * Φ + Cmax * Φ + Cmax * Φ + Cmax * Φ + Cmax * Φ := by ring
        rw [hexp]; linarith [h0, h1, h2, h3, h4]
      exact le_trans this h5
    exact hbound
  have hfinal :
      bernoulliEventProb p
          (fun Omega =>
            NeumannCertificateTermSpectralBound Omega S p 2 ((5 * Cmax) * Φ)) ≥
        1 - (5 * cmax) * Real.rpow (↑(max n₁ n₂)) (-β) := by
    have := le_trans hInter hStep
    linarith [this]
  show bernoulliEventProb p
      (fun Omega =>
        NeumannCertificateTermSpectralBound Omega S p 2 ((5 * Cmax) * Φ)) ≥
    1 - (5 * cmax) * Real.rpow (↑(max n₁ n₂)) (-β)
  exact hfinal
