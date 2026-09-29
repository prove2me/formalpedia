-- Prove2me | solution 1 for quadratic_neumann_section63_first_index_distinct_centered_case_bound_min_dim
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-01T10:30:20.653898+00:00
-- url     : https://prove2.me/submissions/01bd6d0a-4875-44be-b47f-a515e82f5009

import Theorems.Thm_quadratic_neumann_section63_first_index_distinct_centered_case_bound_under_general_sample_bound
import Theorems.Thm_bernoulli_event_probability_mono
import Theorems.Thm_sample_ratio_between_zero_and_one
import Mathlib.Tactic

open MatrixCompletion

/-!
Source: Candès–Recht 2008, Section 6.3, PDF pp. 31--32, the centered part `S₁`
(Lemma 6.7) of the `ω₁ ≠ ω₂ = ω₃` case, transported to the corrected rectangular
five-term §6.3 summary scale `Φ + t₅`.

The existing centered case bound
(`..._first_index_distinct_centered_case_bound_under_general_sample_bound`, `S₁`
by Lemma 6.7) already gives, on a high-probability event,
`spectralNorm(Centered) ≤ Ccent · Φ` at the four-term `N`-only scale `Φ`.  Since
the corrected scale adds only the nonnegative fifth term
`t₅ = √(βlogN)·μ₀²·((N R)/M)^{3/2}·√((N R)/min) ≥ 0`, we have `Φ ≤ Φ + t₅`, so the
same event witnesses the bound at `Ccent · (Φ + t₅)` by monotonicity of the
pointwise bound (`bernoulli_event_probability_mono`).  No new analytic content: the
Bernstein-chaos content of `S₁` remains isolated in the imported centered leaf.
-/
theorem solution :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
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
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              spectralNorm
                (quadraticNeumannFirstIndexDistinctCenteredContribution Omega S
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
                      ((3 : ℝ) / 2) +
                    Real.sqrt (β * logN) * μ₀ ^ 2 *
                        Real.rpow ((N * R) / Mobs) ((3 : ℝ) / 2) *
                          Real.sqrt ((N * R) / (↑(min n₁ n₂)))))) ≥
          1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  rcases
      quadratic_neumann_section63_first_index_distinct_centered_case_bound_under_general_sample_bound with
    ⟨Ccent, ccent, hCcent, hccent, hCentered⟩
  refine ⟨Ccent, ccent, hCcent, hccent, ?_⟩
  intro C' hC' β hβ n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
  set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp
  set N : ℝ := ((max n₁ n₂ : ℕ) : ℝ) with hN
  set R : ℝ := (r : ℝ) with hR
  set Mobs : ℝ := (m : ℝ) with hMobs
  set logN : ℝ := Real.log N with hlogN
  have hμ₀_nonneg : 0 ≤ μ₀ := le_trans zero_le_one hμ₀
  have hμ₁_nonneg : 0 ≤ μ₁ := le_trans zero_le_one hμ₁
  have hN_nat : 0 < max n₁ n₂ := lt_of_lt_of_le hn₁ (Nat.le_max_left n₁ n₂)
  have hN_pos : 0 < N := by rw [hN]; exact_mod_cast hN_nat
  have hR_pos : 0 < R := by rw [hR]; exact_mod_cast hr
  have hMobs_nonneg : 0 ≤ Mobs := by rw [hMobs]; positivity
  have hN_one : 1 ≤ N := by rw [hN]; exact_mod_cast (Nat.succ_le_of_lt hN_nat)
  have hlogN_nonneg : 0 ≤ logN := by rw [hlogN]; exact Real.log_nonneg hN_one
  have hβ_nonneg : 0 ≤ β := by linarith
  have hmn_pos : 0 < ((min n₁ n₂ : ℕ) : ℝ) := by
    have : 0 < min n₁ n₂ := lt_min hn₁ hn₂; exact_mod_cast this
  -- the plain four-term scale Φ
  set Φ : ℝ :=
    ((μ₀ ^ 2 * μ₁) *
        Real.sqrt ((N * R * (β * logN)) / Mobs) * ((N * R) / Mobs) ^ 2 +
      μ₀ ^ 2 * ((N * R) / Mobs) ^ 2 +
      Real.sqrt (β * logN) *
          Real.rpow ((N * R) / Mobs) ((3 : ℝ) / 2) * (μ₀ ^ 2 * R) +
      Real.rpow ((μ₀ * μ₁ * N * R * (β * logN)) / Mobs) ((3 : ℝ) / 2)) with hΦ
  -- the fifth (min-aware) term t₅ ≥ 0
  set t5 : ℝ :=
    Real.sqrt (β * logN) * μ₀ ^ 2 *
      Real.rpow ((N * R) / Mobs) ((3 : ℝ) / 2) *
        Real.sqrt ((N * R) / (↑(min n₁ n₂))) with ht5
  have ht5_nonneg : 0 ≤ t5 := by
    rw [ht5]
    have hbaseM_nonneg : 0 ≤ (N * R) / Mobs := by positivity
    have := Real.rpow_nonneg hbaseM_nonneg ((3:ℝ)/2)
    have h2 := Real.sqrt_nonneg ((N * R) / (↑(min n₁ n₂)))
    positivity
  -- sample ratio in [0,1]
  obtain ⟨hp0, hp1⟩ := sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm
  -- the centered event at scale Ccent * Φ
  have hCent :
      bernoulliEventProb p
          (fun Omega =>
            spectralNorm
              (quadraticNeumannFirstIndexDistinctCenteredContribution Omega S p) ≤
              Ccent * Φ) ≥
        1 - ccent * Real.rpow (↑(max n₁ n₂)) (-β) := by
    have := hCentered C' hC' β hβ n₁ n₂ r m M μ₀ μ₁ S
      hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
    simpa only [hN, hR, hMobs, hlogN, hΦ, hp] using this
  -- transport to scale Ccent * (Φ + t₅) by monotonicity (t₅ ≥ 0)
  refine le_trans hCent ?_
  refine bernoulli_event_probability_mono (n₁ := n₁) (n₂ := n₂) p
    (fun Omega =>
      spectralNorm
        (quadraticNeumannFirstIndexDistinctCenteredContribution Omega S p) ≤
        Ccent * Φ)
    (fun Omega =>
      spectralNorm
        (quadraticNeumannFirstIndexDistinctCenteredContribution Omega S p) ≤ _)
    hp0 hp1 ?_
  intro Omega hΩ
  refine le_trans hΩ ?_
  -- Ccent * Φ ≤ Ccent * (Φ + t₅) = the goal's let-block RHS
  have hΦ_le : Φ ≤ Φ + t5 := by linarith [ht5_nonneg]
  have hstep : Ccent * Φ ≤ Ccent * (Φ + t5) :=
    mul_le_mul_of_nonneg_left hΦ_le (le_of_lt hCcent)
  show Ccent * Φ ≤ _
  simp only [hN, hR, hMobs, hlogN, hΦ, ht5] at hstep ⊢
  linarith [hstep]
