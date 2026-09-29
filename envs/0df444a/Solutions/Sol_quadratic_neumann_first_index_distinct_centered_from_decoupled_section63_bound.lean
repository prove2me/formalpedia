-- Prove2me | solution 1 for quadratic_neumann_first_index_distinct_centered_from_decoupled_section63_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-07-20T20:31:47.365839+00:00
-- url     : https://prove2.me/submissions/a30da78a-a929-4cc5-9bed-92a0ed9d2870

import Theorems.Thm_quadratic_neumann_first_index_distinct_centered_decoupling_transfer_general_sample
import Theorems.Thm_sample_ratio_between_zero_and_one
import Theorems.Thm_bernoulli_event_probability_mono
import Mathlib.Tactic

open MatrixCompletion

/-!
Source: Candes-Recht 2008, Section 6.3, PDF pp. 31--32, the standard
two-variable decoupling step for the centered `omega_1 != omega_2 = omega_3`
quadratic chaos.

Pure formal bridge: instantiate the already isolated generic pair-to-single
decoupling transfer
`quadratic_neumann_first_index_distinct_centered_decoupling_transfer_general_sample`
at the four-term Section 6.3 summary scale `Phi`.
-/
theorem solution
    (Cpair cpair : ℝ) :
    0 < Cpair → 0 < cpair →
    ∃ Ctrans ctrans : ℝ, 0 < Ctrans ∧ 0 < ctrans ∧
      ∀ Cout : ℝ, Ctrans ≤ Cout →
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        bernoulliPairEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega1 Omega2 =>
              spectralNorm
                (quadraticNeumannFirstIndexDistinctCenteredDecoupledContribution
                  Omega1 Omega2 S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
                (let N : ℝ := ↑(max n₁ n₂)
                 let R : ℝ := (r : ℝ)
                 let Mobs : ℝ := (m : ℝ)
                 let logN : ℝ := Real.log N
                 Cpair *
                   ((μ₀ ^ 2 * μ₁) *
                      Real.sqrt ((N * R * (β * logN)) / Mobs) *
                        ((N * R) / Mobs) ^ 2 +
                    μ₀ ^ 2 * ((N * R) / Mobs) ^ 2 +
                    Real.sqrt (β * logN) *
                        Real.rpow ((N * R) / Mobs) ((3 : ℝ) / 2) *
                          (μ₀ ^ 2 * R) +
                    Real.rpow
                      ((μ₀ * μ₁ * N * R * (β * logN)) / Mobs)
                      ((3 : ℝ) / 2)))) ≥
          1 - cpair * Real.rpow (↑(max n₁ n₂)) (-β) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              spectralNorm
                (quadraticNeumannFirstIndexDistinctCenteredContribution Omega S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
                (let N : ℝ := ↑(max n₁ n₂)
                 let R : ℝ := (r : ℝ)
                 let Mobs : ℝ := (m : ℝ)
                 let logN : ℝ := Real.log N
                 Cout *
                   ((μ₀ ^ 2 * μ₁) *
                      Real.sqrt ((N * R * (β * logN)) / Mobs) *
                        ((N * R) / Mobs) ^ 2 +
                    μ₀ ^ 2 * ((N * R) / Mobs) ^ 2 +
                    Real.sqrt (β * logN) *
                        Real.rpow ((N * R) / Mobs) ((3 : ℝ) / 2) *
                          (μ₀ ^ 2 * R) +
                    Real.rpow
                      ((μ₀ * μ₁ * N * R * (β * logN)) / Mobs)
                      ((3 : ℝ) / 2)))) ≥
          1 - ctrans * Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro hCpair hcpair
  rcases quadratic_neumann_first_index_distinct_centered_decoupling_transfer_general_sample with
    ⟨K, L, hK, hL, hTransfer⟩
  refine ⟨K * Cpair, L * cpair, by positivity, by positivity, ?_⟩
  intro Cout hCout β hβ n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hPair
  set N : ℝ := (↑(max n₁ n₂) : ℝ) with hN
  set R : ℝ := (r : ℝ) with hR
  set Mobs : ℝ := (m : ℝ) with hMobs
  set logN : ℝ := Real.log N with hlogN
  set Phi : ℝ :=
    ((μ₀ ^ 2 * μ₁) *
        Real.sqrt ((N * R * (β * logN)) / Mobs) * ((N * R) / Mobs) ^ 2 +
      μ₀ ^ 2 * ((N * R) / Mobs) ^ 2 +
      Real.sqrt (β * logN) *
          Real.rpow ((N * R) / Mobs) ((3 : ℝ) / 2) * (μ₀ ^ 2 * R) +
      Real.rpow ((μ₀ * μ₁ * N * R * (β * logN)) / Mobs) ((3 : ℝ) / 2)) with hPhi
  obtain ⟨hp0, hp1⟩ := sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm
  have hPhi_nonneg : 0 ≤ Phi := by
    have hNnat : 0 < max n₁ n₂ := Nat.lt_of_lt_of_le hn₁ (le_max_left _ _)
    have hNpos : (0 : ℝ) < N := by rw [hN]; exact_mod_cast hNnat
    have hN1 : (1 : ℝ) ≤ N := by rw [hN]; exact_mod_cast hNnat
    have hRnonneg : (0 : ℝ) ≤ R := by rw [hR]; positivity
    have hMnonneg : (0 : ℝ) ≤ Mobs := by rw [hMobs]; positivity
    have hlog_nonneg : 0 ≤ logN := by rw [hlogN]; exact Real.log_nonneg hN1
    have hmu0 : (0 : ℝ) ≤ μ₀ := le_trans zero_le_one hμ₀
    have hmu1 : (0 : ℝ) ≤ μ₁ := le_trans zero_le_one hμ₁
    have hbeta : (0 : ℝ) ≤ β := le_of_lt (lt_trans (by norm_num) hβ)
    have hbase3 : (0 : ℝ) ≤ (N * R) / Mobs := by positivity
    have hbase4 : (0 : ℝ) ≤ (μ₀ * μ₁ * N * R * (β * logN)) / Mobs := by positivity
    rw [hPhi]
    have t1 : (0 : ℝ) ≤ (μ₀ ^ 2 * μ₁) *
        Real.sqrt ((N * R * (β * logN)) / Mobs) * ((N * R) / Mobs) ^ 2 := by
      positivity
    have t2 : (0 : ℝ) ≤ μ₀ ^ 2 * ((N * R) / Mobs) ^ 2 := by
      positivity
    have t3 : (0 : ℝ) ≤ Real.sqrt (β * logN) *
        Real.rpow ((N * R) / Mobs) ((3 : ℝ) / 2) * (μ₀ ^ 2 * R) := by
      have := Real.rpow_nonneg hbase3 ((3 : ℝ) / 2)
      positivity
    have t4 : (0 : ℝ) ≤
        Real.rpow ((μ₀ * μ₁ * N * R * (β * logN)) / Mobs) ((3 : ℝ) / 2) :=
      Real.rpow_nonneg hbase4 _
    linarith
  have hPair' :
      bernoulliPairEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          (fun Omega1 Omega2 =>
            spectralNorm
              (quadraticNeumannFirstIndexDistinctCenteredDecoupledContribution
                Omega1 Omega2 S ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
              Cpair * Phi) ≥
        1 - cpair * Real.rpow (↑(max n₁ n₂)) (-β) := by
    simpa only [hN, hR, hMobs, hlogN, hPhi] using hPair
  have hOut :=
    hTransfer S ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) Cpair cpair β Phi
      hp0 hp1 hCpair hcpair hPhi_nonneg hPair'
  have hBound : (K * Cpair) * Phi ≤ Cout * Phi :=
    mul_le_mul_of_nonneg_right hCout hPhi_nonneg
  have hFinal :=
    bernoulli_event_probability_mono
      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
      (fun Omega =>
        spectralNorm
          (quadraticNeumannFirstIndexDistinctCenteredContribution Omega S
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
          (K * Cpair) * Phi)
      (fun Omega =>
        spectralNorm
          (quadraticNeumannFirstIndexDistinctCenteredContribution Omega S
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
          Cout * Phi)
      hp0 hp1 (fun Omega hOmega => le_trans hOmega hBound)
  exact le_trans hOut hFinal
