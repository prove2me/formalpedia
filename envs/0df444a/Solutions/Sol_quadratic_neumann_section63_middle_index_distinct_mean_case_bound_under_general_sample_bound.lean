-- Prove2me | solution 1 for quadratic_neumann_section63_middle_index_distinct_mean_case_bound_under_general_sample_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-07-02T14:13:34.190667+00:00
-- url     : https://prove2.me/submissions/ad886c36-c8f0-4541-9100-7b093398e131

import Theorems.Thm_quadratic_neumann_middle_index_distinct_mean_response_sampling_section63_bound_under_general_sample_bound
import Theorems.Thm_quadratic_neumann_middle_index_distinct_mean_as_off_diagonal_response
import Theorems.Thm_sample_ratio_between_zero_and_one
import Theorems.Thm_bernoulli_event_probability_mono
import Mathlib.Tactic

open MatrixCompletion

/-!
Source: Candès–Recht 2008, Section 6.3, PDF pp. 32--33 and the p. 34 summary
display.  The mean part `S₂` of the `ω₁ = ω₃ ≠ ω₂` case after expanding
`ξ_{ω₁}² = (1 - 2p)ξ_{ω₁} + p(1-p)`.

Top-level assembly of `ff639324`
(`quadratic_neumann_section63_middle_index_distinct_mean_case_bound_under_general_sample_bound`),
rerouted onto the SOUND rescaled-sign response route:

* the deterministic representation identity (brick 1,
  `quadratic_neumann_middle_index_distinct_mean_as_off_diagonal_response`) writes the
  mean contribution as `(1-p) • MiddleResponse((P_Ω-pI)/p (p⁻¹ 𝟙))`;
* the genuine §6.3 analytic content is the response-sampling estimate at scale `Φ`
  (brick 2,
  `quadratic_neumann_middle_index_distinct_mean_response_sampling_section63_bound_under_general_sample_bound`),
  the Theorem 6.3 (`021320e3`) application to the rescaled all-ones matrix in the
  TIGHT per-entry `μ₀ (r/N)` kernel-square scale.

This BYPASSES the false `mean_from_coefficients_section63_bound` /
`mean_coefficients_section63_bound` (scalar-coefficient → spectral) route, whose
Frobenius transfer picks up a bare `p⁻¹ = n₁n₂/m` factor unabsorbable by `Φ`
(diverges on diagonal/thin matrices under the standard `N^{1/4}` sample bound).
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
                (quadraticNeumannMiddleIndexDistinctMeanContribution Omega S
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
                      ((3 : ℝ) / 2)))) ≥
          1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  rcases
      quadratic_neumann_middle_index_distinct_mean_response_sampling_section63_bound_under_general_sample_bound with
    ⟨Cresp, cresp, hCresp, hcresp, hRespBound⟩
  refine ⟨Cresp, cresp, hCresp, hcresp, ?_⟩
  intro C' hC' β hβ n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
  obtain ⟨hp0, hp1⟩ := sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm
  set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp
  have hResp :=
    hRespBound C' hC' β hβ n₁ n₂ r m M μ₀ μ₁ S
      hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
  refine le_trans hResp ?_
  refine bernoulli_event_probability_mono (n₁ := n₁) (n₂ := n₂) p
    (fun Omega =>
      spectralNorm
        ((1 - p) •
          quadraticMiddleIndexDistinctOffDiagonalResponse S
            (centeredSamplingFluctuation Omega p (p⁻¹ • onesMatrix n₁ n₂))) ≤ _)
    (fun Omega =>
      spectralNorm
        (quadraticNeumannMiddleIndexDistinctMeanContribution Omega S p) ≤ _)
    hp0 hp1 ?_
  intro Omega hΩ
  rw [quadratic_neumann_middle_index_distinct_mean_as_off_diagonal_response Omega S p]
  exact hΩ
