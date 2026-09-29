-- Prove2me | solution 1 for linear_neumann_off_diagonal_coefficient_bound_from_lemma66_min_dim_base_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-30T10:47:33.54337+00:00
-- url     : https://prove2.me/submissions/39a5fa23-9fc6-45c8-a82b-5493fac90d29

import Definitions.Def_linear_neumann_offdiag_bernstein
import Theorems.Thm_linear_neumann_off_diagonal_coefficient_pointwise_two_term_tail_from_min_dim_base_bounds
import Theorems.Thm_linear_neumann_off_diagonal_coefficient_uniform_two_term_bound_from_min_dim_shifted_pointwise_tails
import Theorems.Thm_linear_neumann_off_diagonal_two_term_min_dim_bernstein_threshold_absorbed_under_general_sample_bound
import Theorems.Thm_bernoulli_event_probability_mono
import Theorems.Thm_sample_ratio_between_zero_and_one

open MatrixCompletion

open MatrixCompletion

/-!
Source: Candès--Recht 2008, Section 6.2, PDF pp. 27--29, equations
(6.13)--(6.17), the union bound immediately after (6.17), and the
rectangular convention after equations (6.2)--(6.4).

This is the source-faithful Lemma 6.6 reduction for the corrected
min-dimensional base scales:
1. fixed-coordinate raw scalar Bernstein;
2. finite coordinate union bound with the `β+2` shift;
3. scalar absorption of the two Bernstein terms under the full Theorem 1.3
   sample lower bound.
-/
theorem solution
    (Centry Cfro : ℝ) :
    0 < Centry → 0 < Cfro →
    ∃ Ccoef ccoef : ℝ, 0 < Ccoef ∧ 0 < ccoef ∧
      ∀ C' : ℝ, Ccoef ≤ C' →
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
        (∀ (Omega2 : Finset (Fin n₁ × Fin n₂))
            (w : Fin n₁ × Fin n₂),
          linearNeumannOffDiagonalCoefficientMatrix Omega2 S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w.1 w.2 =
            matrixEntrySum
              (centeredSamplingFluctuation Omega2
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (linearNeumannOffDiagonalCoefficientBaseMatrix S w))) →
        (∀ w : Fin n₁ × Fin n₂,
          entrySupNorm
              (linearNeumannOffDiagonalCoefficientBaseMatrix S w) ≤
            Centry * μ₁ *
              Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))) →
        (∀ w : Fin n₁ × Fin n₂,
          frobeniusNorm
              (linearNeumannOffDiagonalCoefficientBaseMatrix S w) ≤
            Cfro * μ₁ *
              Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                Real.sqrt
                  (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega2 =>
              LinearNeumannOffDiagonalCoefficientBound Omega2 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (Ccoef * μ₁ *
                  Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                    Real.sqrt
                      ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
                          (β * Real.log (↑(max n₁ n₂)))) / (m : ℝ)))) ≥
          1 - ccoef * Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro hCentry hCfro
  rcases
      linear_neumann_off_diagonal_coefficient_pointwise_two_term_tail_from_min_dim_base_bounds
        Centry Cfro hCentry hCfro with
    ⟨Cpoint, cpoint, hCpoint, hcpoint, hPointwise⟩
  rcases
      linear_neumann_off_diagonal_coefficient_uniform_two_term_bound_from_min_dim_shifted_pointwise_tails
        Cpoint cpoint Centry Cfro hCpoint hcpoint with
    ⟨Ctwo, ctwo, hCtwo, hctwo, hUniformTwoTerm⟩
  rcases
      linear_neumann_off_diagonal_two_term_min_dim_bernstein_threshold_absorbed_under_general_sample_bound
        Ctwo Centry Cfro hCtwo hCentry hCfro with
    ⟨Ccoef, hCcoef, hAbsorb⟩
  refine ⟨Ccoef, ctwo, hCcoef, hctwo, ?_⟩
  intro C' hC' β hβ n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower hRep hEntry hFrob
  let p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
  let twoTermScale : ℝ :=
    Real.sqrt
        (((β + 2) * Real.log (↑(max n₁ n₂))) / p) *
      (Cfro * μ₁ *
        Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
          Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))) +
      (((β + 2) * Real.log (↑(max n₁ n₂))) / p) *
        (Centry * μ₁ *
          Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
            (μ₀ * (r : ℝ) / (↑(min n₁ n₂))))
  let cleanScale : ℝ :=
    Ccoef * μ₁ *
      Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
        Real.sqrt
          ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
              (β * Real.log (↑(max n₁ n₂)))) / (m : ℝ))
  have hPointwiseAll :
      ∀ w : Fin n₁ × Fin n₂,
        bernoulliEventProb p
            (fun Omega2 =>
              |linearNeumannOffDiagonalCoefficientMatrix Omega2 S
                  p w.1 w.2| ≤
                Cpoint * twoTermScale) ≥
          1 - cpoint * Real.rpow (↑(max n₁ n₂)) (-(β + 2)) := by
    intro w
    have h := hPointwise C' β hβ n₁ n₂ r m M μ₀ μ₁ S
      hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower w
      (fun Omega2 => hRep Omega2 w) (hEntry w) (hFrob w)
    simpa [p, twoTermScale, mul_assoc] using h
  have hTwoTermEvent :
      bernoulliEventProb p
          (fun Omega2 =>
            LinearNeumannOffDiagonalCoefficientBound Omega2 S p
              (Ctwo * twoTermScale)) ≥
        1 - ctwo * Real.rpow (↑(max n₁ n₂)) (-β) := by
    simpa [p, twoTermScale, mul_assoc] using
      hUniformTwoTerm C' β hβ n₁ n₂ r m M μ₀ μ₁ S
        hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower hPointwiseAll
  have hAbsorb' : Ctwo * twoTermScale ≤ cleanScale := by
    simpa [p, twoTermScale, cleanScale, mul_assoc] using
      hAbsorb C' hC' β hβ n₁ n₂ r m μ₀ μ₁
        hn₁ hn₂ hr hm hμ₀ hμ₁ hmLower
  rcases sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm with
    ⟨hp_nonneg, hp_le_one⟩
  have hMono :
      bernoulliEventProb p
          (fun Omega2 =>
            LinearNeumannOffDiagonalCoefficientBound Omega2 S p
              (Ctwo * twoTermScale)) ≤
        bernoulliEventProb p
          (fun Omega2 =>
            LinearNeumannOffDiagonalCoefficientBound Omega2 S p cleanScale) := by
    refine bernoulli_event_probability_mono p _ _ hp_nonneg hp_le_one ?_
    intro Omega2 hBound
    exact le_trans hBound hAbsorb'
  simpa [p, cleanScale, mul_assoc] using le_trans hTwoTermEvent hMono
