-- Prove2me | solution 1 for linear_neumann_off_diagonal_two_term_min_dim_bernstein_threshold_absorbed_under_general_sample_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-30T10:46:18.682064+00:00
-- url     : https://prove2.me/submissions/80d5b45a-d02c-4fe8-9da5-16c0071fdda1

import Definitions.Def_linear_neumann_offdiag_bernstein
import Theorems.Thm_general_sample_bound_implies_lemma66_density_bound
import Theorems.Thm_linear_neumann_off_diagonal_two_term_min_dim_bernstein_threshold_absorbed_from_density_bound

open MatrixCompletion

open MatrixCompletion

/-!
Source: Candès--Recht 2008, Theorem 1.3/equation (1.9), Section 4.3/equation
(4.19), and Section 6.2, Lemma 6.6/equation (6.17).

The proof separates two scalar facts:
1. the global Theorem 1.3 sample lower bound implies the Lemma 6.6 density
   proviso `m ≥ (8/3) μ₀ N r β log N`;
2. under that density proviso, the two Bernstein terms in (6.17) are absorbed
   into the final coefficient scale.
-/
theorem solution
    (Ctwo Centry Cfro : ℝ) :
    0 < Ctwo → 0 < Centry → 0 < Cfro →
    ∃ Ccoef : ℝ, 0 < Ccoef ∧
      ∀ C' : ℝ, Ccoef ≤ C' →
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (μ₀ μ₁ : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        (m : ℝ) ≥
          C' * max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
                  (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4))
            * (↑(max n₁ n₂)) * (r : ℝ) *
              (β * Real.log (↑(max n₁ n₂))) →
        Ctwo *
            (Real.sqrt
                (((β + 2) * Real.log (↑(max n₁ n₂))) /
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              (Cfro * μ₁ *
                Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                  Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))) +
              (((β + 2) * Real.log (↑(max n₁ n₂))) /
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                (Centry * μ₁ *
                  Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                    (μ₀ * (r : ℝ) / (↑(min n₁ n₂))))) ≤
          Ccoef * μ₁ *
            Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              Real.sqrt
                ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
                    (β * Real.log (↑(max n₁ n₂)))) / (m : ℝ)) := by
  intro hCtwo hCentry hCfro
  rcases general_sample_bound_implies_lemma66_density_bound with
    ⟨Cdensity, hCdensity_pos, hDensity⟩
  rcases
      linear_neumann_off_diagonal_two_term_min_dim_bernstein_threshold_absorbed_from_density_bound
        Ctwo Centry Cfro hCtwo hCentry hCfro with
    ⟨Cabs, hCabs_pos, hAbsorb⟩
  let Ccoef : ℝ := max Cdensity Cabs
  refine ⟨Ccoef, ?_, ?_⟩
  · exact lt_of_lt_of_le hCdensity_pos (le_max_left Cdensity Cabs)
  · intro C' hC' β hβ n₁ n₂ r m μ₀ μ₁
      hn₁ hn₂ hr hm hμ₀ hμ₁ hmLower
    have hCdensity_le_Ccoef : Cdensity ≤ Ccoef := by
      exact le_max_left Cdensity Cabs
    have hCabs_le_Ccoef : Cabs ≤ Ccoef := by
      exact le_max_right Cdensity Cabs
    have hDensityLower :=
      hDensity C' (le_trans hCdensity_le_Ccoef hC') β hβ
        n₁ n₂ r m μ₀ μ₁ hn₁ hn₂ hr hμ₀ hμ₁ hmLower
    exact hAbsorb Ccoef hCabs_le_Ccoef β hβ n₁ n₂ r m μ₀ μ₁
      hn₁ hn₂ hr hm hμ₀ hμ₁ hDensityLower
