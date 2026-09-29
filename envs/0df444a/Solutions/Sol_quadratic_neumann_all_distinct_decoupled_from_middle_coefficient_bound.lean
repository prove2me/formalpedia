-- Prove2me | solution 1 for quadratic_neumann_all_distinct_decoupled_from_middle_coefficient_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T12:58:21.47465+00:00
-- url     : https://prove2.me/submissions/ade8225d-9807-44aa-b953-8ffd66cb638f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_fixed_matrix_centered_sampling_spectral_bound
import Theorems.Thm_quadratic_neumann_sample_lower_implies_fixed_matrix_sample_lower
import Theorems.Thm_quadratic_neumann_all_distinct_decoupled_as_outer_centered_fluctuation
import Theorems.Thm_quadratic_neumann_all_distinct_outer_coefficient_entry_bound_from_middle_nonempty
import Theorems.Thm_quadratic_neumann_all_distinct_decoupled_from_outer_coefficient_bound

open MatrixCompletion

/-- Prove the final outer sampling step for the all-distinct decoupled
quadratic term from the fixed-matrix sampling theorem, the exact outer
fluctuation representation, and the entry-sup bound supplied by the middle
coefficient event. -/
theorem solution :
    ∃ Couter couter : ℝ, 0 < Couter ∧ 0 < couter ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
            (↑(max n₁ n₂)) * Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
              (β * Real.log (↑(max n₁ n₂))) →
        ∀ Cmid cmid : ℝ, 0 < Cmid → 0 < cmid →
        bernoulliPairEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega2 Omega3 =>
              QuadraticAllDistinctMiddleCoefficientBound Omega2 Omega3 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (Cmid * Real.rpow lam (-1))) ≥
          1 - cmid * Real.rpow (↑(max n₁ n₂)) (-β) →
        bernoulliTripleEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega1 Omega2 Omega3 =>
              spectralNorm
                (quadraticNeumannAllDistinctDecoupledContribution
                  Omega1 Omega2 Omega3 S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
                (Couter * Cmid) * Real.rpow lam (-((3 : ℝ) / 2))) ≥
          1 - (couter + cmid) * Real.rpow (↑(max n₁ n₂)) (-β) := by
  rcases fixed_matrix_centered_sampling_spectral_bound with
    ⟨Cfixed, hCfixed, hFixed⟩
  rcases quadratic_neumann_all_distinct_decoupled_from_outer_coefficient_bound
      Cfixed hCfixed with
    ⟨Couter, couter, hCouter, hcouter, hTransfer⟩
  refine ⟨Couter, couter, hCouter, hcouter, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
    Cmid cmid hCmid hcmid hMiddleProb
  let p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
  have hFixedSample :
      (m : ℝ) ≥
        β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂)) :=
    quadratic_neumann_sample_lower_implies_fixed_matrix_sample_lower
      β lam n₁ n₂ r m μ₀ hβ hlam hn₁ hn₂ hr hμ₀ hmLower
  have hFixedAll :
      ∀ X : Matrix (Fin n₁) (Fin n₂) ℝ,
        bernoulliEventProb p
            (fun Omega1 =>
              CenteredSamplingSpectralBound Omega1 p X
                (Cfixed * Real.sqrt
                  ((β * (↑(max n₁ n₂)) *
                      Real.log (↑(max n₁ n₂))) / p) *
                  entrySupNorm X)) ≥
            1 - (1 : ℝ) * Real.rpow (↑(max n₁ n₂)) (-β) := by
    intro X
    exact hFixed β hβ n₁ n₂ m X hn₁ hn₂ hm hFixedSample
  have hRep :
      ∀ (Omega1 Omega2 Omega3 : Finset (Fin n₁ × Fin n₂)),
        quadraticNeumannAllDistinctDecoupledContribution Omega1 Omega2 Omega3 S p =
          centeredSamplingFluctuation Omega1 p
            (quadraticAllDistinctOuterCoefficientMatrix Omega2 Omega3 S p) := by
    intro Omega1 Omega2 Omega3
    exact
      quadratic_neumann_all_distinct_decoupled_as_outer_centered_fluctuation
        Omega1 Omega2 Omega3 S p
  have hEntry :
      ∀ Omega2 Omega3 : Finset (Fin n₁ × Fin n₂),
        QuadraticAllDistinctMiddleCoefficientBound Omega2 Omega3 S p
            (Cmid * Real.rpow lam (-1)) →
          entrySupNorm
              (quadraticAllDistinctOuterCoefficientMatrix Omega2 Omega3 S p) ≤
            Cmid * Real.rpow lam (-1) := by
    intro Omega2 Omega3 hMiddle
    exact
      quadratic_neumann_all_distinct_outer_coefficient_entry_bound_from_middle_nonempty
        Omega2 Omega3 S p (Cmid * Real.rpow lam (-1)) hn₁ hn₂ hMiddle
  exact hTransfer β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
    hFixedAll hRep Cmid cmid hCmid hcmid hEntry hMiddleProb
