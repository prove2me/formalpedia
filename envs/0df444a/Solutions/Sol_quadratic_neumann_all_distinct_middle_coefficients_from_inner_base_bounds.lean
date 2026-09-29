-- Prove2me | solution 1 for quadratic_neumann_all_distinct_middle_coefficients_from_inner_base_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-14T04:53:49.505327+00:00
-- url     : https://prove2.me/submissions/1521fbcc-3bcc-47e4-a727-e8f9f945d0f2

import Theorems.Thm_quadratic_neumann_all_distinct_middle_coefficients_conditional_from_base_bounds
import Theorems.Thm_quadratic_neumann_all_distinct_middle_pair_probability_from_inner_and_conditional_bound
import Definitions.Def_matrix_completion_neumann

open MatrixCompletion


open MatrixCompletion

/-- Split the second all-distinct coefficient transfer into a conditional
Bernstein bound over the `Ω₂` copy and a product-probability lift over the
inner `Ω₃` event. -/
theorem solution
    (Centry Cfro : ℝ) :
    0 < Centry → 0 < Cfro →
    ∃ Cstep cstep : ℝ, 0 < Cstep ∧ 0 < cstep ∧
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
        ∀ Cinner cinner : ℝ, 0 < Cinner → 0 < cinner →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega3 =>
              QuadraticAllDistinctInnerCoefficientBound Omega3 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (Cinner * Real.rpow lam (-((1 : ℝ) / 2)))) ≥
          1 - cinner * Real.rpow (↑(max n₁ n₂)) (-β) →
        (∀ (Omega2 Omega3 : Finset (Fin n₁ × Fin n₂))
            (w1 : Fin n₁ × Fin n₂),
          quadraticAllDistinctMiddleCoefficient Omega2 Omega3 S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1 =
            matrixEntrySum
              (centeredSamplingFluctuation Omega2
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (quadraticAllDistinctMiddleBaseMatrix Omega3 S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1))) →
        (∀ Omega3 : Finset (Fin n₁ × Fin n₂),
          QuadraticAllDistinctInnerCoefficientBound Omega3 S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (Cinner * Real.rpow lam (-((1 : ℝ) / 2))) →
          ∀ w1 : Fin n₁ × Fin n₂,
            entrySupNorm
                (quadraticAllDistinctMiddleBaseMatrix Omega3 S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1) ≤
              Centry * (Cinner * Real.rpow lam (-((1 : ℝ) / 2))) *
                μ₀ * ((r : ℝ) / (↑(max n₁ n₂)))) →
        (∀ Omega3 : Finset (Fin n₁ × Fin n₂),
          QuadraticAllDistinctInnerCoefficientBound Omega3 S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (Cinner * Real.rpow lam (-((1 : ℝ) / 2))) →
          ∀ w1 : Fin n₁ × Fin n₂,
            frobeniusNorm
                (quadraticAllDistinctMiddleBaseMatrix Omega3 S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1) ≤
              Cfro * (Cinner * Real.rpow lam (-((1 : ℝ) / 2))) *
                Real.sqrt (μ₀ * ((r : ℝ) / (↑(max n₁ n₂))))) →
        bernoulliPairEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega2 Omega3 =>
              QuadraticAllDistinctMiddleCoefficientBound Omega2 Omega3 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                ((Cstep * Cinner) * Real.rpow lam (-1))) ≥
          1 - (cstep + cinner) * Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro hCentry hCfro
  rcases
      quadratic_neumann_all_distinct_middle_coefficients_conditional_from_base_bounds
        Centry Cfro hCentry hCfro with
    ⟨Ccond, ccond, hCcond, hccond, hConditional⟩
  rcases
      quadratic_neumann_all_distinct_middle_pair_probability_from_inner_and_conditional_bound
        Ccond ccond hCcond hccond with
    ⟨Cstep, cstep, hCstep, hcstep, hPair⟩
  refine ⟨Cstep, cstep, hCstep, hcstep, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
    Cinner cinner hCinner hcinner hInnerProb hRep hEntryAll hFrobAll
  have hCondProb :
      ∀ Omega3 : Finset (Fin n₁ × Fin n₂),
        QuadraticAllDistinctInnerCoefficientBound Omega3 S
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (Cinner * Real.rpow lam (-((1 : ℝ) / 2))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega2 =>
              QuadraticAllDistinctMiddleCoefficientBound Omega2 Omega3 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                ((Ccond * Cinner) * Real.rpow lam (-1))) ≥
          1 - ccond * Real.rpow (↑(max n₁ n₂)) (-β) := by
    intro Omega3 hInnerEvent
    have hRepOmega3 :
        ∀ (Omega2 : Finset (Fin n₁ × Fin n₂))
            (w1 : Fin n₁ × Fin n₂),
          quadraticAllDistinctMiddleCoefficient Omega2 Omega3 S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1 =
            matrixEntrySum
              (centeredSamplingFluctuation Omega2
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (quadraticAllDistinctMiddleBaseMatrix Omega3 S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1)) := by
      intro Omega2 w1
      exact hRep Omega2 Omega3 w1
    have hEntryOmega3 :
        ∀ w1 : Fin n₁ × Fin n₂,
          entrySupNorm
              (quadraticAllDistinctMiddleBaseMatrix Omega3 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1) ≤
            Centry * (Cinner * Real.rpow lam (-((1 : ℝ) / 2))) *
              μ₀ * ((r : ℝ) / (↑(max n₁ n₂))) :=
      hEntryAll Omega3 hInnerEvent
    have hFrobOmega3 :
        ∀ w1 : Fin n₁ × Fin n₂,
          frobeniusNorm
              (quadraticAllDistinctMiddleBaseMatrix Omega3 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1) ≤
            Cfro * (Cinner * Real.rpow lam (-((1 : ℝ) / 2))) *
              Real.sqrt (μ₀ * ((r : ℝ) / (↑(max n₁ n₂)))) :=
      hFrobAll Omega3 hInnerEvent
    exact hConditional β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
      hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
      Cinner hCinner Omega3 hInnerEvent hRepOmega3 hEntryOmega3 hFrobOmega3
  exact hPair β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
    Cinner cinner hCinner hcinner hInnerProb hCondProb
