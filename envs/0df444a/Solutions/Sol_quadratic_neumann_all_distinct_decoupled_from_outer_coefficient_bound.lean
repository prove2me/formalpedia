-- Prove2me | solution 1 for quadratic_neumann_all_distinct_decoupled_from_outer_coefficient_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T07:49:50.630991+00:00
-- url     : https://prove2.me/submissions/5f3e7319-8af2-4188-ae3d-9bcf730c44f2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_quadratic_neumann_all_distinct_outer_sampling_conditional_from_entry_bound
import Theorems.Thm_quadratic_neumann_all_distinct_triple_probability_from_middle_and_outer_conditional_bound

open MatrixCompletion

/-- Split the final all-distinct outer transfer into a fixed-`Ω₂, Ω₃`
conditional sampling estimate and the product-probability lift over the middle
coefficient event. -/
theorem solution
    (Cfixed : ℝ) :
    0 < Cfixed →
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
        (∀ X : Matrix (Fin n₁) (Fin n₂) ℝ,
          bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega1 =>
                CenteredSamplingSpectralBound Omega1
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X
                  (Cfixed * Real.sqrt
                    ((β * (↑(max n₁ n₂)) *
                        Real.log (↑(max n₁ n₂))) /
                      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                    entrySupNorm X)) ≥
            1 - (1 : ℝ) * Real.rpow (↑(max n₁ n₂)) (-β)) →
        (∀ (Omega1 Omega2 Omega3 : Finset (Fin n₁ × Fin n₂)),
          quadraticNeumannAllDistinctDecoupledContribution Omega1 Omega2 Omega3 S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) =
            centeredSamplingFluctuation Omega1
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (quadraticAllDistinctOuterCoefficientMatrix Omega2 Omega3 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))) →
        ∀ Cmid cmid : ℝ, 0 < Cmid → 0 < cmid →
        (∀ Omega2 Omega3 : Finset (Fin n₁ × Fin n₂),
          QuadraticAllDistinctMiddleCoefficientBound Omega2 Omega3 S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (Cmid * Real.rpow lam (-1)) →
            entrySupNorm
                (quadraticAllDistinctOuterCoefficientMatrix Omega2 Omega3 S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
              Cmid * Real.rpow lam (-1)) →
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
          1 - (couter + cmid) *
            Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro hCfixed
  rcases quadratic_neumann_all_distinct_outer_sampling_conditional_from_entry_bound
      Cfixed hCfixed with
    ⟨Ccond, ccond, hCcond, hccond, hConditional⟩
  rcases
      quadratic_neumann_all_distinct_triple_probability_from_middle_and_outer_conditional_bound
        Ccond ccond hCcond hccond with
    ⟨Couter, couter, hCouter, hcouter, hTriple⟩
  refine ⟨Couter, couter, hCouter, hcouter, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
    hFixedAll hRep Cmid cmid hCmid hcmid hEntry hMiddleProb
  have hOuterCond :
      ∀ Omega2 Omega3 : Finset (Fin n₁ × Fin n₂),
        QuadraticAllDistinctMiddleCoefficientBound Omega2 Omega3 S
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (Cmid * Real.rpow lam (-1)) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega1 =>
              spectralNorm
                (quadraticNeumannAllDistinctDecoupledContribution
                  Omega1 Omega2 Omega3 S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
                (Ccond * Cmid) * Real.rpow lam (-((3 : ℝ) / 2))) ≥
          1 - ccond * Real.rpow (↑(max n₁ n₂)) (-β) := by
    intro Omega2 Omega3 hMiddle
    have hRepFixed :
        ∀ Omega1 : Finset (Fin n₁ × Fin n₂),
          quadraticNeumannAllDistinctDecoupledContribution
              Omega1 Omega2 Omega3 S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) =
            centeredSamplingFluctuation Omega1
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (quadraticAllDistinctOuterCoefficientMatrix Omega2 Omega3 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) := by
      intro Omega1
      exact hRep Omega1 Omega2 Omega3
    have hEntryFixed :
        entrySupNorm
            (quadraticAllDistinctOuterCoefficientMatrix Omega2 Omega3 S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
          Cmid * Real.rpow lam (-1) :=
      hEntry Omega2 Omega3 hMiddle
    exact hConditional β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
      hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
      hFixedAll Cmid hCmid Omega2 Omega3 hRepFixed hEntryFixed
  exact hTriple β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
    Cmid cmid hCmid hcmid hMiddleProb hOuterCond
