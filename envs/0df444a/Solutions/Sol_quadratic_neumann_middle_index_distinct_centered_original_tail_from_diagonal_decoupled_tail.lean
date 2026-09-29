-- Prove2me | solution 1 for quadratic_neumann_middle_index_distinct_centered_original_tail_from_diagonal_decoupled_tail
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-14T04:30:56.557225+00:00
-- url     : https://prove2.me/submissions/529c1228-71fd-4909-85c8-97b56a8d0d9c

import Theorems.Thm_quadratic_neumann_middle_index_distinct_centered_diagonal_decoupled_equals_original
import Theorems.Thm_bernoulli_event_probability_mono
import Definitions.Def_matrix_completion_neumann

open MatrixCompletion


open MatrixCompletion

/-- Prove the original-tail transfer for the centered `ω₁ = ω₃ ≠ ω₂`
quadratic term from the diagonal-coupling identity and event monotonicity. -/
theorem solution
    {n₁ n₂ r : Nat} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (p bound lower : ℝ) :
    0 ≤ p → p ≤ 1 →
    bernoulliEventProb p
        (fun Omega =>
          spectralNorm
            (quadraticNeumannMiddleIndexDistinctCenteredDecoupledContribution
              Omega Omega S p) ≤ bound) ≥ lower →
    bernoulliEventProb p
        (fun Omega =>
          spectralNorm
            (quadraticNeumannMiddleIndexDistinctCenteredContribution Omega S p) ≤
            bound) ≥ lower := by
  intro hp0 hp1 hDiagProb
  have hMono :
      bernoulliEventProb p
          (fun Omega =>
            spectralNorm
              (quadraticNeumannMiddleIndexDistinctCenteredDecoupledContribution
                Omega Omega S p) ≤ bound) ≤
        bernoulliEventProb p
          (fun Omega =>
            spectralNorm
              (quadraticNeumannMiddleIndexDistinctCenteredContribution Omega S p) ≤
              bound) :=
    bernoulli_event_probability_mono p
      (fun Omega =>
        spectralNorm
          (quadraticNeumannMiddleIndexDistinctCenteredDecoupledContribution
            Omega Omega S p) ≤ bound)
      (fun Omega =>
        spectralNorm
          (quadraticNeumannMiddleIndexDistinctCenteredContribution Omega S p) ≤
          bound)
      hp0 hp1
      (by
        intro Omega hOmega
        simpa
          [quadratic_neumann_middle_index_distinct_centered_diagonal_decoupled_equals_original
            Omega S p] using hOmega)
  linarith
