-- Prove2me | solution 1 for rademacher_expectation_eq_bernoulli_half_expectation
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-23T17:25:30.216099+00:00
-- url     : https://prove2.me/submissions/dd26db5d-7598-4836-b874-0b758121f1dc

import Definitions.Def_matrix_completion_rademacher
import Definitions.Def_matrix_completion_bernoulli
open MatrixCompletion
open scoped BigOperators Classical

/-- σ-fiber bridge: `rademacherExpectation F = bernoulliExpectation (1/2) F`.
See `Thm_rademacher_expectation_eq_bernoulli_half_expectation`.  Cite
de la Peña–Montgomery-Smith 1995 (arXiv:math/9309211) §4 (the symmetric `σ`-signs
are the `p = 1/2` Bernoulli model). -/
theorem solution
    {n1 n2 : ℕ} (F : Finset (Fin n1 × Fin n2) → ℝ) :
    rademacherExpectation F = bernoulliExpectation ((1 : ℝ) / 2) F := by
  unfold rademacherExpectation bernoulliExpectation
  apply Finset.sum_congr rfl
  intro Ω _
  congr 1
  unfold rademacherObservationWeight bernoulliObservationWeight
  rw [show ((1 : ℝ) - 1 / 2) = 1 / 2 by ring]
  rw [← pow_add]
  congr 1
  have hle : Ω.card ≤ Fintype.card (Fin n1 × Fin n2) := by
    simpa using Finset.card_le_univ Ω
  omega
