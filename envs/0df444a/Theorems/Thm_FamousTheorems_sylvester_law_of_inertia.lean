-- Prove2me | Theorems.Thm_FamousTheorems_sylvester_law_of_inertia
-- name    : FamousTheorems.sylvester_law_of_inertia
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T21:25:29.005984+00:00
-- url     : https://prove2.me/theorems/5eecffbf-710a-4d74-8e1a-f6fc93a5fe8f
-- title:
--   Sylvester's law of inertia (existence of a diagonal ±1/0 form)
-- statement:
--   **Sylvester's law of inertia (existence part).** Every quadratic form $Q$ on a finite-dimensional real vector space $M$ of dimension $n$ is equivalent to a diagonal form
--   $$w_1x_1^2+\cdots+w_nx_n^2\qquad\text{with each } w_i\in\{-1,0,1\}.$$
--
--   This is the normal form behind the signature of a real quadratic form, which classifies real quadratic forms up to equivalence. It is used throughout geometry and analysis, from the classification of conics and quadrics to the Morse lemma and the index of critical points.
--
--   **Formalization note.** Mathlib's `QuadraticForm.equivalent_one_zero_neg_one_weighted_sum_squared`. `QuadraticMap.Equivalent` means there is a linear isometry equivalence between the two forms, and `QuadraticMap.weightedSumSquares ℝ w` is $x\mapsto\sum_i w_ix_i^2$ on `Fin n → ℝ`. Only the existence of the diagonal form is stated. The invariance of the numbers of $+1$, $-1$ and $0$ entries (the uniqueness half of the law) is not part of this statement.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `QuadraticForm.equivalent_one_zero_neg_one_weighted_sum_squared`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem sylvester_law_of_inertia {M : Type*} [AddCommGroup M] [Module ℝ M] [FiniteDimensional ℝ M] (Q : QuadraticForm ℝ M) :
    ∃ w : Fin (Module.finrank ℝ M) → ℝ,
      (∀ i, w i = -1 ∨ w i = 0 ∨ w i = 1) ∧ QuadraticMap.Equivalent Q (QuadraticMap.weightedSumSquares ℝ w) := by sorry

end FamousTheorems
