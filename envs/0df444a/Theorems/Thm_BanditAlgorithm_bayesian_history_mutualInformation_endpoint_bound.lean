-- Prove2me | Theorems.Thm_BanditAlgorithm_bayesian_history_mutualInformation_endpoint_bound
-- name    : BanditAlgorithm.bayesian_history_mutualInformation_endpoint_bound
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-01T23:45:48.850334+00:00
-- url     : https://prove2.me/theorems/7e2b4f46-25b1-489d-b6af-fc8691713b74
-- title:
--   The information budget of a k-valued optimal action is at most $\log k$
-- statement:
--   Let $I_t=I(H_t;A^*)$, where $H_t$ is the observed length-$t$ bandit history and $A^*$ takes values among $k$ actions. The empty history carries no information, while the complete history cannot reveal more than the entropy of $A^*$. Therefore
--
--   $$
--   I_n-I_0\le H(A^*)\le \log k.
--   $$
--
--   This is the entropy-budget endpoint used when the per-round information gains telescope.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (Cambridge UP, 2020), https://tor-lattimore.com/downloads/book/book.pdf, printed p. 471 (PDF p. 480), proof of Theorem 36.5: the cumulative information gain telescopes and the negentropy diameter on the k-simplex is log k.

import Definitions.Def_BayesianHistoryMutualInformation

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.bayesian_history_mutualInformation_endpoint_bound
    {k n : ℕ} [NeZero k]
    (Q : Measure (Fin n → Fin k → ℝ)) [IsProbabilityMeasure Q]
    (pi : BanditPolicy k) :
    bayesianHistoryMutualInformation Q pi n le_rfl -
        bayesianHistoryMutualInformation Q pi 0 (Nat.zero_le n) ≤ Real.log k := by
  sorry
