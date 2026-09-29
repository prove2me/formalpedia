-- Prove2me | Theorems.Thm_BanditAlgorithm_klucb_index_threshold_feasible
-- name    : BanditAlgorithm.klucb_index_threshold_feasible
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-29T04:02:12.25654+00:00
-- url     : https://prove2.me/theorems/b5135930-ebbe-447f-a45d-f7f55f9be895
-- title:
--   KL-UCB index threshold feasibility
-- statement:
--   Let \(h\) be a finite bandit history, let \(\widehat\mu_i(h)\in[0,1]\) be the empirical mean of arm \(i\), and let \(q\in(0,1)\). Write
--
--   $$
--   U_i(h)=\sup\left\{q'\in[0,1]:
--   d\!\left(\widehat\mu_i(h),q'\right)
--   \le
--   \frac{\log f(n+1)}{T_i(h)}
--   \right\}
--   $$
--
--   for the KL-UCB index after \(n\) observations, with \(f(t)=1+t\log^2t\). Then
--
--   $$
--   q\le U_i(h)
--   \quad\Longleftrightarrow\quad
--   \bar d\!\left(\widehat\mu_i(h),q\right)
--   \le
--   \frac{\log f(n+1)}{T_i(h)}.
--   $$
--
--   This equivalence is the deterministic confidence-set bridge used in the proof of the KL-UCB pull-count decomposition: an interior threshold lies below the supremum index exactly when its one-sided KL constraint is feasible.
--
--   **Formalization Note** The explicit assumption \(\widehat\mu_i(h)\in[0,1]\) is satisfied on Bernoulli histories. The endpoint guards in the definition of the index are retained, while the threshold \(q\) is restricted to the open unit interval.
-- source:
--   Lattimore and Szepesvari, Bandit Algorithms (CUP 2020), Algorithm 8 printed p. 137 / PDF p. 146 and the threshold-feasibility step in the proof of Theorem 10.6 printed p. 139 / PDF p. 148. This is the formal supremum/feasibility bridge implicit in that step.

import Definitions.Def_klucbTruncatedRelativeEntropy

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.klucb_index_threshold_feasible
    {k n : ℕ} (i : Fin k) (h : BanditAlgorithm.BanditHistory k n)
    (q : ℝ) (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (hp : BanditAlgorithm.armEmpiricalMean i h ∈ Set.Icc (0 : ℝ) 1) :
    q ≤ BanditAlgorithm.klucbIndex i h ↔
      BanditAlgorithm.klucbTruncatedRelativeEntropy
          (BanditAlgorithm.armEmpiricalMean i h) q ≤
        Real.log (BanditAlgorithm.klucbExploration (n + 1)) /
          BanditAlgorithm.armPullCount i h := by
  sorry
