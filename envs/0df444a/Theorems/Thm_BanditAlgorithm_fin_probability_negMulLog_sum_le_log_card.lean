-- Prove2me | Theorems.Thm_BanditAlgorithm_fin_probability_negMulLog_sum_le_log_card
-- name    : BanditAlgorithm.fin_probability_negMulLog_sum_le_log_card
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-01T23:25:48.582932+00:00
-- url     : https://prove2.me/theorems/0723036c-844e-40bf-8e31-d8c8fa8abd19
-- title:
--   Entropy of a finite probability vector is at most $\log k$
-- statement:
--   Let $p=(p_a)_{a\in[k]}$ be a probability vector on a nonempty set of $k$ actions. Its Shannon entropy satisfies
--
--   $$
--   \sum_{a=1}^{k} -p_a\log p_a \le \log k.
--   $$
--
--   Here the convention at $p_a=0$ is encoded by `Real.negMulLog`.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (Cambridge UP, 2020), https://tor-lattimore.com/downloads/book/book.pdf, printed p. 471 (PDF p. 480), proof of Theorem 36.5: the diameter of the negative-entropy potential on the k-simplex is log k.

import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

open scoped BigOperators

theorem BanditAlgorithm.fin_probability_negMulLog_sum_le_log_card {k : ℕ} [NeZero k]
    (p : Fin k → ℝ) (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1) :
    ∑ a, Real.negMulLog (p a) ≤ Real.log k := by
  sorry
