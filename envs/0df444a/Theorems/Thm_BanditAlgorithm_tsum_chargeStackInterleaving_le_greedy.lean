-- Prove2me | Theorems.Thm_BanditAlgorithm_tsum_chargeStackInterleaving_le_greedy
-- name    : BanditAlgorithm.tsum_chargeStackInterleaving_le_greedy
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-31T21:08:31.248882+00:00
-- url     : https://prove2.me/theorems/883cc10e-31ed-44fc-92ef-1ffeed404711
-- title:
--   Greedy charge-stack interleaving maximizes the discounted sum
-- statement:
--   Let $k$ be a finite number of arms. For each arm $i$, let $H_i(0),H_i(1),\ldots$ be a nonincreasing real-valued charge stack. An action sequence $a^*$ is greedy when, at every round, it selects an arm whose currently exposed charge is maximal.
--
--   For a discount factor $0\le\alpha\le1$, let $I_n(H,a)$ denote the charge exposed at round $n$ by an arbitrary action sequence $a$. If both discounted interleavings are summable, then
--
--   $$
--   \sum_{n=0}^{\infty}\alpha^n I_n(H,a)
--   \le
--   \sum_{n=0}^{\infty}\alpha^n I_n(H,a^*).
--   $$
--
--   Thus greedy interleaving maximizes the geometrically discounted total of decreasing stacks. This is the deterministic Hardy--Littlewood step used in the Gittins-index theorem.
-- source:
--   Tor Lattimore and Csaba Szepesvári, Bandit Algorithms (free online edition), https://tor-lattimore.com/downloads/book/book.pdf, Section 35.4, printed p. 451 / PDF p. 459, Lemma 35.10; the proof is assigned as Exercise 35.9.

import Definitions.Def_GittinsChargeInterleaving

theorem BanditAlgorithm.tsum_chargeStackInterleaving_le_greedy
    {k : ℕ} {H : Fin k → ℕ → ℝ} {astar : ℕ → Fin k}
    (hH : ∀ i, Antitone (H i))
    (hastar : IsGreedyChargeStackInterleaving H astar)
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (a : ℕ → Fin k)
    (hsuma : Summable
      (fun n ↦ α ^ n * chargeStackInterleaving H a n))
    (hsumg : Summable
      (fun n ↦ α ^ n * chargeStackInterleaving H astar n)) :
    (∑' n : ℕ, α ^ n * chargeStackInterleaving H a n) ≤
      ∑' n : ℕ, α ^ n * chargeStackInterleaving H astar n := by
  sorry
