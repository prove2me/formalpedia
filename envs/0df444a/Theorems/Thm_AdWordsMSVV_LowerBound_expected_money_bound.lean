-- Prove2me | Theorems.Thm_AdWordsMSVV_LowerBound_expected_money_bound
-- name    : AdWordsMSVV.LowerBound.expected_money_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:30:45.238982+00:00
-- url     : https://prove2.me/theorems/44123389-6fca-437f-96d6-acbcaf868817
-- title:
--   Proof of Theorem 9, p. 15 — the expected money spent by bidder j is at most min{1, Σ_{i=1}^{j} 1/(N−i+1)}
-- statement:
--   Let $N \ge 0$, $B \ge 1$, and fix a deterministic online algorithm $a$ for instances with $N$ bidders and $NB$ queries. For a position $j \in \{1,\dots,N\}$, the money spent by the bidder $\pi(j)$ at the end of the run of $a$ on the permuted round instance $I_\pi$ is $L^a_{NB}(\pi(j))/B$ (each won query costs $\epsilon = 1/B$ of a unit budget). Its average over a uniformly random permutation satisfies
--   $$\mathbb E_\pi\!\left[\frac{L^a_{NB}(\pi(j))}{B}\right] \le \min\Big\{1,\ \sum_{i=1}^{j}\frac{1}{N-i+1}\Big\}.$$
--
--   Summed over $j$, this per-bidder bound gives the average revenue of every deterministic algorithm on the distribution $\mathcal D$.
--
--   **Formalization Note** As in the previous milestone, "bidder $j$" is the bidder in position $j$ of the permutation, $\pi(j)$. Money is measured in units of the budget, so the paper's unit budget corresponds to $B$ won queries.
-- source:
--   Mehta, Saberi, Vazirani, Vazirani, AdWords and generalized on-line matching, J. ACM (2007), DOI 10.1145/1284320.1284321, p. 15, proof of Theorem 9, last paragraph, first sentence

import Mathlib
import Definitions.Def_AdWordsMSVV_LowerBound_Setting

namespace AdWordsMSVV.LowerBound

open Finset

theorem expected_money_bound (N B : ℕ) (hB : 1 ≤ B) (a : DetAlg N (N * B))
    (j : ℕ) (hj1 : 1 ≤ j) (hjN : j ≤ N) :
    permAvg N (fun π =>
      (load B (roundInstance N B π) a (N * B) (π ⟨j - 1, by omega⟩) : ℝ) / B)
      ≤ min 1 (∑ i ∈ Icc 1 j, 1 / ((N : ℝ) - i + 1)) := by sorry

end AdWordsMSVV.LowerBound
