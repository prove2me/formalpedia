-- Prove2me | Theorems.Thm_AdWordsMSVV_LowerBound_expected_fraction_bound
-- name    : AdWordsMSVV.LowerBound.expected_fraction_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:30:39.940855+00:00
-- url     : https://prove2.me/theorems/435843d2-86c1-4238-ae81-c71e213efdb0
-- title:
--   Proof of Theorem 9, p. 15 — E_π[q_ij] ≤ 1/(N−i+1) if j ≥ i, and = 0 if j < i
-- statement:
--   Let $N \ge 0$, $B \ge 1$, and fix a deterministic online algorithm $a$ for instances with $N$ bidders and $NB$ queries. For a permutation $\pi$ of the bidders, a round $i \in \{1,\dots,N\}$ and a position $j \in \{1,\dots,N\}$, let
--   $$q_{ij}(\pi) = \frac{W^a_i(\pi(j))}{B}$$
--   be the fraction of the $B$ queries of round $Q_i$ that the bidder in position $j$ of the permutation, $\pi(j)$, wins when $a$ runs on the permuted round instance $I_\pi$. Then, with $\pi$ uniform over the $N!$ permutations,
--   $$\mathbb E_\pi[q_{ij}] \le \frac{1}{N-i+1}\ \text{ if } j \ge i, \qquad \mathbb E_\pi[q_{ij}] = 0\ \text{ if } j < i.$$
--
--   This is the core estimate of the proof of Theorem 9: whatever a deterministic algorithm does, it cannot tell apart the $N-i+1$ bidders still bidding in round $i$, so each of them receives on average at most a $1/(N-i+1)$ share of that round.
--
--   **Formalization Note** "Bidder $j$" in the paper is read as the bidder $\pi(j)$ in position $j$ of the permutation; for a fixed label $j$ the claim "if $j < i$ then bidder $j$ bids $0$ for queries in $Q_i$" would be false. "Allocated" counts successful assignments (an interested bidder with budget left). The $j<i$ case is stated as an equality, as printed. Rounds and positions are 1-based, as in the paper; the Lean index of $\pi(j)$ is $j-1$.
-- source:
--   Mehta, Saberi, Vazirani, Vazirani, AdWords and generalized on-line matching, J. ACM (2007), DOI 10.1145/1284320.1284321, p. 15, proof of Theorem 9, third paragraph, display

import Mathlib
import Definitions.Def_AdWordsMSVV_LowerBound_Setting

namespace AdWordsMSVV.LowerBound

theorem expected_fraction_bound (N B : ℕ) (hB : 1 ≤ B) (a : DetAlg N (N * B))
    (i j : ℕ) (hi1 : 1 ≤ i) (hiN : i ≤ N) (hj1 : 1 ≤ j) (hjN : j ≤ N) :
    (i ≤ j →
      permAvg N (fun π =>
        (wonInRound B (roundInstance N B π) a i (π ⟨j - 1, by omega⟩) : ℝ) / B)
        ≤ 1 / ((N : ℝ) - i + 1)) ∧
    (j < i →
      permAvg N (fun π =>
        (wonInRound B (roundInstance N B π) a i (π ⟨j - 1, by omega⟩) : ℝ) / B) = 0) := by sorry

end AdWordsMSVV.LowerBound
