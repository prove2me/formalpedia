-- Prove2me | Theorems.Thm_AdaptiveDynMIS_Main_lemma_3_2
-- name    : AdaptiveDynMIS.Main.lemma_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:55:35.78367+00:00
-- url     : https://prove2.me/theorems/b049cb10-567d-48ef-84be-0db80a62a798
-- title:
--   Lemma 3.2 — in the membership-query game, |S| = O(pk + log((M+1)/η)) at every step with probability ≥ 1 − η
-- statement:
--   Fix $p\in(0,1/2)$, integers $k\ge2$ and $M\ge1$, and $\eta\in(0,1)$. A player takes at most $M$ steps of the membership-query game with universe bound $k$: it inserts fresh elements (each with a hidden independent bit $X_e\sim\mathrm{Bernoulli}(p)$), reveals and deletes elements (learning their bits), and queries elements of $U$ (learning their bits; the first no answer ends the game), choosing each move adaptively from all earlier answers. Then there is a universal constant $C$ such that, with probability at least $1-\eta$, simultaneously after every update or query, including the query that terminates the game,
--   $$|S|\le C\Bigl(pk+\log\frac{M+1}{\eta}\Bigr),\qquad S=\{e\in U: X_e=1\}.$$
--
--   The game captures what membership information leaks about hidden samples; the paper applies it to the reverse lists of the high MIS vertices (Lemma 4.7).
--
--   **Formalization Note.** The probability is over the i.i.d. bits `bitsMeasure p`; the bad event is that the bound fails at one of the states after steps $0,\dots,M$. $\log$ is the natural logarithm.
--
--   Differences from the source:
--   - encoding: $|S|=O(pk+\log\frac{M+1}{\eta})$ → $|S|\le C(pk+\log\frac{M+1}{\eta})$ for one constant $C$ chosen before $p,k,M,\eta$ and the player; reason: the explicit meaning of $O(\cdot)$
--   - encoding: a player choosing adaptively (randomized players included by averaging) → every deterministic strategy on the player's view; reason: a randomized player is a mixture of deterministic ones, and the paper's proof reduces to this case
--   - encoding: elements with names, re-inserted names getting fresh bits, moves that are not allowed → elements indexed by insertion number with bit $X_i$; a move that is not available ends the game; reason: the player's view and the bits are the same
--   - encoding: "simultaneously after every update or query, including the terminating query", "with probability at least $1-\eta$" → the bits on which the bound fails at some state after $j\le M$ steps have measure at most $\eta$; reason: the states after the end are the final state
--   - encoding: the operations insert, reveal-and-delete, membership query → the same moves plus a voluntary stop; reason: the player "takes at most $M$ steps", so stopping early is a player taking fewer steps
--   - encoding: $\log$ (base not stated) → the natural logarithm `Real.log`; reason: a change of base is a constant factor, absorbed by the universal $C$
-- source:
--   Chen, Fan, Zhang, Faster Dynamic Maximal Independent Set against Adaptive Adversaries, arXiv:2611.05932 (PDF sha256 a65b11d9…ec4a), p. 21, Lemma 3.2

import Mathlib
import Definitions.Def_AdaptiveDynMIS_Main_Games

namespace AdaptiveDynMIS.Main

/-- **Lemma 3.2** (Chen, Fan, Zhang, arXiv:2611.05932 (PDF sha256 a65b11d9…ec4a), p. 21 (PDF 23)).
There is a universal constant `C` such that for every `p ∈ (0, 1/2)`, integers `k ≥ 2`, `M ≥ 1`,
`η ∈ (0, 1)` and every deterministic player of the membership-query game with universe bound `k`,
with probability at least `1 - η` over the i.i.d. `Bernoulli(p)` bits, at every state reached in the
first `M` steps (including the state after the terminating query)
`|S| ≤ C · (p k + log((M + 1)/η))`. -/
theorem lemma_3_2 :
    ∃ C : ℝ, ∀ (p : ℝ) (k M : ℕ) (η : ℝ), 0 < p → p < 1 / 2 → 2 ≤ k → 1 ≤ M → 0 < η → η < 1 →
      ∀ A : MemStrategy,
        bitsMeasure p
            {X | ∃ j ≤ M, C * (p * k + Real.log ((M + 1) / η)) <
              ((sampled X (memStateAt k X A j).U).card : ℝ)}
          ≤ ENNReal.ofReal η := by sorry

end AdaptiveDynMIS.Main
