-- Prove2me | Theorems.Thm_AdaptiveDynMIS_Main_lemma_3_5
-- name    : AdaptiveDynMIS.Main.lemma_3_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:55:42.935431+00:00
-- url     : https://prove2.me/theorems/538a7904-4794-4b1a-8d16-6099389d09ef
-- title:
--   Lemma 3.5 — in the emptiness-query game, |S| = O(pk + log((M+1)/η)) and S = ∅ ⇒ |U| = O(p⁻¹ log((M+1)/η)) at every step w.p. ≥ 1 − η
-- statement:
--   Fix $p\in(0,1]$, integers $k\ge1$ and $M\ge1$, and $\eta\in(0,1)$. A player takes at most $M$ steps of the emptiness-query game with universe bound $k$: it inserts fresh elements (each with a hidden independent bit $X_e\sim\mathrm{Bernoulli}(p)$), deletes elements without learning anything, and asks whether $S$ is empty (the first empty answer ends the game), choosing each move adaptively from all earlier answers, and it may stop voluntarily. Then there is a universal constant $C$ such that, with probability at least $1-\eta$, simultaneously after every update or query, including the query that terminates the game,
--   $$|S|\le C\Bigl(pk+\log\frac{M+1}{\eta}\Bigr),\qquad S=\emptyset\ \Longrightarrow\ |U|\le C\,p^{-1}\log\frac{M+1}{\eta}.$$
--   The second implication holds whether or not the player asks an emptiness query at that state.
--
--   The game is the paper's tool for high domination edge lists (Lemma 4.8): an empty sampled list reveals that few high MIS neighbours exist.
--
--   **Formalization Note.** The probability is over the i.i.d. bits `bitsMeasure p`; the bad event is that one of the two bounds fails at one of the states after steps $0,\dots,M$, whatever the move at that step. $\log$ is the natural logarithm.
--
--   Differences from the source:
--   - encoding: the two $O(\cdot)$ bounds → $|S|\le C(pk+\log\frac{M+1}{\eta})$ and $|U|\le C\,p^{-1}\log\frac{M+1}{\eta}$ with one constant $C$ chosen before $p,k,M,\eta$ and the player; reason: the explicit meaning of $O(\cdot)$
--   - encoding: a player choosing adaptively (randomized players included by averaging) → every deterministic strategy on the player's view; reason: a randomized player is a mixture of deterministic ones, and the paper's proof reduces to this case
--   - encoding: elements with names, re-inserted names getting fresh bits, moves that are not allowed → elements indexed by insertion number with bit $X_i$; a move that is not available ends the game; reason: the player's view and the bits are the same
--   - encoding: "simultaneously after every update or query, including the terminating query", "with probability at least $1-\eta$" → the bits on which a bound fails at some state after $j\le M$ steps have measure at most $\eta$; reason: the states after the end are the final state
--   - encoding: $\log$ (base not stated) → the natural logarithm `Real.log`; reason: a change of base is a constant factor, absorbed by the universal $C$
-- source:
--   Chen, Fan, Zhang, Faster Dynamic Maximal Independent Set against Adaptive Adversaries, arXiv:2611.05932 (PDF sha256 a65b11d9…ec4a), pp. 22–23, Lemma 3.5

import Mathlib
import Definitions.Def_AdaptiveDynMIS_Main_Games

namespace AdaptiveDynMIS.Main

/-- **Lemma 3.5** (Chen, Fan, Zhang, arXiv:2611.05932 (PDF sha256 a65b11d9…ec4a), pp. 22–23
(PDF 24–25)). There is a universal constant `C` such that for every `p ∈ (0, 1]`, integers `k ≥ 1`,
`M ≥ 1`, `η ∈ (0, 1)` and every deterministic player of the emptiness-query game with universe bound
`k`, with probability at least `1 - η` over the i.i.d. `Bernoulli(p)` bits, at every state reached in
the first `M` steps (including the state after the terminating query, and whether or not a query is
asked there) `|S| ≤ C · (p k + log((M + 1)/η))`, and `S = ∅` implies
`|U| ≤ C · p⁻¹ · log((M + 1)/η)`. -/
theorem lemma_3_5 :
    ∃ C : ℝ, ∀ (p : ℝ) (k M : ℕ) (η : ℝ), 0 < p → p ≤ 1 → 1 ≤ k → 1 ≤ M → 0 < η → η < 1 →
      ∀ A : EmpStrategy,
        bitsMeasure p
            {X | ∃ j ≤ M,
              C * (p * k + Real.log ((M + 1) / η)) <
                  ((sampled X (empStateAt k X A j).U).card : ℝ) ∨
                (sampled X (empStateAt k X A j).U = ∅ ∧
                  C * (p⁻¹ * Real.log ((M + 1) / η)) < ((empStateAt k X A j).U.card : ℝ))}
          ≤ ENNReal.ofReal η := by sorry

end AdaptiveDynMIS.Main
