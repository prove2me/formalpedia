-- Prove2me | Theorems.Thm_DermanDenumerable_AvgCost_lemma1
-- name    : DermanDenumerable.AvgCost.lemma1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T21:20:29.771878+00:00
-- url     : https://prove2.me/theorems/b16d0c18-5825-4161-aded-3fa776194899
-- title:
--   Lemma 1 — a strict improvement at some states strictly lowers the average cost from every initial state
-- statement:
--   Assume (A), (B) and (C) (every rule of $C''$ induces an irreducible, positive recurrent Markov chain). Let $R \in C''$ make decision $k_i$ at state $i$, and suppose (D): a number $g$ and a bounded set $\{v_j\}$ satisfy (2) for $R$,
--   $$g + v_i = w_{ik_i} + \sum_{j\in I} q_{ij}(k_i) v_j, \qquad i \in I.$$
--   Let $R' \in C''$ make decision $k_i'$ at state $i$, where at each state either $k_i' = k_i$, or
--   $$w_{ik_i'} + \sum_{j\in I} q_{ij}(k_i') v_j < w_{ik_i} + \sum_{j\in I} q_{ij}(k_i) v_j, \tag{8}$$
--   and suppose the set $I'$ of states where $k_i' \ne k_i$ is nonempty. Then for every initial state $i$,
--   $$Q_{R'}(i) < Q_R(i).$$
--
--   This justifies the name *policy improvement*: changing the decision of $R$ at a nonempty set of states where it is strictly improvable lowers the average cost everywhere.
--
--   **Formalization Note.** The paper builds $R'$ by keeping $k_i$ wherever (7) holds and choosing $k_i'$ satisfying (8) on a set $I'$ of states where (7) fails. The hypothesis "at each state $k_i' = k_i$ or (8) holds" encodes exactly this: (8) forces $k_i' \ne k_i$ and is impossible where (7) holds, so $I' = \{i : k_i' \ne k_i\}$, and "$I'$ nonempty" is the existence of such a state.
-- source:
--   Derman, Denumerable State Markovian Decision Processes—Average Cost Criterion, Ann. Math. Statist. 37(6) (1966), p. 1550, Lemma 1 (with the construction (7), (8) on pp. 1549–1550)

import Mathlib
import Definitions.Def_DermanDenumerable_AvgCost_Model
open scoped Topology
open Filter SennottDP.AvgFinite

namespace DermanDenumerable.AvgCost

/-- Derman (1966), Lemma 1, p. 1550: let `R = e ∈ C''` and a bounded `{g, v_j}` satisfy (2)
(condition (D)), and let `R' = e'` keep the decision of `R` at every state except those of a
nonempty set `I'`, where its decision satisfies the strict improvement (8). Under (A), (B), (C),
`Q_{R'}(i) < Q_R(i)` for every initial state `i`. -/
theorem lemma1 {S Act : Type} [Countable S] (M : MDC S Act)
    (w : S → Act → ℝ) (hB : CostBounded M w) (hC : CondC M) (e e' : StationaryPolicy M) (g : ℝ)
    (v : S → ℝ) (hv : BddFun v) (hD : IsEvaluation M w e g v)
    (h8 : ∀ i : S, e'.f i = e.f i ∨
      w i (e'.f i) + expNext M i (e'.f i) v < w i (e.f i) + expNext M i (e.f i) v)
    (hI' : ∃ i : S, e'.f i ≠ e.f i) :
    ∀ i : S, avgCostR e'.toPolicy w i < avgCostR e.toPolicy w i := by sorry

end DermanDenumerable.AvgCost
