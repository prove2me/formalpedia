-- Prove2me | Theorems.Thm_CollectiveTreeExploration_Async_theorem_2_1
-- name    : CollectiveTreeExploration.Async.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:13:24.7022+00:00
-- url     : https://prove2.me/theorems/9b42fa23-05f8-4624-ae2f-de4714bea5a4
-- title:
--   Theorem 2.1 — tree-mining reduction
-- statement:
--   Fix $k\ge1$ and a function $f(k,D)$. Suppose that a continuous tree-mining strategy for $k$ miners maintains a cumulative cost of at most $f(k,D)$ whenever the underlying tree has depth at most $D$. Then there exists a deterministic asynchronous collective tree exploration algorithm for $k$ agents which, for every rooted tree $T$ with $n$ vertices and depth $D$ and every activation sequence, explores $T$ in at most
--   $$2n+f(k,D)\ \text{moves}.$$
--
--   This reduction, due to [CM24], turns any bound on the tree-mining game into an exploration guarantee; with Theorem 2.2 it yields Theorem 1.1.
--
--   Differences from the source:
--   - encoding: a continuous tree-mining strategy with a cumulative-cost guarantee → a history-dependent response function, an independent operational well-formedness predicate, and an extended nonnegative cost for every finite prefix; reason: arbitrary real elongations and every transfer are charged; an illegal response cannot exclude the play from the guarantee
--   - encoding: k mobile agents and all activation sequences → positive natural k, port-addressed finite trees, Fin k agent identities, and legal history-only policies with no fairness condition; reason: positive agent count is the model convention; all source trees and schedules are represented
-- source:
--   Romain Cosson, Laurent Massoulié, Polylogarithmic Collective Tree Exploration, STOC 2027 submission #263 (October 2026), source.pdf sha256 54f5e43ddf9269e11a2fff4aa4b0ea62348afe16a38aba551313f43cbf3e00e0; Theorem 2.1, p.6 (attributed to [CM24]); game of §2.2, p.6

import Mathlib
import Definitions.Def_CollectiveTreeExploration_Async_Exploration
import Definitions.Def_CollectiveTreeExploration_Async_TreeMining

namespace CollectiveTreeExploration.Async

open scoped BigOperators ENNReal

/-- **Theorem 2.1** (tree-mining reduction, [CM24]; p.6). If a continuous tree-mining strategy for
`k` miners maintains a cumulative cost of at most `f(k, D)` whenever the tree has depth at most
`D`, then some asynchronous collective tree exploration algorithm for `k` agents explores every
tree with `n` vertices and depth `D` in at most `2n + f(k, D)` moves, under every activation
sequence. -/
theorem theorem_2_1 (k : ℕ) (hk : 1 ≤ k) (f : ℕ → ℝ → ℝ) (S : CTMStrategy k) (hS : MaintainsCost S (f k)) :
    ∃ A : ExplorationAlgorithm k, LegalExploration A ∧ ∀ (T : ExpTree) (σ : ℕ → Fin k), ∃ N : ℕ,
      ExploredBy A T σ N ∧ (N : ℝ) ≤ 2 * (T.size : ℝ) + f k (T.depth : ℝ) := by sorry

end CollectiveTreeExploration.Async
