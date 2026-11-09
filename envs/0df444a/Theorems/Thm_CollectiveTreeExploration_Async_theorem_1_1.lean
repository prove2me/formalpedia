-- Prove2me | Theorems.Thm_CollectiveTreeExploration_Async_theorem_1_1
-- name    : CollectiveTreeExploration.Async.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:10:40.065715+00:00
-- url     : https://prove2.me/theorems/0285b07c-4918-49eb-9100-872b8bb9e444
-- title:
--   Theorem 1.1 — asynchronous collective tree exploration with $2n+O(k\log^2(k)D)$ moves, optimal regret
-- statement:
--   **Upper bound.** There is a universal constant $C>0$ such that for every $k\ge2$ there exists a deterministic asynchronous exploration algorithm for $k$ agents that explores any rooted tree with $n$ vertices and depth $D$, for every activation sequence, in at most
--   $$2n+C\,k\log^2(k)\,D\ \text{moves}.$$
--
--   **Optimality.** The normalized regret of $O(\log^2 k)$ is optimal up to a constant factor: there are $c>0$ and $k_0$ such that for every $k\ge k_0$, every deterministic asynchronous exploration algorithm $A$ for $k$ agents has normalized regret
--   $$r(A)\ge c\log^2 k,$$
--   where $r(A)$ is the least $r\ge0$ such that $A$ explores every tree in at most $2n+r\,kD$ moves under every activation sequence (eq. (1)).
--
--   This resolves asynchronous collective tree exploration under unrestricted communication up to a constant factor. The upper bound follows from Theorems 2.1 and 2.2; the lower bound is attributed by the paper to [CM25].
--
--   Differences from the source:
--   - encoding: a deterministic online algorithm on every finite rooted tree, with every activation sequence → a policy on the root degree and revealed history, with independent legality; finite port-addressed trees and Fin k agent identities; reason: labels reveal no hidden subtree, all finite trees are represented, and no termination or cost condition defines a policy
--   - encoding: 2n + O(k log²(k) D) → one constant C > 0, chosen before k, the tree and the activation sequence; reason: the O hides a universal constant
--   - reading: the normalized regret of O(log²(k)) is optimal up to a constant factor → there are c > 0 and k₀ with r(A) ≥ c log² k for every k ≥ k₀ and every deterministic algorithm A, r(A) being the least r with M ≤ 2n + r kD on all trees and activation sequences; reason: the asymptotic (Ω) meaning of optimality of the normalized regret of eq. (1)
-- source:
--   Romain Cosson, Laurent Massoulié, Polylogarithmic Collective Tree Exploration, STOC 2027 submission #263 (October 2026), source.pdf sha256 54f5e43ddf9269e11a2fff4aa4b0ea62348afe16a38aba551313f43cbf3e00e0; Theorem 1.1, p.2; normalized regret eq. (1), p.1; lower bound attributed to [CM25], p.14

import Mathlib
import Definitions.Def_CollectiveTreeExploration_Async_Exploration

namespace CollectiveTreeExploration.Async

open scoped BigOperators ENNReal

/-- **Theorem 1.1** (Cosson–Massoulié, p.2). (Upper bound) There is a universal constant `C` such
that for every `k ≥ 2` some deterministic online asynchronous exploration algorithm explores every
rooted tree with `n` vertices and depth `D`, under every activation sequence, in at most
`2n + C · k log²(k) D` moves. (Optimality) The normalized regret `O(log² k)` is optimal up to a
constant factor: for some `c > 0` and all large `k`, every such algorithm for `k` agents has
normalized regret at least `c log² k`. -/
theorem theorem_1_1 :
    (∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 2 ≤ k → ∃ A : ExplorationAlgorithm k, LegalExploration A ∧
      ∀ (T : ExpTree) (σ : ℕ → Fin k), ∃ N : ℕ, ExploredBy A T σ N ∧
        (N : ℝ) ≤ 2 * (T.size : ℝ) + C * ((k : ℝ) * Real.log k ^ 2 * (T.depth : ℝ))) ∧
    (∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ A : ExplorationAlgorithm k, LegalExploration A →
      ENNReal.ofReal (c * Real.log k ^ 2) ≤ normalizedRegret A) := by sorry

end CollectiveTreeExploration.Async
