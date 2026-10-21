-- Prove2me | Theorems.Thm_FlowsNetworks_DynamicFlow_chain_length_bound
-- name    : FlowsNetworks.DynamicFlow.chain_length_bound
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:37:59.808016+00:00
-- url     : https://prove2.me/theorems/4170ea17-51bb-4e93-a067-ea043f4f2d56
-- title:
--   Chapter III, Theorem 3.5 — every chain from s to t has a + γ length at least p, with equality and a positive γ on flow-carrying chains
-- statement:
--   Let $[N; \mathcal A]$ be a network with positive integer capacities $c(x, y)$ and nonnegative integer arc costs $a(x, y)$, with distinct nodes $s$ and $t$, and let $p \ge 0$ be an integer. Let $f$ be an integral flow from $s$ to $t$ and $\pi$ integer node numbers satisfying the optimality properties (3.18)–(3.20) for the $p$-th related program, and let $\gamma(x, y) = \max(0, \pi(y) - \pi(x) - a(x, y))$ be the arc numbers.
--
--   Let $x_1, x_2, \dots, x_k$ ($x_1 = s$, $x_k = t$) be any chain from $s$ to $t$. Then
--   $$\sum_{i=1}^{k-1} [a(x_i, x_{i+1}) + \gamma(x_i, x_{i+1})] \ge p. \qquad (3.35)$$
--   If $f(x_i, x_{i+1}) > 0$ for all arcs of the chain, then equality holds in (3.35). If moreover $p \ge 1$ and $f$ also satisfies (3.18)–(3.20) for the $(p-1)$-th related program with some integer node numbers $\pi'$, then $\gamma(x_i, x_{i+1}) > 0$ for some arc of the chain.
--
--   The book states this for $f_p$, $\pi_p$, the outputs of the routine. By Theorem 3.1, $f_p$ satisfies the optimality properties for the $p$-th related program with $\pi_p$, and for the $(p-1)$-th with $\pi_{p-1}$ ("so do $\pi_{p-1}$ and $f_p$").
--
--   **Formalization Note** The routine is not formalized; $f_p$ is represented by what Theorem 3.1 says of it. The clause "$\gamma_p(x_i, x_{i+1}) > 0$ for some arc of the chain" carries the extra hypothesis that $f$ is also optimal, with some $\pi'$, for the $(p-1)$-th program, which the routine's $f_p$ is; without it the clause is false (one arc $(s, t)$ with $c = a = 1$, $p = 1$, $f(s, t) = 1$, $\pi(s) = 0$, $\pi(t) = 1$ gives $\gamma = 0$; finding F3). For $p = 0$ the routine's $f_0 = 0$, so the clause is vacuous there and is stated only for $p \ge 1$. The chain is a list of distinct nodes; sums along it are over consecutive pairs.
-- source:
--   Ford & Fulkerson, Flows in Networks, RAND Report R-375-PR (1962), Chapter III, p. 48, Theorem 3.5

import Mathlib
import Definitions.Def_FlowsNetworks_DynamicFlow_Network

namespace FlowsNetworks.DynamicFlow

/-- Chapter III, Theorem 3.5 (p. 48), stated for any integral flow `f` and integer node numbers
`π` satisfying the optimality properties (3.18)–(3.20) for the `p`-th related program, with
`γ(x, y) = max(0, π(y) − π(x) − a(x, y))` (by Theorem 3.1, `f_p, π_p` are such a pair).
For every chain `x₁, …, x_k` from `s` to `t`,
(3.35) `∑_{i=1}^{k−1} [a(x_i, x_{i+1}) + γ(x_i, x_{i+1})] ≥ p`, and if `f(x_i, x_{i+1}) > 0` on
every arc of the chain, equality holds in (3.35). The clause "`γ(x_i, x_{i+1}) > 0` for some arc"
is a property of the routine's `f_p`: it is stated for `p ≥ 1` under the further hypothesis that
`f` also satisfies (3.18)–(3.20) for the `(p − 1)`-th related program with some integer node
numbers `π'`, which Theorem 3.1 gives for `f_p` with `π_{p−1}` ("so do `π_{p−1}` and `f_p`").
(For `p = 0` the routine's `f_0 = 0` and the clause is vacuous; without `π'` it is false, F3.) -/
theorem chain_length_bound {N : Type} [Fintype N] [DecidableEq N]
    (G : Network N) (s t : N) (hst : s ≠ t) (p : ℕ)
    (f : N → N → ℝ) (v : ℝ) (hf : IsStaticFlow G s t f v) (hint : IsIntegral f)
    (π : N → ℤ) (hπ : OptimalityProperties G s t p f π)
    (l : List N) (hl : IsChainFromTo G s t l) :
    (p : ℤ) ≤ chainSum (fun x y => (G.cost x y : ℤ) + arcNumber G π x y) l ∧
    ((∀ (i : ℕ) (h : i + 1 < l.length), 0 < f l[i] l[i + 1]) →
      chainSum (fun x y => (G.cost x y : ℤ) + arcNumber G π x y) l = (p : ℤ)) ∧
    (1 ≤ p → ∀ π' : N → ℤ, OptimalityProperties G s t (p - 1) f π' →
      (∀ (i : ℕ) (h : i + 1 < l.length), 0 < f l[i] l[i + 1]) →
      ∃ (i : ℕ) (h : i + 1 < l.length), 0 < arcNumber G π l[i] l[i + 1]) := by sorry

end FlowsNetworks.DynamicFlow
