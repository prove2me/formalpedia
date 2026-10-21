-- Prove2me | Theorems.Thm_FlowsNetworks_DynamicFlow_temporally_repeated_maximal
-- name    : FlowsNetworks.DynamicFlow.temporally_repeated_maximal
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:38:53.562931+00:00
-- url     : https://prove2.me/theorems/fe060af0-77c6-43ba-9d85-db1d6c3e6cda
-- title:
--   Chapter III, "Theorem 8.1" (§9) — temporally repeated flows are maximal dynamic flows, with a minimal dynamic cut
-- statement:
--   Let $[N; \mathcal A]$ be a network with distinct nodes $s$ and $t$, positive integer arc capacities $c(x, y)$ and positive integer traversal times $a(x, y)$, and let $p \ge 0$ be the number of periods. Let $f$ be an integral static flow from $s$ to $t$ of value $v$, and $\pi$ integer node numbers satisfying the optimality properties for the $(p+1)$-th related program:
--   $$\pi(s) = 0,\quad \pi(t) = p + 1,\qquad \pi(y) - \pi(x) < a(x, y) \Rightarrow f(x, y) = 0,\qquad \pi(y) - \pi(x) > a(x, y) \Rightarrow f(x, y) = c(x, y).$$
--   (By Theorem 3.1, the flow $f_{p+1}$ and node integers $\pi_{p+1}$ of the minimal cost flow routine are such a pair.) Then:
--   1. $f$ has a chain decomposition into chain flows $(C_r; h_r)$ from $s$ to $t$;
--   2. for every chain decomposition of $f$, the temporally repeated flow it generates (each chain flow started at every time $\theta$ with $\theta + \sigma_r \le p$, no hold-overs) is a dynamic flow for $p$ periods that is maximal over all dynamic flows for $p$ periods, with value
--   $$v(p) = (p + 1) v - \sum_{\mathcal A} a(x, y) f(x, y);$$
--   3. the cut $(X, \bar X)$ of the time-expanded network $G(p)$ given by
--   $$X = \{x(\tau) \mid \pi(x) \le \tau\} \qquad (9.18)$$
--   is a minimal dynamic cut for $p$ periods.
--
--   This is the book's statement that the static flow $f_{p+1}$ generates a maximal temporally repeated dynamic flow of value $(p+1)v_{p+1} - \sum a f_{p+1}$, and that the cut (9.17) is a minimal dynamic cut. The theorem reduces the maximal dynamic flow problem, a linear program on the time-expanded network, to a minimal cost flow problem on the original network.
--
--   **Formalization Note** The routine is not formalized: $f$ and $\pi$ are any pair satisfying (3.18)–(3.20) for the $(p+1)$-th program, which is what Theorem 3.1 says of $f_{p+1}$, $\pi_{p+1}$ and all that the proof (pp. 87–89) uses. Dynamic flows are the linear program (9.2)–(9.5) with hold-overs as separate nonnegative variables; the maximal value is not defined through (9.6), and "temporally repeated" is the explicit construction from a chain decomposition, so not every dynamic flow is one. The cut is stated as $(X, \bar X)$ with $X$ from (9.18): the printed (9.17) has the upper limit $\tau < \pi(x) - a(x, y)$, which makes the set empty since $a > 0$; the text right after it describes $(X, \bar X)$, whose arcs are those with $\pi(x) \le \tau < \pi(y) - a(x, y)$. A minimal dynamic cut has no crossing hold-over arc (those have infinite capacity) and least capacity among such cuts. Static flows are in Chapter I's net form, so arcs into $s$ and out of $t$ are allowed, as in (9.2) and (9.4).
-- source:
--   Ford & Fulkerson, Flows in Networks, RAND Report R-375-PR (1962), Chapter III, p. 90, Theorem 8.1 (printed so, in §9), with (9.17)–(9.18) on p. 89

import Mathlib
import Definitions.Def_FlowsNetworks_DynamicFlow_Network
import Definitions.Def_FlowsNetworks_DynamicFlow_DynamicFlow

namespace FlowsNetworks.DynamicFlow

/-- Chapter III, "Theorem 8.1" (p. 90, in §9), stated for any integral static flow `f` of value `v`
and integer node numbers `π` satisfying the optimality properties (3.18)–(3.20) for the
`(p + 1)`-th related program (by Theorem 3.1, `f_{p+1}, π_{p+1}` are such a pair). Traversal times
`a(x, y)` are positive integers. Then:
1. `f` has a chain decomposition, and every chain decomposition of `f` generates a temporally
   repeated dynamic flow that is maximal over all dynamic flows for `p` periods, with value
   `v(p) = (p + 1) v − ∑ a(x, y) f(x, y)`;
2. the cut `(X, X̄)` with `X = {x(τ) | π(x) ≤ τ}` of (9.18) is a minimal dynamic cut for `p`
   periods. (The printed (9.17) has the upper limit `π(x) − a(x, y)`, under which the set is
   empty; the text after it describes `(X, X̄)`, which is stated here.) -/
theorem temporally_repeated_maximal {N : Type} [Fintype N] [DecidableEq N]
    (G : Network N) (s t : N) (hst : s ≠ t)
    (hcost : ∀ q ∈ G.arcs, 0 < G.cost q.1 q.2) (p : ℕ)
    (f : N → N → ℝ) (v : ℝ) (hf : IsStaticFlow G s t f v) (hint : IsIntegral f)
    (π : N → ℤ) (hπ : OptimalityProperties G s t (p + 1) f π) :
    (∃ (m : ℕ) (C : Fin m → List N) (h : Fin m → ℝ), IsChainDecomposition G s t f v C h) ∧
    (∀ (m : ℕ) (C : Fin m → List N) (h : Fin m → ℝ), IsChainDecomposition G s t f v C h →
      IsMaximalDynamicFlow G s t p (repeatedFlow G p C h) (fun _ _ => 0)
        (((p : ℝ) + 1) * v - totalCost G f)) ∧
    IsMinimalDynamicCut G s t p (nodeNumberCut π p) := by sorry

end FlowsNetworks.DynamicFlow
