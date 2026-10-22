-- Prove2me | Theorems.Thm_FlowsNetworks_DynamicFlow_maximal_min_cost_of_large_p
-- name    : FlowsNetworks.DynamicFlow.maximal_min_cost_of_large_p
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:38:08.715437+00:00
-- url     : https://prove2.me/theorems/b3ea2a22-a8c1-44e8-9dcd-0c5f678d1e92
-- title:
--   Chapter III, Corollary 3.3 — for p above every path cost the flow is maximal of minimal cost
-- statement:
--   Let $[N; \mathcal A]$ be a network with positive integer capacities $c(x, y)$ and nonnegative integer arc costs $a(x, y)$, with distinct nodes $s$ and $t$, and let $p \ge 0$ be an integer. Let $f$ be an integral flow from $s$ to $t$ of value $v$ and $\pi$ integer node numbers satisfying the optimality properties (3.18)–(3.20) for the $p$-th related program ($\pi(s) = 0$, $\pi(t) = p$, $f(x, y) = 0$ when $\pi(y) - \pi(x) < a(x, y)$, $f(x, y) = c(x, y)$ when $\pi(y) - \pi(x) > a(x, y)$).
--
--   The **path cost** of a path from $s$ to $t$ (distinct nodes, each step along a forward or a reverse arc) is the total cost of its forward arcs minus the total cost of its reverse arcs. If $p$ is greater than the path cost of every path from $s$ to $t$, then
--   1. $f$ is a maximal flow: $v' \le v$ for every flow from $s$ to $t$ of value $v'$;
--   2. $f$ minimizes cost over all maximal flows: $\sum_{\mathcal A} a f \le \sum_{\mathcal A} a f'$ for every flow $f'$ from $s$ to $t$ of value $v$.
--
--   In the book the flow is $f_p$, the output of the minimal cost flow routine, which satisfies the optimality properties with $\pi_p$ by Theorem 3.1.
--
--   **Formalization Note** "Greater than the maximal path cost" is stated as "greater than the cost of every path", which agrees whenever a path from $s$ to $t$ exists. The routine is not formalized (see Corollary 3.2's note). Flows are in Chapter I's net form.
-- source:
--   Ford & Fulkerson, Flows in Networks, RAND Report R-375-PR (1962), Chapter III, p. 43, Corollary 3.3 (path cost defined on p. 43; paths, Chapter I, p. 5)

import Mathlib
import Definitions.Def_FlowsNetworks_DynamicFlow_Network

namespace FlowsNetworks.DynamicFlow

/-- Chapter III, Corollary 3.3 (p. 43), stated for any integral flow `f` and integer node numbers
`π` satisfying the optimality properties (3.18)–(3.20) for the `p`-th related program (which
`f_p, π_p` satisfy by Theorem 3.1). If `p` is greater than the path cost of every path from `s`
to `t`, then `f` is a maximal flow and minimizes the total cost `∑_𝒜 a(x, y) f(x, y)` over all
maximal flows. -/
theorem maximal_min_cost_of_large_p {N : Type} [Fintype N] [DecidableEq N]
    (G : Network N) (s t : N) (hst : s ≠ t) (p : ℕ)
    (f : N → N → ℝ) (v : ℝ) (hf : IsStaticFlow G s t f v) (hint : IsIntegral f)
    (π : N → ℤ) (hπ : OptimalityProperties G s t p f π)
    (hp : ∀ (n : ℕ) (x : Fin (n + 1) → N) (fwd : Fin n → Bool),
      IsPathFromTo G s t x fwd → pathCost G x fwd < (p : ℤ)) :
    (∀ (f' : N → N → ℝ) (v' : ℝ), IsStaticFlow G s t f' v' → v' ≤ v) ∧
    (∀ f' : N → N → ℝ, IsStaticFlow G s t f' v → totalCost G f ≤ totalCost G f') := by sorry

end FlowsNetworks.DynamicFlow
