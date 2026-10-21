-- Prove2me | Theorems.Thm_FlowsNetworks_DynamicFlow_related_program_optimality
-- name    : FlowsNetworks.DynamicFlow.related_program_optimality
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:38:04.777796+00:00
-- url     : https://prove2.me/theorems/f3d2a898-9df1-43f6-915a-8ef4eb099164
-- title:
--   Chapter III, Corollary 3.2 — the optimality properties solve the related program and its dual
-- statement:
--   Let $[N; \mathcal A]$ be a network with positive integer capacities $c(x, y)$ and nonnegative integer arc costs $a(x, y)$, with distinct nodes $s$ and $t$, and let $p \ge 0$ be an integer. Let $f$ be an integral flow from $s$ to $t$ of value $v$ and $\pi$ integer node numbers satisfying the optimality properties for the $p$-th related program:
--   $$\pi(s) = 0,\quad \pi(t) = p,\qquad \pi(y) - \pi(x) < a(x, y) \Rightarrow f(x, y) = 0,\qquad \pi(y) - \pi(x) > a(x, y) \Rightarrow f(x, y) = c(x, y).$$
--   Put $\gamma(x, y) = \max(0, \pi(y) - \pi(x) - a(x, y))$. Then:
--   1. $f$ maximizes $p v' - \sum_{\mathcal A} a(x, y) f'(x, y)$ over all flows $f'$ from $s$ to $t$ (of any value $v'$);
--   2. $(\pi, \gamma)$ is feasible for the dual program: $-\pi(s) + \pi(t) = p$, and $\pi(x) - \pi(y) + \gamma(x, y) \ge -a(x, y)$, $\gamma(x, y) \ge 0$ on every arc;
--   3. $(\pi, \gamma)$ minimizes $\sum_{\mathcal A} c(x, y) \gamma'(x, y)$ over all real dual feasible $(\pi', \gamma')$;
--   4. $$p v - \sum_{\mathcal A} a(x, y) f(x, y) = \sum_{\mathcal A} c(x, y) \gamma(x, y). \qquad (3.29)$$
--
--   In the book this is said of the flows $f_p$, $f_{p+1}$ and node integers $\pi_p$ produced by the minimal cost flow routine; by Theorem 3.1 both pairs $(f_p, \pi_p)$ and $(f_{p+1}, \pi_p)$ satisfy the optimality properties, so applying the statement to each gives the book's corollary, including the equality of the two left sides of (3.29).
--
--   **Formalization Note** The routine is not formalized: the statement quantifies over every integral flow and integer node numbers satisfying (3.18)–(3.20), which is what Theorem 3.1 asserts of the routine's outputs. Flows are in Chapter I's net form, which agrees with (3.7)–(3.9) when no arc enters $s$ or leaves $t$ (as §3 arranges); the statement is made for every network. The dual variables of item 3 range over all reals.
-- source:
--   Ford & Fulkerson, Flows in Networks, RAND Report R-375-PR (1962), Chapter III, p. 43, Corollary 3.2 (with Theorem 3.1 and (3.12)–(3.21), pp. 37–38)

import Mathlib
import Definitions.Def_FlowsNetworks_DynamicFlow_Network

namespace FlowsNetworks.DynamicFlow

/-- Chapter III, Corollary 3.2 (p. 43), stated for any integral flow `f` and integer node numbers
`π` satisfying the optimality properties (3.18)–(3.20) for the `p`-th related program (by
Theorem 3.1 the outputs `f_p, π_p` and `f_{p+1}, π_p` of the routine are such pairs). Then `f`
maximizes `pv − ∑_𝒜 a(x, y) f(x, y)` over all flows from `s` to `t`; `π` and the arc integers
`γ(x, y) = max(0, π(y) − π(x) − a(x, y))` are feasible and optimal for the dual (3.12)–(3.15);
and (3.29) `pv − ∑_𝒜 a f = ∑_𝒜 c γ`. -/
theorem related_program_optimality {N : Type} [Fintype N] [DecidableEq N]
    (G : Network N) (s t : N) (hst : s ≠ t) (p : ℕ)
    (f : N → N → ℝ) (v : ℝ) (hf : IsStaticFlow G s t f v) (hint : IsIntegral f)
    (π : N → ℤ) (hπ : OptimalityProperties G s t p f π) :
    (∀ (f' : N → N → ℝ) (v' : ℝ), IsStaticFlow G s t f' v' →
        (p : ℝ) * v' - totalCost G f' ≤ (p : ℝ) * v - totalCost G f) ∧
    IsDualFeasible G s t p (fun x => (π x : ℝ)) (fun x y => (arcNumber G π x y : ℝ)) ∧
    (∀ (π' : N → ℝ) (γ' : N → N → ℝ), IsDualFeasible G s t p π' γ' →
        dualObjective G (fun x y => (arcNumber G π x y : ℝ)) ≤ dualObjective G γ') ∧
    (p : ℝ) * v - totalCost G f = dualObjective G (fun x y => (arcNumber G π x y : ℝ)) := by sorry

end FlowsNetworks.DynamicFlow
