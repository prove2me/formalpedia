-- Prove2me | Theorems.Thm_FlowsNetworks_DynamicFlow_max_dynamic_value_increment
-- name    : FlowsNetworks.DynamicFlow.max_dynamic_value_increment
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:38:54.168973+00:00
-- url     : https://prove2.me/theorems/260dc80d-6cc0-41e8-98f8-a6fa0e5bd0e7
-- title:
--   Chapter III, Eq. (9.20) — successive maximal dynamic flow values differ by $v_{p+1}$
-- statement:
--   Let $[N; \mathcal A]$ be a network with distinct nodes $s$ and $t$, positive integer arc capacities $c(x, y)$ and positive integer traversal times $a(x, y)$, and let $p \ge 1$. Write $\bar v(q)$ for the maximal value of a dynamic flow from $s$ to $t$ for $q$ periods. Let $f$ be an integral static flow from $s$ to $t$ of value $v$ that satisfies the optimality properties (3.18)–(3.20) both with integer node numbers $\pi$ for the $(p+1)$-th related program ($\pi(t) = p + 1$) and with integer node numbers $\pi'$ for the $p$-th related program ($\pi'(t) = p$). Then both maximal values $\bar v(p)$ and $\bar v(p-1)$ exist (are attained) and
--   $$\bar v(p) - \bar v(p - 1) = v. \qquad (9.20)$$
--
--   In the book $f = f_{p+1}$ with value $v_{p+1}$; by Theorem 3.1 it satisfies the optimality properties with $\pi_{p+1}$ for the $(p+1)$-th program and with $\pi_p$ for the $p$-th. Since $v_p$ is nondecreasing in $p$, the successive differences of $\bar v(p)$ are nondecreasing, so the piecewise linear curve through the points $(p, \bar v(p))$ is convex.
--
--   **Formalization Note** The routine is not formalized; the two optimality-property hypotheses are what Theorem 3.1 says of $f_{p+1}$. $\bar v(q)$ is the greatest element of the set of dynamic flow values for $q$ periods (stated as attained, not as a supremum); $p \ge 1$ makes $p - 1$ a genuine number of periods.
-- source:
--   Ford & Fulkerson, Flows in Networks, RAND Report R-375-PR (1962), Chapter III, p. 90, Eq. (9.20)

import Mathlib
import Definitions.Def_FlowsNetworks_DynamicFlow_Network
import Definitions.Def_FlowsNetworks_DynamicFlow_DynamicFlow

namespace FlowsNetworks.DynamicFlow

/-- Chapter III, Eq. (9.20) (p. 90): `v̄(p) − v̄(p − 1) = v_{p+1}`, where `v̄(p)` is the maximal
dynamic flow value for `p` periods. Stated for `p ≥ 1` and any integral static flow `f` of value
`v` that, as `f_{p+1}` does by Theorem 3.1, satisfies the optimality properties (3.18)–(3.20) with
some integer node numbers `π` for the `(p + 1)`-th related program and with some integer node
numbers `π'` for the `p`-th. Traversal times are positive integers. Both maximal values exist and
their difference is `v`. -/
theorem max_dynamic_value_increment {N : Type} [Fintype N] [DecidableEq N]
    (G : Network N) (s t : N) (hst : s ≠ t)
    (hcost : ∀ q ∈ G.arcs, 0 < G.cost q.1 q.2) (p : ℕ) (hp : 1 ≤ p)
    (f : N → N → ℝ) (v : ℝ) (hf : IsStaticFlow G s t f v) (hint : IsIntegral f)
    (π π' : N → ℤ) (hπ : OptimalityProperties G s t (p + 1) f π)
    (hπ' : OptimalityProperties G s t p f π') :
    ∃ V V' : ℝ, IsGreatest (dynamicFlowValues G s t p) V ∧
      IsGreatest (dynamicFlowValues G s t (p - 1)) V' ∧ V - V' = v := by sorry

end FlowsNetworks.DynamicFlow
