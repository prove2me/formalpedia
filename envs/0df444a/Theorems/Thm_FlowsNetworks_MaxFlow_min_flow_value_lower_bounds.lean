-- Prove2me | Theorems.Thm_FlowsNetworks_MaxFlow_min_flow_value_lower_bounds
-- name    : FlowsNetworks.MaxFlow.min_flow_value_lower_bounds
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:36:04.706579+00:00
-- url     : https://prove2.me/theorems/9cbd7430-291c-4455-a29d-f1328f664d27
-- title:
--   Chapter I, Theorem 9.2 — minimal flow value with lower bounds equals the maximum of $\ell(X, \bar X) - c(\bar X, X)$
-- statement:
--   Let $[N; \mathcal A]$ be a network with capacities $c$, let $s \neq t$, and let $\ell$ be a real function on the arcs with
--   $$0 \le \ell(x, y) \le c(x, y) \quad \text{for all } (x, y) \in \mathcal A. \qquad (9.3)$$
--   Consider functions $f$ on the arcs satisfying the conservation equations (2.1) for a number $v$ (net flow $v$ out of $s$, $-v$ out of $t$, $0$ out of every other node) and the bounds
--   $$\ell(x, y) \le f(x, y) \le c(x, y) \quad \text{for all } (x, y) \in \mathcal A. \qquad (9.2)$$
--   If there is such a function $f$ for some number $v$, then the minimal value of $v$ subject to these constraints is attained and equals the maximum, also attained, of
--   $$\ell(X, \bar X) - c(\bar X, X)$$
--   over all $X \subseteq N$ with $s \in X$, $t \in \bar X$.
--
--   This is the analogue of the max flow min cut theorem for the minimal flow through a network with lower bounds on the arc flows.
--
--   **Formalization Note** The book's "two distinguished nodes" $s, t$ are assumed distinct ($s \neq t$). The standing condition (9.3) of §9 is a hypothesis. The functions $f$ vanish off $\mathcal A$. "Minimal value" and "maximum" are stated as attained (`IsLeast`, `IsGreatest`) for one common real number; the value $v$ may be negative.
-- source:
--   Ford & Fulkerson, Flows in Networks, RAND Report R-375-PR (1962), Chapter I, p. 39, Theorem 9.2 (with (9.2)–(9.3) on the preceding page)

import Mathlib
import Definitions.Def_FlowsNetworks_MaxFlow_Network

namespace FlowsNetworks.MaxFlow

/-- Ford–Fulkerson, *Flows in Networks*, Chapter I, Theorem 9.2 (p. 39): let `ℓ` satisfy
(9.3) `0 ≤ ℓ(x, y) ≤ c(x, y)` on every arc. If there is a function `f` satisfying (2.1) and
(9.2) `ℓ ≤ f ≤ c` for some number `v`, then the minimal value of `v` subject to these
constraints is equal to the maximum of `ℓ(X, X̄) − c(X̄, X)` taken over all `X ⊆ N` with
`s ∈ X`, `t ∈ X̄`. Both extrema are attained. -/
theorem min_flow_value_lower_bounds {N : Type} [Fintype N] [DecidableEq N]
    (G : Network N) (s t : N) (hst : s ≠ t) (ℓ : N → N → ℝ)
    (hℓ : ∀ p ∈ G.arcs, 0 ≤ ℓ p.1 p.2 ∧ ℓ p.1 p.2 ≤ G.cap p.1 p.2)
    (hfeas : ∃ (f : N → N → ℝ) (v : ℝ), IsBoundedFlow G ℓ s t f v) :
    ∃ v₀ : ℝ,
      IsLeast {v : ℝ | ∃ f : N → N → ℝ, IsBoundedFlow G ℓ s t f v} v₀ ∧
      IsGreatest {κ : ℝ | ∃ X : Finset N, s ∈ X ∧ t ∉ X ∧
        κ = arcSum G ℓ X Xᶜ - arcSum G G.cap Xᶜ X} v₀ := by sorry

end FlowsNetworks.MaxFlow
