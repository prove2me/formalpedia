-- Prove2me | Theorems.Thm_ESRNegotiation_ShortestPath_theorem_2
-- name    : ESRNegotiation.ShortestPath.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:19:59.713001+00:00
-- url     : https://prove2.me/theorems/9704d424-d85f-492f-841e-afac265bae77
-- title:
--   Theorem 2 — a log-cost shortest path tree is optimal
-- statement:
--   In a feasible ESR implementation tree, the cost of a negotiation arc $(i,j)$ is $d_{i,j}=\log\rho_{i,j}$, where $\rho_{i,j}$ is the upstream-to-downstream bargaining-power ratio. Suppose $T^*$ is a shortest path tree in the ESR network: its retailer-to-firm route has no greater cost than any simple directed ESR route to the same firm. Then
--
--   $$
--   \Gamma(T^*)\le\Gamma(T)
--   \qquad\text{for every feasible structure }T.
--   $$
--
--   For any full-participation Nash–Nash equilibria on $T^*$ and $T$, the retailer's gain also satisfies $\pi_0(T,\mathbf 1)\le\pi_0(T^*,\mathbf 1)$. Hence a log-cost shortest path tree is the retailer's preferred implementation structure.
--
--   **Formalization Note** The $\Gamma$ inequality is Theorem 2 as printed. The retailer-gain clause combines it with the paper's §4.2 interpretation and Corollary 1. The power interval is restricted to $0<\theta_{i,j}<1$ so the logarithm is defined as intended; feasible structures are rooted spanning trees, and paths compared for shortestness are simple.
-- source:
--   Feng, Li, Lu & Shanthikumar, Implementing environmental and social responsibility programs in supply networks through multi-unit bilateral negotiation, accepted manuscript (SSRN 3309518, January 3, 2021; forthcoming in Management Science), pp. 20–21 (PDF 21–22), Theorem 2 and §4.2

import Mathlib
import Definitions.Def_ESRNegotiation_ShortestPath_Model

namespace ESRNegotiation.ShortestPath

/-- Theorem 2, pp. 20–21 (PDF 21–22), with its retailer-gain reading. -/
theorem theorem_2 {n : ℕ} (N : Network n) (hN : Standing N)
    (Tstar : Structure N) (hshort : IsShortestPathTree N Tstar) :
    (∀ T : Structure N, Gamma N Tstar ≤ Gamma N T) ∧
    (∀ T : Structure N, ∀ wstar w : Fin (n + 1) → ℝ,
      IsNashNash N Tstar wstar → IsNashNash N T w →
        gain N T w 0 ≤ gain N Tstar wstar 0) := by sorry

end ESRNegotiation.ShortestPath
