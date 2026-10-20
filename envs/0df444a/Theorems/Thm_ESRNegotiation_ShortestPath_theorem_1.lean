-- Prove2me | Theorems.Thm_ESRNegotiation_ShortestPath_theorem_1
-- name    : ESRNegotiation.ShortestPath.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:19:57.304391+00:00
-- url     : https://prove2.me/theorems/3ffecfa6-ecc7-4d4f-aaf1-614258fd89a8
-- title:
--   Theorem 1 — equilibrium payments and positive gains
-- statement:
--   Let $T$ be a feasible ESR implementation tree with positive total surplus $\Pi$, nonnegative investment costs, and interior bargaining powers on its arcs. For a supplier $j$, let $S_j(T)$ comprise $j$ and all firms downstream of it in the tree. The all-investment equilibrium payment from its parent to $j$ is
--
--   $$
--   w^*_{\operatorname{par}(j),j}(\mathbf 1)=
--   \frac{\sum_{v\in S_j(T)}\prod_{a\in P_v(T)}\rho_a}{1+\Gamma(T)}\Pi
--   +\sum_{v\in S_j(T)}c_v.
--   $$
--
--   These payments form a Nash–Nash equilibrium at full participation, every firm's gain is strictly positive, and every Nash–Nash payment profile at full participation agrees on the supplier payments. The contingent contracts pay zero whenever at least one firm does not invest; each firm's gain in that event is nonpositive.
--
--   This is the payment and Pareto-dominance statement from which the paper derives its gain allocation.
--
--   **Formalization Note** The Lean equilibrium is evaluated at $x=\mathbf 1$; the contingent payment rule covers other binary investment profiles. The paper allows endpoint powers in $[0,1]$, while this mission requires $0<\theta<1$ to define $\rho$ and its logarithm. Structures are rooted spanning trees as described in the text.
-- source:
--   Feng, Li, Lu & Shanthikumar, Implementing environmental and social responsibility programs in supply networks through multi-unit bilateral negotiation, accepted manuscript (SSRN 3309518, January 3, 2021; forthcoming in Management Science), p. 17 (PDF 18), Theorem 1

import Mathlib
import Definitions.Def_ESRNegotiation_ShortestPath_Model

namespace ESRNegotiation.ShortestPath

/-- Theorem 1, p. 17 (PDF 18), at universal participation. -/
theorem theorem_1 {n : ℕ} (N : Network n) (hN : Standing N)
    (T : Structure N) :
    IsNashNash N T (wStar N T) ∧
    (∀ i : Fin (n + 1), 0 < gain N T (wStar N T) i) ∧
    (∀ w : Fin (n + 1) → ℝ, IsNashNash N T w →
      ∀ j : Fin (n + 1), j ≠ 0 → w j = wStar N T j) ∧
    (∀ x : Fin (n + 1) → Bool, (∃ i, x i = false) →
      ∀ i : Fin (n + 1),
        gainX N T (contingentWStar N T) x i ≤ 0) := by sorry

end ESRNegotiation.ShortestPath
