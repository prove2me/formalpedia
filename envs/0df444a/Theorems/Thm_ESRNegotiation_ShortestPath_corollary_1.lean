-- Prove2me | Theorems.Thm_ESRNegotiation_ShortestPath_corollary_1
-- name    : ESRNegotiation.ShortestPath.corollary_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:19:53.623977+00:00
-- url     : https://prove2.me/theorems/fa61f60a-688a-419b-a52a-15e9cd4e0551
-- title:
--   Corollary 1 — equilibrium gain distribution
-- statement:
--   Fix a feasible ESR implementation tree $T$ and a full-participation Nash–Nash payment equilibrium. Let $P_i(T)$ be the retailer-to-firm route, $\rho_a$ the upstream-to-downstream bargaining-power ratio on arc $a$, and $\Pi>0$ the total ESR surplus. The retailer's and every supplier's gains are
--
--   $$
--   \pi_0(T,\mathbf 1)=\frac{\Pi}{1+\Gamma(T)},\qquad
--   \pi_i(T,\mathbf 1)=\frac{\prod_{a\in P_i(T)}\rho_a}{1+\Gamma(T)}\Pi
--   \quad(i\ne0).
--   $$
--
--   Here $\Gamma(T)$ is the sum of the suppliers' path products. The formulas make the gain allocation depend on the chain of bilateral negotiations linking each firm to the retailer.
--
--   **Formalization Note** The statement applies to every full-participation Nash–Nash payment profile; Theorem 1 identifies its supplier payments. The standing assumptions require interior bargaining powers and a rooted spanning structure.
-- source:
--   Feng, Li, Lu & Shanthikumar, Implementing environmental and social responsibility programs in supply networks through multi-unit bilateral negotiation, accepted manuscript (SSRN 3309518, January 3, 2021; forthcoming in Management Science), p. 17 (PDF 18), Corollary 1, displays (7)–(8)

import Mathlib
import Definitions.Def_ESRNegotiation_ShortestPath_Model

namespace ESRNegotiation.ShortestPath

/-- Corollary 1, displays (7) and (8), p. 17 (PDF 18). -/
theorem corollary_1 {n : ℕ} (N : Network n) (hN : Standing N)
    (T : Structure N) (w : Fin (n + 1) → ℝ) (hw : IsNashNash N T w) :
    gain N T w 0 = PiGain N / (1 + Gamma N T) ∧
    (∀ i : Fin (n + 1), i ≠ 0 →
      gain N T w i = pathProd N T i * PiGain N / (1 + Gamma N T)) := by sorry

end ESRNegotiation.ShortestPath
