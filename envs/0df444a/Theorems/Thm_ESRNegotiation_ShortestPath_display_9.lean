-- Prove2me | Theorems.Thm_ESRNegotiation_ShortestPath_display_9
-- name    : ESRNegotiation.ShortestPath.display_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:19:58.855038+00:00
-- url     : https://prove2.me/theorems/48eaa62c-f19d-415e-8e3f-ce40810a2356
-- title:
--   §4.2, display (9) — retailer gain and the path-product objective
-- statement:
--   Let $T$ and $T'$ be feasible ESR implementation structures, each with a full-participation Nash–Nash payment equilibrium. Write $\pi_0(T,\mathbf 1)$ for the retailer's equilibrium gain and $\Gamma(T)=\sum_{v\ne0}\prod_{a\in P_v(T)}\rho_a$. Then
--
--   $$
--   \pi_0(T',\mathbf 1)\le\pi_0(T,\mathbf 1)
--   \quad\Longleftrightarrow\quad
--   \Gamma(T)\le\Gamma(T').
--   $$
--
--   Thus maximizing the retailer's equilibrium gain over feasible structures is equivalent to minimizing the paper's path-product objective in display (9).
--
--   **Formalization Note** The comparison uses actual Nash–Nash equilibria, not a payment vector stipulated to be the closed form. Interior bargaining powers ensure the path products and denominators have the intended positive values.
-- source:
--   Feng, Li, Lu & Shanthikumar, Implementing environmental and social responsibility programs in supply networks through multi-unit bilateral negotiation, accepted manuscript (SSRN 3309518, January 3, 2021; forthcoming in Management Science), p. 20 (PDF 21), §4.2, sentence before display (9) and display (9)

import Mathlib
import Definitions.Def_ESRNegotiation_ShortestPath_Model

namespace ESRNegotiation.ShortestPath

/-- Section 4.2, display (9) and its preceding sentence, p. 20 (PDF 21). -/
theorem display_9 {n : ℕ} (N : Network n) (hN : Standing N)
    (T T' : Structure N) (w w' : Fin (n + 1) → ℝ)
    (hw : IsNashNash N T w) (hw' : IsNashNash N T' w') :
    gain N T' w' 0 ≤ gain N T w 0 ↔ Gamma N T ≤ Gamma N T' := by sorry

end ESRNegotiation.ShortestPath
