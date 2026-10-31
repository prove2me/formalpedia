-- Prove2me | Theorems.Thm_DisplayMNL_Rounding_claim_5_5
-- name    : DisplayMNL.Rounding.claim_5_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:31:07.271704+00:00
-- url     : https://prove2.me/theorems/4513cb7a-ca81-4a82-946d-20feb8f07286
-- title:
--   Claim 5.5, p. 22 — k ↦ R_k(Ã) is unimodal over [ẽ_j, ẽ_{j+1}]
-- statement:
--   Work under the standing assumptions ($n\ge2$, positive prices, weights and position weights, $\epsilon\in(0,1/5)$), fix a guess $1\le k_{\mathrm{mid}}\le n-1$, a sequence of dynamic-programming actions $(e_j,S^-_j,S^+_j)_{j=1}^T$ feasible for the boundary and root conditions and constraints (8)–(14), and an assignment $\tilde{\mathcal A}$ rounded from it as in §4.4. Then for every $j\in[T-1]$ the function
--   $$k\ \longmapsto\ R_k(\tilde{\mathcal A})=\frac{\rho(\tilde{\mathcal A}[k])}{1+w(\tilde{\mathcal A}[k])}$$
--   is unimodal over the integer interval $[\tilde e_j,\tilde e_{j+1}]$: for some $m$ in this interval it is non-decreasing on $[\tilde e_j,m]$ and non-increasing on $[m,\tilde e_{j+1}]$.
--
--   Unimodality lets each position's revenue in a block be bounded below by the smaller of the two block-boundary revenues, which is the decomposition (15).
--
--   **Formalization Note** "Rounded" allows any order among items of equal price inside a block. The statement holds for every feasible sequence, not only the DP-optimal one. The hypothesis $k_{\mathrm{mid}}\le n-1$ is added because for $k_{\mathrm{mid}}=n$ the construction of §4.4 can leave items unplaced.
-- source:
--   Aouad & Segev, Display Optimization for Vertically Differentiated Locations Under Multinomial Logit Preferences, SSRN 2709652 (version of 31/07/2019), p. 22, Claim 5.5 (proof: App. C.7, p. 49)

import Mathlib
import Definitions.Def_DisplayMNL_Rounding_Model

open Finset

namespace DisplayMNL.Rounding

theorem claim_5_5 {n : ℕ} (I : Instance n) (ε : ℝ) (kmid : ℕ) (s : DPSeq n) (A : Fin n ≃ Fin n)
    (hst : Standing I ε) (hk1 : 1 ≤ kmid) (hk2 : kmid + 1 ≤ n)
    (hF : IsFeasible I ε kmid s) (hR : IsRounded I s kmid A)
    (j : ℕ) (hj1 : 1 ≤ j) (hjT : j + 1 ≤ s.T) :
    IsUnimodalOn (revAt I A) (etil s kmid j) (etil s kmid (j + 1)) := by sorry

end DisplayMNL.Rounding
