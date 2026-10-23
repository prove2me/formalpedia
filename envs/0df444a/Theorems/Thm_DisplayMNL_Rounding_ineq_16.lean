-- Prove2me | Theorems.Thm_DisplayMNL_Rounding_ineq_16
-- name    : DisplayMNL.Rounding.ineq_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:30:57.74244+00:00
-- url     : https://prove2.me/theorems/1743dc1d-0745-4ba7-8014-048b268dbe53
-- title:
--   Inequality (16), p. 22 — min of R at ẽ_j, ẽ_{j+1} is at least (1 − 8ε)·min{α_j, α_{j+1}}
-- statement:
--   Work under the standing assumptions ($n\ge2$, positive prices, weights and position weights, $\epsilon\in(0,1/5)$), fix a guess $1\le k_{\mathrm{mid}}\le n-1$, a sequence of dynamic-programming actions $(e_j,S^-_j,S^+_j)_{j=1}^T$ feasible for the boundary and root conditions and constraints (8)–(14), and an assignment $\tilde{\mathcal A}$ rounded from it as in §4.4. Then for every $j\in[1,T-1]$
--   $$\min\Big\{R_{\tilde e_j}(\tilde{\mathcal A}),\,R_{\tilde e_{j+1}}(\tilde{\mathcal A})\Big\}\ \ge\ (1-8\epsilon)\cdot\min\left\{\frac{\rho(S^-_j)}{1+w(S^+_j)},\,\frac{\rho(S^-_{j+1})}{1+w(S^+_{j+1})}\right\},$$
--   where $R_k(\tilde{\mathcal A})=\rho(\tilde{\mathcal A}[k])/(1+w(\tilde{\mathcal A}[k]))$ is the revenue of the first $k$ positions.
--
--   This compares the revenue of the rounded assignment at consecutive block boundaries with the DP's proxies, and is applied to every term of the decomposition (15).
--
--   **Formalization Note** The statement holds for every feasible sequence, not only the DP-optimal one, with approximate assortments ranging over all subsets. The hypothesis $k_{\mathrm{mid}}\le n-1$ is added because for $k_{\mathrm{mid}}=n$ the construction of §4.4 can leave items unplaced.
-- source:
--   Aouad & Segev, Display Optimization for Vertically Differentiated Locations Under Multinomial Logit Preferences, SSRN 2709652 (version of 31/07/2019), p. 22, proof of Lemma 5.4, inequality (16)

import Mathlib
import Definitions.Def_DisplayMNL_Rounding_Model

open Finset

namespace DisplayMNL.Rounding

theorem ineq_16 {n : ℕ} (I : Instance n) (ε : ℝ) (kmid : ℕ) (s : DPSeq n) (A : Fin n ≃ Fin n)
    (hst : Standing I ε) (hk1 : 1 ≤ kmid) (hk2 : kmid + 1 ≤ n)
    (hF : IsFeasible I ε kmid s) (hR : IsRounded I s kmid A)
    (j : ℕ) (hj1 : 1 ≤ j) (hjT : j + 1 ≤ s.T) :
    (1 - 8 * ε) * min (alpha I s j) (alpha I s (j + 1)) ≤
      min (revAt I A (etil s kmid j)) (revAt I A (etil s kmid (j + 1))) := by sorry

end DisplayMNL.Rounding
