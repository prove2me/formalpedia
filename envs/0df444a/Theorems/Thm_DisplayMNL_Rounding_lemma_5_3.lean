-- Prove2me | Theorems.Thm_DisplayMNL_Rounding_lemma_5_3
-- name    : DisplayMNL.Rounding.lemma_5_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:30:55.743995+00:00
-- url     : https://prove2.me/theorems/d2b933cf-e48b-4087-81ff-5de041b8ada6
-- title:
--   Lemma 5.3, p. 22 — the prefix of Ã up to ẽ_j weighs at most w(S⁺_j)
-- statement:
--   Work under the standing assumptions ($n\ge2$, positive prices, weights and position weights, $\epsilon\in(0,1/5)$), fix a guess $1\le k_{\mathrm{mid}}\le n-1$, a sequence of dynamic-programming actions $(e_j,S^-_j,S^+_j)_{j=1}^T$ feasible for the boundary and root conditions and constraints (8)–(14), and an assignment $\tilde{\mathcal A}$ rounded from it as in §4.4. Then for every $j\in[T]$
--   $$w(\tilde{\mathcal A}[\tilde e_j])\le w(S^+_j).$$
--
--   Together with Lemma 5.2 it shows that the revenue of the rounded assignment at the positions $\tilde e_j$ is at least about the DP's proxy $\rho(S^-_j)/(1+w(S^+_j))$.
--
--   **Formalization Note** The statement holds for every feasible sequence, not only the DP-optimal one, with approximate assortments ranging over all subsets. The hypothesis $k_{\mathrm{mid}}\le n-1$ is added because for $k_{\mathrm{mid}}=n$ the construction of §4.4 can leave items unplaced.
-- source:
--   Aouad & Segev, Display Optimization for Vertically Differentiated Locations Under Multinomial Logit Preferences, SSRN 2709652 (version of 31/07/2019), p. 22, Lemma 5.3 (proof: App. C.6, pp. 48–49)

import Mathlib
import Definitions.Def_DisplayMNL_Rounding_Model

open Finset

namespace DisplayMNL.Rounding

theorem lemma_5_3 {n : ℕ} (I : Instance n) (ε : ℝ) (kmid : ℕ) (s : DPSeq n) (A : Fin n ≃ Fin n)
    (hst : Standing I ε) (hk1 : 1 ≤ kmid) (hk2 : kmid + 1 ≤ n)
    (hF : IsFeasible I ε kmid s) (hR : IsRounded I s kmid A)
    (j : ℕ) (hj1 : 1 ≤ j) (hjT : j ≤ s.T) :
    wt I (pre A (etil s kmid j)) ≤ wt I (s.sp j) := by sorry

end DisplayMNL.Rounding
