-- Prove2me | Theorems.Thm_DisplayMNL_Rounding_lemma_5_3_subset
-- name    : DisplayMNL.Rounding.lemma_5_3_subset
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:30:59.139998+00:00
-- url     : https://prove2.me/theorems/c7498515-c8e6-46c3-8427-11fcf85056ea
-- title:
--   App. C.6, p. 48, proof of Lemma 5.3 — the prefix of Ã up to ẽ_j is contained in S⁺_j
-- statement:
--   Work under the standing assumptions ($n\ge2$, positive prices, weights and position weights, $\epsilon\in(0,1/5)$), fix a guess $1\le k_{\mathrm{mid}}\le n-1$, a sequence of dynamic-programming actions $(e_j,S^-_j,S^+_j)_{j=1}^T$ feasible for the boundary and root conditions and constraints (8)–(14), and an assignment $\tilde{\mathcal A}$ rounded from it as in §4.4. Then for every $j\in[T]$
--   $$\tilde{\mathcal A}[\tilde e_j]\subseteq S^+_j ,$$
--   where $\tilde e_j=|\Delta_1\cup\dots\cup\Delta_j|$ and $\tilde{\mathcal A}[k]$ is the set of items in positions $1,\dots,k$.
--
--   This set inclusion is the content of Lemma 5.3, which follows from it by taking weights.
--
--   **Formalization Note** The statement holds for every feasible sequence, not only the DP-optimal one used in the paper, and the approximate assortments range over all subsets of items. The hypothesis $k_{\mathrm{mid}}\le n-1$ is added because for $k_{\mathrm{mid}}=n$ the construction of §4.4 can leave items unplaced, in which case no rounded assignment exists.
-- source:
--   Aouad & Segev, Display Optimization for Vertically Differentiated Locations Under Multinomial Logit Preferences, SSRN 2709652 (version of 31/07/2019), p. 48, App. C.6, proof of Lemma 5.3 (first sentence)

import Mathlib
import Definitions.Def_DisplayMNL_Rounding_Model

open Finset

namespace DisplayMNL.Rounding

theorem lemma_5_3_subset {n : ℕ} (I : Instance n) (ε : ℝ) (kmid : ℕ) (s : DPSeq n) (A : Fin n ≃ Fin n)
    (hst : Standing I ε) (hk1 : 1 ≤ kmid) (hk2 : kmid + 1 ≤ n)
    (hF : IsFeasible I ε kmid s) (hR : IsRounded I s kmid A)
    (j : ℕ) (hj1 : 1 ≤ j) (hjT : j ≤ s.T) :
    pre A (etil s kmid j) ⊆ s.sp j := by sorry

end DisplayMNL.Rounding
