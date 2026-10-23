-- Prove2me | Theorems.Thm_DisplayMNL_Rounding_lemma_5_2
-- name    : DisplayMNL.Rounding.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:30:58.978319+00:00
-- url     : https://prove2.me/theorems/af0e5200-ff9a-43ae-9af0-fc7f56c403f0
-- title:
--   Lemma 5.2, p. 22 — ρ(Ã[ẽ_j]) ≥ (1 − 8ε)·ρ(S⁻_j)
-- statement:
--   Work under the standing assumptions ($n\ge2$, positive prices, weights and position weights, $\epsilon\in(0,1/5)$), fix a guess $1\le k_{\mathrm{mid}}\le n-1$, a sequence of dynamic-programming actions $(e_j,S^-_j,S^+_j)_{j=1}^T$ feasible for the boundary and root conditions and constraints (8)–(14), and an assignment $\tilde{\mathcal A}$ rounded from it as in §4.4. Then for every $j\in[T]$
--   $$\rho(\tilde{\mathcal A}[\tilde e_j])\ge(1-8\epsilon)\cdot\rho(S^-_j),$$
--   where $\rho(S)=\sum_{i\in S}r_iw_i$.
--
--   The rounding may discard part of the sub-assortments $S^-_j$ (items already counted in $S^+_{j-1}$); the lemma bounds the resulting loss of $\rho$-mass by a factor $1-8\epsilon$.
--
--   **Formalization Note** The statement holds for every feasible sequence, not only the DP-optimal one, with approximate assortments ranging over all subsets. The hypothesis $k_{\mathrm{mid}}\le n-1$ is added because for $k_{\mathrm{mid}}=n$ the construction of §4.4 can leave items unplaced.
-- source:
--   Aouad & Segev, Display Optimization for Vertically Differentiated Locations Under Multinomial Logit Preferences, SSRN 2709652 (version of 31/07/2019), p. 22, Lemma 5.2 (proof: App. C.5, p. 48)

import Mathlib
import Definitions.Def_DisplayMNL_Rounding_Model

open Finset

namespace DisplayMNL.Rounding

theorem lemma_5_2 {n : ℕ} (I : Instance n) (ε : ℝ) (kmid : ℕ) (s : DPSeq n) (A : Fin n ≃ Fin n)
    (hst : Standing I ε) (hk1 : 1 ≤ kmid) (hk2 : kmid + 1 ≤ n)
    (hF : IsFeasible I ε kmid s) (hR : IsRounded I s kmid A)
    (j : ℕ) (hj1 : 1 ≤ j) (hjT : j ≤ s.T) :
    (1 - 8 * ε) * rhoSet I (s.sm j) ≤ rhoSet I (pre A (etil s kmid j)) := by sorry

end DisplayMNL.Rounding
