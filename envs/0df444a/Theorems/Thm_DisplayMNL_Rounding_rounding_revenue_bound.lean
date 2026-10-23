-- Prove2me | Theorems.Thm_DisplayMNL_Rounding_rounding_revenue_bound
-- name    : DisplayMNL.Rounding.rounding_revenue_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:31:05.066009+00:00
-- url     : https://prove2.me/theorems/c593e5a7-979d-48e6-8ff4-065c1fba4e1c
-- title:
--   Proof of Lemma 5.4, p. 22, (15)+(16) — the assignment rounded from any feasible DP sequence earns at least (1 − 8ε) times the DP's interval-weighted minima
-- statement:
--   Consider $n\ge2$ items with prices $r_i>0$ and MNL weights $w_i>0$, position weights $\lambda_k>0$, and an accuracy $\epsilon\in(0,1/5)$. Fix a guess $1\le k_{\mathrm{mid}}\le n-1$, a sequence of dynamic-programming actions $(e_j,S^-_j,S^+_j)_{j=1}^T$ that satisfies the boundary condition $e_1=1$, $S^-_1=S^+_1=\{i_1\}$, the root condition $e_T=n$, $S^-_T=S^+_T=[n]$, and every transition constraint (8)–(14), and an assignment $\tilde{\mathcal A}$ rounded from it by §4.4 (blocks $\Delta_1,\dots,\Delta_T$ placed in order, each by non-increasing price). Write $\alpha_j=\rho(S^-_j)/(1+w(S^+_j))$, $j_{\mathrm{mid}}=\max\{j: e_j\le k_{\mathrm{mid}}\}$, and $\tilde I_j$ for the position intervals of the proof of Lemma 5.4. Then
--   $$\mathcal R(\tilde{\mathcal A})=\sum_{k=1}^n\lambda_kR_k(\tilde{\mathcal A})\ \ge\ (1-8\epsilon)\left(\sum_{j=1}^{j_{\mathrm{mid}}}\lambda(\tilde I_j)\min\{\alpha_j,\alpha_{j+1}\}+\sum_{j=j_{\mathrm{mid}}+1}^{T}\lambda(\tilde I_j)\min\{\alpha_{j-1},\alpha_j\}\right),$$
--   where $\lambda(\tilde I_j)=\sum_{k\in\tilde I_j}\lambda_k$.
--
--   This is inequality (15) of the paper combined with (16): the expected revenue of the rounded assignment dominates, up to a factor $1-8\epsilon$, the interval-weighted minima of the dynamic program's revenue proxies. It is the part of the proof of Lemma 5.4 that holds as stated; the remaining step of that proof, and hence Lemma 5.4 and Theorem 1.1 themselves, fail for the paper's algorithm.
--
--   **Formalization Note** The bound is stated for every feasible action sequence, not only the DP-optimal one (the paper applies it to the optimal one, which is feasible), with approximate assortments ranging over all subsets of items and any order among equal-priced items within a block. The hypothesis $k_{\mathrm{mid}}\le n-1$ is added: for $k_{\mathrm{mid}}=n$ the construction of §4.4 can leave items unplaced, so no rounded assignment exists. Positions are 1-based; the assignment maps the 0-based position $k-1$ to the item at position $k$.
-- source:
--   Aouad & Segev, Display Optimization for Vertically Differentiated Locations Under Multinomial Logit Preferences, SSRN 2709652 (version of 31/07/2019), p. 22, proof of Lemma 5.4, inequalities (15) and (16)

import Mathlib
import Definitions.Def_DisplayMNL_Rounding_Model

open Finset

namespace DisplayMNL.Rounding

theorem rounding_revenue_bound {n : ℕ} (I : Instance n) (ε : ℝ) (kmid : ℕ) (s : DPSeq n) (A : Fin n ≃ Fin n)
    (hst : Standing I ε) (hk1 : 1 ≤ kmid) (hk2 : kmid + 1 ≤ n)
    (hF : IsFeasible I ε kmid s) (hR : IsRounded I s kmid A) :
    (1 - 8 * ε) *
        ((∑ j ∈ Icc 1 (jmid s kmid),
            lamSum I (Itil s kmid j) * min (alpha I s j) (alpha I s (j + 1))) +
          ∑ j ∈ Icc (jmid s kmid + 1) s.T,
            lamSum I (Itil s kmid j) * min (alpha I s (j - 1)) (alpha I s j)) ≤
      totalRev I A := by sorry

end DisplayMNL.Rounding
