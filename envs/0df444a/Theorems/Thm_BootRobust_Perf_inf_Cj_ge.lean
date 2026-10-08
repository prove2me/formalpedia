-- Prove2me | Theorems.Thm_BootRobust_Perf_inf_Cj_ge
-- name    : BootRobust.Perf.inf_Cj_ge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:08:38.869986+00:00
-- url     : https://prove2.me/theorems/c1175c8a-3d87-4725-9773-b3ee1fb1519e
-- title:
--   Proof of Theorem 6, p. 15 — with c̄ the robust budget (26), inf_{D∈C_j} B(D, D_tr) ≥ max{r, r^j_n}
-- statement:
--   Let $1\le k\le n$, let $\emptyset=N^0\subseteq\dots\subseteq N^n=\Omega_n$ be a nested chain of neighbourhoods, $w>0$ weights, $\ell$ losses, $D_{\mathrm{tr}}\in\mathcal D_n$ with all entries positive, and $r\in\mathbb R$. Let $\bar c_n=\max_{j\in[n]}c^j_n$ be the robust budget (26) and $\mathcal C_j=\{D\in\mathcal D^j_n:E^{n,j}_D>\bar c_n\}$. For every $j\in[n]$,
--   $$\inf_{D\in\mathcal C_j}B(D,D_{\mathrm{tr}})\ \ge\ \max\{r,\ r^j_n\},\qquad r^j_n=\inf_{D\in\mathcal D^j_n}B(D,D_{\mathrm{tr}}).$$
--
--   Every distribution of $\mathcal C_j$ has a partial estimate above the robust budget, hence lies outside the $B$-ball of radius $r$; and $\mathcal C_j\subseteq\mathcal D^j_n$. This is the exponent fed into Csiszár's inequality in the proof of Theorem 6.
--
--   **Formalization Note** The page prints the strict inequalities "$>r$" and "$>r^j_n$" for the infima; an infimum of values above $r$ is only $\ge r$, and $\ge$ is all the proof uses. The infimum is $+\infty$ when $\mathcal C_j$ is empty.
-- source:
--   Bertsimas and Van Parys, Bootstrap robust prescriptive analytics, arXiv:1711.09974v2, proof of Theorem 6, p. 15, "The robust budget cost c̄_n is constructed precisely as to ensure …"; (26), p. 12; (29), p. 14

import Mathlib
import Definitions.Def_BootRobust_Perf_Setting

namespace BootRobust.Perf

/-- Proof of Theorem 6, p. 15: with the threshold `c̄_n` the robust budget (26), every
distribution of `C_j` is at bootstrap distance more than `r` from `D_tr`, so
`inf_{D ∈ C_j} B(D, D_tr) ≥ max{r, r^j_n}`. -/
theorem inf_Cj_ge {ι : Type*} [Fintype ι] [DecidableEq ι] (n k : ℕ) (hn : 1 ≤ n)
    (hk : 1 ≤ k) (hkn : k ≤ n) (N : ℕ → Finset ι) (hNmono : Monotone N) (hN0 : N 0 = ∅)
    (hNn : N n = Finset.univ) (w : ι → ℝ) (hw : ∀ i, 0 < w i) (Dtr : ι → ℝ)
    (hDtr : Dtr ∈ stdSimplex ℝ ι) (hDtrpos : ∀ i, 0 < Dtr i) (r : ℝ) (ℓ : ι → ℝ) (j : ℕ)
    (hj : j ∈ Finset.Icc 1 n) :
    max (r : EReal) (rj n k N Dtr j) ≤
      ⨅ D ∈ Cj n k N w ℓ (robustBudget n k N w ℓ Dtr r) j, bootDist D Dtr := by sorry

end BootRobust.Perf
