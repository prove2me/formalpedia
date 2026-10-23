-- Prove2me | Theorems.Thm_BertsimasVanParys2021_lemma2_nonneg_weights_faithful
-- name    : BertsimasVanParys2021.lemma2_nonneg_weights_faithful
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-23T01:33:00.130631+00:00
-- url     : https://prove2.me/theorems/f36e8221-7adb-4e2d-b552-cc3ccf407f2e
-- title:
--   Lemma 2 (dual of the bootstrap robust Nadaraya–Watson budget) with nonnegative weights and losses
-- statement:
--   Let $\Omega_n=\{1,\dots,m\}$ be a finite empirical support and $D\in\mathcal D_n$ a distribution on it (zeros allowed). Let $r\in\mathbb R$ be a robustness radius, $w_i=w_n(\bar x_i,x_0)\ge0$ the kernel weights with $\sum_i w_iD_i>0$, and $\ell_i=L(\bar z,\bar y_i)\ge0$ the losses of a fixed decision $\bar z$. Let $B(D',D)=\sum_i D'_i\log(D'_i/D_i)$ be the bootstrap distance (27). Then
--
--   $$\sup\Big\{\frac{\sum_i w_i\ell_iD'_i}{\sum_i w_iD'_i}:\ D'\in\mathcal D_n,\ B(D',D)\le r\Big\}=\inf\Big\{\alpha\in\mathbb R:\ \exists\nu>0,\ \nu\log\Big(\sum_i e^{(\ell_i-\alpha)w_i/\nu}D_i\Big)+r\nu\le0\Big\}.$$
--
--   This is Lemma 2 of Bertsimas and Van Parys for finite losses, with the paper's nonnegative weights $w_n\ge0$ (p. 9), which allow the compactly supported smoothers of Figure 4. The existing theorem BootRobust.NWDual.lemma_2 assumes $w_i>0$ at every support point and drops $\ell_i\ge0$.
--
--   **Formalization Note** Both sides are extended reals ($\sup\emptyset=-\infty$, $\inf\emptyset=+\infty$); $B(D',D)=+\infty$ when $D'$ charges a zero of $D$. Distributions $D'$ in the ball with $\sum_i w_iD'_i=0$ get the junk value $0$ for the quotient; with $\ell\ge0$ and $D$ itself in the ball (for $r\ge0$) this does not change the supremum. The hypothesis $\sum_i w_iD_i>0$ excludes only the case where the estimate is undefined at every $D'$ of the ball. The paper's $\nu\in\mathbb R_+$ is $\nu>0$, since the expression is undefined at $\nu=0$. Losses $+\infty$ are not covered.
-- source:
--   Bertsimas and Van Parys, Bootstrap robust prescriptive analytics, Mathematical Programming (2021), doi:10.1007/s10107-021-01679-2 (arXiv:1711.09974v2), Lemma 2 and (33), pp. 17–18; weights p. 9 and Figure 4, p. 10

import Mathlib
import Definitions.Def_BootRobust_NWDual_Setting

theorem BertsimasVanParys2021.lemma2_nonneg_weights_faithful {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : ι → ℝ) (hD : D ∈ stdSimplex ℝ ι) (r : ℝ)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hwD : 0 < ∑ i, w i * D i)
    {Z : Type*} (L : Z → ι → ℝ) (hL : ∀ z i, 0 ≤ L z i) (z : Z) :
    BootRobust.NWDual.robustNW BootRobust.Perf.bootDist D r w (L z) =
      ⨅ α ∈ BootRobust.NWDual.dualSet D r w (L z), (α : EReal) := by sorry
