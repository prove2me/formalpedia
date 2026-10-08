-- Prove2me | Theorems.Thm_BootRobust_NWDual_lemma_1
-- name    : BootRobust.NWDual.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:09:09.311982+00:00
-- url     : https://prove2.me/theorems/48b64022-70bc-466a-902c-36d5f8942d04
-- title:
--   Lemma 1, p. 17 — under Slater's condition the partial bootstrap robust budget (25) equals the dual program (32)
-- statement:
--   Let $\Omega_n$ be the finite support, $N^0\subseteq N^1\subseteq\cdots\subseteq N^n$ nested neighbourhoods with $N^0=\emptyset$ and $N^n=\Omega_n$, integers $1\le k\le n$ and $1\le j\le n$, a distribution $D\in\mathcal D_n$, a radius $r\in\mathbb R$, weights $w_i>0$ and losses $\ell_i=L(\bar z,\bar y_i)$ of a fixed decision $\bar z$. Assume Slater's condition
--   $$\inf\{B(D',D):\ D'\in\mathcal D^j_n\}<r .$$
--   Then the partial bootstrap robust budget (25) with $R=B$,
--   $$c^j_n(\bar z,D,x_0)=\sup_{s>0,\,P}\ \sum_{N^j}w_i\ell_iP_i\quad\text{s.t.}\quad s\,B(P/s,D)\le s\,r,\ \ \sum_{\Omega_n}P=s,\ \ \sum_{N^j}w_iP_i=1,\ \ \sum_{N^j}P\ge s\tfrac kn,\ \ \sum_{N^{j-1}}P\le s\tfrac{k-1}n,$$
--   equals
--   $$\inf\Big\{\alpha:\ \exists\,\eta_1,\eta_2\ge0,\ \nu>0,\ \ \nu\log\Big(\sum_{N^{j-1}}e^{\frac{(\ell_i-\alpha)w_i+\eta_1-\eta_2}{\nu}}D_i+\sum_{N^j\setminus N^{j-1}}e^{\frac{(\ell_i-\alpha)w_i+\eta_1}{\nu}}D_i+\sum_{\Omega_n\setminus N^j}D_i\Big)+r\nu-\tfrac kn(\eta_1-\eta_2)-\tfrac{\eta_2}n\le0\Big\}.$$
--
--   The partial budgets are the pieces of the bootstrap robust nearest-neighbours formulation; the dual replaces a sup over $|\Omega_n|+1$ primal variables by a search over four scalars.
--
--   **Formalization Note** The page assumes "$r>r^j_n$ for all $D\in\mathcal D_n$", where $r^j_n$ (29) is defined from the training distribution, while the lemma is about a general $D$; the statement reads the hypothesis as $r>\inf\{B(D',D):D'\in\mathcal D^j_n\}$, the Slater condition for (25) at $D$, which is what the proof (B.7) uses. Both sides are extended reals; $\nu>0$ instead of $\nu\ge0$; the chain $N^j$ is abstracted to a monotone family of finite sets. The term $-\eta_2/n$ follows the lemma as printed on p. 17 (the last display of B.7 prints $-\frac{\eta_2}{n}\nu$, a slip).
-- source:
--   Bertsimas and Van Parys, Bootstrap robust prescriptive analytics, arXiv:1711.09974v2, Lemma 1 and (32), p. 17 (proof B.7, pp. 30–31)

import Mathlib
import Definitions.Def_BootRobust_NWDual_Setting

namespace BootRobust.NWDual

/-- Lemma 1, p. 17: under the Slater condition `inf {B(D', D) : D' ∈ Dⁿʲ} < r`, the partial bootstrap
robust budget (25) equals the infimum of `α` over the dual program (32). -/
theorem lemma_1 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n k : ℕ) (N : ℕ → Finset ι) (hN : IsNeighborhoodChain n N)
    (hk : 1 ≤ k) (hkn : k ≤ n) (j : ℕ) (hj : 1 ≤ j) (hjn : j ≤ n)
    (D : ι → ℝ) (hD : D ∈ stdSimplex ℝ ι) (r : ℝ)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) {Z : Type*} (L : Z → ι → ℝ) (z : Z)
    (hslater : ⨅ D' ∈ BootRobust.Perf.Dj n k N j, BootRobust.Perf.bootDist D' D < (r : EReal)) :
    partialRobust n k N w (L z) D r j = ⨅ α ∈ dualSet1 n k N w (L z) D r j, (α : EReal) := by sorry

end BootRobust.NWDual
