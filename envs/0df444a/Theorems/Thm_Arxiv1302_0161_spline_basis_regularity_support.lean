-- Prove2me | Theorems.Thm_Arxiv1302_0161_spline_basis_regularity_support
-- name    : Arxiv1302_0161.spline_basis_regularity_support
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T09:27:38.044575+00:00
-- url     : https://prove2.me/theorems/f82eec87-3c38-4e1c-a2e1-fb4df14c9f23
-- title:
--   Remark 5.1: the spline basis functions are $C^3$ with support in $(-R,R)$
-- statement:
--   Let $R>0$ and let $M\ge1$ be an integer. Set $h=2R/(M+5)$ and $t_i=(i+2)h-R$. Let
--
--   $$\phi(t)=\sum_{j=0}^{5}\frac{(-1)^j}{4!}\binom{5}{j}\Big(t+\frac52-j\Big)_+^4,$$
--
--   which is the paper's formula with $k=4$, and let $\phi_i(t)=\phi((t-t_i)/h)$. Then for every $i=1,\dots,M$, $\phi_i\in C^3(\mathbb R)$ and $\operatorname{supp}\phi_i\subset(-R,R)$.
--
--   **Formalization Note** The paper calls $\phi$ "the cubic spline function", but with $k=4$ the formula is a spline of degree four. The statement uses the printed formula with $k=4$.
-- source:
--   H. Zhang and B. Zhang, A novel integral equation for scattering by locally rough surfaces and application to the inverse problem, arXiv:1302.0161v1 (2013), claim c014; Section 5, Remark 5.1, PDF p. 12

import Mathlib
import Definitions.Def_Arxiv1302_0161_Basic

open MeasureTheory Filter Topology

namespace Arxiv1302_0161

theorem spline_basis_regularity_support (R : ℝ) (hR : 0 < R) (M : ℕ) (hM : 1 ≤ M)
    (i : ℕ) (hi1 : 1 ≤ i) (hiM : i ≤ M) :
    ContDiff ℝ 3 (splineBasis R M i) ∧ tsupport (splineBasis R M i) ⊆ Set.Ioo (-R) R := by sorry

end Arxiv1302_0161
