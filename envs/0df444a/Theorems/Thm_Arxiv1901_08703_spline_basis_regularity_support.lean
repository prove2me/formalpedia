-- Prove2me | Theorems.Thm_Arxiv1901_08703_spline_basis_regularity_support
-- name    : Arxiv1901_08703.spline_basis_regularity_support
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T06:29:48.796857+00:00
-- url     : https://prove2.me/theorems/620a4e01-72b2-536f-965b-0dd568dac587
-- title:
--   Remark 5.2: the spline basis functions are $C^3$ with support in $(-R,R)$
-- statement:
--   Let $R>0$ and $M\ge1$, let $h=2R/(M+5)$ and $t_i=(i+2)h-R$, and let
--   $$\phi(t)=\sum_{j=0}^{5}\frac{(-1)^j}{4!}\binom5j\Big(t+\frac52-j\Big)_+^4,\qquad z_+^4=\begin{cases}z^4,&z\ge0,\\0,&z<0,\end{cases}$$
--   the cardinal B-spline of degree $4$ (the paper's $k=4$). Then for $i=1,\dots,M$ the basis function $\phi_{i,M}(t)=\phi((t-t_i)/h)$ belongs to $C^3(\mathbb R)$ and its support is contained in $(-R,R)$.
--
--   **Formalization Note** "Support" is the closed support, which is contained in the open interval $(-R,R)$.
-- source:
--   Qu, Zhang and Zhang, A novel integral equation for scattering by locally rough surfaces and application to the inverse problem: the Neumann case, arXiv:1901.08703v1 (2019), claim c017; Section 5.1, Remark 5.2, PDF p. 22

import Mathlib
import Definitions.Def_Arxiv1901_08703_Basic

open MeasureTheory

namespace Arxiv1901_08703

theorem spline_basis_regularity_support (R : ℝ) (hR : 0 < R) (M : ℕ) (hM : 1 ≤ M)
    (i : ℕ) (hi1 : 1 ≤ i) (hiM : i ≤ M) :
    ContDiff ℝ 3 (splineBasis R M i) ∧ tsupport (splineBasis R M i) ⊆ Set.Ioo (-R) R := by sorry

end Arxiv1901_08703
