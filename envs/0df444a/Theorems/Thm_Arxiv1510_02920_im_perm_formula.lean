-- Prove2me | Theorems.Thm_Arxiv1510_02920_im_perm_formula
-- name    : Arxiv1510_02920.im_perm_formula
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T02:09:17.113367+00:00
-- url     : https://prove2.me/theorems/7f00e759-8014-4365-8bd5-87c9eaae49df
-- title:
--   Eq. (5): the imaginary part of the permittivity
-- statement:
--   Let $c>0$, $\gamma>0$, let $f:\mathbb{R}\to\mathbb{R}$ be differentiable, and let $\varepsilon$ be the permittivity (3) with $P$ from (4). For every $x$ and every real $\omega\ne0$,
--
--   $$\operatorname{Im}\varepsilon(x,\omega)=\frac{4\gamma\omega^2f(x)\big[(\gamma^2+\omega^2)^2+(\gamma^2-\omega^2)f(x)\big]-c(\gamma^2-\omega^2)(\gamma^2+\omega^2)^2f'(x)}{\omega(\gamma^2+\omega^2)^4}.$$
-- source:
--   T. G. Philbin, All-frequency reflectionlessness, arXiv:1510.02920v1 (2015), claim c003; unnumbered main text, eq. (5), PDF p. 3

import Mathlib
import Definitions.Def_Arxiv1510_02920_Basic

open Filter Topology Asymptotics

namespace Arxiv1510_02920

theorem im_perm_formula (c : ℝ) (hc : 0 < c) (γ : ℝ) (hγ : 0 < γ)
    (f : ℝ → ℝ) (hf : Differentiable ℝ f) (x ω : ℝ) (hω : ω ≠ 0) :
    (perm c (ansatzP f γ) x (ω : ℂ)).im =
      (4 * γ * ω ^ 2 * f x * ((γ ^ 2 + ω ^ 2) ^ 2 + (γ ^ 2 - ω ^ 2) * f x) -
          c * (γ ^ 2 - ω ^ 2) * (γ ^ 2 + ω ^ 2) ^ 2 * deriv f x) /
        (ω * (γ ^ 2 + ω ^ 2) ^ 4) := by sorry

end Arxiv1510_02920
