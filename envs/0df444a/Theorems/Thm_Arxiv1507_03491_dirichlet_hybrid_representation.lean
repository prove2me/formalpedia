-- Prove2me | Theorems.Thm_Arxiv1507_03491_dirichlet_hybrid_representation
-- name    : Arxiv1507_03491.dirichlet_hybrid_representation
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T16:44:36.292517+00:00
-- url     : https://prove2.me/theorems/057234f3-8ff7-4a65-a72a-d1b7708d0af5
-- title:
--   Eqs. (2.12)–(2.13) (as derived): hybrid representation of the Dirichlet scattered field
-- statement:
--   Let $\operatorname{Re}k>0$, $\operatorname{Im}k\ge0$, $M_0>4$, $W=W_{M_0}$, and let a source sit at $\mathbf x_0=(x_0,y_0)$ with $y_0>0$, with incident field $u^i=G_k(\cdot,\mathbf x_0)$. Let $u^s=-G_k(\cdot,\mathbf x_0^R)$ be the scattered field of the sound-soft half-space (eq. 2.4) and $\sigma_W=W\cdot(-2u^i)$ on $\Gamma$. Then for every $\mathbf x=(x,y)$ with $y>0$,
--
--   $$u^s(\mathbf x)=\int_{-M_0}^{M_0}\frac{\partial G_k(\mathbf x,(x',0))}{\partial n'}\,\sigma_W(x')\,dx'+\frac1{4\pi}\int_{-\infty}^{\infty}e^{-\sqrt{\lambda^2-k^2}\,y}e^{i\lambda x}\,\tfrac12\hat\xi_W(\lambda)\,d\lambda,$$
--
--   where $\hat\xi_W=-2\,\widehat{(1-W)}*F_{x_0,y_0}$ is the density printed in eq. (2.13).
--
--   This is the hybrid representation: a double-layer potential on the finite segment $\Gamma_0$ plus a Sommerfeld correction.
--
--   **Formalization Note** The statement is the representation as derived. With the paper's Fourier convention, $\widehat{u^i}=\tfrac12F_{x_0,y_0}$, not $F_{x_0,y_0}$ as the text says. The density that makes (2.12) hold is therefore $-2\,\widehat{(1-W)}*\widehat{u^i}=\tfrac12\hat\xi_W$; the paper's own proof of Theorem 2.2 writes it in that form. The convolution is normalized by $\frac1{2\pi}$, as in the definitions.
-- source:
--   Lai, Greengard and O'Neil, A new hybrid integral representation for frequency domain scattering in layered media, arXiv:1507.03491v2 (2015), claim c021; Section 2, eqs. (2.4), (2.12), (2.13), PDF pp. 5 and 8

import Mathlib
import Definitions.Def_Arxiv1507_03491_Basic

open MeasureTheory Filter Topology Set
open scoped ContDiff NNReal

namespace Arxiv1507_03491

theorem dirichlet_hybrid_representation (k : ℂ) (hk : 0 < k.re) (hk' : 0 ≤ k.im)
    (M0 : ℝ) (hM0 : 4 < M0) (x0 y0 : ℝ) (hy0 : 0 < y0) (x y : ℝ) (hy : 0 < y) :
    dirScattered k x0 y0 x y =
      (∫ x' in Ioo (-M0) M0,
          dlKernel k x y x' * ((window M0 x' : ℂ) * (-2 * greenK k x' 0 x0 y0))) +
        1 / (4 * (Real.pi : ℂ)) *
          ∫ lam : ℝ, Complex.exp (-(sqrtLK k lam) * (y : ℂ)) *
            Complex.exp (Complex.I * (lam : ℂ) * (x : ℂ)) *
              ((1 / 2) * dirSommerfeldDensity M0 k x0 y0 lam) := by sorry

end Arxiv1507_03491
