-- Prove2me | Theorems.Thm_DeBruijnNewman_Dobner_gaussian_convolution
-- name    : DeBruijnNewman.Dobner.gaussian_convolution
-- status  : Proved
-- author  : @adobner
-- created : 2026-09-24T22:53:58.741796+00:00
-- url     : https://prove2.me/theorems/ded71fc8-61c1-4b9e-9d32-8c17bc890681
-- title:
--   Gaussian convolution of the canonical De Bruijn–Newman heat flow
-- statement:
--   Let $t<0$ be real and $s\in\mathbb C$. For the canonical heat family
--
--   $$
--   \xi_t(s)=8H_t(-i(2s-1)),\qquad
--   H_t(z)=\int_0^\infty e^{tu^2}\Phi(u)\cos(zu)\,du,
--   $$
--
--   the following identity holds:
--
--   $$
--   \frac1{\sqrt{\pi|t|}}\int_{\mathbb R}
--   \xi_0(2+iv)\exp\!\left(\frac{(s-(2+iv))^2}{|t|}\right)\,dv
--   =\xi_t(s).
--   $$
--
--   Here $\Phi$ is the existing explicit theta kernel in the definition of $H_t$. The identity expresses negative-time deformation as a Gaussian integral of the same canonical family at time zero. It holds at every complex evaluation point and provides the integral representation used in the subsequent Dirichlet-series expansion.
--
--   **Formalization Note.** Both sides use `DeBruijnNewman.Dobner.xiT`, including at time zero. The integration variable $v$ parametrizes the upward vertical line with real part two; the contour factor $i$ cancels the factor $1/i$ in the contour normalization.
-- source:
--   Alexander Dobner, A proof of Newman's conjecture for the extended Selberg class, arXiv:2005.05142v2 (10 January 2026), https://arxiv.org/abs/2005.05142v2, Section 3, equation (9), p. 12, expressed for the canonical heat family at times zero and t. The canonical normalization is obtained from the Fourier integral and theta kernel in equations (1)–(2), p. 2.

import Definitions.Def_DeBruijnNewman_Dobner
open MeasureTheory

theorem DeBruijnNewman.Dobner.gaussian_convolution (t : ℝ) (ht : t < 0) (s : ℂ) :
    (1 / (Real.sqrt (Real.pi * |t|) : ℂ)) *
      (∫ v : ℝ, DeBruijnNewman.Dobner.xiT 0 (2 + (v : ℂ) * Complex.I) *
        Complex.exp ((s - (2 + (v : ℂ) * Complex.I)) ^ 2 / ((|t| : ℝ) : ℂ))) =
      DeBruijnNewman.Dobner.xiT t s := by sorry
