-- Prove2me | Theorems.Thm_DeBruijnNewman_Dobner_xi_zero_eq_gamma_zeta
-- name    : DeBruijnNewman.Dobner.xi_zero_eq_gamma_zeta
-- status  : Proved
-- author  : @adobner
-- created : 2026-09-24T22:53:57.29901+00:00
-- url     : https://prove2.me/theorems/f50cfd2d-724c-4854-975b-8291b360fcc9
-- title:
--   The time-zero heat integral equals the completed Riemann xi function
-- statement:
--   For every complex $s$ with $\operatorname{Re}s>1$, the canonical time-zero heat integral satisfies
--
--   $$
--   8H_0(-i(2s-1))
--   =\frac{s(s-1)}2\pi^{-s/2}\Gamma(s/2)\zeta(s).
--   $$
--
--   Here
--
--   $$
--   H_0(z)=\int_0^\infty\Phi(u)\cos(zu)\,du,\qquad
--   \Phi(u)=\sum_{N=1}^{\infty}
--   \bigl(2\pi^2N^4e^{9u}-3\pi N^2e^{5u}\bigr)e^{-\pi N^2e^{4u}},
--   $$
--
--   and $\zeta$ is the Riemann zeta function. This is the classical Fourier representation of Riemann xi in the stated half-plane, with the factor eight corresponding to the chosen kernel and half-line cosine integral. It connects the canonical heat flow to the arithmetic function whose absolutely convergent Dirichlet series is used on this half-plane.
--
--   **Formalization Note.** The left side is `xiT 0 s`; the right side is `gammaFactor s * riemannZeta s`. The kernel, heat integral, and gamma factor are the existing definitions.
-- source:
--   Alexander Dobner, A proof of Newman's conjecture for the extended Selberg class, arXiv:2005.05142v2 (10 January 2026), https://arxiv.org/abs/2005.05142v2, Introduction, definition of Riemann xi and equations (1)–(2), p. 2. Restricted to Re(s)>1 and converted from the paper's even full-line Fourier integral to the canonical half-line cosine integral. The paper cites Titchmarsh, The Theory of the Riemann Zeta-function, p. 255, for this Fourier representation.

import Definitions.Def_DeBruijnNewman_Dobner

theorem DeBruijnNewman.Dobner.xi_zero_eq_gamma_zeta (s : ℂ) (hs : 1 < s.re) :
    DeBruijnNewman.Dobner.xiT 0 s =
      DeBruijnNewman.Dobner.gammaFactor s * riemannZeta s := by sorry
