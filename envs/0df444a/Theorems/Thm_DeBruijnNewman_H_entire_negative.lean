-- Prove2me | Theorems.Thm_DeBruijnNewman_H_entire_negative
-- name    : DeBruijnNewman.H_entire_negative
-- status  : Proved
-- author  : @adobner
-- created : 2026-09-24T22:32:43.627672+00:00
-- url     : https://prove2.me/theorems/a0324462-4e7c-44ad-8f0e-c9deed69f739
-- title:
--   The negative-time De Bruijn–Newman heat integral is entire
-- statement:
--   For every real $t<0$, the canonical De Bruijn–Newman heat integral
--
--   $$
--   H_t(z)=\int_0^\infty e^{tu^2}\Phi(u)\cos(zu)\,du
--   $$
--
--   is an entire function of $z\in\mathbb C$, where
--
--   $$
--   \Phi(u)=\sum_{n=1}^{\infty}
--   (2\pi^2n^4e^{9u}-3\pi n^2e^{5u})e^{-\pi n^2e^{4u}}.
--   $$
--
--   This gives the holomorphy needed to study the negative-time deformations and their normalized versions. Only negative time is asserted; the theorem uses the existing integral definition of the heat flow.
--
--   **Formalization Note.** Entirety is expressed as complex differentiability at every point of $\mathbb C$.
-- source:
--   Alexander Dobner, A proof of Newman's conjecture for the extended Selberg class, arXiv:2005.05142v2 (10 January 2026), https://arxiv.org/abs/2005.05142v2, Introduction's theta kernel and deformed Fourier integral, pp. 2–3; holomorphy used in Section 3.1, p. 14. The submitted proof establishes the negative-time case directly by Gaussian domination.

import Definitions.Def_DeBruijnNewman_core

theorem DeBruijnNewman.H_entire_negative (t : ℝ) (ht : t < 0) :
    Differentiable ℂ (DeBruijnNewman.H t) := by sorry
