-- Prove2me | Theorems.Thm_ConnesRZ_spectral_star_square
-- name    : ConnesRZ.spectral_star_square
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-06T20:34:42.675617+00:00
-- url     : https://prove2.me/theorems/3aa934b0-85e5-4824-8d28-0e6645290d31
-- title:
--   The full spectral expansion of the Weil quadratic form
-- statement:
--   Let $g:\mathbb R\to\mathbb C$ be smooth with compact support, with transform
--   $$\widehat g(z)=\int_{\mathbb R}g(t)e^{(z-1/2)t}\,dt.$$
--   Let $W$ be the mission's Weil distribution, $g^*(t)=\overline{g(-t)}$, and let $m_\rho$ be the multiplicity of a critical-strip zero of the Riemann zeta function. The family indexed by the distinct critical-strip zeros is unconditionally summable, and
--   $$W(g\star g^*)=\sum_\rho m_\rho\widehat g(\rho)\overline{\widehat g(1-\bar\rho)}.$$
--
--   This formula exposes the reflected-zero cross-terms needed for the necessity direction of Weil's positivity criterion. It assumes neither RH nor positivity. Unconditional summability is part of the conclusion, not an additional assumption. On the critical line the two transform factors combine into a square modulus.
--
--   This is a derived specialization of the explicit formula to a convolution star-square, using the convolution and involution identity for the transform.
-- source:
--   A. Connes, Noncommutative geometry and the Riemann zeta function, Mathematics: Frontiers and Perspectives, AMS (2000), section 3, eqs. (11)-(12), p. 15; Weil positivity/RH discussion, p. 22. Related exposition: https://arxiv.org/abs/math/9811068 . Exact half-shift normalization and explicit formula: https://prove2.me/theorems/57f950e0-75ff-4e78-8619-c0ced98597f5 . Derived specialization to convolution star-squares.

import Definitions.Def_ConnesRZ_weil_defs

open Complex MeasureTheory

namespace ConnesRZ

theorem spectral_star_square (g : ℝ → ℂ) (hg : IsTest g) :
    HasSum (fun ρ : {s : ℂ // IsCriticalZero s} =>
      (zeroMult ρ.1 : ℂ) * (mellinHat g ρ.1 *
        (starRingEnd ℂ) (mellinHat g (1 - (starRingEnd ℂ) ρ.1))))
      (weilDistribution (conv g (starInv g))) := by sorry

end ConnesRZ
