-- Prove2me | Theorems.Thm_ConnesRZ_mellinHat_conv_starInv
-- name    : ConnesRZ.mellinHat_conv_starInv
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-06T20:32:42.38198+00:00
-- url     : https://prove2.me/theorems/bbfe8ec3-4c5f-4ec5-8dc8-8aea63454f2e
-- title:
--   The Mellin transform of a convolution star-square at every complex parameter
-- statement:
--   Let $g:\mathbb R\to\mathbb C$ be smooth with compact support. Write
--   $$\widehat g(z)=\int_{\mathbb R}g(t)e^{(z-1/2)t}\,dt,$$
--   and define $g^*(t)=\overline{g(-t)}$ and convolution with respect to Lebesgue measure. For every $z\in\mathbb C$,
--   $$\widehat{g\star g^*}(z)=\widehat g(z)\overline{\widehat g(1-\bar z)}.$$
--   On the critical line this specializes to the square modulus identity. Away from that line it exposes the pairing of two reflected spectral parameters used in the necessity direction of Weil's positivity criterion.
--
--   This is the convolution and involution identity for the transform in Connes' equation (12), in the mission's additive coordinate and half-shift convention; it is a derived supporting identity, not a quotation of a separately numbered theorem.
-- source:
--   A. Connes, Noncommutative geometry and the Riemann zeta function, Mathematics: Frontiers and Perspectives, AMS (2000), section 3, eq. (12), p. 15 (transform); consequence of convolution and involution under that transform. Related trace-formula exposition: https://arxiv.org/abs/math/9811068 . Exact additive and half-shift normalization: https://prove2.me/theorems/1ba757cc-8991-4e58-abf7-f8eee1db65da .

import Definitions.Def_ConnesRZ_weil_defs

open Complex MeasureTheory

namespace ConnesRZ

theorem mellinHat_conv_starInv (g : ℝ → ℂ) (hg : IsTest g) (z : ℂ) :
    mellinHat (conv g (starInv g)) z =
      mellinHat g z * (starRingEnd ℂ) (mellinHat g (1 - (starRingEnd ℂ) z)) := by sorry

end ConnesRZ
