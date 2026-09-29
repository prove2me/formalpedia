-- Prove2me | Theorems.Thm_ElectroweakWiki_gauge_boson_mass_terms
-- name    : ElectroweakWiki.gauge_boson_mass_terms
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-27T21:15:43.127778+00:00
-- url     : https://prove2.me/theorems/ce70acbd-63f0-4519-b41a-4e5fa70424d7
-- title:
--   Tree-level gauge boson masses from the Higgs vacuum
-- statement:
--   Let $g>0$, $g'>0$ and $v\in\mathbb R$, and let $\theta_W = \arctan(g'/g)$. For real gauge field values $W_1, W_2, W_3, B$ (one spacetime point, one Lorentz component) let
--
--   $$M = \frac{g'}{2}B\,\mathbb 1 + \frac g2\left(W_1\sigma_1 + W_2\sigma_2 + W_3\sigma_3\right)$$
--
--   be the gauge part of the covariant derivative $D_\mu = \partial_\mu - i\frac{g'}2YB_\mu - i\frac g2\sigma_jW^j_\mu$ on the Higgs doublet ($Y=1$), and let $h_0 = (0, v/\sqrt2)$ be the Higgs vacuum. With $W^\pm = (W_1\mp iW_2)/\sqrt2$, $Z^0 = -\sin\theta_W B + \cos\theta_W W_3$, $m_W = gv/2$ and $m_Z = \sqrt{g^2+g'^2}\,v/2$,
--
--   $$|M h_0|^2 = m_W^2\,W^+W^- + \frac12\,m_Z^2\,(Z^0)^2 .$$
--
--   The left side is $|D_\mu h|^2$ evaluated on the vacuum; the right side is the mass part $m_W^2 W^+_\mu W^{-\mu} + \frac12 m_Z^2 Z_\mu Z^\mu$ of the quadratic Lagrangian $\mathcal L_K$. The photon $\gamma$ does not appear, so it remains massless.
--
--   **Formalization Note** $|x|^2$ is $|x_1|^2+|x_2|^2$. The identity is stated in $\mathbb C$ (the left side is cast from $\mathbb R$) so that the product $W^+W^-$ appears literally.
-- source:
--   Wikipedia, "Electroweak interaction", revision oldid=1360331872, https://en.wikipedia.org/w/index.php?title=Electroweak_interaction&oldid=1360331872; Section 'Before electroweak symmetry breaking' (covariant derivative D_μ and L_h, p. 4 of the PDF) and section 'After electroweak symmetry breaking' (mass terms m_W² W⁺W⁻ + ½ m_Z² Z Z in L_K, p. 4); mass relation of section Formulation (p. 3)

import Definitions.Def_ElectroweakWiki_defs
open Matrix

namespace ElectroweakWiki

theorem gauge_boson_mass_terms (g g' v W1 W2 W3 B : ℝ) (hg : 0 < g) (hg' : 0 < g') :
    (doubletNormSq (gaugeTerm g g' 1 B W1 W2 W3 *ᵥ higgsVacuum v) : ℂ) =
      (wMass g v : ℂ) ^ 2 * wPlus W1 W2 * wMinus W1 W2 +
        1 / 2 * (zMass g g' v : ℂ) ^ 2 * (zField (weinbergAngle g g') B W3 : ℂ) ^ 2 := by sorry

end ElectroweakWiki
