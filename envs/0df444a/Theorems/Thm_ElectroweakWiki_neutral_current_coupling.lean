-- Prove2me | Theorems.Thm_ElectroweakWiki_neutral_current_coupling
-- name    : ElectroweakWiki.neutral_current_coupling
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-27T20:41:56.000533+00:00
-- url     : https://prove2.me/theorems/57ecb6db-e56d-4c04-a779-bef2f9f53fdb
-- title:
--   Neutral-current couplings: $eQ\,A + \frac{g}{\cos\theta_W}(T_3 - \sin^2\theta_W Q)Z$
-- statement:
--   Let $g>0$, $g'>0$, $\theta_W = \arctan(g'/g)$ and $e = gg'/\sqrt{g^2+g'^2}$. For a fermion with isospin component $T_3$ and hypercharge $Y$, let $Q = T_3 + Y/2$. For real field values $B, W_3$ let $A = \cos\theta_W B + \sin\theta_W W_3$ (photon) and $Z = -\sin\theta_W B + \cos\theta_W W_3$. Then
--
--   $$g\,T_3\,W_3 + g'\,\frac Y2\,B = e\,Q\,A + \frac{g}{\cos\theta_W}\left(T_3 - \sin^2\theta_W\, Q\right) Z.$$
--
--   The left side is the neutral part of the gauge coupling in the covariant derivative $D_\mu$; the right side gives the couplings of $A$ and $Z$ that appear in $\mathcal L_N = eJ^{em}_\mu A^\mu + \frac{g}{\cos\theta_W}(J^3_\mu - \sin^2\theta_W J^{em}_\mu)Z^\mu$.
-- source:
--   Wikipedia, "Electroweak interaction", revision oldid=1360331872, https://en.wikipedia.org/w/index.php?title=Electroweak_interaction&oldid=1360331872; Section 'After electroweak symmetry breaking', neutral current Lagrangian L_N (p. 5 of the PDF), with the covariant derivative D_μ of p. 4

import Definitions.Def_ElectroweakWiki_defs
open Matrix

namespace ElectroweakWiki

theorem neutral_current_coupling (g g' T3 Y B W3 : ℝ) (hg : 0 < g) (hg' : 0 < g') :
    g * T3 * W3 + g' * (Y / 2) * B =
      elemCharge g g' * electricCharge T3 Y * photonField (weinbergAngle g g') B W3 +
        g / Real.cos (weinbergAngle g g') *
          (T3 - Real.sin (weinbergAngle g g') ^ 2 * electricCharge T3 Y) *
            zField (weinbergAngle g g') B W3 := by sorry

end ElectroweakWiki
