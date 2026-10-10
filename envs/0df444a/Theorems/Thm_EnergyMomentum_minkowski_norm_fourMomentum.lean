-- Prove2me | Theorems.Thm_EnergyMomentum_minkowski_norm_fourMomentum
-- name    : EnergyMomentum.minkowski_norm_fourMomentum
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:12:33.701386+00:00
-- url     : https://prove2.me/theorems/168f8b4d-77ad-43a1-b4a9-8c1803e209f8
-- title:
--   Norm of the four-momentum: $\langle \mathbf P,\mathbf P\rangle = (E/c)^2 - p^2 = (mc)^2$
-- statement:
--   Let $c>0$, $m>0$ and $\mathbf v\in\mathbb R^3$ with $|\mathbf v|<c$, and let $\mathbf P = (E/c, \mathbf p)$ be the four-momentum of the body, $E = \gamma mc^2$, $\mathbf p = \gamma m\mathbf v$. With the Minkowski inner product of signature $(+,-,-,-)$,
--
--   $$
--   \langle \mathbf P, \mathbf P\rangle = \left(\frac{E}{c}\right)^2 - p^2 = (mc)^2 .
--   $$
--
--   The Minkowski square of the four-momentum is thus fixed by the mass alone; rearranging gives (1).
-- source:
--   Wikipedia, *Energy–momentum relation*, https://en.wikipedia.org/wiki/Energy%E2%80%93momentum_relation (PDF snapshot supplied by the proposer), §Norm of the four-momentum → Special relativity (displays computing $\langle \mathbf P,\mathbf P\rangle$ with the Minkowski metric $\eta$, and $(mc)^2 = (E/c)^2 - p^2$).

import Mathlib
import Definitions.Def_EnergyMomentum_basic

namespace EnergyMomentum

/-- Norm of the four-momentum: `⟨P, P⟩ = (E / c)² − p² = (m c)²`. -/
theorem minkowski_norm_fourMomentum (m c : ℝ) (v : Vec3)
    (hc : 0 < c) (hm : 0 < m) (hv : ‖v‖ < c) :
    minkowskiInner (fourMomentum m c v) (fourMomentum m c v)
        = (energy m c v / c) ^ 2 - ‖momentum m c v‖ ^ 2 ∧
      minkowskiInner (fourMomentum m c v) (fourMomentum m c v) = (m * c) ^ 2 := by sorry

end EnergyMomentum
