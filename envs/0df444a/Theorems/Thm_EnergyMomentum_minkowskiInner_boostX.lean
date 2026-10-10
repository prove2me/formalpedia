-- Prove2me | Theorems.Thm_EnergyMomentum_minkowskiInner_boostX
-- name    : EnergyMomentum.minkowskiInner_boostX
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:13:02.561341+00:00
-- url     : https://prove2.me/theorems/1323aa7d-8871-49ba-a51a-8c468eb423bb
-- title:
--   Lorentz invariance of the Minkowski square under a boost
-- statement:
--   Let $c>0$ and let $u$ be a real velocity with $|u|<c$. For every four-vector $P = (P^0, P^x, P^y, P^z)$, let $\Lambda_u P = (\gamma_u(P^0 - \beta P^x),\ \gamma_u(P^x - \beta P^0),\ P^y,\ P^z)$ be its Lorentz boost along the $x$-axis, $\beta = u/c$, $\gamma_u = 1/\sqrt{1-\beta^2}$. Then
--
--   $$
--   \langle \Lambda_u P, \Lambda_u P\rangle = \langle P, P\rangle ,
--   $$
--
--   where $\langle\cdot,\cdot\rangle$ is the Minkowski inner product of signature $(+,-,-,-)$. Hence $\langle\mathbf P,\mathbf P\rangle$ — and so the mass — is independent of the inertial frame.
-- source:
--   Wikipedia, *Energy–momentum relation*, https://en.wikipedia.org/wiki/Energy%E2%80%93momentum_relation (PDF snapshot supplied by the proposer), §Norm of the four-momentum → Special relativity: "This is a Lorentz invariant quantity, and therefore independent of the frame of reference" (boost along one axis as the representative Lorentz transformation; see also the figure caption on hyperbolic rotations).

import Mathlib
import Definitions.Def_EnergyMomentum_basic

namespace EnergyMomentum

/-- Lorentz invariance of `⟨P, P⟩` under a boost along the `x`-axis with speed `|u| < c`. -/
theorem minkowskiInner_boostX (c u : ℝ) (P : FourVec)
    (hc : 0 < c) (hu : |u| < c) :
    minkowskiInner (boostX c u P) (boostX c u P) = minkowskiInner P P := by sorry

end EnergyMomentum
