-- Prove2me | Theorems.Thm_DynamicsRelativity_kepler_energy_eccentricity_planar
-- name    : DynamicsRelativity.kepler_energy_eccentricity_planar
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-24T04:13:00.739178+00:00
-- url     : https://prove2.me/theorems/08bc1e1f-53d6-4d4e-8003-acef7311caeb
-- title:
--   The energy of an inverse-square orbit in terms of its eccentricity (eccentricity vector in the orbital plane)
-- statement:
--   This is Tong's equation (4.16), the relation between the energy of an inverse-square orbit and its eccentricity, with the eccentricity vector taken in the orbital plane.
--
--   Let a particle of mass $m>0$ move under the attractive inverse-square law of strength $k>0$ with nonvanishing angular momentum $L = L(0)$, and suppose its orbit is the conic of semi-latus rectum $r_0=l^{2}/k$ and eccentricity vector $A$ produced by equation (4.14), where $l=\lVert L\rVert/m$: $r(t) + \langle A, x(t)\rangle = r_0$ for all $t$. Assume moreover that $A$ lies in the orbital plane, $\langle A, L\rangle = 0$. Writing $e=\lVert A\rVert$ for the eccentricity, the total energy is
--
--   $$ E \;=\; \frac{m k^{2}}{2 l^{2}}\,\big(e^{2}-1\big), $$
--
--   independently of time.
--
--   The hypothesis $\langle A, L\rangle = 0$ is needed: the conic equation only sees the component of $A$ in the orbital plane, since $x(t) \perp L$, so without it $A + cL$ satisfies the same equation with a different norm and the identity fails. With it, $A$ is the eccentricity vector Tong's $e = \lVert A\rVert$ in (4.16) refers to, and the identity converts the dynamical hypothesis $E<0$ into the geometric condition $e<1$.
-- source:
--   David Tong, Dynamics and Relativity, University of Cambridge Part IA Mathematical Tripos lecture notes, Lent 2013, http://www.damtp.cam.ac.uk/user/tong/relativity.html — §4.3.1, "The Energy of the Orbit Revisited", eq. (4.16) and the three bullet points that follow it, pp. 59–60.

import Definitions.Def_DynamicsRelativity_CentralForces_Defs
import Mathlib

open DynamicsRelativity

theorem DynamicsRelativity.kepler_energy_eccentricity_planar {k m r₀ : ℝ} {x : ℝ → Vec} {A : Vec}
    (hk : 0 < k) (h : KeplerMotion k m x) (hL : angularMomentum m x 0 ≠ 0)
    (hr₀ : r₀ = (‖angularMomentum m x 0‖ / m) ^ 2 / k)
    (hA : ∀ t, ‖x t‖ + inner ℝ A (x t) = r₀)
    (hAL : inner ℝ A (angularMomentum m x 0) = 0) (t : ℝ) :
    keplerEnergy k m x t =
      m * k ^ 2 * (‖A‖ ^ 2 - 1) / (2 * (‖angularMomentum m x 0‖ / m) ^ 2) := by sorry
