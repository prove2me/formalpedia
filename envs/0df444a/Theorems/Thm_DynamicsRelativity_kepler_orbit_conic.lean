-- Prove2me | Theorems.Thm_DynamicsRelativity_kepler_orbit_conic
-- name    : DynamicsRelativity.kepler_orbit_conic
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-22T23:19:59.99266+00:00
-- url     : https://prove2.me/theorems/b8ae9400-b549-4328-80ed-3e5025078ba7
-- title:
--   The orbit of the inverse-square law is a conic with focus at the centre of attraction
-- statement:
--   This is Tong's equation (4.14), the solution of the orbit equation for the attractive inverse-square law, stated without choosing coordinates.
--
--   Let a particle of mass $m>0$ move under the attractive inverse-square law with strength $k=GM>0$ and with nonvanishing angular momentum. Write $l=\lVert L\rVert/m$ for the angular momentum per unit mass and
--
--   $$ r_0 \;=\; \frac{l^{2}}{k} $$
--
--   for the **semi-latus rectum**. Then there is a fixed vector $A$, the **eccentricity vector**, pointing towards the point of closest approach, such that the trajectory satisfies
--
--   $$ r(t) + \big\langle A,\,x(t)\big\rangle \;=\; r_0 \qquad\text{for every } t, \qquad r = \lVert x\rVert .$$
--
--   Measuring the polar angle $\theta$ from the direction of $A$ and writing $e=\lVert A\rVert$ for the **eccentricity**, this is precisely the source's
--
--   $$ r \;=\; \frac{r_0}{1+e\cos\theta}, $$
--
--   the equation of a conic section with a focus at the centre of attraction. As Tong notes, $r_0$ is fixed by the angular momentum while $e$ is effectively the remaining integration constant, and it is $e$ that determines the shape of the orbit.
--
--   The hypothesis that the angular momentum does not vanish excludes purely radial free-fall, for which no such conic exists.
-- source:
--   David Tong, Dynamics and Relativity, University of Cambridge Part IA Mathematical Tripos lecture notes, Lent 2013, http://www.damtp.cam.ac.uk/user/tong/relativity.html — §4.3.1, eq. (4.14) with $r_0 = l^2/k$ and $e = Al^2/k$, p. 57; derived from the orbit equation (4.11), p. 56.

import Definitions.Def_DynamicsRelativity_CentralForces_Defs
import Mathlib

open DynamicsRelativity

theorem DynamicsRelativity.kepler_orbit_conic {k m : ℝ} {x : ℝ → Vec}
    (hk : 0 < k) (h : KeplerMotion k m x) (hL : angularMomentum m x 0 ≠ 0) :
    ∃ A : Vec, ∀ t, ‖x t‖ + inner ℝ A (x t) =
      (‖angularMomentum m x 0‖ / m) ^ 2 / k := by sorry
