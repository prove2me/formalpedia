-- Prove2me | Theorems.Thm_DynamicsRelativity_kepler_energy_eccentricity
-- name    : DynamicsRelativity.kepler_energy_eccentricity
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-09-22T23:21:03.259128+00:00
-- url     : https://prove2.me/theorems/60a22259-2654-4317-98f2-1d35daca789c
-- title:
--   The energy of an inverse-square orbit in terms of its eccentricity
-- statement:
--   This is Tong's equation (4.16), the relation between the energy of an inverse-square orbit and its eccentricity.
--
--   Let a particle of mass $m>0$ move under the attractive inverse-square law of strength $k>0$ with nonvanishing angular momentum, and suppose its orbit is the conic of semi-latus rectum $r_0=l^{2}/k$ and eccentricity vector $A$ produced by equation (4.14), where $l=\lVert L\rVert/m$. Writing $e=\lVert A\rVert$ for the eccentricity, the total energy is
--
--   $$ E \;=\; \frac{m k^{2}}{2 l^{2}}\,\big(e^{2}-1\big), $$
--
--   independently of time — as it must be, the energy being a constant of the motion; the source notes that all the $\theta$-dependence cancels after a couple of lines of algebra.
--
--   This identity is what converts the dynamical hypothesis $E<0$ into the geometric condition $e<1$, and so links the classification of orbits by energy in §4.2.1 with their classification by eccentricity: $e<1$ exactly when $E<0$ (the bounded, elliptical orbits), $e>1$ exactly when $E>0$ (the unbounded, hyperbolic ones), and $e=0$ exactly at the minimum $E=-mk^{2}/2l^{2}$ of the effective potential, the circular orbit.
-- source:
--   David Tong, Dynamics and Relativity, University of Cambridge Part IA Mathematical Tripos lecture notes, Lent 2013, http://www.damtp.cam.ac.uk/user/tong/relativity.html — §4.3.1, "The Energy of the Orbit Revisited", eq. (4.16) and the three bullet points that follow it, pp. 59–60.

import Definitions.Def_DynamicsRelativity_CentralForces_Defs
import Mathlib

open DynamicsRelativity

theorem DynamicsRelativity.kepler_energy_eccentricity {k m r₀ : ℝ} {x : ℝ → Vec} {A : Vec}
    (hk : 0 < k) (h : KeplerMotion k m x) (hL : angularMomentum m x 0 ≠ 0)
    (hr₀ : r₀ = (‖angularMomentum m x 0‖ / m) ^ 2 / k)
    (hA : ∀ t, ‖x t‖ + inner ℝ A (x t) = r₀) (t : ℝ) :
    keplerEnergy k m x t =
      m * k ^ 2 * (‖A‖ ^ 2 - 1) / (2 * (‖angularMomentum m x 0‖ / m) ^ 2) := by sorry
