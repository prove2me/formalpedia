-- Prove2me | Theorems.Thm_DynamicsRelativity_kepler_energy_const
-- name    : DynamicsRelativity.kepler_energy_const
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-22T23:19:37.134973+00:00
-- url     : https://prove2.me/theorems/f3cb1712-cf83-4e42-beff-451eea9237c4
-- title:
--   Conservation of energy in the Kepler problem
-- statement:
--   Let a particle of mass $m>0$ move under the inverse-square law, $m\ddot x = -km\,x/r^{3}$, the force of Tong's potential (4.12) $V(r)=-km/r$. Then its total energy
--
--   $$ E(t) \;=\; \tfrac12 m\lVert\dot x(t)\rVert^{2} \;-\; \frac{km}{r(t)}, \qquad r=\lVert x\rVert, $$
--
--   is the same at all times.
--
--   Energy conservation is what makes the qualitative classification of orbits by the effective potential possible in §4.2.1, and it is the conserved quantity that the energy–eccentricity relation (4.16) evaluates. Together with the conservation of angular momentum it supplies the constants of the motion from which the orbit is determined.
-- source:
--   David Tong, Dynamics and Relativity, University of Cambridge Part IA Mathematical Tripos lecture notes, Lent 2013, http://www.damtp.cam.ac.uk/user/tong/relativity.html — §4.3, p. 55 and §4.3.1, eq. (4.12), p. 56; the energy is displayed at the top of p. 59 ("The energy of a given orbit is $E=\tfrac12 m\dot r^2 + ml^2/2r^2 - km/r$").

import Definitions.Def_DynamicsRelativity_CentralForces_Defs
import Mathlib

open DynamicsRelativity

theorem DynamicsRelativity.kepler_energy_const {k m : ℝ} {x : ℝ → Vec}
    (h : KeplerMotion k m x) (t₀ t₁ : ℝ) :
    keplerEnergy k m x t₀ = keplerEnergy k m x t₁ := by sorry
