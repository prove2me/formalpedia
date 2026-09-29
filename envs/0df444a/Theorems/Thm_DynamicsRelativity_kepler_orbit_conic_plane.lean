-- Prove2me | Theorems.Thm_DynamicsRelativity_kepler_orbit_conic_plane
-- name    : DynamicsRelativity.kepler_orbit_conic_plane
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-22T23:46:52.757509+00:00
-- url     : https://prove2.me/theorems/a5f001ac-5704-4ca2-a073-ab7ed7ec4716
-- title:
--   Kepler orbit eccentricity vector lies in orbital plane with bound < 1
-- statement:
--   For any Kepler motion with positive gravitational parameter $k>0$, non-zero initial angular momentum $L(0) \neq 0$, and negative total energy $E(0) < 0$, the Laplace--Runge--Lenz eccentricity vector $A$ is orthogonal to the angular momentum vector $L(0)$, has norm strictly less than 1, and satisfies the polar conic equation of the orbit for all $t \in \mathbb{R}$:
--
--   $$ \langle L(0), A\rangle = 0 \quad \text{and} \quad \forall t \in \mathbb{R},\quad \|x(t)\| + \langle A, x(t)\rangle = \frac{\|L(0)/m\|^2}{k} \quad \text{and} \quad \|A\| < 1. $$
--
--   This theorem encapsulates the dynamical core of Kepler's First Law from David Tong's lecture notes (eqs. 4.14--4.16). In particular, the condition $\langle L(0), A\rangle = 0$ ensures the eccentricity vector lies in the plane of planetary motion, and the negative energy hypothesis $E(0) < 0$ implies through the energy-eccentricity identity that the eccentricity satisfies $e = \|A\| < 1$, distinguishing elliptic bound orbits from parabolic or hyperbolic trajectories.
-- source:
--   David Tong, Dynamics and Relativity, University of Cambridge Part IA Mathematical Tripos lecture notes, Lent 2013, §4.3.1–§4.3.2, pp. 56–60.

import Definitions.Def_DynamicsRelativity_CentralForces_Defs
import Mathlib

open DynamicsRelativity

theorem DynamicsRelativity.kepler_orbit_conic_plane {k m : ℝ} {x : ℝ → Vec} (hk : 0 < k) (h : KeplerMotion k m x) (hL : angularMomentum m x 0 ≠ 0) (hE : keplerEnergy k m x 0 < 0) : ∃ A : Vec, inner ℝ (angularMomentum m x 0) A = 0 ∧ (∀ t, ‖x t‖ + inner ℝ A (x t) = (‖angularMomentum m x 0‖ / m) ^ 2 / k) ∧ ‖A‖ < 1 := by sorry
