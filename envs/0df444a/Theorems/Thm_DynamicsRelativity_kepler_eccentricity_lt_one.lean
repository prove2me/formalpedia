-- Prove2me | Theorems.Thm_DynamicsRelativity_kepler_eccentricity_lt_one
-- name    : DynamicsRelativity.kepler_eccentricity_lt_one
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-22T23:54:00.297384+00:00
-- url     : https://prove2.me/theorems/af65410c-8475-439b-8a55-0fa1996cfe7f
-- title:
--   Negative energy implies eccentricity strictly less than 1 in Kepler motion
-- statement:
--   For any Kepler motion with positive coupling $k>0$, non-vanishing initial angular momentum $L(0) \neq 0$, and negative total energy $E(0) < 0$, if an eccentricity vector $A \in \mathbb{R}^3$ lies in the orbital plane and satisfies the polar conic equation of the orbit, then its norm is strictly bounded above by 1:
--
--   $$ \|A\| < 1. $$
--
--   This corresponds to David Tong's *Dynamics and Relativity* (§4.3.1, eq. 4.16, pp. 57–58), where the magnitude of the Runge--Lenz vector $e = \|A\| $ is related to the total mechanical energy $E$ by $e^2 - 1 = \frac{2 E (L/m)^2}{m k^2}$. Since $E(0) < 0$, $k > 0$, and $m > 0$, it follows that $e^2 < 1$, establishing that bound orbits are precisely those with eccentricity $e < 1$ (ellipses or circles).
-- source:
--   David Tong, Dynamics and Relativity, University of Cambridge Part IA Mathematical Tripos lecture notes, Lent 2013, §4.3.1, eq. (4.16), pp. 57–58.

import Definitions.Def_DynamicsRelativity_CentralForces_Defs
import Mathlib

open DynamicsRelativity

theorem DynamicsRelativity.kepler_eccentricity_lt_one {k m : ℝ} {x : ℝ → Vec} {A : Vec} (hk : 0 < k) (h : KeplerMotion k m x) (hL : angularMomentum m x 0 ≠ 0) (hE : keplerEnergy k m x 0 < 0) (hAn : inner ℝ (angularMomentum m x 0) A = 0) (hA : ∀ t, ‖x t‖ + inner ℝ A (x t) = (‖angularMomentum m x 0‖ / m) ^ 2 / k) : ‖A‖ < 1 := by sorry
