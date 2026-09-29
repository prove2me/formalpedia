-- Prove2me | Theorems.Thm_DynamicsRelativity_kepler_runge_lenz_in_plane
-- name    : DynamicsRelativity.kepler_runge_lenz_in_plane
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-22T23:54:09.625853+00:00
-- url     : https://prove2.me/theorems/b47297fd-7a3d-41a0-acda-eb06c54a48f6
-- title:
--   Kepler Laplace--Runge--Lenz vector lies in orbital plane and satisfies orbit equation
-- statement:
--   For any Kepler motion with positive coupling $k>0$, positive particle mass $m>0$, and non-vanishing initial angular momentum $L(0) \neq 0$, there exists a constant Laplace--Runge--Lenz eccentricity vector $A \in \mathbb{R}^3$ lying in the orbital plane that satisfies the polar conic orbit equation for all times $t \in \mathbb{R}$:
--
--   $$ \langle L(0), A\rangle = 0 \quad \text{and} \quad \forall t \in \mathbb{R},\quad \|x(t)\| + \langle A, x(t)\rangle = \frac{\|L(0)/m\|^2}{k}. $$
--
--   This is the geometric and kinematic core of the Laplace--Runge--Lenz vector from David Tong's *Dynamics and Relativity* (§4.3.1, eq. 4.14). The vector $A = \frac{\dot{x} \times L}{km} - \hat{x}$ is conserved along the motion, is orthogonal to the angular momentum vector $L(0)$, and taking its scalar product with the radius vector $x(t)$ produces the standard polar conic equation with semi-latus rectum $r_0 = (\|L(0)\|/m)^2 / k$.
-- source:
--   David Tong, Dynamics and Relativity, University of Cambridge Part IA Mathematical Tripos lecture notes, Lent 2013, §4.3.1, eq. (4.14), p. 57.

import Definitions.Def_DynamicsRelativity_CentralForces_Defs
import Mathlib

open DynamicsRelativity

theorem DynamicsRelativity.kepler_runge_lenz_in_plane {k m : ℝ} {x : ℝ → Vec} (hk : 0 < k) (h : KeplerMotion k m x) (hL : angularMomentum m x 0 ≠ 0) : ∃ A : Vec, inner ℝ (angularMomentum m x 0) A = 0 ∧ ∀ t, ‖x t‖ + inner ℝ A (x t) = (‖angularMomentum m x 0‖ / m) ^ 2 / k := by sorry
