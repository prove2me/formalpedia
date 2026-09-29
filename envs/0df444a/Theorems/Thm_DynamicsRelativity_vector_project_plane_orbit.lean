-- Prove2me | Theorems.Thm_DynamicsRelativity_vector_project_plane_orbit
-- name    : DynamicsRelativity.vector_project_plane_orbit
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T00:01:28.970059+00:00
-- url     : https://prove2.me/theorems/83164fb4-ea3a-412d-8066-1087235efa33
-- title:
--   Orthogonal projection of orbit eccentricity vector onto the orbital plane
-- statement:
--   Let $n \in \mathbb{R}^3$ be a non-zero normal vector defining an orbital plane, and let $x : \mathbb{R} \to \mathbb{R}^3$ be a planar trajectory satisfying $\langle n, x(t)\rangle = 0$ for all $t \in \mathbb{R}$. If $A \in \mathbb{R}^3$ is any vector satisfying the polar conic equation
--
--   $$ \forall t \in \mathbb{R},\quad \|x(t)\| + \langle A, x(t)\rangle = r_0 $$
--
--   for some semi-latus rectum $r_0 \in \mathbb{R}$, then there exists an in-plane vector $A' \in \mathbb{R}^3$ orthogonal to $n$ satisfying the exact same polar conic equation:
--
--   $$ \langle n, A'\rangle = 0 \quad \text{and} \quad \forall t \in \mathbb{R},\quad \|x(t)\| + \langle A', x(t)\rangle = r_0. $$
--
--   This is the geometric projection lemma connecting a general conic eccentricity vector to the orbital plane in David Tong's *Dynamics and Relativity* (§4.3.1, p. 57, eq. 4.14). The vector $A'$ is the orthogonal projection $A' = A - \frac{\langle n, A\rangle}{\|n\|^2} n$; since the motion $x(t)$ is entirely perpendicular to $n$, the inner product $\langle A', x(t)\rangle = \langle A, x(t)\rangle$ is preserved for every point along the trajectory while guaranteeing that $A'$ lies within the plane of motion.
-- source:
--   David Tong, Dynamics and Relativity, University of Cambridge Part IA Mathematical Tripos lecture notes, Lent 2013, §4.3.1, eq. (4.14) and p. 57.

import Definitions.Def_DynamicsRelativity_CentralForces_Defs
import Mathlib

open DynamicsRelativity

theorem DynamicsRelativity.vector_project_plane_orbit {n : Vec} {x : ℝ → Vec} {A : Vec} {r₀ : ℝ} (hn : n ≠ 0) (h_plane : ∀ t, inner ℝ n (x t) = 0) (h_orbit : ∀ t, ‖x t‖ + inner ℝ A (x t) = r₀) : ∃ A' : Vec, inner ℝ n A' = 0 ∧ ∀ t, ‖x t‖ + inner ℝ A' (x t) = r₀ := by sorry
