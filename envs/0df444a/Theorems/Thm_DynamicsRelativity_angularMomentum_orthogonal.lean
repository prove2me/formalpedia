-- Prove2me | Theorems.Thm_DynamicsRelativity_angularMomentum_orthogonal
-- name    : DynamicsRelativity.angularMomentum_orthogonal
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T00:06:13.113229+00:00
-- url     : https://prove2.me/theorems/79f6733a-c80f-46c9-a8d3-15da0ec72085
-- title:
--   Instantaneous angular momentum is orthogonal to position and velocity
-- statement:
--   For any particle of mass $m \in \mathbb{R}$ with trajectory $x : \mathbb{R} \to \mathbb{R}^3$, the instantaneous angular momentum vector $L(t) = m (x(t) \times \dot{x}(t))$ is orthogonal to both the instantaneous position vector $x(t)$ and the instantaneous velocity vector $\dot{x}(t)$ for all $t \in \mathbb{R}$:
--
--   $$ \langle L(t), x(t)\rangle = 0 \quad \text{and} \quad \langle L(t), \dot{x}(t)\rangle = 0. $$
--
--   This is the algebraic identity from David Tong's *Dynamics and Relativity* (§4, p. 48) stating that the scalar triple product $(x \times \dot{x}) \cdot x = 0$ and $(x \times \dot{x}) \cdot \dot{x} = 0$ vanishes because the cross product of two vectors is orthogonal to each of its factors. Combined with the conservation law $L(t) = L(0)$, this establishes that central force motion is strictly planar.
-- source:
--   David Tong, Dynamics and Relativity, University of Cambridge Part IA Mathematical Tripos lecture notes, Lent 2013, §4, p. 48.

import Definitions.Def_DynamicsRelativity_CentralForces_Defs
import Mathlib

open DynamicsRelativity

theorem DynamicsRelativity.angularMomentum_orthogonal (m : ℝ) (x : ℝ → Vec) (t : ℝ) : inner ℝ (angularMomentum m x t) (x t) = 0 ∧ inner ℝ (angularMomentum m x t) (vel x t) = 0 := by sorry
