-- Prove2me | Theorems.Thm_DynamicsRelativity_angularMomentum_differentiable
-- name    : DynamicsRelativity.angularMomentum_differentiable
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T00:37:32.319926+00:00
-- url     : https://prove2.me/theorems/1c50f822-8304-4fe3-9507-870589994d48
-- title:
--   Angular momentum trajectory is differentiable everywhere for central force motion
-- statement:
--   For any particle undergoing central force motion $h : \text{CentralForceMotion } m\ F\ x$ whose trajectory $x$ is twice continuously differentiable ($C^2$), the instantaneous angular momentum map $t \mapsto L(t) = m (x(t) \times \dot{x}(t))$ is differentiable on all of $\mathbb{R}$.
-- source:
--   David Tong, Dynamics and Relativity, University of Cambridge Part IA Mathematical Tripos lecture notes, Lent 2013, §4, p. 48.

import Definitions.Def_DynamicsRelativity_CentralForces_Defs
import Mathlib

open DynamicsRelativity

theorem DynamicsRelativity.angularMomentum_differentiable {m : ℝ} {F : ℝ → ℝ} {x : ℝ → Vec} (h : CentralForceMotion m F x) : Differentiable ℝ (angularMomentum m x) := by sorry
