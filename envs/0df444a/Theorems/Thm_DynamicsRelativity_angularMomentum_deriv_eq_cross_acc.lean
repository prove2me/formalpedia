-- Prove2me | Theorems.Thm_DynamicsRelativity_angularMomentum_deriv_eq_cross_acc
-- name    : DynamicsRelativity.angularMomentum_deriv_eq_cross_acc
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T00:47:20.947117+00:00
-- url     : https://prove2.me/theorems/e5501a8f-714d-4dcd-b8b8-c9f4f6420894
-- title:
--   Time derivative of angular momentum equals mass times position cross acceleration
-- statement:
--   For a particle of mass $m > 0$ undergoing central force motion $h : \text{CentralForceMotion } m\ F\ x$, the time derivative of its angular momentum $L(t) = m (x(t) \times \dot{x}(t))$ is equal to $m (x(t) \times \ddot{x}(t))$:
--
--   $$ \frac{d}{dt} L(t) = m (x(t) \times \ddot{x}(t)). $$
--
--   This follows from applying the Leibniz product rule for the cross product to $\frac{d}{dt}(x \times \dot{x}) = \dot{x} \times \dot{x} + x \times \ddot{x}$, where the velocity self-cross product $\dot{x}(t) \times \dot{x}(t) = 0$ vanishes by antisymmetry.
-- source:
--   David Tong, Dynamics and Relativity, University of Cambridge Part IA Mathematical Tripos lecture notes, Lent 2013, §4, p. 48, eq. (4.2).

import Definitions.Def_DynamicsRelativity_CentralForces_Defs
import Mathlib

open DynamicsRelativity

theorem DynamicsRelativity.angularMomentum_deriv_eq_cross_acc {m : ℝ} {F : ℝ → ℝ} {x : ℝ → Vec} (h : CentralForceMotion m F x) (t : ℝ) : deriv (angularMomentum m x) t = m • cross (x t) (acc x t) := by sorry
