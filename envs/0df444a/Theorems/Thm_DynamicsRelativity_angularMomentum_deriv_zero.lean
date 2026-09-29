-- Prove2me | Theorems.Thm_DynamicsRelativity_angularMomentum_deriv_zero
-- name    : DynamicsRelativity.angularMomentum_deriv_zero
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T00:37:33.966205+00:00
-- url     : https://prove2.me/theorems/312d3502-3fca-451e-b786-c3dd9f84f102
-- title:
--   Time derivative of angular momentum vanishes in central force motion
-- statement:
--   For any particle of mass $m > 0$ undergoing central force motion $h : \text{CentralForceMotion } m\ F\ x$ with equation of motion $m \ddot{x} = F(r) \hat{r}$, the time derivative of its angular momentum vector $L(t) = m (x(t) \times \dot{x}(t))$ is zero at every time $t \in \mathbb{R}$:
--
--   $$ \frac{d}{dt} L(t) = 0. $$
--
--   This is Tong eq. (4.2), following from the product rule for cross products $\frac{d}{dt}(x \times \dot{x}) = \dot{x} \times \dot{x} + x \times \ddot{x}$. The first term vanishes because the cross product of any vector with itself is zero ($\dot{x} \times \dot{x} = 0$), and the second term vanishes because the central force is purely radial, so the acceleration $\ddot{x}$ is proportional to $x$ ($x \times x = 0$).
-- source:
--   David Tong, Dynamics and Relativity, University of Cambridge Part IA Mathematical Tripos lecture notes, Lent 2013, §4, p. 48.

import Definitions.Def_DynamicsRelativity_CentralForces_Defs
import Mathlib

open DynamicsRelativity

theorem DynamicsRelativity.angularMomentum_deriv_zero {m : ℝ} {F : ℝ → ℝ} {x : ℝ → Vec} (h : CentralForceMotion m F x) (t : ℝ) : deriv (angularMomentum m x) t = 0 := by sorry
