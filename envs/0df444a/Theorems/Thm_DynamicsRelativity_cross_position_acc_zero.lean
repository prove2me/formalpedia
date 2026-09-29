-- Prove2me | Theorems.Thm_DynamicsRelativity_cross_position_acc_zero
-- name    : DynamicsRelativity.cross_position_acc_zero
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T00:47:11.995433+00:00
-- url     : https://prove2.me/theorems/72c937f7-1c7c-4a8f-9171-948d20f057f8
-- title:
--   Cross product of position and acceleration vanishes in central force motion
-- statement:
--   For any particle undergoing central force motion $h : \text{CentralForceMotion } m\ F\ x$, the cross product of the position vector $x(t)$ and the acceleration vector $\ddot{x}(t) = \text{acc } x(t)$ vanishes at every time $t \in \mathbb{R}$:
--
--   $$ x(t) \times \ddot{x}(t) = 0. $$
--
--   By Newton's second law for a central force ($h.\text{eom}$), $m \ddot{x}(t) = \frac{F(\|x(t)\|)}{\|x(t)\|} x(t)$. Because the force is purely radial, the acceleration is collinear with the radius vector $x(t)$, so their cross product is zero.
-- source:
--   David Tong, Dynamics and Relativity, University of Cambridge Part IA Mathematical Tripos lecture notes, Lent 2013, §4, p. 48, eq. (4.2).

import Definitions.Def_DynamicsRelativity_CentralForces_Defs
import Mathlib

open DynamicsRelativity

theorem DynamicsRelativity.cross_position_acc_zero {m : ℝ} {F : ℝ → ℝ} {x : ℝ → Vec} (h : CentralForceMotion m F x) (t : ℝ) : cross (x t) (acc x t) = 0 := by sorry
