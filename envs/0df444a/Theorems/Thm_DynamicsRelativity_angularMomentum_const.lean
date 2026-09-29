-- Prove2me | Theorems.Thm_DynamicsRelativity_angularMomentum_const
-- name    : DynamicsRelativity.angularMomentum_const
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-22T23:17:20.445526+00:00
-- url     : https://prove2.me/theorems/16dd774b-1ab2-424b-ac6f-552c81c00fb1
-- title:
--   Conservation of angular momentum in a central force field
-- statement:
--   Let a particle of mass $m>0$ move in an arbitrary central force field with radial profile $F$, so that its trajectory $x$ obeys Tong's equation of motion (4.1)
--
--   $$ m\,\ddot x(t) = F\big(r(t)\big)\,\hat r(t), \qquad r=\lVert x\rVert,\ \hat r = x/r . $$
--
--   Then its **angular momentum**
--
--   $$ L(t) \;=\; m\,x(t)\times\dot x(t) $$
--
--   is the same vector at all times.
--
--   This is the first conservation law of the chapter, and the one from which the planarity of the motion and Kepler's second law both follow. The source's argument is that $\dot L = m\,x\times\ddot x = 0$ because the force is parallel to $x$; the statement holds for every central force, with no use of the inverse-square law.
-- source:
--   David Tong, Dynamics and Relativity, University of Cambridge Part IA Mathematical Tripos lecture notes, Lent 2013, http://www.damtp.cam.ac.uk/user/tong/relativity.html — §4, p. 48 (the displayed computation $dL/dt = m\,x\times\ddot x = -x\times\nabla V = 0$).

import Definitions.Def_DynamicsRelativity_CentralForces_Defs
import Mathlib

open DynamicsRelativity

theorem DynamicsRelativity.angularMomentum_const {m : ℝ} {F : ℝ → ℝ} {x : ℝ → Vec}
    (h : CentralForceMotion m F x) (t₀ t₁ : ℝ) :
    angularMomentum m x t₀ = angularMomentum m x t₁ := by sorry
