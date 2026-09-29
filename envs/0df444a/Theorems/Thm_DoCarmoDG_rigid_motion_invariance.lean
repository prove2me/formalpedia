-- Prove2me | Theorems.Thm_DoCarmoDG_rigid_motion_invariance
-- name    : DoCarmoDG.rigid_motion_invariance
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T00:49:40.609299+00:00
-- url     : https://prove2.me/theorems/16e9cbde-dd2d-4af5-af96-9cd4ea2d6656
-- title:
--   Arc length, curvature and torsion are invariant under rigid motions
-- statement:
--   do Carmo §1-5, Exercise 6(c) (p. 23): the arc length, the curvature and the torsion of a parametrized curve are invariant under rigid motions. Concretely, if $M$ is an orthogonal linear map of positive determinant followed by a translation and $\alpha$ is parametrized by arc length with $k \neq 0$, then $M \circ \alpha$ is again parametrized by arc length and has the same curvature and the same torsion at every parameter value. The positivity of the determinant is what makes the torsion — and not only its absolute value — invariant.
-- source:
--   Manfredo P. do Carmo, Differential Geometry of Curves and Surfaces, 2nd ed., Dover, 2016, Chapter 1, Section 1-4 (pp. 12-15), and Section 1-5, Exercise 6 (p. 23)

import Definitions.Def_DoCarmo_local_theory_curves

namespace DoCarmoDG

theorem rigid_motion_invariance
    (a b : ℝ) (alpha : ℝ → EuclideanSpace ℝ (Fin 3))
    (M : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hM : IsRigidMotion M)
    (halpha : IsArcLengthCurve (Set.Ioo a b) alpha)
    (hk : ∀ s ∈ Set.Ioo a b, curvature alpha s ≠ 0) :
    IsArcLengthCurve (Set.Ioo a b) (M ∘ alpha) ∧
      ∀ s ∈ Set.Ioo a b,
        curvature (M ∘ alpha) s = curvature alpha s ∧
        torsion (M ∘ alpha) s = torsion alpha s := by sorry

end DoCarmoDG
