-- Prove2me | Theorems.Thm_DoCarmoDG_fundamental_theorem_uniqueness
-- name    : DoCarmoDG.fundamental_theorem_uniqueness
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T00:53:00.775617+00:00
-- url     : https://prove2.me/theorems/7df30779-ef70-4969-9746-91120d2a524e
-- title:
--   Uniqueness: equal curvature and torsion imply congruence by a rigid motion
-- statement:
--   The uniqueness half of the fundamental theorem of the local theory of curves, the part do Carmo proves in the text (pp. 20-22). Two curves parametrized by arc length on the same interval, with the same everywhere-positive curvature function and the same torsion function, differ by a rigid motion: there is an orthogonal map $\rho$ with $\det \rho > 0$ and a vector $c$ with $\bar\alpha = \rho \circ \alpha + c$.
-- source:
--   Manfredo P. do Carmo, Differential Geometry of Curves and Surfaces, 2nd ed., Dover, 2016, Chapter 1, Section 1-5 (pp. 17-22)

import Definitions.Def_DoCarmo_local_theory_curves

namespace DoCarmoDG

theorem fundamental_theorem_uniqueness
    (a b : ℝ) (alpha beta : ℝ → EuclideanSpace ℝ (Fin 3))
    (halpha : IsArcLengthCurve (Set.Ioo a b) alpha)
    (hbeta : IsArcLengthCurve (Set.Ioo a b) beta)
    (hk : ∀ s ∈ Set.Ioo a b, 0 < curvature alpha s)
    (hcurv : ∀ s ∈ Set.Ioo a b, curvature beta s = curvature alpha s)
    (htors : ∀ s ∈ Set.Ioo a b, torsion beta s = torsion alpha s) :
    ∃ M : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
      IsRigidMotion M ∧ ∀ s ∈ Set.Ioo a b, beta s = M (alpha s) := by sorry

end DoCarmoDG
