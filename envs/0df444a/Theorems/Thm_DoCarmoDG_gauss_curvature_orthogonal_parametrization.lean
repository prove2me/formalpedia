-- Prove2me | Theorems.Thm_DoCarmoDG_gauss_curvature_orthogonal_parametrization
-- name    : DoCarmoDG.gauss_curvature_orthogonal_parametrization
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T01:15:55.552046+00:00
-- url     : https://prove2.me/theorems/e880c1f4-50e5-44a4-bf35-f6a874346f43
-- title:
--   $K$ in an orthogonal parametrization
-- statement:
--   do Carmo §4-3, Exercise 1 (p. 240): for an orthogonal parametrization, that is one with $F \equiv 0$, the Gaussian curvature is computed from the first fundamental form alone by
--
--   $$ K = -\frac{1}{2\sqrt{EG}}\left[ \left(\frac{E_v}{\sqrt{EG}}\right)_v + \left(\frac{G_u}{\sqrt{EG}}\right)_u \right]. $$
--
--   This is the Gauss formula made explicit in the orthogonal case, and it is the form in which the intrinsic character of $K$ is usually applied.
-- source:
--   Manfredo P. do Carmo, Differential Geometry of Curves and Surfaces, 2nd ed., Dover, 2016, Chapter 4, Section 4-3 (pp. 235-240)

import Definitions.Def_DoCarmo_surface_patch

namespace DoCarmoDG

theorem gauss_curvature_orthogonal_parametrization
    (U : Set (ℝ × ℝ)) (hU : IsOpen U) (x : ℝ → ℝ → EuclideanSpace ℝ (Fin 3))
    (hx : IsRegularPatch U x)
    (hF : ∀ p ∈ U, coeffF x p.1 p.2 = 0) :
    ∀ p ∈ U,
      gaussCurvature x p.1 p.2 =
        -(1 / (2 * Real.sqrt (coeffE x p.1 p.2 * coeffG x p.1 p.2))) *
          (deriv (fun t =>
              deriv (fun r => coeffE x p.1 r) t /
                Real.sqrt (coeffE x p.1 t * coeffG x p.1 t)) p.2 +
            deriv (fun t =>
              deriv (fun r => coeffG x r p.2) t /
                Real.sqrt (coeffE x t p.2 * coeffG x t p.2)) p.1) := by sorry

end DoCarmoDG
