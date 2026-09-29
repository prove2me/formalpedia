-- Prove2me | Theorems.Thm_DoCarmoDG_gauss_formula
-- name    : DoCarmoDG.gauss_formula
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T01:03:13.62153+00:00
-- url     : https://prove2.me/theorems/4790fe05-f940-42d0-af0e-e597a8e0c192
-- title:
--   Gauss formula (equation (5))
-- statement:
--   The **Gauss formula**, do Carmo §4-3, equation (5) (p. 237):
--
--   $$ (\Gamma^2_{12})_u - (\Gamma^2_{11})_v + \Gamma^1_{12}\Gamma^2_{11} + \Gamma^2_{12}\Gamma^2_{12} - \Gamma^2_{11}\Gamma^2_{22} - \Gamma^1_{11}\Gamma^2_{12} = -EK. $$
--
--   The left-hand side involves only the Christoffel symbols, hence only the first fundamental form; the right-hand side involves the Gaussian curvature. This identity is the computational heart of the Theorema Egregium.
-- source:
--   Manfredo P. do Carmo, Differential Geometry of Curves and Surfaces, 2nd ed., Dover, 2016, Chapter 4, Section 4-3 (pp. 235-240)

import Definitions.Def_DoCarmo_surface_patch

namespace DoCarmoDG

theorem gauss_formula
    (U : Set (ℝ × ℝ)) (hU : IsOpen U) (x : ℝ → ℝ → EuclideanSpace ℝ (Fin 3))
    (hx : IsRegularPatch U x)
    (G111 G211 G112 G212 G122 G222 : ℝ → ℝ → ℝ)
    (hG : IsChristoffel U x G111 G211 G112 G212 G122 G222) :
    ∀ p ∈ U,
      deriv (fun t => G212 t p.2) p.1 - deriv (fun t => G211 p.1 t) p.2 +
          G112 p.1 p.2 * G211 p.1 p.2 + G212 p.1 p.2 * G212 p.1 p.2 -
          G211 p.1 p.2 * G222 p.1 p.2 - G111 p.1 p.2 * G212 p.1 p.2 =
        -(coeffE x p.1 p.2) * gaussCurvature x p.1 p.2 := by sorry

end DoCarmoDG
