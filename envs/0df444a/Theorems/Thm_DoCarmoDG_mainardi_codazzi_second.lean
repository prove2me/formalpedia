-- Prove2me | Theorems.Thm_DoCarmoDG_mainardi_codazzi_second
-- name    : DoCarmoDG.mainardi_codazzi_second
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T01:11:21.322354+00:00
-- url     : https://prove2.me/theorems/8554d523-a46e-441d-8297-3ec9f92c900f
-- title:
--   Mainardi--Codazzi equation (6a)
-- statement:
--   The second Mainardi–Codazzi equation, do Carmo §4-3, equation (6a) (p. 238):
--
--   $$ f_v - g_u = e\Gamma^1_{22} + f(\Gamma^2_{22} - \Gamma^1_{12}) - g\Gamma^2_{12}. $$
-- source:
--   Manfredo P. do Carmo, Differential Geometry of Curves and Surfaces, 2nd ed., Dover, 2016, Chapter 4, Section 4-3 (pp. 235-240)

import Definitions.Def_DoCarmo_surface_patch

namespace DoCarmoDG

theorem mainardi_codazzi_second
    (U : Set (ℝ × ℝ)) (hU : IsOpen U) (x : ℝ → ℝ → EuclideanSpace ℝ (Fin 3))
    (hx : IsRegularPatch U x)
    (G111 G211 G112 G212 G122 G222 : ℝ → ℝ → ℝ)
    (hG : IsChristoffel U x G111 G211 G112 G212 G122 G222) :
    ∀ p ∈ U,
      deriv (fun t => coefff x p.1 t) p.2 - deriv (fun t => coeffg x t p.2) p.1 =
        coeffe x p.1 p.2 * G122 p.1 p.2 +
          coefff x p.1 p.2 * (G222 p.1 p.2 - G112 p.1 p.2) -
          coeffg x p.1 p.2 * G212 p.1 p.2 := by sorry

end DoCarmoDG
