-- Prove2me | Theorems.Thm_DoCarmoDG_mainardi_codazzi_first
-- name    : DoCarmoDG.mainardi_codazzi_first
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T01:03:44.316191+00:00
-- url     : https://prove2.me/theorems/13a271e0-85c4-4511-8630-210d247f13a2
-- title:
--   Mainardi--Codazzi equation (6)
-- statement:
--   The first Mainardi–Codazzi equation, do Carmo §4-3, equation (6) (p. 238):
--
--   $$ e_v - f_u = e\Gamma^1_{12} + f(\Gamma^2_{12} - \Gamma^1_{11}) - g\Gamma^2_{11}. $$
--
--   It is obtained by equating the normal components in the expansion of $(x_{uu})_v = (x_{uv})_u$, and together with (6a) and the Gauss formula it exhausts the compatibility relations between the first and second fundamental forms.
-- source:
--   Manfredo P. do Carmo, Differential Geometry of Curves and Surfaces, 2nd ed., Dover, 2016, Chapter 4, Section 4-3 (pp. 235-240)

import Definitions.Def_DoCarmo_surface_patch

namespace DoCarmoDG

theorem mainardi_codazzi_first
    (U : Set (ℝ × ℝ)) (hU : IsOpen U) (x : ℝ → ℝ → EuclideanSpace ℝ (Fin 3))
    (hx : IsRegularPatch U x)
    (G111 G211 G112 G212 G122 G222 : ℝ → ℝ → ℝ)
    (hG : IsChristoffel U x G111 G211 G112 G212 G122 G222) :
    ∀ p ∈ U,
      deriv (fun t => coeffe x p.1 t) p.2 - deriv (fun t => coefff x t p.2) p.1 =
        coeffe x p.1 p.2 * G112 p.1 p.2 +
          coefff x p.1 p.2 * (G212 p.1 p.2 - G111 p.1 p.2) -
          coeffg x p.1 p.2 * G211 p.1 p.2 := by sorry

end DoCarmoDG
