-- Prove2me | Theorems.Thm_DoCarmoDG_christoffel_system
-- name    : DoCarmoDG.christoffel_system
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T01:02:48.535828+00:00
-- url     : https://prove2.me/theorems/f256b385-b02b-496c-afbe-340d6eec70da
-- title:
--   System (2): the Christoffel symbols in terms of $E$, $F$, $G$
-- statement:
--   do Carmo §4-3, system (2). Taking the inner products of the decompositions (1) with $x_u$ and $x_v$ gives three pairs of linear equations for the Christoffel symbols,
--
--   $$ \Gamma^1_{11}E + \Gamma^2_{11}F = \tfrac12 E_u, \qquad \Gamma^1_{11}F + \Gamma^2_{11}G = F_u - \tfrac12 E_v, $$
--   $$ \Gamma^1_{12}E + \Gamma^2_{12}F = \tfrac12 E_v, \qquad \Gamma^1_{12}F + \Gamma^2_{12}G = \tfrac12 G_u, $$
--   $$ \Gamma^1_{22}E + \Gamma^2_{22}F = F_v - \tfrac12 G_u, \qquad \Gamma^1_{22}F + \Gamma^2_{22}G = \tfrac12 G_v, $$
--
--   each pair having determinant $EG - F^2 \neq 0$. This is why the Christoffel symbols, and everything expressed through them, depend only on the first fundamental form.
-- source:
--   Manfredo P. do Carmo, Differential Geometry of Curves and Surfaces, 2nd ed., Dover, 2016, Chapter 4, Section 4-3 (pp. 235-240)

import Definitions.Def_DoCarmo_surface_patch

namespace DoCarmoDG

theorem christoffel_system
    (U : Set (ℝ × ℝ)) (hU : IsOpen U) (x : ℝ → ℝ → EuclideanSpace ℝ (Fin 3))
    (hx : IsRegularPatch U x)
    (G111 G211 G112 G212 G122 G222 : ℝ → ℝ → ℝ)
    (hG : IsChristoffel U x G111 G211 G112 G212 G122 G222) :
    ∀ p ∈ U,
      G111 p.1 p.2 * coeffE x p.1 p.2 + G211 p.1 p.2 * coeffF x p.1 p.2 =
          (1 / 2) * deriv (fun t => coeffE x t p.2) p.1 ∧
      G111 p.1 p.2 * coeffF x p.1 p.2 + G211 p.1 p.2 * coeffG x p.1 p.2 =
          deriv (fun t => coeffF x t p.2) p.1 - (1 / 2) * deriv (fun t => coeffE x p.1 t) p.2 ∧
      G112 p.1 p.2 * coeffE x p.1 p.2 + G212 p.1 p.2 * coeffF x p.1 p.2 =
          (1 / 2) * deriv (fun t => coeffE x p.1 t) p.2 ∧
      G112 p.1 p.2 * coeffF x p.1 p.2 + G212 p.1 p.2 * coeffG x p.1 p.2 =
          (1 / 2) * deriv (fun t => coeffG x t p.2) p.1 ∧
      G122 p.1 p.2 * coeffE x p.1 p.2 + G222 p.1 p.2 * coeffF x p.1 p.2 =
          deriv (fun t => coeffF x p.1 t) p.2 - (1 / 2) * deriv (fun t => coeffG x t p.2) p.1 ∧
      G122 p.1 p.2 * coeffF x p.1 p.2 + G222 p.1 p.2 * coeffG x p.1 p.2 =
          (1 / 2) * deriv (fun t => coeffG x p.1 t) p.2 := by sorry

end DoCarmoDG
