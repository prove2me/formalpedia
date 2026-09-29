-- Prove2me | Theorems.Thm_DoCarmoDG_christoffel_decomposition
-- name    : DoCarmoDG.christoffel_decomposition
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T01:02:05.365624+00:00
-- url     : https://prove2.me/theorems/7ccd4dab-2d03-4579-b693-5fa7442e8f5a
-- title:
--   Existence and uniqueness of the Christoffel symbols
-- statement:
--   do Carmo §4-3, equations (1). For a regular patch the vectors $x_u$, $x_v$, $N$ form a basis of $\mathbb{R}^3$ at each point, so the second derivatives of $x$ decompose as
--
--   $$ x_{uu} = \Gamma^1_{11}x_u + \Gamma^2_{11}x_v + eN, \quad x_{uv} = \Gamma^1_{12}x_u + \Gamma^2_{12}x_v + fN, \quad x_{vv} = \Gamma^1_{22}x_u + \Gamma^2_{22}x_v + gN, $$
--
--   and the tangential coefficients — the Christoffel symbols of the patch — are uniquely determined at each point of the domain.
-- source:
--   Manfredo P. do Carmo, Differential Geometry of Curves and Surfaces, 2nd ed., Dover, 2016, Chapter 4, Section 4-3 (pp. 235-240)

import Definitions.Def_DoCarmo_surface_patch

namespace DoCarmoDG

theorem christoffel_decomposition
    (U : Set (ℝ × ℝ)) (hU : IsOpen U) (x : ℝ → ℝ → EuclideanSpace ℝ (Fin 3))
    (hx : IsRegularPatch U x) :
    ∃ G111 G211 G112 G212 G122 G222 : ℝ → ℝ → ℝ,
      IsChristoffel U x G111 G211 G112 G212 G122 G222 ∧
      ∀ H111 H211 H112 H212 H122 H222 : ℝ → ℝ → ℝ,
        IsChristoffel U x H111 H211 H112 H212 H122 H222 →
        ∀ p ∈ U,
          H111 p.1 p.2 = G111 p.1 p.2 ∧ H211 p.1 p.2 = G211 p.1 p.2 ∧
          H112 p.1 p.2 = G112 p.1 p.2 ∧ H212 p.1 p.2 = G212 p.1 p.2 ∧
          H122 p.1 p.2 = G122 p.1 p.2 ∧ H222 p.1 p.2 = G222 p.1 p.2 := by sorry

end DoCarmoDG
