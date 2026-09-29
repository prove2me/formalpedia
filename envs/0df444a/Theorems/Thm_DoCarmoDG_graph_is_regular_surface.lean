-- Prove2me | Theorems.Thm_DoCarmoDG_graph_is_regular_surface
-- name    : DoCarmoDG.graph_is_regular_surface
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T01:26:19.481501+00:00
-- url     : https://prove2.me/theorems/4848f9f3-bb41-4aa4-8f28-640b783a0037
-- title:
--   The graph of a differentiable function is a regular surface
-- statement:
--   do Carmo §2-2, Proposition 1 (p. 59): if $f : U \to \mathbb{R}$ is a differentiable function on an open set $U$ of $\mathbb{R}^2$, then its graph, the subset of $\mathbb{R}^3$ consisting of the points $(x, y, f(x,y))$ with $(x,y) \in U$, is a regular surface. The parametrization $x(u,v) = (u, v, f(u,v))$ covers the whole graph, its Jacobian $\partial(x,y)/\partial(u,v)$ is identically $1$, and its inverse is the restriction of the projection onto the $xy$ plane.
-- source:
--   Manfredo P. do Carmo, Differential Geometry of Curves and Surfaces, 2nd ed., Dover, 2016, Chapter 2, Section 2-2 (pp. 54-71)

import Definitions.Def_DoCarmo_regular_surface

namespace DoCarmoDG

theorem graph_is_regular_surface
    (U : Set (ℝ × ℝ)) (hU : IsOpen U) (f : ℝ × ℝ → ℝ)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U) :
    IsRegularSurface (graphOf U f) := by sorry

end DoCarmoDG
