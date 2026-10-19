-- Prove2me | Theorems.Thm_EuclideanSpace_integral_divergence_ball_three
-- name    : EuclideanSpace.integral_divergence_ball_three
-- status  : Proved
-- author  : @fizzyinc3
-- created : 2026-10-17T19:07:29.087061+00:00
-- url     : https://prove2.me/theorems/d52c6b97-6e6e-43a0-a71a-ac6ea29e1541
-- title:
--   Divergence theorem on a three-dimensional Euclidean ball
-- statement:
--   Let $F:\mathbb R^3\to\mathbb R^3$ be continuously differentiable, let $R>0$, and let $B_R$ be the open Euclidean ball of radius $R$ centered at the origin. Writing $d\sigma$ for surface area measure on the unit sphere $S^2$, its divergence and outward flux satisfy
--
--   $$\int_{B_R}\operatorname{div}F(x)\,dx
--   =R^2\int_{S^2}\langle F(Ru),u\rangle\,d\sigma(u).$$
--
--   This form of the divergence theorem converts volume integrals of second-Hessian null Lagrangians into boundary fluxes. It applies to arbitrary vector fields and does not assume a vacuum equation or spherical symmetry.
--
--   **Formalization Note** The unit-sphere measure is `volume.toSphere`, without probability normalization. The vector field is defined and continuously differentiable on all of Euclidean space; in particular, it and its derivative are bounded on each closed ball, and both displayed integrals exist.
-- source:
--   Bray, Hamm, Hirsch, Wheeler, Zhang, Flatly Foliated Relativity, https://arxiv.org/html/1911.00967v2, proof of Theorem 5, equations (84)–(85) and (94)–(95): the standard divergence theorem on Euclidean balls, stated independently of the vacuum equations.

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open scoped ContDiff
open MeasureTheory Metric

theorem EuclideanSpace.integral_divergence_ball_three
    (F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hF : ContDiff ℝ 1 F) (R : ℝ) (hR : 0 < R) :
    (∫ x in ball (0 : EuclideanSpace ℝ (Fin 3)) R,
      ∑ i : Fin 3, (fderiv ℝ F x (EuclideanSpace.single i 1)) i) =
    R ^ 2 * ∫ u : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      inner ℝ (F (R • u.1)) u.1 ∂((volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere) := by sorry
