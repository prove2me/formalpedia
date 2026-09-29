-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_isDiscreteValuationRing_stalk_of_section
-- name    : AlgebraicGeometry.SmoothOfRelativeDimension.isDiscreteValuationRing_stalk_of_section
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/fc98f8d2-02e2-5a85-b3d9-984d970de344
-- title:
--   Stalk at a k-rational point of a smooth curve is a DVR
-- statement:
--   Let $k$ be a field and let $X$ be a scheme over the base given by a morphism $f \colon X \to \operatorname{Spec} k$, where $X$ is assumed integral and $f$ is assumed smooth of relative dimension $1$ (Mathlib's `SmoothOfRelativeDimension 1 f`). Suppose given a morphism $p \colon \operatorname{Spec} k \to X$ which is a section of $f$, in the sense that $p$ followed by $f$ equals the identity morphism of $\operatorname{Spec} k$; thus $p$ is a $k$-rational point of $X$. Write $x = p(\mathfrak{m})$ for the image under the underlying continuous map of $p$ of the closed point of $\operatorname{Spec} k$, i.e. of the maximal ideal of the local ring $k$. The conclusion is that the stalk $\mathcal{O}_{X,x}$ of the structure sheaf of $X$ at this point is a discrete valuation ring.
--
--   This is the $k$-rational-point form of the statement that the local rings of a smooth curve over $k$ at its closed points are discrete valuation rings, the local ring being read off at the point $p(\mathfrak{m})$ attached to a $k$-point $p$. It is used in the work on smooth proper curves, for instance in the analysis of sections with prescribed poles on a two-chart cover, where one needs the local ring at a rational point to be a discrete valuation ring in order to speak of orders of vanishing there.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmoothOfRelativeDimension_isDiscreteValuationRing_stalk_of_section.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.SmoothOfRelativeDimension.isDiscreteValuationRing_stalk_of_section
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [IsIntegral X] [SmoothOfRelativeDimension 1 f]
    (p : Spec (CommRingCat.of k) ⟶ X) (hp : p ≫ f = 𝟙 _) :
    IsDiscreteValuationRing (X.presheaf.stalk (p.base (IsLocalRing.closedPoint k))) := by sorry
