-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Hom_range_subset_of_closedPoint_mem
-- name    : AlgebraicGeometry.Scheme.Hom.range_subset_of_closedPoint_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/30691082-307f-5737-be19-412a1b51cb18
-- title:
--   Morphism from Spec of a local ring meets only opens containing the closed point
-- statement:
--   Let $O$ be a commutative ring which is local, with closed point $\mathfrak m =$ `IsLocalRing.closedPoint O` of $\operatorname{Spec} O$, and let $Y$ be a scheme (in the same universe). Let $W$ be an open subset of $Y$, i.e. an element of `Y.Opens`, and let $\sigma \colon \operatorname{Spec}(O) \to Y$ be a morphism of schemes, where $\operatorname{Spec}$ is applied to $O$ viewed as an object of `CommRingCat`. Assume that the image of the closed point under the underlying continuous map of $\sigma$, namely $\sigma_{\mathrm{base}}(\mathfrak m)$, lies in $W$. The conclusion is that the whole set-theoretic range of $\sigma_{\mathrm{base}}$ is contained in the underlying set of $W$: every point of $\operatorname{Spec} O$ is carried by $\sigma$ into $W$. Equivalently, a morphism from the spectrum of a local ring lands in any open subset of the target that contains the image of the closed point, so that $\sigma$ factors (set-theoretically, hence as a morphism) through the open subscheme $W$.
--
--   This is the standard fact that $\operatorname{Spec}$ of a local ring has a unique closed point to which every point specialises, so that a morphism out of it cannot leave an open neighbourhood of the image of that closed point; it is the mechanism by which a section valued in a local ring is seen to factor through an open subscheme. It is used in the analysis of sections of resolved models of modular curves, for instance in identifying the component support of a section and in the Euler-characteristic computations for pullbacks of strict transforms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Hom_range_subset_of_closedPoint_mem.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Hom.range_subset_of_closedPoint_mem
    {O : Type u} [CommRing O] [IsLocalRing O] {Y : Scheme.{u}}
    (W : Y.Opens) (σ : Spec (CommRingCat.of O) ⟶ Y) (hW : σ.base (IsLocalRing.closedPoint O) ∈ W) :
    Set.range σ.base ⊆ (W : Set Y) := by sorry
