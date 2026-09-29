-- Prove2me | Theorems.Thm_AlgebraicGeometry_mem_smoothLocus_of_not_mem_range_of_isClosedImmersion
-- name    : AlgebraicGeometry.mem_smoothLocus_of_not_mem_range_of_isClosedImmersion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/d9af551d-cf5a-55c7-a296-0b0217ae7d9f
-- title:
--   Off-crossing points of a reduced fibre lie in the smooth locus
-- statement:
--   Let $R$ be a commutative ring, $C$ a scheme and $c \colon C \to \operatorname{Spec} R$ a morphism that is flat and locally of finite presentation. Let $k$ be a field and $x \colon \operatorname{Spec} k \to \operatorname{Spec} R$ a $k$-valued point, and assume the fibre product $C \times_{\operatorname{Spec} R} \operatorname{Spec} k$ (the Lean `pullback c x`) is a reduced scheme. Let $M_1, M_2$ be schemes, let $g_1 \colon M_1 \to \operatorname{Spec} k$ be smooth of relative dimension $1$, and let $i_1 \colon M_1 \to C \times_R \operatorname{Spec} k$ and $i_2 \colon M_2 \to C \times_R \operatorname{Spec} k$ be closed immersions, with $i_1$ followed by the second projection equal to $g_1$. Assume the two immersions cover the fibre topologically: every point $z$ of $C \times_R \operatorname{Spec} k$ lies in the range of the underlying map of $i_1$ or in the range of that of $i_2$. Then for every point $y$ of the fibre that is not in the range of the underlying map of $i_2$, the image of $y$ under the underlying map of the first projection $C \times_R \operatorname{Spec} k \to C$ belongs to the smooth locus `c.smoothLocus` of $c$.
--
--   This is the statement that points of a reduced fibre lying off the second of two covering closed subschemes — typically the points of a nodal fibre away from the crossing component — are points of the smooth locus of the whole family, a pointwise form of the fibrewise criterion for smoothness. It is used in the analysis of the Deligne–Rapoport model of $X_0(p)$ and its variants, where the two closed subschemes are the components of the special fibre, and is cited by the results constructing étale charts by the affine line on such models.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_mem_smoothLocus_of_not_mem_range_of_isClosedImmersion.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.mem_smoothLocus_of_not_mem_range_of_isClosedImmersion
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [Flat c] [LocallyOfFinitePresentation c]
    {k : Type u} [Field k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    [IsReduced (pullback c x)]
    {M₁ M₂ : Scheme.{u}} (g₁ : M₁ ⟶ Spec (CommRingCat.of k)) [SmoothOfRelativeDimension 1 g₁]
    (i₁ : M₁ ⟶ pullback c x) (i₂ : M₂ ⟶ pullback c x) [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (h₁ : i₁ ≫ pullback.snd c x = g₁)
    (hcover : ∀ z : ↥(pullback c x), z ∈ Set.range i₁.base ∨ z ∈ Set.range i₂.base)
    (y : ↥(pullback c x)) (hy : y ∉ Set.range i₂.base) :
    (pullback.fst c x).base y ∈ c.smoothLocus := by sorry
