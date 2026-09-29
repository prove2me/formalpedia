-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Hom_mem_smoothLocus_of_isRegularLocalRing_stalk_of_ringKrullDim_le_one_of_perfectField
-- name    : AlgebraicGeometry.Scheme.Hom.mem_smoothLocus_of_isRegularLocalRing_stalk_of_ringKrullDim_le_one_of_perfectField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/6be5676f-0fda-5625-8e57-05833de94fe1
-- title:
--   Regular points of dimension ≤ 1 over a perfect field are smooth
-- statement:
--   Let $K$ be a perfect field and let $Y$ be a scheme (in the same universe), equipped with a morphism $g \colon Y \to \operatorname{Spec} K$ that is locally of finite presentation. Let $y$ be a point of $Y$ and assume that the stalk $\mathcal{O}_{Y,y}$ of the structure presheaf of $Y$ at $y$ is a regular local ring, and that its Krull dimension, as an element of $\mathbb{N}_\infty$ with a bottom element adjoined, satisfies $\dim \mathcal{O}_{Y,y} \le 1$. The conclusion is that $y$ belongs to the smooth locus of $g$, the set of points at which $g$ is smooth; by the Mathlib characterisation `Scheme.Hom.mem_smoothLocus` used in the proof, this amounts to the assertion that the algebra $\mathcal{O}_{Y,y}$ over the stalk of the structure sheaf of $\operatorname{Spec} K$ at $g(y)$, via the stalk map of $g$ at $y$, is formally smooth. Thus the statement is the case of relative dimension at most one (local rings that are fields or discrete valuation rings) of the general regularity-implies-smoothness theorem over a perfect field.
--
--   This is the dimension $\le 1$ case of the classical fact that over a perfect field a regular point of a scheme locally of finite presentation is a smooth point (equivalently, a normal curve over a perfect field is smooth); perfectness cannot be dropped. It is used in the construction of smooth models of modular curves, in the results on open subschemes of two-chart integral models of $X_H$ that are smooth over the base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Hom_mem_smoothLocus_of_isRegularLocalRing_stalk_of_ringKrullDim_le_one_of_perfectField.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Hom.mem_smoothLocus_of_isRegularLocalRing_stalk_of_ringKrullDim_le_one_of_perfectField
    {K : Type u} [Field K] [PerfectField K] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (CommRingCat.of K)) [LocallyOfFinitePresentation g]
    (y : ↥Y) (hreg : IsRegularLocalRing (Y.presheaf.stalk y))
    (hdim : ringKrullDim (Y.presheaf.stalk y) ≤ 1) :
    y ∈ g.smoothLocus := by sorry
