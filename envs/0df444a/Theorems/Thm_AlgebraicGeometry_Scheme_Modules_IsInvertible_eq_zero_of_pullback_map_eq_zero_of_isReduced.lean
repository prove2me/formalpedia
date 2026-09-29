-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_eq_zero_of_pullback_map_eq_zero_of_isReduced
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.eq_zero_of_pullback_map_eq_zero_of_isReduced
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/8981cdaf-b7ba-5cff-b09f-3879136d6a06
-- title:
--   Vanishing of a line bundle section on a reduced scheme covered by two closed subschemes
-- statement:
--   Let $X$, $Y_1$, $Y_2$ be schemes (in a fixed universe), with $X$ reduced, and let $i_1 \colon Y_1 \to X$ and $i_2 \colon Y_2 \to X$ be closed immersions whose images cover $X$, i.e. the union of the ranges of the underlying continuous maps of $i_1$ and $i_2$ is all of $X$. Let $L$ be a sheaf of modules on $X$ over its structure sheaf which is invertible in the sense of the project's predicate `Scheme.Modules.IsInvertible`: every point $x \in X$ lies in some open $U \subseteq X$ such that the pullback of $L$ along the inclusion $U \hookrightarrow X$ is isomorphic to the unit sheaf of modules $\mathcal{O}_U$ on $U$. Let $\sigma$ be a morphism of sheaves of modules from the unit object $\mathcal{O}_X$ to $L$, that is, a global section of $L$. Assume that the pullback of $\sigma$ along $i_1$ and the pullback of $\sigma$ along $i_2$ are both the zero morphism, of $\mathcal{O}_{Y_1}$- and $\mathcal{O}_{Y_2}$-modules respectively. Then $\sigma = 0$.
--
--   This is the line-bundle form of the statement that on a reduced scheme covered by two closed subschemes a function vanishing on both closed subschemes vanishes; it rests on the injectivity half of the corresponding gluing statement for sections of the structure sheaf, [`AlgebraicGeometry.IsClosedImmersion.app_injective_and_exists_of_app_pullback_eq_of_isReduced`](thm.html#AlgebraicGeometry.IsClosedImmersion.app_injective_and_exists_of_app_pullback_eq_of_isReduced). It is used in the analysis of line bundles on two glued projective lines, to identify the zero scheme of a nonzero section with a relative effective Cartier divisor supported in the prescribed locus.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_eq_zero_of_pullback_map_eq_zero_of_isReduced.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.eq_zero_of_pullback_map_eq_zero_of_isReduced
    {X Y₁ Y₂ : Scheme.{u}} [IsReduced X] (i₁ : Y₁ ⟶ X) (i₂ : Y₂ ⟶ X)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    {L : X.Modules} (hL : Scheme.Modules.IsInvertible L)
    (σ : SheafOfModules.unit X.ringCatSheaf ⟶ L)
    (h₁ : (Scheme.Modules.pullback i₁).map σ = 0) (h₂ : (Scheme.Modules.pullback i₂).map σ = 0) :
    σ = 0 := by sorry
